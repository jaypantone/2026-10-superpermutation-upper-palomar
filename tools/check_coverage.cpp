// Streaming, literal permutation coverage. This checks the supplied word only;
// it does not certify optimality, deletions, a construction, or a file hash.
// C++17, one CPU thread, one bit per permutation and a 1 MiB input buffer.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <numeric>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#endif

static_assert(sizeof(size_t) >= 8, "A 64-bit platform is required.");
constexpr size_t INPUT_BYTES = 1 << 20;
using Factorials = std::array<uint64_t, 14>;

static Factorials factorials(int n) {
    Factorials f{};
    f[0] = 1;
    for (int i = 1; i <= n; ++i) f[i] = f[i - 1] * i;
    return f;
}

// The ring is a permutation, starting at first. In each position, count the
// still unused symbols smaller than this symbol. These are its Lehmer digits.
static uint64_t permutation_rank(const std::array<uint8_t, 13>& ring,
                                 int first, int n, const Factorials& f) {
    unsigned unused = (1u << n) - 1;
    uint64_t rank = 0;
    for (int j = 0, index = first; j < n; ++j) {
        unsigned bit = 1u << ring[index];
        rank += uint64_t(__builtin_popcount(unused & (bit - 1))) * f[n - j - 1];
        unused ^= bit;
        if (++index == n) index = 0;
    }
    return rank;
}

struct Coverage {
    int n;
    Factorials fact;
    std::array<int, 256> decode{};
    std::array<unsigned, 13> counts{};
    std::array<uint8_t, 13> ring{};
    std::vector<uint64_t> seen;
    int next = 0, filled = 0, distinct_symbols = 0;
    uint64_t length = 0, occurrences = 0, distinct = 0;

    Coverage(int degree, const std::string& alphabet) : n(degree) {
        if (n < 2 || n > 13) throw std::runtime_error("N must be between 2 and 13");
        if (alphabet.size() != size_t(n))
            throw std::runtime_error("ALPHABET must have exactly N bytes");
        decode.fill(-1);
        for (int i = 0; i < n; ++i) {
            unsigned char symbol = static_cast<unsigned char>(alphabet[i]);
            if (symbol < 33 || symbol > 126)
                throw std::runtime_error("ALPHABET must contain printable ASCII without whitespace");
            if (decode[symbol] != -1)
                throw std::runtime_error("ALPHABET symbols must be distinct");
            decode[symbol] = i;
        }
        fact = factorials(n);
        seen.resize((fact[n] + 63) / 64);
    }

    void consume(const char* data, size_t bytes) {
        for (size_t i = 0; i < bytes; ++i) {
            int value = decode[static_cast<unsigned char>(data[i])];
            if (value < 0)
                throw std::runtime_error("Invalid word byte at zero-based position " + std::to_string(length));
            if (length == std::numeric_limits<uint64_t>::max())
                throw std::runtime_error("Word length exceeds the supported counter range");
            ++length;
            if (filled == n) {
                if (--counts[ring[next]] == 0) --distinct_symbols;
            } else {
                ++filled;
            }
            ring[next] = uint8_t(value);
            if (counts[value]++ == 0) ++distinct_symbols;
            if (++next == n) next = 0;
            if (filled != n || distinct_symbols != n) continue;
            ++occurrences;
            uint64_t rank = permutation_rank(ring, next, n, fact);
            uint64_t mask = uint64_t(1) << (rank & 63);
            uint64_t& word = seen[rank >> 6];
            if (!(word & mask)) {
                word |= mask;
                ++distinct;
            }
        }
    }

    bool contains(uint64_t rank) const {
        return (seen.at(rank >> 6) & (uint64_t(1) << (rank & 63))) != 0;
    }
};

static void scan_stream(std::istream& input, Coverage& coverage,
                        size_t chunk_bytes = INPUT_BYTES) {
    if (chunk_bytes == 0) throw std::runtime_error("Input chunk cannot be empty");
    std::vector<char> buffer(chunk_bytes);
    while (true) {
        input.read(buffer.data(), static_cast<std::streamsize>(buffer.size()));
        coverage.consume(buffer.data(), static_cast<size_t>(input.gcount()));
        if (input.bad()) throw std::runtime_error("Input read failed");
        if (input.eof()) break;
        if (input.fail()) throw std::runtime_error("Input read failed before EOF");
    }
    // Never stop early on full coverage: all bytes must be valid and EOF clean.
}

static void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(message);
}

template<class F> static void require_rejection(F test, const char* message) {
    bool rejected = false;
    try { test(); } catch (const std::runtime_error&) { rejected = true; }
    require(rejected, message);
}

static std::pair<std::set<std::string>, uint64_t>
naive_coverage(int n, const std::string& alphabet, const std::string& word) {
    std::set<std::string> seen;
    uint64_t occurrences = 0;
    auto sorted_alphabet = alphabet;
    std::sort(sorted_alphabet.begin(), sorted_alphabet.end());
    for (size_t start = 0; start + n <= word.size(); ++start) {
        auto factor = word.substr(start, n), sorted = factor;
        std::sort(sorted.begin(), sorted.end());
        if (sorted == sorted_alphabet) {
            seen.insert(factor);
            ++occurrences;
        }
    }
    return {seen, occurrences};
}

static void word_control(int n, const std::string& alphabet, const std::string& word) {
    auto expected = naive_coverage(n, alphabet, word);
    for (size_t chunk : {size_t(1), size_t(n - 1), size_t(n), size_t(n + 1), INPUT_BYTES}) {
        Coverage c(n, alphabet);
        std::istringstream input(word);
        scan_stream(input, c, chunk);
        require(c.length == word.size(), "Self-test: length mismatch");
        require(c.distinct == expected.first.size(), "Self-test: distinct coverage mismatch");
        require(c.occurrences == expected.second, "Self-test: occurrence count mismatch");
        // Check every bit independently, using lexicographic permutation order.
        std::vector<int> p(n);
        std::iota(p.begin(), p.end(), 0);
        uint64_t rank = 0;
        do {
            std::string permutation;
            for (int symbol : p) permutation.push_back(alphabet[symbol]);
            require(c.contains(rank++) == (expected.first.count(permutation) != 0),
                    "Self-test: permutation bit mismatch");
        } while (std::next_permutation(p.begin(), p.end()));
    }
}

static uint64_t self_test() {
    for (int n = 2; n <= 9; ++n) {
        auto f = factorials(n);
        std::array<uint8_t, 13> p{};
        for (int i = 0; i < n; ++i) p[i] = uint8_t(i);
        uint64_t expected = 0;
        do {
            require(permutation_rank(p, 0, n, f) == expected++, "Self-test: Lehmer rank mismatch");
            // Every possible ring origin must represent this same permutation.
            for (int first = 1; first < n; ++first) {
                std::array<uint8_t, 13> ring{};
                for (int i = 0; i < n; ++i) ring[(first + i) % n] = p[i];
                require(permutation_rank(ring, first, n, f) == expected - 1,
                        "Self-test: circular Lehmer rank mismatch");
            }
        } while (std::next_permutation(p.begin(), p.begin() + n));
        require(expected == f[n], "Self-test: factorial mismatch");
    }
    uint64_t cases = 0;
    for (int n : {2, 3}) {
        std::string alphabet = std::string("012").substr(0, n);
        uint64_t count = 1;
        for (int length = 0; length <= 8; ++length, count *= n) {
            for (uint64_t code = 0; code < count; ++code) {
                std::string word(length, '0');
                auto rest = code;
                for (char& c : word) { c = alphabet[rest % n]; rest /= n; }
                word_control(n, alphabet, word);
                ++cases;
            }
        }
    }
    word_control(3, "C!A", "C!AC!AAC!C!AC");
    word_control(3, "012", "0120102101201");
    require_rejection([] { Coverage c(1, "0"); }, "Self-test: degree 1 accepted");
    require_rejection([] { Coverage c(14, "0123456789ABCD"); }, "Self-test: degree 14 accepted");
    require_rejection([] { Coverage c(2, "00"); }, "Self-test: repeated alphabet accepted");
    require_rejection([] { Coverage c(2, "0"); }, "Self-test: short alphabet accepted");
    require_rejection([] { Coverage c(2, "0\n"); }, "Self-test: newline alphabet accepted");
    require_rejection([] { Coverage c(2, std::string("0") + char(0xff)); },
                      "Self-test: non-ASCII alphabet accepted");
    for (char invalid : {'\n', '\r', '\0', '2', char(0xff)}) {
        require_rejection([&] {
            Coverage c(2, "01");
            std::istringstream input(std::string("010") + invalid);
            scan_stream(input, c, 1);
        }, "Self-test: invalid trailing byte accepted after full coverage");
    }
    require_rejection([] {
        Coverage c(2, "01");
        c.consume("010", 3);
        std::istringstream input("01");
        input.setstate(std::ios::badbit);
        scan_stream(input, c);
    }, "Self-test: read error accepted after full coverage");
    return cases;
}

int main(int argc, char** argv) {
    try {
        if (argc == 2 && std::string(argv[1]) == "--self-test") {
            auto cases = self_test();
            std::cout << "{\"passed\":true,\"exhaustive_word_controls\":" << cases
                      << ",\"exhaustive_rank_degrees\":[2,3,4,5,6,7,8,9],"
                         "\"chunk_boundaries\":true,\"invalid_input_rejected\":true}\n";
            return 0;
        }
        if (argc < 3 || argc > 4)
            throw std::runtime_error("usage: check_coverage N ALPHABET [FILE or -]; or --self-test");
        std::string degree = argv[1];
        if (degree.empty() || degree.find_first_not_of("0123456789") != std::string::npos)
            throw std::runtime_error("N must be a decimal integer between 2 and 13");
        int n = std::stoi(degree);
        auto start = std::chrono::steady_clock::now();
        Coverage coverage(n, argv[2]);
        std::ifstream file;
        bool use_stdin = argc == 3 || std::string(argv[3]) == "-";
        if (!use_stdin) {
            file.open(argv[3], std::ios::binary);
            if (!file) throw std::runtime_error("Cannot open input file");
        }
#ifdef _WIN32
        if (use_stdin && _setmode(_fileno(stdin), _O_BINARY) == -1)
            throw std::runtime_error("Cannot select binary stdin");
#endif
        scan_stream(use_stdin ? std::cin : file, coverage);
        bool complete = coverage.distinct == coverage.fact[n];
        auto seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
        std::cout << "{\"symbols\":" << n << ",\"length\":" << coverage.length
                  << ",\"valid_occurrences\":" << coverage.occurrences
                  << ",\"distinct_permutations\":" << coverage.distinct
                  << ",\"missing_permutations\":" << coverage.fact[n] - coverage.distinct
                  << ",\"expected_permutations\":" << coverage.fact[n]
                  << ",\"coverage_bytes\":" << coverage.seen.size() * sizeof(uint64_t)
                  << ",\"coverage_complete\":" << (complete ? "true" : "false")
                  << ",\"seconds\":" << seconds << "}\n";
        std::cout.flush();
        if (!std::cout) throw std::runtime_error("Output write failed");
        return complete ? 0 : 1;
    } catch (const std::exception& e) {
        std::cerr << "FAIL: " << e.what() << '\n';
        return 2;
    }
}
