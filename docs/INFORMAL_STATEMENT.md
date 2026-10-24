# Informal statement of the submitted result

**AI disclosure.** The research reported here, its Lean formalization, and this
document were generated entirely by AI under Jay Pantone's direction. The
construction builds on earlier mathematical and formalization work credited
below and in the accompanying paper. Those inherited contributions are not
claimed as work of this project. Independent AI review is not human peer review.

A *superpermutation* on an alphabet of $n$ symbols is a word containing every
permutation of those symbols as a contiguous substring. For example,
`123121321` contains all six permutations of `123`. Let $S(n)$ be the shortest
possible length of such a word, and write

$$
F_3(n)=n!+(n-1)!+(n-2)!.
$$

This submission gives an explicit upper bound for every $n\ge14$, together
with its asymptotic consequence. Put

$$
\lambda=\frac{926683}{1814400},\qquad
\gamma=\frac{30571}{1814400}.
$$

The coefficient $\lambda$ is approximately $0.510738$, improving the
coefficient $43/80$ in [Pantone's earlier construction](https://github.com/jaypantone/superperm-upper-43-80).

**Finite bound.** For every integer $n\ge14$ and every integer
$0\le\ell\le n-4$, set $c=\gamma(n-4)!$. There is a superpermutation on
$n$ symbols of length at most

$$
F_3(n)+\lambda(n-3)!+(n-4-\ell)c
  +\ell\min\left(c,\frac{(n-1)!}{(n-1-\ell)!}\right).
$$

The parameter $\ell$ specifies how many letters to overlap when joining the
final pieces. It can be chosen separately for each $n$ to give the smallest
bound. The Lean declaration `SuperpermutationUpper.finite_bound` uses
$m=n-2$ and $a=n-2-\ell$. Its assumptions $m\ge12$ and $2\le a\le m$
are exactly the conditions above.

**Asymptotic bound.** For every positive rational $\varepsilon$, there is
an integer $N\ge14$ such that, for every integer $n\ge N$, there is a
superpermutation on $n$ symbols of length at most

$$
F_3(n)+(\lambda+\varepsilon)(n-3)!.
$$

This is the declaration `SuperpermutationUpper.asymptotic_bound`. The
statement also holds for every positive real $\varepsilon$, by choosing a
smaller positive rational number. It applies to every sufficiently large
alphabet size. Both declarations assert the existence of actual words;
the finite certificates used to construct them are proved within the
development.

The proof begins by grouping permutations into pieces with large overlaps.
Rotating a permutation by one place costs only one new letter, so cyclic
classes are a natural starting point. Longer pieces combine these classes,
and matching ends arrange the pieces into closed trails. Shortening some
pieces improves the way their ends fit together, at the cost of leaving
some classes uncovered. A completion operation restores all the missing
classes. After the first three factorial terms, the two principal costs
are this repair and the connectors used to join trails.

The finite improvement uses [Halfar's selections and block replacement
method](https://github.com/jhalfar/superpermutations/tree/cc5c763bd5854317b20dadb138990802656e6f03),
followed by an improved choice of connectors. A connector can meet several
trails and join them all. The certificate checks that every required trail
is met at an actual endpoint. At the fourteen-symbol base, the repair cost
is $19{,}714{,}464$ and there are $61{,}142$ connectors; their normalized
contributions add to $\lambda$.

Pantone's transport operation carries this finite construction to every
larger alphabet while preserving its coverage and connector incidences.
Opening the resulting closed pieces and joining them with overlaps of
$\ell$ letters gives the finite formula. For the asymptotic bound, take
$a=\lceil\sqrt{n-2}\rceil$ and $\ell=n-2-a$. Both remaining joining terms,
divided by $(n-3)!$, tend to zero. The [accompanying paper](../papers/upper/upper-bounds.pdf)
gives the construction and cost calculation in detail.

The two declarations above are the claims selected for Palomar. The seven
numerical consequences `word_14` through `word_20` remain in the repository.
[Challenge.lean](../Challenge.lean) states the claims independently, and
[Solution.lean](../Solution.lean) supplies their proofs. The upper development
uses ordinary Lean proofs, without `native_decide`, and depends only on
`propext`, `Classical.choice`, and `Quot.sound`.

The coefficient improves both the earlier $43/80$ construction and Halfar's
announced coefficient $1771/3456$. The reductions are $48557/1814400$ and
$773/453600$, respectively.
