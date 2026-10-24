# The upper-bound paper

[A smaller upper bound for superpermutations](upper/upper-bounds.pdf)
explains the construction, the finite certificate, the transport argument,
and the four explicit words. Its [TeX source](upper/upper-bounds.tex) is
included. The mathematical content is unchanged from the combined release;
this edition updates the paths to the formal statements and supporting proofs.

To rebuild the PDF with an installed Tectonic or pdfLaTeX:

```sh
python3 -B tools/build_papers.py
```

The builder keeps intermediate files in a temporary directory and copies
only the completed PDF into this folder. It does not install a TeX system.
