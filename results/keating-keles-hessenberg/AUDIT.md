# Statement and verification audit

## Source and formalization

Jonathan P. Keating and Ahmet Abdullah Keleş, *Maximum Absolute Determinants of Upper Hessenberg Bohemian Matrices*, arXiv:2003.00454. The fixed-ratio question appears in the March 1, 2020 v1 on p. 18 and the May 9, 2020 v2 on p. 21, with the same wording. The source matrix appears in (4.2) of v1 and (4.1) of v2. We pin the v2 PDF. The experimental HTML renumbers propositions, so all theorem numbers below refer to the PDF. [v1](https://arxiv.org/pdf/2003.00454v1#page=18) · [v2](https://arxiv.org/pdf/2003.00454v2#page=21)

| Source requirement | [Statement.lean](../../lean/Conjectures/KeatingKeles/Statement.lean) |
|---|---|
| §6, Question 2, all integer orders $n\ge4$ | Lines 31–35, natural index and explicit lower bound |
| Problem 2.4 and Definition 2.10, real $n\times n$ matrix, each upper entry (including the diagonal) in the closed interval $[0,1]$ | Lines 10–13, 34–35 |
| First subdiagonal $s=2$, every lower entry below it zero | Line 13, disjoint index conditions |
| Checkerboard $U_n$ of (3.6) | Lines 15–17 |
| Both entry interchanges and both full permutations defining $U_n^{(rc)}$ in (4.1) | Lines 19–29 |
| Proposition 4.2's definition of a maximizing matrix and §6 Question 2, domination in **absolute** determinant | Lines 33–35 include admissibility of the comparator and domination of every admissible matrix |

The correspondence shifts source indices down by one. The three index regions exhaust all entries. Existence is witnessed by the source matrix in every order. For the possible uniqueness reading, an explicit order-four competitor has signed determinant −12 and differs from the source matrix (signed determinant 12). The theorem `order_four_tie` verifies admissibility, distinctness and the common magnitude. The exact replay checks both signs.

## Literature search, 2026-11-25 UTC

We found no earlier resolution (search dated 2026-11-25). We checked the paper in both versions, searches of its full title and arXiv ID with “citing”, both authors' names and “subdiagonal 2”, “transition forms”, “maximizing matrix”, and indexed GitHub, X and Zenodo results. The local spectral-target screen also searched solved-conjectures and trureturing. Searches for equivalent extremal problems used “generalized Stern sequence”, “row maxima”, “scaled continuants”, “Calkin–Wilf” and “matrix monoid maximal entries”. These searches cannot exclude an unindexed result.

- The source's Theorem 2.6 assumes $s/t\le1$. Theorem 2.8 gives a neighborhood of 1 depending on $n$. Theorem 2.9 assumes $s/t>4n^2/5$. Substitution of 2 yields no all-orders statement. Proposition 4.3 evaluates a particular matrix. [Original paper](https://arxiv.org/pdf/2003.00454v2)
- After dividing the target matrices by two, the normalized upper population lies in $[0,1/2]$. The convex hull of the normalized binary population is $[0,1]$. By multiaffinity its maximum equals the binary maximum, and it gives a larger domain than $[0,1/2]$. The resulting bound is already loose at order four. The hollow class also imposes a diagonal restriction. [Fasi and Negri Porzio](https://eprints.maths.manchester.ac.uk/2768/) · [Du et al.](https://doi.org/10.1515/math-2021-0045)
- Han, Masuda, Singh and Thiel treat maximal entries in two-generator shear monoids in Theorem 1, for positive integer parameters $u,v$. Our maps have $u=v=1/2$. The product $uv$ is invariant under diagonal conjugation, so rescaling the two coordinates cannot put both parameters into the integer range. Their coefficient comparison uses integer arguments at least one. Classical Stern row-maxima theorems correspond to unweighted addition. [Han et al., Integers 20 (2020), A31](https://math.colgate.edu/~integers/u31/u31.pdf) · [Paulin, J. Integer Sequences 20 (2017)](https://cs.uwaterloo.ca/journals/JIS/VOL20/Paulin/paulin2.html)

## Checks and internal review

- The proof treats arbitrary real entries by linear inequalities. No reduction to enumerated corner patterns is assumed. The Python Bareiss implementation checks both small maxima exhaustively and checks the determinant and recurrence over orders 4–64. The finite computation supplies numerical controls for the Lean induction.
- Discovery began with exact Pareto pruning of two integer masses through order 22 and an exact convex-hull check through order 15. The bounds on each coordinate alone lost the needed joint information. Bounds on their weighted and unweighted sums close under both allowed updates.
- During development Lean initially rejected the case split identifying the source's boundary swaps with the sign construction. Splitting the natural row and column indices into their boundary and interior cases resolved that check. The final proof covers the four corner overlaps and the empty middle at order four.
- Fresh-context internal review on 2026-11-25 examined the source, the entry, statement alignment, the mass induction, equality, possible uniqueness and earlier work. It found a source-pointer error: Definition 2.11 concerns trailing minors. The formal statement now cites Definition 2.10 and Problem 2.4. The displayed tie is the authors’ $U_4^{(r)}$, whose determinant magnitude already follows from their (4.2). The reviewer checked the order-four tie and identified the integer-parameter hypothesis of Han et al. above.

The OpenAlex citation graph returned one citing work, Du–da Fonseca–Xu–Ye. The reviewer also checked inverse triangular formulations. The Semantic Scholar graph endpoint returned HTTP 429, so it furnished no additional coverage. [OpenAlex source record](https://openalex.org/W3007849735)

The fresh reviewer separately enumerated all 262,136 endpoint sign patterns across orders 4–18 and recovered $D_{18}=6{,}443{,}920$. Direct Leibniz expansion checked the signed tie. All findings from this internal review are closed.

A fresh clone of proof snapshot `9e7183fe36eab1b393cf449e3049bbbd0e52b93b` rebuilt all seven result modules, ran every replay check, and reported exactly `propext`, `Classical.choice` and `Quot.sound` on all five audited declarations. The toolchain’s `leanchecker` replayed every result module. The clean run used the pinned mathlib dependency cache. An initial attempt to copy the entire 24 GiB Git object store exceeded the temporary-directory quota. The successful clone shared immutable Git objects and had its own clean worktree and empty result build directory.

The local public-format export from a clean clone of solve commit `b537f77f8f0f2ee6e136df771abf3ecaf5341f7b` passed the structural release check with zero problems. Its entry verifier rebuilt and replayed all seven modules in 30.49 seconds, peaking at 3,453,708 KiB child RSS. The bibliography and paper section compiled with pdfLaTeX and BibTeX. The source and method credits, AI disclosure and post lengths were checked against the result.

## Publicity review, 2026-11-25 UTC

A fresh-context internal reviewer compared both source versions, the entry, the formal statement, the determinant identity, the three inductive bounds and the equality case. A separate exact signed Leibniz calculation found three binary maximizers at order four and two at order five. A fresh clone of commit `3f7edc5b29a4c76ea026ce0db74033bc3d3fb2c5` rebuilt and kernel-replayed all seven modules and passed the exact entry verifier. All five axiom checks reported only the permitted three axioms.

We found no earlier resolution (search dated 2026-11-25). The search included Bohemian determinants, triangular inverses, fixed-length shear products, continuants, joint spectral radius, citing papers and indexed public solution catalogues. For example, Han et al.’s integer-shear theorem fails under a formal substitution of one half. At length three a single shear cubed has an entry of 3/2, while every entry of the alternating triple is at most 5/4. Alazemi and Kılıç evaluate two parametric matrix families. Their evaluations give no upper bound over the full family in Question 2. [Han et al.](https://math.colgate.edu/~integers/u31/u31.pdf) · [Alazemi and Kılıç](https://doi.org/10.3934/math.20261267)

The headline now states the upper Hessenberg hypothesis. Keating and Keleş supplied the candidate and its determinant recurrence. The contribution cleared for announcement is the proof that their matrix attains the maximum for every order at this ratio. The order-four tie rules out uniqueness. [Original question](https://arxiv.org/pdf/2003.00454v2#page=21)
