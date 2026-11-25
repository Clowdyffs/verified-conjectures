# Source and proof audit

## Statement

The 2022 Problem 7.1 and the 2026 Problem 15 interrogative are transcribed in the [statement module](../../lean/Conjectures/NearHadamard/Statement.lean) and in the [entry](README.md). The accepted manuscript supplied for this audit has SHA-256 `8fee32fa73e4dfe0a1b5941128073ad7021c426426b67a8d686f1ca1a54a127a`. The comparison uses Theorem 1.2, Theorem 1.6, equations (2.2)–(2.4), Theorems 3.4 and 4.1 and Problem 7.1. [Manuscript](https://www.sciencedirect.com/science/article/am/pii/S0024379522003123) · [Survey, v2](https://arxiv.org/html/2610.27175v2#S5.SS6)

| Source requirement | Statement.lean | Interpretation |
|---|---|---|
| Type 1 matrix, §2.2 | lines 14–17 | Membership gives +1 and nonmembership gives −1. The group difference is column minus row in exponent coordinates. |
| Class (4), (2.2), Theorem 3.4 | lines 21–28 | With any generator of the field of size q², use its 2(q−1)-th power for the group, its (q+1)/2-th power for the multiplier and the trace u+u^q. Euler's criterion tests a nonzero square in the fixed subfield. |
| Classes (5) and (6), Theorem 4.1 | lines 31–39 | Index squares by powers of w². The shifted coset test uses t−1 for A and t/w−1 for B. The positive exponent excludes zero. |
| (2.3) and (2.4) | lines 42–53 | Option adds the border. The Boolean chooses the printed signs and square class. Signed simultaneous relabellings preserve the absolute determinant. |
| “for every n = q + 1 ≥ 30” | lines 67–71 | Field cardinalities range over all prime powers. Finite fields exist at every prime power and are unique up to isomorphism. The two source index types have size q+1 at these odd q. |
| “q ≡ 1 (mod 4) a prime power” | lines 68–71 | q is a finite field cardinality, q mod 4 = 1, and E has exactly q² elements. Frobenius identifies its unique q-element subfield, so no choice of embedding in the statement is needed. |
| Primitive choices, §§2.3, 3.4 and 4 | lines 68–71 | Both primitive elements are universally and independently quantified. A primitive element always exists in the other field, so the joint quantifier loses no choices. The files in FiniteOrders cover nonprime q as well. |
| “in each family”, four-fifths of Wₙ | lines 72–75 | The conjunction uses all three integer matrices. Four times 2q(q−1)^((q−1)/2) equals 4Wₙ. The absolute value follows Egan's explicit notation and MSX's Theorem 1.6 table. |

The published determinant ratios have three decimal places. The controls module verifies the exact four absolute determinants in the entry, rounds three of them using integer division in `source_decimals`, and supplies `admissible_order30` with the simultaneous field-cardinality and primitive-order hypotheses. The order-30 Class (4) generator is specified by its field polynomial in the controls module. MSX does not identify its generator. [Sanity checks](../../lean/Conjectures/NearHadamard/Controls.lean)

There is a block-order inconsistency in MSX. The size convention in §2.2 lists the larger block first for type NH*₂, whereas Theorem 4.1 and the last paragraph of §4 explicitly apply (2.4) to (D₀,₀,D₀,₁), whose first block is smaller. The formal definition follows that explicit instruction. Interchanging the two blocks leaves the absolute determinant unchanged. Indeed their sign row sums are −2 and 0. The diagonal core of each Gram half is 2J+AAᵀ+BBᵀ. The extra border row meets it in the difference of the two row sums. Interchange reverses this sign, which is conjugation by the diagonal matrix negating the border coordinate. Off-block products vanish by commutativity of the circulants and the sum of the row sums being −2. Thus both orderings yield the same determinant magnitude.

## Literature and specialization

| UTC date | Search or source | Finding |
|---|---|---|
| 2026-11-24 | Original article and supplied manuscript, both Egan survey versions, OpenAlex works citing W4293571645. Queries included “Problem 7.1”, “near-Hadamard”, “Problem 15”, “0.8”, “Jacobi sums”, “almost supplementary difference sets”, “sharp lower bounds”, “erratum”, “proof” and “counterexample”. | The survey calls the exact question open. The citing-work response returned that survey and the Li–Momihara–Xiang type I paper. [Citation index](https://api.openalex.org/works?filter=cites:W4293571645) · [v1](https://arxiv.org/html/2610.27175v1#S5.SS6) · [v2 and revisions](https://arxiv.org/abs/2610.27175) |
| 2026-11-25 | Rechecked both survey versions, the 2022 publisher record, revisions/corrections, later papers of the posers, and the exact title, authors, two problem numbers and “lower bounds on determinants”. Searched indexed GitHub, X, MathOverflow and personal sites using the names and near-Hadamard terms. Inspected solved-conjectures and OpenAI's math collection. | Located constructions, maximal-determinant results and unrelated Hadamard existence questions. We found no earlier resolution (search dated 2026-11-25). Social and citation indices can omit work. [Collection](https://github.com/1337isnot1337/solved-conjectures) · [OpenAI collection](https://github.com/openai/math/blob/main/overview.tex) · [Poser's publication record](https://www.sciencedirect.com/author/22934594600/koji-momihara) |

**Tests of general theorems.** MSX Proposition 2.1, itself a specialization of a determinant bound from two trace moments, guarantees only $2(32)^{14}/W_{30}<1/4$ at the first eligible order. Brent and Osborn give a lower bound on the *maximum* of the determinants at each order, whereas the present quantifier is over specific matrices. Lin–Phoa's type I formula gives $2(n-2)^{n/2}$, or $28/29$ of $W_{30}$, different from each of these three families at order 30. Li–Momihara–Xiang's subsequent constructions also require type I. Their determinant formula cannot specialize to all of the present matrices. [MSX](https://doi.org/10.1016/j.laa.2022.08.028) · [Brent–Osborn](https://arxiv.org/abs/1208.1805) · [Lin–Phoa, Definition 4 and Lemma 2](https://doi.org/10.5705/ss.202014.0115) · [Li–Momihara–Xiang](https://doi.org/10.1016/j.laa.2026.08.013)

**A positive specialization on the tail.** Liao–Berg, Theorem 1 applied to $-\log$, gives $\sum_i\log(1+x_i)\ge-(1-1/v)h(a)$ for $|x_i|\le a$, where $h(a)=(-\log(1-a)-a)/a^2$. Our field-specific spectral cap gives $a\le1/15$ at $v\ge450$. Thus $h(a)\le1/2+a/[3(1-a)]\le11/21$ and this published inequality suffices for that tail. At $n=30$ its lower estimate using $a=\sqrt{29}/15$ is about $0.7304W_{30}$. MSX report order checks through 1000, but give only one unspecified Class (4) generator value at 30. Together these observations give a shorter tail argument and explain the need to check generator coverage for the universal question. [Liao–Berg, Theorem 1 and Example 2](https://doi.org/10.1080/00031305.2017.1419145)

## Fresh-context internal review, 2026-11-25 UTC

A fresh Codex GPT-6.2 Astra agent received only the MSX manuscript, the version-2 survey and this entry, including its linked Lean statement. It checked the source match, derivation and prior literature. It independently implemented direct signed Bareiss elimination at order 30. It did not run the project build.

| Finding | Resolution |
|---|---|
| MSX write a signed determinant in the brief question. A literal reading can fail. | Added the convention to the landing page and the statement. In displayed order the four signed determinants have signs −, −, −, + and exactly the magnitudes printed by the entry. Indeed (2.2) has sign $(-1)^v$ when nonsingular. The absolute-value header of MSX Theorem 1.6 and Egan Problem 15 resolve the intended reading. |
| The sharp-bound request is broader. | The statement, result and announcement identify the four-fifths subquestion. The optimal constants remain outside this result. |
| A general Jensen-gap bound proves the tail after inserting the spectral cap. Existing type I and maximal-determinant formulas merit explicit specialization. | The computations and citations above record exactly which conclusions follow. |
| Draft-stage replay script and announcement, paper and reference templates were incomplete at the time of inspection. | Replaced the template files, wrote the full exact replay, and tested the result package on a clean checkout. |

The direct signed determinants checked by the reviewer are also checked in the independent replay at order 30.

The reviewer found no gap in the mathematical argument and no previous resolution of the all-generators question. The supplementary determinant computation by the reviewer is an internal cross-check.

## Arithmetic and reproducibility

The reference table was computed with python-flint 0.9.0 using polynomial resultants, full integer determinants and integer matrix multiplication for cubic traces. The separate replay uses only Python's standard library. It constructs polynomial quotient fields by proving irreducibility through trial division, builds each entire source sign matrix, takes its determinant by fraction-free Bareiss elimination, and counts signed triangles in its actual Gram block. It compares all 56 pairs against the table and substitutes every trace into the rational inequality. Finally it constructs 14 Lean goals identifying the independently computed integers with the formal field models' traces, up to exchange of the two Class (4) generators. Lean checks each equality by kernel reduction. [Reference values](certificates.tsv) · [Second implementation](replay.py) · [Reproduction script](verify.sh)

The original exploratory package and this package use the same pinned dependencies. An initial shared-package build caught a type mismatch in the new nonvacuity lemma after simplification. Replacing the two reflexivity tactics by decisions on the simplified propositions fixed it. The four original determinant proofs were unchanged.

The LaTeX section was typeset with pdfLaTeX, BibTeX and two final pdfLaTeX passes. The citations resolved. The two draft posts use 153 and 256 weighted characters when the prospective entry URL counts as 23.

## Verification record for 2026-11-25 UTC

All six repository solve conditions hold for the four-fifths question. A fresh local Git clone began with no result build products. It reused the pinned dependency checkouts and their mathlib artifacts. The separate source-matrix replay matched 56 pairs. The shared target completed 3,382 Lake jobs including imported jobs. A separate Lean invocation checked every cross-language cubic trace and the axiom set of all seven declarations. The toolchain's bundled `leanchecker` replayed all 29 modules, including the statement, the controls and the final theorem. A separate executable named `lean4checker` was absent. The measured clean replay took 408.17 seconds and the largest child used 22,585,320 KiB RSS. Kernel replay and axiom checking use the pinned Lean toolchain. This result has had internal review only.

**Solve-commit replay.** A second fresh clone at `df7104831195e4d404090392b0dc596c41e17c10` began without `lean/.lake`. The script verified each dependency Git revision against the committed Lake manifest. It matched all 56 determinant/trace pairs, rebuilt the theorem, checked the 14 trace equalities and seven axiom reports, replayed all 29 compiled modules, printed the two headline lines and exited 0. Git reported a clean working tree afterwards. This replay of the committed files took 381.20 seconds, with a maximum child RSS of 22,585,688 KiB.
