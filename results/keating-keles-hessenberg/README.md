# The proposed Hessenberg matrix attains the maximum at subdiagonal two

**Solved 2026-11-25 UTC, commit `b537f77f8f0f2ee6e136df771abf3ecaf5341f7b`.** Unrefereed, internal review only.

For every $n\ge4$, the matrix $U_n^{(rc)}$ proposed by Jonathan P. Keating and Ahmet Abdullah Keleş maximizes the absolute determinant among all real upper Hessenberg matrices with twos on the first subdiagonal and every upper-triangular entry in $[0,1]$. The exact maximum satisfies
$$
D_4=12,\qquad D_5=32,\qquad D_n=D_{n-1}+4D_{n-2}\quad(n\ge6).
$$
Keating and Keleş computed the determinant of their matrix in Proposition 4.3. We prove that it bounds every admissible determinant in absolute value. The argument tracks the positive and negative parts of the coefficients in a row operation. The authors’ distinct matrix $U_4^{(r)}$ also attains the maximum at order four. [Proof](PROOF.md) · [Formal statement](../../lean/Conjectures/KeatingKeles/Statement.lean) · [Final theorems](../../lean/Conjectures/KeatingKeles.lean)

<!-- glance:start -->
## At a glance

| | |
| :--- | :--- |
| **Answer** | **True** (proof) |
| **Source** | J. P. Keating and A. A. Keleş, Maximum Absolute Determinants of Upper Hessenberg Bohemian Matrices, [arXiv:2003.00454v2](https://arxiv.org/abs/2003.00454v2) (2020), p. 21, [doi:10.48550/arXiv.2003.00454](https://doi.org/10.48550/arXiv.2003.00454) |
| **Posed** | 2020 |
| **Verification** | `lean-complete`: the Lean kernel checks the exact statement |
| **Lean theorem** | [`KeatingKeles.question_two`](../../lean/Conjectures/KeatingKeles.lean#L33) |
| **Formal statement** | [`Statement.lean`](../../lean/Conjectures/KeatingKeles/Statement.lean) |
| **Toolchain** | Lean v4.35.0, mathlib [`56a005855e`](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679) |
| **Replay** | [`verify.sh`](verify.sh), run as `results/keating-keles-hessenberg/verify.sh` |
| **Solved** | 2026-11-25 (UTC), development commit `b537f77f8f0f` |
| **Lean source hash** | `9d175d1287af1e0e1a53e573de6437db547132f2`, the git tree of `lean/Conjectures/KeatingKeles` at the solve commit |
| **Literature check** | 2026-11-25, see [AUDIT.md](AUDIT.md) |
| **Status** | `ready`, unrefereed, internal review only |
<!-- glance:end -->

## Original question

The authors specify “the case $s=2$ and $t=1$” and ask:

> Is $U_n^{(rc)}$ the maximizing matrix in this case when $n\ge4$?

Question 2 appears in the concluding remarks of both the March 1 and May 9, 2020 preprints. The source's objective is the absolute determinant. Its maximizing-matrix definition permits ties. The theorem covers all entries in the closed real interval, including the binary corners. The [companion result on Question 1](../keating-keles-transitions/README.md) gives the sharp maximum and every maximizing matrix as the positive ratio varies. [Original, v2, p. 21](https://arxiv.org/pdf/2003.00454v2#page=21) · [Definition of a maximizing matrix, p. 8](https://arxiv.org/pdf/2003.00454v2#page=8)

## Verify

From the repository root run:

```sh
./results/keating-keles-hessenberg/verify.sh
```

The replay prints `D_4 = 12` and `D_5 = 32`. Python exhausts the 1,024 and 32,768 binary corners in these two orders and checks the source comparator by independent exact elimination through order 64. Lean checks the all-orders theorem, recurrence, initial values and existence of the order-four tie. The build is `lake build Conjectures.KeatingKeles` from the pinned [Lean package](../../lean/lean-toolchain). Verification uses Python 3, Elan and the dependencies pinned by [the manifest](../../lean/lake-manifest.json). A fresh checkout can use the standard mathlib cache or the local dependency cache specified by `KEATING_KELES_DEPS`.

The clean proof-snapshot replay took 30.46 seconds with the pinned dependency cache and peaked at 3.30 GiB child RSS. All seven result modules were rebuilt. A clean export of the solve commit passed the structural release check and the full result replay in 30.49 seconds.

## Trust base

The Lean toolchain is 4.35.0 and mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`. The final theorem has no hypotheses beyond those in the source question. Its axiom audit permits only `propext`, `Classical.choice` and `Quot.sound`. The replay also runs the toolchain's `leanchecker`. The finite Python computation is a separate check of the numerical claims.

## Prior work and credits

The original paper supplies the comparator, its determinant recurrence and sharp results in other parameter ranges. We found no earlier resolution (search dated 2026-11-25). The search included related extremal results for products of two shear matrices. [Source](https://arxiv.org/abs/2003.00454) · [Hypothesis map, literature and internal review](AUDIT.md)

OpenAI Codex (GPT-6.2 Astra) assisted with the derivation, formalization, exact replay, drafting and internal review.
