# The four-fifths bound for near-Hadamard matrices

**Solved 2026-11-25 (UTC), commit `df7104831195e4d404090392b0dc596c41e17c10`.** Unrefereed, internal review only.

For every prime power $q\equiv1\pmod4$ with $n=q+1\ge30$, all three constructions satisfy
$$
5|\det M|\ge4(2n-2)(n-2)^{(n-2)/2}.
$$
This includes both determinant choices that changing the primitive element can produce in Class (4). The proof embeds the signed Gram blocks into finite-field conference matrices. A spectral bound covers every $n\ge126$, and exact calculations cover the 14 remaining field sizes. [Proof](PROOF.md) · [Statement](../../lean/Conjectures/NearHadamard/Statement.lean) · [Formal theorem](../../lean/Conjectures/NearHadamard/Proof.lean)

<!-- glance:start -->
## At a glance

| | |
| :--- | :--- |
| **Answer** | **True** (proof) |
| **Source** | Linear Algebra and its Applications 654 (2022), 28–55, Theorem 1.6 and §7, [doi:10.1016/j.laa.2022.08.028](https://doi.org/10.1016/j.laa.2022.08.028). Restated in [arXiv:2610.27175v2](https://arxiv.org/abs/2610.27175v2), §5.6. |
| **Posed** | 2022 |
| **Verification** | `lean-complete`: the Lean kernel checks the exact statement |
| **Lean theorem** | [`NearHadamard.problem15`](../../lean/Conjectures/NearHadamard/Proof.lean#L100) |
| **Formal statement** | [`Statement.lean`](../../lean/Conjectures/NearHadamard/Statement.lean) |
| **Toolchain** | Lean v4.35.0, mathlib [`56a005855e`](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679) |
| **Replay** | [`verify.sh`](verify.sh), run as `results/momihara-suda-xiang-determinant/verify.sh` |
| **Solved** | 2026-11-25 (UTC), development commit `df7104831195` |
| **Lean source hash** | `32381d511d037cc59b3b8b1fda5c618df618e7b2`, the git tree of `lean/Conjectures/NearHadamard` at the solve commit |
| **Literature check** | 2026-11-25, see [AUDIT.md](AUDIT.md) |
| **Status** | `verified`, unrefereed, internal review only |
<!-- glance:end -->

## Original question

> Give sharp lower bounds on the determinants of near-Hadamard matrices in Classes (4), (5) and (6) of Theorem 1.6. In particular, prove or disprove that for each $i=4,5,6$, $\det M_n^{(i)}/\Delta_n\ge0.8$ for every $n=q+1\ge30$ with $q\equiv1\pmod4$ a prime power.

Momihara, Suda and Xiang, Problem 7.1, accepted manuscript p. 20 (mathematical typography normalized). Their Theorem 1.6 tabulates absolute determinants. The sign depends on the representative. In the displayed Class (4) construction it is negative at order 30. Egan et al. explicitly ask “Is $|\det M_n|\ge0.8\,W_n$ for every such $n\ge30$ in each family?” Here “such” refers to those three constructions. The theorem resolves that entire yes/no question. Finding the best constant for each family is a separate part of the 2022 problem. [2022 original](https://doi.org/10.1016/j.laa.2022.08.028) · [2026 survey, version 2, §5.6](https://arxiv.org/html/2610.27175v2#S5.SS6)

## Verify

From the repository root, run the following on a machine with Python 3 and the pinned Lean toolchain available through Elan. Python 3.10 or newer is required. The first run needs the pinned mathlib checkout and its dependencies. The script obtains the standard mathlib build cache on an unseeded checkout.

```sh
results/momihara-suda-xiang-determinant/verify.sh
```

The solve commit replayed from a clean clone with a prewarmed pinned dependency cache in 381 seconds including `leanchecker`. The largest child process reached 21.54 GiB RSS. Set `NEAR_HADAMARD_DEPS` to an existing Lake packages directory to reuse dependencies offline. The result modules themselves are rebuilt in the clean clone.

The exact order-30 absolute determinants, in the order Class (4) matching the published decimal, its inverse generator, Class (5), Class (6), are

```text
8912683710503976960000
8625970539669749760000
8937267024850730352640
8691479386489219973120
```

## Trust base

The pinned mathlib revision is `56a005855ea17e0b0958f73ec801ae140b0a1679`. The final declaration has type `NearHadamard.Source.Problem15`. Its kernel axiom set is `propext`, `Classical.choice` and `Quot.sound`. The finite cases use kernel reduction. The separate integer-arithmetic replay supplies a cross-check. [Source-to-statement audit and literature search](AUDIT.md)

## Prior work and credits

Momihara, Suda and Xiang supplied the finite-field constructions and the order-30 numerical controls. The large-order argument uses Paley's conference matrix and moments of its principal submatrices. Egan, Kotsireas, London and Ó Catháin restated the determinant question. We found no earlier resolution (search dated 2026-11-25). The account and formalization were developed with OpenAI Codex, GPT-6.2 Astra. Unrefereed, internal review only.
