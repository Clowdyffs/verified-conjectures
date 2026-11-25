# Sharp normalized determinants

For $q\equiv1\pmod4$ a prime power, put $n=q+1$ and $\Delta_n=(2n-2)(n-2)^{(n-2)/2}$. These are the best uniform lower bounds for $|\det M|/\Delta_n$.

| MSX class | All orders | Attained at | Orders $n\ge30$ | Attained at |
|---|---:|---:|---:|---:|
| (4) | 841/1053 | 14 | 16067122183125/19668469112621 | 30 |
| (5) | 4/5 | 6 | 690199704608000/846441320833557 | 38 |
| (6) | 13/16 | 10 | 13602934789834170625/16620815899787526144 | 50 |

Solved 2026-11-25 UTC. Each attaining order is unique on its stated domain. All primitive generators are covered. In the model $X^2=2$, the Class (4) minimizing primitive elements are $(2+X)^k$ at $q=13$ for $k\equiv1\pmod4$, and $(4+X)^k$ at $q=29$ for $k\equiv3\pmod4$, in both cases with $\gcd(k,q^2-1)=1$. Every primitive generator attains the value at the indicated bordered orders. If ordinary difference sets are excluded, the all-orders Class (5) minimum is 441/544 at order 18. [Proof](PROOF.md)

<!-- glance:start -->
## At a glance

| | |
| :--- | :--- |
| **Answer** | **True** (proof) |
| **Source** | Linear Algebra and its Applications 654 (2022), 28–55, [doi:10.1016/j.laa.2022.08.028](https://doi.org/10.1016/j.laa.2022.08.028) |
| **Posed** | 2022 |
| **Verification** | `lean-complete`: the Lean kernel checks the exact statement |
| **Lean theorem** | [`NearHadamard.Optimal.sharpLowerBounds`](../../lean/Conjectures/NearHadamardSharp/Proof.lean#L366) |
| **Formal statement** | [`Statement.lean`](../../lean/Conjectures/NearHadamardSharp/Statement.lean) |
| **Toolchain** | Lean v4.35.0, mathlib [`56a005855e`](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679) |
| **Replay** | [`verify.sh`](verify.sh), run as `results/momihara-suda-xiang-sharp-bounds/verify.sh` |
| **Solved** | 2026-11-25 (UTC), development commit `7496df6f445f` |
| **Lean source hash** | `2f81050330c94a6e902f3a9b114df7662fc71d19`, the git tree of `lean/Conjectures/NearHadamardSharp` at the solve commit |
| **Literature check** | 2026-11-25, see [AUDIT.md](AUDIT.md) |
| **Status** | `ready`, unrefereed, internal review only |
<!-- glance:end -->

## Original question

The [formal statement](../../lean/Conjectures/NearHadamardSharp/Statement.lean) uses the original sign matrices and quantifies over all primitive choices. [Original manuscript](https://www.sciencedirect.com/science/article/am/pii/S0024379522003123)

> Give sharp lower bounds on the determinants of near-Hadamard matrices in Classes (4), (5) and (6) of Theorem 1.6. In particular, prove or disprove that for each $i=4,5,6$, $\det M_n^{(i)}/\Delta_n\ge0.8$ for every $n=q+1\ge30$ with $q\equiv1\pmod4$ a prime power.

## Reproduction

Run the following from the repository root with Python 3.10 or later and the pinned Lean toolchain. Install python-flint 0.9.0 for `python3`, or set `SHARP_FLINT_PYTHON` to a Python executable with that package installed. Optional `NEAR_HADAMARD_DEPS` identifies an existing Lake packages directory when running offline.

```sh
results/momihara-suda-xiang-sharp-bounds/verify.sh
```

The cold verification reached 8.2 GiB peak process memory and took 52 minutes including lock waits. The reference uses finite-field character rows and integer resultants. The second implementation starts from the two source sign sequences and checks 700 signed cubic traces and 88 full determinants. A spectral estimate handles every order from 2160. The verification script checks the mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, the six-minimum theorem, the supplemental Class (5) minimum and the kernel axiom report. [Source and verification audit](AUDIT.md)

## Prior work and credit

We found no earlier resolution (search dated 2026-11-25). Unrefereed, internal review only. Momihara, Suda and Xiang constructed the three near-Hadamard families, expressed their determinants through character sums and reported numerical checks through order 1000. They credit Lin and Phoa for the near-Hadamard design concept and trace the Class (4) difference sets to Williamson-type constructions of Turyn and Whiteman. [MSX, introduction and §3.4](https://doi.org/10.1016/j.laa.2022.08.028)

Egan, Kotsireas, London and Ó Catháin restated the four-fifths question. Our earlier public entry proves that threshold. Here we determine the best constant for each family and exhibit a matrix attaining each bound. The proof uses the earlier entry’s Paley conference-matrix and logarithmic estimates. [Survey, Problem 15](https://arxiv.org/html/2610.27175v2#S5.SS6) · [Four-fifths entry](../momihara-suda-xiang-determinant/README.md)

OpenAI Codex, GPT-6.2 Astra, assisted with the argument, computation, formalization and exposition.
