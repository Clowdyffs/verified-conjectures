# Sharp uniform normalized determinants

Write $q$ for a prime power congruent to 1 modulo 4, $n=q+1$, $v=n/2$, and $\Delta_n=2q(q-1)^{v-1}$. In each class consider $|\det M|/\Delta_n$.

| Class | All Theorem 1.6 orders | Attaining order | Orders at least 30 | Attaining order |
|---|---:|---:|---:|---:|
| (4) | 841/1053 | 14 | 16067122183125/19668469112621 | 30 |
| (5) | 4/5 | 6 | 690199704608000/846441320833557 | 38 |
| (6) | 13/16 | 10 | 13602934789834170625/16620815899787526144 | 50 |

**Source and generators.** MSX put the order cutoff in the second sentence of Problem 7.1. The table gives both domains. Theorem 1.6 specifies $q\in\Psi_3$ for all three classes. The smallest $q$ is 5. The group-ring definition in §2.2 expressly permits empty and full leaves. At $q=5$ the formulas (2.2)–(2.4) still produce sign matrices satisfying (1.3). The two Class (4) magnitudes are 128 and 160, and those of Classes (5) and (6) are 128 and 160 respectively. At order 30 the four magnitudes, with Class (4) first in descending order, are 8912683710503976960000, 8625970539669749760000, 8937267024850730352640, and 8691479386489219973120. These reproduce the three rounded MSX controls and the inverse-generator control. [Original manuscript](https://www.sciencedirect.com/science/article/am/pii/S0024379522003123) · [Source matrix definitions](../../lean/Conjectures/NearHadamard/Statement.lean)

Here is the reduction to four choices per field. Both bordered magnitudes depend only on the set of nonzero squares and on the family sign. Changing the generator only reindexes the core Gram block. In Class (4) the subgroup of order $v$ inside the norm-one group stays fixed. Replacing a primitive element $z$ by $z^k$ multiplies the trace multiplier $z^v$ by the base-field scalar $(z^{q+1})^{(k-1)/2}$. Its quadratic character is $(-1)^{(k-1)/2}$. Thus $k\equiv1\pmod4$ preserves the determinant and $k\equiv3\pmod4$ gives the inverse-generator determinant. Both choices occur since inversion exchanges these residue classes. In $\mathbb F_q[X]/(X^2-2)$, take $z=2+X$ at $q=13$ and $z=4+X$ at $q=29$. The minimizing exponents $k$ are respectively 1 and 3 modulo 4 among those coprime to $q^2-1$. Both bordered optima hold for every base-field generator at their attaining order. All fields of the specified cardinality are isomorphic. [Field and generator proofs](../../lean/Conjectures/NearHadamard/Torus.lean) · [Bordered proof](../../lean/Conjectures/NearHadamard/Border.lean)

**Ordinary difference sets.** The introduction emphasizes nonordinary difference sets. If this additional restriction is imposed, the Class (5) example at $q=5$ drops out because its leave is the whole nonidentity part of its group. Its next minimum is $441/544$ at $q=17$ ($n=18$), where the leave has size 4 among 7 nonidentity elements. The other five optima have nonempty proper leaves. This is a supplemental reading of the opening sentence.

**Spectral tail.** The signed Gram halves have the form $2vI+2S$ with $S$ real symmetric, zero on the diagonal and otherwise a sign. Each $S$ is a signed principal submatrix of a conference matrix with square $qI$. Thus, for $x_i=\lambda_i(S)/v$ and $r=1/v$, we have $\sum x_i=0$, $\sum x_i^2=1-r$, and $x_i^2\le(2v-1)/v^2$. The absolute determinant of the source matrix is the geometric mean of the Gram-half determinants. [Projective construction and proof](../momihara-suda-xiang-determinant/PROOF.md)

Put $P=\prod_i(1+x_i)$ and $a=\sqrt{2/v}$. For $v\ge1080$, $a\le431/10000$. The fourth-order minorant obtained from $(x+a)(x-a/2)^2(1-x)\ge0$ in the preceding proof gives
$$
\log P\ge-1/2+r^2/2-a/6.
$$
Also $\Delta_n/n^v=(2-r)(1-r)^{v-1}$. Apply $\log(1-r/2)\le-r/2$ and $\log(1-r)\le-r-r^2/2$ to obtain
$$
\log(c\Delta_n/n^v)\le \log(2c)-1+r^2/2,
\qquad c=81844/100000.
$$
The degree-seven exponential Taylor sum at $4928/10000$ exceeds $2c$, and $4928/10000<1/2-(431/10000)/6$. Consequently all three ratios are at least $c$ for $n\ge2160$. Each of the six displayed candidates is strictly less than $c$. [Spectral inequalities](../../lean/Conjectures/NearHadamardSharp/Spectral.lean) · [Source-matrix tail](../../lean/Conjectures/NearHadamardSharp/Tail.lean)

**Finite comparison.** Trial division of every $q\equiv1\pmod4$ with $5\le q<2159$ gives 175 prime powers. At $q\le149$ compute the four exact determinants. We take integer resultants for cyclic Gram cores and check them by Bareiss elimination on the entire source matrices. All six minima follow from cross-multiplication, and no other field order in this interval attains any of them. At every remaining field size the exact cubic trace $t=\operatorname{tr}(S^3)$ passes
$$
4928/10000-1+r^2/2\le -(1-r)/2+t/(3v^3)-(3/8)(2v-1)(1-r)/v^2.
$$
Indeed $|x_i|\le9/25$ and $\log(1+x_i)\ge x_i-x_i^2/2+x_i^3/3-3x_i^4/8$. Summing and using $\sum x_i^4\le (2v-1)(1-r)/v^2$ proves $P\ge c\Delta_n/n^v$.

For a cyclic sign row $a$ of length $m$, the cubic trace is $m$ times the constant coefficient of $a(X)^3$ modulo $X^m-1$. Adding a zero-diagonal border of uniform sign adds $3m\sum a_i$. The two Gram halves agree up to switching the border sign. The primary computation forms the field-character rows. The second forms the source sign sequences, obtains their Gram rows by Hamming-distance autocorrelation, and counts signed triangles. Comparing traces after sorting the two torus values makes the check independent of field coordinates. [Exact certificate](certificates.tsv) · [Source-sequence replay](replay.py)

The first two tables of computations certify lower bounds. Sorting the exact ratios over all small field sizes and applying the strict gap to $c$ identifies each attaining order uniquely. The exhibited matrix in each case proves optimality.
