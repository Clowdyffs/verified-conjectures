# The four-fifths bound for three near-Hadamard families

**Yes.** For each prime power $q\equiv1\pmod4$ with $n=q+1\ge30$, every matrix in Classes (4), (5) and (6) of Momihara–Suda–Xiang (MSX) satisfies
$$
5|\det M|\ \ge\ 4(2n-2)(n-2)^{(n-2)/2}.
$$
Lean verifies the universal statement. A spectral estimate covers every eligible $n\ge126$, and kernel-checked integer certificates cover the remaining 14 prime powers. MSX posed this inequality in 2022 as the particular question in Problem 7.1. Egan, Kotsireas, London and Ó Catháin restated it in 2026 as Problem 15. [MSX, Theorem 1.6 and §7](https://doi.org/10.1016/j.laa.2022.08.028) · [Egan et al., §5.6](https://arxiv.org/html/2610.27175v2#S5.SS6)

## Which matrices are covered?

Write $v=(q+1)/2$, $m=v-1$, and let $\eta$ be the quadratic character on $F=\mathbb F_q$, extended by zero at zero. The type-one matrix of a subset $D$ of a multiplicative group has entry $+1$ at $(x,y)$ when $y/x\in D$, and $-1$ otherwise.

**Class (4).** Choose a primitive $w\in E=\mathbb F_{q^2}$, put $\alpha=w^v$, and let $G=\langle w^{2(q-1)}\rangle$, of order $v$. For $i=0,1$ let $D_i$ comprise those $t\in G$ for which $\operatorname{Tr}_{E/F}(\alpha^i t)$ is a nonzero square of $F$. Use the type-one matrices $A,B$ of $D_0,D_1$, respectively, in
$$
 M=\begin{pmatrix}A&B\\B^T&-A^T\end{pmatrix}.
$$
The leave is $D_1$. Every element of $G$ has norm one, $\alpha^q=-\alpha$, and $v$ is odd. In particular $\operatorname{Tr}(\alpha t)=\alpha(t-t^{-1})$ vanishes in $G$ exactly at $t=1$. [MSX, Proposition 2.5 and Theorem 3.4](https://www.sciencedirect.com/science/article/am/pii/S0024379522003123)

**Classes (5) and (6).** In $F^\times$ choose a primitive $w$, put $H=(F^\times)^2$, $C_0=H$, $C_1=wH$, and form $D_{ij}=H\cap w^j(1+C_i)$. In Class (5) take $i=1,c=1$ and in Class (6) take $i=0,c=-1$. Let $A,B$ be the type-one matrices of $D_{i0},D_{i1}$. The block sizes are $1,m,1,m$, with constant entries expanded over the appropriate row or column. The matrix is
$$
 M=\begin{pmatrix}
 1&\mathbf1^T&c&c\mathbf1^T\\
 \mathbf1&A&\mathbf1&B\\
 1&\mathbf1^T&-c&-c\mathbf1^T\\
 c\mathbf1&cB^T&-c\mathbf1&-cA^T
 \end{pmatrix}.
$$
The leave is $D_{i0}$. Its size is $m/2$ in Class (5) and $m/2-1$ in Class (6). [MSX, (2.3), (2.4) and Theorem 4.1](https://www.sciencedirect.com/science/article/am/pii/S0024379522003123)

## The Gram spectrum

In each class $MM^T=\operatorname{diag}(B_0,B_0)$, where $B_0=nI+2S$ has order $v$. The matrix $S$ is real symmetric, with zero diagonal and all other entries in $\{-1,1\}$. For Class (4) this follows from $B_0=(n-2)I+2J-4A_L$, where $A_L(x,y)=[y/x\in L]$. For the bordered classes the core of $B_0$ is $(n-2)I+2J-4A_L$, and its extra row and column meet the core in entries $2c$. This follows by multiplying the displayed border with the type-one row sums $(0,0)$ and $(-2,0)$, respectively, and applying (4.2). The two Gram blocks agree because the core matrices are circulant. Thus $|\det M|=\det B_0$. [MSX, proofs of Propositions 2.5, 2.6 and 2.8 and equation (4.2)](https://www.sciencedirect.com/science/article/am/pii/S0024379522003123)

We show that every eigenvalue $s$ of $S$ satisfies $s^2\le q$. For a direct finite-field proof, take the $q+1$ lines of $F^2$. Choose a representative $u_i\ne0$ for each line and a nondegenerate alternating form $f$. Set $P_{ij}=\eta(f(u_i,u_j))$. Then $P^TP=qI$. Each column has exactly one zero. For distinct columns $i,j$, multiplying a line representative by any nonzero scalar leaves the product of the two entries invariant. Hence $q-1$ times the column inner product equals
$$
\sum_{u\in F^2}\eta(f(u,u_i))\eta(f(u,u_j))
 = \sum_{a,b\in F}\eta(a)\eta(b)=0.
$$
The middle equality holds because the two independent column vectors give independent linear forms. Also $P=P^T$ since $\eta(-1)=1$. Every principal submatrix of $P$, and its negative, has operator norm at most $\sqrt q$, by extending a vector by zeros and restricting its image.

- In Class (4) view $E$ as a two-dimensional space over $F$. Use $f(x,y)=\alpha(x^qy-y^qx)$. This alternating form takes values in $F$, and its kernel at a nonzero $x$ is the line $Fx$. The elements $x\in G$ represent distinct lines because $G\cap F^\times=\{1\}$. Indeed a scalar of norm one is $\pm1$ and $G$ has odd order. On these representatives $f(x,y)=\operatorname{Tr}(\alpha y/x)$. Hence $S=-P|_G$ by the formula for the leave, including the zero diagonal.
- In Class (5) take representatives $(1,x)$ for $x\in H$ and $(0,1)$ for the extra border. The ordinary determinant form gives core entries $\eta(y-x)$ and border entries $1$. For distinct squares $x,y$ we have $\eta(y/x-1)=\eta(y-x)$. Thus $S$ is exactly this principal submatrix. For Class (6) both the core and the border signs reverse, giving its negative.

The same spectral cap follows from the individual Gauss- and Jacobi-sum factors in Theorem 1.6 if the two exceptional bordered modes are included. The projective argument handles those modes automatically.

## A lower bound for the product

Define $x_i=s_i/v$ for the $v$ eigenvalues of $S$. From the diagonal and the squared entries,
$$
 \sum_i x_i=0,\qquad \sum_i x_i^2=(v-1)/v,\qquad
 |x_i|\le \sqrt{2v-1}/v.
$$
Consequently $\det B_0=n^v\prod_i(1+x_i)$. For $v\ge450$ the last bound is at most $1/15$. The power series for the logarithm gives, for $|x|\le1/15$,
$$
 \log(1+x)\ge x-\tfrac12x^2 + \tfrac13x^3
                   -\frac{|x|^4}{1-|x|}
             \ge x-\tfrac{527}{1000}x^2 .
$$
Indeed $1/2+1/45+1/210<527/1000$. Summing gives $\det B_0\ge n^v e^{-527/1000}$.

Write $W_n=(2n-2)(n-2)^{v-1}$. Then
$$
 W_n/n^v=(2-1/v)(1-1/v)^{v-1}\le 2e^{-1+1/v}.
$$
For $v\ge450$ we have $\log(8/5)<0.4701<1-527/1000-1/450$. These estimates give $5\det B_0>4W_n$. They also explain the observed limit. Along the admissible orders, the cubic and higher terms have total absolute value $O(v^{-1/2})$, since the sum of squares stays bounded. Therefore $\log(\det B_0/n^v)\to-1/2$ and $\det B_0/W_n\to\sqrt e/2$.

## The estimate used in Lean

A fourth-order estimate reduces the formal finite check from 82 field sizes to 14. Write $r=1/v$ and $a=\sqrt{2/v}$. For $v\ge63$, $|x_i|\le a\le179/1000$. The logarithmic series gives
$$
\log(1+x)\ge x-x^2/2+x^3/3-x^4/3.
$$
Indeed, for $|x|\le9/50$ the fifth term has magnitude at most $(9/250)x^4$, and the terms from degree six onward have total magnitude at most $x^4/25$. Together with $x^4/4$ these cost less than $x^4/3$.

The polynomial $(x+a)(x-a/2)^2(1-x)$ is nonnegative throughout $[-a,a]$. Expanding it gives a quadratic lower bound for the combined cubic and quartic terms. Summing and using the exact first two moments yields
$$
\sum_i\log(1+x_i)\ge
-\left(\tfrac12+\tfrac{a^2}{4}\right)(1-r)-\tfrac{v a^3}{12}
=-\tfrac12+\tfrac{r^2}{2}-\tfrac a6.
$$
On the other hand $\log(1-r/2)\le-r/2$ and $\log(1-r)\le-r-r^2/2$ give
$$
\log\bigl((4/5)W_n/n^v\bigr)\le\log(8/5)-1+\tfrac{r^2}{2}.
$$
Since $\log(8/5)<0.4701<1/2-(179/1000)/6$, the required inequality holds at every eligible $n\ge126$. The remaining prime powers are $29,37,41,49,53,61,73,81,89,97,101,109,113,121$. [Formal logarithmic inequalities](../../lean/Conjectures/NearHadamard/Sharp.lean)

## The exact finite checks

The finite interval consists of the fourteen prime powers listed above. Test every integer in the interval by trial division. For each retained order construct the two fields and test the orders of the generators against the prime factors of their group orders.

For Class (4) use the integer polynomial whose coefficient list is the first row of $B_0$. Its resultant with first argument $X^v-1$ is the determinant, since the cyclic shifts diagonalize on all $v$th roots of unity. Take both $w$ and $w^{-1}$. For any other primitive $w'=w^k$ the subgroup stays fixed, and $\alpha'/\alpha=(w^{q+1})^{(k-1)/2}\in F^\times$. Its quadratic character changes at most the overall sign of $S$. Inversion realizes the other sign since $w^{q+1}$ generates $F^\times$. This exhausts the choices.

For Classes (5) and (6), replacing $w$ by another primitive element preserves $H$ and both leaves $D_{i0}$. On nonconstant Fourier modes of $H$, use the core first-row polynomial and the resultant with $1+X+\cdots+X^{m-1}$. On the span of the extra coordinate and the constant vector, the remaining determinant factor is $(q-1)^2$ or $q^2+2q+5$, respectively, as in Theorem 1.6. Equivalently the $2\times2$ block in the orthonormal basis has diagonal $n,n\mp2$ and off-diagonal $\pm2\sqrt m$. All comparisons use integers. No floating-point decision enters the proof.

| Class and choice | Exact order-30 absolute determinant | Ratio |
|---|---:|---:|
| (4), first primitive element | 8,912,683,710,503,976,960,000 | 0.844049782672 |
| (4), inverse primitive element | 8,625,970,539,669,749,760,000 | 0.816897445913 |
| (5) | 8,937,267,024,850,730,352,640 | 0.846377873941 |
| (6) | 8,691,479,386,489,219,973,120 | 0.823101270678 |

The first, third and fourth ratios reproduce the three-decimal values in the introduction to MSX. The paper does not specify a field model or a primitive generator for its order-30 calculation. The other Class (4) value comes from inversion in the same model.

## How Lean verifies the finite interval

The formal proof uses a short integer certificate at each of the 14 field sizes. Let $S$ be either signed half of the conference matrix, with the sign chosen so its Gram block is $nI+2S$. Write $t=\operatorname{tr}(S^3)$, $r=1/v$ and $b=(2v-1)/v^2$. For all $v\ge15$ one has $|x_i|\le9/25$. An eighth-order expansion with geometric tail gives
$$
\log(1+x_i)\ge x_i-x_i^2/2+x_i^3/3-3x_i^4/8.
$$
Since $\sum_i x_i^3=t/v^3$ and $\sum_i x_i^4\le b(1-r)$, it suffices to check the rational inequality
$$
4701/10000-1+r^2/2\ \le\ -(1-r)/2+t/(3v^3)-3b(1-r)/8.
$$
This test applies to each Gram block. Multiplying the two lower bounds and using $\det(MM^T)=|\det M|^2$ gives the required bound for the full matrix.

For a cyclic core $S_{ij}=f(j-i)$ of size $m$, the trace of its cube is $m\sum_{j,k} f(j)f(k-j)f(-k)$. Adjoining a zero diagonal border with constant entries $s$ changes the cubic trace by $3s^2 m\sum_j f(j)$. These identities let Lean compute the certificate in quadratic time. The checker uses the source trace or square-class test to construct the cyclic row. All four generator/class choices are included. The kernel also checks the primality, field cardinalities, primitive orders, coverage of the finite range, and transfer to arbitrary isomorphic field models. [Cyclic trace identities](../../lean/Conjectures/NearHadamard/Cyclic.lean) · [Finite certificate](../../lean/Conjectures/NearHadamard/MomentCheck.lean) · [Cardinality exhaustion](../../lean/Conjectures/NearHadamard/FiniteRange.lean)


The [certificate table](certificates.tsv) lists every cubic trace beside the full absolute determinant. The [replay](replay.py) constructs the fields as polynomial quotients, takes each entire determinant by fraction-free elimination, counts triangles from the Gram matrix and checks the rational inequality above with exact arithmetic.
