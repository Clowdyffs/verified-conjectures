# Maximum absolute determinant at subdiagonal two

Let $A$ be an $n$ by $n$ real upper Hessenberg matrix with twos on the first subdiagonal and every upper-triangular entry in $[0,1]$. We prove that the matrix $U_n^{(rc)}$ of Keating and Keleş, equation (4.1), attains the maximum absolute determinant for every $n\ge4$. Index rows and columns from zero.

## A scalar for each prefix of columns

Set $x_0=1$ and, for $0\le j<n$, put
$$
x_{j+1}=-\tfrac12\sum_{i=0}^j A_{ij}x_i.
$$
Replace row zero by the sum of rows $i$ with coefficients $x_i$ for $0\le i<n$. Its own coefficient is one, so the determinant is preserved. The first $n-1$ entries of the new row vanish. In column $j<n-1$, the extra subdiagonal term $2x_{j+1}$ cancels the sum defining $x_{j+1}$. The remaining entry in column $n-1$ is $-2x_n$. Its complementary minor is upper triangular with diagonal two. Expansion in the new row gives $\det A=(-2)^n x_n$.

Let $p_j=\sum_{i=0}^j\max(x_i,0)$ and $q_j=\sum_{i=0}^j\max(-x_i,0)$. From $0\le A_{ij}\le1$ we have
$$
-p_j/2\le x_{j+1}\le q_j/2.
$$
Initially $(p_0,q_0)=(1,0)$. Every next pair is coordinatewise bounded by one of
$$
L(p,q)=(p+q/2,q),\qquad R(p,q)=(p,q+p/2).
$$
The sign of the new coefficient determines which map to use. Both maps preserve coordinatewise order.

## A sharp bound for every order

Start with $(a_0,b_0)=(1,1)$ and set $(a_{k+1},b_{k+1})=(b_k+a_k/2,a_k)$. Induction gives $0\le b_k\le a_k\le2b_k$. For $j=k+3$, abbreviate $(a_k,b_k)$ by $(a,b)$ and $(p_j,q_j)$ by $(p,q)$. We claim
$$
\max(p,q)\le a+b/2,\qquad
\max(p+q/2,q+p/2)\le a+b,\qquad
p+q\le 3a/2+b.\tag{1}
$$
For $k=0$, the pair after one step is bounded by $(1,1/2)$, and after two steps by $(5/4,1/2)$ or $(1,1)$. After three steps it is bounded by one of $(3/2,1/2),(5/4,9/8),(3/2,1),(1,3/2)$. All four satisfy (1) with $a=b=1$.

For the induction step, symmetry reduces the calculation to $(u,v)=L(p,q)$. Write $(a',b')=(b+a/2,a)$. Both $u$ and $v$ are at most $a+b=a'+b'/2$. For the weighted bounds use
$$
u+v/2=p+q\le 3a/2+b,\quad
v+u/2=(q+p/2)+q/4\le a+b+(a+b/2)/4\le 3a/2+b.
$$
Here $b\le a$ suffices for the last inequality, and $3a/2+b=a'+b'$. Finally
$$
u+v=(q+p/2)+(p+q)/2\le (a+b)+(3a/2+b)/2=3a'/2+b'.
$$
These inequalities are monotone in the coordinates, so they hold for every permitted step. At $n=k+4$, taking one more coefficient gives the universal bound
$$
|x_n|\le (a_k+b_k/2)/2.\tag{2}
$$

## Equality for the source matrix

Assign a sign to the indices $0,\ldots,n$. Index zero is positive, and indices one and two are negative. Starting at index three, alternate signs through $n-2$, so odd indices in $[2,n-2]$ are positive. Index $n-1$ repeats the sign at $n-2$. Index $n$ takes the opposite sign. Form an admissible matrix whose upper entry $(i,j)$ is one precisely when indices $i$ and $j+1$ have different signs.

This matrix is $U_n^{(rc)}$. In the source's checkerboard matrix $U_n$, the upper entry equals one when the original row and column indices have equal parity. Interchange entries $(0,0),(1,0)$ and entries $(n-1,n-2),(n-1,n-1)$, then swap rows zero and one and columns $n-2$ and $n-1$. Away from the four corrected positions the row used is $1,0,2,3,\dots$ and the column used is $0,1,\dots,n-3,n-1,n-2$. On the upper triangle their equal-parity test gives exactly the different-sign test above. The two diagonal corrections supply ones at $(0,0)$ and $(n-1,n-1)$ and the two subdiagonal corrections restore twos at $(1,0)$ and $(n-1,n-2)$. The Lean identity checks every entry, including order four where there is no middle alternation. [Original construction, equation (4.1)](https://arxiv.org/pdf/2003.00454v2#page=7)

Inductively, each $x_i$ has its assigned weak sign. A positive output selects all negative terms, giving $x_{j+1}=q_j/2$. A negative output selects all positive terms and gives $x_{j+1}=-p_j/2$. Thus each step increases the mass of the assigned sign by exactly half the opposite mass. After the two negative increments the two masses are both one. After the next $k=n-4$ alternating increments the masses in the order (most recently increased, opposite) are $(a_k,b_k)$. Repeating the last sign increases its mass to $a_k+b_k/2$. The final opposite increment attains (2). Multiplication by $2^n$ gives equality in the determinant bound.

The maximum is $D_{k+4}=2^{k+3}(a_k+b_k/2)$. Each component of the middle recurrence satisfies $z_{k+2}=z_{k+1}/2+z_k$. Consequently $D_4=12$, $D_5=32$, and $D_n=D_{n-1}+4D_{n-2}$ for $n\ge6$, as in Proposition 4.3.

Attainment permits ties. At order four the source determinant is $12$, while the authors’ distinct matrix $U_4^{(r)}$ with rows $(1,1,0,1),(2,0,1,0),(0,2,1,0),(0,0,2,1)$ has determinant $-12$.
