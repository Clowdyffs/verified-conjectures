module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace KeatingKeles

/-- Zero-based form of Definition 2.10 and Problem 2.4 with s = 2 and t = 1. -/
def Admissible {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, (i.val ≤ j.val → 0 ≤ A i j ∧ A i j ≤ 1) ∧
    (i.val = j.val + 1 → A i j = 2) ∧ (j.val + 1 < i.val → A i j = 0)

/-- U of §3, with ones on the even upper diagonals. -/
def original (i j : ℕ) : ℝ :=
  if i = j + 1 then 2 else if i ≤ j ∧ i % 2 = j % 2 then 1 else 0

/-- Equation (4.1): exchange the two entries in the first column and the two
entries in the last row, then exchange the first two rows and last two columns. -/
def rcEntry (n i j : ℕ) : ℝ :=
  let r := if i = 0 then 1 else if i = 1 then 0 else i
  let c := if j + 2 = n then n - 1 else if j + 1 = n then n - 2 else j
  if c = 0 ∧ r = 0 then 2 else if c = 0 ∧ r = 1 then 1 else
  if r + 1 = n ∧ c + 2 = n then 1 else if r + 1 = n ∧ c + 1 = n then 2 else
  original r c

def comparator (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => rcEntry n i.val j.val

/-- Keating and Keleş, arXiv:2003.00454v2, §6, Question 2, in “the case
s=2 and t=1”: “Is Uₙ⁽ʳᶜ⁾ the maximizing matrix in this case when n ≥ 4?” -/
def QuestionTwo : Prop :=
  ∀ n : ℕ, 4 ≤ n → Admissible (comparator n) ∧
    ∀ A : Matrix (Fin n) (Fin n) ℝ, Admissible A → |A.det| ≤ |(comparator n).det|

end KeatingKeles
