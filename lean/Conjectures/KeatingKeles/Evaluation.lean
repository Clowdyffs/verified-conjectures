module

public import Conjectures.KeatingKeles.Statement
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic

@[expose] public section

namespace KeatingKeles
open Finset Matrix

abbrev Entries := ℕ → ℕ → ℝ

def hEntry (B : Entries) (i j : ℕ) : ℝ :=
  if i ≤ j then B i j else if i = j+1 then 2 else 0

def hess (B : Entries) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => hEntry B i j

/-- Successive coefficients of the linear combination of rows that kills all
but the last column. -/
noncomputable def coeff (B : Entries) : ℕ → ℝ
  | 0 => 1
  | j+1 => -(∑ i : Fin (j+1), coeff B i.val * B i.val j)/2
termination_by k => k
decreasing_by exact i.isLt

@[simp] theorem coeff_zero (B : Entries) : coeff B 0 = 1 := by rw [coeff]

theorem coeff_succ (B : Entries) (j : ℕ) :
    coeff B (j+1) = -(∑ i ∈ range (j+1), coeff B i * B i j)/2 := by
  rw [coeff, Fin.sum_univ_eq_sum_range (fun i => coeff B i * B i j)]

private theorem prefix_sum (B : Entries) (j : ℕ) :
    (∑ i ∈ range (j+1), coeff B i * hEntry B i j) = -2 * coeff B (j+1) := by
  rw [coeff_succ]
  have h : ∀ i ∈ range (j+1), coeff B i * hEntry B i j = coeff B i * B i j := by
    intro i hi
    simp [hEntry, Nat.le_of_lt_succ (mem_range.mp hi)]
  rw [sum_congr rfl h]
  ring

private theorem cancel_column (B : Entries) (j n : ℕ) (hj : j < n) :
    (∑ i ∈ range (n+1), coeff B i * hEntry B i j) = 0 := by
  have h := sum_subset (s₁ := range (j+2)) (s₂ := range (n+1))
    (f := fun i => coeff B i * hEntry B i j) (range_mono (by omega)) (by
      intro i _ hi
      simp only [mem_range, not_lt] at hi
      simp [hEntry, show ¬i ≤ j by omega, show i ≠ j+1 by omega])
  rw [← h, sum_range_succ, prefix_sum]
  simp [hEntry]
  ring

theorem abs_det (B : Entries) (n : ℕ) :
    |(hess B (n+1)).det| = 2^(n+1) * |coeff B (n+1)| := by
  classical
  let A := hess B (n+1)
  let r : Fin (n+1) → ℝ := ∑ k : Fin (n+1), coeff B k.val • A k
  let C := A.updateRow 0 r
  have hdet : C.det = A.det := by
    simpa [C, r] using A.det_updateRow_sum (0 : Fin (n+1)) (fun i => coeff B i.val)
  have hr (j : Fin (n+1)) : r j = ∑ i ∈ range (n+1), coeff B i * hEntry B i j := by
    simp only [r, Finset.sum_apply, A, hess, Pi.smul_apply, smul_eq_mul]
    exact Fin.sum_univ_eq_sum_range (fun i => coeff B i * hEntry B i j) _
  have hrow (j : Fin (n+1)) : C 0 j = r j := by simp [C]
  have hminor : C.submatrix Fin.succ (Fin.last n).succAbove =
      (fun i j : Fin n => hEntry B (i.val+1) j.val : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [C, A, hess, Fin.succAbove_last, Matrix.submatrix_apply, Matrix.updateRow_ne]
  have htri : Matrix.IsUpperTriangular (fun i j : Fin n => hEntry B (i.val+1) j.val :
      Matrix (Fin n) (Fin n) ℝ) := by
    intro i j hij
    change j.val < i.val at hij
    simp [hEntry, show ¬i.val+1 ≤ j.val by omega, show i.val ≠ j.val by omega]
  have hm : (C.submatrix Fin.succ (Fin.last n).succAbove).det = 2^n := by
    rw [hminor, Matrix.det_of_isUpperTriangular htri]
    simp [hEntry]
  have hz (j : Fin (n+1)) (hj : j ≠ Fin.last n) : C 0 j = 0 := by
    rw [hrow, hr, cancel_column]
    have := j.isLt
    have : j.val ≠ n := fun h => hj (Fin.ext h)
    omega
  change |A.det| = _
  rw [← hdet, Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last n)]
  · rw [hrow, hr, Fin.val_last, prefix_sum, hm]
    simp [abs_mul, abs_pow, pow_succ]
    ring
  · intro j _ hj
    simp [hz j hj]
  · simp

end KeatingKeles
