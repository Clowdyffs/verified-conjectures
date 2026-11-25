module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

@[expose] public section
open Matrix Finset

namespace NearHadamard

/-- Store a matrix once at every elimination step. -/
def tabulate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  let rows := Array.ofFn fun i => Array.ofFn (A i)
  fun i j => (rows[i.val]!)[j.val]!

theorem tabulate_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : tabulate A = A := by
  ext i j
  simp [tabulate]

def minorStep {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => A i.succ j.succ - (A i.succ 0 / A 0 0) * A 0 j.succ

theorem det_minorStep {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (ha : A 0 0 ≠ 0) :
    A.det = A 0 0 * (minorStep A).det := by
  let c (i : Fin (n+1)) := if i = 0 then 0 else -(A i 0 / A 0 0)
  let B : Matrix (Fin (n+1)) (Fin (n+1)) ℚ := fun i j => A i j + c i * A 0 j
  have hc : c 0 = 0 := by simp [c]
  have he : B.det = A.det := det_eq_of_forall_row_eq_smul_add_const c 0 hc (fun _ _ => rfl)
  have hz (i : Fin n) : B i.succ 0 = 0 := by simp [B, c, ha]
  have hb : B.submatrix Fin.succ Fin.succ = minorStep A := by
    ext i j
    change B i.succ j.succ = _
    simp [B,c,minorStep,sub_eq_add_neg]
  rw [←he, det_succ_column_zero, Fin.sum_univ_succ]
  simp [hz, Fin.succAbove_zero, hc, hb, B]

/-- Zero-pivot failure is explicit. The finite verification uses positive definite Gram blocks. -/
def elimDet : (n : ℕ) → Matrix (Fin n) (Fin n) ℚ → Option ℚ
  | 0, _ => some 1
  | n+1, A =>
    if A 0 0 = 0 then none
    else (elimDet n (tabulate (minorStep A))).map (A 0 0 * ·)

theorem elimDet_sound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) {d : ℚ}
    (h : elimDet n A = some d) : A.det = d := by
  induction n generalizing d with
  | zero => simpa [elimDet] using h
  | succ n ih =>
    simp only [elimDet] at h
    split at h
    · contradiction
    next ha =>
      cases hd : elimDet n (tabulate (minorStep A)) with
      | none => simp [hd] at h
      | some r =>
        simp [hd] at h
        have he := ih _ hd
        rw [tabulate_eq] at he
        rw [det_minorStep A ha, he, h]

end NearHadamard
