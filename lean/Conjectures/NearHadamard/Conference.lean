module

public import Conjectures.NearHadamard.Paley
import Mathlib.Tactic

@[expose] public section

open Matrix
namespace NearHadamard
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A symmetric integer conference matrix with squared column length q. -/
structure Conference (q : ℕ) (C : Matrix ι ι ℤ) : Prop where
  symm : ∀ i j, C i j = C j i
  diag : ∀ i, C i i = 0
  off : ∀ i j, i ≠ j → (C i j)^2 = 1
  orth : Cᵀ*C = (q:ℤ) • (1 : Matrix ι ι ℤ)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem conference_paley (hq : Fintype.card F % 4 = 1) :
    Conference (Fintype.card F) (paley F) := by
  have hneg : quadraticChar F (-1) = 1 :=
    (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr (one_ne_zero' F))).mpr
      (FiniteField.isSquare_neg_one_iff.mpr (by omega))
  refine ⟨?_,?_,?_, paley_orthogonal (by
    intro hc; have := FiniteField.even_card_of_char_two hc; omega)⟩
  · intro i j; cases i <;> cases j <;> try rfl
    rename_i a b
    change quadraticChar F (a-b) = quadraticChar F (b-a)
    rw [show a-b = (-1)*(b-a) by ring, map_mul, hneg, one_mul]
  · intro i; cases i <;> simp [paley]
  · intro i j hij
    cases i with
    | none => cases j <;> simp_all [paley]
    | some a =>
      cases j with
      | none => simp [paley]
      | some b =>
        exact quadraticChar_sq_one (sub_ne_zero.mpr (fun h => hij (congrArg some h)))

theorem Conference.relabel {κ : Type*} [Fintype κ] [DecidableEq κ]
    {q : ℕ} {C : Matrix ι ι ℤ} (h : Conference q C) (e : κ ≃ ι)
    (c : ℤ) (hc : c^2=1) :
    Conference q (fun i j => c*C (e i) (e j) : Matrix κ κ ℤ) := by
  refine ⟨fun i j => congrArg _ (h.symm _ _), fun i => by simp [h.diag],
    fun i j hij => by simp [mul_pow, hc, h.off _ _ (e.injective.ne hij)], ?_⟩
  ext i j
  have H := congrFun (congrFun h.orth (e i)) (e j)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply] at H ⊢
  have hh (k : κ) : c*C (e k) (e i)*(c*C (e k) (e j)) = C (e k) (e i)*C (e k) (e j) := by
    calc _ = c^2*(C (e k) (e i)*C (e k) (e j)) := by ring
         _ = _ := by rw [hc, one_mul]
  change (∑ k, c * C (e k) (e i) * (c * C (e k) (e j))) = _
  simp_rw [hh]
  rw [Equiv.sum_comp e (fun k => C k (e i)*C k (e j))]
  simpa only [e.injective.eq_iff] using H

theorem Conference.switch {q : ℕ} {C : Matrix ι ι ℤ} (h : Conference q C)
    (w : ι → ℤ) (hw : ∀ i, (w i)^2=1) :
    Conference q (fun i j => w i * C i j * w j : Matrix ι ι ℤ) := by
  refine ⟨?_, fun i => by simp [h.diag], ?_, ?_⟩
  · intro i j; rw [h.symm i j]; ring
  · intro i j hij; simp only [mul_pow, hw, h.off i j hij, one_mul]
  · ext i j
    change (∑ k, (w k * C k i * w i)*(w k * C k j * w j)) = _
    have he (k : ι) : (w k*C k i*w i)*(w k*C k j*w j) =
        (w i*w j)*(C k i*C k j) := by
      calc _ = (w k)^2*((w i*w j)*(C k i*C k j)) := by ring
           _ = _ := by rw [hw,one_mul]
    simp_rw [he]
    rw [←Finset.mul_sum]
    have ho := congrFun (congrFun h.orth i) j
    change (∑ k, C k i*C k j) = _ at ho
    rw [ho]
    by_cases e : i=j
    · subst j
      rw [←sq,hw,one_mul]
    · simp [e]

def diagonalFill (C : Matrix (ι ⊕ ι) (ι ⊕ ι) ℤ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℤ :=
  fun i j => C i j + if i=j then Sum.elim (fun _ => 1) (fun _ => -1) i else 0

def halfSign : ι ⊕ ι → ℤ := Sum.elim (fun _ => 1) (fun _ => -1)

theorem fillGram {C : Matrix (ι ⊕ ι) (ι ⊕ ι) ℤ} {q : ℕ} (h : Conference q C)
    (i j : ι ⊕ ι) :
    (diagonalFill C * (diagonalFill C)ᵀ) i j =
      (if i=j then (q:ℤ)+1 else 0) + (halfSign i + halfSign j)*C i j := by
  let D := diagonal (halfSign (ι:=ι))
  have he : diagonalFill C = C+D := by
    ext a b
    by_cases e : a=b <;> simp [diagonalFill, D, diagonal_apply, halfSign, e]
  have tr : Cᵀ = C := by ext a b; exact h.symm _ _
  have orth := h.orth
  rw [tr] at orth
  have td : Dᵀ = D := diagonal_transpose _
  have DD : D*D = 1 := by
    rw [show D = diagonal (halfSign (ι:=ι)) by rfl, diagonal_mul_diagonal]
    ext a b
    by_cases e : a=b
    · subst b; cases a <;> simp [halfSign]
    · simp [e, diagonal_apply, one_apply]
  rw [he, transpose_add, tr, td, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, orth, DD]
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply,
    smul_eq_mul, one_apply]
  by_cases e : i=j <;> simp [e,D,Matrix.mul_diagonal, Matrix.diagonal_mul] <;> ring

end NearHadamard
