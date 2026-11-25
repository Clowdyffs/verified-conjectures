module
public import Conjectures.NearHadamardSharp.Checks
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic
@[expose] public section
open Matrix Finset NearHadamard.Small
namespace NearHadamard.Optimal

def halfGram {ι : Type*} [DecidableEq ι] (q : ℕ) (S : Matrix ι ι ℤ) : Matrix ι ι ℤ :=
  fun i j => (if i=j then (q:ℤ)+1 else 0) + 2*S i j

theorem fill_det_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    {C : Matrix (ι ⊕ ι) (ι ⊕ ι) ℤ} (h : Conference q C) :
    (diagonalFill C).det^2 =
      (halfGram q C.toBlocks₁₁).det * (halfGram q (-C.toBlocks₂₂)).det := by
  have e : diagonalFill C * (diagonalFill C)ᵀ =
      fromBlocks (halfGram q C.toBlocks₁₁) 0 0 (halfGram q (-C.toBlocks₂₂)) := by
    ext i j
    rw [fillGram h]
    cases i <;> cases j <;> simp [halfSign,halfGram,Matrix.fromBlocks,Matrix.toBlocks₁₁,Matrix.toBlocks₂₂] <;> ring
  rw [←Matrix.det_fromBlocks_zero₂₁,←e,Matrix.det_mul,Matrix.det_transpose,pow_two]

theorem torusExact {q : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F] {w : F}
    [Fact (∀ r : F, r^2≠w+0*r)] (z : Torus.Model w) (hc : Fintype.card F=q)
    (hq : q%4=1) (hw : IsPrimitiveRoot w (q-1)) (hz : IsPrimitiveRoot z (q*q-1)) (d : ℤ)
    (hd : 0≤d) (hx : (halfGram q (torusCore q z)).det=d) : |(Source.class4 q z).det|=d := by
  subst q
  have hd' := Border.char_generator hq hw
  rw [Torus.abs_source hq hd' hz]
  have H := fill_det_sq (Torus.conference hq hd' hz)
  rw [Torus.form_blocks hq hd' hz] at H
  change _ = (halfGram _ (-Torus.V z)).det * (halfGram _ (-(-(-Torus.V z)))).det at H
  rw [neg_neg] at H
  rw [torusCore_eq _ hq hz] at hx
  rw [hx,←pow_two] at H
  rw [Torus.form_blocks hq hd' hz]
  simpa [abs_of_nonneg hd] using (sq_eq_sq_iff_abs_eq_abs _ _).mp H

theorem borderFlip {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ) (s : ℤ)
    (A : Matrix ι ι ℤ) : (halfGram q (borderExtend (-s) A)).det = (halfGram q (borderExtend s A)).det := by
  let t : Option ι → ℤ := fun i => if i=none then -1 else 1
  let D := diagonal t
  have e : halfGram q (borderExtend (-s) A) = D * halfGram q (borderExtend s A) * D := by
    ext i j
    simp only [D,Matrix.diagonal_mul,Matrix.mul_diagonal]
    cases i <;> cases j <;> simp [t,halfGram,borderExtend]
  have hD : D*D=1 := by
    rw [show D=diagonal t by rfl,diagonal_mul_diagonal]
    ext i j; by_cases h : i=j
    · subst j; cases i <;> simp [t, Matrix.one_apply]
    · simp [h,Matrix.one_apply]
  rw [e,det_mul,det_mul,mul_right_comm,←det_mul,hD,det_one,one_mul]

theorem borderExact {q : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {w : F} (hc : Fintype.card F=q) (hq : q%4=1) (hw : IsPrimitiveRoot w (q-1)) (five : Bool)
    (d : ℤ) (hd : 0≤d) (hx : (halfGram q (borderCore q w five false)).det=d) :
    |(Source.bordered q w five).det|=d := by
  subst q
  rw [Border.abs_det_source hq hw,Border.abs_corrected hq hw]
  have H := fill_det_sq (Border.conference hq hw five)
  obtain ⟨h₁,h₂⟩ := borderCore_eq hq hw five
  rw [←h₁,←h₂,hx] at H
  simp only [borderCore,Bool.false_eq_true,ite_false,ite_true] at hx H
  rw [borderFlip,hx,←pow_two] at H
  change |(diagonalFill (Border.C w five)).det|=d
  simpa [abs_of_nonneg hd] using (sq_eq_sq_iff_abs_eq_abs _ _).mp H

/-- A lower triangular integer row transformation L certifies a determinant
when the entries of LA on and below the diagonal have been checked. -/
theorem triangularCert {n : ℕ} (A L : Matrix (Fin n) (Fin n) ℤ) (d : ℤ)
    (p : Fin n → ℤ)
    (hl : ∀ i j : Fin n, i < j → L i j=0)
    (hu : ∀ i j : Fin n, j ≤ i → (∑ k, L i k*A k j) = if i=j then p i else 0)
    (hn : (∏ i, L i i) ≠ 0) (he : (∏ i, L i i)*d = ∏ i, p i) : A.det=d := by
  have hl' : L.IsLowerTriangular := fun _ _ h => hl _ _ h
  have hu' : (L*A).IsUpperTriangular := fun i j h => by
    change j < i at h
    rw [Matrix.mul_apply,hu i j (le_of_lt h),if_neg (ne_of_gt h)]
  have hd (i) : (L*A) i i=p i := by rw [Matrix.mul_apply,hu i i le_rfl,if_pos rfl]
  have H := Matrix.det_of_isUpperTriangular hu'
  simp only [hd,det_mul,det_of_isLowerTriangular _ hl'] at H
  exact mul_left_cancel₀ hn (H.trans he.symm)


def coreMatrix {n : ℕ} (q : ℕ) (r : Array ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  halfGram q (cyclic (fun i : Fin n => r[i.val]!))

def borderedMatrix {m : ℕ} (q : ℕ) (five : Bool) (r : Array ℤ) :
    Matrix (Fin (m+1)) (Fin (m+1)) ℤ :=
  (halfGram q (borderExtend (Border.c five) (cyclic (fun i : Fin m => r[i.val]!)))).submatrix
    (finSuccEquiv m) (finSuccEquiv m)

theorem torusExactRow {q : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F] {w : F}
    [Fact (∀ r : F, r^2≠w+0*r)] (z : Torus.Model w) (hc : Fintype.card F=q)
    (hq : q%4=1) (hw : IsPrimitiveRoot w (q-1)) (hz : IsPrimitiveRoot z (q*q-1))
    (row : Array ℤ) (d : ℤ) (hd : 0≤d) (hr : ∀ i, torusRow q z i=row[i.val]!)
    (hx : (coreMatrix (n:=Torus.v q) q row).det=d) : |(Source.class4 q z).det|=d := by
  apply torusExact z hc hq hw hz d hd
  simpa only [torusCore,coreMatrix,funext hr] using hx

theorem borderExactRow {q : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {w : F} (hc : Fintype.card F=q) (hq : q%4=1) (hw : IsPrimitiveRoot w (q-1))
    (five : Bool) (row : Array ℤ) (d : ℤ) (hd : 0≤d) (hr : ∀ i, borderRow q w five i=row[i.val]!)
    (hx : (borderedMatrix (m:=(q-1)/2) q five row).det=d) :
    |(Source.bordered q w five).det|=d := by
  apply borderExact hc hq hw five d hd
  rw [borderedMatrix,Matrix.det_submatrix_equiv_self] at hx
  simpa only [borderCore,Bool.false_eq_true,ite_false,funext hr] using hx

def lowerMatrix {n : ℕ} (rows : Array (Array ℤ)) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if j ≤ i then (rows[i.val]!)[j.val]! else 0

def cachedMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  let table := Array.ofFn fun i => Array.ofFn (A i)
  fun i j => (table[i.val]!)[j.val]!

theorem cachedMatrix_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : cachedMatrix A = A := by
  ext i j; simp [cachedMatrix]

theorem arrayCert {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (coeff : Array (Array ℤ))
    (p : Array ℤ) (d : ℤ)
    (hu : ∀ i j : Fin n, j ≤ i → (∑ k, lowerMatrix coeff i k * cachedMatrix A k j) =
      if i=j then p[i.val]! else 0)
    (hn : (∏ i : Fin n, lowerMatrix coeff i i) ≠ 0)
    (he : (∏ i : Fin n, lowerMatrix coeff i i)*d = ∏ i : Fin n, p[i.val]!) : A.det=d := by
  rw [cachedMatrix_eq] at hu
  apply triangularCert A (lowerMatrix coeff) d _ _ hu hn he
  intro i j h; simp [lowerMatrix,not_le.mpr h]

end NearHadamard.Optimal
