module

public import Conjectures.NearHadamard.Statement
public import Conjectures.NearHadamard.Elimination
public import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic

@[expose] public section

open Matrix
namespace NearHadamard.Controls

set_option maxRecDepth 100000
set_option maxHeartbeats 0

instance : Fact (Nat.Prime 29) := ⟨by decide⟩
abbrev Base := ZMod 29
abbrev Ext := QuadraticAlgebra Base 27 5
instance : Fact (∀ r : Base, r^2 ≠ 27+5*r) := ⟨by decide⟩

def z : Ext := ⟨0,1⟩

instance : Fintype Ext :=
  Fintype.ofEquiv (Base × Base) (QuadraticAlgebra.equivProd 27 5).symm

theorem extension_size : Fintype.card Ext = 29*29 := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd 27 5)]
  simp [Base]

theorem base_generator : IsPrimitiveRoot (2 : Base) 28 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) (by decide)
  intro p hp h
  change p ∣ 2*(2*7) at h
  have : p = 2 ∨ p = 7 := by
    simpa only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7), or_self_left] using h
  rcases this with rfl|rfl <;> decide

theorem extension_generator : IsPrimitiveRoot z 840 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) (by decide)
  intro p hp h
  change p ∣ 2*(2*(2*(3*(5*7)))) at h
  have : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    simpa only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7), or_self_left] using h
  rcases this with rfl|rfl|rfl|rfl <;> decide

theorem inverse_generator : IsPrimitiveRoot z⁻¹ 840 := extension_generator.inv


def cert {ι : Type*} [Fintype ι] {n : ℕ} (e : Fin n ≃ ι) (A : Matrix ι ι ℤ) :
    Option ℚ :=
  let Q := tabulate fun i j => (A (e i) (e j) : ℚ)
  elimDet n (tabulate (Q * Qᵀ))

theorem abs_det_of_cert {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (e : Fin n ≃ ι) (A : Matrix ι ι ℤ) (d : ℤ) (hd : 0 ≤ d)
    (h : cert e A = some ((d:ℚ)^2)) : |A.det| = d := by
  let Q : Matrix (Fin n) (Fin n) ℚ := fun i j => (A (e i) (e j) : ℚ)
  change elimDet n (tabulate (tabulate Q * (tabulate Q)ᵀ)) = some ((d:ℚ)^2) at h
  simp only [tabulate_eq] at h
  have he := elimDet_sound _ h
  rw [Matrix.det_mul, Matrix.det_transpose] at he
  let B := (Int.castRingHom ℚ).mapMatrix A
  have hdet : Q.det = (A.det : ℚ) := by
    change (B.submatrix e e).det = _
    rw [Matrix.det_submatrix_equiv_self]
    exact (RingHom.map_det (Int.castRingHom ℚ) A).symm
  rw [hdet, ←sq] at he
  have hs : A.det^2 = d^2 := by exact_mod_cast he
  simpa [abs_of_nonneg hd] using (sq_eq_sq_iff_abs_eq_abs _ _).mp hs

def torusIndex : Fin 30 ≃ Fin 15 ⊕ Fin 15 := (@finSumFinEquiv 15 15).symm
def borderIndex : Fin 30 ≃ Option (Fin 14) ⊕ Option (Fin 14) :=
  torusIndex.trans (Equiv.sumCongr (finSuccEquiv 14) (finSuccEquiv 14))

set_option maxHeartbeats 0 in
theorem class5_order30 : |(Source.bordered 29 (2:Base) true).det| = 8937267024850730352640 := by
  apply abs_det_of_cert borderIndex _ _ (by decide)
  decide +kernel

set_option maxHeartbeats 0 in
theorem class6_order30 : |(Source.bordered 29 (2:Base) false).det| = 8691479386489219973120 := by
  apply abs_det_of_cert borderIndex _ _ (by decide)
  decide +kernel

set_option maxHeartbeats 0 in
theorem class4_order30 : |(Source.class4 29 z).det| = 8912683710503976960000 := by
  apply abs_det_of_cert torusIndex _ _ (by decide)
  decide +kernel

set_option maxHeartbeats 0 in
theorem class4_inverse_order30 : |(Source.class4 29 z⁻¹).det| = 8625970539669749760000 := by
  apply abs_det_of_cert torusIndex _ _ (by decide)
  decide +kernel

#print axioms class4_order30
#print axioms class4_inverse_order30
#print axioms class5_order30
#print axioms class6_order30

/-- A simultaneous witness for every hypothesis of Problem 15 at the lower endpoint. -/
theorem admissible_order30 :
    ∃ (w : Base) (a : Ext), let q := Fintype.card Base
      q % 4 = 1 ∧ q+1 = 30 ∧ 30 ≤ q+1 ∧ Fintype.card Ext = q*q ∧
      IsPrimitiveRoot w (q-1) ∧ IsPrimitiveRoot a (q*q-1) := by
  refine ⟨2, z, ?_⟩
  simp only [Base, ZMod.card]
  exact ⟨by decide, by decide, by decide, extension_size, base_generator, extension_generator⟩

/-- The nearest-thousandth operation is exact on a nonnegative determinant. -/
def thousandths30 (d : ℤ) : ℤ :=
  let W : ℤ := 58*28^14
  (2000*d+W)/(2*W)

/-- The three decimals printed together after MSX Theorem 1.6, in class order. -/
theorem source_decimals :
    thousandths30 |(Source.class4 29 z).det| = 844 ∧
    thousandths30 |(Source.bordered 29 (2 : Base) true).det| = 846 ∧
    thousandths30 |(Source.bordered 29 (2 : Base) false).det| = 823 := by
  rw [class4_order30, class5_order30, class6_order30]
  decide

end NearHadamard.Controls
