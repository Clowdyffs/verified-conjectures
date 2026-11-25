module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

open Finset Matrix
open scoped BigOperators

@[expose] public section
namespace NearHadamard

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Two distinct translates of a quadratic character have inner product -1.
The Möbius substitution is extended at its pole using zero inverse. -/
theorem charCorrelation (hc : ringChar F ≠ 2) (a b : F) (hab : a ≠ b) :
    ∑ t : F, quadraticChar F (t-a) * quadraticChar F (t-b) = -1 := by
  let e : F ≃ F :=
    ((Equiv.addRight (-b)).trans (Equiv.inv F)).trans
      ((Equiv.mulLeft₀ (b-a) (sub_ne_zero.mpr hab.symm)).trans (Equiv.addRight 1))
  have ev (t : F) : e t = (b-a)*(t-b)⁻¹+1 := by simp [e, sub_eq_add_neg]
  have localEq (t : F) :
      quadraticChar F (t-a) * quadraticChar F (t-b) =
      quadraticChar F (e t) - if t=b then 1 else 0 := by
    by_cases ht : t=b
    · subst t; simp [ev]
    · have htb : t-b ≠ 0 := sub_ne_zero.mpr ht
      have eh : (e t) * (t-b)^2 = (t-a)*(t-b) := by rw [ev]; field_simp; ring
      rw [←map_mul, ←eh, map_mul, quadraticChar_sq_one' htb]
      simp [ht]
  simp_rw [localEq]
  rw [sum_sub_distrib, Equiv.sum_comp e, quadraticChar_sum_zero hc]
  simp

/-- The symmetric Paley conference matrix, with the extra point indexed
by `none`. The diagonal of its finite core is zero. -/
def paley (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Option F) (Option F) ℤ
  | none, none => 0
  | some _, none | none, some _ => 1
  | some x, some y => quadraticChar F (x-y)

theorem paley_orthogonal (hc : ringChar F ≠ 2) :
    (paley F)ᵀ * paley F = (Fintype.card F : ℤ) • (1 : Matrix _ _ ℤ) := by
  ext i j
  simp only [mul_apply, transpose_apply, Fintype.sum_option, Matrix.smul_apply, smul_eq_mul]
  cases i with
  | none =>
    cases j with
    | none => simp [paley]
    | some b =>
      have hz : ∑ x : F, quadraticChar F (x-b) = 0 := by
        simpa [sub_eq_add_neg] using (Equiv.sum_comp (Equiv.addRight (-b)) (quadraticChar F)).trans (quadraticChar_sum_zero hc)
      simp [paley, hz, -quadraticChar_apply]
  | some a =>
    cases j with
    | none =>
      have hz : ∑ x : F, quadraticChar F (x-a) = 0 := by
        simpa [sub_eq_add_neg] using (Equiv.sum_comp (Equiv.addRight (-a)) (quadraticChar F)).trans (quadraticChar_sum_zero hc)
      simp [paley, hz, -quadraticChar_apply]
    | some b =>
      by_cases hab : a=b
      · subst b
        have hs (x : F) : quadraticChar F (x-a) * quadraticChar F (x-a) =
            1 - if x=a then 1 else 0 := by
          by_cases hx : x=a
          · simp [hx]
          · rw [←sq, quadraticChar_sq_one (sub_ne_zero.mpr hx)]; simp [hx]
        simp [paley, hs, sum_sub_distrib, -quadraticChar_apply]
      · simp [paley, hab, charCorrelation hc a b hab, -quadraticChar_apply]

#print axioms paley_orthogonal

end NearHadamard
