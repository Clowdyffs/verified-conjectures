module
public import Conjectures.NearHadamard.FiniteRange
public import Conjectures.NearHadamard.Bounds
public import Conjectures.NearHadamard.Torus
public import Conjectures.NearHadamard.Controls
import Mathlib.Tactic

@[expose] public section
open Matrix
namespace NearHadamard
/-- The published integer inequality for the actual source matrices in both
bordered classes, for arbitrary eligible finite fields at all orders from 126. -/
theorem bordered_large {F : Type*} [Field F] [Fintype F] [DecidableEq F] {w : F}
    (hq : Fintype.card F % 4 = 1) (hw : IsPrimitiveRoot w (Fintype.card F-1))
    (hn : 126 ≤ Fintype.card F+1) (five : Bool) :
    let q := Fintype.card F
    4 * (2*(q:ℤ)) * ((q:ℤ)-1)^((q-1)/2) ≤ 5*|(Source.bordered q w five).det| := by
  let q := Fintype.card F
  let m := (q-1)/2
  have hv : Fintype.card (Border.half q) = m+1 := by simp [Border.half, Border.core, m]
  have hnq : q+1 = 2*(m+1) := by dsimp [m,q]; omega
  have hl : 63 ≤ m+1 := by dsimp [m,q]; omega
  have H := intFill_det (Border.C (q:=q) w five) (Border.conference hq hw five)
    (by rw [hv]; exact hnq) (by rw [hv]; exact hl)
  change 4 * W (Fintype.card (Border.half q)) ≤ 5 * |((Border.filled (q:=q) w five).det : ℝ)| at H
  rw [hv, W, Nat.add_sub_cancel] at H
  have r : (2:ℝ) * ((m+1:ℕ):ℝ) = (q:ℝ)+1 := by exact_mod_cast hnq.symm
  have e1 : 4*((m+1:ℕ):ℝ)-2 = 2*(q:ℝ) := by linarith
  have e2 : 2*((m+1:ℕ):ℝ)-2 = (q:ℝ)-1 := by linarith
  rw [e1, e2, ←mul_assoc] at H
  change 4 * (2*(q:ℤ)) * ((q:ℤ)-1)^m ≤ 5*|(Source.bordered q w five).det|
  rw [Border.abs_det_source hq hw, Border.abs_corrected hq hw]
  exact_mod_cast H

#print axioms bordered_large

/-- For the Class (4) source matrix in an arbitrary finite field of the
correct order, the published lower bound holds at every eligible order from 126. -/
theorem class4_large {F E : Type*} [Field F] [Field E] [Fintype F] [Fintype E]
    [DecidableEq F] [DecidableEq E] {w : F} {z : E}
    (hq : Fintype.card F % 4 = 1) (hw : IsPrimitiveRoot w (Fintype.card F-1))
    (hE : Fintype.card E = Fintype.card F * Fintype.card F)
    (hz : IsPrimitiveRoot z (Fintype.card F * Fintype.card F-1)) (hn : 126 ≤ Fintype.card F+1) :
    let q := Fintype.card F
    4*(2*(q:ℤ))*((q:ℤ)-1)^((q-1)/2) ≤ 5*|(Source.class4 q z).det| := by
  let q := Fintype.card F
  have hd := Border.char_generator hq hw
  letI : Fact (∀ r : F, r^2 ≠ w+0*r) := ⟨Torus.irreducible hd⟩
  letI : Fintype (Torus.Model w) :=
    Fintype.ofEquiv (F × F) (QuadraticAlgebra.equivProd w 0).symm
  have hsize : Fintype.card E = Fintype.card (Torus.Model w) := by
    rw [hE, Fintype.card_congr (QuadraticAlgebra.equivProd w 0), Fintype.card_prod]
  let e := FiniteField.ringEquivOfCardEq hsize
  have hz' : IsPrimitiveRoot (e z) (q*q-1) := hz.map_of_injective e.injective
  have hc := Torus.conference hq hd hz'
  have hv : Fintype.card (Fin (Torus.v q)) = Torus.v q := Fintype.card_fin _
  have hvq : q+1=2*Torus.v q := by dsimp [Torus.v,q]; omega
  have hl : 63 ≤ Torus.v q := by dsimp [Torus.v,q]; omega
  have H := intFill_det _ hc (by rw [hv]; exact hvq) (by rw [hv]; exact hl)
  rw [hv,W] at H
  have er : (q:ℝ)+1 = 2*(Torus.v q:ℝ) := by exact_mod_cast hvq
  have e1 : 4*(Torus.v q:ℝ)-2 = 2*(q:ℝ) := by linarith
  have e2 : 2*(Torus.v q:ℝ)-2 = (q:ℝ)-1 := by linarith
  have en : Torus.v q - 1 = (q-1)/2 := by dsimp [Torus.v,q]; omega
  rw [e1,e2,en,←mul_assoc] at H
  change 4*(2*(q:ℤ))*((q:ℤ)-1)^((q-1)/2) ≤ 5*|(Source.class4 q z).det|
  rw [←Torus.transport e, Torus.abs_source hq hd hz']
  exact_mod_cast H

#print axioms class4_large

/-- The bounded fragment of Problem 15. It has precisely the eligible orders
from 30 through 122, with all fields and all primitive-element choices. -/
def Below126 : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [DecidableEq F] [Field E] [Fintype E] [DecidableEq E],
    let q := Fintype.card F
    ∀ (w : F) (z : E), q % 4 = 1 → 30 ≤ q+1 → q+1 < 126 → Fintype.card E = q*q →
      IsPrimitiveRoot w (q-1) → IsPrimitiveRoot z (q*q-1) →
      let target := 4 * (2*(q:ℤ)) * ((q:ℤ)-1)^((q-1)/2)
      target ≤ 5*|(Source.class4 q z).det| ∧
      target ≤ 5*|(Source.bordered q w true).det| ∧
      target ≤ 5*|(Source.bordered q w false).det|

/-- The MSX/Egan four-fifths question is equivalent to its finite interval.
The reverse implication handles *every* larger prime power directly. -/
theorem problem15_iff_below126 : Source.Problem15 ↔ Below126 := by
  constructor
  · intro h F E _ _ _ _ _ _ q w z hq hn _ he hw hz
    exact h F E w z hq hn he hw hz
  · intro h F E _ _ _ _ _ _ q w z hq hn he hw hz
    change Fintype.card F % 4 = 1 at hq
    by_cases hsmall : q + 1 < 126
    · exact h F E w z hq hn hsmall he hw hz
    · exact ⟨class4_large hq hw he hz (by omega), bordered_large hq hw (by omega) true,
        bordered_large hq hw (by omega) false⟩

#print axioms problem15_iff_below126
/-- The four-fifths determinant question of MSX (Problem 7.1) and Egan et al.
(Problem 15), for all three classes and every eligible prime power. -/
theorem problem15 : Source.Problem15 := by
  apply problem15_iff_below126.mpr
  intro F E _ _ _ _ _ _ q w z hq hn hs he hw hz
  have H := Small.enumerated q hq hn hs (FiniteField.isPrimePow_card F)
  exact H F E w z rfl he hw hz

#print axioms problem15
end NearHadamard
