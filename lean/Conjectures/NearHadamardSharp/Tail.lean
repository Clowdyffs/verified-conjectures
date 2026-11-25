module
public import Conjectures.NearHadamardSharp.Gram
public import Conjectures.NearHadamard.Torus
import Mathlib.Tactic
@[expose] public section
open Matrix
namespace NearHadamard.Optimal
theorem bordered_large {F : Type*} [Field F] [Fintype F] [DecidableEq F] {w : F}
    (hq : Fintype.card F % 4 = 1) (hw : IsPrimitiveRoot w (Fintype.card F-1))
    (hn : 2160 ≤ Fintype.card F+1) (five : Bool) :
    let q := Fintype.card F
    81844 * (2*(q:ℤ)) * ((q:ℤ)-1)^((q-1)/2) ≤ 100000*|(Source.bordered q w five).det| := by
  let q := Fintype.card F
  let m := (q-1)/2
  have hv : Fintype.card (Border.half q) = m+1 := by simp [Border.half, Border.core, m]
  have hnq : q+1 = 2*(m+1) := by dsimp [m,q]; omega
  have hl : 1080 ≤ m+1 := by dsimp [m,q]; omega
  have H := intFill_det_of_moment_or_large (Border.C (q:=q) w five) (Border.conference hq hw five)
    (by rw [hv]; exact hnq) (by rw [hv]; omega) (Or.inl (by rw [hv]; exact hl)) (Or.inl (by rw [hv]; exact hl))
  change 81844 * W (Fintype.card (Border.half q)) ≤ 100000 * |((Border.filled (q:=q) w five).det : ℝ)| at H
  rw [hv, W, Nat.add_sub_cancel] at H
  have r : (2:ℝ) * ((m+1:ℕ):ℝ) = (q:ℝ)+1 := by exact_mod_cast hnq.symm
  have e1 : 4*((m+1:ℕ):ℝ)-2 = 2*(q:ℝ) := by linarith
  have e2 : 2*((m+1:ℕ):ℝ)-2 = (q:ℝ)-1 := by linarith
  rw [e1, e2, ←mul_assoc] at H
  change 81844 * (2*(q:ℤ)) * ((q:ℤ)-1)^m ≤ 100000*|(Source.bordered q w five).det|
  rw [Border.abs_det_source hq hw, Border.abs_corrected hq hw]
  exact_mod_cast H

#print axioms bordered_large

/-- For the Class (4) source matrix in an arbitrary finite field of the
correct order, the 81844/100000 lower bound holds at every eligible order from 2160. -/
theorem class4_large {F E : Type*} [Field F] [Field E] [Fintype F] [Fintype E]
    [DecidableEq F] [DecidableEq E] {w : F} {z : E}
    (hq : Fintype.card F % 4 = 1) (hw : IsPrimitiveRoot w (Fintype.card F-1))
    (hE : Fintype.card E = Fintype.card F * Fintype.card F)
    (hz : IsPrimitiveRoot z (Fintype.card F * Fintype.card F-1)) (hn : 2160 ≤ Fintype.card F+1) :
    let q := Fintype.card F
    81844*(2*(q:ℤ))*((q:ℤ)-1)^((q-1)/2) ≤ 100000*|(Source.class4 q z).det| := by
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
  have hl : 1080 ≤ Torus.v q := by dsimp [Torus.v,q]; omega
  have H := intFill_det_of_moment_or_large _ hc (by rw [hv]; exact hvq) (by rw [hv]; omega) (Or.inl (by rw [hv]; exact hl)) (Or.inl (by rw [hv]; exact hl))
  rw [hv,W] at H
  have er : (q:ℝ)+1 = 2*(Torus.v q:ℝ) := by exact_mod_cast hvq
  have e1 : 4*(Torus.v q:ℝ)-2 = 2*(q:ℝ) := by linarith
  have e2 : 2*(Torus.v q:ℝ)-2 = (q:ℝ)-1 := by linarith
  have en : Torus.v q - 1 = (q-1)/2 := by dsimp [Torus.v,q]; omega
  rw [e1,e2,en,←mul_assoc] at H
  change 81844*(2*(q:ℤ))*((q:ℤ)-1)^((q-1)/2) ≤ 100000*|(Source.class4 q z).det|
  rw [←Torus.transport e, Torus.abs_source hq hd hz']
  exact_mod_cast H

#print axioms class4_large

end NearHadamard.Optimal
