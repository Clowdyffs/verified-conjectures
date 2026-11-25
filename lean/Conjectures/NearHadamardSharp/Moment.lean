module
public import Conjectures.NearHadamardSharp.Gram
public import Conjectures.NearHadamardSharp.Statement
public import Conjectures.NearHadamard.MomentCheck
import Mathlib.Tactic
@[expose] public section
open Matrix Finset NearHadamard.Small
namespace NearHadamard.Optimal
def passesMoment (v : ℕ) (t : ℤ) : Bool :=
  decide (4928/10000-1+((v:ℚ)⁻¹)^2/2 ≤
      -(1-(v:ℚ)⁻¹)/2+(t:ℚ)/(v:ℚ)^3/3-(3/8)*((2*(v:ℚ)-1)/(v:ℚ)^2)*(1-(v:ℚ)⁻¹))

theorem passesMoment_sound {v : ℕ} {t : ℤ} (h : passesMoment v t = true) :
    cubeCondition (v:ℝ) (t:ℝ) := by
  simp only [passesMoment,decide_eq_true_eq] at h
  unfold cubeCondition
  have H := (Rat.cast_le (K:=ℝ)).mpr h
  push_cast at H
  exact H

theorem filled_of_checks {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (C : Matrix (ι ⊕ ι) (ι ⊕ ι) ℤ) (hc : Conference q C)
    (hq : q+1=2*Fintype.card ι) (hn : 15≤Fintype.card ι)
    (ha : passesMoment (Fintype.card ι) (C.toBlocks₁₁*C.toBlocks₁₁*C.toBlocks₁₁).trace = true)
    (hd : passesMoment (Fintype.card ι) ((-C.toBlocks₂₂)*(-C.toBlocks₂₂)*(-C.toBlocks₂₂)).trace = true) :
    (81844*delta q) ≤ 100000*|(diagonalFill C).det| := by
  have H := intFill_det_of_moment_or_large C hc hq hn
    (Or.inr (passesMoment_sound ha)) (Or.inr (passesMoment_sound hd))
  have er : (q:ℝ)+1=2*(Fintype.card ι:ℝ) := by exact_mod_cast hq
  have e1 : 4*(Fintype.card ι:ℝ)-2=2*(q:ℝ) := by linarith
  have e2 : 2*(Fintype.card ι:ℝ)-2=(q:ℝ)-1 := by linarith
  have en : Fintype.card ι-1 = (q-1)/2 := by omega
  rw [W,e1,e2,en] at H
  unfold delta
  push_cast
  push_cast at H
  exact_mod_cast H


theorem torus_sound {K : Type*} [Field K] [DecidableEq K] [Fintype K] {u : K}
    [Fact (∀ r:K, r^2≠u+0*r)] (a : Torus.Model u) (hq : Fintype.card K%4=1)
    (hd : quadraticChar K u = -1) (ha : IsPrimitiveRoot a (Fintype.card K*Fintype.card K-1))
    (hn : 30≤Fintype.card K+1)
    (ht : passesMoment (Torus.v (Fintype.card K)) (cyclicCube (torusRow (Fintype.card K) a)) = true) :
    (81844*delta (Fintype.card K)) ≤ 100000*|(Source.class4 (Fintype.card K) a).det| := by
  rw [Torus.abs_source hq hd ha]
  have h := Torus.conference hq hd ha
  apply filled_of_checks _ h (by simp [Torus.v]; omega) (by simp [Torus.v]; omega)
  all_goals
    rw [cyclicCube_eq (by dsimp [Torus.v]; omega),triangles_eq] at ht
    change passesMoment _ (torusCore (Fintype.card K) a * torusCore (Fintype.card K) a * torusCore (Fintype.card K) a).trace = true at ht
    rw [torusCore_eq a hq ha] at ht
  all_goals rw [Torus.form_blocks hq hd ha]
  all_goals simpa [Matrix.fromBlocks_neg] using ht


theorem border_sound {K : Type*} [Field K] [DecidableEq K] [Fintype K] {w : K}
    (hq : Fintype.card K%4=1) (hw : IsPrimitiveRoot w (Fintype.card K-1))
    (hn : 30≤Fintype.card K+1) (five : Bool)
    (ha : passesMoment ((Fintype.card K-1)/2+1) (borderCube (Fintype.card K) w five) = true)
    :
    (81844*delta (Fintype.card K)) ≤ 100000*|(Source.bordered (Fintype.card K) w five).det| := by
  rw [Border.abs_det_source hq hw,Border.abs_corrected hq hw]
  have h := Border.conference hq hw five
  have hc := borderCore_eq hq hw five
  apply filled_of_checks _ h (by simp [Border.half,Border.core]; omega)
      (by simp [Border.half,Border.core]; omega)
  · rw [borderCube_eq _ _ _ false (by omega),hc.1] at ha
    simpa [Border.half,Border.core] using ha
  · rw [borderCube_eq _ _ _ true (by omega),hc.2] at ha
    simpa [Border.half,Border.core] using ha

end NearHadamard.Optimal
