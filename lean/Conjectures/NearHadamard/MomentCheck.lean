module
public import Conjectures.NearHadamard.Cyclic
public import Conjectures.NearHadamard.Bounds
public import Conjectures.NearHadamard.Small
import Mathlib.Tactic

@[expose] public section
open Matrix Finset
namespace NearHadamard.Small

def passesMoment (v : ℕ) (t : ℤ) : Bool :=
  decide (4701/10000-1+((v:ℚ)⁻¹)^2/2 ≤
      -(1-(v:ℚ)⁻¹)/2+(t:ℚ)/(v:ℚ)^3/3-(3/8)*((2*(v:ℚ)-1)/(v:ℚ)^2)*(1-(v:ℚ)⁻¹))

theorem passesMoment_sound {v : ℕ} {t : ℤ} (h : passesMoment v t = true) :
    momentCondition (v:ℝ) (t:ℝ) := by
  simp only [passesMoment,decide_eq_true_eq] at h
  unfold momentCondition
  have H := (Rat.cast_le (K:=ℝ)).mpr h
  push_cast at H
  exact H

theorem filled_of_checks {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (C : Matrix (ι ⊕ ι) (ι ⊕ ι) ℤ) (hc : Conference q C)
    (hq : q+1=2*Fintype.card ι) (hn : 15≤Fintype.card ι)
    (ha : passesMoment (Fintype.card ι) (C.toBlocks₁₁*C.toBlocks₁₁*C.toBlocks₁₁).trace = true)
    (hd : passesMoment (Fintype.card ι) ((-C.toBlocks₂₂)*(-C.toBlocks₂₂)*(-C.toBlocks₂₂)).trace = true) :
    threshold q ≤ 5*|(diagonalFill C).det| := by
  have H := intFill_det_of_moment_or_large C hc hq hn
    (Or.inr (passesMoment_sound ha)) (Or.inr (passesMoment_sound hd))
  have er : (q:ℝ)+1=2*(Fintype.card ι:ℝ) := by exact_mod_cast hq
  have e1 : 4*(Fintype.card ι:ℝ)-2=2*(q:ℝ) := by linarith
  have e2 : 2*(Fintype.card ι:ℝ)-2=(q:ℝ)-1 := by linarith
  have en : Fintype.card ι-1 = (q-1)/2 := by omega
  rw [W,e1,e2,en,←mul_assoc] at H
  unfold threshold
  exact_mod_cast H

def charValue {F : Type*} [Field F] [DecidableEq F] (q : ℕ) (t : F) : ℤ :=
  if t=0 then 0 else Source.sign (npowBinRec (q/2) t=1)

theorem charValue_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hq : Fintype.card F%4=1) (t : F) :
    charValue (Fintype.card F) t = quadraticChar F t := by
  by_cases h : t=0
  · simp [h,charValue]
  · simp only [charValue,if_neg h,Source.sign,←fastPower,
      quadraticChar_eq_pow_of_char_ne_two (Border.char_ne_two hq) h]

def torusRow {K : Type*} [Field K] [DecidableEq K] (q : ℕ) {u : K}
    (a : Torus.Model u) (i : Fin (Torus.v q)) : ℤ :=
  let b := npowBinRec (2*(q-1)) a
  let al := npowBinRec (Torus.v q) a
  Neg.neg (charValue q (Torus.tr (al*npowBinRec i.val b)))

def torusCore {K : Type*} [Field K] [DecidableEq K] (q : ℕ) {u : K}
    (a : Torus.Model u) := cyclic (torusRow q a)

theorem torusCore_eq {K : Type*} [Field K] [DecidableEq K] [Fintype K] {u : K}
    [Fact (∀ r:K, r^2≠u+0*r)] (a : Torus.Model u) (hq : Fintype.card K%4=1)
    (ha : IsPrimitiveRoot a (Fintype.card K*Fintype.card K-1)) :
    torusCore (Fintype.card K) a = -Torus.V a := by
  ext i j
  have hs := Torus.step_order hq Fintype.one_lt_card ha
  simp [torusCore,cyclic,torusRow,←shift_val,←fastPower,charValue_eq hq,-quadraticChar_apply]
  change quadraticChar K (Torus.tr (Torus.alpha (Fintype.card K) a * (Torus.b (Fintype.card K) a)^Source.shift i j)) = _
  rw [Border.pow_shift hs]
  rfl

theorem torus_sound {K : Type*} [Field K] [DecidableEq K] [Fintype K] {u : K}
    [Fact (∀ r:K, r^2≠u+0*r)] (a : Torus.Model u) (hq : Fintype.card K%4=1)
    (hd : quadraticChar K u = -1) (ha : IsPrimitiveRoot a (Fintype.card K*Fintype.card K-1))
    (hn : 30≤Fintype.card K+1)
    (ht : passesMoment (Torus.v (Fintype.card K)) (cyclicCube (torusRow (Fintype.card K) a)) = true) :
    threshold (Fintype.card K) ≤ 5*|(Source.class4 (Fintype.card K) a).det| := by
  rw [Torus.abs_source hq hd ha]
  have h := Torus.conference hq hd ha
  apply filled_of_checks _ h (by simp [Torus.v]; omega) (by simp [Torus.v]; omega)
  all_goals
    rw [cyclicCube_eq (by dsimp [Torus.v]; omega),triangles_eq] at ht
    change passesMoment _ (torusCore (Fintype.card K) a * torusCore (Fintype.card K) a * torusCore (Fintype.card K) a).trace = true at ht
    rw [torusCore_eq a hq ha] at ht
  all_goals rw [Torus.form_blocks hq hd ha]
  all_goals simpa [Matrix.fromBlocks_neg] using ht

def borderRow {K : Type*} [Field K] [DecidableEq K] (q : ℕ) (w : K) (five : Bool)
    (i : Border.core q) : ℤ := Border.c five*charValue q (npowBinRec i.val (w^2)-1)

def borderCore {K : Type*} [Field K] [DecidableEq K] (q : ℕ) (w : K) (five lower : Bool) :
    Matrix (Border.half q) (Border.half q) ℤ :=
  borderExtend (if lower then -Border.c five else Border.c five) (cyclic (borderRow q w five))

theorem borderCore_eq {K : Type*} [Field K] [DecidableEq K] [Fintype K] {w : K}
    (hq : Fintype.card K%4=1) (hw : IsPrimitiveRoot w (Fintype.card K-1)) (five : Bool) :
    let q := Fintype.card K
    let C := Border.C (q:=q) w five
    borderCore q w five false = C.toBlocks₁₁ ∧ borderCore q w five true = -C.toBlocks₂₂ := by
  have hn := Fintype.one_lt_card (α:=K)
  have hw0 : w ≠ 0 := (hw.isUnit (by omega)).ne_zero
  have hσ := Border.char_generator hq hw
  have hs := hw.pow_of_dvd (p:=2) (by decide) (by omega)
  have hh (i j : Border.core (Fintype.card K)) :
      quadraticChar K ((w^2)^Source.shift i j-1) =
        quadraticChar K (Border.squareLabel w i-Border.squareLabel w j) := by
    rw [Border.pow_shift hs]
    change quadraticChar K (Border.squareLabel w j/Border.squareLabel w i-1) = _
    have h0 : Border.squareLabel w i ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hw0)
    rw [Border.ratio_char h0 (Border.char_squareLabel hw0 i),
      Border.sym_char hq (Border.squareLabel w j)]
  have divChar (a b : K) : quadraticChar K (a/w-b/w) = -quadraticChar K (a-b) := by
    have h : (a/w-b/w)*w = a-b := by field_simp
    have he := congrArg (quadraticChar K) h
    rw [map_mul,hσ] at he
    linarith
  have negChar (a : K) : quadraticChar K (-a)=quadraticChar K a := by
    simpa only [zero_sub,sub_zero] using Border.sym_char hq 0 a
  have hi (i j : Border.core (Fintype.card K)) : Source.shift i j < (Fintype.card K-1)/2 :=
    Nat.mod_lt _ (by omega)
  constructor <;> ext i j <;> cases i <;> cases j <;>
    simp [borderCore,borderExtend,cyclic,borderRow,←shift_val,←fastPower,charValue_eq hq,hh,Matrix.toBlocks₁₁,Matrix.toBlocks₂₂,
      Border.C,Border.label,paley,negChar,Border.char_squareLabel hw0,
      divChar,quadraticChar_zero,-quadraticChar_apply]

def borderCube {K : Type*} [Field K] [DecidableEq K] (q : ℕ) (w : K) (five : Bool) : ℤ :=
  let r := borderRow q w five
  cyclicCube r + 3*((q-1)/2:ℕ)*(∑ i, r i)

theorem borderCube_eq {K : Type*} [Field K] [DecidableEq K] (q : ℕ) (w : K) (five lower : Bool)
    (hn : 0 < (q-1)/2) :
    let B := borderCore q w five lower
    borderCube q w five = (B*B*B).trace := by
  dsimp only
  rw [←triangles_eq, borderCore, triangles_extend, cyclic_sum hn, borderCube, cyclicCube_eq hn]
  cases five <;> cases lower <;> simp [Border.c] <;> ring

theorem border_sound {K : Type*} [Field K] [DecidableEq K] [Fintype K] {w : K}
    (hq : Fintype.card K%4=1) (hw : IsPrimitiveRoot w (Fintype.card K-1))
    (hn : 30≤Fintype.card K+1) (five : Bool)
    (ha : passesMoment ((Fintype.card K-1)/2+1) (borderCube (Fintype.card K) w five) = true)
    :
    threshold (Fintype.card K) ≤ 5*|(Source.bordered (Fintype.card K) w five).det| := by
  rw [Border.abs_det_source hq hw,Border.abs_corrected hq hw]
  have h := Border.conference hq hw five
  have hc := borderCore_eq hq hw five
  apply filled_of_checks _ h (by simp [Border.half,Border.core]; omega)
      (by simp [Border.half,Border.core]; omega)
  · rw [borderCube_eq _ _ _ false (by omega),hc.1] at ha
    simpa [Border.half,Border.core] using ha
  · rw [borderCube_eq _ _ _ true (by omega),hc.2] at ha
    simpa [Border.half,Border.core] using ha

/-- Numerical data exposed for cross-checking a separate source-matrix implementation.
Sort the two torus traces so the output is invariant under a change of generator. -/
def traceList {K : Type*} [Field K] [DecidableEq K] (q : ℕ) (w : K)
    [Fact (∀ r : K, r^2 ≠ w+0*r)] (z : Torus.Model w) : List ℤ :=
  let a := cyclicCube (torusRow q z)
  let b := cyclicCube (torusRow q z⁻¹)
  [min a b, max a b, borderCube q w true, borderCube q w false]

def momentsPass {K : Type*} [Field K] [DecidableEq K] (q : ℕ) (w : K)
    [Fact (∀ r:K,r^2≠w+0*r)] (z : Torus.Model w) : Bool :=
  passesMoment (Torus.v q) (cyclicCube (torusRow q z)) &&
  passesMoment (Torus.v q) (cyclicCube (torusRow q z⁻¹)) &&
  passesMoment ((q-1)/2+1) (borderCube q w true) &&
  passesMoment ((q-1)/2+1) (borderCube q w false)

theorem order_of_moments {q : ℕ} {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (u : K) [Fact (∀ r:K,r^2≠u+0*r)] (a : Torus.Model u)
    (hK : Fintype.card K=q) (hq : q%4=1) (hn : 30≤q+1)
    (hu : IsPrimitiveRoot u (q-1)) (ha : IsPrimitiveRoot a (q*q-1))
    (hc : momentsPass q u a = true) : AtOrder q := by
  subst q
  simp only [momentsPass,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := hc
  have hd := Border.char_generator hq hu
  exact fromModel u a rfl hq hu ha (torus_sound a hq hd ha hn h1)
    (torus_sound a⁻¹ hq hd ha.inv hn h2) (border_sound hq hu hn true h3)
    (border_sound hq hu hn false h4)

end NearHadamard.Small
