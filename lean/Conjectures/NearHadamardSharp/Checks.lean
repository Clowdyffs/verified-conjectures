module
public import Conjectures.NearHadamardSharp.Row
public import Conjectures.NearHadamardSharp.Moment
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
open NearHadamard.Small

def Good (q : ℕ) (f : Family) (d : ℤ) : Prop :=
  fullMinimum f ≤ (d:ℚ)/(delta q:ℚ) ∧
    (30≤q+1 → restrictedMinimum f ≤ (d:ℚ)/(delta q:ℚ))

instance (q f d) : Decidable (Good q f d) := by unfold Good; infer_instance

def AtOrder (q : ℕ) : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [DecidableEq F] [Field E] [Fintype E] [DecidableEq E]
    (w : F) (z : E), Fintype.card F=q → Fintype.card E=q*q →
    IsPrimitiveRoot w (q-1) → IsPrimitiveRoot z (q*q-1) → ∀ f, Good q f (magnitude q w z f)

theorem good_of_uniform (q : ℕ) (hq : 1<q) (f : Family) (d : ℤ)
    (h : 81844*delta q ≤ 100000*d) : Good q f d := by
  have pos : (0:ℤ)<delta q := by
    unfold delta
    have h' : (1:ℤ)<q := by exact_mod_cast hq
    exact mul_pos (by positivity) (pow_pos (by linarith) _)
  have e : (81844/100000:ℚ) ≤ (d:ℚ)/(delta q:ℚ) := by
    apply (le_div_iff₀ (by exact_mod_cast pos)).mpr
    have H : (81844:ℚ)*(delta q:ℚ) ≤ 100000*(d:ℚ) := by exact_mod_cast h
    linarith
  exact ⟨le_trans (by cases f <;> norm_num [fullMinimum]) e,
    fun _ => le_trans (by cases f <;> norm_num [restrictedMinimum]) e⟩

theorem modelOrder {q : ℕ} {K : Type} [Field K] [Fintype K] [DecidableEq K] (u : K)
    [Fact (∀ r : K, r^2 ≠ u+0*r)] (a : Torus.Model u)
    (hK : Fintype.card K=q) (hq : q%4=1)
    (hu : IsPrimitiveRoot u (q-1)) (ha : IsPrimitiveRoot a (q*q-1))
    (h4 : Good q .four |(Source.class4 q a).det|)
    (h4i : Good q .four |(Source.class4 q a⁻¹).det|)
    (h5 : Good q .five |(Source.bordered q u true).det|)
    (h6 : Good q .six |(Source.bordered q u false).det|) : AtOrder q := by
  subst q
  intro F E _ _ _ _ _ _ w z hF hE hw hz f
  let e := FiniteField.ringEquivOfCardEq (hE.trans (card_model u).symm)
  let g := FiniteField.ringEquivOfCardEq hF
  have hu' := hw.map_of_injective g.injective
  have ha' := hz.map_of_injective e.injective
  cases f with
  | four =>
    change Good _ _ |(Source.class4 _ z).det|
    rw [←Torus.transport e]
    rcases Torus.primitive_choices hq (Border.char_generator hq hu) ha' ha with h|h
    · rwa [h]
    · rwa [h]
  | five =>
    change Good _ _ |(Source.bordered _ w true).det|
    rwa [←Border.transport g _ w true,Border.primitive_independent hq hu' hu]
  | six =>
    change Good _ _ |(Source.bordered _ w false).det|
    rwa [←Border.transport g _ w false,Border.primitive_independent hq hu' hu]

theorem modelValue {q lo : ℕ} {K : Type} [Field K] [Fintype K] [DecidableEq K] (u : K)
    [Fact (∀ r : K, r^2≠u+0*r)] (a : Torus.Model u)
    (hK : Fintype.card K=q) (hq : q%4=1) (hl : lo≤q+1)
    (hu : IsPrimitiveRoot u (q-1)) (ha : IsPrimitiveRoot a (q*q-1)) (f : Family) (r : ℚ)
    (hr : r=(magnitude q u a f:ℚ)/(delta q:ℚ)) : r ∈ values lo f := by
  subst q
  exact ⟨K,Torus.Model u,inferInstance,inferInstance,inferInstance,inferInstance,
    inferInstance,inferInstance,u,a,hq,hl,card_model u,hu,ha,hr⟩

theorem torusGood {q : ℕ} {F : Type*} [Field F] [DecidableEq F] [Fintype F] {w : F}
    [Fact (∀ r : F, r^2≠w+0*r)] (z : Torus.Model w) (hc : Fintype.card F=q)
    (hq : q%4=1) (hw : IsPrimitiveRoot w (q-1)) (hz : IsPrimitiveRoot z (q*q-1))
    (hn : 30≤q+1) [NeZero (Torus.v q)]
    (ht : passesMoment (Torus.v q) (unpackCube (Torus.v q) (torusPack q z (radix (Torus.v q)))) = true) :
    Good q .four |(Source.class4 q z).det| := by
  subst q
  apply good_of_uniform _ Fintype.one_lt_card
  apply torus_sound _ hq (Border.char_generator hq hw) hz hn
  rwa [torusCube_eq]

theorem borderGood {q : ℕ} {F : Type*} [Field F] [DecidableEq F] [Fintype F] {w : F}
    (hc : Fintype.card F=q) (hq : q%4=1) (hw : IsPrimitiveRoot w (q-1)) (hn : 30≤q+1)
    [NeZero ((q-1)/2)] (five : Bool)
    (ht : passesMoment ((q-1)/2+1) (unpackCube ((q-1)/2) (borderPack q w five (radix ((q-1)/2))) +
      3*((q-1)/2:ℕ)*borderPack q w five 1) = true) :
    Good q (if five then .five else .six) |(Source.bordered q w five).det| := by
  subst q
  apply good_of_uniform _ Fintype.one_lt_card
  apply border_sound hq hw hn five
  rwa [borderTrace_eq]
end NearHadamard.Optimal
