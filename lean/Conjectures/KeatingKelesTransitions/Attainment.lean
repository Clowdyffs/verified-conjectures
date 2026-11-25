module
public import Conjectures.KeatingKelesTransitions.Determinants
@[expose] public section
namespace HessenbergTransitions
open Finset

theorem colored_box (c : ℕ → Bool) : KeatingKeles.InBox (colored c) := by
  intro i j _
  unfold colored
  split <;> norm_num

def Signed (b : Bool) (z : ℝ) : Prop := if b then 0 ≤ z else z ≤ 0

private theorem color_aux (h : ℝ) (c : ℕ → Bool) (j : ℕ)
    (hs : ∀ i ≤ j, Signed (c i) (coeff h (colored c) i)) :
    coeff h (colored c) (j+1) = if c (j+1) then h*(masses h (colored c) j).2
      else -(h*(masses h (colored c) j).1) := by
  rw [coeff_next]
  cases hc : c (j+1)
  · simp only [Bool.false_eq_true,ite_false,neg_mul,masses,KeatingKeles.posMass,neg_inj]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hv := hs i (Nat.le_of_lt_succ (mem_range.mp hi))
    change coeff h (colored c) i * colored c i j = max (coeff h (colored c) i) 0
    cases hb : c i <;> simp [Signed,hb] at hv <;> simp [colored,hb,hc,hv]
  · simp only [ite_true,masses,KeatingKeles.negMass,neg_mul,← mul_neg,← sum_neg_distrib]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hv := hs i (Nat.le_of_lt_succ (mem_range.mp hi))
    change coeff h (colored c) i * (-colored c i j) = max (-coeff h (colored c) i) 0
    cases hb : c i <;> simp [Signed,hb] at hv <;> simp [colored,hb,hc,hv]

theorem colored_inc {h : ℝ} (hh : 0 ≤ h) (c : ℕ → Bool) (hc : c 0 = true) (j : ℕ) :
    coeff h (colored c) (j+1) = if c (j+1) then h*(masses h (colored c) j).2
      else -(h*(masses h (colored c) j).1) := by
  apply color_aux
  have H (k : ℕ) : Signed (c k) (coeff h (colored c) k) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero => simp [Signed,hc,coeff]
      | succ i =>
        rw [color_aux _ _ _ (fun a ha => ih a (by omega))]
        have hn := mass_nonneg h (colored c) i
        cases he : c (i+1) <;> simp [Signed,hh,hn.1,hn.2,mul_nonneg]
  exact fun i _ => H i

theorem colored_step {h : ℝ} (hh : 0 ≤ h) (c : ℕ → Bool) (hc : c 0 = true) (j : ℕ) :
    masses h (colored c) (j+1) = move h (c (j+1)) (masses h (colored c) j) := by
  rw [mass_next,colored_inc hh c hc j]
  have hn := mass_nonneg h (colored c) j
  cases he : c (j+1) <;>
    simp [move,leftS,rightS,mul_nonneg hh hn.1,mul_nonneg hh hn.2]

theorem play_colored {h : ℝ} (hh : 0 ≤ h) (c : ℕ → Bool) (hc : c 0 = true) (j k : ℕ) :
    play h k (fun i => c (j+i+1)) (masses h (colored c) j) = masses h (colored c) (j+k) := by
  induction k generalizing j with
  | zero => simp [play]
  | succ k ih =>
    simp only [play,Nat.add_zero,← colored_step hh c hc]
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (j+1)

theorem score_axis (x : V) : score x (1,0) = max x.1 x.2 := by simp [score,dot,sw]

theorem sharp_coeff {h : ℝ} (hh : 0 < h) (m : ℕ) :
    ∃ c : ℕ → Bool, c 0 = true ∧
      |coeff h (colored c) (m+1)| = h*best h m (1,0) (1,0) := by
  obtain ⟨f,hf⟩ := best_witness h m (1,0) (1,0)
  let v := play h m f (1,0)
  let c : ℕ → Bool := fun | 0 => true | i+1 => if i < m then f i else decide (v.1 ≤ v.2)
  have hm : masses h (colored c) m = v := by
    have hp := play_colored hh.le c rfl 0 m
    simp only [Nat.zero_add,masses_zero] at hp
    rw [← hp]
    apply play_congr
    intro i hi
    simp [c,hi]
  refine ⟨c,rfl,?_⟩
  rw [colored_inc hh.le c rfl,hm,hf,score_axis]
  change |if c (m+1) then h*v.2 else -(h*v.1)| = h*max v.1 v.2
  have hn := mass_nonneg h (colored c) m
  rw [hm] at hn
  by_cases he : v.1 ≤ v.2
  · simp [c,he,abs_of_nonneg (mul_nonneg hh.le hn.2)]
  · simp [c,he,max_eq_left (le_of_not_ge he),abs_of_nonneg (mul_nonneg hh.le hn.1)]

theorem upper_coeff {h : ℝ} (hh : 0 ≤ h) {B : Entries} (hB : KeatingKeles.InBox B) (m : ℕ) :
    |coeff h B (m+1)| ≤ h*best h m (1,0) (1,0) := by
  have hb := best_bound hh hB 0 m
  simp only [Nat.zero_add,masses_zero,best,score_axis] at hb
  obtain ⟨hl,hu⟩ := increment_bounds hh hB m
  exact abs_le.mpr ⟨(neg_le_neg (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hb) hh)).trans hl,
    hu.trans (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hb) hh)⟩

end HessenbergTransitions
