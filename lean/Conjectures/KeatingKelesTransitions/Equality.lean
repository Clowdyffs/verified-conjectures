module
public import Conjectures.KeatingKelesTransitions.Rigidity
@[expose] public section
namespace HessenbergTransitions
open Finset

noncomputable def signs (h : ℝ) (B : Entries) (j : ℕ) := decide (0 ≤ coeff h B j)

private theorem last_saturated {h : ℝ} (hh : 0 < h) {B : Entries} (hB : KeatingKeles.InBox B)
    {m : ℕ} (he : Extreme (h := h) B m) :
    (0 ≤ coeff h B (m+1) → coeff h B (m+1) = h*(masses h B m).2) ∧
    (coeff h B (m+1) ≤ 0 → coeff h B (m+1) = -(h*(masses h B m).1)) := by
  obtain ⟨hl,hu⟩ := increment_bounds hh.le hB m
  have hb := every_prefix hh hB he m 0 (by omega)
  change score _ (1,0) = _ at hb
  rw [score_axis] at hb
  unfold Extreme at he
  rw [← hb] at he
  constructor
  · intro hz
    rw [abs_of_nonneg hz] at he
    exact le_antisymm hu (he ▸ mul_le_mul_of_nonneg_left (le_max_right _ _) hh.le)
  · intro hz
    rw [abs_of_nonpos hz] at he
    have := mul_le_mul_of_nonneg_left (le_max_left (masses h B m).1 (masses h B m).2) hh.le
    exact le_antisymm (by linarith) hl

theorem upper_forced {h : ℝ} (hh : 0 < h) {B : Entries} (hB : KeatingKeles.InBox B)
    {m : ℕ} (hm : 2 ≤ m) (he : Extreme (h := h) B m) {i j : ℕ} (hi : i ≤ j) (hj : j ≤ m) :
    B i j = colored (signs h B) i j := by
  have hn (a : ℕ) (ha : a ≤ m) : coeff h B a ≠ 0 := by
    cases a with
    | zero => simp [coeff]
    | succ a => exact (saturated hh hB hm he (by omega : a < m)).1
  have hs : (0 ≤ coeff h B (j+1) → coeff h B (j+1) = h*(masses h B j).2) ∧
      (coeff h B (j+1) ≤ 0 → coeff h B (j+1) = -(h*(masses h B j).1)) := by
    by_cases heq : j=m
    · subst j; exact last_saturated hh hB he
    · exact (saturated hh hB hm he (by omega : j < m)).2
  have hz := hn i (hi.trans hj)
  let z := coeff h B
  have bt (k : ℕ) (hk : k ∈ range (j+1)) := hB k j (Nat.le_of_lt_succ (mem_range.mp hk))
  by_cases hnew : 0 ≤ z (j+1)
  · have hsum := hs.1 hnew
    rw [coeff_next] at hsum
    change -h*(∑ k ∈ range (j+1), z k * B k j) = h*(∑ k ∈ range (j+1), max (-z k) 0) at hsum
    rw [neg_mul,← mul_neg,← sum_neg_distrib] at hsum
    have ht (k : ℕ) (hk : k ∈ range (j+1)) : -(z k * B k j) ≤ max (-z k) 0 := by
      obtain ⟨hl,hu⟩ := bt k hk
      by_cases h : 0 ≤ z k
      · exact (neg_nonpos.mpr (mul_nonneg h hl)).trans (le_max_right _ _)
      · apply le_trans _ (le_max_left _ _)
        nlinarith [mul_nonneg (neg_nonneg.mpr (le_of_not_ge h)) (sub_nonneg.mpr hu)]
    have hv := (sum_eq_sum_iff_of_le ht).mp ((mul_right_inj' hh.ne').mp hsum) i (mem_range.mpr (by omega))
    change z i ≠ 0 at hz
    by_cases hp : 0 ≤ z i
    · rw [max_eq_right (neg_nonpos.mpr hp)] at hv
      have hzero := (mul_eq_zero.mp (neg_eq_zero.mp hv)).resolve_left hz
      simpa [colored,signs,show 0 ≤ coeff h B i from hp,show 0 ≤ coeff h B (j+1) from hnew] using hzero
    · rw [max_eq_left (neg_nonneg.mpr (le_of_not_ge hp)),neg_inj] at hv
      have hone : B i j = 1 := (mul_right_inj' hz).mp (hv.trans (mul_one _).symm)
      simpa [colored,signs,show ¬0 ≤ coeff h B i from hp,show 0 ≤ coeff h B (j+1) from hnew] using hone
  · have hsum := hs.2 (le_of_not_ge hnew)
    rw [coeff_next,neg_mul,neg_inj] at hsum
    change h*(∑ k ∈ range (j+1), z k * B k j) = h*(∑ k ∈ range (j+1), max (z k) 0) at hsum
    have ht (k : ℕ) (hk : k ∈ range (j+1)) : z k * B k j ≤ max (z k) 0 := by
      obtain ⟨hl,hu⟩ := bt k hk
      by_cases hp : 0 ≤ z k
      · exact (by simpa using mul_le_mul_of_nonneg_left hu hp : z k*B k j ≤ z k).trans (le_max_left _ _)
      · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hp) hl).trans (le_max_right _ _)
    have hv := (sum_eq_sum_iff_of_le ht).mp ((mul_right_inj' hh.ne').mp hsum) i (mem_range.mpr (by omega))
    change z i ≠ 0 at hz
    by_cases hp : 0 ≤ z i
    · rw [max_eq_left hp] at hv
      have hone : B i j = 1 := (mul_right_inj' hz).mp (hv.trans (mul_one _).symm)
      simpa [colored,signs,show 0 ≤ coeff h B i from hp,show ¬0 ≤ coeff h B (j+1) from hnew] using hone
    · rw [max_eq_right (le_of_not_ge hp)] at hv
      have hzero := (mul_eq_zero.mp hv).resolve_left hz
      simpa [colored,signs,show ¬0 ≤ coeff h B i from hp,show ¬0 ≤ coeff h B (j+1) from hnew] using hzero

theorem word_masses {h : ℝ} (hh : 0 ≤ h) (c : ℕ → Bool) (hc : c 0 = true) (m : ℕ) :
    run h (word c m) (1,0) = masses h (colored c) m := by
  induction m with
  | zero => simp [run,word,masses_zero]
  | succ m ih =>
    rw [colored_step hh c hc,← ih]
    simp [run,word,List.range_succ,List.foldl_append]

theorem colored_value {h : ℝ} (hh : 0 ≤ h) (c : ℕ → Bool) (hc : c 0 = true) (m : ℕ) :
    |coeff h (colored c) (m+1)| = h * value h (word c m) (1,0) (axis (c (m+1))) := by
  rw [value,word_masses hh c hc,colored_inc hh c hc]
  have hn := mass_nonneg h (colored c) m
  cases hc' : c (m+1) <;> simp [axis,dot,abs_of_nonneg (mul_nonneg hh hn.1),abs_of_nonneg (mul_nonneg hh hn.2)]

theorem colored_extreme_iff {h : ℝ} (hh : 0 < h) (c : ℕ → Bool) (hc : c 0 = true) (m : ℕ) :
    Extreme (h := h) (colored c) m ↔ Form h (word c m) (1,0) (axis (c (m+1))) := by
  have hs (b : Bool) : sorted (1,0) = sorted (axis b) := by cases b <;> norm_num [axis,sorted]
  have hn (b : Bool) : Nonneg (axis b) := by cases b <;> norm_num [Nonneg,axis]
  rw [Extreme,colored_value hh.le c hc,mul_right_inj' hh.ne',form_iff hh _ ⟨zero_le_one,le_rfl⟩
    (hn _) (hs _)]
  simp only [word,List.length_map,List.length_range]
  rw [← best_sort_right h m _ (axis _),← hs, best_sort_right]

end HessenbergTransitions
