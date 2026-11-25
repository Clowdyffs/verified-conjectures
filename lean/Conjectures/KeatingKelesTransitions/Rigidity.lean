module
public import Conjectures.KeatingKelesTransitions.Attainment
public import Conjectures.KeatingKelesTransitions.Forms
@[expose] public section
namespace HessenbergTransitions
open Finset

private theorem increasing_pos {h : ℝ} (hh : 0 < h) (k : ℕ) {x : V}
    (ha : 0 < x.1) (hb : 0 < x.2) :
    best h k x (1,0) < best h (k+1) x (1,0) := by
  induction k generalizing x with
  | zero =>
    simp only [best,score_axis,leftS,rightS]
    have h1 := mul_pos hh ha
    have h2 := mul_pos hh hb
    grind
  | succ k ih =>
    exact max_lt_max (ih (add_pos ha (mul_pos hh hb)) hb) (ih ha (add_pos hb (mul_pos hh ha)))

theorem strictly_increasing {h : ℝ} (hh : 0 < h) (k : ℕ) :
    best h (k+1) (1,0) (1,0) < best h (k+2) (1,0) (1,0) := by
  have step (i : ℕ) : best h (i+1) (1,0) (1,0) = best h i (1,h) (1,0) := by
    simp only [best,leftS,rightS,mul_zero,mul_one,add_zero,zero_add]
    apply max_eq_right
    exact best_mono hh.le i (x := (1,0)) (x' := (1,h)) ⟨zero_le_one,le_rfl⟩ le_rfl hh.le
  rw [step,step]
  exact increasing_pos hh k zero_lt_one hh

def mix (u v : V) (a : ℝ) : V := ((1-a)*u.1+a*v.1,(1-a)*u.2+a*v.2)

private theorem best_convex (h : ℝ) (k : ℕ) (u v y : V) {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ 1) :
    best h k (mix u v a) y ≤ (1-a)*best h k u y + a*best h k v y := by
  have mix_le {x z X Z : ℝ} (hx : x ≤ X) (hz : z ≤ Z) :
      (1-a)*x+a*z ≤ (1-a)*X+a*Z :=
    add_le_add (mul_le_mul_of_nonneg_left hx (by linarith)) (mul_le_mul_of_nonneg_left hz ha)
  induction k generalizing y with
  | zero =>
    have de (q : V) : dot (mix u v a) q = (1-a)*dot u q+a*dot v q := by
      simp [dot,mix]; ring
    simp only [best,score,de]
    exact max_le (mix_le (le_max_left _ _) (le_max_left _ _)) (mix_le (le_max_right _ _) (le_max_right _ _))
  | succ k ih =>
    rw [best_right,best_right h k u,best_right h k v]
    exact max_le ((ih _).trans (mix_le (le_max_left _ _) (le_max_left _ _)))
      ((ih _).trans (mix_le (le_max_right _ _) (le_max_right _ _)))

theorem prefix_step_bound {h : ℝ} (hh : 0 ≤ h) {B : Entries} (hB : KeatingKeles.InBox B) (j k : ℕ) :
    best h k (masses h B (j+1)) (1,0) ≤ best h (k+1) (masses h B j) (1,0) := by
  obtain ⟨hl,hu⟩ := increment_bounds hh hB j
  have hy : Nonneg ((1,0) : V) := ⟨zero_le_one,le_rfl⟩
  rw [mass_next]
  by_cases hc : 0 ≤ coeff h B (j+1)
  · rw [max_eq_left hc,max_eq_right (neg_nonpos.mpr hc),add_zero]
    apply le_trans _ (le_max_left _ _)
    exact best_mono hh k (x' := leftS h (masses h B j)) hy (add_le_add_right hu _) le_rfl
  · rw [max_eq_right (le_of_not_ge hc),max_eq_left (neg_nonneg.mpr (le_of_not_ge hc)),add_zero]
    apply le_trans _ (le_max_right _ _)
    exact best_mono hh k (x' := rightS h (masses h B j)) hy le_rfl
      (add_le_add_right (show -coeff h B (j+1) ≤ h*(masses h B j).1 by linarith) _)

theorem prefix_bound {h : ℝ} (hh : 0 ≤ h) {B : Entries} (hB : KeatingKeles.InBox B) (j k : ℕ) :
    best h k (masses h B j) (1,0) ≤ best h (j+k) (1,0) (1,0) := by
  induction j generalizing k with
  | zero => simp [masses_zero]
  | succ j ih =>
    rw [show j+1+k=j+(k+1) by omega]
    exact (prefix_step_bound hh hB j k).trans (ih _)

def Extreme {h : ℝ} (B : Entries) (m : ℕ) :=
  |coeff h B (m+1)| = h*best h m (1,0) (1,0)

theorem every_prefix {h : ℝ} (hh : 0 < h) {B : Entries} (hB : KeatingKeles.InBox B)
    {m : ℕ} (he : Extreme (h := h) B m) (j k : ℕ) (hj : j+k=m) :
    best h k (masses h B j) (1,0) = best h m (1,0) (1,0) := by
  apply le_antisymm (hj ▸ prefix_bound hh.le hB j k)
  obtain ⟨hl,hu⟩ := increment_bounds hh.le hB m
  have hb := best_bound hh.le hB j k
  rw [hj] at hb
  change max (dot _ _) (dot _ _) ≤ _ at hb
  change score (masses h B m) (1,0) ≤ _ at hb
  rw [score_axis] at hb
  have hc := abs_le.mpr ⟨(neg_le_neg (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hb) hh.le)).trans hl,
    hu.trans (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hb) hh.le)⟩
  rw [show |coeff h B (m+1)| = _ from he] at hc
  exact (mul_le_mul_iff_right₀ hh).mp hc

private theorem no_lazy {h : ℝ} (k : ℕ) {u v : V} {a M : ℝ} (ha : 0 ≤ a) (hb : a < 1)
    (hu : best h k u (1,0) < M) (hv : best h k v (1,0) ≤ M) :
    best h k (mix u v a) (1,0) < M := by
  apply (best_convex h k u v _ ha hb.le).trans_lt
  nlinarith [mul_pos (sub_pos.mpr hb) (sub_pos.mpr hu),mul_nonneg ha (sub_nonneg.mpr hv)]

theorem saturated {h : ℝ} (hh : 0 < h) {B : Entries} (hB : KeatingKeles.InBox B)
    {m : ℕ} (hm : 2 ≤ m) (he : Extreme (h := h) B m) {j : ℕ} (hj : j < m) :
    coeff h B (j+1) ≠ 0 ∧ (0 ≤ coeff h B (j+1) →
      coeff h B (j+1) = h*(masses h B j).2) ∧ (coeff h B (j+1) ≤ 0 →
      coeff h B (j+1) = -(h*(masses h B j).1)) := by
  let k := m-(j+1)
  have hk : j+1+k=m := by dsimp [k]; omega
  have hjk : j+k=m-1 := by omega
  let u := masses h B j
  let M := best h m (1,0) (1,0)
  have hu : best h k u (1,0) < M := by
    apply (prefix_bound hh.le hB j k).trans_lt
    convert strictly_increasing hh (m-2) using 2 <;> omega
  have hw := every_prefix hh hB he (j+1) k hk
  have hv (b : Bool) : best h k (move h b u) (1,0) ≤ M := by
    apply (move_le _ _ _ _ _).trans
    simpa only [show j+(k+1)=m by omega] using prefix_bound hh.le hB j (k+1)
  obtain ⟨hl,hr⟩ := increment_bounds hh.le hB j
  let z := coeff h B (j+1)
  change -(h*u.1) ≤ z at hl
  change z ≤ h*u.2 at hr
  rw [mass_next] at hw
  change best h k (u.1+max z 0,u.2+max (-z) 0) (1,0) = M at hw
  have hn : z ≠ 0 := by
    intro hz
    simp [hz] at hw
    exact hu.ne hw
  refine ⟨hn,?_,?_⟩
  · intro hz
    change z = h*u.2
    by_contra! H
    have hlt := lt_of_le_of_ne hr H
    have hp : 0 < h*u.2 := lt_of_le_of_lt hz hlt
    have hne : u.2 ≠ 0 := by intro heq; simp [heq] at hp
    have hmix : mix u (move h true u) (z/(h*u.2)) = (u.1+z,u.2) := by
      ext <;> simp [mix,move,leftS] <;> field_simp [hne,hh.ne'] <;> ring
    have hlazy := no_lazy k (div_nonneg hz hp.le) ((div_lt_one hp).mpr hlt) hu (hv true)
    rw [hmix] at hlazy
    rw [max_eq_left hz,max_eq_right (neg_nonpos.mpr hz),add_zero] at hw
    exact hlazy.ne hw
  · intro hz
    change z = -(h*u.1)
    by_contra! H
    have hlt : -z < h*u.1 := by grind
    have hp : 0 < h*u.1 := by linarith
    have hne : u.1 ≠ 0 := by intro heq; simp [heq] at hp
    have hmix : mix u (move h false u) (-z/(h*u.1)) = (u.1,u.2+ -z) := by
      ext <;> simp [mix,move,rightS] <;> field_simp [hne,hh.ne'] <;> ring
    have hlazy := no_lazy k (div_nonneg (neg_nonneg.mpr hz) hp.le) ((div_lt_one hp).mpr hlt) hu (hv false)
    rw [hmix] at hlazy
    rw [max_eq_right hz,max_eq_left (neg_nonneg.mpr hz),add_zero] at hw
    exact hlazy.ne hw

end HessenbergTransitions
