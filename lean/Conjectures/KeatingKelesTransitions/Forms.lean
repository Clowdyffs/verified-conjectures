module
public import Conjectures.KeatingKelesTransitions.Words
public import Mathlib.Data.List.Induction
@[expose] public section
namespace HessenbergTransitions

def run (h : ℝ) (w : List Bool) (x : V) := w.foldl (fun z b => move h b z) x
def value (h : ℝ) (w : List Bool) (x y : V) := dot (run h w x) y

theorem value_snoc (h : ℝ) (w : List Bool) (b : Bool) (x y : V) :
    value h (w ++ [b]) x y = value h w x (move h (!b) y) := by
  cases b <;> simp [value,run,List.foldl_append,move,leftS,rightS,dot] <;> ring

theorem move_le (h : ℝ) (k : ℕ) (b : Bool) (x y : V) :
    best h k (move h b x) y ≤ best h (k+1) x y := by
  cases b
  · exact le_max_right _ _
  · exact le_max_left _ _
theorem value_le (h : ℝ) (w : List Bool) (x y : V) : value h w x y ≤ best h w.length x y := by
  induction w generalizing x with
  | nil => exact le_max_left _ _
  | cons a l ih => exact (ih _).trans (move_le _ _ _ _ _)

theorem best_sort_left (h : ℝ) (n : ℕ) (x y : V) : best h n (sorted x) y = best h n x y := by
  by_cases hx : x.2 ≤ x.1
  · simp [sorted,max_eq_left hx,min_eq_right hx]
  · have hk := le_of_not_ge hx
    simp only [sorted,max_eq_right hk,min_eq_left hk]
    exact best_sw_left _ _ _ _
theorem best_sort_right (h : ℝ) (n : ℕ) (x y : V) : best h n x (sorted y) = best h n x y := by
  rw [best_symm h n x, best_sort_left, best_symm]

theorem best_same {h : ℝ} (hh : 0 < h) (n : ℕ) {x y : V} (hx : Nonneg x)
    (hs : sorted x = sorted y) : best h n x y = middleValue h n (sorted x) := by
  rw [← best_sort_left h n x,← best_sort_right h n _ y,← hs]
  apply best_middle hh
  · exact (min_le_left _ _).trans (le_max_left _ _)
  · exact le_min hx.1 hx.2

private theorem move_pos {h : ℝ} (hh : 0 ≤ h) (b : Bool) {x : V} (hx : Nonneg x) :
    Nonneg (move h b x) := by
  cases b
  · exact ⟨hx.1,add_nonneg hx.2 (mul_nonneg hh hx.1)⟩
  · exact ⟨add_nonneg hx.1 (mul_nonneg hh hx.2),hx.2⟩

theorem sort_good (h : ℝ) {b : Bool} {x : V} (hg : Greedy b x) :
    sorted (move h b x) = grow h (sorted x) := by
  cases b
  · change x.2 ≤ x.1 at hg
    simp [sorted,grow,move,rightS,max_eq_left hg,min_eq_right hg]
  · change x.1 ≤ x.2 at hg
    simp [sorted,grow,move,leftS,max_eq_right hg,min_eq_left hg,max_comm,min_comm]

private theorem first_good {h : ℝ} (hh : 0 < h) (n : ℕ) {b : Bool} {x y : V}
    (hx : Nonneg x) (hs : sorted x = sorted y)
    (hw : best h (n+2) x y ≤ best h (n+1) (move h b x) y) : Greedy b x := by
  rw [← best_sort_right _ _ _ y,← best_sort_right _ _ _ y,← hs,best_sort_right,best_sort_right] at hw
  cases b
  · by_contra! H
    have hy : x.1 < x.2 := lt_of_not_ge H
    have hb := bad_lt hh n (x := sw x) hy hx.1
    change best h (n+1) (sw (rightS h x)) (sw x) < best h (n+2) (sw x) (sw x) at hb
    rw [best_sw_left,best_sw_right,best_sw_left,best_sw_right] at hb
    exact hb.not_ge hw
  · by_contra! H
    exact (bad_lt hh n (x := x) (lt_of_not_ge H) hx.2).not_ge hw

theorem form_iff {h : ℝ} (hh : 0 < h) (w : List Bool) {x y : V}
    (hx : Nonneg x) (hy : Nonneg y) (hs : sorted x = sorted y) :
    Form h w x y ↔ value h w x y = best h w.length x y := by
  induction w using List.bidirectionalRecOn generalizing x y with
  | H0 =>
    simp only [Form,List.bidirectionalRec_nil,List.length_nil,best_same hh 0 hx hs]
    rfl
  | H1 a =>
    simp only [Form,List.bidirectionalRec_singleton,List.length_singleton,best_same hh 1 hx hs]
    rfl
  | Hn a w b ih =>
    simp only [Form,List.bidirectionalRec_cons_append]
    change (Greedy a x ∧ Greedy (!b) y ∧ Form h w (move h a x) (move h (!b) y)) ↔ _
    rw [show value h (a :: (w ++ [b])) x y = value h w (move h a x) (move h (!b) y)
      from value_snoc h w b _ _]
    simp only [List.length_cons,List.length_append]
    change _ ↔ value h w _ _ = best h (w.length+2) x y
    have local_eq (ha : Greedy a x) (hb : Greedy (!b) y) :
        best h (w.length+2) x y = best h w.length (move h a x) (move h (!b) y) := by
      rw [best_same hh _ hx hs,middleValue,best_same hh _ (move_pos hh.le _ hx)
        ((sort_good h ha).trans ((congrArg (grow h) hs).trans (sort_good h hb).symm)),sort_good h ha]
    have lep := value_le h w (move h a x) (move h (!b) y)
    constructor
    · rintro ⟨ha,hb,hi⟩
      rw [local_eq ha hb]
      exact (ih (move_pos hh.le _ hx) (move_pos hh.le _ hy)
        ((sort_good h ha).trans ((congrArg (grow h) hs).trans (sort_good h hb).symm))).mp hi
    · intro he
      have hboth := he.ge.trans lep
      have hr := move_le h w.length (!b) y (move h a x)
      rw [best_symm h w.length,best_symm h (w.length+1)] at hr
      have ha := first_good hh w.length hx hs (hboth.trans hr)
      have hl := move_le h w.length a x (move h (!b) y)
      have hlast := hboth.trans hl
      rw [best_symm h (w.length+2),best_symm h (w.length+1)] at hlast
      have hb := first_good hh w.length hy hs.symm hlast
      refine ⟨ha,hb,(ih (move_pos hh.le _ hx) (move_pos hh.le _ hy)
        ((sort_good h ha).trans ((congrArg (grow h) hs).trans (sort_good h hb).symm))).mpr ?_⟩
      exact he.trans (local_eq ha hb)
end HessenbergTransitions
