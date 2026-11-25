module
public import Conjectures.KeatingKelesTransitions.Statement
public import Mathlib.Tactic
@[expose] public section
namespace HessenbergTransitions

def sw (x : V) : V := (x.2,x.1)
def Nonneg (x : V) : Prop := 0 ≤ x.1 ∧ 0 ≤ x.2
def Positive (x : V) : Prop := Nonneg x ∧ 0 < x.1+x.2
noncomputable def score (x y : V) := max (dot x y) (dot x (sw y))
noncomputable def best (h : ℝ) : ℕ → V → V → ℝ
  | 0,x,y => score x y
  | n+1,x,y => max (best h n (leftS h x) y) (best h n (rightS h x) y)

theorem best_sw_left (h : ℝ) (n : ℕ) (x y : V) : best h n (sw x) y = best h n x y := by
  induction n generalizing x with
  | zero =>
    simp only [best, score, dot, sw]
    rw [add_comm (x.2*y.1), add_comm (x.2*y.2), max_comm]
  | succ n ih =>
    change max (best h n (sw (rightS h x)) y) (best h n (sw (leftS h x)) y) = _
    rw [ih, ih, max_comm, best]

theorem best_sw_right (h : ℝ) (n : ℕ) (x y : V) : best h n x (sw y) = best h n x y := by
  induction n generalizing x with
  | zero => exact max_comm _ _
  | succ n ih => simp only [best, ih]

theorem best_right (h : ℝ) (n : ℕ) (x y : V) :
    best h (n+1) x y = max (best h n x (leftS h y)) (best h n x (rightS h y)) := by
  induction n generalizing x y with
  | zero =>
    simp only [best, score, dot, sw, leftS, rightS]
    ring_nf
    grind
  | succ n ih =>
    change max (best h (n+1) (leftS h x) y) (best h (n+1) (rightS h x) y) = _
    rw [ih, ih]
    simp only [best]
    grind

theorem best_symm (h : ℝ) (n : ℕ) (x y : V) : best h n x y = best h n y x := by
  induction n generalizing x y with
  | zero =>
    simp only [best, score, dot, sw]
    congr 1 <;> ring
  | succ n ih => rw [best, best_right h n y, ih (leftS h x) y, ih (rightS h x) y]

theorem positive_left {h : ℝ} (hh : 0 ≤ h) {x : V} (hx : Positive x) :
    Positive (leftS h x) := by
  obtain ⟨⟨hp,hq⟩,hs⟩ := hx
  exact ⟨⟨add_nonneg hp (mul_nonneg hh hq),hq⟩,by dsimp [leftS]; linarith [mul_nonneg hh hq]⟩
theorem positive_right {h : ℝ} (hh : 0 ≤ h) {x : V} (hx : Positive x) :
    Positive (rightS h x) := by
  obtain ⟨⟨hp,hq⟩,hs⟩ := hx
  exact ⟨⟨hp,add_nonneg hq (mul_nonneg hh hp)⟩,by dsimp [rightS]; linarith [mul_nonneg hh hp]⟩

private theorem score_strict {v w y : V} (hy : Positive y)
    (hs : v.1+v.2 < w.1+w.2) (h₁ : v.1 < w.1) (h₂ : v.2 < w.1) :
    score v y < score w y := by
  obtain ⟨⟨hc,hd⟩,hp⟩ := hy
  have lin {a b c d : ℝ} (hcd : d ≤ c) (hd0 : 0 ≤ d) (hc0 : 0 < c)
      (ha : a < w.1) (hsum : a+b < w.1+w.2) :
      a*c+b*d < w.1*c+w.2*d := by
    rcases hd0.eq_or_lt with hzero|hpos
    · rw [← hzero]
      simpa using mul_lt_mul_of_pos_right ha hc0
    · nlinarith [mul_pos hpos (sub_pos.mpr hsum),mul_nonneg (sub_nonneg.mpr hcd) (sub_nonneg.mpr ha.le)]
  have hs' : v.2+v.1 < w.1+w.2 := by linarith
  by_cases hc' : y.2 ≤ y.1
  · apply lt_of_lt_of_le _ (le_max_left _ _)
    apply max_lt (lin hc' hd (by linarith) h₁ hs)
    simpa only [dot,sw,add_comm] using lin hc' hd (by linarith) h₂ hs'
  · have hd' := le_of_not_ge hc'
    apply lt_of_lt_of_le _ (le_max_right _ _)
    apply max_lt _ (lin hd' hc (by linarith) h₁ hs)
    simpa only [dot,sw,add_comm] using lin hd' hc (by linarith) h₂ hs'

private theorem best_strict {h : ℝ} (hh : 0 ≤ h) (n : ℕ) {v w : V}
    (hs : v.1+v.2 < w.1+w.2) (h₁ : v.1 < w.1) (h₂ : v.2 < w.1)
    {y : V} (hy : Positive y) : best h n v y < best h n w y := by
  induction n generalizing y with
  | zero => exact score_strict hy hs h₁ h₂
  | succ n ih =>
    rw [best_right, best_right]
    exact max_lt_max (ih (positive_left hh hy)) (ih (positive_right hh hy))

theorem exchange {h : ℝ} (hh : 0 < h) (n : ℕ) {x y : V} (hx : x.2 < x.1)
    (hb : 0 ≤ x.2) (hy : Positive y) :
    best h n (rightS h (leftS h x)) y < best h n (leftS h (rightS h x)) y := by
  apply best_strict hh.le n _ _ _ hy <;> simp only [leftS,rightS]
  · nlinarith [mul_pos (sq_pos_of_pos hh) (sub_pos.mpr hx)]
  · nlinarith [mul_pos (sq_pos_of_pos hh) (show 0 < x.1 by linarith)]
  · have hc : 0 < 1-h+h^2 := by nlinarith [sq_nonneg (h-1/2)]
    nlinarith [mul_pos hc (sub_pos.mpr hx)]
end HessenbergTransitions
