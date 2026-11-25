module
public import Conjectures.KeatingKelesTransitions.Shears
@[expose] public section
namespace HessenbergTransitions

def lineS (h : ℝ) (j : ℕ) (x : V) : V := (x.1+j*h*x.2,x.2)

private theorem line_cons (h : ℝ) (n : ℕ) (x : V) :
    lineS h n (leftS h x) = lineS h (n+1) x := by
  ext <;> simp [lineS,leftS]
  ring

/-- An optimal word beginning by raising a strictly larger coordinate
can only continue in the same direction. -/
theorem constant_of_bad {h : ℝ} (hh : 0 < h) (n : ℕ) {x y : V}
    (hx : x.2 < x.1) (hb : 0 ≤ x.2) (hy : Positive y)
    (he : best h n (leftS h x) y = best h (n+1) x y) :
    best h (n+1) x y = score (lineS h (n+1) x) y := by
  induction n generalizing x with
  | zero =>
    rw [← he]
    simp [best,lineS,leftS]
  | succ n ih =>
    have hsw := exchange hh n hx hb hy
    have h1 : best h n (leftS h (rightS h x)) y ≤ best h (n+1) (rightS h x) y :=
      le_max_left _ _
    have h2 : best h (n+1) (rightS h x) y ≤ best h (n+2) x y := le_max_right _ _
    have hbad := hsw.trans_le (h1.trans h2)
    rw [← he] at hbad
    have hkeep : best h n (leftS h (leftS h x)) y = best h (n+1) (leftS h x) y := by
      rw [best] at hbad ⊢
      exact (max_eq_left (by grind)).symm
    have hlt : (leftS h x).2 < (leftS h x).1 := by
      dsimp [leftS]; linarith [mul_nonneg hh.le hb]
    rw [← he, ih hlt hb hkeep, line_cons]

private theorem score_aligned {x y : V} (hx : x.2 ≤ x.1) (hy : y.2 ≤ y.1) :
    score x y = dot x y := by
  apply max_eq_left
  unfold dot sw
  dsimp
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

private theorem line_le_best (h : ℝ) (n : ℕ) (x y : V) :
    score (lineS h n x) y ≤ best h n x y := by
  induction n generalizing x with
  | zero => simp [lineS,best]
  | succ n ih => rw [← line_cons]; exact (ih _).trans (le_max_left _ _)

theorem bad_lt {h : ℝ} (hh : 0 < h) (n : ℕ) {x : V} (hx : x.2 < x.1)
    (hb : 0 ≤ x.2) : best h (n+1) (leftS h x) x < best h (n+2) x x := by
  by_contra! hc
  have he := le_antisymm (show best h (n+1) (leftS h x) x ≤ best h (n+2) x x
    from le_max_left _ _) hc
  have hy : Positive x := ⟨⟨by linarith,hb⟩,by linarith⟩
  have hflat := constant_of_bad hh (n+1) hx hb hy he
  have hsort : (lineS h (n+2) x).2 ≤ (lineS h (n+2) x).1 := by
    dsimp [lineS]
    have : 0 ≤ ((n+2:ℕ):ℝ)*h*x.2 := by positivity
    linarith
  rw [score_aligned hsort hx.le] at hflat
  have hcomp : dot (lineS h (n+1) (rightS h x)) x ≤ best h (n+2) x x :=
    (le_max_left _ _ : _ ≤ score _ _).trans ((line_le_best _ _ _ _).trans (le_max_right _ _))
  rw [hflat] at hcomp
  simp only [dot,lineS,rightS,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hcomp
  have ha : 0 < x.1 := by linarith
  nlinarith [mul_pos (show 0 < (n:ℝ)+1 by positivity) (mul_pos (sq_pos_of_pos hh) (sq_pos_of_pos ha))]

private theorem best_sorted (h : ℝ) (n : ℕ) (x : V) :
    best h n (sorted x) (sorted x) = best h n x x := by
  by_cases hy : x.2 ≤ x.1
  · simp [sorted,max_eq_left hy,min_eq_right hy]
  · have hx : x.1 ≤ x.2 := by linarith
    change best h n (max _ _, min _ _) (max _ _, min _ _) = _
    rw [max_eq_right hx,min_eq_left hx]
    exact (best_sw_left h n x (sw x)).trans (best_sw_right h n x x)

theorem peel {h : ℝ} (hh : 0 < h) (n : ℕ) {x : V} (hx : x.2 ≤ x.1) (hb : 0 ≤ x.2) :
    best h (n+2) x x = best h n (grow h x) (grow h x) := by
  rw [show grow h x = sorted (rightS h x) from rfl, best_sorted]
  by_cases he : x.1 = x.2
  · have hs : leftS h x = sw (rightS h x) := by ext <;> simp [leftS,rightS,sw,he]
    rw [best,hs,best_sw_left,max_self,best_right,hs,best_sw_right,max_self]
  · have hn := bad_lt hh n (lt_of_le_of_ne hx (Ne.symm he)) hb
    have hfirst : best h (n+2) x x = best h (n+1) (rightS h x) x := by
      change best h (n+1) (leftS h x) x < max _ _ at hn
      change max _ _ = _
      grind
    have hlast : best h n (rightS h x) (leftS h x) < best h (n+1) (rightS h x) x := by
      rw [← hfirst]
      apply lt_of_le_of_lt _ hn
      rw [best_symm h n, best_right h n]
      exact le_max_right _ _
    rw [hfirst,best_right]
    rw [best_right] at hlast
    grind

theorem best_middle {h : ℝ} (hh : 0 < h) (m : ℕ) (x : V) (hx : x.2 ≤ x.1) (hb : 0 ≤ x.2) :
    best h m x x = middleValue h m x := by
  induction m using Nat.strong_induction_on generalizing x with
  | h m ih =>
    match m with
    | 0 =>
      rw [best,score_aligned hx hx,middleValue]
      simp [dot,pow_two]
    | 1 =>
      simp only [best,score,dot,sw,leftS,rightS,middleValue]
      have hlo : h*x.2^2 ≤ h*x.1^2 := by
        apply mul_le_mul_of_nonneg_left _ hh.le
        nlinarith [mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ x.1+x.2 by linarith)]
      ring_nf at hlo ⊢
      grind
    | n+2 =>
      rw [peel hh n hx hb,middleValue]
      apply ih n (by omega)
      · exact (min_le_left _ _).trans (le_max_left _ _)
      · exact le_min (by linarith) (add_nonneg hb (mul_nonneg hh.le (by linarith)))
end HessenbergTransitions
