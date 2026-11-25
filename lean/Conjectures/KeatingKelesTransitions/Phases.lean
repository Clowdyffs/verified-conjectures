module
public import Conjectures.KeatingKelesTransitions.Forms
@[expose] public section
namespace HessenbergTransitions

private theorem middle_sort_zero (x : V) : middleValue 0 0 (sorted x) = x.1^2+x.2^2 := by
  by_cases hx : x.2 ≤ x.1
  · simp [middleValue,sorted,max_eq_left hx,min_eq_right hx]
  · have hy := le_of_not_ge hx
    simp [middleValue,sorted,max_eq_right hy,min_eq_left hy,add_comm]

/-- Peel k updates on each side while the second coordinate stays below one. -/
theorem initial_runs {h : ℝ} (hh : 0 ≤ h) (k j : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (hb1 : b ≤ 1) (hk : b+(k:ℝ)*h ≤ 1) :
    middleValue h (j+2*k) (1,b) = middleValue h j (1,b+k*h) := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
    rw [show j+2*(k+1)=(j+2*k)+2 by omega,middleValue]
    have hb' : b+h ≤ 1 := by
      push_cast at hk
      nlinarith [mul_nonneg (Nat.cast_nonneg k) hh]
    have hg : grow h (1,b) = (1,b+h) := by simp [grow,sorted,max_eq_left hb',min_eq_right hb']
    rw [hg,ih (add_nonneg hb hh) hb' (by push_cast at hk; linarith)]
    congr 2
    push_cast
    ring

/-- The next pair has crossed the diagonal and must alternate thereafter. -/
theorem balanced_step {h a b : ℝ} (hh : 0 < h) (hb : 0 < b) (hs : b ≤ a)
    (hg : a ≤ (1+h)*b) :
    a < b+h*a ∧ b+h*a ≤ (1+h)*a ∧ grow h (a,b) = (b+h*a,a) := by
  have ht : a < b+h*a := by
    by_cases hd : a=b
    · subst a; nlinarith [mul_pos hh hb]
    · nlinarith [mul_pos hh (sub_pos.mpr (lt_of_le_of_ne hs (Ne.symm hd)))]
  exact ⟨ht,by nlinarith,by simp [grow,sorted,max_eq_right ht.le,min_eq_left ht.le]⟩

/-- On the closed strip k ≤ r ≤ k+1, the first k+1 noncentral steps
at each end prepare the alternating middle. Includes both boundary ties. -/
theorem strip {h : ℝ} (hh : 0 < h) (k j : ℕ) (hk : (k:ℝ)*h ≤ 1)
    (hc : 1 ≤ ((k:ℝ)+1)*h) :
    middleValue h (j+2*(k+1)) (1,0) = middleValue h j (((k:ℝ)+1)*h,1) := by
  rw [show j+2*(k+1)=(j+2)+2*k by omega,
    initial_runs hh.le k (j+2) (b:=0) (by norm_num) (by norm_num) (by simpa using hk)]
  simp only [zero_add,middleValue]
  congr 1
  have hp : 1 ≤ (k:ℝ)*h+h := by nlinarith
  simp [grow,sorted,max_eq_right hp,min_eq_left hp,add_mul]

private theorem pad_one (h : ℝ) (x : V) (b : Bool) (n : ℕ) :
    best h n (move h b x) (move h b x) ≤ best h (n+2) x x := by
  apply le_trans _ (move_le h (n+1) b x x)
  rw [best_symm h (n+1)]
  exact move_le _ _ _ _ _

private theorem pad_right (h : ℝ) (k n : ℕ) (b : ℝ) :
    best h n (1,b+k*h) (1,b+k*h) ≤ best h (n+2*k) (1,b) (1,b) := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
    have hp := pad_one h (1,b) false (n+2*k)
    have hg : move h false (1,b) = (1,b+h) := by simp [move,rightS]
    rw [hg] at hp
    convert (ih (b+h)).trans hp using 2 <;> push_cast <;> congr 1 <;> ring

/-- For odd matrix order n=2k+3 the large-ratio formula is valid exactly
when k*h ≤ 1. Comparison with a single explicit competitor proves strictness. -/
theorem even_steps_tail {h : ℝ} (hh : 0 < h) (k : ℕ) :
    middleValue h (2*(k+1)) (1,0) = 1+((k:ℝ)+1)^2*h^2 ↔ (k:ℝ)*h ≤ 1 := by
  constructor
  · contrapose!
    intro hk
    have hf := pad_right h k 2 0
    rw [zero_add] at hf
    have hp := pad_one h (1,(k:ℝ)*h) true 0
    have hv : best h 0 (move h true (1,(k:ℝ)*h)) (move h true (1,(k:ℝ)*h)) ≥
        (1+h*((k:ℝ)*h))^2 + ((k:ℝ)*h)^2 := by
      apply le_trans _ (le_max_left _ _)
      simp [dot,move,leftS,pow_two]
    have hz := (hv.trans hp).trans hf
    rw [best_middle hh _ _ (by norm_num) (by norm_num),show 2+2*k=2*(k+1) by omega] at hz
    have hpos := mul_pos (sq_pos_of_pos hh) (mul_pos (sub_pos.mpr hk) (show 0 < (k:ℝ)*h+1 by linarith))
    nlinarith
  · intro hk
    rw [show 2*(k+1)=2+2*k by omega,initial_runs hh.le k 2 (b:=0) (by norm_num) (by norm_num)
      (by simpa using hk)]
    simp only [zero_add,middleValue,grow,mul_one]
    have he := middle_sort_zero ((1,(k:ℝ)*h+h) : V)
    simp only [middleValue] at he
    rw [he]
    ring

/-- For even matrix order n=2k+2 and r≥k, the only two values in the
envelope are the single run and balanced two-run values. -/
theorem odd_steps_tail {h : ℝ} (hh : 0 < h) (k : ℕ) (hk : (k:ℝ)*h ≤ 1) :
    middleValue h (1+2*k) (1,0) = max (1+(k:ℝ)*(k+1)*h^2) ((2*(k:ℝ)+1)*h) := by
  rw [initial_runs hh.le k 1 (b:=0) (by norm_num) (by norm_num) (by simpa using hk)]
  simp only [zero_add,middleValue]
  congr 1 <;> ring

theorem odd_difference (h k : ℝ) :
    (1+k*(k+1)*h^2)-(2*k+1)*h = (1-k*h)*(1-(k+1)*h) := by ring

end HessenbergTransitions
