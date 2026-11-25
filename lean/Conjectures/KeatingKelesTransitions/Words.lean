module
public import Conjectures.KeatingKelesTransitions.Greedy
@[expose] public section
namespace HessenbergTransitions

def play (h : ℝ) : ℕ → (ℕ → Bool) → V → V
  | 0, _, x => x
  | n+1, f, x => play h n (fun i => f (i+1)) (move h (f 0) x)

theorem play_congr (h : ℝ) (m : ℕ) {f g : ℕ → Bool} (he : ∀ i < m, f i = g i) (x : V) :
    play h m f x = play h m g x := by
  induction m generalizing f g x with
  | zero => rfl
  | succ m ih =>
    simp only [play,he 0 (by omega)]
    exact ih (fun i hi => he _ (by omega)) _

theorem best_witness (h : ℝ) (m : ℕ) (x y : V) :
    ∃ f : ℕ → Bool, best h m x y = score (play h m f x) y := by
  induction m generalizing x with
  | zero => exact ⟨fun _ => false,rfl⟩
  | succ m ih =>
    by_cases hc : best h m (rightS h x) y ≤ best h m (leftS h x) y
    · obtain ⟨f,hf⟩ := ih (leftS h x)
      refine ⟨(fun | 0 => true | i+1 => f i),?_⟩
      simpa [best,play,move,max_eq_left hc] using hf
    · obtain ⟨f,hf⟩ := ih (rightS h x)
      refine ⟨(fun | 0 => false | i+1 => f i),?_⟩
      simpa [best,play,move,max_eq_right (le_of_not_ge hc)] using hf

theorem best_mono {h : ℝ} (hh : 0 ≤ h) (m : ℕ) {x x' y : V} (hy : Nonneg y)
    (ha : x.1 ≤ x'.1) (hb : x.2 ≤ x'.2) : best h m x y ≤ best h m x' y := by
  induction m generalizing x x' with
  | zero =>
    unfold best score dot sw
    exact max_le_max (add_le_add (mul_le_mul_of_nonneg_right ha hy.1)
      (mul_le_mul_of_nonneg_right hb hy.2)) (add_le_add (mul_le_mul_of_nonneg_right ha hy.2)
      (mul_le_mul_of_nonneg_right hb hy.1))
  | succ m ih =>
    exact max_le_max (ih (add_le_add ha (mul_le_mul_of_nonneg_left hb hh)) hb)
      (ih ha (add_le_add hb (mul_le_mul_of_nonneg_left ha hh)))

end HessenbergTransitions
