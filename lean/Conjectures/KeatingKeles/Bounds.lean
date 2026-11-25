module

public import Mathlib.Tactic

@[expose] public section

namespace KeatingKeles

/-- The first coordinate is the mass most recently increased in the middle
alternating segment.  The segment starts after two equal negative increments. -/
noncomputable def middle : ℕ → ℝ × ℝ
  | 0 => (1, 1)
  | k+1 => ((middle k).2 + (middle k).1/2, (middle k).1)

theorem middle_range (k : ℕ) :
    0 ≤ (middle k).2 ∧ (middle k).2 ≤ (middle k).1 ∧ (middle k).1 ≤ 2*(middle k).2 := by
  induction k with
  | zero => norm_num [middle]
  | succ k ih =>
    simp only [middle]
    obtain ⟨_, _, _⟩ := ih
    exact ⟨by linarith, by linarith, by linarith⟩

def Step (p q u v : ℝ) : Prop :=
  (u ≤ p + q/2 ∧ v ≤ q) ∨ (u ≤ p ∧ v ≤ q + p/2)

def Envelope (a b p q : ℝ) : Prop :=
  p ≤ a+b/2 ∧ q ≤ a+b/2 ∧ p+q/2 ≤ a+b ∧ q+p/2 ≤ a+b ∧ p+q ≤ 3*a/2+b

theorem envelope_step {a b p q u v : ℝ} (hba : b ≤ a) (hab : a ≤ 2*b)
    (h : Envelope a b p q) (s : Step p q u v) :
    Envelope (b+a/2) a u v := by
  obtain ⟨_, _, _, _, _⟩ := h
  rcases s with ⟨_, _⟩ | ⟨_, _⟩ <;>
    unfold Envelope <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem envelope_three {p q r s u v : ℝ}
    (h₁ : Step 1 0 p q) (h₂ : Step p q r s) (h₃ : Step r s u v) :
    Envelope 1 1 u v := by
  rcases h₁ with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases h₂ with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases h₃ with ⟨_, _⟩ | ⟨_, _⟩ <;>
    unfold Envelope <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem envelope_all (p q : ℕ → ℝ) (hp : p 0 = 1) (hq : q 0 = 0)
    (step : ∀ j, Step (p j) (q j) (p (j+1)) (q (j+1))) (k : ℕ) :
    Envelope (middle k).1 (middle k).2 (p (k+3)) (q (k+3)) := by
  induction k with
  | zero =>
    exact envelope_three (hp ▸ hq ▸ step 0) (step 1) (step 2)
  | succ k ih =>
    exact envelope_step (middle_range k).2.1 (middle_range k).2.2 ih (step (k+3))

end KeatingKeles
