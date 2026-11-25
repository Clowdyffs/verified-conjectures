module

public import Conjectures.KeatingKeles.Attainment

@[expose] public section

namespace KeatingKeles

private theorem hess_admissible (B : Entries) (hB : InBox B) (n : ℕ) :
    Admissible (hess B n) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simpa [hess, hEntry, h] using hB i j h
  · simp [hess, hEntry, h]
  · simp [hess, hEntry, show ¬ i.val ≤ j.val by omega, show i.val ≠ j.val+1 by omega]

private theorem realize {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : Admissible A) :
    ∃ B, InBox B ∧ A = hess B n := by
  let B : Entries := fun i j => if hi : i < n then if hj : j < n then A ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0
  refine ⟨B, ?_, ?_⟩
  · intro i j h
    dsimp [B]
    split <;> try split
    · exact (hA _ _).1 h
    all_goals norm_num
  · ext i j
    obtain ⟨_, hsub, hzero⟩ := hA i j
    by_cases hu : i.val ≤ j.val
    · simp [hess, hEntry, hu, B]
    · by_cases hs : i.val = j.val+1
      · simpa [hess, hEntry, hu, hs] using hsub hs
      · simpa [hess, hEntry, hu, hs] using hzero (by omega)

theorem question_two : QuestionTwo := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
  rw [comparator_eq]
  constructor
  · apply hess_admissible
    intro i j _
    simp only [colored]
    split <;> norm_num
  · intro A hA
    obtain ⟨B,hB,rfl⟩ := realize A hA
    rw [abs_det B (k+3), abs_det _ (k+3), comparator_coeff]
    exact mul_le_mul_of_nonneg_left (coeff_bound B hB k) (by positivity)

theorem control_four : |(comparator 4).det| = 12 := by
  rw [comparator_eq 0, abs_det _ 3, comparator_coeff 0]
  norm_num [middle]

theorem control_five : |(comparator 5).det| = 32 := by
  rw [comparator_eq 1, abs_det _ 4, comparator_coeff 1]
  norm_num [middle]

theorem maximum_value (k : ℕ) :
    |(comparator (k+4)).det| = 2^(k+3)*((middle k).1+(middle k).2/2) := by
  rw [comparator_eq, abs_det _ (k+3), comparator_coeff, pow_succ]
  ring

theorem maximum_recurrence (k : ℕ) :
    |(comparator (k+6)).det| =
      |(comparator (k+5)).det| + 4*|(comparator (k+4)).det| := by
  rw [maximum_value (k+2), maximum_value (k+1), maximum_value k]
  change 2^((k+3)+2) * _ = 2^((k+3)+1) * _ + 4*(2^(k+3)*_)
  simp only [middle, pow_succ]
  ring

/-- The distinct order-four maximizer uses the color pattern +, −, −, +, −. -/
theorem order_four_tie : ∃ A : Matrix (Fin 4) (Fin 4) ℝ,
    Admissible A ∧ A ≠ comparator 4 ∧ |A.det| = 12 := by
  let B := colored (fun i => decide (i = 0 ∨ i = 3))
  refine ⟨hess B 4, hess_admissible B (fun i j _ => ?_) _, ?_, ?_⟩
  · simp only [B, colored]
    split <;> norm_num
  · intro h
    have hu := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 2) h
    norm_num [hess, hEntry, B, colored, comparator, rcEntry, original] at hu
  · rw [abs_det _ 3]
    norm_num [coeff_succ, Finset.sum_range_succ, B, colored]

end KeatingKeles
