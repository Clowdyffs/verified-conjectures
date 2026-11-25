module

public import Conjectures.KeatingKeles.Evaluation
public import Conjectures.KeatingKeles.Bounds

@[expose] public section

namespace KeatingKeles
open Finset

noncomputable def posMass (B : Entries) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k+1), max (coeff B i) 0

noncomputable def negMass (B : Entries) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k+1), max (-coeff B i) 0

def InBox (B : Entries) : Prop := ∀ i j, i ≤ j → 0 ≤ B i j ∧ B i j ≤ 1

theorem pos_succ (B : Entries) (k : ℕ) :
    posMass B (k+1) = posMass B k + max (coeff B (k+1)) 0 := by
  simp [posMass, sum_range_succ _ (k+1)]

theorem neg_succ (B : Entries) (k : ℕ) :
    negMass B (k+1) = negMass B k + max (-coeff B (k+1)) 0 := by
  simp [negMass, sum_range_succ _ (k+1)]

theorem increment_bounds (B : Entries) (hB : InBox B) (j : ℕ) :
    -(posMass B j)/2 ≤ coeff B (j+1) ∧ coeff B (j+1) ≤ negMass B j/2 := by
  have bounds (i : ℕ) (hi : i ∈ range (j+1)) :
      -(max (-coeff B i) 0) ≤ coeff B i * B i j ∧ coeff B i * B i j ≤ max (coeff B i) 0 := by
    obtain ⟨hl, hu⟩ := hB i j (Nat.le_of_lt_succ (mem_range.mp hi))
    by_cases h : 0 ≤ coeff B i
    · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      exact ⟨mul_nonneg h hl, by simpa using mul_le_mul_of_nonneg_left hu h⟩
    · have h' : coeff B i ≤ 0 := le_of_not_ge h
      simp [max_eq_right h', max_eq_left (neg_nonneg.mpr h')]
      exact ⟨by simpa using mul_le_mul_of_nonpos_left hu h', mul_nonpos_of_nonpos_of_nonneg h' hl⟩
  have hu := sum_le_sum fun i hi => (bounds i hi).2
  have hl := sum_le_sum fun i hi => (bounds i hi).1
  rw [sum_neg_distrib] at hl
  rw [coeff_succ]
  unfold posMass negMass
  constructor <;> linarith

theorem coeff_bound (B : Entries) (hB : InBox B) (k : ℕ) :
    |coeff B (k+4)| ≤ ((middle k).1+(middle k).2/2)/2 := by
  have step (j : ℕ) : Step (posMass B j) (negMass B j) (posMass B (j+1)) (negMass B (j+1)) := by
    obtain ⟨hl, hu⟩ := increment_bounds B hB j
    rw [pos_succ, neg_succ]
    by_cases h : 0 ≤ coeff B (j+1)
    · left
      simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h), hu]
    · right
      have h' : coeff B (j+1) ≤ 0 := le_of_not_ge h
      simp [max_eq_right h', max_eq_left (neg_nonneg.mpr h')]
      linarith
  have h := envelope_all _ _ (by norm_num [posMass]) (by norm_num [negMass]) step k
  obtain ⟨hp, hq, _⟩ := h
  obtain ⟨hl, hu⟩ := increment_bounds B hB (k+3)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end KeatingKeles
