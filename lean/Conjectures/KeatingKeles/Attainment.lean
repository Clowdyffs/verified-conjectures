module

public import Conjectures.KeatingKeles.Colors

@[expose] public section

namespace KeatingKeles

def oddBit (j : ℕ) : Bool := decide (j % 2 = 1)

/-- The two initial increments are negative. The middle segment alternates.
The penultimate increment repeats its predecessor and the last reverses it. -/
def shade (k i : ℕ) : Bool :=
  if i = 0 then true else if i = 1 then false else
  if i = k+3 then oddBit k else if i = k+4 then !(oddBit k) else oddBit i

private theorem oddFlip (j : ℕ) : oddBit (j+1) = !(oddBit j) := by
  by_cases h : j % 2 = 1
  · simp [oddBit, h, show (j+1)%2 ≠ 1 by omega]
  · simp [oddBit, h, show (j+1)%2 = 1 by omega]

private theorem shade_mid (k j : ℕ) (hj : j ≤ k) : shade k (j+2) = oddBit j := by
  simp [shade, oddBit, show j ≠ k+1 by omega, show j ≠ k+2 by omega]

set_option maxHeartbeats 3000000 in
private theorem rc_entry_colored (k i j : ℕ) (hi : i < k+4) (hj : j < k+4) :
    rcEntry (k+4) i j = hEntry (colored (shade k)) i j := by
  have rows : i = 0 ∨ i = 1 ∨ i = k+3 ∨
      (2 ≤ i ∧ i < k+3) := by omega
  have cols : j = 0 ∨ j = k+2 ∨ j = k+3 ∨
      (1 ≤ j ∧ j < k+2) := by omega
  rcases rows with rfl | rfl | rfl | ⟨il, iu⟩ <;>
    rcases cols with rfl | rfl | rfl | ⟨jl, ju⟩ <;>
    simp (disch := omega) [rcEntry, original, hEntry, colored, shade, oddBit] <;>
    split_ifs
  all_goals try rfl
  all_goals exfalso
  all_goals try omega
  all_goals try grind




theorem comparator_eq (k : ℕ) : comparator (k+4) = hess (colored (shade k)) (k+4) := by
  ext i j
  exact rc_entry_colored k i j i.isLt j.isLt

theorem comparator_coeff (k : ℕ) :
    |coeff (colored (shade k)) (k+4)| = ((middle k).1+(middle k).2/2)/2 := by
  let c := shade k
  let B := colored c
  have hc : c 0 = true := by simp [c, shade]
  have hs := color_step c hc
  have hbase : mass B false 2 = 1 ∧ mass B true 2 = 1 := by
    have z₁ := hs 0 false (by simp [c, shade])
    have z₂ := hs 1 false (by simp [c, shade, oddBit])
    have t : mass B true 0 = 1 := by norm_num [mass, posMass]
    have f : mass B false 0 = 0 := by norm_num [mass, negMass]
    change mass B false 1 = _ ∧ mass B true 1 = _ ∧ _ at z₁
    change mass B false 2 = _ ∧ mass B true 2 = _ ∧ _ at z₂
    simp only [Bool.not_false] at z₁ z₂
    change mass B false 1 = mass B false 0 + mass B true 0/2 ∧
      mass B true 1 = mass B true 0 ∧ _ at z₁
    change mass B false 2 = mass B false 1 + mass B true 1/2 ∧
      mass B true 2 = mass B true 1 ∧ _ at z₂
    rw [z₂.1, z₂.2.1, z₁.1, z₁.2.1, t, f]
    norm_num
  have hm (j : ℕ) (hj : j ≤ k) :
      mass B (oddBit j) (j+2) = (middle j).1 ∧
      mass B (!(oddBit j)) (j+2) = (middle j).2 := by
    induction j with
    | zero => exact hbase
    | succ j ih =>
      obtain ⟨h₁,h₂⟩ := ih (by omega)
      have s := hs (j+2) (oddBit (j+1)) (shade_mid k (j+1) hj)
      rw [oddFlip, Bool.not_not] at s ⊢
      change mass B (!(oddBit j)) (j+3) = _ ∧ mass B (oddBit j) (j+3) = _ ∧ _ at s
      exact ⟨s.1.trans (by change mass B (!(oddBit j)) (j+2) + mass B (oddBit j) (j+2)/2 = _; rw [h₁,h₂]; rfl),
        s.2.1.trans h₁⟩
  obtain ⟨h₁,h₂⟩ := hm k le_rfl
  have pen := (hs (k+2) (oddBit k) (by simp [c, shade])).1
  have last := (hs (k+3) (!(oddBit k)) (by simp [c, shade])).2.2
  rw [Bool.not_not] at last
  change mass B (oddBit k) (k+3) = _ at pen
  change |coeff B (k+4)| = mass B (oddBit k) (k+3)/2 at last
  change |coeff B (k+4)| = _
  rw [last, pen]
  change (mass B (oddBit k) (k+2) + mass B (!(oddBit k)) (k+2)/2)/2 = _
  rw [h₁,h₂]

end KeatingKeles
