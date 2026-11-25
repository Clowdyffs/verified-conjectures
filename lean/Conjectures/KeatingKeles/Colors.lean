module

public import Conjectures.KeatingKeles.Masses

@[expose] public section

namespace KeatingKeles
open Finset

/-- An upper entry is one exactly when its two endpoint colors differ. -/
def colored (c : ℕ → Bool) : Entries := fun i j => if c i = c (j+1) then 0 else 1

noncomputable def mass (B : Entries) (b : Bool) (j : ℕ) : ℝ :=
  if b then posMass B j else negMass B j

theorem mass_nonneg (B : Entries) (b : Bool) (j : ℕ) : 0 ≤ mass B b j := by
  cases b <;> simp only [mass, Bool.false_eq_true, ite_false, ite_true, posMass, negMass] <;>
    apply sum_nonneg <;> intro i _ <;> exact le_max_right _ _

private def Signed (b : Bool) (x : ℝ) : Prop := if b then 0 ≤ x else x ≤ 0

private theorem color_increment_aux (c : ℕ → Bool) (j : ℕ)
    (hs : ∀ i ≤ j, Signed (c i) (coeff (colored c) i)) :
    coeff (colored c) (j+1) = if c (j+1) then negMass (colored c) j/2
      else -(posMass (colored c) j)/2 := by
  rw [coeff_succ]
  cases h : c (j+1)
  · simp only [Bool.false_eq_true, ite_false, posMass]
    congr 2
    apply sum_congr rfl
    intro i hi
    have hsign := hs i (Nat.le_of_lt_succ (mem_range.mp hi))
    cases hi' : c i <;> simp [Signed, hi'] at hsign <;>
      simp [colored, hi', h, hsign]
  · simp only [ite_true, negMass]
    rw [← sum_neg_distrib]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hsign := hs i (Nat.le_of_lt_succ (mem_range.mp hi))
    cases hi' : c i <;> simp [Signed, hi'] at hsign <;>
      simp [colored, hi', h, hsign]

theorem color_increment (c : ℕ → Bool) (hc : c 0 = true) (j : ℕ) :
    coeff (colored c) (j+1) = if c (j+1) then negMass (colored c) j/2
      else -(posMass (colored c) j)/2 := by
  have hs (k : ℕ) : Signed (c k) (coeff (colored c) k) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero => simp [Signed, hc]
      | succ j =>
        rw [color_increment_aux c j (fun i hi => ih i (by omega))]
        cases h : c (j+1)
        · have := mass_nonneg (colored c) true j
          simp [mass, Signed] at this ⊢
          linarith
        · have := mass_nonneg (colored c) false j
          simp [mass, Signed] at this ⊢
          linarith
  exact color_increment_aux c j fun i _ => hs i

theorem color_step (c : ℕ → Bool) (hc : c 0 = true) (j : ℕ) (b : Bool)
    (hb : c (j+1) = b) :
    mass (colored c) b (j+1) = mass (colored c) b j + mass (colored c) (!b) j/2 ∧
    mass (colored c) (!b) (j+1) = mass (colored c) (!b) j ∧
    |coeff (colored c) (j+1)| = mass (colored c) (!b) j/2 := by
  have hpos : 0 ≤ posMass (colored c) j := mass_nonneg _ true _
  have hneg : 0 ≤ negMass (colored c) j := mass_nonneg _ false _
  cases b <;> simp [mass, pos_succ, neg_succ, color_increment c hc j, hb,
    hpos, hneg, abs_of_nonneg, abs_of_nonpos,
    div_nonneg, div_nonpos_of_nonpos_of_nonneg]
  ring

end KeatingKeles
