module
public import Conjectures.KeatingKeles.Masses
public import Conjectures.KeatingKelesTransitions.Words
@[expose] public section
namespace HessenbergTransitions
open Finset
abbrev Entries := KeatingKeles.Entries
def scaled (h : ℝ) (B : Entries) : Entries := fun i j => 2*h*B i j
noncomputable def coeff (h : ℝ) (B : Entries) := KeatingKeles.coeff (scaled h B)
noncomputable def masses (h : ℝ) (B : Entries) (k : ℕ) : V :=
  (KeatingKeles.posMass (scaled h B) k, KeatingKeles.negMass (scaled h B) k)
noncomputable def matrix (r : ℝ) (B : Entries) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (r/2) • KeatingKeles.hess (scaled r⁻¹ B) n

theorem coeff_next (h : ℝ) (B : Entries) (k : ℕ) :
    coeff h B (k+1) = -h*(∑ i ∈ range (k+1), coeff h B i * B i k) := by
  unfold coeff
  rw [KeatingKeles.coeff_succ,mul_sum]
  simp only [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib, scaled]
  apply sum_congr rfl
  intro i hi
  ring

theorem matrix_entry {r : ℝ} (hr : 0 < r) (B : Entries) {n : ℕ} (i j : Fin n) :
    matrix r B n i j = if i.val ≤ j.val then B i j else if i.val = j.val+1 then r else 0 := by
  simp only [matrix,KeatingKeles.hess,KeatingKeles.hEntry,Matrix.smul_apply,smul_eq_mul,scaled]
  split
  · field_simp
  · split <;> ring

theorem matrix_admissible {r : ℝ} (hr : 0 < r) {B : Entries} (hB : KeatingKeles.InBox B) (n : ℕ) :
    Admissible r (matrix r B n) := by
  intro i j
  rw [matrix_entry hr]
  split_ifs with h k
  · exact ⟨fun _ => hB _ _ h,by omega,by omega⟩
  · exact ⟨by omega,fun _ => rfl,by omega⟩
  · exact ⟨by omega,by omega,fun _ => rfl⟩

theorem realize {r : ℝ} (hr : 0 < r) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Admissible r A) : ∃ B, KeatingKeles.InBox B ∧ A = matrix r B n := by
  let B : Entries := fun i j => if hi : i < n then if hj : j < n then A ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0
  refine ⟨B,?_,?_⟩
  · intro i j h
    dsimp [B]
    split <;> try split
    · exact (hA _ _).1 h
    all_goals norm_num
  · ext i j
    obtain ⟨_,hs,hz⟩ := hA i j
    rw [matrix_entry hr]
    split_ifs with hu he
    · simp [B]
    · exact hs he
    · exact hz (by omega)

theorem det_coeff {r : ℝ} (hr : 0 < r) (B : Entries) (m : ℕ) :
    |(matrix r B (m+1)).det| = r^(m+1)*|coeff r⁻¹ B (m+1)| := by
  rw [matrix,Matrix.det_smul,abs_mul,KeatingKeles.abs_det,abs_pow,abs_of_nonneg (by positivity : 0 ≤ r/2)]
  simp only [Fintype.card_fin,coeff]
  rw [← mul_assoc,← mul_pow]
  ring_nf

theorem masses_zero (h : ℝ) (B : Entries) : masses h B 0 = (1,0) := by
  norm_num [masses,KeatingKeles.posMass,KeatingKeles.negMass]
theorem mass_next (h : ℝ) (B : Entries) (j : ℕ) :
    masses h B (j+1) = ((masses h B j).1+max (coeff h B (j+1)) 0,
      (masses h B j).2+max (-coeff h B (j+1)) 0) := by
  exact Prod.ext (KeatingKeles.pos_succ _ _) (KeatingKeles.neg_succ _ _)

theorem mass_nonneg (h : ℝ) (B : Entries) (j : ℕ) : Nonneg (masses h B j) := by
  simp only [Nonneg,masses,KeatingKeles.posMass,KeatingKeles.negMass]
  constructor <;> apply sum_nonneg <;> intro i hi <;> exact le_max_right _ _

theorem increment_bounds {h : ℝ} (hh : 0 ≤ h) {B : Entries} (hB : KeatingKeles.InBox B) (j : ℕ) :
    -(h*(masses h B j).1) ≤ coeff h B (j+1) ∧ coeff h B (j+1) ≤ h*(masses h B j).2 := by
  have term (i : ℕ) (hi : i ∈ range (j+1)) :
      -max (-coeff h B i) 0 ≤ coeff h B i * B i j ∧ coeff h B i * B i j ≤ max (coeff h B i) 0 := by
    obtain ⟨hl,hu⟩ := hB i j (by simpa using hi)
    by_cases hc : 0 ≤ coeff h B i
    · simp only [max_eq_left hc,max_eq_right (neg_nonpos.mpr hc),neg_zero]
      exact ⟨mul_nonneg hc hl, by simpa using mul_le_mul_of_nonneg_left hu hc⟩
    · have hc' := le_of_not_ge hc
      simp only [max_eq_right hc',max_eq_left (neg_nonneg.mpr hc'),neg_neg]
      exact ⟨by simpa using mul_le_mul_of_nonpos_left hu hc',mul_nonpos_of_nonpos_of_nonneg hc' hl⟩
  have hu := sum_le_sum fun i hi => (term i hi).2
  have hl := sum_le_sum fun i hi => (term i hi).1
  rw [sum_neg_distrib] at hl
  rw [coeff_next]
  exact ⟨by simpa [neg_mul,masses,KeatingKeles.posMass,coeff] using neg_le_neg (mul_le_mul_of_nonneg_left hu hh),
    by simpa [mul_neg,neg_mul,masses,KeatingKeles.negMass,coeff] using neg_le_neg (mul_le_mul_of_nonneg_left hl hh)⟩

theorem best_bound {h : ℝ} (hh : 0 ≤ h) {B : Entries} (hB : KeatingKeles.InBox B)
    (j k : ℕ) : best h 0 (masses h B (j+k)) (1,0) ≤ best h k (masses h B j) (1,0) := by
  induction k generalizing j with
  | zero => exact le_rfl
  | succ k ih =>
    rw [show j+(k+1)=j+1+k by omega]
    apply (ih (j+1)).trans
    have hy : Nonneg ((1,0) : V) := ⟨zero_le_one,le_refl _⟩
    obtain ⟨hl,hu⟩ := increment_bounds hh hB j
    rw [mass_next]
    by_cases hc : 0 ≤ coeff h B (j+1)
    · rw [max_eq_left hc,max_eq_right (neg_nonpos.mpr hc),add_zero]
      apply le_trans _ (le_max_left _ _)
      exact best_mono hh k (x' := leftS h (masses h B j)) hy (add_le_add_right hu _) le_rfl
    · have hc' := le_of_not_ge hc
      rw [max_eq_right hc',max_eq_left (neg_nonneg.mpr hc'),add_zero]
      apply le_trans _ (le_max_right _ _)
      exact best_mono hh k (x' := rightS h (masses h B j)) hy le_rfl
        (add_le_add_right (show -coeff h B (j+1) ≤ h*(masses h B j).1 by linarith) _)
end HessenbergTransitions
