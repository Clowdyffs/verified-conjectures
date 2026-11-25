module
public import Conjectures.KeatingKelesTransitions.Equality
public import Conjectures.KeatingKelesTransitions.Permutation
public import Conjectures.KeatingKelesTransitions.Phases
@[expose] public section
namespace HessenbergTransitions

theorem sharp_maximum : SharpMaximum := by
  intro r hr m
  have hh : 0 < r⁻¹ := inv_pos.mpr hr
  have hm := best_middle hh m ((1,0) : V) (by norm_num) (by norm_num)
  have hs : r^(m+1)*r⁻¹ = r^m := by rw [pow_succ,mul_assoc,mul_inv_cancel₀ hr.ne',mul_one]
  constructor
  · obtain ⟨c,_,hc⟩ := sharp_coeff hh m
    refine ⟨matrix r (colored c) _,matrix_admissible hr (colored_box c) _,?_⟩
    rw [det_coeff hr,hc,← mul_assoc,hs,hm]
  · rintro z ⟨A,hA,rfl⟩
    obtain ⟨B,hB,rfl⟩ := realize hr A hA
    rw [det_coeff hr]
    have hb := mul_le_mul_of_nonneg_left (upper_coeff hh.le hB m) (pow_nonneg hr.le (m+1))
    rwa [← mul_assoc,hs,hm] at hb
private theorem scalar_extreme {r : ℝ} (hr : 0 < r) (m : ℕ) (B : Entries) :
    |(matrix r B (m+1)).det| = r^m*middleValue r⁻¹ m (1,0) ↔ Extreme (h := r⁻¹) B m := by
  have hh := inv_pos.mpr hr
  have hm := best_middle hh m ((1,0) : V) (by norm_num) (by norm_num)
  have hcancel : r^(m+1)*r⁻¹ = r^m := by rw [pow_succ,mul_assoc,mul_inv_cancel₀ hr.ne',mul_one]
  rw [det_coeff hr,Extreme,← hm,← hcancel,mul_assoc,mul_right_inj' (pow_ne_zero _ hr.ne')]

private theorem same_upper {r : ℝ} {n : ℕ}
    {A C : Matrix (Fin n) (Fin n) ℝ} (hA : Admissible r A) (hC : Admissible r C)
    (hu : ∀ i j, i.val ≤ j.val → A i j = C i j) : A = C := by
  ext i j
  by_cases hj : i.val ≤ j.val
  · exact hu _ _ hj
  · by_cases hs : i.val=j.val+1
    · rw [(hA i j).2.1 hs,(hC i j).2.1 hs]
    · rw [(hA i j).2.2 (by omega),(hC i j).2.2 (by omega)]

private theorem two_iff {r a b d : ℝ} (hr : 0 < r) (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) (hd : d ∈ Set.Icc 0 1) :
    |a*d-b*r| = max r 1 ↔ (r ≤ 1 ∧ a=1 ∧ d=1 ∧ b=0) ∨ (1 ≤ r ∧ b=1 ∧ a*d=0) := by
  have hpa : a*d ≤ a := by simpa using mul_le_mul_of_nonneg_left hd.2 ha.1
  have hpd : a*d ≤ d := by simpa using mul_le_mul_of_nonneg_right ha.2 hd.1
  have hp := mul_nonneg ha.1 hd.1
  have hbr : b*r ≤ r := by simpa using mul_le_mul_of_nonneg_right hb.2 hr.le
  have hb0 := mul_nonneg hb.1 hr.le
  constructor
  · intro h
    by_cases hz : 0 ≤ a*d-b*r
    · rw [abs_of_nonneg hz] at h
      have h1 := le_max_right r 1
      have h2 := le_max_left r 1
      have hprod : a*d=1 := by linarith [ha.2]
      have hzero : b*r=0 := by linarith
      exact Or.inl ⟨by linarith,by linarith [ha.2],by linarith [hd.2],(mul_eq_zero.mp hzero).resolve_right hr.ne'⟩
    · rw [abs_of_nonpos (le_of_not_ge hz)] at h
      have h1 := le_max_right r 1
      have h2 := le_max_left r 1
      have hprod : b*r=1*r := by linarith
      exact Or.inr ⟨by linarith,(mul_left_inj' hr.ne').mp hprod,by linarith⟩
  · rintro (⟨h,rfl,rfl,rfl⟩ | ⟨h,rfl,he⟩)
    · simp [max_eq_right h]
    · simp [he,max_eq_left h,abs_of_nonneg hr.le]

theorem all_forms : Classify := by
  intro r hr m A hA
  have hh := inv_pos.mpr hr
  match m with
  | 0 =>
    have ha := (hA 0 0).1 (by decide)
    simp [Matrix.det_unique,MaximizingForm,middleValue,abs_of_nonneg ha.1]
  | 1 =>
    have ha := (hA 0 0).1 (by decide)
    have hb := (hA 0 1).1 (by decide)
    have hd := (hA 1 1).1 (by decide)
    have hs := (hA 1 0).2.1 (by decide)
    have hval : r^1 * middleValue r⁻¹ 1 (1,0) = max r 1 := by
      simp only [middleValue,one_pow,
        add_zero,mul_one,mul_zero,zero_add,pow_one]
      norm_num [mul_max_of_nonneg _ _ hr.le,hr.ne']
    rw [hval,Matrix.det_fin_two,hs]
    exact two_iff hr ha hb hd
  | k+2 =>
    constructor
    · intro h
      obtain ⟨B,hB,rfl⟩ := realize hr A hA
      have he := (scalar_extreme hr _ B).mp h
      let c := signs r⁻¹ B
      have h0 : c 0 = true := by simp [c,signs,coeff]
      have heq (i j : Fin (k+2+1)) (hij : i.val ≤ j.val) :
          matrix r B _ i j = colored c i j := by
        rw [matrix_entry hr,ite_eq_left hij]
        exact upper_forced hh hB (by omega) he hij (by have := j.isLt; omega)
      have hmat : matrix r B (k+2+1) = matrix r (colored c) _ := by
        apply same_upper hA (matrix_admissible hr (colored_box c) _)
        intro i j hij
        rw [heq i j hij,matrix_entry hr,ite_eq_left hij]
      refine ⟨c,h0,(colored_extreme_iff hh c h0 _).mp ?_,heq⟩
      exact (scalar_extreme hr _ _).mp (hmat ▸ h)
    · rintro ⟨c,h0,hc,hu⟩
      have hm : A = matrix r (colored c) _ := by
        apply same_upper hA (matrix_admissible hr (colored_box c) _)
        intro i j hij
        rw [hu i j hij,matrix_entry hr,ite_eq_left hij]
      rw [hm]
      exact (scalar_extreme hr _ _).mpr ((colored_extreme_iff hh c h0 _).mpr hc)

theorem no_cancellation : NoCancellation := by
  intro r hr m A ha hm σ τ hσ hτ
  have hf := (all_forms r hr m A ha).mp hm
  match m with
  | 0 => exact congrArg _ (Equiv.ext fun i => Fin.ext (by have := (σ i).isLt; have := (τ i).isLt; omega))
  | 1 =>
    have hne (π : Equiv.Perm (Fin 2)) : π 0 ≠ π 1 := π.injective.ne (by decide)
    have heq (π ρ : Equiv.Perm (Fin 2)) (h : π 0 = ρ 0) : π = ρ := by
      apply Equiv.ext
      intro i
      fin_cases i
      · exact h
      · change π 1 = ρ 1
        have := hne π
        have := hne ρ
        apply Fin.ext
        have := congrArg Fin.val h
        omega
    apply congrArg Equiv.Perm.sign
    apply heq
    rcases hf with ⟨_,_,_,hb⟩ | ⟨_,_,hp⟩
    · have hval (π : Equiv.Perm (Fin 2)) (hn : ∀ j, A (π j) j ≠ 0) : π 0 = 0 := by
        have hn1 := hn 1
        have hπ := hne π
        by_contra H
        have he : π 1 = 0 := by apply Fin.ext; omega
        exact hn1 (he ▸ hb)
      rw [hval σ hσ,hval τ hτ]
    · have hval (π : Equiv.Perm (Fin 2)) (hn : ∀ j, A (π j) j ≠ 0) : π 0 = 1 := by
        have hπ := hne π
        by_contra H
        have h0 : π 0 = 0 := by apply Fin.ext; omega
        have h1 : π 1 = 1 := by apply Fin.ext; omega
        exact (mul_ne_zero (by simpa only [h0] using hn 0) (by simpa only [h1] using hn 1)) hp
      rw [hval σ hσ,hval τ hτ]
  | k+2 =>
    obtain ⟨c,_,_,hu⟩ := hf
    rw [term_sign ha c hu σ hσ,term_sign ha c hu τ hτ]

private def fiveSingle (i : ℕ) : Bool := decide (i = 0 ∨ i = 5)
private def fiveBalanced (i : ℕ) : Bool := decide (i = 0 ∨ i = 3 ∨ i = 4)

theorem order_five_counts : ∃ A B : Matrix (Fin 5) (Fin 5) ℝ,
    Admissible 2 A ∧ Admissible 2 B ∧ |A.det| = 32 ∧ |B.det| = 32 ∧
      upperOnes A = 8 ∧ upperOnes B = 9 := by
  let mat (c : ℕ → Bool) := matrix 2 (colored c) 5
  have det (c : ℕ → Bool) (hc : c 0=true) :
      |(mat c).det| = 2^4*value (2:ℝ)⁻¹ (word c 4) (1,0) (axis (c 5)) := by
    change |(matrix 2 _ (4+1)).det| = _
    rw [det_coeff (by norm_num),colored_value (by norm_num) c hc,← mul_assoc]
    norm_num
  have count (c : ℕ → Bool) : upperOnes (mat c) =
      ∑ i : Fin 5, ∑ j : Fin 5, if i.val ≤ j.val ∧ c i ≠ c (j.val+1) then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [mat,matrix_entry (by norm_num : (0:ℝ)<2)]
    split_ifs <;> simp_all [colored]
  refine ⟨mat fiveSingle,mat fiveBalanced,matrix_admissible (by norm_num) (colored_box _) _,
    matrix_admissible (by norm_num) (colored_box _) _,?_,?_,?_,?_⟩
  · rw [det _ rfl]
    norm_num [word,value,run,List.range_succ,axis,fiveSingle,move,leftS,rightS,dot]
  · rw [det _ rfl]
    norm_num [word,value,run,List.range_succ,axis,fiveBalanced,move,leftS,rightS,dot]
  · rw [count]
    decide
  · rw [count]
    decide

theorem unequal_counts : ¬EqualCounts := by
  obtain ⟨A,B,ha,hb,had,hbd,ca,cb⟩ := order_five_counts
  intro H
  have hv : (2:ℝ)^4 * middleValue (2:ℝ)⁻¹ 4 (1,0) = 32 := by
    norm_num [middleValue,grow,sorted]
  have he := H 2 (by norm_num) 4 A B ha hb (had.trans hv.symm) (hbd.trans hv.symm)
  omega

theorem source_classification : SourceClassification := by
  intro s t hs ht m
  dsimp only
  let r := s/t
  have hr : 0 < r := div_pos hs ht
  have normalize (A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (hA : SourceBox s t A) :
      Admissible r (t⁻¹ • A) := by
    intro i j
    obtain ⟨hu,hd,hz⟩ := hA i j
    simp only [Matrix.smul_apply,smul_eq_mul,r]
    exact ⟨fun h => ⟨mul_nonneg (inv_nonneg.mpr ht.le) (hu h).1,
      by simpa [ht.ne'] using mul_le_mul_of_nonneg_left (hu h).2 (inv_nonneg.mpr ht.le)⟩,
      fun h => by rw [hd h,div_eq_inv_mul],fun h => by simp [hz h]⟩
  have expand (B : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (hB : Admissible r B) :
      SourceBox s t (t • B) := by
    intro i j
    obtain ⟨hu,hd,hz⟩ := hB i j
    simp only [Matrix.smul_apply,smul_eq_mul]
    exact ⟨fun h => ⟨mul_nonneg ht.le (hu h).1,
      by simpa using mul_le_mul_of_nonneg_left (hu h).2 ht.le⟩,
      fun h => by rw [hd h]; dsimp [r]; field_simp,fun h => by simp [hz h]⟩
  have det (A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) :
      |(t • A).det| = t^(m+1)*|A.det| := by
    rw [Matrix.det_smul,abs_mul,abs_pow,abs_of_nonneg ht.le,Fintype.card_fin]
  have denorm (A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) : t • (t⁻¹ • A) = A := by
    rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  have hmax := sharp_maximum r hr m
  change IsGreatest _ (t^(m+1)*r^m*_) ∧ _
  rw [mul_assoc]
  constructor
  · constructor
    · obtain ⟨B,hB,hv⟩ := hmax.1
      exact ⟨t • B,expand B hB,by rw [det,← hv]⟩
    · rintro z ⟨A,hA,rfl⟩
      have h := hmax.2 ⟨_,normalize A hA,rfl⟩
      calc |A.det| = t^(m+1)*|(t⁻¹ • A).det| := by simpa only [denorm A] using det (t⁻¹ • A)
           _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  · intro A hA
    have h := all_forms r hr m _ (normalize A hA)
    have hdet := det (t⁻¹ • A)
    rw [denorm] at hdet
    rw [hdet,mul_right_inj' (pow_ne_zero _ ht.ne')]
    exact h

/-- Observation 5.1, exact maximum printed for n=6, s=100, t=1. -/
theorem observation_five_one :
    IsGreatest {z : ℝ | ∃ A : Matrix (Fin 6) (Fin 6) ℝ, Admissible 100 A ∧ z = |A.det|} 10006000000 := by
  have h := sharp_maximum 100 (by norm_num) 5
  norm_num [middleValue,grow,sorted] at h
  exact h

theorem resolution : SourceClassification ∧ SharpMaximum ∧ Classify ∧ ¬EqualCounts ∧ NoCancellation :=
  ⟨source_classification,sharp_maximum,all_forms,unequal_counts,no_cancellation⟩

end HessenbergTransitions
