module
public import Conjectures.KeatingKelesTransitions.Statement
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic
@[expose] public section
namespace HessenbergTransitions
open Finset

/-- There is one inversion starting at each subdiagonal column, and none
starting at any upper-triangular column. -/
theorem hessenberg_sign {n : ℕ} (σ : Equiv.Perm (Fin n)) (hs : ∀ j, (σ j).val ≤ j.val+1) :
    σ.sign = ∏ j, (if (σ j).val=j.val+1 then (-1 : ℤˣ) else 1) := by
  classical
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  apply prod_congr rfl
  intro i _
  have hl : (Iio i).image σ ⊆ Iic i := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hj
    have hk' : k < i := mem_Iio.mp hk
    apply mem_Iic.mpr
    change (σ k).val ≤ i.val
    have := hs k
    omega
  by_cases he : (σ i).val=i.val+1
  · rw [ite_eq_left he]
    have hcard : (Iic i \ (Iio i).image σ).card=1 := by
      rw [card_sdiff_of_subset hl,card_image_of_injective _ σ.injective,Fin.card_Iic,Fin.card_Iio]
      omega
    obtain ⟨v,hv⟩ := card_eq_one.mp hcard
    have hv0 : v ∈ Iic i \ (Iio i).image σ := by rw [hv]; simp
    obtain ⟨hvi,hvout⟩ := mem_sdiff.mp hv0
    let t := σ.symm v
    have htv : σ t = v := σ.apply_symm_apply _
    have hit : i < t := by
      by_contra! hh
      rcases hh.lt_or_eq with hh'|hh'
      · exact hvout (mem_image.mpr ⟨t,mem_Iio.mpr hh',htv⟩)
      · have : v ≤ i := mem_Iic.mp hvi
        have hv' := congrArg Fin.val (hh' ▸ htv : σ i = v)
        omega
    rw [prod_eq_single t]
    · rw [htv,ite_eq_right]
      have : v ≤ i := mem_Iic.mp hvi
      change ¬ (σ i).val < v.val
      omega
    · intro j hj hne
      apply ite_eq_left
      by_contra! hx
      have hij := mem_Ioi.mp hj
      have hne' : σ j ≠ σ i := σ.injective.ne hij.ne'
      have hh : (σ j).val ≤ i.val := by
        have := lt_of_le_of_ne hx hne'
        change (σ j).val < (σ i).val at this
        omega
      have hin : σ j ∈ Iic i \ (Iio i).image σ := by
        apply mem_sdiff.mpr
        refine ⟨mem_Iic.mpr hh,?_⟩
        rintro h
        obtain ⟨k,hk,heq⟩ := mem_image.mp h
        have := σ.injective heq
        have := mem_Iio.mp hk
        omega
      rw [hv,mem_singleton] at hin
      exact hne (σ.injective (hin.trans htv.symm))
    · simp [mem_Ioi.mpr hit]
  · rw [ite_eq_right he]
    have hii : σ i ≤ i := by
      change (σ i).val ≤ i.val
      have := hs i
      omega
    have hset : (Iic i).image σ = Iic i := by
      apply eq_of_subset_of_card_le
      · intro j hj
        obtain ⟨k,hk,rfl⟩ := mem_image.mp hj
        rcases (mem_Iic.mp hk).lt_or_eq with h|rfl
        · exact hl (mem_image.mpr ⟨_,mem_Iio.mpr h,rfl⟩)
        · exact mem_Iic.mpr hii
      · rw [card_image_of_injective _ σ.injective]
    apply prod_eq_one
    intro j hj
    apply ite_eq_left
    by_contra! hx
    have hji := mem_Ioi.mp hj
    have hin : σ j ∈ (Iic i).image σ := by rw [hset]; exact mem_Iic.mpr (hx.trans hii)
    obtain ⟨k,hk,heq⟩ := mem_image.mp hin
    have := σ.injective heq
    have := mem_Iic.mp hk
    omega

def tag (b : Bool) : ℤˣ := if b then 1 else -1

private theorem telescope (c : ℕ → Bool) (n : ℕ) :
    (∏ j : Fin n, tag (c j)*tag (c (j.val+1))) = tag (c 0)*tag (c n) := by
  induction n with
  | zero => cases h : c 0 <;> simp [tag]
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,ih]
    cases he : c n <;> simp [tag]

theorem term_sign {r : ℝ} {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : Admissible r A) (c : ℕ → Bool)
    (hu : ∀ i j, i.val ≤ j.val → A i j = colored c i j)
    (σ : Equiv.Perm (Fin n)) (hn : ∀ j, A (σ j) j ≠ 0) :
    σ.sign = (-1 : ℤˣ)^n * (tag (c 0) * tag (c n)) := by
  have hs (j : Fin n) : (σ j).val ≤ j.val+1 := by
    by_contra! H
    exact hn j ((hA _ _).2.2 H)
  rw [hessenberg_sign σ hs]
  have ht (j : Fin n) : (if (σ j).val=j.val+1 then (-1 : ℤˣ) else 1)
      = -1 * (tag (c (σ j)) * tag (c (j.val+1))) := by
    by_cases he : (σ j).val=j.val+1
    · rw [he]
      cases h : c (j.val+1) <;> simp [tag]
    · have hij : (σ j).val ≤ j.val := by have := hs j; omega
      have hne : c (σ j) ≠ c (j.val+1) := by
        intro h
        exact hn j (by rw [hu _ _ hij]; simp [colored,h])
      cases h₁ : c (σ j) <;> cases h₂ : c (j.val+1) <;> simp_all [tag]
  simp_rw [ht]
  rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,prod_mul_distrib,
    Equiv.prod_comp σ (fun j : Fin n => tag (c j)),← prod_mul_distrib,telescope]

end HessenbergTransitions
