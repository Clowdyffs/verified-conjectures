module
public import Conjectures.NearHadamardSharp.Spectral
import Mathlib.Tactic
@[expose] public section
open Finset Matrix
namespace NearHadamard.Optimal
section Gram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Unitary
private theorem trace_conj (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    (conjStarAlgAut ℝ _ U A).trace = A.trace := by
  rw [conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self, one_mul]

private theorem det_conj (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    (conjStarAlgAut ℝ _ U A).det = A.det := by
  rw [conjStarAlgAut_apply, det_mul_comm, ← Matrix.mul_assoc, coe_star_mul_self, one_mul]

private theorem trace_cube {S : Matrix ι ι ℝ} (h : S.IsHermitian) :
    (S*S*S).trace = ∑ i, (h.eigenvalues i)^3 := by
  let U := conjStarAlgAut ℝ _ h.eigenvectorUnitary
  have e : S=U (diagonal h.eigenvalues) := h.spectral_theorem
  calc
    _ = (U (diagonal h.eigenvalues * diagonal h.eigenvalues * diagonal h.eigenvalues)).trace := by rw [map_mul,map_mul,←e]
    _ = _ := by rw [trace_conj]; simp [diagonal_mul_diagonal, pow_succ]

theorem gram_bound_of_moment_or_large {S : Matrix ι ι ℝ} (hS : S.IsHermitian)
    (hd : ∀ i, S i i = 0) (ho : ∀ i j, i ≠ j → (S i j)^2 = 1)
    (hv : 15 ≤ Fintype.card ι)
    (hcert : 1080 ≤ Fintype.card ι ∨ cubeCondition (Fintype.card ι:ℝ) (S*S*S).trace)
    (hcap : ∀ i, hS.eigenvalues i ^ 2 ≤ 2*(Fintype.card ι : ℝ)-1) :
    81844 * W (Fintype.card ι) ≤
      100000 * ((2*(Fintype.card ι : ℝ)) • (1 : Matrix ι ι ℝ) + (2:ℝ) • S).det := by
  let v := Fintype.card ι
  have hv' : (15:ℝ) ≤ v := by exact_mod_cast hv
  have hpos : (0:ℝ) < v := by linarith
  let x (i : ι) := hS.eigenvalues i / v
  have cap (i) : (x i)^2 ≤ 2/(v:ℝ) := by
    change (hS.eigenvalues i/(v:ℝ))^2 ≤ _
    rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hpos) hpos]
    have H : hS.eigenvalues i^2 ≤ 2*(v:ℝ)-1 := hcap i
    nlinarith [mul_nonneg (sub_nonneg.mpr H) hpos.le]
  have hz : ∑ i, x i = 0 := by
    have ht : S.trace = ∑ i, hS.eigenvalues i := hS.trace_eq_sum_eigenvalues
    simp only [x, ←sum_div, ←ht]
    simp [Matrix.trace, Matrix.diag, hd]
  have hsq : ∑ i, (x i)^2 = 1-(v:ℝ)⁻¹ := by
    simp only [x, div_pow, ←sum_div, squared_moment hS hd ho]
    change (v:ℝ)*((v:ℝ)-1)/(v:ℝ)^2 = _
    field_simp
  have det_form :
      ((2*(v:ℝ)) • (1 : Matrix ι ι ℝ) + (2:ℝ) • S).det =
      (2*(v:ℝ))^v * ∏ i, (1+x i) := by
    let U := conjStarAlgAut ℝ _ hS.eigenvectorUnitary
    have h : S = U (diagonal hS.eigenvalues) := hS.spectral_theorem
    have ha : (2*(v:ℝ)) • (1 : Matrix ι ι ℝ) + (2:ℝ) • S =
        U (diagonal (fun i => 2*(v:ℝ)*(1+x i))) := by
      have he : diagonal (fun i => 2*(v:ℝ)*(1+x i)) =
          (2*(v:ℝ)) • (1 : Matrix ι ι ℝ) + (2:ℝ) • diagonal hS.eigenvalues := by
        ext i j
        by_cases hij : i = j
        · subst j; simp [x]; field_simp
        · simp [hij]
      rw [he, map_add, map_smul, map_smul, map_one, ←h]
    rw [ha, det_conj, det_diagonal, Finset.prod_mul_distrib, Finset.prod_const, card_univ]
  rw [det_form]
  have H : 81844*((2-(v:ℝ)⁻¹)*(1-(v:ℝ)⁻¹)^(v-1)) ≤ 100000*∏ i,(1+x i) := by
    rcases hcert with hl|hm
    · exact tail_product x hl hz hsq cap
    · apply cube_product x hv hz hsq _ _ _ hm
      · intro i
        change (hS.eigenvalues i/(v:ℝ))^2 ≤ _
        rw [div_pow]; gcongr; exact hcap i
      · simp only [x, v, div_pow, ←sum_div, trace_cube hS]
  have hvn : 1≤v := by change 1≤Fintype.card ι; omega
  have hW : W v=(2*(v:ℝ))^v*((2-(v:ℝ)⁻¹)*(1-(v:ℝ)⁻¹)^(v-1)) := by
    unfold W
    have ep : (2*(v:ℝ))^v = (2*(v:ℝ))^(v-1)*(2*(v:ℝ)) := by
      rw [←pow_succ, Nat.sub_add_cancel hvn]
    rw [ep, show 2*(v:ℝ)-2=(2*(v:ℝ))*(1-(v:ℝ)⁻¹) by field_simp, mul_pow]
    field_simp; ring
  rw [hW]
  have hpos2 : 0 ≤ (2*(v:ℝ))^v := by positivity
  change 81844*((2-(v:ℝ)⁻¹)*(1-(v:ℝ)⁻¹)^(v-1)) ≤ _ at H
  nlinarith [mul_nonneg (sub_nonneg.mpr H) hpos2]

end Gram

theorem balancedFill_det_of_moment_or_large {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B D : Matrix ι ι ℝ)
    (hA : Aᵀ = A) (hD : Dᵀ = D)
    (hAd : ∀ i, A i i = 0) (hDd : ∀ i, D i i = 0)
    (hAo : ∀ i j, i ≠ j → (A i j)^2 = 1)
    (hDo : ∀ i j, i ≠ j → (D i j)^2 = 1)
    (hv : 15 ≤ Fintype.card ι)
    (haCert : 1080≤Fintype.card ι ∨ cubeCondition (Fintype.card ι:ℝ) (A*A*A).trace)
    (hdCert : 1080≤Fintype.card ι ∨ cubeCondition (Fintype.card ι:ℝ) ((-D)*(-D)*(-D)).trace)
    (hc : let C := fromBlocks A B Bᵀ D
          C*C = (2*(Fintype.card ι:ℝ)-1) • (1 : Matrix _ _ ℝ)) :
    81844 * W (Fintype.card ι) ≤ 100000 *
      |(fromBlocks (A+1) B Bᵀ (D-1)).det| := by
  let t : ℝ := 2*(Fintype.card ι:ℝ)
  have hh : fromBlocks (A*A+B*Bᵀ) (A*B+B*D) (Bᵀ*A+D*Bᵀ) (Bᵀ*B+D*D) =
      fromBlocks ((t-1) • (1 : Matrix ι ι ℝ)) 0 0 ((t-1) • (1 : Matrix ι ι ℝ)) := by
    convert hc using 1
    · exact (fromBlocks_multiply ..).symm
    · simpa [t] using (fromBlocks_smul (t-1) (1 : Matrix ι ι ℝ) (0 : Matrix ι ι ℝ) 0 (1 : Matrix ι ι ℝ)).symm
  obtain ⟨h1,h2,h3,h4⟩ := fromBlocks_inj.mp hh
  have hAI : A.IsHermitian := by ext i j; exact congrFun (congrFun hA i) j
  have hDI : D.IsHermitian := by ext i j; exact congrFun (congrFun hD i) j
  have hcapA := completion_cap hAI Bᵀ (t-1) (by simpa [hA] using h1)
  have hcapD := completion_cap hDI.neg B (t-1) (by simpa [hD, add_comm] using h4)
  have hdetA := gram_bound_of_moment_or_large hAI hAd hAo hv haCert hcapA
  have hdetD := gram_bound_of_moment_or_large hDI.neg (by simpa using hDd) (by simpa using hDo) hv hdCert hcapD
  let N := fromBlocks (A+1) B Bᵀ (D-1)
  have hgram : N*N = fromBlocks (t • (1 : Matrix ι ι ℝ) + (2:ℝ) • A) 0 0
      (t • (1 : Matrix ι ι ℝ) + (2:ℝ) • (-D)) := by
    rw [show N = fromBlocks (A+1) B Bᵀ (D-1) by rfl, fromBlocks_multiply, fromBlocks_inj]
    have hId : t • (1 : Matrix ι ι ℝ) = (t-1) • (1 : Matrix ι ι ℝ) + 1 := by
      rw [sub_smul, one_smul]; abel
    rw [hId, show (2:ℝ) = 1+1 by norm_num, add_smul, add_smul, one_smul, one_smul]
    refine ⟨?_,?_,?_,?_⟩
    · rw [←h1]; noncomm_ring
    · rw [←h2]; noncomm_ring
    · rw [←h3]; noncomm_ring
    · rw [←h4]; noncomm_ring
  have H := congrArg Matrix.det hgram
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁] at H
  have hp : 0 ≤ 81844*W (Fintype.card ι) := by
    have hh : (15:ℝ) ≤ Fintype.card ι := by exact_mod_cast hv
    unfold W
    exact mul_nonneg (by norm_num) (mul_nonneg (by linarith) (pow_nonneg (by linarith) _))
  have H' := mul_le_mul hdetA hdetD hp (hp.trans hdetA)
  change 81844 * W (Fintype.card ι) ≤ 100000*|N.det|
  have hab := sq_abs N.det
  dsimp only [t] at H
  nlinarith [abs_nonneg N.det]

theorem intFill_det_of_moment_or_large {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (C : Matrix (ι ⊕ ι) (ι ⊕ ι) ℤ) (h : Conference q C)
    (hq : q+1 = 2*Fintype.card ι) (hv : 15 ≤ Fintype.card ι)
    (hAc : 1080≤Fintype.card ι ∨ cubeCondition (Fintype.card ι:ℝ) ((C.toBlocks₁₁*C.toBlocks₁₁*C.toBlocks₁₁).trace:ℝ))
    (hDc : 1080≤Fintype.card ι ∨ cubeCondition (Fintype.card ι:ℝ) (((-C.toBlocks₂₂)*(-C.toBlocks₂₂)*(-C.toBlocks₂₂)).trace:ℝ)) :
    81844 * W (Fintype.card ι) ≤ 100000 * |((diagonalFill C).det : ℝ)| := by
  let A : Matrix ι ι ℝ := fun i j => C (.inl i) (.inl j)
  let B : Matrix ι ι ℝ := fun i j => C (.inl i) (.inr j)
  let D : Matrix ι ι ℝ := fun i j => C (.inr i) (.inr j)
  let f := Int.castRingHom ℝ
  have hf : f.mapMatrix C = fromBlocks A B Bᵀ D := by
    ext i j
    rcases i with i|i <;> rcases j with j|j <;> try rfl
    exact congrArg (fun z : ℤ => (z : ℝ)) (h.symm _ _)
  have tr : Cᵀ = C := by ext i j; exact h.symm _ _
  have o := h.orth
  rw [tr] at o
  have oq : (q:ℝ) = 2*(Fintype.card ι:ℝ)-1 := by
    have hqn : (q:ℝ)+1 = 2*(Fintype.card ι:ℝ) := by exact_mod_cast hq
    linarith
  have horth : f.mapMatrix C * f.mapMatrix C =
      (2*(Fintype.card ι:ℝ)-1) • (1 : Matrix _ _ ℝ) := by
    change C.map f * C.map f = _
    rw [←Matrix.map_mul, o, ←oq]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    by_cases hij : i=j <;> simp [hij,f]
  have hentry : f.mapMatrix (diagonalFill C) = fromBlocks (A+1) B Bᵀ (D-1) := by
    ext i j
    rcases i with i|i <;> rcases j with j|j
    · change ((C (.inl i) (.inl j) + (if Sum.inl i = (Sum.inl j : ι ⊕ ι) then 1 else 0) : ℤ) : ℝ) =
        (C (.inl i) (.inl j):ℝ) + (1 : Matrix ι ι ℝ) i j
      by_cases he : i=j <;> simp [he, Matrix.one_apply]
    · change ((C (.inl i) (.inr j) + 0 : ℤ) : ℝ) = (C (.inl i) (.inr j):ℝ)
      simp
    · change ((C (.inr i) (.inl j) + 0 : ℤ) : ℝ) = (C (.inl j) (.inr i):ℝ)
      simp [h.symm (Sum.inr i) (Sum.inl j)]
    · change ((C (.inr i) (.inr j) + (if Sum.inr i = (Sum.inr j : ι ⊕ ι) then -1 else 0) : ℤ) : ℝ) =
        (C (.inr i) (.inr j):ℝ) - (1 : Matrix ι ι ℝ) i j
      by_cases he : i=j <;> simp [he, Matrix.one_apply] <;> ring
  have cast_cube (T : Matrix ι ι ℤ) :
      ((T*T*T).trace:ℝ) = (f.mapMatrix T * f.mapMatrix T * f.mapMatrix T).trace := by
    change f ((T*T*T).trace) = _
    change f ((T*T*T).trace) = (T.map f * T.map f * T.map f).trace
    rw [←Matrix.map_mul,←Matrix.map_mul]
    simp [Matrix.trace,Matrix.diag,Matrix.map_apply]
  have hcA : 1080≤Fintype.card ι ∨ cubeCondition (Fintype.card ι:ℝ) (A*A*A).trace := by
    rcases hAc with hl|hm
    · exact Or.inl hl
    · rw [cast_cube] at hm; exact Or.inr hm
  have hcD : 1080≤Fintype.card ι ∨ cubeCondition (Fintype.card ι:ℝ) ((-D)*(-D)*(-D)).trace := by
    rcases hDc with hl|hm
    · exact Or.inl hl
    · have em : f.mapMatrix (-C.toBlocks₂₂) = -D := by ext i j; change ((-C (.inr i) (.inr j):ℤ):ℝ) = -_; simp [D]
      rw [cast_cube,em] at hm; exact Or.inr hm
  have H := balancedFill_det_of_moment_or_large A B D
      (by ext i j; change (C (Sum.inl j) (Sum.inl i):ℝ) = (C (Sum.inl i) (Sum.inl j):ℝ); exact_mod_cast h.symm (Sum.inl j) (Sum.inl i))
      (by ext i j; change (C (Sum.inr j) (Sum.inr i):ℝ) = (C (Sum.inr i) (Sum.inr j):ℝ); exact_mod_cast h.symm (Sum.inr j) (Sum.inr i))
      (by intro i; dsimp [A]; exact_mod_cast h.diag (Sum.inl i))
      (by intro i; dsimp [D]; exact_mod_cast h.diag (Sum.inr i))
      (by intro i j hij; dsimp [A]; exact_mod_cast h.off (Sum.inl i) (Sum.inl j) (fun he => hij (Sum.inl.inj he)))
      (by intro i j hij; dsimp [D]; exact_mod_cast h.off (Sum.inr i) (Sum.inr j) (fun he => hij (Sum.inr.inj he)))
      hv hcA hcD (hf ▸ horth)
  rw [←hentry, ←RingHom.map_det] at H
  exact H

end NearHadamard.Optimal
