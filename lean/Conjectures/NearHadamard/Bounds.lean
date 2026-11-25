module

public import Conjectures.NearHadamard.Sharp
public import Conjectures.NearHadamard.Conference
public import Conjectures.NearHadamard.Paley
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

@[expose] public section

open Finset Matrix
open scoped BigOperators

namespace NearHadamard

/-- The Ehlich–Wojtas bound at the even order `2 * v`. -/
def W (v : ℕ) : ℝ := (4 * (v : ℝ) - 2) * (2 * (v : ℝ) - 2) ^ (v - 1)

/-- For a normalized eigenvalue displacement of size at most 1/15, the
quadratic error in the linear approximation to log is at most 527/1000. -/
theorem log_lower {x : ℝ} (hx : |x| ≤ 1 / 15) :
    x - (527/1000 : ℝ) * x^2 ≤ Real.log (1+x) := by
  have hlt : |-x| < 1 := by rw [abs_neg]; linarith
  have h := (abs_le.mp (Real.abs_log_sub_add_sum_range_le hlt 3)).1
  rw [abs_neg, sub_neg_eq_add] at h
  simp [Finset.sum_range_succ] at h
  have habs : |x|^2 = x^2 := sq_abs x
  have hx3 : |x|^3 ≤ (1/15 : ℝ)*x^2 := by
    rw [pow_succ, habs, mul_comm]
    gcongr
  have hx4 : |x|^4 ≤ (1/225 : ℝ)*x^2 := by
    calc |x|^4 = |x|^2 * |x|^2 := by ring
         _ ≤ (1/15 : ℝ)^2 * |x|^2 := by gcongr
         _ = _ := by rw [habs]; ring
  have herr : |x|^4 / (1-|x|) ≤ (1/210 : ℝ)*x^2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1-|x|)).2
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx)]
  have hc : -(1/15 : ℝ)*x^2 ≤ x^3 := by
    have := neg_abs_le (x^3)
    rw [abs_pow] at this
    linarith
  nlinarith [sq_nonneg x]

/-- The product of all normalized Gram eigenvalues is bounded below by
`exp (-527/1000)` when their displacements have sum zero, sum of squares
at most one, and individual absolute values at most 1/15. -/
theorem normalized_product {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hcap : ∀ i, |x i| ≤ 1/15) (hzero : ∑ i, x i = 0)
    (hsq : ∑ i, x i ^ 2 ≤ 1) :
    Real.exp (-(527/1000 : ℝ)) ≤ ∏ i, (1+x i) := by
  have hp (i) : 0 < 1+x i := by linarith [(abs_le.mp (hcap i)).1]
  rw [← Real.le_log_iff_exp_le (Finset.prod_pos fun i _ => hp i)]
  rw [Real.log_prod (fun i _ => (hp i).ne')]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => log_lower (hcap i))
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hzero] at h
  linarith

/-- At half-order at least 450, the spectral lower bound exceeds four
fifths of the Ehlich–Wojtas bound. -/
theorem scale_bound (v : ℕ) (hv : 450 ≤ v) :
    4 * W v ≤ 5 * (2*(v : ℝ))^v * Real.exp (-(527/1000 : ℝ)) := by
  have hv' : (450 : ℝ) ≤ v := by exact_mod_cast hv
  have hpos : (0 : ℝ) < v := by linarith
  have h1 : 0 < (1 - (v : ℝ)⁻¹) := sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith))
  have hm : ((v-1 : ℕ) : ℝ) = (v : ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ v)]; norm_num
  have hinv : (v : ℝ)⁻¹ ≤ 1/450 := by rw [inv_eq_one_div]; gcongr
  have hbase : 1 - (v : ℝ)⁻¹ ≤ Real.exp (-(v : ℝ)⁻¹) := by linarith [Real.add_one_le_exp (-(v : ℝ)⁻¹)]
  have hpow := pow_le_pow_left₀ h1.le hbase (v-1)
  rw [← Real.exp_nat_mul, hm] at hpow
  have e : ((v : ℝ)-1) * (-(v : ℝ)⁻¹) = -1+(v : ℝ)⁻¹ := by field_simp; ring
  rw [e] at hpow
  have hc : 8 * Real.exp (-1+(v : ℝ)⁻¹) ≤ 5 * Real.exp (-(527/1000 : ℝ)) := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 8), ← Real.exp_log (by norm_num : (0:ℝ) < 5),
      ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
    linarith [Real.log_two_lt_d9, Real.log_five_gt_d9]
  have hW : W v = (2*(v:ℝ))^v * (2-(v:ℝ)⁻¹) * (1-(v:ℝ)⁻¹)^(v-1) := by
    unfold W
    have ep : (2*(v:ℝ))^v = (2*(v:ℝ))^(v-1) * (2*(v:ℝ)) := by
      rw [←pow_succ, show v - 1 + 1 = v by omega]
    rw [ep]
    rw [show 2*(v:ℝ)-2 = (2*(v:ℝ))*(1-(v:ℝ)⁻¹) by field_simp, mul_pow]
    field_simp
    ring
  rw [hW]
  have h := calc
    4 * ((2-(v:ℝ)⁻¹) * (1-(v:ℝ)⁻¹)^(v-1)) ≤ 8 * Real.exp (-1+(v:ℝ)⁻¹) := by
      have htwo : 2 - (v:ℝ)⁻¹ ≤ 2 := by linarith [inv_pos.mpr hpos]
      nlinarith [mul_nonneg (sub_nonneg.mpr htwo) (pow_nonneg h1.le (v-1))]
    _ ≤ _ := hc
  nlinarith [mul_nonneg (pow_nonneg (show 0 ≤ 2*(v:ℝ) by positivity) v) (sub_nonneg.mpr h)]

section Gram

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Unitary

private theorem trace_conj (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    (conjStarAlgAut ℝ _ U A).trace = A.trace := by
  rw [conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self, one_mul]

private theorem det_conj (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    (conjStarAlgAut ℝ _ U A).det = A.det := by
  rw [conjStarAlgAut_apply, det_mul_comm, ← Matrix.mul_assoc, coe_star_mul_self, one_mul]

/-- A zero-diagonal symmetric sign matrix has total squared eigenvalue
equal to the number of off-diagonal entries. -/
theorem squared_moment {S : Matrix ι ι ℝ} (hS : S.IsHermitian)
    (hd : ∀ i, S i i = 0) (ho : ∀ i j, i ≠ j → (S i j)^2 = 1) :
    ∑ i, hS.eigenvalues i ^ 2 = (Fintype.card ι : ℝ) * (Fintype.card ι - 1) := by
  have spectral : (S*S).trace = ∑ i, hS.eigenvalues i ^ 2 := by
    let U := conjStarAlgAut ℝ _ hS.eigenvectorUnitary
    have h : S = U (diagonal hS.eigenvalues) := hS.spectral_theorem
    calc
      _ = (U (diagonal hS.eigenvalues * diagonal hS.eigenvalues)).trace := by rw [map_mul, ← h]
      _ = _ := by rw [trace_conj]; simp [sq, diagonal_mul_diagonal]
  rw [← spectral]
  have hentry (i j) : S i j * S j i = if i = j then 0 else 1 := by
    by_cases h : i = j
    · subst j; simp [hd]
    · have he := hS.apply i j
      simp only [star_trivial] at he
      simp only [h, ite_false]
      rw [he, ← sq, ho _ _ h]
  have row (i : ι) : ∑ j, (if i = j then (0:ℝ) else 1) = (Fintype.card ι : ℝ)-1 := by
    have hj (j : ι) : (if i = j then (0:ℝ) else 1) = 1 - (if i=j then 1 else 0) := by split <;> simp
    simp [hj, sum_sub_distrib]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, hentry, row]
  ring

private theorem trace_cube {S : Matrix ι ι ℝ} (h : S.IsHermitian) :
    (S*S*S).trace = ∑ i, (h.eigenvalues i)^3 := by
  let U := conjStarAlgAut ℝ _ h.eigenvectorUnitary
  have e : S=U (diagonal h.eigenvalues) := h.spectral_theorem
  calc
    _ = (U (diagonal h.eigenvalues * diagonal h.eigenvalues * diagonal h.eigenvalues)).trace := by rw [map_mul,map_mul,←e]
    _ = _ := by rw [trace_conj]; simp [diagonal_mul_diagonal, pow_succ]

/-- A half-sized near-Hadamard Gram block at order at least 126 meets the
four-fifths bound if all eigenvalues of its sign matrix have square at
most the order minus one. -/
theorem gram_bound_of_moment_or_large {S : Matrix ι ι ℝ} (hS : S.IsHermitian)
    (hd : ∀ i, S i i = 0) (ho : ∀ i j, i ≠ j → (S i j)^2 = 1)
    (hv : 15 ≤ Fintype.card ι)
    (hcert : 63 ≤ Fintype.card ι ∨ momentCondition (Fintype.card ι:ℝ) (S*S*S).trace)
    (hcap : ∀ i, hS.eigenvalues i ^ 2 ≤ 2*(Fintype.card ι : ℝ)-1) :
    4 * W (Fintype.card ι) ≤
      5 * ((2*(Fintype.card ι : ℝ)) • (1 : Matrix ι ι ℝ) + (2:ℝ) • S).det := by
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
  have H : 4*((2-(v:ℝ)⁻¹)*(1-(v:ℝ)⁻¹)^(v-1)) ≤ 5*∏ i,(1+x i) := by
    rcases hcert with hl|hm
    · exact sharp_product x hl hz hsq cap
    · apply moment_product x hv hz hsq _ _ _ hm
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
  change 4*((2-(v:ℝ)⁻¹)*(1-(v:ℝ)⁻¹)^(v-1)) ≤ _ at H
  nlinarith [mul_nonneg (sub_nonneg.mpr H) hpos2]

theorem gram_bound {S : Matrix ι ι ℝ} (hS : S.IsHermitian)
    (hd : ∀ i, S i i = 0) (ho : ∀ i j, i ≠ j → (S i j)^2 = 1)
    (hv : 63 ≤ Fintype.card ι)
    (hcap : ∀ i, hS.eigenvalues i ^ 2 ≤ 2*(Fintype.card ι : ℝ)-1) :
    4 * W (Fintype.card ι) ≤
      5 * ((2*(Fintype.card ι : ℝ)) • (1 : Matrix ι ι ℝ) + (2:ℝ) • S).det :=
  gram_bound_of_moment_or_large hS hd ho (by omega) (Or.inl hv) hcap

/-- If additional rows complete the columns of a symmetric sign block to
an orthogonal system of squared length q, its squared eigenvalues are at most q. -/
theorem completion_cap {κ : Type*} [Fintype κ] {S : Matrix ι ι ℝ}
    (hS : S.IsHermitian) (T : Matrix κ ι ℝ) (q : ℝ)
    (horth : Sᵀ*S + Tᵀ*T = q • (1 : Matrix ι ι ℝ)) (i : ι) :
    hS.eigenvalues i ^ 2 ≤ q := by
  let u : ι → ℝ := ⇑(hS.eigenvectorBasis i)
  have heu : S *ᵥ u = hS.eigenvalues i • u := hS.mulVec_eigenvectorBasis i
  have hun : u ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2 (hS.eigenvectorBasis.orthonormal.ne_zero i)
  have hu : 0 < u ⬝ᵥ u := by
    apply lt_of_le_of_ne
    · exact Finset.sum_nonneg fun j _ => mul_self_nonneg (u j)
    · exact Ne.symm (dotProduct_self_eq_zero.not.mpr hun)
  have ht : 0 ≤ (T *ᵥ u) ⬝ᵥ (T *ᵥ u) :=
    Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have h := congrArg (fun A : Matrix ι ι ℝ => u ⬝ᵥ (A *ᵥ u)) horth
  rw [Matrix.add_mulVec, dotProduct_add, ←mulVec_mulVec, ←mulVec_mulVec,
      dotProduct_transpose_mulVec, dotProduct_transpose_mulVec, heu,
      smul_dotProduct, dotProduct_smul, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul] at h
  simp only [smul_eq_mul] at h
  exact (mul_le_mul_iff_of_pos_right hu).mp (by nlinarith)

/-- The actual determinant of an order-2v matrix with two copies of the
completed sign Gram block satisfies Problem 15's inequality for v ≥ 63. -/
theorem completed_gram_det {κ : Type*} [Fintype κ]
    (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) {S : Matrix ι ι ℝ} (hS : S.IsHermitian)
    (hd : ∀ i, S i i = 0) (ho : ∀ i j, i ≠ j → (S i j)^2 = 1)
    (T : Matrix κ ι ℝ) (hv : 63 ≤ Fintype.card ι)
    (horth : Sᵀ*S + Tᵀ*T = (2*(Fintype.card ι:ℝ)-1) • (1 : Matrix ι ι ℝ))
    (hgram : let B := (2*(Fintype.card ι:ℝ)) • (1 : Matrix ι ι ℝ) + (2:ℝ) • S
             M*Mᵀ = Matrix.fromBlocks B 0 0 B) :
    4 * W (Fintype.card ι) ≤ 5*|M.det| := by
  let B := (2*(Fintype.card ι:ℝ)) • (1 : Matrix ι ι ℝ) + (2:ℝ) • S
  have h : M*Mᵀ = Matrix.fromBlocks B 0 0 B := hgram
  have he := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_fromBlocks_zero₂₁] at he
  have ha : |M.det| = |B.det| := (sq_eq_sq_iff_abs_eq_abs _ _).mp (by nlinarith)
  rw [ha]
  exact (gram_bound hS hd ho hv (completion_cap hS T _ horth)).trans
    (mul_le_mul_of_nonneg_left (le_abs_self B.det) (by norm_num))

end Gram


section PaleyBlock

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (s : Option F → Prop) [DecidablePred s]

/-- A principal restriction of the Paley matrix, including the overall sign
and the signs contributed by changing representatives on projective lines. -/
def signedEntry (d : ℝ) (w : Option F → ℝ) (i j : Option F) : ℝ :=
  d * w i * (paley F i j : ℝ) * w j

theorem paleyBlock_det (hd : Fintype.card F % 4 = 1) (hc : ringChar F ≠ 2)
    (d : ℝ) (w : Option F → ℝ) (hds : d^2 = 1) (hws : ∀ i, (w i)^2 = 1)
    (hn : Fintype.card F + 1 = 2*Fintype.card (Subtype s))
    (hv : 63 ≤ Fintype.card (Subtype s))
    (M : Matrix (Subtype s ⊕ Subtype s) (Subtype s ⊕ Subtype s) ℝ)
    (hgram : let S : Matrix (Subtype s) (Subtype s) ℝ := fun i j => signedEntry d w i j
             let B := (2*(Fintype.card (Subtype s):ℝ)) • (1 : Matrix _ _ ℝ) + (2:ℝ) • S
             M*Mᵀ = Matrix.fromBlocks B 0 0 B) :
    4 * W (Fintype.card (Subtype s)) ≤ 5 * |M.det| := by
  let P := paley F
  let S : Matrix (Subtype s) (Subtype s) ℝ := fun i j => signedEntry d w i j
  let T : Matrix {i // ¬s i} (Subtype s) ℝ := fun i j => signedEntry d w i j
  have hneg : quadraticChar F (-1) = 1 :=
    (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr (one_ne_zero' F))).mpr
      (FiniteField.isSquare_neg_one_iff.mpr (by omega))
  have sym (i j : Option F) : P i j = P j i := by
    cases i <;> cases j <;> try rfl
    rename_i a b
    change quadraticChar F (a-b) = quadraticChar F (b-a)
    rw [show a-b = (-1)*(b-a) by ring, map_mul, hneg, one_mul]
  have hs : S.IsHermitian := by
    ext i j
    change star (signedEntry d w j i) = signedEntry d w i j
    simp only [star_trivial, signedEntry]
    change d * w j * (P j i : ℝ) * w i = d * w i * (P i j : ℝ) * w j
    rw [sym j.val i.val]; ring
  have hz (i : Option F) : P i i = 0 := by cases i <;> simp [P, paley]
  have hsg (i j : Option F) (hne : i ≠ j) : (P i j)^2 = 1 := by
    cases i with
    | none => cases j <;> simp_all [P, paley]
    | some a =>
      cases j with
      | none => simp [P, paley]
      | some b =>
        change (quadraticChar F (a-b))^2 = 1
        exact quadraticChar_sq_one (sub_ne_zero.mpr (fun h => hne (congrArg some h)))
  have hcount : (Fintype.card F : ℝ) = 2*(Fintype.card (Subtype s):ℝ)-1 := by
    have hh : (Fintype.card F : ℝ)+1 = 2*(Fintype.card (Subtype s):ℝ) := by exact_mod_cast hn
    linarith
  apply completed_gram_det M hs _ _ T hv _ hgram
  · intro i; simp [S, signedEntry, show paley F i i = 0 from hz i]
  · intro i j hij
    have hab : (P i j : ℝ)^2 = 1 := by exact_mod_cast hsg _ _ (Subtype.coe_injective.ne hij)
    change (d * w i * (P i j : ℝ) * w j)^2 = 1
    simp only [mul_pow, hds, hws, hab, one_mul]
  · ext i j
    let g (k : Option F) := signedEntry d w k i * signedEntry d w k j
    change (∑ k : Subtype s, g k) + (∑ k : {k // ¬s k}, g k) = _
    rw [Fintype.sum_subtype_add_sum_subtype s g]
    have gs (k : Option F) :
        g k = w i * w j * ((P k i : ℝ) * (P k j : ℝ)) := by
      change (d * w k * (P k i : ℝ) * w i) * (d * w k * (P k j : ℝ) * w j) = _
      calc _ = d^2 * (w k)^2 * (w i * w j * ((P k i : ℝ) * (P k j : ℝ))) := by ring
           _ = _ := by rw [hds, hws]; ring
    simp_rw [gs]
    rw [←Finset.mul_sum]
    have orth := congrFun (congrFun (paley_orthogonal (F:=F) hc) i.val) j.val
    by_cases hij : i = j
    · subst j
      have h : ∑ k, P k i * P k i = (Fintype.card F:ℤ) := by simpa [P, Matrix.mul_apply] using orth
      have h' : ∑ k, (P k i:ℝ) * (P k i:ℝ) = (Fintype.card F:ℝ) := by exact_mod_cast h
      rw [h', ←sq, hws]; simp [hcount]
    · have hij' := Subtype.coe_injective.ne hij
      have h : ∑ k, P k i * P k j = 0 := by simpa [P, Matrix.mul_apply, hij'] using orth
      have h' : ∑ k, (P k i:ℝ) * (P k j:ℝ) = 0 := by exact_mod_cast h
      rw [h']; simp [hij]

end PaleyBlock

#print axioms paleyBlock_det


/-- Filling the zeros of a symmetric conference matrix with opposite signs on
two equal parts gives the four-fifths bound at orders at least 126. -/
theorem balancedFill_det_of_moment_or_large {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B D : Matrix ι ι ℝ)
    (hA : Aᵀ = A) (hD : Dᵀ = D)
    (hAd : ∀ i, A i i = 0) (hDd : ∀ i, D i i = 0)
    (hAo : ∀ i j, i ≠ j → (A i j)^2 = 1)
    (hDo : ∀ i j, i ≠ j → (D i j)^2 = 1)
    (hv : 15 ≤ Fintype.card ι)
    (haCert : 63≤Fintype.card ι ∨ momentCondition (Fintype.card ι:ℝ) (A*A*A).trace)
    (hdCert : 63≤Fintype.card ι ∨ momentCondition (Fintype.card ι:ℝ) ((-D)*(-D)*(-D)).trace)
    (hc : let C := fromBlocks A B Bᵀ D
          C*C = (2*(Fintype.card ι:ℝ)-1) • (1 : Matrix _ _ ℝ)) :
    4 * W (Fintype.card ι) ≤ 5 *
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
  have hp : 0 ≤ 4*W (Fintype.card ι) := by
    have hh : (15:ℝ) ≤ Fintype.card ι := by exact_mod_cast hv
    unfold W
    exact mul_nonneg (by norm_num) (mul_nonneg (by linarith) (pow_nonneg (by linarith) _))
  have H' := mul_le_mul hdetA hdetD hp (hp.trans hdetA)
  change 4 * W (Fintype.card ι) ≤ 5*|N.det|
  have hab := sq_abs N.det
  dsimp only [t] at H
  nlinarith [abs_nonneg N.det]

theorem balancedFill_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B D : Matrix ι ι ℝ)
    (hA : Aᵀ = A) (hD : Dᵀ = D)
    (hAd : ∀ i, A i i = 0) (hDd : ∀ i, D i i = 0)
    (hAo : ∀ i j, i ≠ j → (A i j)^2 = 1)
    (hDo : ∀ i j, i ≠ j → (D i j)^2 = 1)
    (hv : 63 ≤ Fintype.card ι)
    (hc : let C := fromBlocks A B Bᵀ D
          C*C = (2*(Fintype.card ι:ℝ)-1) • (1 : Matrix _ _ ℝ)) :
    4 * W (Fintype.card ι) ≤ 5 *
      |(fromBlocks (A+1) B Bᵀ (D-1)).det| :=
  balancedFill_det_of_moment_or_large A B D hA hD hAd hDd hAo hDo (by omega) (Or.inl hv) (Or.inl hv) hc

#print axioms balancedFill_det

/-- The integer determinant of an arbitrary balanced filling of a symmetric
conference matrix satisfies the spectral lower bound at order at least 126. -/
theorem intFill_det_of_moment_or_large {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (C : Matrix (ι ⊕ ι) (ι ⊕ ι) ℤ) (h : Conference q C)
    (hq : q+1 = 2*Fintype.card ι) (hv : 15 ≤ Fintype.card ι)
    (hAc : 63≤Fintype.card ι ∨ momentCondition (Fintype.card ι:ℝ) ((C.toBlocks₁₁*C.toBlocks₁₁*C.toBlocks₁₁).trace:ℝ))
    (hDc : 63≤Fintype.card ι ∨ momentCondition (Fintype.card ι:ℝ) (((-C.toBlocks₂₂)*(-C.toBlocks₂₂)*(-C.toBlocks₂₂)).trace:ℝ)) :
    4 * W (Fintype.card ι) ≤ 5 * |((diagonalFill C).det : ℝ)| := by
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
  have hcA : 63≤Fintype.card ι ∨ momentCondition (Fintype.card ι:ℝ) (A*A*A).trace := by
    rcases hAc with hl|hm
    · exact Or.inl hl
    · rw [cast_cube] at hm; exact Or.inr hm
  have hcD : 63≤Fintype.card ι ∨ momentCondition (Fintype.card ι:ℝ) ((-D)*(-D)*(-D)).trace := by
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

theorem intFill_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (C : Matrix (ι ⊕ ι) (ι ⊕ ι) ℤ) (h : Conference q C)
    (hq : q+1 = 2*Fintype.card ι) (hv : 63 ≤ Fintype.card ι) :
    4 * W (Fintype.card ι) ≤ 5 * |((diagonalFill C).det : ℝ)| :=
  intFill_det_of_moment_or_large C h hq (by omega) (Or.inl hv) (Or.inl hv)

end NearHadamard
