module

public import Conjectures.NearHadamard.Statement
public import Conjectures.NearHadamard.Conference
import Mathlib.Tactic

@[expose] public section
open Matrix
namespace NearHadamard.Border

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev core (q : ℕ) := Fin ((q-1)/2)
abbrev half (q : ℕ) := Option (core q)
abbrev idx (q : ℕ) := half q ⊕ half q

def squareLabel (w : F) {q : ℕ} (i : core q) : F := (w^2)^i.val

def label (w : F) {q : ℕ} : idx q → Option F
  | .inl none => some 0
  | .inr none => none
  | .inl (some i) => some (squareLabel w i)
  | .inr (some i) => some (squareLabel w i / w)

omit [DecidableEq F] in
theorem char_ne_two (h : Fintype.card F % 4 = 1) : ringChar F ≠ 2 := by
  intro e
  have := FiniteField.even_card_of_char_two e
  omega

theorem char_generator {w : F} (hq : Fintype.card F % 4 = 1)
    (hw : IsPrimitiveRoot w (Fintype.card F-1)) : quadraticChar F w = -1 := by
  have h := Fintype.one_lt_card (α := F)
  have nz := (hw.isUnit (by omega)).ne_zero
  rw [quadraticChar_eq_pow_of_char_ne_two (char_ne_two hq) nz]
  simp [hw.pow_ne_one_of_pos_of_lt (by omega : Fintype.card F / 2 ≠ 0) (by omega)]

theorem char_squareLabel {q : ℕ} {w : F} (hw : w ≠ 0) (i : core q) :
    quadraticChar F (squareLabel w i) = 1 := by
  simp only [squareLabel, map_pow, quadraticChar_sq_one hw, one_pow]

theorem char_negativeLabel {q : ℕ} {w : F} (hw : w ≠ 0) (hwχ : quadraticChar F w = -1)
    (i : core q) : quadraticChar F (squareLabel w i / w) = -1 := by
  have hm : (squareLabel w i/w)*w = squareLabel w i := div_mul_cancel₀ _ hw
  have H := congrArg (quadraticChar F) hm
  rw [map_mul, hwχ, char_squareLabel hw] at H
  linarith

theorem label_bijective {w : F} (hq : Fintype.card F % 4 = 1)
    (hw : IsPrimitiveRoot w (Fintype.card F-1)) :
    Function.Bijective (label (q:=Fintype.card F) w) := by
  let q := Fintype.card F
  have hn : 1 < q := Fintype.one_lt_card
  have hw0 : w ≠ 0 := (hw.isUnit (by omega)).ne_zero
  have hsq : IsPrimitiveRoot (w^2) ((q-1)/2) := hw.pow_of_dvd (by decide) (by omega)
  have hin : Function.Injective (squareLabel (q:=q) w) :=
    fun i j e => Fin.ext (hsq.pow_inj i.isLt j.isLt e)
  have hnz (i : core q) : squareLabel w i ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hw0)
  have hdis (i j : core q) : squareLabel w i ≠ squareLabel w j / w := by
    intro h
    have he := congrArg (quadraticChar F) h
    rw [char_squareLabel hw0, char_negativeLabel hw0 (char_generator hq hw)] at he
    omega
  have Hne (i : core q) : squareLabel w i / w ≠ 0 := div_ne_zero (hnz i) hw0
  have Hneq (i j : core q) : squareLabel w i/w = squareLabel w j/w ↔ i=j := by
    rw [div_left_inj' hw0, hin.eq_iff]
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b h
    rcases a with (_|_)|(_|_) <;> rcases b with (_|_)|(_|_) <;>
      simp only [label, Option.some.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
        hin.eq_iff, Hneq] at h ⊢
    all_goals first
      | assumption
      | exact False.elim (hnz _ h)
      | exact False.elim (hnz _ h.symm)
      | exact False.elim (Hne _ h)
      | exact False.elim (Hne _ h.symm)
      | exact False.elim (hdis _ _ h)
      | exact False.elim (hdis _ _ h.symm)
  · simp [idx, half, core]
    omega

omit [Fintype F] [DecidableEq F] in
theorem pow_shift {m : ℕ} {b : F} (hb : IsPrimitiveRoot b m) (i j : Fin m) :
    b ^ Source.shift i j = b^j.val / b^i.val := by
  have hn : m ≠ 0 := (Nat.zero_lt_of_lt i.isLt).ne'
  have hnz := (hb.isUnit hn).ne_zero
  apply (eq_div_iff (pow_ne_zero _ hnz)).mpr
  dsimp [Source.shift]
  have hm (t : ℕ) : b^(t%m) = b^t := by rw [hb.eq_orderOf, pow_mod_orderOf]
  rw [hm, ←pow_add, Nat.sub_add_cancel (by omega : i.val ≤ j.val+m), pow_add, hb.pow_eq_one, mul_one]

def c (five : Bool) : ℤ := if five then 1 else -1

theorem character_member (hq : Fintype.card F % 4 = 1) (five : Bool) (t : F) :
    Source.borderMember (Fintype.card F) five t =
      -c five * quadraticChar F (t-1) - if t=1 then 1 else 0 := by
  have hn := Fintype.one_lt_card (α:=F)
  have hcard : (Fintype.card F-1)/2 = Fintype.card F/2 := by omega
  have hn1 := Ring.neg_one_ne_one_of_char_ne_two (char_ne_two hq)
  have ep := quadraticChar_eq_pow_of_char_ne_two' (char_ne_two hq) (t-1)
  unfold Source.borderMember Source.sign
  rw [hcard, ←ep]
  by_cases ht : t=1
  · subst t
    cases five <;> simp [c]
  · rcases quadraticChar_dichotomy (sub_ne_zero.mpr ht) with h|h <;>
      cases five <;> simp [ht, h, c, hn1, Ne.symm hn1, -quadraticChar_apply]

theorem sym_char (hq : Fintype.card F % 4 = 1) (a b : F) :
    quadraticChar F (a-b) = quadraticChar F (b-a) := by
  have hn : quadraticChar F (-1) = 1 :=
    (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr (one_ne_zero' F))).mpr
      (FiniteField.isSquare_neg_one_iff.mpr (by omega))
  rw [show a-b = -1*(b-a) by ring, map_mul, hn, one_mul]

theorem ratio_char {a : F} (hna : a ≠ 0) (ha : quadraticChar F a = 1) (b : F) :
    quadraticChar F (b/a-1) = quadraticChar F (b-a) := by
  have h : (b/a-1)*a = b-a := by field_simp
  rw [←h, map_mul, ha, mul_one]

theorem sourceA {w : F} (hq : Fintype.card F % 4 = 1)
    (hw : IsPrimitiveRoot w (Fintype.card F-1)) (five : Bool) (i j : core (Fintype.card F)) :
    Source.borderA (Fintype.card F) w five i j =
      -c five * quadraticChar F (squareLabel w i - squareLabel w j) -
        if i=j then 1 else 0 := by
  have hn := Fintype.one_lt_card (α:=F)
  have hw0 : w ≠ 0 := (hw.isUnit (by omega)).ne_zero
  have hs := hw.pow_of_dvd (p:=2) (by decide) (by omega)
  have nz := pow_ne_zero (i:ℕ) (pow_ne_zero 2 hw0)
  have hi : squareLabel w i ≠ 0 := nz
  have he : squareLabel w j / squareLabel w i = 1 ↔ i=j := by
    rw [div_eq_one_iff_eq hi]
    exact ⟨fun h => Fin.ext (hs.pow_inj i.isLt j.isLt h.symm), fun h => h ▸ rfl⟩
  rw [Source.borderA, pow_shift hs, character_member hq]
  change -c five * quadraticChar F (squareLabel w j / squareLabel w i - 1) -
      (if squareLabel w j / squareLabel w i = 1 then 1 else 0) = _
  rw [ratio_char hi (char_squareLabel hw0 i), sym_char hq (squareLabel w j)]
  simp only [he]

theorem sourceB {w : F} (hq : Fintype.card F % 4 = 1)
    (hw : IsPrimitiveRoot w (Fintype.card F-1)) (five : Bool) (i j : core (Fintype.card F)) :
    Source.borderB (Fintype.card F) w five i j =
      -c five * quadraticChar F (squareLabel w i - squareLabel w j / w) := by
  have hn := Fintype.one_lt_card (α:=F)
  have hw0 : w ≠ 0 := (hw.isUnit (by omega)).ne_zero
  have hs := hw.pow_of_dvd (p:=2) (by decide) (by omega)
  have hi : squareLabel w i ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hw0)
  have he : squareLabel w j / w / squareLabel w i ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hi]
    intro h
    have hh := congrArg (quadraticChar F) h
    rw [char_negativeLabel hw0 (char_generator hq hw), char_squareLabel hw0] at hh
    omega
  rw [Source.borderB, pow_shift hs, character_member hq]
  change -c five * quadraticChar F (squareLabel w j / squareLabel w i / w - 1) -
      (if squareLabel w j / squareLabel w i / w = 1 then 1 else 0) = _
  rw [div_right_comm, ratio_char hi (char_squareLabel hw0 i), sym_char hq (squareLabel w j / w),
    ite_eq_right_iff.mpr (fun h => (he h).elim), sub_zero]

def swapEnds {q : ℕ} : idx q → idx q
  | .inl none => .inr none
  | .inr none => .inl none
  | .inl (some i) => .inl (some i)
  | .inr (some i) => .inr (some i)

def swapEquiv (q : ℕ) : idx q ≃ idx q where
  toFun := swapEnds
  invFun := swapEnds
  left_inv := by rintro ((_|_)|(_|_)) <;> rfl
  right_inv := by rintro ((_|_)|(_|_)) <;> rfl

def rowPerm (q : ℕ) (five : Bool) : idx q ≃ idx q :=
  if five then swapEquiv q else Equiv.refl _

def rowSign {q : ℕ} (five : Bool) : idx q → ℤ
  | .inl (some _) => -1
  | .inr (some _) => -c five
  | _ => c five

def colSign {q : ℕ} (five : Bool) : idx q → ℤ
  | .inl none | .inr none => -c five
  | _ => 1

/-- Signed Paley matrix with the diagonal filled by +1 on the squares and zero,
and by -1 on the nonsquares and the point at infinity. -/
def filled {q : ℕ} (w : F) (five : Bool) : Matrix (idx q) (idx q) ℤ :=
  fun i j => c five * paley F (label w i) (label w j) +
    if i=j then Sum.elim (fun _ => 1) (fun _ => -1) i else 0

/-- In Class (5) the two entries connecting zero and infinity in the signed
presentation have reversed signs. -/
def corrected {q : ℕ} (w : F) (five : Bool) : Matrix (idx q) (idx q) ℤ :=
  fun i j => filled w five i j -
    if five && ((i == .inl none && j == .inr none) || (i == .inr none && j == .inl none))
    then 2 else 0

set_option maxHeartbeats 2000000 in
theorem source_entry {w : F} (hq : Fintype.card F % 4 = 1)
    (hw : IsPrimitiveRoot w (Fintype.card F-1)) (five : Bool)
    (i j : idx (Fintype.card F)) :
    Source.bordered (Fintype.card F) w five i j =
      rowSign five i * corrected w five (rowPerm _ five i) (swapEquiv _ j) * colSign five j := by
  have hn := Fintype.one_lt_card (α:=F)
  have hw0 : w ≠ 0 := (hw.isUnit (by omega)).ne_zero
  have hσ := char_generator hq hw
  have negChar (a : F) : quadraticChar F (-a) = quadraticChar F a := by
    simpa only [zero_sub, sub_zero] using sym_char hq 0 a
  have divChar (a b : F) : quadraticChar F (a/w-b/w) = -quadraticChar F (a-b) := by
    have h : (a/w-b/w)*w = a-b := by field_simp
    have hh := congrArg (quadraticChar F) h
    rw [map_mul, hσ] at hh
    linarith
  cases five <;> rcases i with (_|i)|(_|i) <;> rcases j with (_|j)|(_|j) <;>
    simp [Source.bordered, Matrix.fromBlocks, corrected, filled, rowPerm, swapEquiv, swapEnds,
      rowSign, colSign, label, paley, sourceA hq hw, sourceB hq hw,
      quadraticChar_eq_zero_iff, char_squareLabel hw0, char_negativeLabel hw0 hσ, divChar, negChar, c, -quadraticChar_apply]

  all_goals first
    | exact sym_char hq _ _
    | solve | abel
    | rw [sym_char hq (squareLabel w j) (squareLabel w i)]; by_cases h : i=j <;>
        simp [h, eq_comm]

theorem abs_det_source {w : F} (hq : Fintype.card F % 4 = 1)
    (hw : IsPrimitiveRoot w (Fintype.card F-1)) (five : Bool) :
    |(Source.bordered (Fintype.card F) w five).det| =
    |(corrected (q:=Fintype.card F) w five).det| := by
  let q := Fintype.card F
  let K := corrected (q:=q) w five
  have H : Source.bordered q w five =
      diagonal (rowSign five) * K.submatrix (rowPerm q five) (swapEquiv q) *
        diagonal (colSign five) := by
    ext i j
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using source_entry hq hw five i j
  have hr (i : idx q) : |rowSign five i| = 1 := by
    rcases i with (_|_)|(_|_) <;> cases five <;> norm_num [rowSign, colSign, c]
  have hc (i : idx q) : |colSign five i| = 1 := by
    rcases i with (_|_)|(_|_) <;> cases five <;> norm_num [rowSign, colSign, c]
  change |(Source.bordered q w five).det| = |K.det|
  rw [H, Matrix.det_mul, Matrix.det_mul, abs_mul, abs_mul, Matrix.det_diagonal,
    Matrix.det_diagonal, Finset.abs_prod, Finset.abs_prod]
  simp [hr,hc]

def C {q : ℕ} (w : F) (five : Bool) : Matrix (idx q) (idx q) ℤ :=
  fun i j => c five * paley F (label w i) (label w j)

theorem conference {w : F} (hq : Fintype.card F % 4 = 1)
    (hw : IsPrimitiveRoot w (Fintype.card F-1)) (five : Bool) :
    Conference (Fintype.card F) (C (q:=Fintype.card F) w five) :=
  (conference_paley hq).relabel (Equiv.ofBijective _ (label_bijective hq hw))
    (c five) (by cases five <;> decide)

def cornerSign {q : ℕ} : idx q → ℤ
  | .inr none => -1
  | _ => 1

set_option maxHeartbeats 2000000 in
/-- Reversing the two exceptional corner entries in Class (5) interchanges the
two border coordinates of the Gram matrix and negates one border row and column. -/
theorem correctedGram {w : F} (hq : Fintype.card F % 4 = 1)
    (hw : IsPrimitiveRoot w (Fintype.card F-1)) (i j : idx (Fintype.card F)) :
    let K := filled (q:=Fintype.card F) w true
    let R := corrected (q:=Fintype.card F) w true
    (R*Rᵀ) i j = cornerSign i * (K*Kᵀ) (swapEnds i) (swapEnds j) * cornerSign j := by
  let q := Fintype.card F
  let K := filled (q:=q) w true
  let R := corrected (q:=q) w true
  let u : idx q := .inl none
  let v : idx q := .inr none
  have hiL (a : idx q) (k : core q) : R a (.inl (some k)) = K a (.inl (some k)) := by
    simp [R,K,corrected]
  have hiR (a : idx q) (k : core q) : R a (.inr (some k)) = K a (.inr (some k)) := by
    simp [R,K,corrected]
  have delta : (R*Rᵀ) i j = (K*Kᵀ) i j + R i u * R j u - K i u * K j u +
      R i v * R j v - K i v * K j v := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, Fintype.sum_option,
      hiL, hiR, u, v]
    abel
  have form (a b : idx q) : (K*Kᵀ) a b =
      (if a=b then (q:ℤ)+1 else 0) +
      (halfSign a + halfSign b)*C w true a b := fillGram (conference hq hw true) a b
  change (R*Rᵀ) i j = cornerSign i * (K*Kᵀ) (swapEnds i) (swapEnds j) * cornerSign j
  rw [delta, form, form]
  have hn := Fintype.one_lt_card (α:=F)
  have hw0 : w ≠ 0 := (hw.isUnit (by omega)).ne_zero
  have hσ := char_generator hq hw
  have negChar (a : F) : quadraticChar F (-a) = quadraticChar F a := by
    simpa only [zero_sub, sub_zero] using sym_char hq 0 a
  rcases i with (_|i)|(_|i) <;> rcases j with (_|j)|(_|j) <;>
    simp [C,K,R,corrected,filled,u,v,label,cornerSign,halfSign,swapEnds,paley,c,
      char_squareLabel hw0, char_negativeLabel hw0 hσ, negChar, quadraticChar_eq_zero_iff,
      quadraticChar_zero, -quadraticChar_apply] <;> ring

theorem abs_corrected {w : F} (hq : Fintype.card F % 4 = 1)
    (hw : IsPrimitiveRoot w (Fintype.card F-1)) (five : Bool) :
    |(corrected (q:=Fintype.card F) w five).det| = |(filled (q:=Fintype.card F) w five).det| := by
  cases five with
  | false =>
    have h : corrected (q:=Fintype.card F) w false = filled (q:=Fintype.card F) w false := by
      ext i j; simp [corrected]
    rw [h]
  | true =>
    let q := Fintype.card F
    let K := filled (q:=q) w true
    let R := corrected (q:=q) w true
    let e := swapEquiv q
    let D := diagonal (cornerSign (q:=q))
    have h : R*Rᵀ = D * (K*Kᵀ).submatrix e e * D := by
      ext i j
      simpa [D, Matrix.diagonal_mul, Matrix.mul_diagonal, e, swapEquiv] using correctedGram hq hw i j
    have hD : D.det^2 = 1 := by
      have h2 : D*D = 1 := by
        rw [show D = diagonal (cornerSign (q:=q)) by rfl, diagonal_mul_diagonal]
        ext i j
        by_cases h : i=j
        · subst j; rcases i with (_|_)|(_|_) <;> simp [cornerSign]
        · simp [h, diagonal_apply, one_apply]
      have H := congrArg Matrix.det h2
      simpa [sq, Matrix.det_mul] using H
    have H := congrArg Matrix.det h
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_submatrix_equiv_self] at H
    change |R.det| = |K.det|
    apply (sq_eq_sq_iff_abs_eq_abs _ _).mp
    calc R.det^2 = D.det^2 * K.det^2 := by rw [sq, H]; ring
         _ = _ := by rw [hD, one_mul]

/-- The side of the balanced partition is intrinsic to the projective point. -/
def side : Option F → ℤ
  | none => -1
  | some x => if x=0 then 1 else quadraticChar F x

theorem label_side {w : F} (hq : Fintype.card F % 4=1) (hw : IsPrimitiveRoot w (Fintype.card F-1))
    (i : idx (Fintype.card F)) : side (label w i) = halfSign i := by
  have hn := Fintype.one_lt_card (α:=F)
  have hw0 : w ≠ 0 := (hw.isUnit (by omega)).ne_zero
  have h0 (i : core (Fintype.card F)) : squareLabel w i ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hw0)
  rcases i with (_|i)|(_|i) <;> simp [side,label,halfSign,h0,hw0,char_squareLabel hw0,
    char_negativeLabel hw0 (char_generator hq hw),-quadraticChar_apply]

theorem primitive_independent {w z : F} (hq : Fintype.card F % 4=1)
    (hw : IsPrimitiveRoot w (Fintype.card F-1)) (hz : IsPrimitiveRoot z (Fintype.card F-1))
    (five : Bool) :
    |(Source.bordered (Fintype.card F) w five).det| = |(Source.bordered (Fintype.card F) z five).det| := by
  rw [abs_det_source hq hw, abs_corrected hq hw, abs_det_source hq hz, abs_corrected hq hz]
  let ew := Equiv.ofBijective _ (label_bijective hq hw)
  let ez := Equiv.ofBijective _ (label_bijective hq hz)
  let e := ew.trans ez.symm
  have he (i) : label z (e i) = label w i := ez.apply_symm_apply (ew i)
  have hs (i) : halfSign (e i) = halfSign i := by rw [←label_side hq hz, he, label_side hq hw]
  have hM : filled (q:=Fintype.card F) w five = (filled z five).submatrix e e := by
    ext i j
    change c five*paley F (label w i) (label w j)+(if i=j then halfSign i else 0) =
      c five*paley F (label z (e i)) (label z (e j))+(if e i=e j then halfSign (e i) else 0)
    simp only [he, e.injective.eq_iff, hs]
  rw [hM, det_submatrix_equiv_self]

theorem transport {F' : Type*} [Field F'] [DecidableEq F'] (e : F ≃+* F') (q : ℕ) (w : F)
    (five : Bool) : Source.bordered q (e w) five = Source.bordered q w five := by
  have htest (x : F) : Source.borderMember q five (e x) = Source.borderMember q five x := by
    have he : (e x-1)^((q-1)/2) = e ((x-1)^((q-1)/2)) := by simp
    have ho (y : F) : e y=1 ↔ y=1 := (map_one e) ▸ e.injective.eq_iff
    have hm (y : F) : e y= -1 ↔ y= -1 := (show e (-1) = -1 by simp) ▸ e.injective.eq_iff
    cases five <;> simp only [Source.borderMember, he, Source.sign, Bool.false_eq_true,
      ↓reduceIte, ho, hm]
  unfold Source.bordered Source.borderA Source.borderB
  simp only [←map_pow,←map_div₀,htest]

end NearHadamard.Border
