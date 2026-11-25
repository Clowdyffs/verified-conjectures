module

public import Conjectures.NearHadamard.Border
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic

@[expose] public section
open Matrix

namespace NearHadamard.Torus

abbrev v (q : ℕ) := (q+1)/2

def b {E : Type*} [Monoid E] (q : ℕ) (z : E) := z^(2*(q-1))
def alpha {E : Type*} [Monoid E] (q : ℕ) (z : E) := z^(v q)

theorem group_size {q : ℕ} (hq : q%4=1) :
    2*(q-1)*v q = q*q-1 := by
  have hn : 1 ≤ q := by omega
  have h : 2*v q=q+1 := by dsimp [v]; omega
  have h1 := Nat.sub_add_cancel hn
  have h2 := congrArg (fun t : ℕ => (q-1)*t) h
  have h3 := Nat.sub_add_cancel (show 1 ≤ q*q by nlinarith)
  nlinarith

section Roots
variable {E : Type*} [Field E] {q : ℕ} {z : E}

theorem step_order (hq : q%4=1) (hn : 1<q) (hz : IsPrimitiveRoot z (q*q-1)) :
    IsPrimitiveRoot (b q z) (v q) := by
  have hp : 0 < 2*(q-1) := by omega
  have h := group_size hq
  have H := hz.pow_of_dvd hp.ne' (Dvd.intro _ h)
  simpa only [b, ←h, Nat.mul_div_cancel_left _ hp] using H

theorem alpha_frobenius (hq : q%4=1) (hn : 1<q) (hz : IsPrimitiveRoot z (q*q-1)) :
    (alpha q z)^q = -alpha q z := by
  let e := (q-1)*v q
  have h2 : e*2 = q*q-1 := by dsimp [e]; rw [←group_size hq]; ring
  have hp : 0 < e := Nat.mul_pos (by omega) (by dsimp [v]; omega)
  have ha := hz.pow_ne_one_of_pos_of_lt hp.ne' (by omega : e < q*q-1)
  have hsq : (z^e)^2 = 1 := by rw [←pow_mul,h2,hz.pow_eq_one]
  have he := (sq_eq_one_iff.mp hsq).resolve_left ha
  have hex : v q*q = e+v q := by
    calc v q*q = ((q-1)+1)*v q := by rw [Nat.sub_add_cancel (by omega : 1≤q), Nat.mul_comm]
         _ = _ := by dsimp [e]; ring
  rw [alpha, ←pow_mul, hex, pow_add, he, neg_one_mul]

def point (q : ℕ) (z : E) (i : Fin (v q)) : E := (b q z)^i.val

theorem point_pow (hq : q%4=1) (hn : 1<q) (hz : IsPrimitiveRoot z (q*q-1)) (i : Fin (v q)) :
    (point q z i)^(v q) = 1 := by
  unfold point
  rw [←pow_mul, Nat.mul_comm, pow_mul, (step_order hq hn hz).pow_eq_one, one_pow]

theorem ratio_pow (hq : q%4=1) (hn : 1<q) (hz : IsPrimitiveRoot z (q*q-1)) (i j : Fin (v q)) :
    (point q z j / point q z i)^(v q) = 1 := by
  rw [div_pow,point_pow hq hn hz,point_pow hq hn hz,div_one]

theorem qpow_inv {x : E} (hq : q%4=1) (hn : 1<q) (h : x^(v q)=1) : x^q = x⁻¹ := by
  have hfrac : q+1=v q*2 := by dsimp [v]; omega
  have he : x^q*x=1 := by rw [←pow_succ,hfrac,pow_mul,h,one_pow]
  exact eq_inv_of_mul_eq_one_left he

theorem neg_one_ne_of_odd {x : E} (hm : (-1:E) ≠ 1) (hq : q%4=1) (h : x^(v q)=1) :
    x ≠ -1 := by
  rintro rfl
  have hodd : Odd (v q) := ⟨q/4, by dsimp [v]; omega⟩
  exact hm ((hodd.neg_one_pow).symm.trans h)

end Roots

section Model
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : F}
abbrev Model (d : F) := QuadraticAlgebra F d 0

theorem irreducible (h : quadraticChar F d = -1) : ∀ r : F, r^2 ≠ d+0*r := by
  intro r he
  have hn := quadraticChar_neg_one_iff_not_isSquare.mp h
  apply hn
  exact ⟨r, by simpa [sq] using he.symm⟩

theorem frobenius (hq : Fintype.card F % 4 = 1) (hd : quadraticChar F d = -1) (a : Model d) :
    a^(Fintype.card F) = star a := by
  let t : Model d := QuadraticAlgebra.omega
  let f := FiniteField.frobeniusAlgHom F (Model d)
  have hw : d^(Fintype.card F / 2) = -1 := by
    rw [←quadraticChar_eq_pow_of_char_ne_two' (Border.char_ne_two hq), hd]
    norm_num
  have ht : t^2 = algebraMap F (Model d) d := by
    rw [sq]; simpa [t] using (QuadraticAlgebra.omega_mul_omega_eq_algebraMap (a:=d) (b:=0))
  have hpow : f t = -t := by
    change t^(Fintype.card F) = -t
    have e : Fintype.card F = 2*(Fintype.card F/2)+1 := by omega
    conv_lhs => rw [e, pow_succ, pow_mul, ht, ←map_pow, hw, map_neg, map_one, neg_one_mul]
  change f a = star a
  rcases a with ⟨x,y⟩
  rw [QuadraticAlgebra.mk_eq_add_smul_omega, map_add, AlgHom.commutes, map_smul]
  change _ + y • f t = _
  rw [hpow]
  ext <;> simp [t]

/-- The trace in the square-root basis, as an element of the ground field. -/
def tr (a : Model d) : F := 2*a.re

theorem trace_eq (hq : Fintype.card F % 4=1) (hd : quadraticChar F d = -1) (a : Model d) :
    a+a^(Fintype.card F) = algebraMap F (Model d) (tr a) := by
  rw [frobenius hq hd]
  ext <;> simp [tr] <;> ring

theorem member_eq (hq : Fintype.card F % 4=1) (hd : quadraticChar F d = -1) (a : Model d) :
    Source.sign ((a+a^(Fintype.card F))^((Fintype.card F-1)/2)=1) =
      quadraticChar F (tr a) - if tr a=0 then 1 else 0 := by
  have hhalf : (Fintype.card F-1)/2 = Fintype.card F/2 := by omega
  have hn := Fintype.one_lt_card (α:=F)
  rw [trace_eq hq hd, ←map_pow, hhalf]
  have hmap (x : F) : algebraMap F (Model d) x = 1 ↔ x=1 :=
    (map_one (algebraMap F (Model d))) ▸ (algebraMap F (Model d)).injective.eq_iff
  unfold Source.sign
  simp only [hmap]
  by_cases e : tr a=0
  · simp [Source.sign, e, zero_pow (by omega : Fintype.card F/2 ≠ 0)]
  · simp [e, quadraticChar_eq_pow_of_char_ne_two (Border.char_ne_two hq) e,
      -quadraticChar_apply]

def wedge (x y : Model d) := x.re*y.im-x.im*y.re

def project (x : Model d) : Option F := if x.re=0 then none else some (x.im/x.re)
def scale (x : Model d) : F := if x.re=0 then x.im else x.re

theorem scale_ne {x : Model d} (hx : x ≠ 0) : scale x ≠ 0 := by
  by_cases h : x.re=0
  · simp only [scale, h, ↓reduceIte]
    exact fun hi => hx (QuadraticAlgebra.ext h hi)
  · simpa [scale,h]

theorem project_eq_wedge {x y : Model d} (hx : x ≠ 0) (hy : y ≠ 0) :
    project x = project y ↔ wedge x y = 0 := by
  by_cases a : x.re=0 <;> by_cases b : y.re=0
  · simp [project,wedge,a,b]
  · have h := scale_ne hx
    simp [scale,a] at h
    simp [project,wedge,a,b,h]
  · have h := scale_ne hy
    simp [scale,b] at h
    simp [project,wedge,a,b,h]
  · simp only [project, if_neg a, if_neg b, Option.some.injEq, div_eq_div_iff a b,
      wedge, sub_eq_zero]
    constructor <;> intro e <;> simpa only [mul_comm, eq_comm] using e

theorem wedge_paley (hq : Fintype.card F % 4=1) (x y : Model d) :
    quadraticChar F (wedge x y) =
      quadraticChar F (scale x)*paley F (project x) (project y)*quadraticChar F (scale y) := by
  have hneg (a : F) : quadraticChar F (-a) = quadraticChar F a := by
    simpa only [zero_sub, sub_zero] using Border.sym_char hq 0 a
  by_cases a : x.re=0 <;> by_cases b : y.re=0
  · simp [project,scale,wedge,a,b,paley]
  · simp [project,scale,wedge,a,b,paley,hneg,map_mul,-quadraticChar_apply]
  · simp [project,scale,wedge,a,b,paley,map_mul,-quadraticChar_apply]
  · have ee : wedge x y = x.re*(y.im/y.re-x.im/x.re)*y.re := by unfold wedge; field_simp
    rw [ee, map_mul, map_mul, Border.sym_char hq (y.im/y.re) (x.im/x.re)]
    simp [project,scale,a,b,paley,-quadraticChar_apply]

theorem trace_scalar (r : F) (x : Model d) :
    tr (algebraMap F (Model d) r*x) = r*tr x := by simp [tr]; ring

theorem trace_wedge {a : Model d} (ha : a.re=0) (x y : Model d) :
    tr (a*star x*y) = (2*d*a.im)*wedge x y := by simp [tr,wedge,ha]; ring

variable [Fact (∀ r : F, r^2 ≠ d+0*r)]
local notation "q" => Fintype.card F
local notation "E" => Model d
local notation "τ" => fun (z : E) (i j : Fin (v q)) => point q z j / point q z i

theorem model_neg_one (hq : q%4=1) : (-1:E) ≠ 1 := by
  intro h
  exact Ring.neg_one_ne_one_of_char_ne_two (Border.char_ne_two hq)
    (show -(1:F)=1 from congrArg QuadraticAlgebra.re h)

theorem alpha_re (hq : q%4=1) (hd : quadraticChar F d = -1)
    {z : E} (hz : IsPrimitiveRoot z (q*q-1)) : (alpha q z).re = 0 := by
  have h := alpha_frobenius hq Fintype.one_lt_card hz
  rw [frobenius hq hd] at h
  have he := congrArg QuadraticAlgebra.re h
  simp only [QuadraticAlgebra.re_star, zero_mul, add_zero, QuadraticAlgebra.re_neg] at he
  have h2 : (2:F) ≠ 0 := fun H => Ring.neg_one_ne_one_of_char_ne_two (Border.char_ne_two hq)
    (by linear_combination -H)
  exact (mul_eq_zero.mp (show 2*(alpha q z).re=0 by linear_combination he)).resolve_left h2

theorem alpha_ne {z : E} (hz : IsPrimitiveRoot z (q*q-1)) : alpha q z ≠ 0 := by
  have hq := Fintype.one_lt_card (α:=F)
  have hN : 1 < q*q := by nlinarith
  exact pow_ne_zero _ (hz.isUnit (by omega)).ne_zero

def alphaSq (z : E) : F := d*(alpha q z).im^2

theorem alpha_square (hq : q%4=1) (hd : quadraticChar F d = -1)
    {z : E} (hz : IsPrimitiveRoot z (q*q-1)) :
    (alpha q z)^2 = algebraMap F E (alphaSq z) := by
  ext <;> simp [sq, alphaSq,alpha_re hq hd hz]; ring

theorem char_alpha_square (hq : q%4=1) (hd : quadraticChar F d = -1)
    {z : E} (hz : IsPrimitiveRoot z (q*q-1)) : quadraticChar F (alphaSq z) = -1 := by
  have hn : (alpha q z).im ≠ 0 := fun h => alpha_ne hz (QuadraticAlgebra.ext (alpha_re hq hd hz) h)
  rw [alphaSq,map_mul,hd,quadraticChar_sq_one' hn, mul_one]

theorem star_ratio (hq : q%4=1) (hd : quadraticChar F d = -1)
    {z : E} (hz : IsPrimitiveRoot z (q*q-1)) (i j : Fin (v q)) :
    star (point q z i)*point q z j = τ z i j := by
  rw [←frobenius hq hd, qpow_inv hq Fintype.one_lt_card (point_pow hq Fintype.one_lt_card hz i)]
  exact (div_eq_inv_mul ..).symm

theorem trace_nonzero (hq : q%4=1) (hd : quadraticChar F d = -1)
    {z : E} (hz : IsPrimitiveRoot z (q*q-1)) (i j : Fin (v q)) :
    tr (τ z i j) ≠ 0 := by
  let t := τ z i j
  have ht : t^(v q) = 1 := ratio_pow hq Fintype.one_lt_card hz i j
  have h0 : t ≠ 0 := fun h => by
    simpa [h, zero_pow (by dsimp [v]; omega : v q ≠ 0)] using ht
  intro e
  have he := trace_eq hq hd t
  rw [show tr t=0 from e, map_zero, qpow_inv hq Fintype.one_lt_card ht] at he
  have h2 : t^2 = -1 := by
    have hh := congrArg (fun a : E => a*t) he
    simp only [add_mul, inv_mul_cancel₀ h0, zero_mul] at hh
    linear_combination hh
  have hpower : (t^2)^(v q)=1 := by rw [←pow_mul,Nat.mul_comm,pow_mul,ht,one_pow]
  exact neg_one_ne_of_odd (model_neg_one hq) hq hpower h2

theorem trace_alpha_zero (hq : q%4=1) (hd : quadraticChar F d = -1)
    {z : E} (hz : IsPrimitiveRoot z (q*q-1)) (i j : Fin (v q)) :
    tr (alpha q z*(τ z i j)) = 0 ↔ i=j := by
  let t := τ z i j
  have ht : t^(v q) = 1 := ratio_pow hq Fintype.one_lt_card hz i j
  have hsq := step_order hq Fintype.one_lt_card hz
  have hn : v q ≠ 0 := by dsimp [v]; omega
  have hi : point q z i ≠ 0 := pow_ne_zero _ (hsq.isUnit hn).ne_zero
  have h0 : t ≠ 0 := fun h => by simpa [h,zero_pow hn] using ht
  constructor
  · intro e
    have he := trace_eq hq hd (alpha q z*t)
    rw [show tr (alpha q z*t)=0 from e, map_zero, mul_pow, alpha_frobenius hq Fintype.one_lt_card hz,
      qpow_inv hq Fintype.one_lt_card ht] at he
    have he' : t=t⁻¹ :=
      (mul_left_cancel₀ (alpha_ne hz)) (by linear_combination he)
    have hh : t^2=1 := by rw [sq]; nth_rw 1 [he']; exact inv_mul_cancel₀ h0
    have ht1 := (sq_eq_one_iff.mp hh).resolve_right (neg_one_ne_of_odd (model_neg_one hq) hq ht)
    exact Fin.ext (hsq.pow_inj i.isLt j.isLt ((div_eq_one_iff_eq hi).mp ht1).symm)
  · rintro rfl
    simpa [div_self hi,tr,alpha_re hq hd hz]

def U (z : E) : Matrix (Fin (v q)) (Fin (v q)) ℤ := fun i j => quadraticChar F (tr (τ z i j))
def V (z : E) : Matrix (Fin (v q)) (Fin (v q)) ℤ := fun i j => quadraticChar F (tr (alpha q z*(τ z i j)))

def rep (z : E) : Fin (v q) ⊕ Fin (v q) → E
  | .inl i => point q z i
  | .inr i => alpha q z * point q z i

def formEntry (z : E) : Matrix (Fin (v q) ⊕ Fin (v q)) (Fin (v q) ⊕ Fin (v q)) ℤ :=
  fun i j => quadraticChar F (tr (alpha q z * star (rep z i) * rep z j))

/-- The projective character matrix in the two torus cosets has blocks V,-U,-U,-V. -/
theorem form_blocks (hq : q%4=1) (hd : quadraticChar F d = -1)
    {z : E} (hz : IsPrimitiveRoot z (q*q-1)) :
    (formEntry z : Matrix _ _ ℤ) = fromBlocks (V z) (-U z) (-U z) (-V z) := by
  have hs : star (alpha q z) = -alpha q z := (frobenius hq hd _).symm.trans (alpha_frobenius hq Fintype.one_lt_card hz)
  have hneg (a : F) : quadraticChar F (-a) = quadraticChar F a := by
    simpa only [zero_sub, sub_zero] using Border.sym_char hq 0 a
  have hnegTr (a : E) : tr (-a) = -tr a := by simp [tr]
  have sq (x : E) : quadraticChar F (tr ((alpha q z)^2*x)) = -quadraticChar F (tr x) := by
    rw [alpha_square hq hd hz, trace_scalar, map_mul, char_alpha_square hq hd hz, neg_one_mul]
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · change quadraticChar F (tr (alpha q z*star (point q z i)*point q z j)) = _
    rw [mul_assoc,star_ratio hq hd hz]; rfl
  · change quadraticChar F (tr (alpha q z*star (point q z i)*(alpha q z*point q z j))) = _
    rw [show alpha q z*star (point q z i)*(alpha q z*point q z j) =
      (alpha q z)^2*(star (point q z i)*point q z j) by ring, sq,star_ratio hq hd hz]; rfl
  · change quadraticChar F (tr (alpha q z*star (alpha q z*point q z i)*point q z j)) = _
    rw [star_mul,hs,show alpha q z*(star (point q z i)* -alpha q z)*point q z j =
      -((alpha q z)^2*(star (point q z i)*point q z j)) by ring,
      hnegTr,hneg,sq,star_ratio hq hd hz]; rfl
  · change quadraticChar F (tr (alpha q z*star (alpha q z*point q z i)*(alpha q z*point q z j))) = _
    rw [star_mul,hs,show alpha q z*(star (point q z i)* -alpha q z)*(alpha q z*point q z j) =
      -((alpha q z)^2*(alpha q z*(star (point q z i)*point q z j))) by ring,
      hnegTr,hneg,sq,star_ratio hq hd hz]; rfl

theorem rep_nonzero (hq : q%4=1) {z : E} (hz : IsPrimitiveRoot z (q*q-1))
    (i : Fin (v q) ⊕ Fin (v q)) : rep z i ≠ 0 := by
  have hn : v q ≠ 0 := by dsimp [v]; omega
  have hnz := ((step_order hq Fintype.one_lt_card hz).isUnit hn).ne_zero
  cases i with
  | inl i => exact pow_ne_zero _ hnz
  | inr i => exact mul_ne_zero (alpha_ne hz) (pow_ne_zero _ hnz)

theorem kernel_entry (hq : q%4=1) (hd : quadraticChar F d = -1)
    {z : E} (hz : IsPrimitiveRoot z (q*q-1)) (i j : Fin (v q) ⊕ Fin (v q)) :
    formEntry z i j = 0 ↔ i=j := by
  have H := congrFun (congrFun (form_blocks hq hd hz) i) j
  rw [H]
  rcases i with i|i <;> rcases j with j|j <;>
    simp [Matrix.fromBlocks,V,U,-quadraticChar_apply,quadraticChar_eq_zero_iff,
      trace_nonzero hq hd hz, trace_alpha_zero hq hd hz]

theorem project_rep_bijective (hq : q%4=1) (hd : quadraticChar F d = -1)
    {z : E} (hz : IsPrimitiveRoot z (q*q-1)) :
    Function.Bijective (fun i => project (rep z i)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro i j he
    have h := (project_eq_wedge (rep_nonzero hq hz i) (rep_nonzero hq hz j)).mp he
    apply (kernel_entry hq hd hz i j).mp
    rw [formEntry, trace_wedge (alpha_re hq hd hz), h, mul_zero, quadraticChar_zero]
  · simp [v]; omega

theorem conference (hq : q%4=1) (hd : quadraticChar F d = -1)
    {z : E} (hz : IsPrimitiveRoot z (q*q-1)) :
    Conference q (-(formEntry z) : Matrix _ _ ℤ) := by
  let e := Equiv.ofBijective _ (project_rep_bijective hq hd hz)
  let w (i : Fin (v q) ⊕ Fin (v q)) := quadraticChar F (scale (rep z i))
  let k := 2*d*(alpha q z).im
  have hd0 : d ≠ 0 := fun h => by simpa [h] using hd
  have hi0 : (alpha q z).im ≠ 0 := fun h => alpha_ne hz (QuadraticAlgebra.ext (alpha_re hq hd hz) h)
  have h2 : (2:F) ≠ 0 := fun H => Ring.neg_one_ne_one_of_char_ne_two (Border.char_ne_two hq)
    (by linear_combination -H)
  have hk : k ≠ 0 := mul_ne_zero (mul_ne_zero h2 hd0) hi0
  have hC := ((conference_paley hq).relabel e (-quadraticChar F k)
    (by rw [neg_sq,quadraticChar_sq_one hk])).switch w
      (fun i => quadraticChar_sq_one (scale_ne (rep_nonzero hq hz i)))
  have he : -formEntry z = (fun i j => w i * (-(quadraticChar F k)*paley F (e i) (e j))*w j : Matrix _ _ ℤ) := by
    ext i j
    change -quadraticChar F (tr (alpha q z*star (rep z i)*rep z j)) =
      quadraticChar F (scale (rep z i)) *
        (-(quadraticChar F k)*paley F (project (rep z i)) (project (rep z j))) *
        quadraticChar F (scale (rep z j))
    rw [trace_wedge (alpha_re hq hd hz), map_mul, wedge_paley hq]
    dsimp [k]; ring
  rw [he]
  exact hC

theorem source_form (hq : q%4=1) (hd : quadraticChar F d = -1)
    {z : E} (hz : IsPrimitiveRoot z (q*q-1)) :
    Source.class4 q z = fromBlocks (U z) (V z-1 : Matrix _ _ ℤ) (V z-1) (-U z) := by
  let P := (formEntry z : Matrix _ _ ℤ)
  have hs (i j) : P i j = P j i := by
    have H := (conference hq hd hz).symm i j
    exact neg_injective H
  have hu (i j) : U z i j = U z j i := by
    have h := hs (.inl i) (.inr j)
    change (formEntry z : Matrix _ _ ℤ) _ _ = (formEntry z : Matrix _ _ ℤ) _ _ at h
    rw [form_blocks hq hd hz] at h
    exact neg_injective h
  have hv (i j) : V z i j = V z j i := by
    have h := hs (.inl i) (.inl j)
    change (formEntry z : Matrix _ _ ℤ) _ _ = (formEntry z : Matrix _ _ ℤ) _ _ at h
    rw [form_blocks hq hd hz] at h; exact h
  let f (x : E) := Source.sign ((x+x^q)^((q-1)/2)=1)
  have hs0 := step_order hq Fintype.one_lt_card hz
  have hA (i j : Fin (v q)) : f ((b q z)^Source.shift i j) = U z i j := by
    rw [Border.pow_shift hs0]; change Source.sign _ = _
    rw [member_eq hq hd]
    change quadraticChar F (tr (τ z i j)) - (if tr (τ z i j)=0 then 1 else 0) = _
    simp [U,trace_nonzero hq hd hz i j,-quadraticChar_apply]
  have hB (i j : Fin (v q)) : f ((b q z)^Source.shift i j*alpha q z) = (V z-1 : Matrix _ _ ℤ) i j := by
    rw [Border.pow_shift hs0, mul_comm]; change Source.sign _ = _
    rw [member_eq hq hd]
    change quadraticChar F (tr (alpha q z*τ z i j)) -
      (if tr (alpha q z*τ z i j)=0 then 1 else 0) = _
    simp only [trace_alpha_zero hq hd hz, Matrix.sub_apply, Matrix.one_apply, V]
  have ha : (fun i j => f ((b q z)^Source.shift i j)) = U z := funext fun i => funext (hA i)
  have hb : (fun i j => f ((b q z)^Source.shift i j*alpha q z)) = (V z-1 : Matrix _ _ ℤ) := funext fun i => funext (hB i)
  unfold Source.class4
  change fromBlocks _ _ ((fun i j => f ((b q z)^Source.shift i j*alpha q z) : Matrix _ _ ℤ)ᵀ)
      (-((fun i j => f ((b q z)^Source.shift i j) : Matrix _ _ ℤ)ᵀ)) = _
  have huT : (U z : Matrix _ _ ℤ)ᵀ = U z := by ext i j; exact hu j i
  have hvT : (V z : Matrix _ _ ℤ)ᵀ = V z := by ext i j; exact hv j i
  change fromBlocks (fun i j => f ((b q z)^Source.shift i j))
      (fun i j => f ((b q z)^Source.shift i j*alpha q z)) _ _ = _
  rw [ha,hb,transpose_sub,hvT,transpose_one,huT]

theorem abs_source (hq : q%4=1) (hd : quadraticChar F d = -1)
    {z : E} (hz : IsPrimitiveRoot z (q*q-1)) :
    |(Source.class4 q z).det| = |(diagonalFill (-(formEntry z) : Matrix _ _ ℤ)).det| := by
  let M := Source.class4 q z
  let e := Equiv.sumComm (Fin (v q)) (Fin (v q))
  let s (i : Fin (v q) ⊕ Fin (v q)) : ℤ := Sum.elim (fun _ => -1) (fun _ => 1) i
  have he : diagonalFill (-(formEntry z) : Matrix _ _ ℤ) =
      M.submatrix (Equiv.refl _) e * diagonal s := by
    rw [show M = _ from source_form hq hd hz, form_blocks hq hd hz]
    ext i j
    rcases i with i|i <;> rcases j with j|j <;> by_cases hij : i=j <;>
      simp [diagonalFill, Matrix.mul_diagonal, e, s, fromBlocks, hij, Matrix.one_apply,
        Matrix.sub_apply] <;> ring
  have hsign (i) : |s i| = 1 := by cases i <;> norm_num [s]
  rw [he, det_mul, abs_mul, abs_det_submatrix_equiv_equiv, det_diagonal, Finset.abs_prod]
  simp [hsign,M]

theorem same_alpha_character (hq : q%4=1) (hd : quadraticChar F d = -1)
    {z z' : E} (hz : IsPrimitiveRoot z (q*q-1)) (hz' : IsPrimitiveRoot z' (q*q-1))
    {r : F} (hr : quadraticChar F r=1) (ha : alpha q z = algebraMap F E r*alpha q z') :
    (Source.class4 q z).det = (Source.class4 q z').det := by
  letI : NeZero (v q) := ⟨by dsimp [v]; omega⟩
  have h0 := step_order hq Fintype.one_lt_card hz
  have h1 := step_order hq Fintype.one_lt_card hz'
  have hx (i : Fin (v q)) : ∃ j : Fin (v q), point q z' j = point q z i := by
    obtain ⟨k,hk,he⟩ := h1.eq_pow_of_pow_eq_one (point_pow hq Fintype.one_lt_card hz i)
    exact ⟨⟨k,hk⟩,he⟩
  choose f hf using hx
  have hi : Function.Injective f := by
    intro i j hij
    exact Fin.ext (h0.pow_inj i.isLt j.isLt (by change point q z i = point q z j; rw [←hf i,hij,hf j]))
  let e := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hi,rfl⟩)
  have hU (i j) : U z' (e i) (e j) = U z i j := by change U z' (f i) (f j) = _; simp only [U,hf]
  have hV (i j) : V z' (e i) (e j) = V z i j := by
    change V z' (f i) (f j) = _
    simp only [V,hf,ha,mul_assoc,trace_scalar,map_mul,hr,one_mul]
  let perm := Equiv.sumCongr e e
  have hM : Source.class4 q z = (Source.class4 q z').submatrix perm perm := by
    rw [source_form hq hd hz,source_form hq hd hz']
    ext i j; rcases i with i|i <;> rcases j with j|j <;>
      simp [perm, fromBlocks, Matrix.sub_apply, Matrix.one_apply, hU, hV, e.injective.eq_iff]
  rw [hM,det_submatrix_equiv_self]

theorem primitive_choices (hq : q%4=1) (hd : quadraticChar F d = -1)
    {z z' : E} (hz : IsPrimitiveRoot z (q*q-1)) (hz' : IsPrimitiveRoot z' (q*q-1)) :
    (Source.class4 q z).det = (Source.class4 q z').det ∨
    (Source.class4 q z).det = (Source.class4 q z'⁻¹).det := by
  let r := (alpha q z).im / (alpha q z').im
  have hi {x : E} (hx : IsPrimitiveRoot x (q*q-1)) : (alpha q x).im ≠ 0 :=
    fun he => alpha_ne hx (QuadraticAlgebra.ext (alpha_re hq hd hx) he)
  have hr : r ≠ 0 := div_ne_zero (hi hz) (hi hz')
  have ha : alpha q z = algebraMap F E r*alpha q z' := by
    apply QuadraticAlgebra.ext
    · simp [alpha_re hq hd hz,alpha_re hq hd hz']
    · change _ = r*(alpha q z').im + 0*(alpha q z').re + 0*0*(alpha q z').im
      simp [r,hi hz']
  rcases quadraticChar_dichotomy hr with h|h
  · exact Or.inl (same_alpha_character hq hd hz hz' h ha)
  · apply Or.inr
    apply same_alpha_character hq hd hz hz'.inv (r:=r*alphaSq z')
    · rw [map_mul,h,char_alpha_square hq hd hz']; norm_num
    · have hinv : alpha q z'⁻¹ = (alpha q z')⁻¹ := inv_pow ..
      rw [hinv,ha,map_mul,←alpha_square hq hd hz',mul_assoc,sq,mul_assoc,mul_inv_cancel₀ (alpha_ne hz'),mul_one]

end Model
/-- Changing the finite-field model transports the generator and leaves every
entry of the Class (4) sign matrix fixed. -/
theorem transport {E E' : Type*} [Field E] [Field E'] [DecidableEq E] [DecidableEq E']
    (e : E ≃+* E') (q : ℕ) (z : E) : Source.class4 q (e z) = Source.class4 q z := by
  have ho (x : E) : e x=1 ↔ x=1 := (map_one e) ▸ e.injective.eq_iff
  unfold Source.class4
  simp only [Source.sign, ←map_pow, ←map_mul, ←map_add, ho]

end NearHadamard.Torus
