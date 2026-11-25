module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

@[expose] public section
open Finset

namespace NearHadamard

theorem log_quartic {x : ℝ} (hx : |x| ≤ 9/50) :
    x - x^2/2 + x^3/3 - x^4/3 ≤ Real.log (1+x) := by
  have hlt : |-x| < 1 := by rw [abs_neg]; linarith
  have H := (abs_le.mp (Real.abs_log_sub_add_sum_range_le hlt 5)).1
  rw [abs_neg, sub_neg_eq_add] at H
  simp [sum_range_succ] at H
  have he : |x|^6 / (1-|x|) ≤ x^4/25 := by
    apply (div_le_iff₀ (by linarith : 0<1-|x|)).mpr
    have hp : |x|^2 ≤ (9/50:ℝ)^2 := by gcongr
    have eq4 : |x|^4=x^4 := by rw [←abs_pow,abs_of_nonneg (by positivity)]
    calc |x|^6 = |x|^4 * |x|^2 := by ring
         _ ≤ x^4*(9/50)^2 := by rw [eq4]; gcongr
         _ ≤ x^4/25*(1-|x|) := by
           have : (9/50:ℝ)^2 ≤ (1-|x|)/25 := by linarith
           nlinarith [mul_nonneg (sub_nonneg.mpr this) (show 0≤x^4 by positivity)]
  have h5 : -(9/50)*x^4 ≤ x^5 := by
    have h1 : -(9/50) ≤ x := by linarith [(abs_le.mp hx).1]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show 0≤x^4 by positivity)]
  nlinarith [show 0≤x^4 by positivity]

/-- A fourth-order lower bound valid up to the largest normalized spectral
radius required at order 30. -/
theorem log_moment {x : ℝ} (hx : |x| ≤ 9/25) :
    x-x^2/2+x^3/3-(3/8)*x^4 ≤ Real.log (1+x) := by
  have hlt : |-x| < 1 := by rw [abs_neg]; linarith
  have H := (abs_le.mp (Real.abs_log_sub_add_sum_range_le hlt 8)).1
  rw [abs_neg,sub_neg_eq_add] at H
  simp [sum_range_succ] at H
  have hcomp (k : ℕ) : |x|^(4+k) ≤ x^4*(9/25)^k := by
    rw [pow_add, ←abs_pow,abs_of_nonneg (show 0≤x^4 by positivity)]
    gcongr
  have p5 : -(x^4*(9/25)) ≤ x^5 := by
    have h := neg_abs_le (x^5)
    rw [abs_pow] at h
    linarith [show |x|^5 ≤ _ from hcomp 1]
  have p6 : x^6 ≤ x^4*(9/25)^2 := by
    simpa only [←abs_pow,abs_of_nonneg (by positivity : 0≤x^6)] using hcomp 2
  have p7 : -(x^4*(9/25)^3) ≤ x^7 := by
    have h := neg_abs_le (x^7)
    rw [abs_pow] at h
    linarith [show |x|^7 ≤ _ from hcomp 3]
  have p8 : x^8 ≤ x^4*(9/25)^4 := by
    simpa only [←abs_pow,abs_of_nonneg (by positivity : 0≤x^8)] using hcomp 4
  have p9 : |x|^9/(1-|x|) ≤ (1/100)*x^4 := by
    apply (div_le_iff₀ (by linarith : 0<1-|x|)).mpr
    have h9 := hcomp 5
    have he : (9/25:ℝ)^5 ≤ 1/100*(1-|x|) := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr he) (show 0≤x^4 by positivity)]
  nlinarith [show 0≤x^4 by positivity]

theorem log_minus {r : ℝ} (h0 : 0 ≤ r) (hr : r ≤ 1/10) :
    Real.log (1-r) ≤ -r-r^2/2 := by
  have h : |r| < 1 := by rw [abs_of_nonneg h0]; linarith
  have H := (abs_le.mp (Real.abs_log_sub_add_sum_range_le h 3)).2
  simp [sum_range_succ,abs_of_nonneg h0] at H
  have he : r^4/(1-r) ≤ r^3/3 := by
    apply (div_le_iff₀ (by linarith : 0<1-r)).mpr
    nlinarith [mul_nonneg (show 0≤r^3 by positivity) (show 0 ≤ 1-4*r by linarith)]
  linarith

/-- A quadratic minorant obtained from (x+a)(x-a/2)²(1-x) ≥ 0 preserves the
combined third- and fourth-order contributions to the logarithm. -/
theorem log_minorant {x a : ℝ} (hx : |x| ≤ a) (ha : a ≤ 179/1000) :
    (1+a^2/4+a^3/12)*x - (1/2+a^2/4)*x^2 - a^3/12 ≤ Real.log (1+x) := by
  have h1 : 0 ≤ x+a := by linarith [(abs_le.mp hx).1]
  have h2 : 0 ≤ 1-x := by linarith [(abs_le.mp hx).2]
  have H := log_quartic (x:=x) (by linarith)
  nlinarith [mul_nonneg (mul_nonneg h1 (sq_nonneg (x-a/2))) h2]

theorem scale_compare (n : ℕ) (hn : 15≤n) (P : ℝ) (hp : 0<P)
    (hlog : 4701/10000-1+((n:ℝ)⁻¹)^2/2 ≤ Real.log P) :
    4*((2-(n:ℝ)⁻¹)*(1-(n:ℝ)⁻¹)^(n-1)) ≤ 5*P := by
  let v : ℝ := n
  let r := v⁻¹
  have hv' : 15 ≤ v := by dsimp [v]; exact_mod_cast hn
  have vp : 0<v := by linarith
  have rp : 0<r := inv_pos.mpr vp
  have small : r ≤ 1/15 := by dsimp [r]; rw [inv_eq_one_div]; gcongr
  have vr : v*r=1 := mul_inv_cancel₀ vp.ne'
  change 4701/10000-1+r^2/2 ≤ Real.log P at hlog
  have hr1 : 0 < 1-r := by linarith
  have h2 : 0 < 2-r := by linarith
  have h2' : 0 < 1-r/2 := by linarith
  have ha1 : Real.log (1-r) ≤ -r-r^2/2 := log_minus rp.le (by linarith)
  have ha2 : Real.log (1-r/2) ≤ -r/2 := by linarith [Real.log_le_sub_one_of_pos h2']
  have hm : ((n-1:ℕ):ℝ)=v-1 := by
    rw [Nat.cast_sub (by omega : 1≤n), Nat.cast_one]
  have hs1 : 4*((2-r)*(1-r)^(n-1)) > 0 := by positivity
  have hs2 : 0 < 5*P := mul_pos (by norm_num) hp
  apply (Real.log_le_log_iff hs1 hs2).mp
  change Real.log (4*((2-r)*(1-r)^(n-1))) ≤ _
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul h2.ne' (by positivity),
    Real.log_pow, hm, show 2-r=2*(1-r/2) by ring, Real.log_mul (by norm_num) h2'.ne',
    Real.log_mul (by norm_num) hp.ne']
  have hc : Real.log 4+Real.log 2-Real.log 5 ≤ 4701/10000 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    linarith [Real.log_two_lt_d9,Real.log_five_gt_d9]
  have hm' := mul_le_mul_of_nonneg_left ha1 (show 0≤v-1 by linarith)
  have he : (v-1)*(-r-r^2/2) = -1+r/2+r^2/2 := by
    linear_combination -(1+r/2)*vr
  rw [he] at hm'
  linarith
/-- Comparison of the normalized product with four fifths of the normalized
Ehlich–Wojtas bound at half-orders at least 63. -/
theorem sharp_product {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hv : 63 ≤ Fintype.card ι)
    (hz : ∑ i, x i = 0)
    (hs : ∑ i, (x i)^2 = 1 - (Fintype.card ι:ℝ)⁻¹)
    (hcap : ∀ i, (x i)^2 ≤ 2/(Fintype.card ι:ℝ)) :
    4*((2-(Fintype.card ι:ℝ)⁻¹)*(1-(Fintype.card ι:ℝ)⁻¹)^(Fintype.card ι-1)) ≤
      5*∏ i, (1+x i) := by
  let v : ℝ := Fintype.card ι
  let r := v⁻¹
  let a := Real.sqrt (2*r)
  have hv' : 63 ≤ v := by dsimp [v]; exact_mod_cast hv
  have vp : 0<v := by linarith
  have rp : 0<r := inv_pos.mpr vp
  have small : r ≤ 1/63 := by dsimp [r]; rw [inv_eq_one_div]; gcongr
  have vr : v*r=1 := mul_inv_cancel₀ vp.ne'
  have a2 : a^2=2*r := Real.sq_sqrt (by positivity)
  have ha : a ≤ 179/1000 := by nlinarith [Real.sqrt_nonneg (2*r)]
  have cap (i) : |x i| ≤ a := by
    have H : (x i)^2 ≤ 2*r := by simpa [r,v,div_eq_mul_inv] using hcap i
    nlinarith [sq_abs (x i),abs_nonneg (x i),Real.sqrt_nonneg (2*r)]
  have hp (i) : 0 < 1+x i := by linarith [(abs_le.mp (cap i)).1]
  have hprod := sum_le_sum (s:=univ) (fun i _ => log_minorant (cap i) ha)
  simp only [sum_sub_distrib, ←mul_sum, hz, mul_zero, zero_sub, sum_const, card_univ,
    nsmul_eq_mul, hs] at hprod
  have hp' : -1/2 + r^2/2 - a/6 ≤ Real.log (∏ i, (1+x i)) := by
    rw [Real.log_prod (fun i _ => (hp i).ne')]
    change -((1/2+a^2/4)*(1-r))-v*(a^3/12) ≤ _ at hprod
    have a3 : v*a^3=2*a := by calc
      _ = (v*a^2)*a := by ring
      _ = _ := by rw [a2]; linear_combination 2*a*vr
    nlinarith
  apply scale_compare _ (by omega) _ (prod_pos fun i _ => hp i)
  change 4701/10000-1+r^2/2 ≤ _
  linarith

/-- The finite certificate checks a rational inequality involving only the
order and the exact integer trace of the cube of the sign matrix. -/
def momentCondition {R : Type*} [Field R] [LinearOrder R] (v t : R) : Prop :=
  4701/10000-1+v⁻¹^2/2 ≤ -(1-v⁻¹)/2 + t/v^3/3 - (3/8)*((2*v-1)/v^2)*(1-v⁻¹)

theorem moment_product {ι : Type*} [Fintype ι] (x : ι → ℝ) (hv : 15≤Fintype.card ι)
    (hz : ∑ i, x i=0) (hs : ∑ i, (x i)^2=1-(Fintype.card ι:ℝ)⁻¹)
    (hcap : ∀ i, (x i)^2 ≤ (2*(Fintype.card ι:ℝ)-1)/(Fintype.card ι:ℝ)^2)
    (t : ℝ) (ht : ∑ i, (x i)^3 = t/(Fintype.card ι:ℝ)^3)
    (hm : momentCondition (Fintype.card ι:ℝ) t) :
    4*((2-(Fintype.card ι:ℝ)⁻¹)*(1-(Fintype.card ι:ℝ)⁻¹)^(Fintype.card ι-1)) ≤
      5*∏ i, (1+x i) := by
  let v : ℝ := Fintype.card ι
  have hv' : (15:ℝ)≤v := by dsimp [v]; exact_mod_cast hv
  have vp : 0<v := by linarith
  let c := (2*v-1)/v^2
  have hc : c ≤ (9/25:ℝ)^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos vp)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hv') (show 0≤81*v-40 by linarith)]
  have cap (i) : |x i| ≤ 9/25 := by
    have h : (x i)^2 ≤ (9/25)^2 := (hcap i).trans hc
    nlinarith [sq_abs (x i),abs_nonneg (x i)]
  have h4 (i) : (x i)^4 ≤ c*(x i)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (hcap i)) (sq_nonneg (x i))]
  have lb (i) : x i - (x i)^2/2+(x i)^3/3-(3*c/8)*(x i)^2 ≤ Real.log (1+x i) := by
    linarith [log_moment (cap i),h4 i]
  have hp (i) : 0<1+x i := by linarith [(abs_le.mp (cap i)).1]
  apply scale_compare _ hv _ (prod_pos fun i _ => hp i)
  rw [Real.log_prod (fun i _ => (hp i).ne')]
  have h := sum_le_sum (s:=univ) (fun i _ => lb i)
  simp only [sum_sub_distrib,sum_add_distrib,←sum_div,←mul_sum,hz,hs,ht] at h
  unfold momentCondition at hm
  dsimp [c,v] at h
  linarith

end NearHadamard
