module
public import Conjectures.NearHadamard.Bounds
import Mathlib.Tactic
@[expose] public section
open Finset Matrix
namespace NearHadamard.Optimal
theorem scale_compare_opt (n : ℕ) (hn : 15≤n) (P : ℝ) (hp : 0<P)
    (hlog : 4928/10000-1+((n:ℝ)⁻¹)^2/2 ≤ Real.log P) :
    81844*((2-(n:ℝ)⁻¹)*(1-(n:ℝ)⁻¹)^(n-1)) ≤ 100000*P := by
  let v : ℝ := n
  let r := v⁻¹
  have hv' : 15 ≤ v := by dsimp [v]; exact_mod_cast hn
  have vp : 0<v := by linarith
  have rp : 0<r := inv_pos.mpr vp
  have small : r ≤ 1/15 := by dsimp [r]; rw [inv_eq_one_div]; gcongr
  have vr : v*r=1 := mul_inv_cancel₀ vp.ne'
  change 4928/10000-1+r^2/2 ≤ Real.log P at hlog
  have hr1 : 0 < 1-r := by linarith
  have h2 : 0 < 2-r := by linarith
  have h2' : 0 < 1-r/2 := by linarith
  have ha1 : Real.log (1-r) ≤ -r-r^2/2 := log_minus rp.le (by linarith)
  have ha2 : Real.log (1-r/2) ≤ -r/2 := by linarith [Real.log_le_sub_one_of_pos h2']
  have hm : ((n-1:ℕ):ℝ)=v-1 := by
    rw [Nat.cast_sub (by omega : 1≤n), Nat.cast_one]
  have hs1 : 81844*((2-r)*(1-r)^(n-1)) > 0 := by positivity
  have hs2 : 0 < 100000*P := mul_pos (by norm_num) hp
  apply (Real.log_le_log_iff hs1 hs2).mp
  change Real.log (81844*((2-r)*(1-r)^(n-1))) ≤ _
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul h2.ne' (by positivity),
    Real.log_pow, hm, show 2-r=2*(1-r/2) by ring, Real.log_mul (by norm_num) h2'.ne',
    Real.log_mul (by norm_num) hp.ne']
  have hc : Real.log 81844+Real.log 2-Real.log 100000 ≤ 4928/10000 := by
    rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_div (by norm_num) (by norm_num)]
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 4928/10000) 8
    norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
    linarith
  have hm' := mul_le_mul_of_nonneg_left ha1 (show 0≤v-1 by linarith)
  have he : (v-1)*(-r-r^2/2) = -1+r/2+r^2/2 := by
    linear_combination -(1+r/2)*vr
  rw [he] at hm'
  linarith
/-- The normalized ratio is at least 81844/100000 at half-orders of at least 1080. -/
theorem tail_product {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hv : 1080 ≤ Fintype.card ι)
    (hz : ∑ i, x i = 0)
    (hs : ∑ i, (x i)^2 = 1 - (Fintype.card ι:ℝ)⁻¹)
    (hcap : ∀ i, (x i)^2 ≤ 2/(Fintype.card ι:ℝ)) :
    81844*((2-(Fintype.card ι:ℝ)⁻¹)*(1-(Fintype.card ι:ℝ)⁻¹)^(Fintype.card ι-1)) ≤
      100000*∏ i, (1+x i) := by
  let v : ℝ := Fintype.card ι
  let r := v⁻¹
  let a := Real.sqrt (2*r)
  have hv' : 1080 ≤ v := by dsimp [v]; exact_mod_cast hv
  have vp : 0<v := by linarith
  have rp : 0<r := inv_pos.mpr vp
  have small : r ≤ 1/1080 := by dsimp [r]; rw [inv_eq_one_div]; gcongr
  have vr : v*r=1 := mul_inv_cancel₀ vp.ne'
  have a2 : a^2=2*r := Real.sq_sqrt (by positivity)
  have ha : a ≤ 431/10000 := by nlinarith [Real.sqrt_nonneg (2*r)]
  have cap (i) : |x i| ≤ a := by
    have H : (x i)^2 ≤ 2*r := by simpa [r,v,div_eq_mul_inv] using hcap i
    nlinarith [sq_abs (x i),abs_nonneg (x i),Real.sqrt_nonneg (2*r)]
  have hp (i) : 0 < 1+x i := by linarith [(abs_le.mp (cap i)).1]
  have hprod := sum_le_sum (s:=univ) (fun i _ => log_minorant (cap i) (by linarith))
  simp only [sum_sub_distrib, ←mul_sum, hz, mul_zero, zero_sub, sum_const, card_univ,
    nsmul_eq_mul, hs] at hprod
  have hp' : -1/2 + r^2/2 - a/6 ≤ Real.log (∏ i, (1+x i)) := by
    rw [Real.log_prod (fun i _ => (hp i).ne')]
    change -((1/2+a^2/4)*(1-r))-v*(a^3/12) ≤ _ at hprod
    have a3 : v*a^3=2*a := by calc
      _ = (v*a^2)*a := by ring
      _ = _ := by rw [a2]; linear_combination 2*a*vr
    nlinarith
  apply scale_compare_opt _ (by omega) _ (prod_pos fun i _ => hp i)
  change 4928/10000-1+r^2/2 ≤ _
  linarith

/-- The finite certificate checks a rational inequality involving only the
order and the exact integer trace of the cube of the sign matrix. -/
def cubeCondition {R : Type*} [Field R] [LinearOrder R] (v t : R) : Prop :=
  4928/10000-1+v⁻¹^2/2 ≤ -(1-v⁻¹)/2 + t/v^3/3 - (3/8)*((2*v-1)/v^2)*(1-v⁻¹)

theorem cube_product {ι : Type*} [Fintype ι] (x : ι → ℝ) (hv : 15≤Fintype.card ι)
    (hz : ∑ i, x i=0) (hs : ∑ i, (x i)^2=1-(Fintype.card ι:ℝ)⁻¹)
    (hcap : ∀ i, (x i)^2 ≤ (2*(Fintype.card ι:ℝ)-1)/(Fintype.card ι:ℝ)^2)
    (t : ℝ) (ht : ∑ i, (x i)^3 = t/(Fintype.card ι:ℝ)^3)
    (hm : cubeCondition (Fintype.card ι:ℝ) t) :
    81844*((2-(Fintype.card ι:ℝ)⁻¹)*(1-(Fintype.card ι:ℝ)⁻¹)^(Fintype.card ι-1)) ≤
      100000*∏ i, (1+x i) := by
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
  apply scale_compare_opt _ hv _ (prod_pos fun i _ => hp i)
  rw [Real.log_prod (fun i _ => (hp i).ne')]
  have h := sum_le_sum (s:=univ) (fun i _ => lb i)
  simp only [sum_sub_distrib,sum_add_distrib,←sum_div,←mul_sum,hz,hs,ht] at h
  unfold cubeCondition at hm
  dsimp [c,v] at h
  linarith

end NearHadamard.Optimal
