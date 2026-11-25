module
public import Conjectures.NearHadamardSharp.Exact
import Mathlib.Tactic
@[expose] public section
open Finset Matrix
namespace NearHadamard.Optimal

private theorem pack_succ (b : ℤ) {n : ℕ} (f : Fin (n+1) → ℤ) :
    pack b f = f 0 + b*pack b (fun i => f i.succ) := by
  simp only [pack,Fin.sum_univ_succ,Int.cast_id,Fin.val_zero,pow_zero,mul_one,
    Fin.val_succ,pow_succ,Finset.mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  ring

private theorem prefix_zero (b : ℤ) (hb : 0<b) {n : ℕ} (f : Fin n → ℤ) (m : ℕ)
    (h : b^m ∣ pack b f) (hs : ∀ j, |f j| < b) (j : Fin n) (hj : j.val<m) : f j=0 := by
  induction n generalizing m with
  | zero => exact j.elim0
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      rw [pack_succ,pow_succ'] at h
      have hzero : f 0=0 :=
        Int.eq_zero_of_abs_lt_dvd ((dvd_add_left (dvd_mul_right _ _)).mp
          ((dvd_mul_right _ _).trans h)) (hs 0)
      rw [hzero,zero_add] at h
      have ht : b^m ∣ pack b (fun i => f i.succ) := (mul_dvd_mul_iff_left hb.ne').mp h
      refine Fin.cases (fun _ => hzero) (fun i hi => ?_) j hj
      exact ih _ _ ht (fun k => hs k.succ) i (by simpa using hi)

/-- Pack each row of A once. A modular identity then checks a complete prefix
of the triangularized row by one scalar product. -/
def packedRows {n : ℕ} (b : ℤ) (A : Matrix (Fin n) (Fin n) ℤ) : Array ℤ :=
  Array.ofFn (fun i => pack b (A i))

theorem packedCert {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (rows : Array (Array ℤ))
    (p : Array ℤ) (d a l b : ℤ)
    (ha : ∀ i j, |A i j| ≤ a) (hl : ∀ i j : Fin n, |lowerMatrix rows i j| ≤ l)
    (hp : ∀ i : Fin n, |p[i.val]!| < b - (n:ℤ)*l*a) (hb : (n:ℤ)*l*a < b) (hpos : 0<b)
    (hc : ∀ i : Fin n, ((∑ k : Fin n, lowerMatrix rows i k * (packedRows b A)[k.val]!) -
       p[i.val]!*b^i.val) % b^(i.val+1) = 0)
    (hn : (∏ i : Fin n, lowerMatrix rows i i) ≠ 0)
    (he : (∏ i : Fin n, lowerMatrix rows i i)*d = ∏ i : Fin n, p[i.val]!) : A.det=d := by
  let L : Matrix (Fin n) (Fin n) ℤ := lowerMatrix rows
  apply triangularCert A L d (fun i => p[i.val]!) _ _ hn he
  · intro i j hh; simp [L,lowerMatrix,not_le.mpr hh]
  intro i j hji
  let v (j : Fin n) := (L*A) i j - if i=j then p[i.val]! else 0
  have hpack : pack b v = (∑ k, L i k * (packedRows b A)[k.val]!) - p[i.val]!*b^i.val := by
    simp only [pack,v,Int.cast_id,sub_mul,Finset.sum_sub_distrib,Matrix.mul_apply,Finset.sum_mul,
      packedRows, Array.size_ofFn,Fin.is_lt,getElem!_pos,Array.getElem_ofFn,Fin.eta]
    rw [Finset.sum_comm]
    simp [Finset.mul_sum,mul_assoc,ite_mul]
  have hv (k : Fin n) : |(L*A) i k| ≤ (n:ℤ)*l*a := by
    rw [Matrix.mul_apply]
    calc
      _ ≤ ∑ j, |L i j * A j k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, l*a := sum_le_sum fun j _ => by
        rw [abs_mul]; exact mul_le_mul (hl _ _) (ha _ _) (abs_nonneg _) ((abs_nonneg _).trans (hl i j))
      _ = _ := by simp [mul_assoc]
  have hsmall (k : Fin n) : |v k|<b := by
    by_cases hk : i=k
    · simp only [v,hk,ite_true]
      exact (abs_sub _ _).trans_lt (by have := hv k; have := hp k; subst i; omega)
    · simp only [v,hk,ite_false,sub_zero]; exact (hv k).trans_lt hb
  have H := prefix_zero b hpos v (i.val+1) (hpack ▸ Int.dvd_of_emod_eq_zero (hc i)) hsmall j
    (by omega)
  exact sub_eq_zero.mp H

end NearHadamard.Optimal
