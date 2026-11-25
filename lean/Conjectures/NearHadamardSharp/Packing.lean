module
public import Conjectures.NearHadamard.Cyclic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

@[expose] public section
open Finset
namespace NearHadamard.Optimal

variable {n : ℕ} [NeZero n]

def conv (f g : Fin n → ℤ) (k : Fin n) : ℤ := ∑ j, f j * g (k-j)

def pack {R : Type*} [CommRing R] (b : R) (f : Fin n → ℤ) : R :=
  ∑ i, (f i : R) * b^i.val

theorem pack_conv {R : Type*} [CommRing R] (b : R) (hb : b^n = 1) (f g : Fin n → ℤ) :
    pack b (conv f g) = pack b f * pack b g := by
  have powadd (i k : Fin n) : b^(i+k).val = b^i.val * b^k.val := by
    rw [Fin.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div (i.val+k.val) n, pow_add, pow_mul, hb, one_pow, mul_one]
  simp only [pack,conv,Int.cast_sum,Int.cast_mul,Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  rw [← Equiv.sum_comp (Equiv.addLeft i) (fun k : Fin n =>
    ((f i : R)*(g (k-i):R))*b^k.val)]
  simp only [Equiv.coe_addLeft, add_sub_cancel_left, powadd]
  apply sum_congr rfl
  intro j _
  ring

theorem cube_zero (f : Fin n → ℤ) :
    NearHadamard.Small.cyclicCube f = n * conv (conv f f) f 0 := by
  simp [NearHadamard.Small.cyclicCube, NearHadamard.Small.shift_val, conv,
        show ∀ k : Fin n, (n-k.val)%n=(-k).val from fun k => by
          simpa [NearHadamard.Source.shift] using NearHadamard.Small.shift_val k (0:Fin n),
        Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Or.inl rfl

private theorem abs_conv (f g : Fin n → ℤ) {a b : ℤ} (hf : ∀ i, |f i| ≤ a)
    (hg : ∀ i, |g i| ≤ b) (k : Fin n) : |conv f g k| ≤ n*(a*b) := by
  calc
    _ ≤ ∑ j, |f j * g (k-j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, a*b := sum_le_sum fun j _ => by
      rw [abs_mul]; exact mul_le_mul (hf _) (hg _) (abs_nonneg _) ((abs_nonneg _).trans (hf j))
    _ = _ := by simp

private theorem weights (b : ℤ) : (∑ i : Fin n, b^i.val) * (b-1) = b^n-1 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => b^k), geom_sum_mul]

private theorem pack_mod_base (b : ℤ) (f : Fin n → ℤ) :
    pack b f % b = f 0 % b := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ m =>
    simp [pack, Fin.sum_univ_succ, pow_succ, ← mul_assoc, ← Finset.sum_mul, Int.add_emod]

/-- Recover the constant coefficient of a cyclic cube from its packed integer.
The shift makes every output digit positive and strictly below the base minus one. -/
theorem decodeCube (f : Fin n → ℤ) (hf : ∀ i, |f i| ≤ 1)
    (b : ℤ) (hb : 2*(n:ℤ)^2+3 ≤ b) :
    NearHadamard.Small.cyclicCube f =
      n * (((pack b f ^ 3 + ((n:ℤ)^2+1)*(∑ i : Fin n, b^i.val)) %
        (b^n-1)) % b - ((n:ℤ)^2+1)) := by
  let t := conv (conv f f) f
  let u : ℤ := (n:ℤ)^2+1
  let d (i : Fin n) := t i + u
  let G := ∑ i : Fin n, b^i.val
  have H (k) : |t k| ≤ (n:ℤ)^2 := by
    have H1 (i) : |conv f f i| ≤ (n:ℤ) := by simpa using abs_conv f f hf hf i
    simpa [t,pow_two] using abs_conv _ _ H1 hf k
  have hp : 1 < b := by nlinarith [sq_nonneg (n:ℤ)]
  have hd (i) : 0 ≤ d i ∧ d i < b-1 := by
    have h := abs_le.mp (H i)
    dsimp [d,u]; constructor <;> omega
  have dnonneg : 0 ≤ pack b d := sum_nonneg fun i _ => mul_nonneg (hd i).1 (pow_nonneg (by omega) _)
  have dlt : pack b d < b^n-1 := by
    rw [← weights b (n:=n), Finset.sum_mul]
    exact Finset.sum_lt_sum_of_nonempty (s:=univ) univ_nonempty fun i _ =>
      by simpa [mul_comm] using mul_lt_mul_of_pos_right (hd i).2 (pow_pos (by omega : 0 < b) i.val)
  have mpos : 0 < b^n-1 := lt_of_le_of_lt dnonneg dlt
  let M := (b^n-1).toNat
  have hM : (M:ℤ)=b^n-1 := Int.toNat_of_nonneg mpos.le
  have hcast : ((b : ZMod M)^n) = 1 := by
    have hm : (((M:ℤ):ZMod M)) = 0 := by simp
    rw [hM,Int.cast_sub,Int.cast_pow,Int.cast_one,sub_eq_zero] at hm
    exact hm
  have mapPack (v : Fin n → ℤ) : ((pack b v:ℤ):ZMod M)=pack (b:ZMod M) v := by simp [pack]
  have he : ((pack b t : ℤ):ZMod M) = ((pack b f^3:ℤ):ZMod M) := by
    simp only [t,mapPack,pack_conv _ hcast,Int.cast_pow]; ring
  have packd : pack b d = pack b t + u*G := by
    simp [pack,d,G,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  have hcong : ((pack b d:ℤ):ZMod M) = ((pack b f^3 + u*G:ℤ):ZMod M) := by
    rw [packd,Int.cast_add,Int.cast_add,he]
  have hm := (ZMod.intCast_eq_intCast_iff _ _ _).mp hcong
  change pack b d % (M:ℤ) = _ at hm
  rw [hM,Int.emod_eq_of_lt dnonneg dlt] at hm
  rw [cube_zero]
  change ↑n * t 0 = ↑n * (((pack b f^3+u*G) % (b^n-1)) % b - u)
  rw [←hm,pack_mod_base,Int.emod_eq_of_lt (hd 0).1 (by linarith [(hd 0).2])]
  simp [d]

/-- Evaluate the cyclic row at an integer base without constructing a matrix. -/
def orbitPack {F : Type*} [Monoid F] (b : ℤ) (step : F) (sign : F → ℤ) : ℕ → F → ℤ
  | 0, _ => 0
  | k+1, x => sign x + b * orbitPack b step sign k (x*step)

theorem orbitPack_eq {F : Type*} [Monoid F] (b : ℤ) (step : F) (sign : F → ℤ) (k : ℕ) (x : F) :
    orbitPack b step sign k x = ∑ i : Fin k, sign (x * step^i.val)*b^i.val := by
  induction k generalizing x with
  | zero => simp [orbitPack]
  | succ k ih =>
    rw [orbitPack,ih,Fin.sum_univ_succ,Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ' step, ←mul_assoc]
    congr 1
    apply sum_congr rfl
    intro i _
    rw [pow_succ]; ring

def radix (n : ℕ) : ℤ := 2*(n:ℤ)^2+3

def unpackCube (n : ℕ) (h : ℤ) : ℤ :=
  let b := radix n
  let u := (n:ℤ)^2+1
  let m := b^n-1
  n * (((h^3+u*(m/(b-1))) % m) % b-u)

theorem unpackCube_eq (f : Fin n → ℤ) (hf : ∀ i, |f i| ≤ 1) :
    unpackCube n (pack (radix n) f) = NearHadamard.Small.cyclicCube f := by
  rw [decodeCube f hf (radix n) (le_refl _)]
  have h : radix n - 1 ≠ 0 := by unfold radix; nlinarith [sq_nonneg (n:ℤ)]
  simp [unpackCube, ← weights (radix n) (n:=n), h]
end NearHadamard.Optimal
