module
public import Conjectures.NearHadamard.Statement
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

@[expose] public section
open Matrix Finset
namespace NearHadamard.Small

def triangles {ι : Type*} [Fintype ι] (T : Matrix ι ι ℤ) : ℤ :=
  ∑ i : ι, ∑ j : ι, ∑ k : ι, T i j*T j k*T k i

theorem triangles_eq {ι : Type*} [Fintype ι] (T : Matrix ι ι ℤ) : triangles T=(T*T*T).trace := by
  simp only [triangles,Matrix.trace,Matrix.diag,Matrix.mul_apply,Finset.sum_mul]
  apply sum_congr rfl; intro i _
  rw [sum_comm]

def cyclic {n : ℕ} (r : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℤ := fun i j => r (j-i)

def cyclicCube {n : ℕ} (r : Fin n → ℤ) : ℤ :=
  let row := Array.ofFn r
  (n:ℤ)*∑ j : Fin n, ∑ k : Fin n,
    row[j.val]! * row[Source.shift j k]! * row[(n-k.val)%n]!

theorem shift_val {n : ℕ} (i j : Fin n) : Source.shift i j=(j-i).val := by
  simp only [Source.shift,Fin.sub_def,Fin.val_mk]
  congr 1; omega

theorem cyclicCube_eq {n : ℕ} (hn : 0<n) (r : Fin n → ℤ) :
    cyclicCube r=triangles (cyclic r) := by
  letI : NeZero n := ⟨hn.ne'⟩
  have negval (k : Fin n) : (n-k.val)%n = (-k).val := by
    simpa [Source.shift] using (shift_val k (0:Fin n))
  have key (i : Fin n) :
      (∑ j, ∑ k, r (j-i)*r (k-j)*r (i-k)) = ∑ j, ∑ k, r j*r (k-j)*r (-k) := by
    let e := Equiv.addRight i
    rw [←Equiv.sum_comp e (fun j => ∑ k, r (j-i)*r (k-j)*r (i-k))]
    apply sum_congr rfl; intro j _
    rw [←Equiv.sum_comp e (fun k => r (e j-i)*r (k-e j)*r (i-k))]
    simp [e]
  simp only [triangles,cyclic,key,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  unfold cyclicCube
  simp [shift_val,negval]

def borderExtend {ι : Type*} (s : ℤ) (A : Matrix ι ι ℤ) : Matrix (Option ι) (Option ι) ℤ
  | none,none => 0
  | some i,some j => A i j
  | _,_ => s

theorem triangles_extend {ι : Type*} [Fintype ι] (s : ℤ) (A : Matrix ι ι ℤ) :
    triangles (borderExtend s A) = triangles A + 3*s^2*(∑ i, ∑ j, A i j) := by
  simp only [triangles,Fintype.sum_option,borderExtend,zero_mul,mul_zero,sum_const_zero,
    add_zero,zero_add,sum_add_distrib]
  have e1 (i j : ι) : s*A i j*s = s^2*A i j := by ring
  have e2 (i j : ι) : A i j*s*s = s^2*A i j := by ring
  have e3 (i j : ι) : s*s*A i j = s^2*A i j := by ring
  simp only [e1,e2,e3,←mul_sum]
  rw [sum_comm (f:=fun i j => A j i)]
  ring

theorem cyclic_sum {n : ℕ} (hn : 0<n) (r : Fin n → ℤ) :
    (∑ i, ∑ j, cyclic r i j) = (n:ℤ)*∑ j, r j := by
  letI : NeZero n := ⟨hn.ne'⟩
  have e (i : Fin n) : (∑ j,r (j-i))=∑ j,r j := by
    simpa [sub_eq_add_neg] using Equiv.sum_comp (Equiv.addRight (-i)) r
  simp only [cyclic,e,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]

end NearHadamard.Small
