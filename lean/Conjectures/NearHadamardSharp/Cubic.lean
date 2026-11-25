module
public import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal

/-- The polynomial basis 1,X,X² with X³=X+c. Used for F₁₂₅ and F₂₇. -/
structure Cubic (p c : ℕ) where
  a : ZMod p
  b : ZMod p
  d : ZMod p
deriving DecidableEq

namespace Cubic
variable {p c : ℕ}
def equiv (p c : ℕ) : Cubic p c ≃ ZMod p × ZMod p × ZMod p :=
  ⟨fun x => (x.a,x.b,x.d),fun x => ⟨x.1,x.2.1,x.2.2⟩,fun _ => rfl,fun _ => rfl⟩
instance [NeZero p] : Fintype (Cubic p c) := Fintype.ofEquiv _ (equiv p c).symm
instance : Zero (Cubic p c) := ⟨⟨0,0,0⟩⟩
instance : One (Cubic p c) := ⟨⟨1,0,0⟩⟩
instance : Add (Cubic p c) := ⟨fun x y => ⟨x.a+y.a,x.b+y.b,x.d+y.d⟩⟩
instance : Neg (Cubic p c) := ⟨fun x => ⟨-x.a,-x.b,-x.d⟩⟩
instance : Mul (Cubic p c) := ⟨fun x y =>
  let h := x.b*y.d+x.d*y.b
  let k := x.d*y.d
  ⟨x.a*y.a+c*h, x.a*y.b+x.b*y.a+h+c*k,x.a*y.d+x.b*y.b+x.d*y.a+k⟩⟩

theorem mul_a (x y : Cubic p c) : (x*y).a = x.a*y.a+c*(x.b*y.d+x.d*y.b) := rfl
theorem mul_b (x y : Cubic p c) : (x*y).b = x.a*y.b+x.b*y.a+(x.b*y.d+x.d*y.b)+c*(x.d*y.d) := rfl
theorem mul_d (x y : Cubic p c) : (x*y).d = x.a*y.d+x.b*y.b+x.d*y.a+x.d*y.d := rfl
theorem add_a (x y : Cubic p c) : (x+y).a = x.a+y.a := rfl
theorem add_b (x y : Cubic p c) : (x+y).b = x.b+y.b := rfl
theorem add_d (x y : Cubic p c) : (x+y).d = x.d+y.d := rfl
theorem same {x y : Cubic p c} (a : x.a=y.a) (b : x.b=y.b) (d : x.d=y.d) : x=y := by
  cases x; cases y; congr
def rawPower (x : Cubic p c) (n : ℕ) : Cubic p c :=
  if n=0 then 1 else
    let y := rawPower x (n/2)
    if n%2=0 then y*y else y*y*x
termination_by n
instance : Inv (Cubic p c) := ⟨fun x => rawPower x (p^3-2)⟩

def invertible (p c : ℕ) : Prop :=
  (∀ x : Cubic p c, x≠0 → x*x⁻¹=1) ∧ ((0:Cubic p c)⁻¹=0) ∧ (0:Cubic p c)≠1

instance [NeZero p] : Decidable (invertible p c) := by unfold invertible; infer_instance

instance [Fact (invertible p c)] : Field (Cubic p c) := by
  apply Field.ofMinimalAxioms
  · rintro ⟨a,b,d⟩ ⟨e,f,g⟩ ⟨h,i,j⟩; apply Cubic.mk.injEq .. |>.mpr
    exact ⟨add_assoc ..,add_assoc ..,add_assoc ..⟩
  · rintro ⟨a,b,d⟩; change Cubic.mk (0+a) (0+b) (0+d) = _; simp
  · rintro ⟨a,b,d⟩; change Cubic.mk (-a+a) (-b+b) (-d+d) = ⟨0,0,0⟩; simp
  · intro x y z; apply same <;> simp only [mul_a,mul_b,mul_d] <;> ring
  · intro x y; apply same <;> simp only [mul_a,mul_b,mul_d] <;> ring
  · intro x; apply same <;> simp only [mul_a,mul_b,mul_d] <;>
      norm_num [show (1:Cubic p c).a=1 by rfl,show (1:Cubic p c).b=0 by rfl,show (1:Cubic p c).d=0 by rfl]
  · exact (Fact.out : invertible p c).1
  · exact (Fact.out : invertible p c).2.1
  · intro x y z; apply same <;> simp only [mul_a,mul_b,mul_d,add_a,add_b,add_d] <;> ring
  · exact ⟨0,1,(Fact.out : invertible p c).2.2⟩

theorem card [NeZero p] : Fintype.card (Cubic p c) = p^3 := by
  let e : Cubic p c ≃ ZMod p × ZMod p × ZMod p :=
    ⟨fun x => (x.a,x.b,x.d),fun x => ⟨x.1,x.2.1,x.2.2⟩,fun _ => rfl,fun _ => rfl⟩
  rw [Fintype.card_congr e]; simp; ring
end Cubic
end NearHadamard.Optimal
