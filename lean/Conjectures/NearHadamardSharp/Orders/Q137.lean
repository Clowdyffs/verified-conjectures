module
public import Conjectures.NearHadamardSharp.Exact
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Q137
local instance : Fact (Nat.Prime 137) := ⟨by decide⟩
abbrev F0 := ZMod 137
def w : F0 := 3
theorem hc : Fintype.card F0=137 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (137-1) := by
  apply Small.primitiveCheck [2, 2, 2, 17] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 137%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨69,114⟩
theorem hz : IsPrimitiveRoot z (137*137-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 17, 23] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 137 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q137
end NearHadamard.Optimal
