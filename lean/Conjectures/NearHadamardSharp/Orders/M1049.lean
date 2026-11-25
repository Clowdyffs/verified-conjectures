module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1049
local instance : Fact (Nat.Prime 1049) := ⟨by decide⟩
abbrev F0 := ZMod 1049
def w : F0 := 3
theorem hc : Fintype.card F0=1049 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1049-1) := by
  apply Small.primitiveCheck [2, 2, 2, 131] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1049%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨6,1⟩
def zi : Torus.Model w := ⟨477,445⟩
theorem hz : IsPrimitiveRoot z (1049*1049-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 5, 7, 131] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1049 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1049

namespace Q1061
local instance : Fact (Nat.Prime 1061) := ⟨by decide⟩
abbrev F0 := ZMod 1061
def w : F0 := 2
theorem hc : Fintype.card F0=1061 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1061-1) := by
  apply Small.primitiveCheck [2, 2, 5, 53] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1061%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,530⟩
theorem hz : IsPrimitiveRoot z (1061*1061-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 5, 53, 59] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1061 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1061

namespace Q1069
local instance : Fact (Nat.Prime 1069) := ⟨by decide⟩
abbrev F0 := ZMod 1069
def w : F0 := 6
theorem hc : Fintype.card F0=1069 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1069-1) := by
  apply Small.primitiveCheck [2, 2, 3, 89] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1069%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨6,1⟩
def zi : Torus.Model w := ⟨214,677⟩
theorem hz : IsPrimitiveRoot z (1069*1069-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 89, 107] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1069 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1069

namespace Q1093
local instance : Fact (Nat.Prime 1093) := ⟨by decide⟩
abbrev F0 := ZMod 1093
def w : F0 := 5
theorem hc : Fintype.card F0=1093 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1093-1) := by
  apply Small.primitiveCheck [2, 2, 3, 7, 13] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1093%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨820,929⟩
theorem hz : IsPrimitiveRoot z (1093*1093-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 7, 13, 547] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1093 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1093
end NearHadamard.Optimal
