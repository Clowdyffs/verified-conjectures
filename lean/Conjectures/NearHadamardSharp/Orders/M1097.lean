module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1097
local instance : Fact (Nat.Prime 1097) := ⟨by decide⟩
abbrev F0 := ZMod 1097
def w : F0 := 3
theorem hc : Fintype.card F0=1097 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1097-1) := by
  apply Small.primitiveCheck [2, 2, 2, 137] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1097%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨449,349⟩
theorem hz : IsPrimitiveRoot z (1097*1097-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 3, 61, 137] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1097 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1097

namespace Q1109
local instance : Fact (Nat.Prime 1109) := ⟨by decide⟩
abbrev F0 := ZMod 1109
def w : F0 := 2
theorem hc : Fintype.card F0=1109 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1109-1) := by
  apply Small.primitiveCheck [2, 2, 277] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1109%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨1061,675⟩
theorem hz : IsPrimitiveRoot z (1109*1109-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 37, 277] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1109 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1109

namespace Q1117
local instance : Fact (Nat.Prime 1117) := ⟨by decide⟩
abbrev F0 := ZMod 1117
def w : F0 := 2
theorem hc : Fintype.card F0=1117 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1117-1) := by
  apply Small.primitiveCheck [2, 2, 3, 3, 31] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1117%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,558⟩
theorem hz : IsPrimitiveRoot z (1117*1117-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 13, 31, 43] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1117 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1117

namespace Q1129
local instance : Fact (Nat.Prime 1129) := ⟨by decide⟩
abbrev F0 := ZMod 1129
def w : F0 := 11
theorem hc : Fintype.card F0=1129 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1129-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 47] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1129%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨7,1⟩
def zi : Torus.Model w := ⟨327,921⟩
theorem hz : IsPrimitiveRoot z (1129*1129-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 47, 113] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1129 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1129
end NearHadamard.Optimal
