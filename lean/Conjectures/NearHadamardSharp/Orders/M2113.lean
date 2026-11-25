module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q2113
local instance : Fact (Nat.Prime 2113) := ⟨by decide⟩
abbrev F0 := ZMod 2113
def w : F0 := 5
theorem hc : Fintype.card F0=2113 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (2113-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 3, 11] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 2113%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨1585,1796⟩
theorem hz : IsPrimitiveRoot z (2113*2113-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 3, 7, 11, 151] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 2113 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q2113

namespace Q2129
local instance : Fact (Nat.Prime 2129) := ⟨by decide⟩
abbrev F0 := ZMod 2129
def w : F0 := 3
theorem hc : Fintype.card F0=2129 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (2129-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 7, 19] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 2129%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨10,1⟩
def zi : Torus.Model w := ⟨44,1273⟩
theorem hz : IsPrimitiveRoot z (2129*2129-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 5, 7, 19, 71] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 2129 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q2129

namespace Q2137
local instance : Fact (Nat.Prime 2137) := ⟨by decide⟩
abbrev F0 := ZMod 2137
def w : F0 := 10
theorem hc : Fintype.card F0=2137 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (2137-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 89] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 2137%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨1425,1852⟩
theorem hz : IsPrimitiveRoot z (2137*2137-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 89, 1069] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 2137 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q2137

namespace Q2141
local instance : Fact (Nat.Prime 2141) := ⟨by decide⟩
abbrev F0 := ZMod 2141
def w : F0 := 2
theorem hc : Fintype.card F0=2141 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (2141-1) := by
  apply Small.primitiveCheck [2, 2, 5, 107] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 2141%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,1070⟩
theorem hz : IsPrimitiveRoot z (2141*2141-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 5, 7, 17, 107] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 2141 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q2141
end NearHadamard.Optimal
