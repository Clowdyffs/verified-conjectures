module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q2053
local instance : Fact (Nat.Prime 2053) := ⟨by decide⟩
abbrev F0 := ZMod 2053
def w : F0 := 2
theorem hc : Fintype.card F0=2053 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (2053-1) := by
  apply Small.primitiveCheck [2, 2, 3, 3, 3, 19] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 2053%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,1026⟩
theorem hz : IsPrimitiveRoot z (2053*2053-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 3, 13, 19, 79] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 2053 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q2053

namespace Q2069
local instance : Fact (Nat.Prime 2069) := ⟨by decide⟩
abbrev F0 := ZMod 2069
def w : F0 := 2
theorem hc : Fintype.card F0=2069 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (2069-1) := by
  apply Small.primitiveCheck [2, 2, 11, 47] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 2069%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,1034⟩
theorem hz : IsPrimitiveRoot z (2069*2069-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 5, 11, 23, 47] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 2069 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q2069

namespace Q2081
local instance : Fact (Nat.Prime 2081) := ⟨by decide⟩
abbrev F0 := ZMod 2081
def w : F0 := 3
theorem hc : Fintype.card F0=2081 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (2081-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 5, 13] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 2081%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨1041,1734⟩
theorem hz : IsPrimitiveRoot z (2081*2081-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 3, 5, 13, 347] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 2081 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q2081

namespace Q2089
local instance : Fact (Nat.Prime 2089) := ⟨by decide⟩
abbrev F0 := ZMod 2089
def w : F0 := 7
theorem hc : Fintype.card F0=2089 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (2089-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 29] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 2089%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨8,1⟩
def zi : Torus.Model w := ⟨1686,1356⟩
theorem hz : IsPrimitiveRoot z (2089*2089-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 3, 5, 11, 19, 29] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 2089 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q2089
end NearHadamard.Optimal
