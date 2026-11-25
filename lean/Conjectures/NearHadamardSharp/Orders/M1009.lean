module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1009
local instance : Fact (Nat.Prime 1009) := ⟨by decide⟩
abbrev F0 := ZMod 1009
def w : F0 := 11
theorem hc : Fintype.card F0=1009 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1009-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 3, 7] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1009%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨7,1⟩
def zi : Torus.Model w := ⟨664,770⟩
theorem hz : IsPrimitiveRoot z (1009*1009-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 3, 5, 7, 101] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1009 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1009

namespace Q1013
local instance : Fact (Nat.Prime 1013) := ⟨by decide⟩
abbrev F0 := ZMod 1013
def w : F0 := 3
theorem hc : Fintype.card F0=1013 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1013-1) := by
  apply Small.primitiveCheck [2, 2, 11, 23] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1013%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨8,1⟩
def zi : Torus.Model w := ⟨681,548⟩
theorem hz : IsPrimitiveRoot z (1013*1013-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 11, 13, 13, 23] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1013 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1013

namespace Q1021
local instance : Fact (Nat.Prime 1021) := ⟨by decide⟩
abbrev F0 := ZMod 1021
def w : F0 := 10
theorem hc : Fintype.card F0=1021 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1021-1) := by
  apply Small.primitiveCheck [2, 2, 3, 5, 17] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1021%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨10,1⟩
def zi : Torus.Model w := ⟨227,692⟩
theorem hz : IsPrimitiveRoot z (1021*1021-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 7, 17, 73] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1021 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1021

namespace Q1033
local instance : Fact (Nat.Prime 1033) := ⟨by decide⟩
abbrev F0 := ZMod 1033
def w : F0 := 5
theorem hc : Fintype.card F0=1033 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1033-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 43] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1033%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨376,939⟩
theorem hz : IsPrimitiveRoot z (1033*1033-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 11, 43, 47] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1033 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1033
end NearHadamard.Optimal
