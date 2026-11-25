module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q241
local instance : Fact (Nat.Prime 241) := ⟨by decide⟩
abbrev F0 := ZMod 241
def w : F0 := 7
theorem hc : Fintype.card F0=241 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (241-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 241%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨7,1⟩
def zi : Torus.Model w := ⟨201,109⟩
theorem hz : IsPrimitiveRoot z (241*241-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 5, 11, 11] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 241 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q241

namespace Q257
local instance : Fact (Nat.Prime 257) := ⟨by decide⟩
abbrev F0 := ZMod 257
def w : F0 := 3
theorem hc : Fintype.card F0=257 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (257-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 2] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 257%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨129,214⟩
theorem hz : IsPrimitiveRoot z (257*257-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 43] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 257 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q257

namespace Q269
local instance : Fact (Nat.Prime 269) := ⟨by decide⟩
abbrev F0 := ZMod 269
def w : F0 := 2
theorem hc : Fintype.card F0=269 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (269-1) := by
  apply Small.primitiveCheck [2, 2, 67] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 269%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨10,1⟩
def zi : Torus.Model w := ⟨55,129⟩
theorem hz : IsPrimitiveRoot z (269*269-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 3, 5, 67] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 269 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q269

namespace Q277
local instance : Fact (Nat.Prime 277) := ⟨by decide⟩
abbrev F0 := ZMod 277
def w : F0 := 5
theorem hc : Fintype.card F0=277 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (277-1) := by
  apply Small.primitiveCheck [2, 2, 3, 23] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 277%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨227,151⟩
theorem hz : IsPrimitiveRoot z (277*277-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 23, 139] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 277 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q277
end NearHadamard.Optimal
