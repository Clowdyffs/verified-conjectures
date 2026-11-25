module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q193
local instance : Fact (Nat.Prime 193) := ⟨by decide⟩
abbrev F0 := ZMod 193
def w : F0 := 5
theorem hc : Fintype.card F0=193 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (193-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 3] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 193%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨7,1⟩
def zi : Torus.Model w := ⟨180,57⟩
theorem hz : IsPrimitiveRoot z (193*193-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 3, 97] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 193 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q193

namespace Q197
local instance : Fact (Nat.Prime 197) := ⟨by decide⟩
abbrev F0 := ZMod 197
def w : F0 := 2
theorem hc : Fintype.card F0=197 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (197-1) := by
  apply Small.primitiveCheck [2, 2, 7, 7] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 197%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨9,1⟩
def zi : Torus.Model w := ⟨45,192⟩
theorem hz : IsPrimitiveRoot z (197*197-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 7, 7, 11] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 197 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q197

namespace Q229
local instance : Fact (Nat.Prime 229) := ⟨by decide⟩
abbrev F0 := ZMod 229
def w : F0 := 6
theorem hc : Fintype.card F0=229 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (229-1) := by
  apply Small.primitiveCheck [2, 2, 3, 19] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 229%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨92,206⟩
theorem hz : IsPrimitiveRoot z (229*229-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 19, 23] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 229 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q229

namespace Q233
local instance : Fact (Nat.Prime 233) := ⟨by decide⟩
abbrev F0 := ZMod 233
def w : F0 := 3
theorem hc : Fintype.card F0=233 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (233-1) := by
  apply Small.primitiveCheck [2, 2, 2, 29] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 233%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨117,194⟩
theorem hz : IsPrimitiveRoot z (233*233-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 3, 13, 29] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 233 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q233
end NearHadamard.Optimal
