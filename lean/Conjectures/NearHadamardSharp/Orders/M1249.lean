module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1249
local instance : Fact (Nat.Prime 1249) := ⟨by decide⟩
abbrev F0 := ZMod 1249
def w : F0 := 7
theorem hc : Fintype.card F0=1249 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1249-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 13] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1249%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨6,1⟩
def zi : Torus.Model w := ⟨1120,646⟩
theorem hz : IsPrimitiveRoot z (1249*1249-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 3, 5, 5, 5, 5, 13] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1249 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1249

namespace Q1277
local instance : Fact (Nat.Prime 1277) := ⟨by decide⟩
abbrev F0 := ZMod 1277
def w : F0 := 2
theorem hc : Fintype.card F0=1277 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1277-1) := by
  apply Small.primitiveCheck [2, 2, 11, 29] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1277%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨1095,912⟩
theorem hz : IsPrimitiveRoot z (1277*1277-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 11, 29, 71] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1277 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1277

namespace Q1289
local instance : Fact (Nat.Prime 1289) := ⟨by decide⟩
abbrev F0 := ZMod 1289
def w : F0 := 6
theorem hc : Fintype.card F0=1289 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1289-1) := by
  apply Small.primitiveCheck [2, 2, 2, 7, 23] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1289%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨10,1⟩
def zi : Torus.Model w := ⟨960,1193⟩
theorem hz : IsPrimitiveRoot z (1289*1289-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 7, 23, 43] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1289 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1289

namespace Q1297
local instance : Fact (Nat.Prime 1297) := ⟨by decide⟩
abbrev F0 := ZMod 1297
def w : F0 := 10
theorem hc : Fintype.card F0=1297 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1297-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 3, 3, 3] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1297%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨865,1124⟩
theorem hz : IsPrimitiveRoot z (1297*1297-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 3, 3, 3, 11, 59] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1297 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1297
end NearHadamard.Optimal
