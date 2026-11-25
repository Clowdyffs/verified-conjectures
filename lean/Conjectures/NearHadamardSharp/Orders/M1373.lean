module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1373
local instance : Fact (Nat.Prime 1373) := ⟨by decide⟩
abbrev F0 := ZMod 1373
def w : F0 := 2
theorem hc : Fintype.card F0=1373 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1373-1) := by
  apply Small.primitiveCheck [2, 2, 7, 7, 7] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1373%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨12,1⟩
def zi : Torus.Model w := ⟨1025,29⟩
theorem hz : IsPrimitiveRoot z (1373*1373-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 7, 7, 7, 229] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1373 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1373

namespace Q1381
local instance : Fact (Nat.Prime 1381) := ⟨by decide⟩
abbrev F0 := ZMod 1381
def w : F0 := 2
theorem hc : Fintype.card F0=1381 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1381-1) := by
  apply Small.primitiveCheck [2, 2, 3, 5, 23] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1381%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,690⟩
theorem hz : IsPrimitiveRoot z (1381*1381-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 23, 691] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1381 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1381

namespace Q1409
local instance : Fact (Nat.Prime 1409) := ⟨by decide⟩
abbrev F0 := ZMod 1409
def w : F0 := 3
theorem hc : Fintype.card F0=1409 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1409-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 11] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1409%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨705,1174⟩
theorem hz : IsPrimitiveRoot z (1409*1409-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 11, 47] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1409 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1409

namespace Q1429
local instance : Fact (Nat.Prime 1429) := ⟨by decide⟩
abbrev F0 := ZMod 1429
def w : F0 := 6
theorem hc : Fintype.card F0=1429 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1429-1) := by
  apply Small.primitiveCheck [2, 2, 3, 7, 17] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1429%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨572,1286⟩
theorem hz : IsPrimitiveRoot z (1429*1429-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 7, 11, 13, 17] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1429 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1429
end NearHadamard.Optimal
