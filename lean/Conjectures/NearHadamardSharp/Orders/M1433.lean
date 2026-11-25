module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1433
local instance : Fact (Nat.Prime 1433) := ⟨by decide⟩
abbrev F0 := ZMod 1433
def w : F0 := 3
theorem hc : Fintype.card F0=1433 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1433-1) := by
  apply Small.primitiveCheck [2, 2, 2, 179] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1433%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨6,1⟩
def zi : Torus.Model w := ⟨391,1129⟩
theorem hz : IsPrimitiveRoot z (1433*1433-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 179, 239] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1433 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1433

namespace Q1453
local instance : Fact (Nat.Prime 1453) := ⟨by decide⟩
abbrev F0 := ZMod 1453
def w : F0 := 2
theorem hc : Fintype.card F0=1453 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1453-1) := by
  apply Small.primitiveCheck [2, 2, 3, 11, 11] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1453%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,726⟩
theorem hz : IsPrimitiveRoot z (1453*1453-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 11, 11, 727] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1453 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1453

namespace Q1481
local instance : Fact (Nat.Prime 1481) := ⟨by decide⟩
abbrev F0 := ZMod 1481
def w : F0 := 3
theorem hc : Fintype.card F0=1481 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1481-1) := by
  apply Small.primitiveCheck [2, 2, 2, 5, 37] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1481%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨741,1234⟩
theorem hz : IsPrimitiveRoot z (1481*1481-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 13, 19, 37] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1481 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1481

namespace Q1489
local instance : Fact (Nat.Prime 1489) := ⟨by decide⟩
abbrev F0 := ZMod 1489
def w : F0 := 14
theorem hc : Fintype.card F0=1489 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1489-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 31] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1489%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨11,1⟩
def zi : Torus.Model w := ⟨348,1322⟩
theorem hz : IsPrimitiveRoot z (1489*1489-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 5, 31, 149] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1489 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1489
end NearHadamard.Optimal
