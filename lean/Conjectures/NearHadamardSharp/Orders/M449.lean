module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q449
local instance : Fact (Nat.Prime 449) := ⟨by decide⟩
abbrev F0 := ZMod 449
def w : F0 := 3
theorem hc : Fintype.card F0=449 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (449-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 7] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 449%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨6,1⟩
def zi : Torus.Model w := ⟨41,68⟩
theorem hz : IsPrimitiveRoot z (449*449-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 5, 7] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 449 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q449

namespace Q457
local instance : Fact (Nat.Prime 457) := ⟨by decide⟩
abbrev F0 := ZMod 457
def w : F0 := 13
theorem hc : Fintype.card F0=457 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (457-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 19] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 457%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨6,1⟩
def zi : Torus.Model w := ⟨40,298⟩
theorem hz : IsPrimitiveRoot z (457*457-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 19, 229] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 457 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q457

namespace Q461
local instance : Fact (Nat.Prime 461) := ⟨by decide⟩
abbrev F0 := ZMod 461
def w : F0 := 2
theorem hc : Fintype.card F0=461 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (461-1) := by
  apply Small.primitiveCheck [2, 2, 5, 23] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 461%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,230⟩
theorem hz : IsPrimitiveRoot z (461*461-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 7, 11, 23] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 461 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q461

namespace Q509
local instance : Fact (Nat.Prime 509) := ⟨by decide⟩
abbrev F0 := ZMod 509
def w : F0 := 2
theorem hc : Fintype.card F0=509 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (509-1) := by
  apply Small.primitiveCheck [2, 2, 127] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 509%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,254⟩
theorem hz : IsPrimitiveRoot z (509*509-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 17, 127] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 509 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q509
end NearHadamard.Optimal
