module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1493
local instance : Fact (Nat.Prime 1493) := ⟨by decide⟩
abbrev F0 := ZMod 1493
def w : F0 := 2
theorem hc : Fintype.card F0=1493 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1493-1) := by
  apply Small.primitiveCheck [2, 2, 373] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1493%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨1280,1173⟩
theorem hz : IsPrimitiveRoot z (1493*1493-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 83, 373] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1493 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1493

namespace Q1549
local instance : Fact (Nat.Prime 1549) := ⟨by decide⟩
abbrev F0 := ZMod 1549
def w : F0 := 2
theorem hc : Fintype.card F0=1549 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1549-1) := by
  apply Small.primitiveCheck [2, 2, 3, 3, 43] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1549%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨6,1⟩
def zi : Torus.Model w := ⟨638,410⟩
theorem hz : IsPrimitiveRoot z (1549*1549-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 5, 5, 31, 43] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1549 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1549

namespace Q1553
local instance : Fact (Nat.Prime 1553) := ⟨by decide⟩
abbrev F0 := ZMod 1553
def w : F0 := 3
theorem hc : Fintype.card F0=1553 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1553-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 97] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1553%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨956,1314⟩
theorem hz : IsPrimitiveRoot z (1553*1553-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 7, 37, 97] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1553 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1553

namespace Q1597
local instance : Fact (Nat.Prime 1597) := ⟨by decide⟩
abbrev F0 := ZMod 1597
def w : F0 := 11
theorem hc : Fintype.card F0=1597 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1597-1) := by
  apply Small.primitiveCheck [2, 2, 3, 7, 19] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1597%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨7,1⟩
def zi : Torus.Model w := ⟨1303,42⟩
theorem hz : IsPrimitiveRoot z (1597*1597-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 7, 17, 19, 47] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1597 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1597
end NearHadamard.Optimal
