module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q361
local instance : Fact (Nat.Prime 19) := ⟨by decide⟩
abbrev F0 := ZMod 19
def d0 : F0 := 2
local instance : Fact (∀ x : F0, x^2≠d0+0*x) := ⟨by decide +kernel⟩
abbrev F1 := Torus.Model d0
def w : F1 := ⟨2,1⟩
theorem hc : Fintype.card F1=361 := by simp [F0,F1,Small.card_model]
theorem hw : IsPrimitiveRoot w (361-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 5] <;> decide +kernel
local instance : Fact (∀ x : F1, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 361%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨⟨2,0⟩,⟨1,0⟩⟩
def zi : Torus.Model w := ⟨⟨2,1⟩,⟨18,9⟩⟩
theorem hz : IsPrimitiveRoot z (361*361-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 3, 5, 181] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 361 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q361

namespace Q373
local instance : Fact (Nat.Prime 373) := ⟨by decide⟩
abbrev F0 := ZMod 373
def w : F0 := 2
theorem hc : Fintype.card F0=373 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (373-1) := by
  apply Small.primitiveCheck [2, 2, 3, 31] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 373%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,186⟩
theorem hz : IsPrimitiveRoot z (373*373-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 11, 17, 31] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 373 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q373

namespace Q389
local instance : Fact (Nat.Prime 389) := ⟨by decide⟩
abbrev F0 := ZMod 389
def w : F0 := 2
theorem hc : Fintype.card F0=389 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (389-1) := by
  apply Small.primitiveCheck [2, 2, 97] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 389%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨6,1⟩
def zi : Torus.Model w := ⟨229,286⟩
theorem hz : IsPrimitiveRoot z (389*389-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 13, 97] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 389 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q389

namespace Q397
local instance : Fact (Nat.Prime 397) := ⟨by decide⟩
abbrev F0 := ZMod 397
def w : F0 := 5
theorem hc : Fintype.card F0=397 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (397-1) := by
  apply Small.primitiveCheck [2, 2, 3, 3, 11] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 397%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨298,258⟩
theorem hz : IsPrimitiveRoot z (397*397-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 11, 199] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 397 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q397
end NearHadamard.Optimal
