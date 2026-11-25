module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q281
local instance : Fact (Nat.Prime 281) := ⟨by decide⟩
abbrev F0 := ZMod 281
def w : F0 := 3
theorem hc : Fintype.card F0=281 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (281-1) := by
  apply Small.primitiveCheck [2, 2, 2, 5, 7] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 281%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨130,108⟩
theorem hz : IsPrimitiveRoot z (281*281-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 7, 47] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 281 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q281

namespace Q289
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩
abbrev F0 := ZMod 17
def d0 : F0 := 3
local instance : Fact (∀ x : F0, x^2≠d0+0*x) := ⟨by decide +kernel⟩
abbrev F1 := Torus.Model d0
def w : F1 := ⟨3,1⟩
theorem hc : Fintype.card F1=289 := by simp [F0,F1,Small.card_model]
theorem hw : IsPrimitiveRoot w (289-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 3] <;> decide +kernel
local instance : Fact (∀ x : F1, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 289%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨⟨8,0⟩,⟨1,0⟩⟩
def zi : Torus.Model w := ⟨⟨1,12⟩,⟨2,7⟩⟩
theorem hz : IsPrimitiveRoot z (289*289-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 3, 3, 5, 29] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 289 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q289

namespace Q293
local instance : Fact (Nat.Prime 293) := ⟨by decide⟩
abbrev F0 := ZMod 293
def w : F0 := 2
theorem hc : Fintype.card F0=293 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (293-1) := by
  apply Small.primitiveCheck [2, 2, 73] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 293%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨126,251⟩
theorem hz : IsPrimitiveRoot z (293*293-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 7, 7, 73] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 293 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q293

namespace Q313
local instance : Fact (Nat.Prime 313) := ⟨by decide⟩
abbrev F0 := ZMod 313
def w : F0 := 10
theorem hc : Fintype.card F0=313 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (313-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 13] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 313%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨209,146⟩
theorem hz : IsPrimitiveRoot z (313*313-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 13, 157] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 313 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q313
end NearHadamard.Optimal
