module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q401
local instance : Fact (Nat.Prime 401) := ⟨by decide⟩
abbrev F0 := ZMod 401
def w : F0 := 3
theorem hc : Fintype.card F0=401 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (401-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 5, 5] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 401%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨201,334⟩
theorem hz : IsPrimitiveRoot z (401*401-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 5, 5, 67] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 401 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q401

namespace Q409
local instance : Fact (Nat.Prime 409) := ⟨by decide⟩
abbrev F0 := ZMod 409
def w : F0 := 21
theorem hc : Fintype.card F0=409 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (409-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 17] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 409%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨7,1⟩
def zi : Torus.Model w := ⟨307,73⟩
theorem hz : IsPrimitiveRoot z (409*409-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 17, 41] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 409 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q409

namespace Q421
local instance : Fact (Nat.Prime 421) := ⟨by decide⟩
abbrev F0 := ZMod 421
def w : F0 := 2
theorem hc : Fintype.card F0=421 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (421-1) := by
  apply Small.primitiveCheck [2, 2, 3, 5, 7] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 421%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,210⟩
theorem hz : IsPrimitiveRoot z (421*421-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 7, 211] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 421 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q421

namespace Q433
local instance : Fact (Nat.Prime 433) := ⟨by decide⟩
abbrev F0 := ZMod 433
def w : F0 := 5
theorem hc : Fintype.card F0=433 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (433-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 3, 3] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 433%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨325,368⟩
theorem hz : IsPrimitiveRoot z (433*433-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 3, 3, 7, 31] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 433 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q433
end NearHadamard.Optimal
