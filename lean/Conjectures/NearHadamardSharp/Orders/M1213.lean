module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1213
local instance : Fact (Nat.Prime 1213) := ⟨by decide⟩
abbrev F0 := ZMod 1213
def w : F0 := 2
theorem hc : Fintype.card F0=1213 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1213-1) := by
  apply Small.primitiveCheck [2, 2, 3, 101] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1213%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,606⟩
theorem hz : IsPrimitiveRoot z (1213*1213-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 101, 607] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1213 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1213

namespace Q1217
local instance : Fact (Nat.Prime 1217) := ⟨by decide⟩
abbrev F0 := ZMod 1217
def w : F0 := 3
theorem hc : Fintype.card F0=1217 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1217-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 19] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1217%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨609,1014⟩
theorem hz : IsPrimitiveRoot z (1217*1217-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 3, 7, 19, 29] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1217 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1217

namespace Q1229
local instance : Fact (Nat.Prime 1229) := ⟨by decide⟩
abbrev F0 := ZMod 1229
def w : F0 := 2
theorem hc : Fintype.card F0=1229 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1229-1) := by
  apply Small.primitiveCheck [2, 2, 307] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1229%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,614⟩
theorem hz : IsPrimitiveRoot z (1229*1229-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 41, 307] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1229 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1229

namespace Q1237
local instance : Fact (Nat.Prime 1237) := ⟨by decide⟩
abbrev F0 := ZMod 1237
def w : F0 := 2
theorem hc : Fintype.card F0=1237 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1237-1) := by
  apply Small.primitiveCheck [2, 2, 3, 103] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1237%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,618⟩
theorem hz : IsPrimitiveRoot z (1237*1237-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 103, 619] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1237 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1237
end NearHadamard.Optimal
