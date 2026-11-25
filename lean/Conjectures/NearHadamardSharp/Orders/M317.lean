module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q317
local instance : Fact (Nat.Prime 317) := ⟨by decide⟩
abbrev F0 := ZMod 317
def w : F0 := 2
theorem hc : Fintype.card F0=317 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (317-1) := by
  apply Small.primitiveCheck [2, 2, 79] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 317%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,158⟩
theorem hz : IsPrimitiveRoot z (317*317-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 53, 79] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 317 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q317

namespace Q337
local instance : Fact (Nat.Prime 337) := ⟨by decide⟩
abbrev F0 := ZMod 337
def w : F0 := 10
theorem hc : Fintype.card F0=337 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (337-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 7] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 337%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨225,292⟩
theorem hz : IsPrimitiveRoot z (337*337-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 7, 13, 13] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 337 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q337

namespace Q349
local instance : Fact (Nat.Prime 349) := ⟨by decide⟩
abbrev F0 := ZMod 349
def w : F0 := 2
theorem hc : Fintype.card F0=349 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (349-1) := by
  apply Small.primitiveCheck [2, 2, 3, 29] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 349%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,174⟩
theorem hz : IsPrimitiveRoot z (349*349-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 5, 7, 29] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 349 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q349

namespace Q353
local instance : Fact (Nat.Prime 353) := ⟨by decide⟩
abbrev F0 := ZMod 353
def w : F0 := 3
theorem hc : Fintype.card F0=353 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (353-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 11] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 353%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨299,190⟩
theorem hz : IsPrimitiveRoot z (353*353-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 3, 11, 59] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 353 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q353
end NearHadamard.Optimal
