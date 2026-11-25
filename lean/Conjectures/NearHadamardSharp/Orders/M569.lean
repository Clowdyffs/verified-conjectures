module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q569
local instance : Fact (Nat.Prime 569) := ⟨by decide⟩
abbrev F0 := ZMod 569
def w : F0 := 3
theorem hc : Fintype.card F0=569 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (569-1) := by
  apply Small.primitiveCheck [2, 2, 2, 71] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 569%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨233,181⟩
theorem hz : IsPrimitiveRoot z (569*569-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 19, 71] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 569 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q569

namespace Q577
local instance : Fact (Nat.Prime 577) := ⟨by decide⟩
abbrev F0 := ZMod 577
def w : F0 := 5
theorem hc : Fintype.card F0=577 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (577-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 3, 3] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 577%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨10,1⟩
def zi : Torus.Model w := ⟨486,413⟩
theorem hz : IsPrimitiveRoot z (577*577-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 3, 3, 17, 17] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 577 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q577

namespace Q593
local instance : Fact (Nat.Prime 593) := ⟨by decide⟩
abbrev F0 := ZMod 593
def w : F0 := 3
theorem hc : Fintype.card F0=593 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (593-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 37] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 593%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨297,494⟩
theorem hz : IsPrimitiveRoot z (593*593-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 3, 3, 11, 37] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 593 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q593

namespace Q601
local instance : Fact (Nat.Prime 601) := ⟨by decide⟩
abbrev F0 := ZMod 601
def w : F0 := 7
theorem hc : Fintype.card F0=601 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (601-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 5] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 601%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨6,1⟩
def zi : Torus.Model w := ⟨166,373⟩
theorem hz : IsPrimitiveRoot z (601*601-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 5, 7, 43] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 601 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q601
end NearHadamard.Optimal
