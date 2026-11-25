module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q757
local instance : Fact (Nat.Prime 757) := ⟨by decide⟩
abbrev F0 := ZMod 757
def w : F0 := 2
theorem hc : Fintype.card F0=757 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (757-1) := by
  apply Small.primitiveCheck [2, 2, 3, 3, 3, 7] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 757%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,378⟩
theorem hz : IsPrimitiveRoot z (757*757-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 3, 7, 379] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 757 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q757

namespace Q761
local instance : Fact (Nat.Prime 761) := ⟨by decide⟩
abbrev F0 := ZMod 761
def w : F0 := 6
theorem hc : Fintype.card F0=761 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (761-1) := by
  apply Small.primitiveCheck [2, 2, 2, 5, 19] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 761%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨6,1⟩
def zi : Torus.Model w := ⟨609,279⟩
theorem hz : IsPrimitiveRoot z (761*761-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 19, 127] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 761 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q761

namespace Q769
local instance : Fact (Nat.Prime 769) := ⟨by decide⟩
abbrev F0 := ZMod 769
def w : F0 := 11
theorem hc : Fintype.card F0=769 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (769-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 2, 3] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 769%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨8,1⟩
def zi : Torus.Model w := ⟨537,29⟩
theorem hz : IsPrimitiveRoot z (769*769-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 7, 11] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 769 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q769

namespace Q773
local instance : Fact (Nat.Prime 773) := ⟨by decide⟩
abbrev F0 := ZMod 773
def w : F0 := 2
theorem hc : Fintype.card F0=773 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (773-1) := by
  apply Small.primitiveCheck [2, 2, 193] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 773%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨706,168⟩
theorem hz : IsPrimitiveRoot z (773*773-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 43, 193] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 773 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q773
end NearHadamard.Optimal
