module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q881
local instance : Fact (Nat.Prime 881) := ⟨by decide⟩
abbrev F0 := ZMod 881
def w : F0 := 3
theorem hc : Fintype.card F0=881 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (881-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 5, 11] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 881%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨7,1⟩
def zi : Torus.Model w := ⟨862,632⟩
theorem hz : IsPrimitiveRoot z (881*881-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 3, 5, 7, 7, 11] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 881 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q881

namespace Q929
local instance : Fact (Nat.Prime 929) := ⟨by decide⟩
abbrev F0 := ZMod 929
def w : F0 := 3
theorem hc : Fintype.card F0=929 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (929-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 29] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 929%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨465,774⟩
theorem hz : IsPrimitiveRoot z (929*929-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 3, 5, 29, 31] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 929 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q929

namespace Q937
local instance : Fact (Nat.Prime 937) := ⟨by decide⟩
abbrev F0 := ZMod 937
def w : F0 := 5
theorem hc : Fintype.card F0=937 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (937-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 13] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 937%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨767,511⟩
theorem hz : IsPrimitiveRoot z (937*937-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 3, 7, 13, 67] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 937 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q937

namespace Q941
local instance : Fact (Nat.Prime 941) := ⟨by decide⟩
abbrev F0 := ZMod 941
def w : F0 := 2
theorem hc : Fintype.card F0=941 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (941-1) := by
  apply Small.primitiveCheck [2, 2, 5, 47] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 941%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,470⟩
theorem hz : IsPrimitiveRoot z (941*941-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 47, 157] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 941 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q941
end NearHadamard.Optimal
