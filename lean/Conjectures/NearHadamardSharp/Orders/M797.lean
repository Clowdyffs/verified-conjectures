module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q797
local instance : Fact (Nat.Prime 797) := ⟨by decide⟩
abbrev F0 := ZMod 797
def w : F0 := 2
theorem hc : Fintype.card F0=797 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (797-1) := by
  apply Small.primitiveCheck [2, 2, 199] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 797%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,398⟩
theorem hz : IsPrimitiveRoot z (797*797-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 7, 19, 199] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 797 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q797

namespace Q809
local instance : Fact (Nat.Prime 809) := ⟨by decide⟩
abbrev F0 := ZMod 809
def w : F0 := 3
theorem hc : Fintype.card F0=809 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (809-1) := by
  apply Small.primitiveCheck [2, 2, 2, 101] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 809%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨405,674⟩
theorem hz : IsPrimitiveRoot z (809*809-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 3, 3, 3, 5, 101] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 809 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q809

namespace Q821
local instance : Fact (Nat.Prime 821) := ⟨by decide⟩
abbrev F0 := ZMod 821
def w : F0 := 2
theorem hc : Fintype.card F0=821 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (821-1) := by
  apply Small.primitiveCheck [2, 2, 5, 41] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 821%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨704,645⟩
theorem hz : IsPrimitiveRoot z (821*821-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 41, 137] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 821 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q821

namespace Q829
local instance : Fact (Nat.Prime 829) := ⟨by decide⟩
abbrev F0 := ZMod 829
def w : F0 := 2
theorem hc : Fintype.card F0=829 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (829-1) := by
  apply Small.primitiveCheck [2, 2, 3, 3, 23] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 829%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,414⟩
theorem hz : IsPrimitiveRoot z (829*829-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 5, 23, 83] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 829 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q829
end NearHadamard.Optimal
