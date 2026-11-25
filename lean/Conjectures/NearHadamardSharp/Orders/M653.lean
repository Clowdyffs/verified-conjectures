module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q653
local instance : Fact (Nat.Prime 653) := ⟨by decide⟩
abbrev F0 := ZMod 653
def w : F0 := 2
theorem hc : Fintype.card F0=653 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (653-1) := by
  apply Small.primitiveCheck [2, 2, 163] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 653%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,326⟩
theorem hz : IsPrimitiveRoot z (653*653-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 109, 163] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 653 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q653

namespace Q661
local instance : Fact (Nat.Prime 661) := ⟨by decide⟩
abbrev F0 := ZMod 661
def w : F0 := 2
theorem hc : Fintype.card F0=661 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (661-1) := by
  apply Small.primitiveCheck [2, 2, 3, 5, 11] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 661%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,330⟩
theorem hz : IsPrimitiveRoot z (661*661-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 11, 331] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 661 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q661

namespace Q673
local instance : Fact (Nat.Prime 673) := ⟨by decide⟩
abbrev F0 := ZMod 673
def w : F0 := 5
theorem hc : Fintype.card F0=673 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (673-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 7] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 673%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨551,367⟩
theorem hz : IsPrimitiveRoot z (673*673-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 3, 7, 337] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 673 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q673

namespace Q677
local instance : Fact (Nat.Prime 677) := ⟨by decide⟩
abbrev F0 := ZMod 677
def w : F0 := 2
theorem hc : Fintype.card F0=677 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (677-1) := by
  apply Small.primitiveCheck [2, 2, 13, 13] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 677%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨484,290⟩
theorem hz : IsPrimitiveRoot z (677*677-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 13, 13, 113] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 677 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q677
end NearHadamard.Optimal
