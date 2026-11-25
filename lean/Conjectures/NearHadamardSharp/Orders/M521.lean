module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q521
local instance : Fact (Nat.Prime 521) := ⟨by decide⟩
abbrev F0 := ZMod 521
def w : F0 := 3
theorem hc : Fintype.card F0=521 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (521-1) := by
  apply Small.primitiveCheck [2, 2, 2, 5, 13] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 521%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨9,1⟩
def zi : Torus.Model w := ⟨461,354⟩
theorem hz : IsPrimitiveRoot z (521*521-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 3, 5, 13, 29] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 521 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q521

namespace Q529
local instance : Fact (Nat.Prime 23) := ⟨by decide⟩
abbrev F0 := ZMod 23
def d0 : F0 := 5
local instance : Fact (∀ x : F0, x^2≠d0+0*x) := ⟨by decide +kernel⟩
abbrev F1 := Torus.Model d0
def w : F1 := ⟨1,1⟩
theorem hc : Fintype.card F1=529 := by simp [F0,F1,Small.card_model]
theorem hw : IsPrimitiveRoot w (529-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 11] <;> decide +kernel
local instance : Fact (∀ x : F1, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 529%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨⟨5,0⟩,⟨1,0⟩⟩
def zi : Torus.Model w := ⟨⟨16,16⟩,⟨6,6⟩⟩
theorem hz : IsPrimitiveRoot z (529*529-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 5, 11, 53] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 529 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q529

namespace Q541
local instance : Fact (Nat.Prime 541) := ⟨by decide⟩
abbrev F0 := ZMod 541
def w : F0 := 2
theorem hc : Fintype.card F0=541 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (541-1) := by
  apply Small.primitiveCheck [2, 2, 3, 3, 3, 5] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 541%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,270⟩
theorem hz : IsPrimitiveRoot z (541*541-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 3, 5, 271] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 541 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q541

namespace Q557
local instance : Fact (Nat.Prime 557) := ⟨by decide⟩
abbrev F0 := ZMod 557
def w : F0 := 2
theorem hc : Fintype.card F0=557 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (557-1) := by
  apply Small.primitiveCheck [2, 2, 139] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 557%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,278⟩
theorem hz : IsPrimitiveRoot z (557*557-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 31, 139] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 557 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q557
end NearHadamard.Optimal
