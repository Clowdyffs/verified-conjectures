module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q841
local instance : Fact (Nat.Prime 29) := ⟨by decide⟩
abbrev F0 := ZMod 29
def d0 : F0 := 2
local instance : Fact (∀ x : F0, x^2≠d0+0*x) := ⟨by decide +kernel⟩
abbrev F1 := Torus.Model d0
def w : F1 := ⟨4,1⟩
theorem hc : Fintype.card F1=841 := by simp [F0,F1,Small.card_model]
theorem hw : IsPrimitiveRoot w (841-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 7] <;> decide +kernel
local instance : Fact (∀ x : F1, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 841%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨⟨4,0⟩,⟨1,0⟩⟩
def zi : Torus.Model w := ⟨⟨13,18⟩,⟨4,10⟩⟩
theorem hz : IsPrimitiveRoot z (841*841-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 7, 421] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 841 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q841

namespace Q853
local instance : Fact (Nat.Prime 853) := ⟨by decide⟩
abbrev F0 := ZMod 853
def w : F0 := 2
theorem hc : Fintype.card F0=853 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (853-1) := by
  apply Small.primitiveCheck [2, 2, 3, 71] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 853%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨8,1⟩
def zi : Torus.Model w := ⟨633,454⟩
theorem hz : IsPrimitiveRoot z (853*853-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 7, 61, 71] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 853 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q853

namespace Q857
local instance : Fact (Nat.Prime 857) := ⟨by decide⟩
abbrev F0 := ZMod 857
def w : F0 := 3
theorem hc : Fintype.card F0=857 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (857-1) := by
  apply Small.primitiveCheck [2, 2, 2, 107] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 857%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨429,714⟩
theorem hz : IsPrimitiveRoot z (857*857-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 11, 13, 107] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 857 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q857

namespace Q877
local instance : Fact (Nat.Prime 877) := ⟨by decide⟩
abbrev F0 := ZMod 877
def w : F0 := 2
theorem hc : Fintype.card F0=877 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (877-1) := by
  apply Small.primitiveCheck [2, 2, 3, 73] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 877%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,438⟩
theorem hz : IsPrimitiveRoot z (877*877-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 73, 439] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 877 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q877
end NearHadamard.Optimal
