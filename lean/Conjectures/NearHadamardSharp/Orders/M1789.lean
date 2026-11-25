module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1789
local instance : Fact (Nat.Prime 1789) := ⟨by decide⟩
abbrev F0 := ZMod 1789
def w : F0 := 6
theorem hc : Fintype.card F0=1789 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1789-1) := by
  apply Small.primitiveCheck [2, 2, 3, 149] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1789%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨716,1610⟩
theorem hz : IsPrimitiveRoot z (1789*1789-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 149, 179] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1789 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1789

namespace Q1801
local instance : Fact (Nat.Prime 1801) := ⟨by decide⟩
abbrev F0 := ZMod 1801
def w : F0 := 11
theorem hc : Fintype.card F0=1801 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1801-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 5, 5] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1801%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨7,1⟩
def zi : Torus.Model w := ⟨1659,1564⟩
theorem hz : IsPrimitiveRoot z (1801*1801-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 3, 5, 5, 17, 53] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1801 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1801

namespace Q1849
local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
abbrev F0 := ZMod 43
def d0 : F0 := 3
local instance : Fact (∀ x : F0, x^2≠d0+0*x) := ⟨by decide +kernel⟩
abbrev F1 := Torus.Model d0
def w : F1 := ⟨6,1⟩
theorem hc : Fintype.card F1=1849 := by simp [F0,F1,Small.card_model]
theorem hw : IsPrimitiveRoot w (1849-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 7, 11] <;> decide +kernel
local instance : Fact (∀ x : F1, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1849%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨⟨10,0⟩,⟨1,0⟩⟩
def zi : Torus.Model w := ⟨⟨14,34⟩,⟨33,31⟩⟩
theorem hz : IsPrimitiveRoot z (1849*1849-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 5, 7, 11, 37] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1849 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1849

namespace Q1861
local instance : Fact (Nat.Prime 1861) := ⟨by decide⟩
abbrev F0 := ZMod 1861
def w : F0 := 2
theorem hc : Fintype.card F0=1861 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1861-1) := by
  apply Small.primitiveCheck [2, 2, 3, 5, 31] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1861%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,930⟩
theorem hz : IsPrimitiveRoot z (1861*1861-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 7, 7, 19, 31] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1861 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1861
end NearHadamard.Optimal
