module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1637
local instance : Fact (Nat.Prime 1637) := ⟨by decide⟩
abbrev F0 := ZMod 1637
def w : F0 := 2
theorem hc : Fintype.card F0=1637 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1637-1) := by
  apply Small.primitiveCheck [2, 2, 409] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1637%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,818⟩
theorem hz : IsPrimitiveRoot z (1637*1637-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 7, 13, 409] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1637 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1637

namespace Q1657
local instance : Fact (Nat.Prime 1657) := ⟨by decide⟩
abbrev F0 := ZMod 1657
def w : F0 := 11
theorem hc : Fintype.card F0=1657 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1657-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 23] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1657%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨8,1⟩
def zi : Torus.Model w := ⟨219,594⟩
theorem hz : IsPrimitiveRoot z (1657*1657-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 3, 23, 829] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1657 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1657

namespace Q1669
local instance : Fact (Nat.Prime 1669) := ⟨by decide⟩
abbrev F0 := ZMod 1669
def w : F0 := 2
theorem hc : Fintype.card F0=1669 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1669-1) := by
  apply Small.primitiveCheck [2, 2, 3, 139] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1669%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,834⟩
theorem hz : IsPrimitiveRoot z (1669*1669-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 139, 167] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1669 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1669

namespace Q1681
local instance : Fact (Nat.Prime 41) := ⟨by decide⟩
abbrev F0 := ZMod 41
def d0 : F0 := 6
local instance : Fact (∀ x : F0, x^2≠d0+0*x) := ⟨by decide +kernel⟩
abbrev F1 := Torus.Model d0
def w : F1 := ⟨9,1⟩
theorem hc : Fintype.card F1=1681 := by simp [F0,F1,Small.card_model]
theorem hw : IsPrimitiveRoot w (1681-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 7] <;> decide +kernel
local instance : Fact (∀ x : F1, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1681%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨⟨6,0⟩,⟨1,0⟩⟩
def zi : Torus.Model w := ⟨⟨22,16⟩,⟨10,11⟩⟩
theorem hz : IsPrimitiveRoot z (1681*1681-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 5, 7, 29, 29] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1681 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1681
end NearHadamard.Optimal
