module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q613
local instance : Fact (Nat.Prime 613) := ⟨by decide⟩
abbrev F0 := ZMod 613
def w : F0 := 2
theorem hc : Fintype.card F0=613 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (613-1) := by
  apply Small.primitiveCheck [2, 2, 3, 3, 17] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 613%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,306⟩
theorem hz : IsPrimitiveRoot z (613*613-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 17, 307] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 613 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q613

namespace Q617
local instance : Fact (Nat.Prime 617) := ⟨by decide⟩
abbrev F0 := ZMod 617
def w : F0 := 3
theorem hc : Fintype.card F0=617 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (617-1) := by
  apply Small.primitiveCheck [2, 2, 2, 7, 11] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 617%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨380,522⟩
theorem hz : IsPrimitiveRoot z (617*617-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 7, 11, 103] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 617 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q617

namespace Q625
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev F0 := ZMod 5
def d0 : F0 := 2
local instance : Fact (∀ x : F0, x^2≠d0+0*x) := ⟨by decide +kernel⟩
abbrev F1 := Torus.Model d0
def d1 : F1 := ⟨2,1⟩
local instance : Fact (∀ x : F1, x^2≠d1+0*x) := ⟨by decide +kernel⟩
abbrev F2 := Torus.Model d1
def w : F2 := ⟨⟨2,0⟩,⟨1,0⟩⟩
theorem hc : Fintype.card F2=625 := by simp [F0,F1,F2,Small.card_model]
theorem hw : IsPrimitiveRoot w (625-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 13] <;> decide +kernel
local instance : Fact (∀ x : F2, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 625%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨⟨⟨2,0⟩,⟨0,0⟩⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩
def zi : Torus.Model w := ⟨⟨⟨4,2⟩,⟨2,1⟩⟩,⟨⟨3,4⟩,⟨4,2⟩⟩⟩
theorem hz : IsPrimitiveRoot z (625*625-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 13, 313] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 625 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q625

namespace Q641
local instance : Fact (Nat.Prime 641) := ⟨by decide⟩
abbrev F0 := ZMod 641
def w : F0 := 3
theorem hc : Fintype.card F0=641 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (641-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 5] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 641%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨321,534⟩
theorem hz : IsPrimitiveRoot z (641*641-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 107] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 641 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q641
end NearHadamard.Optimal
