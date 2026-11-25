module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1601
local instance : Fact (Nat.Prime 1601) := ⟨by decide⟩
abbrev F0 := ZMod 1601
def w : F0 := 3
theorem hc : Fintype.card F0=1601 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1601-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 5, 5] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1601%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨801,1334⟩
theorem hz : IsPrimitiveRoot z (1601*1601-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 5, 89] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1601 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1601

namespace Q1609
local instance : Fact (Nat.Prime 1609) := ⟨by decide⟩
abbrev F0 := ZMod 1609
def w : F0 := 7
theorem hc : Fintype.card F0=1609 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1609-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 67] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1609%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨14,1⟩
def zi : Torus.Model w := ⟨596,647⟩
theorem hz : IsPrimitiveRoot z (1609*1609-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 7, 23, 67] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1609 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1609

namespace Q1613
local instance : Fact (Nat.Prime 1613) := ⟨by decide⟩
abbrev F0 := ZMod 1613
def w : F0 := 3
theorem hc : Fintype.card F0=1613 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1613-1) := by
  apply Small.primitiveCheck [2, 2, 13, 31] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1613%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨15,1⟩
def zi : Torus.Model w := ⟨545,1039⟩
theorem hz : IsPrimitiveRoot z (1613*1613-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 13, 31, 269] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1613 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1613

namespace Q1621
local instance : Fact (Nat.Prime 1621) := ⟨by decide⟩
abbrev F0 := ZMod 1621
def w : F0 := 2
theorem hc : Fintype.card F0=1621 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1621-1) := by
  apply Small.primitiveCheck [2, 2, 3, 3, 3, 3, 5] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1621%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,810⟩
theorem hz : IsPrimitiveRoot z (1621*1621-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 3, 3, 5, 811] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1621 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1621
end NearHadamard.Optimal
