module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q953
local instance : Fact (Nat.Prime 953) := ⟨by decide⟩
abbrev F0 := ZMod 953
def w : F0 := 3
theorem hc : Fintype.card F0=953 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (953-1) := by
  apply Small.primitiveCheck [2, 2, 2, 7, 17] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 953%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨477,794⟩
theorem hz : IsPrimitiveRoot z (953*953-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 3, 7, 17, 53] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 953 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q953

namespace Q961
local instance : Fact (Nat.Prime 31) := ⟨by decide⟩
abbrev F0 := ZMod 31
def d0 : F0 := 3
local instance : Fact (∀ x : F0, x^2≠d0+0*x) := ⟨by decide +kernel⟩
abbrev F1 := Torus.Model d0
def w : F1 := ⟨4,1⟩
theorem hc : Fintype.card F1=961 := by simp [F0,F1,Small.card_model]
theorem hw : IsPrimitiveRoot w (961-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 3, 5] <;> decide +kernel
local instance : Fact (∀ x : F1, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 961%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨⟨3,0⟩,⟨1,0⟩⟩
def zi : Torus.Model w := ⟨⟨19,10⟩,⟨4,7⟩⟩
theorem hz : IsPrimitiveRoot z (961*961-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 3, 5, 13, 37] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 961 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q961

namespace Q977
local instance : Fact (Nat.Prime 977) := ⟨by decide⟩
abbrev F0 := ZMod 977
def w : F0 := 3
theorem hc : Fintype.card F0=977 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (977-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 61] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 977%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨827,526⟩
theorem hz : IsPrimitiveRoot z (977*977-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 61, 163] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 977 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q977

namespace Q997
local instance : Fact (Nat.Prime 997) := ⟨by decide⟩
abbrev F0 := ZMod 997
def w : F0 := 7
theorem hc : Fintype.card F0=997 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (997-1) := by
  apply Small.primitiveCheck [2, 2, 3, 83] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 997%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨6,1⟩
def zi : Torus.Model w := ⟨344,275⟩
theorem hz : IsPrimitiveRoot z (997*997-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 83, 499] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 997 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q997
end NearHadamard.Optimal
