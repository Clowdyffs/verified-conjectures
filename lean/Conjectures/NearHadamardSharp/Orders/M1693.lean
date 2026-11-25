module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1693
local instance : Fact (Nat.Prime 1693) := ⟨by decide⟩
abbrev F0 := ZMod 1693
def w : F0 := 2
theorem hc : Fintype.card F0=1693 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1693-1) := by
  apply Small.primitiveCheck [2, 2, 3, 3, 47] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1693%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,846⟩
theorem hz : IsPrimitiveRoot z (1693*1693-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 7, 11, 11, 47] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1693 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1693

namespace Q1697
local instance : Fact (Nat.Prime 1697) := ⟨by decide⟩
abbrev F0 := ZMod 1697
def w : F0 := 3
theorem hc : Fintype.card F0=1697 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1697-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 53] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1697%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨653,261⟩
theorem hz : IsPrimitiveRoot z (1697*1697-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 3, 53, 283] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1697 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1697

namespace Q1709
local instance : Fact (Nat.Prime 1709) := ⟨by decide⟩
abbrev F0 := ZMod 1709
def w : F0 := 3
theorem hc : Fintype.card F0=1709 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1709-1) := by
  apply Small.primitiveCheck [2, 2, 7, 61] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1709%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨544,233⟩
theorem hz : IsPrimitiveRoot z (1709*1709-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 5, 7, 19, 61] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1709 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1709

namespace Q1721
local instance : Fact (Nat.Prime 1721) := ⟨by decide⟩
abbrev F0 := ZMod 1721
def w : F0 := 3
theorem hc : Fintype.card F0=1721 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1721-1) := by
  apply Small.primitiveCheck [2, 2, 2, 5, 43] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1721%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨6,1⟩
def zi : Torus.Model w := ⟨626,1043⟩
theorem hz : IsPrimitiveRoot z (1721*1721-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 7, 41, 43] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1721 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1721
end NearHadamard.Optimal
