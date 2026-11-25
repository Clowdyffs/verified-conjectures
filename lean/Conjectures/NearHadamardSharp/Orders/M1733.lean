module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1733
local instance : Fact (Nat.Prime 1733) := ⟨by decide⟩
abbrev F0 := ZMod 1733
def w : F0 := 2
theorem hc : Fintype.card F0=1733 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1733-1) := by
  apply Small.primitiveCheck [2, 2, 433] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1733%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨743,1114⟩
theorem hz : IsPrimitiveRoot z (1733*1733-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 17, 17, 433] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1733 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1733

namespace Q1741
local instance : Fact (Nat.Prime 1741) := ⟨by decide⟩
abbrev F0 := ZMod 1741
def w : F0 := 2
theorem hc : Fintype.card F0=1741 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1741-1) := by
  apply Small.primitiveCheck [2, 2, 3, 5, 29] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1741%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,870⟩
theorem hz : IsPrimitiveRoot z (1741*1741-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 13, 29, 67] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1741 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1741

namespace Q1753
local instance : Fact (Nat.Prime 1753) := ⟨by decide⟩
abbrev F0 := ZMod 1753
def w : F0 := 7
theorem hc : Fintype.card F0=1753 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1753-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 73] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1753%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨7,1⟩
def zi : Torus.Model w := ⟨1461,793⟩
theorem hz : IsPrimitiveRoot z (1753*1753-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 73, 877] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1753 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1753

namespace Q1777
local instance : Fact (Nat.Prime 1777) := ⟨by decide⟩
abbrev F0 := ZMod 1777
def w : F0 := 5
theorem hc : Fintype.card F0=1777 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1777-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 37] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1777%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨1333,1155⟩
theorem hz : IsPrimitiveRoot z (1777*1777-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 7, 37, 127] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1777 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1777
end NearHadamard.Optimal
