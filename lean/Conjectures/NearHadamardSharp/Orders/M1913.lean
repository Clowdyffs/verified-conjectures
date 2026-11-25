module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1913
local instance : Fact (Nat.Prime 1913) := ⟨by decide⟩
abbrev F0 := ZMod 1913
def w : F0 := 3
theorem hc : Fintype.card F0=1913 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1913-1) := by
  apply Small.primitiveCheck [2, 2, 2, 239] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1913%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨14,1⟩
def zi : Torus.Model w := ⟨1021,337⟩
theorem hz : IsPrimitiveRoot z (1913*1913-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 11, 29, 239] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1913 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1913

namespace Q1933
local instance : Fact (Nat.Prime 1933) := ⟨by decide⟩
abbrev F0 := ZMod 1933
def w : F0 := 5
theorem hc : Fintype.card F0=1933 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1933-1) := by
  apply Small.primitiveCheck [2, 2, 3, 7, 23] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1933%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨1450,1643⟩
theorem hz : IsPrimitiveRoot z (1933*1933-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 7, 23, 967] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1933 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1933

namespace Q1949
local instance : Fact (Nat.Prime 1949) := ⟨by decide⟩
abbrev F0 := ZMod 1949
def w : F0 := 2
theorem hc : Fintype.card F0=1949 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1949-1) := by
  apply Small.primitiveCheck [2, 2, 487] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1949%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨1671,1392⟩
theorem hz : IsPrimitiveRoot z (1949*1949-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 5, 13, 487] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1949 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1949

namespace Q1973
local instance : Fact (Nat.Prime 1973) := ⟨by decide⟩
abbrev F0 := ZMod 1973
def w : F0 := 2
theorem hc : Fintype.card F0=1973 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1973-1) := by
  apply Small.primitiveCheck [2, 2, 17, 29] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1973%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,986⟩
theorem hz : IsPrimitiveRoot z (1973*1973-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 7, 17, 29, 47] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1973 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1973
end NearHadamard.Optimal
