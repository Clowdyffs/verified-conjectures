module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1873
local instance : Fact (Nat.Prime 1873) := ⟨by decide⟩
abbrev F0 := ZMod 1873
def w : F0 := 10
theorem hc : Fintype.card F0=1873 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1873-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 3, 13] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1873%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨1249,874⟩
theorem hz : IsPrimitiveRoot z (1873*1873-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 3, 13, 937] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1873 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1873

namespace Q1877
local instance : Fact (Nat.Prime 1877) := ⟨by decide⟩
abbrev F0 := ZMod 1877
def w : F0 := 2
theorem hc : Fintype.card F0=1877 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1877-1) := by
  apply Small.primitiveCheck [2, 2, 7, 67] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1877%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,938⟩
theorem hz : IsPrimitiveRoot z (1877*1877-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 7, 67, 313] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1877 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1877

namespace Q1889
local instance : Fact (Nat.Prime 1889) := ⟨by decide⟩
abbrev F0 := ZMod 1889
def w : F0 := 3
theorem hc : Fintype.card F0=1889 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1889-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 59] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1889%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨945,1574⟩
theorem hz : IsPrimitiveRoot z (1889*1889-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 7, 59] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1889 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1889

namespace Q1901
local instance : Fact (Nat.Prime 1901) := ⟨by decide⟩
abbrev F0 := ZMod 1901
def w : F0 := 2
theorem hc : Fintype.card F0=1901 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1901-1) := by
  apply Small.primitiveCheck [2, 2, 5, 5, 19] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1901%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨8,1⟩
def zi : Torus.Model w := ⟨736,1809⟩
theorem hz : IsPrimitiveRoot z (1901*1901-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 5, 19, 317] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1901 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1901
end NearHadamard.Optimal
