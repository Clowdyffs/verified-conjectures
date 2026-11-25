module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1301
local instance : Fact (Nat.Prime 1301) := ⟨by decide⟩
abbrev F0 := ZMod 1301
def w : F0 := 2
theorem hc : Fintype.card F0=1301 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1301-1) := by
  apply Small.primitiveCheck [2, 2, 5, 5, 13] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1301%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨558,1115⟩
theorem hz : IsPrimitiveRoot z (1301*1301-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 5, 7, 13, 31] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1301 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1301

namespace Q1321
local instance : Fact (Nat.Prime 1321) := ⟨by decide⟩
abbrev F0 := ZMod 1321
def w : F0 := 13
theorem hc : Fintype.card F0=1321 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1321-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 11] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1321%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨6,1⟩
def zi : Torus.Model w := ⟨230,402⟩
theorem hz : IsPrimitiveRoot z (1321*1321-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 11, 661] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1321 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1321

namespace Q1361
local instance : Fact (Nat.Prime 1361) := ⟨by decide⟩
abbrev F0 := ZMod 1361
def w : F0 := 3
theorem hc : Fintype.card F0=1361 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1361-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 5, 17] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1361%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨681,1134⟩
theorem hz : IsPrimitiveRoot z (1361*1361-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 5, 17, 227] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1361 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1361

namespace Q1369
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
abbrev F0 := ZMod 37
def d0 : F0 := 2
local instance : Fact (∀ x : F0, x^2≠d0+0*x) := ⟨by decide +kernel⟩
abbrev F1 := Torus.Model d0
def w : F1 := ⟨2,1⟩
theorem hc : Fintype.card F1=1369 := by simp [F0,F1,Small.card_model]
theorem hw : IsPrimitiveRoot w (1369-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 19] <;> decide +kernel
local instance : Fact (∀ x : F1, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1369%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨⟨2,0⟩,⟨1,0⟩⟩
def zi : Torus.Model w := ⟨⟨2,1⟩,⟨36,18⟩⟩
theorem hz : IsPrimitiveRoot z (1369*1369-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 3, 5, 19, 137] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1369 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1369
end NearHadamard.Optimal
