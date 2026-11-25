module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q157
local instance : Fact (Nat.Prime 157) := ⟨by decide⟩
abbrev F0 := ZMod 157
def w : F0 := 5
theorem hc : Fintype.card F0=157 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (157-1) := by
  apply Small.primitiveCheck [2, 2, 3, 13] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 157%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨118,102⟩
theorem hz : IsPrimitiveRoot z (157*157-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 13, 79] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 157 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q157

namespace Q169
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
abbrev F0 := ZMod 13
def d0 : F0 := 2
local instance : Fact (∀ x : F0, x^2≠d0+0*x) := ⟨by decide +kernel⟩
abbrev F1 := Torus.Model d0
def w : F1 := ⟨2,1⟩
theorem hc : Fintype.card F1=169 := by simp [F0,F1,Small.card_model]
theorem hw : IsPrimitiveRoot w (169-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 7] <;> decide +kernel
local instance : Fact (∀ x : F1, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 169%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨⟨5,0⟩,⟨1,0⟩⟩
def zi : Torus.Model w := ⟨⟨9,10⟩,⟨6,11⟩⟩
theorem hz : IsPrimitiveRoot z (169*169-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 7, 17] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 169 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q169

namespace Q173
local instance : Fact (Nat.Prime 173) := ⟨by decide⟩
abbrev F0 := ZMod 173
def w : F0 := 2
theorem hc : Fintype.card F0=173 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (173-1) := by
  apply Small.primitiveCheck [2, 2, 43] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 173%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,86⟩
theorem hz : IsPrimitiveRoot z (173*173-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 29, 43] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 173 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q173

namespace Q181
local instance : Fact (Nat.Prime 181) := ⟨by decide⟩
abbrev F0 := ZMod 181
def w : F0 := 2
theorem hc : Fintype.card F0=181 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (181-1) := by
  apply Small.primitiveCheck [2, 2, 3, 3, 5] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 181%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,90⟩
theorem hz : IsPrimitiveRoot z (181*181-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 5, 7, 13] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 181 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q181
end NearHadamard.Optimal
