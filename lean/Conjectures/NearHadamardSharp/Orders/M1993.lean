module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1993
local instance : Fact (Nat.Prime 1993) := ⟨by decide⟩
abbrev F0 := ZMod 1993
def w : F0 := 5
theorem hc : Fintype.card F0=1993 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1993-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 83] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1993%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨1495,1694⟩
theorem hz : IsPrimitiveRoot z (1993*1993-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 83, 997] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1993 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1993

namespace Q1997
local instance : Fact (Nat.Prime 1997) := ⟨by decide⟩
abbrev F0 := ZMod 1997
def w : F0 := 2
theorem hc : Fintype.card F0=1997 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1997-1) := by
  apply Small.primitiveCheck [2, 2, 499] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1997%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,998⟩
theorem hz : IsPrimitiveRoot z (1997*1997-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 3, 3, 37, 499] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1997 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1997

namespace Q2017
local instance : Fact (Nat.Prime 2017) := ⟨by decide⟩
abbrev F0 := ZMod 2017
def w : F0 := 5
theorem hc : Fintype.card F0=2017 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (2017-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 3, 7] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 2017%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨5,1⟩
def zi : Torus.Model w := ⟨1513,1311⟩
theorem hz : IsPrimitiveRoot z (2017*2017-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 3, 3, 7, 1009] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 2017 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q2017

namespace Q2029
local instance : Fact (Nat.Prime 2029) := ⟨by decide⟩
abbrev F0 := ZMod 2029
def w : F0 := 2
theorem hc : Fintype.card F0=2029 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (2029-1) := by
  apply Small.primitiveCheck [2, 2, 3, 13, 13] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 2029%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,1014⟩
theorem hz : IsPrimitiveRoot z (2029*2029-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 7, 13, 13, 29] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 2029 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q2029
end NearHadamard.Optimal
