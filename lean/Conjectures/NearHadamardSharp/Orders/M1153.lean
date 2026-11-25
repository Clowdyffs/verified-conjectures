module
public import Conjectures.NearHadamardSharp.Checks
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q1153
local instance : Fact (Nat.Prime 1153) := ⟨by decide⟩
abbrev F0 := ZMod 1153
def w : F0 := 5
theorem hc : Fintype.card F0=1153 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1153-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 3, 3] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1153%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨6,1⟩
def zi : Torus.Model w := ⟨1116,967⟩
theorem hz : IsPrimitiveRoot z (1153*1153-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 577] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1153 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1153

namespace Q1181
local instance : Fact (Nat.Prime 1181) := ⟨by decide⟩
abbrev F0 := ZMod 1181
def w : F0 := 7
theorem hc : Fintype.card F0=1181 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1181-1) := by
  apply Small.primitiveCheck [2, 2, 5, 59] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1181%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨9,1⟩
def zi : Torus.Model w := ⟨48,782⟩
theorem hz : IsPrimitiveRoot z (1181*1181-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 59, 197] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1181 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1181

namespace Q1193
local instance : Fact (Nat.Prime 1193) := ⟨by decide⟩
abbrev F0 := ZMod 1193
def w : F0 := 3
theorem hc : Fintype.card F0=1193 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1193-1) := by
  apply Small.primitiveCheck [2, 2, 2, 149] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1193%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨6,1⟩
def zi : Torus.Model w := ⟨434,723⟩
theorem hz : IsPrimitiveRoot z (1193*1193-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 149, 199] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1193 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1193

namespace Q1201
local instance : Fact (Nat.Prime 1201) := ⟨by decide⟩
abbrev F0 := ZMod 1201
def w : F0 := 11
theorem hc : Fintype.card F0=1201 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (1201-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 5, 5] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 1201%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨14,1⟩
def zi : Torus.Model w := ⟨461,396⟩
theorem hz : IsPrimitiveRoot z (1201*1201-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 5, 5, 601] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
theorem verified : AtOrder 1201 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; apply torusGood zi hc (by decide) hw (invz ▸ hz.inv) (by decide); decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) false; decide +kernel
end Q1201
end NearHadamard.Optimal
