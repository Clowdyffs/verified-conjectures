module
public import Conjectures.NearHadamardSharp.Exact
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Q9
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
abbrev F0 := ZMod 3
def d0 : F0 := 2
local instance : Fact (∀ x : F0, x^2≠d0+0*x) := ⟨by decide +kernel⟩
abbrev F1 := Torus.Model d0
def w : F1 := ⟨1,1⟩
theorem hc : Fintype.card F1=9 := by simp [F0,F1,Small.card_model]
theorem hw : IsPrimitiveRoot w (9-1) := by
  apply Small.primitiveCheck [2, 2, 2] <;> decide +kernel
local instance : Fact (∀ x : F1, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 9%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨⟨0,1⟩,⟨1,0⟩⟩
def zi : Torus.Model w := ⟨⟨1,2⟩,⟨1,1⟩⟩
theorem hz : IsPrimitiveRoot z (9*9-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 5] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
private def torusRow : Array ℤ := #[0,-1,1,1,-1]
private def torusL : Array (Array ℤ) := #[#[1],#[1,5],#[-1,1,6],#[-4,-3,3,14],#[2,-3,-3,2,12]]
private def torusD : Array ℤ := #[10,48,56,120,100]
theorem torus_det : |(Source.class4 9 z).det| = 64000 := by
  apply torusExactRow z hc (by decide) hw hz torusRow _ (by decide) (by decide +kernel)
  apply arrayCert (coreMatrix (n:=5) 9 torusRow) torusL torusD <;> decide +kernel
private def inverseRow : Array ℤ := #[0,1,-1,-1,1]
private def inverseL : Array (Array ℤ) := #[#[1],#[-1,5],#[1,-1,4],#[1,2,-2,9],#[-3,2,2,-3,12]]
private def inverseD : Array ℤ := #[10,48,36,80,100]
theorem inverse_det : |(Source.class4 9 zi).det| = 64000 := by
  apply torusExactRow zi hc (by decide) hw (invz ▸ hz.inv) inverseRow _ (by decide) (by decide +kernel)
  apply arrayCert (coreMatrix (n:=5) 9 inverseRow) inverseL inverseD <;> decide +kernel
private def fiveRow : Array ℤ := #[0,-1,1,-1]
private def fiveL : Array (Array ℤ) := #[#[1],#[-1,5],#[-1,1,4],#[-2,-1,2,9],#[-4,3,-1,3,15]]
private def fiveD : Array ℤ := #[10,48,36,80,128]
theorem five_det : |(Source.bordered 9 w true).det| = 65536 := by
  apply borderExactRow hc (by decide) hw true fiveRow _ (by decide) (by decide +kernel)
  apply arrayCert (borderedMatrix (m:=4) 9 true fiveRow) fiveL fiveD <;> decide +kernel
private def sixRow : Array ℤ := #[0,1,-1,1]
private def sixL : Array (Array ℤ) := #[#[1],#[1,5],#[1,-1,6],#[3,4,-3,14],#[3,-6,7,-6,20]]
private def sixD : Array ℤ := #[10,48,56,120,156]
theorem six_det : |(Source.bordered 9 w false).det| = 59904 := by
  apply borderExactRow hc (by decide) hw false sixRow _ (by decide) (by decide +kernel)
  apply arrayCert (borderedMatrix (m:=4) 9 false sixRow) sixL sixD <;> decide +kernel
theorem verified : AtOrder 9 := by
  apply modelOrder w z hc (by decide) hw hz
  · rw [torus_det]; decide +kernel
  · rw [invz]; rw [inverse_det]; decide +kernel
  · rw [five_det]; decide +kernel
  · rw [six_det]; decide +kernel
theorem attained : fullMinimum .six ∈ values 0 .six := by
  apply modelValue w z hc (by decide) (by decide) hw hz
  simp only [magnitude]
  rw [six_det]; decide +kernel

theorem fiveAbove (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (u : F) (h : Fintype.card F = 9) (hu : IsPrimitiveRoot u (9-1)) :
    (441/544 : ℚ) ≤ (|(Source.bordered 9 u true).det|:ℤ)/(delta 9:ℚ) := by
  let e := FiniteField.ringEquivOfCardEq (h.trans hc.symm)
  rw [←Border.transport e 9 u true]
  have H := Border.primitive_independent (w:=e u) (z:=w) (hc.symm ▸ (by decide : 9%4=1))
    (hc.symm ▸ hu.map_of_injective e.injective) (hc.symm ▸ hw) true
  rw [hc] at H
  rw [H,five_det]; decide +kernel
end Q9
end NearHadamard.Optimal
