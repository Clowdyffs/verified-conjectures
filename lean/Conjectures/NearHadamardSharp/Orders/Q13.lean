module
public import Conjectures.NearHadamardSharp.Exact
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Q13
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
abbrev F0 := ZMod 13
def w : F0 := 2
theorem hc : Fintype.card F0=13 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (13-1) := by
  apply Small.primitiveCheck [2, 2, 3] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 13%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,6⟩
theorem hz : IsPrimitiveRoot z (13*13-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 7] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
private def torusRow : Array ℤ := #[0,-1,1,1,1,1,-1]
private def torusL : Array (Array ℤ) := #[#[1],#[1,7],#[-1,1,8],#[-5,-4,4,27],#[-6,-7,-4,6,33],#[-17,-22,-20,-9,22,104],#[16,-11,-20,-20,-11,16,88]]
private def torusD : Array ℤ := #[14,96,108,352,416,1276,1044]
theorem torus_det : |(Source.class4 13 z).det| = 62005248 := by
  apply torusExactRow z hc (by decide) hw hz torusRow _ (by decide) (by decide +kernel)
  apply arrayCert (coreMatrix (n:=7) 13 torusRow) torusL torusD <;> decide +kernel
private def inverseRow : Array ℤ := #[0,1,-1,-1,-1,-1,1]
private def inverseL : Array (Array ℤ) := #[#[1],#[-1,7],#[1,-1,6],#[2,3,-3,20],#[12,7,15,-12,88],#[43,33,30,52,-33,285],#[-9,11,6,6,11,-9,66]]
private def inverseD : Array ℤ := #[14,96,80,264,1140,3608,820]
theorem inverse_det : |(Source.class4 13 zi).det| = 68853760 := by
  apply torusExactRow zi hc (by decide) hw (invz ▸ hz.inv) inverseRow _ (by decide) (by decide +kernel)
  apply arrayCert (coreMatrix (n:=7) 13 inverseRow) inverseL inverseD <;> decide +kernel
private def fiveRow : Array ℤ := #[0,1,-1,-1,-1,1]
private def fiveL : Array (Array ℤ) := #[#[1],#[-1,7],#[-1,-1,8],#[-4,5,-4,27],#[-4,3,4,-3,24],#[-15,13,8,15,-8,77],#[-15,-11,16,7,16,-11,88]]
private def fiveD : Array ℤ := #[14,96,108,352,308,960,1080]
theorem five_det : |(Source.bordered 13 w true).det| = 66355200 := by
  apply borderExactRow hc (by decide) hw true fiveRow _ (by decide) (by decide +kernel)
  apply arrayCert (borderedMatrix (m:=6) 13 true fiveRow) fiveL fiveD <;> decide +kernel
private def sixRow : Array ℤ := #[0,-1,1,1,1,-1]
private def sixL : Array (Array ℤ) := #[#[1],#[1,7],#[1,1,6],#[3,-2,3,20],#[3,-4,-3,4,24],#[8,-13,-15,-8,15,77],#[8,11,-9,-14,-9,11,66]]
private def sixD : Array ℤ := #[14,96,80,264,308,960,800]
theorem six_det : |(Source.bordered 13 w false).det| = 65536000 := by
  apply borderExactRow hc (by decide) hw false sixRow _ (by decide) (by decide +kernel)
  apply arrayCert (borderedMatrix (m:=6) 13 false sixRow) sixL sixD <;> decide +kernel
theorem verified : AtOrder 13 := by
  apply modelOrder w z hc (by decide) hw hz
  · rw [torus_det]; decide +kernel
  · rw [invz]; rw [inverse_det]; decide +kernel
  · rw [five_det]; decide +kernel
  · rw [six_det]; decide +kernel
theorem attained : fullMinimum .four ∈ values 0 .four := by
  apply modelValue w z hc (by decide) (by decide) hw hz
  simp only [magnitude]
  rw [torus_det]; decide +kernel

theorem fiveAbove (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (u : F) (h : Fintype.card F = 13) (hu : IsPrimitiveRoot u (13-1)) :
    (441/544 : ℚ) ≤ (|(Source.bordered 13 u true).det|:ℤ)/(delta 13:ℚ) := by
  let e := FiniteField.ringEquivOfCardEq (h.trans hc.symm)
  rw [←Border.transport e 13 u true]
  have H := Border.primitive_independent (w:=e u) (z:=w) (hc.symm ▸ (by decide : 13%4=1))
    (hc.symm ▸ hu.map_of_injective e.injective) (hc.symm ▸ hw) true
  rw [hc] at H
  rw [H,five_det]; decide +kernel
end Q13
end NearHadamard.Optimal
