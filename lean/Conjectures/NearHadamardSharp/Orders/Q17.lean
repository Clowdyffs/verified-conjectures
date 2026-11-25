module
public import Conjectures.NearHadamardSharp.Exact
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Q17
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩
abbrev F0 := ZMod 17
def w : F0 := 3
theorem hc : Fintype.card F0=17 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (17-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 17%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨3,1⟩
def zi : Torus.Model w := ⟨9,14⟩
theorem hz : IsPrimitiveRoot z (17*17-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 2, 3, 3] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
private def torusRow : Array ℤ := #[0,-1,1,-1,-1,-1,-1,1,-1]
private def torusL : Array (Array ℤ) := #[#[1],#[1,9],#[-1,1,10],#[1,-1,1,11],#[7,5,-5,5,48],#[20,26,15,-15,20,164],#[356,380,405,285,-196,380,2760],#[-4775,6707,8200,7885,5195,-4712,7245,57095],#[63,-37,58,83,83,58,-37,63,538]]
private def torusD : Array ℤ := #[18,160,176,192,820,2760,45676,938272,8720]
theorem torus_det : |(Source.class4 17 z).det| = 124581314560 := by
  apply torusExactRow z hc (by decide) hw hz torusRow _ (by decide) (by decide +kernel)
  apply arrayCert (coreMatrix (n:=9) 17 torusRow) torusL torusD <;> decide +kernel
private def inverseRow : Array ℤ := #[0,1,-1,1,1,1,1,-1,1]
private def inverseL : Array (Array ℤ) := #[#[1],#[-1,9],#[1,-1,8],#[-1,1,-1,7],#[-1,-2,2,-2,15],#[-5,-2,-6,6,-5,40],#[-80,-95,-54,-114,130,-95,840],#[3832,-3097,-2570,-2318,-4042,3895,-3528,27968],#[-126,134,-113,-61,-61,-113,134,-126,862]]
private def inverseD : Array ℤ := #[18,160,140,120,256,672,13984,456860,13780]
theorem inverse_det : |(Source.class4 17 zi).det| = 119658905600 := by
  apply torusExactRow zi hc (by decide) hw (invz ▸ hz.inv) inverseRow _ (by decide) (by decide +kernel)
  apply arrayCert (coreMatrix (n:=9) 17 inverseRow) inverseL inverseD <;> decide +kernel
private def fiveRow : Array ℤ := #[0,1,-1,-1,1,-1,-1,1]
private def fiveL : Array (Array ℤ) := #[#[1],#[-1,9],#[-1,-1,10],#[-5,6,-5,44],#[-5,4,5,-4,40],#[-1,-1,1,1,-1,9],#[-5,7,-5,5,5,-5,38],#[-420,247,510,-355,420,355,-342,2945],#[-168,-171,133,213,-187,213,133,-171,1349]]
private def fiveD : Array ℤ := #[18,160,176,760,684,152,620,47712,21504]
theorem five_det : |(Source.bordered 17 w true).det| = 118380036096 := by
  apply borderExactRow hc (by decide) hw true fiveRow _ (by decide) (by decide +kernel)
  apply arrayCert (borderedMatrix (m:=8) 17 true fiveRow) fiveL fiveD <;> decide +kernel
private def sixRow : Array ℤ := #[0,-1,1,1,-1,1,1,-1]
private def sixL : Array (Array ℤ) := #[#[1],#[1,9],#[1,1,8],#[4,-3,4,35],#[4,-5,-4,5,40],#[1,1,-1,-1,1,9],#[2,-1,2,-2,-2,2,19],#[138,-209,-102,182,-138,-182,171,1520],#[345,342,-437,-273,383,-273,-437,342,3458]]
private def sixD : Array ℤ := #[18,160,140,608,684,152,320,25116,56580]
theorem six_det : |(Source.bordered 17 w false).det| = 127926927360 := by
  apply borderExactRow hc (by decide) hw false sixRow _ (by decide) (by decide +kernel)
  apply arrayCert (borderedMatrix (m:=8) 17 false sixRow) sixL sixD <;> decide +kernel
theorem verified : AtOrder 17 := by
  apply modelOrder w z hc (by decide) hw hz
  · rw [torus_det]; decide +kernel
  · rw [invz]; rw [inverse_det]; decide +kernel
  · rw [five_det]; decide +kernel
  · rw [six_det]; decide +kernel

theorem nonordinaryAttained : (441/544 : ℚ) ∈ values 10 .five := by
  apply modelValue w z hc (by decide) (by decide) hw hz
  simp only [magnitude, five_det]; decide +kernel

theorem fiveAbove (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (u : F) (h : Fintype.card F = 17) (hu : IsPrimitiveRoot u (17-1)) :
    (441/544 : ℚ) ≤ (|(Source.bordered 17 u true).det|:ℤ)/(delta 17:ℚ) := by
  let e := FiniteField.ringEquivOfCardEq (h.trans hc.symm)
  rw [←Border.transport e 17 u true]
  have H := Border.primitive_independent (w:=e u) (z:=w) (hc.symm ▸ (by decide : 17%4=1))
    (hc.symm ▸ hu.map_of_injective e.injective) (hc.symm ▸ hw) true
  rw [hc] at H
  rw [H,five_det]; decide +kernel
end Q17
end NearHadamard.Optimal
