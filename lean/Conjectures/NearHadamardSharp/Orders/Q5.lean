module
public import Conjectures.NearHadamardSharp.Exact
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Q5
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev F0 := ZMod 5
def w : F0 := 2
theorem hc : Fintype.card F0=5 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (5-1) := by
  apply Small.primitiveCheck [2, 2] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 5%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨2,1⟩
def zi : Torus.Model w := ⟨1,2⟩
theorem hz : IsPrimitiveRoot z (5*5-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
private def torusRow : Array ℤ := #[0,1,1]
private def torusL : Array (Array ℤ) := #[#[1],#[-1,3],#[-1,-1,4]]
private def torusD : Array ℤ := #[6,16,20]
theorem torus_det : |(Source.class4 5 z).det| = 160 := by
  apply torusExactRow z hc (by decide) hw hz torusRow _ (by decide) (by decide +kernel)
  apply arrayCert (coreMatrix (n:=3) 5 torusRow) torusL torusD <;> decide +kernel
private def inverseRow : Array ℤ := #[0,-1,-1]
private def inverseL : Array (Array ℤ) := #[#[1],#[1,3],#[1,1,2]]
private def inverseD : Array ℤ := #[6,16,8]
theorem inverse_det : |(Source.class4 5 zi).det| = 128 := by
  apply torusExactRow zi hc (by decide) hw (invz ▸ hz.inv) inverseRow _ (by decide) (by decide +kernel)
  apply arrayCert (coreMatrix (n:=3) 5 inverseRow) inverseL inverseD <;> decide +kernel
private def fiveRow : Array ℤ := #[0,-1]
private def fiveL : Array (Array ℤ) := #[#[1],#[-1,3],#[-1,1,2]]
private def fiveD : Array ℤ := #[6,16,8]
theorem five_det : |(Source.bordered 5 w true).det| = 128 := by
  apply borderExactRow hc (by decide) hw true fiveRow _ (by decide) (by decide +kernel)
  apply arrayCert (borderedMatrix (m:=2) 5 true fiveRow) fiveL fiveD <;> decide +kernel
private def sixRow : Array ℤ := #[0,1]
private def sixL : Array (Array ℤ) := #[#[1],#[1,3],#[1,-1,4]]
private def sixD : Array ℤ := #[6,16,20]
theorem six_det : |(Source.bordered 5 w false).det| = 160 := by
  apply borderExactRow hc (by decide) hw false sixRow _ (by decide) (by decide +kernel)
  apply arrayCert (borderedMatrix (m:=2) 5 false sixRow) sixL sixD <;> decide +kernel
theorem verified : AtOrder 5 := by
  apply modelOrder w z hc (by decide) hw hz
  · rw [torus_det]; decide +kernel
  · rw [invz]; rw [inverse_det]; decide +kernel
  · rw [five_det]; decide +kernel
  · rw [six_det]; decide +kernel
theorem attained : fullMinimum .five ∈ values 0 .five := by
  apply modelValue w z hc (by decide) (by decide) hw hz
  simp only [magnitude]
  rw [five_det]; decide +kernel
end Q5
end NearHadamard.Optimal
