module
public import Conjectures.NearHadamardSharp.Exact
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Q29
local instance : Fact (Nat.Prime 29) := ⟨by decide⟩
abbrev F0 := ZMod 29
def w : F0 := 2
theorem hc : Fintype.card F0=29 := by simp [F0,Small.card_model]
theorem hw : IsPrimitiveRoot w (29-1) := by
  apply Small.primitiveCheck [2, 2, 7] <;> decide +kernel
local instance : Fact (∀ x : F0, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 29%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨4,1⟩
def zi : Torus.Model w := ⟨21,2⟩
theorem hz : IsPrimitiveRoot z (29*29-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3, 5, 7] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
private def inverseRow : Array ℤ := #[0,-1,-1,-1,1,1,-1,1,1,-1,1,1,-1,-1,-1]
private def inverseL : Array (Array ℤ) := #[#[1],#[1,15],#[1,1,14],#[1,1,1,13],#[-5,7,7,7,96],#[-376,-322,385,385,432,5656],#[18104,-20672,-17655,23815,21552,24136,331760],#[-186607,118768,-163239,-142457,184023,169177,166256,2425233],#[-673739,-724216,384541,-644245,-478037,713989,581704,655925,8811992],#[2099305,-2277432,-2477448,1559143,-2441040,-1880256,2670697,1928712,2208840,31830871],#[-18937687,13786200,-17529096,-19409257,12333600,-16106160,-14452327,20684328,15228216,14639255,228960096],#[-266314222,-287602118,179259363,-274508010,-260501949,194951645,-244464515,-183913569,315918774,201539619,231187454,3271295314],#[145858138,-129683810,-142196009,108316170,-152499213,-147836531,111171445,-140121293,-108916326,174059847,93118750,109652722,1719602536],#[23193241,39539329,-32583890,-34757139,26795124,-41683205,-37077194,27015244,-38620245,-26959824,43501489,22549390,30580171,448714959],#[5503,4333,7024,-5027,-6262,4099,-6782,-6782,4099,-6262,-5027,7024,4333,5503,76574]]
private def inverseD : Array ℤ := #[30,448,416,384,2828,165880,9700932,70495936,254646968,915840384,6542590628,92858536944,48461215572,12611737800,2141100]
theorem inverse_det : |(Source.class4 29 zi).det| = 8625970539669749760000 := by
  apply torusExactRow zi hc (by decide) hw (invz ▸ hz.inv) inverseRow _ (by decide) (by decide +kernel)
  apply arrayCert (coreMatrix (n:=15) 29 inverseRow) inverseL inverseD <;> decide +kernel
private def sixRow : Array ℤ := #[0,1,1,-1,-1,1,-1,1,-1,1,-1,-1,1,1]
private def sixL : Array (Array ℤ) := #[#[1],#[1,15],#[1,-1,16],#[1,-1,-1,17],#[4,5,-4,-4,63],#[220,217,244,-220,-189,3248],#[20735,-27286,23863,26895,-24633,-21224,333410],#[54288,63509,-70285,53240,70416,-55256,-56723,809419],#[41328,-34787,53515,-54152,39792,54344,-41419,-48349,650976],#[861,829,-742,994,-990,829,994,-742,-990,12733],#[5781,-6019,6426,-4982,6674,-7507,6426,6674,-4982,-7507,91512],#[16527879,19992789,-17533407,15879608,-11697031,19026785,-21462513,18426115,16534459,-11751212,-21137427,241640019],#[560609874,468278829,598429278,-583510997,539890189,-338375900,566905392,-649522960,566620004,559564013,-409795317,-637254306,7727919885],#[11064021826,-11644242459,10907595630,13329582195,-13238348987,10614828740,-6209252496,11188268208,-13287611644,11222911717,12765738771,-9606761106,-14242443003,164160061824],#[846365,-1107026,-873229,972739,1023476,-1177651,973191,-592311,973191,-1177651,1023476,972739,-873229,-1107026,13664786]]
private def sixD : Array ℤ := #[30,448,476,504,1856,95260,9713028,23435136,18793908,366048,2619404,6869262120,218880082432,4626158641156,382556980]
theorem six_det : |(Source.bordered 29 w false).det| = 8691479386489219973120 := by
  apply borderExactRow hc (by decide) hw false sixRow _ (by decide) (by decide +kernel)
  apply arrayCert (borderedMatrix (m:=14) 29 false sixRow) sixL sixD <;> decide +kernel
theorem verified : AtOrder 29 := by
  apply modelOrder w z hc (by decide) hw hz
  · apply torusGood z hc (by decide) hw hz (by decide); decide +kernel
  · rw [invz]; rw [inverse_det]; decide +kernel
  · apply borderGood hc (by decide) hw (by decide) true; decide +kernel
  · rw [six_det]; decide +kernel
theorem attained : restrictedMinimum .four ∈ values 30 .four := by
  apply modelValue w zi hc (by decide) (by decide) hw (invz ▸ hz.inv)
  simp only [magnitude]
  rw [inverse_det]; decide +kernel
end Q29
end NearHadamard.Optimal
