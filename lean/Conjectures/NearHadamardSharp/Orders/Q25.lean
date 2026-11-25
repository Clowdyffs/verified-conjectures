module
public import Conjectures.NearHadamardSharp.Exact
public import Conjectures.NearHadamardSharp.Cubic
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Q25
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev F0 := ZMod 5
def d0 : F0 := 2
local instance : Fact (∀ x : F0, x^2≠d0+0*x) := ⟨by decide +kernel⟩
abbrev F1 := Torus.Model d0
def w : F1 := ⟨2,1⟩
theorem hc : Fintype.card F1=25 := by simp [F0,F1,Small.card_model]
theorem hw : IsPrimitiveRoot w (25-1) := by
  apply Small.primitiveCheck [2, 2, 2, 3] <;> decide +kernel
local instance : Fact (∀ x : F1, x^2≠w+0*x) :=
  ⟨Torus.irreducible (Border.char_generator (hc.symm ▸ (by decide : 25%4=1)) (hc.symm ▸ hw))⟩
def z : Torus.Model w := ⟨⟨2,0⟩,⟨1,0⟩⟩
def zi : Torus.Model w := ⟨⟨2,1⟩,⟨4,2⟩⟩
theorem hz : IsPrimitiveRoot z (25*25-1) := by
  apply Small.primitiveCheck [2, 2, 2, 2, 3, 13] <;> decide +kernel
theorem invz : z⁻¹=zi := inv_eq_of_mul_eq_one_right (by decide +kernel : z*zi=1)
private def torusRow : Array ℤ := #[0,1,-1,-1,-1,1,-1,-1,1,-1,-1,-1,1]
private def torusL : Array (Array ℤ) := #[#[1],#[-1,13],#[1,-1,12],#[5,6,-6,77],#[21,17,24,-21,287],#[-3,3,2,3,-3,38],#[26,-21,21,14,21,-21,240],#[4464,7399,-5901,6552,4585,5901,-5808,71904],#[-436860,368352,516197,-468138,449046,377945,395328,-460464,5364852],#[3501407,-2998739,2533096,3434898,-2598326,2467946,2671232,2682104,-3129121,33135373],#[32575,37272,-31919,31816,42008,-32496,31816,33272,27959,-32616,381833],#[577,696,895,-680,776,912,-680,776,713,696,-697,8736],#[-34,29,29,38,-34,38,38,-34,38,29,29,-34,398]]
private def torusD : Array ℤ := #[26,336,308,1968,7296,960,5992,1788284,132541492,809485960,9260160,210940,9540]
theorem torus_det : |(Source.class4 25 z).det| = 1489278420910080000 := by
  apply torusExactRow z hc (by decide) hw hz torusRow _ (by decide) (by decide +kernel)
  apply arrayCert (coreMatrix (n:=13) 25 torusRow) torusL torusD <;> decide +kernel
private def inverseRow : Array ℤ := #[0,-1,1,1,1,-1,1,1,-1,1,1,1,-1]
private def inverseL : Array (Array ℤ) := #[#[1],#[1,13],#[-1,1,14],#[-8,-7,7,90],#[-42,-47,-35,42,492],#[7,-7,-9,-7,7,89],#[-13,21,-21,-27,-21,21,280],#[-5390,-3261,5019,-4095,-5529,-5019,4865,61530],#[371714,-440755,-314763,404383,-381927,-451949,-457485,391790,5366984],#[-1862419,2168858,-2574150,-1794857,2639913,-2508467,-2693085,-2683690,2300306,33278013],#[-65683,-54810,63838,-64165,-43495,66045,-64165,-67610,-76718,65765,898228],#[-2207,-1925,-1283,1880,-1565,-1330,1880,-1565,-1972,-1925,1927,24115],#[47,-55,-55,-38,47,-38,-38,47,-38,-55,-55,47,642]]
private def inverseD : Array ℤ := #[26,336,360,2296,12460,2240,7032,1533424,133112052,822776848,22089340,588072,15572]
theorem inverse_det : |(Source.class4 25 zi).det| = 1568703055044542464 := by
  apply torusExactRow zi hc (by decide) hw (invz ▸ hz.inv) inverseRow _ (by decide) (by decide +kernel)
  apply arrayCert (coreMatrix (n:=13) 25 inverseRow) inverseL inverseD <;> decide +kernel
private def fiveRow : Array ℤ := #[0,-1,1,1,-1,-1,1,-1,-1,1,1,-1]
private def fiveL : Array (Array ℤ) := #[#[1],#[-1,13],#[-1,1,12],#[-6,-5,6,77],#[-6,-7,-6,7,84],#[-1,1,-1,-1,1,13],#[-7,9,7,-7,-7,7,82],#[-1673,-1353,2184,1904,-1673,-1904,1640,20951],#[-445257,245303,-325048,533392,464855,-403376,-458872,401431,5330656],#[-3038553,3367327,1772638,-2302750,3048262,3172295,-2160998,-3046930,2640848,33010497],#[-1270549,-646394,1422249,835590,-965654,1272180,1328901,-900830,-1368426,1090026,14449495],#[-163590,-243629,-112504,230175,136864,-163021,163800,209791,-145264,-223245,169624,2104079],#[-210,182,-277,-154,263,182,-181,182,263,-154,-277,182,2519]]
private def fiveD : Array ℤ := #[26,336,308,1968,2132,328,2044,520064,132041988,809171720,353485272,50783040,60480]
theorem five_det : |(Source.bordered 25 w true).det| = 1503521162448076800 := by
  apply borderExactRow hc (by decide) hw true fiveRow _ (by decide) (by decide +kernel)
  apply arrayCert (borderedMatrix (m:=12) 25 true fiveRow) fiveL fiveD <;> decide +kernel
private def sixRow : Array ℤ := #[0,1,-1,-1,1,1,-1,1,1,-1,-1,1]
private def sixL : Array (Array ℤ) := #[#[1],#[1,13],#[1,-1,14],#[7,8,-7,90],#[7,6,7,-6,84],#[1,-1,1,1,-1,13],#[3,-2,-3,3,3,-3,41],#[843,943,-585,-705,843,705,-820,10578],#[384689,-587776,528285,-338635,-407731,470705,393395,-472156,5414870],#[2250636,-1725089,-3475638,3133723,-2239038,-2385444,3011718,2258597,-2725530,33404969],#[1280676,1880913,-1037956,-1654863,1776308,-1282320,-1349142,1720623,962332,-1494573,17127466],#[673056,325573,924345,-507472,-805545,874123,-673920,-649627,840105,467728,-721305,8675723],#[864,-1053,545,1242,-815,-1053,1310,-1053,-815,1242,545,-1053,12190]]
private def sixD : Array ℤ := #[26,336,360,2296,2132,328,1032,264140,133619876,822118368,416434704,210643200,293760]
theorem six_det : |(Source.bordered 25 w false).det| = 1532952855340646400 := by
  apply borderExactRow hc (by decide) hw false sixRow _ (by decide) (by decide +kernel)
  apply arrayCert (borderedMatrix (m:=12) 25 false sixRow) sixL sixD <;> decide +kernel
theorem verified : AtOrder 25 := by
  apply modelOrder w z hc (by decide) hw hz
  · rw [torus_det]; decide +kernel
  · rw [invz]; rw [inverse_det]; decide +kernel
  · rw [five_det]; decide +kernel
  · rw [six_det]; decide +kernel

theorem fiveAbove (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (u : F) (h : Fintype.card F = 25) (hu : IsPrimitiveRoot u (25-1)) :
    (441/544 : ℚ) ≤ (|(Source.bordered 25 u true).det|:ℤ)/(delta 25:ℚ) := by
  let e := FiniteField.ringEquivOfCardEq (h.trans hc.symm)
  rw [←Border.transport e 25 u true]
  have H := Border.primitive_independent (w:=e u) (z:=w) (hc.symm ▸ (by decide : 25%4=1))
    (hc.symm ▸ hu.map_of_injective e.injective) (hc.symm ▸ hw) true
  rw [hc] at H
  rw [H,five_det]; decide +kernel
end Q25
end NearHadamard.Optimal
