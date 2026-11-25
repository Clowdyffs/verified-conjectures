module
public import Conjectures.NearHadamardSharp.Orders.M1009
public import Conjectures.NearHadamardSharp.Orders.M1049
public import Conjectures.NearHadamardSharp.Orders.M1097
public import Conjectures.NearHadamardSharp.Orders.M1153
public import Conjectures.NearHadamardSharp.Orders.M1213
public import Conjectures.NearHadamardSharp.Orders.M1249
public import Conjectures.NearHadamardSharp.Orders.M1301
public import Conjectures.NearHadamardSharp.Orders.M1373
public import Conjectures.NearHadamardSharp.Orders.M1433
public import Conjectures.NearHadamardSharp.Orders.M1493
public import Conjectures.NearHadamardSharp.Orders.M157
public import Conjectures.NearHadamardSharp.Orders.M1601
public import Conjectures.NearHadamardSharp.Orders.M1637
public import Conjectures.NearHadamardSharp.Orders.M1693
public import Conjectures.NearHadamardSharp.Orders.M1733
public import Conjectures.NearHadamardSharp.Orders.M1789
public import Conjectures.NearHadamardSharp.Orders.M1873
public import Conjectures.NearHadamardSharp.Orders.M1913
public import Conjectures.NearHadamardSharp.Orders.M193
public import Conjectures.NearHadamardSharp.Orders.M1993
public import Conjectures.NearHadamardSharp.Orders.M2053
public import Conjectures.NearHadamardSharp.Orders.M2113
public import Conjectures.NearHadamardSharp.Orders.M2153
public import Conjectures.NearHadamardSharp.Orders.M241
public import Conjectures.NearHadamardSharp.Orders.M281
public import Conjectures.NearHadamardSharp.Orders.M317
public import Conjectures.NearHadamardSharp.Orders.M361
public import Conjectures.NearHadamardSharp.Orders.M401
public import Conjectures.NearHadamardSharp.Orders.M449
public import Conjectures.NearHadamardSharp.Orders.M521
public import Conjectures.NearHadamardSharp.Orders.M569
public import Conjectures.NearHadamardSharp.Orders.M613
public import Conjectures.NearHadamardSharp.Orders.M653
public import Conjectures.NearHadamardSharp.Orders.M701
public import Conjectures.NearHadamardSharp.Orders.M757
public import Conjectures.NearHadamardSharp.Orders.M797
public import Conjectures.NearHadamardSharp.Orders.M841
public import Conjectures.NearHadamardSharp.Orders.M881
public import Conjectures.NearHadamardSharp.Orders.M953
public import Conjectures.NearHadamardSharp.Orders.Q101
public import Conjectures.NearHadamardSharp.Orders.Q109
public import Conjectures.NearHadamardSharp.Orders.Q113
public import Conjectures.NearHadamardSharp.Orders.Q121
public import Conjectures.NearHadamardSharp.Orders.Q125
public import Conjectures.NearHadamardSharp.Orders.Q13
public import Conjectures.NearHadamardSharp.Orders.Q137
public import Conjectures.NearHadamardSharp.Orders.Q149
public import Conjectures.NearHadamardSharp.Orders.Q17
public import Conjectures.NearHadamardSharp.Orders.Q25
public import Conjectures.NearHadamardSharp.Orders.Q29
public import Conjectures.NearHadamardSharp.Orders.Q37
public import Conjectures.NearHadamardSharp.Orders.Q41
public import Conjectures.NearHadamardSharp.Orders.Q49
public import Conjectures.NearHadamardSharp.Orders.Q5
public import Conjectures.NearHadamardSharp.Orders.Q53
public import Conjectures.NearHadamardSharp.Orders.Q61
public import Conjectures.NearHadamardSharp.Orders.Q73
public import Conjectures.NearHadamardSharp.Orders.Q81
public import Conjectures.NearHadamardSharp.Orders.Q89
public import Conjectures.NearHadamardSharp.Orders.Q9
public import Conjectures.NearHadamardSharp.Orders.Q97
public import Conjectures.NearHadamardSharp.Tail
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Optimal
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
private theorem band2 (q : ℕ) (h : IsPrimePow q) (hm : q%4=1)
    (hl : 2≤q) (hh : q<109) : AtOrder q := by
  have check : ∀ i : Fin 107, let q := i.val+2; IsPrimePow q → q%4=1 → ((((q = 5 ∨ q = 9) ∨ (q = 13 ∨ q = 17)) ∨ ((q = 25 ∨ q = 29) ∨ (q = 37 ∨ q = 41))) ∨ (((q = 49 ∨ q = 53) ∨ (q = 61 ∨ q = 73)) ∨ ((q = 81 ∨ q = 89) ∨ (q = 97 ∨ q = 101)))) := by decide +kernel
  have e : (q-2)+2=q := Nat.sub_add_cancel hl
  have r := check ⟨q-2,by omega⟩
  dsimp only at r
  rw [e] at r
  rcases r h hm with ((((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl)))|(((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl))))
  · exact Q5.verified
  · exact Q9.verified
  · exact Q13.verified
  · exact Q17.verified
  · exact Q25.verified
  · exact Q29.verified
  · exact Q37.verified
  · exact Q41.verified
  · exact Q49.verified
  · exact Q53.verified
  · exact Q61.verified
  · exact Q73.verified
  · exact Q81.verified
  · exact Q89.verified
  · exact Q97.verified
  · exact Q101.verified
private theorem band109 (q : ℕ) (h : IsPrimePow q) (hm : q%4=1)
    (hl : 109≤q) (hh : q<269) : AtOrder q := by
  have check : ∀ i : Fin 160, let q := i.val+109; IsPrimePow q → q%4=1 → ((((q = 109 ∨ q = 113) ∨ (q = 121 ∨ q = 125)) ∨ ((q = 137 ∨ q = 149) ∨ (q = 157 ∨ q = 169))) ∨ (((q = 173 ∨ q = 181) ∨ (q = 193 ∨ q = 197)) ∨ ((q = 229 ∨ q = 233) ∨ (q = 241 ∨ q = 257)))) := by decide +kernel
  have e : (q-109)+109=q := Nat.sub_add_cancel hl
  have r := check ⟨q-109,by omega⟩
  dsimp only at r
  rw [e] at r
  rcases r h hm with ((((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl)))|(((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl))))
  · exact Q109.verified
  · exact Q113.verified
  · exact Q121.verified
  · exact Q125.verified
  · exact Q137.verified
  · exact Q149.verified
  · exact Q157.verified
  · exact Q169.verified
  · exact Q173.verified
  · exact Q181.verified
  · exact Q193.verified
  · exact Q197.verified
  · exact Q229.verified
  · exact Q233.verified
  · exact Q241.verified
  · exact Q257.verified
private theorem band269 (q : ℕ) (h : IsPrimePow q) (hm : q%4=1)
    (hl : 269≤q) (hh : q<421) : AtOrder q := by
  have check : ∀ i : Fin 152, let q := i.val+269; IsPrimePow q → q%4=1 → ((((q = 269 ∨ q = 277) ∨ (q = 281 ∨ q = 289)) ∨ ((q = 293 ∨ q = 313) ∨ (q = 317 ∨ q = 337))) ∨ (((q = 349 ∨ q = 353) ∨ (q = 361 ∨ q = 373)) ∨ ((q = 389 ∨ q = 397) ∨ (q = 401 ∨ q = 409)))) := by decide +kernel
  have e : (q-269)+269=q := Nat.sub_add_cancel hl
  have r := check ⟨q-269,by omega⟩
  dsimp only at r
  rw [e] at r
  rcases r h hm with ((((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl)))|(((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl))))
  · exact Q269.verified
  · exact Q277.verified
  · exact Q281.verified
  · exact Q289.verified
  · exact Q293.verified
  · exact Q313.verified
  · exact Q317.verified
  · exact Q337.verified
  · exact Q349.verified
  · exact Q353.verified
  · exact Q361.verified
  · exact Q373.verified
  · exact Q389.verified
  · exact Q397.verified
  · exact Q401.verified
  · exact Q409.verified
private theorem band421 (q : ℕ) (h : IsPrimePow q) (hm : q%4=1)
    (hl : 421≤q) (hh : q<625) : AtOrder q := by
  have check : ∀ i : Fin 204, let q := i.val+421; IsPrimePow q → q%4=1 → ((((q = 421 ∨ q = 433) ∨ (q = 449 ∨ q = 457)) ∨ ((q = 461 ∨ q = 509) ∨ (q = 521 ∨ q = 529))) ∨ (((q = 541 ∨ q = 557) ∨ (q = 569 ∨ q = 577)) ∨ ((q = 593 ∨ q = 601) ∨ (q = 613 ∨ q = 617)))) := by decide +kernel
  have e : (q-421)+421=q := Nat.sub_add_cancel hl
  have r := check ⟨q-421,by omega⟩
  dsimp only at r
  rw [e] at r
  rcases r h hm with ((((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl)))|(((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl))))
  · exact Q421.verified
  · exact Q433.verified
  · exact Q449.verified
  · exact Q457.verified
  · exact Q461.verified
  · exact Q509.verified
  · exact Q521.verified
  · exact Q529.verified
  · exact Q541.verified
  · exact Q557.verified
  · exact Q569.verified
  · exact Q577.verified
  · exact Q593.verified
  · exact Q601.verified
  · exact Q613.verified
  · exact Q617.verified
private theorem band625 (q : ℕ) (h : IsPrimePow q) (hm : q%4=1)
    (hl : 625≤q) (hh : q<821) : AtOrder q := by
  have check : ∀ i : Fin 196, let q := i.val+625; IsPrimePow q → q%4=1 → ((((q = 625 ∨ q = 641) ∨ (q = 653 ∨ q = 661)) ∨ ((q = 673 ∨ q = 677) ∨ (q = 701 ∨ q = 709))) ∨ (((q = 729 ∨ q = 733) ∨ (q = 757 ∨ q = 761)) ∨ ((q = 769 ∨ q = 773) ∨ (q = 797 ∨ q = 809)))) := by decide +kernel
  have e : (q-625)+625=q := Nat.sub_add_cancel hl
  have r := check ⟨q-625,by omega⟩
  dsimp only at r
  rw [e] at r
  rcases r h hm with ((((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl)))|(((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl))))
  · exact Q625.verified
  · exact Q641.verified
  · exact Q653.verified
  · exact Q661.verified
  · exact Q673.verified
  · exact Q677.verified
  · exact Q701.verified
  · exact Q709.verified
  · exact Q729.verified
  · exact Q733.verified
  · exact Q757.verified
  · exact Q761.verified
  · exact Q769.verified
  · exact Q773.verified
  · exact Q797.verified
  · exact Q809.verified
private theorem band821 (q : ℕ) (h : IsPrimePow q) (hm : q%4=1)
    (hl : 821≤q) (hh : q<1021) : AtOrder q := by
  have check : ∀ i : Fin 200, let q := i.val+821; IsPrimePow q → q%4=1 → ((((q = 821 ∨ q = 829) ∨ (q = 841 ∨ q = 853)) ∨ ((q = 857 ∨ q = 877) ∨ (q = 881 ∨ q = 929))) ∨ (((q = 937 ∨ q = 941) ∨ (q = 953 ∨ q = 961)) ∨ ((q = 977 ∨ q = 997) ∨ (q = 1009 ∨ q = 1013)))) := by decide +kernel
  have e : (q-821)+821=q := Nat.sub_add_cancel hl
  have r := check ⟨q-821,by omega⟩
  dsimp only at r
  rw [e] at r
  rcases r h hm with ((((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl)))|(((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl))))
  · exact Q821.verified
  · exact Q829.verified
  · exact Q841.verified
  · exact Q853.verified
  · exact Q857.verified
  · exact Q877.verified
  · exact Q881.verified
  · exact Q929.verified
  · exact Q937.verified
  · exact Q941.verified
  · exact Q953.verified
  · exact Q961.verified
  · exact Q977.verified
  · exact Q997.verified
  · exact Q1009.verified
  · exact Q1013.verified
private theorem band1021 (q : ℕ) (h : IsPrimePow q) (hm : q%4=1)
    (hl : 1021≤q) (hh : q<1229) : AtOrder q := by
  have check : ∀ i : Fin 208, let q := i.val+1021; IsPrimePow q → q%4=1 → ((((q = 1021 ∨ q = 1033) ∨ (q = 1049 ∨ q = 1061)) ∨ ((q = 1069 ∨ q = 1093) ∨ (q = 1097 ∨ q = 1109))) ∨ (((q = 1117 ∨ q = 1129) ∨ (q = 1153 ∨ q = 1181)) ∨ ((q = 1193 ∨ q = 1201) ∨ (q = 1213 ∨ q = 1217)))) := by decide +kernel
  have e : (q-1021)+1021=q := Nat.sub_add_cancel hl
  have r := check ⟨q-1021,by omega⟩
  dsimp only at r
  rw [e] at r
  rcases r h hm with ((((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl)))|(((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl))))
  · exact Q1021.verified
  · exact Q1033.verified
  · exact Q1049.verified
  · exact Q1061.verified
  · exact Q1069.verified
  · exact Q1093.verified
  · exact Q1097.verified
  · exact Q1109.verified
  · exact Q1117.verified
  · exact Q1129.verified
  · exact Q1153.verified
  · exact Q1181.verified
  · exact Q1193.verified
  · exact Q1201.verified
  · exact Q1213.verified
  · exact Q1217.verified
private theorem band1229 (q : ℕ) (h : IsPrimePow q) (hm : q%4=1)
    (hl : 1229≤q) (hh : q<1481) : AtOrder q := by
  have check : ∀ i : Fin 252, let q := i.val+1229; IsPrimePow q → q%4=1 → ((((q = 1229 ∨ q = 1237) ∨ (q = 1249 ∨ q = 1277)) ∨ ((q = 1289 ∨ q = 1297) ∨ (q = 1301 ∨ q = 1321))) ∨ (((q = 1361 ∨ q = 1369) ∨ (q = 1373 ∨ q = 1381)) ∨ ((q = 1409 ∨ q = 1429) ∨ (q = 1433 ∨ q = 1453)))) := by decide +kernel
  have e : (q-1229)+1229=q := Nat.sub_add_cancel hl
  have r := check ⟨q-1229,by omega⟩
  dsimp only at r
  rw [e] at r
  rcases r h hm with ((((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl)))|(((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl))))
  · exact Q1229.verified
  · exact Q1237.verified
  · exact Q1249.verified
  · exact Q1277.verified
  · exact Q1289.verified
  · exact Q1297.verified
  · exact Q1301.verified
  · exact Q1321.verified
  · exact Q1361.verified
  · exact Q1369.verified
  · exact Q1373.verified
  · exact Q1381.verified
  · exact Q1409.verified
  · exact Q1429.verified
  · exact Q1433.verified
  · exact Q1453.verified
private theorem band1481 (q : ℕ) (h : IsPrimePow q) (hm : q%4=1)
    (hl : 1481≤q) (hh : q<1709) : AtOrder q := by
  have check : ∀ i : Fin 228, let q := i.val+1481; IsPrimePow q → q%4=1 → ((((q = 1481 ∨ q = 1489) ∨ (q = 1493 ∨ q = 1549)) ∨ ((q = 1553 ∨ q = 1597) ∨ (q = 1601 ∨ q = 1609))) ∨ (((q = 1613 ∨ q = 1621) ∨ (q = 1637 ∨ q = 1657)) ∨ ((q = 1669 ∨ q = 1681) ∨ (q = 1693 ∨ q = 1697)))) := by decide +kernel
  have e : (q-1481)+1481=q := Nat.sub_add_cancel hl
  have r := check ⟨q-1481,by omega⟩
  dsimp only at r
  rw [e] at r
  rcases r h hm with ((((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl)))|(((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl))))
  · exact Q1481.verified
  · exact Q1489.verified
  · exact Q1493.verified
  · exact Q1549.verified
  · exact Q1553.verified
  · exact Q1597.verified
  · exact Q1601.verified
  · exact Q1609.verified
  · exact Q1613.verified
  · exact Q1621.verified
  · exact Q1637.verified
  · exact Q1657.verified
  · exact Q1669.verified
  · exact Q1681.verified
  · exact Q1693.verified
  · exact Q1697.verified
private theorem band1709 (q : ℕ) (h : IsPrimePow q) (hm : q%4=1)
    (hl : 1709≤q) (hh : q<1949) : AtOrder q := by
  have check : ∀ i : Fin 240, let q := i.val+1709; IsPrimePow q → q%4=1 → ((((q = 1709 ∨ q = 1721) ∨ (q = 1733 ∨ q = 1741)) ∨ ((q = 1753 ∨ q = 1777) ∨ (q = 1789 ∨ q = 1801))) ∨ (((q = 1849 ∨ q = 1861) ∨ (q = 1873 ∨ q = 1877)) ∨ ((q = 1889 ∨ q = 1901) ∨ (q = 1913 ∨ q = 1933)))) := by decide +kernel
  have e : (q-1709)+1709=q := Nat.sub_add_cancel hl
  have r := check ⟨q-1709,by omega⟩
  dsimp only at r
  rw [e] at r
  rcases r h hm with ((((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl)))|(((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl))))
  · exact Q1709.verified
  · exact Q1721.verified
  · exact Q1733.verified
  · exact Q1741.verified
  · exact Q1753.verified
  · exact Q1777.verified
  · exact Q1789.verified
  · exact Q1801.verified
  · exact Q1849.verified
  · exact Q1861.verified
  · exact Q1873.verified
  · exact Q1877.verified
  · exact Q1889.verified
  · exact Q1901.verified
  · exact Q1913.verified
  · exact Q1933.verified
private theorem band1949 (q : ℕ) (h : IsPrimePow q) (hm : q%4=1)
    (hl : 1949≤q) (hh : q<2159) : AtOrder q := by
  have check : ∀ i : Fin 210, let q := i.val+1949; IsPrimePow q → q%4=1 → (((q = 1949 ∨ (q = 1973 ∨ q = 1993)) ∨ ((q = 1997 ∨ q = 2017) ∨ (q = 2029 ∨ q = 2053))) ∨ (((q = 2069 ∨ q = 2081) ∨ (q = 2089 ∨ q = 2113)) ∨ ((q = 2129 ∨ q = 2137) ∨ (q = 2141 ∨ q = 2153)))) := by decide +kernel
  have e : (q-1949)+1949=q := Nat.sub_add_cancel hl
  have r := check ⟨q-1949,by omega⟩
  dsimp only at r
  rw [e] at r
  rcases r h hm with (((rfl|(rfl|rfl))|((rfl|rfl)|(rfl|rfl)))|(((rfl|rfl)|(rfl|rfl))|((rfl|rfl)|(rfl|rfl))))
  · exact Q1949.verified
  · exact Q1973.verified
  · exact Q1993.verified
  · exact Q1997.verified
  · exact Q2017.verified
  · exact Q2029.verified
  · exact Q2053.verified
  · exact Q2069.verified
  · exact Q2081.verified
  · exact Q2089.verified
  · exact Q2113.verified
  · exact Q2129.verified
  · exact Q2137.verified
  · exact Q2141.verified
  · exact Q2153.verified
theorem allOrders (q : ℕ) (hp : IsPrimePow q) (hm : q%4=1) (hn : 1<q) : AtOrder q := by
  by_cases hlarge : 2160≤q+1
  · intro F E _ _ _ _ _ _ w z hc he hw hz f
    subst q
    apply good_of_uniform _ hn
    cases f with
    | four => simpa only [delta,magnitude,←mul_assoc] using class4_large hm hw he hz hlarge
    | five => simpa only [delta,magnitude,←mul_assoc] using bordered_large hm hw hlarge true
    | six => simpa only [delta,magnitude,←mul_assoc] using bordered_large hm hw hlarge false
  by_cases h109 : q < 109
  · exact band2 q hp hm (by omega) h109
  by_cases h269 : q < 269
  · exact band109 q hp hm (by omega) h269
  by_cases h421 : q < 421
  · exact band269 q hp hm (by omega) h421
  by_cases h625 : q < 625
  · exact band421 q hp hm (by omega) h625
  by_cases h821 : q < 821
  · exact band625 q hp hm (by omega) h821
  by_cases h1021 : q < 1021
  · exact band821 q hp hm (by omega) h1021
  by_cases h1229 : q < 1229
  · exact band1021 q hp hm (by omega) h1229
  by_cases h1481 : q < 1481
  · exact band1229 q hp hm (by omega) h1481
  by_cases h1709 : q < 1709
  · exact band1481 q hp hm (by omega) h1709
  by_cases h1949 : q < 1949
  · exact band1709 q hp hm (by omega) h1949
  by_cases h2159 : q < 2159
  · exact band1949 q hp hm (by omega) h2159
  omega

/-- The best uniform multipliers on both domains of MSX Problem 7.1. -/
theorem sharpLowerBounds : SharpLowerBounds := by
  intro f
  have lower (lo : ℕ) (r : ℚ) (hr : r ∈ values lo f) :
      fullMinimum f ≤ r ∧ (30 ≤ lo → restrictedMinimum f ≤ r) := by
    obtain ⟨F,E,_,_,_,_,_,_,w,z,hq,hlo,he,hw,hz,rfl⟩ := hr
    have H := allOrders _ (FiniteField.isPrimePow_card F) hq Fintype.one_lt_card
      F E w z rfl he hw hz f
    exact ⟨H.1,fun h => H.2 (h.trans hlo)⟩
  constructor
  · refine ⟨?_,fun r hr => (lower 0 r hr).1⟩
    cases f with
    | four => exact Q13.attained
    | five => exact Q5.attained
    | six => exact Q9.attained
  · refine ⟨?_,fun r hr => (lower 30 r hr).2 le_rfl⟩
    cases f with
    | four => exact Q29.attained
    | five => exact Q37.attained
    | six => exact Q49.attained

/-- The supplementary reading excluding the ordinary Class (5) case q=5. -/
theorem nonordinaryFive : IsLeast (values 10 .five) (441/544 : ℚ) := by
  refine ⟨Q17.nonordinaryAttained,?_⟩
  intro r hr
  obtain ⟨F,E,_,_,_,_,_,_,w,z,hq,hlo,he,hw,hz,rfl⟩ := hr
  let q := Fintype.card F
  by_cases hlarge : 30≤q+1
  · have H := allOrders _ (FiniteField.isPrimePow_card F) hq Fintype.one_lt_card F E w z rfl he hw hz .five
    exact le_trans (by norm_num [restrictedMinimum]) (H.2 hlarge)
  have hpow := FiniteField.isPrimePow_card F
  have check : ∀ i : Fin 29, 9 ≤ i.val → i.val%4=1 → IsPrimePow i.val →
      i.val=9 ∨ i.val=13 ∨ i.val=17 ∨ i.val=25 := by decide +kernel
  have d := check ⟨q,by omega⟩ (by change 9 ≤ q; change 10 ≤ q+1 at hlo; omega) hq hpow
  change (441/544:ℚ) ≤ (|(Source.bordered q w true).det|:ℤ)/(delta q:ℚ)
  rcases d with h|h|h|h
  · change q=9 at h; rw [h]; exact Q9.fiveAbove F w h (h ▸ hw)
  · change q=13 at h; rw [h]; exact Q13.fiveAbove F w h (h ▸ hw)
  · change q=17 at h; rw [h]; exact Q17.fiveAbove F w h (h ▸ hw)
  · change q=25 at h; rw [h]; exact Q25.fiveAbove F w h (h ▸ hw)

#print axioms nonordinaryFive
#print axioms sharpLowerBounds
end NearHadamard.Optimal
