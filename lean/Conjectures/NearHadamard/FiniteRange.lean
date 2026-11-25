module
public import Conjectures.NearHadamard.FiniteOrders.Q29
public import Conjectures.NearHadamard.FiniteOrders.Q37
public import Conjectures.NearHadamard.FiniteOrders.Q41
public import Conjectures.NearHadamard.FiniteOrders.Q49
public import Conjectures.NearHadamard.FiniteOrders.Q53
public import Conjectures.NearHadamard.FiniteOrders.Q61
public import Conjectures.NearHadamard.FiniteOrders.Q73
public import Conjectures.NearHadamard.FiniteOrders.Q81
public import Conjectures.NearHadamard.FiniteOrders.Q89
public import Conjectures.NearHadamard.FiniteOrders.Q97
public import Conjectures.NearHadamard.FiniteOrders.Q101
public import Conjectures.NearHadamard.FiniteOrders.Q109
public import Conjectures.NearHadamard.FiniteOrders.Q113
public import Conjectures.NearHadamard.FiniteOrders.Q121
import Mathlib.Tactic

@[expose] public section
namespace NearHadamard.Small

/-- Exhaustion of the possible finite field cardinalities below 125. -/
theorem enumerated (q : ℕ) (hq : q%4=1) (hn : 30≤q+1) (hs : q+1<126)
    (hp : IsPrimePow q) : AtOrder q := by
  have check : ∀ a : Fin 125, a.val%4=1 → 29≤a.val → IsPrimePow a.val →
      a.val ∈ ([29,37,41,49,53,61,73,81,89,97,101,109,113,121] : List ℕ) := by decide +kernel
  have hm := check ⟨q,by omega⟩ hq (show 29 ≤ q by omega) hp
  simp only [Fin.val_mk,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | exact Q29.verified
    | exact Q37.verified
    | exact Q41.verified
    | exact Q49.verified
    | exact Q53.verified
    | exact Q61.verified
    | exact Q73.verified
    | exact Q81.verified
    | exact Q89.verified
    | exact Q97.verified
    | exact Q101.verified
    | exact Q109.verified
    | exact Q113.verified
    | exact Q121.verified

end NearHadamard.Small
