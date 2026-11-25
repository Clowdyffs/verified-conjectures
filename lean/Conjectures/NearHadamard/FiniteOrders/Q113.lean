module
public import Conjectures.NearHadamard.MomentCheck
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q113
local instance : Fact (Nat.Prime 113) := ⟨by decide⟩
abbrev F0 := ZMod 113
def w : F0 := 3
local instance : Fact (∀ r : F0, r^2 ≠ w+0*r) := ⟨by decide⟩
def z : Torus.Model w := ⟨3,1⟩
def certificateTraces := traceList 113 w z

theorem verified : AtOrder 113 := by
  apply order_of_moments w z
  · simp [F0]
  · decide
  · decide
  · apply primitiveCheck [2, 2, 2, 2, 7] <;> decide +kernel
  · apply primitiveCheck [2, 2, 2, 2, 2, 3, 7, 19] <;> decide +kernel
  · decide +kernel
end Q113
end NearHadamard.Small
