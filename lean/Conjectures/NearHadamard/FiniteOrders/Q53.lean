module
public import Conjectures.NearHadamard.MomentCheck
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q53
local instance : Fact (Nat.Prime 53) := ⟨by decide⟩
abbrev F0 := ZMod 53
def w : F0 := 2
local instance : Fact (∀ r : F0, r^2 ≠ w+0*r) := ⟨by decide⟩
def z : Torus.Model w := ⟨2,1⟩
def certificateTraces := traceList 53 w z

theorem verified : AtOrder 53 := by
  apply order_of_moments w z
  · simp [F0]
  · decide
  · decide
  · apply primitiveCheck [2, 2, 13] <;> decide +kernel
  · apply primitiveCheck [2, 2, 2, 3, 3, 3, 13] <;> decide +kernel
  · decide +kernel
end Q53
end NearHadamard.Small
