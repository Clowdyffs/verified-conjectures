module
public import Conjectures.NearHadamard.MomentCheck
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q97
local instance : Fact (Nat.Prime 97) := ⟨by decide⟩
abbrev F0 := ZMod 97
def w : F0 := 5
local instance : Fact (∀ r : F0, r^2 ≠ w+0*r) := ⟨by decide⟩
def z : Torus.Model w := ⟨8,1⟩
def certificateTraces := traceList 97 w z

theorem verified : AtOrder 97 := by
  apply order_of_moments w z
  · simp [F0]
  · decide
  · decide
  · apply primitiveCheck [2, 2, 2, 2, 2, 3] <;> decide +kernel
  · apply primitiveCheck [2, 2, 2, 2, 2, 2, 3, 7, 7] <;> decide +kernel
  · decide +kernel
end Q97
end NearHadamard.Small
