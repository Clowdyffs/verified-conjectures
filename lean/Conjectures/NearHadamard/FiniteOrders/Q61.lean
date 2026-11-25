module
public import Conjectures.NearHadamard.MomentCheck
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q61
local instance : Fact (Nat.Prime 61) := ⟨by decide⟩
abbrev F0 := ZMod 61
def w : F0 := 2
local instance : Fact (∀ r : F0, r^2 ≠ w+0*r) := ⟨by decide⟩
def z : Torus.Model w := ⟨2,1⟩
def certificateTraces := traceList 61 w z

theorem verified : AtOrder 61 := by
  apply order_of_moments w z
  · simp [F0]
  · decide
  · decide
  · apply primitiveCheck [2, 2, 3, 5] <;> decide +kernel
  · apply primitiveCheck [2, 2, 2, 3, 5, 31] <;> decide +kernel
  · decide +kernel
end Q61
end NearHadamard.Small
