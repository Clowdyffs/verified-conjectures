module
public import Conjectures.NearHadamard.MomentCheck
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q73
local instance : Fact (Nat.Prime 73) := ⟨by decide⟩
abbrev F0 := ZMod 73
def w : F0 := 5
local instance : Fact (∀ r : F0, r^2 ≠ w+0*r) := ⟨by decide⟩
def z : Torus.Model w := ⟨4,1⟩
def certificateTraces := traceList 73 w z

theorem verified : AtOrder 73 := by
  apply order_of_moments w z
  · simp [F0]
  · decide
  · decide
  · apply primitiveCheck [2, 2, 2, 3, 3] <;> decide +kernel
  · apply primitiveCheck [2, 2, 2, 2, 3, 3, 37] <;> decide +kernel
  · decide +kernel
end Q73
end NearHadamard.Small
