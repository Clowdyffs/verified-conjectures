module
public import Conjectures.NearHadamard.MomentCheck
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q37
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
abbrev F0 := ZMod 37
def w : F0 := 2
local instance : Fact (∀ r : F0, r^2 ≠ w+0*r) := ⟨by decide⟩
def z : Torus.Model w := ⟨2,1⟩
def certificateTraces := traceList 37 w z

theorem verified : AtOrder 37 := by
  apply order_of_moments w z
  · simp [F0]
  · decide
  · decide
  · apply primitiveCheck [2, 2, 3, 3] <;> decide +kernel
  · apply primitiveCheck [2, 2, 2, 3, 3, 19] <;> decide +kernel
  · decide +kernel
end Q37
end NearHadamard.Small
