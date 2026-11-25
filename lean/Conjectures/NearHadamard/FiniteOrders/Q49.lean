module
public import Conjectures.NearHadamard.MomentCheck
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q49
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
abbrev F0 := ZMod 7
def d0 : F0 := 3
local instance : Fact (∀ r : F0, r^2 ≠ d0+0*r) := ⟨by decide⟩
abbrev F1 := Torus.Model d0
def w : F1 := ⟨1,1⟩
local instance : Fact (∀ r : F1, r^2 ≠ w+0*r) := ⟨by decide⟩
def z : Torus.Model w := ⟨⟨3,0⟩,⟨1,0⟩⟩
def certificateTraces := traceList 49 w z

theorem verified : AtOrder 49 := by
  apply order_of_moments w z
  · simp [F0,F1,card_model]
  · decide
  · decide
  · apply primitiveCheck [2, 2, 2, 2, 3] <;> decide +kernel
  · apply primitiveCheck [2, 2, 2, 2, 2, 3, 5, 5] <;> decide +kernel
  · decide +kernel
end Q49
end NearHadamard.Small
