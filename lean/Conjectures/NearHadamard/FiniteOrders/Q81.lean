module
public import Conjectures.NearHadamard.MomentCheck
import Mathlib.Tactic
@[expose] public section
namespace NearHadamard.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q81
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
abbrev F0 := ZMod 3
def d0 : F0 := 2
local instance : Fact (∀ r : F0, r^2 ≠ d0+0*r) := ⟨by decide⟩
abbrev F1 := Torus.Model d0
def d1 : F1 := ⟨1,1⟩
local instance : Fact (∀ r : F1, r^2 ≠ d1+0*r) := ⟨by decide⟩
abbrev F2 := Torus.Model d1
def w : F2 := ⟨⟨0,1⟩,⟨1,0⟩⟩
local instance : Fact (∀ r : F2, r^2 ≠ w+0*r) := ⟨by decide⟩
def z : Torus.Model w := ⟨⟨⟨0,1⟩,⟨0,0⟩⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩
def certificateTraces := traceList 81 w z

theorem verified : AtOrder 81 := by
  apply order_of_moments w z
  · simp [F0,F1,F2,card_model]
  · decide
  · decide
  · apply primitiveCheck [2, 2, 2, 2, 5] <;> decide +kernel
  · apply primitiveCheck [2, 2, 2, 2, 2, 5, 41] <;> decide +kernel
  · decide +kernel
end Q81
end NearHadamard.Small
