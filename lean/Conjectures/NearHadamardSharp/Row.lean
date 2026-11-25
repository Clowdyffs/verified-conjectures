module
public import Conjectures.NearHadamardSharp.Packing
public import Conjectures.NearHadamard.MomentCheck
import Mathlib.Tactic
@[expose] public section
open Finset NearHadamard.Small
namespace NearHadamard.Optimal

def torusPack {F : Type*} [Field F] [DecidableEq F] {u : F} (q : ℕ) (z : Torus.Model u) (b : ℤ) : ℤ :=
  orbitPack b (npowBinRec (2*(q-1)) z) (fun y => -charValue q (Torus.tr y))
    (Torus.v q) (npowBinRec (Torus.v q) z)

theorem torusPack_eq {F : Type*} [Field F] [DecidableEq F] {u : F} (q : ℕ) (z : Torus.Model u)
    (b : ℤ) : torusPack q z b = pack b (torusRow q z) := by
  simp only [torusPack,orbitPack_eq,pack,torusRow,←fastPower,Int.cast_id]

theorem torusCube_eq {F : Type*} [Field F] [DecidableEq F] {u : F} (q : ℕ) (z : Torus.Model u)
    [NeZero (Torus.v q)] :
    cyclicCube (torusRow q z) = unpackCube (Torus.v q) (torusPack q z (radix (Torus.v q))) := by
  rw [torusPack_eq,unpackCube_eq]
  intro i
  unfold torusRow charValue Source.sign
  dsimp only; split_ifs <;> norm_num

def borderPack {F : Type*} [Field F] [DecidableEq F] (q : ℕ) (w : F) (five : Bool) (b : ℤ) : ℤ :=
  orbitPack b (w^2) (fun y => Border.c five*charValue q (y-1)) ((q-1)/2) 1

theorem borderPack_eq {F : Type*} [Field F] [DecidableEq F] (q : ℕ) (w : F) (five : Bool)
    (b : ℤ) : borderPack q w five b = pack b (borderRow q w five) := by
  simp only [borderPack,orbitPack_eq,pack,borderRow,←fastPower,Int.cast_id,one_mul]

theorem borderTrace_eq {F : Type*} [Field F] [DecidableEq F] (q : ℕ) (w : F) (five : Bool)
    [NeZero ((q-1)/2)] :
    borderCube q w five = unpackCube ((q-1)/2) (borderPack q w five (radix ((q-1)/2))) +
      3*((q-1)/2:ℕ)*borderPack q w five 1 := by
  rw [borderPack_eq,borderPack_eq,unpackCube_eq]
  · simp [borderCube,pack]
  · intro i
    unfold borderRow charValue Source.sign Border.c
    cases five <;> split_ifs <;> norm_num

end NearHadamard.Optimal
