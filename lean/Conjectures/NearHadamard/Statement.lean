module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

namespace NearHadamard.Source

/-- $C_0^{(2,q)}$ contains exactly the nonzero squares. -/
def sqMem {F : Type*} [Field F] (t : F) : Prop := t ≠ 0 ∧ IsSquare t

def sign (p : Prop) [Decidable p] : ℤ := if p then 1 else -1

/-- In the cyclic group of order m the type-one matrix entry at (i,j) uses j-i. -/
def shift {m : ℕ} (i j : Fin m) : ℕ := (j.val + m - i.val) % m

/-- MSX (2.2), formed from the two trace tests in Theorem 3.4. A nonzero element
of the subfield is a square there iff its (q-1)/2 power is one. -/
def class4 {E : Type*} [Field E] [DecidableEq E] (q : ℕ) (w : E) :
    Matrix (Fin ((q+1)/2) ⊕ Fin ((q+1)/2)) (Fin ((q+1)/2) ⊕ Fin ((q+1)/2)) ℤ :=
  let b := w ^ (2*(q-1))
  let c := w ^ ((q+1)/2)
  let f (u : E) := sign ((u + u^q) ^ ((q-1)/2) = 1)
  let A : Matrix (Fin ((q+1)/2)) (Fin ((q+1)/2)) ℤ := fun i j => f (b ^ shift i j)
  let B : Matrix (Fin ((q+1)/2)) (Fin ((q+1)/2)) ℤ := fun i j => f (b ^ shift i j * c)
  Matrix.fromBlocks A B B.transpose (-A.transpose)

/-- Test membership of the shifted square or nonsquare class in Theorem 4.1. -/
def borderMember {F : Type*} [Field F] [DecidableEq F] (q : ℕ) (five : Bool) (t : F) : ℤ :=
  sign ((t-1)^((q-1)/2) = if five then (-1:F) else 1)

def borderA {F : Type*} [Field F] [DecidableEq F] (q : ℕ) (w : F) (five : Bool)
    (i j : Fin ((q-1)/2)) : ℤ := borderMember q five ((w^2)^shift i j)

def borderB {F : Type*} [Field F] [DecidableEq F] (q : ℕ) (w : F) (five : Bool)
    (i j : Fin ((q-1)/2)) : ℤ := borderMember q five (((w^2)^shift i j)/w)

/-- The bordered matrices (2.3) and (2.4), indexed in the printed order.
Class 5 uses the nonsquare translate and Class 6 uses the square translate. -/
def bordered {F : Type*} [Field F] [DecidableEq F] (q : ℕ) (w : F) (five : Bool) :
    Matrix (Option (Fin ((q-1)/2)) ⊕ Option (Fin ((q-1)/2)))
           (Option (Fin ((q-1)/2)) ⊕ Option (Fin ((q-1)/2))) ℤ :=
  let c : ℤ := if five then 1 else -1
  let A := borderA q w five
  let B := borderB q w five
  Matrix.fromBlocks
    (fun x y => match x,y with | some i, some j => A i j | _,_ => 1)
    (fun x y => match x,y with | none,_ => c | some _,none => 1 | some i,some j => B i j)
    (fun x y => match x,y with | none,_ => 1 | some _,none => c | some i,some j => c*B j i)
    (fun x y => match x,y with | some i,some j => -c*A j i | _,_ => -c)

/-- Momihara–Suda–Xiang, accepted manuscript, Problem 7.1 (2022), p. 20:
“Give sharp lower bounds on the determinants of near-Hadamard matrices
in Classes (4), (5) and (6) of Theorem 1.6. In particular, prove or disprove that for each
i = 4, 5, 6, det Mₙ⁽ⁱ⁾/Δₙ ≥ 0.8 for every n = q + 1 ≥ 30 with q ≡ 1 (mod 4) a prime power.”

Egan–Kotsireas–London–Ó Catháin, arXiv:2610.27175v2, §5.6, Problem 15:
“Is |det Mₙ| ≥ 0.8 Wₙ for every such n ≥ 30 in each family?”
Here “such” refers to the three Theorem 1.6 constructions above.
The proposition answers the particular question, with no claim of sharpness.

The published four-fifths question, with absolute determinants over the
integers. Quantification over fields of size q covers exactly the prime powers.
Generators of the multiplicative groups have orders q-1 and q²-1. -/
def Problem15 : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [DecidableEq F] [Field E] [Fintype E] [DecidableEq E],
    let q := Fintype.card F
    ∀ (w : F) (z : E), q % 4 = 1 → 30 ≤ q+1 → Fintype.card E = q*q →
      IsPrimitiveRoot w (q-1) → IsPrimitiveRoot z (q*q-1) →
      let target := 4 * (2*(q:ℤ)) * ((q:ℤ)-1)^((q-1)/2)
      target ≤ 5*|(class4 q z).det| ∧
      target ≤ 5*|(bordered q w true).det| ∧
      target ≤ 5*|(bordered q w false).det|

end NearHadamard.Source
