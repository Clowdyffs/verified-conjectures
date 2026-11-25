module
public import Conjectures.NearHadamard.Statement
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Order.Bounds.Defs

@[expose] public section
namespace NearHadamard.Optimal

inductive Family | four | five | six deriving DecidableEq, Repr

/-- Theorem 1.2 and the paragraph after Theorem 1.6, with n=q+1. -/
def delta (q : ℕ) : ℤ := 2*(q:ℤ)*((q:ℤ)-1)^((q-1)/2)

/-- Theorem 1.6 labels its column |det M|. These are its three source matrices. -/
def magnitude {F E : Type} [Field F] [DecidableEq F] [Field E] [DecidableEq E]
    (q : ℕ) (w : F) (z : E) : Family → ℤ
  | .four => |(Source.class4 q z).det|
  | .five => |(Source.bordered q w true).det|
  | .six => |(Source.bordered q w false).det|

/-- All prime powers in Ψ₃ and all primitive elements in either field.
The optional lower endpoint is expressed in the matrix order n. -/
def values (lo : ℕ) (f : Family) : Set ℚ :=
  {r | ∃ (F E : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F)
      (_ : Field E) (_ : Fintype E) (_ : DecidableEq E) (w : F) (z : E),
      let q := Fintype.card F
      q%4=1 ∧ lo≤q+1 ∧ Fintype.card E=q*q ∧ IsPrimitiveRoot w (q-1) ∧
        IsPrimitiveRoot z (q*q-1) ∧ r=(magnitude q w z f:ℚ)/(delta q:ℚ)}

def fullMinimum : Family → ℚ
  | .four => 841/1053
  | .five => 4/5
  | .six => 13/16

def restrictedMinimum : Family → ℚ
  | .four => 16067122183125/19668469112621
  | .five => 690199704608000/846441320833557
  | .six => 13602934789834170625/16620815899787526144

/-- Momihara, Suda and Xiang (2022), Problem 7.1, accepted manuscript p. 20:
“Give sharp lower bounds on the determinants of near-Hadamard matrices
in Classes (4), (5) and (6) of Theorem 1.6. In particular, prove or disprove that for each
i = 4, 5, 6, det Mₙ⁽ⁱ⁾/Δₙ ≥ 0.8 for every n = q + 1 ≥ 30 with q ≡ 1 (mod 4) a prime power.”
We give the greatest uniform normalized lower bounds on the full domain of
Theorem 1.6 and on the explicit subdomain. An attained minimum proves sharpness
also among real constants, because every normalized determinant is rational. -/
def SharpLowerBounds : Prop :=
  ∀ f, IsLeast (values 0 f) (fullMinimum f) ∧
       IsLeast (values 30 f) (restrictedMinimum f)

end NearHadamard.Optimal
