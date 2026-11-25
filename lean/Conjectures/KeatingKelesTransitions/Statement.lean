module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.List.Induction

@[expose] public section
namespace HessenbergTransitions
abbrev V := ℝ × ℝ

/-- Keating–Keleş, Problem 2.4, after division by the upper endpoint t. -/
def Admissible {n : ℕ} (r : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, (i.val ≤ j.val → 0 ≤ A i j ∧ A i j ≤ 1) ∧
    (i.val = j.val + 1 → A i j = r) ∧ (j.val + 1 < i.val → A i j = 0)

noncomputable def sorted (x : V) : V := (max x.1 x.2, min x.1 x.2)
noncomputable def grow (h : ℝ) (x : V) : V := sorted (x.1, x.2+h*x.1)

/-- Evaluate from both ends. The input pair is in decreasing order. -/
noncomputable def middleValue (h : ℝ) : ℕ → V → ℝ
  | 0, x => x.1^2 + x.2^2
  | 1, x => max (x.1^2 + x.2^2 + h*x.1*x.2) (2*x.1*x.2 + h*x.1^2)
  | m+2, x => middleValue h m (grow h x)

/-- Keating–Keleş v2, §6 Q1: “Which matrices maximize the absolute determinant as
s/t goes to 1 from n², in other words, what are the transition forms?”
This part asserts sharpness over the full real box; Classify below gives equality. -/
def SharpMaximum : Prop :=
  ∀ (r : ℝ), 0 < r → ∀ m : ℕ,
    IsGreatest {z : ℝ | ∃ A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ,
      Admissible r A ∧ z = |A.det|} (r^m * middleValue r⁻¹ m (1,0))

def leftS (h : ℝ) (x : V) : V := (x.1+h*x.2,x.2)
def rightS (h : ℝ) (x : V) : V := (x.1,x.2+h*x.1)
def dot (x y : V) : ℝ := x.1*y.1+x.2*y.2
def move (h : ℝ) (b : Bool) (x : V) : V := if b then leftS h x else rightS h x
/-- An update is greedy when it raises a weakly smaller coordinate. -/
def Greedy (b : Bool) (x : V) := if b then x.1 ≤ x.2 else x.2 ≤ x.1

/-- Peel one update at each end. The right endpoint uses the transposed shear.
Only a length-zero or length-one central test involves a scalar comparison. -/
noncomputable def Form (h : ℝ) (w : List Bool) : V → V → Prop :=
  w.bidirectionalRec (fun x y => dot x y = middleValue h 0 (sorted x))
    (fun a x y => dot (move h a x) y = middleValue h 1 (sorted x))
    (fun a _ b inner x y =>
      Greedy a x ∧ Greedy (!b) y ∧ inner (move h a x) (move h (!b) y))

def word (c : ℕ → Bool) (m : ℕ) := (List.range m).map (fun i => c (i+1))
def axis (b : Bool) : V := if b then (0,1) else (1,0)

def colored (c : ℕ → Bool) : ℕ → ℕ → ℝ := fun i j => if c i = c (j+1) then 0 else 1

/-- For the two small orders this includes all nonvertex matrices at a tie.
For larger orders, generate the colors from both ends using Form. -/
def MaximizingForm (r : ℝ) : (m : ℕ) → Matrix (Fin (m+1)) (Fin (m+1)) ℝ → Prop
  | 0, A => A 0 0 = 1
  | 1, A => (r ≤ 1 ∧ A 0 0 = 1 ∧ A 1 1 = 1 ∧ A 0 1 = 0) ∨
      (1 ≤ r ∧ A 0 1 = 1 ∧ A 0 0 * A 1 1 = 0)
  | k+2, A => ∃ c : ℕ → Bool, c 0 = true ∧
      Form r⁻¹ (word c (k+2)) (1,0) (axis (c (k+3))) ∧
      ∀ i j, i.val ≤ j.val → A i j = colored c i.val j.val

/-- Complete equality classification over the closed real box, including ties. -/
def Classify : Prop := ∀ (r : ℝ), 0 < r → ∀ (m : ℕ) (A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ),
    Admissible r A → (|A.det| = r^m * middleValue r⁻¹ m (1,0) ↔ MaximizingForm r m A)

/-- §6 Question 8 asks whether every maximizing matrix has the same sign
for all its nonzero terms of the determinant. Every allowed entry is nonnegative. -/
def NoCancellation : Prop := ∀ (r : ℝ), 0 < r → ∀ (m : ℕ) (A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ),
    Admissible r A → |A.det| = r^m*middleValue r⁻¹ m (1,0) →
    ∀ σ τ : Equiv.Perm (Fin (m+1)),
      (∀ j, A (σ j) j ≠ 0) → (∀ j, A (τ j) j ≠ 0) → σ.sign = τ.sign

noncomputable def upperOnes {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℕ := by
  classical exact ∑ i, ∑ j, if i.val ≤ j.val ∧ A i j = 1 then 1 else 0

/-- Fixed-ratio version of §6 Question 7. Two maximizers of the
same order at the same ratio would have equal counts of upper ones. -/
def EqualCounts : Prop := ∀ (r : ℝ), 0 < r → ∀ (m : ℕ) (A B : Matrix (Fin (m+1)) (Fin (m+1)) ℝ),
    Admissible r A → Admissible r B →
    |A.det| = r^m*middleValue r⁻¹ m (1,0) → |B.det| = r^m*middleValue r⁻¹ m (1,0) →
    upperOnes A = upperOnes B

/-- Problem 2.4 before normalization, with upper endpoint t and subdiagonal s. -/
def SourceBox {n : ℕ} (s t : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, (i.val ≤ j.val → 0 ≤ A i j ∧ A i j ≤ t) ∧
    (i.val = j.val+1 → A i j = s) ∧ (j.val+1 < i.val → A i j = 0)

def SourceClassification : Prop := ∀ (s t : ℝ), 0 < s → 0 < t → ∀ m : ℕ,
  let r := s / t
  let D := t^(m+1)*r^m*middleValue r⁻¹ m (1,0)
  IsGreatest {z : ℝ | ∃ A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ, SourceBox s t A ∧ z = |A.det|} D ∧
    ∀ A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ, SourceBox s t A →
      (|A.det| = D ↔ MaximizingForm r m (t⁻¹ • A))

end HessenbergTransitions
