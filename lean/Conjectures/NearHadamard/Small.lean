module
public import Conjectures.NearHadamard.Torus
import Mathlib.Tactic

@[expose] public section
open Matrix
namespace NearHadamard.Small

def threshold (q : ℕ) : ℤ := 4*(2*(q:ℤ))*((q:ℤ)-1)^((q-1)/2)

/-- Three inequalities at one cardinality, including every field model and primitive choice. -/
def AtOrder (q : ℕ) : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [DecidableEq F] [Field E] [Fintype E] [DecidableEq E]
    (w : F) (z : E), Fintype.card F=q → Fintype.card E=q*q →
    IsPrimitiveRoot w (q-1) → IsPrimitiveRoot z (q*q-1) →
    threshold q ≤ 5*|(Source.class4 q z).det| ∧
    threshold q ≤ 5*|(Source.bordered q w true).det| ∧ threshold q ≤ 5*|(Source.bordered q w false).det|

instance modelFintype {F : Type*} [Field F] [Fintype F] (d : F) : Fintype (Torus.Model d) :=
  Fintype.ofEquiv (F × F) (QuadraticAlgebra.equivProd d 0).symm

theorem card_model {F : Type*} [Field F] [Fintype F] (d : F) :
    Fintype.card (Torus.Model d) = Fintype.card F * Fintype.card F := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd d 0), Fintype.card_prod]

theorem fromModel {q : ℕ} {K : Type} [Field K] [Fintype K] [DecidableEq K] (u : K)
    [Fact (∀ r : K, r^2 ≠ u+0*r)] (a : Torus.Model u)
    (hK : Fintype.card K=q) (hq : q%4=1)
    (hu : IsPrimitiveRoot u (q-1)) (ha : IsPrimitiveRoot a (q*q-1))
    (h4 : threshold q ≤ 5*|(Source.class4 q a).det|)
    (h4i : threshold q ≤ 5*|(Source.class4 q a⁻¹).det|)
    (h5 : threshold q ≤ 5*|(Source.bordered q u true).det|)
    (h6 : threshold q ≤ 5*|(Source.bordered q u false).det|) : AtOrder q := by
  subst q
  intro F E _ _ _ _ _ _ w z hF hE hw hz
  let f := FiniteField.ringEquivOfCardEq hF
  let e := FiniteField.ringEquivOfCardEq (hE.trans (card_model u).symm)
  have hwu := hw.map_of_injective f.injective
  have hze := hz.map_of_injective e.injective
  rw [←Torus.transport e, ←Border.transport f _ w true, ←Border.transport f _ w false,
    Border.primitive_independent hq hwu hu true, Border.primitive_independent hq hwu hu false]
  refine ⟨?_,h5,h6⟩
  rcases Torus.primitive_choices hq (Border.char_generator hq hu) hze ha with H|H
  · rwa [H]
  · rwa [H]

private theorem prime_mem {p : ℕ} (hp : p.Prime) (l : List ℕ)
    (hs : ∀ a ∈ l, Nat.Prime a) (hd : p ∣ l.prod) : p ∈ l := by
  induction l with
  | nil => simp [hp.not_dvd_one] at hd
  | cons a l ih =>
    rw [List.prod_cons, hp.dvd_mul] at hd
    rcases hd with h|h
    · exact List.mem_cons.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (hs a (by simp))).mp h))
    · exact List.mem_cons.mpr (Or.inr (ih (fun t ht => hs t (by simp [ht])) h))

theorem fastPower {F : Type*} [Monoid F] (x : F) (n : ℕ) : x^n = npowBinRec n x := by
  induction n with
  | zero => simp [npowBinRec_zero]
  | succ n ih => rw [pow_succ,npowBinRec_succ,ih]

theorem primitiveCheck {F : Type*} [Field F] {x : F} {n : ℕ} (factors : List ℕ)
    (hn : n ≠ 0) (hf : factors.prod=n) (hs : ∀ a ∈ factors, Nat.Prime a)
    (h : npowBinRec n x=1) (hh : ∀ p ∈ factors, npowBinRec (n/p) x ≠ 1) : IsPrimitiveRoot x n := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_of_pow_and_pow_div_prime (Nat.pos_of_ne_zero hn) ((fastPower ..).trans h)
  intro p hp hd
  rw [fastPower]
  exact hh p (prime_mem hp factors hs (hf ▸ hd))

end NearHadamard.Small
