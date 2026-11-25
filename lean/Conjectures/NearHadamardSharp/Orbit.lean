module
public import Conjectures.NearHadamardSharp.Checks
import Mathlib.Tactic
@[expose] public section
open NearHadamard.Small
namespace NearHadamard.Optimal

/-- Each triple contains the current orbit point, the quadratic character,
and a square root after removing the nonsquare multiplier when needed. -/
abbrev Sample (K F : Type*) := K × ℤ × F

def squareCheck {F : Type*} [Field F] [DecidableEq F] (w t : F) (s : ℤ) (u : F) : Bool :=
  if t=0 then decide (s=0) else
    if s=1 then decide (t=u*u) else decide (s= -1 ∧ t=w*(u*u))

theorem squareCheck_sound {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {w t u : F} {s : ℤ} (hw : quadraticChar F w = -1) (hc : squareCheck w t s u = true) :
    quadraticChar F t = s := by
  unfold squareCheck at hc
  split at hc
  · rename_i ht; simpa [ht] using (of_decide_eq_true hc).symm
  split at hc
  · rename_i hs
    have e := of_decide_eq_true hc
    have hu : u≠0 := by intro h; simp_all
    rw [hs,e,←sq,quadraticChar_sq_one' hu]
  · obtain ⟨hs,he⟩ := of_decide_eq_true hc
    have hu : u≠0 := by intro h; simp_all
    rw [he,hs,map_mul,hw,←sq,quadraticChar_sq_one' hu,mul_one]

def samplesOK {K F : Type*} [Monoid K] [DecidableEq K] [Field F] [DecidableEq F]
    (w : F) (step : K) (f : K → F) : List (Sample K F) → K → Bool
  | [], _ => true
  | (y,s,u)::ys,x => decide (x=y) && squareCheck w (f y) s u && samplesOK w step f ys (y*step)

def horner {K F : Type*} (b c : ℤ) : List (Sample K F) → ℤ
  | [] => 0
  | (_,s,_)::ys => c*s+b*horner b c ys

theorem orbit_samples {K F : Type*} [Monoid K] [DecidableEq K] [Field F] [DecidableEq F] [Fintype F]
    (w : F) (step : K) (f : K → F) (b c : ℤ) (l : List (Sample K F)) (x : K)
    (hw : quadraticChar F w = -1) (h : samplesOK w step f l x=true) :
    orbitPack b step (fun y => c*quadraticChar F (f y)) l.length x = horner b c l := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨y,s,u⟩ := a
    simp only [samplesOK,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨⟨rfl,hs⟩,ht⟩ := h
    simp only [List.length_cons,orbitPack,horner, squareCheck_sound hw hs,ih _ ht]

theorem torusSamples {q : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F] {w : F}
    (z : Torus.Model w) (hc : Fintype.card F=q) (hq : q%4=1)
    (hw : IsPrimitiveRoot w (q-1)) (l : List (Sample (Torus.Model w) F))
    (hl : l.length=Torus.v q)
    (h : samplesOK w (npowBinRec (2*(q-1)) z) Torus.tr l (npowBinRec (Torus.v q) z)=true)
    (b : ℤ) : torusPack q z b = horner b (-1) l := by
  subst q
  have he := orbit_samples w _ Torus.tr b (-1) l _ (Border.char_generator hq hw) h
  rw [hl] at he
  simpa only [torusPack,charValue_eq hq,neg_one_mul] using he

theorem borderSamples {q : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F] {w : F}
    (hc : Fintype.card F=q) (hq : q%4=1) (hw : IsPrimitiveRoot w (q-1))
    (l : List (Sample F F)) (hl : l.length=(q-1)/2)
    (h : samplesOK w (w^2) (fun x => x-1) l 1=true) (five : Bool) (b : ℤ) :
    borderPack q w five b = horner b (Border.c five) l := by
  subst q
  have he := orbit_samples w _ (fun x => x-1) b (Border.c five) l 1 (Border.char_generator hq hw) h
  rw [hl] at he
  simpa only [borderPack,charValue_eq hq] using he
end NearHadamard.Optimal
