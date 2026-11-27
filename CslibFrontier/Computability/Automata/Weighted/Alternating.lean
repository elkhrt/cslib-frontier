module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Set.Finite.Basic
public import CslibFrontier.Computability.Automata.Weighted.Rep
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Finite.List
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Weighted Alternating Finite Automata, Normal Forms, and Polynomial Automata

This module develops weighted alternating finite automata (WAFA) and weighted finite
automata (WFA) over arbitrary commutative semirings, their nice, purely polynomial, and
equalized normal forms, locally finite commutative semirings, and polynomial automata (PA)
together with the reversal correspondence between WAFA and PA.

## Main definitions

* `PaperLib.WeightedSeries`, `PaperLib.hadamard`, `PaperLib.charFun`,
  `PaperLib.wordHomPullback`, `PaperLib.wordHomPushforward`, `PaperLib.reverseSeries`:
  formal power series on words and standard series operations.
* `PaperLib.WAFA`, `PaperLib.WAFA.stateBehavior`, `PaperLib.WAFA.behavior`,
  `PaperLib.IsWAFARecognizable`: weighted alternating finite automata and recognizability.
* `PaperLib.WAFA.IsWFA`, `PaperLib.WFA`, `PaperLib.IsWFARecognizable`: linear-representation
  weighted finite automata and their equivalence with degree-1 WAFA.
* `PaperLib.WAFA.IsNice`, `PaperLib.WAFA.IsPurelyPolynomial`, `PaperLib.WAFA.IsEqualized`:
  normal forms for WAFA.
* `PaperLib.IsLocallyFiniteSemiring`: locally finite commutative semirings.
* `PaperLib.PolynomialAutomaton`, `PaperLib.IsPARecognizable`: polynomial automata over
  commutative semirings.

## Main results

* `PaperLib.WAFA.exists_nice_purelyPolynomial_equiv`: every WAFA has an equivalent nice,
  purely polynomial WAFA.
* `PaperLib.WAFA.exists_nice_equalized_equiv`: every WAFA has an equivalent nice,
  equalized, purely polynomial WAFA.
* `PaperLib.isWFARecognizable_of_isWAFARecognizable_of_locallyFinite`: over any locally
  finite commutative semiring, every WAFA-recognizable series is WFA-recognizable.
* `PaperLib.isWAFARecognizable_iff_reverse_isPARecognizable`: a series `s` is
  WAFA-recognizable if and only if its reversal `s^R` is PA-recognizable.
-/

public section

universe u v w

namespace CslibFrontier

open Finset

/-! ### Weighted Series and Word Homomorphism Operations -/

/-- A formal power series (weighted language) over `M` with weights in `S`. -/
abbrev WeightedSeries (S : Type u) (M : Type v) := M → S

/-- Pointwise (Hadamard) product of two weighted series. -/
@[expose] def hadamard {S : Type u} {M : Type v} [Mul S]
    (s₁ s₂ : WeightedSeries S M) : WeightedSeries S M :=
  fun w => s₁ w * s₂ w

@[simp] theorem hadamard_apply {S : Type u} {M : Type v} [Mul S]
    (s₁ s₂ : WeightedSeries S M) (w : M) : hadamard s₁ s₂ w = s₁ w * s₂ w := rfl

/-- Characteristic series `1_L` of a subset `L ⊆ M` with values in `S`. -/
@[expose] noncomputable def charFun (S : Type u) {M : Type v} [Zero S] [One S]
    (L : Set M) : WeightedSeries S M := by
  classical
  exact fun w => if w ∈ L then 1 else 0

theorem charFun_apply_of_mem {S : Type u} {M : Type v} [Zero S] [One S]
    {L : Set M} {w : M} (hw : w ∈ L) : charFun S L w = 1 := by
  classical
  simp [charFun, hw]

theorem charFun_apply_of_notMem {S : Type u} {M : Type v} [Zero S] [One S]
    {L : Set M} {w : M} (hw : w ∉ L) : charFun S L w = 0 := by
  classical
  simp [charFun, hw]

/-- Reversal `s^R` of a weighted word language. -/
@[expose] def reverseSeries {S : Type u} {Alph : Type v} (s : List Alph → S) : List Alph → S :=
  fun w => s w.reverse

@[simp] theorem reverseSeries_apply {S : Type u} {Alph : Type v} (s : List Alph → S)
    (w : List Alph) :
    reverseSeries s w = s w.reverse := rfl

@[simp] theorem reverseSeries_reverseSeries {S : Type u} {Alph : Type v} (s : List Alph → S) :
    reverseSeries (reverseSeries s) = s := by
  funext w
  simp [reverseSeries]

/-- A word homomorphism `f : Λ → List Σ` is non-deleting if `f a ≠ []` for all `a`. -/
@[expose] def IsNonDeletingWordHom {Λ : Type u} {Alph : Type v} (f : Λ → List Alph) : Prop :=
  ∀ a : Λ, f a ≠ []

/-- Pullback (inverse homomorphism) `h⁻¹(s)` of a weighted word language along `f : Λ → List Σ`. -/
@[expose] def wordHomPullback {S : Type u} {Λ : Type v} {Alph : Type w}
    (f : Λ → List Alph) (s : List Alph → S) : List Λ → S :=
  fun w => s (w.flatMap f)

@[simp] theorem wordHomPullback_apply {S : Type u} {Λ : Type v} {Alph : Type w}
    (f : Λ → List Alph) (s : List Alph → S) (w : List Λ) :
    wordHomPullback f s w = s (w.flatMap f) := rfl

/-- Non-deleting word homomorphisms do not decrease word length. -/
theorem length_le_length_flatMap {Λ : Type u} {Alph : Type v} {f : Λ → List Alph}
    (hf : IsNonDeletingWordHom f) (v : List Λ) : v.length ≤ (v.flatMap f).length := by
  induction v with
  | nil => simp
  | cons a t ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    have hpos : 1 ≤ (f a).length := List.length_pos_iff.mpr (hf a)
    omega

/-- Non-deleting word homomorphisms over a finite alphabet have finite fibers. -/
theorem finite_preimage_wordHom_of_isNonDeleting {Λ : Type u} {Alph : Type v} [Finite Λ]
    {f : Λ → List Alph} (hf : IsNonDeletingWordHom f) (w : List Alph) :
    {v : List Λ | v.flatMap f = w}.Finite := by
  have hsub : {v : List Λ | v.flatMap f = w} ⊆ {v : List Λ | v.length ≤ w.length} := by
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    rw [← hv]
    exact length_le_length_flatMap hf v
  have hfin : {v : List Λ | v.length ≤ w.length}.Finite := by
    have heq : {v : List Λ | v.length ≤ w.length} =
        ⋃ k ∈ Finset.range (w.length + 1), {v : List Λ | v.length = k} := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
      constructor
      · intro h; exact ⟨v.length, by omega, rfl⟩
      · rintro ⟨k, hk, rfl⟩; omega
    rw [heq]
    exact (Finset.finite_toSet _).biUnion (fun k _ => List.finite_length_eq Λ k)
  exact hfin.subset hsub

/-- Pushforward `h(r)` of a weighted language along a non-deleting word homomorphism. -/
@[expose] noncomputable def wordHomPushforward {S : Type u} [AddCommMonoid S] {Λ : Type v}
    {Alph : Type w} [Finite Λ] (f : Λ → List Alph) (hf : IsNonDeletingWordHom f)
    (r : List Λ → S) : List Alph → S :=
  fun w => ∑ v ∈ (finite_preimage_wordHom_of_isNonDeleting hf w).toFinset, r v

theorem wordHomPushforward_apply {S : Type u} [AddCommMonoid S] {Λ : Type v} {Alph : Type w}
    [Finite Λ] (f : Λ → List Alph) (hf : IsNonDeletingWordHom f) (r : List Λ → S) (w : List Alph) :
    wordHomPushforward f hf r w =
      ∑ v ∈ (finite_preimage_wordHom_of_isNonDeleting hf w).toFinset, r v := rfl

/-! ### Weighted Alternating Finite Automata (WAFA) -/

/-- A weighted alternating finite automaton (WAFA) over commutative semiring `S`, finite state
space `Q`, and alphabet `Alph`. -/
@[ext]
structure WAFA (S : Type u) [CommSemiring S] (Q : Type v) (Alph : Type w) where
  /-- Transition function assigning a polynomial in `S[Q]` to each state and letter. -/
  δ : Q → Alph → MvPolynomial Q S
  /-- Initial polynomial `P_0 ∈ S[Q]`. -/
  init : MvPolynomial Q S
  /-- Final weight function `τ : Q → S`. -/
  final : Q → S

namespace WAFA

variable {S : Type u} [CommSemiring S] {Q : Type v} {Q' : Type*} {Alph : Type w}

/-- State behavior `[A]_q(w)` of a WAFA, defined recursively on the word `w`. -/
@[expose] noncomputable def stateBehavior (A : WAFA S Q Alph) : Q → List Alph → S
  | q, [] => A.final q
  | q, a :: v => MvPolynomial.eval (fun p => A.stateBehavior p v) (A.δ q a)

@[simp] theorem stateBehavior_nil (A : WAFA S Q Alph) (q : Q) :
    A.stateBehavior q [] = A.final q := rfl

@[simp] theorem stateBehavior_cons (A : WAFA S Q Alph) (q : Q) (a : Alph) (v : List Alph) :
    A.stateBehavior q (a :: v) = MvPolynomial.eval (fun p => A.stateBehavior p v) (A.δ q a) := rfl

/-- Behavior `[[A]](w) = P_0⟨[A]_{q_1}(w), ..., [A]_{q_n}(w)⟩` of a WAFA. -/
@[expose] noncomputable def behavior (A : WAFA S Q Alph) : List Alph → S :=
  fun w => MvPolynomial.eval (fun q => A.stateBehavior q w) A.init

@[simp] theorem behavior_apply (A : WAFA S Q Alph) (w : List Alph) :
    A.behavior w = MvPolynomial.eval (fun q => A.stateBehavior q w) A.init := rfl

/-- Transfer a WAFA across an equivalence of state spaces. -/
noncomputable def mapStates (A : WAFA S Q Alph) (e : Q ≃ Q') : WAFA S Q' Alph where
  δ q' a := MvPolynomial.rename e (A.δ (e.symm q') a)
  init := MvPolynomial.rename e A.init
  final q' := A.final (e.symm q')

theorem stateBehavior_mapStates (A : WAFA S Q Alph) (e : Q ≃ Q') (q' : Q') (w : List Alph) :
    (A.mapStates e).stateBehavior q' w = A.stateBehavior (e.symm q') w := by
  induction w generalizing q' with
  | nil => rfl
  | cons a v ih =>
    rw [stateBehavior_cons, stateBehavior_cons]
    have hδ : (A.mapStates e).δ q' a = MvPolynomial.rename e (A.δ (e.symm q') a) := rfl
    rw [hδ, MvPolynomial.eval_rename]
    congr 2
    funext p
    exact (ih (e p)).trans (by simp)

@[simp] theorem behavior_mapStates (A : WAFA S Q Alph) (e : Q ≃ Q') :
    (A.mapStates e).behavior = A.behavior := by
  funext w
  rw [behavior_apply, behavior_apply]
  have hinit : (A.mapStates e).init = MvPolynomial.rename e A.init := rfl
  rw [hinit, MvPolynomial.eval_rename]
  congr 2
  funext p
  exact (stateBehavior_mapStates A e (e p) w).trans (by simp)

/-- Degree of a monomial exponent vector `m : Q →₀ ℕ`. -/
@[expose] def monomialDegree (m : Q →₀ ℕ) : ℕ :=
  m.sum (fun _ k => k)

theorem monomialDegree_eq_sum (m : Q →₀ ℕ) :
    monomialDegree m = ∑ q ∈ m.support, m q := rfl

@[simp] theorem monomialDegree_zero : monomialDegree (0 : Q →₀ ℕ) = 0 := by
  simp [monomialDegree]

@[simp] theorem monomialDegree_single (q : Q) (k : ℕ) :
    monomialDegree (Finsupp.single q k) = k := by
  simp [monomialDegree]

theorem monomialDegree_add (m₁ m₂ : Q →₀ ℕ) :
    monomialDegree (m₁ + m₂) = monomialDegree m₁ + monomialDegree m₂ := by
  classical
  simp only [monomialDegree]
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/-- A WAFA is a weighted finite automaton (WFA) if its initial polynomial and every transition
polynomial are homogeneous of degree `1` (linear combinations of single states). -/
@[expose] def IsWFA (A : WAFA S Q Alph) : Prop :=
  (∀ m ∈ A.init.support, monomialDegree m = 1) ∧
  (∀ q a, ∀ m ∈ (A.δ q a).support, monomialDegree m = 1)

/-- A WAFA is nice if all monomials in `P_0` and `δ` are non-constant (`coeff 0 = 0`) and
`P_0 = X q₀` for some initial state `q₀`. -/
@[expose] def IsNice (A : WAFA S Q Alph) : Prop :=
  A.init.coeff 0 = 0 ∧
  (∀ q a, (A.δ q a).coeff 0 = 0) ∧
  (∃ q₀ : Q, A.init = MvPolynomial.X q₀)

/-- A WAFA is purely polynomial if every monomial appearing in `P_0` and `δ` has coefficient
`1`. -/
@[expose] def IsPurelyPolynomial (A : WAFA S Q Alph) : Prop :=
  (∀ m ∈ A.init.support, A.init.coeff m = 1) ∧
  (∀ q a, ∀ m ∈ (A.δ q a).support, (A.δ q a).coeff m = 1)

/-- A WAFA is equalized if all monomials appearing in `δ` share a common positive degree `r`. -/
@[expose] def IsEqualized (A : WAFA S Q Alph) : Prop :=
  ∃ r : ℕ, 1 ≤ r ∧ ∀ q a, ∀ m ∈ (A.δ q a).support, monomialDegree m = r

end WAFA

/-- A weighted word language `s : List Σ → S` is recognized by a WAFA. -/
@[expose] def IsWAFARecognizable {S : Type u} [CommSemiring S] {Alph : Type w}
    (s : List Alph → S) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (A : WAFA S Q Alph), A.behavior = s

/-- A weighted word language `s : List Σ → S` is recognized by a WFA (linear WAFA). -/
@[expose] def IsWFARecognizable {S : Type u} [CommSemiring S] {Alph : Type w}
    (s : List Alph → S) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (A : WAFA S Q Alph), A.IsWFA ∧ A.behavior = s

/-- Every WFA-recognizable series is WAFA-recognizable. -/
theorem IsWFARecognizable.isWAFARecognizable {S : Type u} [CommSemiring S] {Alph : Type w}
    {s : List Alph → S} (h : IsWFARecognizable s) : IsWAFARecognizable s :=
  let ⟨Q, hQ, A, _, hA⟩ := h
  ⟨Q, hQ, A, hA⟩

/-- Transfer `IsWAFARecognizable` from any finite state space in any universe. -/
theorem IsWAFARecognizable.of_wafa {S : Type u} [CommSemiring S] {Q : Type v} [Finite Q]
    {Alph : Type w} (A : WAFA S Q Alph) : IsWAFARecognizable A.behavior := by
  have := Fintype.ofFinite Q
  exact ⟨Fin (Fintype.card Q), inferInstance, A.mapStates (Fintype.equivFin Q),
    A.behavior_mapStates _⟩

/-! ### Linear-Representation WFA and Equivalence with Degree-1 WAFA -/

/-- A linear-representation weighted finite automaton `(Q, Σ, init, trans, final)` over
commutative semiring `S`. -/
@[ext]
structure WFA (S : Type u) [CommSemiring S] (Q : Type v) (Alph : Type w) where
  /-- Initial weight vector `λ : Q → S`. -/
  init : Q → S
  /-- Transition weight matrices `μ(a)(q, q')`. -/
  trans : Alph → Q → Q → S
  /-- Final weight vector `γ : Q → S`. -/
  final : Q → S

namespace WFA

variable {S : Type u} [CommSemiring S] {Q : Type v} [Fintype Q] {Alph : Type w}

/-- State behavior of a linear WFA. -/
@[expose] def stateBehavior (A : WFA S Q Alph) : Q → List Alph → S
  | q, [] => A.final q
  | q, a :: v => ∑ p : Q, A.trans a q p * A.stateBehavior p v

@[simp] theorem stateBehavior_nil (A : WFA S Q Alph) (q : Q) :
    A.stateBehavior q [] = A.final q := rfl

@[simp] theorem stateBehavior_cons (A : WFA S Q Alph) (q : Q) (a : Alph) (v : List Alph) :
    A.stateBehavior q (a :: v) = ∑ p : Q, A.trans a q p * A.stateBehavior p v := rfl

/-- Behavior of a linear WFA. -/
@[expose] def behavior (A : WFA S Q Alph) : List Alph → S :=
  fun w => ∑ q : Q, A.init q * A.stateBehavior q w

@[simp] theorem behavior_apply (A : WFA S Q Alph) (w : List Alph) :
    A.behavior w = ∑ q : Q, A.init q * A.stateBehavior q w := rfl

/-- Convert a linear WFA into a degree-1 WAFA with the same behavior. -/
noncomputable def toWAFA (A : WFA S Q Alph) : WAFA S Q Alph where
  δ q a := ∑ p : Q, MvPolynomial.C (A.trans a q p) * MvPolynomial.X p
  init := ∑ q : Q, MvPolynomial.C (A.init q) * MvPolynomial.X q
  final := A.final

private theorem mem_support_linear_sum (f : Q → S) (m : Q →₀ ℕ)
    (hm : m ∈ (∑ q : Q, MvPolynomial.C (f q) * MvPolynomial.X q).support) :
    ∃ q : Q, m = Finsupp.single q 1 := by
  classical
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum] at hm
  by_contra hno
  apply hm
  refine Finset.sum_eq_zero (fun q _ => ?_)
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
  have hneq : Finsupp.single q 1 ≠ m := fun heq => hno ⟨q, heq.symm⟩
  simp [hneq]

/-- `A.toWAFA` satisfies `WAFA.IsWFA`. -/
theorem toWAFA_isWFA (A : WFA S Q Alph) : A.toWAFA.IsWFA := by
  have hlin : ∀ (f : Q → S) (m : Q →₀ ℕ),
      m ∈ (∑ q : Q, MvPolynomial.C (f q) * MvPolynomial.X q).support →
        WAFA.monomialDegree m = 1 := by
    intro f m hm
    obtain ⟨q, rfl⟩ := mem_support_linear_sum f m hm
    simp
  exact ⟨hlin A.init, fun q a => hlin (A.trans a q)⟩

theorem stateBehavior_toWAFA (A : WFA S Q Alph) (q : Q) (w : List Alph) :
    A.toWAFA.stateBehavior q w = A.stateBehavior q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a v ih =>
    rw [WAFA.stateBehavior_cons, stateBehavior_cons]
    have hδ : A.toWAFA.δ q a = ∑ p : Q, MvPolynomial.C (A.trans a q p) * MvPolynomial.X p := rfl
    rw [hδ, map_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp [ih p]

@[simp] theorem behavior_toWAFA (A : WFA S Q Alph) : A.toWAFA.behavior = A.behavior := by
  funext w
  rw [WAFA.behavior_apply, behavior_apply]
  have hinit : A.toWAFA.init = ∑ q : Q, MvPolynomial.C (A.init q) * MvPolynomial.X q := rfl
  rw [hinit, map_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  simp [stateBehavior_toWAFA]

/-- Extract a linear WFA from any WAFA satisfying `IsWFA`. -/
noncomputable def ofWAFA (A : WAFA S Q Alph) : WFA S Q Alph where
  init q := A.init.coeff (Finsupp.single q 1)
  trans a q p := (A.δ q a).coeff (Finsupp.single p 1)
  final := A.final

private theorem eval_of_linear {p : MvPolynomial Q S}
    (hp : ∀ m ∈ p.support, WAFA.monomialDegree m = 1) (v : Q → S) :
    MvPolynomial.eval v p = ∑ q : Q, p.coeff (Finsupp.single q 1) * v q := by
  classical
  have hsingle : ∀ m ∈ p.support, ∃ q : Q, m = Finsupp.single q 1 := by
    intro m hm
    have hdeg := hp m hm
    have hne : m.support.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      simp [WAFA.monomialDegree, Finsupp.sum, hempty] at hdeg
    obtain ⟨q, hq⟩ := hne
    have hmq : 1 ≤ m q := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hq)
    have hle : m q ≤ ∑ r ∈ m.support, m r := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hq
    have hdeg' : ∑ r ∈ m.support, m r = 1 := hdeg
    have hmq1 : m q = 1 := by omega
    have hother : ∀ r, r ≠ q → m r = 0 := by
      intro r hr
      by_cases hrm : r ∈ m.support
      · have hrpos : 1 ≤ m r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hrm)
        have hsum := Finset.add_le_sum (f := fun x => m x) (fun _ _ => Nat.zero_le _) hq hrm hr.symm
        omega
      · exact Finsupp.notMem_support_iff.mp hrm
    refine ⟨q, ?_⟩
    ext r
    by_cases hr : r = q
    · subst hr; simp [hmq1]
    · simp [Finsupp.single_eq_of_ne hr, hother r hr]
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [map_sum]
  have h1 : ∑ m ∈ p.support, MvPolynomial.eval v (MvPolynomial.monomial m (p.coeff m)) =
      ∑ m ∈ p.support, p.coeff m * (m.prod fun q k => v q ^ k) :=
    Finset.sum_congr rfl (fun m _ => MvPolynomial.eval_monomial)
  rw [h1]
  let φ : Q → (Q →₀ ℕ) := fun q => Finsupp.single q 1
  have hinj : Function.Injective φ := by
    intro q₁ q₂ h
    have := congrArg (fun d : Q →₀ ℕ => d q₁) h
    by_cases hq : q₁ = q₂
    · exact hq
    · simp [φ, Finsupp.single_eq_of_ne hq] at this
  have hsub : p.support ⊆ Finset.univ.image φ := by
    intro m hm
    obtain ⟨q, rfl⟩ := hsingle m hm
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
  rw [Finset.sum_subset hsub (fun m _ hm => by simp [Finsupp.notMem_support_iff.mp hm])]
  rw [Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  simp [φ, Finsupp.prod_single_index]

theorem behavior_ofWAFA {A : WAFA S Q Alph} (hA : A.IsWFA) :
    (ofWAFA A).behavior = A.behavior := by
  have hst : ∀ (w : List Alph) (q : Q), (ofWAFA A).stateBehavior q w = A.stateBehavior q w := by
    intro w
    induction w with
    | nil => intro q; rfl
    | cons a v ih =>
      intro q
      rw [stateBehavior_cons, WAFA.stateBehavior_cons, eval_of_linear (hA.2 q a)]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      have ht : (ofWAFA A).trans a q p = (A.δ q a).coeff (Finsupp.single p 1) := rfl
      rw [ht, ih p]
  funext w
  rw [behavior_apply, WAFA.behavior_apply, eval_of_linear hA.1]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  have hi : (ofWAFA A).init q = A.init.coeff (Finsupp.single q 1) := rfl
  rw [hi, hst w q]

/-- Equivalence between `IsWFARecognizable` and existence of a finite linear `WFA`. -/
theorem isWFARecognizable_iff_exists_wfa {s : List Alph → S} :
    IsWFARecognizable s ↔
      ∃ (Q : Type) (_ : Fintype Q) (A : WFA S Q Alph), A.behavior = s := by
  constructor
  · rintro ⟨Q, _, A, hA, rfl⟩
    exact ⟨Q, inferInstance, ofWAFA A, behavior_ofWAFA hA⟩
  · rintro ⟨Q, _, A, rfl⟩
    exact ⟨Q, inferInstance, A.toWAFA, A.toWAFA_isWFA, A.behavior_toWAFA⟩

/-- Bridge from `PaperLib.WFA` to `Cslib.Automata.Weighted.Rep` over a commutative ring. -/
def toCslibRep {F : Type u} [CommRing F] {Q : Type v} {Alph : Type w}
    (A : WFA F Q Alph) : Cslib.Automata.Weighted.Rep F Alph Q where
  lam := A.init
  mu a := Matrix.of (A.trans a)
  gam := A.final

/-- `toCslibRep` realizes the exact same formal power series as `A.behavior`. -/
theorem toCslibRep_series {F : Type u} [CommRing F]
    (A : WFA F Q Alph) : A.toCslibRep.series = A.behavior := by
  have htail : ∀ (w : List Alph) (q : Q), A.toCslibRep.tail w q = A.stateBehavior q w := by
    intro w
    induction w with
    | nil => intro q; rfl
    | cons a v ih =>
      intro q
      change (∑ p : Q, A.trans a q p * A.toCslibRep.tail v p) = _
      rw [stateBehavior_cons]
      exact Finset.sum_congr rfl (fun p _ => by rw [ih p])
  funext w
  change (∑ q : Q, A.init q * A.toCslibRep.tail w q) = _
  rw [behavior_apply]
  exact Finset.sum_congr rfl (fun q _ => by rw [htail w q])

end WFA

/-! ### Normal Forms for WAFA -/

namespace WAFA

variable {S : Type u} [CommSemiring S] {Q : Type v} [Fintype Q] {Alph : Type w}

/-- Helper: evaluating `MvPolynomial.bind₁ f p` at `v` equals evaluating `p` at `eval v ∘ f`. -/
private theorem eval_bind₁_eq {Q₁ Q₂ : Type*} (f : Q₁ → MvPolynomial Q₂ S)
    (v : Q₂ → S) (p : MvPolynomial Q₁ S) :
    MvPolynomial.eval v (MvPolynomial.bind₁ f p) =
      MvPolynomial.eval (fun q => MvPolynomial.eval v (f q)) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    simp only [map_mul, MvPolynomial.eval_monomial, MvPolynomial.bind₁_monomial,
      MvPolynomial.eval_C]
    congr 1
    rw [Finsupp.prod, map_prod]
    refine Finset.prod_congr rfl (fun q _ => by simp)
  | add p₁ p₂ ih₁ ih₂ =>
    simp only [map_add, ih₁, ih₂]

/-- Helper: a polynomial with zero constant term evaluates to `0` at `0`. -/
private theorem eval_zero_eq_coeff_zero {Q₁ : Type*} (p : MvPolynomial Q₁ S) :
    MvPolynomial.eval (0 : Q₁ → S) p = p.coeff 0 := by
  rw [MvPolynomial.eval_eq]
  rw [Finset.sum_eq_single (0 : Q₁ →₀ ℕ)]
  · simp
  · intro m _ hm
    have hne : m.support.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      exact hm (Finsupp.support_eq_empty.mp hempty)
    obtain ⟨q, hq⟩ := hne
    have hmq : m q ≠ 0 := Finsupp.mem_support_iff.mp hq
    have hprod : (∏ i ∈ m.support, (0 : Q₁ → S) i ^ m i) = 0 := by
      refine Finset.prod_eq_zero hq ?_
      simp [hmq]
    rw [hprod, mul_zero]
  · intro h0
    simp [Finsupp.notMem_support_iff.mp h0]

/-- Helper: substituting non-constant polynomials into a non-constant polynomial preserves
`coeff 0 = 0`. -/
private theorem coeff_zero_bind₁ {Q₁ Q₂ : Type*} (p : MvPolynomial Q₁ S)
    (f : Q₁ → MvPolynomial Q₂ S) (hp : p.coeff 0 = 0) (hf : ∀ q, (f q).coeff 0 = 0) :
    (MvPolynomial.bind₁ f p).coeff 0 = 0 := by
  rw [← eval_zero_eq_coeff_zero, eval_bind₁_eq]
  have hzero : (fun q => MvPolynomial.eval (0 : Q₂ → S) (f q)) = 0 := by
    funext q
    rw [eval_zero_eq_coeff_zero, hf q]
    rfl
  rw [hzero, eval_zero_eq_coeff_zero, hp]

/-- The non-constant part of a multivariate polynomial over a commutative semiring. -/
noncomputable def nonConstPart {ι : Type*} (p : MvPolynomial ι S) : MvPolynomial ι S := by
  classical
  exact ∑ m ∈ p.support.erase 0, MvPolynomial.monomial m (p.coeff m)

theorem coeff_nonConstPart_zero {ι : Type*} (p : MvPolynomial ι S) :
    (nonConstPart p).coeff 0 = 0 := by
  classical
  simp only [nonConstPart, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  exact Finset.sum_eq_zero (fun k hk => by simp [Finset.ne_of_mem_erase hk])

theorem coeff_nonConstPart_ne {ι : Type*} (p : MvPolynomial ι S) {m : ι →₀ ℕ} (hm : m ≠ 0) :
    (nonConstPart p).coeff m = p.coeff m := by
  classical
  simp only [nonConstPart, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases hmem : m ∈ p.support
  · rw [Finset.sum_eq_single m]
    · simp
    · intro k _ hkm; simp [hkm]
    · intro hm'; exact absurd (Finset.mem_erase.mpr ⟨hm, hmem⟩) hm'
  · rw [Finsupp.notMem_support_iff.mp hmem]
    exact Finset.sum_eq_zero (fun k hk => by
      split_ifs with hkm
      · subst hkm; exact absurd (Finset.mem_of_mem_erase hk) hmem
      · rfl)

theorem nonConstPart_add_C_coeff_zero {ι : Type*} (p : MvPolynomial ι S) :
    nonConstPart p + MvPolynomial.C (p.coeff 0) = p := by
  classical
  ext m
  change (nonConstPart p).coeff m + (MvPolynomial.C (p.coeff 0)).coeff m = p.coeff m
  rw [MvPolynomial.coeff_C]
  by_cases hm : m = 0
  · subst hm; simp [coeff_nonConstPart_zero]
  · simp [coeff_nonConstPart_ne p hm, Ne.symm hm]

/-- Step (ii) (semiring-safe, zero subtraction): replace constant terms in `P_0`
and `δ` by fresh constant-`1` states `inr (some (q, a))` and `inr none`.
-/
noncomputable def eliminateConstants (A : WAFA S Q Alph) :
    WAFA S (Q ⊕ Option (Q × Alph)) Alph where
  δ
    | .inl q, a =>
      MvPolynomial.rename Sum.inl (nonConstPart (A.δ q a)) +
        MvPolynomial.C ((A.δ q a).coeff 0) * MvPolynomial.X (.inr (some (q, a)))
    | .inr c, _ => MvPolynomial.X (.inr c)
  init :=
    MvPolynomial.rename Sum.inl (nonConstPart A.init) +
      MvPolynomial.C (A.init.coeff 0) * MvPolynomial.X (.inr none)
  final
    | .inl q => A.final q
    | .inr _ => 1

omit [Fintype Q] in
private theorem stateBehavior_eliminateConstants_inr (A : WAFA S Q Alph)
    (c : Option (Q × Alph)) (w : List Alph) :
    (eliminateConstants A).stateBehavior (.inr c) w = 1 := by
  induction w with
  | nil => rfl
  | cons a v ih =>
    rw [stateBehavior_cons]
    have hδ : (eliminateConstants A).δ (.inr c) a = MvPolynomial.X (.inr c) := rfl
    rw [hδ, MvPolynomial.eval_X, ih]

omit [Fintype Q] in
theorem stateBehavior_eliminateConstants_inl (A : WAFA S Q Alph) (q : Q) (w : List Alph) :
    (eliminateConstants A).stateBehavior (.inl q) w = A.stateBehavior q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a v ih =>
    rw [stateBehavior_cons, stateBehavior_cons]
    have hδ : (eliminateConstants A).δ (.inl q) a =
        MvPolynomial.rename Sum.inl (nonConstPart (A.δ q a)) +
          MvPolynomial.C ((A.δ q a).coeff 0) * MvPolynomial.X (.inr (some (q, a))) := rfl
    rw [hδ, map_add, map_mul, MvPolynomial.eval_rename, MvPolynomial.eval_C,
      MvPolynomial.eval_X, stateBehavior_eliminateConstants_inr, mul_one]
    have hfun : (fun p => (eliminateConstants A).stateBehavior p v) ∘ Sum.inl =
        fun p => A.stateBehavior p v := by
      funext p; exact ih p
    rw [hfun]
    have h := congrArg (MvPolynomial.eval (fun p => A.stateBehavior p v))
      (nonConstPart_add_C_coeff_zero (A.δ q a))
    simpa only [map_add, MvPolynomial.eval_C] using h

omit [Fintype Q] in
theorem behavior_eliminateConstants (A : WAFA S Q Alph) :
    (eliminateConstants A).behavior = A.behavior := by
  funext w
  rw [behavior_apply, behavior_apply]
  have hinit : (eliminateConstants A).init =
      MvPolynomial.rename Sum.inl (nonConstPart A.init) +
        MvPolynomial.C (A.init.coeff 0) * MvPolynomial.X (.inr none) := rfl
  rw [hinit, map_add, map_mul, MvPolynomial.eval_rename, MvPolynomial.eval_C,
    MvPolynomial.eval_X, stateBehavior_eliminateConstants_inr, mul_one]
  have hfun : (fun p => (eliminateConstants A).stateBehavior p w) ∘ Sum.inl =
      fun p => A.stateBehavior p w := by
    funext p; exact stateBehavior_eliminateConstants_inl A p w
  rw [hfun]
  have h := congrArg (MvPolynomial.eval (fun p => A.stateBehavior p w))
    (nonConstPart_add_C_coeff_zero A.init)
  simpa only [map_add, MvPolynomial.eval_C] using h

omit [Fintype Q] in
theorem coeff_zero_eliminateConstants (A : WAFA S Q Alph) :
    (eliminateConstants A).init.coeff 0 = 0 ∧
      ∀ q a, ((eliminateConstants A).δ q a).coeff 0 = 0 := by
  classical
  have hC_mul_X : ∀ (s : S) (x : Q ⊕ Option (Q × Alph)),
      (MvPolynomial.C s * MvPolynomial.X x).coeff 0 = 0 := by
    intro s x
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
    have hne : Finsupp.single x 1 ≠ (0 : (Q ⊕ Option (Q × Alph)) →₀ ℕ) :=
      Finsupp.single_ne_zero.mpr Nat.one_ne_zero
    simp [hne]
  have hren : ∀ (p : MvPolynomial Q S),
      (MvPolynomial.rename (Sum.inl : Q → Q ⊕ Option (Q × Alph)) (nonConstPart p)).coeff 0 = 0 := by
    intro p
    rw [← eval_zero_eq_coeff_zero, MvPolynomial.eval_rename]
    have hz : (0 : (Q ⊕ Option (Q × Alph)) → S) ∘ Sum.inl = 0 := rfl
    rw [hz, eval_zero_eq_coeff_zero, coeff_nonConstPart_zero]
  refine ⟨?_, ?_⟩
  · change (MvPolynomial.rename Sum.inl (nonConstPart A.init)).coeff 0 +
      (MvPolynomial.C (A.init.coeff 0) *
        MvPolynomial.X (Sum.inr none : Q ⊕ Option (Q × Alph))).coeff 0 = 0
    rw [hren, hC_mul_X, add_zero]
  · intro q a
    cases q with
    | inl q =>
      change (MvPolynomial.rename Sum.inl (nonConstPart (A.δ q a))).coeff 0 +
        (MvPolynomial.C ((A.δ q a).coeff 0) *
          MvPolynomial.X (Sum.inr (some (q, a)) : Q ⊕ Option (Q × Alph))).coeff 0 = 0
      rw [hren, hC_mul_X, add_zero]
    | inr c =>
      change (MvPolynomial.X (Sum.inr c : Q ⊕ Option (Q × Alph)) : MvPolynomial _ S).coeff 0 = 0
      rw [MvPolynomial.coeff_X]
      have hne : Finsupp.single (Sum.inr c : Q ⊕ Option (Q × Alph)) 1 ≠ 0 :=
        Finsupp.single_ne_zero.mpr Nat.one_ne_zero
      simp [hne]

/-- Step (iii): introduce a fresh initial
state `none` with `P_0' = X none`, preserving zero constant terms.
-/
noncomputable def makeSingleInitial (A : WAFA S Q Alph) : WAFA S (Option Q) Alph where
  δ
    | some q, a => MvPolynomial.rename some (A.δ q a)
    | none, a => MvPolynomial.bind₁ (fun q => MvPolynomial.rename some (A.δ q a)) A.init
  init := MvPolynomial.X none
  final
    | some q => A.final q
    | none => MvPolynomial.eval A.final A.init

omit [Fintype Q] in
theorem stateBehavior_makeSingleInitial_some (A : WAFA S Q Alph) (q : Q) (w : List Alph) :
    (makeSingleInitial A).stateBehavior (some q) w = A.stateBehavior q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a v ih =>
    rw [stateBehavior_cons, stateBehavior_cons]
    have hδ : (makeSingleInitial A).δ (some q) a = MvPolynomial.rename some (A.δ q a) := rfl
    rw [hδ, MvPolynomial.eval_rename]
    congr 2; funext p; exact ih p

omit [Fintype Q] in
theorem behavior_makeSingleInitial (A : WAFA S Q Alph) :
    (makeSingleInitial A).behavior = A.behavior := by
  funext w
  rw [behavior_apply]
  have hinit : (makeSingleInitial A).init = MvPolynomial.X none := rfl
  rw [hinit, MvPolynomial.eval_X]
  cases w with
  | nil => rfl
  | cons a v =>
    rw [stateBehavior_cons, behavior_apply]
    have hδ : (makeSingleInitial A).δ none a =
        MvPolynomial.bind₁ (fun q => MvPolynomial.rename some (A.δ q a)) A.init := rfl
    rw [hδ, eval_bind₁_eq]
    congr 2; funext q
    rw [MvPolynomial.eval_rename, stateBehavior_cons]
    congr 2; funext p
    exact stateBehavior_makeSingleInitial_some A p v

omit [Fintype Q] in
theorem isNice_makeSingleInitial {A : WAFA S Q Alph}
    (hinit : A.init.coeff 0 = 0) (hδ : ∀ q a, (A.δ q a).coeff 0 = 0) :
    (makeSingleInitial A).IsNice := by
  classical
  have hren0 : ∀ (p : MvPolynomial Q S), p.coeff 0 = 0 →
      (MvPolynomial.rename (some : Q → Option Q) p).coeff 0 = 0 := by
    intro p hp
    rw [← eval_zero_eq_coeff_zero, MvPolynomial.eval_rename]
    have hz : (0 : Option Q → S) ∘ some = 0 := rfl
    rw [hz, eval_zero_eq_coeff_zero, hp]
  refine ⟨?_, ?_, ⟨none, rfl⟩⟩
  · change (MvPolynomial.X (none : Option Q) : MvPolynomial (Option Q) S).coeff 0 = 0
    rw [MvPolynomial.coeff_X]
    have hne : Finsupp.single (none : Option Q) 1 ≠ 0 :=
      Finsupp.single_ne_zero.mpr Nat.one_ne_zero
    simp [hne]
  · intro q a
    cases q with
    | some q => exact hren0 (A.δ q a) (hδ q a)
    | none => exact coeff_zero_bind₁ A.init _ hinit (fun q => hren0 (A.δ q a) (hδ q a))

/-- Step (iv): convert any nice WAFA into an equivalent nice, purely polynomial
WAFA by replacing each monomial `s * m` in `δ(q, a)` with `m * q_{(q, a, m)}`.
-/
noncomputable def makePurelyPolynomial (A : WAFA S Q Alph) (q₀ : Q) :
    WAFA S (Q ⊕ (Σ q : Q, Σ a : Alph, {m : Q →₀ ℕ // m ∈ (A.δ q a).support})) Alph where
  δ
    | .inl q, a =>
      ∑ m ∈ (A.δ q a).support.attach,
        MvPolynomial.monomial
          (m.1.mapDomain Sum.inl + Finsupp.single (.inr ⟨q, a, m⟩) 1) 1
    | .inr c, _ => MvPolynomial.X (.inr c)
  init := MvPolynomial.X (.inl q₀)
  final
    | .inl q => A.final q
    | .inr ⟨q, a, m⟩ => (A.δ q a).coeff m.1

omit [Fintype Q] in
private theorem stateBehavior_makePurelyPolynomial_inr (A : WAFA S Q Alph) (q₀ : Q)
    (c : Σ q : Q, Σ a : Alph, {m : Q →₀ ℕ // m ∈ (A.δ q a).support}) (w : List Alph) :
    (makePurelyPolynomial A q₀).stateBehavior (.inr c) w =
      (makePurelyPolynomial A q₀).final (.inr c) := by
  induction w with
  | nil => rfl
  | cons a v ih =>
    rw [stateBehavior_cons]
    have hδ : (makePurelyPolynomial A q₀).δ (.inr c) a = MvPolynomial.X (.inr c) := rfl
    rw [hδ, MvPolynomial.eval_X, ih]

omit [Fintype Q] in
theorem stateBehavior_makePurelyPolynomial_inl (A : WAFA S Q Alph) (q₀ q : Q) (w : List Alph) :
    (makePurelyPolynomial A q₀).stateBehavior (.inl q) w = A.stateBehavior q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a v ih =>
    rw [stateBehavior_cons, stateBehavior_cons]
    have hδ : (makePurelyPolynomial A q₀).δ (.inl q) a =
        ∑ m ∈ (A.δ q a).support.attach,
          MvPolynomial.monomial
            (m.1.mapDomain Sum.inl + Finsupp.single (Sum.inr ⟨q, a, m⟩) 1) 1 := rfl
    rw [hδ, map_sum, MvPolynomial.eval_eq]
    have hprod : ∀ m : {m : Q →₀ ℕ // m ∈ (A.δ q a).support},
        MvPolynomial.eval (fun p => (makePurelyPolynomial A q₀).stateBehavior p v)
          (MvPolynomial.monomial
            (m.1.mapDomain Sum.inl + Finsupp.single (Sum.inr ⟨q, a, m⟩) 1) 1) =
        (A.δ q a).coeff m.1 * (m.1.prod fun p k => A.stateBehavior p v ^ k) := by
      intro m
      rw [MvPolynomial.eval_monomial, one_mul]
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      simp only [Finsupp.prod_single_index, pow_zero, pow_one,
        stateBehavior_makePurelyPolynomial_inr]
      rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      rw [mul_comm]
      congr 1
      refine Finset.prod_congr rfl (fun p _ => ?_)
      dsimp only
      rw [ih p]
    rw [Finset.sum_congr rfl (fun m _ => hprod m)]
    rw [Finset.sum_attach (A.δ q a).support
      (fun m => (A.δ q a).coeff m * (m.prod fun p k => A.stateBehavior p v ^ k))]
    rfl

omit [Fintype Q] in
theorem behavior_makePurelyPolynomial {A : WAFA S Q Alph} {q₀ : Q} (hinit : A.init =
    MvPolynomial.X q₀) :
    (makePurelyPolynomial A q₀).behavior = A.behavior := by
  funext w
  rw [behavior_apply, behavior_apply, hinit]
  have hi : (makePurelyPolynomial A q₀).init = MvPolynomial.X (.inl q₀) := rfl
  rw [hi, MvPolynomial.eval_X, MvPolynomial.eval_X, stateBehavior_makePurelyPolynomial_inl]

omit [Fintype Q] in
theorem isNice_isPurelyPolynomial_makePurelyPolynomial (A : WAFA S Q Alph) (q₀ : Q) :
    (makePurelyPolynomial A q₀).IsNice ∧ (makePurelyPolynomial A q₀).IsPurelyPolynomial := by
  classical
  let Q' := Q ⊕ (Σ q : Q, Σ a : Alph, {m : Q →₀ ℕ // m ∈ (A.δ q a).support})
  let B := makePurelyPolynomial A q₀
  have hsingle_ne : ∀ x : Q', Finsupp.single x 1 ≠ 0 :=
    fun x => Finsupp.single_ne_zero.mpr Nat.one_ne_zero
  have hinj : ∀ (q : Q) (a : Alph)
      (m₁ m₂ : {m : Q →₀ ℕ // m ∈ (A.δ q a).support}),
      m₁.1.mapDomain (Sum.inl : Q → Q') + Finsupp.single (Sum.inr ⟨q, a, m₁⟩ : Q') 1 =
        m₂.1.mapDomain (Sum.inl : Q → Q') + Finsupp.single (Sum.inr ⟨q, a, m₂⟩ : Q') 1 →
      m₁ = m₂ := by
    intro q a m₁ m₂ heq
    have hval := congrArg (fun d : Q' →₀ ℕ => d (Sum.inr ⟨q, a, m₁⟩)) heq
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hval
    have hmap : ∀ (d : Q →₀ ℕ) (c), d.mapDomain (Sum.inl : Q → Q') (Sum.inr c) = 0 := by
      intro d c
      rw [Finsupp.mapDomain_of_notMem_range]
      rintro ⟨x, hx⟩; exact nomatch hx
    rw [hmap, hmap, zero_add, zero_add] at hval
    by_cases h : m₁ = m₂
    · exact h
    · have hne : (⟨q, a, m₂⟩ : Σ q : Q, Σ a : Alph, {m : Q →₀ ℕ // m ∈ (A.δ q a).support}) ≠
          ⟨q, a, m₁⟩ := by
        intro heq'; apply h; cases heq'; rfl
      rw [Finsupp.single_eq_of_ne (fun he => hne (Sum.inr.inj he).symm)] at hval
      exact absurd hval (by omega)
  have hcoeff_B : ∀ (q : Q) (a : Alph) (d),
      (B.δ (.inl q) a).coeff d =
        if ∃ m : {m : Q →₀ ℕ // m ∈ (A.δ q a).support},
            d = m.1.mapDomain Sum.inl + Finsupp.single (.inr ⟨q, a, m⟩) 1
        then 1 else 0 := by
    intro q a d
    simp only [B, makePurelyPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    split_ifs with h
    · obtain ⟨m₀, rfl⟩ := h
      rw [Finset.sum_eq_single m₀]
      · simp
      · intro m _ hm
        split_ifs with heq
        · exact absurd (hinj q a m m₀ heq) hm
        · rfl
      · intro hm; exact absurd (Finset.mem_attach _ m₀) hm
    · refine Finset.sum_eq_zero (fun m _ => ?_)
      split_ifs with heq
      · exact absurd ⟨m, heq.symm⟩ h
      · rfl
  refine ⟨⟨?_, ?_, ⟨.inl q₀, rfl⟩⟩, ⟨?_, ?_⟩⟩
  · simp [makePurelyPolynomial, MvPolynomial.coeff_X, hsingle_ne]
  · intro q a
    cases q with
    | inl q =>
      rw [hcoeff_B]
      split_ifs with h0
      · rcases h0 with ⟨m, h0⟩
        have hval := congrArg (fun d => d (.inr ⟨q, a, m⟩)) h0
        simp only [Finsupp.zero_apply, Finsupp.add_apply, Finsupp.single_eq_same] at hval
        omega
      · rfl
    | inr c => simp [makePurelyPolynomial, MvPolynomial.coeff_X, hsingle_ne]
  · intro m hm
    simp only [makePurelyPolynomial, MvPolynomial.mem_support_iff, MvPolynomial.coeff_X] at hm ⊢
    split_ifs at hm ⊢ with h
    · rfl
    · exact absurd rfl hm
  · intro q a m hm
    cases q with
    | inl q =>
      rw [MvPolynomial.mem_support_iff, hcoeff_B] at hm
      rw [hcoeff_B]
      split_ifs at hm ⊢ with h
      · rfl
      · exact absurd rfl hm
    | inr c =>
      simp only [makePurelyPolynomial, MvPolynomial.mem_support_iff,
        MvPolynomial.coeff_X] at hm ⊢
      split_ifs at hm ⊢ with h
      · rfl
      · exact absurd rfl hm

omit [Fintype Q] in
/-- Every WAFA has an equivalent nice, purely
polynomial WAFA.
-/
theorem exists_nice_purelyPolynomial_equiv [Finite Q] [Finite Alph] (A : WAFA S Q Alph) :
    ∃ (Q' : Type) (_ : Fintype Q') (A' : WAFA S Q' Alph),
      A'.IsNice ∧ A'.IsPurelyPolynomial ∧ A'.behavior = A.behavior := by
  classical
  have := Fintype.ofFinite Q
  have := Fintype.ofFinite Alph
  let A₁ := eliminateConstants A
  let A₂ := makeSingleInitial A₁
  let A₃ := makePurelyPolynomial A₂ none
  have hnice_pp := isNice_isPurelyPolynomial_makePurelyPolynomial A₂ none
  let Q₃ := Option (Q ⊕ Option (Q × Alph)) ⊕
    (Σ q : Option (Q ⊕ Option (Q × Alph)), Σ a : Alph, {m : _ // m ∈ (A₂.δ q a).support})
  let e : Q₃ ≃ Fin (Fintype.card Q₃) := Fintype.equivFin Q₃
  let A' := A₃.mapStates e
  refine ⟨Fin (Fintype.card Q₃), inferInstance, A', ?_, ?_, ?_⟩
  · -- `IsNice` transfers across `mapStates e`
    have hcoeff_ren : ∀ (p : MvPolynomial Q₃ S), p.coeff 0 = 0 →
        (MvPolynomial.rename e p).coeff 0 = 0 := by
      intro p hp
      rw [← eval_zero_eq_coeff_zero, MvPolynomial.eval_rename]
      have hz : (0 : Fin (Fintype.card Q₃) → S) ∘ e = 0 := rfl
      rw [hz, eval_zero_eq_coeff_zero, hp]
    refine ⟨hcoeff_ren _ hnice_pp.1.1, fun q' a => hcoeff_ren _ (hnice_pp.1.2.1 _ _), ?_⟩
    obtain ⟨q₀, hq₀⟩ := hnice_pp.1.2.2
    exact ⟨e q₀, by dsimp [A', mapStates]; rw [hq₀, MvPolynomial.rename_X]⟩
  · -- `IsPurelyPolynomial` transfers across `mapStates e`
    have hcoeff_eq : ∀ (p : MvPolynomial Q₃ S) (m),
        (MvPolynomial.rename e p).coeff m = p.coeff (m.comapDomain e e.injective.injOn) := by
      intro p m
      have h1 :=
        MvPolynomial.coeff_rename_mapDomain e e.injective p (m.comapDomain e e.injective.injOn)
      have h2 : (m.comapDomain e e.injective.injOn).mapDomain e = m := by
        ext x
        rw [Finsupp.mapDomain_equiv_apply]
        simp [Finsupp.comapDomain_apply]
      rw [h2] at h1
      exact h1
    refine ⟨?_, ?_⟩
    · intro m hm
      dsimp only [A', mapStates] at hm ⊢
      rw [MvPolynomial.mem_support_iff, hcoeff_eq] at hm
      rw [hcoeff_eq]
      exact hnice_pp.2.1 _ (MvPolynomial.mem_support_iff.mpr hm)
    · intro q' a m hm
      dsimp only [A', mapStates] at hm ⊢
      rw [MvPolynomial.mem_support_iff, hcoeff_eq] at hm
      rw [hcoeff_eq]
      exact hnice_pp.2.2 _ _ _ (MvPolynomial.mem_support_iff.mpr hm)
  · rw [behavior_mapStates, behavior_makePurelyPolynomial rfl, behavior_makeSingleInitial,
      behavior_eliminateConstants]

/-- Padding construction: given a nice WAFA `A` and a target degree `d ≥ 1`
bounding all monomial degrees in `δ`, pad every monomial in `δ` with powers of a fresh
state `none` (`τ(none) = 1`, `δ(none, a) = X(none)^d`).
-/
noncomputable def equalizeAt (A : WAFA S Q Alph) (q₀ : Q) (d : ℕ) : WAFA S (Option Q) Alph where
  δ
    | some q, a =>
      ∑ m ∈ (A.δ q a).support,
        MvPolynomial.monomial
          (m.mapDomain some + Finsupp.single none (d - monomialDegree m))
          ((A.δ q a).coeff m)
    | none, _ => MvPolynomial.X none ^ d
  init := MvPolynomial.X (some q₀)
  final
    | some q => A.final q
    | none => 1

omit [Fintype Q] in
private theorem stateBehavior_equalizeAt_none (A : WAFA S Q Alph) (q₀ : Q) (d : ℕ) (w : List Alph) :
    (equalizeAt A q₀ d).stateBehavior none w = 1 := by
  induction w with
  | nil => rfl
  | cons a v ih =>
    rw [stateBehavior_cons]
    have hδ : (equalizeAt A q₀ d).δ none a = MvPolynomial.X none ^ d := rfl
    rw [hδ, map_pow, MvPolynomial.eval_X, ih, one_pow]

omit [Fintype Q] in
theorem stateBehavior_equalizeAt_some (A : WAFA S Q Alph) (q₀ : Q) (d : ℕ) (q : Q) (w : List Alph) :
    (equalizeAt A q₀ d).stateBehavior (some q) w = A.stateBehavior q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a v ih =>
    rw [stateBehavior_cons, stateBehavior_cons]
    have hδ : (equalizeAt A q₀ d).δ (some q) a =
        ∑ m ∈ (A.δ q a).support,
          MvPolynomial.monomial
            (m.mapDomain some + Finsupp.single none (d - monomialDegree m))
            ((A.δ q a).coeff m) := rfl
    rw [hδ, map_sum, MvPolynomial.eval_eq]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [MvPolynomial.eval_monomial]
    congr 1
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    simp only [Finsupp.prod_single_index, pow_zero, stateBehavior_equalizeAt_none, one_pow, mul_one]
    rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    dsimp only
    rw [ih p]

omit [Fintype Q] in
theorem behavior_equalizeAt {A : WAFA S Q Alph} {q₀ : Q} (hinit : A.init = MvPolynomial.X q₀)
    (d : ℕ) : (equalizeAt A q₀ d).behavior = A.behavior := by
  funext w
  rw [behavior_apply, behavior_apply, hinit]
  have hi : (equalizeAt A q₀ d).init = MvPolynomial.X (some q₀) := rfl
  rw [hi, MvPolynomial.eval_X, MvPolynomial.eval_X, stateBehavior_equalizeAt_some]

omit [Fintype Q] in
/-- Every WAFA has an equivalent nice, equalized,
purely polynomial WAFA.
-/
theorem exists_nice_equalized_equiv [Finite Q] [Finite Alph] (A : WAFA S Q Alph) :
    ∃ (Q' : Type) (_ : Fintype Q') (A' : WAFA S Q' Alph),
      A'.IsNice ∧ A'.IsPurelyPolynomial ∧ A'.IsEqualized ∧ A'.behavior = A.behavior := by
  classical
  have := Fintype.ofFinite Q
  have := Fintype.ofFinite Alph
  obtain ⟨Q₁, _, A₁, hnice₁, hpp₁, hbeh₁⟩ := exists_nice_purelyPolynomial_equiv A
  obtain ⟨q₀, hq₀⟩ := hnice₁.2.2
  let degOf : Q₁ × Alph → ℕ := fun p =>
    (A₁.δ p.1 p.2).support.sup monomialDegree
  let d : ℕ := max 1 (Finset.univ.sup degOf)
  have hd_pos : 1 ≤ d := le_max_left _ _
  have hd_ge : ∀ q a, ∀ m ∈ (A₁.δ q a).support, monomialDegree m ≤ d := by
    intro q a m hm
    exact (Finset.le_sup (f := monomialDegree) hm).trans
      ((Finset.le_sup (f := degOf) (Finset.mem_univ (q, a))).trans (le_max_right _ _))
  let B := equalizeAt A₁ q₀ d
  have hinj : ∀ (q : Q₁) (a : Alph) (m₁ m₂ : Q₁ →₀ ℕ),
      m₁.mapDomain some + Finsupp.single none (d - monomialDegree m₁) =
        m₂.mapDomain some + Finsupp.single none (d - monomialDegree m₂) → m₁ = m₂ := by
    intro q a m₁ m₂ heq
    ext p
    have hval := congrArg (fun f : Option Q₁ →₀ ℕ => f (some p)) heq
    have hne : (some p : Option Q₁) ≠ none := Option.some_ne_none p
    simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hne, add_zero] at hval
    have hmap : ∀ (m : Q₁ →₀ ℕ), (m.mapDomain some) (some p) = m p := fun m => by
      simp [Option.some_injective]
    rw [hmap, hmap] at hval
    exact hval
  have hcoeff_B : ∀ (q : Q₁) (a : Alph) (k : Option Q₁ →₀ ℕ),
      (B.δ (some q) a).coeff k =
        if h : ∃ m ∈ (A₁.δ q a).support,
            k = m.mapDomain some + Finsupp.single none (d - monomialDegree m)
        then (A₁.δ q a).coeff h.choose
        else 0 := by
    intro q a k
    simp only [B, equalizeAt, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    split_ifs with h
    · let m₀ := h.choose
      have hm₀ : m₀ ∈ (A₁.δ q a).support ∧
          k = m₀.mapDomain some + Finsupp.single none (d - monomialDegree m₀) := h.choose_spec
      rw [Finset.sum_eq_single m₀]
      · split_ifs with heq
        · rfl
        · exact absurd hm₀.2.symm heq
      · intro m _ hne
        split_ifs with heq
        · exact absurd (hinj q a m m₀ (heq.trans hm₀.2)) hne
        · rfl
      · intro hnot; exact absurd hm₀.1 hnot
    · refine Finset.sum_eq_zero (fun m hm => ?_)
      split_ifs with heq
      · exact absurd ⟨m, hm, heq.symm⟩ h
      · rfl
  have hB_deg : ∀ q a, ∀ k ∈ (B.δ q a).support, monomialDegree k = d := by
    intro q a k hk
    cases q with
    | some q =>
      rw [MvPolynomial.mem_support_iff, hcoeff_B] at hk
      split_ifs at hk with h
      · obtain ⟨m, hm, rfl⟩ := h
        rw [monomialDegree_add, monomialDegree_single]
        have hmap : monomialDegree (m.mapDomain (some : Q₁ → Option Q₁)) = monomialDegree m := by
          simp only [monomialDegree]
          exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)
        rw [hmap]
        have hle := hd_ge q a m hm
        omega
      · exact absurd rfl hk
    | none =>
      have hX : (MvPolynomial.X (none : Option Q₁) ^ d : MvPolynomial (Option Q₁) S) =
          MvPolynomial.monomial (Finsupp.single none d) 1 := by
        rw [MvPolynomial.X_pow_eq_monomial]
      simp only [B, equalizeAt, hX, MvPolynomial.mem_support_iff,
        MvPolynomial.coeff_monomial] at hk
      split_ifs at hk with h
      · rw [← h, monomialDegree_single]
      · exact absurd rfl hk
  have hB_nice : B.IsNice := by
    refine ⟨?_, ?_, ⟨some q₀, rfl⟩⟩
    · simp only [B, equalizeAt, MvPolynomial.coeff_X]
      have hne : Finsupp.single (some q₀) 1 ≠ 0 := Finsupp.single_ne_zero.mpr Nat.one_ne_zero
      simp [hne]
    · intro q a
      by_contra hne
      have hmem : (0 : Option Q₁ →₀ ℕ) ∈ (B.δ q a).support :=
        MvPolynomial.mem_support_iff.mpr hne
      have hdeg := hB_deg q a 0 hmem
      simp only [monomialDegree_zero] at hdeg
      omega
  have hB_pp : B.IsPurelyPolynomial := by
    refine ⟨?_, ?_⟩
    · intro m hm
      simp only [B, equalizeAt, MvPolynomial.mem_support_iff, MvPolynomial.coeff_X] at hm ⊢
      split_ifs at hm ⊢ with h
      · rfl
      · exact absurd rfl hm
    · intro q a k hk
      cases q with
      | some q =>
        rw [MvPolynomial.mem_support_iff, hcoeff_B] at hk
        rw [hcoeff_B]
        split_ifs at hk ⊢ with h
        · exact hpp₁.2 q a _ h.choose_spec.1
        · exact absurd rfl hk
      | none =>
        have hX : (MvPolynomial.X (none : Option Q₁) ^ d : MvPolynomial (Option Q₁) S) =
            MvPolynomial.monomial (Finsupp.single none d) 1 := by
          rw [MvPolynomial.X_pow_eq_monomial]
        simp only [B, equalizeAt, hX, MvPolynomial.mem_support_iff,
          MvPolynomial.coeff_monomial] at hk ⊢
        split_ifs at hk ⊢ with h
        · rfl
        · exact absurd rfl hk
  exact ⟨Option Q₁, inferInstance, B, hB_nice, hB_pp, ⟨d, hd_pos, hB_deg⟩,
    (behavior_equalizeAt hq₀ d).trans hbeh₁⟩

end WAFA

/-! ### Polynomial Automata (PA) and Reversal Equivalence -/

/-- A polynomial automaton (PA) with `n` states over commutative semiring `S` and alphabet `Σ`. -/
@[ext]
structure PolynomialAutomaton (S : Type u) [CommSemiring S] (n : ℕ) (Alph : Type w) where
  /-- Initial weight vector `α ∈ S^n`. -/
  init : Fin n → S
  /-- Transition polynomials `p_i(a) ∈ S[X_n]`. -/
  trans : Alph → Fin n → MvPolynomial (Fin n) S
  /-- Output polynomial `γ ∈ S[X_n]`. -/
  output : MvPolynomial (Fin n) S

namespace PolynomialAutomaton

variable {S : Type u} [CommSemiring S] {n : ℕ} {Alph : Type w}

/-- Auxiliary state behavior operating on the reversed word so that appending `a` on the right
is structural recursion. -/
@[expose] noncomputable def stateBehaviorRev (A : PolynomialAutomaton S n Alph) :
    List Alph → Fin n → S
  | [], i => A.init i
  | a :: u, i => MvPolynomial.eval (A.stateBehaviorRev u) (A.trans a i)

/-- State behavior `[A](i, w)` of a polynomial automaton, reading `w` left-to-right. -/
@[expose] noncomputable def stateBehavior (A : PolynomialAutomaton S n Alph) (w : List Alph)
    (i : Fin n) : S :=
  A.stateBehaviorRev w.reverse i

@[simp] theorem stateBehavior_nil (A : PolynomialAutomaton S n Alph) (i : Fin n) :
    A.stateBehavior [] i = A.init i := rfl

@[simp] theorem stateBehavior_append_singleton (A : PolynomialAutomaton S n Alph) (v : List Alph)
    (a : Alph) (i : Fin n) :
    A.stateBehavior (v ++ [a]) i = MvPolynomial.eval (A.stateBehavior v) (A.trans a i) := by
  simp only [stateBehavior, List.reverse_append, List.reverse_singleton, List.singleton_append,
    stateBehaviorRev]
  rfl

/-- Behavior `[[A]](w) = γ([A]_1(w), ..., [A]_n(w))` of a polynomial automaton. -/
@[expose] noncomputable def behavior (A : PolynomialAutomaton S n Alph) : List Alph → S :=
  fun w => MvPolynomial.eval (A.stateBehavior w) A.output

@[simp] theorem behavior_apply (A : PolynomialAutomaton S n Alph) (w : List Alph) :
    A.behavior w = MvPolynomial.eval (A.stateBehavior w) A.output := rfl

/-- Convert a WAFA on `Fin n` into the corresponding PA recognizing the reversed series. -/
@[expose] def ofWAFA (A : WAFA S (Fin n) Alph) : PolynomialAutomaton S n Alph where
  init := A.final
  trans a i := A.δ i a
  output := A.init

/-- Convert a PA with `n` states into the corresponding WAFA recognizing the reversed series. -/
@[expose] def toWAFA (A : PolynomialAutomaton S n Alph) : WAFA S (Fin n) Alph where
  δ i a := A.trans a i
  init := A.output
  final := A.init

theorem stateBehaviorRev_ofWAFA (A : WAFA S (Fin n) Alph) (w : List Alph) (i : Fin n) :
    (ofWAFA A).stateBehaviorRev w i = A.stateBehavior i w := by
  induction w generalizing i with
  | nil => rfl
  | cons a v ih =>
    simp only [stateBehaviorRev, WAFA.stateBehavior_cons, ofWAFA]
    congr
    funext p
    exact ih p

theorem behavior_ofWAFA (A : WAFA S (Fin n) Alph) :
    (ofWAFA A).behavior = reverseSeries A.behavior := by
  funext w
  rw [behavior_apply, reverseSeries_apply, WAFA.behavior_apply]
  have hout : (ofWAFA A).output = A.init := rfl
  rw [hout]
  congr
  funext p
  exact stateBehaviorRev_ofWAFA A w.reverse p

theorem behavior_toWAFA (A : PolynomialAutomaton S n Alph) :
    A.toWAFA.behavior = reverseSeries A.behavior := by
  have h : ofWAFA A.toWAFA = A := by ext <;> rfl
  funext w
  have h1 := congrFun (behavior_ofWAFA A.toWAFA) w.reverse
  rw [h] at h1
  simpa [reverseSeries_apply] using h1.symm

end PolynomialAutomaton

/-- A weighted word language `s : List Σ → S` is recognized by a polynomial automaton. -/
@[expose] def IsPARecognizable {S : Type u} [CommSemiring S] {Alph : Type w}
    (s : List Alph → S) : Prop :=
  ∃ (n : ℕ) (A : PolynomialAutomaton S n Alph), A.behavior = s

/-- A weighted language `s` is recognized
by a WAFA if and only if its reversal `s^R` is recognized by a polynomial automaton.
-/
theorem isWAFARecognizable_iff_reverse_isPARecognizable {S : Type u} [CommSemiring S]
    {Alph : Type w} (s : List Alph → S) :
    IsWAFARecognizable s ↔ IsPARecognizable (reverseSeries s) := by
  constructor
  · rintro ⟨Q, _, A, rfl⟩
    let n := Fintype.card Q
    let e : Q ≃ Fin n := Fintype.equivFin Q
    refine ⟨n, PolynomialAutomaton.ofWAFA (A.mapStates e), ?_⟩
    rw [PolynomialAutomaton.behavior_ofWAFA, WAFA.behavior_mapStates]
  · rintro ⟨n, A, hA⟩
    refine ⟨Fin n, inferInstance, A.toWAFA, ?_⟩
    rw [PolynomialAutomaton.behavior_toWAFA, hA, reverseSeries_reverseSeries]

end CslibFrontier
