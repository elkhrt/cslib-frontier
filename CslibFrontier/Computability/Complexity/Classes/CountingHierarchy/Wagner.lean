module

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Mathlib.Algebra.Polynomial.Eval.Defs

import Cslib.Foundations.Data.Polynomial.Monotone
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.Deterministic
import CslibFrontier.Computability.Complexity.Classes.PP.Closure
import CslibFrontier.Computability.Complexity.Classes.PP.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.TruncatedVerifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.OutputLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Partial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Foundations.Data.BitString.WordCount
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Data.Fintype.Pi

/-!
# Wagner Counting Hierarchy and Equivalence with Oracle Counting Levels

This module defines the counting hierarchy via iterated majority counting operators (`countingOp`,
`CHLevel`, `CH`), establishes closure under polynomial-time many-one reductions, complement,
tagged unions, polynomial-time conditionals, existential/universal quantification, and strict
majority, and proves Torán's equivalence between the counting-operator definition and the
oracle-based counting hierarchy `⋃ a, CountingLevel a encBits`.

## Main definitions

* `CslibFrontier.Complexity.countingOp`: majority counting operator `C.K` on bitstring languages.
* `CslibFrontier.Complexity.CHLevel`: `i`-th level `C_i P` of the counting-operator hierarchy.
* `CslibFrontier.Complexity.CH`: union `⋃ i, CHLevel i`.

## Main results

* `CslibFrontier.Complexity.PolyTimeReducible.mem_CHLevel`, `compl_mem_CHLevel`,
  `taggedUnion_mem_CHLevel`, `ite_mem_CHLevel`: closure properties of each level.
* `CslibFrontier.Complexity.exists_bits_mem_CHLevel`, `forall_bits_mem_CHLevel`,
  `strictMajority_mem_CHLevel`: quantifier and strict-majority stepping lemmas.
* `CslibFrontier.Complexity.PWithOracle_subset_CHLevel`, `PPWithOracle_subset_CHLevel`:
  simulation of relativized `P` and `PP` inside `CHLevel`.
* `CslibFrontier.Complexity.CH_eq_iUnion_CountingLevel`: `CH = ⋃ a, CountingLevel a encBits`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM Turing.MultiTapeMachine Turing.MultiTapePTM

open Classical in
/-- Majority counting operator `C.K`: a language `A` belongs to `countingOp K` when there exist
`B ∈ K` and a polynomial `p` such that `x ∈ A` iff at least half of all `y ∈ {0, 1}^{p(|x|)}`
satisfy `(x, y) ∈ B`. -/
def countingOp (K : Set (Set (List Bool))) : Set (Set (List Bool)) :=
  {A | ∃ B ∈ K, ∃ p : Polynomial ℕ,
    ∀ x : List Bool, x ∈ A ↔
      2 ^ p.eval x.length ≤
        2 * (Finset.univ.filter fun y : Fin (p.eval x.length) → Bool ↦
          encPair encBits encBits (x, List.ofFn y) ∈ B).card}

/-- The `i`-th level `C_i P` of the counting-operator hierarchy. -/
def CHLevel : ℕ → Set (Set (List Bool))
  | 0 => P encBits
  | i + 1 => countingOp (CHLevel i)

/-- The counting hierarchy `CH = ⋃ i, C_i P`. -/
def CH : Set (Set (List Bool)) :=
  ⋃ i, CHLevel i

/-- The zeroth level of the counting hierarchy is `P`. -/
@[simp] theorem CHLevel_zero : CHLevel 0 = P encBits := by
  rfl

/-- Each successor level applies `countingOp`. -/
@[simp] theorem CHLevel_succ (i : ℕ) : CHLevel (i + 1) = countingOp (CHLevel i) := by
  rfl

open Classical in
/-- Membership characterization for `countingOp`. -/
theorem mem_countingOp_iff {K : Set (Set (List Bool))} {A : Set (List Bool)} :
    A ∈ countingOp K ↔ ∃ B ∈ K, ∃ p : Polynomial ℕ,
      ∀ x : List Bool, x ∈ A ↔
        2 ^ p.eval x.length ≤
          2 * (Finset.univ.filter fun y : Fin (p.eval x.length) → Bool ↦
            encPair encBits encBits (x, List.ofFn y) ∈ B).card :=
  Iff.rfl

/-- Membership characterization for `CH`. -/
theorem mem_CH_iff {A : Set (List Bool)} : A ∈ CH ↔ ∃ i, A ∈ CHLevel i := by
  change A ∈ ⋃ i, CHLevel i ↔ _
  exact Set.mem_iUnion

/-! ### Elementary cardinality and encoding helpers -/

/-- Strict-pair partial decoder for `encPair encBits encBits`. -/
private def pairBitsDecoder : PartialDecoder (encPair encBits encBits) :=
  PartialDecoder.pair (PartialDecoder.ofDecoder Decoder.bits)
    (PartialDecoder.ofDecoder Decoder.bits)

/-- Strict triple partial decoder for `encPair (encPair encBits encBits) encBits`. -/
private def tripleBitsDecoder :
    PartialDecoder (encPair (encPair encBits encBits) encBits) :=
  PartialDecoder.pair pairBitsDecoder (PartialDecoder.ofDecoder Decoder.bits)

/-- Pointwise-equivalent predicates give equal filtered cardinalities for any two `Decidable`
instances. -/
private theorem card_filter_congr_dec {α : Type*} [Fintype α] {P Q : α → Prop}
    {instP : DecidablePred P} {instQ : DecidablePred Q} (h : ∀ a, P a ↔ Q a) :
    (@Finset.filter _ P instP Finset.univ).card = (@Finset.filter _ Q instQ Finset.univ).card := by
  congr 1; ext a; simp [h a]

private abbrev card_filter_congr_iff {α : Type*} [Fintype α] {P Q : α → Prop}
    {instP : DecidablePred P} [DecidablePred Q] (h : ∀ a, P a ↔ Q a) :=
  card_filter_congr_dec (instP := instP) (instQ := ‹_›) h

/-- Nested bitstring pairing equals `encPair (encPair encBits encBits) encBits`. -/
private theorem encPair_encPair_eq (x w u : List Bool) :
    encPair encBits encBits (encPair encBits encBits (x, w), u) =
      encPair (encPair encBits encBits) encBits ((x, w), u) := by
  simp only [encPair_apply, encBits_apply]

/-- Composing a strict `PartialDecoder` with a polynomial-time function and default fallback. -/
private theorem partialDecoder_optionElim {α β : Type} {enc : α ↪ List Bool}
    {encB : β ↪ List Bool} (D : PartialDecoder enc) (d : β) {f : α → β}
    (hf : ComputableInPolyTime f enc encB) :
    ComputableInPolyTime (fun z ↦ (D.decode z).elim d f) encBits encB :=
  D.computable.optionElimWithInput (ComputableInPolyTime.const d)
    (hf.comp (ComputableInPolyTime.snd encBits enc))

/-- Taking a prefix of length `k ≤ K` scales the filtered bitstring cardinality by `2 ^ (K - k)`. -/
private theorem card_filter_take_eq {k K : ℕ} (hk : k ≤ K) (P : List Bool → Prop)
    [DecidablePred P] :
    (Finset.univ.filter fun y : Fin K → Bool ↦ P ((List.ofFn y).take k)).card =
      2 ^ (K - k) * (Finset.univ.filter fun y : Fin k → Bool ↦ P (List.ofFn y)).card := by
  have h := acceptCount_eq_two_pow_mul_of_take (V := fun q : Unit × List Bool ↦ decide (P q.2))
    (V' := fun q : Unit × List Bool ↦ decide (P (q.2.take k))) (a := ()) (b := ()) hk
    (fun _ ↦ rfl)
  simp only [acceptCount, decide_eq_true_eq] at h
  exact (card_filter_congr_iff fun _ ↦ Iff.rfl).trans
    (h.trans (congrArg (2 ^ (K - k) * ·) (card_filter_congr_iff fun _ ↦ Iff.rfl)))

/-- Taking a prefix of length `k ≤ K` preserves the nonstrict majority inequality. -/
private theorem nonstrictMajority_take_iff {k K : ℕ} (hk : k ≤ K) (P : List Bool → Prop)
    [DecidablePred P] :
    (2 ^ K ≤ 2 * (Finset.univ.filter fun y : Fin K → Bool ↦ P ((List.ofFn y).take k)).card) ↔
      (2 ^ k ≤ 2 * (Finset.univ.filter fun y : Fin k → Bool ↦ P (List.ofFn y)).card) := by
  rw [card_filter_take_eq hk P, ← pow_sub_mul_pow 2 hk, mul_left_comm 2]
  exact Nat.mul_le_mul_left_iff (by positivity)

/-- Splitting an `(m + 1)`-bit filter by its leading bit. -/
private theorem card_filter_succ_split (m : ℕ) (P : List Bool → Prop) [DecidablePred P] :
    (Finset.univ.filter fun y : Fin (m + 1) → Bool ↦ P (List.ofFn y)).card =
      (Finset.univ.filter fun y : Fin m → Bool ↦ P (false :: List.ofFn y)).card +
      (Finset.univ.filter fun y : Fin m → Bool ↦ P (true :: List.ofFn y)).card := by
  have h := acceptCount_add (V := fun q : Unit × List Bool ↦ decide (P q.2)) () 1 m
  have h1 : 1 + m = m + 1 := Nat.add_comm 1 m
  rw [h1] at h
  simp only [acceptCount, decide_eq_true_eq] at h
  rw [card_filter_congr_iff (Q := fun y : Fin (m + 1) → Bool ↦ P (List.ofFn y)) (fun _ ↦ Iff.rfl)]
  rw [h]
  let e : (Fin 1 → Bool) ≃ Bool :=
    { toFun := fun f ↦ f 0
      invFun := fun b _ ↦ b
      left_inv := fun f ↦ funext fun i ↦ by fin_cases i; rfl
      right_inv := fun _ ↦ rfl }
  rw [← e.symm.sum_comp, Fintype.sum_bool, add_comm]
  refine congrArg₂ (· + ·) ?_ ?_ <;>
    · apply card_filter_congr_iff; intro y; simp [e, List.ofFn_succ]

/-- Count of `m`-bit strings (`m ≥ 1`) starting with `false` and containing at least one `true`. -/
private theorem card_filter_headFalse_anyTrue {m : ℕ} (hm : 1 ≤ m) :
    (Finset.univ.filter fun y : Fin m → Bool ↦
      (List.ofFn y).headD true = false ∧ (List.ofFn y).any id = true).card =
      2 ^ (m - 1) - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [card_filter_succ_split k (P := fun w ↦ w.headD true = false ∧ w.any id = true)]
  have htrue : (Finset.univ.filter fun y : Fin k → Bool ↦
      (true :: List.ofFn y).headD true = false ∧ (true :: List.ofFn y).any id = true).card = 0 := by
    simp
  rw [htrue, add_zero]
  have hfalse : (Finset.univ.filter fun y : Fin k → Bool ↦
      (false :: List.ofFn y).headD true = false ∧ (false :: List.ofFn y).any id = true) =
      Finset.univ.erase (fun _ : Fin k ↦ false) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.headD_cons, List.any_cons,
      id_eq, Bool.false_or, List.any_eq_true, List.mem_ofFn, exists_exists_eq_and,
      Finset.mem_erase, ne_eq, funext_iff, not_forall, Bool.not_eq_false, and_true]
  rw [hfalse, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

/-- Count of `m`-bit strings containing at least one `true`. -/
private theorem card_filter_anyTrue (m : ℕ) :
    (Finset.univ.filter fun y : Fin m → Bool ↦ (List.ofFn y).any id = true).card = 2 ^ m - 1 := by
  have heq : (Finset.univ.filter fun y : Fin m → Bool ↦ (List.ofFn y).any id = true) =
      Finset.univ.erase (fun _ : Fin m ↦ false) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.any_eq_true, List.mem_ofFn,
      exists_exists_eq_and, id_eq, Finset.mem_erase, ne_eq, funext_iff, not_forall,
      Bool.not_eq_false, and_true]
  rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

/-- Count of `m`-bit strings (`m ≥ 1`) starting with `false` or being all-`true`. -/
private theorem card_filter_headFalse_or_allTrue {m : ℕ} (hm : 1 ≤ m) :
    (Finset.univ.filter fun y : Fin m → Bool ↦
      (List.ofFn y).headD true = false ∨ (List.ofFn y).all id = true).card =
      2 ^ (m - 1) + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [card_filter_succ_split k (P := fun w ↦ w.headD true = false ∨ w.all id = true)]
  have hfalse : (Finset.univ.filter fun y : Fin k → Bool ↦
      (false :: List.ofFn y).headD true = false ∨ (false :: List.ofFn y).all id = true).card =
      2 ^ k := by
    simp
  have htrue : (Finset.univ.filter fun y : Fin k → Bool ↦
      (true :: List.ofFn y).headD true = false ∨ (true :: List.ofFn y).all id = true) =
      {fun _ : Fin k ↦ true} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.headD_cons, Bool.true_eq_false,
      List.all_cons, id_eq, Bool.true_and, false_or, List.all_eq_true, List.mem_ofFn,
      forall_exists_index, forall_apply_eq_imp_iff, Finset.mem_singleton, funext_iff]
  rw [hfalse, htrue, Finset.card_singleton]
  simp

/-- Polynomial-time computability of `List.any id` on `encBits`. -/
private theorem computableInPolyTime_bitsAny :
    ComputableInPolyTime (fun w : List Bool ↦ w.any id) encBits encBool := by
  have h := ComputableInPolyTime.foldl' (encA := encBool) (encL := encBits) (encB := encBool)
    (list := fun w : List Bool ↦ w) (init := fun _ ↦ false) (step := fun a b ↦ a || b)
    ComputableInPolyTime.id' (ComputableInPolyTime.const false) (by fun_prop)
    (B := fun _ ↦ 1) (PolyBounded.of_forall_le 1 0 fun _ ↦ by simp)
    (fun _ _ _ ↦ by simp [encBool_apply])
  have heq : (fun w : List Bool ↦ w.foldl (fun a b ↦ a || b) false) = fun w ↦ w.any id := by
    funext w
    induction w with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.foldl_cons, Bool.false_or, List.any_cons, id_eq]
      cases b with
      | false => exact ih
      | true =>
        simp only [Bool.true_or]
        clear ih
        induction bs with
        | nil => rfl
        | cons _ _ ih' => simpa using ih'
  rwa [heq] at h

/-- Polynomial-time computability of `List.all id` on `encBits`. -/
private theorem computableInPolyTime_bitsAll :
    ComputableInPolyTime (fun w : List Bool ↦ w.all id) encBits encBool := by
  have h := ComputableInPolyTime.foldl' (encA := encBool) (encL := encBits) (encB := encBool)
    (list := fun w : List Bool ↦ w) (init := fun _ ↦ true) (step := fun a b ↦ a && b)
    ComputableInPolyTime.id' (ComputableInPolyTime.const true) (by fun_prop)
    (B := fun _ ↦ 1) (PolyBounded.of_forall_le 1 0 fun _ ↦ by simp)
    (fun _ _ _ ↦ by simp [encBool_apply])
  have heq : (fun w : List Bool ↦ w.foldl (fun a b ↦ a && b) true) = fun w ↦ w.all id := by
    funext w
    induction w with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.foldl_cons, Bool.true_and, List.all_cons, id_eq]
      cases b with
      | true => exact ih
      | false =>
        simp only [Bool.false_and]
        clear ih
        induction bs with
        | nil => rfl
        | cons _ _ ih' => simpa using ih'
  rwa [heq] at h

/-- Polynomial-time computability of `w.count true` in unary on `encBits`. -/
private theorem computableInPolyTime_bitsCountTrue :
    ComputableInPolyTime (fun w : List Bool ↦ w.count true) encBits encUnary := by
  have hstep : ComputableInPolyTime (fun p : ℕ × Bool ↦ p.1 + p.2.toNat)
      (encPair encUnary encBool) encUnary := by fun_prop
  have h := ComputableInPolyTime.foldl' (encA := encBool) (encL := encBits) (encB := encUnary)
    (list := fun w : List Bool ↦ w) (init := fun _ ↦ 0) (step := fun acc b ↦ acc + b.toNat)
    ComputableInPolyTime.id' (ComputableInPolyTime.const 0) hstep
    (B := fun w ↦ w.length) (PolyBounded.of_forall_le 1 1 fun w ↦ by simp)
    (fun w i _ ↦ by
      simp only [encUnary_apply, List.length_replicate]
      have hfold : ∀ (l : List Bool) (a : ℕ),
          l.foldl (fun acc b ↦ acc + b.toNat) a ≤ a + l.length := by
        intro l
        induction l with
        | nil => intro a; simp
        | cons b bs ih =>
          intro a
          simp only [List.foldl_cons, List.length_cons]
          have := ih (a + b.toNat)
          cases b <;> simp at this ⊢ <;> omega
      exact (hfold (w.take i) 0).trans (by simp))
  have heq : (fun w : List Bool ↦ w.foldl (fun acc b ↦ acc + b.toNat) 0) =
      fun w ↦ w.count true := by
    funext w
    have hgen : ∀ (l : List Bool) (a : ℕ),
        l.foldl (fun acc b ↦ acc + b.toNat) a = a + l.count true := by
      intro l
      induction l with
      | nil => intro a; simp
      | cons b bs ih =>
        intro a
        simp only [List.foldl_cons, List.count_cons, ih]
        cases b
        · simp
        · simp; omega
    simpa using hgen w 0
  rwa [heq] at h

/-! ### Closure properties of Wagner's levels `CHLevel` -/

/-- The empty language belongs to every level `CHLevel k`. -/
theorem empty_mem_CHLevel (k : ℕ) : (∅ : Set (List Bool)) ∈ CHLevel k := by
  induction k with
  | zero => rw [CHLevel_zero]; exact empty_mem_P
  | succ k ih =>
    rw [CHLevel_succ, mem_countingOp_iff]
    refine ⟨∅, ih, 0, fun x ↦ ?_⟩
    simp

/-- The universal language belongs to every level `CHLevel k`. -/
theorem univ_mem_CHLevel (k : ℕ) : (Set.univ : Set (List Bool)) ∈ CHLevel k := by
  induction k with
  | zero =>
    rw [CHLevel_zero]
    exact ⟨fun _ ↦ true, ComputableInPolyTime.const true, fun _ ↦ by simp⟩
  | succ k ih =>
    rw [CHLevel_succ, mem_countingOp_iff]
    refine ⟨Set.univ, ih, 0, fun x ↦ ?_⟩
    simp

/-- Every level `CHLevel k` is closed under polynomial-time many-one reductions. -/
theorem PolyTimeReducible.mem_CHLevel {k : ℕ} {A B : Set (List Bool)}
    (h : PolyTimeReducible encBits encBits A B) (hB : B ∈ CHLevel k) : A ∈ CHLevel k := by
  induction k generalizing A B with
  | zero =>
    rw [CHLevel_zero] at hB ⊢
    exact h.mem_P hB
  | succ k ih =>
    rw [CHLevel_succ, mem_countingOp_iff] at hB ⊢
    obtain ⟨f, hf, hAB⟩ := h
    obtain ⟨C, hC, p, hBC⟩ := hB
    by_cases hCuniv : C = Set.univ
    · have hAuniv : A = Set.univ := by
        ext x
        simp only [Set.mem_univ, iff_true]
        rw [hAB x, hBC (f x), hCuniv]
        simp
      rw [hAuniv]
      have hu := univ_mem_CHLevel (k + 1)
      rwa [CHLevel_succ, mem_countingOp_iff] at hu
    · obtain ⟨w₀, hw₀⟩ := Set.nonempty_compl.mpr hCuniv
      obtain ⟨q, hpq⟩ := hf.exists_polynomial_eval_length_le p
      simp only [encBits_apply] at hpq
      let g : List Bool → List Bool := fun w ↦
        (pairBitsDecoder.decode w).elim w₀ fun xy ↦
          encPair encBits encBits (f xy.1, xy.2.take (p.eval (f xy.1).length))
      have hg : ComputableInPolyTime g encBits encBits := by
        refine pairBitsDecoder.computable.optionElimWithInput (ComputableInPolyTime.const w₀) ?_
        have h1 : ComputableInPolyTime (fun z : List Bool × (List Bool × List Bool) ↦ f z.2.1)
            (encPair encBits (encPair encBits encBits)) encBits :=
          hf.comp ((ComputableInPolyTime.fst encBits encBits).comp
            (ComputableInPolyTime.snd encBits (encPair encBits encBits)))
        have hlen : ComputableInPolyTime
            (fun z : List Bool × (List Bool × List Bool) ↦ p.eval (f z.2.1).length)
            (encPair encBits (encPair encBits encBits)) encUnary :=
          (ComputableInPolyTime.unary_eval p).comp
            ((ComputableInPolyTime.encoding_length encBits).comp h1)
        have h2 : ComputableInPolyTime
            (fun z : List Bool × (List Bool × List Bool) ↦
              z.2.2.take (p.eval (f z.2.1).length))
            (encPair encBits (encPair encBits encBits)) encBits :=
          ComputableInPolyTime.bitsTakeWithInput
            ((ComputableInPolyTime.snd encBits encBits).comp
              (ComputableInPolyTime.snd encBits (encPair encBits encBits))) hlen
        exact (h1.prod h2).of_enc_eq fun _ ↦ rfl
      let C' : Set (List Bool) := g ⁻¹' C
      have hC' : C' ∈ CHLevel k := ih ⟨g, hg, fun _ ↦ Iff.rfl⟩ hC
      refine ⟨C', hC', q, fun x ↦ ?_⟩
      rw [hAB x, hBC (f x)]
      have hiff : ∀ y : List Bool,
          encPair encBits encBits (x, y) ∈ C' ↔
            encPair encBits encBits (f x, y.take (p.eval (f x).length)) ∈ C := by
        intro y
        change g (encPair encBits encBits (x, y)) ∈ C ↔ _
        simp only [g, PartialDecoder.decode_enc, Option.elim_some]
      classical
      rw [card_filter_congr_iff (Q := fun y : Fin (q.eval x.length) → Bool ↦
        encPair encBits encBits (f x, (List.ofFn y).take (p.eval (f x).length)) ∈ C)
        (fun y ↦ hiff (List.ofFn y))]
      rw [card_filter_congr_iff (Q := fun y : Fin (p.eval (f x).length) → Bool ↦
        encPair encBits encBits (f x, List.ofFn y) ∈ C) (fun _ ↦ Iff.rfl)]
      exact (nonstrictMajority_take_iff (hpq x) (fun u ↦ encPair encBits encBits (f x, u) ∈ C)).symm

/-- Every Wagner level embeds into the next. -/
theorem CHLevel_subset_succ (k : ℕ) : CHLevel k ⊆ CHLevel (k + 1) := by
  intro A hA
  by_cases hAuniv : A = Set.univ
  · rw [hAuniv]; exact univ_mem_CHLevel (k + 1)
  · obtain ⟨w₀, hw₀⟩ := Set.nonempty_compl.mpr hAuniv
    let g : List Bool → List Bool := fun w ↦ (pairBitsDecoder.decode w).elim w₀ Prod.fst
    have hg : ComputableInPolyTime g encBits encBits :=
      pairBitsDecoder.computable.optionElimWithInput (ComputableInPolyTime.const w₀)
        ((ComputableInPolyTime.fst encBits encBits).comp
          (ComputableInPolyTime.snd encBits (encPair encBits encBits)))
    rw [CHLevel_succ, mem_countingOp_iff]
    refine ⟨g ⁻¹' A, PolyTimeReducible.mem_CHLevel ⟨g, hg, fun _ ↦ Iff.rfl⟩ hA, 0, fun x ↦ ?_⟩
    classical
    have hcard : (Finset.univ.filter fun y : Fin (Polynomial.eval x.length 0) → Bool ↦
        encPair encBits encBits (x, List.ofFn y) ∈ g ⁻¹' A).card =
        if x ∈ A then 1 else 0 := by
      rw [card_filter_congr_iff (Q := fun _ : Fin (Polynomial.eval x.length 0) → Bool ↦ x ∈ A)
        (fun y ↦ by
          change g (encPair encBits encBits (x, List.ofFn y)) ∈ A ↔ x ∈ A
          simp only [g, PartialDecoder.decode_enc, Option.elim_some])]
      by_cases hx : x ∈ A <;> simp [hx]
    rw [card_filter_congr_iff (Q := fun y : Fin (Polynomial.eval x.length 0) → Bool ↦
      encPair encBits encBits (x, List.ofFn y) ∈ g ⁻¹' A) (fun _ ↦ Iff.rfl), hcard]
    simp only [Polynomial.eval_zero, pow_zero]
    split_ifs <;> simp_all

/-- Monotonicity of `CHLevel` in the hierarchy index. -/
theorem CHLevel_mono {a b : ℕ} (hab : a ≤ b) : CHLevel a ⊆ CHLevel b := by
  induction hab with
  | refl => exact Set.Subset.refl _
  | step _ ih => exact ih.trans (CHLevel_subset_succ _)

/-- `P` is contained in every level `CHLevel k`. -/
theorem P_subset_CHLevel (k : ℕ) : P encBits ⊆ CHLevel k := by
  rw [← CHLevel_zero]
  exact CHLevel_mono (Nat.zero_le k)

/-- Every level `CHLevel k` is closed under `taggedUnion`. -/
theorem taggedUnion_mem_CHLevel {k : ℕ} {A B : Set (List Bool)}
    (hA : A ∈ CHLevel k) (hB : B ∈ CHLevel k) : taggedUnion A B ∈ CHLevel k := by
  induction k generalizing A B with
  | zero =>
    rw [CHLevel_zero] at hA hB ⊢
    exact taggedUnion_mem_CountingLevel (a := 0) hA hB
  | succ k ih =>
    rw [CHLevel_succ, mem_countingOp_iff] at hA hB ⊢
    obtain ⟨A₀, hA₀, p₀, hAA₀⟩ := hA
    obtain ⟨B₀, hB₀, p₁, hBB₀⟩ := hB
    let U := taggedUnion A₀ B₀
    have hU : U ∈ CHLevel k := ih hA₀ hB₀
    by_cases hUuniv : U = Set.univ
    · have hAB : taggedUnion A B = Set.univ := by
        ext w
        simp only [Set.mem_univ, iff_true]
        change if w.headD false then w.tail ∈ B else w.tail ∈ A
        cases hw : w.headD false with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hAA₀ w.tail]
          have hmem : ∀ y, encPair encBits encBits (w.tail, y) ∈ A₀ := fun y ↦ by
            have := Set.eq_univ_iff_forall.mp hUuniv (false :: encPair encBits encBits (w.tail, y))
            simpa [U, taggedUnion] using this
          rw [card_filter_congr_iff (Q := fun _ : Fin (p₀.eval w.tail.length) → Bool ↦ True)
            (fun y ↦ iff_true_intro (hmem (List.ofFn y)))]
          simp only [Finset.filter_true, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin]
          omega
        | true =>
          simp only [↓reduceIte]
          rw [hBB₀ w.tail]
          have hmem : ∀ y, encPair encBits encBits (w.tail, y) ∈ B₀ := fun y ↦ by
            have := Set.eq_univ_iff_forall.mp hUuniv (true :: encPair encBits encBits (w.tail, y))
            simpa [U, taggedUnion] using this
          rw [card_filter_congr_iff (Q := fun _ : Fin (p₁.eval w.tail.length) → Bool ↦ True)
            (fun y ↦ iff_true_intro (hmem (List.ofFn y)))]
          simp only [Finset.filter_true, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin]
          omega
      rw [hAB]
      have hu := univ_mem_CHLevel (k + 1)
      rwa [CHLevel_succ, mem_countingOp_iff] at hu
    · obtain ⟨w₀, hw₀⟩ := Set.nonempty_compl.mpr hUuniv
      let g : List Bool → List Bool := fun w ↦
        (pairBitsDecoder.decode w).elim w₀ fun xy ↦
          if xy.1.headD false then
            true :: encPair encBits encBits (xy.1.tail, xy.2.take (p₁.eval xy.1.tail.length))
          else
            false :: encPair encBits encBits (xy.1.tail, xy.2.take (p₀.eval xy.1.tail.length))
      have hg : ComputableInPolyTime g encBits encBits := by
        refine pairBitsDecoder.computable.optionElimWithInput (ComputableInPolyTime.const w₀) ?_
        have hx : ComputableInPolyTime (fun z : List Bool × (List Bool × List Bool) ↦ z.2.1)
            (encPair encBits (encPair encBits encBits)) encBits :=
          (ComputableInPolyTime.fst encBits encBits).comp
            (ComputableInPolyTime.snd encBits (encPair encBits encBits))
        have hy : ComputableInPolyTime (fun z : List Bool × (List Bool × List Bool) ↦ z.2.2)
            (encPair encBits (encPair encBits encBits)) encBits :=
          (ComputableInPolyTime.snd encBits encBits).comp
            (ComputableInPolyTime.snd encBits (encPair encBits encBits))
        have htail : ComputableInPolyTime
            (fun z : List Bool × (List Bool × List Bool) ↦ z.2.1.tail)
            (encPair encBits (encPair encBits encBits)) encBits :=
          ComputableInPolyTime.bitsTail.comp hx
        have hhead : ComputableInPolyTime
            (fun z : List Bool × (List Bool × List Bool) ↦ z.2.1.headD false)
            (encPair encBits (encPair encBits encBits)) encBool :=
          (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp hx
        have hlen1 : ComputableInPolyTime
            (fun z : List Bool × (List Bool × List Bool) ↦ p₁.eval z.2.1.tail.length)
            (encPair encBits (encPair encBits encBits)) encUnary :=
          (ComputableInPolyTime.unary_eval p₁).comp
            ((ComputableInPolyTime.encoding_length encBits).comp htail)
        have hlen0 : ComputableInPolyTime
            (fun z : List Bool × (List Bool × List Bool) ↦ p₀.eval z.2.1.tail.length)
            (encPair encBits (encPair encBits encBits)) encUnary :=
          (ComputableInPolyTime.unary_eval p₀).comp
            ((ComputableInPolyTime.encoding_length encBits).comp htail)
        have hbranch1 : ComputableInPolyTime
            (fun z : List Bool × (List Bool × List Bool) ↦
              true :: encPair encBits encBits (z.2.1.tail, z.2.2.take (p₁.eval z.2.1.tail.length)))
            (encPair encBits (encPair encBits encBits)) encBits :=
          ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true)
            ((htail.prod (ComputableInPolyTime.bitsTakeWithInput hy hlen1)).of_enc_eq fun _ ↦ rfl)
        have hbranch0 : ComputableInPolyTime
            (fun z : List Bool × (List Bool × List Bool) ↦
              false :: encPair encBits encBits (z.2.1.tail, z.2.2.take (p₀.eval z.2.1.tail.length)))
            (encPair encBits (encPair encBits encBits)) encBits :=
          ComputableInPolyTime.bitsCons (ComputableInPolyTime.const false)
            ((htail.prod (ComputableInPolyTime.bitsTakeWithInput hy hlen0)).of_enc_eq fun _ ↦ rfl)
        exact ComputableInPolyTime.ite' hhead hbranch1 hbranch0
      refine ⟨g ⁻¹' U, PolyTimeReducible.mem_CHLevel ⟨g, hg, fun _ ↦ Iff.rfl⟩ hU,
        p₀ + p₁, fun x ↦ ?_⟩
      have htail_le : x.tail.length ≤ x.length := by simp only [List.length_tail]; omega
      have hp0 : p₀.eval x.tail.length ≤ (p₀ + p₁).eval x.length := by
        rw [Polynomial.eval_add]
        exact (Polynomial.eval_mono p₀ htail_le).trans (Nat.le_add_right _ _)
      have hp1 : p₁.eval x.tail.length ≤ (p₀ + p₁).eval x.length := by
        rw [Polynomial.eval_add]
        exact (Polynomial.eval_mono p₁ htail_le).trans (Nat.le_add_left _ _)
      classical
      change (if x.headD false then x.tail ∈ B else x.tail ∈ A) ↔ _
      cases hx : x.headD false with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hAA₀ x.tail]
        have hiff : ∀ y : List Bool,
            encPair encBits encBits (x, y) ∈ g ⁻¹' U ↔
              encPair encBits encBits (x.tail, y.take (p₀.eval x.tail.length)) ∈ A₀ := by
          intro y
          change g (encPair encBits encBits (x, y)) ∈ U ↔ _
          simp only [g, PartialDecoder.decode_enc, Option.elim_some, hx, Bool.false_eq_true,
            ↓reduceIte, U, taggedUnion, Set.mem_ofPred_eq, List.headD_cons, List.tail_cons]
        rw [card_filter_congr_iff (Q := fun y : Fin ((p₀ + p₁).eval x.length) → Bool ↦
          encPair encBits encBits (x.tail, (List.ofFn y).take (p₀.eval x.tail.length)) ∈ A₀)
          (fun y ↦ hiff (List.ofFn y))]
        rw [card_filter_congr_iff (Q := fun y : Fin (p₀.eval x.tail.length) → Bool ↦
          encPair encBits encBits (x.tail, List.ofFn y) ∈ A₀) (fun _ ↦ Iff.rfl)]
        exact (nonstrictMajority_take_iff hp0
          (fun u ↦ encPair encBits encBits (x.tail, u) ∈ A₀)).symm
      | true =>
        simp only [↓reduceIte]
        rw [hBB₀ x.tail]
        have hiff : ∀ y : List Bool,
            encPair encBits encBits (x, y) ∈ g ⁻¹' U ↔
              encPair encBits encBits (x.tail, y.take (p₁.eval x.tail.length)) ∈ B₀ := by
          intro y
          change g (encPair encBits encBits (x, y)) ∈ U ↔ _
          simp only [g, PartialDecoder.decode_enc, Option.elim_some, hx, ↓reduceIte, U,
            taggedUnion, Set.mem_ofPred_eq, List.headD_cons, List.tail_cons]
        rw [card_filter_congr_iff (Q := fun y : Fin ((p₀ + p₁).eval x.length) → Bool ↦
          encPair encBits encBits (x.tail, (List.ofFn y).take (p₁.eval x.tail.length)) ∈ B₀)
          (fun y ↦ hiff (List.ofFn y))]
        rw [card_filter_congr_iff (Q := fun y : Fin (p₁.eval x.tail.length) → Bool ↦
          encPair encBits encBits (x.tail, List.ofFn y) ∈ B₀) (fun _ ↦ Iff.rfl)]
        exact (nonstrictMajority_take_iff hp1
          (fun u ↦ encPair encBits encBits (x.tail, u) ∈ B₀)).symm

/-- Polynomial-time conditional branching preserves every level `CHLevel k`. -/
theorem ite_mem_CHLevel {k : ℕ} {c : List Bool → Bool} {A B : Set (List Bool)}
    (hc : ComputableInPolyTime c encBits encBool) (hA : A ∈ CHLevel k) (hB : B ∈ CHLevel k) :
    {w | if c w then w ∈ A else w ∈ B} ∈ CHLevel k := by
  refine PolyTimeReducible.mem_CHLevel
    ⟨fun w ↦ c w :: w, ComputableInPolyTime.bitsCons hc ComputableInPolyTime.id', fun w ↦ ?_⟩
    (taggedUnion_mem_CHLevel hB hA)
  cases hw : c w <;> simp [taggedUnion, hw]

/-- Every level `CHLevel k` is closed under complement. -/
theorem compl_mem_CHLevel {k : ℕ} {A : Set (List Bool)} (hA : A ∈ CHLevel k) :
    Aᶜ ∈ CHLevel k := by
  induction k generalizing A with
  | zero =>
    rw [CHLevel_zero] at hA ⊢
    obtain ⟨f, hf, hAf⟩ := hA
    refine ⟨fun w ↦ !f w, ComputableInPolyTime.bool_not.comp hf, fun w ↦ ?_⟩
    simp [hAf w]
  | succ k ih =>
    rw [CHLevel_succ, mem_countingOp_iff] at hA ⊢
    obtain ⟨B, hB, p, hAB⟩ := hA
    let p' : Polynomial ℕ := p + 1
    have hp_le : ∀ n, p.eval n ≤ p'.eval n := fun n ↦ by simp [p']
    have hp'_pos : ∀ n, 1 ≤ p'.eval n := fun n ↦ by simp [p']
    by_cases hBc : Bᶜ = Set.univ
    · have hAempty : A = ∅ := by
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        rw [hAB x]
        have hBempty : B = ∅ := by
          ext w
          have := Set.eq_univ_iff_forall.mp hBc w
          simpa using this
        simp [hBempty]
      rw [hAempty, Set.compl_empty]
      have hu := univ_mem_CHLevel (k + 1)
      rwa [CHLevel_succ, mem_countingOp_iff] at hu
    · obtain ⟨w₀, hw₀⟩ := Set.nonempty_compl.mpr hBc
      let condBranch : List Bool → Bool := fun w ↦
        (pairBitsDecoder.decode w).elim false fun xy ↦ xy.2.headD false
      have hcond : ComputableInPolyTime condBranch encBits encBool :=
        pairBitsDecoder.computable.optionElimWithInput (ComputableInPolyTime.const false)
          ((ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp
            ((ComputableInPolyTime.snd encBits encBits).comp
              (ComputableInPolyTime.snd encBits (encPair encBits encBits))))
      let gFalse : List Bool → List Bool := fun w ↦
        (pairBitsDecoder.decode w).elim w₀ fun xy ↦
          encPair encBits encBits (xy.1, xy.2.tail.take (p.eval xy.1.length))
      have hgFalse : ComputableInPolyTime gFalse encBits encBits := by
        refine pairBitsDecoder.computable.optionElimWithInput (ComputableInPolyTime.const w₀) ?_
        have hx : ComputableInPolyTime (fun z : List Bool × (List Bool × List Bool) ↦ z.2.1)
            (encPair encBits (encPair encBits encBits)) encBits :=
          (ComputableInPolyTime.fst encBits encBits).comp
            (ComputableInPolyTime.snd encBits (encPair encBits encBits))
        have hy : ComputableInPolyTime (fun z : List Bool × (List Bool × List Bool) ↦ z.2.2.tail)
            (encPair encBits (encPair encBits encBits)) encBits :=
          ComputableInPolyTime.bitsTail.comp
            ((ComputableInPolyTime.snd encBits encBits).comp
              (ComputableInPolyTime.snd encBits (encPair encBits encBits)))
        have hlen : ComputableInPolyTime
            (fun z : List Bool × (List Bool × List Bool) ↦ p.eval z.2.1.length)
            (encPair encBits (encPair encBits encBits)) encUnary :=
          (ComputableInPolyTime.unary_eval p).comp
            ((ComputableInPolyTime.encoding_length encBits).comp hx)
        exact (hx.prod (ComputableInPolyTime.bitsTakeWithInput hy hlen)).of_enc_eq fun _ ↦ rfl
      let checkTrue : List Bool → Bool := fun w ↦
        (pairBitsDecoder.decode w).elim false fun xy ↦
          !(xy.2.tail.headD true) && xy.2.tail.any id
      have hcheckTrue : ComputableInPolyTime checkTrue encBits encBool := by
        refine pairBitsDecoder.computable.optionElimWithInput (ComputableInPolyTime.const false) ?_
        have hy : ComputableInPolyTime (fun z : List Bool × (List Bool × List Bool) ↦ z.2.2.tail)
            (encPair encBits (encPair encBits encBits)) encBits :=
          ComputableInPolyTime.bitsTail.comp
            ((ComputableInPolyTime.snd encBits encBits).comp
              (ComputableInPolyTime.snd encBits (encPair encBits encBits)))
        have h1 : ComputableInPolyTime
            (fun z : List Bool × (List Bool × List Bool) ↦ !(z.2.2.tail.headD true))
            (encPair encBits (encPair encBits encBits)) encBool :=
          ComputableInPolyTime.bool_not.comp
            ((ComputableInPolyTime.headD (encA := encBool) (encL := encBits) true).comp hy)
        have h2 : ComputableInPolyTime
            (fun z : List Bool × (List Bool × List Bool) ↦ z.2.2.tail.any id)
            (encPair encBits (encPair encBits encBits)) encBool :=
          computableInPolyTime_bitsAny.comp hy
        exact ComputableInPolyTime.bool_and' h1 h2
      let B' : Set (List Bool) :=
        {w | if condBranch w then w ∈ {u | checkTrue u = true} else w ∈ gFalse ⁻¹' Bᶜ}
      have hB' : B' ∈ CHLevel k :=
        ite_mem_CHLevel hcond
          (P_subset_CHLevel k ⟨checkTrue, hcheckTrue, fun _ ↦ Iff.rfl⟩)
          (PolyTimeReducible.mem_CHLevel ⟨gFalse, hgFalse, fun _ ↦ Iff.rfl⟩ (ih hB))
      refine ⟨B', hB', p' + 1, fun x ↦ ?_⟩
      classical
      have heval_add : (p' + 1).eval x.length = p'.eval x.length + 1 := by simp
      rw [heval_add]
      rw [card_filter_congr_iff (Q := fun y : Fin (p'.eval x.length + 1) → Bool ↦
        encPair encBits encBits (x, List.ofFn y) ∈ B') (fun _ ↦ Iff.rfl)]
      rw [card_filter_succ_split (p'.eval x.length)
        (P := fun y ↦ encPair encBits encBits (x, y) ∈ B')]
      have hleft : (Finset.univ.filter fun y : Fin (p'.eval x.length) → Bool ↦
          encPair encBits encBits (x, false :: List.ofFn y) ∈ B').card =
          (Finset.univ.filter fun y : Fin (p'.eval x.length) → Bool ↦
            encPair encBits encBits (x, (List.ofFn y).take (p.eval x.length)) ∈ Bᶜ).card := by
        apply card_filter_congr_iff
        intro y
        change (if condBranch (encPair encBits encBits (x, false :: List.ofFn y)) = true then _
          else gFalse (encPair encBits encBits (x, false :: List.ofFn y)) ∈ Bᶜ) ↔ _
        simp only [condBranch, gFalse, PartialDecoder.decode_enc, Option.elim_some,
          List.headD_cons, Bool.false_eq_true, ↓reduceIte, List.tail_cons]
      have hright : (Finset.univ.filter fun y : Fin (p'.eval x.length) → Bool ↦
          encPair encBits encBits (x, true :: List.ofFn y) ∈ B').card =
          2 ^ (p'.eval x.length - 1) - 1 := by
        rw [card_filter_congr_iff (Q := fun y : Fin (p'.eval x.length) → Bool ↦
          (List.ofFn y).headD true = false ∧ (List.ofFn y).any id = true) (fun y ↦ by
            change (if condBranch (encPair encBits encBits (x, true :: List.ofFn y)) = true then
              checkTrue (encPair encBits encBits (x, true :: List.ofFn y)) = true else _) ↔ _
            simp only [condBranch, checkTrue, PartialDecoder.decode_enc, Option.elim_some,
              List.headD_cons, ↓reduceIte, List.tail_cons, Bool.and_eq_true, Bool.not_eq_true'])]
        exact card_filter_headFalse_anyTrue (hp'_pos x.length)
      rw [hleft, hright]
      set m := p'.eval x.length
      have hm1 : 1 ≤ m := hp'_pos x.length
      set c := (Finset.univ.filter fun y : Fin m → Bool ↦
        encPair encBits encBits (x, (List.ofFn y).take (p.eval x.length)) ∈ B).card
      have hcompl_sum : (Finset.univ.filter fun y : Fin m → Bool ↦
          encPair encBits encBits (x, (List.ofFn y).take (p.eval x.length)) ∈ Bᶜ).card + c =
          2 ^ m := by
        have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
          (fun y : Fin m → Bool ↦
            encPair encBits encBits (x, (List.ofFn y).take (p.eval x.length)) ∈ B)
        have hcard_univ : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m := by simp
        rw [hcard_univ] at h
        have hce : (Finset.univ.filter fun y : Fin m → Bool ↦
            encPair encBits encBits (x, (List.ofFn y).take (p.eval x.length)) ∈ Bᶜ).card =
            (Finset.univ.filter fun y : Fin m → Bool ↦
              ¬ encPair encBits encBits (x, (List.ofFn y).take (p.eval x.length)) ∈ B).card :=
          card_filter_congr_dec fun _ ↦ Iff.rfl
        omega
      have h2m : 2 ^ m = 2 * 2 ^ (m - 1) := by
        have : m = m - 1 + 1 := by omega
        conv_lhs => rw [this, pow_succ']
      have hpow_pos : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow _ _ (by omega)
      have hAiff : x ∈ A ↔ 2 ^ m ≤ 2 * c := by
        rw [hAB x]
        rw [card_filter_congr_iff (Q := fun y : Fin (p.eval x.length) → Bool ↦
          encPair encBits encBits (x, List.ofFn y) ∈ B) (fun _ ↦ Iff.rfl)]
        exact (nonstrictMajority_take_iff (hp_le x.length)
          (fun u ↦ encPair encBits encBits (x, u) ∈ B)).symm
      change x ∉ A ↔ _
      rw [hAiff, not_le, pow_succ']
      omega

/-- Existential quantification over polynomial-length bitstrings steps up one Wagner level. -/
theorem exists_bits_mem_CHLevel {k : ℕ} {B : Set (List Bool)} (hB : B ∈ CHLevel k)
    (p : Polynomial ℕ) :
    {x : List Bool | ∃ y : Fin (p.eval x.length) → Bool,
      encPair encBits encBits (x, List.ofFn y) ∈ B} ∈ CHLevel (k + 1) := by
  by_cases hBuniv : B = Set.univ
  · have heq : {x : List Bool | ∃ y : Fin (p.eval x.length) → Bool,
        encPair encBits encBits (x, List.ofFn y) ∈ B} = Set.univ := by
      ext x; simp [hBuniv]
    rw [heq]
    exact univ_mem_CHLevel (k + 1)
  · obtain ⟨w₀, hw₀⟩ := Set.nonempty_compl.mpr hBuniv
    let condBranch : List Bool → Bool := fun w ↦
      (pairBitsDecoder.decode w).elim false fun xy ↦ xy.2.headD false
    have hcond : ComputableInPolyTime condBranch encBits encBool :=
      pairBitsDecoder.computable.optionElimWithInput (ComputableInPolyTime.const false)
        ((ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp
          ((ComputableInPolyTime.snd encBits encBits).comp
            (ComputableInPolyTime.snd encBits (encPair encBits encBits))))
    let gFalse : List Bool → List Bool := fun w ↦
      (pairBitsDecoder.decode w).elim w₀ fun xy ↦ encPair encBits encBits (xy.1, xy.2.tail)
    have hgFalse : ComputableInPolyTime gFalse encBits encBits := by
      refine pairBitsDecoder.computable.optionElimWithInput (ComputableInPolyTime.const w₀) ?_
      have hx : ComputableInPolyTime (fun z : List Bool × (List Bool × List Bool) ↦ z.2.1)
          (encPair encBits (encPair encBits encBits)) encBits :=
        (ComputableInPolyTime.fst encBits encBits).comp
          (ComputableInPolyTime.snd encBits (encPair encBits encBits))
      have hy : ComputableInPolyTime (fun z : List Bool × (List Bool × List Bool) ↦ z.2.2.tail)
          (encPair encBits (encPair encBits encBits)) encBits :=
        ComputableInPolyTime.bitsTail.comp
          ((ComputableInPolyTime.snd encBits encBits).comp
            (ComputableInPolyTime.snd encBits (encPair encBits encBits)))
      exact (hx.prod hy).of_enc_eq fun _ ↦ rfl
    let checkTrue : List Bool → Bool := fun w ↦
      (pairBitsDecoder.decode w).elim false fun xy ↦ xy.2.tail.any id
    have hcheckTrue : ComputableInPolyTime checkTrue encBits encBool :=
      pairBitsDecoder.computable.optionElimWithInput (ComputableInPolyTime.const false)
        (computableInPolyTime_bitsAny.comp (ComputableInPolyTime.bitsTail.comp
          ((ComputableInPolyTime.snd encBits encBits).comp
            (ComputableInPolyTime.snd encBits (encPair encBits encBits)))))
    let B' : Set (List Bool) :=
      {w | if condBranch w then w ∈ {u | checkTrue u = true} else w ∈ gFalse ⁻¹' B}
    have hB' : B' ∈ CHLevel k :=
      ite_mem_CHLevel hcond
        (P_subset_CHLevel k ⟨checkTrue, hcheckTrue, fun _ ↦ Iff.rfl⟩)
        (PolyTimeReducible.mem_CHLevel ⟨gFalse, hgFalse, fun _ ↦ Iff.rfl⟩ hB)
    rw [CHLevel_succ, mem_countingOp_iff]
    refine ⟨B', hB', p + 1, fun x ↦ ?_⟩
    classical
    have heval : (p + 1).eval x.length = p.eval x.length + 1 := by simp
    rw [heval]
    rw [card_filter_congr_iff (Q := fun y : Fin (p.eval x.length + 1) → Bool ↦
      encPair encBits encBits (x, List.ofFn y) ∈ B') (fun _ ↦ Iff.rfl)]
    rw [card_filter_succ_split (p.eval x.length)
      (P := fun y ↦ encPair encBits encBits (x, y) ∈ B')]
    have hleft : (Finset.univ.filter fun y : Fin (p.eval x.length) → Bool ↦
        encPair encBits encBits (x, false :: List.ofFn y) ∈ B').card =
        (Finset.univ.filter fun y : Fin (p.eval x.length) → Bool ↦
          encPair encBits encBits (x, List.ofFn y) ∈ B).card := by
      apply card_filter_congr_iff
      intro y
      change (if condBranch (encPair encBits encBits (x, false :: List.ofFn y)) = true then _
        else gFalse (encPair encBits encBits (x, false :: List.ofFn y)) ∈ B) ↔ _
      simp only [condBranch, gFalse, PartialDecoder.decode_enc, Option.elim_some,
        List.headD_cons, Bool.false_eq_true, ↓reduceIte, List.tail_cons]
    have hright : (Finset.univ.filter fun y : Fin (p.eval x.length) → Bool ↦
        encPair encBits encBits (x, true :: List.ofFn y) ∈ B').card =
        2 ^ p.eval x.length - 1 := by
      rw [card_filter_congr_iff (Q := fun y : Fin (p.eval x.length) → Bool ↦
        (List.ofFn y).any id = true) (fun y ↦ by
          change (if condBranch (encPair encBits encBits (x, true :: List.ofFn y)) = true then
            checkTrue (encPair encBits encBits (x, true :: List.ofFn y)) = true else _) ↔ _
          simp only [condBranch, checkTrue, PartialDecoder.decode_enc, Option.elim_some,
            List.headD_cons, ↓reduceIte, List.tail_cons])]
      exact card_filter_anyTrue (p.eval x.length)
    rw [hleft, hright, pow_succ']
    have hpos : 1 ≤ 2 ^ p.eval x.length := Nat.one_le_pow _ _ (by omega)
    have hcard_pos : (0 < (Finset.univ.filter fun y : Fin (p.eval x.length) → Bool ↦
        encPair encBits encBits (x, List.ofFn y) ∈ B).card) ↔
        ∃ y : Fin (p.eval x.length) → Bool, encPair encBits encBits (x, List.ofFn y) ∈ B := by
      rw [Finset.card_pos, Finset.filter_nonempty_iff]
      simp
    change (∃ y : Fin (p.eval x.length) → Bool, encPair encBits encBits (x, List.ofFn y) ∈ B) ↔ _
    rw [← hcard_pos]
    omega

/-- Universal quantification over polynomial-length bitstrings steps up one Wagner level. -/
theorem forall_bits_mem_CHLevel {k : ℕ} {B : Set (List Bool)} (hB : B ∈ CHLevel k)
    (p : Polynomial ℕ) :
    {x : List Bool | ∀ y : Fin (p.eval x.length) → Bool,
      encPair encBits encBits (x, List.ofFn y) ∈ B} ∈ CHLevel (k + 1) := by
  have hex := exists_bits_mem_CHLevel (compl_mem_CHLevel hB) p
  have hcompl := compl_mem_CHLevel hex
  convert hcompl using 1
  ext x
  simp

open Classical in
/-- Strict majority over polynomial-length bitstrings steps up one Wagner level. -/
theorem strictMajority_mem_CHLevel {k : ℕ} {B : Set (List Bool)} (hB : B ∈ CHLevel k)
    (p : Polynomial ℕ) :
    {x : List Bool |
      2 ^ p.eval x.length <
        2 * (Finset.univ.filter fun y : Fin (p.eval x.length) → Bool ↦
          encPair encBits encBits (x, List.ofFn y) ∈ B).card} ∈ CHLevel (k + 1) := by
  have hnon : {x : List Bool |
      2 ^ p.eval x.length ≤
        2 * (Finset.univ.filter fun y : Fin (p.eval x.length) → Bool ↦
          encPair encBits encBits (x, List.ofFn y) ∈ Bᶜ).card} ∈ CHLevel (k + 1) := by
    rw [CHLevel_succ, mem_countingOp_iff]
    refine ⟨Bᶜ, compl_mem_CHLevel hB, p, fun x ↦ ?_⟩
    exact Iff.of_eq (congrArg (fun c ↦ 2 ^ p.eval x.length ≤ 2 * c)
      (card_filter_congr_dec fun _ ↦ Iff.rfl))
  have hcompl := compl_mem_CHLevel hnon
  convert hcompl using 1
  ext x
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun y : Fin (p.eval x.length) → Bool ↦ encPair encBits encBits (x, List.ofFn y) ∈ B)
  have huniv :
      (Finset.univ : Finset (Fin (p.eval x.length) → Bool)).card = 2 ^ p.eval x.length := by
    simp
  rw [huniv] at hsum
  rw [card_filter_congr_iff (Q := fun y : Fin (p.eval x.length) → Bool ↦
    encPair encBits encBits (x, List.ofFn y) ∈ B) (fun _ ↦ Iff.rfl)]
  rw [card_filter_congr_iff (Q := fun y : Fin (p.eval x.length) → Bool ↦
    ¬ encPair encBits encBits (x, List.ofFn y) ∈ B) (fun _ ↦ Iff.rfl)]
  omega

/-! ### Simulating deterministic and majority oracle machines inside `CHLevel` -/

/-- One step of a coin-fixed oracle machine reading its oracle reply bit from a transcript. -/
private def transcriptStep {k m : ℕ} (machine : MultiTapePTM k Bool (Fin m) Unit)
    (cfg : FiniteConfig k Bool (Fin m) Unit) (b : Bool) :
    FiniteConfig k Bool (Fin m) Unit :=
  if (machine.pendingQuery cfg).isSome then machine.receiveBit (cfg, b) else machine.localStep cfg

/-- Configuration reached by running `machine` on `x` for `t` steps using transcript `w`. -/
private def transcriptCfg {k m : ℕ} (machine : MultiTapePTM k Bool (Fin m) Unit)
    (x w : List Bool) (t : ℕ) : FiniteConfig k Bool (Fin m) Unit :=
  (w.take t).foldl (transcriptStep machine) (FiniteConfig.init machine.initial x)

/-- `transcriptStep` preserves the single-bit-answer space bound. -/
private theorem spaceBound_transcriptStep {k m : ℕ} (machine : MultiTapePTM k Bool (Fin m) Unit)
    {inputSize steps : ℕ} {cfg : FiniteConfig k Bool (Fin m) Unit}
    (h : FiniteConfig.SpaceBound inputSize steps 1 cfg) (b : Bool) :
    FiniteConfig.SpaceBound inputSize (steps + 1) 1 (transcriptStep machine cfg b) := by
  have heq : transcriptStep machine cfg b = machine.answerStep (fun _ ↦ [b]) cfg :=
    (machine.answerStep_bit (fun _ ↦ b) cfg).symm
  rw [heq]
  exact machine.spaceBound_answerStep (fun _ ↦ b) h

/-- Folded `transcriptStep` satisfies the linear step space bound. -/
private theorem spaceBound_foldl_transcriptStep {k m : ℕ}
    (machine : MultiTapePTM k Bool (Fin m) Unit) (x w : List Bool) :
    FiniteConfig.SpaceBound x.length w.length 1
      (w.foldl (transcriptStep machine) (FiniteConfig.init machine.initial x)) := by
  induction w using List.reverseRecOn with
  | nil => exact FiniteConfig.spaceBound_init _ _ _
  | append_singleton w b ih =>
    rw [List.foldl_concat, List.length_append, List.length_singleton]
    exact spaceBound_transcriptStep machine ih b

/-- `transcriptStep` is polynomial-time computable. -/
private theorem computableInPolyTime_transcriptStep {k m : ℕ}
    (machine : MultiTapePTM k Bool (Fin m) Unit) :
    ComputableInPolyTime (fun p : FiniteConfig k Bool (Fin m) Unit × Bool ↦
      transcriptStep machine p.1 p.2) (encPair encFiniteConfig encBool) encFiniteConfig := by
  have hcond : ComputableInPolyTime
      (fun p : FiniteConfig k Bool (Fin m) Unit × Bool ↦ (machine.pendingQuery p.1).isSome)
      (encPair encFiniteConfig encBool) encBool :=
    ((ComputableInPolyTime.of_finite Option.isSome).comp machine.pendingQuery_pt).comp
      (ComputableInPolyTime.fst encFiniteConfig encBool)
  exact ComputableInPolyTime.ite' hcond machine.receiveBit_pt
    (machine.localStep_pt.comp (ComputableInPolyTime.fst encFiniteConfig encBool))

/-- Simulating `machine` on input `x` along transcript bits `w` is polynomial-time computable. -/
private theorem computableInPolyTime_runTranscript {k m : ℕ}
    (machine : MultiTapePTM k Bool (Fin m) Unit) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool ↦
        p.2.foldl (transcriptStep machine) (FiniteConfig.init machine.initial p.1))
      (encPair encBits encBits) encFiniteConfig := by
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Fin m) (Oracle := Unit)
  refine ComputableInPolyTime.foldl' (encA := encBool) (encL := encBits) (encB := encFiniteConfig)
    (ComputableInPolyTime.snd encBits encBits)
    (ComputableInPolyTime.finiteConfig_init (ComputableInPolyTime.fst encBits encBits)
      machine.initial)
    (computableInPolyTime_transcriptStep machine)
    (B := fun p ↦ cf * (p.1.length + p.2.length + 1 + 1)) ?_ ?_
  · refine PolyBounded.of_forall_le (cf * 4) 1 fun p ↦ ?_
    simp only [length_encPair, encBits_apply, pow_one]
    nlinarith
  · intro p i hi
    have hsb := spaceBound_foldl_transcriptStep machine p.1 (p.2.take i)
    have hlen : (p.2.take i).length ≤ p.2.length := (List.length_take_le i p.2).trans hi
    exact (hcf _ _ _ _ hsb).trans (Nat.mul_le_mul_left cf (by omega))

/-- If every step `< t` of transcript `w` agrees with oracle `A`, then folding `w.take t`
reproduces `t` steps of `answerStep (languageOracle A)`. -/
private theorem foldl_transcriptStep_take_eq {k m : ℕ}
    (machine : MultiTapePTM k Bool (Fin m) Unit) (A : Set (List Bool)) (x w : List Bool)
    (t : ℕ) (ht : t ≤ w.length)
    (hvalid : ∀ i < t,
      (machine.pendingQuery (transcriptCfg machine x w i)).isSome →
        (machine.pendingRequest (transcriptCfg machine x w i) ∈ A ↔ w.getD i false = true)) :
    transcriptCfg machine x w t =
      (machine.answerStep (languageOracle A))^[t] (FiniteConfig.init machine.initial x) := by
  induction t with
  | zero => simp [transcriptCfg]
  | succ t ih =>
    have hprev := ih (Nat.le_of_succ_le ht) (fun i hi ↦ hvalid i (Nat.lt_succ_of_lt hi))
    have htake : w.take (t + 1) = w.take t ++ [w[t]'(by omega)] :=
      List.take_succ_eq_append_getElem _
    unfold transcriptCfg
    rw [htake, List.foldl_concat, Function.iterate_succ_apply']
    change transcriptStep machine (transcriptCfg machine x w t) (w[t]'(by omega)) = _
    rw [← hprev]
    set cfg := transcriptCfg machine x w t
    classical
    have hbit := machine.answerStep_bit (fun q ↦ decide (q ∈ A)) cfg
    have hlo : (languageOracle A : Unit × List Bool → List Bool) = fun q ↦ [decide (q.2 ∈ A)] :=
      rfl
    rw [hlo, hbit]
    unfold transcriptStep
    by_cases hq : (machine.pendingQuery cfg).isSome
    · simp only [hq, ↓reduceIte]
      have hgt : w.getD t false = w[t]'(by omega) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : t < w.length)]
      have hagree : machine.pendingRequest cfg ∈ A ↔ w[t]'(by omega) = true := by
        simpa only [hgt] using hvalid t (Nat.lt_succ_self t) hq
      have hdec : decide (machine.pendingRequest cfg ∈ A) = w[t]'(by omega) := by
        cases hw : w[t]'(by omega) with
        | true => simp [hagree.mpr hw]
        | false =>
          have hnot : machine.pendingRequest cfg ∉ A := by
            intro hmem
            have := hagree.mp hmem
            rw [hw] at this
            cases this
          simp [hnot]
      rw [hdec]
    · simp [hq]

/-- Step-checker language for a transcript `(x, w, u)` relative to `A` and clock polynomial `T`. -/
private def transcriptStepLang {k m : ℕ}
    (D : PartialDecoder (encPair (encPair encBits encBits) encBits))
    (machine : MultiTapePTM k Bool (Fin m) Unit)
    (T : Polynomial ℕ) (A : Set (List Bool)) : Set (List Bool) :=
  {z | match D.decode z with
    | none => False
    | some ((x, w), u) =>
      (transcriptCfg machine x w (T.eval x.length)).tapes.output = [true] ∧
      let t := u.count true
      t < T.eval x.length →
      (machine.pendingQuery (transcriptCfg machine x w t)).isSome →
      (machine.pendingRequest (transcriptCfg machine x w t) ∈ A ↔ w.getD t false = true)}

/-- Decoded acceptance check for a transcript `(x, w, u)` after `T(|x|)` steps. -/
private def transcriptOutCheck {k m : ℕ}
    (D : PartialDecoder (encPair (encPair encBits encBits) encBits))
    (machine : MultiTapePTM k Bool (Fin m) Unit) (T : Polynomial ℕ) (z : List Bool) : Bool :=
  (D.decode z).elim false fun q ↦
    decide ((transcriptCfg machine q.1.1 q.1.2 (T.eval q.1.1.length)).tapes.output = [true])

/-- Decoded guard testing whether step `t = u.count true` is in range and issues a query. -/
private def transcriptQueryCheck {k m : ℕ}
    (D : PartialDecoder (encPair (encPair encBits encBits) encBits))
    (machine : MultiTapePTM k Bool (Fin m) Unit) (T : Polynomial ℕ) (z : List Bool) : Bool :=
  (D.decode z).elim false fun q ↦
    decide (q.2.count true < T.eval q.1.1.length) &&
      (machine.pendingQuery (transcriptCfg machine q.1.1 q.1.2 (q.2.count true))).isSome

/-- Decoded transcript answer bit at step `t = u.count true`. -/
private def transcriptAnswerBit
    (D : PartialDecoder (encPair (encPair encBits encBits) encBits)) (z : List Bool) : Bool :=
  (D.decode z).elim false fun q ↦ q.1.2.getD (q.2.count true) false

/-- Decoded oracle query word at step `t = u.count true`. -/
private def transcriptRequest {k m : ℕ}
    (D : PartialDecoder (encPair (encPair encBits encBits) encBits))
    (machine : MultiTapePTM k Bool (Fin m) Unit) (z : List Bool) : List Bool :=
  (D.decode z).elim [] fun q ↦
    machine.pendingRequest (transcriptCfg machine q.1.1 q.1.2 (q.2.count true))

private theorem pt_triple_x :
    ComputableInPolyTime (fun q : (List Bool × List Bool) × List Bool ↦ q.1.1)
      (encPair (encPair encBits encBits) encBits) encBits :=
  (ComputableInPolyTime.fst encBits encBits).comp
    (ComputableInPolyTime.fst (encPair encBits encBits) encBits)

private theorem pt_triple_w :
    ComputableInPolyTime (fun q : (List Bool × List Bool) × List Bool ↦ q.1.2)
      (encPair (encPair encBits encBits) encBits) encBits :=
  (ComputableInPolyTime.snd encBits encBits).comp
    (ComputableInPolyTime.fst (encPair encBits encBits) encBits)

private theorem pt_triple_count :
    ComputableInPolyTime (fun q : (List Bool × List Bool) × List Bool ↦ q.2.count true)
      (encPair (encPair encBits encBits) encBits) encUnary :=
  computableInPolyTime_bitsCountTrue.comp
    (ComputableInPolyTime.snd (encPair encBits encBits) encBits)

private theorem pt_triple_clock (T : Polynomial ℕ) :
    ComputableInPolyTime (fun q : (List Bool × List Bool) × List Bool ↦ T.eval q.1.1.length)
      (encPair (encPair encBits encBits) encBits) encUnary :=
  (ComputableInPolyTime.unary_eval T).comp
    ((ComputableInPolyTime.encoding_length encBits).comp pt_triple_x)

private theorem pt_triple_cfg_step {k m : ℕ} (machine : MultiTapePTM k Bool (Fin m) Unit) :
    ComputableInPolyTime
      (fun q : (List Bool × List Bool) × List Bool ↦
        transcriptCfg machine q.1.1 q.1.2 (q.2.count true))
      (encPair (encPair encBits encBits) encBits) encFiniteConfig := by
  have h := (computableInPolyTime_runTranscript machine).comp
    (pt_triple_x.prod (ComputableInPolyTime.bitsTakeWithInput pt_triple_w pt_triple_count))
  refine (show (fun q : (List Bool × List Bool) × List Bool ↦
      (q.1.2.take (q.2.count true)).foldl (transcriptStep machine)
        (FiniteConfig.init machine.initial q.1.1)) =
      (fun q ↦ transcriptCfg machine q.1.1 q.1.2 (q.2.count true)) from
      funext fun _ ↦ rfl) ▸ h

private theorem computableInPolyTime_transcriptOutCheck {k m : ℕ}
    (D : PartialDecoder (encPair (encPair encBits encBits) encBits))
    (machine : MultiTapePTM k Bool (Fin m) Unit) (T : Polynomial ℕ) :
    ComputableInPolyTime (transcriptOutCheck D machine T) encBits encBool := by
  have hcfgT := (computableInPolyTime_runTranscript machine).comp
    (pt_triple_x.prod (ComputableInPolyTime.bitsTakeWithInput pt_triple_w (pt_triple_clock T)))
  have hproj : ComputableInPolyTime
      (fun cfg : FiniteConfig k Bool (Fin m) Unit ↦ cfg.tapes.output)
      encFiniteConfig encBits :=
    ComputableInPolyTime.finiteCfg_output.comp ComputableInPolyTime.finiteConfig_tapes
  have hdec := (hproj.comp hcfgT).decide_eq' (ComputableInPolyTime.const [true])
  exact partialDecoder_optionElim D false hdec

private theorem computableInPolyTime_transcriptQueryCheck {k m : ℕ}
    (D : PartialDecoder (encPair (encPair encBits encBits) encBits))
    (machine : MultiTapePTM k Bool (Fin m) Unit) (T : Polynomial ℕ) :
    ComputableInPolyTime (transcriptQueryCheck D machine T) encBits encBool :=
  partialDecoder_optionElim D false (ComputableInPolyTime.bool_and'
    (ComputableInPolyTime.unary_lt' pt_triple_count (pt_triple_clock T))
    (((ComputableInPolyTime.of_finite Option.isSome).comp machine.pendingQuery_pt).comp
      (pt_triple_cfg_step machine)))

private theorem computableInPolyTime_transcriptAnswerBit
    (D : PartialDecoder (encPair (encPair encBits encBits) encBits)) :
    ComputableInPolyTime (transcriptAnswerBit D) encBits encBool :=
  partialDecoder_optionElim D false
    (ComputableInPolyTime.bitsGetDWithInput pt_triple_w pt_triple_count false)

private theorem computableInPolyTime_transcriptRequest {k m : ℕ}
    (D : PartialDecoder (encPair (encPair encBits encBits) encBits))
    (machine : MultiTapePTM k Bool (Fin m) Unit) :
    ComputableInPolyTime (transcriptRequest D machine) encBits encBits :=
  partialDecoder_optionElim D [] (machine.pendingRequest_pt.comp (pt_triple_cfg_step machine))

/-- The transcript step-checker language lies in `CHLevel k` whenever `A ∈ CHLevel k`. -/
private theorem transcriptStepLang_mem_CHLevel {k m : ℕ}
    (D : PartialDecoder (encPair (encPair encBits encBits) encBits))
    (machine : MultiTapePTM k Bool (Fin m) Unit) (T : Polynomial ℕ)
    {level : ℕ} {A : Set (List Bool)} (hA : A ∈ CHLevel level) :
    transcriptStepLang D machine T A ∈ CHLevel level := by
  let S_o : Set (List Bool) :=
    {z | if transcriptAnswerBit D z then z ∈ transcriptRequest D machine ⁻¹' A
      else z ∈ transcriptRequest D machine ⁻¹' Aᶜ}
  have hM_oracle : S_o ∈ CHLevel level :=
    ite_mem_CHLevel (computableInPolyTime_transcriptAnswerBit D)
      (PolyTimeReducible.mem_CHLevel
        ⟨_, computableInPolyTime_transcriptRequest D machine, fun _ ↦ Iff.rfl⟩ hA)
      (PolyTimeReducible.mem_CHLevel
        ⟨_, computableInPolyTime_transcriptRequest D machine, fun _ ↦ Iff.rfl⟩
        (compl_mem_CHLevel hA))
  let S_s : Set (List Bool) :=
    {z | if transcriptQueryCheck D machine T z then z ∈ S_o else z ∈ (Set.univ : Set (List Bool))}
  have hM_step : S_s ∈ CHLevel level :=
    ite_mem_CHLevel (computableInPolyTime_transcriptQueryCheck D machine T) hM_oracle
      (univ_mem_CHLevel level)
  let S_m : Set (List Bool) :=
    {z | if transcriptOutCheck D machine T z then z ∈ S_s else z ∈ (∅ : Set (List Bool))}
  have hM : S_m ∈ CHLevel level :=
    ite_mem_CHLevel (computableInPolyTime_transcriptOutCheck D machine T) hM_step
      (empty_mem_CHLevel level)
  have heq : transcriptStepLang D machine T A = S_m := by
    ext z
    simp only [transcriptStepLang, S_m, S_s, S_o, transcriptOutCheck, transcriptQueryCheck,
      transcriptAnswerBit, transcriptRequest, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ,
      Set.mem_empty_iff_false, Set.mem_compl_iff]
    cases hd : D.decode z with
    | none => simp
    | some q =>
      rcases q with ⟨⟨x, w⟩, u⟩
      simp only [Option.elim_some]
      by_cases hout : (transcriptCfg machine x w (T.eval x.length)).tapes.output = [true]
      · simp only [hout, decide_true, ↓reduceIte, true_and]
        by_cases hlt : u.count true < T.eval x.length
        · by_cases hq : (machine.pendingQuery (transcriptCfg machine x w (u.count true))).isSome
          · simp only [hlt, decide_true, hq, Bool.and_self, ↓reduceIte, forall_const]
            split_ifs with hb <;> simp_all
          · simp [hq]
        · simp [hlt]
      · simp [hout]
  rwa [heq]

/-- Helper counting `true` entries of an indicator vector `fun j : Fin n ↦ decide (j.val < i)`. -/
private theorem count_true_ofFn_lt {n i : ℕ} (hi : i ≤ n) :
    (List.ofFn fun j : Fin n ↦ decide (j.val < i)).count true = i := by
  have h1 : ∀ (m : ℕ) (f : Fin m → Bool),
      (List.ofFn f).count true = (Finset.univ.filter fun j : Fin m ↦ f j = true).card := by
    intro m f
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.ofFn_succ, List.count_cons, ih, Fin.univ_succ, Finset.filter_cons]
      by_cases hf0 : f 0 = true
      · simp only [hf0, beq_self_eq_true, ↓reduceIte, Finset.card_cons,
          Finset.filter_map, Finset.card_map, Function.comp_def]
        rfl
      · simp only [hf0, Bool.false_eq_true, ↓reduceIte, Finset.filter_map,
          Finset.card_map, Function.comp_def]
        rfl
  rw [h1 n]
  have hfin : (Finset.univ.filter fun j : Fin n ↦ decide (j.val < i) = true) =
      Finset.univ.map ⟨fun j : Fin i ↦ ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩,
        fun a b h ↦ Fin.ext (by simpa using congrArg Fin.val h)⟩ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Finset.mem_map]
    constructor
    · intro hj; exact ⟨⟨j.val, hj⟩, rfl⟩
    · rintro ⟨a, rfl⟩; exact a.isLt
  rw [hfin, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Every `P` language relative to an oracle `A ∈ CHLevel k` lies in `CHLevel (k + 2)`. -/
theorem PWithOracle_subset_CHLevel {k : ℕ} {A : Set (List Bool)} (hA : A ∈ CHLevel k) :
    PWithOracle A encBits ⊆ CHLevel (k + 2) := by
  rintro L ⟨f, ⟨program, hcert, hprog⟩, hLf⟩
  obtain ⟨k_t, m_s, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
  let T : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) ^ d
  have hTeval : ∀ n, T.eval n = c * (n + 1) ^ d := fun n ↦ by simp [T]
  have hL_run : ∀ x : List Bool,
      x ∈ L ↔
        ((machine.answerStep (languageOracle A))^[T.eval x.length]
          (FiniteConfig.init machine.initial x)).tapes.output = [true] := by
    intro x
    rw [hLf x, ← hprog x]
    have h1 := hrun x (languageOracle A)
    simp only [encBits_apply] at h1
    rw [← hTeval x.length, machine.interpret_run_pure_false, encBool_apply] at h1
    rw [h1]
    simp
  have hM : transcriptStepLang tripleBitsDecoder machine T A ∈ CHLevel k :=
    transcriptStepLang_mem_CHLevel tripleBitsDecoder machine T hA
  let N : Set (List Bool) :=
    {p | ∀ u : Fin (T.eval p.length) → Bool,
      encPair encBits encBits (p, List.ofFn u) ∈ transcriptStepLang tripleBitsDecoder machine T A}
  have hN : N ∈ CHLevel (k + 1) := forall_bits_mem_CHLevel hM T
  have hL_eq : L = {x : List Bool | ∃ w : Fin (T.eval x.length) → Bool,
      encPair encBits encBits (x, List.ofFn w) ∈ N} := by
    ext x
    rw [hL_run x]
    change _ ↔ ∃ w : Fin (T.eval x.length) → Bool,
      ∀ u : Fin (T.eval (encPair encBits encBits (x, List.ofFn w)).length) → Bool,
        encPair encBits encBits (encPair encBits encBits (x, List.ofFn w), List.ofFn u) ∈
          transcriptStepLang tripleBitsDecoder machine T A
    constructor
    · intro hout
      classical
      let wStar : Fin (T.eval x.length) → Bool := fun i ↦
        decide (machine.pendingRequest
          ((machine.answerStep (languageOracle A))^[i.val]
            (FiniteConfig.init machine.initial x)) ∈ A)
      have hagree : ∀ t ≤ T.eval x.length,
          transcriptCfg machine x (List.ofFn wStar) t =
            (machine.answerStep (languageOracle A))^[t] (FiniteConfig.init machine.initial x) := by
        intro t ht
        induction t using Nat.strong_induction_on with
        | _ t ih =>
          apply foldl_transcriptStep_take_eq machine A x (List.ofFn wStar) t (by simpa using ht)
          intro i hi _
          have hi_lt : i < T.eval x.length := Nat.lt_of_lt_of_le hi ht
          have hprev := ih i hi (Nat.le_of_lt hi_lt)
          have hget : (List.ofFn wStar).getD i false = wStar ⟨i, hi_lt⟩ := by
            rw [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hi_lt)]
            simp
          rw [hprev, hget]
          simp [wStar]
      refine ⟨wStar, fun u ↦ ?_⟩
      rw [encPair_encPair_eq]
      unfold transcriptStepLang
      simp only [Set.mem_ofPred_eq, tripleBitsDecoder.decode_enc]
      refine ⟨by rw [hagree _ le_rfl]; exact hout, fun hlt _ ↦ ?_⟩
      set i := (List.ofFn u).count true
      have hi_eq := hagree i (Nat.le_of_lt hlt)
      have hget : (List.ofFn wStar).getD i false = wStar ⟨i, hlt⟩ := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hlt)]
        simp
      rw [hi_eq, hget]
      simp [wStar]
    · rintro ⟨w, hw⟩
      have hxlen : x.length ≤ (encPair encBits encBits (x, List.ofFn w)).length := by
        simp only [length_encPair, encBits_apply]
        omega
      have hTle : T.eval x.length ≤ T.eval (encPair encBits encBits (x, List.ofFn w)).length :=
        Polynomial.eval_mono T hxlen
      have hmem : ∀ u : Fin (T.eval (encPair encBits encBits (x, List.ofFn w)).length) → Bool,
          (transcriptCfg machine x (List.ofFn w) (T.eval x.length)).tapes.output = [true] ∧
          ((List.ofFn u).count true < T.eval x.length →
            (machine.pendingQuery
              (transcriptCfg machine x (List.ofFn w) ((List.ofFn u).count true))).isSome →
            (machine.pendingRequest
              (transcriptCfg machine x (List.ofFn w) ((List.ofFn u).count true)) ∈ A ↔
                (List.ofFn w).getD ((List.ofFn u).count true) false = true)) := by
        intro u
        have h := hw u
        rw [encPair_encPair_eq] at h
        unfold transcriptStepLang at h
        simpa only [Set.mem_ofPred_eq, tripleBitsDecoder.decode_enc] using h
      have hout := (hmem (fun _ ↦ false)).1
      have hvalid : ∀ i < T.eval x.length,
          (machine.pendingQuery (transcriptCfg machine x (List.ofFn w) i)).isSome →
            (machine.pendingRequest (transcriptCfg machine x (List.ofFn w) i) ∈ A ↔
              (List.ofFn w).getD i false = true) := by
        intro i hi hq
        let Llen := T.eval (encPair encBits encBits (x, List.ofFn w)).length
        let u : Fin Llen → Bool := fun j ↦ decide (j.val < i)
        have hcnt : (List.ofFn u).count true = i :=
          count_true_ofFn_lt ((Nat.le_of_lt hi).trans hTle)
        have hstep := (hmem u).2
        rw [hcnt] at hstep
        exact hstep hi hq
      have heq := foldl_transcriptStep_take_eq machine A x (List.ofFn w) (T.eval x.length)
        (by simp) hvalid
      rw [← heq]
      exact hout
  rw [hL_eq]
  exact exists_bits_mem_CHLevel hN T

/-- Every relativized `PP` language with oracle `A ∈ CHLevel k` lies in `CHLevel (k + 3)`. -/
theorem PPWithOracle_subset_CHLevel {k : ℕ} {A : Set (List Bool)} (hA : A ∈ CHLevel k) :
    PPWithOracle A encBits ⊆ CHLevel (k + 3) := by
  rintro L ⟨p, V, hV, hL⟩
  let B : Set (List Bool) :=
    {w | (pairBitsDecoder.decode w).elim false V = true}
  have hB_oracle : B ∈ PWithOracle A encBits := by
    refine ⟨fun w ↦ (pairBitsDecoder.decode w).elim false V, ?_, fun _ ↦ Iff.rfl⟩
    let defaultPair : List Bool × List Bool := ([], [])
    have hdecVal : ComputableInPolyTime
        (fun w ↦ (pairBitsDecoder.decode w).elim defaultPair id)
        encBits (encPair encBits encBits) :=
      pairBitsDecoder.computable.optionElimWithInput (ComputableInPolyTime.const defaultPair)
        (ComputableInPolyTime.snd encBits (encPair encBits encBits))
    have hvalid : ComputableInPolyTime
        (fun w ↦ (pairBitsDecoder.decode w).elim false fun _ ↦ true)
        encBits encBool :=
      pairBitsDecoder.computable.optionElimWithInput (ComputableInPolyTime.const false)
        (body := fun _ _ ↦ true) (ComputableInPolyTime.const true)
    have hV' := hV.preprocess hdecVal
    have hboth := (hvalid.computableInPolyTimeWithOracle A).prod hV'
    have hcomb := hboth.map ComputableInPolyTime.bool_and
    have heq : (fun w ↦ ((pairBitsDecoder.decode w).elim false fun _ ↦ true) &&
        V ((pairBitsDecoder.decode w).elim defaultPair id)) =
        fun w ↦ (pairBitsDecoder.decode w).elim false V := by
      funext w
      cases pairBitsDecoder.decode w <;> simp
    rwa [heq] at hcomb
  have hB : B ∈ CHLevel (k + 2) := PWithOracle_subset_CHLevel hA hB_oracle
  have hL_eq : L = {x : List Bool |
      2 ^ p.eval x.length <
        2 * (Finset.univ.filter fun y : Fin (p.eval x.length) → Bool ↦
          encPair encBits encBits (x, List.ofFn y) ∈ B).card} := by
    ext x
    rw [hL x]
    change 2 ^ p.eval (encBits x).length < 2 * acceptCount V x (p.eval (encBits x).length) ↔
      2 ^ p.eval x.length < 2 * (Finset.univ.filter _).card
    have henc : (encBits x).length = x.length := rfl
    rw [henc, acceptCount]
    exact Iff.of_eq (congrArg (fun c ↦ 2 ^ p.eval x.length < 2 * c)
      (card_filter_congr_dec fun y ↦ by
        change V (x, List.ofFn y) = true ↔
          (pairBitsDecoder.decode (encPair encBits encBits (x, List.ofFn y))).elim false V = true
        rw [pairBitsDecoder.decode_enc]
        rfl))
  rw [hL_eq]
  have hres := strictMajority_mem_CHLevel hB p
  convert hres using 2
  ext x
  exact Iff.of_eq (congrArg (fun c ↦ 2 ^ p.eval x.length < 2 * c)
    (card_filter_congr_dec fun _ ↦ Iff.rfl))

/-! ### Torán's equivalence between `CH` and `⋃ a, CountingLevel a encBits` -/

/-- Every oracle counting-hierarchy level `CountingLevel a encBits` embeds into
`CHLevel (3 * a)`. -/
theorem CountingLevel_subset_CHLevel (a : ℕ) : CountingLevel a encBits ⊆ CHLevel (3 * a) := by
  induction a with
  | zero =>
    rw [Nat.mul_zero, CHLevel_zero, CountingLevel_zero]
  | succ a ih =>
    rintro L ⟨A, hA, hL⟩
    exact PPWithOracle_subset_CHLevel (ih hA) hL

/-- Every Wagner level `CHLevel a` embeds into `CountingLevel a encBits`. -/
theorem CHLevel_subset_CountingLevel (a : ℕ) : CHLevel a ⊆ CountingLevel a encBits := by
  induction a with
  | zero =>
    rw [CHLevel_zero, CountingLevel_zero]
  | succ a ih =>
    intro A hA
    rw [CHLevel_succ, mem_countingOp_iff] at hA
    obtain ⟨B, hB, p, hAB⟩ := hA
    refine ⟨B, ih hB, ?_⟩
    let p' : Polynomial ℕ := p + 1
    have hp_le : ∀ n, p.eval n ≤ p'.eval n := fun n ↦ by simp [p']
    have hp'_pos : ∀ n, 1 ≤ p'.eval n := fun n ↦ by simp [p']
    classical
    let V : List Bool × List Bool → Bool := fun xy ↦
      if xy.2.headD false then
        !(xy.2.tail.headD true) || xy.2.tail.all id
      else
        decide (encPair encBits encBits (xy.1, xy.2.tail.take (p.eval xy.1.length)) ∈ B)
    have hV : ComputableInPolyTimeWithOracle B V (encPair encBits encBits) encBool := by
      have hx : ComputableInPolyTime (fun xy : List Bool × List Bool ↦ xy.1)
          (encPair encBits encBits) encBits := ComputableInPolyTime.fst encBits encBits
      have hy : ComputableInPolyTime (fun xy : List Bool × List Bool ↦ xy.2)
          (encPair encBits encBits) encBits := ComputableInPolyTime.snd encBits encBits
      have hyt : ComputableInPolyTime (fun xy : List Bool × List Bool ↦ xy.2.tail)
          (encPair encBits encBits) encBits := ComputableInPolyTime.bitsTail.comp hy
      have hhead : ComputableInPolyTime (fun xy : List Bool × List Bool ↦ xy.2.headD false)
          (encPair encBits encBits) encBool :=
        (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp hy
      have htrueBranch : ComputableInPolyTime
          (fun xy : List Bool × List Bool ↦ !(xy.2.tail.headD true) || xy.2.tail.all id)
          (encPair encBits encBits) encBool :=
        ComputableInPolyTime.bool_or'
          (ComputableInPolyTime.bool_not.comp
            ((ComputableInPolyTime.headD (encA := encBool) (encL := encBits) true).comp hyt))
          (computableInPolyTime_bitsAll.comp hyt)
      have hlen : ComputableInPolyTime (fun xy : List Bool × List Bool ↦ p.eval xy.1.length)
          (encPair encBits encBits) encUnary :=
        (ComputableInPolyTime.unary_eval p).comp
          ((ComputableInPolyTime.encoding_length encBits).comp hx)
      have hreq : ComputableInPolyTime
          (fun xy : List Bool × List Bool ↦
            encPair encBits encBits (xy.1, xy.2.tail.take (p.eval xy.1.length)))
          (encPair encBits encBits) encBits :=
        (hx.prod (ComputableInPolyTime.bitsTakeWithInput hyt hlen)).of_enc_eq fun _ ↦ rfl
      have hfalseBranch : ComputableInPolyTimeWithOracle B
          (fun xy : List Bool × List Bool ↦
            decide (encPair encBits encBits (xy.1, xy.2.tail.take (p.eval xy.1.length)) ∈ B))
          (encPair encBits encBits) encBool :=
        (computableInPolyTimeWithOracle_mem B).preprocess hreq
      have hcomb := ((hhead.prod htrueBranch).computableInPolyTimeWithOracle B).prod hfalseBranch
      have hsel : ComputableInPolyTime
          (fun q : (Bool × Bool) × Bool ↦ if q.1.1 then q.1.2 else q.2)
          (encPair (encPair encBool encBool) encBool) encBool :=
        ComputableInPolyTime.ite'
          ((ComputableInPolyTime.fst encBool encBool).comp
            (ComputableInPolyTime.fst (encPair encBool encBool) encBool))
          ((ComputableInPolyTime.snd encBool encBool).comp
            (ComputableInPolyTime.fst (encPair encBool encBool) encBool))
          (ComputableInPolyTime.snd (encPair encBool encBool) encBool)
      exact hcomb.map hsel
    refine ⟨p' + 1, V, hV, fun x ↦ ?_⟩
    have heval : (p' + 1).eval (encBits x).length = p'.eval x.length + 1 := by simp
    change x ∈ A ↔
      2 ^ (p' + 1).eval (encBits x).length < 2 * acceptCount V x ((p' + 1).eval (encBits x).length)
    rw [heval, acceptCount]
    rw [card_filter_succ_split (p'.eval x.length) (P := fun y ↦ V (x, y) = true)]
    have hleft : (Finset.univ.filter fun y : Fin (p'.eval x.length) → Bool ↦
        V (x, false :: List.ofFn y) = true).card =
        (Finset.univ.filter fun y : Fin (p'.eval x.length) → Bool ↦
          encPair encBits encBits (x, (List.ofFn y).take (p.eval x.length)) ∈ B).card := by
      apply card_filter_congr_iff
      intro y
      simp only [V, List.headD_cons, Bool.false_eq_true, ↓reduceIte, List.tail_cons]
      exact decide_eq_true_iff
    have hright : (Finset.univ.filter fun y : Fin (p'.eval x.length) → Bool ↦
        V (x, true :: List.ofFn y) = true).card =
        2 ^ (p'.eval x.length - 1) + 1 := by
      rw [card_filter_congr_iff (Q := fun y : Fin (p'.eval x.length) → Bool ↦
        (List.ofFn y).headD true = false ∨ (List.ofFn y).all id = true) (fun y ↦ by
          simp only [V, List.headD_cons, ↓reduceIte, List.tail_cons, Bool.or_eq_true,
            Bool.not_eq_true'])]
      exact card_filter_headFalse_or_allTrue (hp'_pos x.length)
    rw [hleft, hright]
    set m := p'.eval x.length
    have hm1 : 1 ≤ m := hp'_pos x.length
    have h2m : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have : m = m - 1 + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    have hAiff : x ∈ A ↔ 2 ^ m ≤
        2 * (Finset.univ.filter fun y : Fin m → Bool ↦
          encPair encBits encBits (x, (List.ofFn y).take (p.eval x.length)) ∈ B).card := by
      rw [hAB x]
      rw [card_filter_congr_iff (Q := fun y : Fin (p.eval x.length) → Bool ↦
        encPair encBits encBits (x, List.ofFn y) ∈ B) (fun _ ↦ Iff.rfl)]
      exact (nonstrictMajority_take_iff (hp_le x.length)
        (fun u ↦ encPair encBits encBits (x, u) ∈ B)).symm
    rw [hAiff, pow_succ']
    omega

/-- **Torán's equivalence:** Wagner's counting hierarchy `CH` coincides with the union of the oracle
counting levels `⋃ a, CountingLevel a encBits`. -/
theorem CH_eq_iUnion_CountingLevel : CH = ⋃ a, CountingLevel a encBits := by
  ext L
  rw [mem_CH_iff, Set.mem_iUnion]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, CHLevel_subset_CountingLevel a ha⟩,
    fun ⟨a, ha⟩ ↦ ⟨3 * a, CountingLevel_subset_CHLevel a ha⟩⟩

/-! ### Closure and advice lifting for `CH` and `CHPoly` -/

/-- `CH` is closed under polynomial-time many-one reductions. -/
theorem PolyTimeReducible.mem_CH {A B : Set (List Bool)}
    (h : PolyTimeReducible encBits encBits A B) (hB : B ∈ CH) : A ∈ CH := by
  rw [mem_CH_iff] at hB ⊢
  obtain ⟨k, hk⟩ := hB
  exact ⟨k, PolyTimeReducible.mem_CHLevel h hk⟩

/-- `CH` is closed under complement. -/
theorem compl_mem_CH {A : Set (List Bool)} (hA : A ∈ CH) : Aᶜ ∈ CH := by
  rw [mem_CH_iff] at hA ⊢
  obtain ⟨k, hk⟩ := hA
  exact ⟨k, compl_mem_CHLevel hk⟩

/-- Every Boolean `CountingFunction` defines a language in `CH`. -/
theorem mem_CH_of_countingFunction {a : ℕ} {f : List Bool → Bool}
    (hf : f ∈ CountingFunction a encBits encBool) : {w | f w = true} ∈ CH := by
  rw [CH_eq_iUnion_CountingLevel, Set.mem_iUnion]
  exact ⟨a + 1, CountingFunction.decision hf⟩


end CslibFrontier.Complexity
