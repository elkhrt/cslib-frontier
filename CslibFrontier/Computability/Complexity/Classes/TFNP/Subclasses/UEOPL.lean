/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.Completeness
public import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.PotentialLineNormalization

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.List.GetD

/-!
# Unique End of Potential Line (`UEOPL`)

This module formalizes the total search complexity class `UEOPL` (*Unique End of Potential Line*)
introduced by Fearnley, Gordon, Mehta, and Savani, under standard Lean axioms, built
directly on the multi-tape Turing-machine and Boolean-circuit complexity hierarchy of
`Cslib.Complexity` (`FNP`, `TFNP`, `PLS`, `PPAD`, `EOPL`, `SOPL`, `SearchReducible`, and
`SearchComplete`).

An instance on vertex space `{0, 1}^n` is given by successor and predecessor maps
`S, P : {0, 1}^n → {0, 1}^n` and a potential (odometer) `V : {0, 1}^n → {0, …, 2^m - 1}`
satisfying the source promise `P(0^n) = 0^n ≠ S(0^n)` and `V(0^n) = 0`
(`Cslib.Complexity.PromisedPotentialLine`). The four solution types of *UniqueEOPL* are:

* **(U1)** a vertex `x ∈ {0, 1}^n` with `P(S(x)) ≠ x` (end of the line);
* **(UV1)** a vertex `x ∈ {0, 1}^n` with `x ≠ S(x)`, `P(S(x)) = x`, and `V(S(x)) ≤ V(x)` (failure of
  strict potential increase);
* **(UV2)** a vertex `x ∈ {0, 1}^n` with `S(P(x)) ≠ x` and `x ≠ 0^n` (start of a second line);
* **(UV3)** two vertices `x, y ∈ {0, 1}^n` with `x ≠ y`, `x ≠ S(x)`, `y ≠ S(y)`, and either
  `V(x) = V(y)` or `V(x) < V(y) < V(S(x))` (potential collision or potential-interval intrusion
  witnessing two distinct active lines).

Single-vertex solutions `(U1)/(UV1)/(UV2)` are encoded as `false :: x` of length `n + 1`, and
two-vertex solutions `(UV3)` are encoded as `true :: (x ++ y)` of length `2n + 1`. Following
`Cslib.Complexity.EOPL`, we prove equivalence between the uniform totalized family presentation,
the promised `(n + 1)`-bit normalized presentation with explicit binary potential width `m`, and
polynomial-time search reducibility to the canonical Boolean-circuit-presented problem `UniqueEOPL`
(`UniqueEOPL_searchComplete`). We also establish the subclass inclusions
`UEOPL ⊆ EOPL ⊆ SOPL`, `UEOPL ⊆ PLS`, `UEOPL ⊆ PPAD`, and `UEOPL ⊆ TFNP`, together with a reusable
single-active-line criterion `mem_UEOPL_of_singleLine` eliminating `(UV1)–(UV3)` violations.

## Main definitions

* `Cslib.Complexity.IsUniqueEOPLSolU1`, `Cslib.Complexity.IsUniqueEOPLSolUV1`,
  `Cslib.Complexity.IsUniqueEOPLSolUV2`, `Cslib.Complexity.IsUniqueEOPLSolUV3`: the four
  solution predicates `(U1)`, `(UV1)`, `(UV2)`, `(UV3)` of Fearnley et al.
* `Cslib.Complexity.uniqueEOPLPromisedRel`, `Cslib.Complexity.uniqueEOPLViolationRel`:
  promised and totalized *UniqueEOPL* search relations for uniform families.
* `Cslib.Complexity.UEOPL`: the complexity class of `FNP` search problems polynomial-time
  search-reducible to *UniqueEOPL*.
* `Cslib.Complexity.UniqueEOPLInstance`, `Cslib.Complexity.encUniqueEOPL`,
  `Cslib.Complexity.UniqueEOPL`: the canonical Boolean-circuit-presented *UniqueEOPL* total
  search problem.

## Main results

* `Cslib.Complexity.isTotalSearch_uniqueEOPLPromisedRel`,
  `Cslib.Complexity.isTotalSearch_uniqueEOPLViolationRel`: totality of *UniqueEOPL*.
* `Cslib.Complexity.SearchReducible.mem_UEOPL`: closure of `UEOPL` under `SearchReducible`.
* `Cslib.Complexity.UEOPL_subset_EOPL`, `Cslib.Complexity.UEOPL_subset_SOPL`,
  `Cslib.Complexity.UEOPL_subset_PLS`, `Cslib.Complexity.UEOPL_subset_PPAD`,
  `Cslib.Complexity.UEOPL_subset_TFNP`: inclusions of `UEOPL` into `EOPL`, `SOPL`, `PLS`,
  `PPAD`, and `TFNP`.
* `Cslib.Complexity.UniqueEOPL_mem_UEOPL`, `Cslib.Complexity.UniqueEOPL_searchComplete`,
  `Cslib.Complexity.mem_UEOPL_iff_searchReducible_UniqueEOPL`: `UEOPL`-completeness of the
  canonical Boolean-circuit *UniqueEOPL* problem.
* `Cslib.Complexity.mem_UEOPL_of_singleLine`: membership criterion in `UEOPL` for uniform
  single-line unit-step odometer families (handling even immediate termination at `0^n`).
-/

public section

namespace Cslib.Complexity

open Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

attribute [local irreducible] ComputableInPolyTime

private theorem cond_pt {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {c : α → Bool} {yes no : α → β}
    (hc : ComputableInPolyTime c encA encBool)
    (hyes : ComputableInPolyTime yes encA encB)
    (hno : ComputableInPolyTime no encA encB) :
    ComputableInPolyTime (fun a => if c a then yes a else no a) encA encB :=
  hc.ite hyes hno

attribute [local fun_prop] bool_and' bool_or' cond_pt binary_le' binary_lt'

section SolutionPredicates

variable {α : Type}

/-- Solution type **(U1)** of *UniqueEOPL*: a point `x` with `P(S(x)) ≠ x` (an end of the line). -/
def IsUniqueEOPLSolU1 (P S : α × List Bool → List Bool) (a : α) (x : List Bool) : Prop :=
  P (a, S (a, x)) ≠ x

/-- Solution type **(UV1)** of *UniqueEOPL*: an active edge `x → S(x)` (`x ≠ S(x)` and
`P(S(x)) = x`) along which the potential `V` fails to strictly increase (`V(S(x)) ≤ V(x)`). -/
def IsUniqueEOPLSolUV1 (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ)
    (a : α) (x : List Bool) : Prop :=
  x ≠ S (a, x) ∧ P (a, S (a, x)) = x ∧ V (a, S (a, x)) ≤ V (a, x)

/-- Solution type **(UV2)** of *UniqueEOPL*: a point `x ≠ 0^n` with `S(P(x)) ≠ x` (start of a line
distinct from the canonical line at `0^n`). -/
def IsUniqueEOPLSolUV2 (n : α → ℕ) (P S : α × List Bool → List Bool)
    (a : α) (x : List Bool) : Prop :=
  S (a, P (a, x)) ≠ x ∧ x ≠ zeroVertex (n a)

/-- Solution type **(UV3)** of *UniqueEOPL*: two distinct non-fixed points `x ≠ y` (`x ≠ S(x)` and
`y ≠ S(y)`) that either share the same potential `V(x) =
  V(y)` or satisfy `V(x) < V(y) < V(S(x))`. -/
def IsUniqueEOPLSolUV3 (S : α × List Bool → List Bool) (V : α × List Bool → ℕ)
    (a : α) (x y : List Bool) : Prop :=
  x ≠ y ∧ x ≠ S (a, x) ∧ y ≠ S (a, y) ∧
    (V (a, x) = V (a, y) ∨ (V (a, x) < V (a, y) ∧ V (a, y) < V (a, S (a, x))))

/-- Promised *UniqueEOPL* search relation of Fearnley, Gordon, Mehta, and Savani: a solution `w` is
either `false :: x` for `x ∈ {0, 1}^{n a}` satisfying `(U1)`, `(UV1)`, or `(UV2)`, or
`true :: (x ++ y)` for `x, y ∈ {0, 1}^{n a}` satisfying `(UV3)`. -/
def uniqueEOPLPromisedRel (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) (w : List Bool) : Prop :=
  (∃ x, w = false :: x ∧ x.length = n a ∧
    (IsUniqueEOPLSolU1 P S a x ∨ IsUniqueEOPLSolUV1 P S V a x ∨
      IsUniqueEOPLSolUV2 n P S a x)) ∨
  (∃ x y, w = true :: (x ++ y) ∧ x.length = n a ∧ y.length = n a ∧
    IsUniqueEOPLSolUV3 S V a x y)

/-- Totalized *UniqueEOPL* search relation: accepts all `uniqueEOPLPromisedRel` solutions and also
accepts the fallback witness `false :: 0^{n a}` whenever the syntactic source promise
`PromisedPotentialLine n P S V a` (`P(0^n) = 0^n ≠ S(0^n)` and `V(0^n) = 0`) fails. -/
def uniqueEOPLViolationRel (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) (w : List Bool) : Prop :=
  (w = false :: zeroVertex (n a) ∧ ¬PromisedPotentialLine n P S V a) ∨
    uniqueEOPLPromisedRel n P S V a w

/-- Computable Boolean decider for `uniqueEOPLPromisedRel`. -/
def checkUniqueEOPLPromised (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (p : α × List Bool) : Bool :=
  !p.2.isEmpty &&
    if p.2.headD false then
      let x := p.2.tail.take (n p.1)
      let y := p.2.tail.drop (n p.1)
      decide (p.2.tail.length = 2 * n p.1) &&
        decide (x ≠ y) && decide (x ≠ S (p.1, x)) && decide (y ≠ S (p.1, y)) &&
        (decide (V (p.1, x) = V (p.1, y)) ||
          (decide (V (p.1, x) < V (p.1, y)) && decide (V (p.1, y) < V (p.1, S (p.1, x)))))
    else
      let x := p.2.tail
      decide (x.length = n p.1) &&
        (decide (P (p.1, S (p.1, x)) ≠ x) ||
          (decide (x ≠ S (p.1, x)) && decide (P (p.1, S (p.1, x)) = x) &&
            decide (V (p.1, S (p.1, x)) ≤ V (p.1, x))) ||
          (decide (S (p.1, P (p.1, x)) ≠ x) && decide (x ≠ zeroVertex (n p.1))))

/-- Computable Boolean decider for the source promise `PromisedPotentialLine`. -/
def checkPromisedPotentialLine (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) : Bool :=
  decide (P (a, zeroVertex (n a)) = zeroVertex (n a)) &&
    decide (S (a, zeroVertex (n a)) ≠ zeroVertex (n a)) &&
    decide (V (a, zeroVertex (n a)) = 0)

/-- Computable Boolean decider for `uniqueEOPLViolationRel`. -/
def checkUniqueEOPLViolation (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (p : α × List Bool) : Bool :=
  (decide (p.2 = false :: zeroVertex (n p.1)) && !checkPromisedPotentialLine n P S V p.1) ||
    checkUniqueEOPLPromised n P S V p

variable {n : α → ℕ} {P S : α × List Bool → List Bool} {V : α × List Bool → ℕ}
  {a : α} {x w : List Bool}

/-- `checkPromisedPotentialLine` decides `PromisedPotentialLine`. -/
theorem checkPromisedPotentialLine_eq_true_iff :
    checkPromisedPotentialLine n P S V a = true ↔ PromisedPotentialLine n P S V a := by
  simp only [checkPromisedPotentialLine, PromisedPotentialLine, LineSourcePromise,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- `checkUniqueEOPLPromised` decides `uniqueEOPLPromisedRel`. -/
theorem checkUniqueEOPLPromised_eq_true_iff :
    checkUniqueEOPLPromised n P S V (a, w) = true ↔ uniqueEOPLPromisedRel n P S V a w := by
  rcases w with _ | ⟨_ | _, t⟩
  · simp only [checkUniqueEOPLPromised, List.isEmpty_nil, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, uniqueEOPLPromisedRel, reduceCtorEq, false_and, exists_false, or_self]
  · change (decide (t.length = n a) &&
        (decide (P (a, S (a, t)) ≠ t) ||
          (decide (t ≠ S (a, t)) && decide (P (a, S (a, t)) = t) &&
            decide (V (a, S (a, t)) ≤ V (a, t))) ||
          (decide (S (a, P (a, t)) ≠ t) && decide (t ≠ zeroVertex (n a))))) = true ↔ _
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, uniqueEOPLPromisedRel,
      List.cons.injEq, true_and, exists_eq_left', reduceCtorEq, false_and, exists_false, or_false,
      IsUniqueEOPLSolU1, IsUniqueEOPLSolUV1, IsUniqueEOPLSolUV2, and_assoc, or_assoc]
  · change (decide (t.length = 2 * n a) &&
        decide (t.take (n a) ≠ t.drop (n a)) &&
        decide (t.take (n a) ≠ S (a, t.take (n a))) &&
        decide (t.drop (n a) ≠ S (a, t.drop (n a))) &&
        (decide (V (a, t.take (n a)) = V (a, t.drop (n a))) ||
          (decide (V (a, t.take (n a)) < V (a, t.drop (n a))) &&
            decide (V (a, t.drop (n a)) < V (a, S (a, t.take (n a))))))) = true ↔ _
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, uniqueEOPLPromisedRel,
      List.cons.injEq, reduceCtorEq, false_and, exists_false, true_and, false_or,
      IsUniqueEOPLSolUV3, and_assoc]
    constructor
    · rintro ⟨htlen, hne, hxS, hyS, hV⟩
      refine ⟨t.take (n a), t.drop (n a), (List.take_append_drop (n a) t).symm, ?_, ?_,
        hne, hxS, hyS, hV⟩
      · rw [List.length_take]; omega
      · rw [List.length_drop]; omega
    · rintro ⟨x, y, rfl, hx, hy, hne, hxS, hyS, hV⟩
      have htk : (x ++ y).take (n a) = x := List.take_left' hx
      have hdr : (x ++ y).drop (n a) = y := List.drop_left' hx
      rw [htk, hdr, List.length_append, hx, hy]
      exact ⟨by omega, hne, hxS, hyS, hV⟩

/-- `checkUniqueEOPLViolation` decides `uniqueEOPLViolationRel`. -/
theorem checkUniqueEOPLViolation_eq_true_iff :
    checkUniqueEOPLViolation n P S V (a, w) = true ↔ uniqueEOPLViolationRel n P S V a w := by
  simp only [checkUniqueEOPLViolation, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, ← Bool.not_eq_true, checkPromisedPotentialLine_eq_true_iff,
    checkUniqueEOPLPromised_eq_true_iff, uniqueEOPLViolationRel]

/-- Under `PromisedPotentialLine`, the totalized and promised *UniqueEOPL* relations coincide. -/
theorem uniqueEOPLViolationRel_iff_promised_of_promise (h : PromisedPotentialLine n P S V a) :
    uniqueEOPLViolationRel n P S V a w ↔ uniqueEOPLPromisedRel n P S V a w := by
  simp only [uniqueEOPLViolationRel, h, not_true_eq_false, and_false, false_or]

/-- Every promised *UniqueEOPL* solution is a totalized *UniqueEOPL* solution. -/
theorem uniqueEOPLViolationRel_of_promised (h : uniqueEOPLPromisedRel n P S V a w) :
    uniqueEOPLViolationRel n P S V a w :=
  .inr h

/-- Every promised *EOPL* solution `x` (`(R1)` or `(R2)`) gives a single-vertex *UniqueEOPL*
solution `false :: x` (`(UV2)`, `(U1)`, or `(UV1)`). -/
theorem uniqueEOPLPromisedRel_of_eoplPromised (h : endOfPotentialLinePromisedRel n P S V a x) :
    uniqueEOPLPromisedRel n P S V a (false :: x) := by
  obtain ⟨hlen, hUV2 | hU1 | hUV1⟩ := h
  · exact .inl ⟨x, rfl, hlen, .inr (.inr hUV2)⟩
  · exact .inl ⟨x, rfl, hlen, .inl hU1⟩
  · exact .inl ⟨x, rfl, hlen, .inr (.inl hUV1)⟩

/-- Length bound on solutions of `uniqueEOPLPromisedRel`: every solution has length at most
`2 * n a + 1`. -/
theorem length_le_of_uniqueEOPLPromisedRel (h : uniqueEOPLPromisedRel n P S V a w) :
    w.length ≤ 2 * n a + 1 := by
  rcases h with ⟨x, rfl, hx, -⟩ | ⟨x, y, rfl, hx, hy, -⟩
  · simp only [List.length_cons, hx]; omega
  · simp only [List.length_cons, List.length_append, hx, hy]; omega

/-- Length bound on solutions of `uniqueEOPLViolationRel`: every solution has length at most
`2 * n a + 1`. -/
theorem length_le_of_uniqueEOPLViolationRel (h : uniqueEOPLViolationRel n P S V a w) :
    w.length ≤ 2 * n a + 1 := by
  rcases h with ⟨rfl, -⟩ | h
  · simp only [List.length_cons, length_zeroVertex]; omega
  · exact length_le_of_uniqueEOPLPromisedRel h

/-- **Totality of promised *UniqueEOPL*:** any width-preserving family satisfying
`LineSourcePromise` admits at least one solution in `uniqueEOPLPromisedRel`. -/
theorem isTotalSearch_uniqueEOPLPromisedRel (hprom : ∀ a, LineSourcePromise n P S a)
    (hP_len : PreservesWidth n P) (hS_len : PreservesWidth n S) :
    IsTotalSearch (uniqueEOPLPromisedRel n P S V) := fun a => by
  obtain ⟨x, hx⟩ := isTotalSearch_endOfPotentialLinePromisedRel (V := V) hprom hP_len hS_len a
  exact ⟨false :: x, uniqueEOPLPromisedRel_of_eoplPromised hx⟩

/-- **Totality of *UniqueEOPL*:** any width-preserving family admits at least one solution in
`uniqueEOPLViolationRel`. -/
theorem isTotalSearch_uniqueEOPLViolationRel
    (hP_len : PreservesWidth n P) (hS_len : PreservesWidth n S) :
    IsTotalSearch (uniqueEOPLViolationRel n P S V) := fun a => by
  by_cases hprom : PromisedPotentialLine n P S V a
  · obtain ⟨u, hu⟩ := isTotalSearch_endOfPotentialLineRel (P := P) (V := V) hS_len a
    have hv := (endOfPotentialLineViolationRel_iff_promised_of_promise hprom.1).mp
      (endOfPotentialLineViolationRel_potentialLineBack (hP_len a) hu)
    exact ⟨false :: potentialLineBack n P S V (a, u),
      .inr (uniqueEOPLPromisedRel_of_eoplPromised hv)⟩
  · exact ⟨false :: zeroVertex (n a), .inl ⟨rfl, hprom⟩⟩

end SolutionPredicates

/-! ### Polynomial-time computability and `FNP` / `TFNP` membership -/

section Computability

variable {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
  {P S : α × List Bool → List Bool} {V : α × List Bool → ℕ}

/-- Testing the source promise `PromisedPotentialLine` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_checkPromisedPotentialLine
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    ComputableInPolyTime (checkPromisedPotentialLine n P S V) enc encBool := by
  have hz : ComputableInPolyTime (fun a => (a, zeroVertex (n a))) enc (encPair enc encBits) :=
    ComputableInPolyTime.id'.prod (computableInPolyTime_zeroVertex_comp hn)
  have hPz := hP.comp hz
  have hSz := hS.comp hz
  have hVz := hV.comp hz
  have h0 := computableInPolyTime_zeroVertex_comp hn
  exact bool_and'
    (bool_and' (decide_eq' hPz h0) (bool_not.comp (decide_eq' hSz h0)))
    (decide_eq' hVz (const 0))

/-- Deciding `uniqueEOPLPromisedRel` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_checkUniqueEOPLPromised
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    ComputableInPolyTime (checkUniqueEOPLPromised n P S V) (encPair enc encBits) encBool := by
  have ha := fst enc encBits
  have hw := snd enc encBits
  have hna := hn.comp ha
  have h2n : ComputableInPolyTime (fun p : α × List Bool => 2 * n p.1)
      (encPair enc encBits) encUnary :=
    unary_mul.comp ((const 2).prod hna)
  have ht : ComputableInPolyTime (fun p : α × List Bool => p.2.tail)
      (encPair enc encBits) encBits := bitsTail.comp hw
  have hx2 := bitsTake.comp (ht.prod hna)
  have hy2 := bitsDropWithInput ht hna
  have hSx2 := hS.comp (ha.prod hx2)
  have hSy2 := hS.comp (ha.prod hy2)
  have hVx2 := hV.comp (ha.prod hx2)
  have hVy2 := hV.comp (ha.prod hy2)
  have hVSx2 := hV.comp (ha.prod hSx2)
  have hbranchT : ComputableInPolyTime
      (fun p : α × List Bool =>
        decide (p.2.tail.length = 2 * n p.1) &&
          decide (p.2.tail.take (n p.1) ≠ p.2.tail.drop (n p.1)) &&
          decide (p.2.tail.take (n p.1) ≠ S (p.1, p.2.tail.take (n p.1))) &&
          decide (p.2.tail.drop (n p.1) ≠ S (p.1, p.2.tail.drop (n p.1))) &&
          (decide (V (p.1, p.2.tail.take (n p.1)) = V (p.1, p.2.tail.drop (n p.1))) ||
            (decide (V (p.1, p.2.tail.take (n p.1)) < V (p.1, p.2.tail.drop (n p.1))) &&
              decide (V (p.1, p.2.tail.drop (n p.1)) <
                V (p.1, S (p.1, p.2.tail.take (n p.1)))))))
      (encPair enc encBits) encBool :=
    bool_and'
      (bool_and'
        (bool_and'
          (bool_and' (decide_eq' (length_bits.comp ht) h2n)
            (bool_not.comp (decide_eq' hx2 hy2)))
          (bool_not.comp (decide_eq' hx2 hSx2)))
        (bool_not.comp (decide_eq' hy2 hSy2)))
      (bool_or' (decide_eq' hVx2 hVy2)
        (bool_and' (binary_lt' hVx2 hVy2) (binary_lt' hVy2 hVSx2)))
  have hSt := hS.comp (ha.prod ht)
  have hPt := hP.comp (ha.prod ht)
  have hPSt := hP.comp (ha.prod hSt)
  have hSPt := hS.comp (ha.prod hPt)
  have hVt := hV.comp (ha.prod ht)
  have hVSt := hV.comp (ha.prod hSt)
  have hz := computableInPolyTime_zeroVertex_comp hna
  have hbranchF : ComputableInPolyTime
      (fun p : α × List Bool =>
        decide (p.2.tail.length = n p.1) &&
          (decide (P (p.1, S (p.1, p.2.tail)) ≠ p.2.tail) ||
            (decide (p.2.tail ≠ S (p.1, p.2.tail)) &&
              decide (P (p.1, S (p.1, p.2.tail)) = p.2.tail) &&
              decide (V (p.1, S (p.1, p.2.tail)) ≤ V (p.1, p.2.tail))) ||
            (decide (S (p.1, P (p.1, p.2.tail)) ≠ p.2.tail) &&
              decide (p.2.tail ≠ zeroVertex (n p.1)))))
      (encPair enc encBits) encBool :=
    bool_and' (decide_eq' (length_bits.comp ht) hna)
      (bool_or'
        (bool_or' (bool_not.comp (decide_eq' hPSt ht))
          (bool_and'
            (bool_and' (bool_not.comp (decide_eq' ht hSt)) (decide_eq' hPSt ht))
            (binary_le' hVSt hVt)))
        (bool_and' (bool_not.comp (decide_eq' hSPt ht)) (bool_not.comp (decide_eq' ht hz))))
  have hhead : ComputableInPolyTime (fun p : α × List Bool => p.2.headD false)
      (encPair enc encBits) encBool := by
    have hraw := decide_eq' (bitsTake.comp (hw.prod (const 1))) (const [true])
    convert hraw using 1; funext ⟨_, bs⟩; rcases bs with _ | ⟨_ | _, _⟩ <;> rfl
  have hempty : ComputableInPolyTime (fun p : α × List Bool => p.2.isEmpty)
      (encPair enc encBits) encBool := by
    have hraw := decide_eq' hw (const [])
    convert hraw using 1; funext ⟨_, bs⟩; rcases bs <;> rfl
  exact bool_and' (bool_not.comp hempty) (hhead.ite hbranchT hbranchF)

/-- Deciding `uniqueEOPLViolationRel` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_checkUniqueEOPLViolation
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    ComputableInPolyTime (checkUniqueEOPLViolation n P S V) (encPair enc encBits) encBool := by
  have ha := fst enc encBits
  have hw := snd enc encBits
  have hf0 := bitsCons (const false) (computableInPolyTime_zeroVertex_comp (hn.comp ha))
  have hprom := (computableInPolyTime_checkPromisedPotentialLine hn hP hS hV).comp ha
  unfold checkUniqueEOPLViolation
  exact bool_or' (bool_and' (decide_eq' hw hf0) (bool_not.comp hprom))
    (computableInPolyTime_checkUniqueEOPLPromised hn hP hS hV)

/-- A uniform polynomial-time family defines an `FNP` promised *UniqueEOPL* relation. -/
theorem uniqueEOPLPromisedRel_mem_FNP
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    uniqueEOPLPromisedRel n P S V ∈ FNP enc := by
  obtain ⟨p, hp⟩ := (polyBounded hn).exists_polynomial
  refine mem_FNP.mpr ⟨⟨2 * p + 1, fun a w hw => ?_⟩,
    checkUniqueEOPLPromised n P S V,
    computableInPolyTime_checkUniqueEOPLPromised hn hP hS hV,
    fun a w => checkUniqueEOPLPromised_eq_true_iff.symm⟩
  have hlen := length_le_of_uniqueEOPLPromisedRel hw
  have hpa := hp a
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

/-- A uniform polynomial-time family defines an `FNP` totalized *UniqueEOPL* relation. -/
theorem uniqueEOPLViolationRel_mem_FNP
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    uniqueEOPLViolationRel n P S V ∈ FNP enc := by
  obtain ⟨p, hp⟩ := (polyBounded hn).exists_polynomial
  refine mem_FNP.mpr ⟨⟨2 * p + 1, fun a w hw => ?_⟩,
    checkUniqueEOPLViolation n P S V,
    computableInPolyTime_checkUniqueEOPLViolation hn hP hS hV,
    fun a w => checkUniqueEOPLViolation_eq_true_iff.symm⟩
  have hlen := length_le_of_uniqueEOPLViolationRel hw
  have hpa := hp a
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

end Computability

/-! ### The complexity class `UEOPL` and its inclusions in `EOPL`, `SOPL`, `PLS`, `PPAD`, `TFNP` -/

section Class

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
  {R : α → List Bool → Prop} {T : β → List Bool → Prop}

/-- **Unique End of Potential Line (`UEOPL`)**: the
class of `FNP` search problems polynomial-time search-reducible to finding a *UniqueEOPL* solution
of a uniform polynomial-time width-preserving family `(n, P, S, V)`.
-/
def UEOPL (enc : α ↪ List Bool) : Set (α → List Bool → Prop) :=
  {R | R ∈ FNP enc ∧ ∃ (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ),
    ComputableInPolyTime n enc encUnary ∧
    ComputableInPolyTime P (encPair enc encBits) encBits ∧
    ComputableInPolyTime S (encPair enc encBits) encBits ∧
    ComputableInPolyTime V (encPair enc encBits) encNat ∧
    PreservesWidth n P ∧ PreservesWidth n S ∧
    SearchReducible enc enc R (uniqueEOPLViolationRel n P S V)}

/-- Characterization of membership in `UEOPL`. -/
theorem mem_UEOPL : R ∈ UEOPL enc ↔ R ∈ FNP enc ∧
    ∃ (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ),
      ComputableInPolyTime n enc encUnary ∧
      ComputableInPolyTime P (encPair enc encBits) encBits ∧
      ComputableInPolyTime S (encPair enc encBits) encBits ∧
      ComputableInPolyTime V (encPair enc encBits) encNat ∧
      PreservesWidth n P ∧ PreservesWidth n S ∧
      SearchReducible enc enc R (uniqueEOPLViolationRel n P S V) :=
  Iff.rfl

/-- Every uniform polynomial-time width-preserving *UniqueEOPL* family lies in `UEOPL`. -/
theorem uniqueEOPLViolationRel_mem_UEOPL {n : α → ℕ} {P S : α × List Bool → List Bool}
    {V : α × List Bool → ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat)
    (hP_len : PreservesWidth n P) (hS_len : PreservesWidth n S) :
    uniqueEOPLViolationRel n P S V ∈ UEOPL enc :=
  ⟨uniqueEOPLViolationRel_mem_FNP hn hP hS hV, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len,
    .refl _ _⟩

/-- Every promised uniform polynomial-time width-preserving *UniqueEOPL* family lies in `UEOPL`. -/
theorem uniqueEOPLPromisedRel_mem_UEOPL {n : α → ℕ} {P S : α × List Bool → List Bool}
    {V : α × List Bool → ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat)
    (hP_len : PreservesWidth n P) (hS_len : PreservesWidth n S)
    (hprom : ∀ a, PromisedPotentialLine n P S V a) :
    uniqueEOPLPromisedRel n P S V ∈ UEOPL enc :=
  ⟨uniqueEOPLPromisedRel_mem_FNP hn hP hS hV, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len,
    .of_isTotalSearch (isTotalSearch_uniqueEOPLViolationRel hP_len hS_len)
      ComputableInPolyTime.id' (snd enc encBits) fun a _ hw =>
      (uniqueEOPLViolationRel_iff_promised_of_promise (hprom a)).mp hw⟩

/-- `UEOPL` is closed under polynomial-time search reductions across arbitrary instance types. -/
theorem SearchReducible.mem_UEOPL (h : SearchReducible enc encB R T) (hR : R ∈ FNP enc)
    (hT : T ∈ UEOPL encB) : R ∈ UEOPL enc := by
  obtain ⟨-, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hT⟩ := hT
  obtain ⟨f, hf, hred⟩ := (h.trans hT).exists_reindex
  have hpair := (hf.comp (fst enc encBits)).prod (snd enc encBits)
  exact ⟨hR, n ∘ f, fun p => P (f p.1, p.2), fun p => S (f p.1, p.2), fun p => V (f p.1, p.2),
    hn.comp hf, hP.comp hpair, hS.comp hpair, hV.comp hpair,
    fun a => hP_len (f a), fun a => hS_len (f a), hred⟩

/-- **`UEOPL ⊆ TFNP`:** every search problem in `UEOPL` is total and lies in `FNP`. -/
theorem UEOPL_subset_TFNP : UEOPL enc ⊆ TFNP enc := by
  rintro R ⟨hR, n, P, S, V, -, -, -, -, hP_len, hS_len, hred⟩
  exact ⟨hR, hred.isTotalSearch (isTotalSearch_uniqueEOPLViolationRel hP_len hS_len)⟩

/-- **`UEOPL ⊆ EOPL`**: every `(R1)` or `(R2)` solution
of *End-of-Potential-Line* is immediately a `(U1)`, `(UV1)`, or `(UV2)` solution of *UniqueEOPL*.
-/
theorem UEOPL_subset_EOPL : UEOPL enc ⊆ EOPL enc := by
  rintro R ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hred⟩
  let back (p : α × List Bool) : List Bool :=
    if checkPromisedPotentialLine n P S V p.1 then false :: p.2
    else false :: zeroVertex (n p.1)
  have hback : ComputableInPolyTime back (encPair enc encBits) encBits := by
    have ha := fst enc encBits
    have hw := snd enc encBits
    exact ((computableInPolyTime_checkPromisedPotentialLine hn hP hS hV).comp ha).ite
      (bitsCons (const false) hw)
      (bitsCons (const false) (computableInPolyTime_zeroVertex_comp (hn.comp ha)))
  have htot : IsTotalSearch (endOfPotentialLineViolationRel n P S V) := fun a => by
    obtain ⟨u, hu⟩ := isTotalSearch_endOfPotentialLineRel (P := P) (V := V) hS_len a
    exact ⟨_, endOfPotentialLineViolationRel_potentialLineBack (hP_len a) hu⟩
  have hstep : SearchReducible enc enc (uniqueEOPLViolationRel n P S V)
      (endOfPotentialLineViolationRel n P S V) :=
    .of_isTotalSearch htot ComputableInPolyTime.id' hback fun a x hx => by
      dsimp only [back]
      cases hcp : checkPromisedPotentialLine n P S V a
      · refine .inl ⟨rfl, fun hp => ?_⟩
        rw [checkPromisedPotentialLine_eq_true_iff.mpr hp] at hcp
        exact Bool.false_ne_true hcp.symm
      · have hp := checkPromisedPotentialLine_eq_true_iff.mp hcp
        have hxp := (endOfPotentialLineViolationRel_iff_promised_of_promise hp.1).mp hx
        exact .inr (uniqueEOPLPromisedRel_of_eoplPromised hxp)
  exact mem_EOPL_iff_violation.mpr
    ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hred.trans hstep⟩

/-- **`UEOPL ⊆ SOPL`.** -/
theorem UEOPL_subset_SOPL : UEOPL enc ⊆ SOPL enc :=
  UEOPL_subset_EOPL.trans EOPL_subset_SOPL

/-- **`UEOPL ⊆ PLS`:** every search problem in `UEOPL` lies in `PLS`. -/
theorem UEOPL_subset_PLS : UEOPL enc ⊆ PLS enc :=
  UEOPL_subset_EOPL.trans EOPL_subset_PLS

/-- **`UEOPL ⊆ PPAD`:** every search problem in `UEOPL` lies in `PPAD`. -/
theorem UEOPL_subset_PPAD : UEOPL enc ⊆ PPAD enc :=
  UEOPL_subset_EOPL.trans EOPL_subset_PPAD

/-- **`UEOPL ⊆ PLS ∩ PPAD`.** -/
theorem UEOPL_subset_PLS_inter_PPAD : UEOPL enc ⊆ PLS enc ∩ PPAD enc :=
  fun _ h => ⟨UEOPL_subset_PLS h, UEOPL_subset_PPAD h⟩

end Class

/-! ### Promised `(n + 1)`-bit embedding and canonical Boolean-circuit `UniqueEOPL` completeness -/

section PromisedEmbedding

variable {α : Type}

/-- Padded predecessor map on `{0, 1}^{n a + 1}` enforcing `PromisedPotentialLine` unconditionally:
when `useInner a = true`, embeds `(P, S, V)` on `{true} × {0, 1}^{n a}` with source edge
`false :: 0^{n a} → true :: 0^{n a}`; when `useInner a = false`, creates the single-edge line
`false :: 0^{n a} → true :: 0^{n a}` with all other vertices isolated. -/
def ueoplPadPred (useInner : α → Bool) (n : α → ℕ) (P : α × List Bool → List Bool)
    (p : α × List Bool) : List Bool :=
  if p.2.headD false then
    if decide (p.2.tail = zeroVertex (n p.1)) then
      false :: zeroVertex (n p.1)
    else if useInner p.1 then
      true :: P (p.1, p.2.tail)
    else
      true :: p.2.tail
  else
    false :: p.2.tail

/-- Padded successor map on `{0, 1}^{n a + 1}` paired with `ueoplPadPred`. -/
def ueoplPadSucc (useInner : α → Bool) (n : α → ℕ) (S : α × List Bool → List Bool)
    (p : α × List Bool) : List Bool :=
  if p.2.headD false then
    if useInner p.1 then
      true :: S (p.1, p.2.tail)
    else
      true :: p.2.tail
  else if decide (p.2.tail = zeroVertex (n p.1)) then
    true :: zeroVertex (n p.1)
  else
    false :: p.2.tail

/-- Padded potential map on `{0, 1}^{n a + 1}` paired with `ueoplPadPred` and `ueoplPadSucc`:
assigns `0` to all `false :: u`, `V(a, u) + 1` to `true :: u` when `useInner a = true`, and `1`
to `true :: 0^{n a}` (else `0`) when `useInner a = false`. -/
def ueoplPadPotential (useInner : α → Bool) (n : α → ℕ) (V : α × List Bool → ℕ)
    (p : α × List Bool) : ℕ :=
  if p.2.headD false then
    if useInner p.1 then
      V (p.1, p.2.tail) + 1
    else if decide (p.2.tail = zeroVertex (n p.1)) then 1 else 0
  else 0

/-- The padded family unconditionally satisfies `PromisedPotentialLine` on width `n a + 1`. -/
theorem promisedPotentialLine_ueoplPad (useInner : α → Bool) (n : α → ℕ)
    (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ) (a : α) :
    PromisedPotentialLine (fun a => n a + 1) (ueoplPadPred useInner n P)
      (ueoplPadSucc useInner n S) (ueoplPadPotential useInner n V) a := by
  have hz : zeroVertex (n a + 1) = false :: zeroVertex (n a) := List.replicate_succ
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hz]; rfl
  · rw [hz]
    have hS0 : ueoplPadSucc useInner n S (a, false :: zeroVertex (n a)) =
        true :: zeroVertex (n a) := by
      change (if decide (zeroVertex (n a) = zeroVertex (n a)) then true :: zeroVertex (n a)
        else false :: zeroVertex (n a)) = _
      rw [ite_eq_left (decide_eq_true rfl)]
    rw [hS0]; intro h; cases h
  · rw [hz]; rfl

/-- `ueoplPadPred` preserves width `n a + 1` whenever `P` preserves width `n a`. -/
theorem preservesWidth_ueoplPadPred {useInner : α → Bool} {n : α → ℕ}
    {P : α × List Bool → List Bool} (hP : PreservesWidth n P) :
    PreservesWidth (fun a => n a + 1) (ueoplPadPred useInner n P) := by
  intro a w hw
  rcases w with _ | ⟨b, u⟩
  · simp only [List.length_nil] at hw; omega
  · have hu : u.length = n a := by simp only [List.length_cons] at hw; omega
    cases b <;> simp only [ueoplPadPred, List.headD_cons, List.tail_cons, Bool.false_eq_true,
      ↓reduceIte]
    · simp only [List.length_cons, hu]
    · split_ifs <;> simp only [List.length_cons, length_zeroVertex, hu, hP a u hu]

/-- `ueoplPadSucc` preserves width `n a + 1` whenever `S` preserves width `n a`. -/
theorem preservesWidth_ueoplPadSucc {useInner : α → Bool} {n : α → ℕ}
    {S : α × List Bool → List Bool} (hS : PreservesWidth n S) :
    PreservesWidth (fun a => n a + 1) (ueoplPadSucc useInner n S) := by
  intro a w hw
  rcases w with _ | ⟨b, u⟩
  · simp only [List.length_nil] at hw; omega
  · have hu : u.length = n a := by simp only [List.length_cons] at hw; omega
    cases b <;> simp only [ueoplPadSucc, List.headD_cons, List.tail_cons, Bool.false_eq_true,
      ↓reduceIte]
    · split_ifs <;> simp only [List.length_cons, length_zeroVertex, hu]
    · split_ifs <;> simp only [List.length_cons, hu, hS a u hu]

/-- When `useInner a = true` and `P(0^n) = 0^n` and `V(0^n) = 0`, every single-vertex solution of
the padded family is `true :: x` where either `x = 0^n = S(0^n)` or `x` is a `(U1)/(UV1)/(UV2)`
solution of `(n, P, S, V)`. -/
private theorem ueoplPad_single_sound {useInner : α → Bool} {n : α → ℕ}
    {P S : α × List Bool → List Bool} {V : α × List Bool → ℕ} {a : α} {z : List Bool}
    (hui : useInner a = true) (hP0 : P (a, zeroVertex (n a)) = zeroVertex (n a))
    (hV0 : V (a, zeroVertex (n a)) = 0) (hz : z.length = n a + 1)
    (hsol : IsUniqueEOPLSolU1 (ueoplPadPred useInner n P) (ueoplPadSucc useInner n S) a z ∨
      IsUniqueEOPLSolUV1 (ueoplPadPred useInner n P) (ueoplPadSucc useInner n S)
        (ueoplPadPotential useInner n V) a z ∨
      IsUniqueEOPLSolUV2 (fun a => n a + 1) (ueoplPadPred useInner n P)
        (ueoplPadSucc useInner n S) a z) :
    ∃ x, z = true :: x ∧ x.length = n a ∧
      ((x = zeroVertex (n a) ∧ S (a, x) = x) ∨
        IsUniqueEOPLSolU1 P S a x ∨ IsUniqueEOPLSolUV1 P S V a x ∨
        IsUniqueEOPLSolUV2 n P S a x) := by
  have hz0 : zeroVertex (n a + 1) = false :: zeroVertex (n a) := List.replicate_succ
  rcases z with _ | ⟨b, x⟩
  · simp only [List.length_nil] at hz; omega
  have hx : x.length = n a := by simp only [List.length_cons] at hz; omega
  cases b
  · exfalso
    by_cases hx0 : x = zeroVertex (n a)
    · subst hx0
      rcases hsol with h1 | ⟨_, _, hV⟩ | ⟨_, hne⟩
      · apply h1
        simp only [ueoplPadSucc, ueoplPadPred, List.headD_cons, List.tail_cons,
          Bool.false_eq_true, ↓reduceIte, decide_true]
      · simp only [ueoplPadSucc, ueoplPadPotential, List.headD_cons, List.tail_cons,
          Bool.false_eq_true, ↓reduceIte, decide_true, hui, hV0] at hV
        omega
      · exact hne hz0.symm
    · have hSf : ueoplPadSucc useInner n S (a, false :: x) = false :: x := by
        change (if decide (x = zeroVertex (n a)) then true :: zeroVertex (n a) else false :: x) = _
        exact ite_eq_right (by rw [decide_eq_false hx0]; decide)
      have hPf : ueoplPadPred useInner n P (a, false :: x) = false :: x := rfl
      rcases hsol with h1 | ⟨hne, _, _⟩ | ⟨h2, _⟩
      · exact h1 (by rw [hSf, hPf])
      · exact hne hSf.symm
      · exact h2 (by rw [hPf, hSf])
  · refine ⟨x, rfl, hx, ?_⟩
    rcases hsol with h1 | ⟨hne, hPS, hV⟩ | ⟨h2, _⟩
    · dsimp only [IsUniqueEOPLSolU1, ueoplPadSucc, ueoplPadPred] at h1
      simp only [↓reduceIte, hui, List.headD_cons, List.tail_cons] at h1
      by_cases hS0 : S (a, x) = zeroVertex (n a)
      · by_cases hx0 : x = zeroVertex (n a)
        · exact .inl ⟨hx0, hS0.trans hx0.symm⟩
        · exact .inr (.inl fun hPSx => hx0 (by rw [← hPSx, hS0, hP0]))
      · simp only [decide_eq_false hS0, Bool.false_eq_true, ↓reduceIte, ne_eq, List.cons.injEq,
          true_and] at h1
        exact .inr (.inl h1)
    · dsimp only [ueoplPadSucc, ueoplPadPred, ueoplPadPotential] at hne hPS hV
      simp only [↓reduceIte, hui, List.headD_cons, List.tail_cons, ne_eq, List.cons.injEq,
        true_and] at hne hPS hV
      by_cases hS0 : S (a, x) = zeroVertex (n a)
      · simp only [decide_eq_true hS0, ↓reduceIte] at hPS; cases hPS
      · simp only [decide_eq_false hS0, Bool.false_eq_true, ↓reduceIte, List.cons.injEq,
          true_and] at hPS
        exact .inr (.inr (.inl ⟨hne, hPS, by omega⟩))
    · by_cases hx0 : x = zeroVertex (n a)
      · exfalso; apply h2; rw [hx0]; dsimp only [ueoplPadPred, ueoplPadSucc]
        simp only [↓reduceIte, decide_true, List.headD_cons, List.tail_cons, Bool.false_eq_true]
      · have hPt : ueoplPadPred useInner n P (a, true :: x) = true :: P (a, x) := by
          change (if decide (x = zeroVertex (n a)) then false :: zeroVertex (n a)
            else if useInner a then true :: P (a, x) else true :: x) = _
          rw [ite_eq_right (by rw [decide_eq_false hx0]; decide), ite_eq_left hui]
        have hSt : ueoplPadSucc useInner n S (a, true :: P (a, x)) =
            true :: S (a, P (a, x)) := by
          change (if useInner a then true :: S (a, P (a, x)) else true :: P (a, x)) = _
          exact ite_eq_left hui
        rw [hPt, hSt] at h2
        exact .inr (.inr (.inr ⟨fun h => h2 (congrArg (true :: ·) h), hx0⟩))

/-- When `useInner a = true` and `V(0^n) = 0`, every two-vertex `(UV3)` solution `(z₁, z₂)` of the
padded family has `z₁ = true :: x` and `z₂ = true :: y` where `(x, y)` is a `(UV3)` solution of
`(n, P, S, V)`. -/
private theorem ueoplPad_pair_sound {useInner : α → Bool} {n : α → ℕ}
    {S : α × List Bool → List Bool} {V : α × List Bool → ℕ} {a : α} {z₁ z₂ : List Bool}
    (hui : useInner a = true) (hV0 : V (a, zeroVertex (n a)) = 0)
    (hz₁ : z₁.length = n a + 1) (hz₂ : z₂.length = n a + 1)
    (hsol : IsUniqueEOPLSolUV3 (ueoplPadSucc useInner n S) (ueoplPadPotential useInner n V)
      a z₁ z₂) :
    ∃ x y, z₁ = true :: x ∧ z₂ = true :: y ∧ x.length = n a ∧ y.length = n a ∧
      IsUniqueEOPLSolUV3 S V a x y := by
  rcases z₁ with _ | ⟨b₁, x⟩
  · simp only [List.length_nil] at hz₁; omega
  rcases z₂ with _ | ⟨b₂, y⟩
  · simp only [List.length_nil] at hz₂; omega
  have hx : x.length = n a := by simp only [List.length_cons] at hz₁; omega
  have hy : y.length = n a := by simp only [List.length_cons] at hz₂; omega
  obtain ⟨hne, hS₁, hS₂, hV⟩ := hsol
  have hfalse_eq {u : List Bool} (h : false :: u ≠ ueoplPadSucc useInner n S (a, false :: u)) :
      u = zeroVertex (n a) := by
    by_contra hu
    have hSu : ueoplPadSucc useInner n S (a, false :: u) = false :: u := by
      change (if decide (u = zeroVertex (n a)) then true :: zeroVertex (n a) else false :: u) = _
      exact ite_eq_right (by rw [decide_eq_false hu]; decide)
    exact h hSu.symm
  cases b₁ <;> cases b₂
  · exact absurd (congrArg (false :: ·) ((hfalse_eq hS₁).trans (hfalse_eq hS₂).symm)) hne
  · have hx0 := hfalse_eq hS₁
    subst hx0
    simp only [ueoplPadPotential, ueoplPadSucc, List.headD_cons, List.tail_cons,
      Bool.false_eq_true, ↓reduceIte, decide_true, hui, hV0] at hV
    omega
  · have hy0 := hfalse_eq hS₂
    subst hy0
    simp only [ueoplPadPotential, List.headD_cons, List.tail_cons, Bool.false_eq_true,
      ↓reduceIte, hui] at hV
    omega
  · simp only [ueoplPadSucc, ueoplPadPotential, List.headD_cons, List.tail_cons, ↓reduceIte,
      hui, ne_eq, List.cons.injEq, true_and] at hne hS₁ hS₂ hV
    exact ⟨x, y, rfl, rfl, hx, hy, hne, hS₁, hS₂, by omega⟩

/-- Back-map decoding a padded `(n a + 1)`-bit *UniqueEOPL* witness `w` back to a witness of
`uniqueEOPLViolationRel n P S V a`. -/
private def ueoplPadBack (useInner : α → Bool) (n : α → ℕ) (p : α × List Bool) : List Bool :=
  if useInner p.1 then
    if p.2.headD false then
      true :: (p.2.tail.take (n p.1 + 1)).tail ++ (p.2.tail.drop (n p.1 + 1)).tail
    else
      false :: p.2.tail.tail
  else
    false :: zeroVertex (n p.1)

private theorem computableInPolyTime_bitsHeadDFalse :
    ComputableInPolyTime (fun bs : List Bool => bs.headD false) encBits encBool := by
  have hraw := decide_eq' (bitsTake.comp (ComputableInPolyTime.id'.prod (const 1))) (const [true])
  convert hraw using 1; funext bs; rcases bs with _ | ⟨_ | _, _⟩ <;> rfl

private theorem computableInPolyTime_ueoplPadPred {enc : α ↪ List Bool} {useInner : α → Bool}
    {n : α → ℕ} {P : α × List Bool → List Bool}
    (hui : ComputableInPolyTime useInner enc encBool)
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits) :
    ComputableInPolyTime (ueoplPadPred useInner n P) (encPair enc encBits) encBits := by
  have ha := fst enc encBits
  have hw := snd enc encBits
  have ht := bitsTail.comp hw
  have hz := computableInPolyTime_zeroVertex_comp (hn.comp ha)
  unfold ueoplPadPred
  exact (computableInPolyTime_bitsHeadDFalse.comp hw).ite
    ((decide_eq' ht hz).ite (bitsCons (const false) hz)
      ((hui.comp ha).ite (bitsCons (const true) (hP.comp (ha.prod ht)))
        (bitsCons (const true) ht)))
    (bitsCons (const false) ht)

private theorem computableInPolyTime_ueoplPadSucc {enc : α ↪ List Bool} {useInner : α → Bool}
    {n : α → ℕ} {S : α × List Bool → List Bool}
    (hui : ComputableInPolyTime useInner enc encBool)
    (hn : ComputableInPolyTime n enc encUnary)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits) :
    ComputableInPolyTime (ueoplPadSucc useInner n S) (encPair enc encBits) encBits := by
  have ha := fst enc encBits
  have hw := snd enc encBits
  have ht := bitsTail.comp hw
  have hz := computableInPolyTime_zeroVertex_comp (hn.comp ha)
  unfold ueoplPadSucc
  exact (computableInPolyTime_bitsHeadDFalse.comp hw).ite
    ((hui.comp ha).ite (bitsCons (const true) (hS.comp (ha.prod ht)))
      (bitsCons (const true) ht))
    ((decide_eq' ht hz).ite (bitsCons (const true) hz) (bitsCons (const false) ht))

private theorem computableInPolyTime_ueoplPadPotential {enc : α ↪ List Bool} {useInner : α → Bool}
    {n : α → ℕ} {V : α × List Bool → ℕ}
    (hui : ComputableInPolyTime useInner enc encBool)
    (hn : ComputableInPolyTime n enc encUnary)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    ComputableInPolyTime (ueoplPadPotential useInner n V) (encPair enc encBits) encNat := by
  have ha := fst enc encBits
  have hw := snd enc encBits
  have ht := bitsTail.comp hw
  have hz := computableInPolyTime_zeroVertex_comp (hn.comp ha)
  unfold ueoplPadPotential
  exact (computableInPolyTime_bitsHeadDFalse.comp hw).ite
    ((hui.comp ha).ite (binary_add' (hV.comp (ha.prod ht)) (const 1))
      ((decide_eq' ht hz).ite (const 1) (const 0)))
    (const 0)

/-- Every totalized *UniqueEOPL* family search-reduces in polynomial time to an unconditionally
promised *UniqueEOPL* family on width `n a + 1`. -/
theorem mem_UEOPL_iff_promised {enc : α ↪ List Bool} {R : α → List Bool → Prop} :
    R ∈ UEOPL enc ↔ R ∈ FNP enc ∧
      ∃ (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ),
        ComputableInPolyTime n enc encUnary ∧
        ComputableInPolyTime P (encPair enc encBits) encBits ∧
        ComputableInPolyTime S (encPair enc encBits) encBits ∧
        ComputableInPolyTime V (encPair enc encBits) encNat ∧
        PreservesWidth n P ∧ PreservesWidth n S ∧
        (∀ a, PromisedPotentialLine n P S V a) ∧
        SearchReducible enc enc R (uniqueEOPLPromisedRel n P S V) := by
  constructor
  · rintro ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hred⟩
    let ui := checkPromisedPotentialLine n P S V
    have hui : ComputableInPolyTime ui enc encBool :=
      computableInPolyTime_checkPromisedPotentialLine hn hP hS hV
    let n' (a : α) : ℕ := n a + 1
    let P' := ueoplPadPred ui n P
    let S' := ueoplPadSucc ui n S
    let V' := ueoplPadPotential ui n V
    have hn' : ComputableInPolyTime n' enc encUnary := unary_add' hn (const 1)
    have hP'_len : PreservesWidth n' P' := preservesWidth_ueoplPadPred hP_len
    have hS'_len : PreservesWidth n' S' := preservesWidth_ueoplPadSucc hS_len
    have hprom' : ∀ a, PromisedPotentialLine n' P' S' V' a :=
      promisedPotentialLine_ueoplPad ui n P S V
    have hback : ComputableInPolyTime (ueoplPadBack ui n) (encPair enc encBits) encBits := by
      have ha := fst enc encBits
      have hw := snd enc encBits
      have ht := bitsTail.comp hw
      have hn1 := hn'.comp ha
      have hfst := bitsTail.comp (bitsTake.comp (ht.prod hn1))
      have hsnd := bitsTail.comp (bitsDropWithInput ht hn1)
      unfold ueoplPadBack
      exact (hui.comp ha).ite
        ((computableInPolyTime_bitsHeadDFalse.comp hw).ite
          (bitsAppend (bitsCons (const true) hfst) hsnd)
          (bitsCons (const false) (bitsTail.comp ht)))
        (bitsCons (const false) (computableInPolyTime_zeroVertex_comp (hn.comp ha)))
    refine ⟨hR, n', P', S', V', hn',
      computableInPolyTime_ueoplPadPred hui hn hP,
      computableInPolyTime_ueoplPadSucc hui hn hS,
      computableInPolyTime_ueoplPadPotential hui hn hV,
      hP'_len, hS'_len, hprom',
      hred.trans (.of_isTotalSearch
        (isTotalSearch_uniqueEOPLPromisedRel (fun a => (hprom' a).1) hP'_len hS'_len)
        ComputableInPolyTime.id' hback fun a w hw => ?_)⟩
    unfold ueoplPadBack
    cases hca : ui a
    · refine .inl ⟨rfl, fun hp => ?_⟩
      have : ui a = true := checkPromisedPotentialLine_eq_true_iff.mpr hp
      rw [this] at hca; exact Bool.false_ne_true hca.symm
    · have hp : PromisedPotentialLine n P S V a := checkPromisedPotentialLine_eq_true_iff.mp hca
      rcases hw with ⟨z, rfl, hz, hsol⟩ | ⟨z₁, z₂, rfl, hz₁, hz₂, hsol⟩
      · obtain ⟨x, rfl, hx, ⟨hx0, hSx⟩ | hvalid⟩ :=
          ueoplPad_single_sound hca hp.1.1 hp.2 hz hsol
        · exact absurd (hx0 ▸ hSx) hp.1.2
        · exact .inr (.inl ⟨x, rfl, hx, hvalid⟩)
      · obtain ⟨x, y, rfl, rfl, hx, hy, hUV3⟩ :=
          ueoplPad_pair_sound hca hp.2 hz₁ hz₂ hsol
        have htk : ((true :: x) ++ (true :: y)).take (n a + 1) = true :: x :=
          List.take_left' (by simp only [List.length_cons, hx])
        have hdr : ((true :: x) ++ (true :: y)).drop (n a + 1) = true :: y :=
          List.drop_left' (by simp only [List.length_cons, hx])
        dsimp only [List.headD_cons, List.tail_cons]
        rw [ite_eq_left rfl, htk, hdr]
        exact .inr (.inr ⟨x, y, rfl, hx, hy, hUV3⟩)
  · rintro ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hprom, hred⟩
    exact SearchReducible.mem_UEOPL hred hR
      (uniqueEOPLPromisedRel_mem_UEOPL hn hP hS hV hP_len hS_len hprom)

/-- **Single-line criterion for `UEOPL` membership.** Suppose `R ∈ FNP enc` is equipped with a
uniform polynomial-time width-preserving family `(n, P, S, V)` representing a single active line
from `0^{n a}` with unit-step odometer:

1. `P(a, 0^{n a}) = 0^{n a}` and `V(a, 0^{n a}) = 0`;
2. every active vertex strictly increments the odometer by `1`: if `x ≠ S(a, x)`, then
   `V(a, S(a, x)) = V(a, x) + 1`;
3. every non-zero vertex cancels on the left: if `x ≠ 0^{n a}`, then `S(a, P(a, x)) = x`;
4. active vertices have distinct potentials: if `x ≠ S(a, x)`, `y ≠ S(a, y)`, and
   `V(a, x) = V(a, y)`, then `x = y`;
5. every `(U1)` point `x ∈ {0, 1}^{n a}` with `P(a, S(a, x)) ≠ x`, as well as `0^{n a}` if
   `S(a, 0^{n a}) = 0^{n a}` (immediate finish at the origin), decodes via `g(a, x)` to a valid
   solution of `R a`.

Then `(UV1)`, `(UV2)`, and `(UV3)` have zero solutions on the `(n a + 1)`-bit promised embedding,
every *UniqueEOPL* solution is a `(U1)` solution corresponding to the unique end of the line, and
`R ∈ UEOPL enc`. -/
theorem mem_UEOPL_of_singleLine {enc : α ↪ List Bool} {R : α → List Bool → Prop}
    {n : α → ℕ} {P S : α × List Bool → List Bool} {V : α × List Bool → ℕ}
    {g : α × List Bool → List Bool}
    (hR : R ∈ FNP enc)
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat)
    (hg : ComputableInPolyTime g (encPair enc encBits) encBits)
    (hP_len : PreservesWidth n P) (hS_len : PreservesWidth n S)
    (hP0 : ∀ a, P (a, zeroVertex (n a)) = zeroVertex (n a))
    (hV0 : ∀ a, V (a, zeroVertex (n a)) = 0)
    (hodom : ∀ a x, x.length = n a → x ≠ S (a, x) → V (a, S (a, x)) = V (a, x) + 1)
    (hSP : ∀ a x, x.length = n a → x ≠ zeroVertex (n a) → S (a, P (a, x)) = x)
    (hinj : ∀ a x y, x.length = n a → y.length = n a →
      x ≠ S (a, x) → y ≠ S (a, y) → V (a, x) = V (a, y) → x = y)
    (hend : ∀ a x, x.length = n a →
      (P (a, S (a, x)) ≠ x ∨ (x = zeroVertex (n a) ∧ S (a, x) = x)) → R a (g (a, x))) :
    R ∈ UEOPL enc := by
  let ui : α → Bool := fun _ => true
  let n' (a : α) : ℕ := n a + 1
  let P' := ueoplPadPred ui n P
  let S' := ueoplPadSucc ui n S
  let V' := ueoplPadPotential ui n V
  have hP'_len : PreservesWidth n' P' := preservesWidth_ueoplPadPred hP_len
  have hS'_len : PreservesWidth n' S' := preservesWidth_ueoplPadSucc hS_len
  have hprom' : ∀ a, PromisedPotentialLine n' P' S' V' a :=
    promisedPotentialLine_ueoplPad ui n P S V
  have hback : ComputableInPolyTime (fun p : α × List Bool => g (p.1, p.2.tail.tail))
      (encPair enc encBits) encBits :=
    hg.comp ((fst enc encBits).prod (bitsTail.comp (bitsTail.comp (snd enc encBits))))
  refine mem_UEOPL_iff_promised.mpr ⟨hR, n', P', S', V', unary_add' hn (const 1),
    computableInPolyTime_ueoplPadPred (const true) hn hP,
    computableInPolyTime_ueoplPadSucc (const true) hn hS,
    computableInPolyTime_ueoplPadPotential (const true) hn hV,
    hP'_len, hS'_len, hprom',
    .of_isTotalSearch
      (isTotalSearch_uniqueEOPLPromisedRel (fun a => (hprom' a).1) hP'_len hS'_len)
      ComputableInPolyTime.id' hback fun a w hw => ?_⟩
  rcases hw with ⟨z, rfl, hz, hsol⟩ | ⟨z₁, z₂, rfl, hz₁, hz₂, hsol⟩
  · obtain ⟨x, rfl, hx, h0 | hU1 | ⟨hne, -, hle⟩ | ⟨hne, hx0⟩⟩ :=
      ueoplPad_single_sound (useInner := ui) rfl (hP0 a) (hV0 a) hz hsol
    · exact hend a x hx (.inr h0)
    · exact hend a x hx (.inl hU1)
    · have := hodom a x hx hne; omega
    · exact absurd (hSP a x hx hx0) hne
  · exfalso
    obtain ⟨x, y, -, -, hx, hy, hne, hxS, hyS, hVeq | ⟨hlt₁, hlt₂⟩⟩ :=
      ueoplPad_pair_sound (useInner := ui) rfl (hV0 a) hz₁ hz₂ hsol
    · exact hne (hinj a x y hx hy hxS hyS hVeq)
    · have := hodom a x hx hxS; omega

end PromisedEmbedding

/-! ### Canonical Boolean-circuit `UniqueEOPL` problem and `UEOPL`-completeness -/

section CircuitProblem

/-- An instance of the canonical Boolean-circuit-presented **UniqueEOPL** problem
: vertex bit-width `n` (in unary), potential bit-width `m` (in
unary, bounding outputs to `{0, …, 2^m - 1}`), predecessor circuit code `predCircuit`, successor
circuit code `succCircuit`, and potential (odometer) circuit code `potCircuit`.
-/
@[ext]
structure UniqueEOPLInstance where
  /-- Vertex bit-width `n` for domain `{0, 1}^n`. -/
  width : ℕ
  /-- Potential bit-width `m` for codomain `{0, …, 2^m - 1}`. -/
  potWidth : ℕ
  /-- Boolean circuit code computing the predecessor function `P : {0, 1}^n → {0, 1}^n`. -/
  predCircuit : CircuitCode
  /-- Boolean circuit code computing the successor function `S : {0, 1}^n → {0, 1}^n`. -/
  succCircuit : CircuitCode
  /-- Boolean circuit code computing the `m`-bit potential `V : {0, 1}^n → {0, …, 2^m - 1}`. -/
  potCircuit : CircuitCode

/-- Raw tuple representation of `UniqueEOPLInstance` for polynomial-time encoding (`n` and `m` in
unary, followed by the three De Morgan circuit codes `cP`, `cS`, `cV`). -/
abbrev UniqueEOPLRaw : Type := ℕ × ℕ × CircuitCode × CircuitCode × CircuitCode

/-- Canonical binary encoding of `UniqueEOPLRaw`: `n` and `m` in unary, and `cP, cS, cV` via
`Cslib.Circuits.Boolean.encCode`. -/
abbrev encUniqueEOPLRaw : UniqueEOPLRaw ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encCode (encPair encCode encCode)))

/-- Canonical binary encoding of `UniqueEOPLInstance`. -/
def encUniqueEOPL : UniqueEOPLInstance ↪ List Bool where
  toFun I := encUniqueEOPLRaw (I.width, I.potWidth, I.predCircuit, I.succCircuit, I.potCircuit)
  inj' I₁ I₂ h := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ :
        I₁.width = I₂.width ∧ I₁.potWidth = I₂.potWidth ∧
          I₁.predCircuit = I₂.predCircuit ∧ I₁.succCircuit = I₂.succCircuit ∧
          I₁.potCircuit = I₂.potCircuit := by
      simpa only [Prod.mk.injEq] using encUniqueEOPLRaw.injective h
    exact UniqueEOPLInstance.ext h₁ h₂ h₃ h₄ h₅

/-- Evaluate the potential circuit of `I` on `u`, truncated to `I.potWidth` bits so its binary
value lies in `{0, …, 2^{I.potWidth} - 1}`. -/
def evalUniqueEOPLPotential (I : UniqueEOPLInstance) (u : List Bool) : ℕ :=
  binaryValue (padBits I.potWidth (evalCircuitOutputs I.potCircuit u))

/-- Every potential value `evalUniqueEOPLPotential I u` lies strictly below `2 ^ I.potWidth`. -/
theorem evalUniqueEOPLPotential_lt_two_pow (I : UniqueEOPLInstance) (u : List Bool) :
    evalUniqueEOPLPotential I u < 2 ^ I.potWidth := by
  simpa only [evalUniqueEOPLPotential, length_padBits] using
    binaryValue_lt_two_pow (padBits I.potWidth (evalCircuitOutputs I.potCircuit u))

/-- **Canonical circuit-presented `UniqueEOPL` search problem**
: given Boolean circuits `S, P : {0, 1}^n → {0, 1}^n` and
`V : {0, 1}^n → {0, …, 2^m - 1}` (with `P(0^n) = 0^n ≠ S(0^n)` and `V(0^n) = 0`), find a solution
of type `(U1)`, `(UV1)`, `(UV2)`, or `(UV3)` (or `false :: 0^n` if the syntactic promise fails).
-/
def UniqueEOPL : UniqueEOPLInstance → List Bool → Prop :=
  uniqueEOPLViolationRel UniqueEOPLInstance.width
    (fun p => evalCircuitCode p.1.width p.1.predCircuit p.2)
    (fun p => evalCircuitCode p.1.width p.1.succCircuit p.2)
    (fun p => evalUniqueEOPLPotential p.1 p.2)

/-- On any circuit instance satisfying `P(0^n) = 0^n ≠ S(0^n)` and `V(0^n) = 0`, solutions of
`UniqueEOPL` are precisely the pure `(U1)`, `(UV1)`, `(UV2)`, and `(UV3)` solutions. -/
theorem UniqueEOPL_iff_promised {I : UniqueEOPLInstance}
    (hprom : PromisedPotentialLine UniqueEOPLInstance.width
      (fun p => evalCircuitCode p.1.width p.1.predCircuit p.2)
      (fun p => evalCircuitCode p.1.width p.1.succCircuit p.2)
      (fun p => evalUniqueEOPLPotential p.1 p.2) I)
    {w : List Bool} :
    UniqueEOPL I w ↔
      uniqueEOPLPromisedRel UniqueEOPLInstance.width
        (fun p => evalCircuitCode p.1.width p.1.predCircuit p.2)
        (fun p => evalCircuitCode p.1.width p.1.succCircuit p.2)
        (fun p => evalUniqueEOPLPotential p.1 p.2) I w :=
  uniqueEOPLViolationRel_iff_promised_of_promise hprom

/-- `UniqueEOPL` is a total search problem. -/
theorem isTotalSearch_UniqueEOPL : IsTotalSearch UniqueEOPL :=
  isTotalSearch_uniqueEOPLViolationRel
    (fun _ _ _ => length_evalCircuitCode _ _ _)
    (fun _ _ _ => length_evalCircuitCode _ _ _)

private theorem computableInPolyTime_toRaw :
    ComputableInPolyTime
      (fun I : UniqueEOPLInstance =>
        (I.width, I.potWidth, I.predCircuit, I.succCircuit, I.potCircuit))
      encUniqueEOPL encUniqueEOPLRaw :=
  of_eq fun _ => rfl

private theorem computableInPolyTime_mkInstance {α : Type} {enc : α ↪ List Bool}
    {n m : α → ℕ} {cP cS cV : α → CircuitCode}
    (hn : ComputableInPolyTime n enc encUnary)
    (hm : ComputableInPolyTime m enc encUnary)
    (hcP : ComputableInPolyTime cP enc encCode)
    (hcS : ComputableInPolyTime cS enc encCode)
    (hcV : ComputableInPolyTime cV enc encCode) :
    ComputableInPolyTime (fun a => UniqueEOPLInstance.mk (n a) (m a) (cP a) (cS a) (cV a))
      enc encUniqueEOPL :=
  (hn.prod (hm.prod (hcP.prod (hcS.prod hcV)))).of_enc_eq fun _ => rfl

/-- Canonical circuit-presented `UniqueEOPL` lies in `UEOPL`. -/
theorem UniqueEOPL_mem_UEOPL : UniqueEOPL ∈ UEOPL encUniqueEOPL := by
  have hraw := computableInPolyTime_toRaw
  have hn : ComputableInPolyTime UniqueEOPLInstance.width encUniqueEOPL encUnary :=
    (fst _ _).comp hraw
  have hm : ComputableInPolyTime UniqueEOPLInstance.potWidth encUniqueEOPL encUnary :=
    (fst _ _).comp ((snd _ _).comp hraw)
  have hrest := (snd _ _).comp ((snd _ _).comp hraw)
  have hcP : ComputableInPolyTime UniqueEOPLInstance.predCircuit encUniqueEOPL encCode :=
    (fst _ _).comp hrest
  have hcS : ComputableInPolyTime UniqueEOPLInstance.succCircuit encUniqueEOPL encCode :=
    (fst _ _).comp ((snd _ _).comp hrest)
  have hcV : ComputableInPolyTime UniqueEOPLInstance.potCircuit encUniqueEOPL encCode :=
    (snd _ _).comp ((snd _ _).comp hrest)
  have ha := fst encUniqueEOPL encBits
  have hu := snd encUniqueEOPL encBits
  have hP := computableInPolyTime_evalCircuitCode (hn.comp ha) (hcP.comp ha) hu
  have hS := computableInPolyTime_evalCircuitCode (hn.comp ha) (hcS.comp ha) hu
  have hV : ComputableInPolyTime
      (fun p : UniqueEOPLInstance × List Bool => evalUniqueEOPLPotential p.1 p.2)
      (encPair encUniqueEOPL encBits) encNat := by
    unfold evalUniqueEOPLPotential
    have hout : ComputableInPolyTime
        (fun p : UniqueEOPLInstance × List Bool => evalCircuitOutputs p.1.potCircuit p.2)
        (encPair encUniqueEOPL encBits) encBits := by
      have := hcV.comp ha
      fun_prop
    exact computableInPolyTime_binaryValue_comp
      (computableInPolyTime_padBits (hm.comp ha) hout)
  exact uniqueEOPLViolationRel_mem_UEOPL hn hP hS hV
    (fun _ _ _ => length_evalCircuitCode _ _ _)
    (fun _ _ _ => length_evalCircuitCode _ _ _)

/-- Canonical circuit-presented `UniqueEOPL` lies in `TFNP`. -/
theorem UniqueEOPL_mem_TFNP : UniqueEOPL ∈ TFNP encUniqueEOPL :=
  UEOPL_subset_TFNP UniqueEOPL_mem_UEOPL

/-- Every promised uniform polynomial-time width-preserving *UniqueEOPL* family compiles in
polynomial time to promised instances of canonical Boolean-circuit `UniqueEOPL`. -/
theorem uniqueEOPLPromisedRel_searchReducible_UniqueEOPL {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {P S : α × List Bool → List Bool} {V : α × List Bool → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat)
    (hP_len : PreservesWidth n P) (hS_len : PreservesWidth n S)
    (hprom : ∀ a, PromisedPotentialLine n P S V a) :
    SearchReducible enc encUniqueEOPL (uniqueEOPLPromisedRel n P S V) UniqueEOPL := by
  obtain ⟨cP, hcP, hPs⟩ := exists_uniformCircuitCodes hn hn hP hP_len
  obtain ⟨cS, hcS, hSs⟩ := exists_uniformCircuitCodes hn hn hS hS_len
  obtain ⟨m, hm, hbits⟩ := exists_length_bits_le hn hV
  have hword : ComputableInPolyTime
      (fun p : α × List Bool => binaryWord (m p.1) (V p)) (encPair enc encBits) encBits := by
    have hb := (of_eq (f := Nat.bits) (encIn := encNat) (encOut := encBits) fun _ => rfl).comp hV
    have hpad := unary_sub.comp
      ((hm.comp (fst enc encBits)).prod (length_bits.comp hb))
    exact bitsAppend ((bitsReplicate false).comp hpad) (bitsReverse.comp hb)
  have hword_len (a : α) (u : List Bool) (hu : u.length = n a) :
      (binaryWord (m a) (V (a, u))).length = m a := by
    have := hbits a u hu
    simp only [binaryWord, List.length_append, List.length_replicate, List.length_reverse]
    omega
  obtain ⟨cV, hcV, hVs⟩ := exists_uniformCircuitCodes hn hm hword hword_len
  let f (a : α) : UniqueEOPLInstance := ⟨n a, m a, cP a, cS a, cV a⟩
  have hevalP (a : α) (u : List Bool) (hu : u.length = n a) :
      evalCircuitCode (f a).width (f a).predCircuit u = P (a, u) := by
    change padBits (n a) (evalCircuitOutputs (cP a) u) = P (a, u)
    rw [hPs a u hu, padBits_of_length_eq (hP_len a u hu)]
  have hevalS (a : α) (u : List Bool) (hu : u.length = n a) :
      evalCircuitCode (f a).width (f a).succCircuit u = S (a, u) := by
    change padBits (n a) (evalCircuitOutputs (cS a) u) = S (a, u)
    rw [hSs a u hu, padBits_of_length_eq (hS_len a u hu)]
  have hevalV (a : α) (u : List Bool) (hu : u.length = n a) :
      evalUniqueEOPLPotential (f a) u = V (a, u) := by
    change binaryValue (padBits (m a) (evalCircuitOutputs (cV a) u)) = V (a, u)
    rw [hVs a u hu, padBits_of_length_eq (hword_len a u hu), binaryValue_binaryWord]
  have hfprom (a : α) : PromisedPotentialLine UniqueEOPLInstance.width
      (fun p => evalCircuitCode p.1.width p.1.predCircuit p.2)
      (fun p => evalCircuitCode p.1.width p.1.succCircuit p.2)
      (fun p => evalUniqueEOPLPotential p.1 p.2) (f a) := by
    have hz : (zeroVertex (n a)).length = n a := length_zeroVertex (n a)
    exact ⟨⟨(hevalP a _ hz).trans (hprom a).1.1,
        by dsimp only; rw [hevalS a _ hz]; exact (hprom a).1.2⟩,
      (hevalV a _ hz).trans (hprom a).2⟩
  refine SearchReducible.of_isTotalSearch isTotalSearch_UniqueEOPL
    (computableInPolyTime_mkInstance hn hm hcP hcS hcV) (snd enc encBits) fun a w hw => ?_
  have hwp := (UniqueEOPL_iff_promised (hfprom a)).mp hw
  rcases hwp with ⟨x, rfl, hx, hsol⟩ | ⟨x, y, rfl, hx, hy, hsol⟩
  · refine .inl ⟨x, rfl, hx, ?_⟩
    have hSx := hS_len a x hx
    have hPx := hP_len a x hx
    simp only [IsUniqueEOPLSolU1, IsUniqueEOPLSolUV1, IsUniqueEOPLSolUV2,
      hevalS a x hx, hevalP a x hx, hevalP a _ hSx, hevalS a _ hPx,
      hevalV a x hx, hevalV a _ hSx] at hsol
    exact hsol
  · refine .inr ⟨x, y, rfl, hx, hy, ?_⟩
    have hSx := hS_len a x hx
    simp only [IsUniqueEOPLSolUV3, hevalS a x hx, hevalS a y hy,
      hevalV a x hx, hevalV a y hy, hevalV a _ hSx] at hsol
    exact hsol

/-- **Canonical circuit `UniqueEOPL` is `UEOPL`-complete** under polynomial-time search reductions
.
-/
theorem UniqueEOPL_searchComplete : SearchComplete @UEOPL encUniqueEOPL UniqueEOPL := by
  refine ⟨UniqueEOPL_mem_UEOPL, fun _ enc R hR => ?_⟩
  obtain ⟨-, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hprom, hred⟩ :=
    mem_UEOPL_iff_promised.mp hR
  exact hred.trans (uniqueEOPLPromisedRel_searchReducible_UniqueEOPL hn hP hS hV hP_len hS_len
    hprom)

/-- **Equivalence with the circuit definition:** an `FNP` search problem lies in `UEOPL` if and
only if it is polynomial-time search-reducible to canonical Boolean-circuit `UniqueEOPL`. -/
theorem mem_UEOPL_iff_searchReducible_UniqueEOPL {α : Type} {enc : α ↪ List Bool}
    {R : α → List Bool → Prop} :
    R ∈ UEOPL enc ↔ R ∈ FNP enc ∧ SearchReducible enc encUniqueEOPL R UniqueEOPL :=
  ⟨fun h => ⟨(UEOPL_subset_TFNP h).1, UniqueEOPL_searchComplete.2 enc R h⟩,
   fun ⟨hR, hred⟩ => SearchReducible.mem_UEOPL hred hR UniqueEOPL_mem_UEOPL⟩

end CircuitProblem

end Cslib.Complexity
