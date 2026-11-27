/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Problems.ExactThreeSAT
public import CslibFrontier.Logics.Propositional.CNF.ModelCount
public import CslibFrontier.Foundations.Combinatorics.Words.Zimin
public import Mathlib.Logic.Relation
public import CslibFrontier.Computability.Complexity.Problems.WordUnavoidability.GraphFree

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import Mathlib.Data.List.Nodup

/-!
# Polynomial-Time `3`-CNF Word Gadget Construction and Block-Chain Criteria

This module constructs a polynomial-time mapping `threeCNFWord : CNF ℕ → List ℕ` encoding `3`-CNF
satisfiability into word-pattern unavoidability:

* Each clause `C_j` (`j < φ.length`) has a `10`-block positive `3`-clause gadget on three
  dedicated
  literal-occurrence slots `orig_{j, 0}, orig_{j, 1}, orig_{j, 2}`.
* Each variable `v ∈ φ.distinctVars` has a `7`-block positive `2`-clause choice gadget on
  `(px_v, py_v)`.
* Each literal occurrence `(j, k)` (`k ∈ Fin 3`) has a `13`-block negative `2`-clause tap gadget
  on
  `(qo_{j, k}, qv_{j, k})` coupled to `orig_{j, k}` and `py_v`/`px_v` via dedicated `4`-letter
  guard
  blocks `[go_{j, k}, orig_{j, k}, qo_{j, k}, go_{j, k}]` and
  `[gv_{j, k}, conflictVarSlot lit, qv_{j, k}, gv_{j, k}]`, with fresh separator letters between
  all
  blocks.

## Main definitions

* `ClauseGadgetLetter`: structured alphabet for the `3`-CNF gadget word `clauseGadgetPattern φ`.
* `clauseGadgetPattern`, `threeCNFWord`: structured and `ℕ`-encoded `3`-CNF word patterns.
* `GadgetBlockPair`, `GadgetSameRight`: block-local `2`-factor and shared-right-neighbor
  relations.

## Main results

* `computableInPolyTime_threeCNFWord`: `threeCNFWord` runs in polynomial time on multi-tape Turing
  machines.
* `gadget_hasAlternatingChain_nonSep_iff`: separator letters do not participate in alternating
  `2`-factor chains between non-separator letters.
* `isFreeSet_of_noLeft`, `isFreeSet_of_noRight`, `isFreeSet_of_closed_left_region`: sufficient
  criteria for free sets after partial letter deletion.
-/

public section

namespace CslibFrontier.Complexity

open CslibFrontier.Word Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM
  ComputableInPolyTime

/-- Structured alphabet for the `3`-CNF gadget word pattern `clauseGadgetPattern φ`. -/
inductive ClauseGadgetLetter where
  /-- Clause `C_j` helper `a_j`. -/
  | ao : ℕ → ClauseGadgetLetter
  /-- Clause `C_j` helper `b_j`. -/
  | bo : ℕ → ClauseGadgetLetter
  /-- Clause `C_j` helper `c_j`. -/
  | co : ℕ → ClauseGadgetLetter
  /-- Clause `C_j` helper `d_j`. -/
  | do_ : ℕ → ClauseGadgetLetter
  /-- Variable `P_v` helper `ap_v`. -/
  | ap : ℕ → ClauseGadgetLetter
  /-- Variable `P_v` helper `bp_v`. -/
  | bp : ℕ → ClauseGadgetLetter
  /-- Variable `P_v` helper `cp_v`. -/
  | cp : ℕ → ClauseGadgetLetter
  /-- Variable `P_v` positive slot `px_v`. -/
  | px : ℕ → ClauseGadgetLetter
  /-- Variable `P_v` negative slot `py_v`. -/
  | py : ℕ → ClauseGadgetLetter
  /-- Clause `C_j` literal slot `k ∈ Fin 3`. -/
  | orig : ℕ → Fin 3 → ClauseGadgetLetter
  /-- Occurrence tap `D_{j, k}` helper `an_{j, k}`. -/
  | an : ℕ → Fin 3 → ClauseGadgetLetter
  /-- Occurrence tap `D_{j, k}` helper `bn_{j, k}`. -/
  | bn : ℕ → Fin 3 → ClauseGadgetLetter
  /-- Occurrence tap `D_{j, k}` helper `cn_{j, k}`. -/
  | cn : ℕ → Fin 3 → ClauseGadgetLetter
  /-- Occurrence tap `D_{j, k}` slot `qo_{j, k}` paired with `orig_{j, k}`. -/
  | qo : ℕ → Fin 3 → ClauseGadgetLetter
  /-- Occurrence tap `D_{j, k}` slot `qv_{j, k}` paired with `py_v` / `px_v`. -/
  | qv : ℕ → Fin 3 → ClauseGadgetLetter
  /-- Dedicated guard letter pairing `orig_{j, k}` with `qo_{j, k}`. -/
  | go : ℕ → Fin 3 → ClauseGadgetLetter
  /-- Dedicated guard letter pairing `py_v` / `px_v` with `qv_{j, k}`. -/
  | gv : ℕ → Fin 3 → ClauseGadgetLetter
  /-- Unique block separator `z_idx`. -/
  | sep : ℕ → ClauseGadgetLetter
  deriving DecidableEq

/-- Boolean test identifying separator letters `.sep idx`. -/
@[expose]
def ClauseGadgetLetter.isSep : ClauseGadgetLetter → Bool
  | .sep _ => true
  | _ => false

/-- `.sep z` is a separator letter. -/
@[simp]
theorem ClauseGadgetLetter.isSep_sep (z : ℕ) : (sep z).isSep = true := rfl

/-- Characterization of `u.isSep = true`. -/
theorem ClauseGadgetLetter.isSep_eq_true_iff {u : ClauseGadgetLetter} :
    u.isSep = true ↔ ∃ z, u = .sep z := by
  cases u <;> simp [ClauseGadgetLetter.isSep]

/-- Boolean test identifying guard letters `.go j k` and `.gv j k`. -/
@[expose]
def ClauseGadgetLetter.isGuard : ClauseGadgetLetter → Bool
  | .go _ _ => true
  | .gv _ _ => true
  | _ => false

/-- `.go j k` is a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_go (j : ℕ) (k : Fin 3) : (go j k).isGuard = true := rfl

/-- `.gv j k` is a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_gv (j : ℕ) (k : Fin 3) : (gv j k).isGuard = true := rfl

/-- `.ao j` is not a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_ao (j : ℕ) : (ao j).isGuard = false := rfl

/-- `.bo j` is not a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_bo (j : ℕ) : (bo j).isGuard = false := rfl

/-- `.co j` is not a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_co (j : ℕ) : (co j).isGuard = false := rfl

/-- `.do_ j` is not a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_do (j : ℕ) : (do_ j).isGuard = false := rfl

/-- `.ap v` is not a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_ap (v : ℕ) : (ap v).isGuard = false := rfl

/-- `.bp v` is not a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_bp (v : ℕ) : (bp v).isGuard = false := rfl

/-- `.cp v` is not a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_cp (v : ℕ) : (cp v).isGuard = false := rfl

/-- `.px v` is not a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_px (v : ℕ) : (px v).isGuard = false := rfl

/-- `.py v` is not a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_py (v : ℕ) : (py v).isGuard = false := rfl

/-- `.orig j k` is not a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_orig (j : ℕ) (k : Fin 3) : (orig j k).isGuard = false := rfl

/-- `.an j k` is not a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_an (j : ℕ) (k : Fin 3) : (an j k).isGuard = false := rfl

/-- `.bn j k` is not a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_bn (j : ℕ) (k : Fin 3) : (bn j k).isGuard = false := rfl

/-- `.cn j k` is not a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_cn (j : ℕ) (k : Fin 3) : (cn j k).isGuard = false := rfl

/-- `.qo j k` is not a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_qo (j : ℕ) (k : Fin 3) : (qo j k).isGuard = false := rfl

/-- `.qv j k` is not a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_qv (j : ℕ) (k : Fin 3) : (qv j k).isGuard = false := rfl

/-- `.sep z` is not a guard letter. -/
@[simp]
theorem ClauseGadgetLetter.isGuard_sep (z : ℕ) : (sep z).isGuard = false := rfl

/-- Injective linear encoding `ClauseGadgetLetter → ℕ` placing the `18` constructor roles into
distinct
residue classes modulo `32`. -/
@[expose]
def ClauseGadgetLetter.toNat : ClauseGadgetLetter → ℕ
  | .ao j => 32 * j + 0
  | .bo j => 32 * j + 1
  | .co j => 32 * j + 2
  | .do_ j => 32 * j + 3
  | .ap v => 32 * v + 4
  | .bp v => 32 * v + 5
  | .cp v => 32 * v + 6
  | .px v => 32 * v + 7
  | .py v => 32 * v + 8
  | .orig j k => 32 * (3 * j + k.1) + 9
  | .an j k => 32 * (3 * j + k.1) + 10
  | .bn j k => 32 * (3 * j + k.1) + 11
  | .cn j k => 32 * (3 * j + k.1) + 12
  | .qo j k => 32 * (3 * j + k.1) + 13
  | .qv j k => 32 * (3 * j + k.1) + 14
  | .go j k => 32 * (3 * j + k.1) + 15
  | .gv j k => 32 * (3 * j + k.1) + 16
  | .sep z => 32 * z + 17

/-- `ClauseGadgetLetter.toNat` is injective. -/
theorem ClauseGadgetLetter.toNat_injective : Function.Injective ClauseGadgetLetter.toNat := by
  intro x y hxy
  cases x <;> cases y <;> simp only [ClauseGadgetLetter.toNat] at hxy <;> try omega
  all_goals
    congr 1 <;> omega

/-- Extract the `k`-th literal (`k ∈ Fin 3`) of clause `c` via `headD` / `tail`, defaulting to
`(0, true)` outside length `3`. -/
@[expose]
def clauseLitAt (c : Clause ℕ) : Fin 3 → Literal ℕ
  | ⟨0, _⟩ => c.headD (0, true)
  | ⟨1, _⟩ => c.tail.headD (0, true)
  | ⟨2, _⟩ => c.tail.tail.headD (0, true)

/-- On any clause `c` of length `3`, `clauseLitAt c k` equals `c[k.1]`. -/
theorem clauseLitAt_eq_getElem {c : Clause ℕ} (hc : c.length = 3) (k : Fin 3) :
    clauseLitAt c k = c[k.1]'(by omega) := by
  rcases c with _ | ⟨l₀, _ | ⟨l₁, _ | ⟨l₂, _ | _⟩⟩⟩ <;> simp at hc
  fin_cases k <;> rfl

/-- The `10` blocks of the positive `3`-clause gadget on `(orig_{j, 0}, orig_{j, 1}, orig_{j,
2})`. -/
@[expose]
def origClauseBlocks (j : ℕ) : List (List ClauseGadgetLetter) :=
  [[.ao j, .orig j 0], [.bo j, .orig j 0], [.bo j, .orig j 1], [.co j, .orig j 1],
   [.co j, .orig j 2], [.do_ j, .orig j 2], [.do_ j, .ao j],
   [.ao j, .bo j], [.ao j, .co j], [.ao j, .do_ j]]

/-- Membership characterization for `origClauseBlocks j`. -/
theorem mem_origClauseBlocks_iff {j : ℕ} {blk : List ClauseGadgetLetter} :
    blk ∈ origClauseBlocks j ↔
      blk = [.ao j, .orig j 0] ∨ blk = [.bo j, .orig j 0] ∨ blk = [.bo j, .orig j 1] ∨
      blk = [.co j, .orig j 1] ∨ blk = [.co j, .orig j 2] ∨ blk = [.do_ j, .orig j 2] ∨
      blk = [.do_ j, .ao j] ∨ blk = [.ao j, .bo j] ∨ blk = [.ao j, .co j] ∨
      blk = [.ao j, .do_ j] := by
  simp only [origClauseBlocks, List.mem_cons, List.not_mem_nil, or_false]

/-- The `7` blocks of the `+++` `2`-clause gadget `P_v` on `(px_v, py_v)`. -/
@[expose]
def varPosBlocks (v : ℕ) : List (List ClauseGadgetLetter) :=
  [[.ap v, .px v], [.bp v, .px v], [.bp v, .py v], [.cp v, .py v],
   [.cp v, .ap v], [.ap v, .bp v], [.ap v, .cp v]]

/-- Membership characterization for `varPosBlocks v`. -/
theorem mem_varPosBlocks_iff {v : ℕ} {blk : List ClauseGadgetLetter} :
    blk ∈ varPosBlocks v ↔
      blk = [.ap v, .px v] ∨ blk = [.bp v, .px v] ∨ blk = [.bp v, .py v] ∨
      blk = [.cp v, .py v] ∨ blk = [.cp v, .ap v] ∨ blk = [.ap v, .bp v] ∨
      blk = [.ap v, .cp v] := by
  simp only [varPosBlocks, List.mem_cons, List.not_mem_nil, or_false]

/-- Variable slot paired against `qv_{j, k}` for literal `lit = (v, pol)`: `py_v` when `pol =
true`,
`px_v` when `pol = false`. -/
@[expose]
def conflictVarSlot (lit : Literal ℕ) : ClauseGadgetLetter :=
  if lit.2 then .py lit.1 else .px lit.1

/-- `conflictVarSlot` on `(v, true)` yields `.py v`. -/
@[simp]
theorem conflictVarSlot_mk_true (v : ℕ) : conflictVarSlot (v, true) = .py v := rfl

/-- `conflictVarSlot` on `(v, false)` yields `.px v`. -/
@[simp]
theorem conflictVarSlot_mk_false (v : ℕ) : conflictVarSlot (v, false) = .px v := rfl

/-- When `lit.2 = true`, `conflictVarSlot lit = .py lit.1`. -/
theorem conflictVarSlot_of_true {lit : Literal ℕ} (h : lit.2 = true) :
    conflictVarSlot lit = .py lit.1 := by
  simp [conflictVarSlot, h]

/-- When `lit.2 = false`, `conflictVarSlot lit = .px lit.1`. -/
theorem conflictVarSlot_of_false {lit : Literal ℕ} (h : lit.2 = false) :
    conflictVarSlot lit = .px lit.1 := by
  simp [conflictVarSlot, h]

/-- Dichotomy for `conflictVarSlot lit` according to literal polarity. -/
theorem conflictVarSlot_cases (lit : Literal ℕ) :
    (lit.2 = true ∧ conflictVarSlot lit = .py lit.1) ∨
    (lit.2 = false ∧ conflictVarSlot lit = .px lit.1) := by
  rcases lit with ⟨_, _ | _⟩ <;> simp

/-- The `13` blocks of the `---` `2`-clause tap `D_{j, k}` and its two guards `go_{j, k}`,
`gv_{j, k}` for occurrence `(j, k)` with literal `lit`. -/
@[expose]
def occTapBlocks (j : ℕ) (k : Fin 3) (lit : Literal ℕ) : List (List ClauseGadgetLetter) :=
  let pvar := conflictVarSlot lit
  [[.an j k, .bn j k], [.qo j k, .bn j k], [.qo j k, .cn j k], [.qv j k, .cn j k],
   [.qv j k, .an j k], [.bn j k, .an j k], [.cn j k, .an j k],
   [.go j k, .orig j k, .qo j k, .go j k], [.ao j, .go j k], [.go j k, .an j k],
   [.gv j k, pvar, .qv j k, .gv j k], [.ap lit.1, .gv j k], [.gv j k, .an j k]]

/-- Membership characterization for `occTapBlocks j k lit`. -/
theorem mem_occTapBlocks_iff {j : ℕ} {k : Fin 3} {lit : Literal ℕ} {blk : List ClauseGadgetLetter} :
    blk ∈ occTapBlocks j k lit ↔
      blk = [.an j k, .bn j k] ∨ blk = [.qo j k, .bn j k] ∨ blk = [.qo j k, .cn j k] ∨
      blk = [.qv j k, .cn j k] ∨ blk = [.qv j k, .an j k] ∨ blk = [.bn j k, .an j k] ∨
      blk = [.cn j k, .an j k] ∨ blk = [.go j k, .orig j k, .qo j k, .go j k] ∨
      blk = [.ao j, .go j k] ∨ blk = [.go j k, .an j k] ∨
      blk = [.gv j k, conflictVarSlot lit, .qv j k, .gv j k] ∨
      blk = [.ap lit.1, .gv j k] ∨ blk = [.gv j k, .an j k] := by
  simp only [occTapBlocks, List.mem_cons, List.not_mem_nil, or_false]

/-- All `39` tap and guard blocks for the three literal positions of clause `c` at index `j`. -/
@[expose]
def clauseTapBlocks (c : Clause ℕ) (j : ℕ) : List (List ClauseGadgetLetter) :=
  occTapBlocks j 0 (clauseLitAt c 0) ++
    occTapBlocks j 1 (clauseLitAt c 1) ++
    occTapBlocks j 2 (clauseLitAt c 2)

/-- All unseparated blocks of `clauseGadgetPattern φ`. -/
@[expose]
def clauseGadgetBlocks (φ : CNF ℕ) : List (List ClauseGadgetLetter) :=
  (φ.zipIdx.flatMap fun p ↦ origClauseBlocks p.2) ++
    (φ.distinctVars.flatMap varPosBlocks) ++
    (φ.zipIdx.flatMap fun p ↦ clauseTapBlocks p.1 p.2)

/-- Membership in `l.zipIdx` coincides with indexed element lookup. -/
theorem mem_zipIdx_zero {A : Type*} {l : List A} {c : A} {j : ℕ} :
    (c, j) ∈ l.zipIdx ↔ ∃ hj : j < l.length, l[j]'hj = c := by
  have haux : ∀ (xs : List A) (s : ℕ),
      (c, j) ∈ xs.zipIdx s ↔ ∃ (hle : s ≤ j) (hlt : j - s < xs.length), xs[j - s]'hlt = c := by
    intro xs
    induction xs with
    | nil => intro s; simp
    | cons a xs ih =>
      intro s
      simp only [List.zipIdx_cons, List.mem_cons, Prod.mk.injEq, ih, List.length_cons]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨hle, hlt, heq⟩)
        · exact ⟨Nat.le_refl _, by simp, by simp⟩
        · refine ⟨by omega, by omega, ?_⟩
          have hpos : j - s = (j - (s + 1)) + 1 := by omega
          simpa [hpos] using heq
      · rintro ⟨hle, hlt, heq⟩
        by_cases hjs : j = s
        · subst hjs
          exact Or.inl ⟨by simpa using heq.symm, rfl⟩
        · right
          have hpos : j - s = (j - (s + 1)) + 1 := by omega
          exact ⟨by omega, by omega, by simpa [hpos] using heq⟩
  simpa using haux l 0

/-- Membership characterization for `clauseGadgetBlocks φ`. -/
theorem mem_clauseGadgetBlocks_iff {φ : CNF ℕ} {blk : List ClauseGadgetLetter} :
    blk ∈ clauseGadgetBlocks φ ↔
      (∃ j < φ.length, blk ∈ origClauseBlocks j) ∨
      (∃ v ∈ φ.distinctVars, blk ∈ varPosBlocks v) ∨
      (∃ (j : ℕ) (hj : j < φ.length) (k : Fin 3),
        blk ∈ occTapBlocks j k (clauseLitAt φ[j] k)) := by
  simp only [clauseGadgetBlocks, List.mem_append, List.mem_flatMap, Prod.exists, mem_zipIdx_zero]
  constructor
  · rintro ((⟨c, j, ⟨hj, rfl⟩, h0⟩ | ⟨v, hv, hvp⟩) | ⟨c, j, ⟨hj, rfl⟩, ht⟩)
    · exact Or.inl ⟨j, hj, h0⟩
    · exact Or.inr (Or.inl ⟨v, hv, hvp⟩)
    · simp only [clauseTapBlocks, List.mem_append] at ht
      rcases ht with (ht0 | ht1) | ht2
      · exact Or.inr (Or.inr ⟨j, hj, 0, ht0⟩)
      · exact Or.inr (Or.inr ⟨j, hj, 1, ht1⟩)
      · exact Or.inr (Or.inr ⟨j, hj, 2, ht2⟩)
  · rintro (⟨j, hj, h0⟩ | ⟨v, hv, hvp⟩ | ⟨j, hj, k, ht⟩)
    · exact Or.inl (Or.inl ⟨φ[j], j, ⟨hj, rfl⟩, h0⟩)
    · exact Or.inl (Or.inr ⟨v, hv, hvp⟩)
    · refine Or.inr ⟨φ[j], j, ⟨hj, rfl⟩, ?_⟩
      simp only [clauseTapBlocks, List.mem_append]
      fin_cases k
      · exact Or.inl (Or.inl ht)
      · exact Or.inl (Or.inr ht)
      · exact Or.inr ht

/-- Attach fresh trailing separator letters `.sep idx` to each block in `bs`. -/
@[expose]
def attachGadgetSeps (bs : List (List ClauseGadgetLetter)) : List ClauseGadgetLetter :=
  (bs.zipIdx.map fun q ↦ q.1 ++ [.sep q.2]).flatten

/-- Structured gadget word pattern for a `3`-CNF formula `φ`. -/
@[expose]
def clauseGadgetPattern (φ : CNF ℕ) : List ClauseGadgetLetter :=
  attachGadgetSeps (clauseGadgetBlocks φ)

/-- Boolean check that every clause of `φ` has length `3`. -/
@[expose]
def isExactThreeCNF (φ : CNF ℕ) : Bool :=
  φ.all fun c ↦ c.length == 3

/-- `isExactThreeCNF φ = true` if and only if every clause in `φ` has length `3`. -/
theorem isExactThreeCNF_eq_true_iff {φ : CNF ℕ} :
    isExactThreeCNF φ = true ↔ ∀ c ∈ φ, c.length = 3 := by
  simp [isExactThreeCNF]

/-- Encoded `ℕ`-blocks of `origClauseBlocks j`. -/
def origClauseNatBlocks (j : ℕ) : List (List ℕ) :=
  (origClauseBlocks j).map (List.map ClauseGadgetLetter.toNat)

/-- Encoded `ℕ`-blocks of `varPosBlocks v`. -/
def varPosNatBlocks (v : ℕ) : List (List ℕ) :=
  (varPosBlocks v).map (List.map ClauseGadgetLetter.toNat)

/-- Encoded `ℕ`-blocks of `clauseTapBlocks c j`. -/
def clauseTapNatBlocks (c : Clause ℕ) (j : ℕ) : List (List ℕ) :=
  (clauseTapBlocks c j).map (List.map ClauseGadgetLetter.toNat)

/-- Encoded `ℕ`-blocks of `clauseGadgetBlocks φ`. -/
def gadgetNatBlocks (φ : CNF ℕ) : List (List ℕ) :=
  (φ.zipIdx.flatMap fun p ↦ origClauseNatBlocks p.2) ++
    (φ.distinctVars.flatMap varPosNatBlocks) ++
    (φ.zipIdx.flatMap fun p ↦ clauseTapNatBlocks p.1 p.2)

/-- Polynomial-time mapping `CNF ℕ → List ℕ` reducing `ExactThreeSAT` to
`WordUnavoidability`: maps any `3`-CNF `φ` to `(clauseGadgetPattern φ).map
ClauseGadgetLetter.toNat`,
and maps non-`3`-CNF inputs to the avoidable square `[0, 0]`. -/
def threeCNFWord (φ : CNF ℕ) : List ℕ :=
  if isExactThreeCNF φ then
    ((gadgetNatBlocks φ).zipIdx.map fun q ↦ q.1 ++ [32 * q.2 + 17]).flatten
  else
    [0, 0]

private theorem zipIdx_map_eq {A B : Type*} (f : A → B) :
    ∀ (l : List A) (k : ℕ), (l.map f).zipIdx k = (l.zipIdx k).map (fun q ↦ (f q.1, q.2))
  | [], _ => rfl
  | _ :: as, k => by
    simp only [List.map_cons, List.zipIdx_cons, zipIdx_map_eq f as (k + 1)]

/-- When `isExactThreeCNF φ = false`, `threeCNFWord φ` equals `[0, 0]`. -/
theorem threeCNFWord_eq_of_false {φ : CNF ℕ} (h3 : isExactThreeCNF φ = false) :
    threeCNFWord φ = [0, 0] := by
  simp [threeCNFWord, h3]

/-- When `isExactThreeCNF φ = true`, `threeCNFWord φ` equals `(clauseGadgetPattern φ).map toNat`.
-/
theorem threeCNFWord_eq_map_toNat {φ : CNF ℕ} (h3 : isExactThreeCNF φ = true) :
    threeCNFWord φ = (clauseGadgetPattern φ).map ClauseGadgetLetter.toNat := by
  simp only [threeCNFWord, h3, ↓reduceIte, clauseGadgetPattern, attachGadgetSeps]
  have hblks : gadgetNatBlocks φ =
    (clauseGadgetBlocks φ).map (List.map ClauseGadgetLetter.toNat) := by
    simp only [gadgetNatBlocks, clauseGadgetBlocks, origClauseNatBlocks, clauseTapNatBlocks,
      List.map_append, List.map_flatMap]
    rfl
  rw [hblks, zipIdx_map_eq, List.map_map, List.map_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨blk, idx⟩ _
  simp [ClauseGadgetLetter.toNat]

section PolyTimeReduction

private abbrev encBlockList : List (List ℕ) ↪ List Bool :=
  encList encWord

private theorem linNat {γ : Type} {encIn : γ ↪ List Bool} (a b : ℕ)
    {f : γ → ℕ} (hf : ComputableInPolyTime f encIn encNat) :
    ComputableInPolyTime (fun x ↦ a * f x + b) encIn encNat :=
  binary_add' (binary_mul' (const a) hf) (const b)

private theorem consWordList {γ : Type} {encIn : γ ↪ List Bool}
    {f : γ → List ℕ} {fs : γ → List (List ℕ)}
    (hf : ComputableInPolyTime f encIn encWord)
    (hfs : ComputableInPolyTime fs encIn encBlockList) :
    ComputableInPolyTime (fun x ↦ f x :: fs x) encIn encBlockList :=
  (cons encWord).comp (hf.prod hfs)

private theorem computableInPolyTime_pair2Nat {γ : Type} {encIn : γ ↪ List Bool}
    {f g : γ → ℕ} (hf : ComputableInPolyTime f encIn encNat)
    (hg : ComputableInPolyTime g encIn encNat) :
    ComputableInPolyTime (fun x ↦ [f x, g x]) encIn encWord := by
  have h0 : ComputableInPolyTime (fun _ : γ ↦ ([] : List ℕ)) encIn encWord := const []
  have h1 : ComputableInPolyTime (fun x ↦ [g x]) encIn encWord :=
    (cons encNat).comp (hg.prod h0)
  exact (cons encNat).comp (hf.prod h1)

private theorem computableInPolyTime_quad4Nat {γ : Type} {encIn : γ ↪ List Bool}
    {f₁ f₂ f₃ f₄ : γ → ℕ}
    (h₁ : ComputableInPolyTime f₁ encIn encNat)
    (h₂ : ComputableInPolyTime f₂ encIn encNat)
    (h₃ : ComputableInPolyTime f₃ encIn encNat)
    (h₄ : ComputableInPolyTime f₄ encIn encNat) :
    ComputableInPolyTime (fun x ↦ [f₁ x, f₂ x, f₃ x, f₄ x]) encIn encWord := by
  have htail := computableInPolyTime_pair2Nat h₃ h₄
  have h2 := (cons encNat).comp (h₂.prod htail)
  exact (cons encNat).comp (h₁.prod h2)

private theorem computableInPolyTime_origClauseNatBlocks :
    ComputableInPolyTime origClauseNatBlocks encUnary encBlockList := by
  have hj : ComputableInPolyTime (fun j : ℕ ↦ j) encUnary encNat := unary_to_binary
  have ho0 := linNat 32 9 (linNat 3 0 hj)
  have ho1 := linNat 32 9 (linNat 3 1 hj)
  have ho2 := linNat 32 9 (linNat 3 2 hj)
  have ha := linNat 32 0 hj
  have hb := linNat 32 1 hj
  have hc := linNat 32 2 hj
  have hd := linNat 32 3 hj
  have h_eq : origClauseNatBlocks = fun j : ℕ ↦
      [[32 * j + 0, 32 * (3 * j + 0) + 9],
       [32 * j + 1, 32 * (3 * j + 0) + 9],
       [32 * j + 1, 32 * (3 * j + 1) + 9],
       [32 * j + 2, 32 * (3 * j + 1) + 9],
       [32 * j + 2, 32 * (3 * j + 2) + 9],
       [32 * j + 3, 32 * (3 * j + 2) + 9],
       [32 * j + 3, 32 * j + 0],
       [32 * j + 0, 32 * j + 1],
       [32 * j + 0, 32 * j + 2],
       [32 * j + 0, 32 * j + 3]] := by
    funext j; rfl
  rw [h_eq]
  exact consWordList (computableInPolyTime_pair2Nat ha ho0)
    (consWordList (computableInPolyTime_pair2Nat hb ho0)
    (consWordList (computableInPolyTime_pair2Nat hb ho1)
    (consWordList (computableInPolyTime_pair2Nat hc ho1)
    (consWordList (computableInPolyTime_pair2Nat hc ho2)
    (consWordList (computableInPolyTime_pair2Nat hd ho2)
    (consWordList (computableInPolyTime_pair2Nat hd ha)
    (consWordList (computableInPolyTime_pair2Nat ha hb)
    (consWordList (computableInPolyTime_pair2Nat ha hc)
    (consWordList (computableInPolyTime_pair2Nat ha hd) (const []))))))))))

private theorem computableInPolyTime_varPosNatBlocks :
    ComputableInPolyTime varPosNatBlocks encNat encBlockList := by
  have hv : ComputableInPolyTime (fun v : ℕ ↦ v) encNat encNat := id'
  have hap := linNat 32 4 hv
  have hbp := linNat 32 5 hv
  have hcp := linNat 32 6 hv
  have hpx := linNat 32 7 hv
  have hpy := linNat 32 8 hv
  have h_eq : varPosNatBlocks = fun v : ℕ ↦
      [[32 * v + 4, 32 * v + 7],
       [32 * v + 5, 32 * v + 7],
       [32 * v + 5, 32 * v + 8],
       [32 * v + 6, 32 * v + 8],
       [32 * v + 6, 32 * v + 4],
       [32 * v + 4, 32 * v + 5],
       [32 * v + 4, 32 * v + 6]] := by
    funext v; rfl
  rw [h_eq]
  exact consWordList (computableInPolyTime_pair2Nat hap hpx)
    (consWordList (computableInPolyTime_pair2Nat hbp hpx)
    (consWordList (computableInPolyTime_pair2Nat hbp hpy)
    (consWordList (computableInPolyTime_pair2Nat hcp hpy)
    (consWordList (computableInPolyTime_pair2Nat hcp hap)
    (consWordList (computableInPolyTime_pair2Nat hap hbp)
    (consWordList (computableInPolyTime_pair2Nat hap hcp) (const [])))))))

private def singleOccTapNatBlocks (kVal : ℕ) (p : Literal ℕ × ℕ) : List (List ℕ) :=
  let v := p.1.1
  let j := p.2
  let occ := 3 * j + kVal
  let pvar := if p.1.2 then 32 * v + 8 else 32 * v + 7
  [[32 * occ + 10, 32 * occ + 11],
   [32 * occ + 13, 32 * occ + 11],
   [32 * occ + 13, 32 * occ + 12],
   [32 * occ + 14, 32 * occ + 12],
   [32 * occ + 14, 32 * occ + 10],
   [32 * occ + 11, 32 * occ + 10],
   [32 * occ + 12, 32 * occ + 10],
   [32 * occ + 15, 32 * occ + 9, 32 * occ + 13, 32 * occ + 15],
   [32 * j + 0, 32 * occ + 15],
   [32 * occ + 15, 32 * occ + 10],
   [32 * occ + 16, pvar, 32 * occ + 14, 32 * occ + 16],
   [32 * v + 4, 32 * occ + 16],
   [32 * occ + 16, 32 * occ + 10]]

private theorem computableInPolyTime_singleOccTapNatBlocks (kVal : ℕ) :
    ComputableInPolyTime (singleOccTapNatBlocks kVal)
      (encPair (encPair encNat encBool) encUnary) encBlockList := by
  let encIn := encPair (encPair encNat encBool) encUnary
  have hj : ComputableInPolyTime (fun p : Literal ℕ × ℕ ↦ p.2) encIn encNat :=
    unary_to_binary.comp (snd _ _)
  have hlit : ComputableInPolyTime (fun p : Literal ℕ × ℕ ↦ p.1)
      encIn (encPair encNat encBool) := fst _ _
  have hv : ComputableInPolyTime (fun p : Literal ℕ × ℕ ↦ p.1.1) encIn encNat :=
    (fst encNat encBool).comp hlit
  have hpol : ComputableInPolyTime (fun p : Literal ℕ × ℕ ↦ p.1.2) encIn encBool :=
    (snd encNat encBool).comp hlit
  have hpvar : ComputableInPolyTime
      (fun p : Literal ℕ × ℕ ↦ if p.1.2 then 32 * p.1.1 + 8 else 32 * p.1.1 + 7)
      encIn encNat :=
    hpol.ite' (linNat 32 8 hv) (linNat 32 7 hv)
  have hocc : ComputableInPolyTime (fun p : Literal ℕ × ℕ ↦ 3 * p.2 + kVal) encIn encNat :=
    linNat 3 kVal hj
  have horig := linNat 32 9 hocc
  have han := linNat 32 10 hocc
  have hbn := linNat 32 11 hocc
  have hcn := linNat 32 12 hocc
  have hqo := linNat 32 13 hocc
  have hqv := linNat 32 14 hocc
  have hgo := linNat 32 15 hocc
  have hgv := linNat 32 16 hocc
  have hao := linNat 32 0 hj
  have hap := linNat 32 4 hv
  unfold singleOccTapNatBlocks
  exact consWordList (computableInPolyTime_pair2Nat han hbn)
    (consWordList (computableInPolyTime_pair2Nat hqo hbn)
    (consWordList (computableInPolyTime_pair2Nat hqo hcn)
    (consWordList (computableInPolyTime_pair2Nat hqv hcn)
    (consWordList (computableInPolyTime_pair2Nat hqv han)
    (consWordList (computableInPolyTime_pair2Nat hbn han)
    (consWordList (computableInPolyTime_pair2Nat hcn han)
    (consWordList (computableInPolyTime_quad4Nat hgo horig hqo hgo)
    (consWordList (computableInPolyTime_pair2Nat hao hgo)
    (consWordList (computableInPolyTime_pair2Nat hgo han)
    (consWordList (computableInPolyTime_quad4Nat hgv hpvar hqv hgv)
    (consWordList (computableInPolyTime_pair2Nat hap hgv)
    (consWordList (computableInPolyTime_pair2Nat hgv han) (const [])))))))))))))

private theorem clauseTapNatBlocks_eq (c : Clause ℕ) (j : ℕ) :
    clauseTapNatBlocks c j =
      singleOccTapNatBlocks 0 (c.headD (0, true), j) ++
        singleOccTapNatBlocks 1 (c.tail.headD (0, true), j) ++
        singleOccTapNatBlocks 2 (c.tail.tail.headD (0, true), j) := by
  have hocc : ∀ (k : Fin 3) (lit : Literal ℕ),
      (occTapBlocks j k lit).map (List.map ClauseGadgetLetter.toNat) =
        singleOccTapNatBlocks k.1 (lit, j) := by
    intro k ⟨v, pol⟩
    cases pol <;> rfl
  simp only [clauseTapNatBlocks, clauseTapBlocks, List.map_append,
    hocc 0 (clauseLitAt c 0), hocc 1 (clauseLitAt c 1), hocc 2 (clauseLitAt c 2)]
  rfl

private theorem computableInPolyTime_clauseTapNatBlocks :
    ComputableInPolyTime (fun p : Clause ℕ × ℕ ↦ clauseTapNatBlocks p.1 p.2)
      (encPair (encClause encNat) encUnary) encBlockList := by
  let encIn := encPair (encClause encNat) encUnary
  let encLit := encPair encNat encBool
  have hc : ComputableInPolyTime (fun p : Clause ℕ × ℕ ↦ p.1) encIn (encClause encNat) :=
    fst _ _
  have hj : ComputableInPolyTime (fun p : Clause ℕ × ℕ ↦ p.2) encIn encUnary :=
    snd _ _
  have htail1 : ComputableInPolyTime (fun p : Clause ℕ × ℕ ↦ p.1.tail)
      encIn (encClause encNat) := (listTail encLit).comp hc
  have htail2 : ComputableInPolyTime (fun p : Clause ℕ × ℕ ↦ p.1.tail.tail)
      encIn (encClause encNat) := (listTail encLit).comp htail1
  have hl0 : ComputableInPolyTime (fun p : Clause ℕ × ℕ ↦ p.1.headD (0, true)) encIn encLit :=
    listHeadDWithInput hc (const (0, true))
  have hl1 : ComputableInPolyTime (fun p : Clause ℕ × ℕ ↦ p.1.tail.headD (0, true))
      encIn encLit := listHeadDWithInput htail1 (const (0, true))
  have hl2 : ComputableInPolyTime (fun p : Clause ℕ × ℕ ↦ p.1.tail.tail.headD (0, true))
      encIn encLit := listHeadDWithInput htail2 (const (0, true))
  have heq : (fun p : Clause ℕ × ℕ ↦ clauseTapNatBlocks p.1 p.2) =
      fun p ↦ singleOccTapNatBlocks 0 (p.1.headD (0, true), p.2) ++
        singleOccTapNatBlocks 1 (p.1.tail.headD (0, true), p.2) ++
        singleOccTapNatBlocks 2 (p.1.tail.tail.headD (0, true), p.2) := by
    funext p
    exact clauseTapNatBlocks_eq p.1 p.2
  rw [heq]
  have h0 := (computableInPolyTime_singleOccTapNatBlocks 0).comp (hl0.prod hj)
  have h1 := (computableInPolyTime_singleOccTapNatBlocks 1).comp (hl1.prod hj)
  have h2 := (computableInPolyTime_singleOccTapNatBlocks 2).comp (hl2.prod hj)
  exact (listAppend encWord).comp (((listAppend encWord).comp (h0.prod h1)).prod h2)

/-- `threeCNFWord` is computable in polynomial time under `encCNF` and `encWord`. -/
@[fun_prop]
theorem computableInPolyTime_threeCNFWord :
    ComputableInPolyTime threeCNFWord encCNF encWord := by
  have hexact : ComputableInPolyTime isExactThreeCNF encCNF encBool := by
    unfold isExactThreeCNF
    fun_prop
  have hzipC : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.zipIdx)
      encCNF (encList (encPair (encClause encNat) encUnary)) :=
    zipIdx (encClause encNat)
  have hb1 : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ φ.zipIdx.flatMap fun p ↦ origClauseNatBlocks p.2)
      encCNF encBlockList :=
    flatMapWith
      (computableInPolyTime_origClauseNatBlocks.comp
        ((snd (encClause encNat) encUnary).comp
          (snd encBool (encPair (encClause encNat) encUnary))))
      (const true) hzipC
  have hb2 : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ φ.distinctVars.flatMap varPosNatBlocks)
      encCNF encBlockList :=
    flatMapWith (computableInPolyTime_varPosNatBlocks.comp (snd encBool encNat))
      (const true) (CNF.computableInPolyTime_distinctVars encNat)
  have hb3 : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ φ.zipIdx.flatMap fun p ↦ clauseTapNatBlocks p.1 p.2)
      encCNF encBlockList :=
    flatMapWith
      (computableInPolyTime_clauseTapNatBlocks.comp
        (snd encBool (encPair (encClause encNat) encUnary)))
      (const true) hzipC
  have hblks : ComputableInPolyTime gadgetNatBlocks encCNF encBlockList :=
    (listAppend encWord).comp (((listAppend encWord).comp (hb1.prod hb2)).prod hb3)
  have hsepStep : ComputableInPolyTime (fun q : List ℕ × ℕ ↦ q.1 ++ [32 * q.2 + 17])
      (encPair encWord encUnary) encWord := by
    have hz : ComputableInPolyTime (fun q : List ℕ × ℕ ↦ 32 * q.2 + 17)
        (encPair encWord encUnary) encNat :=
      linNat 32 17 (unary_to_binary.comp (snd encWord encUnary))
    have hsing : ComputableInPolyTime (fun q : List ℕ × ℕ ↦ [32 * q.2 + 17])
        (encPair encWord encUnary) encWord :=
      (cons encNat).comp (hz.prod (const []))
    exact (listAppend encNat).comp ((fst encWord encUnary).prod hsing)
  have hbranch : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ ((gadgetNatBlocks φ).zipIdx.map fun q ↦ q.1 ++ [32 * q.2 + 17]).flatten)
      encCNF encWord :=
    (flatten encNat).comp ((map hsepStep).comp ((zipIdx encWord).comp hblks))
  exact hexact.ite' hbranch (const [0, 0])

end PolyTimeReduction

section SeparatorInvisibility

private theorem attachGadgetSeps_aux_eq :
    ∀ (bs : List (List ClauseGadgetLetter)) (start : ℕ),
      ((bs.zipIdx start).map fun q ↦ q.1 ++ [.sep q.2]).flatten =
        match bs with
        | [] => []
        | blk :: rest => blk ++ [.sep start] ++
            ((rest.zipIdx (start + 1)).map fun q ↦ q.1 ++ [.sep q.2]).flatten
  | [], _ => rfl
  | _ :: _, _ => by simp [List.zipIdx_cons, List.append_assoc]

theorem no_sep_in_clauseGadgetBlocks (φ : CNF ℕ) :
    ∀ blk ∈ clauseGadgetBlocks φ, ∀ u ∈ blk, u.isSep = false := by
  intro blk hblk u hu
  simp only [clauseGadgetBlocks, List.mem_append, List.mem_flatMap, Prod.exists] at hblk
  rcases hblk with (⟨c, j, _, h0⟩ | ⟨v, _, hv⟩) | ⟨c, j, _, ht⟩
  · simp only [origClauseBlocks, List.mem_cons, List.not_mem_nil, or_false] at h0
    rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [List.mem_cons, List.not_mem_nil, or_false] at hu;
       rcases hu with rfl | rfl <;> rfl)
  · simp only [varPosBlocks, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [List.mem_cons, List.not_mem_nil, or_false] at hu;
       rcases hu with rfl | rfl <;> rfl)
  · simp only [clauseTapBlocks, List.mem_append] at ht
    have htap : ∀ (k : Fin 3) (lit : Literal ℕ),
        blk ∈ occTapBlocks j k lit → u.isSep = false := by
      intro k lit hmem
      have hpv : (conflictVarSlot lit).isSep = false := by
        rcases lit with ⟨_, _ | _⟩ <;> rfl
      simp only [occTapBlocks, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      · rcases hu with rfl | rfl <;> rfl
      · rcases hu with rfl | rfl <;> rfl
      · rcases hu with rfl | rfl <;> rfl
      · rcases hu with rfl | rfl <;> rfl
      · rcases hu with rfl | rfl <;> rfl
      · rcases hu with rfl | rfl <;> rfl
      · rcases hu with rfl | rfl <;> rfl
      · rcases hu with rfl | rfl | rfl | rfl <;> rfl
      · rcases hu with rfl | rfl <;> rfl
      · rcases hu with rfl | rfl <;> rfl
      · rcases hu with rfl | rfl | rfl | rfl
        · rfl
        · exact hpv
        · rfl
        · rfl
      · rcases hu with rfl | rfl <;> rfl
      · rcases hu with rfl | rfl <;> rfl
    rcases ht with (ht0 | ht1) | ht2
    · exact htap 0 _ ht0
    · exact htap 1 _ ht1
    · exact htap 2 _ ht2

private theorem blk_infix_zipSeps :
    ∀ (bs : List (List ClauseGadgetLetter)) (start : ℕ) {blk : List ClauseGadgetLetter},
      blk ∈ bs → blk <:+: ((bs.zipIdx start).map fun q ↦ q.1 ++ [.sep q.2]).flatten
  | [], _, _, h => by simp at h
  | b :: bs, start, blk, h => by
    rw [attachGadgetSeps_aux_eq]
    rcases List.mem_cons.mp h with rfl | hbs
    · exact ⟨[], [.sep start] ++ ((bs.zipIdx (start + 1)).map fun q ↦ q.1 ++ [.sep q.2]).flatten,
        by simp⟩
    · rcases blk_infix_zipSeps bs (start + 1) hbs with ⟨s, t, hst⟩
      exact ⟨b ++ [.sep start] ++ s, t, by simp [← hst, List.append_assoc]⟩

theorem blk_infix_clauseGadgetPattern (φ : CNF ℕ) {blk : List ClauseGadgetLetter}
    (hblk : blk ∈ clauseGadgetBlocks φ) : blk <:+: clauseGadgetPattern φ :=
  blk_infix_zipSeps (clauseGadgetBlocks φ) 0 hblk

theorem mem_sep_zipSeps :
    ∀ (bs : List (List ClauseGadgetLetter)),
      (∀ blk ∈ bs, ∀ u ∈ blk, u.isSep = false) →
      ∀ (start z : ℕ),
        ClauseGadgetLetter.sep z ∈ ((bs.zipIdx start).map fun q ↦ q.1 ++ [.sep q.2]).flatten ↔
          start ≤ z ∧ z < start + bs.length
  | [], _, start, z => by simp
  | blk :: bs, hns, start, z => by
    rw [attachGadgetSeps_aux_eq]
    have hnot : ClauseGadgetLetter.sep z ∉ blk := fun hm ↦ by
      have := hns blk (by simp) (.sep z) hm
      simp [ClauseGadgetLetter.isSep] at this
    have ih := mem_sep_zipSeps bs (fun b hb ↦ hns b (by simp [hb])) (start + 1) z
    simp only [List.mem_append, List.mem_singleton, ClauseGadgetLetter.sep.injEq, hnot, false_or,
      ih,
      List.length_cons]
    omega

private theorem count_sep_zipSeps :
    ∀ (bs : List (List ClauseGadgetLetter)),
      (∀ blk ∈ bs, ∀ u ∈ blk, u.isSep = false) →
      ∀ (start z : ℕ),
        (((bs.zipIdx start).map fun q ↦ q.1 ++ [.sep q.2]).flatten).count (.sep z) ≤ 1
  | [], _, _, _ => by simp
  | blk :: bs, hns, start, z => by
    rw [attachGadgetSeps_aux_eq]
    have hnot : ClauseGadgetLetter.sep z ∉ blk := fun hm ↦ by
      have := hns blk (by simp) (.sep z) hm
      simp [ClauseGadgetLetter.isSep] at this
    simp only [List.count_append, List.count_eq_zero.mpr hnot, Nat.zero_add]
    by_cases hz : z = start
    · subst hz
      have hnt : ClauseGadgetLetter.sep z ∉
          ((bs.zipIdx (z + 1)).map fun q ↦ q.1 ++ [.sep q.2]).flatten := by
        rw [mem_sep_zipSeps bs (fun b hb ↦ hns b (by simp [hb]))]
        omega
      rw [List.count_eq_zero.mpr hnt]
      simp
    · have hcm : ([ClauseGadgetLetter.sep start] : List ClauseGadgetLetter).count (.sep z) = 0 :=
        List.count_eq_zero.mpr (by simp [hz])
      rw [hcm, Nat.zero_add]
      exact count_sep_zipSeps bs (fun b hb ↦ hns b (by simp [hb])) (start + 1) z

private theorem count_filter_le_rep (p : ClauseGadgetLetter → Bool) (z : ClauseGadgetLetter) :
    ∀ l : List ClauseGadgetLetter, (l.filter p).count z ≤ l.count z
  | [] => by simp
  | a :: as => by
    simp only [List.filter_cons]
    split_ifs
    · simp only [List.count_cons]
      exact Nat.add_le_add_right (count_filter_le_rep p z as) _
    · calc
        (as.filter p).count z ≤ as.count z := count_filter_le_rep p z as
        _ ≤ (a :: as).count z := by simp only [List.count_cons]; omega

theorem count_sep_deleteLetters_clauseGadgetPattern (φ : CNF ℕ) (B : Set ClauseGadgetLetter)
    (z : ℕ) : (deleteLetters B (clauseGadgetPattern φ)).count (.sep z) ≤ 1 := by
  classical
  rw [deleteLetters_eq_filter]
  exact (count_filter_le_rep _ _ _).trans
    (count_sep_zipSeps (clauseGadgetBlocks φ) (no_sep_in_clauseGadgetBlocks φ) 0 z)

theorem deleteLetters_zipSeps {B : Set ClauseGadgetLetter}
    (hB : ∀ z : ℕ, ClauseGadgetLetter.sep z ∉ B) :
    ∀ (bs : List (List ClauseGadgetLetter)) (start : ℕ),
      deleteLetters B (((bs.zipIdx start).map fun q ↦ q.1 ++ [.sep q.2]).flatten) =
        (((bs.map (deleteLetters B)).zipIdx start).map fun q ↦ q.1 ++ [.sep q.2]).flatten
  | [], _ => by simp
  | blk :: bs, start => by
    rw [attachGadgetSeps_aux_eq, List.map_cons, attachGadgetSeps_aux_eq]
    simp only [deleteLetters_append, deleteLetters_cons_of_not_mem (hB start),
      deleteLetters_nil]
    congr 1
    exact deleteLetters_zipSeps hB bs (start + 1)

private theorem getElem_eq_of_eq_rep {A : Type*} {l₁ l₂ : List A} (h : l₁ = l₂) (i : ℕ)
    (h₁ : i < l₁.length) (h₂ : i < l₂.length) : l₁[i]'h₁ = l₂[i]'h₂ := by
  subst h
  rfl

private theorem infix_pair_zipSeps :
    ∀ (bs : List (List ClauseGadgetLetter)),
      (∀ blk ∈ bs, ∀ u ∈ blk, u.isSep = false) →
      ∀ (start : ℕ) {x y : ClauseGadgetLetter},
        x.isSep = false → y.isSep = false →
        ([x, y] <:+: ((bs.zipIdx start).map fun q ↦ q.1 ++ [.sep q.2]).flatten ↔
          ∃ blk ∈ bs, [x, y] <:+: blk)
  | [], _, _, _, _, _, _ => by
    simp only [List.zipIdx_nil, List.map_nil, List.flatten_nil, List.not_mem_nil, false_and,
      exists_false, iff_false]
    rintro ⟨s, t, h⟩; simp at h
  | blk :: bs, hns, start, x, y, hx, hy => by
    have ih := infix_pair_zipSeps bs (fun b hb ↦ hns b (by simp [hb])) (start + 1) hx hy
    constructor
    · rintro ⟨s, t, hst⟩
      rw [attachGadgetSeps_aux_eq] at hst
      simp only [List.append_assoc] at hst
      let tailW := ((bs.zipIdx (start + 1)).map fun q ↦ q.1 ++ [.sep q.2]).flatten
      change s ++ ([x, y] ++ t) = blk ++ ([ClauseGadgetLetter.sep start] ++ tailW) at hst
      have hlen_eq := congrArg List.length hst
      by_cases hs_lt : s.length + 1 < blk.length
      · refine ⟨blk, List.mem_cons_self .., s.take s.length, blk.drop (s.length + 2), ?_⟩
        have hget0 : (s ++ ([x, y] ++ t))[s.length]'(by simp) = x := by
          rw [List.getElem_append_right (Nat.le_refl _)]; simp
        have hget1 : (s ++ ([x, y] ++ t))[s.length + 1]'(by simp) = y := by
          have hcat : s ++ ([x, y] ++ t) = (s ++ [x]) ++ (y :: t) := by simp [List.append_assoc]
          simp only [hcat]; rw [List.getElem_append_right (by simp)]; simp
        have hrhs0 : (blk ++ ([ClauseGadgetLetter.sep start] ++ tailW))[s.length]'(by
            simp at hlen_eq ⊢; omega) = blk[s.length]'(by omega) :=
          List.getElem_append_left (by omega)
        have hrhs1 : (blk ++ ([ClauseGadgetLetter.sep start] ++ tailW))[s.length + 1]'(by
            simp at hlen_eq ⊢; omega) = blk[s.length + 1]'(by omega) :=
          List.getElem_append_left (by omega)
        have hx_eq : blk[s.length]'(by omega) = x :=
          hrhs0.symm.trans ((getElem_eq_of_eq_rep hst.symm s.length _ _).trans hget0)
        have hy_eq : blk[s.length + 1]'(by omega) = y :=
          hrhs1.symm.trans ((getElem_eq_of_eq_rep hst.symm (s.length + 1) _ _).trans hget1)
        have hpre : s.take s.length = blk.take s.length := by
          have htake := congrArg (List.take s.length) hst
          rw [List.take_left, List.take_append_of_le_length (by omega)] at htake
          simpa using htake
        rw [hpre]
        have ht1 := List.take_succ_eq_append_getElem (l := blk) (i := s.length) (by omega)
        have ht2 := List.take_succ_eq_append_getElem (l := blk) (i := s.length + 1) (by omega)
        calc
          blk.take s.length ++ [x, y] ++ blk.drop (s.length + 2)
              = (blk.take s.length ++ [blk[s.length]] ++ [blk[s.length + 1]]) ++
                  blk.drop (s.length + 2) := by simp [hx_eq, hy_eq, List.append_assoc]
          _ = blk.take (s.length + 2) ++ blk.drop (s.length + 2) := by rw [← ht1, ← ht2]
          _ = blk := List.take_append_drop _ _
      · by_cases hs_eq1 : s.length + 1 = blk.length
        · exfalso
          have hget1 : (s ++ ([x, y] ++ t))[s.length + 1]'(by simp) = y := by
            have hcat : s ++ ([x, y] ++ t) = (s ++ [x]) ++ (y :: t) := by simp [List.append_assoc]
            simp only [hcat]; rw [List.getElem_append_right (by simp)]; simp
          have hrhs1 : (blk ++ ([ClauseGadgetLetter.sep start] ++ tailW))[s.length + 1]'(by
              simp at hlen_eq ⊢; omega) = .sep start := by
            rw [List.getElem_append_right (by omega)]; simp [hs_eq1]
          have hy_sep : y = .sep start :=
            hget1.symm.trans ((getElem_eq_of_eq_rep hst (s.length + 1) _ _).trans hrhs1)
          rw [hy_sep] at hy; simp [ClauseGadgetLetter.isSep] at hy
        · by_cases hs_eq0 : s.length = blk.length
          · exfalso
            have hget0 : (s ++ ([x, y] ++ t))[s.length]'(by simp) = x := by
              rw [List.getElem_append_right (Nat.le_refl _)]; simp
            have hrhs0 : (blk ++ ([ClauseGadgetLetter.sep start] ++ tailW))[s.length]'(by
                simp at hlen_eq ⊢; omega) = .sep start := by
              rw [List.getElem_append_right (by omega)]; simp [hs_eq0]
            have hx_sep : x = .sep start :=
              hget0.symm.trans ((getElem_eq_of_eq_rep hst s.length _ _).trans hrhs0)
            rw [hx_sep] at hx; simp [ClauseGadgetLetter.isSep] at hx
          · let m0 := (blk ++ [ClauseGadgetLetter.sep start]).length
            have hge : m0 ≤ s.length := by dsimp [m0]; simp; omega
            have hpref : blk ++ [ClauseGadgetLetter.sep start] <+: s := by
              have htake := congrArg (List.take m0) hst
              have hcat : blk ++ ([ClauseGadgetLetter.sep start] ++ tailW) =
                  (blk ++ [ClauseGadgetLetter.sep start]) ++ tailW := by simp [List.append_assoc]
              rw [hcat, List.take_left, List.take_append_of_le_length hge] at htake
              refine ⟨s.drop m0, ?_⟩
              rw [← htake]
              exact List.take_append_drop m0 s
            rcases hpref with ⟨s', rfl⟩
            have htail : [x, y] <:+: tailW := by
              refine ⟨s', t, ?_⟩
              have hst' : (blk ++ [ClauseGadgetLetter.sep start]) ++ (s' ++ ([x, y] ++ t)) =
                  (blk ++ [ClauseGadgetLetter.sep start]) ++ tailW := by
                simpa [List.append_assoc] using hst
              simpa [List.append_assoc] using List.append_cancel_left hst'
            obtain ⟨b, hb, hxy⟩ := ih.mp htail
            exact ⟨b, List.mem_cons_of_mem _ hb, hxy⟩
    · rintro ⟨b, hb, hxy⟩
      exact hxy.trans (blk_infix_zipSeps (blk :: bs) start hb)

/-- Non-separator `2`-factor inside a deleted block of `clauseGadgetBlocks φ`. -/
@[expose]
def GadgetBlockPair (φ : CNF ℕ) (B : Set ClauseGadgetLetter) (x y : ClauseGadgetLetter) : Prop :=
  x.isSep = false ∧ y.isSep = false ∧ ∃ blk ∈ clauseGadgetBlocks φ, [x, y] <:+: deleteLetters B blk

/-- Shared-right-neighbor step on `GadgetBlockPair φ B`. -/
@[expose]
def GadgetSameRight (φ : CNF ℕ) (B : Set ClauseGadgetLetter) (u v : ClauseGadgetLetter) : Prop :=
  ∃ c, GadgetBlockPair φ B u c ∧ GadgetBlockPair φ B v c

private theorem gadgetBlockPair_iff_infix {φ : CNF ℕ} {B : Set ClauseGadgetLetter}
    (hB : ∀ z, ClauseGadgetLetter.sep z ∉ B) {x y : ClauseGadgetLetter}
    (hx : x.isSep = false) (hy : y.isSep = false) :
    [x, y] <:+: deleteLetters B (clauseGadgetPattern φ) ↔ GadgetBlockPair φ B x y := by
  rw [clauseGadgetPattern, attachGadgetSeps, deleteLetters_zipSeps hB]
  have hns : ∀ blk ∈ (clauseGadgetBlocks φ).map (deleteLetters B), ∀ u ∈ blk, u.isSep = false := by
    intro blk hblk u hu
    rcases List.mem_map.mp hblk with ⟨b₀, hb₀, rfl⟩
    rw [mem_deleteLetters] at hu
    exact no_sep_in_clauseGadgetBlocks φ b₀ hb₀ u hu.1
  rw [infix_pair_zipSeps _ hns 0 hx hy]
  simp only [GadgetBlockPair, hx, hy, true_and, List.mem_map]
  exact ⟨fun ⟨_, ⟨b₀, hb₀, rfl⟩, h⟩ ↦ ⟨b₀, hb₀, h⟩,
    fun ⟨b₀, hb₀, h⟩ ↦ ⟨deleteLetters B b₀, ⟨b₀, hb₀, rfl⟩, h⟩⟩

private theorem unique_sep_neighbors_rep {φ : CNF ℕ} {B : Set ClauseGadgetLetter} (z : ℕ) :
    let w := deleteLetters B (clauseGadgetPattern φ)
    (∀ {u₁ u₂}, [u₁, .sep z] <:+: w → [u₂, .sep z] <:+: w → u₁ = u₂) ∧
    (∀ {v₁ v₂}, [.sep z, v₁] <:+: w → [.sep z, v₂] <:+: w → v₁ = v₂) ∧
    ¬ ([.sep z, .sep z] <:+: w) := by
  intro w
  have hcnt := count_sep_deleteLetters_clauseGadgetPattern φ B z
  have hgen : ∀ {l : List ClauseGadgetLetter}, l.count (.sep z) ≤ 1 →
      (∀ {u₁ u₂}, [u₁, .sep z] <:+: l → [u₂, .sep z] <:+: l → u₁ = u₂) ∧
      (∀ {v₁ v₂}, [.sep z, v₁] <:+: l → [.sep z, v₂] <:+: l → v₁ = v₂) ∧
      ¬ ([.sep z, .sep z] <:+: l) := by
    intro l hl
    induction l with
    | nil =>
      refine ⟨?_, ?_, ?_⟩
      · intro _ _ ⟨s, t, h⟩; simp at h
      · intro _ _ ⟨s, t, h⟩; simp at h
      · rintro ⟨s, t, h⟩; simp at h
    | cons a rest ihr =>
      cases rest with
      | nil =>
        refine ⟨?_, ?_, ?_⟩
        · intro _ _ ⟨s, t, h⟩; have := congrArg List.length h; simp at this; omega
        · intro _ _ ⟨s, t, h⟩; have := congrArg List.length h; simp at this; omega
        · rintro ⟨s, t, h⟩; have := congrArg List.length h; simp at this; omega
      | cons b rest' =>
        have htail : (b :: rest').count (.sep z) ≤ 1 := by
          rw [List.count_cons] at hl; omega
        obtain ⟨ihL, ihR, ihZ⟩ := ihr htail
        have hp : ∀ {x y : ClauseGadgetLetter}, [x, y] <:+: a :: b :: rest' ↔
            (x = a ∧ y = b) ∨ [x, y] <:+: b :: rest' := by
          intro x y; constructor
          · rintro ⟨s, t, hst⟩
            cases s with
            | nil =>
              simp only [List.nil_append, List.cons_append, List.cons.injEq] at hst
              exact Or.inl ⟨hst.1, hst.2.1⟩
            | cons c cs =>
              simp only [List.cons_append, List.cons.injEq] at hst
              exact Or.inr ⟨cs, t, hst.2⟩
          · rintro (⟨rfl, rfl⟩ | ⟨s, t, hst⟩)
            · exact ⟨[], rest', rfl⟩
            · exact ⟨a :: s, t, by simp [hst]⟩
        have hmem2 : ∀ {u}, [u, b] <:+: b :: rest' → b ∈ rest' := by
          rintro u ⟨s, t, hst⟩
          cases s with
          | nil =>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at hst
            have hbt : b :: t = rest' := hst.2
            rw [← hbt]; simp
          | cons c cs =>
            simp only [List.cons_append, List.cons.injEq] at hst
            have hin : [u, b] <:+: rest' := ⟨cs, t, hst.2⟩
            exact hin.subset (by simp)
        refine ⟨?_, ?_, ?_⟩
        · intro u₁ u₂ h₁ h₂
          rcases hp.mp h₁ with ⟨hu₁, hzb⟩ | h₁'
          · rcases hp.mp h₂ with ⟨hu₂, _⟩ | h₂'
            · exact hu₁.trans hu₂.symm
            · exfalso; rw [hzb] at h₂' hl
              have := List.count_pos_iff.mpr (hmem2 h₂')
              rw [List.count_cons, List.count_cons_self] at hl; omega
          · rcases hp.mp h₂ with ⟨_, hzb⟩ | h₂'
            · exfalso; rw [hzb] at h₁' hl
              have := List.count_pos_iff.mpr (hmem2 h₁')
              rw [List.count_cons, List.count_cons_self] at hl; omega
            · exact ihL h₁' h₂'
        · intro v₁ v₂ h₁ h₂
          rcases hp.mp h₁ with ⟨hza, hv₁⟩ | h₁'
          · rcases hp.mp h₂ with ⟨_, hv₂⟩ | h₂'
            · exact hv₁.trans hv₂.symm
            · exfalso; rw [hza] at h₂' hl
              have ha_mem : a ∈ [a, v₂] := List.mem_cons_self ..
              have := List.count_pos_iff.mpr (h₂'.subset ha_mem)
              rw [List.count_cons_self] at hl; omega
          · rcases hp.mp h₂ with ⟨hza, _⟩ | h₂'
            · exfalso; rw [hza] at h₁' hl
              have ha_mem : a ∈ [a, v₁] := List.mem_cons_self ..
              have := List.count_pos_iff.mpr (h₁'.subset ha_mem)
              rw [List.count_cons_self] at hl; omega
            · exact ihR h₁' h₂'
        · intro hzz
          rcases hp.mp hzz with ⟨hza, hzb⟩ | hzz'
          · rw [← hza, ← hzb, List.count_cons_self, List.count_cons_self] at hl; omega
          · exact ihZ hzz'
  exact hgen hcnt

/-- **Separator-Invisibility on `clauseGadgetPattern φ`**. -/
theorem gadget_hasAlternatingChain_nonSep_iff {φ : CNF ℕ} {B : Set ClauseGadgetLetter}
    (hB : ∀ z, ClauseGadgetLetter.sep z ∉ B) {x y : ClauseGadgetLetter}
    (hx : x.isSep = false) (hy : y.isSep = false) :
    CslibFrontier.Word.HasAlternatingChain (deleteLetters B (clauseGadgetPattern φ)) x y ↔
      ∃ b, Relation.ReflTransGen (GadgetSameRight φ B) x b ∧ GadgetBlockPair φ B b y := by
  let w := deleteLetters B (clauseGadgetPattern φ)
  rw [hasAlternatingChain_iff_reflTransGen]
  constructor
  · rintro ⟨b, hxb, hby⟩
    have hinv : ∀ u, Relation.ReflTransGen (SameRightNeighbor w) x u →
        (u.isSep = false ∧ Relation.ReflTransGen (GadgetSameRight φ B) x u) ∨
        (∃ z u₀ c₀, u = .sep z ∧ u₀.isSep = false ∧
          Relation.ReflTransGen (GadgetSameRight φ B) x u₀ ∧
          [u₀, c₀] <:+: w ∧ [ClauseGadgetLetter.sep z, c₀] <:+: w) := by
      intro u hxu
      induction hxu with
      | refl => exact Or.inl ⟨hx, Relation.ReflTransGen.refl⟩
      | @tail u₁ u₂ _ hstep ih =>
        rcases sameRightNeighbor_iff.mp hstep with ⟨c, hu₁c, hu₂c⟩
        rcases ih with ⟨hu₁_ns, hp₁⟩ | ⟨z₁, u₀, c₀, rfl, hu₀_ns, hp₀, hu₀c₀, hzc₀⟩
        · by_cases hsc : c.isSep = false
          · by_cases hsu₂ : u₂.isSep = false
            · exact Or.inl ⟨hsu₂, hp₁.tail
                ⟨c, (gadgetBlockPair_iff_infix hB hu₁_ns hsc).mp hu₁c,
                    (gadgetBlockPair_iff_infix hB hsu₂ hsc).mp hu₂c⟩⟩
            · cases u₂ with
              | sep z₂ => exact Or.inr ⟨z₂, u₁, c, rfl, hu₁_ns, hp₁, hu₁c, hu₂c⟩
              | _ => exact absurd rfl hsu₂
          · cases c with
            | sep zc =>
              have hu := (unique_sep_neighbors_rep zc).1 hu₁c hu₂c
              subst hu; exact Or.inl ⟨hu₁_ns, hp₁⟩
            | _ => exact absurd rfl hsc
        · have hceq : c₀ = c := (unique_sep_neighbors_rep z₁).2.1 hzc₀ hu₁c
          subst hceq
          by_cases hsc : c₀.isSep = false
          · by_cases hsu₂ : u₂.isSep = false
            · exact Or.inl ⟨hsu₂, hp₀.tail
                ⟨c₀, (gadgetBlockPair_iff_infix hB hu₀_ns hsc).mp hu₀c₀,
                     (gadgetBlockPair_iff_infix hB hsu₂ hsc).mp hu₂c⟩⟩
            · cases u₂ with
              | sep z₂ => exact Or.inr ⟨z₂, u₀, c₀, rfl, hu₀_ns, hp₀, hu₀c₀, hu₂c⟩
              | _ => exact absurd rfl hsu₂
          · cases c₀ with
            | sep zc =>
              have hu := (unique_sep_neighbors_rep zc).1 hu₀c₀ hu₂c
              subst hu; exact Or.inl ⟨hu₀_ns, hp₀⟩
            | _ => exact absurd rfl hsc
    rcases hinv b hxb with ⟨hb_ns, hp⟩ | ⟨z, u₀, c₀, rfl, hu₀_ns, hp₀, hu₀c₀, hzc₀⟩
    · exact ⟨b, hp, (gadgetBlockPair_iff_infix hB hb_ns hy).mp hby⟩
    · have hceq : c₀ = y := (unique_sep_neighbors_rep z).2.1 hzc₀ hby
      subst hceq
      exact ⟨u₀, hp₀, (gadgetBlockPair_iff_infix hB hu₀_ns hy).mp hu₀c₀⟩
  · rintro ⟨b, hpath, hbp⟩
    refine ⟨b, ?_, (gadgetBlockPair_iff_infix hB hbp.1 hy).mpr hbp⟩
    clear hbp
    induction hpath with
    | refl => exact Relation.ReflTransGen.refl
    | @tail u₁ u₂ _ hstep ih =>
      rcases hstep with ⟨c, h₁, h₂⟩
      exact ih.tail (sameRightNeighbor_iff.mpr
        ⟨c, (gadgetBlockPair_iff_infix hB h₁.1 h₁.2.1).mpr h₁,
            (gadgetBlockPair_iff_infix hB h₂.1 h₂.2.1).mpr h₂⟩)

/-- Exact characterization of `2`-factors inside `deleteLetters B [u, v]`. -/
theorem infix_pair_two_gadget {B : Set ClauseGadgetLetter} {u v x y : ClauseGadgetLetter} :
    [x, y] <:+: deleteLetters B [u, v] ↔ x = u ∧ y = v ∧ u ∉ B ∧ v ∉ B := by
  constructor
  · intro h
    by_cases hu : u ∈ B
    · rw [deleteLetters_cons_of_mem hu] at h
      by_cases hv : v ∈ B
      · rw [deleteLetters_cons_of_mem hv, deleteLetters_nil] at h
        rcases h with ⟨s, t, hst⟩; simp at hst
      · rw [deleteLetters_cons_of_not_mem hv, deleteLetters_nil] at h
        rcases h with ⟨s, t, hst⟩; have := congrArg List.length hst; simp at this; omega
    · rw [deleteLetters_cons_of_not_mem hu] at h
      by_cases hv : v ∈ B
      · rw [deleteLetters_cons_of_mem hv, deleteLetters_nil] at h
        rcases h with ⟨s, t, hst⟩; have := congrArg List.length hst; simp at this; omega
      · rw [deleteLetters_cons_of_not_mem hv, deleteLetters_nil] at h
        rcases h with ⟨s, t, hst⟩
        have hlen := congrArg List.length hst
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        have hs : s = [] := List.eq_nil_of_length_eq_zero (by omega)
        have ht : t = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hs ht
        simp only [List.nil_append, List.append_nil, List.cons.injEq, and_true] at hst
        exact ⟨hst.1, hst.2, hu, hv⟩
  · rintro ⟨rfl, rfl, hu, hv⟩
    rw [deleteLetters_cons_of_not_mem hu, deleteLetters_cons_of_not_mem hv, deleteLetters_nil]

/-- Exact characterization of `2`-factors inside a deleted `4`-letter guard `[g, p, q, g]`. -/
theorem infix_pair_guard4 {B : Set ClauseGadgetLetter} {g p q x y : ClauseGadgetLetter} :
    [x, y] <:+: deleteLetters B [g, p, q, g] ↔
      (x = p ∧ y = q ∧ p ∉ B ∧ q ∉ B) ∨
      (g ∉ B ∧ (
        (x = g ∧ y = p ∧ p ∉ B) ∨
        (x = q ∧ y = g ∧ q ∉ B) ∨
        (x = g ∧ y = q ∧ p ∈ B ∧ q ∉ B) ∨
        (x = p ∧ y = g ∧ p ∉ B ∧ q ∈ B) ∨
        (x = g ∧ y = g ∧ p ∈ B ∧ q ∈ B))) := by
  have hp0 : ¬ ([x, y] <:+: ([] : List ClauseGadgetLetter)) := by rintro ⟨s, t, h⟩; simp at h
  have hp1 : ∀ {a : ClauseGadgetLetter}, ¬ ([x, y] <:+: [a]) := by
    rintro a ⟨s, t, h⟩; have := congrArg List.length h; simp at this; omega
  have hp2 : ∀ {a b : ClauseGadgetLetter}, [x, y] <:+: [a, b] ↔ x = a ∧ y = b := by
    intro a b; constructor
    · rintro ⟨s, t, hst⟩
      have hlen := congrArg List.length hst
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      have hs : s = [] := List.eq_nil_of_length_eq_zero (by omega)
      have ht : t = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hs ht
      simp only [List.nil_append, List.append_nil, List.cons.injEq, and_true] at hst
      exact hst
    · rintro ⟨rfl, rfl⟩; exact List.infix_refl _
  have hp3 : ∀ {a b c : ClauseGadgetLetter}, [x, y] <:+: [a, b, c] ↔
      (x = a ∧ y = b) ∨ (x = b ∧ y = c) := by
    intro a b c; constructor
    · rintro ⟨s, t, hst⟩
      cases s with
      | nil =>
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at hst
        exact Or.inl ⟨hst.1, hst.2.1⟩
      | cons u us =>
        have hlen := congrArg List.length hst
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        have hus : us = [] := List.eq_nil_of_length_eq_zero (by omega)
        have ht : t = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hus ht
        simp only [List.cons_append, List.nil_append, List.append_nil, List.cons.injEq,
          and_true] at hst
        exact Or.inr ⟨hst.2.1, hst.2.2⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨[], [c], rfl⟩
      · exact ⟨[a], [], rfl⟩
  have hp4 : ∀ {a b c d : ClauseGadgetLetter}, [x, y] <:+: [a, b, c, d] ↔
      (x = a ∧ y = b) ∨ (x = b ∧ y = c) ∨ (x = c ∧ y = d) := by
    intro a b c d; constructor
    · rintro ⟨s, t, hst⟩
      cases s with
      | nil =>
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at hst
        exact Or.inl ⟨hst.1, hst.2.1⟩
      | cons u us =>
        simp only [List.cons_append, List.cons.injEq] at hst
        rcases hp3.mp ⟨us, t, hst.2⟩ with h1 | h2
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr h2)
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨[], [c, d], rfl⟩
      · exact ⟨[a], [d], rfl⟩
      · exact ⟨[a, b], [], rfl⟩
  by_cases hg : g ∈ B <;> by_cases hp : p ∈ B <;> by_cases hq : q ∈ B
  · rw [deleteLetters_cons_of_mem hg, deleteLetters_cons_of_mem hp,
      deleteLetters_cons_of_mem hq, deleteLetters_cons_of_mem hg, deleteLetters_nil]
    exact ⟨fun h ↦ (hp0 h).elim, by tauto⟩
  · rw [deleteLetters_cons_of_mem hg, deleteLetters_cons_of_mem hp,
      deleteLetters_cons_of_not_mem hq, deleteLetters_cons_of_mem hg, deleteLetters_nil]
    exact ⟨fun h ↦ (hp1 h).elim, by tauto⟩
  · rw [deleteLetters_cons_of_mem hg, deleteLetters_cons_of_not_mem hp,
      deleteLetters_cons_of_mem hq, deleteLetters_cons_of_mem hg, deleteLetters_nil]
    exact ⟨fun h ↦ (hp1 h).elim, by tauto⟩
  · rw [deleteLetters_cons_of_mem hg, deleteLetters_cons_of_not_mem hp,
      deleteLetters_cons_of_not_mem hq, deleteLetters_cons_of_mem hg, deleteLetters_nil, hp2]
    tauto
  · rw [deleteLetters_cons_of_not_mem hg, deleteLetters_cons_of_mem hp,
      deleteLetters_cons_of_mem hq, deleteLetters_cons_of_not_mem hg, deleteLetters_nil, hp2]
    tauto
  · rw [deleteLetters_cons_of_not_mem hg, deleteLetters_cons_of_mem hp,
      deleteLetters_cons_of_not_mem hq, deleteLetters_cons_of_not_mem hg, deleteLetters_nil, hp3]
    tauto
  · rw [deleteLetters_cons_of_not_mem hg, deleteLetters_cons_of_not_mem hp,
      deleteLetters_cons_of_mem hq, deleteLetters_cons_of_not_mem hg, deleteLetters_nil, hp3]
    tauto
  · rw [deleteLetters_cons_of_not_mem hg, deleteLetters_cons_of_not_mem hp,
      deleteLetters_cons_of_not_mem hq, deleteLetters_cons_of_not_mem hg, deleteLetters_nil, hp4]
    tauto

/-- Free-set criterion 1 (`noLeft`): if no `x ∈ X` occurs as left component of `GadgetBlockPair φ
B`,
then `X` is a free set for `deleteLetters B (clauseGadgetPattern φ)`. -/
theorem isFreeSet_of_no_left {φ : CNF ℕ} {B X : Set ClauseGadgetLetter}
    (hB : ∀ z, ClauseGadgetLetter.sep z ∉ B) (hX : ∀ x ∈ X, x.isSep = false)
    (hnoL : ∀ x ∈ X, ∀ c, ¬ GadgetBlockPair φ B x c) :
    IsFreeSet (deleteLetters B (clauseGadgetPattern φ)) X := by
  rw [isFreeSet_iff]
  intro x hx y hy hch
  rw [gadget_hasAlternatingChain_nonSep_iff hB (hX x hx) (hX y hy)] at hch
  rcases hch with ⟨b, hpath, hby⟩
  cases hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact hnoL x hx y hby
  | head hsr _ _ =>
    rcases hsr with ⟨c, hxc, _⟩
    exact hnoL x hx c hxc

/-- Free-set criterion 2 (`noRight`): if no `y ∈ X` occurs as right component of
`GadgetBlockPair φ B`, then `X` is a free set for `deleteLetters B (clauseGadgetPattern φ)`. -/
theorem isFreeSet_of_no_right {φ : CNF ℕ} {B X : Set ClauseGadgetLetter}
    (hB : ∀ z, ClauseGadgetLetter.sep z ∉ B) (hX : ∀ x ∈ X, x.isSep = false)
    (hnoR : ∀ y ∈ X, ∀ b, ¬ GadgetBlockPair φ B b y) :
    IsFreeSet (deleteLetters B (clauseGadgetPattern φ)) X := by
  rw [isFreeSet_iff]
  intro x hx y hy hch
  rw [gadget_hasAlternatingChain_nonSep_iff hB (hX x hx) (hX y hy)] at hch
  rcases hch with ⟨b, _, hby⟩
  exact hnoR y hy b hby

/-- Closed-left-region criterion: if `S` contains `X`, is closed under `GadgetSameRight φ B`, and
no
`u ∈ S` has a `GadgetBlockPair φ B u y` into `y ∈ X`, then `X` is a free set. -/
theorem isFreeSet_of_closed_left_region {φ : CNF ℕ} {B X S : Set ClauseGadgetLetter}
    (hB : ∀ z, ClauseGadgetLetter.sep z ∉ B) (hX : ∀ x ∈ X, x.isSep = false)
    (hsub : X ⊆ S)
    (hclosed : ∀ u ∈ S, ∀ c v, GadgetBlockPair φ B u c → GadgetBlockPair φ B v c → v ∈ S)
    (hdisj : ∀ u ∈ S, ∀ y ∈ X, ¬ GadgetBlockPair φ B u y) :
    IsFreeSet (deleteLetters B (clauseGadgetPattern φ)) X := by
  rw [isFreeSet_iff]
  intro x hx y hy hch
  rw [gadget_hasAlternatingChain_nonSep_iff hB (hX x hx) (hX y hy)] at hch
  rcases hch with ⟨b, hpath, hby⟩
  have hbS : b ∈ S := by
    clear hby
    induction hpath with
    | refl => exact hsub hx
    | @tail u₁ u₂ _ hsr ih =>
      rcases hsr with ⟨c, h₁, h₂⟩
      exact hclosed u₁ ih c u₂ h₁ h₂
  exact hdisj b hbS y hy hby

end SeparatorInvisibility

end CslibFrontier.Complexity

end
