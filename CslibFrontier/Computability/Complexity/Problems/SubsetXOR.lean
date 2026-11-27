/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Computability.Complexity.Problems.XORSAT.Dense
public import Mathlib.Data.List.Sublists
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Tactic.FunProp

/-!
# Subset Bitwise XOR (`SubsetXOR`)

`SubsetXOR` is the decision problem asking whether a given collection of equal-width Boolean vectors
`x.vectors : List (List Bool)` admits a subcollection whose componentwise XOR equals `x.target`.
Unlike `SubsetSum` over `ℕ` (which is `NP`-complete under binary encoding), `SubsetXOR` is linear
span membership over `GF(2)` and belongs to `Cslib.Complexity.P` via polynomial-time compilation to
dense Boolean Gaussian elimination (`Cslib.Complexity.XORSAT.Dense`).

## Main definitions

* `CslibFrontier.Computability.Complexity.SubsetXORInstance`,
  `CslibFrontier.Computability.Complexity.encSubsetXOR`: problem instances and framed binary
  encoding.
* `CslibFrontier.Computability.Complexity.SubsetXOR`: well-formed instances admitting a sublist
  whose bitwise XOR equals `target`.
* `CslibFrontier.Computability.Complexity.toDenseXORSAT`,
  `CslibFrontier.Computability.Complexity.decideSubsetXOR`: compilation to dense `GF(2)` Gaussian
  elimination and deterministic polynomial-time decider.

## Main results

* `CslibFrontier.Computability.Complexity.decideSubsetXOR_eq_true_iff`: correctness of
  `decideSubsetXOR`.
* `CslibFrontier.Computability.Complexity.computableInPolyTime_decideSubsetXOR`: polynomial-time
  certificate on multi-tape Turing machines.
* `CslibFrontier.Computability.Complexity.SubsetXOR_mem_P`,
  `CslibFrontier.Computability.Complexity.SubsetXOR_mem_NP`,
  `CslibFrontier.Computability.Complexity.SubsetXOR_mem_coNP`: membership in `P`, `NP`, and `coNP`.
* `CslibFrontier.Computability.Complexity.polyTimeReducible_SubsetXOR_SAT`: polynomial-time
  many-one reduction to `SAT`.
* `CslibFrontier.Computability.Complexity.SubsetXOR_npComplete_iff`: `SubsetXOR` is `NP`-complete
  iff `P = NP`.
-/

public section

namespace CslibFrontier.Computability.Complexity

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime
open scoped List Cslib.Complexity.XORSAT.Dense

/-- Componentwise Boolean XOR of two bit lists. -/
@[expose] def xorBits (u v : List Bool) : List Bool :=
  List.zipWith Bool.xor u v

/-- Iterated componentwise XOR of a list of `k`-bit vectors. -/
@[expose] def xorFoldBits (k : ℕ) (vs : List (List Bool)) : List Bool :=
  vs.foldl xorBits (List.replicate k false)

/-- An instance of Subset Bitwise XOR: candidate binary vectors and a target binary vector. -/
@[ext]
structure SubsetXORInstance where
  /-- Candidate binary vectors. -/
  vectors : List (List Bool)
  /-- Target binary vector. -/
  target : List Bool
  deriving DecidableEq, Repr

/-- Framed list of raw binary vectors paired with the raw target binary vector. -/
enc_structure encSubsetXOR : SubsetXORInstance where
  vectors : (encList encBits), target : encBits

/-- Every candidate vector has the same bit-width as `target`. -/
@[expose] def SubsetXORInstance.WellFormed (x : SubsetXORInstance) : Prop :=
  ∀ v ∈ x.vectors, v.length = x.target.length

/-- The Subset Bitwise XOR language: well-formed instances admitting a sublist whose componentwise
XOR equals `x.target`. -/
@[expose] def SubsetXOR : Set SubsetXORInstance :=
  {x | x.WellFormed ∧ ∃ s : List (List Bool), s <+ x.vectors ∧
    xorFoldBits x.target.length s = x.target}

private theorem getD_xorBits :
    ∀ (u v : List Bool) (j : ℕ), j < u.length → j < v.length →
      (xorBits u v).getD j false = Bool.xor (u.getD j false) (v.getD j false)
  | [], _, _, hu, _ => by simp at hu
  | _ :: _, [], _, _, hv => by simp at hv
  | _ :: _, _ :: _, 0, _, _ => rfl
  | _ :: us, _ :: vs, j + 1, hu, hv =>
    getD_xorBits us vs j (Nat.lt_of_succ_lt_succ hu) (Nat.lt_of_succ_lt_succ hv)

private theorem getD_replicate_false : ∀ (k j : ℕ), (List.replicate k false).getD j false = false
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | k + 1, j + 1 => getD_replicate_false k j

private theorem foldl_xor_init (bs : List Bool) (init : Bool) :
    bs.foldl Bool.xor init = Bool.xor init (bs.foldl Bool.xor false) := by
  induction bs generalizing init with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [ih (Bool.xor init b), ih b, Bool.xor_assoc]

private theorem length_foldl_xorBits {k : ℕ} :
    ∀ (vs : List (List Bool)) (acc : List Bool),
      acc.length = k → (∀ v ∈ vs, v.length = k) → (vs.foldl xorBits acc).length = k
  | [], acc, hacc, _ => hacc
  | v :: vs, acc, hacc, hv => by
    have hv0 : v.length = k := hv v List.mem_cons_self
    have hacc' : (xorBits acc v).length = k := by
      simp [xorBits, hacc, hv0]
    exact length_foldl_xorBits vs (xorBits acc v) hacc'
      (fun w hw => hv w (List.mem_cons_of_mem v hw))

private theorem getD_foldl_xorBits {k j : ℕ} (hj : j < k) :
    ∀ (vs : List (List Bool)) (acc : List Bool),
      acc.length = k → (∀ v ∈ vs, v.length = k) →
      (vs.foldl xorBits acc).getD j false =
        Bool.xor (acc.getD j false) ((vs.map fun v => v.getD j false).foldl Bool.xor false)
  | [], _, _, _ => by simp
  | v :: vs, acc, hacc, hv => by
    have hv0 : v.length = k := hv v List.mem_cons_self
    have hacc' : (xorBits acc v).length = k := by simp [xorBits, hacc, hv0]
    simp only [List.foldl_cons, List.map_cons]
    rw [getD_foldl_xorBits hj vs (xorBits acc v) hacc'
      (fun w hw => hv w (List.mem_cons_of_mem v hw)),
      getD_xorBits acc v j (hacc ▸ hj) (hv0 ▸ hj),
      Bool.false_xor, foldl_xor_init _ (v.getD j false), Bool.xor_assoc]

private theorem list_eq_of_length_eq_of_getD_eq :
    ∀ (u v : List Bool), u.length = v.length →
      (∀ j < v.length, u.getD j false = v.getD j false) → u = v
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: us, b :: vs, hlen, hget => by
    have h0 : a = b := hget 0 (Nat.zero_lt_succ _)
    have htail : us = vs := list_eq_of_length_eq_of_getD_eq us vs (Nat.succ.inj hlen)
      (fun j hj => hget (j + 1) (Nat.succ_lt_succ hj))
    rw [h0, htail]

private theorem maskSelect_nil_right :
    ∀ (l : List (List Bool)), maskSelect l [] = []
  | [] => maskSelect_nil []
  | _ :: l => by
    rw [maskSelect_cons]
    simpa using maskSelect_nil_right l

private theorem foldl_xor_maskSelect_eq_dot (j : ℕ) :
    ∀ (vs : List (List Bool)) (w : List Bool),
      ((maskSelect vs w).map fun v => v.getD j false).foldl Bool.xor false =
        XORSAT.Dense.dot (vs.map fun v => v.getD j false) w
  | [], _ => by simp [maskSelect_nil, XORSAT.Dense.dot]
  | _ :: _, [] => by rw [maskSelect_nil_right]; rfl
  | v :: vs, b :: ws => by
    rw [maskSelect_cons]
    cases b
    · simpa [XORSAT.Dense.dot, ← Bool.zero_eq_false] using foldl_xor_maskSelect_eq_dot j vs ws
    · simp only [List.headD_cons, ↓reduceIte, List.singleton_append, List.map_cons,
        List.foldl_cons, Bool.false_xor, List.tail_cons, XORSAT.Dense.dot]
      rw [foldl_xor_init, foldl_xor_maskSelect_eq_dot j vs ws]
      cases v.getD j false <;>
        cases XORSAT.Dense.dot (List.map (fun v => v.getD j false) vs) ws <;> rfl

private theorem exists_sublist_iff_exists_maskSelect {α : Type*} (vs : List α)
    (P : List α → Prop) :
    (∃ s : List α, s <+ vs ∧ P s) ↔
      ∃ w : List Bool, w.length = vs.length ∧ P (maskSelect vs w) := by
  constructor
  · rintro ⟨s, hsub, hP⟩
    have hex : ∃ w : List Bool, w.length = vs.length ∧ maskSelect vs w = s := by
      clear hP
      induction hsub with
      | slnil => exact ⟨[], rfl, maskSelect_nil []⟩
      | cons _ _ ih =>
        obtain ⟨w, hlen, hws⟩ := ih
        exact ⟨false :: w, by simp [hlen], by simpa [maskSelect_cons] using hws⟩
      | cons_cons _ _ ih =>
        obtain ⟨w, hlen, hws⟩ := ih
        exact ⟨true :: w, by simp [hlen], by simpa [maskSelect_cons] using hws⟩
    obtain ⟨w, hlen, rfl⟩ := hex
    exact ⟨w, hlen, hP⟩
  · rintro ⟨w, _, hP⟩
    exact ⟨maskSelect vs w, maskSelect_sublist vs w, hP⟩

/-- Compile `SubsetXORInstance` to a dense parity linear system `A^T s = t` over `GF(2)`. -/
@[expose] def toDenseXORSAT (x : SubsetXORInstance) : XORSAT.Dense.Input :=
  ⟨x.vectors.length,
    (List.range x.target.length).map fun j =>
      ⟨x.vectors.map (fun v => v.getD j false), x.target.getD j false⟩⟩

/-- Deterministic Boolean decider for `SubsetXOR`. -/
@[expose] def decideSubsetXOR (x : SubsetXORInstance) : Bool :=
  x.vectors.all (fun v => decide (v.length = x.target.length)) &&
    XORSAT.Dense.decide (toDenseXORSAT x)

/-- `decideSubsetXOR` decides `SubsetXOR`. -/
theorem decideSubsetXOR_eq_true_iff (x : SubsetXORInstance) :
    decideSubsetXOR x = true ↔ x ∈ SubsetXOR := by
  simp only [decideSubsetXOR, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    XORSAT.Dense.decide_eq_true_iff, SubsetXOR, SubsetXORInstance.WellFormed, Set.mem_ofPred_eq]
  refine and_congr_right fun hwf => ?_
  have hwidth : XORSAT.Dense.Width x.vectors.length
      ((List.range x.target.length).map fun j =>
        (⟨x.vectors.map (fun v => v.getD j false), x.target.getD j false⟩ :
          XORSAT.Dense.Row)) := by
    intro e he
    simp only [List.mem_map, List.mem_range] at he
    obtain ⟨_, _, rfl⟩ := he
    simp
  simp only [XORSAT.Dense.Satisfiable, toDenseXORSAT, hwidth, true_and, XORSAT.Dense.Holds,
    List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rw [exists_sublist_iff_exists_maskSelect]
  refine exists_congr fun w => and_congr_right fun _ => ?_
  have hsub_wf : ∀ v ∈ maskSelect x.vectors w, v.length = x.target.length :=
    fun v hv => hwf v ((maskSelect_sublist x.vectors w).subset hv)
  constructor
  · intro hrows
    apply list_eq_of_length_eq_of_getD_eq
    · exact length_foldl_xorBits _ _ List.length_replicate hsub_wf
    · intro j hj
      rw [xorFoldBits, getD_foldl_xorBits hj _ _ List.length_replicate hsub_wf,
        getD_replicate_false, Bool.false_xor, foldl_xor_maskSelect_eq_dot]
      exact hrows j hj
  · intro hxor j hj
    rw [← foldl_xor_maskSelect_eq_dot,
      ← show (xorFoldBits x.target.length (maskSelect x.vectors w)).getD j false =
          ((maskSelect x.vectors w).map fun v => v.getD j false).foldl Bool.xor false by
        rw [xorFoldBits, getD_foldl_xorBits hj _ _ List.length_replicate hsub_wf,
          getD_replicate_false, Bool.false_xor],
      hxor]

/-- `toDenseXORSAT` is computable in polynomial time on a multi-tape Turing machine. -/
theorem computableInPolyTime_toDenseXORSAT :
    ComputableInPolyTime toDenseXORSAT encSubsetXOR XORSAT.Dense.encInput := by
  have hcoeffs_list : ComputableInPolyTime
      (fun p : SubsetXORInstance × ℕ => p.1.vectors.map fun v => v.getD p.2 false)
      (encPair encSubsetXOR encUnary) (encList encBool) := by
    fun_prop
  have hcoeffs : ComputableInPolyTime
      (fun p : SubsetXORInstance × ℕ => p.1.vectors.map fun v => v.getD p.2 false)
      (encPair encSubsetXOR encUnary) encBits :=
    (bits_encList_polyTime encBool).2.comp hcoeffs_list
  have hrow : ComputableInPolyTime
      (fun p : SubsetXORInstance × ℕ =>
        (⟨p.1.vectors.map (fun v => v.getD p.2 false), p.1.target.getD p.2 false⟩ :
          XORSAT.Dense.Row))
      (encPair encSubsetXOR encUnary) XORSAT.Dense.encRow :=
    XORSAT.Dense.encRow_mk_polyTime hcoeffs (by fun_prop)
  have hrows : ComputableInPolyTime
      (fun x : SubsetXORInstance =>
        (List.range x.target.length).map fun j =>
          (⟨x.vectors.map (fun v => v.getD j false), x.target.getD j false⟩ : XORSAT.Dense.Row))
      encSubsetXOR XORSAT.Dense.encSystem :=
    mapWithInput (by fun_prop) hrow
  exact XORSAT.Dense.encInput_mk_polyTime (by fun_prop) hrows

/-- `decideSubsetXOR` is computable in polynomial time on a multi-tape Turing machine. -/
theorem computableInPolyTime_decideSubsetXOR :
    ComputableInPolyTime decideSubsetXOR encSubsetXOR encBool := by
  have hwf_check : ComputableInPolyTime
      (fun x : SubsetXORInstance => x.vectors.all fun v => v.length == x.target.length)
      encSubsetXOR encBool := by
    fun_prop
  have heq : decideSubsetXOR =
      fun x : SubsetXORInstance =>
        (x.vectors.all fun v => v.length == x.target.length) &&
          XORSAT.Dense.decide (toDenseXORSAT x) := by
    funext x
    simp [decideSubsetXOR, beq_eq_decide]
  rw [heq]
  exact hwf_check.bool_and'
    (XORSAT.Dense.computableInPolyTime_decide.comp computableInPolyTime_toDenseXORSAT)

/-- `SubsetXOR` belongs to `P`. -/
theorem SubsetXOR_mem_P : SubsetXOR ∈ P encSubsetXOR :=
  ⟨decideSubsetXOR, computableInPolyTime_decideSubsetXOR,
    fun x => (decideSubsetXOR_eq_true_iff x).symm⟩

/-- `SubsetXOR` belongs to `NP`. -/
theorem SubsetXOR_mem_NP : SubsetXOR ∈ NP encSubsetXOR :=
  P_subset_NP SubsetXOR_mem_P

/-- `SubsetXOR` belongs to `coNP`. -/
theorem SubsetXOR_mem_coNP : SubsetXOR ∈ coNP encSubsetXOR :=
  P_subset_coNP SubsetXOR_mem_P

/-- `SubsetXOR` reduces in polynomial time to `SAT`. -/
theorem polyTimeReducible_SubsetXOR_SAT :
    PolyTimeReducible encSubsetXOR encCNF SubsetXOR SAT := by
  refine ⟨fun x => if decideSubsetXOR x then ([] : Cslib.Logic.PL.CNF ℕ) else [[]],
    computableInPolyTime_decideSubsetXOR.ite
      (const (encOut := encCNF) []) (const (encOut := encCNF) [[]]),
    fun x => ?_⟩
  by_cases h : decideSubsetXOR x = true
  · simp only [h, ↓reduceIte, ← decideSubsetXOR_eq_true_iff x, SAT, Set.mem_ofPred_eq]
    exact ⟨fun _ => ⟨fun _ => false, rfl⟩, fun _ => trivial⟩
  · have hf : decideSubsetXOR x = false := Bool.eq_false_iff.mpr h
    simp only [hf, Bool.false_eq_true, ↓reduceIte, ← decideSubsetXOR_eq_true_iff x, SAT,
      Set.mem_ofPred_eq]
    exact ⟨False.elim, fun ⟨_, hσ⟩ => Bool.noConfusion hσ⟩

/-- `SubsetXOR` is `NP`-complete if and only if `P = NP`. -/
theorem SubsetXOR_npComplete_iff :
    NPComplete encSubsetXOR SubsetXOR ↔
      ∀ {α : Type} (enc : α ↪ List Bool), P enc = NP enc := by
  constructor
  · intro hnpc
    exact hnpc.mem_P_iff.mp SubsetXOR_mem_P
  · intro hPeqNP
    refine ⟨SubsetXOR_mem_NP, fun {α} enc A hA => ?_⟩
    have hAP : A ∈ P enc := by rwa [hPeqNP enc]
    obtain ⟨f, hf, hfA⟩ := hAP
    let yesInst : SubsetXORInstance := ⟨[[true]], [true]⟩
    let noInst : SubsetXORInstance := ⟨[[false]], [true]⟩
    have hyes : yesInst ∈ SubsetXOR :=
      ⟨by simp [yesInst, SubsetXORInstance.WellFormed], [[true]], List.Sublist.refl _, rfl⟩
    have hno : noInst ∉ SubsetXOR := by
      rw [← decideSubsetXOR_eq_true_iff]
      decide
    refine ⟨fun a => if f a then yesInst else noInst,
      hf.ite (const yesInst) (const noInst), fun a => ?_⟩
    rw [hfA a]
    cases hfa : f a
    · simp [hfa, hno]
    · simp [hfa, hyes]

end CslibFrontier.Computability.Complexity
