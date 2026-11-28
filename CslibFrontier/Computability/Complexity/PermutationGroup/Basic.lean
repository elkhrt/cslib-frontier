/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.Basic

import Mathlib.Tactic.Linarith

/-!
# Polynomial-Time Permutation-Table Operations on Multi-Tape Turing Machines

Canonical binary-list (`encList encNat`) encoding of finite permutations `Equiv.Perm (Fin N)` as
value tables `[σ(0), σ(1), ..., σ(N - 1)]`, together with deterministic polynomial-time
(`Turing.MultiTapeTM.ComputableInPolyTime`) algorithms for list slicing, identity tables,
permutation composition, inverse-multiplication, inversion, and permutation-table validity
verification.

## Main definitions

* `CslibFrontier.PermutationGroup.encNatList`: framed list of binary naturals `encList encNat`.
* `CslibFrontier.PermutationGroup.permToNatList`: table `[σ(0), ..., σ(N - 1)]` of
  `σ : Equiv.Perm (Fin N)`.
* `CslibFrontier.PermutationGroup.natListToPerm`: total decoder
  `List ℕ → Option (Equiv.Perm (Fin N))`.
* `CslibFrontier.PermutationGroup.natListSlice`: length-`N` slice extraction from flattened lists.
* `CslibFrontier.PermutationGroup.permIdTable`, `permMulTable`, `permInvMulTable`, `permInvTable`:
  table-level permutation group operations on `List ℕ`.
* `CslibFrontier.PermutationGroup.isValidPermTable`: Boolean decider checking whether the first `N`
  entries form a bijection on `Fin N`.

## Main results

* `CslibFrontier.PermutationGroup.natListToPerm_permToNatList`: round-trip decoding identity.
* `CslibFrontier.PermutationGroup.computableInPolyTime_natListSlice`,
  `computableInPolyTime_permIdTable`, `computableInPolyTime_permMulTable`,
  `computableInPolyTime_permInvMulTable`, `computableInPolyTime_permInvTable`,
  `computableInPolyTime_isValidPermTable`: `Turing.MultiTapeTM.ComputableInPolyTime` witnesses.
-/

public section

namespace CslibFrontier.PermutationGroup

open Turing.MultiTapeTM

/-- Framed list of little-endian binary natural numbers (`encList encNat`), used as the canonical
binary encoding of permutation tables and flattened generator lists on `MultiTapeTM`. -/
abbrev encNatList : List ℕ ↪ List Bool := encList encNat

private def PolyTimeOn {α β : Type} (ea : α ↪ List Bool) (eb : β ↪ List Bool)
    (f : α → β) : Prop :=
  ComputableInPolyTime f ea eb

private lemma PolyTimeOn.comp {α β γ : Type} {ea : α ↪ List Bool} {eb : β ↪ List Bool}
    {ec : γ ↪ List Bool} {f : α → β} {g : β → γ}
    (hf : PolyTimeOn ea eb f) (hg : PolyTimeOn eb ec g) :
    PolyTimeOn ea ec (fun x ↦ g (f x)) :=
  ComputableInPolyTime.comp hg hf

private lemma PolyTimeOn.pair {α β γ : Type} {ea : α ↪ List Bool} {eb : β ↪ List Bool}
    {ec : γ ↪ List Bool} {f : α → β} {g : α → γ}
    (hf : PolyTimeOn ea eb f) (hg : PolyTimeOn ea ec g) :
    PolyTimeOn ea (encPair eb ec) (fun x ↦ (f x, g x)) :=
  ComputableInPolyTime.prod hf hg

private lemma PolyTimeOn.of_eq {α β : Type} {ea : α ↪ List Bool} {eb : β ↪ List Bool}
    {f g : α → β} (hf : PolyTimeOn ea eb f) (heq : ∀ x, f x = g x) :
    PolyTimeOn ea eb g :=
  ComputableInPolyTime.of_enc_eq hf fun x ↦ by rw [heq x]

private lemma PolyTimeOn.not {α : Type} {ea : α ↪ List Bool} {p : α → Bool}
    (hp : PolyTimeOn ea encBool p) :
    PolyTimeOn ea encBool (fun x ↦ !(p x)) :=
  ComputableInPolyTime.bool_not.comp hp

private lemma PolyTimeOn.and {α : Type} {ea : α ↪ List Bool} {p q : α → Bool}
    (hp : PolyTimeOn ea encBool p) (hq : PolyTimeOn ea encBool q) :
    PolyTimeOn ea encBool (fun x ↦ p x && q x) :=
  ComputableInPolyTime.bool_and' hp hq

private lemma PolyTimeOn.count_lt {α : Type} {ea : α ↪ List Bool}
    {bound : α → ℕ} {P : α × ℕ → Bool}
    (hbound : PolyTimeOn ea encUnary bound)
    (hP : PolyTimeOn (encPair ea encUnary) encBool P) :
    PolyTimeOn ea encUnary
      (fun x ↦ ((List.range (bound x)).filter fun i ↦ P (x, i)).length) :=
  (ComputableInPolyTime.countPWith hP ComputableInPolyTime.id'
    (ComputableInPolyTime.range.comp hbound)).of_enc_eq fun _ ↦ by
      simp only [Function.comp, List.countP_eq_length_filter]

private lemma PolyTimeOn.exists_lt {α : Type} {ea : α ↪ List Bool}
    {bound : α → ℕ} {P : α × ℕ → Bool}
    (hbound : PolyTimeOn ea encUnary bound)
    (hP : PolyTimeOn (encPair ea encUnary) encBool P) :
    PolyTimeOn ea encBool (fun x ↦ (List.range (bound x)).any fun i ↦ P (x, i)) :=
  ComputableInPolyTime.anyWith hP ComputableInPolyTime.id'
    (ComputableInPolyTime.range.comp hbound)

private lemma PolyTimeOn.forall_lt {α : Type} {ea : α ↪ List Bool}
    {bound : α → ℕ} {P : α × ℕ → Bool}
    (hbound : PolyTimeOn ea encUnary bound)
    (hP : PolyTimeOn (encPair ea encUnary) encBool P) :
    PolyTimeOn ea encBool (fun x ↦ (List.range (bound x)).all fun i ↦ P (x, i)) :=
  ComputableInPolyTime.allWith hP ComputableInPolyTime.id'
    (ComputableInPolyTime.range.comp hbound)

private abbrev FP := @PolyTimeOn
private abbrev eB := encNat
private abbrev eL := encNatList
private abbrev eU := encUnary
private abbrev eP := @encPair

private lemma fpId {α : Type} (ea : α ↪ List Bool) : PolyTimeOn ea ea id :=
  ComputableInPolyTime.id'

private lemma fpFst {α β : Type} (ea : α ↪ List Bool) (eb : β ↪ List Bool) :
    PolyTimeOn (encPair ea eb) ea Prod.fst :=
  ComputableInPolyTime.fst ea eb

private lemma fpSnd {α β : Type} (ea : α ↪ List Bool) (eb : β ↪ List Bool) :
    PolyTimeOn (encPair ea eb) eb Prod.snd :=
  ComputableInPolyTime.snd ea eb

private lemma fpSuccU : PolyTimeOn encUnary encUnary (· + 1) :=
  ComputableInPolyTime.unary_add.comp
    (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const 1))

private lemma fpAddU : PolyTimeOn (encPair encUnary encUnary) encUnary (fun p ↦ p.1 + p.2) :=
  ComputableInPolyTime.unary_add

private lemma fpToBin : PolyTimeOn encUnary encNat id :=
  ComputableInPolyTime.unary_to_binary

private lemma fpEqBin :
    PolyTimeOn (encPair encNat encNat) encBool (fun p ↦ decide (p.1 = p.2)) :=
  ComputableInPolyTime.decide_eq'
    (ComputableInPolyTime.fst encNat encNat) (ComputableInPolyTime.snd encNat encNat)

private lemma fpLtBin :
    PolyTimeOn (encPair encNat encNat) encBool (fun p ↦ decide (p.1 < p.2)) :=
  ComputableInPolyTime.binary_lt'
    (ComputableInPolyTime.fst encNat encNat) (ComputableInPolyTime.snd encNat encNat)

private lemma fpMinBinU :
    PolyTimeOn (encPair encNat encUnary) encUnary (fun p ↦ min p.1 p.2) :=
  (ComputableInPolyTime.binary_min_unary'
    (ComputableInPolyTime.snd encNat encUnary)
    (ComputableInPolyTime.fst encNat encUnary)).of_enc_eq fun p ↦ by rw [min_comm]

private lemma fpGetDList :
    PolyTimeOn (encPair encNatList encUnary) encNat (fun p ↦ p.1.getD p.2 0) :=
  ComputableInPolyTime.listGetDWithInput
    (ComputableInPolyTime.fst encNatList encUnary)
    (ComputableInPolyTime.snd encNatList encUnary) 0

private lemma fpBuild {α : Type} {ea : α ↪ List Bool} {len : α → ℕ} {elem : α × ℕ → ℕ}
    (hlen : PolyTimeOn ea encUnary len)
    (helem : PolyTimeOn (encPair ea encUnary) encNat elem) :
    PolyTimeOn ea encNatList (fun x ↦ (List.range (len x)).map fun i ↦ elem (x, i)) :=
  ComputableInPolyTime.mapWith helem ComputableInPolyTime.id'
    (ComputableInPolyTime.range.comp hlen)

private lemma fp_add {α : Type} {ea : α ↪ List Bool} {f g : α → ℕ}
    (hf : FP ea eU f) (hg : FP ea eU g) : FP ea eU (fun x ↦ f x + g x) :=
  (hf.pair hg).comp fpAddU

private lemma fp_getD {α : Type} {ea : α ↪ List Bool} {xs : α → List ℕ} {f : α → ℕ}
    (hxs : FP ea eL xs) (hf : FP ea eU f) :
    FP ea eB (fun x ↦ (xs x).getD (f x) 0) :=
  (hxs.pair hf).comp fpGetDList

private lemma fp_eqB {α : Type} {ea : α ↪ List Bool} {f g : α → ℕ}
    (hf : FP ea eB f) (hg : FP ea eB g) :
    FP ea encBool (fun x ↦ decide (f x = g x)) :=
  (hf.pair hg).comp fpEqBin

private lemma fp_min {α : Type} {ea : α ↪ List Bool} {f g : α → ℕ}
    (hf : FP ea eB f) (hg : FP ea eU g) : FP ea eU (fun x ↦ min (f x) (g x)) :=
  (hf.pair hg).comp fpMinBinU

private lemma fp_toBin {α : Type} {ea : α ↪ List Bool} {f : α → ℕ}
    (hf : FP ea eU f) : FP ea eB f :=
  hf.comp fpToBin

private lemma length_filter_range_lt (bound k : ℕ) :
    ((List.range bound).filter fun i ↦ decide (i < k)).length = min bound k := by
  induction bound with
  | zero => simp
  | succ b ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : b < k <;> simp [h] <;> omega

/-- Smallest index `k < bound` satisfying `P k = true`, or `bound` if none exists. -/
def firstIdx (bound : ℕ) (P : ℕ → Bool) : ℕ :=
  ((List.range bound).filter fun i ↦ !(List.range (i + 1)).any P).length

private lemma firstIdx_eq_of_min {bound k : ℕ} {P : ℕ → Bool}
    (hk : k < bound) (hPk : P k = true) (hprev : ∀ j < k, P j = false) :
    firstIdx bound P = k := by
  unfold firstIdx
  rw [List.filter_congr (q := fun i ↦ decide (i < k)) fun i _ ↦ by
    by_cases hik : i < k
    · have h0 : (List.range (i + 1)).any P = false := List.any_eq_false.mpr fun j hj ↦ by
        rw [hprev j (by have := List.mem_range.mp hj; omega)]; simp
      simp [hik, h0]
    · have h1 : (List.range (i + 1)).any P = true :=
        List.any_eq_true.mpr ⟨k, List.mem_range.mpr (by omega), hPk⟩
      simp [hik, h1]]
  rw [length_filter_range_lt]; omega

private lemma computableInPolyTime_firstIdx {α : Type} {ea : α ↪ List Bool}
    {bound : α → ℕ} {P : α × ℕ → Bool}
    (hbound : PolyTimeOn ea encUnary bound)
    (hP : PolyTimeOn (encPair ea encUnary) encBool P) :
    PolyTimeOn ea encUnary (fun x ↦ firstIdx (bound x) (fun i ↦ P (x, i))) :=
  hbound.count_lt (((fpSnd ea eU).comp fpSuccU).exists_lt
    ((((fpFst (eP ea eU) eU).comp (fpFst ea eU)).pair (fpSnd (eP ea eU) eU)).comp hP)).not

/-- Encode a permutation `σ : Equiv.Perm (Fin N)` as its value table `[σ(0), ..., σ(N - 1)]`. -/
def permToNatList {N : ℕ} (σ : Equiv.Perm (Fin N)) : List ℕ :=
  List.ofFn fun i : Fin N ↦ (σ i).val

/-- Length of `permToNatList σ` equals `N`. -/
lemma permToNatList_length {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (permToNatList σ).length = N := by
  simp [permToNatList]

/-- Lookup at index `i < N` in `permToNatList σ`. -/
lemma permToNatList_getD {N : ℕ} (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    (permToNatList σ).getD i.val 0 = (σ i).val := by
  simp [permToNatList, List.getD_eq_getElem?_getD, i.isLt]

private lemma permToNatList_getElem {N : ℕ} (σ : Equiv.Perm (Fin N)) (i : ℕ)
    (hi : i < (permToNatList σ).length) :
    (permToNatList σ)[i] = (σ ⟨i, by rwa [permToNatList_length] at hi⟩).val := by
  simp [permToNatList]

/-- `permToNatList` is injective on `Equiv.Perm (Fin N)`. -/
lemma permToNatList_injective {N : ℕ} : Function.Injective (permToNatList (N := N)) :=
  fun σ τ h ↦ Equiv.ext fun i ↦ Fin.ext (by
    have h1 := congrArg (fun l : List ℕ ↦ l.getD i.val 0) h
    rwa [permToNatList_getD, permToNatList_getD] at h1)

/-- Decode a length-`N` natural-number table as a permutation of `Fin N`, or `none` if invalid. -/
noncomputable def natListToPerm (N : ℕ) (xs : List ℕ) : Option (Equiv.Perm (Fin N)) := by
  classical
  exact if h : ∃ σ : Equiv.Perm (Fin N), permToNatList σ = xs then some h.choose else none

/-- Round-trip decoding of `permToNatList σ`. -/
lemma natListToPerm_permToNatList {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    natListToPerm N (permToNatList σ) = some σ := by
  classical
  have hex : ∃ τ : Equiv.Perm (Fin N), permToNatList τ = permToNatList σ := ⟨σ, rfl⟩
  unfold natListToPerm; simp only [hex, ↓reduceDIte]
  exact congrArg some (permToNatList_injective hex.choose_spec)

private lemma permToNatList_of_natListToPerm_eq_some {N : ℕ} {xs : List ℕ}
    {σ : Equiv.Perm (Fin N)} (h : natListToPerm N xs = some σ) : permToNatList σ = xs := by
  classical
  unfold natListToPerm at h
  by_cases hex : ∃ τ : Equiv.Perm (Fin N), permToNatList τ = xs
  · simp only [hex, ↓reduceDIte, Option.some.injEq] at h; exact h ▸ hex.choose_spec
  · simp only [hex, ↓reduceDIte, reduceCtorEq] at h

/-- `natListToPerm N xs` yields `some σ` if and only if `permToNatList σ = xs`. -/
lemma natListToPerm_eq_some_iff {N : ℕ} {xs : List ℕ} {σ : Equiv.Perm (Fin N)} :
    natListToPerm N xs = some σ ↔ permToNatList σ = xs :=
  ⟨permToNatList_of_natListToPerm_eq_some, fun h ↦ h ▸ natListToPerm_permToNatList σ⟩

/-- Extract a length-`N` slice starting at `offset` from a flattened `List ℕ`. -/
def natListSlice (xs : List ℕ) (offset N : ℕ) : List ℕ :=
  (List.range N).map fun i ↦ xs.getD (offset + i) 0

/-- Length of `natListSlice xs offset N` equals `N`. -/
lemma natListSlice_length (xs : List ℕ) (offset N : ℕ) :
    (natListSlice xs offset N).length = N := by
  simp [natListSlice]

/-- Lookup at `i < N` in `natListSlice xs offset N` accesses `offset + i` in `xs`. -/
lemma natListSlice_getD (xs : List ℕ) (offset N i : ℕ) (hi : i < N) :
    (natListSlice xs offset N).getD i 0 = xs.getD (offset + i) 0 := by
  simp [natListSlice, List.getD_eq_getElem?_getD, hi]

/-- Slicing a framed binary natural-number list runs in deterministic polynomial time. -/
theorem computableInPolyTime_natListSlice :
    ComputableInPolyTime (fun p : (List ℕ × ℕ) × ℕ ↦ natListSlice p.1.1 p.1.2 p.2)
      (encPair (encPair encNatList encUnary) encUnary) encNatList :=
  fpBuild (fpSnd _ _) (fp_getD ((fpFst _ _).comp ((fpFst _ _).comp (fpFst _ _)))
    (fp_add ((fpFst _ _).comp ((fpFst _ _).comp (fpSnd _ _))) (fpSnd _ _)))

/-- Identity permutation table `[0, 1, ..., N - 1]`. -/
def permIdTable (N : ℕ) : List ℕ := List.range N

/-- `permIdTable N` encodes the identity permutation `(1 : Equiv.Perm (Fin N))`. -/
lemma permIdTable_eq (N : ℕ) : permIdTable N = permToNatList (1 : Equiv.Perm (Fin N)) :=
  List.ext_getElem (by simp [permIdTable, permToNatList]) fun _ _ _ ↦ by
    simp [permIdTable, permToNatList]

/-- `permIdTable` is computable in deterministic polynomial time from unary `N`. -/
theorem computableInPolyTime_permIdTable :
    ComputableInPolyTime permIdTable encUnary encNatList :=
  ((fpBuild (fpId eU) (fp_toBin (fpSnd eU eU))) :
    FP eU eL (fun N ↦ (List.range N).map fun i ↦ i)).of_eq fun N ↦ by simp [permIdTable]

/-- Composition of two length-`N` permutation tables `(xs ∘ ys)(i) = xs(ys(i))`. -/
def permMulTable (N : ℕ) (xs ys : List ℕ) : List ℕ :=
  (List.range N).map fun i ↦ xs.getD (min (ys.getD i 0) N) 0

/-- `permMulTable N` computes the value table of `σ * τ`. -/
lemma permMulTable_eq {N : ℕ} (σ τ : Equiv.Perm (Fin N)) :
    permMulTable N (permToNatList σ) (permToNatList τ) = permToNatList (σ * τ) :=
  List.ext_getElem (by simp [permMulTable, permToNatList]) fun i hi _ ↦ by
    have hiN : i < N := by simpa [permMulTable] using hi
    simp only [permMulTable, List.getElem_map, List.getElem_range]
    rw [permToNatList_getD τ ⟨i, hiN⟩, Nat.min_eq_left (Nat.le_of_lt (τ ⟨i, hiN⟩).isLt),
      permToNatList_getD σ (τ ⟨i, hiN⟩)]
    simp [permToNatList]

/-- Combined `σ⁻¹ * τ` on length-`N` permutation tables. -/
def permInvMulTable (N : ℕ) (xs ys : List ℕ) : List ℕ :=
  (List.range N).map fun i ↦ firstIdx N fun x ↦ decide (xs.getD x 0 = ys.getD i 0)

/-- `permInvMulTable N` computes the value table of `σ⁻¹ * τ`. -/
lemma permInvMulTable_eq {N : ℕ} (σ τ : Equiv.Perm (Fin N)) :
    permInvMulTable N (permToNatList σ) (permToNatList τ) = permToNatList (σ⁻¹ * τ) :=
  List.ext_getElem (by simp [permInvMulTable, permToNatList]) fun i hi _ ↦ by
    have hiN : i < N := by simpa [permInvMulTable] using hi
    simp only [permInvMulTable, List.getElem_map, List.getElem_range]
    rw [permToNatList_getElem, permToNatList_getD τ ⟨i, hiN⟩]
    exact firstIdx_eq_of_min ((σ⁻¹ * τ) ⟨i, hiN⟩).isLt
      (by rw [permToNatList_getD σ ((σ⁻¹ * τ) ⟨i, hiN⟩)]; simp)
      fun j hj ↦ by
        have hjN := lt_trans hj ((σ⁻¹ * τ) ⟨i, hiN⟩).isLt
        rw [permToNatList_getD σ ⟨j, hjN⟩, decide_eq_false_iff_not]; intro heq
        have : j = ((σ⁻¹ * τ) ⟨i, hiN⟩).val := congrArg Fin.val
          (show (⟨j, hjN⟩ : Fin N) = σ⁻¹ (τ ⟨i, hiN⟩) by rw [← Fin.ext heq]; simp)
        omega

/-- Inverse of a length-`N` permutation table `xs⁻¹(y) = (xs⁻¹ ∘ id)(y)`. -/
def permInvTable (N : ℕ) (xs : List ℕ) : List ℕ := permInvMulTable N xs (permIdTable N)

/-- `permInvTable N` computes the value table of `σ⁻¹`. -/
lemma permInvTable_eq {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    permInvTable N (permToNatList σ) = permToNatList σ⁻¹ := by
  rw [permInvTable, permIdTable_eq, permInvMulTable_eq, mul_one]

/-- Boolean test checking whether the first `N` entries of `xs` form a bijection on `Fin N`. -/
def isValidPermTable (N : ℕ) (xs : List ℕ) : Bool :=
  ((List.range N).all fun x ↦ decide (xs.getD x 0 < N)) &&
    ((List.range N).all fun y ↦ (List.range N).any fun x ↦ decide (xs.getD x 0 = y))

/-- For a length-`N` list `xs`, `isValidPermTable N xs = true` iff `natListToPerm N xs` succeeds. -/
lemma isValidPermTable_iff {N : ℕ} {xs : List ℕ} (hlen : xs.length = N) :
    isValidPermTable N xs = true ↔ ∃ σ : Equiv.Perm (Fin N), natListToPerm N xs = some σ := by
  simp only [isValidPermTable, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.mem_range, decide_eq_true_eq, natListToPerm_eq_some_iff]
  refine ⟨fun ⟨hlt, hsurj⟩ ↦ ?_, fun ⟨σ, hσ⟩ ↦ hσ ▸ ⟨fun x hx ↦ by
      rw [permToNatList_getD σ ⟨x, hx⟩]; exact (σ ⟨x, hx⟩).isLt,
    fun y hy ↦ ⟨(σ⁻¹ ⟨y, hy⟩).val, (σ⁻¹ ⟨y, hy⟩).isLt, by
      rw [permToNatList_getD σ (σ⁻¹ ⟨y, hy⟩)]; simp⟩⟩⟩
  let f : Fin N → Fin N := fun i ↦ ⟨xs.getD i.val 0, hlt i.val i.isLt⟩
  refine ⟨Equiv.ofBijective f (Finite.surjective_iff_bijective.mp fun y ↦
      let ⟨x, hxN, hxy⟩ := hsurj y.val y.isLt; ⟨⟨x, hxN⟩, Fin.ext hxy⟩),
    List.ext_getElem (by rw [permToNatList_length, hlen]) fun i hi _ ↦ by
      have hiN : i < N := by rw [permToNatList_length] at hi; exact hi
      simp [permToNatList, f, List.getD_eq_getElem?_getD, hlen ▸ hiN]⟩

/-- Composition of permutation tables runs in deterministic polynomial time. -/
theorem computableInPolyTime_permMulTable :
    ComputableInPolyTime (fun p : (ℕ × List ℕ) × List ℕ ↦ permMulTable p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encNatList) encNatList) encNatList := by
  let enc0 := eP (eP eU eL) eL; let pf := fpFst enc0 eU
  have hN := (fpFst (eP eU eL) eL).comp (fpFst eU eL)
  exact fpBuild hN (fp_getD (pf.comp ((fpFst _ _).comp (fpSnd _ _)))
    (fp_min (fp_getD (pf.comp (fpSnd _ _)) (fpSnd enc0 eU)) (pf.comp hN)))

/-- Combined inverse-multiplication `σ⁻¹ * τ` on permutation tables runs in polynomial time. -/
theorem computableInPolyTime_permInvMulTable :
    ComputableInPolyTime (fun p : (ℕ × List ℕ) × List ℕ ↦ permInvMulTable p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encNatList) encNatList) encNatList := by
  let enc0 := eP (eP eU eL) eL; let enc1 := eP enc0 eU
  let pf1 := fpFst enc0 eU; let pf2 := fpFst enc1 eU
  have hN0 := (fpFst (eP eU eL) eL).comp (fpFst eU eL)
  exact fpBuild hN0 (fp_toBin (computableInPolyTime_firstIdx (pf1.comp hN0)
    (fp_eqB (fp_getD (pf2.comp (pf1.comp ((fpFst _ _).comp (fpSnd _ _)))) (fpSnd enc1 eU))
      (fp_getD (pf2.comp (pf1.comp (fpSnd _ _))) (pf2.comp (fpSnd enc0 eU))))))

/-- Inversion of permutation tables runs in deterministic polynomial time. -/
theorem computableInPolyTime_permInvTable :
    ComputableInPolyTime (fun p : ℕ × List ℕ ↦ permInvTable p.1 p.2)
      (encPair encUnary encNatList) encNatList := by
  have hid : FP (eP eU eL) eL (fun p ↦ permIdTable p.1) :=
    (fpBuild (fpFst eU eL) (fp_toBin (fpSnd (eP eU eL) eU))).of_eq fun _ ↦ by
      simp [permIdTable]
  exact ((fpId (eP eU eL)).pair hid).comp computableInPolyTime_permInvMulTable

/-- Testing whether a length-`N` table encodes a valid permutation runs in polynomial time. -/
theorem computableInPolyTime_isValidPermTable :
    ComputableInPolyTime (fun p : ℕ × List ℕ ↦ isValidPermTable p.1 p.2)
      (encPair encUnary encNatList) encBool := by
  let enc0 := eP eU eL; let enc1 := eP enc0 eU; let pf1 := fpFst enc0 eU; let pf2 := fpFst enc1 eU
  have hN0 := fpFst eU eL
  have hltP := ((fp_getD (pf1.comp (fpSnd eU eL)) (fpSnd enc0 eU)).pair
    (fp_toBin (pf1.comp hN0))).comp fpLtBin
  have heqP := fp_eqB (fp_getD (pf2.comp (pf1.comp (fpSnd eU eL))) (fpSnd enc1 eU))
    (fp_toBin (pf2.comp (fpSnd enc0 eU)))
  exact (hN0.forall_lt hltP).and (hN0.forall_lt ((pf1.comp hN0).exists_lt heqP))

end CslibFrontier.PermutationGroup
