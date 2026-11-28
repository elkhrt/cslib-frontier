module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EditDistance.LCS
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomial-Time Longest Common Subsequence and Ulam Rank Aggregation Operations

This module establishes polynomial-time multi-tape Turing-machine computability for longest-common-
subsequence length, Ulam distance, Ulam median cost, Ulam center radius, and the cyclic-block
reduction and lossless block-extraction algorithms between Ulam median and Ulam center over framed
lists of binary natural-number symbols.

## Main definitions

* `CslibFrontier.Computability.PolyTime.encNatSeq`,
  `CslibFrontier.Computability.PolyTime.encNatSeqList`: framed binary encodings for symbol
  sequences `List ℕ` and sequence families `List (List ℕ)`.
* `CslibFrontier.Computability.PolyTime.ulamSeqDist`,
  `CslibFrontier.Computability.PolyTime.ulamMedianCost`,
  `CslibFrontier.Computability.PolyTime.ulamCenterRadius`: Ulam distance, median objective, and
  center objective on finite symbol sequences.
* `CslibFrontier.Computability.PolyTime.cyclicMedianToCenter`,
  `CslibFrontier.Computability.PolyTime.extractMedianFromCenter`: cyclic `m`-block transformation
  mapping `m` rankings of length `n` to `m` rankings of length `m * n` and minimum-cost block
  extraction.

## Main results

* `CslibFrontier.Computability.PolyTime.computableInPolyTime_lcsLength`: two-row dynamic-programming
  evaluation of `Cslib.Algorithms.Lean.EditDistance.lcsLength` runs in polynomial time on a
  multi-tape Turing machine.
* `CslibFrontier.Computability.PolyTime.computableInPolyTime_ulamSeqDist`,
  `CslibFrontier.Computability.PolyTime.computableInPolyTime_ulamMedianCost`,
  `CslibFrontier.Computability.PolyTime.computableInPolyTime_ulamCenterRadius`: polynomial-time
  evaluation of Ulam distance, median cost, and center radius.
* `CslibFrontier.Computability.PolyTime.computableInPolyTime_cyclicMedianToCenter`,
  `CslibFrontier.Computability.PolyTime.computableInPolyTime_extractMedianFromCenter`:
  polynomial-time certificates for the cyclic-block median-to-center transformation and block
  extractor.
-/

public section

namespace CslibFrontier.Computability.PolyTime

open Cslib.Algorithms.Lean.EditDistance Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

/-- Framed list encoding of a sequence of binary natural-number symbols (`encList encNat`). -/
abbrev encNatSeq : List ℕ ↪ List Bool := encList encNat

/-- Framed list encoding of a finite family of symbol sequences (`encList encNatSeq`). -/
abbrev encNatSeqList : List (List ℕ) ↪ List Bool := encList encNatSeq

/-- Ulam distance `|π| - lcsLength ρ π` on finite symbol sequences. -/
@[expose] def ulamSeqDist (ρ π : List ℕ) : ℕ :=
  π.length - lcsLength ρ π

/-- Total Ulam distance `∑_{π ∈ insts} ulamSeqDist ρ π` from candidate `ρ` to `insts`. -/
@[expose] def ulamMedianCost (insts : List (List ℕ)) (ρ : List ℕ) : ℕ :=
  (insts.map (ulamSeqDist ρ)).sum

/-- Maximum Ulam distance `max_{π ∈ insts} ulamSeqDist ρ π` from candidate `ρ` to `insts`. -/
@[expose] def ulamCenterRadius (insts : List (List ℕ)) (ρ : List ℕ) : ℕ :=
  (insts.map (ulamSeqDist ρ)).foldr max 0

private def lcsInnerStep (a : ℕ) (s : List ℕ) (bud : ℕ × (ℕ × ℕ)) : List ℕ :=
  (if decide (a = bud.1) then bud.2.2 + 1 else max bud.2.1 (s.headD 0)) :: s

private def lcsStepRowFast (a : ℕ) (y : List ℕ) (r : List ℕ) : List ℕ :=
  (y.zip (r.zip r.tail)).reverse.foldl (lcsInnerStep a) [r.reverse.headD 0]

private def lcsRowFast (x y : List ℕ) : List ℕ :=
  x.reverse.foldl (fun r a => lcsStepRowFast a y r) (List.replicate (y.length + 1) 0)

private lemma lcsTable_nilRow_eq (y : List ℕ) :
    lcsTable.nilRow y = List.replicate (y.length + 1) 0 := by
  induction y with
  | nil => rfl
  | cons b ys ih =>
    change lcsTable.nilCons b ((lcsTable.nilRow ys).headD lcsTable.nilNil) ::
      lcsTable.nilRow ys = List.replicate (ys.length + 2) 0
    rw [ih]
    simp [lcsTable, List.replicate_succ]

private lemma length_lcsTable_stepRow (a : ℕ) (y r : List ℕ) :
    (lcsTable.stepRow a y r).length = y.length + 1 := by
  induction y generalizing r with
  | nil => rfl
  | cons b ys ih => simp [GridDP.stepRow, ih]

private lemma length_lcsTable_row (y x : List ℕ) :
    (lcsTable.row y x).length = y.length + 1 := by
  induction x with
  | nil => simp [GridDP.row, lcsTable_nilRow_eq]
  | cons a xs ih => simp [GridDP.row, length_lcsTable_stepRow]

private lemma headD_append_of_ne_nil {α : Type*} {l₁ : List α} (hl₁ : l₁ ≠ []) (l₂ : List α)
    (d : α) : (l₁ ++ l₂).headD d = l₁.headD d := by
  cases l₁ with
  | nil => exact False.elim (hl₁ rfl)
  | cons x xs => rfl

private lemma lcsStepRowFast_eq_stepRow (a : ℕ) :
    ∀ (y r : List ℕ), r.length = y.length + 1 → lcsStepRowFast a y r = lcsTable.stepRow a y r
  | [], r, hr => by
    rcases r with _ | ⟨u, _ | _⟩ <;> simp at hr
    rfl
  | b :: ys, r, hr => by
    rcases r with _ | ⟨u, _ | ⟨d, rs⟩⟩
    · simp at hr
    · simp at hr
    · have hrs : (d :: rs).length = ys.length + 1 := by simpa using hr
      have hhead : (u :: d :: rs).reverse.headD 0 = (d :: rs).reverse.headD 0 := by
        rw [List.reverse_cons]
        exact headD_append_of_ne_nil (List.reverse_ne_nil_iff.mpr (List.cons_ne_nil d rs)) [u] 0
      have hzip : ((b :: ys).zip ((u :: d :: rs).zip (u :: d :: rs).tail)).reverse =
          (ys.zip ((d :: rs).zip (d :: rs).tail)).reverse ++ [(b, (u, d))] := by
        simp [List.zip_cons_cons]
      unfold lcsStepRowFast
      rw [hhead, hzip, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have ih := lcsStepRowFast_eq_stepRow a ys (d :: rs) hrs
      unfold lcsStepRowFast at ih
      rw [ih]
      change lcsInnerStep a (lcsTable.stepRow a ys (d :: rs)) (b, (u, d)) =
        lcsTable.consCons a b d u ((lcsTable.stepRow a ys (d :: rs)).headD lcsTable.nilNil) ::
          lcsTable.stepRow a ys (d :: rs)
      simp [lcsInnerStep, lcsTable]

private lemma lcsRowFast_eq_row (x y : List ℕ) : lcsRowFast x y = lcsTable.row y x := by
  induction x with
  | nil => simp [lcsRowFast, GridDP.row, lcsTable_nilRow_eq]
  | cons a xs ih =>
    unfold lcsRowFast
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change lcsStepRowFast a y (lcsRowFast xs y) = lcsTable.row y (a :: xs)
    rw [ih, lcsStepRowFast_eq_stepRow a y (lcsTable.row y xs) (length_lcsTable_row y xs)]
    rfl

private lemma forall_mem_stepRow_le (a : ℕ) {m : ℕ} :
    ∀ (y r : List ℕ), (∀ v ∈ r, v ≤ m) → ∀ v ∈ lcsTable.stepRow a y r, v ≤ m + 1
  | [], r, hr => by
    intro v hv
    simp only [GridDP.stepRow, lcsTable, List.mem_singleton] at hv
    subst hv
    cases r with
    | nil => exact Nat.zero_le _
    | cons u rs => exact (hr u List.mem_cons_self).trans (Nat.le_succ m)
  | b :: ys, r, hr => by
    have htail : ∀ v ∈ r.tail, v ≤ m := fun v hv => hr v (List.mem_of_mem_tail hv)
    have ih := forall_mem_stepRow_le a ys r.tail htail
    intro v hv
    set s := lcsTable.stepRow a ys r.tail
    change v ∈ (if a = b then r.tail.headD 0 + 1 else max (r.headD 0) (s.headD 0)) :: s at hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · split_ifs
      · have hd : r.tail.headD 0 ≤ m := by
          cases hrt : r.tail with
          | nil => exact Nat.zero_le _
          | cons d ds => exact htail d (hrt ▸ List.mem_cons_self)
        omega
      · refine max_le ?_ ?_
        · cases r with
          | nil => exact Nat.zero_le _
          | cons u rs => exact (hr u List.mem_cons_self).trans (Nat.le_succ m)
        · cases hs : s with
          | nil => exact Nat.zero_le _
          | cons w ws =>
            rw [List.headD_cons]
            exact ih w (hs ▸ List.mem_cons_self)
    · exact ih v hv

private lemma forall_mem_row_le (y x : List ℕ) :
    ∀ v ∈ lcsTable.row y x, v ≤ x.length := by
  induction x with
  | nil =>
    intro v hv
    rw [GridDP.row, lcsTable_nilRow_eq] at hv
    simp [List.eq_of_mem_replicate hv]
  | cons a xs ih =>
    intro v hv
    exact forall_mem_stepRow_le a y (lcsTable.row y xs) ih v hv

private abbrev encStepIn : ((ℕ × List ℕ) × List ℕ) ↪ List Bool :=
  encPair (encPair encNat encNatSeq) (encList encUnary)

private abbrev encTriple : (ℕ × (ℕ × ℕ)) ↪ List Bool :=
  encPair encNat (encPair encUnary encUnary)

private theorem computableInPolyTime_lcsStepRowFast :
    ComputableInPolyTime (fun p : (ℕ × List ℕ) × List ℕ => lcsStepRowFast p.1.1 p.1.2 p.2)
      encStepIn (encList encUnary) := by
  have hpar : ComputableInPolyTime (fun p : (ℕ × List ℕ) × List ℕ => p.1.1) encStepIn encNat :=
    (fst _ _).fst'
  have hlist : ComputableInPolyTime
      (fun p : (ℕ × List ℕ) × List ℕ => (p.1.2.zip (p.2.zip p.2.tail)).reverse)
      encStepIn (encList encTriple) :=
    (listReverse encTriple).comp ((zip encNat (encPair encUnary encUnary)).comp
      ((fst _ _).snd'.prod ((zip encUnary encUnary).comp
        ((snd _ _).prod ((listTail encUnary).comp (snd _ _))))))
  have hinit : ComputableInPolyTime
      (fun p : (ℕ × List ℕ) × List ℕ => [p.2.reverse.headD 0]) encStepIn (encList encUnary) :=
    cons' ((headD 0).comp ((listReverse encUnary).comp (snd _ _))) (const [])
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × List ℕ) × (ℕ × (ℕ × ℕ)) => lcsInnerStep q.1.1 q.1.2 q.2)
      (encPair (encPair encNat (encList encUnary)) encTriple) (encList encUnary) := by
    let encQ := encPair (encPair encNat (encList encUnary)) encTriple
    have hq11 : ComputableInPolyTime (fun q : (ℕ × List ℕ) × (ℕ × (ℕ × ℕ)) => q.1.1) encQ encNat :=
      (fst _ _).fst'
    have hq21 : ComputableInPolyTime (fun q : (ℕ × List ℕ) × (ℕ × (ℕ × ℕ)) => q.2.1) encQ encNat :=
      (snd _ _).fst'
    have hcond := decide_eq' hq11 hq21
    have htrue : ComputableInPolyTime
        (fun q : (ℕ × List ℕ) × (ℕ × (ℕ × ℕ)) => q.2.2.2 + 1) encQ encUnary :=
      unary_add' (snd (encPair encNat (encList encUnary)) encTriple).snd'.snd' (const 1)
    have hfalse : ComputableInPolyTime
        (fun q : (ℕ × List ℕ) × (ℕ × (ℕ × ℕ)) => max q.2.2.1 (q.1.2.headD 0)) encQ encUnary :=
      unary_max.comp
        ((snd (encPair encNat (encList encUnary)) encTriple).snd'.fst'.prod
          ((headD 0).comp (fst (encPair encNat (encList encUnary)) encTriple).snd'))
    exact cons' (ite hcond htrue hfalse)
      (fst (encPair encNat (encList encUnary)) encTriple).snd'
  refine (foldlWith_spec (encIn := encStepIn) (encA := encTriple) (encB := encList encUnary)
    (encL := encList encTriple) (encP := encNat)
    hpar hlist hinit hstep
    (fun p consumed s => s.length = consumed.length + 1 ∧
      ∀ v ∈ s, v ≤ (encList encUnary p.2).length + 1)
    ?_ ?_
    (size := fun p => ((encStepIn p).length + 1) * (2 * (encStepIn p).length + 5))
    ((PolyBounded.self.add (.const 1)).mul (((PolyBounded.const 2).mul .self).add (.const 5)))
    ?_).1
  · intro p
    refine ⟨rfl, fun v hv => ?_⟩
    rw [List.mem_singleton.mp hv]
    cases hr : p.2.reverse with
    | nil => exact Nat.zero_le _
    | cons w ws =>
      rw [List.headD_cons]
      have hw : w ∈ p.2 := List.mem_reverse.mp (hr ▸ List.mem_cons_self)
      have hle := SizedListEncoding.length_elem_le (encA := encUnary) (encL := encList encUnary)
        p.2 w hw
      simp only [encUnary_apply, List.length_replicate] at hle
      omega
  · intro p consumed s bud hpref ⟨hlen, hs⟩
    refine ⟨by simp [lcsInnerStep, hlen], fun v hv => ?_⟩
    have hmem_rev : bud ∈ (p.1.2.zip (p.2.zip p.2.tail)).reverse :=
      hpref.subset (by simp)
    have hmem_zip1 := List.of_mem_zip (List.mem_reverse.mp hmem_rev)
    have hmem_zip2 := List.of_mem_zip hmem_zip1.2
    have hu_mem : bud.2.1 ∈ p.2 := hmem_zip2.1
    have hd_mem : bud.2.2 ∈ p.2 := List.mem_of_mem_tail hmem_zip2.2
    have hu_le : bud.2.1 ≤ (encList encUnary p.2).length := by
      simpa [encUnary_apply] using
        SizedListEncoding.length_elem_le (encA := encUnary) (encL := encList encUnary)
          p.2 bud.2.1 hu_mem
    have hd_le : bud.2.2 ≤ (encList encUnary p.2).length := by
      simpa [encUnary_apply] using
        SizedListEncoding.length_elem_le (encA := encUnary) (encL := encList encUnary)
          p.2 bud.2.2 hd_mem
    simp only [lcsInnerStep, List.mem_cons] at hv
    rcases hv with rfl | hv
    · split_ifs
      · omega
      · refine max_le (by omega) ?_
        cases s with
        | nil => exact Nat.zero_le _
        | cons w ws => exact hs w List.mem_cons_self
    · exact hs v hv
  · intro p consumed s hpref ⟨hlen, hs⟩
    have hlen_le : consumed.length ≤ (encStepIn p).length := by
      have h1 : consumed.length ≤ (p.1.2.zip (p.2.zip p.2.tail)).reverse.length := hpref.length_le
      have h2 : (p.1.2.zip (p.2.zip p.2.tail)).reverse.length ≤ p.1.2.length := by simp
      have h3 : p.1.2.length ≤ (encNatSeq p.1.2).length :=
        SizedListEncoding.length_le (encA := encNat) (encL := encNatSeq) p.1.2
      have h4 : (encNatSeq p.1.2).length ≤ (encStepIn p).length := by
        simp only [encStepIn, length_encPair]; omega
      omega
    have hr_le : (encList encUnary p.2).length ≤ (encStepIn p).length := by
      simp only [encStepIn, length_encPair]; omega
    have hbound_s := length_encList_le encUnary s (b := (encList encUnary p.2).length + 1)
      fun v hv => by simpa [encUnary_apply] using hs v hv
    rw [hlen] at hbound_s
    exact hbound_s.trans (Nat.mul_le_mul (by omega) (by omega))

/-- Longest-common-subsequence length `lcsLength x y` is computable in polynomial time on a
multi-tape Turing machine over framed binary natural-number lists. -/
theorem computableInPolyTime_lcsLength :
    ComputableInPolyTime (fun p : List ℕ × List ℕ => lcsLength p.1 p.2)
      (encPair encNatSeq encNatSeq) encNat := by
  let encXY := encPair encNatSeq encNatSeq
  have hpar : ComputableInPolyTime (fun p : List ℕ × List ℕ => p.2) encXY encNatSeq := snd _ _
  have hlist : ComputableInPolyTime (fun p : List ℕ × List ℕ => p.1.reverse) encXY encNatSeq :=
    (listReverse encNat).comp (fst _ _)
  have hinit : ComputableInPolyTime
      (fun p : List ℕ × List ℕ => List.replicate (p.2.length + 1) 0) encXY (encList encUnary) :=
    replicate (unary_add' ((length_list encNat).comp (snd _ _)) (const 1)) (const 0)
  have hstep : ComputableInPolyTime
      (fun q : (List ℕ × List ℕ) × ℕ => lcsStepRowFast q.2 q.1.1 q.1.2)
      (encPair (encPair encNatSeq (encList encUnary)) encNat) (encList encUnary) :=
    computableInPolyTime_lcsStepRowFast.comp
      (((snd _ _).prod (fst _ _).fst').prod (fst _ _).snd')
  have hrow : ComputableInPolyTime (fun p : List ℕ × List ℕ => lcsRowFast p.1 p.2)
      encXY (encList encUnary) := by
    refine foldlWith (encIn := encXY) (encA := encNat) (encB := encList encUnary)
      (encL := encNatSeq) (encP := encNatSeq)
      (step := fun y r a => lcsStepRowFast a y r)
      hpar hlist hinit hstep
      (B := fun p => ((encXY p).length + 1) * (2 * (encXY p).length + 1))
      ((PolyBounded.self.add (.const 1)).mul (((PolyBounded.const 2).mul .self).add (.const 1)))
      ?_
    intro p i _
    let xs' : List ℕ := (p.1.reverse.take i).reverse
    have htake : p.1.reverse.take i = xs'.reverse := by simp [xs']
    have hfold_eq :
        (p.1.reverse.take i).foldl (fun r a => lcsStepRowFast a p.2 r)
          (List.replicate (p.2.length + 1) 0) = lcsTable.row p.2 xs' := by
      rw [htake]
      exact lcsRowFast_eq_row xs' p.2
    rw [hfold_eq]
    have hx_le : xs'.length ≤ (encXY p).length := by
      have h1 : xs'.length ≤ p.1.length := by simp [xs']
      have h2 : p.1.length ≤ (encNatSeq p.1).length :=
        SizedListEncoding.length_le (encA := encNat) (encL := encNatSeq) p.1
      have h3 : (encNatSeq p.1).length ≤ (encXY p).length := by
        simp only [encXY, length_encPair]; omega
      omega
    have hy_le : p.2.length ≤ (encXY p).length := by
      have h2 : p.2.length ≤ (encNatSeq p.2).length :=
        SizedListEncoding.length_le (encA := encNat) (encL := encNatSeq) p.2
      have h3 : (encNatSeq p.2).length ≤ (encXY p).length := by
        simp only [encXY, length_encPair]; omega
      omega
    have hbound_r := length_encList_le encUnary (lcsTable.row p.2 xs') (b := xs'.length)
      fun v hv => by simpa [encUnary_apply] using forall_mem_row_le p.2 xs' v hv
    rw [length_lcsTable_row] at hbound_r
    exact hbound_r.trans (Nat.mul_le_mul (by omega) (by omega))
  have hlcs_unary : ComputableInPolyTime (fun p : List ℕ × List ℕ => (lcsRowFast p.1 p.2).headD 0)
      encXY encUnary := (headD 0).comp hrow
  convert unary_to_binary.comp hlcs_unary using 1
  funext p
  simp only [Function.comp_apply, lcsRowFast_eq_row, lcsLength, GridDP.value, lcsTable]

/-- `ulamSeqDist` is computable in polynomial time on `(encPair encNatSeq encNatSeq)`. -/
theorem computableInPolyTime_ulamSeqDist :
    ComputableInPolyTime (fun p : List ℕ × List ℕ => ulamSeqDist p.1 p.2)
      (encPair encNatSeq encNatSeq) encNat :=
  binary_sub' (unary_to_binary.comp ((length_list encNat).comp (snd _ _)))
    computableInPolyTime_lcsLength

/-- `ulamMedianCost` is computable in polynomial time on `(encPair encNatSeqList encNatSeq)`. -/
theorem computableInPolyTime_ulamMedianCost :
    ComputableInPolyTime (fun p : List (List ℕ) × List ℕ => ulamMedianCost p.1 p.2)
      (encPair encNatSeqList encNatSeq) encNat :=
  binary_sum.comp (mapWith computableInPolyTime_ulamSeqDist (snd _ _) (fst _ _))

private lemma foldr_max_eq_foldl_max (l : List ℕ) : l.foldr max 0 = l.foldl max 0 := by
  have haux (acc : ℕ) : ∀ xs : List ℕ, xs.foldl max acc = max acc (xs.foldr max 0) := by
    intro xs
    induction xs generalizing acc with
    | nil => simp
    | cons a tl ih =>
      simp only [List.foldl_cons, List.foldr_cons, ih]
      exact max_assoc acc a (tl.foldr max 0)
  simpa using (haux 0 l).symm

private theorem computableInPolyTime_binary_listMax :
    ComputableInPolyTime (fun l : List ℕ => l.foldl max 0) (encList encNat) encNat := by
  have hstep : ComputableInPolyTime (fun p : ℕ × ℕ => max p.1 p.2)
      (encPair encNat encNat) encNat := by
    convert ite (binary_le' (fst _ _) (snd _ _)) (snd _ _) (fst _ _) using 1
    funext p
    by_cases h : p.1 ≤ p.2 <;> simp [h, Nat.max_def]
  refine (foldl_spec (encIn := encList encNat) (encA := encNat) (encB := encNat)
    (encL := encList encNat) id' (const 0) hstep
    (fun _ consumed m => m = 0 ∨ m ∈ consumed)
    (fun _ => Or.inl rfl)
    (fun _ consumed m v _ hm => by
      rcases le_total m v with hmv | hvm
      · rw [max_eq_right hmv]; exact Or.inr (by simp)
      · rw [max_eq_left hvm]
        rcases hm with rfl | hm
        · exact Or.inl rfl
        · exact Or.inr (List.mem_append_left _ hm))
    (size := fun l => (encList encNat l).length) PolyBounded.self
    (fun l consumed m hpref hm => by
      rcases hm with rfl | hm
      · simp
      · exact SizedListEncoding.length_elem_le (encA := encNat) (encL := encList encNat)
          l m (hpref.subset hm))).1

/-- `ulamCenterRadius` is computable in polynomial time on `(encPair encNatSeqList encNatSeq)`. -/
theorem computableInPolyTime_ulamCenterRadius :
    ComputableInPolyTime (fun p : List (List ℕ) × List ℕ => ulamCenterRadius p.1 p.2)
      (encPair encNatSeqList encNatSeq) encNat := by
  convert computableInPolyTime_binary_listMax.comp
    (mapWith computableInPolyTime_ulamSeqDist (snd _ _) (fst _ _)) using 1
  funext p
  simp only [Function.comp_apply, ulamCenterRadius, ← foldr_max_eq_foldl_max]

/-- Cyclic `m`-block median-to-center instance construction over disjoint alphabet copies
`x * m + i` (`0 ≤ i < m`). -/
def cyclicMedianToCenter (insts : List (List ℕ)) : List (List ℕ) :=
  let m := insts.length
  (List.range m).map fun j =>
    (List.range m).flatMap fun i =>
      let idx := if j + i < m then j + i else j + i - m
      (insts.getD idx []).map fun x => x * m + i

/-- Extract the `i`-th copy block from a candidate sequence over `cyclicMedianToCenter insts`. -/
def extractCopyBlock (m : ℕ) (τ : List ℕ) (i : ℕ) : List ℕ :=
  (τ.filter fun y => decide (y % m = i)).map (· / m)

/-- Select a minimum-median-cost block among the `m` copy blocks extracted from `τ`. -/
def extractMedianFromCenter (p : List (List ℕ) × List ℕ) : List ℕ :=
  let insts := p.1
  let τ := p.2
  let m := insts.length
  let cands := (List.range m).map (extractCopyBlock m τ)
  cands.foldl
    (fun best ρ => if decide (ulamMedianCost insts ρ < ulamMedianCost insts best) then ρ else best)
    (insts.headD [])

/-- `cyclicMedianToCenter` is computable in polynomial time on a multi-tape Turing machine. -/
theorem computableInPolyTime_cyclicMedianToCenter :
    ComputableInPolyTime cyclicMedianToCenter encNatSeqList encNatSeqList := by
  have hm_un : ComputableInPolyTime (fun insts : List (List ℕ) => insts.length)
      encNatSeqList encUnary := length_list encNatSeq
  refine mapWithInput (range.comp hm_un) ?_
  let encJ := encPair encNatSeqList encUnary
  refine flatMapWithInput (range.comp (hm_un.comp (fst _ _))) ?_
  let encJI := encPair encJ encUnary
  have hm_ji : ComputableInPolyTime (fun p : (List (List ℕ) × ℕ) × ℕ => p.1.1.length)
      encJI encUnary := hm_un.comp (fst _ _).fst'
  have hj_ji : ComputableInPolyTime (fun p : (List (List ℕ) × ℕ) × ℕ => p.1.2)
      encJI encUnary := (fst _ _).snd'
  have hi_ji : ComputableInPolyTime (fun p : (List (List ℕ) × ℕ) × ℕ => p.2)
      encJI encUnary := snd _ _
  have hsum_ji := unary_add' hj_ji hi_ji
  have hidx_ji : ComputableInPolyTime
      (fun p : (List (List ℕ) × ℕ) × ℕ =>
        if p.1.2 + p.2 < p.1.1.length then p.1.2 + p.2 else p.1.2 + p.2 - p.1.1.length)
      encJI encUnary :=
    ite_decide (unary_lt.comp (hsum_ji.prod hm_ji)) hsum_ji (unary_sub' hsum_ji hm_ji)
  have hperm : ComputableInPolyTime
      (fun p : (List (List ℕ) × ℕ) × ℕ =>
        p.1.1.getD
          (if p.1.2 + p.2 < p.1.1.length then p.1.2 + p.2 else p.1.2 + p.2 - p.1.1.length) [])
      encJI encNatSeq :=
    listGetDWithInput (fst _ _).fst' hidx_ji []
  have hm_bin : ComputableInPolyTime (fun p : (List (List ℕ) × ℕ) × ℕ => p.1.1.length) encJI
      encNat := unary_to_binary.comp hm_ji
  have hi_bin : ComputableInPolyTime (fun p : (List (List ℕ) × ℕ) × ℕ => p.2) encJI encNat :=
    unary_to_binary.comp hi_ji
  exact mapWith
    (binary_add'
      (binary_mul' (snd (encPair encNat encNat) encNat) (fst (encPair encNat encNat) encNat).fst')
      (fst (encPair encNat encNat) encNat).snd')
    (hm_bin.prod hi_bin) hperm

/-- `extractMedianFromCenter` is computable in polynomial time on a multi-tape Turing machine. -/
theorem computableInPolyTime_extractMedianFromCenter :
    ComputableInPolyTime extractMedianFromCenter (encPair encNatSeqList encNatSeq) encNatSeq := by
  let encIT := encPair encNatSeqList encNatSeq
  have hm_un : ComputableInPolyTime (fun p : List (List ℕ) × List ℕ => p.1.length)
      encIT encUnary := (length_list encNatSeq).comp (fst encNatSeqList encNatSeq)
  have hcands : ComputableInPolyTime
      (fun p : List (List ℕ) × List ℕ =>
        (List.range p.1.length).map (extractCopyBlock p.1.length p.2))
      encIT encNatSeqList := by
    refine mapWithInput (range.comp hm_un) ?_
    let encITI := encPair encIT encUnary
    have hm_bin : ComputableInPolyTime (fun q : (List (List ℕ) × List ℕ) × ℕ => q.1.1.length)
        encITI encNat := unary_to_binary.comp (hm_un.comp (fst encIT encUnary))
    have hi_bin : ComputableInPolyTime (fun q : (List (List ℕ) × List ℕ) × ℕ => q.2)
        encITI encNat := unary_to_binary.comp (snd encIT encUnary)
    have hτ : ComputableInPolyTime (fun q : (List (List ℕ) × List ℕ) × ℕ => q.1.2)
        encITI encNatSeq := (fst encIT encUnary).snd'
    have hfilt : ComputableInPolyTime
        (fun q : (List (List ℕ) × List ℕ) × ℕ =>
          q.1.2.filter fun y => decide (y % q.1.1.length = q.2))
        encITI encNatSeq :=
      filterWithInput hτ (decide_eq'
        (binary_mod' (snd encITI encNat) (hm_bin.comp (fst encITI encNat)))
        (hi_bin.comp (fst encITI encNat)))
    exact mapWith (binary_div' (snd encNat encNat) (fst encNat encNat)) hm_bin hfilt
  have hinit : ComputableInPolyTime (fun p : List (List ℕ) × List ℕ => p.1.headD [])
      encIT encNatSeq := (headD []).comp (fst encNatSeqList encNatSeq)
  have hstep : ComputableInPolyTime
      (fun q : (List (List ℕ) × List ℕ) × List ℕ =>
        if decide (ulamMedianCost q.1.1 q.2 < ulamMedianCost q.1.1 q.1.2) then q.2 else q.1.2)
      (encPair (encPair encNatSeqList encNatSeq) encNatSeq) encNatSeq := by
    let encIB := encPair encNatSeqList encNatSeq
    have hc_new := computableInPolyTime_ulamMedianCost.comp
      ((fst encIB encNatSeq).fst'.prod (snd encIB encNatSeq))
    have hc_best := computableInPolyTime_ulamMedianCost.comp (fst encIB encNatSeq)
    exact ite (binary_lt' hc_new hc_best) (snd encIB encNatSeq) (fst encIB encNatSeq).snd'
  obtain ⟨cC, dC, hC_bound⟩ := hcands.polyBounded_length.exists_le
  refine (foldlWith_spec (encIn := encIT) (encA := encNatSeq) (encB := encNatSeq)
    (encL := encNatSeqList) (encP := encNatSeqList)
    (step := fun insts best ρ =>
      if decide (ulamMedianCost insts ρ < ulamMedianCost insts best) then ρ else best)
    (fst encNatSeqList encNatSeq) hcands hinit hstep
    (fun p consumed best => best = p.1.headD [] ∨ best ∈ consumed)
    (fun _ => Or.inl rfl)
    (fun p consumed best ρ _ hbest => by
      split_ifs
      · exact Or.inr (by simp)
      · rcases hbest with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_append_left _ h))
    (size := fun p => (encIT p).length + cC * ((encIT p).length + 1) ^ dC)
    (PolyBounded.self.add (PolyBounded.of_forall_le cC dC fun _ => le_rfl))
    (fun p consumed best hpref hbest => by
      rcases hbest with rfl | hmem
      · cases hp : p.1 with
        | nil => simp
        | cons π₀ rest =>
          have h1 := SizedListEncoding.length_elem_le (encA := encNatSeq)
            (encL := encNatSeqList) (π₀ :: rest) π₀ List.mem_cons_self
          have h2 : (encNatSeqList p.1).length ≤ (encIT p).length := by
            simp only [encIT, length_encPair]; omega
          rw [← hp] at h1
          simp only [hp, List.headD_cons] at *
          omega
      · have hmem_all := hpref.subset hmem
        have h1 := SizedListEncoding.length_elem_le (encA := encNatSeq)
          (encL := encNatSeqList) _ best hmem_all
        have h2 := hC_bound p
        omega)).1

end CslibFrontier.Computability.PolyTime
