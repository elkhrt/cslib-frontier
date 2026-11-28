/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.ClowSequence
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Mahajan–Vinay Sign-Reversing Involution on Clow Sequences

This module constructs the Mahajan–Vinay sign-reversing, weight-preserving involution on
non-cycle-cover clow sequences and deduces that the sum of signed weights over all clow sequences
on `Fin n` equals `M.det`.

## Main results

* `CslibFrontier.Computability.Circuit.sum_clowSeq_eq_det`: for every `n × n` matrix `M` over a
  commutative ring `R`, `∑ w : ClowSeq n, w.signedWeight M = M.det`.
-/

public section

namespace CslibFrontier.Computability.Circuit

open scoped Matrix

section Clows

/-! ### Sign-Reversing Involution on Non-Cycle-Cover Clow Sequences -/

/-- Find the first element of `tail` (with prefix already scanned in reverse as `seen`)
that either appears in `restVerts` or repeats an earlier element in `seen`. -/
private def findFirstCollision {n : ℕ} (restVerts : List (Fin n)) :
    List (Fin n) → List (Fin n) → Option (List (Fin n) × Fin n × List (Fin n))
  | _, [] => none
  | seen, v :: vs =>
    if v ∈ restVerts ∨ v ∈ seen then some (seen.reverse, v, vs)
    else findFirstCollision restVerts (v :: seen) vs

private theorem findFirstCollision_clean {n : ℕ} (restVerts seen tail : List (Fin n))
    (hseen_nd : seen.Nodup) (hseen_disj : ∀ u ∈ seen, u ∉ restVerts) :
    (∀ pref v suff, findFirstCollision restVerts seen tail = some (pref, v, suff) →
      seen.reverse ++ tail = pref ++ (v :: suff) ∧
      (v ∈ restVerts ∨ v ∈ pref) ∧
      pref.Nodup ∧ (∀ u ∈ pref, u ∉ restVerts)) ∧
    (findFirstCollision restVerts seen tail = none →
      (seen.reverse ++ tail).Nodup ∧ (∀ u ∈ tail, u ∉ restVerts)) := by
  induction tail generalizing seen with
  | nil =>
    refine ⟨fun _ _ _ h => by simp [findFirstCollision] at h,
      fun _ => ⟨by simpa using hseen_nd, fun _ h => by simp at h⟩⟩
  | cons v vs ih =>
    simp only [findFirstCollision]
    by_cases hcol : v ∈ restVerts ∨ v ∈ seen
    · simp only [hcol, ↓reduceIte]
      refine ⟨fun pref w suff h => ?_, fun h => by simp at h⟩
      injection h with h'
      obtain ⟨rfl, h''⟩ := Prod.mk.inj h'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h''
      refine ⟨rfl, ?_, List.nodup_reverse.mpr hseen_nd,
        fun u hu => hseen_disj u (List.mem_reverse.mp hu)⟩
      rcases hcol with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_reverse.mpr h)
    · simp only [hcol, ↓reduceIte]
      have hv_r : v ∉ restVerts := fun h => hcol (Or.inl h)
      have hv_s : v ∉ seen := fun h => hcol (Or.inr h)
      have hih := ih (v :: seen) (List.nodup_cons.mpr ⟨hv_s, hseen_nd⟩) fun u hu => by
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hv_r
        · exact hseen_disj u hu
      have hrev : (v :: seen).reverse ++ vs = seen.reverse ++ (v :: vs) := by
        simp [List.reverse_cons, List.append_assoc]
      refine ⟨fun pref w suff h => ?_, fun h => ?_⟩
      · have hs := hih.1 pref w suff h
        rw [hrev] at hs
        exact hs
      · obtain ⟨hnd, hdisj⟩ := hih.2 h
        rw [hrev] at hnd
        refine ⟨hnd, fun u hu => ?_⟩
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hv_r
        · exact hdisj u hu

private theorem findFirstCollision_eq_some {n : ℕ} (restVerts pref : List (Fin n))
    (v : Fin n) (suff : List (Fin n))
    (hnd : pref.Nodup) (hdisj : ∀ u ∈ pref, u ∉ restVerts) :
    ∀ (seen : List (Fin n)), (∀ u ∈ pref, u ∉ seen) →
      (v ∈ restVerts ∨ v ∈ pref ∨ v ∈ seen) →
      findFirstCollision restVerts seen (pref ++ (v :: suff)) =
        some (seen.reverse ++ pref, v, suff) := by
  induction pref with
  | nil =>
    intro seen _ hcol
    simp only [List.nil_append, List.append_nil, findFirstCollision]
    have hc : v ∈ restVerts ∨ v ∈ seen := by
      rcases hcol with h | h | h
      · exact Or.inl h
      · simp at h
      · exact Or.inr h
    simp [hc]
  | cons u us ih =>
    intro seen hseen hcol
    simp only [List.cons_append, findFirstCollision]
    have hu_r : u ∉ restVerts := hdisj u List.mem_cons_self
    have hu_s : u ∉ seen := hseen u List.mem_cons_self
    have hnot : ¬ (u ∈ restVerts ∨ u ∈ seen) := by tauto
    simp only [hnot, ↓reduceIte]
    have hnd_us : us.Nodup := (List.nodup_cons.mp hnd).2
    have hu_us : u ∉ us := (List.nodup_cons.mp hnd).1
    have hdisj_us : ∀ w ∈ us, w ∉ restVerts := fun w hw => hdisj w (List.mem_cons_of_mem _ hw)
    have hseen_us : ∀ w ∈ us, w ∉ u :: seen := fun w hw h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact hu_us hw
      · exact hseen w (List.mem_cons_of_mem _ hw) h'
    have hcol_us : v ∈ restVerts ∨ v ∈ us ∨ v ∈ u :: seen := by
      rcases hcol with h | h | h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with rfl | h'
        · exact Or.inr (Or.inr List.mem_cons_self)
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h))
    rw [ih hnd_us hdisj_us (u :: seen) hseen_us hcol_us]
    simp [List.reverse_cons, List.append_assoc]

/-- Remove the first clow containing `v` from `cs`. -/
private def extractClow {n : ℕ} (v : Fin n) : List (Clow n) → Option (Clow n × List (Clow n))
  | [] => none
  | c :: cs =>
    if v ∈ c.verts then some (c, cs)
    else (extractClow v cs).map fun p => (p.1, c :: p.2)

private theorem extractClow_spec {n : ℕ} (v : Fin n) (cs : List (Clow n)) :
    (∀ c' rest', extractClow v cs = some (c', rest') →
      v ∈ c'.verts ∧ cs.Perm (c' :: rest') ∧
      (cs.Pairwise (fun a b => a.head < b.head) → rest'.Pairwise (fun a b => a.head < b.head)) ∧
      (∀ h, (∀ c ∈ cs, h < c.head) → ∀ c ∈ rest', h < c.head)) ∧
    (extractClow v cs = none → v ∉ cs.flatMap Clow.verts) := by
  induction cs with
  | nil =>
    exact ⟨fun _ _ h => by simp [extractClow] at h, fun _ => by simp⟩
  | cons c cs ih =>
    simp only [extractClow]
    by_cases hv : v ∈ c.verts
    · simp only [hv, ↓reduceIte]
      refine ⟨fun c' rest' h => ?_, fun h => by simp at h⟩
      have h1 : c' = c := by injection h with h'; exact (congrArg Prod.fst h').symm
      have h2 : rest' = cs := by injection h with h'; exact (congrArg Prod.snd h').symm
      subst h1; subst h2
      exact ⟨hv, List.Perm.refl _, fun hp => (List.pairwise_cons.mp hp).2,
        fun h hh x hx => hh x (List.mem_cons_of_mem _ hx)⟩
    · simp only [hv, ↓reduceIte]
      refine ⟨fun c' rest' h => ?_, fun h => ?_⟩
      · cases hex : extractClow v cs with
        | none => simp [hex] at h
        | some p =>
          rw [hex] at h; simp only [Option.map_some, Option.some.injEq] at h
          have h1 : c' = p.1 := (congrArg Prod.fst h).symm
          have h2 : rest' = c :: p.2 := (congrArg Prod.snd h).symm
          subst h1; subst h2
          obtain ⟨hpv, hperm, hpw, hhd⟩ := ih.1 p.1 p.2 hex
          refine ⟨hpv, (List.Perm.cons c hperm).trans (List.Perm.swap p.1 c p.2), ?_, ?_⟩
          · intro hp
            have hpc := List.pairwise_cons.mp hp
            refine List.pairwise_cons.mpr ⟨fun x hx => ?_, hpw hpc.2⟩
            exact hpc.1 x (hperm.mem_iff.mpr (List.mem_cons_of_mem _ hx))
          · intro h hh x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hh _ List.mem_cons_self
            · exact hhd h (fun y hy => hh y (List.mem_cons_of_mem _ hy)) x hx
      · cases hex : extractClow v cs with
        | none =>
          simp only [List.flatMap_cons, List.mem_append, not_or]
          exact ⟨hv, ih.2 hex⟩
        | some p => simp [hex] at h

/-- Insert a clow `c` into a head-sorted list `cs` in strictly increasing head order. -/
private def insertClow {n : ℕ} (c : Clow n) : List (Clow n) → List (Clow n)
  | [] => [c]
  | c' :: cs => if c.head < c'.head then c :: c' :: cs else c' :: insertClow c cs

private theorem insertClow_perm {n : ℕ} (c : Clow n) (cs : List (Clow n)) :
    (insertClow c cs).Perm (c :: cs) := by
  induction cs with
  | nil => exact List.Perm.refl _
  | cons c' cs ih =>
    simp only [insertClow]
    split_ifs
    · exact List.Perm.refl _
    · exact (List.Perm.cons c' ih).trans (List.Perm.swap c c' cs)

private theorem insertClow_pairwise {n : ℕ} (c : Clow n) (cs : List (Clow n))
    (hp : cs.Pairwise (fun a b => a.head < b.head)) (hne : ∀ c' ∈ cs, c.head ≠ c'.head) :
    (insertClow c cs).Pairwise (fun a b => a.head < b.head) := by
  induction cs with
  | nil => exact List.pairwise_singleton _ _
  | cons c' cs ih =>
    simp only [insertClow]
    have hpc := List.pairwise_cons.mp hp
    split_ifs with hlt
    · exact List.pairwise_cons.mpr ⟨fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hlt
        · exact lt_trans hlt (hpc.1 x hx), hp⟩
    · have hgt : c'.head < c.head :=
        lt_of_le_of_ne (not_lt.mp hlt) (hne c' List.mem_cons_self).symm
      refine List.pairwise_cons.mpr ⟨fun x hx => ?_,
        ih hpc.2 (fun y hy => hne y (List.mem_cons_of_mem _ hy))⟩
      rcases List.mem_cons.mp ((insertClow_perm c cs).mem_iff.mp hx) with rfl | hx
      · exact hgt
      · exact hpc.1 x hx

private theorem extractClow_insertClow {n : ℕ} {v : Fin n} {c : Clow n} {cs : List (Clow n)}
    (hv : v ∈ c.verts) (hdisj : v ∉ cs.flatMap Clow.verts) :
    extractClow v (insertClow c cs) = some (c, cs) := by
  induction cs with
  | nil => simp [insertClow, extractClow, hv]
  | cons c' cs ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at hdisj
    simp only [insertClow]
    split_ifs
    · simp [extractClow, hv]
    · simp [extractClow, hdisj.1, ih hdisj.2]

private theorem insertClow_of_extractClow {n : ℕ} {v : Fin n} {c' : Clow n}
    {cs rest' : List (Clow n)} (hp : cs.Pairwise (fun a b => a.head < b.head))
    (hex : extractClow v cs = some (c', rest')) :
    insertClow c' rest' = cs := by
  induction cs generalizing rest' with
  | nil => simp [extractClow] at hex
  | cons c cs ih =>
    have hpc := List.pairwise_cons.mp hp
    simp only [extractClow] at hex
    split_ifs at hex with hv
    · have h1 : c' = c := by injection hex with h'; exact (congrArg Prod.fst h').symm
      have h2 : rest' = cs := by injection hex with h'; exact (congrArg Prod.snd h').symm
      subst h1; subst h2
      cases rest' with
      | nil => rfl
      | cons c2 cs2 =>
        have hlt : c'.head < c2.head := hpc.1 c2 List.mem_cons_self
        simp [insertClow, hlt]
    · cases h : extractClow v cs with
      | none => simp [h] at hex
      | some p =>
        rw [h] at hex; simp only [Option.map_some, Option.some.injEq] at hex
        have h1 : c' = p.1 := (congrArg Prod.fst hex).symm
        have h2 : rest' = c :: p.2 := (congrArg Prod.snd hex).symm
        subst h1; subst h2
        have hp_in : p.1 ∈ cs :=
          ((extractClow_spec v cs).1 p.1 p.2 h).2.1.mem_iff.mpr List.mem_cons_self
        have hlt : c.head < p.1.head := hpc.1 p.1 hp_in
        have hnot : ¬ p.1.head < c.head := not_lt.mpr (le_of_lt hlt)
        simp only [insertClow, hnot, ↓reduceIte, ih hpc.2 h]

/-- Minimum element of a nonempty `List (Fin n)`. -/
private def listMin {n : ℕ} : (l : List (Fin n)) → l ≠ [] → Fin n
  | [x], _ => x
  | x :: y :: ys, _ => min x (listMin (y :: ys) (List.cons_ne_nil _ _))

private theorem listMin_mem {n : ℕ} : ∀ (l : List (Fin n)) (hl : l ≠ []), listMin l hl ∈ l
  | [x], _ => List.mem_cons_self
  | x :: y :: ys, _ => by
    simp only [listMin]
    rcases min_choice x (listMin (y :: ys) (List.cons_ne_nil _ _)) with h | h
    · rw [h]; exact List.mem_cons_self
    · rw [h]; exact List.mem_cons_of_mem _ (listMin_mem (y :: ys) _)

private theorem listMin_le {n : ℕ} : ∀ (l : List (Fin n)) (hl : l ≠ []) (u : Fin n),
    u ∈ l → listMin l hl ≤ u
  | [x], _, u, hu => by rw [List.mem_singleton.mp hu]; exact le_rfl
  | x :: y :: ys, _, u, hu => by
    simp only [listMin]
    rcases List.mem_cons.mp hu with rfl | hu
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (listMin_le (y :: ys) _ u hu)

private theorem listMin_eq_of_lt {n : ℕ} {l : List (Fin n)} {hl : l ≠ []} {h : Fin n}
    (hh : h ∈ l) (hlt : ∀ u ∈ l, h ≤ u) : listMin l hl = h :=
  le_antisymm (listMin_le l hl h hh) (hlt _ (listMin_mem l hl))

private theorem mem_takeWhile_spec {α : Type*} (p : α → Bool) :
    ∀ (l : List α) {x : α}, x ∈ l.takeWhile p → x ∈ l ∧ p x = true
  | [], _, h => by simp at h
  | a :: as, x, h => by
    simp only [List.takeWhile_cons] at h
    cases hp : p a
    · simp [hp] at h
    · simp only [hp, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨List.mem_cons_self, hp⟩
      · have := mem_takeWhile_spec p as h
        exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

private theorem split_at_first_mem {α : Type*} [DecidableEq α] {l : List α} {v : α}
    (hv : v ∈ l) :
    l = l.takeWhile (· ≠ v) ++ (v :: (l.dropWhile (· ≠ v)).tail) ∧
    v ∉ l.takeWhile (· ≠ v) := by
  have htd : l.takeWhile (· ≠ v) ++ l.dropWhile (· ≠ v) = l :=
    List.takeWhile_append_dropWhile
  have hne : l.dropWhile (· ≠ v) ≠ [] := by
    intro he; rw [he, List.append_nil] at htd
    have hfalse := (mem_takeWhile_spec (fun x => decide (x ≠ v)) l (htd ▸ hv)).2
    exact of_decide_eq_true hfalse rfl
  have hhead_dw : ∀ (xs : List α) (w : α) (ws : List α),
      xs.dropWhile (· ≠ v) = w :: ws → w = v := by
    intro xs
    induction xs with
    | nil => intro _ _ h; simp at h
    | cons a as ih =>
      intro w ws h
      simp only [List.dropWhile_cons] at h
      by_cases hav : a = v
      · subst hav
        simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
          List.cons.injEq] at h
        exact h.1.symm
      · have hne' : decide (a ≠ v) = true := decide_eq_true hav
        simp only [hne', ↓reduceIte] at h
        exact ih w ws h
  have hdrop : l.dropWhile (· ≠ v) = v :: (l.dropWhile (· ≠ v)).tail := by
    cases hd : l.dropWhile (· ≠ v) with
    | nil => exact absurd hd hne
    | cons w ws =>
      have hw : w = v := hhead_dw l w ws hd
      subst hw; simp
  refine ⟨?_, fun h => of_decide_eq_true (mem_takeWhile_spec (fun x => decide (x ≠ v)) l h).2 rfl⟩
  conv_lhs => rw [← htd, hdrop]

/-- Core Mahajan–Vinay merge/split involution on `(c, rest)`. -/
private def flipHeadPair {n : ℕ} (c : Clow n) (rest : List (Clow n))
    (hhead : ∀ c' ∈ rest, c.head < c'.head) : List (Clow n) :=
  let restVerts := rest.flatMap Clow.verts
  match hfc : findFirstCollision restVerts [] c.tail with
  | none => c :: rest
  | some (pref, v, suff) =>
    if hv : v ∈ restVerts then
      match hex : extractClow v rest with
      | none => c :: rest
      | some (c', rest') =>
        let rot := rotateTo c'.verts v
        let cNew : Clow n :=
          { head := c.head
            tail := pref ++ rot ++ (v :: suff)
            lt_tail := fun u hu => by
              have hspec := (findFirstCollision_clean restVerts [] c.tail List.nodup_nil
                (fun _ h => by simp at h)).1 pref v suff hfc
              have htail_eq : c.tail = pref ++ (v :: suff) := by simpa using hspec.1
              have hc'_in : c' ∈ rest :=
                ((extractClow_spec v rest).1 c' rest' hex).2.1.mem_iff.mpr List.mem_cons_self
              simp only [List.mem_append, List.mem_cons] at hu
              rcases hu with (hu | hu) | (rfl | hu)
              · exact c.lt_tail u (htail_eq ▸ List.mem_append_left _ hu)
              · have hu' : u ∈ c'.verts := (rotateTo_perm c'.verts v).mem_iff.mp hu
                rcases List.mem_cons.mp hu' with rfl | hu''
                · exact hhead c' hc'_in
                · exact lt_trans (hhead c' hc'_in) (c'.lt_tail u hu'')
              · exact c.lt_tail u (htail_eq ▸ List.mem_append_right _ List.mem_cons_self)
              · exact c.lt_tail u (htail_eq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hu)) }
        cNew :: rest'
    else
      let a := pref.takeWhile (· ≠ v)
      let b := (pref.dropWhile (· ≠ v)).tail
      let loopVerts := v :: b
      let hStar := listMin loopVerts (List.cons_ne_nil _ _)
      let rotLoop := rotateTo loopVerts hStar
      let cStar : Clow n :=
        { head := hStar
          tail := rotLoop.tail
          lt_tail := fun u hu => by
            have hspec := (findFirstCollision_clean restVerts [] c.tail List.nodup_nil
              (fun _ h => by simp at h)).1 pref v suff hfc
            have hpref_split := (split_at_first_mem (hspec.2.1.resolve_left hv)).1
            have hloop_nd : loopVerts.Nodup := by
              have := hspec.2.2.1; rw [hpref_split] at this
              exact (List.nodup_append.mp this).2.1
            have hrot_eq : rotLoop = hStar :: rotLoop.tail := by
              obtain ⟨r, hr⟩ := rotateTo_head (listMin_mem loopVerts (List.cons_ne_nil _ _))
              dsimp only [rotLoop, hStar]
              rw [hr]
              rfl
            have hrot_nd : (hStar :: rotLoop.tail).Nodup := by
              rw [← hrot_eq]; exact (rotateTo_perm loopVerts hStar).nodup_iff.mpr hloop_nd
            have hu_rot : u ∈ rotLoop := by rw [hrot_eq]; exact List.mem_cons_of_mem _ hu
            have hu_mem : u ∈ loopVerts := (rotateTo_perm loopVerts hStar).mem_iff.mp hu_rot
            have hu_ne : u ≠ hStar := fun heq => (List.nodup_cons.mp hrot_nd).1 (heq ▸ hu)
            exact lt_of_le_of_ne (listMin_le loopVerts _ u hu_mem) hu_ne.symm }
      let cShort : Clow n :=
        { head := c.head
          tail := a ++ (v :: suff)
          lt_tail := fun u hu => by
            have hspec := (findFirstCollision_clean restVerts [] c.tail List.nodup_nil
              (fun _ h => by simp at h)).1 pref v suff hfc
            have htail_eq : c.tail = pref ++ (v :: suff) := by simpa using hspec.1
            simp only [List.mem_append, List.mem_cons] at hu
            rcases hu with hu | (rfl | hu)
            · exact c.lt_tail u
                (htail_eq ▸ List.mem_append_left _ (mem_takeWhile_spec _ _ hu).1)
            · exact c.lt_tail u (htail_eq ▸ List.mem_append_right _ List.mem_cons_self)
            · exact c.lt_tail u (htail_eq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hu)) }
      cShort :: insertClow cStar rest

private theorem flipHeadPair_eq_merge {n : ℕ} {c c' : Clow n} {rest rest' : List (Clow n)}
    {hhead : ∀ x ∈ rest, c.head < x.head} {pref : List (Fin n)} {v : Fin n} {suff : List (Fin n)}
    (hfc : findFirstCollision (rest.flatMap Clow.verts) [] c.tail = some (pref, v, suff))
    (hv : v ∈ rest.flatMap Clow.verts) (hex : extractClow v rest = some (c', rest'))
    (hlt : ∀ u ∈ pref ++ rotateTo c'.verts v ++ (v :: suff), c.head < u) :
    flipHeadPair c rest hhead =
      Clow.mk c.head (pref ++ rotateTo c'.verts v ++ (v :: suff)) hlt :: rest' := by
  unfold flipHeadPair
  dsimp only
  split
  · rename_i h; rw [h] at hfc; simp at hfc
  · rename_i pref' v' suff' h
    rw [h] at hfc
    injection hfc with h'
    obtain ⟨rfl, h''⟩ := Prod.mk.inj h'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h''
    simp only [hv, ↓reduceDIte]
    split
    · rename_i h2; rw [h2] at hex; simp at hex
    · rename_i c'' rest'' h2
      rw [h2] at hex
      injection hex with he'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
      exact congrArg₂ List.cons (Clow.ext rfl rfl) rfl

private theorem flipHeadPair_eq_split {n : ℕ} {c : Clow n} {rest : List (Clow n)}
    {hhead : ∀ x ∈ rest, c.head < x.head} {pref : List (Fin n)} {v : Fin n} {suff : List (Fin n)}
    (hfc : findFirstCollision (rest.flatMap Clow.verts) [] c.tail = some (pref, v, suff))
    (hv : v ∉ rest.flatMap Clow.verts)
    (hlt1 : ∀ u ∈ pref.takeWhile (· ≠ v) ++ (v :: suff), c.head < u)
    (hlt2 : ∀ u ∈ (rotateTo (v :: (pref.dropWhile (· ≠ v)).tail)
        (listMin (v :: (pref.dropWhile (· ≠ v)).tail) (List.cons_ne_nil _ _))).tail,
      listMin (v :: (pref.dropWhile (· ≠ v)).tail) (List.cons_ne_nil _ _) < u) :
    flipHeadPair c rest hhead =
      Clow.mk c.head (pref.takeWhile (· ≠ v) ++ (v :: suff)) hlt1 ::
        insertClow (Clow.mk (listMin (v :: (pref.dropWhile (· ≠ v)).tail) (List.cons_ne_nil _ _))
          (rotateTo (v :: (pref.dropWhile (· ≠ v)).tail)
            (listMin (v :: (pref.dropWhile (· ≠ v)).tail) (List.cons_ne_nil _ _))).tail hlt2)
          rest := by
  unfold flipHeadPair
  dsimp only
  split
  · rename_i h; rw [h] at hfc; simp at hfc
  · rename_i pref' v' suff' h
    rw [h] at hfc
    injection hfc with h'
    obtain ⟨rfl, h''⟩ := Prod.mk.inj h'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h''
    simp only [hv, ↓reduceDIte]

/-- Full Mahajan–Vinay involution on `List (Clow n)`. -/
private def flipClowList {n : ℕ} : (cs : List (Clow n)) →
    cs.Pairwise (fun a b => a.head < b.head) → List (Clow n)
  | [], _ => []
  | c :: rest, hp =>
    if (rest.flatMap Clow.verts).Nodup then
      flipHeadPair c rest (List.pairwise_cons.mp hp).1
    else
      c :: flipClowList rest (List.pairwise_cons.mp hp).2

/-- Helper proving all invariants of `flipHeadPair` (Case A merges with a clow in `rest`,
Case B splits off a simple loop from `c`, and the two cases are exact inverses). -/
private theorem flipHeadPair_props {n : ℕ} (c : Clow n) (rest : List (Clow n))
    (hp : (c :: rest).Pairwise (fun a b => a.head < b.head))
    (hrest_nd : (rest.flatMap Clow.verts).Nodup)
    (hnot_nd : ¬ ((c :: rest).flatMap Clow.verts).Nodup) :
    ∃ (cNew : Clow n) (restNew : List (Clow n)) (hheadNew : ∀ c' ∈ restNew, cNew.head < c'.head),
      flipHeadPair c rest (List.pairwise_cons.mp hp).1 = cNew :: restNew ∧
      cNew.head = c.head ∧
      (cNew :: restNew).Pairwise (fun a b => a.head < b.head) ∧
      ((cNew :: restNew).map Clow.len).sum = ((c :: rest).map Clow.len).sum ∧
      ((cNew :: restNew).flatMap Clow.edges).Perm ((c :: rest).flatMap Clow.edges) ∧
      ((cNew :: restNew).length + (c :: rest).length) % 2 = 1 ∧
      (restNew.flatMap Clow.verts).Nodup ∧
      ¬ ((cNew :: restNew).flatMap Clow.verts).Nodup ∧
      flipHeadPair cNew restNew hheadNew = c :: rest := by
  have hhead := (List.pairwise_cons.mp hp).1
  have hrest_pw := (List.pairwise_cons.mp hp).2
  let restVerts := rest.flatMap Clow.verts
  have hc_head_not_rest : c.head ∉ restVerts := by
    intro hmem
    obtain ⟨c', hc', hu⟩ := List.mem_flatMap.mp hmem
    have hlt := hhead c' hc'
    rcases List.mem_cons.mp hu with h | h
    · exact ne_of_lt hlt h
    · exact lt_irrefl _ (lt_trans hlt (c'.lt_tail _ h))
  have hc_head_not_tail : c.head ∉ c.tail := fun h => lt_irrefl _ (c.lt_tail _ h)
  -- `findFirstCollision restVerts [] c.tail` cannot be `none` since `c :: rest` is NOT nodup!
  cases hfc : findFirstCollision restVerts [] c.tail with
  | none =>
    exfalso
    have ⟨hnd_t, hdisj_t⟩ := (findFirstCollision_clean restVerts [] c.tail List.nodup_nil
      (fun _ h => by simp at h)).2 hfc
    simp only [List.reverse_nil, List.nil_append] at hnd_t
    apply hnot_nd
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨List.nodup_cons.mpr ⟨hc_head_not_tail, hnd_t⟩, hrest_nd, fun u hu w hw heq => ?_⟩
    subst heq
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hc_head_not_rest hw
    · exact hdisj_t u hu hw
  | some p =>
    rcases p with ⟨pref, v, suff⟩
    have hspec := (findFirstCollision_clean restVerts [] c.tail List.nodup_nil
      (fun _ h => by simp at h)).1 pref v suff hfc
    have htail_eq : c.tail = pref ++ (v :: suff) := by simpa using hspec.1
    have hp_nd : pref.Nodup := hspec.2.2.1
    have hp_disj : ∀ u ∈ pref, u ∉ restVerts := hspec.2.2.2
    by_cases hv : v ∈ restVerts
    · -- Case A (Merge)
      cases hex : extractClow v rest with
      | none => exact absurd hv ((extractClow_spec v rest).2 hex)
      | some q =>
        rcases q with ⟨c', rest'⟩
        have hex_s := (extractClow_spec v rest).1 c' rest' hex
        have hc'_in : c' ∈ rest := hex_s.2.1.mem_iff.mpr List.mem_cons_self
        have hperm_rv : restVerts.Perm (c'.verts ++ rest'.flatMap Clow.verts) := by
          simpa [restVerts, List.flatMap_cons] using
            hex_s.2.1.flatMap (f := Clow.verts) (fun _ _ => List.Perm.refl _)
        have hnd_split : c'.verts.Nodup ∧ (rest'.flatMap Clow.verts).Nodup ∧
            ∀ u ∈ c'.verts, u ∉ rest'.flatMap Clow.verts := by
          have := hperm_rv.nodup_iff.mp hrest_nd
          exact ⟨(List.nodup_append.mp this).1, (List.nodup_append.mp this).2.1,
            fun u hu hr => (List.nodup_append.mp this).2.2 u hu u hr rfl⟩
        have hrot_head : ∃ rotTail, rotateTo c'.verts v = v :: rotTail := rotateTo_head hex_s.1
        obtain ⟨rotTail, hrot_eq⟩ := hrot_head
        have hrot_perm : (v :: rotTail).Perm c'.verts := hrot_eq ▸ rotateTo_perm c'.verts v
        have hrot_nd : (v :: rotTail).Nodup := hrot_perm.nodup_iff.mpr hnd_split.1
        let cNew : Clow n :=
          { head := c.head
            tail := pref ++ (v :: rotTail) ++ (v :: suff)
            lt_tail := fun u hu => by
              simp only [List.mem_append, List.mem_cons] at hu
              rcases hu with (hu | (rfl | hu)) | (rfl | hu)
              · exact c.lt_tail u (htail_eq ▸ List.mem_append_left _ hu)
              · exact c.lt_tail u (htail_eq ▸ List.mem_append_right _ List.mem_cons_self)
              · have hu' : u ∈ c'.verts := hrot_perm.mem_iff.mp (List.mem_cons_of_mem _ hu)
                rcases List.mem_cons.mp hu' with rfl | hu''
                · exact hhead c' hc'_in
                · exact lt_trans (hhead c' hc'_in) (c'.lt_tail u hu'')
              · exact c.lt_tail u (htail_eq ▸ List.mem_append_right _ List.mem_cons_self)
              · exact c.lt_tail u (htail_eq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hu)) }
        have hflip_eq : flipHeadPair c rest hhead = cNew :: rest' := by
          rw [flipHeadPair_eq_merge (hhead := hhead) hfc hv hex
            (by rw [hrot_eq]; exact cNew.lt_tail)]
          exact congrArg₂ List.cons (Clow.ext rfl (by simp [cNew, hrot_eq])) rfl
        have hheadNew : ∀ x ∈ rest', cNew.head < x.head := hex_s.2.2.2 c.head hhead
        refine ⟨cNew, rest', hheadNew, hflip_eq, rfl,
          List.pairwise_cons.mpr ⟨hheadNew, hex_s.2.2.1 hrest_pw⟩, ?_, ?_, ?_, hnd_split.2.1,
          ?_, ?_⟩
        · -- Length sum preserved:
          have hlen_rot : rotTail.length + 1 = c'.len := by
            have := hrot_perm.length_eq
            simpa [Clow.verts_eq_cons, Clow.len_eq_length_tail_add_one] using this
          have hsum_rest : (rest.map Clow.len).sum = c'.len + (rest'.map Clow.len).sum := by
            simpa using (hex_s.2.1.map Clow.len).sum_eq
          have hlen_c : c.len = pref.length + 1 + suff.length + 1 := by
            simp [Clow.len_eq_length_tail_add_one, htail_eq]; omega
          have hlen_new :
              cNew.len = pref.length + (rotTail.length + 1) + (suff.length + 1) + 1 := by
            simp [cNew]; omega
          simp only [List.map_cons, List.sum_cons, hsum_rest, hlen_c, hlen_new, hlen_rot]; omega
        · -- Edge multiset preserved up to permutation:
          have h1 : cNew.edges.Perm (c.edges ++ c'.edges) := by
            have hce : c.edges = cycleEdges ((c.head :: pref) ++ (v :: suff)) := by
              simp [Clow.edges_eq_cycleEdges_verts, Clow.verts_eq_cons, htail_eq]
            have hcne :
                cNew.edges = cycleEdges ((c.head :: pref) ++ (v :: rotTail) ++ (v :: suff)) := by
              simp [cNew, Clow.edges_eq_cycleEdges_verts, List.append_assoc]
            rw [hcne, hce]
            refine (cycleEdges_splice_perm c.head v pref rotTail suff).trans ?_
            refine List.Perm.append_left _ ?_
            rw [← hrot_eq]; exact cycleEdges_rotateTo_perm c'.verts v
          have h2 : (rest.flatMap Clow.edges).Perm (c'.edges ++ rest'.flatMap Clow.edges) := by
            simpa [List.flatMap_cons] using
              hex_s.2.1.flatMap (f := Clow.edges) (fun _ _ => List.Perm.refl _)
          simp only [List.flatMap_cons]
          refine (List.Perm.append_right _ h1).trans ?_
          rw [List.append_assoc]
          exact List.Perm.append_left _ h2.symm
        · -- Length parity flipped:
          have hlen_r : rest.length = rest'.length + 1 := by
            simpa using hex_s.2.1.length_eq
          simp only [List.length_cons, hlen_r]; omega
        · -- `cNew :: rest'` is NOT nodup (since `v` repeats in `cNew.tail`!):
          intro hnd_new
          rw [List.flatMap_cons, List.nodup_append] at hnd_new
          have hcnew_nd : cNew.tail.Nodup := (List.nodup_cons.mp hnd_new.1).2
          have h1 := (List.nodup_append.mp hcnew_nd).2.2 v
            (List.mem_append_right _ List.mem_cons_self) v List.mem_cons_self
          exact h1 rfl
        · -- Involution (`flipHeadPair cNew rest' = c :: rest`):
          have hpref2_nd : (pref ++ (v :: rotTail)).Nodup := by
            rw [List.nodup_append]
            refine ⟨hp_nd, hrot_nd, fun u hu w hw heq => ?_⟩
            subst heq
            exact hp_disj u hu
              (hperm_rv.mem_iff.mpr (List.mem_append_left _ (hrot_perm.mem_iff.mp hw)))
          have hpref2_disj : ∀ u ∈ pref ++ (v :: rotTail), u ∉ rest'.flatMap Clow.verts := by
            intro u hu hr
            rcases List.mem_append.mp hu with hu | hu
            · exact hp_disj u hu (hperm_rv.mem_iff.mpr (List.mem_append_right _ hr))
            · exact hnd_split.2.2 u (hrot_perm.mem_iff.mp hu) hr
          have hfc2 : findFirstCollision (rest'.flatMap Clow.verts) [] cNew.tail =
              some (pref ++ (v :: rotTail), v, suff) := by
            simpa [cNew] using findFirstCollision_eq_some (rest'.flatMap Clow.verts)
              (pref ++ (v :: rotTail)) v suff hpref2_nd hpref2_disj [] (fun _ _ => List.not_mem_nil)
              (Or.inr (Or.inl (List.mem_append_right _ List.mem_cons_self)))
          have hv2 : v ∉ rest'.flatMap Clow.verts := hnd_split.2.2 v hex_s.1
          -- Show `a = pref`, `b = rotTail`, `cStar = c'`, `cShort = c`, and `rest` is recovered.
          have hv_not_pref : v ∉ pref := fun h => hp_disj v h hv
          have htd_pref : ∀ (xs : List (Fin n)), v ∉ xs →
              (xs ++ v :: rotTail).takeWhile (· ≠ v) = xs ∧
              ((xs ++ v :: rotTail).dropWhile (· ≠ v)).tail = rotTail := by
            intro xs hxs
            induction xs with
            | nil => simp
            | cons u us ih =>
              have huv : u ≠ v := fun h => hxs (h ▸ List.mem_cons_self)
              have ⟨h1, h2⟩ := ih (fun h => hxs (List.mem_cons_of_mem _ h))
              simp only [List.cons_append, List.takeWhile_cons, List.dropWhile_cons,
                decide_eq_true huv, ↓reduceIte, h1, h2, and_self]
          have ha_eq : (pref ++ (v :: rotTail)).takeWhile (· ≠ v) = pref :=
            (htd_pref pref hv_not_pref).1
          have hb_eq : ((pref ++ (v :: rotTail)).dropWhile (· ≠ v)).tail = rotTail :=
            (htd_pref pref hv_not_pref).2
          have hhStar : listMin (v :: rotTail) (List.cons_ne_nil _ _) = c'.head := by
            apply listMin_eq_of_lt (hrot_perm.mem_iff.mpr List.mem_cons_self)
            intro u hu
            rcases List.mem_cons.mp (hrot_perm.mem_iff.mp hu) with rfl | hu'
            · exact le_rfl
            · exact le_of_lt (c'.lt_tail u hu')
          have hrot_back : rotateTo (v :: rotTail) c'.head = c'.verts := by
            rw [← hrot_eq, rotateTo_rotateTo hnd_split.1 hex_s.1 List.mem_cons_self]
            simp [Clow.verts_eq_cons]
          have hlt1' : ∀ u ∈ (pref ++ (v :: rotTail)).takeWhile (· ≠ v) ++ (v :: suff),
              cNew.head < u := by
            rw [ha_eq, ← htail_eq]; exact c.lt_tail
          have hlt2' : ∀ u ∈ (rotateTo (v :: ((pref ++ (v :: rotTail)).dropWhile (· ≠ v)).tail)
                (listMin (v :: ((pref ++ (v :: rotTail)).dropWhile (· ≠ v)).tail)
                  (List.cons_ne_nil _ _))).tail,
              listMin (v :: ((pref ++ (v :: rotTail)).dropWhile (· ≠ v)).tail)
                (List.cons_ne_nil _ _) < u := by
            intro u hu
            simp only [hb_eq, hhStar, hrot_back, Clow.verts_eq_cons, List.tail_cons] at hu ⊢
            exact c'.lt_tail u hu
          rw [flipHeadPair_eq_split (hhead := hheadNew) hfc2 hv2 hlt1' hlt2']
          refine congrArg₂ List.cons (Clow.ext rfl ?_) ?_
          · change (pref ++ v :: rotTail).takeWhile (· ≠ v) ++ v :: suff = c.tail
            rw [ha_eq, htail_eq]
          · have hclow_eq : Clow.mk
                (listMin (v :: ((pref ++ v :: rotTail).dropWhile (· ≠ v)).tail)
                  (List.cons_ne_nil _ _))
                (rotateTo (v :: ((pref ++ v :: rotTail).dropWhile (· ≠ v)).tail)
                  (listMin (v :: ((pref ++ v :: rotTail).dropWhile (· ≠ v)).tail)
                    (List.cons_ne_nil _ _))).tail hlt2' = c' := by
              refine Clow.ext ?_ ?_
              · simp only [hb_eq]; exact hhStar
              · simp only [hb_eq, hhStar, hrot_back, Clow.verts_eq_cons, List.tail_cons]
            rw [hclow_eq]
            exact insertClow_of_extractClow hrest_pw hex
    · -- Case B (Split)
      have hv_pref : v ∈ pref := hspec.2.1.resolve_left hv
      obtain ⟨hpref_split, hv_not_a⟩ := split_at_first_mem hv_pref
      let a := pref.takeWhile (· ≠ v)
      let b := (pref.dropWhile (· ≠ v)).tail
      let loopVerts := v :: b
      let hStar := listMin loopVerts (List.cons_ne_nil _ _)
      let rotLoop := rotateTo loopVerts hStar
      have hloop_nd : loopVerts.Nodup :=
        (List.nodup_append.mp (hpref_split ▸ hp_nd)).2.1
      have ha_nd : a.Nodup := (List.nodup_append.mp (hpref_split ▸ hp_nd)).1
      have ha_disj_loop : ∀ u ∈ a, u ∉ loopVerts := fun u hu hr =>
        (List.nodup_append.mp (hpref_split ▸ hp_nd)).2.2 u hu u hr rfl
      have hrot_head : ∃ r, rotLoop = hStar :: r := rotateTo_head (listMin_mem loopVerts _)
      obtain ⟨rotT, hrot_eq⟩ := hrot_head
      have hrot_perm : rotLoop.Perm loopVerts := rotateTo_perm loopVerts hStar
      let cStar : Clow n :=
        { head := hStar, tail := rotLoop.tail,
          lt_tail := fun u hu => by
            have hrot_nd : (hStar :: rotLoop.tail).Nodup := by
              rw [← (by simp [hrot_eq] : rotLoop = hStar :: rotLoop.tail)]
              exact hrot_perm.nodup_iff.mpr hloop_nd
            have hu_m : u ∈ loopVerts := hrot_perm.mem_iff.mp
              ((by simp [hrot_eq] : rotLoop = hStar :: rotLoop.tail) ▸ List.mem_cons_of_mem _ hu)
            exact lt_of_le_of_ne (listMin_le loopVerts _ u hu_m)
              (Ne.symm fun (heq : u = hStar) => (List.nodup_cons.mp hrot_nd).1 (heq ▸ hu)) }
      let cShort : Clow n :=
        { head := c.head, tail := a ++ (v :: suff),
          lt_tail := fun u hu => by
            simp only [List.mem_append, List.mem_cons] at hu
            rcases hu with hu | (rfl | hu)
            · exact c.lt_tail u
                (htail_eq ▸ List.mem_append_left _ (mem_takeWhile_spec _ _ hu).1)
            · exact c.lt_tail u (htail_eq ▸ List.mem_append_right _ List.mem_cons_self)
            · exact c.lt_tail u (htail_eq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hu)) }
      let restNew := insertClow cStar rest
      have hflip_eq : flipHeadPair c rest hhead = cShort :: restNew :=
        flipHeadPair_eq_split (hhead := hhead) hfc hv cShort.lt_tail cStar.lt_tail
      have hcStar_verts : cStar.verts = rotLoop := by simp [cStar, hrot_eq]
      have hcStar_disj : ∀ u ∈ cStar.verts, u ∉ restVerts := fun u hu =>
        hp_disj u (hpref_split ▸ List.mem_append_right _ (hrot_perm.mem_iff.mp (hcStar_verts ▸ hu)))
      have hcStar_head_gt : c.head < cStar.head :=
        c.lt_tail _ (htail_eq ▸ List.mem_append_left _
          (hpref_split ▸ List.mem_append_right _ (listMin_mem loopVerts _)))
      have hcStar_ne_rest : ∀ c' ∈ rest, cStar.head ≠ c'.head :=
        fun c' hc' (heq : cStar.head = c'.head) =>
          hcStar_disj cStar.head List.mem_cons_self
            (heq ▸ List.mem_flatMap.mpr ⟨c', hc', List.mem_cons_self⟩)
      have hheadNew : ∀ x ∈ restNew, cShort.head < x.head := fun x hx => by
        rcases List.mem_cons.mp ((insertClow_perm cStar rest).mem_iff.mp hx) with rfl | hx
        · exact hcStar_head_gt
        · exact hhead x hx
      have hrestNew_perm_v : (restNew.flatMap Clow.verts).Perm (loopVerts ++ restVerts) :=
        ((insertClow_perm cStar rest).flatMap (f := Clow.verts) (fun _ _ => List.Perm.refl _)).trans
          (List.Perm.append_right _ (hcStar_verts ▸ hrot_perm))
      have hrestNew_nd : (restNew.flatMap Clow.verts).Nodup := by
        rw [hrestNew_perm_v.nodup_iff, List.nodup_append]
        refine ⟨hloop_nd, hrest_nd, fun u hu w hw heq => ?_⟩
        subst heq
        exact hp_disj u (hpref_split ▸ List.mem_append_right _ hu) hw
      refine ⟨cShort, restNew, hheadNew, hflip_eq, rfl,
        List.pairwise_cons.mpr ⟨hheadNew, insertClow_pairwise cStar rest hrest_pw hcStar_ne_rest⟩,
        ?_, ?_, ?_, hrestNew_nd, ?_, ?_⟩
      · -- Length sum preserved:
        have hlen_cS : cStar.len = b.length + 1 := by
          have := hrot_perm.length_eq; simpa [cStar, loopVerts, hrot_eq] using this
        have hsum_r : (restNew.map Clow.len).sum = cStar.len + (rest.map Clow.len).sum := by
          simpa using ((insertClow_perm cStar rest).map Clow.len).sum_eq
        have hlen_p : pref.length = a.length + (b.length + 1) := by
          have := congrArg List.length hpref_split
          simp only [List.length_append, List.length_cons] at this
          exact this
        simp only [List.map_cons, List.sum_cons]
        rw [hsum_r, hlen_cS]
        simp only [cShort, Clow.len_eq_length_tail_add_one, htail_eq, List.length_append,
          List.length_cons, hlen_p]
        omega
      · -- Edge multiset preserved:
        have h1 : (c.edges).Perm (cShort.edges ++ cStar.edges) := by
          have hce : c.edges = cycleEdges ((c.head :: a) ++ (v :: b) ++ (v :: suff)) := by
            simp only [Clow.edges_eq_cycleEdges_verts, Clow.verts_eq_cons]
            rw [htail_eq, hpref_split]
            simp only [List.cons_append, List.append_assoc, a, b]
          have hcse : cShort.edges = cycleEdges ((c.head :: a) ++ (v :: suff)) := by
            simp [cShort, Clow.edges_eq_cycleEdges_verts]
          rw [hce, hcse]
          refine (cycleEdges_splice_perm c.head v a b suff).trans (List.Perm.append_left _ ?_)
          rw [show cStar.edges = cycleEdges rotLoop by
            rw [Clow.edges_eq_cycleEdges_verts, hcStar_verts]]
          exact (cycleEdges_rotateTo_perm loopVerts hStar).symm
        have h2 : (restNew.flatMap Clow.edges).Perm (cStar.edges ++ rest.flatMap Clow.edges) := by
          simpa [List.flatMap_cons] using
            (insertClow_perm cStar rest).flatMap (f := Clow.edges) (fun _ _ => List.Perm.refl _)
        simp only [List.flatMap_cons]
        refine (List.Perm.append_left _ h2).trans ?_
        rw [← List.append_assoc]
        exact List.Perm.append_right _ h1.symm
      · -- Length parity flipped:
        have hlen_r : restNew.length = rest.length + 1 := by
          simpa using (insertClow_perm cStar rest).length_eq
        simp only [List.length_cons, hlen_r]; omega
      · -- `cShort :: restNew` is NOT nodup (`v ∈ cShort.verts` and `v ∈ restNew.flatMap verts`):
        intro hnd_new
        have hv1 : v ∈ cShort.verts :=
          List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
        have hv2 : v ∈ restNew.flatMap Clow.verts :=
          hrestNew_perm_v.mem_iff.mpr (List.mem_append_left _ List.mem_cons_self)
        rw [List.flatMap_cons, List.nodup_append] at hnd_new
        exact hnd_new.2.2 v hv1 v hv2 rfl
      · -- Involution (`flipHeadPair cShort restNew = c :: rest`):
        have ha_disj_new : ∀ u ∈ a, u ∉ restNew.flatMap Clow.verts := fun u hu hr => by
          rcases List.mem_append.mp (hrestNew_perm_v.mem_iff.mp hr) with hl | hr'
          · exact ha_disj_loop u hu hl
          · exact hp_disj u (hpref_split ▸ List.mem_append_left _ hu) hr'
        have hv_in_new : v ∈ restNew.flatMap Clow.verts :=
          hrestNew_perm_v.mem_iff.mpr (List.mem_append_left _ List.mem_cons_self)
        have hfc2 : findFirstCollision (restNew.flatMap Clow.verts) [] cShort.tail =
            some (a, v, suff) := by
          simpa [cShort] using findFirstCollision_eq_some (restNew.flatMap Clow.verts) a v suff
            ha_nd ha_disj_new [] (fun _ _ => List.not_mem_nil) (Or.inl hv_in_new)
        have hex2 : extractClow v restNew = some (cStar, rest) :=
          extractClow_insertClow (hcStar_verts ▸ hrot_perm.mem_iff.mpr List.mem_cons_self) hv
        have hrot_back : rotateTo cStar.verts v = loopVerts := by
          rw [hcStar_verts,
            rotateTo_rotateTo hloop_nd (listMin_mem loopVerts _) List.mem_cons_self]
          simp [loopVerts]
        have htail_back : a ++ rotateTo cStar.verts v ++ (v :: suff) = c.tail := by
          rw [hrot_back, htail_eq, hpref_split]
        rw [flipHeadPair_eq_merge (hhead := hheadNew) hfc2 hv_in_new hex2
          (by rw [htail_back]; exact c.lt_tail)]
        exact congrArg₂ List.cons (Clow.ext rfl htail_back) rfl

/-- Sum of `w.signedWeight M` over all clow sequences equals `M.det`. -/
public theorem sum_clowSeq_eq_det {n : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) :
    let _ : Fintype (ClowSeq n) := @Fintype.ofFinite _ (clowSeq_finite n)
    ∑ w : ClowSeq n, w.signedWeight M = M.det := by
  let _ : Fintype (ClowSeq n) := @Fintype.ofFinite _ (clowSeq_finite n)
  dsimp only
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun w : ClowSeq n => w.IsCycleCover),
    sum_cycleCover_eq_det M]
  suffices hzero :
      ∑ w ∈ Finset.univ.filter (fun w : ClowSeq n => ¬ w.IsCycleCover), w.signedWeight M = 0 by
    rw [hzero, add_zero]
  -- Define the involution on `{w : ClowSeq n | ¬ w.IsCycleCover}` via `flipClowList`.
  have hflip : ∀ (cs : List (Clow n)) (hp : cs.Pairwise (fun a b => a.head < b.head)),
      ¬ (cs.flatMap Clow.verts).Nodup →
      let res := flipClowList cs hp
      ∃ (hp' : res.Pairwise (fun a b => a.head < b.head)),
        (res.map Clow.len).sum = (cs.map Clow.len).sum ∧
        (res.flatMap Clow.edges).Perm (cs.flatMap Clow.edges) ∧
        (res.length + cs.length) % 2 = 1 ∧
        ¬ (res.flatMap Clow.verts).Nodup ∧
        flipClowList res hp' = cs := by
    intro cs
    induction cs with
    | nil => intro _ hnd; exact absurd List.nodup_nil hnd
    | cons c rest ih =>
      intro hp hnd
      by_cases hrest_nd : (rest.flatMap Clow.verts).Nodup
      · dsimp only
        simp only [flipClowList, hrest_nd, ↓reduceIte]
        obtain ⟨cNew, restNew, hheadNew, hfeq, -, hpw', hlen', hedge', hpar', hrestNew_nd,
          hnot', hinv⟩ := flipHeadPair_props c rest hp hrest_nd hnd
        have hgoal : ∀ (l : List (Clow n)) (hl : l.Pairwise (fun a b => a.head < b.head)),
            l = cNew :: restNew → flipClowList l hl = c :: rest := by
          rintro _ _ rfl
          simp only [flipClowList, hrestNew_nd, ↓reduceIte]
          exact hinv
        exact ⟨hfeq.symm ▸ hpw', hfeq.symm ▸ hlen', hfeq.symm ▸ hedge',
          hfeq.symm ▸ hpar', hfeq.symm ▸ hnot', hgoal _ _ hfeq⟩
      · dsimp only
        simp only [flipClowList, hrest_nd, ↓reduceIte]
        have hhead := (List.pairwise_cons.mp hp).1
        have hrest_pw := (List.pairwise_cons.mp hp).2
        obtain ⟨hp'_r, hlen_r, hedge_r, hpar_r, hnot_r, hinv_r⟩ := ih hrest_pw hrest_nd
        -- Show all heads in `flipClowList rest` remain strictly `> c.head`:
        have hhead_pres : ∀ (l : List (Clow n)) (hpl : l.Pairwise (fun a b => a.head < b.head)),
            ¬ (l.flatMap Clow.verts).Nodup →
            ∀ x : Fin n, (∀ y ∈ l, x < y.head) → ∀ y ∈ flipClowList l hpl, x < y.head := by
          intro l
          induction l with
          | nil => intro _ h; exact absurd List.nodup_nil h
          | cons d ds ihd =>
            intro hpl hndl x hx y hy
            by_cases hds : (ds.flatMap Clow.verts).Nodup
            · simp only [flipClowList, hds, ↓reduceIte] at hy
              obtain ⟨cN, rN, hhdN, hfeq', hchd', hpwN, _, _, _, _, _, _⟩ :=
                flipHeadPair_props d ds hpl hds hndl
              rw [hfeq'] at hy
              rcases List.mem_cons.mp hy with rfl | hy'
              · rw [hchd']; exact hx d List.mem_cons_self
              · exact lt_trans (hx d List.mem_cons_self) (hchd' ▸ hhdN y hy')
            · simp only [flipClowList, hds, ↓reduceIte] at hy
              rcases List.mem_cons.mp hy with rfl | hy'
              · exact hx _ List.mem_cons_self
              · exact ihd (List.pairwise_cons.mp hpl).2 hds x
                  (fun z hz => hx z (List.mem_cons_of_mem _ hz)) y hy'
        have hpw' : (c :: flipClowList rest hrest_pw).Pairwise (fun a b => a.head < b.head) :=
          List.pairwise_cons.mpr ⟨hhead_pres rest hrest_pw hrest_nd c.head hhead, hp'_r⟩
        refine ⟨hpw', by simp [hlen_r], List.Perm.append_left _ hedge_r, by simp; omega, ?_, ?_⟩
        · intro hnd'
          exact hnot_r (List.nodup_append.mp (by simpa [List.flatMap_cons] using hnd')).2.1
        · simp only [hnot_r, ↓reduceIte, hinv_r]
  let inv : (w : ClowSeq n) →
      w ∈ Finset.univ.filter (fun w : ClowSeq n => ¬ w.IsCycleCover) → ClowSeq n :=
    fun w hw =>
      let hnd : ¬ (w.clows.flatMap Clow.verts).Nodup := (Finset.mem_filter.mp hw).2
      let h := hflip w.clows w.heads_strict hnd
      ⟨flipClowList w.clows w.heads_strict, h.choose, h.choose_spec.1.trans w.len_sum⟩
  refine Finset.sum_involution inv ?_ ?_ ?_ ?_
  · intro w hw
    have hnd : ¬ (w.clows.flatMap Clow.verts).Nodup := (Finset.mem_filter.mp hw).2
    have hs := (hflip w.clows w.heads_strict hnd).choose_spec
    simp only [inv, ClowSeq.signedWeight_eq]
    have hprod : ((flipClowList w.clows w.heads_strict).map (Clow.weight M)).prod =
        (w.clows.map (Clow.weight M)).prod := by
      have h1 : ∀ cs : List (Clow n), (cs.map (Clow.weight M)).prod =
          ((cs.flatMap Clow.edges).map fun p => M p.1 p.2).prod := fun cs => by
        induction cs with
        | nil => simp
        | cons c cs ih =>
          simp only [List.map_cons, List.prod_cons, List.flatMap_cons, List.map_append,
            List.prod_append, ih, Clow.weight_eq_prod_edges]
      rw [h1, h1]
      exact (hs.2.1.map _).prod_eq
    rw [hprod]
    have hneg : (-1 : R) ^ (n + (flipClowList w.clows w.heads_strict).length) =
        -((-1 : R) ^ (n + w.clows.length)) := by
      have hpar := hs.2.2.1
      rcases Nat.mod_two_eq_zero_or_one (n + w.clows.length) with ha | ha
      · have hb : (n + (flipClowList w.clows w.heads_strict).length) % 2 = 1 := by omega
        rw [Even.neg_one_pow (Nat.even_iff.mpr ha), Odd.neg_one_pow (Nat.odd_iff.mpr hb)]
      · have hb : (n + (flipClowList w.clows w.heads_strict).length) % 2 = 0 := by omega
        rw [Odd.neg_one_pow (Nat.odd_iff.mpr ha), Even.neg_one_pow (Nat.even_iff.mpr hb)]; ring
    rw [hneg]; ring
  · intro w hw _ hne
    have hnd : ¬ (w.clows.flatMap Clow.verts).Nodup := (Finset.mem_filter.mp hw).2
    have hpar := (hflip w.clows w.heads_strict hnd).choose_spec.2.2.1
    have hlen_eq : (flipClowList w.clows w.heads_strict).length = w.clows.length :=
      congrArg (fun x : ClowSeq n => x.clows.length) hne
    omega
  · intro w hw
    have hnd : ¬ (w.clows.flatMap Clow.verts).Nodup := (Finset.mem_filter.mp hw).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (hflip w.clows w.heads_strict hnd).choose_spec.2.2.2.1⟩
  · intro w hw
    have hnd : ¬ (w.clows.flatMap Clow.verts).Nodup := (Finset.mem_filter.mp hw).2
    have hs := (hflip w.clows w.heads_strict hnd).choose_spec
    have hw' : inv w hw ∈ Finset.univ.filter (fun w : ClowSeq n => ¬ w.IsCycleCover) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.2.2.2.1⟩
    have hcl : (inv (inv w hw) hw').clows = w.clows := hs.2.2.2.2
    cases w; dsimp only [inv] at hcl ⊢; simp [hcl]


end Clows

end CslibFrontier.Computability.Circuit
