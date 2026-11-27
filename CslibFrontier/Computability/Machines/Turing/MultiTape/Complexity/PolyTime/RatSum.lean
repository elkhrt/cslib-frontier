/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Lemmas

/-!
# Polynomial-time summation of rational lists

This module proves that summing a list of binary-encoded rational numbers (`List.sum : List ℚ → ℚ`)
is computable in polynomial time under `Turing.MultiTapeTM.encRat`, using a common-denominator
evaluation that avoids denominator blowup from sequential pairwise additions.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.rat_sum`: `List.sum` on `List ℚ` is computable in
  polynomial time.
* `Turing.MultiTapeTM.ComputableInPolyTime.rat_sum'`: composition form of `rat_sum`.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Common-denominator formula for summing a list of rational numbers in polynomial time. -/
private def ratSumAux (l : List ℚ) : ℚ :=
  let D : ℤ := (l.map fun q ↦ (q.den : ℤ)).prod
  let N : ℤ := (l.zipIdx.map fun p ↦
    p.1.num * ((l.zipIdx.filter fun r ↦ decide (r.2 ≠ p.2)).map fun r ↦ (r.1.den : ℤ)).prod).sum
  Rat.divInt N D

private lemma prod_filter_ne_mul (l : List ℚ) (i : ℕ) (hi : i < l.length) :
    (l[i].den : ℤ) * ((l.zipIdx.filter fun r ↦ decide (r.2 ≠ i)).map fun r ↦ (r.1.den : ℤ)).prod =
      (l.map fun q ↦ (q.den : ℤ)).prod := by
  have haux : ∀ (m : List ℚ) (k idx : ℕ),
      (∀ r ∈ m.zipIdx k, r.2 = idx → False) →
      ((m.zipIdx k).filter fun r ↦ decide (r.2 ≠ idx)).map (fun r ↦ (r.1.den : ℤ)) =
        m.map (fun q ↦ (q.den : ℤ)) := by
    intro m k idx hk
    have hfilt : (m.zipIdx k).filter (fun r ↦ decide (r.2 ≠ idx)) = m.zipIdx k :=
      List.filter_eq_self.mpr fun r hr ↦ decide_eq_true (fun h ↦ hk r hr h)
    rw [hfilt]
    clear hk hfilt
    induction m generalizing k with
    | nil => rfl
    | cons a as ih => simp [List.zipIdx_cons, ih]
  have hsplit : ∀ (m : List ℚ) (k j : ℕ) (hj : j < m.length),
      (m[j].den : ℤ) *
        (((m.zipIdx k).filter fun r ↦ decide (r.2 ≠ k + j)).map fun r ↦ (r.1.den : ℤ)).prod =
      (m.map fun q ↦ (q.den : ℤ)).prod := by
    intro m
    induction m with
    | nil => intro _ _ hj; simp at hj
    | cons a as ih =>
      intro k j hj
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, List.zipIdx_cons, List.filter_cons,
          Nat.add_zero, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
          List.map_cons, List.prod_cons]
        congr 2
        refine haux as (k + 1) k fun r hr heq ↦ ?_
        have hge := List.le_snd_of_mem_zipIdx hr
        omega
      | succ j' =>
        have hj' : j' < as.length := by simpa using hj
        have hne : k ≠ k + (j' + 1) := by omega
        simp only [List.getElem_cons_succ, List.zipIdx_cons, List.filter_cons]
        rw [decide_eq_true hne]
        simp only [↓reduceIte, List.map_cons, List.prod_cons]
        have hih := ih (k + 1) j' hj'
        have heq_idx : k + 1 + j' = k + (j' + 1) := by omega
        rw [heq_idx] at hih
        rw [← mul_left_comm, hih]
  simpa using hsplit l 0 i hi

private lemma ratSumAux_eq_sum (l : List ℚ) : ratSumAux l = l.sum := by
  unfold ratSumAux
  set D : ℤ := (l.map fun q ↦ (q.den : ℤ)).prod
  have hDpos : 0 < D := by
    refine List.prod_pos fun x hx ↦ ?_
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
    exact Nat.cast_pos.mpr q.pos
  have hDne : (D : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hDpos)
  rw [Rat.divInt_eq_div]
  apply (div_eq_iff hDne).mpr
  symm
  have hsum_zip : l.sum = (l.zipIdx.map Prod.fst).sum := by
    congr 1
    have hmap_fst : ∀ (m : List ℚ) (k : ℕ), (m.zipIdx k).map Prod.fst = m := by
      intro m
      induction m with
      | nil => intro _; rfl
      | cons a as ih => intro k; simp [List.zipIdx_cons, ih]
    exact (hmap_fst l 0).symm
  have hmul_sum : ∀ (m : List ℚ) (c : ℚ), m.sum * c = (m.map (· * c)).sum := by
    intro m c
    induction m with
    | nil => simp
    | cons a as ih => simp [add_mul, ih]
  have hcast_sum : ∀ m : List ℤ, ((m.sum : ℤ) : ℚ) = (m.map Int.cast).sum := by
    intro m
    induction m with
    | nil => simp
    | cons a as ih => simp [ih]
  rw [hsum_zip, hmul_sum, hcast_sum, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun p hp ↦ ?_
  obtain ⟨hi, hp_eq⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hp)
  have hmul := prod_filter_ne_mul l p.2 hi
  rw [hp_eq] at hmul
  have hmulQ : ((p.1.den : ℤ) : ℚ) *
      (((l.zipIdx.filter fun r ↦ decide (r.2 ≠ p.2)).map fun r ↦ (r.1.den : ℤ)).prod : ℚ) =
      (D : ℚ) := by exact_mod_cast hmul
  simp only [Function.comp_apply, Int.cast_mul]
  rw [← hmulQ, ← mul_assoc]
  have hq : p.1 * (p.1.den : ℚ) = (p.1.num : ℚ) := Rat.mul_den_eq_num p.1
  simp only [Int.cast_natCast, hq]

/-- Summing a list of binary-encoded rational numbers is computable in polynomial time. -/
@[fun_prop]
theorem rat_sum : ComputableInPolyTime List.sum (encList encRat) encRat := by
  have haux : ComputableInPolyTime ratSumAux (encList encRat) encRat := by
    unfold ratSumAux
    fun_prop
  exact haux.of_enc_eq fun l ↦ congrArg encRat (ratSumAux_eq_sum l).symm

/-- Composition form of `rat_sum`. -/
@[fun_prop]
theorem rat_sum' {α : Type} {encIn : α ↪ List Bool} {f : α → List ℚ}
    (hf : ComputableInPolyTime f encIn (encList encRat)) :
    ComputableInPolyTime (fun x ↦ (f x).sum) encIn encRat :=
  rat_sum.comp hf

end Turing.MultiTapeTM.ComputableInPolyTime
