module

public import CslibFrontier.Computability.Complexity.Parameterized.PolytopeProximity

import CslibFrontier.Algorithms.LinearAlgebra.BareissElimination
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.PolyTime.Int.DotProduct
import CslibFrontier.Computability.PolyTime.LinearAlgebra.RationalElimination
import Mathlib.Data.Rat.Floor
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import CslibFrontier.Computability.Complexity.Parameterized.FPTIterate

/-!
# FPT-Time Feasibility of Bounded-Coefficient Integer Linear Programming

Constructs a fixed-parameter-tractable (FPT) multi-tape Turing machine decision procedure for
`CslibFrontier.Complexity.BoundedCoeffILP` parameterized by `ilpParam = numVars + maxAbsCoeff`.

## Main definitions

- `CslibFrontier.Complexity.solveBoundedCoeffILP`: executable FPT-time feasibility decision
  procedure.

## Main results

- `CslibFrontier.Complexity.solveBoundedCoeffILP_eq_true_iff`: exact soundness and completeness.
- `CslibFrontier.Complexity.computableInFPTTime_solveBoundedCoeffILP`: `solveBoundedCoeffILP` runs
  in FPT time parameterized by `ilpParam`.
- `CslibFrontier.Complexity.BoundedCoeffILP_mem_FPT`:
  `BoundedCoeffILP ∈ FPT encBoundedCoeffILP ilpParam`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.Complexity Cslib.LinearAlgebra Turing.MultiTapeTM ComputableInPolyTime Matrix
open Mathlib.Tactic.Matrix
open scoped BoundedCoeffILPInstance RatTable LinearSystemInput LinearSolveResult

/-! ### 1. Row Normalization, Deduplication, and Polytope Construction -/

private def normRow (p : ℕ) (r : List ℤ) : List ℤ :=
  (List.range p).map fun j ↦ r.getD j 0

private def dedupInsert (acc : List (List ℤ × ℤ)) (row : List ℤ × ℤ) : List (List ℤ × ℤ) :=
  if acc.any (fun r ↦ decide (r.1 = row.1)) then
    acc.map fun r ↦ if r.1 = row.1 then (r.1, min r.2 row.2) else r
  else
    row :: acc

private def rawPolyRows (inst : BoundedCoeffILPInstance) : List (List ℤ × ℤ) :=
  (List.range inst.rows.length).map fun i ↦
    (normRow inst.numVars (inst.rows.getD i []), inst.rhs.getD i 0)

private def dedupRows (inst : BoundedCoeffILPInstance) : List (List ℤ × ℤ) :=
  (rawPolyRows inst).foldl dedupInsert []

private def unitRow (p j : ℕ) (val : ℤ) : List ℤ :=
  (List.range p).map fun k ↦ if k = j then val else 0

private def allPolyRows (inst : BoundedCoeffILPInstance) : List (List ℤ × ℤ) :=
  dedupRows inst ++
    (List.range inst.numVars).map (fun j ↦ (unitRow inst.numVars j 1, inst.upper.getD j 0)) ++
    (List.range inst.numVars).map (fun j ↦ (unitRow inst.numVars j (-1), -inst.lower.getD j 0))

private theorem list_getD_eq {α : Type*} (l : List α) (d : α) (i : ℕ) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem list_getD_default {α : Type*} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private theorem sum_map_range_eq_sum_fin {α : Type*} [AddCommMonoid α] (p : ℕ) (f : ℕ → α) :
    ((List.range p).map f).sum = ∑ j : Fin p, f j.1 := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ih, Fin.sum_univ_castSucc]; rfl

private theorem normRow_getD (p : ℕ) (r : List ℤ) (j : ℕ) (hj : j < p) :
    (normRow p r).getD j 0 = r.getD j 0 := by
  unfold normRow
  rw [list_getD_eq _ _ _ (by simp [hj]), List.getElem_map, List.getElem_range]

private theorem normRow_length (p : ℕ) (r : List ℤ) : (normRow p r).length = p := by
  simp [normRow]

private theorem unitRow_getD (p j k : ℕ) (val : ℤ) (hk : k < p) :
    (unitRow p j val).getD k 0 = if k = j then val else 0 := by
  unfold unitRow
  rw [list_getD_eq _ _ _ (by simp [hk]), List.getElem_map, List.getElem_range]

private theorem dedupInsert_props (acc : List (List ℤ × ℤ)) (row : List ℤ × ℤ) :
    (∀ r ∈ dedupInsert acc row, r.1 ∈ row.1 :: acc.map Prod.fst) ∧
    (∀ r ∈ dedupInsert acc row, r.2 ∈ row.2 :: acc.map Prod.snd) ∧
    (dedupInsert acc row).length ≤ acc.length + 1 ∧
    (acc.Pairwise (fun a b ↦ a.1 ≠ b.1) →
      (dedupInsert acc row).Pairwise (fun a b ↦ a.1 ≠ b.1)) ∧
    ∀ (p : ℕ) (y : Fin p → ℚ),
      (∀ r ∈ dedupInsert acc row, ∑ j : Fin p, (r.1.getD j.1 0 : ℚ) * y j ≤ (r.2 : ℚ)) ↔
      (∑ j : Fin p, (row.1.getD j.1 0 : ℚ) * y j ≤ (row.2 : ℚ) ∧
        ∀ r ∈ acc, ∑ j : Fin p, (r.1.getD j.1 0 : ℚ) * y j ≤ (r.2 : ℚ)) := by
  unfold dedupInsert
  split_ifs with hany
  · have hex : ∃ r ∈ acc, r.1 = row.1 := by
      simpa [List.any_eq_true, decide_eq_true_eq] using hany
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
      split_ifs <;> exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r0, hr0, rfl⟩)
    · intro r hr
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
      split_ifs with h
      · rcases min_choice r0.2 row.2 with hmin | hmin
        · dsimp only; rw [hmin]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hr0)
        · dsimp only; rw [hmin]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hr0)
    · simp
    · intro hpw
      have hmap : ∀ (l : List (List ℤ × ℤ)), l.Pairwise (fun a b ↦ a.1 ≠ b.1) →
          (l.map fun r ↦ if r.1 = row.1 then (r.1, min r.2 row.2) else r).Pairwise
            (fun a b ↦ a.1 ≠ b.1) := by
        intro l hl
        rw [List.pairwise_map]
        refine hl.imp fun {a b} hab ↦ ?_
        split_ifs <;> exact hab
      exact hmap acc hpw
    · intro p y
      constructor
      · intro hall
        refine ⟨?_, fun r hr ↦ ?_⟩
        · obtain ⟨r0, hr0, heq⟩ := hex
          have hmem : (r0.1, min r0.2 row.2) ∈
              acc.map (fun r ↦ if r.1 = row.1 then (r.1, min r.2 row.2) else r) :=
            List.mem_map.mpr ⟨r0, hr0, by simp [heq]⟩
          have hle := hall _ hmem
          rw [heq] at hle
          exact hle.trans (by exact_mod_cast min_le_right r0.2 row.2)
        · have hmem : (if r.1 = row.1 then (r.1, min r.2 row.2) else r) ∈
              acc.map (fun r ↦ if r.1 = row.1 then (r.1, min r.2 row.2) else r) :=
            List.mem_map.mpr ⟨r, hr, rfl⟩
          have hle := hall _ hmem
          split_ifs at hle with h
          · exact hle.trans (by exact_mod_cast min_le_left r.2 row.2)
          · exact hle
      · rintro ⟨hrow, hacc⟩ r hr
        obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
        split_ifs with h
        · dsimp only
          have h1 := hacc r0 hr0
          rw [h] at h1 ⊢
          rcases min_choice r0.2 row.2 with hmin | hmin <;> rw [hmin]
          · exact h1
          · exact hrow
        · exact hacc r0 hr0
  · have hnot : ∀ r ∈ acc, r.1 ≠ row.1 := by
      intro r hr h
      exact hany (List.any_eq_true.mpr ⟨r, hr, decide_eq_true h⟩)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hr')
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hr')
    · simp
    · intro hpw
      exact List.pairwise_cons.mpr ⟨fun r hr ↦ (hnot r hr).symm, hpw⟩
    · intro p y
      simp only [List.mem_cons, forall_eq_or_imp]

private theorem dedupRows_props (inst : BoundedCoeffILPInstance) :
    (dedupRows inst).Pairwise (fun a b ↦ a.1 ≠ b.1) ∧
    (∀ r ∈ dedupRows inst, r.1.length = inst.numVars ∧
      ∀ j : Fin inst.numVars, (r.1.getD j.1 0).natAbs ≤ maxAbsCoeff inst) ∧
    ∀ y : Fin inst.numVars → ℚ,
      (∀ r ∈ dedupRows inst, ∑ j : Fin inst.numVars, (r.1.getD j.1 0 : ℚ) * y j ≤ (r.2 : ℚ)) ↔
      (∀ i : Fin inst.rows.length,
        ∑ j : Fin inst.numVars, ((inst.rows.getD i.1 []).getD j.1 0 : ℚ) * y j ≤
          (inst.rhs.getD i.1 0 : ℚ)) := by
  have hfold : ∀ (l : List (List ℤ × ℤ)) (acc : List (List ℤ × ℤ)),
      acc.Pairwise (fun a b ↦ a.1 ≠ b.1) →
      (l.foldl dedupInsert acc).Pairwise (fun a b ↦ a.1 ≠ b.1) ∧
      (∀ r ∈ l.foldl dedupInsert acc, r.1 ∈ l.map Prod.fst ∨ r.1 ∈ acc.map Prod.fst) ∧
      ∀ y : Fin inst.numVars → ℚ,
        (∀ r ∈ l.foldl dedupInsert acc, ∑ j, (r.1.getD j.1 0 : ℚ) * y j ≤ (r.2 : ℚ)) ↔
        ((∀ r ∈ l, ∑ j, (r.1.getD j.1 0 : ℚ) * y j ≤ (r.2 : ℚ)) ∧
         (∀ r ∈ acc, ∑ j, (r.1.getD j.1 0 : ℚ) * y j ≤ (r.2 : ℚ))) := by
    intro l
    induction l with
    | nil => intro acc hpw; exact ⟨hpw, fun r hr ↦ Or.inr (List.mem_map_of_mem hr), fun _ ↦ by simp⟩
    | cons hd tl ih =>
      intro acc hpw
      have hstep := dedupInsert_props acc hd
      obtain ⟨hpw', hmem', hiff'⟩ := ih (dedupInsert acc hd) (hstep.2.2.2.1 hpw)
      refine ⟨hpw', fun r hr ↦ ?_, fun y ↦ ?_⟩
      · rcases hmem' r hr with h1 | h2
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · obtain ⟨r0, hr0, hr0_eq⟩ := List.mem_map.mp h2
          rw [← hr0_eq]
          rcases List.mem_cons.mp (hstep.1 r0 hr0) with heq | hacc
          · exact Or.inl (heq ▸ List.mem_cons_self)
          · exact Or.inr hacc
      · rw [List.foldl_cons, hiff', hstep.2.2.2.2]
        simp only [List.mem_cons, forall_eq_or_imp]
        tauto
  obtain ⟨hpw, hmem, hiff⟩ := hfold (rawPolyRows inst) [] List.Pairwise.nil
  refine ⟨hpw, fun r hr ↦ ?_, fun y ↦ ?_⟩
  · have hr1 := (hmem r hr).resolve_right (by simp)
    obtain ⟨r0, hr0, heq⟩ := List.mem_map.mp hr1
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr0
    have hi_lt : i < inst.rows.length := List.mem_range.mp hi
    rw [← heq]
    refine ⟨normRow_length _ _, fun j ↦ ?_⟩
    rw [normRow_getD _ _ _ j.isLt]
    exact le_maxAbsCoeff inst ⟨i, hi_lt⟩ j
  · unfold dedupRows; rw [hiff]
    simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, rawPolyRows,
      List.mem_map, List.mem_range, forall_exists_index, and_imp]
    constructor
    · intro h i
      have := h _ i.1 i.isLt rfl
      refine (Eq.trans_le (Finset.sum_congr rfl fun j _ ↦ ?_) this)
      rw [normRow_getD _ _ _ j.isLt]
    · rintro h _ i hi rfl
      refine (Eq.trans_le (Finset.sum_congr rfl fun j _ ↦ ?_) (h ⟨i, hi⟩))
      rw [normRow_getD _ _ _ j.isLt]

private theorem dedupRows_length_le (inst : BoundedCoeffILPInstance) :
    (dedupRows inst).length ≤ (2 * maxAbsCoeff inst + 1) ^ inst.numVars := by
  let W := maxAbsCoeff inst
  let p := inst.numVars
  let rows := dedupRows inst
  obtain ⟨hpw, hbd, _⟩ := dedupRows_props inst
  let φ : Fin rows.length → (Fin p → Fin (2 * W + 1)) := fun i j ↦
    ⟨((rows[i.1].1.getD j.1 0) + (W : ℤ)).toNat, by
      have h1 : (rows[i.1].1.getD j.1 0).natAbs ≤ W :=
        (hbd rows[i.1] (List.getElem_mem i.isLt)).2 j
      have h2 : -(W : ℤ) ≤ rows[i.1].1.getD j.1 0 := by omega
      have h3 : rows[i.1].1.getD j.1 0 ≤ (W : ℤ) := by omega
      omega⟩
  have hinj : Function.Injective φ := by
    intro i1 i2 heq
    by_contra hne
    have hneq_val : i1.1 ≠ i2.1 := fun h ↦ hne (Fin.ext h)
    have hrow_ne : rows[i1.1].1 ≠ rows[i2.1].1 := by
      rcases lt_or_gt_of_ne hneq_val with hlt | hgt
      · exact List.pairwise_iff_getElem.mp hpw i1.1 i2.1 i1.isLt i2.isLt hlt
      · exact (List.pairwise_iff_getElem.mp hpw i2.1 i1.1 i2.isLt i1.isLt hgt).symm
    have hlen1 : rows[i1.1].1.length = p := (hbd _ (List.getElem_mem i1.isLt)).1
    have hlen2 : rows[i2.1].1.length = p := (hbd _ (List.getElem_mem i2.isLt)).1
    apply hrow_ne
    apply List.ext_getElem (by omega)
    intro j hj1 hj2
    have h1 := congrFun heq ⟨j, by omega⟩
    have hv : ((rows[i1.1].1.getD j 0) + (W : ℤ)).toNat =
        ((rows[i2.1].1.getD j 0) + (W : ℤ)).toNat := congrArg Fin.val h1
    have hb1 : (rows[i1.1].1.getD j 0).natAbs ≤ W :=
      (hbd _ (List.getElem_mem i1.isLt)).2 ⟨j, by omega⟩
    have hb2 : (rows[i2.1].1.getD j 0).natAbs ≤ W :=
      (hbd _ (List.getElem_mem i2.isLt)).2 ⟨j, by omega⟩
    have hget : rows[i1.1].1.getD j 0 = rows[i2.1].1.getD j 0 := by omega
    rwa [list_getD_eq _ _ _ hj1, list_getD_eq _ _ _ hj2] at hget
  have hcard := Fintype.card_le_of_injective φ hinj
  simpa [Fintype.card_pi, Fintype.card_fin] using hcard

private theorem allPolyRows_iff (inst : BoundedCoeffILPInstance) (y : Fin inst.numVars → ℚ) :
    (∀ r ∈ allPolyRows inst, ∑ j : Fin inst.numVars, (r.1.getD j.1 0 : ℚ) * y j ≤ (r.2 : ℚ)) ↔
      inst.IsFeasibleRat y := by
  unfold allPolyRows
  simp only [List.mem_append, List.mem_map, List.mem_range]
  have hdd := (dedupRows_props inst).2.2 y
  have hU : (∀ r, (∃ j < inst.numVars, (unitRow inst.numVars j 1, inst.upper.getD j 0) = r) →
      ∑ k : Fin inst.numVars, (r.1.getD k.1 0 : ℚ) * y k ≤ (r.2 : ℚ)) ↔
      ∀ j : Fin inst.numVars, y j ≤ (inst.upper.getD j.1 0 : ℚ) := by
    have hunitSum : ∀ (j : Fin inst.numVars) (val : ℤ),
        ∑ k : Fin inst.numVars, ((unitRow inst.numVars j.1 val).getD k.1 0 : ℚ) * y k =
          (val : ℚ) * y j := fun j val ↦ by
      rw [Finset.sum_eq_single j]
      · rw [unitRow_getD _ _ _ _ j.isLt]; simp
      · intro k _ hk; rw [unitRow_getD _ _ _ _ k.isLt]; simp [Fin.val_ne_of_ne hk]
      · exact fun h' ↦ absurd (Finset.mem_univ j) h'
    constructor
    · intro h j
      have := h _ ⟨j.1, j.isLt, rfl⟩
      rw [hunitSum j 1, Int.cast_one, one_mul] at this; exact this
    · rintro h _ ⟨j, hj, rfl⟩
      rw [hunitSum ⟨j, hj⟩ 1, Int.cast_one, one_mul]; exact h ⟨j, hj⟩
  have hL : (∀ r, (∃ j < inst.numVars, (unitRow inst.numVars j (-1), -inst.lower.getD j 0) = r) →
      ∑ k : Fin inst.numVars, (r.1.getD k.1 0 : ℚ) * y k ≤ (r.2 : ℚ)) ↔
      ∀ j : Fin inst.numVars, (inst.lower.getD j.1 0 : ℚ) ≤ y j := by
    have hunitSum : ∀ (j : Fin inst.numVars),
        ∑ k : Fin inst.numVars, ((unitRow inst.numVars j.1 (-1)).getD k.1 0 : ℚ) * y k = -y j :=
      fun j ↦ by
        rw [Finset.sum_eq_single j]
        · rw [unitRow_getD _ _ _ _ j.isLt]; simp
        · intro k _ hk; rw [unitRow_getD _ _ _ _ k.isLt]; simp [Fin.val_ne_of_ne hk]
        · exact fun h' ↦ absurd (Finset.mem_univ j) h'
    constructor
    · intro h j
      have := h _ ⟨j.1, j.isLt, rfl⟩; rw [hunitSum j] at this; push_cast at this; linarith
    · rintro h _ ⟨j, hj, rfl⟩
      rw [hunitSum ⟨j, hj⟩]; push_cast; linarith [h ⟨j, hj⟩]
  constructor
  · intro hall
    refine ⟨fun j ↦ ⟨?_, ?_⟩, ?_⟩
    · exact hL.mp (fun r hr ↦ hall r (Or.inr hr)) j
    · exact hU.mp (fun r hr ↦ hall r (Or.inl (Or.inr hr))) j
    · exact hdd.mp (fun r hr ↦ hall r (Or.inl (Or.inl hr)))
  · rintro ⟨hbox, hrows⟩ r ((hr | hr) | hr)
    · exact hdd.mpr hrows r hr
    · exact hU.mpr (fun j ↦ (hbox j).2) r hr
    · exact hL.mpr (fun j ↦ (hbox j).1) r hr

/-! ### 2. Base-`q` Tuple Decoder and Feasibility Checkers -/

private def decodeDigits (base len idx : ℕ) : List ℕ :=
  ((List.range len).foldl (fun (st : ℕ × List ℕ) _ ↦ (st.1 / base, (st.1 % base) :: st.2))
    (idx, [])).2

private theorem decodeDigits_step (base len idx : ℕ) :
    ((List.range len).foldl (fun (st : ℕ × List ℕ) _ ↦ (st.1 / base, (st.1 % base) :: st.2))
      (idx, [])).1 = idx / base ^ len := by
  induction len with
  | zero => simp
  | succ len ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Nat.div_div_eq_div_mul, ← Nat.pow_succ]

private theorem decodeDigits_succ (base len idx : ℕ) :
    decodeDigits base (len + 1) idx = ((idx / base ^ len) % base) :: decodeDigits base len idx := by
  unfold decodeDigits
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, decodeDigits_step]

private theorem decodeDigits_mod_pow (base len a r : ℕ) (hb : 0 < base) :
    decodeDigits base len (a * base ^ len + r) = decodeDigits base len r := by
  induction len generalizing a with
  | zero => simp [decodeDigits]
  | succ len ih =>
    rw [decodeDigits_succ, decodeDigits_succ]
    have hdiv2 : (a * base ^ (len + 1) + r) / base ^ len % base = (r / base ^ len) % base := by
      have hmul : a * base ^ (len + 1) = (a * base) * base ^ len := by rw [Nat.pow_succ]; ring
      rw [hmul, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos hb),
        Nat.add_mul_mod_self_right]
    have htail : a * base ^ (len + 1) + r = (a * base) * base ^ len + r := by
      rw [Nat.pow_succ]; ring
    rw [hdiv2, htail, ih (a * base)]

private theorem exists_decodeDigits (base len : ℕ) (hb : 0 < base) (f : Fin len → ℕ)
    (hf : ∀ k, f k < base) :
    ∃ idx < base ^ len, ∀ k : Fin len, (decodeDigits base len idx).getD k.1 0 = f k := by
  induction len with
  | zero => exact ⟨0, by simp, fun k ↦ k.elim0⟩
  | succ len ih =>
    obtain ⟨r, hr, hfr⟩ := ih (fun k ↦ f k.succ) (fun k ↦ hf k.succ)
    let idx := f 0 * base ^ len + r
    have hidx : idx < base ^ (len + 1) := by
      have hle : f 0 + 1 ≤ base := hf 0
      rw [Nat.pow_succ]
      calc f 0 * base ^ len + r < f 0 * base ^ len + base ^ len := Nat.add_lt_add_left hr _
        _ = (f 0 + 1) * base ^ len := by ring
        _ ≤ base * base ^ len := Nat.mul_le_mul_right _ hle
        _ = base ^ len * base := by ring
    refine ⟨idx, hidx, fun k ↦ ?_⟩
    have hdec : decodeDigits base (len + 1) idx = f 0 :: decodeDigits base len r := by
      rw [decodeDigits_succ]
      have htop : idx / base ^ len = f 0 := by
        dsimp only [idx]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos hb), Nat.div_eq_of_lt hr,
          Nat.zero_add]
      rw [htop, Nat.mod_eq_of_lt (hf 0), decodeDigits_mod_pow base len (f 0) r hb]
    rw [hdec]
    refine Fin.cases ?_ (fun k' ↦ ?_) k
    · rfl
    · simpa only [Fin.val_succ, List.getD_cons_succ] using hfr k'

private def checkRatFeasible (p : ℕ) (rows : List (List ℤ × ℤ)) (y : List ℚ) : Bool :=
  let D : ℕ := ((List.range p).map fun j ↦ (y.getD j 0).den).foldl (· * ·) 1
  let yScaled : List ℤ := (List.range p).map fun j ↦
    (y.getD j 0).num * ((D / (y.getD j 0).den : ℕ) : ℤ)
  rows.all fun r ↦ decide (ListMatrix.dotProduct p r.1 yScaled ≤ r.2 * (D : ℤ))

private theorem checkRatFeasible_eq_true_iff (p : ℕ) (rows : List (List ℤ × ℤ)) (y : List ℚ) :
    checkRatFeasible p rows y = true ↔
      ∀ r ∈ rows, ∑ j : Fin p, (r.1.getD j.1 0 : ℚ) * y.getD j.1 0 ≤ (r.2 : ℚ) := by
  unfold checkRatFeasible
  set D : ℕ := ((List.range p).map fun j ↦ (y.getD j 0).den).foldl (· * ·) 1
  set yScaled : List ℤ := (List.range p).map fun j ↦
    (y.getD j 0).num * ((D / (y.getD j 0).den : ℕ) : ℤ)
  have hD_pos_dvd : 0 < D ∧ ∀ j : Fin p, (y.getD j.1 0).den ∣ D := by
    have hgen : ∀ (l : List ℕ) (acc : ℕ), 0 < acc → (∀ a ∈ l, 0 < a) →
        0 < l.foldl (· * ·) acc ∧ acc ∣ l.foldl (· * ·) acc ∧
          ∀ a ∈ l, a ∣ l.foldl (· * ·) acc := by
      intro l
      induction l with
      | nil => intro acc hacc _; exact ⟨hacc, dvd_refl _, fun _ h ↦ by simp at h⟩
      | cons a t ih =>
        intro acc hacc hall
        have ha : 0 < a := hall a List.mem_cons_self
        obtain ⟨hpos, hdvd_acc, hdvd_t⟩ := ih (acc * a) (Nat.mul_pos hacc ha)
          (fun x hx ↦ hall x (List.mem_cons_of_mem _ hx))
        refine ⟨hpos, (dvd_mul_right acc a).trans hdvd_acc, fun x hx ↦ ?_⟩
        rcases List.mem_cons.mp hx with rfl | ht
        · exact (dvd_mul_left x acc).trans hdvd_acc
        · exact hdvd_t x ht
    obtain ⟨hpos, _, hdvd⟩ := hgen ((List.range p).map fun j ↦ (y.getD j 0).den) 1 one_pos
      (fun a ha ↦ by
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
        exact (y.getD j 0).den_pos)
    exact ⟨hpos, fun j ↦ hdvd _ (List.mem_map.mpr ⟨j.1, List.mem_range.mpr j.isLt, rfl⟩)⟩
  have hyS : ∀ j : Fin p, ((yScaled.getD j.1 0 : ℤ) : ℚ) = y.getD j.1 0 * (D : ℚ) := by
    intro j
    dsimp only [yScaled]
    rw [list_getD_eq _ _ _ (by simp [j.isLt]), List.getElem_map, List.getElem_range]
    have hdvd := hD_pos_dvd.2 j
    have hdpos : (0 : ℚ) < ((y.getD j.1 0).den : ℚ) := Nat.cast_pos.mpr (y.getD j.1 0).den_pos
    have hmul : (((D / (y.getD j.1 0).den : ℕ) : ℚ) * ((y.getD j.1 0).den : ℚ)) = (D : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    have hdiv : ((D / (y.getD j.1 0).den : ℕ) : ℚ) = (D : ℚ) / ((y.getD j.1 0).den : ℚ) := by
      rw [eq_div_iff hdpos.ne']; exact hmul
    rw [Int.cast_mul, Int.cast_natCast, hdiv, ← mul_div_assoc, mul_div_right_comm, Rat.num_div_den]
  rw [List.all_eq_true]
  refine forall₂_congr fun r _ ↦ ?_
  simp only [decide_eq_true_eq, ListMatrix.dotProduct_eq_sum_map_range, sum_map_range_eq_sum_fin]
  have hcast : (((∑ j : Fin p, r.1.getD j.1 0 * yScaled.getD j.1 0 : ℤ) : ℚ)) =
      (∑ j : Fin p, (r.1.getD j.1 0 : ℚ) * y.getD j.1 0) * (D : ℚ) := by
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hyS j]; ring
  have hDpos_q : (0 : ℚ) < (D : ℚ) := Nat.cast_pos.mpr hD_pos_dvd.1
  constructor
  · intro h
    have hq : (((∑ j : Fin p, r.1.getD j.1 0 * yScaled.getD j.1 0 : ℤ) : ℚ)) ≤
        ((r.2 * (D : ℤ) : ℤ) : ℚ) := by exact_mod_cast h
    rw [hcast] at hq
    push_cast at hq
    exact le_of_mul_le_mul_right hq hDpos_q
  · intro h
    have hq : (∑ j : Fin p, (r.1.getD j.1 0 : ℚ) * y.getD j.1 0) * (D : ℚ) ≤
        (r.2 : ℚ) * (D : ℚ) := mul_le_mul_of_nonneg_right h hDpos_q.le
    rw [← hcast] at hq
    exact_mod_cast hq

private def checkIntFeasible (inst : BoundedCoeffILPInstance) (x : List ℤ) : Bool :=
  (List.range inst.numVars).all (fun j ↦
    decide (inst.lower.getD j 0 ≤ x.getD j 0) && decide (x.getD j 0 ≤ inst.upper.getD j 0)) &&
  (List.range inst.rows.length).all fun i ↦
    decide (ListMatrix.dotProduct inst.numVars (inst.rows.getD i []) x ≤ inst.rhs.getD i 0)

private theorem checkIntFeasible_eq_true_iff (inst : BoundedCoeffILPInstance) (x : List ℤ) :
    checkIntFeasible inst x = true ↔ inst.IsFeasibleInt (fun j ↦ x.getD j.1 0) := by
  unfold checkIntFeasible
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    ListMatrix.dotProduct_eq_sum_map_range, sum_map_range_eq_sum_fin]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun j ↦ h1 j.1 j.isLt, fun i ↦ h2 i.1 i.isLt⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun j hj ↦ h1 ⟨j, hj⟩, fun i hi ↦ h2 ⟨i, hi⟩⟩

/-! ### 3. Two-Phase FPT Solver: Vertex Search + CGST Proximity Search -/

private def vertexStep (p : BoundedCoeffILPInstance × ℕ) : Option (List ℚ) :=
  let inst := p.1
  let rows := allPolyRows inst
  let q := rows.length
  let n := inst.numVars
  let inds := decodeDigits q n p.2
  let mat : RatTable :=
    { numRows := n, numCols := n,
      rows := inds.map fun i ↦ (rows.getD i ([], 0)).1.map fun z : ℤ ↦ (z : ℚ) }
  let bVec : List ℚ := inds.map fun i ↦ ((rows.getD i ([], 0)).2 : ℚ)
  let res := ratSolve { matrix := mat, rhs := bVec }
  res.solution.elim none fun y ↦ if checkRatFeasible n rows y then some y else none

private def findRationalVertex (inst : BoundedCoeffILPInstance) : Option (List ℚ) :=
  searchFirst vertexStep (fun x ↦ (allPolyRows x).length ^ x.numVars) inst

private def intProximityDelta (inst : BoundedCoeffILPInstance) : ℕ :=
  inst.numVars.factorial * (max 1 (maxAbsCoeff inst)) ^ inst.numVars

private def intPointStep (p : (BoundedCoeffILPInstance × List ℚ) × ℕ) : Option (List ℤ) :=
  let inst := p.1.1
  let y := p.1.2
  let Δ := intProximityDelta inst
  let base := 2 * Δ + 1
  let offs := decodeDigits base inst.numVars p.2
  let x := (List.range inst.numVars).map fun j ↦
    (y.getD j 0).floor - (Δ : ℤ) + (offs.getD j 0 : ℤ)
  if checkIntFeasible inst x then some x else none

private def findIntegerPoint (inst : BoundedCoeffILPInstance) (y : List ℚ) : Option (List ℤ) :=
  searchFirst intPointStep (fun q ↦ (2 * intProximityDelta q.1 + 1) ^ q.1.numVars) (inst, y)

/-- Executable FPT-time decision procedure for bounded-coefficient ILP feasibility. -/
def solveBoundedCoeffILP (inst : BoundedCoeffILPInstance) : Bool :=
  if inst.numVars = 0 then
    (List.range inst.rows.length).all fun i ↦ decide (0 ≤ inst.rhs.getD i 0)
  else
    ((findRationalVertex inst).bind (findIntegerPoint inst)).isSome

/-- Exact soundness and completeness of `solveBoundedCoeffILP`. -/
theorem solveBoundedCoeffILP_eq_true_iff (inst : BoundedCoeffILPInstance) :
    solveBoundedCoeffILP inst = true ↔ inst ∈ BoundedCoeffILP := by
  unfold solveBoundedCoeffILP
  change _ ↔ ∃ x : Fin inst.numVars → ℤ, inst.IsFeasibleInt x
  split_ifs with h0
  · simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨fun j ↦ (h0 ▸ j).elim0, fun j ↦ (h0 ▸ j).elim0, fun i ↦ ?_⟩
      have hsum : (∑ j : Fin inst.numVars, (inst.rows.getD i.1 []).getD j.1 0 *
          ((h0 ▸ j).elim0 : ℤ)) = 0 := by
        refine Finset.sum_eq_zero fun j _ ↦ (h0 ▸ j).elim0
      rw [hsum]; exact h i.1 i.isLt
    · rintro ⟨x, _, hrows⟩ i hi
      have hi' := hrows ⟨i, hi⟩
      have hsum : (∑ j : Fin inst.numVars, (inst.rows.getD i []).getD j.1 0 * x j) = 0 :=
        Finset.sum_eq_zero fun j _ ↦ (h0 ▸ j).elim0
      rwa [hsum] at hi'
  · have hp : 1 ≤ inst.numVars := by omega
    constructor
    · intro hsome
      obtain ⟨x, hx_bind⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨y, hy_some, hx_some⟩ := Option.bind_eq_some_iff.mp hx_bind
      obtain ⟨idx, _, hstep, _⟩ := searchFirst_eq_some_iff.mp hx_some
      unfold intPointStep at hstep
      dsimp only at hstep
      split_ifs at hstep with hchk
      exact ⟨_, (checkIntFeasible_eq_true_iff inst _).mp hchk⟩
    · rintro ⟨x₀, hx₀⟩
      have hy₀ : inst.IsFeasibleRat (fun j ↦ (x₀ j : ℚ)) := hx₀.isFeasibleRat
      -- Phase 1: `findRationalVertex inst` returns `some ystar` with `inst.IsFeasibleRat ystar`.
      let rows := allPolyRows inst
      let q := rows.length
      have hq_pos : 0 < q := by
        dsimp only [q, rows, allPolyRows]
        simp only [List.length_append, List.length_map, List.length_range]; omega
      let M : Matrix (Fin q) (Fin inst.numVars) ℚ := fun i j ↦
        ((rows.getD i.1 ([], 0)).1.getD j.1 0 : ℚ)
      let h : Fin q → ℚ := fun i ↦ ((rows.getD i.1 ([], 0)).2 : ℚ)
      have hM_iff : ∀ y : Fin inst.numVars → ℚ, (∀ i, (M *ᵥ y) i ≤ h i) ↔ inst.IsFeasibleRat y := by
        intro y
        rw [← allPolyRows_iff]
        constructor
        · intro hall r hr
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
          have := hall ⟨i, hi⟩
          dsimp only [M, h, Matrix.mulVec, dotProduct] at this
          rw [list_getD_eq _ _ _ hi] at this
          exact this
        · intro hall i
          have hr : rows.getD i.1 ([], 0) ∈ rows := by
            rw [list_getD_eq _ _ _ i.isLt]; exact List.getElem_mem i.isLt
          simpa [M, h, Matrix.mulVec, dotProduct] using hall _ hr
      obtain ⟨yv, I, hyv_feas, hI_li, hI_eq⟩ := exists_vertex_of_bounded_polytope M h
        (fun j ↦ (inst.lower.getD j.1 0 : ℚ)) (fun j ↦ (inst.upper.getD j.1 0 : ℚ))
        ⟨fun j ↦ (x₀ j : ℚ), (hM_iff _).mpr hy₀⟩
        (fun y hy ↦ ((hM_iff y).mp hy).1)
      obtain ⟨idx_v, hidx_v, hdec_v⟩ := exists_decodeDigits q inst.numVars hq_pos
        (fun k ↦ (I k).1) (fun k ↦ (I k).isLt)
      have hdec_len : ∀ l a, (decodeDigits q l a).length = l := by
        intro l; induction l with
        | zero => intro _; simp [decodeDigits]
        | succ l ihl => intro a; rw [decodeDigits_succ, List.length_cons, ihl]
      have hvstep_some : (vertexStep (inst, idx_v)).isSome = true := by
        unfold vertexStep
        set inds := decodeDigits q inst.numVars idx_v
        let mat : RatTable :=
          { numRows := inst.numVars, numCols := inst.numVars,
            rows := inds.map fun i ↦ (rows.getD i ([], 0)).1.map fun z : ℤ ↦ (z : ℚ) }
        let bVec : List ℚ := inds.map fun i ↦ ((rows.getD i ([], 0)).2 : ℚ)
        have hmat_eq : mat.toMatrix = M.submatrix I id := by
          ext k j
          have hk_len : k.1 < inds.length := by rw [hdec_len]; exact k.isLt
          have hrow_len : (rows.getD (I k).1 ([], 0)).1.length = inst.numVars := by
            have hr : rows.getD (I k).1 ([], 0) ∈ allPolyRows inst := by
              rw [list_getD_eq _ _ _ (I k).isLt]; exact List.getElem_mem (I k).isLt
            unfold allPolyRows at hr
            simp only [List.mem_append, List.mem_map, List.mem_range] at hr
            rcases hr with (hr | ⟨j0, _, heq⟩) | ⟨j0, _, heq⟩
            · exact ((dedupRows_props inst).2.1 _ hr).1
            · rw [← heq]; simp [unitRow]
            · rw [← heq]; simp [unitRow]
          have hinds_k : inds[k.1] = (I k).1 := by rw [← list_getD_eq inds 0 k.1 hk_len, hdec_v k]
          dsimp only [Cslib.RowTable.toMatrix_apply, Cslib.RowTable.entry, M]
          rw [list_getD_eq mat.rows [] k.1 (by simp [mat, hk_len])]
          dsimp only [mat]
          rw [List.getElem_map, hinds_k,
            list_getD_eq _ 0 j.1 (by rw [List.length_map, hrow_len]; exact j.isLt),
            List.getElem_map, ← list_getD_eq _ 0 j.1 (by rw [hrow_len]; exact j.isLt)]
          rfl
        have hb_eq : (fun k : Fin inst.numVars ↦ bVec.getD k.1 0) = fun k ↦ h (I k) := by
          ext k
          have hk_len : k.1 < inds.length := by rw [hdec_len]; exact k.isLt
          dsimp only [bVec, h]
          rw [list_getD_eq _ _ _ (by simp [hk_len]), List.getElem_map,
            ← list_getD_eq inds 0 k.1 hk_len, hdec_v k]
        obtain ⟨hsol, hnone⟩ := ratSolve_spec { matrix := mat, rhs := bVec }
        have hex_sol : ∃ y : Fin inst.numVars → ℚ, mat.toMatrix *ᵥ y = fun k ↦ bVec.getD k.1 0 :=
          ⟨yv, by rw [hmat_eq, hb_eq]; ext k; exact hI_eq k⟩
        cases hres : (ratSolve { matrix := mat, rhs := bVec }).solution with
        | none => exact absurd (hnone.mp hres) (not_not.mpr hex_sol)
        | some ys =>
          obtain ⟨hys_len, hys_eq⟩ := hsol ys hres
          have hys_eq_yv : (fun j : Fin inst.numVars ↦ ys.getD j.1 0) = yv := by
            -- `mat.toMatrix = M.submatrix I id` has linearly independent rows, hence `det ≠ 0`!
            have hdet : mat.toMatrix.det ≠ 0 := by
              rw [hmat_eq]
              intro hd
              have hdep := Matrix.exists_vecMul_eq_zero_iff.mpr hd
              obtain ⟨c, hc_ne, hc_eq⟩ := hdep
              have hsum : ∑ k : Fin inst.numVars, c k • M (I k) = 0 := by
                ext j; have := congrFun hc_eq j
                simpa [Matrix.vecMul, dotProduct, Matrix.submatrix_apply] using this
              exact hc_ne (funext (Fintype.linearIndependent_iff.mp hI_li c hsum))
            have hdiff : mat.toMatrix *ᵥ ((fun j ↦ ys.getD j.1 0) - yv) = 0 := by
              rw [Matrix.mulVec_sub, hys_eq, hb_eq, sub_eq_zero]
              rw [hmat_eq]; ext k; exact (hI_eq k).symm
            have hzero := Matrix.eq_zero_of_mulVec_eq_zero hdet hdiff
            exact sub_eq_zero.mp hzero
          have hchk_true : checkRatFeasible inst.numVars rows ys = true := by
            rw [checkRatFeasible_eq_true_iff]
            have hfeas_ys : inst.IsFeasibleRat (fun j ↦ ys.getD j.1 0) := by
              rw [hys_eq_yv]; exact (hM_iff yv).mp hyv_feas
            exact (allPolyRows_iff inst _).mpr hfeas_ys
          dsimp only
          rw [hres, Option.elim_some]
          change (if checkRatFeasible inst.numVars rows ys = true then some ys else none).isSome =
            true
          rw [hchk_true]; rfl
      have hv_some : (findRationalVertex inst).isSome = true :=
        searchFirst_isSome_iff.mpr ⟨idx_v, hidx_v, hvstep_some⟩
      obtain ⟨ystar, hystar⟩ := Option.isSome_iff_exists.mp hv_some
      have hystar_feas : inst.IsFeasibleRat (fun j ↦ ystar.getD j.1 0) := by
        obtain ⟨idx, _, hstep, _⟩ := searchFirst_eq_some_iff.mp hystar
        dsimp only [vertexStep] at hstep
        generalize (ratSolve _).solution = sol at hstep
        cases sol with
        | none => simp at hstep
        | some ys =>
          simp only [Option.elim_some] at hstep
          split_ifs at hstep with hchk
          cases hstep
          exact (allPolyRows_iff inst _).mp ((checkRatFeasible_eq_true_iff _ _ _).mp hchk)
      -- Phase 2: CGST proximity guarantees `findIntegerPoint inst ystar` returns `some x`!
      obtain ⟨xstar, hxstar_feas, hxstar_prox⟩ :=
        boundedCoeffILP_proximity inst hp (fun j ↦ ystar.getD j.1 0) hystar_feas ⟨x₀, hx₀⟩
      let Δ := intProximityDelta inst
      let base := 2 * Δ + 1
      have hbase_pos : 0 < base := by omega
      have hoffs_bd : ∀ j : Fin inst.numVars,
          (xstar j - ((ystar.getD j.1 0).floor - (Δ : ℤ))).toNat < base := by
        intro j
        have hpr := hxstar_prox j
        have hfl_le : ((ystar.getD j.1 0).floor : ℚ) ≤ ystar.getD j.1 0 := Rat.floor_le _
        have hlt_fl : ystar.getD j.1 0 < ((ystar.getD j.1 0).floor : ℚ) + 1 := by
          exact_mod_cast Rat.lt_floor_add_one (ystar.getD j.1 0)
        have hlow_q : ((ystar.getD j.1 0).floor : ℚ) - (Δ : ℚ) ≤ (xstar j : ℚ) := by
          have := (abs_le.mp hpr).1; dsimp only [Δ, intProximityDelta] at *; linarith
        have hhi_q : (xstar j : ℚ) < ((ystar.getD j.1 0).floor : ℚ) + 1 + (Δ : ℚ) := by
          have := (abs_le.mp hpr).2; dsimp only [Δ, intProximityDelta] at *; linarith
        have hlow : (ystar.getD j.1 0).floor - (Δ : ℤ) ≤ xstar j := by exact_mod_cast hlow_q
        have hhi : xstar j < (ystar.getD j.1 0).floor + 1 + (Δ : ℤ) := by exact_mod_cast hhi_q
        omega
      obtain ⟨idx_i, hidx_i, hdec_i⟩ := exists_decodeDigits base inst.numVars hbase_pos
        (fun j ↦ (xstar j - ((ystar.getD j.1 0).floor - (Δ : ℤ))).toNat) hoffs_bd
      have histep_some : (intPointStep ((inst, ystar), idx_i)).isSome = true := by
        unfold intPointStep
        have hx_eq : (fun j : Fin inst.numVars ↦
            (((List.range inst.numVars).map fun k ↦
              (ystar.getD k 0).floor - (Δ : ℤ) +
                ((decodeDigits base inst.numVars idx_i).getD k 0 : ℤ)).getD j.1 0)) = xstar := by
          ext j
          rw [list_getD_eq _ _ _ (by simp [j.isLt]), List.getElem_map, List.getElem_range,
            hdec_i j]
          have hpr := hxstar_prox j
          have hfl_le : ((ystar.getD j.1 0).floor : ℚ) ≤ ystar.getD j.1 0 := Rat.floor_le _
          have hlow_q : ((ystar.getD j.1 0).floor : ℚ) - (Δ : ℚ) ≤ (xstar j : ℚ) := by
            have := (abs_le.mp hpr).1; dsimp only [Δ, intProximityDelta] at *; linarith
          have hlow : (ystar.getD j.1 0).floor - (Δ : ℤ) ≤ xstar j := by exact_mod_cast hlow_q
          omega
        have hchk : checkIntFeasible inst
            ((List.range inst.numVars).map fun k ↦
              (ystar.getD k 0).floor - (Δ : ℤ) +
                ((decodeDigits base inst.numVars idx_i).getD k 0 : ℤ)) = true := by
          rw [checkIntFeasible_eq_true_iff, hx_eq]; exact hxstar_feas
        dsimp only
        rw [show checkIntFeasible inst _ = true from hchk]
        rfl
      have hi_some : (findIntegerPoint inst ystar).isSome = true :=
        searchFirst_isSome_iff.mpr ⟨idx_i, hidx_i, histep_some⟩
      rw [Option.isSome_iff_exists] at hi_some
      obtain ⟨x, hx⟩ := hi_some
      rw [Option.isSome_iff_exists]
      exact ⟨x, Option.bind_eq_some_iff.mpr ⟨ystar, hystar, hx⟩⟩

/-! ### 4. Polynomial-Time Step Certificates and FPT Membership -/

private theorem computableInPolyTime_maxAbsCoeff :
    ComputableInPolyTime maxAbsCoeff encBoundedCoeffILP encNat := by
  -- Fold over rows computing max absolute value in first `numVars` entries; each accumulator ≤ max
  -- binary length of input, so encoding length is linearly bounded.
  have hmax : ComputableInPolyTime (fun p : ℕ × ℕ ↦ max p.1 p.2)
      (encPair encNat encNat) encNat :=
    (ComputableInPolyTime.ite (binary_le' (fst _ _) (snd _ _)) (snd _ _) (fst _ _)).of_enc_eq
      fun p ↦ by simp [max_def]
  have hacc_mem : ∀ (l : List ℕ) (acc : ℕ), l.foldl max acc = acc ∨ l.foldl max acc ∈ l := by
    intro l; induction l with
    | nil => intro acc; left; rfl
    | cons a t ih =>
      intro acc; dsimp only [List.foldl_cons]
      rcases ih (max acc a) with h | h
      · rw [h]; rcases max_choice acc a with hm | hm
        · left; exact hm
        · right; rw [hm]; exact List.mem_cons_self
      · right; exact List.mem_cons_of_mem _ h
  have hrowMax : ComputableInPolyTime
      (fun p : ℕ × List ℤ ↦
        ((List.range p.1).map fun j ↦ (p.2.getD j 0).natAbs).foldl max 0)
      (encPair encUnary (encList encIntBin)) encNat := by
    have hmap : ComputableInPolyTime
        (fun p : ℕ × List ℤ ↦ (List.range p.1).map fun j ↦ (p.2.getD j 0).natAbs)
        (encPair encUnary (encList encIntBin)) (encList encNat) :=
      mapWithInput (range.comp (fst _ _))
        (intBin_natAbs.comp (listGetDWithInput ((snd _ _).comp (fst _ _)) (snd _ _) 0))
    refine foldl' hmap (const 0) hmax (B := fun p ↦ (encPair encUnary (encList encIntBin) p).length)
      .self fun p i _ ↦ ?_
    rcases hacc_mem (((List.range p.1).map fun j ↦ (p.2.getD j 0).natAbs).take i) 0 with h0 | hm
    · rw [h0]; simp [encNat_apply]
    · have hmem := List.mem_of_mem_take hm
      obtain ⟨j, _, heq⟩ := List.mem_map.mp hmem
      rw [← heq]
      by_cases hj : j < p.2.length
      · rw [list_getD_eq _ _ _ hj]
        have h1 : (encNat (p.2[j]).natAbs).length ≤ (encIntBin p.2[j]).length := by
          rw [length_encIntBin, encNat_apply, Nat.size_eq_bits_len]; omega
        exact h1.trans ((length_le_encList_of_mem encIntBin (List.getElem_mem hj)).trans
          (length_le_encPair_right encUnary _ p))
      · rw [list_getD_default _ _ _ (not_lt.mp hj)]; simp [encNat_apply]
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × ℕ) × List ℤ ↦
        max q.1.2 (((List.range q.1.1).map fun j ↦ (q.2.getD j 0).natAbs).foldl max 0))
      (encPair (encPair encUnary encNat) (encList encIntBin)) encNat :=
    hmax.comp (((snd _ _).comp (fst _ _)).prod
      (hrowMax.comp (((fst _ _).comp (fst _ _)).prod (snd _ _))))
  refine foldlWith (par := fun inst : BoundedCoeffILPInstance ↦ inst.numVars)
    (list := fun inst ↦ inst.rows)
    (step := fun p acc row ↦
      max acc (((List.range p).map fun j ↦ (row.getD j 0).natAbs).foldl max 0))
    (by fun_prop) (by fun_prop) (const 0) hstep
    (B := fun inst ↦ (encBoundedCoeffILP inst).length) .self fun inst i _ ↦ ?_
  have hacc_le : ∀ (rows : List (List ℤ)) (acc : ℕ),
      (∀ r ∈ rows, ∀ j < inst.numVars, (encNat (r.getD j 0).natAbs).length ≤
        (encBoundedCoeffILP inst).length) →
      (encNat acc).length ≤ (encBoundedCoeffILP inst).length →
      (encNat (rows.foldl (fun a row ↦
        max a (((List.range inst.numVars).map fun j ↦
          (row.getD j 0).natAbs).foldl max 0)) acc)).length ≤
        (encBoundedCoeffILP inst).length := by
    intro rows; induction rows with
    | nil => intro _ _ h; exact h
    | cons r rs ih =>
      intro acc hrows hacc
      refine ih _ (fun x hx ↦ hrows x (List.mem_cons_of_mem _ hx)) ?_
      have hrm : (encNat (((List.range inst.numVars).map fun j ↦
            (r.getD j 0).natAbs).foldl max 0)).length ≤
          (encBoundedCoeffILP inst).length := by
        rcases hacc_mem _ 0 with h0 | hm
        · rw [h0]; simp [encNat_apply]
        · obtain ⟨j, hj, heq⟩ := List.mem_map.mp hm
          rw [← heq]; exact hrows r List.mem_cons_self j (List.mem_range.mp hj)
      dsimp only
      rcases max_choice acc
          (((List.range inst.numVars).map fun j ↦ (r.getD j 0).natAbs).foldl max 0) with hm | hm
      · rwa [hm]
      · rwa [hm]
  refine hacc_le _ 0 (fun r hr j _ ↦ ?_) (by simp [encNat_apply])
  have hr_mem : r ∈ inst.rows := List.mem_of_mem_take hr
  by_cases hj : j < r.length
  · rw [list_getD_eq _ _ _ hj]
    have h1 : (encNat (r[j]).natAbs).length ≤ (encIntBin r[j]).length := by
      rw [length_encIntBin, encNat_apply, Nat.size_eq_bits_len]; omega
    have h2 : (encIntBin r[j]).length ≤ (encList encIntBin r).length :=
      length_le_encList_of_mem encIntBin (List.getElem_mem hj)
    have h3 : (encList encIntBin r).length ≤ (encList (encList encIntBin) inst.rows).length :=
      length_le_encList_of_mem (encList encIntBin) hr_mem
    have h4 : (encList (encList encIntBin) inst.rows).length ≤
      (encBoundedCoeffILP inst).length := by
      simp only [BoundedCoeffILPInstance.enc_apply,
        BoundedCoeffILPInstance.encFields, length_encPair]
      omega
    omega
  · rw [list_getD_default _ _ _ (not_lt.mp hj)]; simp [encNat_apply]

private def dedupRowUpdate (row r : List ℤ × ℤ) : List ℤ × ℤ :=
  if r.1 = row.1 then (r.1, min r.2 row.2) else r

private theorem computableInPolyTime_dedupRows :
    ComputableInPolyTime dedupRows encBoundedCoeffILP
      (encList (encPair (encList encIntBin) encIntBin)) := by
  let encRow := encPair (encList encIntBin) encIntBin
  have hraw : ComputableInPolyTime rawPolyRows encBoundedCoeffILP (encList encRow) := by
    unfold rawPolyRows normRow
    have hrows_p : ComputableInPolyTime (fun p : BoundedCoeffILPInstance × ℕ ↦ p.1.rows)
        (encPair encBoundedCoeffILP encUnary) (encList (encList encIntBin)) := by fun_prop
    have hrhs_p : ComputableInPolyTime (fun p : BoundedCoeffILPInstance × ℕ ↦ p.1.rhs)
        (encPair encBoundedCoeffILP encUnary) (encList encIntBin) := by fun_prop
    have hnum_p : ComputableInPolyTime (fun p : BoundedCoeffILPInstance × ℕ ↦ p.1.numVars)
        (encPair encBoundedCoeffILP encUnary) encUnary := by fun_prop
    have hnorm : ComputableInPolyTime
        (fun p : BoundedCoeffILPInstance × ℕ ↦
          ((List.range p.1.numVars).map fun j ↦ (p.1.rows.getD p.2 []).getD j 0,
            p.1.rhs.getD p.2 0))
        (encPair encBoundedCoeffILP encUnary) encRow := by
      have hrow_i : ComputableInPolyTime
          (fun p : BoundedCoeffILPInstance × ℕ ↦ p.1.rows.getD p.2 [])
          (encPair encBoundedCoeffILP encUnary) (encList encIntBin) :=
        listGetDWithInput hrows_p (snd _ _) []
      have hvec : ComputableInPolyTime
          (fun p : BoundedCoeffILPInstance × ℕ ↦
            (List.range p.1.numVars).map fun j ↦ (p.1.rows.getD p.2 []).getD j 0)
          (encPair encBoundedCoeffILP encUnary) (encList encIntBin) :=
        mapWithInput (range.comp hnum_p)
          (listGetDWithInput (hrow_i.comp (fst _ _)) (snd _ _) 0)
      exact hvec.prod (listGetDWithInput hrhs_p (snd _ _) 0)
    exact mapWithInput (range.comp (length_list (encList encIntBin) |>.comp (by fun_prop))) hnorm
  have hmin : ComputableInPolyTime (fun p : ℤ × ℤ ↦ min p.1 p.2)
      (encPair encIntBin encIntBin) encIntBin :=
    (ComputableInPolyTime.ite (intBin_le' (fst _ _) (snd _ _)) (fst _ _) (snd _ _)).of_enc_eq
      fun p ↦ by simp [min_def]
  have hupd : ComputableInPolyTime (fun q : (List (List ℤ × ℤ) × (List ℤ × ℤ)) × (List ℤ × ℤ) ↦
        dedupRowUpdate q.1.2 q.2)
      (encPair (encPair (encList encRow) encRow) encRow) encRow := by
    have hcond : ComputableInPolyTime
        (fun q : (List (List ℤ × ℤ) × (List ℤ × ℤ)) × (List ℤ × ℤ) ↦ decide (q.2.1 = q.1.2.1))
        (encPair (encPair (encList encRow) encRow) encRow) encBool :=
      ((fst _ _).comp (snd _ _)).decide_eq' ((fst _ _).comp ((snd _ _).comp (fst _ _)))
    have hthen : ComputableInPolyTime
        (fun q : (List (List ℤ × ℤ) × (List ℤ × ℤ)) × (List ℤ × ℤ) ↦
          (q.2.1, min q.2.2 q.1.2.2))
        (encPair (encPair (encList encRow) encRow) encRow) encRow :=
      ((fst _ _).comp (snd _ _)).prod
        (hmin.comp (((snd _ _).comp (snd _ _)).prod ((snd _ _).comp ((snd _ _).comp (fst _ _)))))
    exact (ComputableInPolyTime.ite hcond hthen (snd _ _)).of_enc_eq fun q ↦ by
      simp [dedupRowUpdate, decide_eq_true_eq]
  have hins : ComputableInPolyTime (fun p : List (List ℤ × ℤ) × (List ℤ × ℤ) ↦ dedupInsert p.1 p.2)
      (encPair (encList encRow) encRow) (encList encRow) := by
    have hany : ComputableInPolyTime
        (fun p : List (List ℤ × ℤ) × (List ℤ × ℤ) ↦ p.1.any fun r ↦ decide (r.1 = p.2.1))
        (encPair (encList encRow) encRow) encBool :=
      anyWithInput (fst _ _)
        ((fst _ _).comp (snd _ _) |>.decide_eq' ((fst _ _).comp ((snd _ _).comp (fst _ _))))
    have hmap : ComputableInPolyTime
        (fun p : List (List ℤ × ℤ) × (List ℤ × ℤ) ↦ p.1.map fun r ↦ dedupRowUpdate p.2 r)
        (encPair (encList encRow) encRow) (encList encRow) :=
      mapWithInput (fst _ _) hupd
    exact (ComputableInPolyTime.ite hany hmap
      ((cons encRow).comp ((snd _ _).prod (fst _ _)))).of_enc_eq fun p ↦ by
        simp [dedupInsert, dedupRowUpdate]
  -- Bound intermediate accumulator length by `(raw.length + 1) * (2 * (3 * |enc raw| + 1) + 1)`:
  have hB : PolyBounded (fun inst : BoundedCoeffILPInstance ↦ (encBoundedCoeffILP inst).length)
      (fun inst ↦ ((rawPolyRows inst).length + 1) *
        (2 * (3 * (encList encRow (rawPolyRows inst)).length + 1) + 1)) := by
    have h1 := hraw.polyBounded_length
    have h2 : PolyBounded (fun inst : BoundedCoeffILPInstance ↦ (encBoundedCoeffILP inst).length)
        (fun inst ↦ (rawPolyRows inst).length) :=
      ((length_list encRow).comp hraw).polyBounded_length.mono fun inst ↦ by
        simp [encUnary_apply]
    exact (h2.add (.const 1)).mul
      (((PolyBounded.const 2).mul (((PolyBounded.const 3).mul h1).add (.const 1))).add (.const 1))
  refine foldl' hraw (const []) hins hB fun inst i _ ↦ ?_
  have hinv : ∀ (l : List (List ℤ × ℤ)) (acc : List (List ℤ × ℤ)),
      (∀ r ∈ acc, r.1 ∈ (rawPolyRows inst).map Prod.fst ∧ r.2 ∈ (rawPolyRows inst).map Prod.snd) →
      (∀ r ∈ l, r.1 ∈ (rawPolyRows inst).map Prod.fst ∧ r.2 ∈ (rawPolyRows inst).map Prod.snd) →
      (∀ r ∈ l.foldl dedupInsert acc,
        r.1 ∈ (rawPolyRows inst).map Prod.fst ∧ r.2 ∈ (rawPolyRows inst).map Prod.snd) ∧
      (l.foldl dedupInsert acc).length ≤ acc.length + l.length := by
    intro l
    induction l with
    | nil => intro acc hacc _; exact ⟨hacc, by simp⟩
    | cons a t ih =>
      intro acc hacc hl
      have hs := dedupInsert_props acc a
      have ha := hl a List.mem_cons_self
      have hacc' : ∀ r ∈ dedupInsert acc a,
          r.1 ∈ (rawPolyRows inst).map Prod.fst ∧ r.2 ∈ (rawPolyRows inst).map Prod.snd := by
        intro r hr
        constructor
        · rcases List.mem_cons.mp (hs.1 r hr) with h1 | h2
          · exact h1 ▸ ha.1
          · obtain ⟨r0, hr0, hr0_eq⟩ := List.mem_map.mp h2; exact hr0_eq ▸ (hacc r0 hr0).1
        · rcases List.mem_cons.mp (hs.2.1 r hr) with h1 | h2
          · exact h1 ▸ ha.2
          · obtain ⟨r0, hr0, hr0_eq⟩ := List.mem_map.mp h2; exact hr0_eq ▸ (hacc r0 hr0).2
      obtain ⟨h1, h2⟩ := ih (dedupInsert acc a) hacc' (fun r hr ↦ hl r (List.mem_cons_of_mem _ hr))
      exact ⟨h1, h2.trans (by have := hs.2.2.1; simp only [List.length_cons]; omega)⟩
  obtain ⟨hmem, hlen⟩ := hinv ((rawPolyRows inst).take i) [] (by simp)
    (fun r hr ↦ ⟨List.mem_map_of_mem (List.mem_of_mem_take hr),
      List.mem_map_of_mem (List.mem_of_mem_take hr)⟩)
  refine (length_encList_le encRow _ (b := 3 * (encList encRow (rawPolyRows inst)).length + 1)
    fun r hr ↦ ?_).trans ?_
  · obtain ⟨h1, h2⟩ := hmem r hr
    obtain ⟨r1, hr1, hr1_eq⟩ := List.mem_map.mp h1
    obtain ⟨r2, hr2, hr2_eq⟩ := List.mem_map.mp h2
    have hl1 : (encList encIntBin r.1).length ≤ (encList encRow (rawPolyRows inst)).length := by
      rw [← hr1_eq]
      exact (length_le_encPair_left _ _ r1).trans (length_le_encList_of_mem encRow hr1)
    have hl2 : (encIntBin r.2).length ≤ (encList encRow (rawPolyRows inst)).length := by
      rw [← hr2_eq]
      exact (length_le_encPair_right _ _ r2).trans (length_le_encList_of_mem encRow hr2)
    rw [length_encPair]; omega
  · have hlen' : (((rawPolyRows inst).take i).foldl dedupInsert []).length ≤
        (rawPolyRows inst).length + 1 := by
      have ht := List.length_take_le i (rawPolyRows inst)
      simp only [List.length_nil, zero_add] at hlen; omega
    exact Nat.mul_le_mul_right _ hlen'

private theorem computableInPolyTime_allPolyRows :
    ComputableInPolyTime allPolyRows encBoundedCoeffILP
      (encList (encPair (encList encIntBin) encIntBin)) := by
  let encRow := encPair (encList encIntBin) encIntBin
  have hunit : ∀ val : ℤ, ComputableInPolyTime (fun p : ℕ × ℕ ↦ unitRow p.1 p.2 val)
      (encPair encUnary encUnary) (encList encIntBin) := fun val ↦ by
    unfold unitRow
    have hite : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × ℕ ↦ if decide (q.2 = q.1.2) = true then val else 0)
        (encPair (encPair encUnary encUnary) encUnary) encIntBin :=
      ComputableInPolyTime.ite ((snd _ _).decide_eq' ((snd _ _).comp (fst _ _)))
        (const val) (const 0)
    have hstep : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ ↦ if q.2 = q.1.2 then val else 0)
        (encPair (encPair encUnary encUnary) encUnary) encIntBin :=
      hite.of_enc_eq fun _ ↦ by simp [decide_eq_true_eq]
    exact mapWithInput (range.comp (fst _ _)) hstep
  have hnum_p : ComputableInPolyTime (fun p : BoundedCoeffILPInstance × ℕ ↦ p.1.numVars)
      (encPair encBoundedCoeffILP encUnary) encUnary := by fun_prop
  have hup_p : ComputableInPolyTime (fun p : BoundedCoeffILPInstance × ℕ ↦ p.1.upper)
      (encPair encBoundedCoeffILP encUnary) (encList encIntBin) := by fun_prop
  have hlo_p : ComputableInPolyTime (fun p : BoundedCoeffILPInstance × ℕ ↦ p.1.lower)
      (encPair encBoundedCoeffILP encUnary) (encList encIntBin) := by fun_prop
  have hU : ComputableInPolyTime
      (fun inst : BoundedCoeffILPInstance ↦
        (List.range inst.numVars).map fun j ↦ (unitRow inst.numVars j 1, inst.upper.getD j 0))
      encBoundedCoeffILP (encList encRow) :=
    mapWithInput (range.comp (by fun_prop))
      (((hunit 1).comp (hnum_p.prod (snd _ _))).prod (listGetDWithInput hup_p (snd _ _) 0))
  have hL : ComputableInPolyTime
      (fun inst : BoundedCoeffILPInstance ↦
        (List.range inst.numVars).map fun j ↦ (unitRow inst.numVars j (-1), -inst.lower.getD j 0))
      encBoundedCoeffILP (encList encRow) :=
    mapWithInput (range.comp (by fun_prop))
      (((hunit (-1)).comp (hnum_p.prod (snd _ _))).prod
        (intBin_neg.comp (listGetDWithInput hlo_p (snd _ _) 0)))
  exact (listAppend encRow).comp
    (((listAppend encRow).comp (computableInPolyTime_dedupRows.prod hU)).prod hL)

private theorem computableInPolyTime_decodeDigits :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ ↦ decodeDigits p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encUnary) encNat) (encList encNat) := by
  let encIn := encPair (encPair encNat encUnary) encNat
  let encSt := encPair encNat (encList encNat)
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × (ℕ × List ℕ)) × ℕ ↦ (q.1.2.1 / q.1.1, (q.1.2.1 % q.1.1) :: q.1.2.2))
      (encPair (encPair encNat encSt) encUnary) encSt := by
    have hq1 := fst (encPair encNat encSt) encUnary
    have hbase := (fst encNat encSt).comp hq1
    have hst := (snd encNat encSt).comp hq1
    have ha := (fst encNat (encList encNat)).comp hst
    have hl := (snd encNat (encList encNat)).comp hst
    exact (binary_div' ha hbase).prod ((cons encNat).comp ((binary_mod' ha hbase).prod hl))
  have hB : PolyBounded (fun p : (ℕ × ℕ) × ℕ ↦ (encIn p).length)
      (fun p ↦ 2 * (encNat p.2).length + 1 + p.1.2 * (2 * (encNat p.2).length + 1)) := by
    have h1 : PolyBounded (fun p : (ℕ × ℕ) × ℕ ↦ (encIn p).length) (fun p ↦ (encNat p.2).length) :=
      (snd _ _).polyBounded_length
    have h2 : PolyBounded (fun p : (ℕ × ℕ) × ℕ ↦ (encIn p).length) (fun p ↦ p.1.2) :=
      ((snd _ _).comp (fst _ _)).polyBounded_length.mono fun p ↦ by simp [encUnary_apply]
    exact (((PolyBounded.const 2).mul h1).add (.const 1)).add
      (h2.mul (((PolyBounded.const 2).mul h1).add (.const 1)))
  have hfold : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ ↦
        (List.range p.1.2).foldl (fun st _ ↦ (st.1 / p.1.1, (st.1 % p.1.1) :: st.2)) (p.2, []))
      encIn encSt := by
    refine foldlWith (par := fun p : (ℕ × ℕ) × ℕ ↦ p.1.1)
      (list := fun p ↦ List.range p.1.2)
      (step := fun base st _ ↦ (st.1 / base, (st.1 % base) :: st.2))
      ((fst _ _).comp (fst _ _)) (range.comp ((snd _ _).comp (fst _ _)))
      ((snd _ _).prod (const [])) hstep hB fun p i hi ↦ ?_
    have hinv : ∀ (l : List ℕ) (st : ℕ × List ℕ),
        (l.foldl (fun s _ ↦ (s.1 / p.1.1, (s.1 % p.1.1) :: s.2)) st).1 ≤ st.1 ∧
        (l.foldl (fun s _ ↦ (s.1 / p.1.1, (s.1 % p.1.1) :: s.2)) st).2.length =
          st.2.length + l.length ∧
        ∀ x ∈ (l.foldl (fun s _ ↦ (s.1 / p.1.1, (s.1 % p.1.1) :: s.2)) st).2,
          x ∈ st.2 ∨ x ≤ st.1 := by
      intro l
      induction l with
      | nil => intro st; exact ⟨le_rfl, by simp, fun _ h ↦ Or.inl h⟩
      | cons _ t ih =>
        intro st
        obtain ⟨h1, h2, h3⟩ := ih (st.1 / p.1.1, (st.1 % p.1.1) :: st.2)
        refine ⟨h1.trans (Nat.div_le_self _ _), by simp [h2]; omega, fun x hx ↦ ?_⟩
        rcases h3 x hx with hm | hle
        · rcases List.mem_cons.mp hm with rfl | hst
          · right; exact Nat.mod_le _ _
          · exact Or.inl hst
        · exact Or.inr (hle.trans (Nat.div_le_self _ _))
    obtain ⟨h1, h2, h3⟩ := hinv ((List.range p.1.2).take i) (p.2, [])
    rw [length_encPair]
    have hle1 : (encNat ((List.take i (List.range p.1.2)).foldl
        (fun s _ ↦ (s.1 / p.1.1, (s.1 % p.1.1) :: s.2)) (p.2, [])).1).length ≤
          (encNat p.2).length := by
      rw [encNat_apply, encNat_apply, Nat.size_eq_bits_len, Nat.size_eq_bits_len]
      exact Nat.size_le_size h1
    have hle2 : (encList encNat ((List.take i (List.range p.1.2)).foldl
        (fun s _ ↦ (s.1 / p.1.1, (s.1 % p.1.1) :: s.2)) (p.2, [])).2).length ≤
        p.1.2 * (2 * (encNat p.2).length + 1) := by
      refine (length_encList_le encNat _ (b := (encNat p.2).length) fun x hx ↦ ?_).trans ?_
      · rcases h3 x hx with hnil | hle
        · simp at hnil
        · rw [encNat_apply, encNat_apply, Nat.size_eq_bits_len, Nat.size_eq_bits_len]
          exact Nat.size_le_size hle
      · have hlen_take : ((List.take i (List.range p.1.2)).foldl
            (fun s _ ↦ (s.1 / p.1.1, (s.1 % p.1.1) :: s.2)) (p.2, [])).2.length ≤ p.1.2 := by
          rw [h2, List.length_nil, zero_add]
          exact (List.length_take_le i _).trans (by simpa using hi)
        exact Nat.mul_le_mul_right _ hlen_take
    omega
  exact (snd encNat (encList encNat)).comp hfold

private theorem computableInPolyTime_checkRatFeasible :
    ComputableInPolyTime
      (fun p : (ℕ × List (List ℤ × ℤ)) × List ℚ ↦ checkRatFeasible p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary (encList (encPair (encList encIntBin) encIntBin)))
        (encList encRat))
      encBool := by
  let encRow := encPair (encList encIntBin) encIntBin
  let encIn := encPair (encPair encUnary (encList encRow)) (encList encRat)
  have hp : ComputableInPolyTime (fun q : (ℕ × List (List ℤ × ℤ)) × List ℚ ↦ q.1.1)
      encIn encUnary := (fst _ _).comp (fst _ _)
  have hrows : ComputableInPolyTime (fun q : (ℕ × List (List ℤ × ℤ)) × List ℚ ↦ q.1.2)
      encIn (encList encRow) := (snd _ _).comp (fst _ _)
  have hy : ComputableInPolyTime (fun q : (ℕ × List (List ℤ × ℤ)) × List ℚ ↦ q.2)
      encIn (encList encRat) := snd _ _
  have hdens : ComputableInPolyTime
      (fun q : (ℕ × List (List ℤ × ℤ)) × List ℚ ↦ (List.range q.1.1).map fun j ↦ (q.2.getD j 0).den)
      encIn (encList encNat) :=
    mapWithInput (range.comp hp)
      (rat_den.comp (listGetDWithInput (hy.comp (fst _ _)) (snd _ _) 0))
  have hD : ComputableInPolyTime
      (fun q : (ℕ × List (List ℤ × ℤ)) × List ℚ ↦
        ((List.range q.1.1).map fun j ↦ (q.2.getD j 0).den).foldl (· * ·) 1)
      encIn encNat := by
    have hB : PolyBounded (fun q : (ℕ × List (List ℤ × ℤ)) × List ℚ ↦ (encIn q).length)
        (fun q ↦ q.1.1 * (encList encRat q.2).length + 1) := by
      have h1 : PolyBounded (fun q : (ℕ × List (List ℤ × ℤ)) × List ℚ ↦ (encIn q).length)
          (fun q ↦ q.1.1) := hp.polyBounded_length.mono fun q ↦ by simp [encUnary_apply]
      exact (h1.mul hy.polyBounded_length).add (.const 1)
    refine foldl' hdens (const 1) binary_mul hB fun q i hi ↦ ?_
    have hprod_le : ∀ (l : List ℕ) (acc : ℕ),
        (∀ x ∈ l, x ≤ 2 ^ (encList encRat q.2).length) →
        l.foldl (· * ·) acc ≤ acc * (2 ^ (encList encRat q.2).length) ^ l.length := by
      intro l; induction l with
      | nil => intro acc _; simp
      | cons a t ih =>
        intro acc hall
        have ha : a ≤ 2 ^ (encList encRat q.2).length := hall a List.mem_cons_self
        calc t.foldl (· * ·) (acc * a)
            ≤ (acc * a) * (2 ^ (encList encRat q.2).length) ^ t.length :=
              ih (acc * a) fun x hx ↦ hall x (List.mem_cons_of_mem _ hx)
          _ ≤ (acc * 2 ^ (encList encRat q.2).length) *
                (2 ^ (encList encRat q.2).length) ^ t.length :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ha)
          _ = acc * (2 ^ (encList encRat q.2).length) ^ (t.length + 1) := by rw [Nat.pow_succ]; ring
    have hlt : (((List.range q.1.1).map fun j ↦ (q.2.getD j 0).den).take i).foldl (· * ·) 1 ≤
        2 ^ (q.1.1 * (encList encRat q.2).length) := by
      have h1 := hprod_le (((List.range q.1.1).map fun j ↦ (q.2.getD j 0).den).take i) 1
        fun x hx ↦ by
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hx)
        by_cases hj : j < q.2.length
        · rw [list_getD_eq _ _ _ hj]
          exact (den_lt_two_pow_length_encRat q.2[j]).le.trans
            (Nat.pow_le_pow_right (by omega)
              (length_le_encList_of_mem encRat (List.getElem_mem hj)))
        · rw [list_getD_default _ _ _ (not_lt.mp hj)]; exact Nat.one_le_two_pow
      rw [one_mul, ← Nat.pow_mul] at h1
      have hlen_t : (((List.range q.1.1).map fun j ↦ (q.2.getD j 0).den).take i).length ≤ q.1.1 :=
        (List.length_take_le i _).trans (by simpa using hi)
      rw [Nat.mul_comm q.1.1]
      exact h1.trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hlen_t))
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (hlt.trans_lt (by
      rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := q.1.1 * (encList encRat q.2).length)
      omega))
  have hyScaled : ComputableInPolyTime
      (fun q : (ℕ × List (List ℤ × ℤ)) × List ℚ ↦
        (List.range q.1.1).map fun j ↦
          (q.2.getD j 0).num *
            (((((List.range q.1.1).map fun k ↦ (q.2.getD k 0).den).foldl (· * ·) 1) /
              (q.2.getD j 0).den : ℕ) : ℤ))
      encIn (encList encIntBin) :=
    mapWithInput (range.comp hp)
      (intBin_mul'
        (rat_num.comp (listGetDWithInput (hy.comp (fst _ _)) (snd _ _) 0))
        (intBin_natCast.comp (binary_div' (hD.comp (fst _ _))
          (rat_den.comp (listGetDWithInput (hy.comp (fst _ _)) (snd _ _) 0)))))
  exact allWithInput hrows
    (intBin_le'
      (listDotProduct.comp
        ((hp.comp (fst _ _)).prod (((fst _ _).comp (snd _ _)).prod (hyScaled.comp (fst _ _)))))
      (intBin_mul' ((snd _ _).comp (snd _ _)) (intBin_natCast.comp (hD.comp (fst _ _)))))

private theorem computableInPolyTime_checkIntFeasible :
    ComputableInPolyTime (fun p : BoundedCoeffILPInstance × List ℤ ↦ checkIntFeasible p.1 p.2)
      (encPair encBoundedCoeffILP (encList encIntBin)) encBool := by
  let encIn := encPair encBoundedCoeffILP (encList encIntBin)
  have hx : ComputableInPolyTime (fun p : BoundedCoeffILPInstance × List ℤ ↦ p.2)
      encIn (encList encIntBin) := snd _ _
  have hlo_q : ComputableInPolyTime (fun q : (BoundedCoeffILPInstance × List ℤ) × ℕ ↦ q.1.1.lower)
      (encPair encIn encUnary) (encList encIntBin) := by fun_prop
  have hup_q : ComputableInPolyTime (fun q : (BoundedCoeffILPInstance × List ℤ) × ℕ ↦ q.1.1.upper)
      (encPair encIn encUnary) (encList encIntBin) := by fun_prop
  have hrows_q : ComputableInPolyTime (fun q : (BoundedCoeffILPInstance × List ℤ) × ℕ ↦ q.1.1.rows)
      (encPair encIn encUnary) (encList (encList encIntBin)) := by fun_prop
  have hrhs_q : ComputableInPolyTime (fun q : (BoundedCoeffILPInstance × List ℤ) × ℕ ↦ q.1.1.rhs)
      (encPair encIn encUnary) (encList encIntBin) := by fun_prop
  have hnum_q : ComputableInPolyTime
      (fun q : (BoundedCoeffILPInstance × List ℤ) × ℕ ↦ q.1.1.numVars)
      (encPair encIn encUnary) encUnary := by fun_prop
  have hbox : ComputableInPolyTime
      (fun p : BoundedCoeffILPInstance × List ℤ ↦
        (List.range p.1.numVars).all fun j ↦
          decide (p.1.lower.getD j 0 ≤ p.2.getD j 0) && decide (p.2.getD j 0 ≤ p.1.upper.getD j 0))
      encIn encBool :=
    allWithInput (range.comp (by fun_prop))
      (bool_and'
        (intBin_le' (listGetDWithInput hlo_q (snd _ _) 0)
          (listGetDWithInput (hx.comp (fst _ _)) (snd _ _) 0))
        (intBin_le' (listGetDWithInput (hx.comp (fst _ _)) (snd _ _) 0)
          (listGetDWithInput hup_q (snd _ _) 0)))
  have hrows : ComputableInPolyTime
      (fun p : BoundedCoeffILPInstance × List ℤ ↦
        (List.range p.1.rows.length).all fun i ↦
          decide (ListMatrix.dotProduct p.1.numVars (p.1.rows.getD i []) p.2 ≤ p.1.rhs.getD i 0))
      encIn encBool :=
    allWithInput (range.comp ((length_list (encList encIntBin)).comp (by fun_prop)))
      (intBin_le'
        (listDotProduct.comp (hnum_q.prod
          ((listGetDWithInput hrows_q (snd _ _) []).prod (hx.comp (fst _ _)))))
        (listGetDWithInput hrhs_q (snd _ _) 0))
  exact bool_and' hbox hrows

private theorem computableInPolyTime_factorial :
    ComputableInPolyTime Nat.factorial encUnary encNat := by
  have hinv : ∀ k, (List.range k).foldl (fun acc j ↦ acc * (j + 1)) 1 = k.factorial := by
    intro k; induction k with
    | zero => rfl
    | succ k ihk =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ihk,
        Nat.factorial_succ, Nat.mul_comm]
  have hfold : ComputableInPolyTime
      (fun n : ℕ ↦ (List.range n).foldl (fun acc i ↦ acc * (i + 1)) 1) encUnary encNat := by
    have hstep : ComputableInPolyTime (fun p : ℕ × ℕ ↦ p.1 * (p.2 + 1))
        (encPair encNat encUnary) encNat :=
      binary_mul' (fst _ _) (unary_to_binary.comp (unary_add' (snd _ _) (const 1)))
    have hB : PolyBounded (fun n : ℕ ↦ (encUnary n).length) (fun n ↦ n * (n + 1) + 1) := by
      have h1 : PolyBounded (fun n : ℕ ↦ (encUnary n).length) (fun n ↦ n) :=
        .mono .self fun n ↦ by simp [encUnary_apply]
      exact (h1.mul (h1.add (.const 1))).add (.const 1)
    refine foldl' range (const 1) hstep hB fun n i _ ↦ ?_
    rw [List.take_range, hinv]
    have hle : (min i n).factorial ≤ (min i n + 1) ^ (min i n) := by
      have h1 : ∀ k, k.factorial ≤ (k + 1) ^ k := by
        intro k; induction k with
        | zero => simp
        | succ k ihk =>
          rw [Nat.factorial_succ, Nat.pow_succ]
          calc (k + 1) * k.factorial ≤ (k + 1) ^ k * (k + 1) := by
                rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ ihk
            _ ≤ (k + 2) ^ k * (k + 2) :=
                Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) k) (by omega)
      exact h1 _
    have hpow : (min i n + 1) ^ (min i n) < 2 ^ (n * (n + 1) + 1) := by
      have hm : min i n ≤ n := Nat.min_le_right _ _
      have hbase : min i n + 1 ≤ 2 ^ (n + 1) := by
        have := Nat.lt_two_pow_self (n := n + 1); omega
      calc (min i n + 1) ^ (min i n) ≤ (2 ^ (n + 1)) ^ n :=
            (Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right (by omega) hm)
        _ = 2 ^ ((n + 1) * n) := by rw [← Nat.pow_mul]
        _ = 2 ^ (n * (n + 1)) := by ring_nf
        _ < 2 ^ (n * (n + 1) + 1) := Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _)
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (hle.trans_lt hpow)
  exact hfold.of_enc_eq fun n ↦ congrArg encNat (hinv n).symm

private theorem computableInPolyTime_intProximityDelta :
    ComputableInPolyTime intProximityDelta encBoundedCoeffILP encNat := by
  unfold intProximityDelta
  have hW1 : ComputableInPolyTime (fun inst : BoundedCoeffILPInstance ↦ max 1 (maxAbsCoeff inst))
      encBoundedCoeffILP encNat :=
    (ComputableInPolyTime.ite (binary_le' (const 1) computableInPolyTime_maxAbsCoeff)
      computableInPolyTime_maxAbsCoeff (const 1)).of_enc_eq fun inst ↦ by simp [max_def]
  exact binary_mul' (computableInPolyTime_factorial.comp (by fun_prop))
    (binary_pow' hW1 (by fun_prop))

private theorem computableInPolyTime_vertexStep :
    ComputableInPolyTime vertexStep
      (encPair encBoundedCoeffILP encNat) (encOption (encList encRat)) := by
  let encIn := encPair encBoundedCoeffILP encNat
  let encRow := encPair (encList encIntBin) encIntBin
  have hinst : ComputableInPolyTime (fun p : BoundedCoeffILPInstance × ℕ ↦ p.1)
      encIn encBoundedCoeffILP := fst _ _
  have hrows : ComputableInPolyTime (fun p : BoundedCoeffILPInstance × ℕ ↦ allPolyRows p.1)
      encIn (encList encRow) := computableInPolyTime_allPolyRows.comp hinst
  have hq : ComputableInPolyTime (fun p : BoundedCoeffILPInstance × ℕ ↦ (allPolyRows p.1).length)
      encIn encNat := unary_to_binary.comp ((length_list encRow).comp hrows)
  have hn : ComputableInPolyTime (fun p : BoundedCoeffILPInstance × ℕ ↦ p.1.numVars)
      encIn encUnary := by fun_prop
  have hinds : ComputableInPolyTime
      (fun p : BoundedCoeffILPInstance × ℕ ↦ decodeDigits (allPolyRows p.1).length p.1.numVars p.2)
      encIn (encList encNat) :=
    computableInPolyTime_decodeDigits.comp ((hq.prod hn).prod (snd _ _))
  have hrowLookup : ComputableInPolyTime
      (fun q : (BoundedCoeffILPInstance × ℕ) × ℕ ↦ (allPolyRows q.1.1).getD q.2 ([], 0))
      (encPair encIn encNat) encRow :=
    listGetD_binary ([], 0) (hrows.comp (fst _ _)) (snd _ _)
  have hmatRows : ComputableInPolyTime
      (fun p : BoundedCoeffILPInstance × ℕ ↦
        (decodeDigits (allPolyRows p.1).length p.1.numVars p.2).map fun i ↦
          ((allPolyRows p.1).getD i ([], 0)).1.map fun z : ℤ ↦ (z : ℚ))
      encIn (encList (encList encRat)) :=
    mapWithInput hinds (mapWithInput ((fst _ _).comp hrowLookup) (rat_intCast.comp (snd _ _)))
  have hmat : ComputableInPolyTime
      (fun p : BoundedCoeffILPInstance × ℕ ↦
        ({ numRows := p.1.numVars, numCols := p.1.numVars,
           rows := (decodeDigits (allPolyRows p.1).length p.1.numVars p.2).map fun i ↦
             ((allPolyRows p.1).getD i ([], 0)).1.map fun z : ℤ ↦ (z : ℚ) } : RatTable))
      encIn RatTable.enc := by fun_prop
  have hbVec : ComputableInPolyTime
      (fun p : BoundedCoeffILPInstance × ℕ ↦
        (decodeDigits (allPolyRows p.1).length p.1.numVars p.2).map fun i ↦
          (((allPolyRows p.1).getD i ([], 0)).2 : ℚ))
      encIn (encList encRat) :=
    mapWithInput hinds (rat_intCast.comp ((snd _ _).comp hrowLookup))
  have hsys : ComputableInPolyTime
      (fun p : BoundedCoeffILPInstance × ℕ ↦
        ({ matrix := { numRows := p.1.numVars, numCols := p.1.numVars,
                       rows := (decodeDigits (allPolyRows p.1).length p.1.numVars p.2).map fun i ↦
                         ((allPolyRows p.1).getD i ([], 0)).1.map fun z : ℤ ↦ (z : ℚ) },
           rhs := (decodeDigits (allPolyRows p.1).length p.1.numVars p.2).map fun i ↦
             (((allPolyRows p.1).getD i ([], 0)).2 : ℚ) } : LinearSystemInput))
      encIn LinearSystemInput.enc := by fun_prop
  have hsol : ComputableInPolyTime
      (fun p : BoundedCoeffILPInstance × ℕ ↦
        (ratSolve { matrix := { numRows := p.1.numVars, numCols := p.1.numVars,
                                rows := (decodeDigits (allPolyRows p.1).length p.1.numVars p.2).map
                                  fun i ↦ ((allPolyRows p.1).getD i ([], 0)).1.map
                                    fun z : ℤ ↦ (z : ℚ) },
                    rhs := (decodeDigits (allPolyRows p.1).length p.1.numVars p.2).map fun i ↦
                      (((allPolyRows p.1).getD i ([], 0)).2 : ℚ) }).solution)
      encIn (encOption (encList encRat)) := by
    have := ratSolve_computableInPolyTime.comp hsys
    fun_prop
  exact optionElimWithInput hsol (const none)
    (ComputableInPolyTime.ite
      (computableInPolyTime_checkRatFeasible.comp
        (((hn.comp (fst _ _)).prod (hrows.comp (fst _ _))).prod (snd _ _)))
      ((optionSome _).comp (snd _ _)) (const none))

private theorem computableInPolyTime_intPointStep :
    ComputableInPolyTime intPointStep
      (encPair (encPair encBoundedCoeffILP (encList encRat)) encNat)
      (encOption (encList encIntBin)) := by
  let encP := encPair encBoundedCoeffILP (encList encRat)
  let encIn := encPair encP encNat
  have hinst : ComputableInPolyTime (fun p : (BoundedCoeffILPInstance × List ℚ) × ℕ ↦ p.1.1)
      encIn encBoundedCoeffILP := (fst _ _).comp (fst _ _)
  have hy : ComputableInPolyTime (fun p : (BoundedCoeffILPInstance × List ℚ) × ℕ ↦ p.1.2)
      encIn (encList encRat) := (snd _ _).comp (fst _ _)
  have hΔ : ComputableInPolyTime
      (fun p : (BoundedCoeffILPInstance × List ℚ) × ℕ ↦ intProximityDelta p.1.1) encIn encNat :=
    computableInPolyTime_intProximityDelta.comp hinst
  have hbase : ComputableInPolyTime
      (fun p : (BoundedCoeffILPInstance × List ℚ) × ℕ ↦ 2 * intProximityDelta p.1.1 + 1)
      encIn encNat := binary_add' (binary_mul' (const 2) hΔ) (const 1)
  have hoffs : ComputableInPolyTime
      (fun p : (BoundedCoeffILPInstance × List ℚ) × ℕ ↦
        decodeDigits (2 * intProximityDelta p.1.1 + 1) p.1.1.numVars p.2)
      encIn (encList encNat) :=
    computableInPolyTime_decodeDigits.comp ((hbase.prod (by fun_prop)).prod (snd _ _))
  have hx : ComputableInPolyTime
      (fun p : (BoundedCoeffILPInstance × List ℚ) × ℕ ↦
        (List.range p.1.1.numVars).map fun j ↦
          (p.1.2.getD j 0).floor - (intProximityDelta p.1.1 : ℤ) +
            ((decodeDigits (2 * intProximityDelta p.1.1 + 1) p.1.1.numVars p.2).getD j 0 : ℤ))
      encIn (encList encIntBin) :=
    mapWithInput (range.comp (by fun_prop))
      (intBin_add'
        (intBin_sub'
          (rat_floor.comp (listGetDWithInput (hy.comp (fst _ _)) (snd _ _) 0))
          (intBin_natCast.comp (hΔ.comp (fst _ _))))
        (intBin_natCast.comp (listGetDWithInput (hoffs.comp (fst _ _)) (snd _ _) 0)))
  exact ComputableInPolyTime.ite
    (computableInPolyTime_checkIntFeasible.comp (hinst.prod hx))
    ((optionSome _).comp hx) (const none)

/-- `solveBoundedCoeffILP` is computable in FPT time parameterized by `ilpParam`. -/
theorem computableInFPTTime_solveBoundedCoeffILP :
    ComputableInFPTTime solveBoundedCoeffILP encBoundedCoeffILP encBool ilpParam := by
  let encRow := encPair (encList encIntBin) encIntBin
  have hboundV : ComputableInPolyTime
      (fun inst : BoundedCoeffILPInstance ↦ (allPolyRows inst).length ^ inst.numVars)
      encBoundedCoeffILP encNat :=
    binary_pow' (unary_to_binary.comp ((length_list encRow).comp computableInPolyTime_allPolyRows))
      (by fun_prop)
  have hF_V : ∀ inst : BoundedCoeffILPInstance,
      (allPolyRows inst).length ^ inst.numVars ≤
        ((2 * ilpParam inst + 1) ^ ilpParam inst + 2 * ilpParam inst) ^ ilpParam inst := by
    intro inst
    have hq : (allPolyRows inst).length ≤
      (2 * maxAbsCoeff inst + 1) ^ inst.numVars + 2 * inst.numVars := by
      dsimp only [allPolyRows]
      simp only [List.length_append, List.length_map, List.length_range]
      have := dedupRows_length_le inst; omega
    have h1 : (2 * maxAbsCoeff inst + 1) ^ inst.numVars + 2 * inst.numVars ≤
        (2 * ilpParam inst + 1) ^ ilpParam inst + 2 * ilpParam inst := by
      have hp : inst.numVars ≤ ilpParam inst := Nat.le_add_right _ _
      have hW : maxAbsCoeff inst ≤ ilpParam inst := Nat.le_add_left _ _
      have hpow : (2 * maxAbsCoeff inst + 1) ^ inst.numVars ≤
        (2 * ilpParam inst + 1) ^ ilpParam inst :=
        (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hp)
      omega
    have hbase_pos : 0 < (2 * ilpParam inst + 1) ^ ilpParam inst + 2 * ilpParam inst := by
      have := Nat.one_le_pow (ilpParam inst) (2 * ilpParam inst + 1) (by omega); omega
    exact (Nat.pow_le_pow_left (hq.trans h1) _).trans
      (Nat.pow_le_pow_right hbase_pos (Nat.le_add_right _ _))
  let vStepPair : BoundedCoeffILPInstance × ℕ → Option (BoundedCoeffILPInstance × List ℚ) :=
    fun p ↦ (vertexStep p).map fun y ↦ (p.1, y)
  have hvStepPair : ComputableInPolyTime vStepPair
      (encPair encBoundedCoeffILP encNat)
      (encOption (encPair encBoundedCoeffILP (encList encRat))) :=
    optionMapWithInput computableInPolyTime_vertexStep
      (((fst _ _).comp (fst _ _)).prod (snd _ _))
  have hVpair : ComputableInFPTTime
      (searchFirst vStepPair fun x ↦ (allPolyRows x).length ^ x.numVars)
      encBoundedCoeffILP (encOption (encPair encBoundedCoeffILP (encList encRat))) ilpParam :=
    computableInFPTTime_searchFirst (F := fun k ↦ ((2 * k + 1) ^ k + 2 * k) ^ k)
      hvStepPair hboundV hF_V
  -- Phase 2 on `Option (BoundedCoeffILPInstance × List ℚ)` via `searchFirst`:
  let optStep : Option (BoundedCoeffILPInstance × List ℚ) × ℕ → Option (List ℤ) :=
    fun q ↦ q.1.elim none fun p ↦ intPointStep (p, q.2)
  let optBound : Option (BoundedCoeffILPInstance × List ℚ) → ℕ :=
    fun opt ↦ opt.elim 0 fun p ↦ (2 * intProximityDelta p.1 + 1) ^ p.1.numVars
  let κOpt : Option (BoundedCoeffILPInstance × List ℚ) → ℕ :=
    fun opt ↦ opt.elim 0 fun p ↦ ilpParam p.1
  have hoptStep : ComputableInPolyTime optStep
      (encPair (encOption (encPair encBoundedCoeffILP (encList encRat))) encNat)
      (encOption (encList encIntBin)) :=
    optionElimWithInput (fst _ _) (const none)
      (computableInPolyTime_intPointStep.comp ((snd _ _).prod ((snd _ _).comp (fst _ _))))
  have hoptBound : ComputableInPolyTime optBound
      (encOption (encPair encBoundedCoeffILP (encList encRat))) encNat :=
    optionElimWithInput id' (const 0)
      (binary_pow'
        (binary_add' (binary_mul' (const 2)
          (computableInPolyTime_intProximityDelta.comp ((fst _ _).comp (snd _ _)))) (const 1))
        (by fun_prop))
  have hF_I : ∀ opt : Option (BoundedCoeffILPInstance × List ℚ),
      optBound opt ≤
        (2 * (κOpt opt).factorial * (max 1 (κOpt opt)) ^ (κOpt opt) + 1) ^ (κOpt opt) := by
    intro opt
    cases opt with
    | none => simp [optBound]
    | some p =>
      simp only [optBound, κOpt, intProximityDelta, Option.elim_some]
      have hp : p.1.numVars ≤ ilpParam p.1 := Nat.le_add_right _ _
      have hW : maxAbsCoeff p.1 ≤ ilpParam p.1 := Nat.le_add_left _ _
      have hfac : p.1.numVars.factorial ≤ (ilpParam p.1).factorial := Nat.factorial_le hp
      have hpow1 : (max 1 (maxAbsCoeff p.1)) ^ p.1.numVars ≤
          (max 1 (ilpParam p.1)) ^ (ilpParam p.1) :=
        (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hp)
      have hΔ : 2 * (p.1.numVars.factorial * (max 1 (maxAbsCoeff p.1)) ^ p.1.numVars) ≤
          2 * ((ilpParam p.1).factorial * (max 1 (ilpParam p.1)) ^ (ilpParam p.1)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul hfac hpow1)
      have hbase_le : 2 * (p.1.numVars.factorial * (max 1 (maxAbsCoeff p.1)) ^ p.1.numVars) + 1 ≤
          2 * (ilpParam p.1).factorial * (max 1 (ilpParam p.1)) ^ (ilpParam p.1) + 1 := by
        rw [Nat.mul_assoc]; exact Nat.add_le_add_right hΔ 1
      exact (Nat.pow_le_pow_left hbase_le _).trans (Nat.pow_le_pow_right (by omega) hp)
  have hI : ComputableInFPTTime (searchFirst optStep optBound)
      (encOption (encPair encBoundedCoeffILP (encList encRat)))
      (encOption (encList encIntBin)) κOpt :=
    computableInFPTTime_searchFirst (F := fun k ↦ (2 * k.factorial * (max 1 k) ^ k + 1) ^ k)
      hoptStep hoptBound hF_I
  have hphase2 : ComputableInFPTTime
      (fun inst ↦ (searchFirst optStep optBound
        (searchFirst vStepPair (fun x ↦ (allPolyRows x).length ^ x.numVars) inst)).isSome)
      encBoundedCoeffILP encBool ilpParam := by
    have hcomp1 : ComputableInFPTTime
        (fun inst ↦ searchFirst optStep optBound
          (searchFirst vStepPair (fun x ↦ (allPolyRows x).length ^ x.numVars) inst))
        encBoundedCoeffILP (encOption (encList encIntBin)) ilpParam :=
      hI.comp hVpair (h := id) fun inst ↦ by
        cases h : searchFirst vStepPair (fun x ↦ (allPolyRows x).length ^ x.numVars) inst with
        | none => simp [κOpt]
        | some p =>
          obtain ⟨idx, _, hst, _⟩ := searchFirst_eq_some_iff.mp h
          dsimp only [vStepPair] at hst
          cases hv : vertexStep (inst, idx) with
          | none => simp [hv] at hst
          | some y =>
            simp only [hv, Option.map_some, Option.some.injEq] at hst
            subst hst; simp [κOpt]
    exact ((optionIsSome id').computableInFPTTime (fun _ ↦ 0)).comp hcomp1 (h := id) fun _ ↦
      Nat.zero_le _
  have hzero : ComputableInPolyTime
      (fun inst : BoundedCoeffILPInstance ↦
        (List.range inst.rows.length).all fun i ↦ decide (0 ≤ inst.rhs.getD i 0))
      encBoundedCoeffILP encBool := by
    have hrhs_p : ComputableInPolyTime (fun p : BoundedCoeffILPInstance × ℕ ↦ p.1.rhs)
        (encPair encBoundedCoeffILP encUnary) (encList encIntBin) := by fun_prop
    exact allWithInput (range.comp ((length_list (encList encIntBin)).comp (by fun_prop)))
      (intBin_le' (const 0) (listGetDWithInput hrhs_p (snd _ _) 0))
  have hcond : ComputableInPolyTime
      (fun inst : BoundedCoeffILPInstance ↦ decide (inst.numVars = 0))
      encBoundedCoeffILP encBool := by
    have hnv : ComputableInPolyTime (fun inst : BoundedCoeffILPInstance ↦ inst.numVars)
        encBoundedCoeffILP encUnary := by fun_prop
    exact (unary_beq hnv (const 0)).of_enc_eq fun inst ↦ by simp [beq_eq_decide]
  have hite : ComputableInFPTTime
      (fun inst : BoundedCoeffILPInstance ↦
        if decide (inst.numVars = 0) = true then
          (List.range inst.rows.length).all fun i ↦ decide (0 ≤ inst.rhs.getD i 0)
        else
          (searchFirst optStep optBound
            (searchFirst vStepPair (fun x ↦ (allPolyRows x).length ^ x.numVars) inst)).isSome)
      encBoundedCoeffILP encBool ilpParam :=
    ComputableInFPTTime.ite (hcond.computableInFPTTime ilpParam)
      (hzero.computableInFPTTime ilpParam) hphase2
  refine computableInFPTTime_congr hite fun inst ↦ ?_
  unfold solveBoundedCoeffILP
  simp only [decide_eq_true_eq]
  split_ifs with h0
  · rfl
  · have hv_map : searchFirst vStepPair (fun x ↦ (allPolyRows x).length ^ x.numVars) inst =
        (findRationalVertex inst).map (fun y ↦ (inst, y)) := by
      ext p; simp only [searchFirst_eq_some_iff, Option.map_eq_some_iff,
        findRationalVertex, vStepPair]
      constructor
      · rintro ⟨i, hi, ⟨y, hy, rfl⟩, hprev⟩
        refine ⟨y, ⟨i, hi, hy, fun j hj ↦ ?_⟩, rfl⟩
        have := hprev j hj; cases hv : vertexStep (inst, j) <;> simp [hv] at this ⊢
      · rintro ⟨y, ⟨i, hi, hy, hprev⟩, rfl⟩
        exact ⟨i, hi, ⟨y, hy, rfl⟩, fun j hj ↦ by simp [hprev j hj]⟩
    rw [hv_map]
    cases findRationalVertex inst with
    | none =>
      simp only [Option.map_none, Option.bind_none, Option.isSome_none, Option.isSome_eq_false_iff]
      cases h : searchFirst optStep optBound none with
      | none => rfl
      | some x => obtain ⟨_, hi, _⟩ := searchFirst_eq_some_iff.mp h; simp [optBound] at hi
    | some y =>
      simp only [Option.map_some, Option.bind_some]
      congr 1; ext x; simp only [findIntegerPoint, searchFirst_eq_some_iff,
        optStep, optBound, Option.elim_some]

/-- Bounded-coefficient ILP feasibility belongs to `FPT` parameterized by
`numVars + maxAbsCoeff`. -/
theorem BoundedCoeffILP_mem_FPT :
    BoundedCoeffILP ∈ FPT encBoundedCoeffILP ilpParam := by
  rw [mem_FPT_iff_computableInFPTTime]
  exact ⟨solveBoundedCoeffILP, computableInFPTTime_solveBoundedCoeffILP,
    fun inst ↦ (solveBoundedCoeffILP_eq_true_iff inst).symm⟩

end CslibFrontier.Complexity

