/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.BranchingProgram.MonoidProgram

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

/-!
# Acceptance, Closure, and Counting Bounds for Programs over Monoids

This module develops general set-acceptance semantics (`MonoidProgram.Decides`), Boolean and
monoid-division closure lemmas, a linear length lower bound for `n`-ary conjunction over arbitrary
monoids, and the finite-monoid slice counting bound for `Cslib.BranchingPrograms.MonoidProgram`
:

## Main definitions

* `CslibFrontier.BranchingPrograms.MonoidProgram.Decides`: a program `P : MonoidProgram ι α M`
  decides `f : (ι → α) → Bool` via `F : Set M` when `∀ x, f x = true ↔ P.eval x ∈ F`.
* `CslibFrontier.BranchingPrograms.RecognizableSlices`: the set of Boolean functions
  `(Fin n → Bool) → Bool` decided by a program of length at most `l` over some monoid of
  cardinality `i`.

## Main results

* `CslibFrontier.BranchingPrograms.MonoidProgram.Decides.not`,
  `CslibFrontier.BranchingPrograms.MonoidProgram.Decides.and`,
  `CslibFrontier.BranchingPrograms.MonoidProgram.Decides.or`: complementation without length
  increase, and conjunction/disjunction over `M × N` with additive length.
* `CslibFrontier.BranchingPrograms.MonoidProgram.Decides.of_divides`: length-preserving lifting of
  programs along a surjective monoid homomorphism `g : S →* M` from a submonoid `S : Submonoid N`.
* `CslibFrontier.BranchingPrograms.not_decides_allTrue_of_length_lt`: any program over any monoid
  deciding the `n`-bit AND function has length at least `n`.
* `CslibFrontier.BranchingPrograms.card_recognizableSlices_le` and
  `CslibFrontier.BranchingPrograms.card_recognizableSlices_le_max`: the number of `n`-bit Boolean
  functions decided by programs of length `≤ l` over monoids of size `i > 0` is at most
  `i ^ (i ^ 2) * 2 ^ i * (n * i ^ 2) ^ l` when `0 < n ∨ l = 0` (and at most
  `i ^ (i ^ 2) * 2 ^ i * (max n 1 * i ^ 2) ^ l` for all `n, l : ℕ`).
-/

public section

namespace CslibFrontier.BranchingPrograms

open Cslib.BranchingPrograms

namespace MonoidProgram

variable {ι α M N : Type*} [Monoid M] [Monoid N]

/-- A program `P` over `M` **decides** `f : (ι → α) → Bool` via acceptance set `F : Set M` when
`P.eval x ∈ F` holds if and only if `f x = true`. -/
@[expose]
def Decides (P : MonoidProgram ι α M) (F : Set M) (f : (ι → α) → Bool) : Prop :=
  ∀ x : ι → α, f x = true ↔ P.eval x ∈ F

/-- Every `σ`-computing program (`σ ≠ 1`) decides `f` via `{σ}`. -/
theorem Decides.of_computes {P : MonoidProgram ι α M} {σ : M} (hσ : σ ≠ 1)
    {f : (ι → α) → Bool} (h : P.Computes σ f) : Decides P {σ} f := fun x ↦ by
  rw [h x, Set.mem_singleton_iff]
  cases f x <;> simp [hσ.symm]

/-- Complementing the acceptance set negates the decided function with identical program length. -/
theorem Decides.not {P : MonoidProgram ι α M} {F : Set M} {f : (ι → α) → Bool}
    (h : Decides P F f) : Decides P Fᶜ (fun x ↦ !f x) := fun x ↦ by
  rw [Bool.not_eq_true', ← Bool.not_eq_true, h x, Set.mem_compl_iff]

/-- Conjunction of two decided functions via the product monoid `M × N` in additive length. -/
theorem Decides.and {P : MonoidProgram ι α M} {F : Set M} {f : (ι → α) → Bool}
    {Q : MonoidProgram ι α N} {G : Set N} {g : (ι → α) → Bool}
    (hP : Decides P F f) (hQ : Decides Q G g) :
    Decides (P.map (MonoidHom.inl M N) * Q.map (MonoidHom.inr M N))
      (F ×ˢ G) (fun x ↦ f x && g x) := fun x ↦ by
  rw [Bool.and_eq_true, hP x, hQ x, MonoidProgram.eval_mul, MonoidProgram.eval_map,
    MonoidProgram.eval_map]
  simp [MonoidHom.inl_apply, MonoidHom.inr_apply, Set.mem_prod]

/-- Disjunction of two decided functions via the product monoid `M × N` in additive length. -/
theorem Decides.or {P : MonoidProgram ι α M} {F : Set M} {f : (ι → α) → Bool}
    {Q : MonoidProgram ι α N} {G : Set N} {g : (ι → α) → Bool}
    (hP : Decides P F f) (hQ : Decides Q G g) :
    Decides (P.map (MonoidHom.inl M N) * Q.map (MonoidHom.inr M N))
      {p : M × N | p.1 ∈ F ∨ p.2 ∈ G} (fun x ↦ f x || g x) := fun x ↦ by
  rw [Bool.or_eq_true, hP x, hQ x, MonoidProgram.eval_mul, MonoidProgram.eval_map,
    MonoidProgram.eval_map]
  simp [MonoidHom.inl_apply, MonoidHom.inr_apply]

/-- Division invariance: if `g : S →* M` is a surjective homomorphism from a submonoid
`S : Submonoid N`, every program `P` over `M` lifts to a program `P'` over `N` of identical length
deciding the same function. -/
theorem Decides.of_divides {P : MonoidProgram ι α M} {F : Set M} {f : (ι → α) → Bool}
    (hP : Decides P F f) (S : Submonoid N) (g : S →* M) (hg : Function.Surjective g) :
    ∃ (P' : MonoidProgram ι α N) (F' : Set N),
      P'.toList.length = P.toList.length ∧ Decides P' F' f := by
  classical
  let liftElem : M → S := fun m ↦ Classical.choose (hg m)
  have hlift : ∀ m : M, g (liftElem m) = m := fun m ↦ Classical.choose_spec (hg m)
  let P' : MonoidProgram ι α N :=
    FreeMonoid.map (Instruction.map (fun m ↦ (liftElem m : N))) P
  let F' : Set N := Subtype.val '' (g ⁻¹' F)
  refine ⟨P', F', by simp [P'], fun x ↦ ?_⟩
  rw [hP x]
  have hprod : ∀ L : List (Instruction ι α M),
      ∃ s : S, ((L.map (Instruction.map (fun m ↦ (liftElem m : N)))).map (·.eval x)).prod = s.1 ∧
        g s = (L.map (·.eval x)).prod := by
    intro L
    induction L with
    | nil => exact ⟨1, rfl, map_one g⟩
    | cons I rest ih =>
      rcases ih with ⟨s, hs1, hs2⟩
      refine ⟨liftElem (I.eval x) * s, ?_, ?_⟩
      · rw [List.map_cons, List.map_cons, List.prod_cons, Instruction.eval_map, hs1,
          Submonoid.coe_mul]
      · simp [map_mul, hlift, hs2]
  obtain ⟨s, hs1, hs2⟩ := hprod P.toList
  have hev' : P'.eval x = s.1 := by
    rw [MonoidProgram.eval_eq_prod]
    exact hs1
  rw [MonoidProgram.eval_eq_prod, ← hs2, hev']
  simp [F']

end MonoidProgram

/-- Sensitivity lower bound: no program of length strictly less than `n` over any monoid `M` can
decide the `n`-ary conjunction `∀ i, x i = true`. -/
theorem not_decides_allTrue_of_length_lt {n : ℕ} {M : Type*} [Monoid M]
    (P : MonoidProgram (Fin n) Bool M) (F : Set M) (hlen : P.toList.length < n) :
    ¬ MonoidProgram.Decides P F (fun x ↦ decide (∀ i : Fin n, x i = true)) := by
  classical
  intro hdec
  let Vars : Finset (Fin n) := (P.toList.map Instruction.var).toFinset
  have hVars_lt : Vars.card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (le_trans (List.toFinset_card_le _) (by simp)) hlen
  have hnot_sub : ¬ Finset.univ ⊆ Vars := fun h ↦ not_le_of_gt hVars_lt (Finset.card_le_card h)
  obtain ⟨i₀, _, hi₀_out⟩ := Finset.not_subset.mp hnot_sub
  let x₁ : Fin n → Bool := fun _ ↦ true
  let x₂ : Fin n → Bool := Function.update x₁ i₀ false
  have hPeval : P.eval x₁ = P.eval x₂ := by
    rw [MonoidProgram.eval_eq_prod, MonoidProgram.eval_eq_prod]
    congr 1
    refine List.map_congr_left fun I hI ↦ ?_
    have hne : I.var ≠ i₀ := fun hEq ↦
      hi₀_out (hEq ▸ List.mem_toFinset.mpr (List.mem_map_of_mem hI))
    simp [Instruction.eval, x₂, Function.update_of_ne hne]
  have h1 : P.eval x₁ ∈ F := (hdec x₁).mp (decide_eq_true fun _ ↦ rfl)
  have h2 : ¬ (decide (∀ i : Fin n, x₂ i = true) = true) := by
    rw [decide_eq_true_eq]
    intro hall
    have := hall i₀
    simp [x₂] at this
  exact h2 ((hdec x₂).mpr (hPeval ▸ h1))

/-- The set of `n`-bit Boolean functions decided by a program of length at most `l` over some
monoid of cardinality `i`. -/
@[expose]
def RecognizableSlices (i n l : ℕ) : Set ((Fin n → Bool) → Bool) :=
  {f | ∃ (M : Type) (_ : Monoid M) (_ : Fintype M), Fintype.card M = i ∧
    ∃ (P : MonoidProgram (Fin n) Bool M) (F : Set M),
      MonoidProgram.Decides P F f ∧ P.toList.length ≤ l}

noncomputable instance instFintypeRecognizableSlices (i n l : ℕ) :
    Fintype (RecognizableSlices i n l) :=
  Fintype.ofFinite _

/-- Counting bound on `n`-bit Boolean functions decided by programs of length `≤ l` over a monoid
of size `i > 0` when `0 < n ∨ l = 0`. -/
theorem card_recognizableSlices_le {i n l : ℕ} (hi : 0 < i) (hnl : 0 < n ∨ l = 0) :
    Fintype.card (RecognizableSlices i n l) ≤ i ^ (i ^ 2) * 2 ^ i * (n * i ^ 2) ^ l := by
  classical
  rcases hnl with hn | rfl
  · let Code := ((Fin i × Fin i) → Fin i) × (Fin i → Bool) × (Fin l → Fin n × (Bool → Fin i))
    let evalCode : Code → ((Fin n → Bool) → Bool) := fun ⟨mulOp, accPred, prog⟩ x ↦
      if h1 : ∃ e : Fin i, ∀ a : Fin i, mulOp (e, a) = a ∧ mulOp (a, e) = a then
        let e₀ := Classical.choose h1
        let res := (List.finRange l).foldl
          (fun acc r ↦ mulOp (acc, (prog r).2 (x (prog r).1))) e₀
        accPred res
      else false
    have hsurj_sub : ∀ s : RecognizableSlices i n l, ∃ c : Code, evalCode c = s.1 := by
      rintro ⟨f, M, instM, instFM, hcardM, P, F, hPF, hPlen⟩
      let _ : Monoid M := instM
      let _ : Fintype M := instFM
      let eqv : M ≃ Fin i := (Fintype.equivFin M).trans (finCongr hcardM)
      let mulOp : Fin i × Fin i → Fin i := fun p ↦ eqv (eqv.symm p.1 * eqv.symm p.2)
      have hid : ∃ e : Fin i, ∀ a : Fin i, mulOp (e, a) = a ∧ mulOp (a, e) = a :=
        ⟨eqv 1, fun a ↦ by dsimp [mulOp]; simp⟩
      let e₀ := Classical.choose hid
      have he₀_eq : e₀ = eqv 1 := by
        have hspec := Classical.choose_spec hid (eqv 1)
        have h1 : mulOp (e₀, eqv 1) = e₀ := by
          dsimp [mulOp]; rw [Equiv.symm_apply_apply, mul_one, Equiv.apply_symm_apply]
        exact h1.symm.trans hspec.1
      let accPred : Fin i → Bool := fun a ↦ decide (eqv.symm a ∈ F)
      let prog : Fin l → Fin n × (Bool → Fin i) := fun r ↦
        if hr : r.val < P.toList.length then
          ((P.toList[r.val]'hr).var, fun b ↦ eqv ((P.toList[r.val]'hr).select b))
        else
          (⟨0, hn⟩, fun _ ↦ eqv 1)
      refine ⟨(mulOp, accPred, prog), funext fun x ↦ ?_⟩
      dsimp [evalCode]
      simp only [hid, ↓reduceDIte]
      change accPred ((List.finRange l).foldl
        (fun acc r ↦ mulOp (acc, (prog r).2 (x (prog r).1))) e₀) = f x
      have hfold_eq : ∀ (m : ℕ) (hm : m ≤ l),
          ((List.finRange l).take m).foldl
            (fun acc r ↦ mulOp (acc, (prog r).2 (x (prog r).1))) e₀ =
            eqv (((P.toList.take m).map (fun I ↦ I.eval x)).prod) := by
        intro m; induction m with
        | zero => intro _; simp [he₀_eq]
        | succ m ihm =>
          intro hm
          have hm_lt : m < l := Nat.lt_of_succ_le hm
          have hm_fr : m < (List.finRange l).length := by simp [hm_lt]
          rw [List.take_succ_eq_append_getElem hm_fr, List.foldl_append, List.foldl_cons,
            List.foldl_nil, List.getElem_finRange, ihm (Nat.le_of_lt hm_lt)]
          dsimp [mulOp, prog]
          by_cases hr : m < P.toList.length
          · simp only [hr, ↓reduceDIte, Equiv.symm_apply_apply]
            rw [List.take_succ_eq_append_getElem hr, List.map_append, List.prod_append,
              List.map_singleton, List.prod_singleton]
            rfl
          · simp only [hr, ↓reduceDIte, Equiv.symm_apply_apply, mul_one]
            have hge : P.toList.length ≤ m := Nat.not_lt.mp hr
            rw [List.take_of_length_le (le_trans hge (Nat.le_succ m)),
              List.take_of_length_le hge]
      have hfull := hfold_eq l le_rfl
      rw [show (List.finRange l).take l = List.finRange l by simp,
        List.take_of_length_le hPlen, ← MonoidProgram.eval_eq_prod] at hfull
      rw [hfull]
      dsimp [accPred]
      rw [Equiv.symm_apply_apply]
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq, ← hPF x]
    let pickCode : RecognizableSlices i n l → Code := fun s ↦ Classical.choose (hsurj_sub s)
    have hpick_inj : Function.Injective pickCode := fun s₁ s₂ hEq ↦ Subtype.ext <| by
      dsimp [pickCode] at hEq
      rw [← Classical.choose_spec (hsurj_sub s₁), ← Classical.choose_spec (hsurj_sub s₂), hEq]
    have hcard_le : Fintype.card (RecognizableSlices i n l) ≤ Fintype.card Code :=
      Fintype.card_le_of_injective pickCode hpick_inj
    have hCode_card : Fintype.card Code = i ^ (i ^ 2) * 2 ^ i * (n * i ^ 2) ^ l := by
      dsimp [Code]
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      rw [show i * i = i ^ 2 by ring, Nat.mul_assoc]
    rwa [hCode_card] at hcard_le
  · have hconst : ∀ s : RecognizableSlices i n 0, ∃ b : Bool, s.1 = fun _ ↦ b := by
      rintro ⟨f, M, instM, _, _, P, F, hPF, hPlen⟩
      let _ : Monoid M := instM
      have hP1 : P.toList = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hPlen)
      refine ⟨decide ((1 : M) ∈ F), funext fun x ↦ ?_⟩
      apply Bool.eq_iff_iff.mpr
      rw [hPF x, decide_eq_true_eq, MonoidProgram.eval_eq_prod, hP1]
      simp
    let pickB : RecognizableSlices i n 0 → Bool := fun s ↦ Classical.choose (hconst s)
    have hinjB : Function.Injective pickB := fun s₁ s₂ hEq ↦ Subtype.ext <| by
      dsimp [pickB] at hEq
      rw [Classical.choose_spec (hconst s₁), Classical.choose_spec (hconst s₂), hEq]
    have hle2 : Fintype.card (RecognizableSlices i n 0) ≤ 2 := by
      simpa using Fintype.card_le_of_injective pickB hinjB
    have hge2 : 2 ≤ i ^ (i ^ 2) * 2 ^ i * (n * i ^ 2) ^ 0 := by
      rw [pow_zero, Nat.mul_one]
      have h1 : 1 ≤ i ^ (i ^ 2) := Nat.one_le_pow _ _ hi
      have h2 : 2 ≤ 2 ^ i :=
        le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hi)
      exact le_trans h2 (Nat.le_mul_of_pos_left _ h1)
    exact le_trans hle2 hge2

/-- All-`(n, l)` counting bound replacing `n` by `max n 1`. -/
theorem card_recognizableSlices_le_max {i : ℕ} (hi : 0 < i) (n l : ℕ) :
    Fintype.card (RecognizableSlices i n l) ≤
      i ^ (i ^ 2) * 2 ^ i * (max n 1 * i ^ 2) ^ l := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hconst : ∀ s : RecognizableSlices i 0 l, ∃ b : Bool, s.1 = fun _ ↦ b := by
      rintro ⟨f, _, _, _, _, _, _, _, _⟩
      exact ⟨f Fin.elim0, funext fun x ↦ congrArg f (Subsingleton.elim x Fin.elim0)⟩
    let pickB : RecognizableSlices i 0 l → Bool := fun s ↦ Classical.choose (hconst s)
    have hinjB : Function.Injective pickB := fun s₁ s₂ hEq ↦ Subtype.ext <| by
      dsimp [pickB] at hEq
      rw [Classical.choose_spec (hconst s₁), Classical.choose_spec (hconst s₂), hEq]
    have hle2 : Fintype.card (RecognizableSlices i 0 l) ≤ 2 := by
      simpa using Fintype.card_le_of_injective pickB hinjB
    have hge2 : 2 ≤ i ^ (i ^ 2) * 2 ^ i * (max 0 1 * i ^ 2) ^ l := by
      have h1 : 1 ≤ i ^ (i ^ 2) := Nat.one_le_pow _ _ hi
      have h2 : 1 ≤ (max 0 1 * i ^ 2) ^ l :=
        Nat.one_le_pow _ _ (Nat.mul_pos (by decide) (Nat.pow_pos hi))
      have h3 : 2 ≤ 2 ^ i := le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hi)
      calc
        2 ≤ 1 * 2 ^ i * 1 := by simp [h3]
        _ ≤ i ^ (i ^ 2) * 2 ^ i * (max 0 1 * i ^ 2) ^ l :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ h1) h2
    exact le_trans hle2 hge2
  · rw [Nat.max_eq_left hn]
    exact card_recognizableSlices_le hi (Or.inl hn)

end CslibFrontier.BranchingPrograms
