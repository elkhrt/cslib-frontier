/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/
module
-- upstream: candidate

public import Cslib.Computability.QueryComplexity.Measures
public import CslibFrontier.Computability.Communication.Amplification
public import CslibFrontier.Computability.Communication.Corruption
public import CslibFrontier.Computability.Communication.Nondeterministic.UniqueDisjointness
public import CslibFrontier.Computability.Communication.Randomized

import CslibFrontier.Foundations.Combinatorics.PowersetTail
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# $\mathrm{AND}$-Lifted Communication, Monotone Block Sensitivity, and Unique Disjointness

This module develops two-party $\mathrm{AND}$-lifted Boolean communication problems
`(f ∘ AND₂)(x, y) = f(x₁ ∧ y₁, …, x_n ∧ y_n)`, monotone zero-block sensitivity `mbs(f)`,
zero-communication reductions from the unique set disjointness promise problem `UDISJ_{mbs(f)}` to
`f ∘ AND₂`, and a linear public-coin randomized communication complexity lower bound for unique set
disjointness via partition corruption.

## Main definitions

* `CslibFrontier.Communication.andLift`: two-party $\mathrm{AND}$-lifted Boolean function.
* `CslibFrontier.Communication.IsZeroBlock`, `CslibFrontier.Communication.IsSensitiveZeroBlock`,
  `CslibFrontier.Communication.IsMonotoneSensitiveFamily`,
  `CslibFrontier.Communication.monotoneBlockSensitivityAt`,
  `CslibFrontier.Communication.monotoneBlockSensitivity`: monotone zero-block sensitivity on the
  Boolean hypercube.

## Main results

* `CslibFrontier.Communication.one_le_monotoneBlockSensitivity_of_nonconst`: every non-constant
  Boolean function has monotone block sensitivity at least `1`.
* `CslibFrontier.Communication.exists_udisj_embedding_of_monotoneBlockSensitivity` and
  `CslibFrontier.Communication.rcc_uniqueDisjointness_le_rccFun_andLift`: submatrix embedding of
  `UDISJ_{mbs(f)}` into `f ∘ AND₂` up to output negation and public-coin communication reduction.
* `CslibFrontier.Communication.le_mul_rcc_uniqueDisjointness_add`: linear lower bound
  `k ≤ 2 ^ 16 * Rcc_{1/3}(UDISJ_k) + 2 ^ 12` for unique set disjointness.
-/

public section

open Finset
open scoped BigOperators ENNReal NNReal

namespace CslibFrontier.Communication

/-- Two-party $\mathrm{AND}$-lifted function `(f ∘ AND₂)(x, y) = f(x₁ ∧ y₁, …, x_n ∧ y_n)`. -/
@[expose]
def andLift {n : ℕ} (f : Cslib.BooleanFunction n) (x y : Cslib.BitString n) : Bool :=
  f fun i ↦ x i && y i

/-- `B` is a `0`-block of `x` if `x i = false` for all `i ∈ B`. -/
@[expose]
def IsZeroBlock {n : ℕ} (x : Cslib.BitString n) (B : Cslib.QueryComplexity.Block n) : Prop :=
  ∀ i ∈ B, x i = false

instance {n : ℕ} (x : Cslib.BitString n) (B : Cslib.QueryComplexity.Block n) :
    Decidable (IsZeroBlock x B) :=
  inferInstanceAs (Decidable (∀ i ∈ B, x i = false))

/-- `B` is a sensitive `0`-block of `f` at `x` if `x|_B = 0` and flipping `B` to `1` flips `f`. -/
@[expose]
def IsSensitiveZeroBlock {n : ℕ} (f : Cslib.BooleanFunction n) (x : Cslib.BitString n)
    (B : Cslib.QueryComplexity.Block n) : Prop :=
  IsZeroBlock x B ∧ Cslib.QueryComplexity.IsSensitiveBlock f x B

instance {n : ℕ} (f : Cslib.BooleanFunction n) (x : Cslib.BitString n)
    (B : Cslib.QueryComplexity.Block n) :
    Decidable (IsSensitiveZeroBlock f x B) :=
  inferInstanceAs (Decidable (IsZeroBlock x B ∧ Cslib.QueryComplexity.IsSensitiveBlock f x B))

/-- Pairwise disjoint family of sensitive `0`-blocks of `f` at `x`. -/
@[expose]
def IsMonotoneSensitiveFamily {n : ℕ} (f : Cslib.BooleanFunction n) (x : Cslib.BitString n)
    (F : Finset (Cslib.QueryComplexity.Block n)) : Prop :=
  (∀ B ∈ F, IsSensitiveZeroBlock f x B) ∧
    (F : Set (Cslib.QueryComplexity.Block n)).PairwiseDisjoint id

instance {n : ℕ} (f : Cslib.BooleanFunction n) (x : Cslib.BitString n)
    (F : Finset (Cslib.QueryComplexity.Block n)) :
    Decidable (IsMonotoneSensitiveFamily f x F) :=
  decidable_of_iff
    ((∀ B ∈ F, IsSensitiveZeroBlock f x B) ∧ ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → Disjoint P Q)
    ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, fun ⦃P⦄ hP ⦃Q⦄ hQ hne ↦ h2 P hP Q hQ hne⟩,
     fun ⟨h1, h2⟩ ↦ ⟨h1, fun _ hP _ hQ hne ↦ h2 hP hQ hne⟩⟩

/-- Pointwise monotone block sensitivity `mbs(f, x)`. -/
@[expose]
def monotoneBlockSensitivityAt {n : ℕ} (f : Cslib.BooleanFunction n)
    (x : Cslib.BitString n) : ℕ :=
  (univ.filter (IsMonotoneSensitiveFamily f x)).sup Finset.card

/-- Monotone block sensitivity `mbs(f) = max_x mbs(f, x)`. -/
@[expose]
def monotoneBlockSensitivity {n : ℕ} (f : Cslib.BooleanFunction n) : ℕ :=
  univ.sup (monotoneBlockSensitivityAt f)

/-- Every non-constant Boolean function `f` satisfies `1 ≤ monotoneBlockSensitivity f`. -/
theorem one_le_monotoneBlockSensitivity_of_nonconst {n : ℕ} {f : Cslib.BooleanFunction n}
    (h : ∃ x₁ x₂, f x₁ ≠ f x₂) :
    1 ≤ monotoneBlockSensitivity f := by
  obtain ⟨x₁, x₂, hne⟩ := h
  let z0 : Cslib.BitString n := fun _ ↦ false
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ f z0 := by
    by_cases h1 : f x₁ = f z0
    · exact ⟨x₂, fun h2 ↦ hne (h1.trans h2.symm)⟩
    · exact ⟨x₁, h1⟩
  let B : Cslib.QueryComplexity.Block n := univ.filter fun i ↦ x i = true
  have hflip : Cslib.BitString.flipBlock B z0 = x := by
    funext i
    simp only [Cslib.BitString.flipBlock, B, mem_filter, mem_univ, true_and, z0]
    cases hx_i : x i <;> simp
  have hfam : IsMonotoneSensitiveFamily f z0 {B} := by
    refine ⟨fun B' hB' ↦ ?_, by rw [coe_singleton]; exact Set.pairwiseDisjoint_singleton B id⟩
    rw [mem_singleton.mp hB']
    refine ⟨fun _ _ ↦ rfl, ?_⟩
    rw [Cslib.QueryComplexity.IsSensitiveBlock, hflip]
    exact hx
  have h1 : 1 ≤ monotoneBlockSensitivityAt f z0 := by
    have hmem : ({B} : Finset (Cslib.QueryComplexity.Block n)) ∈
        univ.filter (IsMonotoneSensitiveFamily f z0) :=
      mem_filter.mpr ⟨mem_univ _, hfam⟩
    exact (card_singleton B).symm.trans_le (Finset.le_sup hmem)
  exact h1.trans (Finset.le_sup (mem_univ z0))

/-- Submatrix embedding of `uniqueDisjointnessRel (Fin k)` into `andLift f` up to output negation
whenever `k ≤ monotoneBlockSensitivity f`. -/
theorem exists_udisj_embedding_of_monotoneBlockSensitivity {n k : ℕ}
    {f : Cslib.BooleanFunction n} (hk : k ≤ monotoneBlockSensitivity f) :
    ∃ (embA embB : Finset (Fin k) → Cslib.BitString n) (flipOut : Bool),
      (∀ a b : Finset (Fin k), Disjoint a b →
        (flipOut ^^ andLift f (embA a) (embB b)) = false) ∧
      (∀ a b : Finset (Fin k), #(a ∩ b) = 1 →
        (flipOut ^^ andLift f (embA a) (embB b)) = true) ∧
      (∀ a b : Finset (Fin k),
        Cslib.Communication.Nondeterministic.uniqueDisjointnessRel (Fin k) a b
          (!(flipOut ^^ andLift f (embA a) (embB b)))) := by
  have hne_univ : (univ : Finset (Cslib.BitString n)).Nonempty := ⟨fun _ ↦ false, mem_univ _⟩
  obtain ⟨x, -, hx_sup⟩ := exists_mem_eq_sup univ hne_univ (monotoneBlockSensitivityAt f)
  have hk_x : k ≤ monotoneBlockSensitivityAt f x := hk.trans_eq hx_sup
  have hne_fam : (univ.filter (IsMonotoneSensitiveFamily f x)).Nonempty := by
    refine ⟨∅, mem_filter.mpr ⟨mem_univ _, fun _ h ↦ absurd h (notMem_empty _), ?_⟩⟩
    simp
  obtain ⟨F₀, hF₀_mem, hF₀_sup⟩ :=
     exists_mem_eq_sup (univ.filter (IsMonotoneSensitiveFamily f x)) hne_fam Finset.card
  have hk_F₀ : k ≤ #F₀ := hk_x.trans_eq hF₀_sup
  obtain ⟨F, hFF₀, hFk⟩ := exists_subset_card_eq hk_F₀
  obtain ⟨hF₀_sens, hF₀_disj⟩ := (mem_filter.mp hF₀_mem).2
  let e : Fin k ≃ F := (Fintype.equivFinOfCardEq (by simp [hFk])).symm
  let blk (j : Fin k) : Cslib.QueryComplexity.Block n := (e j).1
  have hblk_sens (j : Fin k) : IsSensitiveZeroBlock f x (blk j) :=
    hF₀_sens _ (hFF₀ (e j).2)
  have hblk_disj : ∀ j₁ j₂ : Fin k, j₁ ≠ j₂ → Disjoint (blk j₁) (blk j₂) := by
    intro j₁ j₂ hne
    refine hF₀_disj (hFF₀ (e j₁).2) (hFF₀ (e j₂).2) ?_
    intro heq
    exact hne (e.injective (Subtype.ext heq))
  let emb (s : Finset (Fin k)) : Cslib.BitString n := fun i ↦
    if h : ∃ j : Fin k, i ∈ blk j then
      decide (Classical.choose h ∈ s)
    else
      x i
  have hchoose_eq {i : Fin n} {j : Fin k} (hi : i ∈ blk j) :
      Classical.choose (⟨j, hi⟩ : ∃ j' : Fin k, i ∈ blk j') = j := by
    let j' := Classical.choose (⟨j, hi⟩ : ∃ j' : Fin k, i ∈ blk j')
    have hj' : i ∈ blk j' := Classical.choose_spec (⟨j, hi⟩ : ∃ j' : Fin k, i ∈ blk j')
    by_contra hne
    exact disjoint_left.mp (hblk_disj j' j hne) hj' hi
  have hemb {i : Fin n} {j : Fin k} (hj : i ∈ blk j) (s : Finset (Fin k)) :
      emb s i = decide (j ∈ s) := by
    have hex : ∃ j' : Fin k, i ∈ blk j' := ⟨j, hj⟩
    simp only [emb, dite_eq_left hex, hchoose_eq hj]
  have hand_disj (a b : Finset (Fin k)) (hab : Disjoint a b) :
      (fun i ↦ emb a i && emb b i) = x := by
    funext i
    by_cases h : ∃ j : Fin k, i ∈ blk j
    · obtain ⟨j, hj⟩ := h
      have h0 : x i = false := (hblk_sens j).1 i hj
      rw [hemb hj a, hemb hj b, h0]
      by_cases hja : j ∈ a
      · have hjb : j ∉ b := disjoint_left.mp hab hja
        simp [hja, hjb]
      · simp [hja]
    · simp [emb, h]
  have hand_one (a b : Finset (Fin k)) (hab : #(a ∩ b) = 1) :
      ∃ j₀ : Fin k, (fun i ↦ emb a i && emb b i) = Cslib.BitString.flipBlock (blk j₀) x := by
    obtain ⟨j₀, hj₀⟩ := card_eq_one.mp hab
    refine ⟨j₀, ?_⟩
    funext i
    by_cases h : ∃ j : Fin k, i ∈ blk j
    · obtain ⟨j, hj⟩ := h
      have h0 : x i = false := (hblk_sens j).1 i hj
      rw [hemb hj a, hemb hj b]
      simp only [Cslib.BitString.flipBlock]
      by_cases hjj₀ : j = j₀
      · subst hjj₀
        have hmem : j ∈ a ∩ b := hj₀ ▸ mem_singleton_self j
        obtain ⟨ha, hb⟩ := mem_inter.mp hmem
        simp [hj, h0, ha, hb]
      · have hnot_inter : j ∉ a ∩ b := by rw [hj₀]; simp [hjj₀]
        have hij₀ : i ∉ blk j₀ := fun hi₀ ↦ disjoint_left.mp (hblk_disj j j₀ hjj₀) hj hi₀
        have hfalse : (decide (j ∈ a) && decide (j ∈ b)) = false := by
          rw [Bool.and_eq_false_iff]
          by_cases ha : j ∈ a
          · right; simp [show j ∉ b from fun hb ↦ hnot_inter (mem_inter.mpr ⟨ha, hb⟩)]
          · left; simp [ha]
        rw [hfalse]
        simp [hij₀, h0]
    · have hij₀ : i ∉ blk j₀ := fun hi₀ ↦ h ⟨j₀, hi₀⟩
      simp [emb, h, Cslib.BitString.flipBlock, hij₀]
  refine ⟨emb, emb, f x, ?_, ?_, ?_⟩
  · intro a b hab
    rw [andLift, hand_disj a b hab, Bool.xor_self]
  · intro a b hab
    obtain ⟨j₀, hj₀⟩ := hand_one a b hab
    rw [andLift, hj₀]
    have hsens : f (Cslib.BitString.flipBlock (blk j₀) x) ≠ f x := (hblk_sens j₀).2
    cases hfx : f x <;> cases hfl : f (Cslib.BitString.flipBlock (blk j₀) x) <;> simp_all
  · intro a b
    by_cases hdisj : Disjoint a b
    · have h0 : (f x ^^ andLift f (emb a) (emb b)) = false := by
        rw [andLift, hand_disj a b hdisj, Bool.xor_self]
      rw [h0]
      simp [Cslib.Communication.Nondeterministic.uniqueDisjointnessRel,
        disjoint_iff_inter_eq_empty.mp hdisj]
    · by_cases h1 : #(a ∩ b) = 1
      · obtain ⟨j₀, hj₀⟩ := hand_one a b h1
        have hsens : f (Cslib.BitString.flipBlock (blk j₀) x) ≠ f x := (hblk_sens j₀).2
        have htrue : (f x ^^ andLift f (emb a) (emb b)) = true := by
          rw [andLift, hj₀]
          cases hfx : f x <;> cases hfl : f (Cslib.BitString.flipBlock (blk j₀) x) <;> simp_all
        rw [htrue]
        simp [Cslib.Communication.Nondeterministic.uniqueDisjointnessRel, hdisj]
      · cases !(f x ^^ andLift f (emb a) (emb b)) <;>
          simp [Cslib.Communication.Nondeterministic.uniqueDisjointnessRel, hdisj, h1]

/-- Public-coin communication reduction from `UDISJ_{mbs(f)}` to `andLift f`. -/
theorem rcc_uniqueDisjointness_le_rccFun_andLift {n : ℕ} (ε : ℝ) (f : Cslib.BooleanFunction n) :
    Cslib.Communication.PublicCoin.ecomplexity ε
      (Cslib.Communication.Nondeterministic.uniqueDisjointnessRel
        (Fin (monotoneBlockSensitivity f)))
      Set.univ Set.univ ≤
      Cslib.Communication.PublicCoin.ecomplexityFun ε (andLift f) := by
  obtain ⟨embA, embB, flipOut, -, -, hrel⟩ :=
    exists_udisj_embedding_of_monotoneBlockSensitivity (le_rfl : monotoneBlockSensitivity f ≤ _)
  rw [Cslib.Communication.PublicCoin.ecomplexityFun,
    Cslib.Communication.PublicCoin.ecomplexity_eq_randomizedCost,
    Cslib.Communication.PublicCoin.ecomplexity_eq_randomizedCost]
  refine Cslib.RandomizedCost.le_ecomplexity_iff.mpr fun μ hμ ↦ ?_
  let mapP (p : Cslib.Communication.Protocol (Cslib.BitString n) (Cslib.BitString n) Bool) :
      Cslib.Communication.Protocol (Finset (Fin (monotoneBlockSensitivity f)))
        (Finset (Fin (monotoneBlockSensitivity f))) Bool :=
    (p.comap embA embB).map fun z ↦ !(flipOut ^^ z)
  let μ' := μ.map mapP
  have hcost : Cslib.Probability.PMF.maxCost Cslib.Communication.Protocol.depth μ' ≤
      Cslib.Probability.PMF.maxCost Cslib.Communication.Protocol.depth μ :=
    Cslib.Probability.PMF.maxCost_map_le _ _ _ _ fun p _ ↦ by
      simp [mapP, Cslib.Communication.Protocol.depth_map]
  have hsolves :
      (Cslib.Communication.Protocol.randomizedCost _ _ Bool).Solves μ' ε
        (fun q z ↦ Cslib.Communication.Nondeterministic.uniqueDisjointnessRel _ q.1 q.2 z)
        (Set.univ ×ˢ Set.univ) := by
    rintro ⟨a, b⟩ -
    refine le_trans ?_ (hμ (embA a, embB b) ⟨trivial, trivial⟩)
    simp only [Cslib.RandomizedCost.errorProb, Cslib.Communication.Protocol.randomizedCost,
      Cslib.Probability.PMF.errorProb, μ']
    rw [PMF.toOuterMeasure_map_apply]
    refine Cslib.Probability.PMF.toOuterMeasure_toReal_mono μ fun p hp hpeq ↦ ?_
    have hp' :
        ¬Cslib.Communication.Nondeterministic.uniqueDisjointnessRel _ a b ((mapP p).run a b) := hp
    simp only [mapP, Cslib.Communication.Protocol.run_map,
      Cslib.Communication.Protocol.run_comap] at hp'
    rw [← hpeq] at hp'
    exact hp' (hrel a b)
  exact (Cslib.RandomizedCost.ecomplexity_le_maxCost hsolves).trans hcost

section PartitionCorruption

private def udisjParts (U : Type*) [Fintype U] [DecidableEq U] (m : ℕ) :
    Finset (U × Finset U × Finset U) :=
  univ.filter fun T ↦
    T.1 ∉ T.2.1 ∧ T.1 ∉ T.2.2 ∧ Disjoint T.2.1 T.2.2 ∧ #T.2.1 = m ∧ #T.2.2 = m

private lemma compl_insert_of_udisjParts {U : Type*} [Fintype U] [DecidableEq U] {m : ℕ}
    (hU : Fintype.card U = 2 * m + 1) {T : U × Finset U × Finset U} (hT : T ∈ udisjParts U m) :
    (insert T.1 T.2.2)ᶜ = T.2.1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := (mem_filter.mp hT).2
  symm
  refine eq_of_subset_of_card_le (fun a ha ↦ ?_) ?_
  · rw [mem_compl, mem_insert, not_or]
    exact ⟨fun h ↦ h1 (h ▸ ha), fun h ↦ disjoint_left.mp h3 ha h⟩
  · rw [card_compl, card_insert_of_notMem h2, hU, h4, h5]
    omega

private lemma sum_udisjParts {U : Type*} [Fintype U] [DecidableEq U] {m : ℕ}
    (hU : Fintype.card U = 2 * m + 1) {M : Type*} [AddCommMonoid M]
    (F : U × Finset U × Finset U → M) :
    ∑ T ∈ udisjParts U m, F T =
      ∑ Ty ∈ powersetCard m (univ : Finset U), ∑ i ∈ Tyᶜ, F (i, (insert i Ty)ᶜ, Ty) := by
  rw [sum_sigma']
  refine sum_nbij' (fun T ↦ ⟨T.2.2, T.1⟩) (fun x ↦ (x.2, (insert x.2 x.1)ᶜ, x.1))
    (fun T hT ↦ by
      obtain ⟨_, h2, _, _, h5⟩ := (mem_filter.mp hT).2
      exact mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, h5⟩, mem_compl.mpr h2⟩)
    (fun ⟨Ty, i⟩ hx ↦ by
      have hTy : #Ty = m := (mem_powersetCard.mp (mem_sigma.mp hx).1).2
      have hi : i ∉ Ty := mem_compl.mp (mem_sigma.mp hx).2
      refine mem_filter.mpr ⟨mem_univ _, by simp, hi,
        disjoint_left.mpr fun _ ha haTy ↦ mem_compl.mp ha (mem_insert_of_mem haTy), ?_, hTy⟩
      rw [card_compl, card_insert_of_notMem hi, hU, hTy]; omega)
    (fun T hT ↦ by ext <;> simp [compl_insert_of_udisjParts hU hT])
    (fun _ _ ↦ rfl)
    (fun T hT ↦ by simp [compl_insert_of_udisjParts hU hT])

private lemma sum_udisjParts_swap {U : Type*} [Fintype U] [DecidableEq U] {m : ℕ}
    {M : Type*} [AddCommMonoid M] (F : U × Finset U × Finset U → M) :
    ∑ T ∈ udisjParts U m, F T = ∑ T ∈ udisjParts U m, F (T.1, T.2.2, T.2.1) := by
  refine sum_nbij' (fun T ↦ (T.1, T.2.2, T.2.1)) (fun T ↦ (T.1, T.2.2, T.2.1))
    (fun T hT ↦ by
      obtain ⟨h1, h2, h3, h4, h5⟩ := (mem_filter.mp hT).2
      exact mem_filter.mpr ⟨mem_univ _, h2, h1, h3.symm, h5, h4⟩)
    (fun T hT ↦ by
      obtain ⟨h1, h2, h3, h4, h5⟩ := (mem_filter.mp hT).2
      exact mem_filter.mpr ⟨mem_univ _, h2, h1, h3.symm, h5, h4⟩)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

private lemma card_udisjParts {U : Type*} [Fintype U] [DecidableEq U] {m : ℕ}
    (hU : Fintype.card U = 2 * m + 1) :
    #(udisjParts U m) = #(powersetCard m (univ : Finset U)) * (m + 1) := by
  rw [card_eq_sum_ones, sum_udisjParts hU]
  simp only [sum_const, smul_eq_mul, mul_one]
  rw [sum_congr rfl fun Ty hTy ↦ by rw [card_compl, hU, (mem_powersetCard.mp hTy).2],
    sum_const, smul_eq_mul]
  exact congrArg (_ * ·) (by omega)

private lemma card_udisjParts_pos {U : Type*} [Fintype U] [DecidableEq U] {m : ℕ}
    (hU : Fintype.card U = 2 * m + 1) :
    0 < #(udisjParts U m) := by
  rw [card_udisjParts hU, card_powersetCard, card_univ, hU]
  exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.succ_pos m)

private noncomputable def udisjWeight {U : Type*} [Fintype U] [DecidableEq U] (m : ℕ)
    (q : Finset U × Finset U) : ℝ :=
  (∑ T ∈ udisjParts U m,
    ((if q.1 ⊆ T.2.1 then (1 : ℝ) else 0) * (if q.2 ⊆ T.2.2 then 1 else 0) +
      (if T.1 ∈ q.1 ∧ q.1 ⊆ T.2.2ᶜ then 1 else 0) *
        (if T.1 ∈ q.2 ∧ q.2 ⊆ T.2.1ᶜ then 1 else 0))) /
    (2 * #(udisjParts U m) * 4 ^ m)

private lemma udisjWeight_nonneg {U : Type*} [Fintype U] [DecidableEq U] (m : ℕ)
    (q : Finset U × Finset U) : 0 ≤ udisjWeight m q := by
  unfold udisjWeight
  refine div_nonneg (sum_nonneg fun _ _ ↦ ?_) (by positivity)
  split_ifs <;> norm_num

private lemma card_inter_le_one_of_udisjWeight_pos {U : Type*} [Fintype U] [DecidableEq U]
    {m : ℕ} (hU : Fintype.card U = 2 * m + 1) {q : Finset U × Finset U}
    (hq : udisjWeight m q ≠ 0) :
    #(q.1 ∩ q.2) ≤ 1 := by
  by_contra hgt
  have hzero : udisjWeight m q = 0 := by
    unfold udisjWeight
    rw [div_eq_zero_iff]
    left
    refine sum_eq_zero fun T hT ↦ ?_
    obtain ⟨_, _, hdisj, _, _⟩ := (mem_filter.mp hT).2
    have hleft0 : (if q.1 ⊆ T.2.1 then (1 : ℝ) else 0) * (if q.2 ⊆ T.2.2 then 1 else 0) = 0 := by
      split_ifs with ha hb
      · have hd : Disjoint q.1 q.2 := hdisj.mono ha hb
        have hc0 : #(q.1 ∩ q.2) = 0 := by simp [disjoint_iff_inter_eq_empty.mp hd]
        omega
      all_goals norm_num
    have hright0 :
        (if T.1 ∈ q.1 ∧ q.1 ⊆ T.2.2ᶜ then (1 : ℝ) else 0) *
          (if T.1 ∈ q.2 ∧ q.2 ⊆ T.2.1ᶜ then 1 else 0) = 0 := by
      split_ifs with ha hb
      · have hcompl : T.2.1 = (insert T.1 T.2.2)ᶜ := (compl_insert_of_udisjParts hU hT).symm
        have hsub : q.1 ∩ q.2 ⊆ {T.1} := by
          intro u hu
          obtain ⟨hu1, hu2⟩ := mem_inter.mp hu
          by_contra hu_ne
          have hu_not_R : u ∉ T.2.2 := mem_compl.mp (ha.2 hu1)
          have hu_in_L : u ∈ T.2.1 := by
            rw [hcompl, mem_compl, mem_insert, not_or]
            exact ⟨mem_singleton.not.mp hu_ne, hu_not_R⟩
          exact mem_compl.mp (hb.2 hu2) hu_in_L
        have hle1 : #(q.1 ∩ q.2) ≤ 1 := (card_le_card hsub).trans (card_singleton T.1).le
        omega
      all_goals norm_num
    rw [hleft0, hright0, add_zero]
  exact hq hzero

private lemma ite_udisjWeight {U : Type*} [Fintype U] [DecidableEq U] (m : ℕ)
    (x y : Finset U) :
    (if decide (Disjoint x y) = true then udisjWeight m (x, y) else 0) =
        (∑ T ∈ udisjParts U m,
          (if x ⊆ T.2.1 then (1 : ℝ) else 0) * (if y ⊆ T.2.2 then 1 else 0)) /
          (2 * #(udisjParts U m) * 4 ^ m) ∧
      (if decide (Disjoint x y) = true then 0 else udisjWeight m (x, y)) =
        (∑ T ∈ udisjParts U m,
          (if T.1 ∈ x ∧ x ⊆ T.2.2ᶜ then (1 : ℝ) else 0) *
            (if T.1 ∈ y ∧ y ⊆ T.2.1ᶜ then 1 else 0)) /
          (2 * #(udisjParts U m) * 4 ^ m) := by
  unfold udisjWeight
  by_cases h : Disjoint x y
  · have hzero (T : U × Finset U × Finset U) :
        (if T.1 ∈ x ∧ x ⊆ T.2.2ᶜ then (1 : ℝ) else 0) *
          (if T.1 ∈ y ∧ y ⊆ T.2.1ᶜ then 1 else 0) = 0 := by
      split_ifs with h1 h2
      · exact absurd h2.1 (disjoint_left.mp h h1.1)
      all_goals norm_num
    simp only [h, decide_true, ↓reduceIte, hzero, add_zero, sum_const_zero, zero_div, and_self]
  · have hzero {T : U × Finset U × Finset U} (hT : T ∈ udisjParts U m) :
        (if x ⊆ T.2.1 then (1 : ℝ) else 0) * (if y ⊆ T.2.2 then 1 else 0) = 0 := by
      split_ifs with h1 h2
      · exact absurd (((mem_filter.mp hT).2.2.2.1).mono h1 h2) h
      all_goals norm_num
    simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨(div_eq_zero_iff.mpr (.inl (sum_eq_zero fun _ hT ↦ hzero hT))).symm,
      congrArg (· / _) (sum_congr rfl fun _ hT ↦ by rw [hzero hT, zero_add])⟩

private lemma udisj_slack_le {r s : ℕ} (hs : 48 * r ≤ s) (hs1 : 1 ≤ s) :
    8 * (s : ℝ) * (27 / 32 : ℝ) ^ r + (((12 * r : ℕ) : ℝ) + 1) * 2 ^ (12 * r) * (3 / 4) ^ s ≤
      9 * (s : ℝ) * (27 / 32) ^ r := by
  have h1 : ((12 * r : ℕ) : ℝ) + 1 ≤ s := by exact_mod_cast (show 12 * r + 1 ≤ s by omega)
  have h2 : (3 / 4 : ℝ) ^ s ≤ (3 / 4) ^ (48 * r) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
  have h3 : (2 : ℝ) ^ (12 * r) * (3 / 4) ^ (48 * r) ≤ (27 / 32) ^ r := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) r
  have h4 : (((12 * r : ℕ) : ℝ) + 1) * 2 ^ (12 * r) * (3 / 4) ^ s ≤ (s : ℝ) * (27 / 32) ^ r := by
    calc (((12 * r : ℕ) : ℝ) + 1) * 2 ^ (12 * r) * (3 / 4) ^ s
        ≤ (s : ℝ) * (2 ^ (12 * r) * (3 / 4) ^ (48 * r)) := by rw [mul_assoc]; gcongr
      _ ≤ (s : ℝ) * (27 / 32) ^ r := mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith

private lemma udisj_sum_rect {U : Type*} [Fintype U] [DecidableEq U] {m : ℕ}
    (A B : Finset (Finset U)) (p q : (U × Finset U × Finset U) → Finset U → Prop)
    [∀ T x, Decidable (p T x)] [∀ T y, Decidable (q T y)] (D : ℝ) :
    ∑ x ∈ A, ∑ y ∈ B,
      (∑ T ∈ udisjParts U m, (if p T x then (1 : ℝ) else 0) * (if q T y then 1 else 0)) / D =
      (∑ T ∈ udisjParts U m, (#{x ∈ A | p T x} : ℝ) * #{y ∈ B | q T y}) / D := by
  simp only [← sum_div]
  congr 1
  calc ∑ x ∈ A, ∑ y ∈ B, ∑ T ∈ udisjParts U m,
        (if p T x then (1 : ℝ) else 0) * (if q T y then 1 else 0)
      = ∑ x ∈ A, ∑ T ∈ udisjParts U m, ∑ y ∈ B,
          (if p T x then (1 : ℝ) else 0) * (if q T y then 1 else 0) :=
        sum_congr rfl fun _ _ ↦ sum_comm
    _ = ∑ T ∈ udisjParts U m, ∑ x ∈ A, ∑ y ∈ B,
          (if p T x then (1 : ℝ) else 0) * (if q T y then 1 else 0) := sum_comm
    _ = _ := by
        refine sum_congr rfl fun _ _ ↦ ?_
        rw [← sum_mul_sum, sum_boole, sum_boole]

private lemma sum_udisjWeight_univ {U : Type*} [Fintype U] [DecidableEq U] {m : ℕ}
    (hU : Fintype.card U = 2 * m + 1) :
    (∑ x : Finset U, ∑ y : Finset U,
        if decide (Disjoint x y) = true then udisjWeight m (x, y) else 0) = 1 / 2 ∧
      ∑ q : Finset U × Finset U, udisjWeight m q = 1 := by
  have hP : (0 : ℝ) < #(udisjParts U m) := by exact_mod_cast card_udisjParts_pos hU
  have h4m : (2 ^ m : ℝ) * 2 ^ m = 4 ^ m := by rw [← mul_pow]; norm_num
  have hlow (s : Finset U) : #{x : Finset U | x ⊆ s} = 2 ^ #s := by
    rw [← card_powerset]
    exact congrArg card (ext fun _ ↦ by simp [mem_powerset])
  have hhigh {i : U} {s : Finset U} (hi : i ∉ s) :
      #{x : Finset U | i ∈ x ∧ x ⊆ sᶜ} = 2 ^ (#sᶜ - 1) := by
    have hi' : i ∈ sᶜ := mem_compl.mpr hi
    have h1 : #{x : Finset U | i ∈ x ∧ x ⊆ sᶜ} = #{x ∈ sᶜ.powerset | i ∈ x} :=
      congrArg card (ext fun _ ↦ by simp [mem_powerset, and_comm])
    have h2 : {x ∈ sᶜ.powerset | i ∉ x} = (sᶜ.erase i).powerset :=
      ext fun _ ↦ by simp [mem_powerset, subset_erase]
    have h3 := (card_filter_add_card_filter_not (s := sᶜ.powerset) fun x ↦ i ∈ x).trans
      (card_powerset sᶜ)
    have h5 : 2 ^ #sᶜ = 2 ^ (#sᶜ - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (card_pos.mpr ⟨i, hi'⟩)]
    rw [h2, card_powerset, card_erase_of_mem hi', h5] at h3
    rw [h1]; omega
  have hdisj_half :
      (∑ x : Finset U, ∑ y : Finset U,
        if decide (Disjoint x y) = true then udisjWeight m (x, y) else 0) = 1 / 2 := by
    simp only [fun x y ↦ (ite_udisjWeight m x y).1]
    rw [udisj_sum_rect univ univ (fun T x ↦ x ⊆ T.2.1) (fun T y ↦ y ⊆ T.2.2)]
    rw [sum_congr rfl fun T hT ↦ by
      obtain ⟨_, _, _, h4, h5⟩ := (mem_filter.mp hT).2
      rw [hlow, hlow, h4, h5, Nat.cast_pow, Nat.cast_ofNat, h4m], sum_const, nsmul_eq_mul]
    field_simp
  have hinter_half :
      (∑ x : Finset U, ∑ y : Finset U,
        if decide (Disjoint x y) = true then 0 else udisjWeight m (x, y)) = 1 / 2 := by
    simp only [fun x y ↦ (ite_udisjWeight m x y).2]
    rw [udisj_sum_rect univ univ (fun T x ↦ T.1 ∈ x ∧ x ⊆ T.2.2ᶜ)
      (fun T y ↦ T.1 ∈ y ∧ y ⊆ T.2.1ᶜ)]
    have hcompl {s : Finset U} (hs : #s = m) : #sᶜ - 1 = m := by simp [card_compl, hU, hs]; omega
    rw [sum_congr rfl fun T hT ↦ by
      obtain ⟨h1, h2, _, h4, h5⟩ := (mem_filter.mp hT).2
      rw [hhigh h2, hhigh h1, hcompl h5, hcompl h4, Nat.cast_pow, Nat.cast_ofNat, h4m],
      sum_const, nsmul_eq_mul]
    field_simp
  refine ⟨hdisj_half, ?_⟩
  rw [Fintype.sum_prod_type]
  have hsplit :
      (∑ x : Finset U, ∑ y : Finset U, udisjWeight m (x, y)) =
        (∑ x : Finset U, ∑ y : Finset U,
          if decide (Disjoint x y) = true then udisjWeight m (x, y) else 0) +
        (∑ x : Finset U, ∑ y : Finset U,
          if decide (Disjoint x y) = true then 0 else udisjWeight m (x, y)) := by
    simp only [← sum_add_distrib]
    refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ ?_
    split_ifs <;> simp
  rw [hsplit, hdisj_half, hinter_half]
  norm_num

private noncomputable def udisjHardDist {U : Type*} [Fintype U] [DecidableEq U] (m : ℕ)
    (hU : Fintype.card U = 2 * m + 1) : PMF (Finset U × Finset U) :=
  PMF.ofFintype (fun q ↦ ENNReal.ofReal (udisjWeight m q)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun q _ ↦ udisjWeight_nonneg m q,
      (sum_udisjWeight_univ hU).2, ENNReal.ofReal_one])

private lemma udisjHardDist_corrupted {U : Type*} [Fintype U] [DecidableEq U] {m r : ℕ}
    (hU : Fintype.card U = 2 * m + 1) (hr : 48 * r ≤ m + 1) :
    Cslib.Communication.Corrupted (udisjHardDist m hU)
      (fun x y ↦ decide (Disjoint x y)) true (1 / 18) ((27 / 32) ^ r / 2) := by
  intro A B
  have htoReal (q : Finset U × Finset U) : (udisjHardDist m hU q).toReal = udisjWeight m q := by
    rw [udisjHardDist, PMF.ofFintype_apply, ENNReal.toReal_ofReal (udisjWeight_nonneg m q)]
  simp only [htoReal, fun x y ↦ (ite_udisjWeight m x y).1, fun x y ↦ (ite_udisjWeight m x y).2]
  rw [udisj_sum_rect A B (fun T x ↦ x ⊆ T.2.1) (fun T y ↦ y ⊆ T.2.2),
     udisj_sum_rect A B (fun T x ↦ T.1 ∈ x ∧ x ⊆ T.2.2ᶜ) (fun T y ↦ T.1 ∈ y ∧ y ⊆ T.2.1ᶜ)]
  let low (X0 : Finset (Finset U)) (s : Finset U) : ℕ := #{x ∈ X0 | x ⊆ s}
  let high (X0 : Finset (Finset U)) (i : U) (s : Finset U) : ℕ := #{x ∈ X0 | i ∈ x ∧ x ⊆ sᶜ}
  have hlow_compl (X0 : Finset (Finset U)) (i : U) (s : Finset U) :
      low X0 (insert i s)ᶜ = #{x ∈ X0 | x ⊆ sᶜ ∧ i ∉ x} := by
    dsimp [low]; congr 1; refine filter_congr fun x _ ↦ ?_
    simp only [subset_iff, mem_compl, mem_insert, not_or]
    exact ⟨fun h ↦ ⟨fun a ha ↦ (h ha).2, fun hi ↦ (h hi).1 rfl⟩,
      fun h a ha ↦ ⟨fun hai ↦ h.2 (hai ▸ ha), h.1 ha⟩⟩
  have hlow_le (X0 : Finset (Finset U)) (s : Finset U) : low X0 s ≤ 2 ^ #s := by
    rw [← card_powerset]
    exact card_le_card fun x hx ↦ mem_powerset.mpr (mem_filter.mp hx).2
  have hone_side (A' B' : Finset (Finset U)) :
      4 * ∑ T ∈ udisjParts U m with 3 * high A' T.1 T.2.2 < low A' T.2.1,
          ((low A' T.2.1 : ℝ) * low B' T.2.2) ≤
        ∑ T ∈ udisjParts U m, ((low A' T.2.1 : ℝ) * low B' T.2.2) +
          18 * #(udisjParts U m) * 4 ^ m * (27 / 32) ^ r := by
    rw [sum_filter, sum_udisjParts hU, sum_udisjParts hU, card_udisjParts hU, mul_sum]
    have hconst :
        (18 : ℝ) * ((#(powersetCard m (univ : Finset U)) * (m + 1) : ℕ) : ℝ) * 4 ^ m *
          (27 / 32) ^ r =
        ∑ _Ty ∈ powersetCard m (univ : Finset U),
          18 * ((m : ℝ) + 1) * 4 ^ m * (27 / 32) ^ r := by
      rw [sum_const, nsmul_eq_mul]; push_cast; ring
    rw [hconst, ← sum_add_distrib]
    refine sum_le_sum fun Ty hTy ↦ ?_
    have hTym : #Ty = m := (mem_powersetCard.mp hTy).2
    have hS : #Tyᶜ = m + 1 := by simp [card_compl, hU, hTym]; omega
    have hb : (low B' Ty : ℝ) ≤ 2 ^ m := by exact_mod_cast hTym ▸ hlow_le B' Ty
    have hb0 : (0 : ℝ) ≤ low B' Ty := Nat.cast_nonneg _
    have hKL := Cslib.four_mul_sum_card_filter_notMem_le A' Tyᶜ (r := r) (j := 12 * r) (by omega)
    rw [hS] at hKL
    push_cast at hKL
    simp only [hlow_compl, high]
    rw [← sum_filter, ← sum_mul, ← sum_mul]
    have hsl := udisj_slack_le (r := r) (s := m + 1) hr (by omega)
    push_cast at hsl
    have h4m : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
    have hrhs :
        (2 : ℝ) ^ (m + 1) * (8 * ((m : ℝ) + 1) * (27 / 32) ^ r +
          (12 * (r : ℝ) + 1) * 2 ^ (12 * r) * (3 / 4) ^ (m + 1)) * (low B' Ty : ℝ) ≤
        18 * ((m : ℝ) + 1) * 4 ^ m * (27 / 32) ^ r := by
      calc (2 : ℝ) ^ (m + 1) * (8 * ((m : ℝ) + 1) * (27 / 32) ^ r +
            (12 * (r : ℝ) + 1) * 2 ^ (12 * r) * (3 / 4) ^ (m + 1)) * (low B' Ty : ℝ)
          ≤ (2 : ℝ) ^ (m + 1) * (9 * ((m : ℝ) + 1) * (27 / 32) ^ r) * 2 ^ m := by gcongr
        _ = 18 * ((m : ℝ) + 1) * 4 ^ m * (27 / 32) ^ r := by rw [pow_succ, h4m]; ring
    linarith [mul_le_mul_of_nonneg_right hKL hb0]
  have hX := hone_side A B
  have hY := hone_side B A
  rw [sum_filter] at hX hY
  rw [sum_udisjParts_swap, sum_udisjParts_swap (fun T ↦ (low B T.2.1 : ℝ) * low A T.2.2)] at hY
  have hpt : ∀ T ∈ udisjParts U m, (low A T.2.1 : ℝ) * low B T.2.2 ≤
      9 * ((high A T.1 T.2.2 : ℝ) * high B T.1 T.2.1) +
        ((if 3 * high A T.1 T.2.2 < low A T.2.1 then (low A T.2.1 : ℝ) * low B T.2.2 else 0) +
          (if 3 * high B T.1 T.2.1 < low B T.2.2 then (low B T.2.2 : ℝ) * low A T.2.1 else 0)) := by
    intro T _
    have h0 : (0 : ℝ) ≤ (low A T.2.1 : ℝ) * low B T.2.2 := by positivity
    have h0' : (0 : ℝ) ≤ (high A T.1 T.2.2 : ℝ) * high B T.1 T.2.1 := by positivity
    by_cases hx : 3 * high A T.1 T.2.2 < low A T.2.1 <;>
      by_cases hy : 3 * high B T.1 T.2.1 < low B T.2.2 <;>
      simp only [hx, hy, ↓reduceIte, add_zero]
    · nlinarith
    · linarith
    · nlinarith
    · push Not at hx hy
      have hx' : (low A T.2.1 : ℝ) ≤ 3 * high A T.1 T.2.2 := by exact_mod_cast hx
      have hy' : (low B T.2.2 : ℝ) ≤ 3 * high B T.1 T.2.1 := by exact_mod_cast hy
      nlinarith [mul_le_mul hx' hy' (Nat.cast_nonneg _) (by positivity)]
  have hsum_pt := sum_le_sum hpt
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum] at hsum_pt
  rw [sum_congr rfl fun _ _ ↦ mul_comm _ _] at hY
  have hmain :
      ∑ T ∈ udisjParts U m, ((low A T.2.1 : ℝ) * low B T.2.2) ≤
        18 * ∑ T ∈ udisjParts U m, ((high A T.1 T.2.2 : ℝ) * high B T.1 T.2.1) +
          18 * #(udisjParts U m) * 4 ^ m * (27 / 32) ^ r := by
    linarith
  have hP : (0 : ℝ) < #(udisjParts U m) := by exact_mod_cast card_udisjParts_pos hU
  have hdiv := div_le_div_of_nonneg_right hmain
    (by positivity : (0 : ℝ) ≤ 2 * #(udisjParts U m) * 4 ^ m)
  have hcancel :
      (18 * #(udisjParts U m) * 4 ^ m * (27 / 32) ^ r : ℝ) /
        (2 * #(udisjParts U m) * 4 ^ m) = 9 * (27 / 32) ^ r := by
    field_simp; ring
  rw [add_div, mul_div_assoc, hcancel] at hdiv
  change (1 / 18 : ℝ) *
      ((∑ T ∈ udisjParts U m, (low A T.2.1 : ℝ) * low B T.2.2) /
        (2 * #(udisjParts U m) * 4 ^ m)) ≤
    (∑ T ∈ udisjParts U m, (high A T.1 T.2.2 : ℝ) * high B T.1 T.2.1) /
      (2 * #(udisjParts U m) * 4 ^ m) + (27 / 32) ^ r / 2
  linarith

/-- Linear lower bound on public-coin randomized communication complexity of unique set
disjointness: `k ≤ 2 ^ 16 * Rcc_{1/3}(UDISJ_k) + 2 ^ 12` for all `k : ℕ`. -/
theorem le_mul_rcc_uniqueDisjointness_add (k : ℕ) :
    (k : ℕ∞) ≤
      2 ^ 16 *
        Cslib.Communication.PublicCoin.ecomplexity (1 / 3)
          (Cslib.Communication.Nondeterministic.uniqueDisjointnessRel (Fin k))
          Set.univ Set.univ +
      2 ^ 12 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  set m := (k - 1) / 2
  have hmk : 2 * m + 1 ≤ k := by omega
  let U := Fin (2 * m + 1)
  have hU : Fintype.card U = 2 * m + 1 := Fintype.card_fin (2 * m + 1)
  have hred :
      Cslib.Communication.PublicCoin.ecomplexity (1 / 3)
        (Cslib.Communication.Nondeterministic.uniqueDisjointnessRel U) Set.univ Set.univ ≤
      Cslib.Communication.PublicCoin.ecomplexity (1 / 3)
        (Cslib.Communication.Nondeterministic.uniqueDisjointnessRel (Fin k)) Set.univ Set.univ := by
    let e := Fin.castLEEmb hmk
    rw [Cslib.Communication.PublicCoin.ecomplexity_eq_randomizedCost,
      Cslib.Communication.PublicCoin.ecomplexity_eq_randomizedCost]
    refine Cslib.RandomizedCost.le_ecomplexity_iff.mpr fun μ hμ ↦ ?_
    let mapP (p : Cslib.Communication.Protocol (Finset (Fin k)) (Finset (Fin k)) Bool) :=
      p.comap (fun a : Finset U ↦ a.map e) (fun b : Finset U ↦ b.map e)
    let μ' := μ.map mapP
    have hcost : Cslib.Probability.PMF.maxCost Cslib.Communication.Protocol.depth μ' ≤
        Cslib.Probability.PMF.maxCost Cslib.Communication.Protocol.depth μ :=
      Cslib.Probability.PMF.maxCost_map_le _ _ _ _ fun p _ ↦ by simp [mapP]
    have hsolves :
        (Cslib.Communication.Protocol.randomizedCost (Finset U) (Finset U) Bool).Solves μ' (1 / 3)
          (fun q z ↦ Cslib.Communication.Nondeterministic.uniqueDisjointnessRel U q.1 q.2 z)
          (Set.univ ×ˢ Set.univ) := by
      rintro ⟨a, b⟩ -
      refine le_trans ?_ (hμ (a.map e, b.map e) ⟨trivial, trivial⟩)
      have heq_rel (z : Bool) :
          Cslib.Communication.Nondeterministic.uniqueDisjointnessRel U a b z ↔
            Cslib.Communication.Nondeterministic.uniqueDisjointnessRel (Fin k)
              (a.map e) (b.map e) z := by
        simp only [Cslib.Communication.Nondeterministic.uniqueDisjointnessRel,
          ← map_inter, card_map, disjoint_map]
      simp only [Cslib.RandomizedCost.errorProb, Cslib.Communication.Protocol.randomizedCost,
        Cslib.Probability.PMF.errorProb, μ', PMF.toOuterMeasure_map_apply]
      refine le_of_eq (congrArg ENNReal.toReal (congrArg μ.toOuterMeasure ?_))
      ext p
      simp [mapP, heq_rel]
    exact (Cslib.RandomizedCost.ecomplexity_le_maxCost hsolves).trans hcost
  cases hck : Cslib.Communication.PublicCoin.ecomplexity (1 / 3)
      (Cslib.Communication.Nondeterministic.uniqueDisjointnessRel (Fin k)) Set.univ Set.univ
    using ENat.recTopCoe with
  | top => simp
  | coe c =>
    have hU_le :
        Cslib.Communication.PublicCoin.ecomplexity (1 / 3)
           (Cslib.Communication.Nondeterministic.uniqueDisjointnessRel U) Set.univ Set.univ ≤ c :=
      hred.trans (by rw [hck])
    rw [Cslib.Communication.PublicCoin.ecomplexity_eq_randomizedCost] at hU_le
    obtain ⟨μ, hμ_solves, hμ_cost⟩ := Cslib.RandomizedCost.ecomplexity_le_iff.mp hU_le
    let S_prom : Set (Finset U × Finset U) := {q | #(q.1 ∩ q.2) ≤ 1}
    have hμ_disj :
        (Cslib.Communication.Protocol.randomizedCost (Finset U) (Finset U) Bool).Solves μ (1 / 3)
          (fun q b ↦ decide (Disjoint q.1 q.2) = b) S_prom := by
      intro q hq
      have hiff (b : Bool) :
          (decide (Disjoint q.1 q.2) = b) ↔
            Cslib.Communication.Nondeterministic.uniqueDisjointnessRel U q.1 q.2 b := by
        have hle1 : #(q.1 ∩ q.2) ≤ 1 := hq
        by_cases hd : Disjoint q.1 q.2
        · have hc0 : #(q.1 ∩ q.2) = 0 := by simp [disjoint_iff_inter_eq_empty.mp hd]
          cases b <;> simp [Cslib.Communication.Nondeterministic.uniqueDisjointnessRel, hd, hc0]
        · have hne : (q.1 ∩ q.2).Nonempty := not_disjoint_iff_nonempty_inter.mp hd
          have hc1 : #(q.1 ∩ q.2) = 1 := le_antisymm hle1 (card_pos.mpr hne)
          cases b <;> simp [Cslib.Communication.Nondeterministic.uniqueDisjointnessRel, hd, hc1]
      refine le_trans (le_of_eq ?_) (hμ_solves q ⟨trivial, trivial⟩)
      simp only [Cslib.RandomizedCost.errorProb, Cslib.Probability.PMF.errorProb]
      congr 2; ext p; simp [hiff]
    have hamp_solves :=
      Cslib.RandomizedCost.Solves.amplify
        (runAll := @Cslib.Communication.Protocol.runAll (Finset U) (Finset U) Bool Bool)
        (fun ps g q ↦ Cslib.Communication.Protocol.run_runAll ps g q.1 q.2)
        hμ_disj (by norm_num) 36
    have hamp_cost :
        Cslib.Probability.PMF.maxCost Cslib.Communication.Protocol.depth
          ((Cslib.Communication.Protocol.randomizedCost (Finset U) (Finset U) Bool).amplify
            (@Cslib.Communication.Protocol.runAll (Finset U) (Finset U) Bool Bool) μ 36) ≤
          ((72 * c : ℕ) : ℕ∞) := by
      have hc' := Cslib.Communication.PublicCoin.depth_amplify_le (c := c) hμ_cost 36
      refine hc'.trans_eq ?_
      push_cast
      ring
    have hsupp_prom : ∀ q ∈ (udisjHardDist m hU).support, q ∈ S_prom := by
      intro q hq
      have hne0 : udisjWeight m q ≠ 0 := by
        intro h0
        apply (PMF.mem_support_iff _ _).mp hq
        simp [udisjHardDist, h0]
      exact card_inter_le_one_of_udisjWeight_pos hU hne0
    obtain ⟨p, hp_mem, hp_err⟩ := hamp_solves.exists_distributionalError_le (udisjHardDist m hU)
      hsupp_prom
    have hp_depth : p.depth ≤ 72 * c := by
      exact_mod_cast (Cslib.Probability.PMF.le_maxCost hp_mem).trans hamp_cost
    have hp_err64 :
        p.distributionalError (udisjHardDist m hU)
          (fun x y b ↦ decide (Disjoint x y) = b) ≤ 1 / 64 :=
      hp_err.trans (by norm_num)
    set r := (m + 1) / 48
    have hr : 48 * r ≤ m + 1 := Nat.mul_div_le (m + 1) 48
    have hcorr := (udisjHardDist_corrupted hU hr).mul_sub_distributionalError_le (by norm_num) p
    have hmass :
        ((udisjHardDist m hU).toOuterMeasure
          {q | decide (Disjoint q.1 q.2) = true}).toReal = 1 / 2 := by
      rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal, Fintype.sum_prod_type]
      have htoReal (q : Finset U × Finset U) :
          (udisjHardDist m hU q).toReal = udisjWeight m q := by
        rw [udisjHardDist, PMF.ofFintype_apply, ENNReal.toReal_ofReal (udisjWeight_nonneg m q)]
      simp only [Set.mem_ofPred_eq, htoReal]
      exact (sum_udisjWeight_univ hU).1
    rw [hmass] at hcorr
    have hpow_le : (2 : ℝ) ^ p.depth * ((27 / 32 : ℝ) ^ r / 2) ≤
        (2 : ℝ) ^ (72 * c) * ((27 / 32 : ℝ) ^ r / 2) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hp_depth) (by positivity)
    have h13 : (13 : ℝ) / 1152 ≤ (2 : ℝ) ^ (72 * c) * ((27 / 32 : ℝ) ^ r / 2) := by linarith
    have hreal : (13 : ℝ) * 32 ^ r ≤ 576 * 2 ^ (72 * c) * 27 ^ r := by
      rw [div_pow, ← mul_div_assoc, ← mul_div_assoc, div_div, le_div_iff₀ (by positivity)] at h13
      linarith
    have hnat : 13 * 32 ^ r ≤ 576 * 2 ^ (72 * c) * 27 ^ r := by exact_mod_cast hreal
    have hr_le : r ≤ 5 * (72 * c) + 29 := by
      set q0 := r / 5
      set t0 := r % 5
      have hr0 : r = 5 * q0 + t0 := (Nat.div_add_mod r 5).symm
      have h1 : 2 ^ q0 * 27 ^ (5 * q0) ≤ 32 ^ (5 * q0) := by
        rw [pow_mul, pow_mul, ← mul_pow]
        exact Nat.pow_le_pow_left (by norm_num) q0
      have h2 : 27 ^ t0 ≤ 32 ^ t0 := Nat.pow_le_pow_left (by norm_num) t0
      have h3 : 13 * 2 ^ q0 * 27 ^ r ≤ 576 * 2 ^ (72 * c) * 27 ^ r :=
        calc 13 * 2 ^ q0 * 27 ^ r = 13 * (2 ^ q0 * 27 ^ (5 * q0)) * 27 ^ t0 := by
              rw [hr0, pow_add]; ring
          _ ≤ 13 * 32 ^ (5 * q0) * 32 ^ t0 := by gcongr
          _ = 13 * 32 ^ r := by rw [hr0, pow_add]; ring
          _ ≤ 576 * 2 ^ (72 * c) * 27 ^ r := hnat
      have h4 : 13 * 2 ^ q0 ≤ 576 * 2 ^ (72 * c) :=
        Nat.le_of_mul_le_mul_right h3 (by positivity)
      have h5 : q0 < 72 * c + 6 := by
        by_contra hq0
        have h6 : 2 ^ (72 * c) * 2 ^ 6 ≤ 2 ^ q0 := by
          rw [← pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 0 < 2 ^ (72 * c) := by positivity
        omega
      omega
    exact_mod_cast (by omega : k ≤ 2 ^ 16 * c + 2 ^ 12)

end PartitionCorruption

end CslibFrontier.Communication
