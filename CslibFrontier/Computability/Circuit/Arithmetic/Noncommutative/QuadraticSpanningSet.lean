/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.XYDecomposition
public import CslibFrontier.Foundations.Algebra.ElementarySymmetricBound

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Spanning Sets, Valid Parameterizations, and Surviving Generator Count

This module formalizes the inductive spanning-set framework for noncommutative circuits:
* syntactic-degree classes $G_k, P_k$, multiplier sets $\mathcal{M}_k$, and inductive spanning
  sets $\mathcal{B}_k \subseteq F\langle X\rangle$;
* spanning containment (`claim_spanning`) for all four $X,Y$-separated parts;
* valid parameterizations (`ValidParam`), parameterization existence (`lem_parametrization`),
  minimum-degree multiplier bounds (`lem_min_degree_multiplier`), degree truncation
  (`lem_degree_truncation`), elementary symmetric bound (`lem_elementary_symmetric`), and the
  surviving-generator count bound (`thm_surviving_generators`).

## Main definitions

* `CslibFrontier.Circuits.Arithmetic.Noncommutative.synDegValues`, `numSynDegs`, `synDegVal`:
  distinct syntactic degrees
  in $\Psi$ in strictly increasing order.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.gateClass`, `prodClass`, `prodClassCard`,
  `leftMultipliers`,
  `baseSet`, `spanningSet`, `terminalSet`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.ValidParam`: valid parameterizations $v = p_1
  \cdots p_r q$.

## Main results

* `CslibFrontier.Circuits.Arithmetic.Noncommutative.claim_spanning`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.lem_parametrization`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.lem_min_degree_multiplier`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.lem_degree_truncation`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.lem_elementary_symmetric`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.thm_surviving_generators`.
-/

public section

namespace CslibFrontier.Circuits.Arithmetic.Noncommutative

open _root_.FreeAlgebra

section SpanningSetDefs

variable {F : Type*} {n : ℕ}

/-- The finite set $\mathcal{D}_\Psi$ of distinct syntactic degrees appearing in $\Psi$. -/
def synDegValues (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) : Finset ℕ :=
  Finset.univ.image Ψ.synDeg

/-- The number $d' = |\mathcal{D}_\Psi|$ of distinct syntactic degrees in $\Psi$. -/
def numSynDegs (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) : ℕ :=
  (synDegValues Ψ).card

/-- Every circuit has at least one syntactic degree (`0 < numSynDegs Ψ`). -/
theorem numSynDegs_pos (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) : 0 < numSynDegs Ψ := by
  unfold numSynDegs synDegValues
  exact Finset.card_pos.mpr ⟨Ψ.synDeg Ψ.output, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

/-- The strictly increasing enumeration $l_0 < l_1 < \dots < l_{d'-1}$ of $\mathcal{D}_\Psi$. -/
def synDegVal (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) : Fin (numSynDegs Ψ) ↪o ℕ :=
  (synDegValues Ψ).orderEmbOfFin rfl

/-- `synDegVal Ψ k` belongs to `synDegValues Ψ`. -/
theorem synDegVal_mem (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) (k : Fin (numSynDegs Ψ)) :
    synDegVal Ψ k ∈ synDegValues Ψ :=
  Finset.orderEmbOfFin_mem (synDegValues Ψ) rfl k

/-- Every gate `g` has a unique syntactic degree class index `k` with `synDegVal Ψ k = Ψ.synDeg g`.
-/
theorem exists_synDegVal_eq (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) (g : Fin Ψ.size) :
    ∃ k : Fin (numSynDegs Ψ), synDegVal Ψ k = Ψ.synDeg g := by
  have hmem : Ψ.synDeg g ∈ synDegValues Ψ :=
    Finset.mem_image_of_mem _ (Finset.mem_univ g)
  have hmem' : Ψ.synDeg g ∈ Set.range ((synDegValues Ψ).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hmem
  exact hmem'

/-- The syntactic degree class $G_k = \{g \mid d(g) = l_k\}$. -/
def gateClass (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) (k : Fin (numSynDegs Ψ)) :
    Finset (Fin Ψ.size) :=
  Finset.univ.filter fun g ↦ Ψ.synDeg g = synDegVal Ψ k

/-- The product-gate class $P_k = \{g \in G_k \mid g\text{ is a product gate}\}$. -/
def prodClass (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) (k : Fin (numSynDegs Ψ)) :
    Finset (Fin Ψ.size) :=
  (gateClass Ψ k).filter Ψ.IsMulGate

/-- The size $s_k = |P_k|$ of the $k$-th product-gate class. -/
def prodClassCard (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) (k : Fin (numSynDegs Ψ)) : ℕ :=
  (prodClass Ψ k).card

/-- Total product-gate count bound: $\sum_k s_k \le s$. -/
theorem sum_prodClassCard_le_size (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) :
    ∑ k : Fin (numSynDegs Ψ), prodClassCard Ψ k ≤ Ψ.size := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin (numSynDegs Ψ))))
      (prodClass Ψ) := by
    intro k₁ _ k₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hg1).1).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hg2).1).2
    exact hne ((synDegVal Ψ).injective (h1.symm.trans h2))
  calc
    ∑ k : Fin (numSynDegs Ψ), prodClassCard Ψ k =
        (Finset.univ.biUnion (prodClass Ψ)).card := by
      rw [Finset.card_biUnion hdisj]
      rfl
    _ ≤ (Finset.univ : Finset (Fin Ψ.size)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Ψ.size := by simp

variable [CommSemiring F]

/-- The $X$-only polynomial $\widehat a_X$ of the left child of gate `g` if `g` is a product gate,
and `0` otherwise. -/
noncomputable def leftChildX (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) (g : Fin Ψ.size) :
    FreeAlgebra F (Fin n) :=
  match Ψ.gates g with
  | .mul a _ _ _ => extractX (Ψ.evalGate ⟨a.val, lt_trans a.isLt g.isLt⟩)
  | _ => 0

/-- The set of left multipliers $\mathcal{M}_k = \{\widehat a_X \mid g = a \times b \in P_k\}$. -/
noncomputable def leftMultipliers (Ψ : NoncommCircuit F (Fin n ⊕ Fin n))
    (k : Fin (numSynDegs Ψ)) : Finset (FreeAlgebra F (Fin n)) := by
  classical
  exact (prodClass Ψ k).image (leftChildX Ψ)

/-- $|\mathcal{M}_k| \le s_k$. -/
theorem card_leftMultipliers_le (Ψ : NoncommCircuit F (Fin n ⊕ Fin n))
    (k : Fin (numSynDegs Ψ)) :
    (leftMultipliers Ψ k).card ≤ prodClassCard Ψ k := by
  classical
  unfold leftMultipliers prodClassCard
  exact Finset.card_image_le

/-- The base set $\mathcal{B}_1 = \{1, x_1, \dots, x_n\} \subseteq F\langle X\rangle$. -/
noncomputable def baseSet (F : Type*) [CommSemiring F] (n : ℕ) :
    Finset (FreeAlgebra F (Fin n)) := by
  classical
  exact insert 1 (Finset.univ.image (ι F))

/-- $|\mathcal{B}_1| \le n + 1$. -/
theorem card_baseSet_le (F : Type*) [CommSemiring F] (n : ℕ) :
    (baseSet F n).card ≤ n + 1 := by
  classical
  unfold baseSet
  calc
    (insert (1 : FreeAlgebra F (Fin n)) (Finset.univ.image (ι F))).card ≤
        (Finset.univ.image (ι F)).card + 1 := Finset.card_insert_le _ _
    _ ≤ (Finset.univ : Finset (Fin n)).card + 1 :=
        Nat.add_le_add_right Finset.card_image_le 1
    _ = n + 1 := by simp

/-- Helper recursion defining $\mathcal{B}_k$ by natural-number index `k`. -/
noncomputable def spanningSetNat (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) :
    ℕ → Finset (FreeAlgebra F (Fin n))
  | 0 => baseSet F n
  | k + 1 =>
      if h : k + 1 < numSynDegs Ψ then by
        classical
        exact spanningSetNat Ψ k ∪
          ((prodClass Ψ ⟨k + 1, h⟩).image (fun g ↦ extractX (Ψ.evalGate g))) ∪
          ((leftMultipliers Ψ ⟨k + 1, h⟩).biUnion fun p ↦
            (spanningSetNat Ψ k).image fun v ↦ p * v)
      else spanningSetNat Ψ k

/-- The inductive spanning set $\mathcal{B}_k \subseteq F\langle X\rangle$ for
`k : Fin (numSynDegs Ψ)`. -/
noncomputable def spanningSet (Ψ : NoncommCircuit F (Fin n ⊕ Fin n))
    (k : Fin (numSynDegs Ψ)) : Finset (FreeAlgebra F (Fin n)) :=
  spanningSetNat Ψ k.val

/-- Monotonicity $\mathcal{B}_j \subseteq \mathcal{B}_k$ for $j \le k$. -/
theorem spanningSetNat_mono (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) {j k : ℕ} (hjk : j ≤ k) :
    spanningSetNat Ψ j ⊆ spanningSetNat Ψ k := by
  induction k with
  | zero =>
    have hj : j = 0 := by omega
    subst hj; exact Finset.Subset.refl _
  | succ k ih =>
    by_cases hle : j ≤ k
    · refine (ih hle).trans ?_
      dsimp only [spanningSetNat]
      split_ifs with hk
      · classical
        intro x hx
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
      · exact Finset.Subset.refl _
    · have hj : j = k + 1 := by omega
      subst hj; exact Finset.Subset.refl _

/-- Monotonicity $\mathcal{B}_j \subseteq \mathcal{B}_k$ on `Fin (numSynDegs Ψ)`. -/
theorem spanningSet_mono (Ψ : NoncommCircuit F (Fin n ⊕ Fin n))
    {j k : Fin (numSynDegs Ψ)} (hjk : j ≤ k) :
    spanningSet Ψ j ⊆ spanningSet Ψ k :=
  spanningSetNat_mono Ψ hjk

/-- `1 ∈ spanningSet Ψ k` for every `k`. -/
theorem one_mem_spanningSet (Ψ : NoncommCircuit F (Fin n ⊕ Fin n))
    (k : Fin (numSynDegs Ψ)) : (1 : FreeAlgebra F (Fin n)) ∈ spanningSet Ψ k := by
  apply spanningSetNat_mono Ψ (Nat.zero_le k.val)
  classical
  simp [spanningSetNat, baseSet]

/-- `ι F x ∈ spanningSet Ψ k` for every `x` and `k`. -/
theorem iota_mem_spanningSet (Ψ : NoncommCircuit F (Fin n ⊕ Fin n))
    (k : Fin (numSynDegs Ψ)) (x : Fin n) : ι F x ∈ spanningSet Ψ k := by
  apply spanningSetNat_mono Ψ (Nat.zero_le k.val)
  classical
  simp [spanningSetNat, baseSet]

/-- The terminal factor set $\mathcal{Q} = \mathcal{B}_1 \cup \{\widehat g_X \mid g\text{ is a
product gate}\}$. -/
noncomputable def terminalSet (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) :
    Finset (FreeAlgebra F (Fin n)) := by
  classical
  exact baseSet F n ∪
    (Finset.univ.filter Ψ.IsMulGate).image fun g ↦ extractX (Ψ.evalGate g)

/-- $|\mathcal{Q}| \le s + n + 1$. -/
theorem card_terminalSet_le (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) :
    (terminalSet Ψ).card ≤ Ψ.size + n + 1 := by
  classical
  unfold terminalSet
  calc
    (baseSet F n ∪
        (Finset.univ.filter Ψ.IsMulGate).image fun g ↦ extractX (Ψ.evalGate g)).card ≤
        (baseSet F n).card +
          ((Finset.univ.filter Ψ.IsMulGate).image fun g ↦ extractX (Ψ.evalGate g)).card :=
      Finset.card_union_le _ _
    _ ≤ (n + 1) + (Finset.univ.filter Ψ.IsMulGate).card :=
      Nat.add_le_add (card_baseSet_le F n) Finset.card_image_le
    _ ≤ (n + 1) + (Finset.univ : Finset (Fin Ψ.size)).card :=
      Nat.add_le_add_left (Finset.card_le_card (Finset.filter_subset _ _)) _
    _ = Ψ.size + n + 1 := by simp; omega

end SpanningSetDefs

section ClaimSpanning

variable {F : Type*} [Field F] {n : ℕ}

/-- Spanning containment: For every normalized circuit $\Psi$, every syntactic-degree
class $k$, and every gate $g \in G_k$, the coefficient sets of $\widehat g_1, \widehat g_X,
\widehat g_Y, \widehat g_{XY}$ all lie in $\mathrm{span}(\mathcal{B}_k)$. -/
theorem claim_spanning (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) (hNorm : Ψ.IsNormalized)
    (k : Fin (numSynDegs Ψ)) (g : Fin Ψ.size) (hg : g ∈ gateClass Ψ k) :
    coeffXSet (partOne (Ψ.evalGate g)) ⊆
        (Submodule.span F (spanningSet Ψ k : Set (FreeAlgebra F (Fin n))) :
          Set (FreeAlgebra F (Fin n))) ∧
      coeffXSet (partX (Ψ.evalGate g)) ⊆
        (Submodule.span F (spanningSet Ψ k : Set (FreeAlgebra F (Fin n))) :
          Set (FreeAlgebra F (Fin n))) ∧
      coeffXSet (partY (Ψ.evalGate g)) ⊆
        (Submodule.span F (spanningSet Ψ k : Set (FreeAlgebra F (Fin n))) :
          Set (FreeAlgebra F (Fin n))) ∧
      coeffXSet (partXY (Ψ.evalGate g)) ⊆
        (Submodule.span F (spanningSet Ψ k : Set (FreeAlgebra F (Fin n))) :
          Set (FreeAlgebra F (Fin n))) := by
  induction hn : g.val using Nat.strong_induction_on generalizing g k with
  | ind idx ih =>
    subst hn
    have hdeg : Ψ.synDeg g = synDegVal Ψ k := (Finset.mem_filter.mp hg).2
    have h1_mem : (1 : FreeAlgebra F (Fin n)) ∈ Submodule.span F (spanningSet Ψ k : Set _) :=
      Submodule.subset_span (Finset.mem_coe.mpr (one_mem_spanningSet Ψ k))
    have hconst_in : ∀ c : F, c • (1 : FreeAlgebra F (Fin n)) ∈
        Submodule.span F (spanningSet Ψ k : Set _) :=
      fun c ↦ Submodule.smul_mem _ c h1_mem
    -- Show all four via `coeffXSet_subset_submodule_iff`.
    simp only [coeffXSet_subset_submodule_iff]
    cases hgate : Ψ.gates g with
    | const c =>
      have heval : Ψ.evalGate g = algebraMap F (FreeAlgebra F (Fin n ⊕ Fin n)) c :=
        Ψ.evalGate_const hgate
      refine ⟨fun m ↦ ?_, fun m ↦ ?_, fun m ↦ ?_, fun m ↦ ?_⟩
      · obtain ⟨r, hr⟩ := coeffY_partOne_eq_smul_one m (Ψ.evalGate g)
        rw [hr]; exact hconst_in r
      · by_cases hm : m = 1
        · subst hm
          rw [coeffY_one_partX, heval, extractX_algebraMap]
          exact Submodule.zero_mem _
        · rw [coeffY_partX_of_ne_one hm]; exact Submodule.zero_mem _
      · obtain ⟨r, hr⟩ := coeffY_partY_eq_smul_one m (Ψ.evalGate g)
        rw [hr]; exact hconst_in r
      · rw [heval, partXY_algebraMap, map_zero]; exact Submodule.zero_mem _
    | var x =>
      have heval : Ψ.evalGate g = ι F x := Ψ.evalGate_var hgate
      refine ⟨fun m ↦ ?_, fun m ↦ ?_, fun m ↦ ?_, fun m ↦ ?_⟩
      · obtain ⟨r, hr⟩ := coeffY_partOne_eq_smul_one m (Ψ.evalGate g)
        rw [hr]; exact hconst_in r
      · by_cases hm : m = 1
        · subst hm
          rw [coeffY_one_partX, heval]
          cases x with
          | inl i =>
            rw [extractX_iota_inl]
            exact Submodule.subset_span (Finset.mem_coe.mpr (iota_mem_spanningSet Ψ k i))
          | inr i =>
            rw [extractX_iota_inr]; exact Submodule.zero_mem _
        · rw [coeffY_partX_of_ne_one hm]; exact Submodule.zero_mem _
      · obtain ⟨r, hr⟩ := coeffY_partY_eq_smul_one m (Ψ.evalGate g)
        rw [hr]; exact hconst_in r
      · rw [heval, partXY_iota, map_zero]; exact Submodule.zero_mem _
    | add a b wa wb =>
      let ga : Fin Ψ.size := ⟨a.val, lt_trans a.isLt g.isLt⟩
      let gb : Fin Ψ.size := ⟨b.val, lt_trans b.isLt g.isLt⟩
      obtain ⟨ka, hka⟩ := exists_synDegVal_eq Ψ ga
      obtain ⟨kb, hkb⟩ := exists_synDegVal_eq Ψ gb
      have hdeg_g : Ψ.synDeg g = max (Ψ.synDeg ga) (Ψ.synDeg gb) := Ψ.synDeg_add hgate
      have hka_le : ka ≤ k :=
        (synDegVal Ψ).le_iff_le.mp (by rw [hka, ← hdeg, hdeg_g]; exact le_max_left _ _)
      have hkb_le : kb ≤ k :=
        (synDegVal Ψ).le_iff_le.mp (by rw [hkb, ← hdeg, hdeg_g]; exact le_max_right _ _)
      have hga_mem : ga ∈ gateClass Ψ ka := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hka.symm⟩
      have hgb_mem : gb ∈ gateClass Ψ kb := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkb.symm⟩
      have iha := ih a.val a.isLt ka ga hga_mem rfl
      have ihb := ih b.val b.isLt kb gb hgb_mem rfl
      simp only [coeffXSet_subset_submodule_iff] at iha ihb
      have hmono_a : Submodule.span F (spanningSet Ψ ka : Set (FreeAlgebra F (Fin n))) ≤
          Submodule.span F (spanningSet Ψ k : Set (FreeAlgebra F (Fin n))) :=
        Submodule.span_mono (Finset.coe_subset.mpr (spanningSet_mono Ψ hka_le))
      have hmono_b : Submodule.span F (spanningSet Ψ kb : Set (FreeAlgebra F (Fin n))) ≤
          Submodule.span F (spanningSet Ψ k : Set (FreeAlgebra F (Fin n))) :=
        Submodule.span_mono (Finset.coe_subset.mpr (spanningSet_mono Ψ hkb_le))
      have heval : Ψ.evalGate g = wa • Ψ.evalGate ga + wb • Ψ.evalGate gb :=
        Ψ.evalGate_add hgate
      refine ⟨fun m ↦ ?_, fun m ↦ ?_, fun m ↦ ?_, fun m ↦ ?_⟩
      · rw [heval, map_add, map_smul, map_smul, map_add, map_smul, map_smul]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (hmono_a (iha.1 m)))
          (Submodule.smul_mem _ _ (hmono_b (ihb.1 m)))
      · rw [heval, map_add, map_smul, map_smul, map_add, map_smul, map_smul]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (hmono_a (iha.2.1 m)))
          (Submodule.smul_mem _ _ (hmono_b (ihb.2.1 m)))
      · rw [heval, map_add, map_smul, map_smul, map_add, map_smul, map_smul]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (hmono_a (iha.2.2.1 m)))
          (Submodule.smul_mem _ _ (hmono_b (ihb.2.2.1 m)))
      · rw [heval, map_add, map_smul, map_smul, map_add, map_smul, map_smul]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (hmono_a (iha.2.2.2 m)))
          (Submodule.smul_mem _ _ (hmono_b (ihb.2.2.2 m)))
    | mul a b wa wb =>
      let ga : Fin Ψ.size := ⟨a.val, lt_trans a.isLt g.isLt⟩
      let gb : Fin Ψ.size := ⟨b.val, lt_trans b.isLt g.isLt⟩
      obtain ⟨ka, hka⟩ := exists_synDegVal_eq Ψ ga
      obtain ⟨kb, hkb⟩ := exists_synDegVal_eq Ψ gb
      have hdeg_g : Ψ.synDeg g = Ψ.synDeg ga + Ψ.synDeg gb := Ψ.synDeg_mul hgate
      obtain ⟨hpos_a, hpos_b⟩ := hNorm.mul_pos g a b wa wb hgate
      change 1 ≤ Ψ.synDeg ga at hpos_a
      change 1 ≤ Ψ.synDeg gb at hpos_b
      have hka_lt : ka < k :=
        (synDegVal Ψ).lt_iff_lt.mp (by rw [hka, ← hdeg, hdeg_g]; omega)
      have hkb_lt : kb < k :=
        (synDegVal Ψ).lt_iff_lt.mp (by rw [hkb, ← hdeg, hdeg_g]; omega)
      have hk_pos : 0 < k.val := by omega
      have hpred_lt : k.val - 1 < numSynDegs Ψ := by omega
      let kprev : Fin (numSynDegs Ψ) := ⟨k.val - 1, hpred_lt⟩
      have hka_le : ka ≤ kprev := by change ka.val ≤ k.val - 1; omega
      have hkb_le : kb ≤ kprev := by change kb.val ≤ k.val - 1; omega
      have hga_mem : ga ∈ gateClass Ψ ka := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hka.symm⟩
      have hgb_mem : gb ∈ gateClass Ψ kb := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkb.symm⟩
      have iha := ih a.val a.isLt ka ga hga_mem rfl
      have ihb := ih b.val b.isLt kb gb hgb_mem rfl
      simp only [coeffXSet_subset_submodule_iff] at iha ihb
      have hmono_a : Submodule.span F (spanningSet Ψ ka : Set (FreeAlgebra F (Fin n))) ≤
          Submodule.span F (spanningSet Ψ kprev : Set (FreeAlgebra F (Fin n))) :=
        Submodule.span_mono (Finset.coe_subset.mpr (spanningSet_mono Ψ hka_le))
      have hmono_b : Submodule.span F (spanningSet Ψ kb : Set (FreeAlgebra F (Fin n))) ≤
          Submodule.span F (spanningSet Ψ kprev : Set (FreeAlgebra F (Fin n))) :=
        Submodule.span_mono (Finset.coe_subset.mpr (spanningSet_mono Ψ hkb_le))
      have hmono_prev : Submodule.span F (spanningSet Ψ kprev : Set (FreeAlgebra F (Fin n))) ≤
          Submodule.span F (spanningSet Ψ k : Set (FreeAlgebra F (Fin n))) :=
        Submodule.span_mono (Finset.coe_subset.mpr (spanningSet_mono Ψ (show kprev ≤ k by
          change k.val - 1 ≤ k.val; omega)))
      have hg_prod : g ∈ prodClass Ψ k := by
        rw [prodClass, Finset.mem_filter]
        exact ⟨hg, by simp [NoncommCircuit.IsMulGate, hgate]⟩
      have hgx_mem : extractX (Ψ.evalGate g) ∈ spanningSet Ψ k := by
        have hk_eq : k = ⟨(k.val - 1) + 1, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [spanningSet, hk_eq]
        dsimp only
        rw [spanningSetNat, dite_eq_left (by omega)]
        classical
        have hg_prod' : g ∈ prodClass Ψ ⟨k.val - 1 + 1, by omega⟩ := hk_eq ▸ hg_prod
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image_of_mem _ hg_prod'))
      have haX_mem : extractX (Ψ.evalGate ga) ∈ leftMultipliers Ψ k := by
        classical
        unfold leftMultipliers
        refine Finset.mem_image.mpr ⟨g, hg_prod, ?_⟩
        simp [leftChildX, hgate, ga]
      have hmul_mem : ∀ h ∈ spanningSet Ψ kprev,
          extractX (Ψ.evalGate ga) * h ∈ spanningSet Ψ k := by
        intro h hh
        have hk_eq : k = ⟨(k.val - 1) + 1, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [spanningSet, hk_eq]
        dsimp only
        rw [spanningSetNat, dite_eq_left (by omega)]
        classical
        refine Finset.mem_union_right _ ?_
        rw [Finset.mem_biUnion]
        refine ⟨extractX (Ψ.evalGate ga), hk_eq ▸ haX_mem, ?_⟩
        exact Finset.mem_image_of_mem _ hh
      have hmul_span : ∀ h ∈ Submodule.span F (spanningSet Ψ kprev : Set _),
          extractX (Ψ.evalGate ga) * h ∈ Submodule.span F (spanningSet Ψ k : Set _) := by
        intro h hh
        induction hh using Submodule.span_induction with
        | mem v hv =>
          exact Submodule.subset_span (Finset.mem_coe.mpr (hmul_mem v (Finset.mem_coe.mp hv)))
        | zero => rw [mul_zero]; exact Submodule.zero_mem _
        | add v₁ v₂ _ _ ih₁ ih₂ => rw [mul_add]; exact Submodule.add_mem _ ih₁ ih₂
        | smul c v _ ihv => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ihv
      have heval : Ψ.evalGate g = (wa * wb) • (Ψ.evalGate ga * Ψ.evalGate gb) := by
        rw [Ψ.evalGate_mul hgate, smul_mul_smul_comm]
      refine ⟨fun m ↦ ?_, fun m ↦ ?_, fun m ↦ ?_, fun m ↦ ?_⟩
      · obtain ⟨r, hr⟩ := coeffY_partOne_eq_smul_one m (Ψ.evalGate g)
        rw [hr]; exact hconst_in r
      · by_cases hm : m = 1
        · subst hm
          rw [coeffY_one_partX]
          exact Submodule.subset_span (Finset.mem_coe.mpr hgx_mem)
        · rw [coeffY_partX_of_ne_one hm]; exact Submodule.zero_mem _
      · obtain ⟨r, hr⟩ := coeffY_partY_eq_smul_one m (Ψ.evalGate g)
        rw [hr]; exact hconst_in r
      · rw [heval, map_smul, map_smul]
        apply Submodule.smul_mem
        rw [partXY_mul, map_add, map_add, map_add, map_add]
        refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
          ?_ ?_) ?_) ?_) ?_
        · -- `partX a * partY b`
          obtain ⟨r, hr⟩ := coeffY_partX_mul_partY_eq_smul m (Ψ.evalGate ga) (Ψ.evalGate gb)
          rw [hr]
          apply Submodule.smul_mem
          have h1_prev : (1 : FreeAlgebra F (Fin n)) ∈
              Submodule.span F (spanningSet Ψ kprev : Set _) :=
            Submodule.subset_span (Finset.mem_coe.mpr (one_mem_spanningSet Ψ kprev))
          simpa [mul_one] using hmul_span 1 h1_prev
        · -- `partXY a * partY b`
          rw [coeffY_partXY_mul_partY]
          exact Submodule.sum_mem _ fun j _ ↦
            Submodule.smul_mem _ _ (hmono_prev (hmono_a (iha.2.2.2 _)))
        · -- `partX a * partXY b`
          rw [coeffY_partX_mul_partXY]
          exact hmul_span _ (hmono_b (ihb.2.2.2 m))
        · -- `partXY a * partOne b`
          rw [coeffY_partXY_mul_partOne]
          exact Submodule.smul_mem _ _ (hmono_prev (hmono_a (iha.2.2.2 m)))
        · -- `partOne a * partXY b`
          rw [coeffY_partOne_mul_partXY]
          exact Submodule.smul_mem _ _ (hmono_prev (hmono_b (ihb.2.2.2 m)))

/-- Spanning corollary: if a normalized circuit $\Psi$ computes $\mathrm{Pal}_{n,n}(X,Y)$,
then $\mathrm{Coeff}_X(\mathrm{Pal}_{n,n}(X,Y)) \subseteq \mathrm{span}(\mathcal{B}_{d'})$. -/
theorem coeffXSet_palPoly_subset_span (Ψ : NoncommCircuit F (Fin n ⊕ Fin n))
    (hNorm : Ψ.IsNormalized) (hΨ : Ψ.eval = palPoly F n n) :
    coeffXSet (palPoly F n n) ⊆
      (Submodule.span F (spanningSet Ψ ⟨numSynDegs Ψ - 1, Nat.sub_lt (numSynDegs_pos Ψ)
        Nat.zero_lt_one⟩ : Set (FreeAlgebra F (Fin n))) : Set (FreeAlgebra F (Fin n))) := by
  let last : Fin (numSynDegs Ψ) :=
    ⟨numSynDegs Ψ - 1, Nat.sub_lt (numSynDegs_pos Ψ) Nat.zero_lt_one⟩
  obtain ⟨k, hk⟩ := exists_synDegVal_eq Ψ Ψ.output
  have hmem : Ψ.output ∈ gateClass Ψ k := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.symm⟩
  have hclaim := claim_spanning Ψ hNorm k Ψ.output hmem
  simp only [coeffXSet_subset_submodule_iff] at hclaim ⊢
  have hmono : Submodule.span F (spanningSet Ψ k : Set (FreeAlgebra F (Fin n))) ≤
      Submodule.span F (spanningSet Ψ last : Set (FreeAlgebra F (Fin n))) :=
    Submodule.span_mono (Finset.coe_subset.mpr (spanningSet_mono Ψ (show k ≤ last by
      change k.val ≤ numSynDegs Ψ - 1; omega)))
  intro m
  have hsum : palPoly F n n = partOne (Ψ.evalGate Ψ.output) + partX (Ψ.evalGate Ψ.output) +
      partY (Ψ.evalGate Ψ.output) + partXY (Ψ.evalGate Ψ.output) := by
    have hd := part_decomposition (palPoly F n n)
    rw [partOther_palPoly F n n, add_zero] at hd
    rw [Ψ.eval_eq_evalGate_output] at hΨ
    rw [hΨ]
    exact hd.symm
  rw [hsum, map_add, map_add, map_add]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (hmono (hclaim.1 m)) (hmono (hclaim.2.1 m))) (hmono (hclaim.2.2.1 m)))
    (hmono (hclaim.2.2.2 m))

end ClaimSpanning

section ParameterizationAndCounting

variable {F : Type*} [Field F] {n : ℕ}

/-- A valid parameterization $v = p_1 p_2 \cdots p_r q$ of an element of $F\langle X\rangle$
in the spanning-set recursion. -/
structure ValidParam (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) where
  /-- Length $r \ge 0$ of the multiplier prefix. -/
  r : ℕ
  /-- Strictly decreasing sequence of syntactic-degree class indices $m_1 > \dots > m_r$. -/
  indices : Fin r → Fin (numSynDegs Ψ)
  /-- Class indices strictly decrease. -/
  strictAnti : StrictAnti indices
  /-- Left multipliers $p_i \in \mathcal{M}_{m_i}$. -/
  multipliers : Fin r → FreeAlgebra F (Fin n)
  /-- Membership of each multiplier in $\mathcal{M}_{m_i}$. -/
  mem_mul : ∀ i : Fin r, multipliers i ∈ leftMultipliers Ψ (indices i)
  /-- Terminal factor $q \in \mathcal{Q}$. -/
  terminal : FreeAlgebra F (Fin n)
  /-- Membership of the terminal factor in $\mathcal{Q}$. -/
  mem_term : terminal ∈ terminalSet Ψ

/-- The polynomial $p_1 p_2 \cdots p_r q$ represented by a valid parameterization. -/
noncomputable def ValidParam.val {Ψ : NoncommCircuit F (Fin n ⊕ Fin n)}
    (vp : ValidParam Ψ) : FreeAlgebra F (Fin n) :=
  (List.ofFn vp.multipliers).prod * vp.terminal

/-- Existence of valid parameterizations: Every element of $\mathcal{B}_k$ admits a valid
parameterization in which all class indices are at most $k$. -/
theorem lem_parametrization (Ψ : NoncommCircuit F (Fin n ⊕ Fin n))
    (k : Fin (numSynDegs Ψ)) {v : FreeAlgebra F (Fin n)} (hv : v ∈ spanningSet Ψ k) :
    ∃ vp : ValidParam Ψ, vp.val = v ∧ ∀ i : Fin vp.r, vp.indices i ≤ k := by
  induction hn : k.val generalizing k v with
  | zero =>
    have hbase : v ∈ baseSet F n := by
      simpa [spanningSet, hn, spanningSetNat] using hv
    refine ⟨{
      r := 0
      indices := Fin.elim0
      strictAnti := fun i ↦ Fin.elim0 i
      multipliers := Fin.elim0
      mem_mul := fun i ↦ Fin.elim0 i
      terminal := v
      mem_term := by classical exact Finset.mem_union_left _ hbase
    }, ?_, fun i ↦ Fin.elim0 i⟩
    simp [ValidParam.val]
  | succ m ih =>
    have hlt : m < numSynDegs Ψ := by omega
    have hk_eq : k = ⟨m + 1, by omega⟩ := Fin.ext hn
    have hv' : v ∈ spanningSetNat Ψ (m + 1) := by simpa [spanningSet, hn] using hv
    rw [spanningSetNat, dite_eq_left (by omega)] at hv'
    classical
    rcases Finset.mem_union.mp hv' with h12 | h3
    · rcases Finset.mem_union.mp h12 with h1 | h2
      · obtain ⟨vp, hval, hle⟩ := ih ⟨m, hlt⟩ h1 rfl
        exact ⟨vp, hval, fun i ↦ (hle i).trans (by change m ≤ k.val; omega)⟩
      · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp h2
        have hg_mul : g ∈ Finset.univ.filter Ψ.IsMulGate :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hg).2⟩
        refine ⟨{
          r := 0
          indices := Fin.elim0
          strictAnti := fun i ↦ Fin.elim0 i
          multipliers := Fin.elim0
          mem_mul := fun i ↦ Fin.elim0 i
          terminal := extractX (Ψ.evalGate g)
          mem_term := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hg_mul)
        }, by simp [ValidParam.val], fun i ↦ Fin.elim0 i⟩
    · obtain ⟨p, hp, hmem_im⟩ := Finset.mem_biUnion.mp h3
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hmem_im
      obtain ⟨vp, hval, hle⟩ := ih ⟨m, hlt⟩ hh rfl
      refine ⟨{
        r := vp.r + 1
        indices := Fin.cons k vp.indices
        strictAnti := by
          intro i j hij
          cases i using Fin.cases with
          | zero =>
            cases j using Fin.cases with
            | zero => exact absurd hij (lt_irrefl _)
            | succ j' =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              exact lt_of_le_of_lt (hle j') (by change m < k.val; omega)
          | succ i' =>
            cases j using Fin.cases with
            | zero => exact absurd hij (Fin.not_lt_zero _)
            | succ j' =>
              simp only [Fin.cons_succ]
              exact vp.strictAnti (Fin.succ_lt_succ_iff.mp hij)
        multipliers := Fin.cons p vp.multipliers
        mem_mul := fun i ↦ by
          refine Fin.cases ?_ (fun i' ↦ ?_) i
          · simpa [hk_eq] using hp
          · exact vp.mem_mul i'
        terminal := vp.terminal
        mem_term := vp.mem_term
      }, ?_, ?_⟩
      · simp only [ValidParam.val, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons,
          mul_assoc]
        rw [← hval]
        rfl
      · intro i
        refine Fin.cases le_rfl (fun i' ↦ (hle i').trans (by change m ≤ k.val; omega)) i

/-- Minimum-degree bound: For every gate $g$ of $\Psi$, either
$\widehat g_X = 0$ or $\mathrm{mindeg}(\widehat g_X) \ge 1$. In particular, every nonzero
$p \in \mathcal{M}_k$ satisfies $\mathrm{mindeg}(p) \ge 1$. -/
theorem lem_min_degree_multiplier (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) :
    (∀ g : Fin Ψ.size,
      extractX (Ψ.evalGate g) = 0 ∨
        1 ≤ CslibFrontier.FreeAlgebra.minDeg (extractX (Ψ.evalGate g))) ∧
    (∀ (k : Fin (numSynDegs Ψ)) (p : FreeAlgebra F (Fin n)),
      p ∈ leftMultipliers Ψ k → p ≠ 0 → 1 ≤ CslibFrontier.FreeAlgebra.minDeg p) := by
  refine ⟨fun g ↦ extractX_eq_zero_or_one_le_minDeg (Ψ.evalGate g), fun k p hp hp0 ↦ ?_⟩
  classical
  obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hp
  unfold leftChildX at hp0 ⊢
  cases hgate : Ψ.gates g with
  | const _ => simp [hgate] at hp0
  | var _ => simp [hgate] at hp0
  | add _ _ _ _ => simp [hgate] at hp0
  | mul a _ _ _ =>
    simp only [hgate] at hp0 ⊢
    exact (extractX_eq_zero_or_one_le_minDeg _).resolve_left hp0

/-- Degree truncation: If $v = p_1 p_2 \cdots p_r q$ is a
valid parameterization with $r > n$, then $\pi_n(v) = 0$. -/
theorem lem_degree_truncation (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) (vp : ValidParam Ψ)
    (hr : n < vp.r) :
    CslibFrontier.FreeAlgebra.homogeneousComponent n vp.val = 0 := by
  by_cases hq : vp.terminal = 0
  · simp [ValidParam.val, hq]
  · by_cases hall : ∀ i : Fin vp.r, vp.multipliers i ≠ 0
    · have hlist : ∀ p ∈ List.ofFn vp.multipliers,
          p ≠ 0 ∧ 1 ≤ CslibFrontier.FreeAlgebra.minDeg p := by
        intro p hp
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
        exact ⟨hall i, (lem_min_degree_multiplier Ψ).2 (vp.indices i) _ (vp.mem_mul i) (hall i)⟩
      obtain ⟨hprod_ne, hlen_le⟩ :=
        CslibFrontier.FreeAlgebra.listProd_ne_zero_and_length_le_minDeg _ hlist
      rw [List.length_ofFn] at hlen_le
      have hmin : vp.r ≤ CslibFrontier.FreeAlgebra.minDeg vp.val := by
        rw [ValidParam.val, CslibFrontier.FreeAlgebra.minDeg_mul hprod_ne hq]
        omega
      exact CslibFrontier.FreeAlgebra.homogeneousComponent_eq_zero_of_lt_minDeg
        (lt_of_lt_of_le hr hmin)
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      have hzero : (List.ofFn vp.multipliers).prod = 0 :=
        List.prod_eq_zero (List.mem_ofFn.mpr ⟨i, hi⟩)
      simp [ValidParam.val, hzero]

/-- Elementary symmetric inequality: For any nonnegative reals $a_1, \dots, a_t$ and
integer $r \ge 0$, $e_r(a_1, \dots, a_t) \le \frac{1}{r!}(\sum_{i=1}^t a_i)^r$. -/
theorem lem_elementary_symmetric {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (r : ℕ) :
    (s.val.map a).esymm r ≤ (∑ i ∈ s, a i) ^ r / (r.factorial : ℝ) :=
  CslibFrontier.MvPolynomial.esymm_le_sum_pow_div_factorial s a ha r

/-- Finite index type of length-`r` parameterizations `(S, multipliers, terminal)` with `|S| = r`.
-/
private abbrev ParamChoice (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) (r : ℕ) :=
  Σ (S : {S : Finset (Fin (numSynDegs Ψ)) // S.card = r}),
    (∀ k : S.1, {p : FreeAlgebra F (Fin n) // p ∈ leftMultipliers Ψ k.1}) ×
      {q : FreeAlgebra F (Fin n) // q ∈ terminalSet Ψ}

/-- The surviving generators $\{v \in \mathcal{B}_{d'} \mid \pi_n(v) \neq 0\}$ with nonzero
degree-$n$ homogeneous component. -/
noncomputable def survivingGenerators (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) :
    Finset (FreeAlgebra F (Fin n)) := by
  classical
  exact (spanningSet Ψ ⟨numSynDegs Ψ - 1,
    Nat.sub_lt (numSynDegs_pos Ψ) Nat.zero_lt_one⟩).filter fun v ↦
      CslibFrontier.FreeAlgebra.homogeneousComponent n v ≠ 0

/-- Membership characterization for `survivingGenerators`. -/
theorem mem_survivingGenerators (Ψ : NoncommCircuit F (Fin n ⊕ Fin n))
    {v : FreeAlgebra F (Fin n)} :
    v ∈ survivingGenerators Ψ ↔
      v ∈ spanningSet Ψ ⟨numSynDegs Ψ - 1, Nat.sub_lt (numSynDegs_pos Ψ) Nat.zero_lt_one⟩ ∧
        CslibFrontier.FreeAlgebra.homogeneousComponent n v ≠ 0 := by
  classical
  simp [survivingGenerators]

/-- Surviving-generator count bound: The number of elements $v \in \mathcal{B}_{d'}$
with nonzero degree-$n$ projection satisfies
$|\{v \in \mathcal{B}_{d'} \mid \pi_n(v) \neq 0\}| \le (s + n + 1)\sum_{r=0}^n \frac{s^r}{r!}$. -/
theorem thm_surviving_generators (Ψ : NoncommCircuit F (Fin n ⊕ Fin n)) :
    ((survivingGenerators Ψ).card : ℝ) ≤
      ((Ψ.size + n + 1 : ℕ) : ℝ) *
        ∑ r ∈ Finset.range (n + 1), (Ψ.size : ℝ) ^ r / (r.factorial : ℝ) := by
  classical
  let last : Fin (numSynDegs Ψ) :=
    ⟨numSynDegs Ψ - 1, Nat.sub_lt (numSynDegs_pos Ψ) Nat.zero_lt_one⟩
  let surv := survivingGenerators Ψ
  let evalChoice : (Σ r : Fin (n + 1), ParamChoice Ψ r.val) → FreeAlgebra F (Fin n) :=
    fun ⟨⟨r, _⟩, ⟨⟨S, hS⟩, mults, q⟩⟩ ↦
      let emb : Fin r ↪o Fin (numSynDegs Ψ) := S.orderEmbOfFin hS
      (List.ofFn fun i : Fin r ↦
        (mults ⟨emb (Fin.rev i), Finset.orderEmbOfFin_mem S hS (Fin.rev i)⟩).1).prod * q.1
  have hsurj : (surv : Set (FreeAlgebra F (Fin n))) ⊆ Set.range evalChoice := by
    intro v hv
    have hv_mem : v ∈ spanningSet Ψ last ∧
        CslibFrontier.FreeAlgebra.homogeneousComponent n v ≠ 0 := by
      simpa [surv, survivingGenerators, last] using Finset.mem_coe.mp hv
    obtain ⟨vp, rfl, -⟩ := lem_parametrization Ψ last hv_mem.1
    have hle_n : vp.r ≤ n := by
      by_contra hgt
      exact hv_mem.2 (lem_degree_truncation Ψ vp (Nat.lt_of_not_le hgt))
    let S : Finset (Fin (numSynDegs Ψ)) := Finset.univ.image vp.indices
    have hS : S.card = vp.r := by
      rw [Finset.card_image_of_injective _ vp.strictAnti.injective, Finset.card_fin]
    let emb : Fin vp.r ↪o Fin (numSynDegs Ψ) := S.orderEmbOfFin hS
    have hemb_rev : ∀ i : Fin vp.r, emb (Fin.rev i) = vp.indices i := by
      have hinc : StrictMono (fun i : Fin vp.r ↦ vp.indices (Fin.rev i)) := by
        intro i j hij
        exact vp.strictAnti (Fin.rev_lt_rev.mpr hij)
      have hrange_eq : Set.range (fun i : Fin vp.r ↦ vp.indices (Fin.rev i)) = (S : Set _) := by
        ext x
        simp only [Set.mem_range, Finset.mem_coe, S, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, rfl⟩; exact ⟨Fin.rev i, rfl⟩
        · rintro ⟨i, rfl⟩; exact ⟨Fin.rev i, by simp⟩
      have hfun_eq : (emb : Fin vp.r → Fin (numSynDegs Ψ)) = fun i ↦ vp.indices (Fin.rev i) :=
        StrictMono.range_inj_of_wellFoundedLT emb.strictMono hinc |>.mp (by
          rw [Finset.range_orderEmbOfFin, hrange_eq])
      intro i
      simpa using congrFun hfun_eq (Fin.rev i)
    let mults : ∀ k : S, {p : FreeAlgebra F (Fin n) // p ∈ leftMultipliers Ψ k.1} := fun k ↦
      let i : Fin vp.r := (Finset.mem_image.mp k.2).choose
      have hi : vp.indices i = k.1 := (Finset.mem_image.mp k.2).choose_spec.2
      ⟨vp.multipliers i, hi ▸ vp.mem_mul i⟩
    refine ⟨⟨⟨vp.r, Nat.lt_succ_of_le hle_n⟩, ⟨⟨S, hS⟩, mults, ⟨vp.terminal, vp.mem_term⟩⟩⟩, ?_⟩
    simp only [evalChoice, ValidParam.val]
    congr 1
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext i
    dsimp only [mults]
    have hidx : (Finset.mem_image.mp (Finset.orderEmbOfFin_mem S hS (Fin.rev i))).choose = i := by
      apply vp.strictAnti.injective
      have hspec := (Finset.mem_image.mp (Finset.orderEmbOfFin_mem S hS (Fin.rev i))).choose_spec.2
      exact hspec.trans (hemb_rev i)
    rw [hidx]
  have hcard_le : surv.card ≤ Fintype.card (Σ r : Fin (n + 1), ParamChoice Ψ r.val) := by
    have hsub : surv ⊆ Finset.univ.image evalChoice := by
      intro v hv
      obtain ⟨x, rfl⟩ := hsurj hv
      exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have hcard_eq : Fintype.card (Σ r : Fin (n + 1), ParamChoice Ψ r.val) =
      ∑ r ∈ Finset.range (n + 1), Fintype.card (ParamChoice Ψ r) := by
    rw [Fintype.card_sigma, Fin.sum_univ_eq_sum_range (fun r ↦ Fintype.card (ParamChoice Ψ r))]
  have hcard_r : ∀ r : ℕ,
      (Fintype.card (ParamChoice Ψ r) : ℝ) ≤
        ((Ψ.size + n + 1 : ℕ) : ℝ) * ((Ψ.size : ℝ) ^ r / (r.factorial : ℝ)) := by
    intro r
    have hpc : Fintype.card (ParamChoice Ψ r) =
        (terminalSet Ψ).card *
          ∑ S ∈ (Finset.univ : Finset (Fin (numSynDegs Ψ))).powersetCard r,
            ∏ k ∈ S, (leftMultipliers Ψ k).card := by
      rw [Fintype.card_sigma]
      simp_rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_coe]
      rw [← Finset.sum_mul, mul_comm]
      congr 1
      refine Finset.sum_bij (fun S _ ↦ (S : Finset (Fin (numSynDegs Ψ)))) ?_ ?_ ?_ ?_
      · intro S _; exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.2⟩
      · intro S₁ _ S₂ _ h; exact Subtype.ext h
      · intro S hS; exact ⟨⟨S, (Finset.mem_powersetCard.mp hS).2⟩, Finset.mem_univ _, rfl⟩
      · intro S _
        exact Finset.prod_coe_sort S.1 (fun k ↦ (leftMultipliers Ψ k).card)
    have hnat_le :
        Fintype.card (ParamChoice Ψ r) ≤
          (Ψ.size + n + 1) *
            ∑ S ∈ (Finset.univ : Finset (Fin (numSynDegs Ψ))).powersetCard r,
              ∏ k ∈ S, prodClassCard Ψ k := by
      rw [hpc]
      refine Nat.mul_le_mul (card_terminalSet_le Ψ) ?_
      exact Finset.sum_le_sum fun S _ ↦
        Finset.prod_le_prod fun k _ ↦ card_leftMultipliers_le Ψ k
    have hcast :
        (Fintype.card (ParamChoice Ψ r) : ℝ) ≤
          ((Ψ.size + n + 1 : ℕ) : ℝ) *
            ((Finset.univ : Finset (Fin (numSynDegs Ψ))).val.map
              (fun k ↦ (prodClassCard Ψ k : ℝ))).esymm r := by
      have h1 : ((Fintype.card (ParamChoice Ψ r) : ℕ) : ℝ) ≤
          (((Ψ.size + n + 1) *
            ∑ S ∈ (Finset.univ : Finset (Fin (numSynDegs Ψ))).powersetCard r,
              ∏ k ∈ S, prodClassCard Ψ k : ℕ) : ℝ) := by exact_mod_cast hnat_le
      refine h1.trans_eq ?_
      rw [Finset.esymm_map_val]
      push_cast
      rfl
    have hes := lem_elementary_symmetric (Finset.univ : Finset (Fin (numSynDegs Ψ)))
      (fun k ↦ (prodClassCard Ψ k : ℝ)) (fun _ _ ↦ Nat.cast_nonneg _) r
    have hsum_le : (∑ k : Fin (numSynDegs Ψ), (prodClassCard Ψ k : ℝ)) ≤ (Ψ.size : ℝ) := by
      exact_mod_cast sum_prodClassCard_le_size Ψ
    have hsum_nonneg : 0 ≤ ∑ k : Fin (numSynDegs Ψ), (prodClassCard Ψ k : ℝ) :=
      Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
    have hpow_le : (∑ k : Fin (numSynDegs Ψ), (prodClassCard Ψ k : ℝ)) ^ r / (r.factorial : ℝ) ≤
        (Ψ.size : ℝ) ^ r / (r.factorial : ℝ) := by
      gcongr
    refine hcast.trans ?_
    exact mul_le_mul_of_nonneg_left (hes.trans hpow_le) (Nat.cast_nonneg _)
  calc
    (surv.card : ℝ) ≤
        ((Fintype.card (Σ r : Fin (n + 1), ParamChoice Ψ r.val) : ℕ) : ℝ) := by
      exact_mod_cast hcard_le
    _ = ∑ r ∈ Finset.range (n + 1), (Fintype.card (ParamChoice Ψ r) : ℝ) := by
      rw [hcard_eq]
      push_cast
      rfl
    _ ≤ ∑ r ∈ Finset.range (n + 1),
          ((Ψ.size + n + 1 : ℕ) : ℝ) * ((Ψ.size : ℝ) ^ r / (r.factorial : ℝ)) :=
      Finset.sum_le_sum fun r _ ↦ hcard_r r
    _ = ((Ψ.size + n + 1 : ℕ) : ℝ) *
          ∑ r ∈ Finset.range (n + 1), (Ψ.size : ℝ) ^ r / (r.factorial : ℝ) := by
      rw [← Finset.mul_sum]

end ParameterizationAndCounting

end CslibFrontier.Circuits.Arithmetic.Noncommutative
