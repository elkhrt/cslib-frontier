module

public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Computability.DecisionTree.NormalForm
public import CslibFrontier.Logics.Propositional.CNF
public import CslibFrontier.Logics.Propositional.DNF
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Certificate-Complexity Switching, Truncated Decision Trees, and Entropy Bounds

This module collects three general combinatorial tools for Boolean functions:

1. **Binomial-sum entropy bounds**: for `0 < β ≤ 1/2` and `k ≤ ⌊β m⌋`, the number of subsets of
   `Fin m` of size at most `k` satisfies `∑_{a ≤ k} C(m, a) ≤ exp (binEntropy β * m)`.
2. **Weighted degeneracy coloring**: every loopless directed graph on a finite vertex set with
   maximum outdegree at most `W` admits a proper `(2W + 1)`-coloring and an independent set of
   weight at least `(∑ w_v) / (2W + 1)`.
3. **Truncated decision trees from small certificates**: for any CNF `H` of width at most `W` on
   `Fin K → Bool` and any `q ≥ 1`, there exists a deterministic decision tree `T` of depth at most
   `W * q` (and hence a DNF of at most `2 ^ (W * q)` terms of width at most `W * q`) such that
   `T ≤ H` pointwise and `T z = true` whenever `H z = true` and `certOneAt H.eval z ≤ q`.

## Main definitions

* `CslibFrontier.BooleanFunction.chooseSum`: `∑ a ∈ range (min m t + 1), m.choose a`.
* `CslibFrontier.BooleanFunction.cnfWidth`, `CslibFrontier.BooleanFunction.dnfWidth`: maximum
  clause/term length.
* `CslibFrontier.BooleanFunction.IsOneCertificate`, `CslibFrontier.BooleanFunction.certOneAt`:
  1-certificate complexity of a Boolean function at an accepting input `z`.
* `CslibFrontier.BooleanFunction.substClause`, `CslibFrontier.BooleanFunction.substCNF`:
  normalized partial assignment substitution on CNF formulas.

## Main results

* `CslibFrontier.BooleanFunction.chooseSum_le_exp_binEntropy`: binomial tail bound via binary
  entropy.
* `CslibFrontier.BooleanFunction.exists_indep_weight_ge_of_outdeg_le`: weighted `(2W+1)`-coloring
  lemma for bounded-outdegree directed graphs.
* `CslibFrontier.BooleanFunction.exists_truncated_decisionTree` and
  `CslibFrontier.BooleanFunction.exists_truncated_dnf`: truncated certificate-to-decision-tree
  theorem.

-/

public section

namespace CslibFrontier

namespace BooleanFunction

open Cslib Cslib.Logic.PL Finset

/-! ### Binomial-sum binary entropy bounds -/

/-- The binomial sum `∑_{a = 0}^{min m t} C(m, a)`, i.e. the number of subsets of `Fin m` of size
at most `t`. -/
@[expose] def chooseSum (m t : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (min m t + 1), m.choose a

@[simp] theorem chooseSum_zero_right (m : ℕ) : chooseSum m 0 = 1 := by
  simp [chooseSum]

@[simp] theorem chooseSum_zero_left (t : ℕ) : chooseSum 0 t = 1 := by
  simp [chooseSum]

theorem chooseSum_eq_sum_range (m t : ℕ) :
    chooseSum m t = ∑ a ∈ Finset.range (t + 1), m.choose a := by
  unfold chooseSum
  rcases le_or_gt m t with h | h
  · rw [min_eq_left h]
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun a ha hna => ?_
    rw [Finset.mem_range] at ha hna
    exact Nat.choose_eq_zero_of_lt (by omega)
  · rw [min_eq_right h.le]

theorem chooseSum_eq_card_powerset (m t : ℕ) :
    chooseSum m t = #{S : Finset (Fin m) | S.card ≤ t} := by
  rw [chooseSum_eq_sum_range]
  have hpart : ({S : Finset (Fin m) | S.card ≤ t} : Finset (Finset (Fin m))) =
      (Finset.range (t + 1)).biUnion (fun a => (Finset.univ : Finset (Fin m)).powersetCard a) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard, Finset.subset_univ]
    exact ⟨fun h => ⟨S.card, by omega, rfl⟩, fun ⟨a, ha, hS⟩ => by omega⟩
  rw [hpart, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · intro a _ b _ hab
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro S hSa hSb
    rw [Finset.mem_powersetCard] at hSa hSb
    exact hab (hSa.2.symm.trans hSb.2)

/-- **Chernoff / binary-entropy binomial tail bound**: for `0 < β ≤ 1/2` and `k ≤ β m`,
`chooseSum m k ≤ exp (Real.binEntropy β * m)`. -/
theorem chooseSum_le_exp_binEntropy {m k : ℕ} {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1 / 2)
    (hk : (k : ℝ) ≤ β * m) :
    (chooseSum m k : ℝ) ≤ Real.exp (Real.binEntropy β * m) := by
  rw [chooseSum_eq_sum_range]
  have h1β : 0 < 1 - β := by linarith
  have hratio : β / (1 - β) ≤ 1 := (div_le_one h1β).mpr (by linarith)
  have hsum1 : (∑ a ∈ Finset.range (k + 1), (m.choose a : ℝ)) * β ^ k * (1 - β) ^ (m - k) ≤
      (∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) * β ^ a * (1 - β) ^ (m - a)) := by
    have hk_le_m : k ≤ m := by
      have : (k : ℝ) ≤ (1 / 2 : ℝ) * m := hk.trans (mul_le_mul_of_nonneg_right hβ₁ (by positivity))
      have : (k : ℝ) ≤ m := by linarith
      exact_mod_cast this
    have hsub : Finset.range (k + 1) ⊆ Finset.range (m + 1) :=
      Finset.range_mono (by omega)
    calc (∑ a ∈ Finset.range (k + 1), (m.choose a : ℝ)) * β ^ k * (1 - β) ^ (m - k)
        = ∑ a ∈ Finset.range (k + 1), (m.choose a : ℝ) * (β ^ k * (1 - β) ^ (m - k)) := by
          rw [Finset.sum_mul, Finset.sum_mul]; refine Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ ∑ a ∈ Finset.range (k + 1), (m.choose a : ℝ) * (β ^ a * (1 - β) ^ (m - a)) := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [Finset.mem_range] at ha
          have ham : a ≤ m := by omega
          have hpow : β ^ k * (1 - β) ^ (m - k) ≤ β ^ a * (1 - β) ^ (m - a) := by
            have h1 : (β / (1 - β)) ^ k ≤ (β / (1 - β)) ^ a :=
              pow_le_pow_of_le_one (by positivity) hratio (by omega)
            rw [div_pow, div_pow, div_le_div_iff₀ (by positivity) (by positivity)] at h1
            have hsub_eq : (1 - β) ^ (m - a) = (1 - β) ^ (k - a) * (1 - β) ^ (m - k) := by
              rw [← pow_add]; congr 1; omega
            have hpow_k : (1 - β) ^ k = (1 - β) ^ a * (1 - β) ^ (k - a) := by
              rw [← pow_add]; congr 1; omega
            have hmul : (1 - β) ^ a * (β ^ k * (1 - β) ^ (m - k)) ≤
                (1 - β) ^ a * (β ^ a * (1 - β) ^ (m - a)) := by
              have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg h1β.le (m - k))
              calc (1 - β) ^ a * (β ^ k * (1 - β) ^ (m - k))
                  = β ^ k * (1 - β) ^ a * (1 - β) ^ (m - k) := by ring
                _ ≤ β ^ a * (1 - β) ^ k * (1 - β) ^ (m - k) := h2
                _ = (1 - β) ^ a * (β ^ a * ((1 - β) ^ (k - a) * (1 - β) ^ (m - k))) := by
                    rw [hpow_k]; ring
                _ = (1 - β) ^ a * (β ^ a * (1 - β) ^ (m - a)) := by rw [hsub_eq]
            exact le_of_mul_le_mul_left hmul (pow_pos h1β a)
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ ∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) * (β ^ a * (1 - β) ^ (m - a)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = ∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) * β ^ a * (1 - β) ^ (m - a) := by
          refine Finset.sum_congr rfl fun _ _ => by ring
  have hbinom : (∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) * β ^ a * (1 - β) ^ (m - a)) = 1 := by
    have := add_pow β (1 - β) m
    rw [add_sub_cancel, one_pow] at this
    calc (∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) * β ^ a * (1 - β) ^ (m - a))
        = ∑ a ∈ Finset.range (m + 1), β ^ a * (1 - β) ^ (m - a) * (m.choose a : ℝ) :=
          Finset.sum_congr rfl fun _ _ => by ring
      _ = 1 := this.symm
  rw [hbinom] at hsum1
  have hbound : (∑ a ∈ Finset.range (k + 1), (m.choose a : ℝ)) ≤
      (β ^ k * (1 - β) ^ (m - k))⁻¹ := by
    rw [← one_div, le_div_iff₀ (by positivity)]
    linarith
  have hexp_eq : Real.exp (Real.binEntropy β * m) =
      (β ^ (β * m) * (1 - β) ^ ((1 - β) * m))⁻¹ := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog]
    rw [show (-β * Real.log β + -(1 - β) * Real.log (1 - β)) * (m : ℝ) =
        -(Real.log β * (β * m) + Real.log (1 - β) * ((1 - β) * m)) by ring,
      Real.exp_neg, Real.exp_add, Real.rpow_def_of_pos hβ₀, Real.rpow_def_of_pos h1β]
  -- Compare `β^k * (1-β)^(m-k)` vs `β^(β m) * (1-β)^((1-β) m)` using `β / (1-β) ≤ 1` and `k ≤ β m`
  have hcomp : β ^ (β * m) * (1 - β) ^ ((1 - β) * m) ≤
    β ^ (k : ℝ) * (1 - β) ^ ((m - k : ℕ) : ℝ) := by
    have hk_le_m : k ≤ m := by
      have : (k : ℝ) ≤ m := by nlinarith
      exact_mod_cast this
    have hdiff : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := Nat.cast_sub hk_le_m
    rw [hdiff]
    have hlog_le : Real.log (β / (1 - β)) ≤ 0 := Real.log_nonpos (by positivity) hratio
    have hmul : (β * m - k) * Real.log (β / (1 - β)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hlog_le
    rw [Real.log_div (ne_of_gt hβ₀) (ne_of_gt h1β)] at hmul
    have hlin : β * m * Real.log β + (1 - β) * m * Real.log (1 - β) ≤
        (k : ℝ) * Real.log β + ((m : ℝ) - k) * Real.log (1 - β) := by linarith
    have hexp := Real.exp_le_exp.mpr hlin
    rw [Real.exp_add, Real.exp_add,
      show β * m * Real.log β = Real.log β * (β * m) by ring,
      show (1 - β) * m * Real.log (1 - β) = Real.log (1 - β) * ((1 - β) * m) by ring,
      show (k : ℝ) * Real.log β = Real.log β * k by ring,
      show ((m : ℝ) - k) * Real.log (1 - β) = Real.log (1 - β) * ((m : ℝ) - k) by ring,
      ← Real.rpow_def_of_pos hβ₀, ← Real.rpow_def_of_pos h1β,
      ← Real.rpow_def_of_pos hβ₀, ← Real.rpow_def_of_pos h1β] at hexp
    exact hexp
  have hcast : (∑ a ∈ Finset.range (k + 1), (m.choose a : ℝ)) =
      ((∑ a ∈ Finset.range (k + 1), m.choose a : ℕ) : ℝ) := by push_cast; rfl
  rw [← hcast]
  calc (∑ a ∈ Finset.range (k + 1), (m.choose a : ℝ))
      ≤ (β ^ k * (1 - β) ^ (m - k))⁻¹ := hbound
    _ = (β ^ (k : ℝ) * (1 - β) ^ ((m - k : ℕ) : ℝ))⁻¹ := by
        rw [Real.rpow_natCast, Real.rpow_natCast]
    _ ≤ (β ^ (β * m) * (1 - β) ^ ((1 - β) * m))⁻¹ :=
        inv_anti₀ (by positivity) hcomp
    _ = Real.exp (Real.binEntropy β * m) := hexp_eq.symm

/-! ### Weighted degeneracy coloring for bounded-outdegree directed graphs -/

/-- **Weighted degeneracy coloring**: any directed graph on a finite set `V` in which every vertex
has outdegree at most `W` (and no self-loops) admits an independent subset `S ⊆ V` whose total
weight is at least `(∑ v ∈ V, wt v) / (2 W + 1)`. -/
theorem exists_indep_weight_ge_of_outdeg_le {α : Type*} [DecidableEq α] (V : Finset α)
    (adj : α → Finset α) (wt : α → ℕ) (W : ℕ)
    (hloopless : ∀ v ∈ V, v ∉ adj v)
    (hout : ∀ v ∈ V, (adj v ∩ V).card ≤ W) :
    ∃ S ⊆ V, (∀ u ∈ S, ∀ v ∈ S, v ∉ adj u) ∧
      ∑ v ∈ V, wt v ≤ (2 * W + 1) * ∑ v ∈ S, wt v := by
  -- First prove existence of a proper `(2*W+1)`-coloring by strong induction on `V.card`
  have hcol : ∀ (U : Finset α), U ⊆ V →
      ∃ c : α → Fin (2 * W + 1), ∀ u ∈ U, ∀ v ∈ U, v ∈ adj u → c u ≠ c v := by
    intro U
    induction hcard : U.card using Nat.strong_induction_on generalizing U with
    | ind k ih =>
      intro hUV
      by_cases hU : U.Nonempty
      · -- Find a vertex `v₀ ∈ U` of total (in + out) degree `≤ 2 * W` in `U`
        have hsum_deg : ∑ u ∈ U, ((adj u ∩ U).card + (U.filter fun x => u ∈ adj x).card) ≤
            2 * W * U.card := by
          have houtU : ∑ u ∈ U, (adj u ∩ U).card ≤ W * U.card := by
            calc ∑ u ∈ U, (adj u ∩ U).card
                ≤ ∑ _u ∈ U, W := Finset.sum_le_sum fun u hu =>
                  (Finset.card_le_card (Finset.inter_subset_inter_left hUV)).trans (hout u (hUV hu))
              _ = W * U.card := by simp [mul_comm]
          have hinU : ∑ u ∈ U, (U.filter fun x => u ∈ adj x).card =
              ∑ x ∈ U, (adj x ∩ U).card := by
            simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
          rw [Finset.sum_add_distrib, hinU]
          linarith
        have hex : ∃ v₀ ∈ U, (adj v₀ ∩ U).card + (U.filter fun x => v₀ ∈ adj x).card ≤ 2 * W := by
          by_contra hall
          push Not at hall
          have hgt : ∑ u ∈ U, (2 * W + 1) ≤
              ∑ u ∈ U, ((adj u ∩ U).card + (U.filter fun x => u ∈ adj x).card) :=
            Finset.sum_le_sum fun u hu => hall u hu
          simp only [Finset.sum_const, smul_eq_mul] at hgt
          have hpos : 0 < U.card := hU.card_pos
          nlinarith
        obtain ⟨v₀, hv₀, hdeg⟩ := hex
        let U' := U.erase v₀
        have hU'card : U'.card < k := by
          rw [← hcard]; exact Finset.card_erase_lt_of_mem hv₀
        obtain ⟨c', hc'⟩ := ih U'.card hU'card U' rfl ((Finset.erase_subset v₀ U).trans hUV)
        -- The neighbors of `v₀` in `U'` use at most `2 * W` colors
        let nbrs := (adj v₀ ∩ U') ∪ (U'.filter fun x => v₀ ∈ adj x)
        have hnbrs_le : (nbrs.image c').card ≤ 2 * W := by
          refine (Finset.card_image_le).trans ?_
          refine (Finset.card_union_le _ _).trans ?_
          have h1 : (adj v₀ ∩ U').card ≤ (adj v₀ ∩ U).card :=
            Finset.card_le_card (Finset.inter_subset_inter_left (Finset.erase_subset v₀ U))
          have h2 : (U'.filter fun x => v₀ ∈ adj x).card ≤ (U.filter fun x => v₀ ∈ adj x).card :=
            Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset v₀ U))
          omega
        have hfree : (Finset.univ \ nbrs.image c').Nonempty := by
          rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
            Fintype.card_fin]
          omega
        obtain ⟨col, hcol⟩ := hfree
        rw [Finset.mem_sdiff] at hcol
        refine ⟨Function.update c' v₀ col, fun u hu v hv huv => ?_⟩
        by_cases hu0 : u = v₀
        · subst hu0
          have hv0 : v ≠ u := fun h => hloopless u (hUV hu) (h ▸ huv)
          have hv' : v ∈ U' := Finset.mem_erase.mpr ⟨hv0, hv⟩
          rw [Function.update_self, Function.update_of_ne hv0]
          intro heq
          apply hcol.2
          exact Finset.mem_image.mpr ⟨v, Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨huv, hv'⟩),
            heq.symm⟩
        · by_cases hv0 : v = v₀
          · subst hv0
            have hu' : u ∈ U' := Finset.mem_erase.mpr ⟨hu0, hu⟩
            rw [Function.update_of_ne hu0, Function.update_self]
            intro heq
            apply hcol.2
            exact Finset.mem_image.mpr ⟨u,
              Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu', huv⟩), heq⟩
          · rw [Function.update_of_ne hu0, Function.update_of_ne hv0]
            exact hc' u (Finset.mem_erase.mpr ⟨hu0, hu⟩) v (Finset.mem_erase.mpr ⟨hv0, hv⟩) huv
      · rw [Finset.not_nonempty_iff_eq_empty] at hU
        subst hU
        exact ⟨fun _ => 0, fun _ h => by simp at h⟩
  obtain ⟨c, hc⟩ := hcol V (Finset.Subset.refl V)
  -- Take a color class maximizing total weight
  have hsum_part : ∑ v ∈ V, wt v = ∑ col : Fin (2 * W + 1), ∑ v ∈ V.filter (fun v => c v =
    col), wt v := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := V) (t := (Finset.univ : Finset (Fin (2 * W + 1))))
      (g := c) (fun _ _ => Finset.mem_univ _)]
  have hex_max : ∃ col : Fin (2 * W + 1),
      ∑ v ∈ V, wt v ≤ (2 * W + 1) * ∑ v ∈ V.filter (fun v => c v = col), wt v := by
    by_contra hall
    push Not at hall
    have hlt : ∑ col : Fin (2 * W + 1), (2 * W + 1) *
        ∑ v ∈ V.filter (fun v => c v = col), wt v <
        ∑ _col : Fin (2 * W + 1), ∑ v ∈ V, wt v :=
      Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) fun col _ => hall col
    rw [← Finset.mul_sum, ← hsum_part] at hlt
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
    omega
  obtain ⟨col, hcol_wt⟩ := hex_max
  refine ⟨V.filter (fun v => c v = col), Finset.filter_subset _ _, ?_, hcol_wt⟩
  intro u hu v hv huv
  rw [Finset.mem_filter] at hu hv
  exact hc u hu.1 v hv.1 huv (hu.2.trans hv.2.symm)

/-! ### CNF/DNF width and 1-certificate complexity -/

/-- The width of a CNF formula (maximum length of its clauses, `0` if empty). -/
@[expose] def cnfWidth {V : Type*} (H : CNF V) : ℕ :=
  H.foldr (fun c acc => max c.length acc) 0

/-- The width of a DNF formula (maximum length of its terms, `0` if empty). -/
@[expose] def dnfWidth {V : Type*} (Φ : DNF V) : ℕ :=
  Φ.foldr (fun t acc => max t.length acc) 0

@[simp] theorem cnfWidth_nil {V : Type*} : cnfWidth ([] : CNF V) = 0 := rfl

@[simp] theorem cnfWidth_cons {V : Type*} (c : Clause V) (H : CNF V) :
    cnfWidth (c :: H) = max c.length (cnfWidth H) := rfl

@[simp] theorem dnfWidth_nil {V : Type*} : dnfWidth ([] : DNF V) = 0 := rfl

@[simp] theorem dnfWidth_cons {V : Type*} (t : Term V) (Φ : DNF V) :
    dnfWidth (t :: Φ) = max t.length (dnfWidth Φ) := rfl

theorem length_le_cnfWidth {V : Type*} {H : CNF V} {c : Clause V} (hc : c ∈ H) :
    c.length ≤ cnfWidth H := by
  induction H with
  | nil => simp at hc
  | cons c' H ih =>
    simp only [cnfWidth, List.foldr_cons]
    rcases List.mem_cons.mp hc with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem cnfWidth_le_iff {V : Type*} {H : CNF V} {W : ℕ} :
    cnfWidth H ≤ W ↔ ∀ c ∈ H, c.length ≤ W := by
  induction H with
  | nil => simp [cnfWidth]
  | cons c H ih =>
    simp only [cnfWidth, List.foldr_cons, max_le_iff, List.mem_cons, forall_eq_or_imp]
    exact and_congr_right fun _ => ih

theorem length_le_dnfWidth {V : Type*} {Φ : DNF V} {t : Term V} (ht : t ∈ Φ) :
    t.length ≤ dnfWidth Φ := by
  induction Φ with
  | nil => simp at ht
  | cons t' Φ ih =>
    simp only [dnfWidth, List.foldr_cons]
    rcases List.mem_cons.mp ht with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem dnfWidth_le_iff {V : Type*} {Φ : DNF V} {W : ℕ} :
    dnfWidth Φ ≤ W ↔ ∀ t ∈ Φ, t.length ≤ W := by
  induction Φ with
  | nil => simp [dnfWidth]
  | cons t Φ ih =>
    simp only [dnfWidth, List.foldr_cons, max_le_iff, List.mem_cons, forall_eq_or_imp]
    exact and_congr_right fun _ => ih

/-- A set `S : Finset (Fin K)` is a **1-certificate** of `f : (Fin K → Bool) → Bool` at `z` if
`f z = true` and `f z' = true` whenever `z'` agrees with `z` on `S`. -/
@[expose] def IsOneCertificate {K : ℕ} (f : (Fin K → Bool) → Bool) (z : Fin K → Bool)
    (S : Finset (Fin K)) : Prop :=
  f z = true ∧ ∀ z' : Fin K → Bool, (∀ i ∈ S, z' i = z i) → f z' = true

/-- Every 1-certificate of `f` at `z` witnesses `f z = true`. -/
theorem IsOneCertificate.eval_eq_true {K : ℕ} {f : (Fin K → Bool) → Bool} {z : Fin K → Bool}
    {S : Finset (Fin K)} (h : IsOneCertificate f z S) : f z = true :=
  h.1

/-- Every input `z'` agreeing with `z` on a 1-certificate `S` also satisfies `f z' = true`. -/
theorem IsOneCertificate.eval_of_agree {K : ℕ} {f : (Fin K → Bool) → Bool} {z z' : Fin K → Bool}
    {S : Finset (Fin K)} (h : IsOneCertificate f z S) (hagree : ∀ i ∈ S, z' i = z i) :
    f z' = true :=
  h.2 z' hagree

/-- Construct a 1-certificate of `f` at `z` from `f z = true` and agreement invariance on `S`. -/
theorem IsOneCertificate.of_forall_agree {K : ℕ} {f : (Fin K → Bool) → Bool} {z : Fin K → Bool}
    {S : Finset (Fin K)} (hz : f z = true)
    (hagree : ∀ z' : Fin K → Bool, (∀ i ∈ S, z' i = z i) → f z' = true) :
    IsOneCertificate f z S :=
  ⟨hz, hagree⟩

theorem isOneCertificate_univ {K : ℕ} {f : (Fin K → Bool) → Bool} {z : Fin K → Bool}
    (h : f z = true) : IsOneCertificate f z Finset.univ :=
  ⟨h, fun z' hz' => by
    have : z' = z := funext fun i => hz' i (Finset.mem_univ i)
    rw [this, h]⟩

/-- The **1-certificate complexity** of `f` at an input `z` (for accepting `z`, the minimum size of
a 1-certificate; `0` if `f z = false`). -/
@[expose] noncomputable def certOneAt {K : ℕ} (f : (Fin K → Bool) → Bool) (z : Fin K → Bool) :
    ℕ := by
  classical
  exact if h : f z = true then
    Nat.find (⟨K, Finset.univ, isOneCertificate_univ h, by simp⟩ :
      ∃ m, ∃ S : Finset (Fin K), IsOneCertificate f z S ∧ S.card ≤ m)
  else
    0

theorem certOneAt_le_iff {K : ℕ} {f : (Fin K → Bool) → Bool} {z : Fin K → Bool}
    (hf : f z = true) {q : ℕ} :
    certOneAt f z ≤ q ↔ ∃ S : Finset (Fin K), IsOneCertificate f z S ∧ S.card ≤ q := by
  classical
  simp only [certOneAt, hf, ↓reduceDIte]
  constructor
  · intro h
    obtain ⟨S, hS, hcard⟩ := Nat.find_spec
      (⟨K, Finset.univ, isOneCertificate_univ hf, by simp⟩ :
        ∃ m, ∃ S : Finset (Fin K), IsOneCertificate f z S ∧ S.card ≤ m)
    exact ⟨S, hS, hcard.trans h⟩
  · intro h
    exact Nat.find_min' _ h

theorem lt_certOneAt_iff {K : ℕ} {f : (Fin K → Bool) → Bool} {z : Fin K → Bool}
    (hf : f z = true) {q : ℕ} :
    q < certOneAt f z ↔ ∀ S : Finset (Fin K), IsOneCertificate f z S → q < S.card := by
  rw [← not_le, certOneAt_le_iff hf]
  push Not
  rfl

/-- Substitute a partial assignment `ρ` into a clause `c`, returning `none` if the clause is
satisfied (contains a true literal or both `v` and `¬v`), or `some c'` with surviving non-false
deduplicated literals. -/
@[expose] def substClause {K : ℕ} (ρ : Fin K → Option Bool) (c : Clause (Fin K)) :
    Option (Clause (Fin K)) :=
  let rec
    /-- Recursive worker substituting a partial assignment `ρ` into a list of literals. -/
    go : Clause (Fin K) → Option (Clause (Fin K))
    | [] => some []
    | l :: ls =>
      match ρ l.1 with
      | some b => if b == l.2 then none else go ls
      | none =>
        if (l.1, !l.2) ∈ ls then none
        else
          match go ls with
          | none => none
          | some c' => if l ∈ c' then some c' else some (l :: c')
  go c

/-- Substitute a partial assignment `ρ` into a CNF `H`, deleting satisfied clauses. -/
@[expose] def substCNF {K : ℕ} (ρ : Fin K → Option Bool) (H : CNF (Fin K)) : CNF (Fin K) :=
  H.filterMap (substClause ρ)

@[simp] theorem substClause_nil {K : ℕ} (ρ : Fin K → Option Bool) :
    substClause ρ [] = some [] := rfl

@[simp] theorem substCNF_nil {K : ℕ} (ρ : Fin K → Option Bool) :
    substCNF ρ [] = [] := rfl

private theorem substClause_go_eval {K : ℕ} (ρ : Fin K → Option Bool) (c : Clause (Fin K))
    (z : Fin K → Bool) (hagree : ∀ i b, ρ i = some b → z i = b) :
    (match substClause.go ρ c with
      | none => true
      | some c' => Clause.eval z c') = Clause.eval z c := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    unfold substClause.go
    cases hρ : ρ l.1 with
    | some b =>
      dsimp only
      have hzb := hagree l.1 b hρ
      cases hb : (b == l.2)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [Clause.eval_cons, Literal.eval, hzb, hb, Bool.false_or]
        exact ih
      · simp only [↓reduceIte]
        rw [Clause.eval_cons, Literal.eval, hzb, hb, Bool.true_or]
    | none =>
      dsimp only
      by_cases hneg : (l.1, !l.2) ∈ ls
      · simp only [hneg, ↓reduceIte]
        rw [Clause.eval_cons]
        cases hzl : Literal.eval z l
        · have hmem : Clause.eval z ls = true := by
            rw [Clause.eval_eq_true_iff]
            refine ⟨(l.1, !l.2), hneg, ?_⟩
            simp only [Literal.eval, beq_eq_false_iff_ne] at hzl
            cases h1 : z l.1 <;> cases h2 : l.2 <;> simp_all
          simp [hmem]
        · simp
      · simp only [hneg, ↓reduceIte]
        cases hgo : substClause.go ρ ls with
        | none =>
          rw [hgo] at ih
          rw [Clause.eval_cons, ← ih, Bool.or_true]
        | some c' =>
          rw [hgo] at ih
          by_cases hmem : l ∈ c'
          · simp only [hmem, ↓reduceIte]
            rw [Clause.eval_cons, ← ih]
            by_cases hl : Literal.eval z l = true
            · have : Clause.eval z c' = true := by
                rw [Clause.eval_eq_true_iff]
                exact ⟨l, hmem, (Literal.eval_eq_true_iff z l).mp hl⟩
              simp [hl, this]
            · simp [Bool.eq_false_iff.mpr hl]
          · simp only [hmem, ↓reduceIte, Clause.eval_cons, ← ih]

theorem eval_substCNF {K : ℕ} (ρ : Fin K → Option Bool) (H : CNF (Fin K)) (z : Fin K → Bool)
    (hagree : ∀ i b, ρ i = some b → z i = b) :
    CNF.eval z (substCNF ρ H) = CNF.eval z H := by
  induction H with
  | nil => rfl
  | cons c H ih =>
    simp only [substCNF, List.filterMap_cons]
    have hc := substClause_go_eval ρ c z hagree
    cases hsub : substClause ρ c with
    | none =>
      change (match substClause.go ρ c with | none => true | some c' => Clause.eval z c') = _ at hc
      rw [show substClause.go ρ c = none from hsub] at hc
      rw [CNF.eval_cons, ← hc, Bool.true_and]
      exact ih
    | some c' =>
      change (match substClause.go ρ c with | none => true | some c' => Clause.eval z c') = _ at hc
      rw [show substClause.go ρ c = some c' from hsub] at hc
      rw [CNF.eval_cons, CNF.eval_cons, ← hc]
      exact congrArg (Clause.eval z c' && ·) ih

private theorem substClause_go_cons_cases {K : ℕ} {ρ : Fin K → Option Bool}
    {l₀ : Literal (Fin K)} {ls c' : Clause (Fin K)}
    (h : substClause.go ρ (l₀ :: ls) = some c') :
    (∃ b, ρ l₀.1 = some b ∧ substClause.go ρ ls = some c') ∨
    (ρ l₀.1 = none ∧ (l₀.1, !l₀.2) ∉ ls ∧
      ((l₀ ∈ c' ∧ substClause.go ρ ls = some c') ∨
       ∃ c'', substClause.go ρ ls = some c'' ∧ l₀ ∉ c'' ∧ c' = l₀ :: c'')) := by
  unfold substClause.go at h
  cases hρ : ρ l₀.1 with
  | some b =>
    rw [hρ] at h; dsimp only at h
    split_ifs at h with hb
    exact Or.inl ⟨b, rfl, h⟩
  | none =>
    rw [hρ] at h; dsimp only at h
    split_ifs at h with hneg
    cases hgo : substClause.go ρ ls with
    | none => rw [hgo] at h; dsimp only at h; simp at h
    | some c'' =>
      rw [hgo] at h; dsimp only at h
      split_ifs at h with hm
      · cases h; exact Or.inr ⟨rfl, hneg, Or.inl ⟨hm, rfl⟩⟩
      · cases h; exact Or.inr ⟨rfl, hneg, Or.inr ⟨c'', rfl, hm, rfl⟩⟩

private theorem substClause_go_mem_none {K : ℕ} (ρ : Fin K → Option Bool) (c : Clause (Fin K))
    {c' : Clause (Fin K)} (h : substClause.go ρ c = some c') {l : Literal (Fin K)} (hl : l ∈ c') :
    l ∈ c ∧ ρ l.1 = none := by
  induction c generalizing c' with
  | nil =>
    simp only [substClause.go, Option.some.injEq] at h
    subst h; simp at hl
  | cons l₀ ls ih =>
    rcases substClause_go_cons_cases h with ⟨_, _, hls⟩ | ⟨hρ, _, ⟨_, hls⟩ | ⟨c'', hgo, _, rfl⟩⟩
    · exact ⟨List.mem_cons_of_mem _ (ih hls hl).1, (ih hls hl).2⟩
    · exact ⟨List.mem_cons_of_mem _ (ih hls hl).1, (ih hls hl).2⟩
    · rcases List.mem_cons.mp hl with rfl | hl'
      · exact ⟨List.mem_cons_self, hρ⟩
      · exact ⟨List.mem_cons_of_mem _ (ih hgo hl').1, (ih hgo hl').2⟩

private theorem substClause_go_length_le {K : ℕ} (ρ : Fin K → Option Bool) (c : Clause (Fin K))
    {c' : Clause (Fin K)} (h : substClause.go ρ c = some c') : c'.length ≤ c.length := by
  induction c generalizing c' with
  | nil => simp only [substClause.go, Option.some.injEq] at h; subst h; simp
  | cons l₀ ls ih =>
    rcases substClause_go_cons_cases h with ⟨_, _, hls⟩ | ⟨_, _, ⟨_, hls⟩ | ⟨_, hgo, _, rfl⟩⟩
    · exact (ih hls).trans (Nat.le_succ _)
    · exact (ih hls).trans (Nat.le_succ _)
    · exact Nat.succ_le_succ (ih hgo)

private theorem substClause_go_length_lt_of_true {K : ℕ} (ρ : Fin K → Option Bool)
    (c : Clause (Fin K)) {c' : Clause (Fin K)} (h : substClause.go ρ c = some c')
    {l : Literal (Fin K)} (hl : l ∈ c) (hρ : ∃ b, ρ l.1 = some b) :
    c'.length < c.length := by
  induction c generalizing c' with
  | nil => simp at hl
  | cons l₀ ls ih =>
    rcases List.mem_cons.mp hl with rfl | hl'
    · obtain ⟨b, hb⟩ := hρ
      unfold substClause.go at h
      rw [hb] at h; dsimp only at h
      split_ifs at h with hbl
      exact Nat.lt_succ_of_le (substClause_go_length_le ρ ls h)
    · rcases substClause_go_cons_cases h with ⟨_, _, hls⟩ | ⟨_, _, ⟨_, hls⟩ | ⟨_, hgo, _, rfl⟩⟩
      · exact (ih hls hl').trans (Nat.lt_succ_self _)
      · exact (ih hls hl').trans (Nat.lt_succ_self _)
      · exact Nat.succ_lt_succ (ih hgo hl')

private theorem substClause_go_no_contra {K : ℕ} (ρ : Fin K → Option Bool) (c : Clause (Fin K))
    {c' : Clause (Fin K)} (h : substClause.go ρ c = some c') {l : Literal (Fin K)} (hl : l ∈ c') :
    (l.1, !l.2) ∉ c' := by
  induction c generalizing c' with
  | nil =>
    simp only [substClause.go, Option.some.injEq] at h
    subst h; simp at hl
  | cons l₀ ls ih =>
    rcases substClause_go_cons_cases h with ⟨_, _, hls⟩ | ⟨_, hneg, ⟨_, hls⟩ | ⟨c'', hgo, _, rfl⟩⟩
    · exact ih hls hl
    · exact ih hls hl
    · intro hcontra
      rcases List.mem_cons.mp hl with rfl | hl'
      · rcases List.mem_cons.mp hcontra with hc0 | hc'
        · have h2 : (!l.2) = l.2 := (Prod.mk.inj hc0).2
          cases hl2 : l.2 <;> simp [hl2] at h2
        · exact hneg (substClause_go_mem_none ρ ls hgo hc').1
      · rcases List.mem_cons.mp hcontra with hc0 | hc'
        · have h1 : l.1 = l₀.1 := (Prod.mk.inj hc0).1
          have h2 : (!l.2) = l₀.2 := (Prod.mk.inj hc0).2
          have heq : (l₀.1, !l₀.2) = l := Prod.ext h1.symm (by rw [← h2]; simp)
          exact hneg (heq ▸ (substClause_go_mem_none ρ ls hgo hl').1)
        · exact ih hgo hl' hc'

private theorem substClause_go_nodup {K : ℕ} (ρ : Fin K → Option Bool) (c : Clause (Fin K))
    {c' : Clause (Fin K)} (h : substClause.go ρ c = some c') : c'.Nodup := by
  induction c generalizing c' with
  | nil =>
    simp only [substClause.go, Option.some.injEq] at h
    subst h; exact List.nodup_nil
  | cons l₀ ls ih =>
    rcases substClause_go_cons_cases h with ⟨_, _, hls⟩ | ⟨_, _, ⟨_, hls⟩ | ⟨_, hgo, hm, rfl⟩⟩
    · exact ih hls
    · exact ih hls
    · exact List.nodup_cons.mpr ⟨hm, ih hgo⟩

private theorem substClause_go_eq_none_of_mem_true {K : ℕ} (ρ : Fin K → Option Bool)
    (c : Clause (Fin K)) {l : Literal (Fin K)} (hl : l ∈ c) {b : Bool}
    (hρ : ρ l.1 = some b) (hb : (b == l.2) = true) :
    substClause.go ρ c = none := by
  induction c with
  | nil => simp at hl
  | cons l₀ ls ih =>
    unfold substClause.go
    rcases List.mem_cons.mp hl with rfl | hl'
    · rw [hρ]; dsimp only; simp only [hb, ↓reduceIte]
    · cases hρ₀ : ρ l₀.1 with
      | some b₀ =>
        dsimp only
        split_ifs with hb₀
        · rfl
        · exact ih hl'
      | none =>
        dsimp only
        split_ifs with hneg
        · rfl
        · rw [ih hl']

private theorem substClause_go_none_of_ext {K : ℕ} {ρ ρ' : Fin K → Option Bool}
    (hext : ∀ i b, ρ i = some b → ρ' i = some b) (c : Clause (Fin K))
    (h : substClause.go ρ c = none) : substClause.go ρ' c = none := by
  induction c with
  | nil => simp [substClause.go] at h
  | cons l₀ ls ih =>
    unfold substClause.go at h ⊢
    cases hρ : ρ l₀.1 with
    | some b =>
      rw [hρ] at h; dsimp only at h
      have hρ' := hext l₀.1 b hρ
      rw [hρ']; dsimp only
      split_ifs at h ⊢ with hb
      · rfl
      · exact ih h
    | none =>
      rw [hρ] at h; dsimp only at h
      split_ifs at h with hneg
      · cases hρ' : ρ' l₀.1 with
        | some b =>
          dsimp only
          split_ifs with hb
          · rfl
          · have hbneg : (b == !l₀.2) = true := by
              cases b <;> cases h2 : l₀.2 <;> simp_all
            exact substClause_go_eq_none_of_mem_true ρ' ls hneg hρ' hbneg
        | none =>
          dsimp only
          simp only [hneg, ↓reduceIte]
      · cases hgo : substClause.go ρ ls with
        | none =>
          have hgo' := ih hgo
          cases hρ' : ρ' l₀.1 with
          | some b =>
            dsimp only
            split_ifs with hb
            · rfl
            · exact hgo'
          | none =>
            dsimp only
            rw [ite_eq_right hneg, hgo']
        | some c'' =>
          rw [hgo] at h; dsimp only at h
          split_ifs at h

private theorem substClause_go_mem_of_ext {K : ℕ} {ρ ρ' : Fin K → Option Bool}
    (hext : ∀ i b, ρ i = some b → ρ' i = some b) (c : Clause (Fin K))
    {cρ c' : Clause (Fin K)} (hρ : substClause.go ρ c = some cρ)
    (hρ' : substClause.go ρ' c = some c') {l : Literal (Fin K)} (hl : l ∈ c') :
    l ∈ cρ := by
  induction c generalizing cρ c' l with
  | nil =>
    simp only [substClause.go, Option.some.injEq] at hρ hρ'
    subst hρ; subst hρ'; exact hl
  | cons l₀ ls ih =>
    unfold substClause.go at hρ hρ'
    cases h0 : ρ l₀.1 with
    | some b =>
      rw [h0] at hρ; dsimp only at hρ
      have h0' := hext l₀.1 b h0
      rw [h0'] at hρ'; dsimp only at hρ'
      split_ifs at hρ hρ' with hb
      exact ih hρ hρ' hl
    | none =>
      rw [h0] at hρ; dsimp only at hρ
      split_ifs at hρ with hneg
      cases hgo : substClause.go ρ ls with
      | none => rw [hgo] at hρ; dsimp only at hρ; simp at hρ
      | some cρ'' =>
        rw [hgo] at hρ; dsimp only at hρ
        have hmem_of_go : ∀ {c''}, substClause.go ρ' ls = some c'' →
            ∀ x ∈ c'', x ∈ cρ := by
          intro c'' hgo' x hx
          have hx'' := ih hgo hgo' hx
          split_ifs at hρ with hm
          · cases hρ; exact hx''
          · cases hρ; exact List.mem_cons_of_mem _ hx''
        have hl0_mem : l₀ ∈ cρ := by
          split_ifs at hρ with hm
          · cases hρ; exact hm
          · cases hρ; exact List.mem_cons_self
        cases h0' : ρ' l₀.1 with
        | some b =>
          rw [h0'] at hρ'; dsimp only at hρ'
          split_ifs at hρ' with hb
          exact hmem_of_go hρ' l hl
        | none =>
          rw [h0'] at hρ'; dsimp only at hρ'
          split_ifs at hρ'
          cases hgo' : substClause.go ρ' ls with
          | none => rw [hgo'] at hρ'; dsimp only at hρ'; simp at hρ'
          | some c'' =>
            rw [hgo'] at hρ'; dsimp only at hρ'
            split_ifs at hρ' with hm'
            · cases hρ'; exact hmem_of_go hgo' l hl
            · cases hρ'
              rcases List.mem_cons.mp hl with rfl | hl'
              · exact hl0_mem
              · exact hmem_of_go hgo' l hl'

private theorem substClause_go_length_lt_of_ext {K : ℕ} {ρ ρ' : Fin K → Option Bool}
    (hext : ∀ i b, ρ i = some b → ρ' i = some b) (c : Clause (Fin K))
    {cρ c' : Clause (Fin K)} (hρ : substClause.go ρ c = some cρ)
    (hρ' : substClause.go ρ' c = some c')
    {l₀ : Literal (Fin K)} (hl₀ : l₀ ∈ cρ) (hset : (ρ' l₀.1).isSome) :
    c'.length < cρ.length := by
  have hsub : c'.toFinset ⊂ cρ.toFinset := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun x hx => List.mem_toFinset.mpr
      (substClause_go_mem_of_ext hext c hρ hρ' (List.mem_toFinset.mp hx)), fun heq => ?_⟩
    have hl0_in : l₀ ∈ c' := List.mem_toFinset.mp (heq ▸ List.mem_toFinset.mpr hl₀)
    have hnone := (substClause_go_mem_none ρ' c hρ' hl0_in).2
    rw [hnone] at hset
    simp at hset
  have hcard := Finset.card_lt_card hsub
  rw [List.toFinset_card_of_nodup (substClause_go_nodup ρ' c hρ'),
    List.toFinset_card_of_nodup (substClause_go_nodup ρ c hρ)] at hcard
  exact hcard

theorem cnfWidth_substCNF_le {K : ℕ} (ρ : Fin K → Option Bool) (H : CNF (Fin K)) :
    cnfWidth (substCNF ρ H) ≤ cnfWidth H := by
  rw [cnfWidth_le_iff]
  intro c' hc'
  simp only [substCNF, List.mem_filterMap] at hc'
  obtain ⟨c, hc, hsub⟩ := hc'
  exact (substClause_go_length_le ρ c hsub).trans (length_le_cnfWidth hc)

/-- A partial assignment `τ : Fin K → Option Bool` (supported on unqueried variables) **forces**
`H` to `true` if every completion agreeing with `τ` satisfies `H`. -/
private def ForcesTrue {K : ℕ} (H : CNF (Fin K)) (τ : Fin K → Option Bool) : Prop :=
  ∀ z : Fin K → Bool, (∀ i b, τ i = some b → z i = b) → H.eval z = true

/-- Support size of a partial assignment `τ : Fin K → Option Bool`. -/
private def supportCard {K : ℕ} (τ : Fin K → Option Bool) : ℕ :=
  #{i : Fin K | (τ i).isSome}

private def queryList {K : ℕ} : List (Fin K) → (Fin K → Option Bool) →
    ((Fin K → Option Bool) → DecisionTree (Fin K) Bool) → DecisionTree (Fin K) Bool
  | [], ρ, k => k ρ
  | i :: is, ρ, k =>
    DecisionTree.node i
      (queryList is (Function.update ρ i (some false)) k)
      (queryList is (Function.update ρ i (some true)) k)

private theorem eval_queryList {K : ℕ} (l : List (Fin K)) (ρ : Fin K → Option Bool)
    (k : (Fin K → Option Bool) → DecisionTree (Fin K) Bool) (z : Fin K → Bool) :
    (queryList l ρ k).eval z =
      (k (fun i => if i ∈ l then some (z i) else ρ i)).eval z := by
  induction l generalizing ρ with
  | nil => simp [queryList]
  | cons j js ih =>
    simp only [queryList, DecisionTree.eval_node]
    cases hzj : z j
    · simp only [Bool.cond_false, ih]
      congr 2; funext i
      by_cases hi : i ∈ js
      · simp [hi]
      · by_cases hij : i = j
        · subst hij; simp [hzj]
        · simp [hi, hij]
    · simp only [Bool.cond_true, ih]
      congr 2; funext i
      by_cases hi : i ∈ js
      · simp [hi]
      · by_cases hij : i = j
        · subst hij; simp [hzj]
        · simp [hi, hij]

private theorem depth_queryList_le {K : ℕ} (l : List (Fin K)) (ρ : Fin K → Option Bool)
    (k : (Fin K → Option Bool) → DecisionTree (Fin K) Bool) {d : ℕ}
    (hk : ∀ ρ', (k ρ').depth ≤ d) :
    (queryList l ρ k).depth ≤ l.length + d := by
  induction l generalizing ρ with
  | nil => simpa [queryList] using hk ρ
  | cons j js ih =>
    simp only [queryList, DecisionTree.depth_node, List.length_cons]
    have h0 := ih (Function.update ρ j (some false))
    have h1 := ih (Function.update ρ j (some true))
    omega

/-- **Truncated certificate-to-decision-tree theorem**: for every CNF `H` of width at most `W` on
`Fin K → Bool` and every `q ≥ 1`, there exists a deterministic decision tree `T` of depth at most
`W * q` such that `T ≤ H` pointwise and `T z = true` whenever `H z = true` and
`certOneAt H.eval z ≤ q`. -/
theorem exists_truncated_decisionTree {K W q : ℕ} (H : CNF (Fin K)) (hW : cnfWidth H ≤ W)
    (_hq : 1 ≤ q) :
    ∃ T : DecisionTree (Fin K) Bool,
      T.depth ≤ W * q ∧
      (∀ z, T.eval z = true → H.eval z = true) ∧
      (∀ z, H.eval z = true → certOneAt H.eval z ≤ q → T.eval z = true) := by
  classical
  have hbuild : ∀ (w : ℕ) (ρ : Fin K → Option Bool), cnfWidth (substCNF ρ H) ≤ w →
      ∃ T : DecisionTree (Fin K) Bool,
        T.depth ≤ w * q ∧
        (∀ z, (∀ i b, ρ i = some b → z i = b) → T.eval z = true → H.eval z = true) ∧
        (∀ z, (∀ i b, ρ i = some b → z i = b) → H.eval z = true →
          certOneAt H.eval z ≤ q → T.eval z = true) := by
    intro w
    induction w with
    | zero =>
      intro ρ hw
      by_cases hnil : [] ∈ substCNF ρ H
      · refine ⟨DecisionTree.leaf false, by simp, fun z _ h => by simp at h,
          fun z hagree hz _ => ?_⟩
        rw [← eval_substCNF ρ H z hagree, CNF.eval_eq_true_iff] at hz
        have := hz [] hnil
        simp at this
      · refine ⟨DecisionTree.leaf true, by simp, fun z hagree _ => ?_, fun _ _ _ _ => rfl⟩
        rw [← eval_substCNF ρ H z hagree, CNF.eval_eq_true_iff]
        intro c hc
        have hlen : c.length = 0 := Nat.eq_zero_of_le_zero ((length_le_cnfWidth hc).trans hw)
        exact absurd (List.eq_nil_of_length_eq_zero hlen ▸ hc) hnil
    | succ w ih =>
      intro ρ hw
      set Hρ := substCNF ρ H
      by_cases hconst1 : ∀ z, (∀ i b, ρ i = some b → z i = b) → H.eval z = true
      · exact ⟨DecisionTree.leaf true, by simp, fun z hagree _ => hconst1 z hagree,
          fun _ _ _ _ => rfl⟩
      · by_cases hforce : ∃ τ : Fin K → Option Bool,
            supportCard τ ≤ q ∧ (∀ i, (τ i).isSome → ρ i = none) ∧ ForcesTrue Hρ τ
        · choose τ hτcard hτdisj hτforce using hforce
          let vars : List (Fin K) := (Finset.univ.filter fun i : Fin K => (τ i).isSome).toList
          have hvars_len : vars.length ≤ q := by
            simpa [vars, supportCard] using hτcard
          have hvars_mem : ∀ i, i ∈ vars ↔ (τ i).isSome := fun i => by simp [vars]
          have hbranch : ∀ ρ' : Fin K → Option Bool,
              (∀ i ∈ vars, (ρ' i).isSome) → (∀ i, i ∉ vars → ρ' i = ρ i) →
              ∃ T' : DecisionTree (Fin K) Bool,
                T'.depth ≤ w * q ∧
                (∀ z, (∀ i b, ρ' i = some b → z i = b) → T'.eval z = true → H.eval z = true) ∧
                (∀ z, (∀ i b, ρ' i = some b → z i = b) → H.eval z = true →
                  certOneAt H.eval z ≤ q → T'.eval z = true) := by
            intro ρ' hρ'vars hρ'off
            have hρext : ∀ i b, ρ i = some b → ρ' i = some b := by
              intro i b hρi
              have hni : i ∉ vars := by
                rw [hvars_mem]; intro hsome
                rw [hτdisj i hsome] at hρi; simp at hρi
              exact (hρ'off i hni).trans hρi
            by_cases hmatch : ∀ i b, τ i = some b → ρ' i = some b
            · refine ⟨DecisionTree.leaf true, by simp, fun z hagree _ => ?_, fun _ _ _ _ => rfl⟩
              have hagreeρ : ∀ i b, ρ i = some b → z i = b := fun i b h =>
                hagree i b (hρext i b h)
              have hagreeτ : ∀ i b, τ i = some b → z i = b := fun i b h =>
                hagree i b (hmatch i b h)
              rw [← eval_substCNF ρ H z hagreeρ]
              exact hτforce z hagreeτ
            · have hdrop : cnfWidth (substCNF ρ' H) ≤ w := by
                rw [cnfWidth_le_iff]
                intro c' hc'
                simp only [substCNF, List.mem_filterMap] at hc'
                obtain ⟨c, hc, hsub'⟩ := hc'
                cases hsubρ : substClause ρ c with
                | none =>
                  exfalso
                  have hnone' := substClause_go_none_of_ext hρext c hsubρ
                  change substClause.go ρ' c = some c' at hsub'
                  rw [hnone'] at hsub'; simp at hsub'
                | some cρ =>
                  have hcρ_mem : cρ ∈ Hρ := List.mem_filterMap.mpr ⟨c, hc, hsubρ⟩
                  have hcρ_len : cρ.length ≤ w + 1 := (length_le_cnfWidth hcρ_mem).trans hw
                  -- Show `cρ` contains a literal whose variable is in `vars`
                  have hex_lit : ∃ l ∈ cρ, (τ l.1).isSome := by
                    by_contra hno
                    push Not at hno
                    have hnone_τ : ∀ l ∈ cρ, τ l.1 = none := fun l hl =>
                      Option.not_isSome_iff_eq_none.mp (hno l hl)
                    let z₀ : Fin K → Bool := fun i =>
                      match τ i with
                      | some b => b
                      | none => if (i, false) ∈ cρ then true else false
                    have hagreeτ : ∀ i b, τ i = some b → z₀ i = b := fun i b h => by
                      simp [z₀, h]
                    have htrue : Hρ.eval z₀ = true := hτforce z₀ hagreeτ
                    rw [CNF.eval_eq_true_iff] at htrue
                    have hcρ_true := htrue cρ hcρ_mem
                    rw [Clause.eval_eq_true_iff] at hcρ_true
                    obtain ⟨l, hl, hzl⟩ := hcρ_true
                    have hτl := hnone_τ l hl
                    simp only [z₀, hτl] at hzl
                    cases hl2 : l.2
                    · rw [hl2] at hzl
                      have hmemf : (l.1, false) ∈ cρ := hl2 ▸ hl
                      simp [hmemf] at hzl
                    · rw [hl2] at hzl
                      have hnof : (l.1, false) ∉ cρ := by
                        have hcontra := substClause_go_no_contra ρ c hsubρ hl
                        simpa [hl2] using hcontra
                      simp [hnof] at hzl
                  obtain ⟨l₀, hl₀, hτl₀⟩ := hex_lit
                  have hlt := substClause_go_length_lt_of_ext hρext c hsubρ hsub' hl₀
                    (hρ'vars l₀.1 ((hvars_mem l₀.1).mpr hτl₀))
                  omega
              exact ih ρ' hdrop
          let k : (Fin K → Option Bool) → DecisionTree (Fin K) Bool := fun ρ' =>
            if h : (∀ i ∈ vars, (ρ' i).isSome) ∧ (∀ i, i ∉ vars → ρ' i = ρ i) then
              (hbranch ρ' h.1 h.2).choose
            else
              DecisionTree.leaf false
          refine ⟨queryList vars ρ k, ?_, ?_, ?_⟩
          · have hqd := depth_queryList_le vars ρ k (d := w * q) fun ρ' => by
              simp only [k]
              split_ifs with h
              · exact (hbranch ρ' h.1 h.2).choose_spec.1
              · simp
            have hmul : (w + 1) * q = q + w * q := by ring
            omega
          · intro z hagree heval
            rw [eval_queryList] at heval
            set ρ' : Fin K → Option Bool := fun i => if i ∈ vars then some (z i) else ρ i
            have hcond : (∀ i ∈ vars, (ρ' i).isSome) ∧ (∀ i, i ∉ vars → ρ' i = ρ i) :=
              ⟨fun i hi => by simp [ρ', hi], fun i hi => by simp [ρ', hi]⟩
            have hagree' : ∀ i b, ρ' i = some b → z i = b := by
              intro i b hi
              by_cases hiv : i ∈ vars
              · simp only [ρ', hiv, ↓reduceIte, Option.some.injEq] at hi; exact hi
              · simp only [ρ', hiv, ↓reduceIte] at hi; exact hagree i b hi
            dsimp only [k] at heval
            rw [dite_eq_left hcond] at heval
            exact (hbranch ρ' hcond.1 hcond.2).choose_spec.2.1 z hagree' heval
          · intro z hagree hz hcert
            rw [eval_queryList]
            set ρ' : Fin K → Option Bool := fun i => if i ∈ vars then some (z i) else ρ i
            have hcond : (∀ i ∈ vars, (ρ' i).isSome) ∧ (∀ i, i ∉ vars → ρ' i = ρ i) :=
              ⟨fun i hi => by simp [ρ', hi], fun i hi => by simp [ρ', hi]⟩
            have hagree' : ∀ i b, ρ' i = some b → z i = b := by
              intro i b hi
              by_cases hiv : i ∈ vars
              · simp only [ρ', hiv, ↓reduceIte, Option.some.injEq] at hi; exact hi
              · simp only [ρ', hiv, ↓reduceIte] at hi; exact hagree i b hi
            dsimp only [k]
            rw [dite_eq_left hcond]
            exact (hbranch ρ' hcond.1 hcond.2).choose_spec.2.2 z hagree' hz hcert
        · refine ⟨DecisionTree.leaf false, by simp, fun _ _ h => by simp at h,
            fun z hagree hz hcert => ?_⟩
          exfalso
          obtain ⟨S, hS, hScard⟩ := (certOneAt_le_iff hz).mp hcert
          let τ : Fin K → Option Bool := fun i =>
            if i ∈ S ∧ ρ i = none then some (z i) else none
          apply hforce
          refine ⟨τ, ?_, ?_, ?_⟩
          · refine (Finset.card_le_card ?_).trans hScard
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, τ] at hi
            split_ifs at hi with h
            · exact h.1
            · simp at hi
          · intro i hi
            simp only [τ] at hi
            split_ifs at hi with h
            · exact h.2
            · simp at hi
          · intro z' hz'
            let z'' : Fin K → Bool := fun i =>
              match ρ i with
              | some b => b
              | none => z' i
            have hagree'' : ∀ i b, ρ i = some b → z'' i = b := fun i b hi => by
              simp [z'', hi]
            have hHρ_eq : Hρ.eval z' = Hρ.eval z'' := by
              have hcl : ∀ c ∈ Hρ, Clause.eval z' c = Clause.eval z'' c := by
                intro c hc
                simp only [Hρ, substCNF, List.mem_filterMap] at hc
                obtain ⟨c₀, _, hsub⟩ := hc
                have hlit : ∀ l ∈ c, Literal.eval z' l = Literal.eval z'' l := by
                  intro l hl
                  have hnone := (substClause_go_mem_none ρ c₀ hsub hl).2
                  simp only [Literal.eval, z'', hnone]
                have hcl_eq : ∀ (cl : Clause (Fin K)),
                    (∀ l ∈ cl, Literal.eval z' l = Literal.eval z'' l) →
                    Clause.eval z' cl = Clause.eval z'' cl := by
                  intro cl hcl'
                  induction cl with
                  | nil => rfl
                  | cons l ls ihc =>
                    rw [Clause.eval_cons, Clause.eval_cons, hcl' l List.mem_cons_self,
                      ihc fun l' hl' => hcl' l' (List.mem_cons_of_mem _ hl')]
                exact hcl_eq c hlit
              rw [Bool.eq_iff_iff, CNF.eval_eq_true_iff, CNF.eval_eq_true_iff]
              exact ⟨fun h c hc => hcl c hc ▸ h c hc, fun h c hc => (hcl c hc).symm ▸ h c hc⟩
            rw [hHρ_eq, eval_substCNF ρ H z'' hagree'']
            apply hS.2
            intro i hi
            cases hρi : ρ i with
            | some b =>
              simp only [z'', hρi]
              exact (hagree i b hρi).symm
            | none =>
              simp only [z'', hρi]
              exact hz' i (z i) (by simp [τ, hi, hρi])
  obtain ⟨T, hT1, hT2, hT3⟩ := hbuild W (fun _ => none) ((cnfWidth_substCNF_le _ H).trans hW)
  exact ⟨T, hT1, fun z => hT2 z (by simp), fun z => hT3 z (by simp)⟩

/-- Converting a truncated decision tree into a DNF of at most `2 ^ (W * q)` terms of width at most
`W * q` satisfying the same lower-approximation and certificate-completeness properties. -/
theorem exists_truncated_dnf {K W q : ℕ} (H : CNF (Fin K)) (hW : cnfWidth H ≤ W) (hq : 1 ≤ q) :
    ∃ Φ : DNF (Fin K),
      Φ.length ≤ 2 ^ (W * q) ∧
      dnfWidth Φ ≤ W * q ∧
      (∀ z, Φ.eval z = true → H.eval z = true) ∧
      (∀ z, H.eval z = true → certOneAt H.eval z ≤ q → Φ.eval z = true) := by
  obtain ⟨T, hdepth, hsound, hcomp⟩ := exists_truncated_decisionTree H hW hq
  refine ⟨T.toDNF, ?_, ?_, ?_, ?_⟩
  · have hlen : ∀ (t : DecisionTree (Fin K) Bool) (p : Term (Fin K)),
        (DecisionTree.toDNFAux t p).length ≤ 2 ^ t.depth := by
      intro t
      induction t with
      | leaf b =>
        intro p
        cases b <;> simp [DecisionTree.toDNFAux]
      | node i lo hi ihlo ihhi =>
        intro p
        simp only [DecisionTree.toDNFAux, DecisionTree.depth_node]
        cases p.lookup i with
        | some b =>
          cases b
          · exact (ihlo p).trans (Nat.pow_le_pow_right (by norm_num)
              (Nat.le_succ_of_le (le_max_left _ _)))
          · exact (ihhi p).trans (Nat.pow_le_pow_right (by norm_num)
              (Nat.le_succ_of_le (le_max_right _ _)))
        | none =>
          rw [List.length_append, Nat.pow_succ]
          have h1 : 2 ^ lo.depth ≤ 2 ^ max lo.depth hi.depth :=
            Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
          have h2 : 2 ^ hi.depth ≤ 2 ^ max lo.depth hi.depth :=
            Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
          have hlo := ihlo ((i, false) :: p)
          have hhi := ihhi ((i, true) :: p)
          omega
    exact (hlen T []).trans (Nat.pow_le_pow_right (by norm_num) hdepth)
  · rw [dnfWidth_le_iff]
    intro t ht
    exact (DecisionTree.length_le_depth_of_mem_toDNF ht).trans hdepth
  · intro z hz
    rw [DecisionTree.eval_toDNF] at hz
    exact hsound z hz
  · intro z hz hc
    rw [DecisionTree.eval_toDNF]
    exact hcomp z hz hc

end BooleanFunction

end CslibFrontier
