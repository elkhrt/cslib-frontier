/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Equality
public import CslibFrontier.Computability.Communication.Functions
public import CslibFrontier.Computability.Communication.Newman
public import CslibFrontier.Computability.Communication.Randomized
import CslibFrontier.Computability.Communication.Rectangle
import Cslib.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Log
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tight `Θ(log n)` Private-Coin Randomized Communication Complexity of Equality

Proves both the `O(log n)` upper bound (via a 3-bit `1/4`-error public-coin parity-check protocol
and Newman's theorem) and the `Ω(log n)` lower bound (via a leaf-probability quantization argument)
for the private-coin randomized communication complexity of `n`-bit equality.

## Main results

* `Cslib.Communication.PublicCoin.ecomplexityFun_equality_le_three`:
  3-bit public-coin protocol for `n`-bit equality with error `≤ 1/4`.
* `Cslib.Communication.PrivateCoin.ecomplexityFun_equality_upper`:
  `R^{cc}_{1/3}(EQ_n) ≤ 3 + ⌈log₂ ⌈144 n⌉⌉`.
* `Cslib.Communication.PrivateCoin.ecomplexityFun_equality_lower`:
  `⌈log₂ n⌉ ≤ 2 * R^{cc}_{1/3}(EQ_n) + 1`.
-/

public section

namespace Cslib.Communication

open Finset

private theorem prob_run_true_eq_sum_leaves {a b : ℕ} {X Y : Type*}
    (P : PrivateCoin a b X Y Bool) (x : X) (y : Y) :
    (((Cslib.Probability.PMF.uniformOfFintype (BitString a × BitString b)).map
      (fun r => P.run (x, r.1) (y, r.2))).toOuterMeasure {z | z = true}).toReal =
      ∑ i : Fin P.leafCount with P.leafOutput i = true,
        (((Cslib.Probability.PMF.uniformOfFintype (BitString a)).toOuterMeasure
            {rA | (x, rA) ∈ P.leafAlice i}).toReal *
         ((Cslib.Probability.PMF.uniformOfFintype (BitString b)).toOuterMeasure
            {rB | (y, rB) ∈ P.leafBob i}).toReal) := by
  classical
  have hprod : (Cslib.Probability.PMF.uniformOfFintype (BitString a)).bind
      (fun rA => (Cslib.Probability.PMF.uniformOfFintype (BitString b)).map
        fun rB => (rA, rB)) =
      Cslib.Probability.PMF.uniformOfFintype (BitString a × BitString b) := by
    ext ⟨rA, rB⟩
    simp only [PMF.bind_apply, PMF.map_apply, Cslib.Probability.PMF.uniformOfFintype_apply,
      Fintype.card_prod]
    rw [tsum_eq_single rA, tsum_eq_single rB]
    · simp [ENNReal.mul_inv]
    · intro rB' hrB'; simp [hrB'.symm]
    · intro rA' hrA'
      simp [hrA'.symm]
  set μA := Cslib.Probability.PMF.uniformOfFintype (BitString a)
  set μB := Cslib.Probability.PMF.uniformOfFintype (BitString b)
  set ν := μA.bind fun rA => μB.map fun rB => P.run (x, rA) (y, rB)
  have hν_eq : ((Cslib.Probability.PMF.uniformOfFintype (BitString a × BitString b)).map
      (fun r => P.run (x, r.1) (y, r.2))) = ν := by
    rw [← hprod, PMF.map_bind]
    congr 1; funext rA; rw [PMF.map_comp]; rfl
  rw [hν_eq, Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
  have hν : ∀ z : Bool, (ν z).toReal =
      ∑ rA : BitString a, ∑ rB : BitString b, (μA rA).toReal * (μB rB).toReal *
        if P.run (x, rA) (y, rB) = z then 1 else 0 := by
    intro z
    simp only [ν, PMF.bind_apply, PMF.map_apply]
    rw [tsum_fintype, ENNReal.toReal_sum (fun rA _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (by
        rw [tsum_fintype]
        exact ENNReal.sum_ne_top.mpr fun rB _ => by split_ifs <;> simp [PMF.apply_ne_top]))]
    refine Finset.sum_congr rfl fun rA _ => ?_
    rw [ENNReal.toReal_mul, tsum_fintype, ENNReal.toReal_sum (fun rB _ => by
      split_ifs <;> simp [PMF.apply_ne_top]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun rB _ => ?_
    split_ifs with h1 h2 <;> simp_all [mul_comm]
  trans (ν true).toReal
  · simp
  rw [hν true]
  have hpart : ∀ (rA : BitString a) (rB : BitString b),
      ((if P.run (x, rA) (y, rB) = true then (1 : ℝ) else 0) : ℝ) =
        ∑ i : Fin P.leafCount with P.leafOutput i = true,
          (if (x, rA) ∈ P.leafAlice i then (1 : ℝ) else 0) *
          (if (y, rB) ∈ P.leafBob i then (1 : ℝ) else 0) := by
    intro rA rB
    rw [P.run_eq_leafOutput_leaf]
    have huniq : ∀ i : Fin P.leafCount,
        ((if (x, rA) ∈ P.leafAlice i then (1 : ℝ) else 0) *
         (if (y, rB) ∈ P.leafBob i then (1 : ℝ) else 0)) =
        if P.leaf (x, rA) (y, rB) = i then 1 else 0 := by
      intro i; simp only [P.leaf_eq_iff]; split_ifs <;> simp_all
    simp_rw [huniq]
    by_cases hout : P.leafOutput (P.leaf (x, rA) (y, rB)) = true
    · simp only [hout, ↓reduceIte]
      rw [Finset.sum_eq_single (P.leaf (x, rA) (y, rB))]
      · simp
      · intro i _ hi; simp [hi.symm]
      · intro hnot
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ (P.leaf (x, rA) (y, rB)), hout⟩) hnot
    · simp only [hout]
      symm
      refine Finset.sum_eq_zero fun i hi => ?_
      have hne : P.leaf (x, rA) (y, rB) ≠ i := fun heq => hout (heq ▸ (Finset.mem_filter.mp hi).2)
      simp [hne]
  calc ∑ rA : BitString a, ∑ rB : BitString b, (μA rA).toReal * (μB rB).toReal *
        (if P.run (x, rA) (y, rB) = true then 1 else 0)
      = ∑ rA : BitString a, ∑ rB : BitString b, ∑ i : Fin P.leafCount with P.leafOutput i = true,
          ((μA rA).toReal * (if (x, rA) ∈ P.leafAlice i then 1 else 0)) *
          ((μB rB).toReal * (if (y, rB) ∈ P.leafBob i then 1 else 0)) := by
        refine Finset.sum_congr rfl fun rA _ => Finset.sum_congr rfl fun rB _ => ?_
        rw [hpart rA rB, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i : Fin P.leafCount with P.leafOutput i = true,
          (∑ rA : BitString a, (μA rA).toReal * (if (x, rA) ∈ P.leafAlice i then 1 else 0)) *
          (∑ rB : BitString b, (μB rB).toReal * (if (y, rB) ∈ P.leafBob i then 1 else 0)) := by
        trans ∑ rA : BitString a, ∑ i : Fin P.leafCount with P.leafOutput i = true,
            ∑ rB : BitString b, ((μA rA).toReal * (if (x, rA) ∈ P.leafAlice i then 1 else 0)) *
              ((μB rB).toReal * (if (y, rB) ∈ P.leafBob i then 1 else 0))
        · refine Finset.sum_congr rfl fun rA _ => Finset.sum_comm
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun rA _ => ?_; rw [Finset.mul_sum]
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        · rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
          refine Finset.sum_congr rfl fun rA _ => by
            simp only [Set.mem_ofPred_eq]; split_ifs <;> simp
        · rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
          refine Finset.sum_congr rfl fun rB _ => by
            simp only [Set.mem_ofPred_eq]; split_ifs <;> simp

private theorem dotProduct_update_not {n : ℕ} (v r : BitString n) (i₀ : Fin n) :
    v ⬝ᵥ Function.update r i₀ (!r i₀) = (v ⬝ᵥ r) + v i₀ := by
  classical
  simp only [dotProduct]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
    ← Finset.add_sum_erase _ (fun i => v i * r i) (Finset.mem_univ i₀)]
  have hrest : ∑ i ∈ Finset.univ.erase i₀, v i * Function.update r i₀ (!r i₀) i =
      ∑ i ∈ Finset.univ.erase i₀, v i * r i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hrest, Function.update_self]
  cases v i₀ <;> cases r i₀ <;> cases (∑ i ∈ Finset.univ.erase i₀, v i * r i) <;> decide

/-- Public-coin protocol for `n`-bit equality with error at most `1/4` and cost `3` bits. -/
theorem PublicCoin.ecomplexityFun_equality_le_three (n : ℕ) :
    PublicCoin.ecomplexityFun (1 / 4) (equality : BitString n → BitString n → Bool) ≤ 3 := by
  classical
  let detProt (r : BitString n × BitString n) : Protocol (BitString n) (BitString n) Bool :=
    Protocol.alice (fun x => x ⬝ᵥ r.1)
      (Protocol.alice (fun x => x ⬝ᵥ r.2)
        (Protocol.bob (fun y => !(y ⬝ᵥ r.1) && !(y ⬝ᵥ r.2))
          (Protocol.output false) (Protocol.output true))
        (Protocol.bob (fun y => !(y ⬝ᵥ r.1) && (y ⬝ᵥ r.2))
          (Protocol.output false) (Protocol.output true)))
      (Protocol.alice (fun x => x ⬝ᵥ r.2)
        (Protocol.bob (fun y => (y ⬝ᵥ r.1) && !(y ⬝ᵥ r.2))
          (Protocol.output false) (Protocol.output true))
        (Protocol.bob (fun y => (y ⬝ᵥ r.1) && (y ⬝ᵥ r.2))
          (Protocol.output false) (Protocol.output true)))
  have hrun : ∀ r x y, (detProt r).run x y =
      (decide (x ⬝ᵥ r.1 = y ⬝ᵥ r.1) && decide (x ⬝ᵥ r.2 = y ⬝ᵥ r.2)) := by
    intro r x y
    simp only [detProt, Protocol.run_alice, Protocol.run_bob, Protocol.run_output]
    cases x ⬝ᵥ r.1 <;> cases x ⬝ᵥ r.2 <;> cases y ⬝ᵥ r.1 <;> cases y ⬝ᵥ r.2 <;> decide
  let μ : PublicCoin (BitString n) (BitString n) Bool :=
    (Cslib.Probability.PMF.uniformOfFintype (BitString n × BitString n)).map detProt
  refine (PublicCoin.ecomplexity_le_depth (μ := μ) ?_).trans ?_
  · intro x _ y _
    simp only [PublicCoin.errorProb, Cslib.Probability.PMF.errorProb, μ]
    rw [PMF.toOuterMeasure_map_apply, Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
    by_cases hxy : x = y
    · subst hxy
      have h0 : ∀ r : BitString n × BitString n,
          ¬(r ∈ detProt ⁻¹' {p | ¬equality x x = p.run x x}) := by
        intro r hr
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, equality, hrun, decide_true,
          Bool.and_self] at hr
        exact hr trivial
      simp only [h0, ↓reduceIte, Finset.sum_const_zero]
      norm_num
    · obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n, x i₀ ≠ y i₀ := Function.ne_iff.mp hxy
      have hhalf : #{r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} * 2 = 2 ^ n := by
        let flip : BitString n → BitString n := fun r => Function.update r i₀ (!r i₀)
        have hflip_inv : ∀ r, flip (flip r) = r := fun r => by
          ext j; by_cases hj : j = i₀ <;> simp [flip, hj]
        have hflip_xor : ∀ r, (x ⬝ᵥ flip r = y ⬝ᵥ flip r) ↔ ¬(x ⬝ᵥ r = y ⬝ᵥ r) := by
          intro r; rw [dotProduct_update_not, dotProduct_update_not]
          cases x ⬝ᵥ r <;> cases y ⬝ᵥ r <;> cases hx : x i₀ <;> cases hy : y i₀
          all_goals first | (exfalso; exact hi₀ (hx.trans hy.symm)) | decide
        have hbij : #{r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} =
            #{r : BitString n | ¬(x ⬝ᵥ r = y ⬝ᵥ r)} := by
          refine Finset.card_bij (fun r _ => flip r) ?_ ?_ ?_
          · intro r hr
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
            exact fun h => (hflip_xor r).mp h hr
          · intro r₁ _ r₂ _ h; simpa [hflip_inv] using congrArg flip h
          · intro r hr
            refine ⟨flip r, ?_, hflip_inv r⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
            exact (hflip_xor r).mpr hr
        have htot := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (BitString n))) (fun r => x ⬝ᵥ r = y ⬝ᵥ r)
        simp only [Finset.card_univ, BitString.card] at htot; omega
      have hprod : #{q : BitString n × BitString n |
          x ⬝ᵥ q.1 = y ⬝ᵥ q.1 ∧ x ⬝ᵥ q.2 = y ⬝ᵥ q.2} * 4 = (2 ^ n) * (2 ^ n) := by
        have hp : #{q : BitString n × BitString n |
            x ⬝ᵥ q.1 = y ⬝ᵥ q.1 ∧ x ⬝ᵥ q.2 = y ⬝ᵥ q.2} =
            #{r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} * #{r : BitString n | x ⬝ᵥ r = y ⬝ᵥ r} := by
          rw [← Finset.card_product]; congr 1; ext ⟨r₁, r₂⟩; simp
        rw [hp]; nlinarith [hhalf]
      have hsum : ∑ r : BitString n × BitString n,
          (if r ∈ (detProt ⁻¹' {p | ¬equality x y = p.run x y}) then
            ((Cslib.Probability.PMF.uniformOfFintype (BitString n × BitString n)) r).toReal
          else 0) =
          (#{q : BitString n × BitString n |
            x ⬝ᵥ q.1 = y ⬝ᵥ q.1 ∧ x ⬝ᵥ q.2 = y ⬝ᵥ q.2} : ℝ) / ((2 ^ n : ℝ) * (2 ^ n : ℝ)) := by
        have hset : ∀ r : BitString n × BitString n,
            (r ∈ (detProt ⁻¹' {p | ¬equality x y = p.run x y})) ↔
            (x ⬝ᵥ r.1 = y ⬝ᵥ r.1 ∧ x ⬝ᵥ r.2 = y ⬝ᵥ r.2) := by
          intro r
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, equality, hxy, decide_false, hrun]
          cases h1 : decide (x ⬝ᵥ r.1 = y ⬝ᵥ r.1) <;>
            cases h2 : decide (x ⬝ᵥ r.2 = y ⬝ᵥ r.2) <;> simp_all
        simp_rw [hset]
        simp only [Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_prod, BitString.card,
          ENNReal.toReal_inv]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
        congr 1
        rw [ENNReal.toReal_natCast]
        push_cast; ring
      rw [hsum, div_le_iff₀ (by positivity)]
      have hprodR : (#{q : BitString n × BitString n |
          x ⬝ᵥ q.1 = y ⬝ᵥ q.1 ∧ x ⬝ᵥ q.2 = y ⬝ᵥ q.2} : ℝ) * 4 = ((2 ^ n : ℝ) * (2 ^ n : ℝ)) := by
        exact_mod_cast hprod
      linarith
  · rw [PublicCoin.depth_le_iff]
    intro p hp
    simp only [μ, PMF.mem_support_map_iff] at hp
    obtain ⟨r, -, rfl⟩ := hp; simp [detProt]

/-- Private-coin upper bound for `n`-bit equality via Newman's theorem: `O(log n)`. -/
theorem PrivateCoin.ecomplexityFun_equality_upper (n : ℕ) :
    PrivateCoin.ecomplexityFun (1 / 3) (equality : BitString n → BitString n → Bool) ≤
      ((3 + Nat.clog 2 ⌈(n : ℝ) / (1 / 12 : ℝ) ^ 2⌉₊ : ℕ) : ℕ∞) := by
  have hnew := PrivateCoin.ecomplexity_le_add_clog
    (X := BitString n) (Y := BitString n) (R := fun x y z => equality x y = z)
    (A := Set.univ) (B := Set.univ) (n := n)
    (by simp [Nat.card_eq_fintype_card]) (by simp [Nat.card_eq_fintype_card])
    (ε := 1 / 4) (δ := 1 / 12) (by norm_num)
  have h13 : (1 / 4 : ℝ) + 1 / 12 = 1 / 3 := by norm_num
  rw [h13] at hnew
  calc PrivateCoin.ecomplexityFun (1 / 3) (equality : BitString n → BitString n → Bool)
      ≤ PublicCoin.ecomplexityFun (1 / 4) (equality : BitString n → BitString n → Bool) +
          Nat.clog 2 ⌈(n : ℝ) / (1 / 12 : ℝ) ^ 2⌉₊ := hnew
    _ ≤ 3 + Nat.clog 2 ⌈(n : ℝ) / (1 / 12 : ℝ) ^ 2⌉₊ := by
        gcongr; exact PublicCoin.ecomplexityFun_equality_le_three n
    _ = ((3 + Nat.clog 2 ⌈(n : ℝ) / (1 / 12 : ℝ) ^ 2⌉₊ : ℕ) : ℕ∞) := by norm_cast

private theorem privateCoin_equality_depth_lower {a b n : ℕ}
    (P : PrivateCoin a b (BitString n) (BitString n) Bool)
    (hP : P.Solves (1 / 3) (fun x y z => equality x y = z) Set.univ Set.univ) :
    Nat.clog 2 n ≤ 2 * P.depth + 1 := by
  classical
  set L := P.leafCount
  have hLpos : 0 < L := P.leafCount_pos
  set M : ℕ := 3 * L
  have hMpos : 0 < M := by omega
  let α : BitString n → Fin L → ℝ := fun x i =>
    ((Cslib.Probability.PMF.uniformOfFintype (BitString a)).toOuterMeasure
      {rA | (x, rA) ∈ P.leafAlice i}).toReal
  let β : BitString n → Fin L → ℝ := fun y i =>
    ((Cslib.Probability.PMF.uniformOfFintype (BitString b)).toOuterMeasure
      {rB | (y, rB) ∈ P.leafBob i}).toReal
  have ha0 : ∀ x i, 0 ≤ α x i := fun _ _ => ENNReal.toReal_nonneg
  have hb0 : ∀ y i, 0 ≤ β y i := fun _ _ => ENNReal.toReal_nonneg
  have ha1 : ∀ x i, α x i ≤ 1 := fun x i =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by
      simpa using (((Cslib.Probability.PMF.uniformOfFintype (BitString a)).toOuterMeasure.mono
        (Set.subset_univ _)).trans_eq (by
          simp [ENNReal.mul_inv_cancel])))
  have hb1 : ∀ y i, β y i ≤ 1 := fun y i =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by
      simpa using (((Cslib.Probability.PMF.uniformOfFintype (BitString b)).toOuterMeasure.mono
        (Set.subset_univ _)).trans_eq (by
          simp [ENNReal.mul_inv_cancel])))
  let quant : BitString n → Fin L → Fin (M + 1) := fun x i =>
    ⟨⌊(M : ℝ) * α x i⌋₊, by
      have : (M : ℝ) * α x i ≤ M := by nlinarith [ha1 x i]
      have := Nat.floor_le_of_le this; omega⟩
  have hinj : Function.Injective quant := by
    intro x x' hq
    by_contra hne
    have hclose : ∀ i, |α x i - α x' i| < (1 / 3 : ℝ) / L := by
      intro i
      have hki : ⌊(M : ℝ) * α x i⌋₊ = ⌊(M : ℝ) * α x' i⌋₊ := congrArg Fin.val (congrFun hq i)
      have h1 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg M) (ha0 x i))
      have h2 := Nat.lt_floor_add_one ((M : ℝ) * α x i)
      have h3 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg M) (ha0 x' i))
      have h4 := Nat.lt_floor_add_one ((M : ℝ) * α x' i)
      rw [hki] at h1 h2
      have hdiff : |(M : ℝ) * α x i - (M : ℝ) * α x' i| < 1 := by
        rw [abs_lt]; constructor <;> linarith
      rw [← mul_sub, abs_mul, abs_of_pos (Nat.cast_pos.mpr hMpos)] at hdiff
      have hMposR : (0 : ℝ) < M := Nat.cast_pos.mpr hMpos
      have hlt : |α x i - α x' i| < (M : ℝ)⁻¹ := by
        rw [inv_eq_one_div]; exact (lt_div_iff₀' hMposR).mpr hdiff
      have heq : (M : ℝ)⁻¹ = (1 / 3 : ℝ) / L := by push_cast [M]; field_simp
      rwa [heq] at hlt
    have hdiag : (2 / 3 : ℝ) ≤ ∑ i : Fin L with P.leafOutput i = true, α x i * β x i := by
      have h1 := hP x (Set.mem_univ _) x (Set.mem_univ _)
      rw [← prob_run_true_eq_sum_leaves P x x]
      set ν := (Cslib.Probability.PMF.uniformOfFintype (BitString a × BitString b)).map
        (fun r => P.run (x, r.1) (x, r.2))
      have hcomp : (ν.toOuterMeasure {z | z = true}).toReal =
          1 - P.errorProb (fun u v z => equality u v = z) x x := by
        have herr : P.errorProb (fun u v z => equality u v = z) x x =
            (ν.toOuterMeasure {z | ¬equality x x = z}).toReal := by
          simp only [PrivateCoin.errorProb, ν, PMF.toOuterMeasure_map_apply]
          rfl
        rw [herr, Cslib.Probability.PMF.toOuterMeasure_apply_toReal,
          Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
        have htot := Cslib.Probability.PMF.sum_toReal ν
        simp only [Fintype.sum_bool, equality, decide_true] at htot ⊢
        simp; linarith
      rw [hcomp]; linarith
    have hoff : ∑ i : Fin L with P.leafOutput i = true, α x' i * β x i ≤ 1 / 3 := by
      have h1 := hP x' (Set.mem_univ _) x (Set.mem_univ _)
      rw [← prob_run_true_eq_sum_leaves P x' x]
      have hcomp : (((Cslib.Probability.PMF.uniformOfFintype (BitString a × BitString b)).map
          (fun r => P.run (x', r.1) (x, r.2))).toOuterMeasure {z | z = true}).toReal =
          P.errorProb (fun u v z => equality u v = z) x' x := by
        simp only [PrivateCoin.errorProb, PMF.toOuterMeasure_map_apply]
        congr 2; ext r
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, equality, Ne.symm hne, decide_false]
        cases P.run (x', r.1) (x, r.2) <;> decide
      rw [hcomp]; exact h1
    have hne_fin : (Finset.univ.filter fun i : Fin L => P.leafOutput i = true).Nonempty := by
      by_contra hem; rw [Finset.not_nonempty_iff_eq_empty] at hem
      rw [hem, Finset.sum_empty] at hdiag; linarith
    have hstrict : ∑ i : Fin L with P.leafOutput i = true, |(α x i - α x' i) * β x i| < 1 / 3 := by
      calc ∑ i : Fin L with P.leafOutput i = true, |(α x i - α x' i) * β x i|
          < ∑ _i : Fin L with P.leafOutput _i = true, ((1 / 3 : ℝ) / L) := by
            refine Finset.sum_lt_sum_of_nonempty hne_fin fun i _ => ?_
            rw [abs_mul, abs_of_nonneg (hb0 x i)]
            exact (mul_le_mul_of_nonneg_left (hb1 x i) (abs_nonneg _)).trans_lt
              (by simpa using hclose i)
        _ ≤ 1 / 3 := by
            rw [Finset.sum_const, nsmul_eq_mul]
            have hcard :
                (#(Finset.univ.filter fun i : Fin L => P.leafOutput i = true) : ℝ) ≤ L := by
              exact_mod_cast (Finset.card_filter_le _ _).trans_eq (by simp [L])
            have hLposR : (0 : ℝ) < L := Nat.cast_pos.mpr hLpos
            calc _ ≤ (L : ℝ) * ((1 / 3 : ℝ) / L) :=
                  mul_le_mul_of_nonneg_right hcard (by positivity)
              _ = 1 / 3 := mul_div_cancel₀ _ hLposR.ne'
    have hsub : ∑ i : Fin L with P.leafOutput i = true, (α x i - α x' i) * β x i =
        (∑ i : Fin L with P.leafOutput i = true, α x i * β x i) -
        (∑ i : Fin L with P.leafOutput i = true, α x' i * β x i) := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => by ring
    linarith [(le_abs_self _).trans_lt ((Finset.abs_sum_le_sum_abs _ _).trans_lt hstrict)]
  have hcard : 2 ^ n ≤ (3 * L + 1) ^ L := by
    have := Fintype.card_le_of_injective quant hinj
    simpa [Fintype.card_fun, Fintype.card_fin, BitString.card, M] using this
  set c := P.depth
  have hL : L ≤ 2 ^ c := P.leafCount_le_two_pow_depth
  have hpow : 2 ^ n ≤ 2 ^ ((c + 2) * 2 ^ c) :=
    calc 2 ^ n ≤ (3 * L + 1) ^ L := hcard
      _ ≤ (4 * 2 ^ c) ^ (2 ^ c) := (Nat.pow_le_pow_left (by omega) L).trans
            (Nat.pow_le_pow_right (by positivity) hL)
      _ = (2 ^ (c + 2)) ^ (2 ^ c) := by
            have : 4 * 2 ^ c = 2 ^ (c + 2) := by rw [pow_add]; ring
            rw [this]
      _ = 2 ^ ((c + 2) * 2 ^ c) := by rw [← pow_mul]
  have hn : n ≤ (c + 2) * 2 ^ c := (Nat.pow_le_pow_iff_right one_lt_two).mp hpow
  have hc2 : c + 2 ≤ 2 * 2 ^ c := by
    induction c with
    | zero => norm_num
    | succ k ih => have := Nat.one_le_two_pow (n := k); rw [pow_succ]; omega
  have hn2 : n ≤ 2 ^ (2 * c + 1) :=
    calc n ≤ (c + 2) * 2 ^ c := hn
      _ ≤ (2 * 2 ^ c) * 2 ^ c := Nat.mul_le_mul_right _ hc2
      _ = 2 ^ c * 2 ^ c * 2 := by ring
      _ = 2 ^ (c + c) * 2 := by rw [← pow_add]
      _ = 2 ^ (2 * c + 1) := by rw [pow_succ, two_mul]
  exact Nat.clog_le_of_le_pow hn2

/-- Private-coin lower bound for `n`-bit equality via leaf-probability quantization: `Ω(log n)`. -/
theorem PrivateCoin.ecomplexityFun_equality_lower (n : ℕ) :
    (Nat.clog 2 n : ℕ∞) ≤
      2 * PrivateCoin.ecomplexityFun (1 / 3) (equality : BitString n → BitString n → Bool) + 1 := by
  generalize hE : PrivateCoin.ecomplexityFun (1 / 3)
      (equality : BitString n → BitString n → Bool) = E
  induction E using ENat.recTopCoe with
  | top =>
    have h2 : (2 : ℕ∞) ≠ 0 := by norm_num
    rw [ENat.mul_top h2, _root_.top_add]
    exact le_top
  | coe d =>
    have hlt : (d : ℕ∞) < ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self d
    rw [← hE] at hlt
    simp only [PrivateCoin.ecomplexityFun, PrivateCoin.ecomplexity, iInf_lt_iff] at hlt
    obtain ⟨a, b, ⟨P, hP⟩, hdP⟩ := hlt
    have hd : P.depth ≤ d := Nat.lt_succ_iff.mp (Nat.cast_lt.mp hdP)
    have hcl : Nat.clog 2 n ≤ 2 * d + 1 := (privateCoin_equality_depth_lower P hP).trans (by omega)
    exact_mod_cast hcl

end Cslib.Communication
