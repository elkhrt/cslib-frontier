module

public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.Schedule
public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.WorstCase
public import CslibFrontier.Computability.Circuit.Boolean.Oracle

import CslibFrontier.Computability.Circuit.Boolean.AtLeast
import CslibFrontier.Computability.Circuit.Boolean.BitBlast
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Circuit.Complexity
import CslibFrontier.Foundations.Data.Nat.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Relativized Worst-Case-to-Average-Case Hardness Amplification for Oracle Circuits

This module relativizes Sudan–Trevisan–Vadhan local list-decoding reconstruction to Boolean
circuits equipped with oracle gates for an arbitrary language `A : Language Bool`
(`oracleInterpretation A`), deriving exponential average-case `A`-oracle circuit hardness from
exponential worst-case `A`-oracle circuit hardness.

## Main definitions

* `CslibFrontier.Computability.Circuit.Boolean.Oracle.oracleCircuitComplexity`: minimum size of
  an `A`-oracle circuit computing `f.slice n`.
* `CslibFrontier.Computability.Circuit.Boolean.Oracle.IsOracleAverageCaseHard`: average-case
  hardness against `A`-oracle circuits of a given size bound.

## Main results

* `isComplete_oracleInterpretation`: completeness of the `A`-oracle circuit basis.
* `oracleComplexity_le_pow_of_agree_hardnessEncode`: relativized Sudan–Trevisan–Vadhan
  reconstruction for `A`-oracle circuits.
* `eventually_isOracleAverageCaseHard_encodedSlice`: exponential worst-case `A`-oracle hardness
  implies exponential average-case `A`-oracle hardness of the hardness-encoded language.
-/

public section

namespace CslibFrontier.Computability.Circuit.Boolean.Oracle

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean Cslib.Code
open Cslib.HardnessEncoding Cslib.LinearAlgebra Filter Finset

/-- The oracle circuit basis is complete since it contains the De Morgan basis via `toOracle`. -/
theorem isComplete_oracleInterpretation (A : Language Bool) :
    (oracleInterpretation A).IsComplete where
  exists_computes_single f := by
    obtain ⟨c, hc⟩ :=
      Interpretation.IsComplete.exists_computes_single (I := Boolean.interpretation) f
    exact ⟨c.mapOp toOracle, fun x => by
      rw [Circuit.eval_mapOp (I := Boolean.interpretation), hc x]⟩

/-- The `A`-oracle circuit complexity `C_f^A(n)` of a Boolean language `f` at length `n`:
minimum size of a circuit over `oracleSignature` with oracle `A` computing `f.slice n`. -/
noncomputable def oracleCircuitComplexity (A f : Language Bool) (n : ℕ) : ℕ :=
  @Cslib.Circuits.complexity _ _ _ _ (oracleInterpretation A)
    (isComplete_oracleInterpretation A) (single (f.slice n))

theorem oracleCircuitComplexity_eq (A f : Language Bool) (n : ℕ) :
    oracleCircuitComplexity A f n =
      @Cslib.Circuits.complexity _ _ _ _ (oracleInterpretation A)
        (isComplete_oracleInterpretation A) (single (f.slice n)) := by
  rfl

local instance instIsCompleteOracle (A : Language Bool) :
    (oracleInterpretation A).IsComplete :=
  isComplete_oracleInterpretation A

/-! ### Part 1: Lifting De Morgan Circuits and Synthesis to `oracleInterpretation A` -/

/-- Every De Morgan circuit embeds into the `A`-oracle basis with the same size. -/
theorem oracleComplexity_le_deMorgan (A : Language Bool) {n m : ℕ}
    (f : (Fin n → Bool) → (Fin m → Bool)) :
    complexity (oracleInterpretation A) f ≤ complexity interpretation f := by
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := f)
  exact (complexity_le_of_computes (c.mapOp toOracle) hc.mapOp).trans (by simp [hsize])

/-- Negating a Boolean function adds at most one gate under `oracleInterpretation A`. -/
theorem oracleComplexity_not_le (A : Language Bool) {n : ℕ} (f : BooleanFunction n) :
    complexity (oracleInterpretation A) (single fun x => !f x) ≤
      complexity (oracleInterpretation A) (single f) + 1 := by
  have h1 := complexity_single_unary_le (I := oracleInterpretation A) (fun b => !b) f
  have h2 : complexity (oracleInterpretation A) (single fun y : Fin 1 → Bool => !y 0) ≤ 1 := by
    refine (oracleComplexity_le_deMorgan A _).trans ?_
    have hnot := complexity_not_le (fun y : Fin 1 → Bool => y 0)
    simp only [complexity_single_proj] at hnot
    exact hnot
  omega

/-- Constant Boolean functions cost at most one gate under `oracleInterpretation A`. -/
theorem oracleComplexity_const_le (A : Language Bool) {n : ℕ} (b : Bool) :
    complexity (oracleInterpretation A) (single fun _ : Fin n → Bool => b) ≤ 1 :=
  (oracleComplexity_le_deMorgan A _).trans (Synthesis.const b).complexity_le

/-- Disjoining two Boolean functions costs at most their complexities plus one gate. -/
theorem oracleComplexity_or_le (A : Language Bool) {n : ℕ} (f g : BooleanFunction n) :
    complexity (oracleInterpretation A) (single fun x => f x || g x) ≤
      complexity (oracleInterpretation A) (single f) +
        complexity (oracleInterpretation A) (single g) + 1 := by
  have h1 := complexity_single_binary_le (I := oracleInterpretation A) (· || ·) f g
  have h2 : complexity (oracleInterpretation A)
      (single fun y : Fin 2 → Bool => y 0 || y 1) ≤ 1 := by
    refine (oracleComplexity_le_deMorgan A _).trans ?_
    have hor := complexity_or_le (fun y : Fin 2 → Bool => y 0) (fun y : Fin 2 → Bool => y 1)
    simp only [complexity_single_proj] at hor
    exact hor
  omega

/-- Conjoining two Boolean functions costs at most their complexities plus one gate. -/
theorem oracleComplexity_and_le (A : Language Bool) {n : ℕ} (f g : BooleanFunction n) :
    complexity (oracleInterpretation A) (single fun x => f x && g x) ≤
      complexity (oracleInterpretation A) (single f) +
        complexity (oracleInterpretation A) (single g) + 1 := by
  have h1 := complexity_single_binary_le (I := oracleInterpretation A) (· && ·) f g
  have h2 : complexity (oracleInterpretation A)
      (single fun y : Fin 2 → Bool => y 0 && y 1) ≤ 1 := by
    refine (oracleComplexity_le_deMorgan A _).trans ?_
    have hand := complexity_and_le (fun y : Fin 2 → Bool => y 0) (fun y : Fin 2 → Bool => y 1)
    simp only [complexity_single_proj] at hand
    exact hand
  omega

/-- Input substitutions add at most two gates under `oracleInterpretation A`. -/
theorem oracleComplexity_substitute_le (A : Language Bool) {n N : ℕ}
    (ρ : Fin N → Fin n ⊕ Bool) (f : BooleanFunction N) :
    complexity (oracleInterpretation A) (single fun x => f (substitute ρ x)) ≤
      complexity (oracleInterpretation A) (single f) + 2 := by
  have h1 := complexity_comp_le (I := oracleInterpretation A) (substitute ρ) (single f)
  have h2 : complexity (oracleInterpretation A) (substitute ρ) ≤ 2 :=
    (oracleComplexity_le_deMorgan A _).trans (complexity_substitute_le_two ρ)
  have hcomp : (single fun x => f (substitute ρ x)) = single f ∘ substitute ρ := rfl
  rw [hcomp]
  omega

/-- Hardwiring a prefix `u` into a language slice costs at most two oracle gates. -/
theorem oracleComplexity_le_of_append_take (A L : Language Bool) (u : List Bool)
    {P Q : ℕ} (hPQ : P ≤ Q) {f : BooleanFunction Q}
    (hf : ∀ r, f r = true ↔ u ++ (List.ofFn r).take P ∈ L) :
    complexity (oracleInterpretation A) (single f) ≤
      complexity (oracleInterpretation A) (single (L.slice (u.length + P))) + 2 := by
  let ρ : Fin (u.length + P) → Fin Q ⊕ Bool := fun j =>
    if h : (j : ℕ) < u.length then .inr u[j] else .inl ⟨j - u.length, by omega⟩
  have hsub (r : Fin Q → Bool) :
      List.ofFn (substitute ρ r) = u ++ (List.ofFn r).take P := by
    refine List.ext_getElem (by simp; omega) fun j h₁ h₂ => ?_
    simp only [List.length_ofFn] at h₁
    rw [List.getElem_ofFn]
    by_cases hj : j < u.length
    · rw [List.getElem_append_left hj]; simp [substitute, ρ, hj]
    · rw [List.getElem_append_right (by omega)]; simp [substitute, ρ, hj]
  have heq : f = fun r => L.slice (u.length + P) (substitute ρ r) := by
    funext r
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, hsub, hf]
  rw [heq]
  exact oracleComplexity_substitute_le A ρ _

private theorem oracleSynthesis_complexity_le {A : Language Bool} {n cost : ℕ}
    {f : BooleanFunction n} (h : Synthesis (oracleInterpretation A) (inputs n) {f} cost) :
    complexity (oracleInterpretation A) (single f) ≤ cost := by
  obtain ⟨c, hc, hsize⟩ := h.exists_circuit
  exact (complexity_le_of_computes c hc).trans hsize

/-- Any De Morgan synthesis of a `Fin r`-indexed family from `inputs m` lifts to an `A`-oracle
synthesis on top of any available `m`-tuple of functions `g` with the same gate budget. -/
private theorem oracleSynthesis_of_deMorgan {A : Language Bool} {n m r cost : ℕ}
    {S : Set (BooleanFunction n)} (g : Fin m → BooleanFunction n)
    (hg : ∀ i, g i ∈ S) (F : Fin r → BooleanFunction m)
    (h : Synthesis interpretation (inputs m) (Set.range F) cost) :
    Synthesis (oracleInterpretation A) S (Set.range fun j x => F j (fun i => g i x)) cost := by
  obtain ⟨c, hc, hsize⟩ := h.exists_circuit_outputs
  have hcm : (c.mapOp toOracle).Computes (oracleInterpretation A) (fun y j => F j y) := hc.mapOp
  have hsyn := Synthesis.circuit (I := oracleInterpretation A) (c.mapOp toOracle) g hg
  refine hsyn.mono Set.Subset.rfl ?_ (by simpa [Circuit.size_mapOp] using hsize)
  rintro _ ⟨o, rfl⟩
  exact ⟨o, funext fun x => congrFun (hcm (fun i => g i x)) o⟩

private theorem oracleSynthesis_const {A : Language Bool} {n : ℕ} {S : Set (BooleanFunction n)}
    (b : Bool) : Synthesis (oracleInterpretation A) S {fun _ => b} 1 := by
  have h := oracleSynthesis_of_deMorgan (A := A) (n := n) (m := 0) (r := 1) (S := S)
    Fin.elim0 (fun i => i.elim0) (fun _ _ => b)
    ((Synthesis.const b).mono Set.Subset.rfl (by rintro _ ⟨_, rfl⟩; rfl) le_rfl)
  exact h.mono Set.Subset.rfl (Set.singleton_subset_iff.2 ⟨0, rfl⟩) le_rfl

private theorem oracleSynthesis_not {A : Language Bool} {n a : ℕ} {S : Set (BooleanFunction n)}
    {f : BooleanFunction n} (hf : Synthesis (oracleInterpretation A) S {f} a) :
    Synthesis (oracleInterpretation A) S {fun x => !f x} (a + 1) := by
  have hstep : Synthesis (oracleInterpretation A) (S ∪ {f}) {fun x => !f x} 1 := by
    have hnot : Synthesis interpretation (inputs 1)
        (Set.range fun _ : Fin 1 => fun y : Fin 1 → Bool => !y 0) 1 := by
      have h0 : Synthesis interpretation (inputs 1) {fun y : Fin 1 → Bool => !y 0} 1 :=
        (Synthesis.of_mem (⟨0, rfl⟩ : (fun y : Fin 1 → Bool => y 0) ∈ inputs 1)).not
      exact h0.mono Set.Subset.rfl (by rintro _ ⟨_, rfl⟩; rfl) le_rfl
    have h1 := oracleSynthesis_of_deMorgan (A := A) (S := S ∪ {f}) (fun _ : Fin 1 => f)
      (fun _ => Set.mem_union_right _ rfl)
      (fun _ : Fin 1 => fun y : Fin 1 → Bool => !y 0) hnot
    exact h1.mono Set.Subset.rfl (Set.singleton_subset_iff.2 ⟨0, rfl⟩) le_rfl
  exact hf.trans hstep

private theorem oracleSynthesis_atLeast {A : Language Bool} {n k j : ℕ}
    {S : Set (BooleanFunction n)} (f : ℕ → BooleanFunction n)
    (hf : ∀ i < k, f i ∈ S) (hj : j ≤ k + 1) :
    Synthesis (oracleInterpretation A) S {atLeast f k j} (2 + k * (2 * (k + 2))) := by
  have hdm := synthesis_atLeast (n := k) (s := inputs k)
    (fun l y => if h : l < k then y ⟨l, h⟩ else false)
    (fun l hl => ⟨⟨l, hl⟩, funext fun y => by simp [hl]⟩) hj
  have h1 := oracleSynthesis_of_deMorgan (A := A) (S := S) (fun i : Fin k => f i.1)
    (fun i => hf i.1 i.2)
    (fun _ : Fin 1 => atLeast (fun l y => if h : l < k then y ⟨l, h⟩ else false) k j)
    (hdm.mono Set.Subset.rfl (by rintro _ ⟨_, rfl⟩; rfl) le_rfl)
  refine h1.mono Set.Subset.rfl (Set.singleton_subset_iff.2 ⟨0, funext fun x => ?_⟩) le_rfl
  simp only [atLeast]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  have hcard : #{l ∈ Finset.range k | (if h : l < k then f l x else false) = true} =
      #{l ∈ Finset.range k | f l x = true} := by
    congr 1; exact Finset.filter_congr fun l hl => by simp [Finset.mem_range.mp hl]
  rw [hcard]

private theorem oracleSynthesis_bitBlast {A : Language Bool} {F : Type*} {w n N cost : ℕ}
    {ι : Type*} [Finite ι] (enc : F ≃ BitString w) (Ψ : ι → (Fin N → F) → F)
    (h : Synthesis (fullInterpretation (k := 2)) (inputs N) (Set.range Ψ) cost)
    {S : Set (BooleanFunction n)} (φ : Fin N → (Fin n → Bool) → F)
    (hφ : ∀ i j, bitsOf enc (φ i) j ∈ S) :
    Synthesis (oracleInterpretation A) S
      (Set.range fun oj : ι × Fin w => bitsOf enc (fun x => Ψ oj.1 (fun i => φ i x)) oj.2)
      (cost * bitBlastCost w) := by
  classical
  have := Fintype.ofFinite ι
  let e := Fintype.equivFin (ι × Fin w)
  let φ₀ : Fin N → BitString (N * w) → F :=
    fun i y => enc.symm fun j => y (finProdFinEquiv (i, j))
  have hφ₀ : ∀ i j, bitsOf enc (φ₀ i) j ∈ inputs (N * w) := fun i j =>
    ⟨finProdFinEquiv (i, j), funext fun y => by simp [bitsOf, φ₀]⟩
  have hdm := Synthesis.bitBlast_synthesis enc enc.symm enc.symm_apply_apply Ψ h φ₀ hφ₀
  have hdm' : Synthesis interpretation (inputs (N * w))
      (Set.range fun idx : Fin (Fintype.card (ι × Fin w)) =>
        bitsOf enc (fun y => Ψ (e.symm idx).1 (fun i => φ₀ i y)) (e.symm idx).2)
      (cost * bitBlastCost w) :=
    hdm.mono Set.Subset.rfl (by rintro _ ⟨idx, rfl⟩; exact ⟨e.symm idx, rfl⟩) le_rfl
  let g : Fin (N * w) → BooleanFunction n :=
    fun idx => bitsOf enc (φ (finProdFinEquiv.symm idx).1) (finProdFinEquiv.symm idx).2
  have hg : ∀ idx, g idx ∈ S := fun idx => hφ _ _
  have h1 := oracleSynthesis_of_deMorgan (A := A) (S := S) g hg
    (fun idx : Fin (Fintype.card (ι × Fin w)) =>
      bitsOf enc (fun y => Ψ (e.symm idx).1 (fun i => φ₀ i y)) (e.symm idx).2) hdm'
  refine h1.mono Set.Subset.rfl ?_ le_rfl
  rintro _ ⟨oj, rfl⟩
  refine ⟨e oj, funext fun x => ?_⟩
  have hφeq : (fun i => φ₀ i (fun idx => g idx x)) = fun i => φ i x := by
    funext i
    simp only [φ₀, g, bitsOf, Equiv.symm_apply_apply]
  simp only [bitsOf, hφeq, e.symm_apply_apply]

/-! ### Part 2: Relativized Sudan–Trevisan–Vadhan Reconstruction -/

private theorem append_apply' {n p q : ℕ} (X : Fin p → BooleanFunction n)
    (Y : Fin q → BooleanFunction n) (k : Fin (p + q)) (v : Fin n → Bool) :
    Fin.append X Y k v = Fin.append (fun i => X i v) (fun i => Y i v) k := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · simp only [Fin.append_left]
  · simp only [Fin.append_right]

private theorem strictMajorityOn_eq_atLeast' {n : ℕ} {ι : Type*} (T : Finset ι)
    (vote : ι → BooleanFunction n) (v : Fin n → Bool) :
    BitString.strictMajorityOn T (fun i => vote i v) =
      atLeast (fun l => if h : l < #T then vote (T.equivFin.symm ⟨l, h⟩) else fun _ => false)
        #T (#T / 2 + 1) v := by
  classical
  simp only [BitString.strictMajorityOn, atLeast]
  congr 1
  rw [Nat.lt_iff_add_one_le]
  congr 1
  refine card_bij (fun i hi => (T.equivFin ⟨i, (mem_filter.1 hi).1⟩ : ℕ)) (fun i hi => ?_)
    (fun i hi i' hi' h => ?_) (fun l hl => ?_)
  · rw [mem_filter] at hi ⊢
    refine ⟨mem_range.2 (T.equivFin _).2, ?_⟩
    rw [dite_eq_left (T.equivFin _).2]
    simpa using hi.2
  · have := T.equivFin.injective (Fin.ext h)
    exact congrArg Subtype.val this
  · rw [mem_filter, mem_range] at hl
    obtain ⟨hl, hv⟩ := hl
    rw [dite_eq_left hl] at hv
    refine ⟨T.equivFin.symm ⟨l, hl⟩, mem_filter.2 ⟨(T.equivFin.symm ⟨l, hl⟩).2, hv⟩, ?_⟩
    simp

private theorem oracleSynthesis_candidate_apply {A : Language Bool} {a w n : ℕ}
    {C : BooleanFunction (a + w)} {sC : ℕ}
    (hC : complexity (oracleInterpretation A) (single C) ≤ sC) {K : ℕ}
    (masks : Fin K → BitString w) (guess : BitString K) {S : Set (BooleanFunction n)}
    (xb : Fin a → BooleanFunction n) (hxb : ∀ k, xb k ∈ S)
    (htrue : (fun _ => true) ∈ S) (hfalse : (fun _ => false) ∈ S) (j : Fin w) :
    Synthesis (oracleInterpretation A) S
      {fun v => Crypto.GoldreichLevin.candidate
        (fun r => C (Fin.append (fun k => xb k v) r)) masks guess j}
      (glBitCost K sC) := by
  classical
  obtain ⟨c, hc, hsize⟩ := complexity_le_iff.1 hC
  have hvote : ∀ (r : BitString w) (bit : Bool), Synthesis (oracleInterpretation A) S
      {fun v => C (Fin.append (fun k => xb k v) r) ^^ bit} (sC + 1) := by
    intro r bit
    let g : Fin (a + w) → BooleanFunction n := Fin.append xb fun k _ => r k
    have hg : ∀ k, g k ∈ S := by
      intro k
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · simp only [g, Fin.append_left]; exact hxb i
      · simp only [g, Fin.append_right]
        cases r i
        · exact hfalse
        · exact htrue
    have hcirc := Synthesis.circuit (I := oracleInterpretation A) c g hg
    have heval : (fun v => c.eval (oracleInterpretation A) (fun k => g k v) 0) =
        fun v => C (Fin.append (fun k => xb k v) r) := by
      funext v
      rw [hc]
      simp only [single_apply]
      congr 1 with k : 1
      change Fin.append xb (fun k _ => r k) k v = _
      rw [append_apply']
    have h1 : Synthesis (oracleInterpretation A) S
        {fun v => C (Fin.append (fun k => xb k v) r)} sC :=
      hcirc.mono Set.Subset.rfl (Set.singleton_subset_iff.2 ⟨0, heval⟩) hsize
    cases bit
    · simpa using h1.mono Set.Subset.rfl Set.Subset.rfl (Nat.le_succ _)
    · simpa using oracleSynthesis_not h1
  set T := Crypto.GoldreichLevin.nonemptySubsets K
  let V : Finset (Fin K) → BooleanFunction n := fun t v =>
    C (Fin.append (fun k => xb k v) (Pi.single j 1 + ∑ l ∈ t, masks l)) ^^ ∑ l ∈ t, guess l
  have hvotes := Synthesis.biUnion (I := oracleInterpretation A) (s := S) T (fun t => {V t})
    (fun _ => sC + 1) fun t _ => hvote _ _
  set S₂ := S ∪ ⋃ t ∈ T, {V t}
  have hmaj := oracleSynthesis_atLeast (A := A) (S := S₂) (k := #T) (j := #T / 2 + 1)
    (fun l => if h : l < #T then V (T.equivFin.symm ⟨l, h⟩) else fun _ => false)
    (fun l hl => by
      rw [dite_eq_left hl]
      exact Set.mem_union_right _ (Set.mem_biUnion (T.equivFin.symm ⟨l, hl⟩).2 rfl))
    (by omega)
  refine (hvotes.trans hmaj).mono Set.Subset.rfl (Set.singleton_subset_iff.2 ?_) ?_
  · change _ = _
    funext v
    rw [← strictMajorityOn_eq_atLeast' T V v]
    simp only [Crypto.GoldreichLevin.candidate, V, T]
    rfl
  · simp only [sum_const, smul_eq_mul, glBitCost, T, Crypto.GoldreichLevin.card_nonemptySubsets]
    exact le_rfl

private theorem oracleSynthesis_candidate {A : Language Bool} {a w n : ℕ}
    {C : BooleanFunction (a + w)} {sC : ℕ}
    (hC : complexity (oracleInterpretation A) (single C) ≤ sC) {K : ℕ}
    (masks : Fin K → BitString w) (guess : BitString K) {S : Set (BooleanFunction n)}
    (xb : Fin a → BooleanFunction n) (hxb : ∀ k, xb k ∈ S) :
    Synthesis (oracleInterpretation A) S
      (Set.range fun j v =>
        Crypto.GoldreichLevin.candidate (fun r => C (Fin.append (fun k => xb k v) r))
          masks guess j)
      (glCost w K sC) := by
  have hconst : Synthesis (oracleInterpretation A) S
      ({fun _ => true} ∪ {fun _ => false}) 2 :=
    (oracleSynthesis_const true).union (oracleSynthesis_const false)
  set S₁ := S ∪ ({fun _ => true} ∪ {fun _ => false})
  let bit : Fin w → BooleanFunction n := fun j v =>
    Crypto.GoldreichLevin.candidate (fun r => C (Fin.append (fun k => xb k v) r)) masks guess j
  have hall := Synthesis.iUnion (I := oracleInterpretation A) (s := S₁) (fun j => {bit j})
    (fun _ => glBitCost K sC) fun j =>
      oracleSynthesis_candidate_apply hC masks guess xb (fun k => Set.mem_union_left _ (hxb k))
        (Set.mem_union_right _ (Set.mem_union_left _ rfl))
        (Set.mem_union_right _ (Set.mem_union_right _ rfl)) j
  refine (hconst.trans hall).mono Set.Subset.rfl ?_ ?_
  · rintro _ ⟨j, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, rfl⟩
  · simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, glCost_eq]
    exact le_rfl

private def OracleBitSynthesis (A : Language Bool) {F : Type*} {w m : ℕ}
    (enc : F ≃ BitString w) (G : (Fin m → F) → F) (cost : ℕ) : Prop :=
  ∀ (n : ℕ) (S : Set (BooleanFunction n)) (φ : Fin m → (Fin n → Bool) → F),
    (∀ i j, bitsOf enc (φ i) j ∈ S) →
      Synthesis (oracleInterpretation A) S
        (Set.range fun j => bitsOf enc (fun v => G fun i => φ i v) j) cost

private theorem oracleBitSynthesis_glPredictor {A : Language Bool} {F : Type*} {w m : ℕ}
    (enc : F ≃ BitString w) {C : BooleanFunction (m * w + w)} {sC : ℕ}
    (hC : complexity (oracleInterpretation A) (single C) ≤ sC) {K : ℕ}
    (masks : Fin K → BitString w) (guess : BitString K) :
    OracleBitSynthesis A enc (glPredictor enc C masks guess) (glCost w K sC) := by
  intro n S φ hφ
  refine (oracleSynthesis_candidate hC masks guess
    (fun k v => BitString.pointBits enc (fun i => φ i v) k)
    fun k => hφ (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).mono
    Set.Subset.rfl ?_ le_rfl
  rintro _ ⟨j, rfl⟩
  exact ⟨j, by funext v; simp [bitsOf, glPredictor]⟩

private theorem oracleBitSynthesis_lineListDecode {A : Language Bool} {F : Type*}
    [Field F] [Fintype F] [DecidableEq F] {w m : ℕ} {enc : F ≃ BitString w}
    {G : (Fin m → F) → F} {SG : ℕ} (hG : OracleBitSynthesis A enc G SG)
    (d D : ℕ) (z : Fin m → F) (a : F) :
    OracleBitSynthesis A enc (Code.lineListDecode G d D z a)
      (lineCost w (Fintype.card F) m #(Sudan.monomials d D) (D / d) d SG) := by
  intro n S φ hφ
  set q := Fintype.card F
  let ΨA : Option (F × Fin m) → (Fin m → F) → F := fun o v => match o with
    | none => firstNonzero (z - fun i => v i)
    | some (t, i) =>
      ((fun i => v i) + t • (firstNonzero (z - fun i => v i))⁻¹ • (z - fun i => v i)) i
  have hA : Synthesis (fullInterpretation (k := 2)) (inputs m) (Set.range ΨA)
      ((q + 5) * m + 2) :=
    Synthesis.full_linePoints (s := inputs m) (fun i v => v i) (fun i => ⟨i, rfl⟩) z
  have hA' := oracleSynthesis_bitBlast (A := A) enc ΨA hA φ hφ
  set TA := Set.range fun oj : Option (F × Fin m) × Fin w =>
    bitsOf enc (fun x => ΨA oj.1 fun i => φ i x) oj.2
  let pt : F → Fin m → (Fin n → Bool) → F := fun t i x => ΨA (some (t, i)) fun k => φ k x
  have hB : Synthesis (oracleInterpretation A) (S ∪ TA)
      (⋃ t : F, Set.range fun j => bitsOf enc (fun x => G fun i => pt t i x) j) (q * SG) := by
    simpa [q] using Synthesis.iUnion (I := oracleInterpretation A) (s := S ∪ TA)
      (fun t : F => Set.range fun j => bitsOf enc (fun x => G fun i => pt t i x) j)
      (fun _ => SG) (fun t => hG n (S ∪ TA) (pt t) fun i j =>
        Set.mem_union_right _ ⟨(some (t, i), j), rfl⟩)
  set TB := ⋃ t : F, Set.range fun j => bitsOf enc (fun x => G fun i => pt t i x) j
  let e := Fintype.equivFin F
  let ΨC : Unit → (Fin (q + 1) → F) → F := fun _ v =>
    hintDecode id (fun t => v (Fin.castSucc (e t))) d D (v (Fin.last q)) a
  have hC : Synthesis (fullInterpretation (k := 2)) (inputs (q + 1)) (Set.range ΨC)
      (1 + hintDecodeCost q q #(Sudan.monomials d D) (D / d) d) := by
    have hconst := Synthesis.full_const (k := 2) (s := inputs (q + 1)) a
    have hdec := Synthesis.full_hintDecode (s := inputs (q + 1) ∪ {fun _ => a}) (ι := F) id
      (fun t v => v (Fin.castSucc (e t)))
      (fun t => Set.mem_union_left _ (⟨Fin.castSucc (e t), rfl⟩ :
        (fun v : Fin (q + 1) → F => v (Fin.castSucc (e t))) ∈ inputs (q + 1)))
      (τ := fun v => v (Fin.last q)) (Set.mem_union_left _ (⟨Fin.last q, rfl⟩ :
        (fun v : Fin (q + 1) → F => v (Fin.last q)) ∈ inputs (q + 1)))
      (Set.mem_union_right _ rfl) d D
    exact (hconst.trans hdec).mono Set.Subset.rfl (by rintro _ ⟨u, rfl⟩; rfl) le_rfl
  let φC : Fin (q + 1) → (Fin n → Bool) → F :=
    Fin.lastCases (fun x => ΨA none fun i => φ i x) fun k x => G fun i => pt (e.symm k) i x
  have hφC : ∀ k j, bitsOf enc (φC k) j ∈ (S ∪ TA) ∪ TB := by
    intro k j
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp only [φC, Fin.lastCases_last]
      exact Set.mem_union_left _ (Set.mem_union_right _ ⟨(none, j), rfl⟩)
    · simp only [φC, Fin.lastCases_castSucc]
      exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨e.symm k, j, rfl⟩)
  have hC' := oracleSynthesis_bitBlast (A := A) enc ΨC hC φC hφC
  refine (hA'.trans (hB.comp hC')).mono Set.Subset.rfl ?_ ?_
  · rintro _ ⟨j, rfl⟩
    refine Or.inr ⟨((), j), funext fun x => ?_⟩
    simp only [bitsOf, ΨC, φC, Fin.lastCases_last, Fin.lastCases_castSucc,
      Equiv.symm_apply_apply, Code.lineListDecode, pt, ΨA]
  · unfold lineCost
    nlinarith

private theorem oracleBitSynthesis_selfCorrect {A : Language Bool} {F : Type*}
    [Field F] [DecidableEq F] {w m : ℕ} {enc : F ≃ BitString w}
    {C1 : (Fin m → F) → F} {S1 : ℕ} (hC1 : OracleBitSynthesis A enc C1 S1)
    {d : ℕ} (ν : Fin (d + 1) ↪ F) {L : ℕ} (V : Fin (3 ^ L) → Fin m → F) :
    OracleBitSynthesis A enc (fun x => majTree L fun τ => lagrangeDecode ν C1 x (V τ))
      (selfCorrectCost w m d L S1) := by
  intro n S φ hφ
  let ΨA : (Fin (3 ^ L) × Fin (d + 1)) × Fin m → (Fin m → F) → F := fun o v =>
    v o.2 + ν o.1.2 * V o.1.1 o.2
  have hA : Synthesis (fullInterpretation (k := 2)) (inputs m) (Set.range ΨA)
      (m * (3 ^ L * (d + 1))) := by
    simpa [Fintype.card_prod, mul_comm, mul_left_comm, mul_assoc] using
      Synthesis.family (I := fullInterpretation (k := 2)) (s := inputs m) ΨA (fun _ => 1)
        (fun o => Synthesis.full_unary (fun a => a + ν o.1.2 * V o.1.1 o.2)
          (⟨o.2, rfl⟩ : (fun v : Fin m → F => v o.2) ∈ inputs m))
  have hA' := oracleSynthesis_bitBlast (A := A) enc ΨA hA φ hφ
  set TA := Set.range fun oj : ((Fin (3 ^ L) × Fin (d + 1)) × Fin m) × Fin w =>
    bitsOf enc (fun x => ΨA oj.1 fun i => φ i x) oj.2
  let pt : Fin (3 ^ L) × Fin (d + 1) → Fin m → (Fin n → Bool) → F := fun τi k x =>
    ΨA (τi, k) fun i => φ i x
  have hB : Synthesis (oracleInterpretation A) (S ∪ TA)
      (⋃ τi : Fin (3 ^ L) × Fin (d + 1),
        Set.range fun j => bitsOf enc (fun x => C1 fun k => pt τi k x) j)
      (3 ^ L * (d + 1) * S1) := by
    simpa [Fintype.card_prod, mul_comm, mul_left_comm, mul_assoc] using
      Synthesis.iUnion (I := oracleInterpretation A) (s := S ∪ TA)
        (fun τi : Fin (3 ^ L) × Fin (d + 1) =>
          Set.range fun j => bitsOf enc (fun x => C1 fun k => pt τi k x) j)
        (fun _ => S1) (fun τi => hC1 n (S ∪ TA) (pt τi) fun k j =>
          Set.mem_union_right _ ⟨((τi, k), j), rfl⟩)
  set TB := ⋃ τi : Fin (3 ^ L) × Fin (d + 1),
    Set.range fun j => bitsOf enc (fun x => C1 fun k => pt τi k x) j
  let ΨC : Unit → (Fin (3 ^ L * (d + 1)) → F) → F := fun _ v =>
    majTree L fun τ => ∑ i, lagrangeWeight ν i * v (finProdFinEquiv (τ, i))
  have hC : Synthesis (fullInterpretation (k := 2)) (inputs (3 ^ L * (d + 1))) (Set.range ΨC)
      (3 ^ L * (2 * (d + 1) + 1) + (2 * 3 ^ L - 2)) := by
    have hsums := Synthesis.family (I := fullInterpretation (k := 2))
      (s := inputs (3 ^ L * (d + 1)))
      (fun τ v => ∑ i, lagrangeWeight ν i * v (finProdFinEquiv (τ, i)))
      (fun _ => 2 * (d + 1) + 1)
      (fun τ => by
        simpa using Synthesis.full_weightedSum (s := inputs (3 ^ L * (d + 1))) (lagrangeWeight ν)
          (fun i v => v (finProdFinEquiv (τ, i))) (fun i => ⟨_, rfl⟩))
    have htree := Synthesis.full_majTree (s := inputs (3 ^ L * (d + 1)) ∪
        Set.range fun τ (v : Fin (3 ^ L * (d + 1)) → F) =>
          ∑ i, lagrangeWeight ν i * v (finProdFinEquiv (τ, i))) L
      (fun τ v => ∑ i, lagrangeWeight ν i * v (finProdFinEquiv (τ, i)))
      (fun τ => Set.mem_union_right _ ⟨τ, rfl⟩)
    exact (hsums.trans htree).mono Set.Subset.rfl (by rintro _ ⟨u, rfl⟩; rfl)
      (by simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, le_refl])
  let φC : Fin (3 ^ L * (d + 1)) → (Fin n → Bool) → F := fun k x =>
    C1 fun i => pt (finProdFinEquiv.symm k) i x
  have hφC : ∀ k j, bitsOf enc (φC k) j ∈ (S ∪ TA) ∪ TB := fun k j =>
    Set.mem_union_right _ (Set.mem_iUnion.2 ⟨finProdFinEquiv.symm k, j, rfl⟩)
  have hC' := oracleSynthesis_bitBlast (A := A) enc ΨC hC φC hφC
  refine (hA'.trans (hB.comp hC')).mono Set.Subset.rfl ?_ ?_
  · rintro _ ⟨j, rfl⟩
    refine Or.inr ⟨((), j), funext fun x => ?_⟩
    simp only [bitsOf, ΨC, φC, Equiv.symm_apply_apply, lagrangeDecode, pt, ΨA]
    rfl
  · unfold selfCorrectCost
    nlinarith

private theorem le_half_of_agree' {N : ℕ} {C E : BooleanFunction N} {ε : ℝ}
    (hagree : (1 / 2 + ε) * 2 ^ N ≤ #{y | C y = E y}) : ε ≤ 1 / 2 := by
  have hN : (#{y | C y = E y} : ℝ) ≤ 2 ^ N := by
    exact_mod_cast (card_le_univ _).trans_eq BitString.card
  linarith only [le_of_mul_le_mul_right
    (hagree.trans (by linarith only [hN]) : (1 / 2 + ε) * 2 ^ N ≤ 1 * 2 ^ N)
    (by positivity : (0 : ℝ) < 2 ^ N)]

private theorem two_mul_mul_le' {q Q a ε D : ℝ} (hq : 0 ≤ q) (hQ : 0 ≤ Q) {K : ℕ}
    (hgl : ε * Q ≤ 2 ^ (K + 2) * a) (hmargin : 2 ^ (K + 3) * D ≤ q * ε) :
    2 * D * Q ≤ q * a := by
  refine le_of_mul_le_mul_left (a := (2 : ℝ) ^ (K + 2)) ?_ (by positivity)
  calc 2 ^ (K + 2) * (2 * D * Q) = 2 ^ (K + 3) * D * Q := by ring
    _ ≤ q * ε * Q := mul_le_mul_of_nonneg_right hmargin hQ
    _ = q * (ε * Q) := by ring
    _ ≤ q * (2 ^ (K + 2) * a) := mul_le_mul_of_nonneg_left hgl hq
    _ = 2 ^ (K + 2) * (q * a) := by ring

private theorem lineErrors_le' {q Q a ε D δ : ℝ} (hq : 1 < q) (hQ : 1 ≤ Q) (ha : 0 < a)
    (hε : 0 < ε) {K : ℕ} (hgl : ε * Q ≤ 2 ^ (K + 2) * a) (_hD : 0 ≤ D)
    (hmargin : 2 ^ (K + 3) * D ≤ q * ε) (hδ : 0 ≤ δ) (hδD : δ ≤ D) :
    1 + (q * a * (Q - 1) / (q * a / Q - D) ^ 2 + Q * (Q - 1) * δ / (q - 1)) / Q ≤
      Q * (1 / Q + 2 ^ (K + 4) / (q * ε) + D / (q - 1)) := by
  have hQpos : 0 < Q := by linarith
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  set μ := q * a / Q
  have hμpos : 0 < μ := by positivity
  have hμ : 2 * D ≤ μ := (le_div_iff₀ hQpos).2 (two_mul_mul_le' hq0.le hQpos.le hgl hmargin)
  have hμD : μ / 2 ≤ μ - D := by linarith only [hμ]
  have hsq : μ ^ 2 / 4 ≤ (μ - D) ^ 2 := by
    simpa only [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      pow_le_pow_left₀ (by positivity) hμD 2
  have hterm1 : q * a * (Q - 1) / (μ - D) ^ 2 / Q ≤ Q * (2 ^ (K + 4) / (q * ε)) := by
    have hμD' : 0 < μ - D := by linarith only [hμpos, hμD]
    rw [div_div, div_le_iff₀ (by positivity)]
    have hμsq : μ ^ 2 * Q ^ 2 = (q * a) ^ 2 := by simp only [μ]; field_simp
    have key : q * a * (Q - 1) ≤ q * a * Q :=
      mul_le_mul_of_nonneg_left (by linarith only [hQ]) (by positivity)
    have hstep : q * a * Q * 4 ≤ Q * (2 ^ (K + 4) / (q * ε)) * (μ ^ 2 * Q) := by
      rw [show Q * (2 ^ (K + 4) / (q * ε)) * (μ ^ 2 * Q) = 2 ^ (K + 4) * (μ ^ 2 * Q ^ 2) /
        (q * ε) by field_simp, hμsq, le_div_iff₀ (by positivity)]
      calc q * a * Q * 4 * (q * ε) = 4 * q * (q * a) * (ε * Q) := by ring
        _ ≤ 4 * q * (q * a) * (2 ^ (K + 2) * a) :=
            mul_le_mul_of_nonneg_left hgl (by positivity)
        _ = 2 ^ (K + 4) * (q * a) ^ 2 := by ring
    calc q * a * (Q - 1) ≤ q * a * Q := key
      _ = q * a * Q * 4 / 4 := by ring
      _ ≤ Q * (2 ^ (K + 4) / (q * ε)) * (μ ^ 2 * Q) / 4 := by gcongr
      _ = Q * (2 ^ (K + 4) / (q * ε)) * (μ ^ 2 / 4 * Q) := by ring
      _ ≤ Q * (2 ^ (K + 4) / (q * ε)) * ((μ - D) ^ 2 * Q) := by gcongr
  have hterm2 : Q * (Q - 1) * δ / (q - 1) / Q ≤ Q * (D / (q - 1)) := by
    rw [div_div, div_le_iff₀ (by positivity)]
    have : Q * (Q - 1) * δ ≤ Q * Q * D := by gcongr; linarith only [hQ]
    calc Q * (Q - 1) * δ ≤ Q * Q * D := this
      _ = Q * (D / (q - 1)) * ((q - 1) * Q) := by field_simp
  rw [add_div]
  calc 1 + (q * a * (Q - 1) / (μ - D) ^ 2 / Q + Q * (Q - 1) * δ / (q - 1) / Q)
      ≤ 1 + (Q * (2 ^ (K + 4) / (q * ε)) + Q * (D / (q - 1))) := by linarith only [hterm1, hterm2]
    _ = Q * (1 / Q + 2 ^ (K + 4) / (q * ε) + D / (q - 1)) := by field_simp; ring

private theorem reconstruction_ranges' {q d D K m : ℕ} {ε : ℝ} (hq2 : 2 ≤ q) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) (hn : q < #(Sudan.monomials d D))
    (hmargin : (2 : ℝ) ^ (K + 3) * D ≤ q * ε)
    (herr : 6 * ((d : ℝ) + 1) * (1 / (q : ℝ) ^ m + 2 ^ (K + 4) / (q * ε) + D / (q - 1)) ≤ 1) :
    1 ≤ D ∧ D < q ∧ d + 1 ≤ q - 1 := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq2
  have hD1 : 1 ≤ D := by
    by_contra! hD0
    have : #(Sudan.monomials d D) ≤ 1 := card_le_one.2 fun x hx y hy => by
      rw [Sudan.mem_monomials] at hx hy; ext <;> omega
    omega
  have hDq : D < q := by
    have hqε : (q : ℝ) * ε ≤ q / 2 := by
      linarith only [mul_le_mul_of_nonneg_left hε1 (by linarith only [hq1] : (0 : ℝ) ≤ q)]
    have h8 : (8 : ℝ) ≤ 2 ^ (K + 3) := by
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (K + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h8D : 8 * (D : ℝ) ≤ q / 2 :=
      (mul_le_mul_of_nonneg_right h8 (Nat.cast_nonneg D)).trans (hmargin.trans hqε)
    exact_mod_cast (by linarith only [h8D, hq1] : (D : ℝ) < q)
  refine ⟨hD1, hDq, ?_⟩
  have hpos_sum : (0 : ℝ) ≤ 1 / (q : ℝ) ^ m + 2 ^ (K + 4) / (q * ε) := by positivity
  have h6 : 6 * ((d : ℝ) + 1) * (D / (q - 1)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (by linarith only [hpos_sum]) (by positivity)).trans herr
  have h6' : 6 * ((d : ℝ) + 1) * D ≤ q - 1 := by
    rwa [mul_div_assoc', div_le_one (by linarith only [hq1])] at h6
  have h6d : 6 * ((d : ℝ) + 1) ≤ q - 1 :=
    (le_mul_of_one_le_right (by positivity) (by exact_mod_cast hD1)).trans h6'
  rw [← Nat.cast_le (α := ℝ), Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  linarith [Nat.cast_nonneg (α := ℝ) d]

/-- **Relativized Sudan–Trevisan–Vadhan reconstruction theorem.** -/
theorem oracleComplexity_le_of_agree_hardnessEncode {A : Language Bool} {F : Type*}
    [Field F] [Fintype F] {w m b : ℕ} (enc : F ≃ BitString w) (h : BitString b ↪ F)
    (f : BooleanFunction (m * b)) {C : BooleanFunction (m * w + w)} {s : ℕ}
    (hC : complexity (oracleInterpretation A) (single C) ≤ s) {ε : ℝ} (hε : 0 < ε)
    (hagree : (1 / 2 + ε) * 2 ^ (m * w + w) ≤ #{y | C y = hardnessEncode enc h f y})
    {K D L : ℕ} (hK : 0 < K) (hsize : (w : ℝ) ≤ 2 * (ε / 2) ^ 2 * (2 ^ K - 1 : ℕ))
    (hd : 1 ≤ m * (2 ^ b - 1))
    (hn : Fintype.card F < #(Sudan.monomials (m * (2 ^ b - 1)) D))
    (hmargin : (2 : ℝ) ^ (K + 3) * D ≤ Fintype.card F * ε)
    (herr : 6 * ((m * (2 ^ b - 1) : ℕ) + 1 : ℝ) * (1 / (Fintype.card F : ℝ) ^ m +
      2 ^ (K + 4) / (Fintype.card F * ε) + D / (Fintype.card F - 1)) ≤ 1)
    (hL : m * b ≤ 2 ^ L) :
    complexity (oracleInterpretation A) (single f) ≤
      reconstructionCost w b m D K L s (Fintype.card F)
        #(Sudan.monomials (m * (2 ^ b - 1)) D) := by
  classical
  set d := m * (2 ^ b - 1) with hd_def
  set q := Fintype.card F with hq_def
  set p := truthTableExtension h f
  have hp : p ∈ reedMuller F m d := truthTableExtension_mem_reedMuller h f
  have hqw : q = 2 ^ w := (Fintype.card_congr enc).trans BitString.card
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq2
  obtain ⟨masks, guess, hgl⟩ := exists_glPredictor_agree enc h f C hε hagree hK hsize
  set G := glPredictor enc C masks guess
  have hε1 : ε ≤ 1 / 2 := le_half_of_agree' hagree
  obtain ⟨hD1, hDq, hdq⟩ := reconstruction_ranges' hq2 hε hε1 hn hmargin herr
  set Q : ℝ := (q : ℝ) ^ m with hQ_def
  have hQ : (Fintype.card (Fin m → F) : ℝ) = Q := by simp [Q, q]
  have hQ2 : (2 : ℝ) ^ (m * w) = Q := by simp [Q, hqw, ← pow_mul, mul_comm]
  have hQ1 : (1 : ℝ) ≤ Q := one_le_pow₀ hq1.le
  set a := (#{x | G x = p x} : ℕ)
  have ha : ε * Q ≤ 2 ^ (K + 2) * a := by rw [← hQ2]; exact hgl
  have hapos : (0 : ℝ) < a :=
    pos_of_mul_pos_right ((by positivity : (0 : ℝ) < ε * Q).trans_le ha) (by positivity)
  have hμ : (D : ℝ) < q * #{y | G y = p y} / q ^ m := by
    rw [lt_div_iff₀ (by positivity)]
    have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
    linarith only [two_mul_mul_le' (Nat.cast_nonneg q) (by linarith only [hQ1]) ha hmargin,
      one_le_mul_of_one_le_of_one_le hD1' hQ1]
  obtain ⟨z, hz⟩ := exists_card_lineListDecode_ne_le hd hn hDq hp G hμ
  set C1 := lineListDecode G d D z (p z)
  have herrC1 : ((d : ℝ) + 1) * #{x | C1 x ≠ p x} ≤ Q / 6 := by
    have hbound := lineErrors_le' (q := q) (Q := Q) (a := a) (ε := ε) (D := D)
      (δ := ((D - d : ℕ) : ℝ)) hq1 hQ1 hapos hε ha (by positivity) hmargin (by positivity)
      (by exact_mod_cast Nat.sub_le D d)
    calc ((d : ℝ) + 1) * #{x | C1 x ≠ p x} ≤
          ((d : ℝ) + 1) * (Q * (1 / Q + 2 ^ (K + 4) / (q * ε) + D / (q - 1))) := by
          gcongr; exact hz.trans hbound
      _ = Q / 6 * (6 * ((d : ℝ) + 1) * (1 / Q + 2 ^ (K + 4) / (q * ε) + D / (q - 1))) := by
          ring
      _ ≤ Q / 6 := mul_le_of_le_one_right (by positivity) herr
  have hdq' : d + 2 ≤ Fintype.card F := by omega
  let ν : Fin (d + 1) ↪ F := nonzeroNodes hdq'
  have hν : ∀ i, ν i ≠ 0 := nonzeroNodes_ne_zero hdq'
  let grid : Finset (Fin m → F) :=
    univ.image fun x : BitString (m * b) => fun i => h (BitString.block x i)
  have hgrid : #grid ≤ 2 ^ (2 ^ L) := by
    calc #grid ≤ #(univ : Finset (BitString (m * b))) := card_image_le
      _ = 2 ^ (m * b) := by rw [card_univ, BitString.card]
      _ ≤ 2 ^ (2 ^ L) := Nat.pow_le_pow_right (by decide) hL
  obtain ⟨V, hV⟩ := exists_forall_majTree_eq (α := F) (Ω := Fin m → F) grid
    (fun x v => lagrangeDecode ν C1 x v) p (ρ := 1 / 6) (fun x _ => by
      have := card_lagrangeDecode_ne_le ν hν hp C1 x
      rw [hQ]
      calc (#{v | lagrangeDecode ν C1 x v ≠ p x} : ℝ) ≤ ((d + 1) * #{y | C1 y ≠ p y} : ℕ) := by
            exact_mod_cast this
        _ = ((d : ℝ) + 1) * #{y | C1 y ≠ p y} := by push_cast; ring
        _ ≤ Q / 6 := herrC1
        _ = 1 / 6 * Q := by ring) (by norm_num) hgrid
  have hU := oracleBitSynthesis_selfCorrect
    (oracleBitSynthesis_lineListDecode (oracleBitSynthesis_glPredictor enc hC masks guess)
      d D z (p z)) ν V
  let gp : Fin m → (Fin (m * b) → Bool) → F := fun i x => h (BitString.block x i)
  have hemb : Synthesis (oracleInterpretation A) (inputs (m * b))
      (Set.range fun ij : Fin m × Fin w => bitsOf enc (gp ij.1) ij.2)
      (m * w * (2 ^ b * (2 * b + 2) + 1)) := by
    have hdm : Synthesis interpretation (inputs (m * b))
        (Set.range fun idx : Fin (m * w) =>
          bitsOf enc (gp (finProdFinEquiv.symm idx).1) (finProdFinEquiv.symm idx).2)
        (m * w * (2 ^ b * (2 * b + 2) + 1)) := by
      simpa only [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
        mul_assoc] using Synthesis.family (I := interpretation) (s := inputs (m * b))
        (fun idx : Fin (m * w) =>
          bitsOf enc (gp (finProdFinEquiv.symm idx).1) (finProdFinEquiv.symm idx).2)
        (fun _ => 2 ^ b * (2 * b + 2) + 1)
        fun idx => Synthesis.selected (fun l => finProdFinEquiv ((finProdFinEquiv.symm idx).1, l))
          fun y => enc (h y) (finProdFinEquiv.symm idx).2
    have h1 := oracleSynthesis_of_deMorgan (A := A) (S := inputs (m * b))
      (fun i x => x i) (fun i => ⟨i, rfl⟩)
      (fun idx : Fin (m * w) =>
        bitsOf enc (gp (finProdFinEquiv.symm idx).1) (finProdFinEquiv.symm idx).2) hdm
    refine h1.mono Set.Subset.rfl ?_ le_rfl
    rintro _ ⟨ij, rfl⟩
    exact ⟨finProdFinEquiv ij, funext fun x => by simp [bitsOf]⟩
  set T₁ := Set.range fun ij : Fin m × Fin w => bitsOf enc (gp ij.1) ij.2
  have hUs := hU (m * b) (inputs (m * b) ∪ T₁) gp fun i j =>
    Set.mem_union_right _ ⟨(i, j), rfl⟩
  set U : (Fin m → F) → F := fun x => majTree L fun τ => lagrangeDecode ν C1 x (V τ)
  set T₂ := Set.range fun j => bitsOf enc (fun v => U fun i => gp i v) j
  have hout : Synthesis (oracleInterpretation A) ((inputs (m * b) ∪ T₁) ∪ T₂) {f}
      (2 ^ w * (2 * w + 2) + 1) := by
    obtain ⟨c, hc, hsize⟩ := (Synthesis.selected (n := w) id
      (fun y => decide (enc.symm y = 1))).exists_circuit
    have hcm : (c.mapOp toOracle).Computes (oracleInterpretation A)
        (single fun y => decide (enc.symm y = 1)) := hc.mapOp
    refine (Synthesis.circuit (I := oracleInterpretation A) (c.mapOp toOracle)
      (fun j => bitsOf enc (fun v => U fun i => gp i v) j)
      fun j => Or.inr ⟨j, rfl⟩).mono Set.Subset.rfl
      (Set.singleton_subset_iff.2 ⟨0, funext fun x => (congrFun (hcm _) 0).trans ?_⟩)
      (by simpa [Circuit.size_mapOp] using hsize)
    have hUx : U (fun i => gp i x) = p (fun i => gp i x) :=
      hV _ (mem_image.2 ⟨x, mem_univ _, rfl⟩)
    simp only [single_apply, bitsOf, Equiv.symm_apply_apply,
      hUx, p, gp, truthTableExtension_block]
    cases f x <;> simp
  refine (oracleSynthesis_complexity_le (hemb.trans (hUs.trans hout))).trans ?_
  simp only [reconstructionCost, ← hd_def, ← hq_def]; omega

/-- **Relativized Sudan–Trevisan–Vadhan reconstruction with polynomial bound.** -/
theorem oracleComplexity_le_pow_of_agree_hardnessEncode {A : Language Bool} {F : Type*}
    [Field F] [Fintype F] {w m b : ℕ} (enc : F ≃ BitString w) (h : BitString b ↪ F)
    (f : BooleanFunction (m * b)) {C : BooleanFunction (m * w + w)} {s : ℕ}
    (hC : complexity (oracleInterpretation A) (single C) ≤ s) {ε : ℝ} (hε : 0 < ε)
    (hagree : (1 / 2 + ε) * 2 ^ (m * w + w) ≤ #{y | C y = hardnessEncode enc h f y})
    {K D L : ℕ} (hK : 0 < K) (hsize : (w : ℝ) ≤ 2 * (ε / 2) ^ 2 * (2 ^ K - 1 : ℕ))
    (hd : 1 ≤ m * (2 ^ b - 1))
    (hn : Fintype.card F < #(Sudan.monomials (m * (2 ^ b - 1)) D))
    (hmargin : (2 : ℝ) ^ (K + 3) * D ≤ Fintype.card F * ε)
    (herr : 6 * ((m * (2 ^ b - 1) : ℕ) + 1 : ℝ) * (1 / (Fintype.card F : ℝ) ^ m +
      2 ^ (K + 4) / (Fintype.card F * ε) + D / (Fintype.card F - 1)) ≤ 1)
    (hL : m * b ≤ 2 ^ L) :
    complexity (oracleInterpretation A) (single f) ≤
      2 ^ 11 * 3 ^ L * m * w ^ 2 * Fintype.card F ^ 9 * 4 ^ K * (s + 1) := by
  refine (oracleComplexity_le_of_agree_hardnessEncode enc h f hC hε hagree hK hsize hd hn hmargin
    herr hL).trans ?_
  have hqw : Fintype.card F = 2 ^ w := (Fintype.card_congr enc).trans BitString.card
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hε1 : ε ≤ 1 / 2 := le_half_of_agree' hagree
  obtain ⟨-, hDq, hdq⟩ := reconstruction_ranges' hq2 hε hε1 hn hmargin herr
  refine reconstructionCost_le hqw ?_ ?_ ?_ hDq ?_ (by omega)
  · exact Nat.pos_of_ne_zero fun hw => by rw [hw, pow_zero] at hqw; omega
  · exact Nat.pos_of_ne_zero fun hm => by simp [hm] at hd
  · simpa [BitString] using Fintype.card_le_of_embedding h
  · calc #(Sudan.monomials (m * (2 ^ b - 1)) D) ≤ #(range (D + 1) ×ˢ range (D + 1)) :=
          card_filter_le _ _
      _ = (D + 1) * (D + 1) := by rw [card_product, card_range]
      _ ≤ Fintype.card F * Fintype.card F := Nat.mul_le_mul hDq hDq
      _ = Fintype.card F ^ 2 := (sq _).symm

/-- Average-case hardness against `A`-oracle circuits of size at most `s`. -/
def IsOracleAverageCaseHard (A : Language Bool) {n : ℕ} (f : BooleanFunction n) (s : ℕ) : Prop :=
  ∀ g : BooleanFunction n, complexity (oracleInterpretation A) (single g) ≤ s →
    (#{x | g x = f x} : ℝ) / 2 ^ n ≤ 1 / 2 + 1 / s

theorem IsOracleAverageCaseHard.div_lt {A : Language Bool} {n s : ℕ}
    {f : BooleanFunction n} (hf : IsOracleAverageCaseHard A f s) {δ : ℝ}
    (hδ : 1 / (s : ℝ) < δ) {g : BooleanFunction n}
    (hg : complexity (oracleInterpretation A) (single g) ≤ s) :
    (#{x | g x = f x} : ℝ) / 2 ^ n < 1 / 2 + δ := by
  have := hf g hg; linarith

private theorem exists_oracleComplexity_le_of_agree_prefix (A : Language Bool) {n N : ℕ}
    (hle : n ≤ N) (E : BooleanFunction n) (g : BooleanFunction N) {δ : ℝ}
    (hagree : δ * 2 ^ N < #{y | g y = E fun i => y (Fin.castLE hle i)}) :
    ∃ C : BooleanFunction n, complexity (oracleInterpretation A) (single C) ≤
      complexity (oracleInterpretation A) (single g) + 2 ∧ δ * 2 ^ n < #{x | C x = E x} := by
  classical
  set p := N - n
  have hN : n + p = N := Nat.add_sub_cancel' hle
  let ρ : BitString p → Fin N → Fin n ⊕ Bool := fun z k => appendInputs z (Fin.cast hN.symm k)
  have hρ : ∀ z x, substitute (ρ z) x = fun k => Fin.append x z (Fin.cast hN.symm k) :=
    fun z x => funext fun k => congrFun (substitute_appendInputs z x) (Fin.cast hN.symm k)
  have hleft : ∀ (x : BitString n) (z : BitString p) (i : Fin n),
      Fin.append x z (Fin.cast hN.symm (Fin.castLE hle i)) = x i := fun x z i => by
    rw [show Fin.cast hN.symm (Fin.castLE hle i) = Fin.castAdd p i from Fin.ext rfl,
      Fin.append_left]
  have hsplit : #{y | g y = E fun i => y (Fin.castLE hle i)} =
      ∑ z : BitString p, #{x | g (substitute (ρ z) x) = E x} := by
    have hinv (y : BitString N) : (fun k => Fin.append (fun i => y (Fin.castLE hle i))
        (fun j => y (Fin.cast hN (Fin.natAdd n j))) (Fin.cast hN.symm k)) = y := by
      funext k
      obtain ⟨k', rfl⟩ : ∃ k', k = Fin.cast hN k' := ⟨Fin.cast hN.symm k, by simp⟩
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k'
      · simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.append_left]; rfl
      · simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.append_right]
    rw [← card_sigma]
    refine card_nbij' (fun y => ⟨fun j => y (Fin.cast hN (Fin.natAdd n j)),
      fun i => y (Fin.castLE hle i)⟩) (fun q => fun k => Fin.append q.2 q.1 (Fin.cast hN.symm k))
      (fun y hy => ?_) (fun q hq => ?_) (fun y _ => ?_) (fun q _ => ?_)
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, coe_sigma,
        Set.mem_sigma_iff, mem_coe, hρ] at hy ⊢
      rwa [hinv]
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, coe_sigma,
        Set.mem_sigma_iff, mem_coe, hρ] at hq ⊢
      rw [show (fun i => Fin.append q.2 q.1 (Fin.cast hN.symm (Fin.castLE hle i))) = q.2 from
        funext (hleft q.2 q.1)]
      exact hq
    · exact hinv y
    · obtain ⟨z, x⟩ := q
      simp only [Sigma.mk.injEq]
      refine ⟨funext fun j => ?_, heq_of_eq (funext (hleft x z))⟩
      simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.append_right]
  have hex : ∃ z : BitString p, δ * 2 ^ n < #{x | g (substitute (ρ z) x) = E x} := by
    by_contra hall
    push Not at hall
    have hsum : (#{y | g y = E fun i => y (Fin.castLE hle i)} : ℝ) ≤
        ∑ _z : BitString p, δ * 2 ^ n := by
      rw [hsplit, Nat.cast_sum]
      exact sum_le_sum fun z _ => hall z
    rw [sum_const, card_univ, nsmul_eq_mul] at hsum
    have hcard : (Fintype.card (BitString p) : ℝ) * (δ * 2 ^ n) = δ * 2 ^ N := by
      rw [BitString.card, Nat.cast_pow, Nat.cast_ofNat, mul_left_comm, ← pow_add, ← hN, add_comm]
    linarith
  obtain ⟨z, hz⟩ := hex
  exact ⟨fun x => g (substitute (ρ z) x), oracleComplexity_substitute_le A (ρ z) g, hz⟩

private theorem three_pow_log_le' {x : ℕ} (hx : 0 < x) : 3 ^ (Nat.log 2 x + 1) ≤ 3 * x ^ 2 := by
  have h1 : 3 ^ Nat.log 2 x ≤ 4 ^ Nat.log 2 x := Nat.pow_le_pow_left (by norm_num) _
  have h2 : 4 ^ Nat.log 2 x = (2 ^ Nat.log 2 x) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h3 : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 hx.ne'
  rw [pow_succ]
  calc 3 ^ Nat.log 2 x * 3 ≤ (2 ^ Nat.log 2 x) ^ 2 * 3 := by rw [← h2]; gcongr
    _ ≤ x ^ 2 * 3 := by gcongr
    _ = 3 * x ^ 2 := by ring

private theorem schedule_bounds' {M b : ℕ} (hb : 1 ≤ b)
    (hev : (2 ^ 27 * M ^ 3 + 4608 * M + 128) * b ^ 6 ≤ 2 ^ (b / 4)) :
    2 * M ≤ 2 ^ (b / 2) ∧ 128 * b ≤ 2 ^ (b / 4) ∧ 4608 * M * b ≤ 2 ^ (b / 4) ∧
      36 * M ≤ 2 ^ (b / 4) ∧ 2 ^ 27 * M ^ 3 * b ^ 6 ≤ 2 ^ (b / 4) := by
  have hb6 : b ≤ b ^ 6 := Nat.le_self_pow (by norm_num) b
  have hB : 128 * b ≤ 2 ^ (b / 4) := (Nat.mul_le_mul (Nat.le_add_left _ _) hb6).trans hev
  have hD : 4608 * M * b ≤ 2 ^ (b / 4) := (Nat.mul_le_mul (by omega) hb6).trans hev
  have hF : 2 ^ 27 * M ^ 3 * b ^ 6 ≤ 2 ^ (b / 4) := (Nat.mul_le_mul_right _ (by omega)).trans hev
  have hE : 36 * M ≤ 2 ^ (b / 4) := by
    have : 4608 * M * 1 ≤ 4608 * M * b := Nat.mul_le_mul_left _ hb; omega
  have hA : 2 * M ≤ 2 ^ (b / 2) :=
    calc 2 * M ≤ 2 ^ (b / 4) := by omega
      _ ≤ 2 ^ (b / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨hA, hB, hD, hE, hF⟩

private theorem two_pow_masks' (σ b : ℕ) :
    2 ^ (2 * σ + Nat.log 2 (4 * b) + 2) = 4 ^ σ * 4 * 2 ^ Nat.log 2 (4 * b) := by
  rw [pow_add, pow_add, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]; ring

private theorem two_pow_masks_le' (σ : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    2 ^ (2 * σ + Nat.log 2 (4 * b) + 2) ≤ 16 * b * 4 ^ σ := by
  rw [two_pow_masks']
  calc 4 ^ σ * 4 * 2 ^ Nat.log 2 (4 * b) ≤ 4 ^ σ * 4 * (4 * b) :=
        Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (by omega))
    _ = 16 * b * 4 ^ σ := by ring

private theorem two_pow_masks_ge' (σ b : ℕ) :
    2 * (4 * b) * 4 ^ σ + 1 ≤ 2 ^ (2 * σ + Nat.log 2 (4 * b) + 2) := by
  rw [two_pow_masks']
  have h : 4 * b < 2 ^ (Nat.log 2 (4 * b) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  rw [pow_succ] at h
  have h4 : 1 ≤ 4 ^ σ := Nat.one_le_pow _ _ (by norm_num)
  have h' : 2 * (4 * b) + 2 ≤ 4 * 2 ^ Nat.log 2 (4 * b) := by omega
  calc 2 * (4 * b) * 4 ^ σ + 1 ≤ 2 * (4 * b) * 4 ^ σ + 2 * 4 ^ σ := by omega
    _ = (2 * (4 * b) + 2) * 4 ^ σ := by ring
    _ ≤ 4 * 2 ^ Nat.log 2 (4 * b) * 4 ^ σ := Nat.mul_le_mul_right _ h'
    _ = 4 ^ σ * 4 * 2 ^ Nat.log 2 (4 * b) := by ring

private theorem masks_size' {w σ K : ℕ} (hK : 2 * w * 4 ^ σ + 1 ≤ 2 ^ K) :
    (w : ℝ) ≤ 2 * (1 / ((2 ^ σ : ℕ) : ℝ) / 2) ^ 2 * ((2 ^ K - 1 : ℕ) : ℝ) := by
  have hcast : (2 * w * 4 ^ σ : ℝ) ≤ ((2 ^ K - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_sub_one_of_lt hK
  have hpos : (0 : ℝ) < 2 ^ σ := by positivity
  have h4 : (2 : ℝ) * (1 / ((2 ^ σ : ℕ) : ℝ) / 2) ^ 2 * (2 * w * 4 ^ σ) = w := by
    rw [show (4 : ℝ) ^ σ = (2 ^ σ) ^ 2 by rw [← pow_mul, mul_comm σ 2, pow_mul]; norm_num]
    push_cast; field_simp
  calc (w : ℝ) = 2 * (1 / ((2 ^ σ : ℕ) : ℝ) / 2) ^ 2 * (2 * w * 4 ^ σ) := h4.symm
    _ ≤ 2 * (1 / ((2 ^ σ : ℕ) : ℝ) / 2) ^ 2 * ((2 ^ K - 1 : ℕ) : ℝ) := by gcongr

private theorem card_lt_card_monomials' {M b : ℕ} (hM : 1 ≤ M) (hb : 1 ≤ b)
    (hA : 2 * M ≤ 2 ^ (b / 2)) :
    2 ^ (4 * b) < #(Sudan.monomials (M * (2 ^ b - 1)) (2 ^ (3 * b - b / 4))) := by
  have h2b : 2 ≤ 2 ^ b :=
    (show 2 = 2 ^ 1 by norm_num).trans_le (Nat.pow_le_pow_right (by norm_num) hb)
  set d := M * (2 ^ b - 1)
  set D := 2 ^ (3 * b - b / 4)
  have hd1 : 1 ≤ d := Nat.mul_pos (by omega) (by omega)
  have hdlt : d < M * 2 ^ b := mul_lt_mul_of_pos_left (by omega) (by omega)
  have hmon := Sudan.add_one_mul_add_two_le_two_mul_mul_card_monomials hd1 D
  have hDsq : 2 ^ (6 * b - b / 2) ≤ D * D := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2dq : 2 * d * 2 ^ (4 * b) < 2 ^ (6 * b - b / 2) :=
    calc 2 * d * 2 ^ (4 * b) < 2 * (M * 2 ^ b) * 2 ^ (4 * b) :=
          mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = 2 * M * 2 ^ (b + 4 * b) := by rw [pow_add]; ring
      _ ≤ 2 ^ (b / 2) * 2 ^ (b + 4 * b) := Nat.mul_le_mul_right _ hA
      _ = 2 ^ (b / 2 + (b + 4 * b)) := (pow_add 2 (b / 2) (b + 4 * b)).symm
      _ ≤ 2 ^ (6 * b - b / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt : 2 * d * 2 ^ (4 * b) < 2 * d * #(Sudan.monomials d D) :=
    calc 2 * d * 2 ^ (4 * b) < D * D := h2dq.trans_le hDsq
      _ ≤ (D + 1) * (D + 2) := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ 2 * d * #(Sudan.monomials d D) := hmon
  exact lt_of_mul_lt_mul_left hlt (Nat.zero_le _)

private theorem margin_le' {b σ : ℕ} (hb : 1 ≤ b) (hB : 128 * b ≤ 2 ^ (b / 4))
    (h3σ : 3 * σ ≤ b) :
    (2 : ℝ) ^ (2 * σ + Nat.log 2 (4 * b) + 2 + 3) * ((2 ^ (3 * b - b / 4) : ℕ) : ℝ) ≤
      ((2 ^ (4 * b) : ℕ) : ℝ) * (1 / ((2 ^ σ : ℕ) : ℝ)) := by
  have hnat : 2 ^ (2 * σ + Nat.log 2 (4 * b) + 2 + 3) * 2 ^ (3 * b - b / 4) * 2 ^ σ ≤
      2 ^ (4 * b) :=
    calc 2 ^ (2 * σ + Nat.log 2 (4 * b) + 2 + 3) * 2 ^ (3 * b - b / 4) * 2 ^ σ
        = 2 ^ (2 * σ + Nat.log 2 (4 * b) + 2) * 8 * 2 ^ (3 * b - b / 4) * 2 ^ σ := by
          rw [pow_add _ _ 3, show (2 : ℕ) ^ 3 = 8 by norm_num]
      _ ≤ 16 * b * 4 ^ σ * 8 * 2 ^ (3 * b - b / 4) * 2 ^ σ := by
          gcongr; exact two_pow_masks_le' σ hb
      _ = 128 * b * 2 ^ (3 * σ) * 2 ^ (3 * b - b / 4) := by
          rw [show 3 * σ = 2 * σ + σ by ring, pow_add, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
          ring
      _ ≤ 2 ^ (b / 4) * 2 ^ b * 2 ^ (3 * b - b / 4) := by gcongr
      _ = 2 ^ (4 * b) := by rw [← pow_add, ← pow_add]; congr 1; omega
  have hpos : (0 : ℝ) < ((2 ^ σ : ℕ) : ℝ) := by positivity
  rw [mul_one_div, le_div_iff₀ hpos]
  exact_mod_cast hnat

private theorem errors_le' {M b σ : ℕ} (hM : 1 ≤ M) (hb : 1 ≤ b)
    (hD' : 4608 * M * b ≤ 2 ^ (b / 4)) (hE : 36 * M ≤ 2 ^ (b / 4)) (h3σ : 3 * σ ≤ b) :
    6 * (((M * (2 ^ b - 1) : ℕ) : ℝ) + 1) * (1 / ((2 ^ (4 * b) : ℕ) : ℝ) ^ M +
      2 ^ (2 * σ + Nat.log 2 (4 * b) + 2 + 4) /
        (((2 ^ (4 * b) : ℕ) : ℝ) * (1 / ((2 ^ σ : ℕ) : ℝ))) +
      ((2 ^ (3 * b - b / 4) : ℕ) : ℝ) / (((2 ^ (4 * b) : ℕ) : ℝ) - 1)) ≤ 1 := by
  have h2b : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hMle : M ≤ M * 2 ^ b := Nat.le_mul_of_pos_right _ (by positivity)
  set q := 2 ^ (4 * b) with hq
  set d := M * (2 ^ b - 1)
  set K := 2 * σ + Nat.log 2 (4 * b) + 2
  set D := 2 ^ (3 * b - b / 4) with hD
  have hd1 : d + 1 ≤ M * 2 ^ b := by grind [Nat.mul_sub_one]
  have hq18 : 18 * (d + 1) ≤ q := by
    have h18 : 18 * M ≤ 2 ^ (3 * b) :=
      calc 18 * M ≤ 2 ^ (b / 4) := by omega
        _ ≤ 2 ^ (3 * b) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 18 * (d + 1) ≤ 18 * (M * 2 ^ b) := Nat.mul_le_mul_left _ hd1
      _ = 18 * M * 2 ^ b := by ring
      _ ≤ 2 ^ (3 * b) * 2 ^ b := Nat.mul_le_mul_right _ h18
      _ = q := by rw [hq, ← pow_add]; congr 1; ring
  have hT1 : 18 * (d + 1) ≤ q ^ M := hq18.trans (Nat.le_self_pow (by omega) q)
  have hT2 : 18 * (d + 1) * 2 ^ (K + 4) * 2 ^ σ ≤ q :=
    calc 18 * (d + 1) * 2 ^ (K + 4) * 2 ^ σ
        ≤ 18 * (M * 2 ^ b) * (16 * b * 4 ^ σ * 16) * 2 ^ σ := by
          rw [pow_add _ K 4, show (2 : ℕ) ^ 4 = 16 by norm_num]
          gcongr; exact two_pow_masks_le' σ hb
      _ = 4608 * M * b * 2 ^ b * 2 ^ (3 * σ) := by
          rw [show 3 * σ = 2 * σ + σ by ring, pow_add, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
          ring
      _ ≤ 2 ^ (b / 4) * 2 ^ b * 2 ^ b := by gcongr
      _ = 2 ^ (b / 4 + b + b) := by rw [pow_add, pow_add]
      _ ≤ q := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hT3 : 18 * (d + 1) * D + 1 ≤ q := by
    have h1 : 18 * (d + 1) * D ≤ 18 * M * 2 ^ (4 * b - b / 4) :=
      calc 18 * (d + 1) * D ≤ 18 * (M * 2 ^ b) * D := by gcongr
        _ = 18 * M * 2 ^ (b + (3 * b - b / 4)) := by rw [hD, pow_add]; ring
        _ = 18 * M * 2 ^ (4 * b - b / 4) := by congr 2; omega
    have h2 : 36 * M * 2 ^ (4 * b - b / 4) ≤ q :=
      calc 36 * M * 2 ^ (4 * b - b / 4) ≤ 2 ^ (b / 4) * 2 ^ (4 * b - b / 4) := by gcongr
        _ = q := by rw [hq, ← pow_add]; congr 1; omega
    have h3 : 1 ≤ 18 * M * 2 ^ (4 * b - b / 4) := Nat.one_le_iff_ne_zero.2 (by positivity)
    linarith
  have hq1 : (1 : ℝ) < q := by exact_mod_cast Nat.one_lt_two_pow (by omega : 4 * b ≠ 0)
  have hdpos : (0 : ℝ) < 18 * ((d : ℝ) + 1) := by positivity
  have e1 : 1 / (q : ℝ) ^ M ≤ 1 / (18 * ((d : ℝ) + 1)) :=
    one_div_le_one_div_of_le hdpos (by exact_mod_cast hT1)
  have e2 : (2 : ℝ) ^ (K + 4) / ((q : ℝ) * (1 / ((2 ^ σ : ℕ) : ℝ))) ≤
      1 / (18 * ((d : ℝ) + 1)) := by
    rw [mul_one_div, div_div_eq_mul_div, div_le_div_iff₀ (by linarith) hdpos, one_mul]
    have : ((18 * (d + 1) * 2 ^ (K + 4) * 2 ^ σ : ℕ) : ℝ) ≤ q := by exact_mod_cast hT2
    push_cast at this ⊢; linarith
  have e3 : (D : ℝ) / ((q : ℝ) - 1) ≤ 1 / (18 * ((d : ℝ) + 1)) := by
    rw [div_le_div_iff₀ (by linarith) hdpos, one_mul]
    have : ((18 * (d + 1) * D + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast hT3
    push_cast at this; linarith
  have hne : (d : ℝ) + 1 ≠ 0 := by positivity
  calc _ ≤ 6 * ((d : ℝ) + 1) * (3 * (1 / (18 * ((d : ℝ) + 1)))) := by gcongr; linarith
    _ = 1 := by field_simp; ring

private theorem final_lt' {M b σ : ℕ} (hM : 1 ≤ M) (hb : 1 ≤ b)
    (hF : 2 ^ 27 * M ^ 3 * b ^ 6 ≤ 2 ^ (b / 4)) (h5σ : 5 * σ ≤ b) :
    2 ^ 11 * 3 ^ (Nat.log 2 (M * b) + 1) * M * (4 * b) ^ 2 * (2 ^ (4 * b)) ^ 9 *
      4 ^ (2 * σ + Nat.log 2 (4 * b) + 2) * (2 ^ σ + 2 + 1) < 2 ^ (40 * b) := by
  have h3L := three_pow_log_le' (show 0 < M * b by positivity)
  have h4K : 4 ^ (2 * σ + Nat.log 2 (4 * b) + 2) ≤ 256 * b ^ 2 * 16 ^ σ := by
    rw [show 4 ^ (2 * σ + Nat.log 2 (4 * b) + 2) = (2 ^ (2 * σ + Nat.log 2 (4 * b) + 2)) ^ 2 by
      rw [← pow_mul, mul_comm _ 2, pow_mul]; norm_num]
    calc (2 ^ (2 * σ + Nat.log 2 (4 * b) + 2)) ^ 2 ≤ (16 * b * 4 ^ σ) ^ 2 :=
          Nat.pow_le_pow_left (two_pow_masks_le' σ hb) 2
      _ = 256 * b ^ 2 * 16 ^ σ := by
          rw [mul_pow, mul_pow, ← pow_mul, mul_comm σ 2, pow_mul]; norm_num
  have hs : 2 ^ σ + 2 + 1 ≤ 4 * 2 ^ σ := by grind
  calc 2 ^ 11 * 3 ^ (Nat.log 2 (M * b) + 1) * M * (4 * b) ^ 2 * (2 ^ (4 * b)) ^ 9 *
        4 ^ (2 * σ + Nat.log 2 (4 * b) + 2) * (2 ^ σ + 2 + 1)
      ≤ 2 ^ 11 * (3 * (M * b) ^ 2) * M * (4 * b) ^ 2 * (2 ^ (4 * b)) ^ 9 *
          (256 * b ^ 2 * 16 ^ σ) * (4 * 2 ^ σ) := by gcongr
    _ = 3 * 2 ^ 25 * (M ^ 3 * b ^ 6) * 2 ^ (36 * b) * 2 ^ (5 * σ) := by
        rw [show 16 ^ σ = 2 ^ (4 * σ) by rw [pow_mul]; norm_num, show 5 * σ = 4 * σ + σ by ring,
          pow_add 2 (4 * σ) σ, ← pow_mul, show 4 * b * 9 = 36 * b by ring]
        ring
    _ ≤ 3 * 2 ^ 25 * (M ^ 3 * b ^ 6) * 2 ^ (36 * b) * 2 ^ b := by gcongr
    _ < 2 ^ 27 * M ^ 3 * b ^ 6 * 2 ^ (37 * b) := by
        rw [show 37 * b = 36 * b + b by ring, pow_add 2 (36 * b) b]
        have : 0 < M ^ 3 * b ^ 6 * 2 ^ (36 * b) * 2 ^ b := by positivity
        nlinarith
    _ ≤ 2 ^ (b / 4) * 2 ^ (37 * b) := Nat.mul_le_mul_right _ hF
    _ ≤ 2 ^ (40 * b) := by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Relativized hardness at one length.** -/
theorem isOracleAverageCaseHard_encodedSlice_of {A L : Language Bool} {M N σ : ℕ} (hM : 1 ≤ M)
    (hb : 1 ≤ blockLength M N)
    (hev : (2 ^ 27 * M ^ 3 + 4608 * M + 128) * blockLength M N ^ 6 ≤ 2 ^ (blockLength M N / 4))
    (hσ : 50 * σ ≤ blockLength M N + 1)
    (hhard : 2 ^ (40 * blockLength M N) ≤
      complexity (oracleInterpretation A) (single (L.slice (M * blockLength M N)))) :
    IsOracleAverageCaseHard A (encodedSlice L M N) (2 ^ σ) := by
  classical
  set b := blockLength M N with hb_def
  have hb0 : b ≠ 0 := by omega
  have hw0 : 4 * b ≠ 0 := by omega
  obtain ⟨hA, hB, hD', hE, hF⟩ := schedule_bounds' hb hev
  have h3σ : 3 * σ ≤ b := by omega
  have h5σ : 5 * σ ≤ b := by omega
  have h2b : 2 ≤ 2 ^ b :=
    (show 2 = 2 ^ 1 by norm_num).trans_le (Nat.pow_le_pow_right (by norm_num) hb)
  have hd1 : 1 ≤ M * (2 ^ b - 1) := Nat.mul_pos (by omega) (by omega)
  intro g hg
  by_contra hcon
  push Not at hcon
  rw [encodedSlice, dite_eq_right hb0, lt_div_iff₀ (by positivity)] at hcon
  obtain ⟨C, hC, hCagree⟩ := exists_oracleComplexity_le_of_agree_prefix A
    (encodedLength_le M N) _ g hcon
  have hrec := oracleComplexity_le_pow_of_agree_hardnessEncode (A := A)
    (BinaryField.equivBits hw0).toEquiv
    (BinaryField.embed hw0 (by omega : b ≤ 4 * b)) (L.slice (M * b)) (C := C)
    (s := 2 ^ σ + 2) (hC.trans (by omega)) (ε := 1 / ((2 ^ σ : ℕ) : ℝ)) (by positivity)
    hCagree.le (K := 2 * σ + Nat.log 2 (4 * b) + 2) (D := 2 ^ (3 * b - b / 4))
    (L := Nat.log 2 (M * b) + 1) (by omega) (masks_size' (two_pow_masks_ge' σ b)) hd1
    (by rw [BinaryField.card hw0]; exact card_lt_card_monomials' hM hb hA)
    (by rw [BinaryField.card hw0]; exact margin_le' hb hB h3σ)
    (by rw [BinaryField.card hw0]; exact errors_le' hM hb hD' hE h3σ)
    (Nat.lt_pow_succ_log_self (by norm_num) (M * b)).le
  rw [BinaryField.card hw0] at hrec
  exact absurd hhard (not_le.2 (hrec.trans_lt (final_lt' hM hb hF h5σ)))

/-- **Relativized exponential worst-case hardness gives exponential average-case hardness.** -/
theorem eventually_isOracleAverageCaseHard_encodedSlice {A L : Language Bool} {γ : ℝ} (hγ : 0 < γ)
    (hard : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ (γ * n) ≤ complexity (oracleInterpretation A) (single (L.slice n))) :
    ∀ᶠ N in atTop, IsOracleAverageCaseHard A (encodedSlice L (blockFactor γ) N)
      (2 ^ (N / hardnessDivisor γ)) := by
  set M := blockFactor γ with hM_def
  have hM : 1 ≤ M := Nat.le_add_left 1 _
  have hγM : 40 ≤ γ * M := by
    have h : 40 / γ ≤ M := by
      simpa only [hM_def, blockFactor, Nat.cast_add, Nat.cast_one] using
        (Nat.le_ceil (40 / γ)).trans (le_add_of_nonneg_right zero_le_one)
    rwa [div_le_iff₀ hγ, mul_comm] at h
  have hblock : Tendsto (blockLength M) atTop atTop :=
    Nat.tendsto_div_const_atTop (by positivity)
  have hMb : Tendsto (fun b : ℕ => M * b) atTop atTop :=
    tendsto_id.const_mul_atTop' (by omega)
  have hhard : ∀ᶠ b : ℕ in atTop,
      2 ^ (40 * b) ≤ complexity (oracleInterpretation A) (single (L.slice (M * b))) := by
    filter_upwards [hMb.eventually hard] with b hb
    have h1 : (2 : ℝ) ^ ((40 * b : ℕ) : ℝ) ≤ (2 : ℝ) ^ (γ * ((M * b : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; nlinarith)
    rw [Real.rpow_natCast] at h1
    exact_mod_cast h1.trans hb
  have hev := Nat.eventually_mul_pow_le_pow_div (2 ^ 27 * M ^ 3 + 4608 * M + 128) 6 4
    one_lt_two (by positivity)
  filter_upwards [hblock.eventually (hhard.and (hev.and (eventually_ge_atTop 1)))] with N hN
  refine isOracleAverageCaseHard_encodedSlice_of hM hN.2.2 hN.2.1 ?_ hN.1
  have h1 := Nat.div_mul_le_self N (hardnessDivisor γ)
  have h2 := Nat.lt_div_mul_add (a := N) (b := 4 * (M + 1)) (by positivity)
  simp only [hardnessDivisor, ← hM_def, blockLength] at h1 h2 ⊢
  nlinarith


end CslibFrontier.Computability.Circuit.Boolean.Oracle
