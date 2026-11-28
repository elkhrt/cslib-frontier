/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google LLC
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.CircuitLowerBound
public import CslibFrontier.Computability.Circuit.Arithmetic.DepthThree
import CslibFrontier.Foundations.LinearAlgebra.Matrix.ListProd
import CslibFrontier.Tactic.LinarithCast
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Constant-depth algebraic circuit lower bounds via set-multilinear rank

This module develops semantic set-multilinearity, subcube-imbalanced unbiased words, sharp
low-depth relative-rank bounds, variable-padding reductions, growing-depth superpolynomial lower
bounds for iterated matrix multiplication, and an explicit full-rank split-bilinear polynomial
separating homogeneous depth-three circuits from set-multilinear depth-four formulas.

## Main definitions

* `Cslib.Circuits.Arithmetic.SPFormula.IsSemanticallySetMultilinear`,
  `Cslib.Circuits.Arithmetic.SPCircuit.IsSemanticallySetMultilinear`: gate-wise semantic
  set-multilinearity for unbounded fan-in formulas and circuits.
* `Cslib.Circuits.Arithmetic.SPFormula.normalizeSetMultilinear`: normalization of a semantically
  set-multilinear formula to a syntactically set-multilinear one without increasing size or
  product-depth.
* `Cslib.Circuits.Arithmetic.HasSubcubeImbalance`: uniform lower bound on the absolute weight sum
  of every small subset of blocks of an integer word.
* `Cslib.Circuits.Arithmetic.altWord`, `Cslib.Circuits.Arithmetic.sqrtStepWord`: unbiased
  two-letter words tailored to product-depth one and product-depth two.
* `Cslib.Circuits.Arithmetic.immPadSubst`, `Cslib.Circuits.Arithmetic.SPFormula.substConst`:
  zero-one identity-matrix padding and constant/variable substitution for unbounded fan-in
  formulas.
* `Cslib.Circuits.Arithmetic.growingProductDepth`: an explicit unboundedly growing product-depth
  schedule supporting superpolynomial circuit lower bounds.
* `Cslib.Circuits.Arithmetic.splitBilinearPoly`,
  `Cslib.Circuits.Arithmetic.splitBilinearFormula`: an explicit set-multilinear polynomial with
  unit relative rank and a linear-size product-depth-two formula.

## Main results

* `Cslib.Circuits.Arithmetic.SPFormula.isSetMultilinear_normalizeSetMultilinear`,
  `Cslib.Circuits.Arithmetic.SPFormula.polynomial_normalizeSetMultilinear`,
  `Cslib.Circuits.Arithmetic.SPFormula.IsSetMultilinear.flatten`,
  `Cslib.Circuits.Arithmetic.SPCircuit.exists_setMultilinear_formula`: semantic-to-syntactic
  normalization for set-multilinear formulas and simple circuits.
* `Cslib.Circuits.Arithmetic.hasSubcubeImbalance_twoLetter`,
  `Cslib.Circuits.Arithmetic.hasSubcubeImbalance_sqrtTwoWord`: subcube-imbalance bounds for
  two-letter integer words.
* `Cslib.Circuits.Arithmetic.SPFormula.IsSetMultilinear.relRank_polynomial_le_depthOne`,
  `Cslib.Circuits.Arithmetic.SPFormula.IsSetMultilinear.relRank_polynomial_le_depthTwo`:
  relative-rank upper bounds for set-multilinear formulas of product-depth one and two.
* `SPFormula.IsSemanticallySetMultilinear.two_rpow_depthOne_le_nodeCount_of_imm`,
  `SPFormula.IsSemanticallySetMultilinear.two_rpow_sqrt_le_nodeCount_of_imm`,
  `SPFormula.IsSemanticallySetMultilinear.two_rpow_le_nodeCount_of_imm`, and
  `SPCircuit.IsSemanticallySetMultilinear.two_rpow_le_size_of_imm`: exponential,
  square-root-exponent, and general constant-depth lower bounds for semantically set-multilinear
  formulas and simple circuits computing iterated matrix multiplication.
* `Cslib.Circuits.Arithmetic.SPFormula.two_rpow_sqrt_le_of_imm_depthOne`,
  `Cslib.Circuits.Arithmetic.SPCircuit.two_rpow_sqrt_le_of_imm_depthOne`: square-root-exponent
  lower bounds for unrestricted product-depth-one formulas and simple circuits over any field.
* `Cslib.Circuits.Arithmetic.projection_immPadSubst_imm`,
  `Cslib.Circuits.Arithmetic.SPCircuit.two_rpow_le_of_imm_of_le`,
  `Cslib.Circuits.Arithmetic.SPCircuit.rpow_le_size_add_of_imm`,
  `Cslib.Circuits.Arithmetic.SPCircuit.eventually_pow_lt_size_of_imm_range`,
  `Cslib.Circuits.Arithmetic.SPCircuit.eventually_pow_lt_size_of_imm_growingDepth`:
  zero-one padding, explicit power bounds for arbitrary product-depth, full polynomial-range
  superpolynomial bounds, and superpolynomial bounds at unboundedly growing product-depth.
* `Cslib.Circuits.Arithmetic.relRank_splitBilinearPoly`,
  `Cslib.Circuits.Arithmetic.pow_le_rank_partialDerivatives_splitBilinearPoly`,
  `Cslib.Circuits.Arithmetic.two_pow_le_cost_splitBilinearPoly`,
  `Cslib.Circuits.Arithmetic.splitBilinearFormula_witness`: unit relative rank, partial-derivative
  lower bound, and exponential depth-three vs. linear depth-four separation.
-/

public section

namespace Cslib.Circuits.Arithmetic

open Filter Finset Function MvPolynomial

/-! ### : Semantic set-multilinearity and normalization -/

section SemanticNormalization

variable {σ K : Type*} {d : ℕ}

/-- A nonzero polynomial is set-multilinear on at most one set of blocks. -/
theorem isSetMultilinear_eq_of_ne_zero [CommSemiring K] {blk : σ → Fin d}
    {S T : Finset (Fin d)} {f : MvPolynomial σ K} (hf : f ≠ 0)
    (hS : IsSetMultilinear blk S f) (hT : IsSetMultilinear blk T f) : S = T := by
  obtain ⟨m, hm⟩ := support_nonempty.2 hf
  exact eq_of_mem_range_blockMonomial (hS m hm) (hT m hm)

/-- Renaming variables along their blocks preserves set-multilinearity. -/
theorem isSetMultilinear_rename [CommSemiring K] {τ : Type*} {blk : σ → Fin d}
    {blk' : τ → Fin d} (e : σ → τ) (he : ∀ v, blk' (e v) = blk v)
    {S : Finset (Fin d)} {f : MvPolynomial σ K} (hf : IsSetMultilinear blk S f) :
    IsSetMultilinear blk' S (rename e f) := by
  rw [← smProj_eq_self_iff, ← rename_smProj e he, hf.smProj_eq_self]

/-- Every monomial in the support of a finite product of polynomials is a sum of monomials from
the supports of the factors. -/
private theorem exists_sum_mem_support_of_mem_support_prod [CommSemiring K] {ι : Type*}
    (s : Finset ι) (f : ι → MvPolynomial σ K) {μ : σ →₀ ℕ}
    (hμ : μ ∈ (∏ j ∈ s, f j).support) :
    ∃ y : ι → (σ →₀ ℕ), (∀ j ∈ s, y j ∈ (f j).support) ∧ ∑ j ∈ s, y j = μ := by
  classical
  induction s using Finset.induction_on generalizing μ with
  | empty =>
    rw [prod_empty] at hμ
    have hμ0 : μ = 0 := by
      by_contra hne
      rw [mem_support_iff, coeff_one, ite_eq_right (Ne.symm hne)] at hμ
      exact hμ rfl
    exact ⟨fun _ => 0, fun _ h => absurd h (notMem_empty _), by simp [hμ0]⟩
  | insert a s ha ih =>
    rw [prod_insert ha] at hμ
    obtain ⟨μ₁, hμ₁, μ₂, hμ₂, rfl⟩ := Finset.mem_add.1 (support_mul (f a) (∏ j ∈ s, f j) hμ)
    obtain ⟨y, hy, hysum⟩ := ih hμ₂
    refine ⟨Function.update y a μ₁, fun j hj => ?_, ?_⟩
    · rcases mem_insert.1 hj with rfl | hjs
      · simpa using hμ₁
      · have hja : j ≠ a := fun h => ha (h ▸ hjs)
        simpa [Function.update_of_ne hja] using hy j hjs
    · rw [sum_insert ha, Function.update_self]
      congr 1
      rw [← hysum]
      refine sum_congr rfl fun j hjs => ?_
      have hja : j ≠ a := fun h => ha (h ▸ hjs)
      exact Function.update_of_ne hja _ _

/-- If a finite product of set-multilinear polynomials on block sets `T j` is nonzero and
set-multilinear on `S`, then `T` is an ordered partition of `S`. -/
theorem prod_blockSplits_of_ne_zero [CommSemiring K] {ι : Type*} [Fintype ι]
    {blk : σ → Fin d} {S : Finset (Fin d)} {T : ι → Finset (Fin d)} {f : ι → MvPolynomial σ K}
    (hprod : ∏ j, f j ≠ 0) (hS : IsSetMultilinear blk S (∏ j, f j))
    (hT : ∀ j, IsSetMultilinear blk (T j) (f j)) :
    Pairwise (Disjoint on T) ∧ univ.biUnion T = S := by
  classical
  obtain ⟨μ, hμ⟩ := support_nonempty.2 hprod
  obtain ⟨y, hy, hysum⟩ := exists_sum_mem_support_of_mem_support_prod univ f hμ
  have hsum : ∑ j, y j ∈ Set.range (blockMonomial blk S) := hysum.symm ▸ hS μ hμ
  obtain ⟨T', hT', hy'⟩ := (sum_mem_range_blockMonomial_iff y).1 hsum
  have hTeq : T = T' := funext fun j =>
    eq_of_mem_range_blockMonomial (hT j (y j) (hy j (mem_univ j))) (hy' j)
  exact hTeq ▸ mem_blockSplits.1 hT'

/-- The iterated matrix multiplication polynomial `imm K n d` is nonzero over any nontrivial
commutative semiring. -/
theorem imm_ne_zero (K : Type*) [CommSemiring K] [Nontrivial K] (n d : ℕ) [NeZero n] :
    imm K n d ≠ 0 := by
  intro h
  let pt : Fin d × Fin n × Fin n → K := fun v => if v.2.1 = v.2.2 then 1 else 0
  have hev := congrArg (MvPolynomial.eval pt) h
  rw [map_zero] at hev
  have h1 : MvPolynomial.eval pt (imm K n d) = 1 := by
    change ((MvPolynomial.eval pt).mapMatrix (List.ofFn (immMatrix K n d)).prod) 0 0 = 1
    rw [map_list_prod, List.prod_eq_one]
    · simp
    · intro M hM
      rw [List.mem_map] at hM
      obtain ⟨_, hM', rfl⟩ := hM
      rw [List.mem_ofFn] at hM'
      obtain ⟨i, rfl⟩ := hM'
      ext a c
      simp [immMatrix, Matrix.one_apply, pt]
  exact one_ne_zero (h1.symm.trans hev)

namespace SPFormula

variable {n : ℕ}

/-- A formula is **semantically set-multilinear** with respect to the block map `blk` when every
subformula computes a set-multilinear polynomial on some subset of blocks. -/
@[expose] def IsSemanticallySetMultilinear [CommSemiring K] (blk : Fin n → Fin d) :
    SPFormula K n → Prop
  | .input _ => True
  | .gate (.const _) _ => True
  | .gate (.add _ c) args =>
      (∃ S, MvPolynomial.IsSetMultilinear blk S (add c args).polynomial) ∧
        ∀ j, IsSemanticallySetMultilinear blk (args j)
  | .gate (.mul _) args =>
      (∃ S, MvPolynomial.IsSetMultilinear blk S (mul args).polynomial) ∧
        ∀ j, IsSemanticallySetMultilinear blk (args j)

/-- Every semantically set-multilinear formula computes a set-multilinear polynomial on some set
of blocks. -/
theorem IsSemanticallySetMultilinear.exists_isSetMultilinear [CommSemiring K]
    {blk : Fin n → Fin d} {F : SPFormula K n} (hF : F.IsSemanticallySetMultilinear blk) :
    ∃ S : Finset (Fin d), MvPolynomial.IsSetMultilinear blk S F.polynomial := by
  cases F with
  | input i => exact ⟨{blk i}, isSetMultilinear_X blk i⟩
  | gate op args =>
    cases op with
    | const a => exact ⟨∅, isSetMultilinear_C blk a⟩
    | add _ _ => exact hF.1
    | mul _ => exact hF.1

/-- Every syntactically set-multilinear formula is semantically set-multilinear. -/
theorem IsSetMultilinear.isSemanticallySetMultilinear [CommSemiring K] {blk : Fin n → Fin d}
    {F : SPFormula K n} {S : Finset (Fin d)} (hF : F.IsSetMultilinear blk S) :
    F.IsSemanticallySetMultilinear blk := by
  induction hF with
  | input _ => trivial
  | const _ => trivial
  | add c G S hG ih =>
    exact ⟨⟨S, (IsSetMultilinear.add c G S hG).isSetMultilinear_polynomial⟩, ih⟩
  | mul G T hT hG ih =>
    exact ⟨⟨univ.biUnion T, (IsSetMultilinear.mul G T hT hG).isSetMultilinear_polynomial⟩, ih⟩

/-- Choose a set of blocks on which `F.polynomial` is set-multilinear, or `∅` if none exists. -/
private noncomputable def chosenBlockSet [CommSemiring K] (blk : Fin n → Fin d)
    (F : SPFormula K n) : Finset (Fin d) :=
  letI := Classical.dec (∃ S : Finset (Fin d), MvPolynomial.IsSetMultilinear blk S F.polynomial)
  if h : ∃ S : Finset (Fin d), MvPolynomial.IsSetMultilinear blk S F.polynomial then
    Classical.choose h
  else ∅

private theorem isSetMultilinear_chosenBlockSet [CommSemiring K] {blk : Fin n → Fin d}
    {F : SPFormula K n} (hF : F.IsSemanticallySetMultilinear blk) :
    MvPolynomial.IsSetMultilinear blk (chosenBlockSet blk F) F.polynomial := by
  classical
  have hex := hF.exists_isSetMultilinear
  simpa [chosenBlockSet, hex] using Classical.choose_spec hex

private theorem chosenBlockSet_eq_of_ne_zero [CommSemiring K] {blk : Fin n → Fin d}
    {F : SPFormula K n} {S : Finset (Fin d)} (hne : F.polynomial ≠ 0)
    (hS : MvPolynomial.IsSetMultilinear blk S F.polynomial) :
    chosenBlockSet blk F = S := by
  classical
  have hex : ∃ T : Finset (Fin d), MvPolynomial.IsSetMultilinear blk T F.polynomial := ⟨S, hS⟩
  have hspec : MvPolynomial.IsSetMultilinear blk (chosenBlockSet blk F) F.polynomial := by
    simpa [chosenBlockSet, hex] using Classical.choose_spec hex
  exact isSetMultilinear_eq_of_ne_zero hne hspec hS

/-- Normalize a formula to be syntactically set-multilinear on `S`: subformulas that compute zero
or are not set-multilinear on their target block set are pruned to `SPFormula.zero`. -/
noncomputable def normalizeSetMultilinear [CommSemiring K] (blk : Fin n → Fin d) :
    Finset (Fin d) → SPFormula K n → SPFormula K n
  | S, .input i =>
      letI := Classical.dec ((X i : MvPolynomial (Fin n) K) = 0 ∨
        ¬ MvPolynomial.IsSetMultilinear blk S (X i : MvPolynomial (Fin n) K))
      if (X i : MvPolynomial (Fin n) K) = 0 ∨
          ¬ MvPolynomial.IsSetMultilinear blk S (X i : MvPolynomial (Fin n) K) then
        zero
      else .input i
  | S, .gate (.const a) _ =>
      letI := Classical.dec ((C a : MvPolynomial (Fin n) K) = 0 ∨
        ¬ MvPolynomial.IsSetMultilinear blk S (C a : MvPolynomial (Fin n) K))
      if (C a : MvPolynomial (Fin n) K) = 0 ∨
          ¬ MvPolynomial.IsSetMultilinear blk S (C a : MvPolynomial (Fin n) K) then
        zero
      else const a
  | S, .gate (.add _ c) args =>
      letI := Classical.dec ((add c args).polynomial = 0 ∨
        ¬ MvPolynomial.IsSetMultilinear blk S (add c args).polynomial)
      if (add c args).polynomial = 0 ∨
          ¬ MvPolynomial.IsSetMultilinear blk S (add c args).polynomial then
        zero
      else add c fun j => normalizeSetMultilinear blk S (args j)
  | S, .gate (.mul _) args =>
      letI := Classical.dec ((mul args).polynomial = 0 ∨
        ¬ MvPolynomial.IsSetMultilinear blk S (mul args).polynomial)
      if (mul args).polynomial = 0 ∨
          ¬ MvPolynomial.IsSetMultilinear blk S (mul args).polynomial then
        zero
      else mul fun j => normalizeSetMultilinear blk (chosenBlockSet blk (args j)) (args j)

private theorem normalizeSetMultilinear_of_zero_or_not [CommSemiring K] {blk : Fin n → Fin d}
    {S : Finset (Fin d)} {F : SPFormula K n}
    (h : F.polynomial = 0 ∨ ¬ MvPolynomial.IsSetMultilinear blk S F.polynomial) :
    F.normalizeSetMultilinear blk S = zero := by
  cases F with
  | input i =>
    unfold normalizeSetMultilinear
    exact ite_eq_left h
  | gate op args =>
    cases op with
    | const a =>
      unfold normalizeSetMultilinear
      exact ite_eq_left h
    | add m c =>
      unfold normalizeSetMultilinear
      exact ite_eq_left h
    | mul m =>
      unfold normalizeSetMultilinear
      exact ite_eq_left h

/-- Normalization never increases the node count. -/
theorem nodeCount_normalizeSetMultilinear_le [CommSemiring K] (blk : Fin n → Fin d)
    (S : Finset (Fin d)) (F : SPFormula K n) :
    (F.normalizeSetMultilinear blk S).nodeCount ≤ F.nodeCount := by
  induction F generalizing S with
  | input i =>
    unfold normalizeSetMultilinear
    split_ifs <;> simp
  | gate op args ih =>
    cases op with
    | const a =>
      unfold normalizeSetMultilinear
      split_ifs <;> simp [Formula.nodeCount_gate]
    | add m c =>
      unfold normalizeSetMultilinear
      split_ifs
      · exact Formula.nodeCount_pos _
      · rw [Formula.nodeCount_gate, Formula.nodeCount_gate]
        exact Nat.add_le_add_right (sum_le_sum fun j _ => ih j S) 1
    | mul m =>
      unfold normalizeSetMultilinear
      split_ifs
      · exact Formula.nodeCount_pos _
      · rw [Formula.nodeCount_gate, Formula.nodeCount_gate]
        exact Nat.add_le_add_right (sum_le_sum fun j _ => ih j _) 1

/-- Normalization never increases the product-depth. -/
theorem productDepth_normalizeSetMultilinear_le [CommSemiring K] (blk : Fin n → Fin d)
    (S : Finset (Fin d)) (F : SPFormula K n) :
    (F.normalizeSetMultilinear blk S).productDepth ≤ F.productDepth := by
  induction F generalizing S with
  | input i =>
    unfold normalizeSetMultilinear
    split_ifs
    · rw [productDepth_zero]; exact Nat.zero_le _
    · exact le_rfl
  | gate op args ih =>
    cases op with
    | const a =>
      unfold normalizeSetMultilinear
      split_ifs
      · rw [productDepth_zero]; exact Nat.zero_le _
      · rw [productDepth_const]; exact Nat.zero_le _
    | add m c =>
      unfold normalizeSetMultilinear
      split_ifs
      · rw [productDepth_zero]; exact Nat.zero_le _
      · rw [productDepth_add, productDepth_add]
        exact Finset.sup_mono_fun fun j _ => ih j S
    | mul m =>
      unfold normalizeSetMultilinear
      split_ifs
      · rw [productDepth_zero]; exact Nat.zero_le _
      · rw [productDepth_mul, productDepth_mul]
        exact Nat.add_le_add_right (Finset.sup_mono_fun fun j _ => ih j _) 1

/-- The normalized formula of a semantically set-multilinear formula is syntactically
set-multilinear on `S`. -/
theorem isSetMultilinear_normalizeSetMultilinear [CommSemiring K] {blk : Fin n → Fin d}
    {F : SPFormula K n} (hF : F.IsSemanticallySetMultilinear blk) (S : Finset (Fin d)) :
    (F.normalizeSetMultilinear blk S).IsSetMultilinear blk S := by
  induction F generalizing S with
  | input i =>
    unfold normalizeSetMultilinear
    split_ifs with h
    · exact isSetMultilinear_zero S
    · push Not at h
      have hS : S = {blk i} :=
        isSetMultilinear_eq_of_ne_zero h.1 h.2 (isSetMultilinear_X blk i)
      exact hS ▸ .input i
  | gate op args ih =>
    cases op with
    | const a =>
      unfold normalizeSetMultilinear
      split_ifs with h
      · exact isSetMultilinear_zero S
      · push Not at h
        have hS : S = ∅ :=
          isSetMultilinear_eq_of_ne_zero h.1 h.2 (isSetMultilinear_C blk a)
        exact hS ▸ .const a
    | add m c =>
      unfold normalizeSetMultilinear
      split_ifs with h
      · exact isSetMultilinear_zero S
      · exact .add c _ S fun j => ih j (hF.2 j) S
    | mul m =>
      unfold normalizeSetMultilinear
      split_ifs with h
      · exact isSetMultilinear_zero S
      · push Not at h
        have hT : ∀ j, MvPolynomial.IsSetMultilinear blk
            (chosenBlockSet blk (args j)) (SPFormula.polynomial (args j)) :=
          fun j => isSetMultilinear_chosenBlockSet (hF.2 j)
        obtain ⟨hdisj, hunion⟩ :=
          prod_blockSplits_of_ne_zero (by simpa [polynomial_mul] using h.1)
            (by simpa [polynomial_mul] using h.2) hT
        exact hunion ▸ .mul _ _ hdisj fun j => ih j (hF.2 j) (chosenBlockSet blk (args j))

/-- The normalized formula computes the same polynomial when `F` is semantically set-multilinear
and its output polynomial is set-multilinear on `S`. -/
theorem polynomial_normalizeSetMultilinear [CommSemiring K] {blk : Fin n → Fin d}
    {F : SPFormula K n} (hF : F.IsSemanticallySetMultilinear blk) {S : Finset (Fin d)}
    (hS : MvPolynomial.IsSetMultilinear blk S F.polynomial) :
    (F.normalizeSetMultilinear blk S).polynomial = F.polynomial := by
  induction F generalizing S with
  | input i =>
    unfold normalizeSetMultilinear
    split_ifs with h
    · rcases h with h0 | hnot
      · rw [polynomial_zero, polynomial_input, h0]
      · exact absurd hS hnot
    · rfl
  | gate op args ih =>
    cases op with
    | const a =>
      unfold normalizeSetMultilinear
      split_ifs with h
      · rcases h with h0 | hnot
        · rw [polynomial_zero]; exact h0.symm
        · exact absurd hS hnot
      · rfl
    | add m c =>
      unfold normalizeSetMultilinear
      split_ifs with h
      · rcases h with h0 | hnot
        · rw [polynomial_zero, h0]
        · exact absurd hS hnot
      · rw [polynomial_add]
        have hterm (j : Fin m) :
            (normalizeSetMultilinear blk S (args j)).polynomial =
              smProj blk S (SPFormula.polynomial (args j)) := by
          by_cases hj : MvPolynomial.IsSetMultilinear blk S (SPFormula.polynomial (args j))
          · rw [ih j (hF.2 j) hj, hj.smProj_eq_self]
          · rw [normalizeSetMultilinear_of_zero_or_not (Or.inr hj), polynomial_zero]
            obtain ⟨T, hT⟩ := (hF.2 j).exists_isSetMultilinear
            have hST : S ≠ T := fun heq => hj (heq ▸ hT)
            exact (hT.smProj_eq_zero hST).symm
        calc ∑ j, C (c j) * (normalizeSetMultilinear blk S (args j)).polynomial
            = ∑ j, C (c j) * smProj blk S (SPFormula.polynomial (args j)) :=
              sum_congr rfl fun j _ => by rw [hterm j]
          _ = smProj blk S (∑ j, C (c j) * SPFormula.polynomial (args j)) := by
              rw [map_sum]
              exact sum_congr rfl fun j _ => (smProj_C_mul (c j)).symm
          _ = (add c args).polynomial := by
              rw [← polynomial_add, hS.smProj_eq_self]
    | mul m =>
      unfold normalizeSetMultilinear
      split_ifs with h
      · rcases h with h0 | hnot
        · rw [polynomial_zero, h0]
        · exact absurd hS hnot
      · rw [polynomial_mul, polynomial_mul]
        exact prod_congr rfl fun j _ =>
          ih j (hF.2 j) (isSetMultilinear_chosenBlockSet (hF.2 j))

/-- Flattening preserves syntactic set-multilinearity. -/
theorem IsSetMultilinear.flatten [Semiring K] {blk : Fin n → Fin d} {F : SPFormula K n}
    {S : Finset (Fin d)} (hF : F.IsSetMultilinear blk S) :
    F.flatten.IsSetMultilinear blk S := by
  classical
  have hsupp : ∀ {G : SPFormula K n} {T : Finset (Fin d)},
      G.IsSetMultilinear blk T → ∀ H ∈ (linComb G).support, H.IsSetMultilinear blk T := by
    intro G T hG
    induction hG with
    | input i =>
      intro H hH
      rw [linComb_input] at hH
      rw [mem_singleton.1 (Finsupp.support_single_subset hH)]
      exact .input i
    | const a =>
      intro H hH
      rw [linComb_const] at hH
      rw [mem_singleton.1 (Finsupp.support_single_subset hH)]
      exact .const a
    | add c G T _ ih =>
      intro H hH
      rw [linComb_add] at hH
      obtain ⟨j, -, hj⟩ := mem_biUnion.1 (Finsupp.support_finsetSum hH)
      exact ih j H (Finsupp.support_smul hj)
    | mul G U hU _ ih =>
      intro H hH
      rw [linComb_mul] at hH
      rw [mem_singleton.1 (Finsupp.support_single_subset hH)]
      refine .mul _ U hU fun j => ?_
      exact .add _ _ (U j) fun k => ih j _ ((linComb (G j)).support.equivFin.symm k).2
  exact .add _ _ S fun k => hsupp hF _ ((linComb F).support.equivFin.symm k).2

/-- A semantically set-multilinear formula whose renamed polynomial equals `imm K n d`
automatically has its polynomial set-multilinear on all `d` blocks. -/
theorem IsSemanticallySetMultilinear.isSetMultilinear_univ_of_rename_imm [CommSemiring K]
    [Nontrivial K] {m : ℕ} [NeZero m] (e : Fin n → Fin d × Fin m × Fin m)
    {F : SPFormula K n} (hF : F.IsSemanticallySetMultilinear (fun v => (e v).1))
    (hFP : rename e F.polynomial = imm K m d) :
    MvPolynomial.IsSetMultilinear (fun v => (e v).1) univ F.polynomial := by
  obtain ⟨S, hS⟩ := hF.exists_isSetMultilinear
  have hren : MvPolynomial.IsSetMultilinear Prod.fst S (imm K m d) :=
    hFP ▸ isSetMultilinear_rename e (fun _ => rfl) hS
  have himm : MvPolynomial.IsSetMultilinear Prod.fst univ (imm K m d) :=
    smProj_eq_self_iff.1 smProj_imm
  have hSuniv : S = univ :=
    isSetMultilinear_eq_of_ne_zero (imm_ne_zero K m d) hren himm
  exact hSuniv ▸ hS

end SPFormula

namespace SPCircuit

variable {N : ℕ}

/-- A circuit is **semantically set-multilinear** with respect to `blk` when every internal gate
computes a set-multilinear polynomial on some subset of blocks (inputs are automatically
set-multilinear on their own blocks). -/
@[expose] def IsSemanticallySetMultilinear [CommSemiring K] (blk : Fin N → Fin d)
    (C : SPCircuit K N) : Prop :=
  ∀ k : Fin C.size, ∃ S : Finset (Fin d),
    MvPolynomial.IsSetMultilinear blk S
      (C.program.eval (sigmaPiInterpretationWith K MvPolynomial.C) MvPolynomial.X k)

/-- The circuit of a semantically set-multilinear formula is semantically set-multilinear. -/
theorem isSemanticallySetMultilinear_toCircuit [CommSemiring K] {blk : Fin N → Fin d}
    {F : SPFormula K N} (hF : F.IsSemanticallySetMultilinear blk) :
    SPCircuit.IsSemanticallySetMultilinear blk F.toCircuit := by
  intro k
  have hclosed : ∀ (op : SigmaPiOp K) (args : Fin op.arity → SPFormula K N) (j : Fin op.arity),
      SPFormula.IsSemanticallySetMultilinear blk (.gate op args) →
      SPFormula.IsSemanticallySetMultilinear blk (args j) := by
    intro op args j h
    cases op with
    | const _ => exact j.elim0
    | add _ _ => exact h.2 j
    | mul _ => exact h.2 j
  have hk := Formula.gateFormula_toCircuit_of_closed
    (SPFormula.IsSemanticallySetMultilinear blk) hclosed hF k
  obtain ⟨S, hS⟩ := hk.exists_isSetMultilinear
  refine ⟨S, ?_⟩
  simpa [SPFormula.polynomial, Program.eval_gateFormula] using hS

/-- Every wire of a semantically set-multilinear circuit unfolds to a semantically
set-multilinear formula. -/
theorem isSemanticallySetMultilinear_wireFormula [CommSemiring K] {blk : Fin N → Fin d}
    {C : SPCircuit K N} (hC : C.IsSemanticallySetMultilinear blk) (w : Wire N C.size) :
    SPFormula.IsSemanticallySetMultilinear blk (C.program.wireFormula w) := by
  suffices h : ∀ (F : SPFormula K N),
      (∃ w : Wire N C.size, C.program.wireFormula w = F) →
      F.IsSemanticallySetMultilinear blk from h _ ⟨w, rfl⟩
  intro F
  induction F with
  | input _ => intro _; trivial
  | gate op args ih =>
    rintro ⟨w, hw⟩
    have hchild : ∀ j, SPFormula.IsSemanticallySetMultilinear blk (args j) := fun j =>
      ih j (C.program.exists_wireFormula_eq_of_eq_gate hw j)
    cases op with
    | const _ => trivial
    | add m c =>
      refine ⟨?_, hchild⟩
      cases w with
      | input _ => cases hw
      | gate k =>
        obtain ⟨S, hS⟩ := hC k
        refine ⟨S, ?_⟩
        rw [Program.wireFormula_gate] at hw
        simpa [← hw, SPFormula.polynomial, Program.eval_gateFormula] using hS
    | mul m =>
      refine ⟨?_, hchild⟩
      cases w with
      | input _ => cases hw
      | gate k =>
        obtain ⟨S, hS⟩ := hC k
        refine ⟨S, ?_⟩
        rw [Program.wireFormula_gate] at hw
        simpa [← hw, SPFormula.polynomial, Program.eval_gateFormula] using hS

/-- A simple semantically set-multilinear circuit computing a polynomial set-multilinear on `S`
unfolds, normalizes, and flattens to a syntactically set-multilinear formula on `S` of no larger
product-depth and at most `(C.size + N + 2) ^ (2 * C.productDepth + 1)` nodes. -/
theorem exists_setMultilinear_formula [CommSemiring K] {blk : Fin N → Fin d}
    {C : SPCircuit K N} (hsim : C.IsSimple) (hsem : C.IsSemanticallySetMultilinear blk)
    {S : Finset (Fin d)} (hS : MvPolynomial.IsSetMultilinear blk S C.polynomial) :
    ∃ G : SPFormula K N,
      G.IsSetMultilinear blk S ∧
      G.polynomial = C.polynomial ∧
      G.productDepth ≤ C.productDepth ∧
      G.nodeCount ≤ (C.size + N + 2) ^ (2 * C.productDepth + 1) := by
  classical
  let F₀ : SPFormula K N := C.toFormula 0
  let Fnorm : SPFormula K N := F₀.normalizeSetMultilinear blk S
  let G : SPFormula K N := Fnorm.flatten
  have hF₀sem : F₀.IsSemanticallySetMultilinear blk :=
    isSemanticallySetMultilinear_wireFormula hsem (C.outputs 0)
  have hF₀poly : F₀.polynomial = C.polynomial := polynomial_toFormula C
  have hnorm_sm : Fnorm.IsSetMultilinear blk S :=
    SPFormula.isSetMultilinear_normalizeSetMultilinear hF₀sem S
  have hnorm_poly : Fnorm.polynomial = C.polynomial :=
    (SPFormula.polynomial_normalizeSetMultilinear hF₀sem (hF₀poly.symm ▸ hS)).trans hF₀poly
  have hnorm_depth : Fnorm.productDepth ≤ C.productDepth :=
    (SPFormula.productDepth_normalizeSetMultilinear_le blk S F₀).trans
      (C.depthWith_toFormula_le 0 _)
  -- Build a small closed finset of formulas containing `Fnorm`.
  set W : Finset (SPFormula K N) := univ.image C.program.wireFormula
  set normOf : SPFormula K N → SPFormula K N :=
    fun H => H.normalizeSetMultilinear blk (SPFormula.chosenBlockSet blk H)
  set Sn : Finset (SPFormula K N) := insert SPFormula.zero (W.image normOf)
  have hnorm_mem_Sn : ∀ H ∈ W, ∀ T : Finset (Fin d),
      H.normalizeSetMultilinear blk T ∈ Sn := by
    intro H hH T
    by_cases h0 : H.polynomial = 0 ∨ ¬ MvPolynomial.IsSetMultilinear blk T H.polynomial
    · rw [SPFormula.normalizeSetMultilinear_of_zero_or_not h0]
      exact mem_insert_self _ _
    · push Not at h0
      have hTeq : T = SPFormula.chosenBlockSet blk H :=
        (SPFormula.chosenBlockSet_eq_of_ne_zero h0.1 h0.2).symm
      rw [hTeq]
      exact mem_insert_of_mem (mem_image_of_mem normOf hH)
  have hWclosed : ∀ op args, Formula.gate op args ∈ W → ∀ j, args j ∈ W := by
    intro op args h j
    obtain ⟨w, -, hw⟩ := mem_image.1 h
    obtain ⟨w', hw'⟩ := C.program.exists_wireFormula_eq_of_eq_gate hw j
    exact mem_image.2 ⟨w', mem_univ _, hw'⟩
  have hWmul : ∀ m args, Formula.gate (SigmaPiOp.mul m) args ∈ W → m ≤ C.size + N := by
    intro m args h
    obtain ⟨w, -, hw⟩ := mem_image.1 h
    cases w with
    | input _ => cases hw
    | gate k =>
      rw [Program.wireFormula_gate, C.program.gateFormula_eq_gate] at hw
      have hop : (C.program.lines k).op = .mul m := (Formula.gate.inj hw).1
      have hcard := Fintype.card_le_of_injective _ (hsim k m hop)
      rw [Fintype.card_fin, Wire.card, hop] at hcard
      exact (show m ≤ N + C.size from hcard).trans_eq (Nat.add_comm _ _)
  have hSn_closed : ∀ op args, Formula.gate op args ∈ Sn → ∀ j, args j ∈ Sn := by
    intro op args h j
    rcases mem_insert.1 h with hzero | hmem
    · change Formula.gate op args =
        Formula.gate (SigmaPiOp.add 0 Fin.elim0) Fin.elim0 at hzero
      cases hzero
      exact j.elim0
    · obtain ⟨H, hHW, hHeq⟩ := mem_image.1 hmem
      cases H with
      | input i =>
        dsimp only [normOf, SPFormula.normalizeSetMultilinear] at hHeq
        split_ifs at hHeq; cases hHeq
        exact j.elim0
      | gate op' args' =>
        cases op' with
        | const a =>
          dsimp only [normOf, SPFormula.normalizeSetMultilinear] at hHeq
          split_ifs at hHeq <;> (cases hHeq; exact j.elim0)
        | add m c =>
          dsimp only [normOf, SPFormula.normalizeSetMultilinear] at hHeq
          split_ifs at hHeq
          · cases hHeq; exact j.elim0
          · cases hHeq
            exact hnorm_mem_Sn _ (hWclosed _ _ hHW j) _
        | mul m =>
          dsimp only [normOf, SPFormula.normalizeSetMultilinear] at hHeq
          split_ifs at hHeq
          · cases hHeq; exact j.elim0
          · cases hHeq
            exact hnorm_mem_Sn _ (hWclosed _ _ hHW j) _
  have hSn_card : Sn.card ≤ C.size + N + 1 := by
    calc Sn.card ≤ (W.image normOf).card + 1 := card_insert_le _ _
      _ ≤ W.card + 1 := Nat.add_le_add_right card_image_le 1
      _ ≤ (C.size + N) + 1 := Nat.add_le_add_right
          (card_image_le.trans (by rw [card_univ, Wire.card, Nat.add_comm])) 1
  have hSn_mul : ∀ m args, Formula.gate (SigmaPiOp.mul m) args ∈ Sn → m ≤ C.size + N + 1 := by
    intro m args h
    rcases mem_insert.1 h with hzero | hmem
    · cases hzero
    · obtain ⟨H, hHW, hHeq⟩ := mem_image.1 hmem
      cases H with
      | input i =>
        dsimp only [normOf, SPFormula.normalizeSetMultilinear] at hHeq
        split_ifs at hHeq; cases hHeq
      | gate op' args' =>
        cases op' with
        | const a =>
          dsimp only [normOf, SPFormula.normalizeSetMultilinear] at hHeq
          split_ifs at hHeq <;> cases hHeq
        | add m' c =>
          dsimp only [normOf, SPFormula.normalizeSetMultilinear] at hHeq
          split_ifs at hHeq <;> cases hHeq
        | mul m' =>
          dsimp only [normOf, SPFormula.normalizeSetMultilinear] at hHeq
          split_ifs at hHeq
          · cases hHeq
          · cases hHeq
            exact (hWmul m' args' hHW).trans (Nat.le_succ _)
  have hFnorm_mem : Fnorm ∈ Sn :=
    hnorm_mem_Sn F₀ (mem_image.2 ⟨C.outputs 0, mem_univ _, rfl⟩) S
  have hG_nodes : G.nodeCount ≤ (C.size + N + 2) ^ (2 * C.productDepth + 1) := by
    refine (SPFormula.nodeCount_flatten_le hSn_closed hSn_card hSn_mul hFnorm_mem).trans ?_
    exact Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  exact ⟨G, hnorm_sm.flatten, (SPFormula.polynomial_flatten Fnorm).trans hnorm_poly,
    (SPFormula.productDepth_flatten_le Fnorm).trans hnorm_depth, hG_nodes⟩

end SPCircuit

end SemanticNormalization

/-! ### : Subcube imbalance and unbiased two-letter words -/

section SubcubeImbalance

variable {σ K : Type*} {d : ℕ}

/-- A word `w : Fin d → ℤ` has **`(τ, c)`-subcube imbalance** when every subset `T` of at most
`τ` blocks has absolute weight sum at least `|T| * c`. -/
@[expose] def HasSubcubeImbalance (w : Fin d → ℤ) (τ c : ℝ) : Prop :=
  ∀ T : Finset (Fin d), (T.card : ℝ) ≤ τ → (T.card : ℝ) * c ≤ |∑ i ∈ T, (w i : ℝ)|

/-- Subcube imbalance directly upper-bounds the relative rank on every subset of at most `τ`
blocks. -/
theorem relRank_le_two_rpow_of_subcubeImbalance [Fintype σ] [Field K] {blk : σ → Fin d}
    {w : Fin d → ℤ} {τ c : ℝ}
    (hblk : ∀ i, Fintype.card {x : σ // blk x = i} = 2 ^ (w i).natAbs)
    (himb : HasSubcubeImbalance w τ c) {T : Finset (Fin d)} (hT : (T.card : ℝ) ≤ τ)
    (f : MvPolynomial σ K) :
    relRank blk (wordPos w ∩ T) (wordNeg w ∩ T) f ≤ 2 ^ (-((T.card : ℝ) * (c / 2))) := by
  refine (relRank_le_two_rpow_abs_sum w hblk T f).trans
    (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
  have h1 := himb T hT
  linarith

/-- **Subcube imbalance for two-letter words**: if every letter of `w` lies in `{k - r, -k}`
with `2 * ℓ * r ≤ k`, then every subset `T` of at most `ℓ` blocks has
`|∑ i ∈ T, w i| ≥ |T| * (r / 2)`. -/
theorem hasSubcubeImbalance_twoLetter {k r ℓ : ℕ} {w : Fin d → ℤ}
    (hw : ∀ i, w i = (k : ℤ) - r ∨ w i = -(k : ℤ)) (hkr : 2 * ℓ * r ≤ k) :
    HasSubcubeImbalance w ℓ ((r : ℝ) / 2) := by
  intro T hT
  classical
  have hTnat : T.card ≤ ℓ := by exact_mod_cast hT
  set Tn := T.filter fun i => w i = -(k : ℤ)
  set Tp := T.filter fun i => ¬ w i = -(k : ℤ)
  have hab : Tn.card + Tp.card = T.card := card_filter_add_card_filter_not _
  have h1 : ∑ i ∈ Tn, (w i : ℝ) = Tn.card * (-(k : ℝ)) := by
    calc ∑ i ∈ Tn, (w i : ℝ) = ∑ _i ∈ Tn, (-(k : ℝ)) :=
          sum_congr rfl fun i hi => by simp [(mem_filter.1 hi).2]
      _ = Tn.card * (-(k : ℝ)) := by rw [sum_const, nsmul_eq_mul]
  have h2 : ∑ i ∈ Tp, (w i : ℝ) = Tp.card * ((k : ℝ) - r) := by
    calc ∑ i ∈ Tp, (w i : ℝ) = ∑ _i ∈ Tp, ((k : ℝ) - r) :=
          sum_congr rfl fun i hi => by
            rw [(hw i).resolve_right (mem_filter.1 hi).2]
            push_cast
            rfl
      _ = Tp.card * ((k : ℝ) - r) := by rw [sum_const, nsmul_eq_mul]
  have hsum : ∑ i ∈ T, (w i : ℝ) =
      ((Tp.card : ℝ) - Tn.card) * k - (Tp.card : ℝ) * r := by
    rw [← sum_filter_add_sum_filter_not T (fun i => w i = -(k : ℤ))]
    change ∑ i ∈ Tn, (w i : ℝ) + ∑ i ∈ Tp, (w i : ℝ) = _
    rw [h1, h2]
    ring
  rw [hsum]
  have hkrR : 2 * (ℓ : ℝ) * (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkr
  have hTp : (Tp.card : ℝ) ≤ ℓ := by exact_mod_cast (show Tp.card ≤ ℓ by omega)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hTcardR : (T.card : ℝ) = (Tn.card : ℝ) + (Tp.card : ℝ) := by exact_mod_cast hab.symm
  by_cases hEq : Tp.card = Tn.card
  · have hEqR : (Tp.card : ℝ) = Tn.card := by exact_mod_cast hEq
    rw [hEqR, sub_self, zero_mul, zero_sub, abs_neg,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hr0)]
    exact le_of_eq (by rw [hTcardR, hEqR]; ring)
  · have hdiff : (1 : ℝ) ≤ |(Tp.card : ℝ) - Tn.card| := by
      have hne : (Tp.card : ℤ) - Tn.card ≠ 0 := by omega
      exact_mod_cast Int.one_le_abs hne
    have hk_le : (k : ℝ) ≤ |((Tp.card : ℝ) - Tn.card) * k| := by
      rw [abs_mul, abs_of_nonneg (a := (k : ℝ)) (Nat.cast_nonneg k)]
      nlinarith
    have hrev : |((Tp.card : ℝ) - Tn.card) * k| - |(Tp.card : ℝ) * r| ≤
        |((Tp.card : ℝ) - Tn.card) * k - (Tp.card : ℝ) * r| :=
      abs_sub_abs_le_abs_sub _ _
    have hpr : |(Tp.card : ℝ) * r| = (Tp.card : ℝ) * r :=
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hr0)
    have hpr_le : (Tp.card : ℝ) * r ≤ (ℓ : ℝ) * r := mul_le_mul_of_nonneg_right hTp hr0
    have hTr_le : (T.card : ℝ) * ((r : ℝ) / 2) ≤ (ℓ : ℝ) * r := by nlinarith
    linarith

/-- The `√2`-alphabet word satisfies subcube imbalance on every cutoff `τ > 0` with
`10 * τ ^ 2 ≤ k`. -/
theorem hasSubcubeImbalance_sqrtTwoWord {k : ℕ} {τ : ℝ} (hτ : 0 < τ) (hk : 10 * τ ^ 2 ≤ k) :
    HasSubcubeImbalance (sqrtTwoWord k d) τ ((k : ℝ) / (10 * τ ^ 2)) := by
  intro T hT
  classical
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hw := sqrtTwoWord_eq_or (d := d) k
    set Tn := T.filter fun i => sqrtTwoWord k d i = -(k : ℤ)
    set Tp := T.filter fun i => ¬ sqrtTwoWord k d i = -(k : ℤ)
    have hab : Tn.card + Tp.card = T.card := card_filter_add_card_filter_not _
    have h1 : ∑ i ∈ Tn, (sqrtTwoWord k d i : ℝ) = Tn.card * (-(k : ℝ)) := by
      calc ∑ i ∈ Tn, (sqrtTwoWord k d i : ℝ) = ∑ _i ∈ Tn, (-(k : ℝ)) :=
            sum_congr rfl fun i hi => by simp [(mem_filter.1 hi).2]
        _ = Tn.card * (-(k : ℝ)) := by rw [sum_const, nsmul_eq_mul]
    have h2 : ∑ i ∈ Tp, (sqrtTwoWord k d i : ℝ) =
        Tp.card * ((⌊(k : ℝ) / √2⌋ : ℤ) : ℝ) := by
      calc ∑ i ∈ Tp, (sqrtTwoWord k d i : ℝ) =
            ∑ _i ∈ Tp, ((⌊(k : ℝ) / √2⌋ : ℤ) : ℝ) :=
            sum_congr rfl fun i hi => by
              rw [(hw i).resolve_right (mem_filter.1 hi).2]
        _ = Tp.card * ((⌊(k : ℝ) / √2⌋ : ℤ) : ℝ) := by rw [sum_const, nsmul_eq_mul]
    have hsum : ∑ i ∈ T, (sqrtTwoWord k d i : ℝ) =
        Tp.card * ((⌊(k : ℝ) / √2⌋ : ℤ) : ℝ) + Tn.card * (-(k : ℝ)) := by
      rw [← sum_filter_add_sum_filter_not T (fun i => sqrtTwoWord k d i = -(k : ℤ))]
      change ∑ i ∈ Tn, (sqrtTwoWord k d i : ℝ) + ∑ i ∈ Tp, (sqrtTwoWord k d i : ℝ) = _
      rw [h1, h2, add_comm]
    rw [hsum]
    have hab' : (Tp.card : ℤ) ≠ 0 ∨ (Tn.card : ℤ) ≠ 0 := by
      have hpos : 0 < T.card := hne.card_pos
      omega
    have h17 := one_div_le_abs_div_sqrt_two_sub hab'
    push_cast at h17
    have hs2 : (4 : ℝ) / 3 ≤ √2 := by nlinarith [Real.sq_sqrt zero_le_two, Real.sqrt_nonneg 2]
    have hs2pos : 0 < √2 := by positivity
    have haτ : (Tp.card : ℝ) ≤ τ :=
      le_trans (by exact_mod_cast (hab ▸ Nat.le_add_left Tp.card Tn.card)) hT
    have hτ1 : 1 ≤ τ := le_trans (by exact_mod_cast hne.card_pos) hT
    have ha0 : (0 : ℝ) ≤ Tp.card := Nat.cast_nonneg _
    have hxa : (Tp.card : ℝ) / √2 ≤ 3 / 4 * Tp.card := (div_le_iff₀ hs2pos).2 (by nlinarith)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Tp.card / √2)] at h17
    have hden : 4 * ((Tp.card : ℝ) / √2) + 2 ≤ 5 * τ := by linarith
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hA : 2 * ((k : ℝ) / (10 * τ)) ≤ k * |(Tp.card : ℝ) / √2 - Tn.card| := by
      calc 2 * ((k : ℝ) / (10 * τ)) = k / (5 * τ) := by ring
        _ ≤ k / (4 * ((Tp.card : ℝ) / √2) + 2) := by gcongr
        _ ≤ k * |(Tp.card : ℝ) / √2 - Tn.card| :=
          div_eq_mul_one_div (k : ℝ) _ ▸ mul_le_mul_of_nonneg_left h17 hk0
    set Fval : ℤ := ⌊(k : ℝ) / √2⌋
    have hF1 : (Fval : ℝ) ≤ k / √2 := Int.floor_le _
    have hF2 : (k : ℝ) / √2 < Fval + 1 := Int.lt_floor_add_one _
    have hB : (k : ℝ) * |(Tp.card : ℝ) / √2 - Tn.card| - Tp.card ≤
        |Tp.card * (Fval : ℝ) + Tn.card * -(k : ℝ)| := by
      have e : (Tp.card : ℝ) * Fval + Tn.card * -(k : ℝ) =
          k * ((Tp.card : ℝ) / √2 - Tn.card) - Tp.card * (k / √2 - Fval) := by ring
      have h0 : |(Tp.card : ℝ) * (k / √2 - Fval)| ≤ Tp.card := by
        rw [abs_of_nonneg (mul_nonneg ha0 (by linarith))]; nlinarith
      rw [e]
      calc (k : ℝ) * |(Tp.card : ℝ) / √2 - Tn.card| - Tp.card
          ≤ |(k : ℝ) * ((Tp.card : ℝ) / √2 - Tn.card)| -
              |(Tp.card : ℝ) * (k / √2 - Fval)| := by
            rw [abs_mul, abs_of_nonneg hk0]; linarith
        _ ≤ _ := abs_sub_abs_le_abs_sub _ _
    have hτk : τ ≤ k / (10 * τ) := (le_div_iff₀ (by positivity)).2 (by nlinarith)
    have hlow : (k : ℝ) / (10 * τ) ≤ |Tp.card * (Fval : ℝ) + Tn.card * -(k : ℝ)| := by linarith
    have hTscale : (T.card : ℝ) * ((k : ℝ) / (10 * τ ^ 2)) ≤ (k : ℝ) / (10 * τ) := by
      calc (T.card : ℝ) * ((k : ℝ) / (10 * τ ^ 2))
          ≤ τ * ((k : ℝ) / (10 * τ ^ 2)) :=
            mul_le_mul_of_nonneg_right hT (by positivity)
        _ = (k : ℝ) / (10 * τ) := by field_simp
    exact hTscale.trans hlow

/-- The alternating `k`-unbiased word over `{k, -k}`, tailored to product-depth one. -/
@[expose] def altWord (k d : ℕ) : Fin d → ℤ :=
  greedyWord k k d

/-- Every letter of `altWord k d` has absolute value `k`. -/
theorem natAbs_altWord (k d : ℕ) (i : Fin d) : (altWord k d i).natAbs = k := by
  rcases greedyWord_eq_or (k : ℤ) (k : ℤ) i with h | h <;> simp [altWord, h]

/-- `altWord k d` is `k`-unbiased. -/
theorem isUnbiased_altWord (k d : ℕ) : IsUnbiased (altWord k d) k :=
  isUnbiased_greedyWord (Int.natCast_nonneg k) le_rfl

/-- The total sum of `altWord k d` has absolute value at most `k`. -/
theorem natAbs_sum_altWord_le (k d : ℕ) : (∑ i, altWord k d i).natAbs ≤ k := by
  simpa using isUnbiased_altWord k d d le_rfl

/-- The two-letter `k`-unbiased word over `{k - ⌊k / (2 ⌊√d⌋)⌋, -k}`, tailored to
product-depth two and yielding a square-root-in-`d` exponent. -/
@[expose] def sqrtStepWord (k d : ℕ) : Fin d → ℤ :=
  let r : ℕ := k / (2 * Nat.sqrt d)
  greedyWord ((k : ℤ) - r) k d

/-- Every letter of `sqrtStepWord k d` is `k - r` or `-k`, where `r = ⌊k / (2 ⌊√d⌋)⌋`. -/
theorem sqrtStepWord_eq_or (k d : ℕ) (i : Fin d) :
    sqrtStepWord k d i = (k : ℤ) - (k / (2 * Nat.sqrt d) : ℕ) ∨
      sqrtStepWord k d i = -(k : ℤ) :=
  greedyWord_eq_or _ _ i

/-- `sqrtStepWord k d` is `k`-unbiased whenever `1 ≤ d`. -/
theorem isUnbiased_sqrtStepWord {k d : ℕ} (_hd : 1 ≤ d) : IsUnbiased (sqrtStepWord k d) k := by
  have hr : k / (2 * Nat.sqrt d) ≤ k := Nat.div_le_self k _
  have hrZ : ((k / (2 * Nat.sqrt d) : ℕ) : ℤ) ≤ (k : ℤ) := Int.ofNat_le.2 hr
  have h0Z : (0 : ℤ) ≤ ((k / (2 * Nat.sqrt d) : ℕ) : ℤ) := Int.natCast_nonneg _
  exact isUnbiased_greedyWord (by linarith) (by linarith)

/-- The total sum of `sqrtStepWord k d` has absolute value at most `k` when `1 ≤ d`. -/
theorem natAbs_sum_sqrtStepWord_le {k d : ℕ} (hd : 1 ≤ d) :
    (∑ i, sqrtStepWord k d i).natAbs ≤ k := by
  simpa using isUnbiased_sqrtStepWord (k := k) hd d le_rfl

/-- Every letter of `sqrtStepWord k d` has magnitude at least `k / 2` when `1 ≤ d`. -/
theorem half_le_natAbs_sqrtStepWord {k d : ℕ} (hd : 1 ≤ d) (i : Fin d) :
    (k : ℝ) / 2 ≤ ((sqrtStepWord k d i).natAbs : ℝ) := by
  have hℓ : 1 ≤ Nat.sqrt d := Nat.le_sqrt.2 (by simpa using hd)
  set r := k / (2 * Nat.sqrt d)
  have h2r : 2 * r ≤ k := by
    calc 2 * r ≤ 2 * Nat.sqrt d * r :=
          Nat.mul_le_mul_right r (Nat.mul_le_mul_left 2 hℓ)
      _ ≤ k := Nat.mul_div_le k (2 * Nat.sqrt d)
  rcases sqrtStepWord_eq_or k d i with h | h
  · rw [h]
    have hsub : ((k : ℤ) - (r : ℤ)).natAbs = k - r := by omega
    rw [hsub]
    have hle : k ≤ 2 * (k - r) := by omega
    have hleR : (k : ℝ) ≤ 2 * ((k - r : ℕ) : ℝ) := by exact_mod_cast hle
    linarith
  · rw [h, Int.natAbs_neg, Int.natAbs_natCast]
    linarith [Nat.cast_nonneg (α := ℝ) k]

end SubcubeImbalance

/-! ### : Sharp relative-rank upper bounds for product-depth one and two -/

section LowDepthRank

variable {K : Type*} [Field K] {n d : ℕ} {blk : Fin n → Fin d}

/-- **Product-depth-one relative-rank upper bound**: if every letter of `w` has magnitude at
least `a ≥ 0` and block `i` has `2 ^ |w i|` variables, then every syntactically set-multilinear
formula on `S` of product-depth at most `1` satisfies
`relRank ≤ nodeCount · 2 ^ (-|S| · a / 2)`. -/
theorem SPFormula.IsSetMultilinear.relRank_polynomial_le_depthOne {w : Fin d → ℤ} {a : ℝ}
    (hblk : ∀ i, Fintype.card {x : Fin n // blk x = i} = 2 ^ (w i).natAbs)
    (hmin : ∀ i, a ≤ ((w i).natAbs : ℝ))
    {F : SPFormula K n} {S : Finset (Fin d)}
    (hF : F.IsSetMultilinear blk S) (hFΔ : F.productDepth ≤ 1) :
    relRank blk (wordPos w ∩ S) (wordNeg w ∩ S) F.polynomial ≤
      F.nodeCount * 2 ^ (-((S.card : ℝ) * (a / 2))) := by
  have hsmall (U : Finset (Fin d)) (hU : U.card ≤ 1) (f : MvPolynomial (Fin n) K) :
      relRank blk (wordPos w ∩ U) (wordNeg w ∩ U) f ≤ 2 ^ (-((U.card : ℝ) * (a / 2))) := by
    rcases U.eq_empty_or_nonempty with rfl | hne
    · simpa using relRank_le_one blk _ _ f
    · obtain ⟨i, rfl⟩ := card_eq_one.1 (le_antisymm hU hne.card_pos)
      refine (relRank_le_two_rpow_abs_sum w hblk {i} f).trans
        (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
      simp only [sum_singleton, card_singleton, Nat.cast_one, one_mul]
      have habs : ((w i).natAbs : ℝ) = |(w i : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      linarith [hmin i]
  refine SPFormula.relRank_polynomial_le_nodeCount_mul _ _ 1
    (fun U => 2 ^ (-((U.card : ℝ) * (a / 2)))) (fun _ => by positivity) hsmall ?_ hF hFΔ
  intro m G T hT hG hGΔ
  rw [SPFormula.polynomial_mul]
  refine (relRank_prod_le_two_rpow _ _ univ T _ (hT.set_pairwise _)
    (fun j _ => (hG j).isSetMultilinear_polynomial) (a / 2) fun j _ => ?_).trans ?_
  · rcases (hG j).card_le_one_or_polynomial_eq_zero (Nat.lt_one_iff.1 (hGΔ j)) with h | h
    · exact hsmall _ h _
    · rw [h, relRank_zero]
      positivity
  · have hnode : (1 : ℝ) ≤ (SPFormula.mul G).nodeCount := by
      exact_mod_cast Formula.nodeCount_pos (SPFormula.mul G)
    exact le_mul_of_one_le_left (by positivity) hnode

/-- **Product-depth-two relative-rank upper bound**: if every letter of `w` has magnitude at
least `a ≥ 0` and `w` has `(ℓ, c)`-subcube imbalance with `0 ≤ c ≤ a`, then every syntactically
set-multilinear formula on `S` of product-depth at most `2` satisfies
`relRank ≤ nodeCount · 2 ^ (- min ((ℓ + 1) * a / 2) (|S| * c / 2))`. -/
theorem SPFormula.IsSetMultilinear.relRank_polynomial_le_depthTwo {w : Fin d → ℤ} {ℓ : ℕ}
    {a c : ℝ} (ha : 0 ≤ a) (hca : c ≤ a)
    (hblk : ∀ i, Fintype.card {x : Fin n // blk x = i} = 2 ^ (w i).natAbs)
    (hmin : ∀ i, a ≤ ((w i).natAbs : ℝ))
    (himb : HasSubcubeImbalance w ℓ c)
    {F : SPFormula K n} {S : Finset (Fin d)}
    (hF : F.IsSetMultilinear blk S) (hFΔ : F.productDepth ≤ 2) :
    relRank blk (wordPos w ∩ S) (wordNeg w ∩ S) F.polynomial ≤
      F.nodeCount * 2 ^ (-min (((ℓ : ℝ) + 1) * (a / 2)) ((S.card : ℝ) * (c / 2))) := by
  let β : Finset (Fin d) → ℝ :=
    fun U => 2 ^ (-min (((ℓ : ℝ) + 1) * (a / 2)) ((U.card : ℝ) * (c / 2)))
  have hsmall (U : Finset (Fin d)) (hU : U.card ≤ 1) (f : MvPolynomial (Fin n) K) :
      relRank blk (wordPos w ∩ U) (wordNeg w ∩ U) f ≤ β U := by
    rcases U.eq_empty_or_nonempty with rfl | hne
    · have hmin0 : min (((ℓ : ℝ) + 1) * (a / 2)) 0 = 0 := min_eq_right (by positivity)
      simpa [β, hmin0] using relRank_le_one blk _ _ f
    · obtain ⟨i, rfl⟩ := card_eq_one.1 (le_antisymm hU hne.card_pos)
      refine (relRank_le_two_rpow_abs_sum w hblk {i} f).trans
        (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
      simp only [sum_singleton, card_singleton, Nat.cast_one, one_mul]
      have habs : ((w i).natAbs : ℝ) = |(w i : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      have hmin_le : min (((ℓ : ℝ) + 1) * (a / 2)) (c / 2) ≤ c / 2 := min_le_right _ _
      linarith [hmin i]
  refine SPFormula.relRank_polynomial_le_nodeCount_mul _ _ 2 β (fun _ => by positivity) hsmall
    ?_ hF hFΔ
  intro m G T hT hG hGΔ
  have hGp := fun j (_ : j ∈ (univ : Finset (Fin m))) => (hG j).isSetMultilinear_polynomial
  have hdisj := hT.set_pairwise (↑(univ : Finset (Fin m)))
  rw [SPFormula.polynomial_mul]
  by_cases hbig : ∃ j : Fin m, ℓ < (T j).card
  · obtain ⟨j, hj⟩ := hbig
    have hG1 : (G j).productDepth ≤ 1 := Nat.lt_succ_iff.1 (hGΔ j)
    refine (relRank_prod_le_of_mem _ _ T _ hdisj hGp (mem_univ j)).trans
      (((hG j).relRank_polynomial_le_depthOne hblk hmin hG1).trans ?_)
    refine mul_le_mul (by exact_mod_cast SPFormula.nodeCount_le_nodeCount_mul G j)
      (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) (by positivity) (by positivity)
    have hjR : (ℓ : ℝ) + 1 ≤ (T j).card := by exact_mod_cast (show ℓ + 1 ≤ (T j).card by omega)
    have h1 : min (((ℓ : ℝ) + 1) * (a / 2)) (((univ.biUnion T).card : ℝ) * (c / 2)) ≤
        ((ℓ : ℝ) + 1) * (a / 2) := min_le_left _ _
    have h2 : ((ℓ : ℝ) + 1) * (a / 2) ≤ (T j).card * (a / 2) :=
      mul_le_mul_of_nonneg_right hjR (by positivity)
    linarith
  · push Not at hbig
    refine (relRank_prod_le_two_rpow _ _ univ T _ hdisj hGp (c / 2) fun j _ =>
      relRank_le_two_rpow_of_subcubeImbalance hblk himb (by exact_mod_cast hbig j) _).trans ?_
    have hnode : (1 : ℝ) ≤ (SPFormula.mul G).nodeCount := by
      exact_mod_cast Formula.nodeCount_pos (SPFormula.mul G)
    refine (Real.rpow_le_rpow_of_exponent_le one_le_two ?_).trans
      (le_mul_of_one_le_left (by positivity) hnode)
    exact neg_le_neg (min_le_right _ _)

/-- **Specialization of the product-depth-two bound to `sqrtStepWord`**: for `1 ≤ d` and
`4 * Nat.sqrt d ≤ k`, every syntactically set-multilinear formula on all `d` blocks of
product-depth at most `2` has relative rank at most `nodeCount · 2 ^ (-k · √d / 12)`. -/
theorem SPFormula.IsSetMultilinear.relRank_polynomial_le_sqrtStepWord {k : ℕ}
    (hd : 1 ≤ d) (hk : 4 * Nat.sqrt d ≤ k)
    (hblk : ∀ i, Fintype.card {x : Fin n // blk x = i} = 2 ^ (sqrtStepWord k d i).natAbs)
    {F : SPFormula K n} (hF : F.IsSetMultilinear blk univ) (hFΔ : F.productDepth ≤ 2) :
    relRank blk (wordPos (sqrtStepWord k d)) (wordNeg (sqrtStepWord k d)) F.polynomial ≤
      F.nodeCount * 2 ^ (-((k : ℝ) * √(d : ℝ) / 12)) := by
  set ℓ := Nat.sqrt d
  set r := k / (2 * ℓ)
  have hℓpos : 1 ≤ ℓ := Nat.le_sqrt.2 (by simpa using hd)
  have hkr : 2 * ℓ * r ≤ k := Nat.mul_div_le k (2 * ℓ)
  have hr2 : 2 ≤ r := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have h3kr : k ≤ 3 * ℓ * r := by
    have hlt : k < 2 * ℓ * (r + 1) := Nat.lt_mul_div_succ k (by omega)
    have h23 : 2 * (r + 1) ≤ 3 * r := by omega
    have hmul : 2 * ℓ * (r + 1) ≤ 3 * ℓ * r := by
      calc 2 * ℓ * (r + 1) = ℓ * (2 * (r + 1)) := by ring
        _ ≤ ℓ * (3 * r) := Nat.mul_le_mul_left ℓ h23
        _ = 3 * ℓ * r := by ring
    omega
  have himb : HasSubcubeImbalance (sqrtStepWord k d) ℓ ((r : ℝ) / 2) :=
    hasSubcubeImbalance_twoLetter (sqrtStepWord_eq_or k d) hkr
  have h2r : 2 * r ≤ k :=
    (Nat.mul_le_mul_right r (Nat.mul_le_mul_left 2 hℓpos)).trans hkr
  have hca : (r : ℝ) / 2 ≤ (k : ℝ) / 2 := by
    have : (r : ℝ) ≤ k := by exact_mod_cast (show r ≤ k by omega)
    linarith
  have hbound := hF.relRank_polynomial_le_depthTwo (a := (k : ℝ) / 2) (c := (r : ℝ) / 2)
    (by positivity) hca hblk (half_le_natAbs_sqrtStepWord hd) himb hFΔ
  rw [inter_univ, inter_univ, card_univ, Fintype.card_fin] at hbound
  refine hbound.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) (Nat.cast_nonneg _))
  -- Show `k * √d / 12 ≤ min ((ℓ + 1) * (k / 4)) (d * (r / 4))`.
  have hℓle : (ℓ : ℝ) ≤ √(d : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast (by simpa [sq] using Nat.sqrt_le d : ℓ ^ 2 ≤ d)
  have hltℓ : √(d : ℝ) < (ℓ : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    exact_mod_cast (by simpa [sq, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt d : d < (ℓ + 1) ^ 2)
  have hleft : (k : ℝ) * √(d : ℝ) / 12 ≤ ((ℓ : ℝ) + 1) * ((k : ℝ) / 2 / 2) := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [Real.sqrt_nonneg (d : ℝ)]
  have hright : (k : ℝ) * √(d : ℝ) / 12 ≤ (d : ℝ) * ((r : ℝ) / 2 / 2) := by
    have hℓposR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
    have h3krR : (k : ℝ) ≤ 3 * (ℓ : ℝ) * (r : ℝ) := by exact_mod_cast h3kr
    have hsqd : (ℓ : ℝ) * √(d : ℝ) ≤ (d : ℝ) := by
      calc (ℓ : ℝ) * √(d : ℝ) ≤ √(d : ℝ) * √(d : ℝ) :=
            mul_le_mul_of_nonneg_right hℓle (Real.sqrt_nonneg _)
        _ = (d : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg d)
    have hmul : (ℓ : ℝ) * ((k : ℝ) * √(d : ℝ)) ≤ (ℓ : ℝ) * (3 * (d : ℝ) * (r : ℝ)) := by
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have hd0 : (0 : ℝ) ≤ √(d : ℝ) := Real.sqrt_nonneg _
      nlinarith
    have hcancel := le_of_mul_le_mul_left hmul hℓposR
    linarith
  exact neg_le_neg (le_min hleft hright)

end LowDepthRank

/-! ### : Lower bounds for semantically set-multilinear and unrestricted models -/

section SemanticAndSharpLowerBounds

variable {K : Type*} [Field K] {n d N : ℕ} [NeZero n]

/-- Helper transferring a formula relative-rank upper bound for a `k`-unbiased word `w` into a
node-count lower bound for computing `imm K n d`. -/
private theorem nodeCount_lower_of_word {w : Fin d → ℤ} {k : ℕ} {E : ℝ}
    (hw : IsUnbiased w k) (hn : 2 ^ k ≤ n) (e : Fin N → Fin d × Fin n × Fin n)
    {F : SPFormula K N} (hF : F.IsSetMultilinear (fun v => (e v).1) univ)
    (hFP : rename e F.polynomial = imm K n d)
    (hup : ∀ (m : ℕ) (blk' : Fin m → Fin d) (G : SPFormula K m),
      (∀ i, Fintype.card {x : Fin m // blk' x = i} = 2 ^ (w i).natAbs) →
      G.IsSetMultilinear blk' univ → G.productDepth ≤ F.productDepth →
      G.nodeCount = F.nodeCount →
      relRank blk' (wordPos w) (wordNeg w) G.polynomial ≤ G.nodeCount * 2 ^ (-E)) :
    (2 : ℝ) ^ (E - (k : ℝ) / 2) ≤ F.nodeCount := by
  classical
  set f := Fintype.equivFin (WordVar w)
  let ρ : Fin N → Option (Fin (Fintype.card (WordVar w))) :=
    fun v => (wordSubst w 0 n K (e v)).elim (fun x => some (f x)) fun _ => none
  let blk' : Fin (Fintype.card (WordVar w)) → Fin d := fun j => (f.symm j).1
  let G := SPFormula.subst ρ F
  have hρ : ∀ v j, ρ v = some j → blk' j = (e v).1 := by
    intro v j hv
    simp only [ρ] at hv
    rcases h : wordSubst w 0 n K (e v) with x | a <;>
      simp only [h, Sum.elim_inl, Sum.elim_inr, Option.some.injEq, reduceCtorEq] at hv
    subst hv
    simpa only [blk', Equiv.symm_apply_apply] using wordSubst_eq_inl h
  have hG : G.IsSetMultilinear blk' univ := hF.subst hρ
  have hGP : G.polynomial = rename f (wordPoly K w 0) := by
    have hτ : 0 < 2 ^ (∑ i, w i).natAbs := Nat.two_pow_pos _
    rw [← projection_wordSubst_imm hw hn hτ, ← hFP, SPFormula.polynomial_subst]
    change _ = ((rename f).comp ((projection (wordSubst w 0 n K)).comp (rename e))) F.polynomial
    congr 1
    refine algHom_ext fun v => ?_
    simp only [aeval_X, AlgHom.comp_apply, rename_X, projection_X, ρ]
    rcases h : wordSubst w 0 n K (e v) with x | a
    · simp
    · simp [wordSubst_eq_inr h]
  have hblk : ∀ i, Fintype.card {x // blk' x = i} = 2 ^ (w i).natAbs := by
    intro i
    rw [Fintype.card_congr ((f.symm.subtypeEquiv fun _ => Iff.rfl).trans (Equiv.sigmaSubtype i)),
      Fintype.card_fin]
  have hrank := hup _ blk' G hblk hG (by simp [G]) (SPFormula.nodeCount_subst ρ F)
  rw [hGP, relRank_rename (blk := Sigma.fst) f (fun _ => by simp [blk']),
    relRank_wordPoly (Nat.two_pow_pos _), SPFormula.nodeCount_subst] at hrank
  have hsum_abs : (∑ i, w i).natAbs ≤ k := by simpa using hw d le_rfl
  have hlow : (2 : ℝ) ^ (-(k : ℝ) / 2) ≤ 2 ^ (-((∑ i, w i).natAbs : ℝ) / 2) := by
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    cast_linarith [hsum_abs]
  have hsplit : (2 : ℝ) ^ (E - (k : ℝ) / 2) * 2 ^ (-E) = 2 ^ (-(k : ℝ) / 2) := by
    rw [← Real.rpow_add two_pos]
    ring_nf
  exact le_of_mul_le_mul_right (hsplit.trans_le (hlow.trans hrank))
    (Real.rpow_pos_of_pos two_pos _)

/-- **Exponential lower bound for semantically set-multilinear product-depth-one formulas**:
for every `d`, `k`, and `n` with `2 ^ k ≤ n`, every semantically set-multilinear formula of
product-depth at most `1` computing `imm K n d` has at least `2 ^ (k * (d - 1) / 2)` nodes. -/
theorem SPFormula.IsSemanticallySetMultilinear.two_rpow_depthOne_le_nodeCount_of_imm
    (e : Fin N → Fin d × Fin n × Fin n) {k : ℕ} (hn : 2 ^ k ≤ n) {F : SPFormula K N}
    (hF : F.IsSemanticallySetMultilinear (fun v => (e v).1))
    (hFΔ : F.productDepth ≤ 1) (hFP : rename e F.polynomial = imm K n d) :
    (2 : ℝ) ^ ((k : ℝ) * ((d : ℝ) - 1) / 2) ≤ F.nodeCount := by
  have huniv := hF.isSetMultilinear_univ_of_rename_imm e hFP
  set F' := F.normalizeSetMultilinear (fun v => (e v).1) univ
  have hF'sm := SPFormula.isSetMultilinear_normalizeSetMultilinear hF univ
  have hF'poly : rename e F'.polynomial = imm K n d := by
    rw [SPFormula.polynomial_normalizeSetMultilinear hF huniv, hFP]
  have hF'Δ : F'.productDepth ≤ 1 :=
    (SPFormula.productDepth_normalizeSetMultilinear_le _ _ F).trans hFΔ
  have hlb := nodeCount_lower_of_word (w := altWord k d) (E := (d : ℝ) * ((k : ℝ) / 2))
    (isUnbiased_altWord k d) hn e hF'sm hF'poly fun m blk' G hblk hG hGΔ _ => by
      have h := hG.relRank_polynomial_le_depthOne (a := (k : ℝ)) hblk
        (fun i => by simp [natAbs_altWord]) (hGΔ.trans hF'Δ)
      simpa [inter_univ, card_univ, Fintype.card_fin] using h
  have hexp : (k : ℝ) * ((d : ℝ) - 1) / 2 = (d : ℝ) * ((k : ℝ) / 2) - (k : ℝ) / 2 := by ring
  rw [hexp]
  exact hlb.trans (by exact_mod_cast SPFormula.nodeCount_normalizeSetMultilinear_le _ _ F)

/-- **Square-root-exponent lower bound for semantically set-multilinear product-depth-two
formulas**: for `1 ≤ d`, `4 * Nat.sqrt d ≤ k`, and `2 ^ k ≤ n`, every semantically
set-multilinear formula of product-depth at most `2` computing `imm K n d` has at least
`2 ^ (k * (√d / 12 - 1 / 2))` nodes. -/
theorem SPFormula.IsSemanticallySetMultilinear.two_rpow_sqrt_le_nodeCount_of_imm
    (e : Fin N → Fin d × Fin n × Fin n) {k : ℕ} (hd : 1 ≤ d) (hk : 4 * Nat.sqrt d ≤ k)
    (hn : 2 ^ k ≤ n) {F : SPFormula K N}
    (hF : F.IsSemanticallySetMultilinear (fun v => (e v).1))
    (hFΔ : F.productDepth ≤ 2) (hFP : rename e F.polynomial = imm K n d) :
    (2 : ℝ) ^ ((k : ℝ) * (√(d : ℝ) / 12 - 1 / 2)) ≤ F.nodeCount := by
  have huniv := hF.isSetMultilinear_univ_of_rename_imm e hFP
  set F' := F.normalizeSetMultilinear (fun v => (e v).1) univ
  have hF'sm := SPFormula.isSetMultilinear_normalizeSetMultilinear hF univ
  have hF'poly : rename e F'.polynomial = imm K n d := by
    rw [SPFormula.polynomial_normalizeSetMultilinear hF huniv, hFP]
  have hF'Δ : F'.productDepth ≤ 2 :=
    (SPFormula.productDepth_normalizeSetMultilinear_le _ _ F).trans hFΔ
  have hlb := nodeCount_lower_of_word (w := sqrtStepWord k d)
    (E := (k : ℝ) * √(d : ℝ) / 12) (isUnbiased_sqrtStepWord hd) hn e hF'sm hF'poly
    fun m blk' G hblk hG hGΔ _ =>
      hG.relRank_polynomial_le_sqrtStepWord hd hk hblk (hGΔ.trans hF'Δ)
  have hexp : (k : ℝ) * (√(d : ℝ) / 12 - 1 / 2) = (k : ℝ) * √(d : ℝ) / 12 - (k : ℝ) / 2 := by ring
  rw [hexp]
  exact hlb.trans (by exact_mod_cast SPFormula.nodeCount_normalizeSetMultilinear_le _ _ F)

/-- **Arbitrary-depth lower bound for semantically set-multilinear formulas**: lifts the
syntactic set-multilinear lower bound to the gate-wise semantic model. -/
theorem SPFormula.IsSemanticallySetMultilinear.two_rpow_le_nodeCount_of_imm
    (e : Fin N → Fin d × Fin n × Fin n) {k Δ : ℕ} (hk : 10 * d ≤ k) (hn : 2 ^ k ≤ n)
    (hΔ : 1 ≤ Δ) {F : SPFormula K N}
    (hF : F.IsSemanticallySetMultilinear (fun v => (e v).1))
    (hFΔ : F.productDepth ≤ Δ) (hFP : rename e F.polynomial = imm K n d) :
    (2 : ℝ) ^ ((k : ℝ) * ((d : ℝ) ^ (1 / (2 ^ Δ - 1 : ℝ)) / 20 - 1 / 2)) ≤ F.nodeCount := by
  have huniv := hF.isSetMultilinear_univ_of_rename_imm e hFP
  set F' := F.normalizeSetMultilinear (fun v => (e v).1) univ
  have hF'sm := SPFormula.isSetMultilinear_normalizeSetMultilinear hF univ
  have hF'poly : rename e F'.polynomial = imm K n d := by
    rw [SPFormula.polynomial_normalizeSetMultilinear hF huniv, hFP]
  have hF'Δ : F'.productDepth ≤ Δ :=
    (SPFormula.productDepth_normalizeSetMultilinear_le _ _ F).trans hFΔ
  exact (hF'sm.two_rpow_le_nodeCount_of_imm e hk hn hΔ hF'Δ hF'poly).trans
    (by exact_mod_cast SPFormula.nodeCount_normalizeSetMultilinear_le _ _ F)

/-- **Arbitrary-depth lower bound for semantically set-multilinear simple circuits**:
unfolds and normalizes a simple semantically set-multilinear circuit of product-depth at most `Δ`
computing `imm K n d`. -/
theorem SPCircuit.IsSemanticallySetMultilinear.two_rpow_le_size_of_imm
    (e : Fin N → Fin d × Fin n × Fin n) {k Δ : ℕ} (hk : 10 * d ≤ k) (hn : 2 ^ k ≤ n)
    (hΔ : 1 ≤ Δ) {C : SPCircuit K N} (hsim : C.IsSimple)
    (hsem : C.IsSemanticallySetMultilinear (fun v => (e v).1))
    (hCΔ : C.productDepth ≤ Δ) (hCP : rename e C.polynomial = imm K n d) :
    (2 : ℝ) ^ ((k : ℝ) * ((d : ℝ) ^ (1 / (2 ^ Δ - 1 : ℝ)) / 20 - 1 / 2)) ≤
      (C.size + N + 2) ^ (2 * Δ + 1) := by
  have hF₀sem := SPCircuit.isSemanticallySetMultilinear_wireFormula hsem (C.outputs 0)
  have hF₀poly : SPFormula.polynomial (C.toFormula 0) = C.polynomial :=
    SPCircuit.polynomial_toFormula C
  have huniv : MvPolynomial.IsSetMultilinear (fun v => (e v).1) univ C.polynomial :=
    hF₀poly ▸ hF₀sem.isSetMultilinear_univ_of_rename_imm e (hF₀poly.symm ▸ hCP)
  obtain ⟨G, hGsm, hGpoly, hGΔ, hGnodes⟩ :=
    SPCircuit.exists_setMultilinear_formula hsim hsem huniv
  have hlb := hGsm.two_rpow_le_nodeCount_of_imm e hk hn hΔ (hGΔ.trans hCΔ)
    (by rw [hGpoly, hCP])
  refine hlb.trans ?_
  have hpow : G.nodeCount ≤ (C.size + N + 2) ^ (2 * Δ + 1) :=
    hGnodes.trans (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
  exact_mod_cast hpow

/-- **Square-root-exponent lower bound for semantically set-multilinear product-depth-two
simple circuits**. -/
theorem SPCircuit.IsSemanticallySetMultilinear.two_rpow_sqrt_le_size_of_imm
    (e : Fin N → Fin d × Fin n × Fin n) {k : ℕ} (hd : 1 ≤ d) (hk : 4 * Nat.sqrt d ≤ k)
    (hn : 2 ^ k ≤ n) {C : SPCircuit K N} (hsim : C.IsSimple)
    (hsem : C.IsSemanticallySetMultilinear (fun v => (e v).1))
    (hCΔ : C.productDepth ≤ 2) (hCP : rename e C.polynomial = imm K n d) :
    (2 : ℝ) ^ ((k : ℝ) * (√(d : ℝ) / 12 - 1 / 2)) ≤ (C.size + N + 2) ^ 5 := by
  have hF₀sem := SPCircuit.isSemanticallySetMultilinear_wireFormula hsem (C.outputs 0)
  have hF₀poly : SPFormula.polynomial (C.toFormula 0) = C.polynomial :=
    SPCircuit.polynomial_toFormula C
  have huniv : MvPolynomial.IsSetMultilinear (fun v => (e v).1) univ C.polynomial :=
    hF₀poly ▸ hF₀sem.isSetMultilinear_univ_of_rename_imm e (hF₀poly.symm ▸ hCP)
  obtain ⟨G, hGsm, hGpoly, hGΔ, hGnodes⟩ :=
    SPCircuit.exists_setMultilinear_formula hsim hsem huniv
  have hlb := hGsm.isSemanticallySetMultilinear.two_rpow_sqrt_le_nodeCount_of_imm
    e hd hk hn (hGΔ.trans hCΔ) (by rw [hGpoly, hCP])
  refine hlb.trans ?_
  have hpow : G.nodeCount ≤ (C.size + N + 2) ^ 5 :=
    hGnodes.trans (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
  exact_mod_cast hpow

/-- **Square-root-exponent lower bound for unrestricted product-depth-one formulas over any
field**: set-multilinearizing a product-depth-one formula yields a product-depth-two
set-multilinear formula, improving the exponent from `d ^ (1 / 3)` to `√d`. -/
theorem SPFormula.two_rpow_sqrt_le_of_imm_depthOne (e : Fin N → Fin d × Fin n × Fin n)
    {k : ℕ} (hd : 1 ≤ d) (hk : 4 * Nat.sqrt d ≤ k) (hn : 2 ^ k ≤ n) {F : SPFormula K N}
    (hFΔ : F.productDepth ≤ 1) (hFP : rename e F.polynomial = imm K n d) :
    (2 : ℝ) ^ ((k : ℝ) * (√(d : ℝ) / 12 - 1 / 2)) ≤ SPFormula.smCost d * F.nodeCount := by
  classical
  let blk : Fin N → Fin d := fun v => (e v).1
  let G := SPFormula.smPart blk univ F
  have hGΔ : G.productDepth ≤ 2 :=
    (SPFormula.productDepth_smPart_le _ F).trans (by omega)
  have hGP : rename e G.polynomial = imm K n d := by
    rw [SPFormula.polynomial_smPart, rename_smProj (blk' := Prod.fst) e fun _ => rfl, hFP,
      smProj_imm]
  have hGsm := (SPFormula.isSetMultilinear_smPart (blk := blk) univ F).isSemanticallySetMultilinear
  have hlb := hGsm.two_rpow_sqrt_le_nodeCount_of_imm e hd hk hn hGΔ hGP
  refine hlb.trans ?_
  have hnodes : G.nodeCount ≤ SPFormula.smCost d * F.nodeCount := by
    calc G.nodeCount ≤ SPFormula.smCost d ^ F.productDepth * F.nodeCount :=
          SPFormula.nodeCount_smPart_le _ F
      _ ≤ SPFormula.smCost d ^ 1 * F.nodeCount :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (SPFormula.one_le_smCost d) hFΔ)
      _ = SPFormula.smCost d * F.nodeCount := by rw [pow_one]
  exact_mod_cast hnodes

/-- **Square-root-exponent lower bound for unrestricted product-depth-one simple circuits over
any field**. -/
theorem SPCircuit.two_rpow_sqrt_le_of_imm_depthOne (e : Fin N → Fin d × Fin n × Fin n)
    {k : ℕ} (hd : 1 ≤ d) (hk : 4 * Nat.sqrt d ≤ k) (hn : 2 ^ k ≤ n) {C : SPCircuit K N}
    (hsim : C.IsSimple) (hCΔ : C.productDepth ≤ 1) (hCP : rename e C.polynomial = imm K n d) :
    (2 : ℝ) ^ ((k : ℝ) * (√(d : ℝ) / 12 - 1 / 2)) ≤
      SPFormula.smCost d * (C.size + N + 1) ^ 3 := by
  refine (SPFormula.two_rpow_sqrt_le_of_imm_depthOne e hd hk hn
    ((SPCircuit.productDepth_toSPFormula_le C).trans hCΔ)
    (by rw [SPCircuit.polynomial_toSPFormula, hCP])).trans ?_
  have hnodes : C.toSPFormula.nodeCount ≤ (C.size + N + 1) ^ 3 :=
    (SPCircuit.nodeCount_toSPFormula_le hsim).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
  exact_mod_cast Nat.mul_le_mul_left (SPFormula.smCost d) hnodes

end SemanticAndSharpLowerBounds

/-! ### : Zero-one padding, full-range bounds, and growing product-depth -/

section PaddingAndGrowingDepth

variable {K : Type*}

/-- Zero-one identity-matrix substitution projecting `imm K n d'` down to `imm K n d` for
`d ≤ d'`: variables of matrices `i < d` are kept, and matrices `i ≥ d` are set to the `n × n`
identity matrix. -/
@[expose] def immPadSubst (K : Type*) [Zero K] [One K] (n : ℕ) {d d' : ℕ} (_hd : d ≤ d') :
    Fin d' × Fin n × Fin n → (Fin d × Fin n × Fin n) ⊕ K :=
  fun v =>
    if h : v.1.1 < d then Sum.inl (⟨v.1.1, h⟩, v.2.1, v.2.2)
    else Sum.inr (if v.2.1 = v.2.2 then 1 else 0)

/-- **Zero-one padding reduction for iterated matrix multiplication**: substituting identity
matrices for the trailing `d' - d` factors maps `imm K n d'` to `imm K n d`. -/
theorem projection_immPadSubst_imm [CommSemiring K] {n d d' : ℕ} [NeZero n] (hd : d ≤ d') :
    projection (immPadSubst K n hd) (imm K n d') = imm K n d := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hd
  have hprod :
      (projection (immPadSubst K n hd)).mapMatrix (List.ofFn (immMatrix K n (d + m))).prod =
        (List.ofFn (immMatrix K n d)).prod := by
    rw [map_list_prod, List.map_ofFn, List.ofFn_add, List.prod_append]
    have hleft :
        (List.ofFn fun i : Fin d =>
          ((projection (immPadSubst K n hd)).mapMatrix ∘ immMatrix K n (d + m))
            (Fin.castLE (Nat.le_add_right d m) i)) =
        List.ofFn (immMatrix K n d) := by
      congr 1
      funext i
      ext a c
      simp [immMatrix, immPadSubst, i.isLt]
    have hright :
        (List.ofFn fun j : Fin m =>
          ((projection (immPadSubst K n hd)).mapMatrix ∘ immMatrix K n (d + m))
            (Fin.natAdd d j)).prod = 1 := by
      refine List.prod_eq_one fun M hM => ?_
      rw [List.mem_ofFn] at hM
      obtain ⟨j, rfl⟩ := hM
      ext a c
      simp [immMatrix, immPadSubst, Matrix.one_apply]
    rw [hleft, hright, mul_one]
  exact congrArg (fun M => M 0 0) hprod

namespace SPFormula

variable {N N' : ℕ}

/-- Substitute variables or field constants into an unbounded fan-in formula. -/
@[expose] def substConst (ρ : Fin N' → Fin N ⊕ K) (F : SPFormula K N') : SPFormula K N :=
  F.bind fun v => (ρ v).elim .input const

/-- Substituting into a gate substitutes into each child. -/
@[simp] theorem substConst_gate (ρ : Fin N' → Fin N ⊕ K) (op : SigmaPiOp K)
    (args : Fin ((sigmaPiSignature K).Arity op) → SPFormula K N') :
    substConst ρ (Formula.gate op args : SPFormula K N') =
      .gate op fun j => substConst ρ (args j) :=
  rfl

/-- Constant/variable substitution preserves node count. -/
@[simp] theorem nodeCount_substConst (ρ : Fin N' → Fin N ⊕ K) (F : SPFormula K N') :
    (F.substConst ρ).nodeCount = F.nodeCount := by
  induction F with
  | input v => cases h : ρ v <;> simp [substConst, h]
  | gate op args ih => simp only [substConst_gate, Formula.nodeCount_gate, ih]

/-- Constant/variable substitution preserves product-depth. -/
@[simp] theorem productDepth_substConst (ρ : Fin N' → Fin N ⊕ K) (F : SPFormula K N') :
    (F.substConst ρ).productDepth = F.productDepth := by
  induction F with
  | input v => cases h : ρ v <;> simp [substConst, h]
  | gate op args ih =>
    simp only [productDepth, substConst_gate, Formula.depthWith] at ih ⊢
    simp only [ih]

/-- Constant/variable substitution computes the corresponding polynomial evaluation. -/
theorem polynomial_substConst [CommSemiring K] (ρ : Fin N' → Fin N ⊕ K) (F : SPFormula K N') :
    (F.substConst ρ).polynomial = aeval (fun v => (ρ v).elim X C) F.polynomial := by
  rw [aeval_polynomial, algebraMap_eq, polynomial, substConst, Formula.eval_bind]
  congr 1
  funext v
  cases ρ v <;> rfl

end SPFormula

private theorem rename_substConst_immPadSubst [CommSemiring K] {n d d' N' : ℕ} [NeZero n]
    (hd : d ≤ d') (e : Fin N' → Fin d' × Fin n × Fin n) (F : SPFormula K N')
    (hFP : rename e F.polynomial = imm K n d') :
    rename (immVarEquiv n d)
        (F.substConst fun v =>
          (immPadSubst K n hd (e v)).map (immVarEquiv n d).symm id).polynomial =
      imm K n d := by
  rw [← projection_immPadSubst_imm (K := K) hd, ← hFP, SPFormula.polynomial_substConst]
  generalize F.polynomial = P
  change ((rename (immVarEquiv n d)).comp
      (aeval fun v => ((immPadSubst K n hd (e v)).map (immVarEquiv n d).symm id).elim X C)) P =
    ((projection (immPadSubst K n hd)).comp (rename e)) P
  congr 1
  refine algHom_ext fun v => ?_
  simp only [AlgHom.comp_apply, aeval_X, rename_X, projection_X]
  cases immPadSubst K n hd (e v) <;> simp

/-- **Explicit lower bound for formulas computing `imm K n d'` for any `d' ≥ d`**: reduces to
`imm K n d` via zero-one identity-matrix substitution without changing node count or
product-depth. -/
theorem SPFormula.two_rpow_le_of_imm_of_le [Field K] {n d d' N' : ℕ} [NeZero n]
    (hd : d ≤ d') (e : Fin N' → Fin d' × Fin n × Fin n) {k Δ : ℕ}
    (hk : 10 * d ≤ k) (hn : 2 ^ k ≤ n) (hΔ : 1 ≤ Δ) {F : SPFormula K N'}
    (hFΔ : F.productDepth ≤ Δ) (hFP : rename e F.polynomial = imm K n d') :
    (2 : ℝ) ^ ((k : ℝ) * ((d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / 20 - 1 / 2)) ≤
      SPFormula.smCost d ^ Δ * F.nodeCount := by
  let ρ : Fin N' → Fin (d * (n * n)) ⊕ K :=
    fun v => (immPadSubst K n hd (e v)).map (immVarEquiv n d).symm id
  let G : SPFormula K (d * (n * n)) := F.substConst ρ
  have hGΔ : G.productDepth ≤ Δ := by simpa [G] using hFΔ
  have hGP : rename (immVarEquiv n d) G.polynomial = imm K n d :=
    rename_substConst_immPadSubst hd e F hFP
  simpa [G] using SPFormula.two_rpow_le_of_imm (immVarEquiv n d) hk hn hΔ hGΔ hGP

/-- **Explicit lower bound for simple circuits computing `imm K n d'` for any `d' ≥ d`**. -/
theorem SPCircuit.two_rpow_le_of_imm_of_le [Field K] {n d d' N' : ℕ} [NeZero n]
    (hd : d ≤ d') (e : Fin N' → Fin d' × Fin n × Fin n) {k Δ : ℕ}
    (hk : 10 * d ≤ k) (hn : 2 ^ k ≤ n) (hΔ : 1 ≤ Δ) {C : SPCircuit K N'}
    (hsim : C.IsSimple) (hCΔ : C.productDepth ≤ Δ) (hCP : rename e C.polynomial = imm K n d') :
    (2 : ℝ) ^ ((k : ℝ) * ((d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / 20 - 1 / 2)) ≤
      SPFormula.smCost d ^ Δ * (C.size + N' + 1) ^ (2 * Δ + 1) := by
  refine (SPFormula.two_rpow_le_of_imm_of_le hd e hk hn hΔ
    ((SPCircuit.productDepth_toSPFormula_le C).trans hCΔ)
    (by rw [SPCircuit.polynomial_toSPFormula, hCP])).trans ?_
  exact_mod_cast Nat.mul_le_mul_left (SPFormula.smCost d ^ Δ)
    ((SPCircuit.nodeCount_toSPFormula_le hsim).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)))

/-- **Explicit `n ^ (d ^ (1 / (4 ^ Δ - 1)) / 80)` formula lower bound supporting arbitrary
(possibly growing) product-depth `Δ` and any `d' ≥ d`**. -/
theorem SPFormula.rpow_le_nodeCount_of_imm [Field K] {n d d' N' Δ : ℕ} [NeZero n]
    (hn2 : 2 ≤ n) (hΔ : 1 ≤ Δ) (hd : d ≤ d') (hk : 10 * d ≤ Nat.log 2 n)
    (hr40 : (40 : ℝ) ≤ (d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)))
    (hsm : (Δ : ℝ) * (((2 * (Nat.log 2 (d + 1) + 1) + 1) * (d + 1) + 2 : ℕ) : ℝ) ≤
      (Nat.log 2 n : ℝ) * (d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / 80)
    (e : Fin N' → Fin d' × Fin n × Fin n) {F : SPFormula K N'}
    (hFΔ : F.productDepth ≤ Δ) (hFP : rename e F.polynomial = imm K n d') :
    (n : ℝ) ^ ((d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / 80) ≤ F.nodeCount := by
  set L := Nat.log 2 n
  set r : ℝ := (d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ))
  have h2L : 2 ^ L ≤ n := Nat.pow_log_le_self 2 (NeZero.ne n)
  have hL1 : 1 ≤ L := Nat.le_log_of_pow_le one_lt_two (by simpa using hn2)
  have hbase := SPFormula.two_rpow_le_of_imm_of_le hd e hk h2L hΔ hFΔ hFP
  set b := Nat.log 2 (d + 1) + 1
  have hdb : d + 1 ≤ 2 ^ b := (Nat.lt_pow_succ_log_self one_lt_two (d + 1)).le
  set M := (2 * b + 1) * (d + 1) + 2
  have hsm_pow : SPFormula.smCost d ^ Δ ≤ 2 ^ (M * Δ) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (SPFormula.smCost_le_two_pow hdb) Δ
  have hsmR : ((SPFormula.smCost d ^ Δ : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((M * Δ : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hsm_pow
  have hmain : (2 : ℝ) ^ ((L : ℝ) * (r / 20 - 1 / 2)) ≤
      (2 : ℝ) ^ ((M * Δ : ℕ) : ℝ) * F.nodeCount := by
    refine hbase.trans ?_
    have hsmR' : (SPFormula.smCost d : ℝ) ^ Δ ≤ (2 : ℝ) ^ ((M * Δ : ℕ) : ℝ) := by
      simpa using hsmR
    exact mul_le_mul_of_nonneg_right hsmR' (Nat.cast_nonneg _)
  have hexp_diff : (L : ℝ) * r / 40 + ((M * Δ : ℕ) : ℝ) ≤ (L : ℝ) * (r / 20 - 1 / 2) := by
    have hMD : ((M * Δ : ℕ) : ℝ) = (Δ : ℝ) * (M : ℝ) := by push_cast; ring
    rw [hMD]
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith
  have h2bound : (2 : ℝ) ^ ((L : ℝ) * r / 40) ≤ F.nodeCount := by
    have hprod : (2 : ℝ) ^ ((L : ℝ) * r / 40) * (2 : ℝ) ^ ((M * Δ : ℕ) : ℝ) ≤
        (2 : ℝ) ^ ((M * Δ : ℕ) : ℝ) * F.nodeCount := by
      rw [← Real.rpow_add two_pos]
      exact (Real.rpow_le_rpow_of_exponent_le one_le_two hexp_diff).trans hmain
    rw [mul_comm ((2 : ℝ) ^ ((M * Δ : ℕ) : ℝ))] at hprod
    exact le_of_mul_le_mul_right hprod (Real.rpow_pos_of_pos two_pos _)
  have hn_le : (n : ℝ) ≤ (2 : ℝ) ^ (2 * L : ℕ) := by
    have hlt : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self one_lt_two n
    have hle : n ≤ 2 ^ (2 * L) := hlt.le.trans (Nat.pow_le_pow_right two_pos (by omega))
    exact_mod_cast hle
  have hrpos : 0 ≤ r / 80 := by linarith
  calc (n : ℝ) ^ (r / 80) ≤ ((2 : ℝ) ^ (2 * L : ℕ)) ^ (r / 80) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) hn_le hrpos
    _ = (2 : ℝ) ^ ((L : ℝ) * r / 40) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
        congr 1
        push_cast
        ring
    _ ≤ F.nodeCount := h2bound

/-- **Explicit `n ^ (d ^ (1 / (4 ^ Δ - 1)) / (80 * (2 * Δ + 1)))` simple-circuit lower bound
supporting arbitrary (possibly growing) product-depth `Δ` and any `d' ≥ d`**. -/
theorem SPCircuit.rpow_le_size_add_of_imm [Field K] {n d d' N' Δ : ℕ} [NeZero n]
    (hn2 : 2 ≤ n) (hΔ : 1 ≤ Δ) (hd : d ≤ d') (hk : 10 * d ≤ Nat.log 2 n)
    (hr40 : (40 : ℝ) ≤ (d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)))
    (hsm : (Δ : ℝ) * (((2 * (Nat.log 2 (d + 1) + 1) + 1) * (d + 1) + 2 : ℕ) : ℝ) ≤
      (Nat.log 2 n : ℝ) * (d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / 80)
    (e : Fin N' → Fin d' × Fin n × Fin n) {C : SPCircuit K N'}
    (hsim : C.IsSimple) (hCΔ : C.productDepth ≤ Δ) (hCP : rename e C.polynomial = imm K n d') :
    (n : ℝ) ^ ((d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / (80 * (2 * (Δ : ℝ) + 1))) ≤
      (C.size + N' + 1 : ℕ) := by
  have hF := SPFormula.rpow_le_nodeCount_of_imm hn2 hΔ hd hk hr40 hsm e
    ((SPCircuit.productDepth_toSPFormula_le C).trans hCΔ)
    (by rw [SPCircuit.polynomial_toSPFormula, hCP])
  have hnodes : (C.toSPFormula.nodeCount : ℝ) ≤ ((C.size + N' + 1 : ℕ) : ℝ) ^ (2 * Δ + 1) := by
    exact_mod_cast (SPCircuit.nodeCount_toSPFormula_le hsim).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
  have hpow : (n : ℝ) ^ ((d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / 80) ≤
      ((C.size + N' + 1 : ℕ) : ℝ) ^ (2 * Δ + 1) := hF.trans hnodes
  set E : ℝ := (d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / (80 * (2 * (Δ : ℝ) + 1))
  have hDpos : (0 : ℝ) < (2 * Δ + 1 : ℕ) := by positivity
  have hEeq : ((n : ℝ) ^ E) ^ (2 * Δ + 1 : ℕ) =
      (n : ℝ) ^ ((d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / 80) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    have hne : (2 * (Δ : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    dsimp only [E]
    field_simp
  rw [← hEeq] at hpow
  exact le_of_pow_le_pow_left₀ (by omega : 2 * Δ + 1 ≠ 0) (Nat.cast_nonneg _) hpow

/-- **Full-range superpolynomial circuit lower bound**: for every constant product-depth `Δ` and
every polynomial degree cap `n ^ b` and size exponent `c`, for all sufficiently large `n` and
every `d'` in the range `[⌊log₂ ⌊log₂ n⌋⌋, n ^ b]`, every simple circuit of product-depth at most
`Δ` computing `imm K n d'` has more than `n ^ c` gates. -/
theorem SPCircuit.eventually_pow_lt_size_of_imm_range (K : Type*) [Field K] (Δ c b : ℕ) :
    ∀ᶠ n in atTop, ∀ [NeZero n] (d' : ℕ),
      Nat.log 2 (Nat.log 2 n) ≤ d' → d' ≤ n ^ b →
      ∀ {N' : ℕ} (e : Fin N' ≃ Fin d' × Fin n × Fin n) (C : SPCircuit K N'),
        C.IsSimple → C.productDepth ≤ Δ → rename e C.polynomial = imm K n d' →
        n ^ c < C.size := by
  let cF : ℕ := (max c (b + 2) + 2) * (2 * Δ + 1)
  filter_upwards [SPFormula.eventually_pow_lt_nodeCount_of_imm K Δ cF,
    eventually_ge_atTop 2] with n hn hn2 _ d' hd_lo hd_hi N' e C hsim hCΔ hCP
  by_contra hs
  have hs : C.size ≤ n ^ c := not_lt.1 hs
  set d := Nat.log 2 (Nat.log 2 n)
  let ρ : Fin N' → Fin (d * (n * n)) ⊕ K :=
    fun v => (immPadSubst K n hd_lo (e v)).map (immVarEquiv n d).symm id
  let G : SPFormula K (d * (n * n)) := C.toSPFormula.substConst ρ
  have hGP : rename (immVarEquiv n d) G.polynomial = imm K n d :=
    rename_substConst_immPadSubst hd_lo e C.toSPFormula
      (by rw [SPCircuit.polynomial_toSPFormula]; exact hCP)
  have hlt := hn (immVarEquiv n d) G
    (by
      rw [SPFormula.productDepth_substConst]
      exact (SPCircuit.productDepth_toSPFormula_le C).trans hCΔ)
    hGP
  rw [SPFormula.nodeCount_substConst] at hlt
  have hN' : N' ≤ n ^ (b + 2) := by
    have hcard : N' = d' * (n * n) := by simpa using Fintype.card_congr e
    rw [hcard, pow_add, pow_two]
    exact Nat.mul_le_mul_right _ hd_hi
  set M := max c (b + 2)
  have h1 : 1 ≤ n ^ M := Nat.one_le_pow _ _ (by omega)
  have hC_le : C.size ≤ n ^ M := hs.trans (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have hN_le : N' ≤ n ^ M := hN'.trans (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  have h4 : 4 ≤ n ^ 2 := (by norm_num : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_left hn2 2)
  have hbase : C.size + N' + 1 ≤ n ^ (M + 2) := by
    calc C.size + N' + 1 ≤ 3 * n ^ M := by omega
      _ ≤ n ^ 2 * n ^ M := Nat.mul_le_mul_right _ (by omega)
      _ = n ^ (M + 2) := by rw [← pow_add, add_comm]
  have hnode := SPCircuit.nodeCount_toSPFormula_le hsim
  have hmono : (C.size + N' + 1) ^ (2 * C.productDepth + 1) ≤ (n ^ (M + 2)) ^ (2 * Δ + 1) :=
    (Nat.pow_le_pow_left hbase _).trans
      (Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by omega)) (by omega))
  rw [← pow_mul] at hmono
  exact not_lt_of_ge (hnode.trans hmono) hlt

/-- An explicit unboundedly growing product-depth schedule:
`Δ(n) = max 1 ⌊log₄ ⌊√⌊log₂ ⌊log₂ ⌊log₂ n⌋⌋⌋⌋⌋`. -/
@[expose] def growingProductDepth (n : ℕ) : ℕ :=
  max 1 (Nat.log 4 (Nat.sqrt (Nat.log 2 (Nat.log 2 (Nat.log 2 n)))))

/-- `growingProductDepth` tends to infinity. -/
theorem tendsto_growingProductDepth : Tendsto growingProductDepth atTop atTop := by
  refine tendsto_atTop_atTop.2 fun B => ?_
  refine ⟨2 ^ (2 ^ (2 ^ ((4 ^ B) ^ 2))), fun n hn => ?_⟩
  have h1 : 2 ^ (2 ^ ((4 ^ B) ^ 2)) ≤ Nat.log 2 n := Nat.le_log_of_pow_le one_lt_two hn
  have h2 : 2 ^ ((4 ^ B) ^ 2) ≤ Nat.log 2 (Nat.log 2 n) := Nat.le_log_of_pow_le one_lt_two h1
  have h3 : (4 ^ B) ^ 2 ≤ Nat.log 2 (Nat.log 2 (Nat.log 2 n)) :=
    Nat.le_log_of_pow_le one_lt_two h2
  have h4 : 4 ^ B ≤ Nat.sqrt (Nat.log 2 (Nat.log 2 (Nat.log 2 n))) :=
    Nat.le_sqrt.2 (by simpa [sq] using h3)
  have h5 : B ≤ Nat.log 4 (Nat.sqrt (Nat.log 2 (Nat.log 2 (Nat.log 2 n)))) :=
    Nat.le_log_of_pow_le (by norm_num) h4
  exact h5.trans (le_max_right _ _)

/-- Auxiliary growth estimate: a cubic polynomial is eventually below `2 ^ d`. -/
private theorem eventually_mul_cube_le_two_pow (a : ℕ) :
    ∀ᶠ d : ℕ in atTop, a * (d + 1) ^ 3 ≤ 2 ^ d := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 3 (r := (2 : ℝ)) one_lt_two
  have hε : (0 : ℝ) < 1 / (8 * a + 1) := by positivity
  filter_upwards [(tendsto_order.1 hlim).2 _ hε, eventually_ge_atTop 1] with d hd hd1
  have h2 : (0 : ℝ) < 2 ^ d := by positivity
  have h8 : (0 : ℝ) < 8 * a + 1 := by positivity
  rw [div_lt_div_iff₀ h2 h8, one_mul] at hd
  have hd' : (8 * a + 1) * d ^ 3 < 2 ^ d := by exact_mod_cast (mul_comm _ _).trans_lt hd
  have hcu : (d + 1) ^ 3 ≤ 8 * d ^ 3 :=
    (Nat.pow_le_pow_left (by omega : d + 1 ≤ 2 * d) 3).trans_eq (by ring)
  calc a * (d + 1) ^ 3 ≤ a * (8 * d ^ 3) := Nat.mul_le_mul_left _ hcu
    _ = 8 * a * d ^ 3 := by ring
    _ ≤ (8 * a + 1) * d ^ 3 := Nat.mul_le_mul_right _ (by omega)
    _ ≤ 2 ^ d := hd'.le

/-- **Superpolynomial lower bound for simple circuits at unboundedly growing product-depth**:
for every size exponent `c` and degree exponent `b`, for all sufficiently large `n` and every
`d' ∈ [⌊log₂ ⌊log₂ n⌋⌋, n ^ b]`, every simple circuit of product-depth at most
`growingProductDepth n` computing `imm K n d'` has more than `n ^ c` gates. -/
theorem SPCircuit.eventually_pow_lt_size_of_imm_growingDepth (K : Type*) [Field K] (c b : ℕ) :
    ∀ᶠ n in atTop, ∀ [NeZero n] (d' : ℕ),
      Nat.log 2 (Nat.log 2 n) ≤ d' → d' ≤ n ^ b →
      ∀ {N' : ℕ} (e : Fin N' ≃ Fin d' × Fin n × Fin n) (C : SPCircuit K N'),
        C.IsSimple → C.productDepth ≤ growingProductDepth n →
        rename e C.polynomial = imm K n d' → n ^ c < C.size := by
  set M := max c (b + 2)
  have hlin : ∀ᶠ s : ℕ in atTop, 80 * (M + 3) * (2 * s + 1) ≤ 2 ^ s := by
    filter_upwards [eventually_mul_sq_le_two_pow (160 * (M + 3))] with s hs
    have h1 : 2 * s + 1 ≤ 2 * (s + 1) ^ 2 := by nlinarith
    calc 80 * (M + 3) * (2 * s + 1) ≤ 80 * (M + 3) * (2 * (s + 1) ^ 2) :=
          Nat.mul_le_mul_left _ h1
      _ = 160 * (M + 3) * (s + 1) ^ 2 := by ring
      _ ≤ 2 ^ s := hs
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.1 (hlin.and (eventually_ge_atTop 4))
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.1
    ((eventually_mul_cube_le_two_pow 8).and (eventually_ge_atTop (max 20 (2 ^ (S₀ ^ 2)))))
  refine eventually_atTop.2 ⟨max 2 (2 ^ (2 ^ D₀)),
    fun n hn _ d' hd_lo hd_hi N' e C hsim hCΔ hCP => ?_⟩
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have h22D : 2 ^ (2 ^ D₀) ≤ n := (le_max_right _ _).trans hn
  set L := Nat.log 2 n
  set d := Nat.log 2 L
  set Δ := growingProductDepth n
  have hL_ge : 2 ^ D₀ ≤ L := Nat.le_log_of_pow_le one_lt_two h22D
  have hd_ge : D₀ ≤ d := Nat.le_log_of_pow_le one_lt_two hL_ge
  obtain ⟨hcube, hd_min⟩ := hD₀ d hd_ge
  have hd20 : 20 ≤ d := (le_max_left _ _).trans hd_min
  have h2S : 2 ^ (S₀ ^ 2) ≤ d := (le_max_right _ _).trans hd_min
  have h2dL : 2 ^ d ≤ L := Nat.pow_log_le_self 2 (by have := Nat.one_le_two_pow (n := D₀); omega)
  set m := Nat.log 2 d
  set s := Nat.sqrt m
  have hs_ge : S₀ ≤ s := Nat.le_sqrt.2 (by simpa [sq] using Nat.le_log_of_pow_le one_lt_two h2S)
  obtain ⟨hs_exp, hs4⟩ := hS₀ s hs_ge
  have hΔ1 : 1 ≤ Δ := le_max_left _ _
  have hΔ_le_s : Δ ≤ s := by
    refine max_le (by omega) ?_
    exact (Nat.log_le_self 4 s)
  have hΔdef : Δ = max 1 (Nat.log 4 s) := rfl
  have h4Δ_le : 4 ^ Δ ≤ s := by
    have hlog4 : 4 ^ Nat.log 4 s ≤ s := Nat.pow_log_le_self 4 (by omega)
    rcases le_or_gt 1 (Nat.log 4 s) with hge | hlt
    · have hEq : Δ = Nat.log 4 s := hΔdef.trans (max_eq_right hge)
      rw [hEq]; exact hlog4
    · have hEq : Δ = 1 := hΔdef.trans (max_eq_left (by omega))
      rw [hEq]; simp; omega
  have h4Δ_pos : 1 ≤ 4 ^ Δ - 1 := by
    have : 4 ≤ 4 ^ Δ := (by norm_num : 4 = 4 ^ 1).trans_le (Nat.pow_le_pow_right (by norm_num) hΔ1)
    omega
  -- Show `2 ^ s ≤ d ^ (1 / (4 ^ Δ - 1))`.
  have h2s_le_r : ((2 ^ s : ℕ) : ℝ) ≤ (d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) := by
    have hms : s * (4 ^ Δ - 1) ≤ m := by
      calc s * (4 ^ Δ - 1) ≤ s * 4 ^ Δ := Nat.mul_le_mul_left s (Nat.sub_le _ _)
        _ ≤ s * s := Nat.mul_le_mul_left s h4Δ_le
        _ ≤ m := Nat.sqrt_le m
    have hpow_le : (2 ^ s) ^ (4 ^ Δ - 1) ≤ d := by
      rw [← pow_mul]
      exact (Nat.pow_le_pow_right two_pos hms).trans (Nat.pow_log_le_self 2 (by omega))
    have hq_ne : 4 ^ Δ - 1 ≠ 0 := by omega
    have hq_cast : (4 ^ Δ - 1 : ℝ) = ((4 ^ Δ - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
      push_cast; rfl
    rw [hq_cast, one_div,
      ← Real.pow_rpow_inv_natCast (Nat.cast_nonneg (2 ^ s)) hq_ne]
    refine Real.rpow_le_rpow (by positivity) ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
    exact_mod_cast hpow_le
  have hr40 : (40 : ℝ) ≤ (d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) := by
    have h40s : 40 ≤ 2 ^ s := by
      have h1 : 40 ≤ 80 * (M + 3) * (2 * s + 1) := by
        calc 40 ≤ 80 * 1 * 1 := by norm_num
          _ ≤ 80 * (M + 3) * (2 * s + 1) := by gcongr <;> omega
      exact h1.trans hs_exp
    exact (by exact_mod_cast h40s : (40 : ℝ) ≤ (2 ^ s : ℕ)).trans h2s_le_r
  have h10d : 10 * d ≤ L := by
    have h10 : 10 * d ≤ 8 * (d + 1) ^ 3 := by
      have hsq : 2 ≤ (d + 1) ^ 2 := by
        calc 2 ≤ 2 ^ 2 := by norm_num
          _ ≤ (d + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      calc 10 * d ≤ 8 * 2 * (d + 1) := by omega
        _ ≤ 8 * (d + 1) ^ 2 * (d + 1) := by gcongr
        _ = 8 * (d + 1) ^ 3 := by ring
    exact h10.trans (hcube.trans h2dL)
  have hsm : (Δ : ℝ) * (((2 * (Nat.log 2 (d + 1) + 1) + 1) * (d + 1) + 2 : ℕ) : ℝ) ≤
      (L : ℝ) * (d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / 80 := by
    have hlogd : Nat.log 2 (d + 1) ≤ d := Nat.lt_succ_iff.1 (Nat.log_lt_self 2 (by omega))
    have hΔd : Δ ≤ d := hΔ_le_s.trans ((Nat.sqrt_le_self m).trans (Nat.log_le_self 2 d))
    have hnat : Δ * ((2 * (Nat.log 2 (d + 1) + 1) + 1) * (d + 1) + 2) ≤ 4 * (d + 1) ^ 3 := by
      have hfac : (2 * (Nat.log 2 (d + 1) + 1) + 1) * (d + 1) + 2 ≤ 4 * (d + 1) ^ 2 := by
        have h1 : 2 * (Nat.log 2 (d + 1) + 1) + 1 ≤ 3 * (d + 1) := by omega
        calc (2 * (Nat.log 2 (d + 1) + 1) + 1) * (d + 1) + 2
            ≤ 3 * (d + 1) * (d + 1) + (d + 1) * (d + 1) := by
              nlinarith
          _ = 4 * (d + 1) ^ 2 := by ring
      calc Δ * ((2 * (Nat.log 2 (d + 1) + 1) + 1) * (d + 1) + 2)
          ≤ (d + 1) * (4 * (d + 1) ^ 2) := Nat.mul_le_mul (by omega) hfac
        _ = 4 * (d + 1) ^ 3 := by ring
    have hLhalf : 2 * (Δ * ((2 * (Nat.log 2 (d + 1) + 1) + 1) * (d + 1) + 2)) ≤ L := by
      calc 2 * (Δ * ((2 * (Nat.log 2 (d + 1) + 1) + 1) * (d + 1) + 2))
          ≤ 2 * (4 * (d + 1) ^ 3) := Nat.mul_le_mul_left 2 hnat
        _ = 8 * (d + 1) ^ 3 := by ring
        _ ≤ 2 ^ d := hcube
        _ ≤ L := h2dL
    have hLhalfR : 2 * ((Δ : ℝ) * (((2 * (Nat.log 2 (d + 1) + 1) + 1) * (d + 1) + 2 : ℕ) : ℝ)) ≤
        (L : ℝ) := by exact_mod_cast hLhalf
    have hr80 : (40 : ℝ) ≤ (d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) := hr40
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith
  have hlb := SPCircuit.rpow_le_size_add_of_imm hn2 hΔ1 hd_lo h10d hr40 hsm e hsim hCΔ hCP
  -- Show `(M + 3) ≤ r / (80 * (2 * Δ + 1))`.
  have hexp_ge : ((M + 3 : ℕ) : ℝ) ≤
      (d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / (80 * (2 * (Δ : ℝ) + 1)) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : 80 * (M + 3) * (2 * Δ + 1) ≤ 2 ^ s :=
      (Nat.mul_le_mul_left _ (by omega : 2 * Δ + 1 ≤ 2 * s + 1)).trans hs_exp
    have h1R : ((M + 3 : ℕ) : ℝ) * (80 * (2 * (Δ : ℝ) + 1)) ≤ ((2 ^ s : ℕ) : ℝ) := by
      have hcast : ((80 * (M + 3) * (2 * Δ + 1) : ℕ) : ℝ) ≤ ((2 ^ s : ℕ) : ℝ) := by
        exact_mod_cast h1
      push_cast at hcast ⊢
      linarith
    exact h1R.trans h2s_le_r
  have hn_pow : ((n ^ (M + 3) : ℕ) : ℝ) ≤ ((C.size + N' + 1 : ℕ) : ℝ) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    calc ((n ^ (M + 3) : ℕ) : ℝ) = (n : ℝ) ^ ((M + 3 : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]; push_cast; rfl
      _ ≤ (n : ℝ) ^ ((d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / (80 * (2 * (Δ : ℝ) + 1))) :=
          Real.rpow_le_rpow_of_exponent_le hn1 hexp_ge
      _ ≤ ((C.size + N' + 1 : ℕ) : ℝ) := hlb
  have hn_pow_nat : n ^ (M + 3) ≤ C.size + N' + 1 := by exact_mod_cast hn_pow
  by_contra hle
  have hs : C.size ≤ n ^ c := not_lt.1 hle
  have hN' : N' ≤ n ^ (b + 2) := by
    have hcard : N' = d' * (n * n) := by simpa using Fintype.card_congr e
    rw [hcard, pow_add, pow_two]
    exact Nat.mul_le_mul_right _ hd_hi
  have h1 : 1 ≤ n ^ M := Nat.one_le_pow _ _ (by omega)
  have hC_le : C.size ≤ n ^ M := hs.trans (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have hN_le : N' ≤ n ^ M := hN'.trans (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  have h8 : 8 ≤ n ^ 3 := (by norm_num : 8 ≤ 2 ^ 3).trans (Nat.pow_le_pow_left hn2 3)
  have hlt : C.size + N' + 1 < n ^ (M + 3) := by
    calc C.size + N' + 1 ≤ 3 * n ^ M := by omega
      _ < 8 * n ^ M := by omega
      _ ≤ n ^ 3 * n ^ M := Nat.mul_le_mul_right _ h8
      _ = n ^ (M + 3) := by rw [← pow_add, add_comm]
  omega

end PaddingAndGrowingDepth

/-! ### : Explicit full-rank split-bilinear polynomial and depth separation -/

section SplitBilinear

variable {K : Type*}

/-- Block assignment for `splitBilinearPoly K k w`: left variables `(false, i, a)` lie in block
`i` and right variables `(true, i, a)` lie in block `k + i`. -/
@[expose] def splitBlock (k w : ℕ) : Bool × Fin k × Fin w → Fin (2 * k)
  | (false, i, _) => ⟨i.1, by omega⟩
  | (true, i, _) => ⟨k + i.1, by omega⟩

/-- The `k` left blocks `{0, …, k - 1}` of `splitBlock`. -/
@[expose] def splitLeftBlocks (k : ℕ) : Finset (Fin (2 * k)) :=
  univ.image fun i : Fin k => (⟨i.1, by omega⟩ : Fin (2 * k))

/-- The `k` right blocks `{k, …, 2k - 1}` of `splitBlock`. -/
@[expose] def splitRightBlocks (k : ℕ) : Finset (Fin (2 * k)) :=
  univ.image fun i : Fin k => (⟨k + i.1, by omega⟩ : Fin (2 * k))

/-- The explicit degree-`2k` set-multilinear polynomial
`∏ i < k, ∑ a < w, X (false, i, a) * X (true, i, a)`. -/
@[expose] noncomputable def splitBilinearPoly (K : Type*) [CommSemiring K] (k w : ℕ) :
    MvPolynomial (Bool × Fin k × Fin w) K :=
  ∏ i : Fin k, ∑ a : Fin w, X (false, i, a) * X (true, i, a)

/-- `splitBilinearPoly K k w` is homogeneous of degree `2 * k`. -/
theorem isHomogeneous_splitBilinearPoly [CommSemiring K] (k w : ℕ) :
    (splitBilinearPoly K k w).IsHomogeneous (2 * k) := by
  have hfac (i : Fin k) :
      (∑ a : Fin w, (X (false, i, a) * X (true, i, a) :
        MvPolynomial (Bool × Fin k × Fin w) K)).IsHomogeneous 2 :=
    IsHomogeneous.sum _ _ _ fun a _ => by
      simpa using (isHomogeneous_X K (false, i, a)).mul (isHomogeneous_X K (true, i, a))
  simpa [splitBilinearPoly, mul_comm] using
    IsHomogeneous.prod (univ : Finset (Fin k))
      (fun i => ∑ a : Fin w, (X (false, i, a) * X (true, i, a) :
        MvPolynomial (Bool × Fin k × Fin w) K)) (fun _ => 2) fun i _ => hfac i

/-- Monomial expansion of `splitBilinearPoly K k w` over all functions `f : Fin k → Fin w`. -/
theorem splitBilinearPoly_eq_sum [CommSemiring K] (k w : ℕ) :
    splitBilinearPoly K k w =
      ∑ f : Fin k → Fin w,
        monomial (∑ i : Fin k, (Finsupp.single (false, i, f i) 1 +
          Finsupp.single (true, i, f i) 1)) (1 : K) := by
  rw [splitBilinearPoly, Fintype.prod_sum]
  refine sum_congr rfl fun f _ => ?_
  have hterm (i : Fin k) :
      (X (false, i, f i) * X (true, i, f i) : MvPolynomial (Bool × Fin k × Fin w) K) =
        monomial (Finsupp.single (false, i, f i) 1 + Finsupp.single (true, i, f i) 1) 1 := by
    rw [X, X, monomial_mul_monomial, one_mul]
  calc ∏ i : Fin k, (X (false, i, f i) * X (true, i, f i) : MvPolynomial _ K)
      = ∏ i : Fin k, monomial (Finsupp.single (false, i, f i) 1 +
          Finsupp.single (true, i, f i) 1) (1 : K) := prod_congr rfl fun i _ => hterm i
    _ = monomial (∑ i : Fin k, (Finsupp.single (false, i, f i) 1 +
          Finsupp.single (true, i, f i) 1)) (∏ _i : Fin k, (1 : K)) :=
        (monomial_sum_prod _ _ _).symm
    _ = _ := by rw [prod_const_one]

/-- `splitBilinearPoly K k w` is set-multilinear on all `2 * k` blocks. -/
theorem isSetMultilinear_splitBilinearPoly [CommSemiring K] (k w : ℕ) :
    IsSetMultilinear (splitBlock k w) univ (splitBilinearPoly K k w) := by
  have hfac (i : Fin k) :
      IsSetMultilinear (splitBlock k w)
        ({⟨i.1, by omega⟩, ⟨k + i.1, by omega⟩} : Finset (Fin (2 * k)))
        (∑ a : Fin w, (X (false, i, a) * X (true, i, a) : MvPolynomial _ K)) := by
    refine IsSetMultilinear.sum univ fun a _ => ?_
    have hdisj : Disjoint ({⟨i.1, by omega⟩} : Finset (Fin (2 * k))) {⟨k + i.1, by omega⟩} := by
      rw [disjoint_singleton]
      intro h
      have := congrArg Fin.val h
      dsimp only at this
      omega
    have hmul := (isSetMultilinear_X (K := K) (splitBlock k w) (false, i, a)).mul
      (isSetMultilinear_X (K := K) (splitBlock k w) (true, i, a)) hdisj
    have hset : ({splitBlock k w (false, i, a)} ∪ {splitBlock k w (true, i, a)}) =
        ({⟨i.1, by omega⟩, ⟨k + i.1, by omega⟩} : Finset (Fin (2 * k))) := by
      ext x
      simp [splitBlock]
    exact hset ▸ hmul
  have hTdisj : ((univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun i : Fin k => ({⟨i.1, by omega⟩, ⟨k + i.1, by omega⟩} : Finset (Fin (2 * k)))) := by
    intro i _ j _ hij
    change Disjoint _ _
    rw [disjoint_left]
    intro x hxi hxj
    simp only [mem_insert, mem_singleton] at hxi hxj
    rcases hxi with rfl | rfl <;> rcases hxj with h | h <;>
      have hv := congrArg Fin.val h <;> dsimp only at hv <;>
      exact hij (Fin.ext (by omega))
  have hunion : (univ : Finset (Fin k)).biUnion
      (fun i : Fin k => ({⟨i.1, by omega⟩, ⟨k + i.1, by omega⟩} : Finset (Fin (2 * k)))) =
      univ := by
    ext x
    simp only [mem_biUnion, mem_univ, true_and, mem_insert, mem_singleton, iff_true]
    by_cases hx : x.1 < k
    · exact ⟨⟨x.1, hx⟩, Or.inl (Fin.ext rfl)⟩
    · exact ⟨⟨x.1 - k, by omega⟩, Or.inr (Fin.ext (by dsimp only; omega))⟩
  simpa [splitBilinearPoly, hunion] using
    IsSetMultilinear.prod (univ : Finset (Fin k)) hTdisj fun i _ => hfac i

/-- Equivalence between left-block choices and tuples `Fin k → Fin w`. -/
@[expose] def leftBlockChoiceEquiv (k w : ℕ) :
    BlockChoice (splitBlock k w) (splitLeftBlocks k) ≃ (Fin k → Fin w) where
  toFun r i := (r ⟨⟨i.1, by omega⟩, mem_image_of_mem _ (mem_univ i)⟩).1.2.2
  invFun f b :=
    let i : Fin k := ⟨b.1.1, by
      obtain ⟨j, -, hj⟩ := mem_image.1 b.2
      have hv := congrArg Fin.val hj
      dsimp only at hv
      omega⟩
    ⟨(false, i, f i), Fin.ext (by dsimp only [splitBlock, i])⟩
  left_inv r := by
    funext ⟨b, hb⟩
    obtain ⟨j, -, rfl⟩ := mem_image.1 hb
    apply Subtype.ext
    rcases hr : (r ⟨⟨j.1, by omega⟩, hb⟩).1 with ⟨fl, idx, val⟩
    have hblk := (r ⟨⟨j.1, by omega⟩, hb⟩).2
    rw [hr] at hblk
    cases fl with
    | false =>
      have hidx : idx = j := Fin.ext (by simpa [splitBlock] using congrArg Fin.val hblk)
      subst hidx
      dsimp only
      simp [hr]
    | true =>
      have hv := congrArg Fin.val hblk
      simp only [splitBlock] at hv
      omega
  right_inv f := by
    funext i
    rfl

/-- Equivalence between right-block choices and tuples `Fin k → Fin w`. -/
@[expose] def rightBlockChoiceEquiv (k w : ℕ) :
    BlockChoice (splitBlock k w) (splitRightBlocks k) ≃ (Fin k → Fin w) where
  toFun c i := (c ⟨⟨k + i.1, by omega⟩, mem_image_of_mem _ (mem_univ i)⟩).1.2.2
  invFun g b :=
    let i : Fin k := ⟨b.1.1 - k, by
      obtain ⟨j, -, hj⟩ := mem_image.1 b.2
      have hv := congrArg Fin.val hj
      dsimp only at hv
      omega⟩
    ⟨(true, i, g i), Fin.ext (by
      obtain ⟨j, -, hj⟩ := mem_image.1 b.2
      have hv := congrArg Fin.val hj
      dsimp only [splitBlock, i] at hv ⊢
      omega)⟩
  left_inv c := by
    funext ⟨b, hb⟩
    obtain ⟨j, -, rfl⟩ := mem_image.1 hb
    apply Subtype.ext
    rcases hc : (c ⟨⟨k + j.1, by omega⟩, hb⟩).1 with ⟨fl, idx, val⟩
    have hblk := (c ⟨⟨k + j.1, by omega⟩, hb⟩).2
    rw [hc] at hblk
    cases fl with
    | false =>
      have hv := congrArg Fin.val hblk
      simp only [splitBlock] at hv
      omega
    | true =>
      have hidx : idx = j := Fin.ext (by
        have hv := congrArg Fin.val hblk
        simp only [splitBlock] at hv
        omega)
      subst hidx
      dsimp only
      have hcoe : ∀ (x y : splitRightBlocks k), x = y → (c x).1 = (c y).1 := by
        rintro x _ rfl; rfl
      rw [hcoe _ ⟨⟨k + idx.1, by omega⟩, hb⟩ (Subtype.ext (Fin.ext (by simp))), hc]
      exact Prod.ext rfl (Prod.ext (Fin.ext (by simp)) rfl)
  right_inv g := by
    funext i
    simp

private theorem blockMonomial_left_add_right (k w : ℕ) (f g : Fin k → Fin w) :
    blockMonomial (splitBlock k w) (splitLeftBlocks k) ((leftBlockChoiceEquiv k w).symm f) +
      blockMonomial (splitBlock k w) (splitRightBlocks k) ((rightBlockChoiceEquiv k w).symm g) =
      ∑ i : Fin k, (Finsupp.single (false, i, f i) 1 + Finsupp.single (true, i, g i) 1) := by
  classical
  ext ⟨fl, i, a⟩
  rw [Finsupp.add_apply, blockMonomial_apply, blockMonomial_apply, Finsupp.finsetSum_apply]
  cases fl with
  | false =>
    have hL : splitBlock k w (false, i, a) ∈ splitLeftBlocks k :=
      mem_image_of_mem _ (mem_univ i)
    have hR : splitBlock k w (false, i, a) ∉ splitRightBlocks k := by
      intro h
      obtain ⟨j, -, hj⟩ := mem_image.1 h
      have hv := congrArg Fin.val hj
      simp only [splitBlock] at hv
      omega
    rw [dite_eq_left hL, dite_eq_right hR, add_zero]
    rw [Finset.sum_eq_single i]
    · have hval : ((leftBlockChoiceEquiv k w).symm f
          ⟨splitBlock k w (false, i, a), hL⟩).1 = (false, i, f i) := rfl
      rw [hval]
      simp [Finsupp.single_apply]
    · intro j _ hji
      simp [hji]
    · intro hi; exact absurd (mem_univ i) hi
  | true =>
    have hL : splitBlock k w (true, i, a) ∉ splitLeftBlocks k := by
      intro h
      obtain ⟨j, -, hj⟩ := mem_image.1 h
      have hv := congrArg Fin.val hj
      simp only [splitBlock] at hv
      omega
    have hR : splitBlock k w (true, i, a) ∈ splitRightBlocks k :=
      mem_image_of_mem _ (mem_univ i)
    rw [dite_eq_right hL, dite_eq_left hR, zero_add]
    rw [Finset.sum_eq_single i]
    · have hval : ((rightBlockChoiceEquiv k w).symm g
          ⟨splitBlock k w (true, i, a), hR⟩).1 = (true, i, g i) := by
        have hi : (⟨k + i.1 - k, by omega⟩ : Fin k) = i :=
          Fin.ext (Nat.add_sub_cancel_left k i.1)
        exact Prod.ext rfl (Prod.ext hi (congrArg g hi))
      rw [hval]
      simp [Finsupp.single_apply]
    · intro j _ hji
      simp [hji]
    · intro hi; exact absurd (mem_univ i) hi

/-- Reindexing the relative-rank matrix of `splitBilinearPoly K k w` across its left and right
blocks gives the `w ^ k × w ^ k` identity matrix. -/
theorem relMatrix_splitBilinearPoly_submatrix [CommSemiring K] (k w : ℕ) :
    (relMatrix (splitBlock k w) (splitLeftBlocks k) (splitRightBlocks k)
      (splitBilinearPoly K k w)).submatrix
        (leftBlockChoiceEquiv k w).symm (rightBlockChoiceEquiv k w).symm = 1 := by
  classical
  ext f g
  rw [Matrix.submatrix_apply, relMatrix_apply, blockMonomial_left_add_right,
    splitBilinearPoly_eq_sum, coeff_sum, Matrix.one_apply]
  have hinj : ∀ h : Fin k → Fin w,
      (∑ i : Fin k, (Finsupp.single (false, i, h i) 1 + Finsupp.single (true, i, h i) 1)) =
      (∑ i : Fin k, (Finsupp.single (false, i, f i) 1 + Finsupp.single (true, i, g i) 1)) ↔
      h = f ∧ f = g := by
    intro h
    constructor
    · intro heq
      have hfl (i : Fin k) : h i = f i := by
        have hv := congrArg (fun u : Bool × Fin k × Fin w →₀ ℕ => u (false, i, h i)) heq
        simp only [Finsupp.finsetSum_apply, Finsupp.add_apply, Finsupp.single_apply] at hv
        have hlhs :
            (∑ j : Fin k, ((if (false, j, h j) = (false, i, h i) then 1 else 0) +
              (if (true, j, h j) = (false, i, h i) then 1 else 0))) = 1 := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji; simp [hji]
          · intro hi; exact absurd (mem_univ i) hi
        have hrhs :
            (∑ j : Fin k, ((if (false, j, f j) = (false, i, h i) then 1 else 0) +
              (if (true, j, g j) = (false, i, h i) then 1 else 0))) =
            if f i = h i then 1 else 0 := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji; simp [hji]
          · intro hi; exact absurd (mem_univ i) hi
        rw [hlhs, hrhs] at hv
        split_ifs at hv with h'
        exact h'.symm
      have htr (i : Fin k) : h i = g i := by
        have hv := congrArg (fun u : Bool × Fin k × Fin w →₀ ℕ => u (true, i, h i)) heq
        simp only [Finsupp.finsetSum_apply, Finsupp.add_apply, Finsupp.single_apply] at hv
        have hlhs :
            (∑ j : Fin k, ((if (false, j, h j) = (true, i, h i) then 1 else 0) +
              (if (true, j, h j) = (true, i, h i) then 1 else 0))) = 1 := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji; simp [hji]
          · intro hi; exact absurd (mem_univ i) hi
        have hrhs :
            (∑ j : Fin k, ((if (false, j, f j) = (true, i, h i) then 1 else 0) +
              (if (true, j, g j) = (true, i, h i) then 1 else 0))) =
            if g i = h i then 1 else 0 := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji; simp [hji]
          · intro hi; exact absurd (mem_univ i) hi
        rw [hlhs, hrhs] at hv
        split_ifs at hv with h'
        exact h'.symm
      exact ⟨funext hfl, funext fun i => (hfl i).symm.trans (htr i)⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  simp only [coeff_monomial, hinj]
  by_cases hfg : f = g
  · subst hfg
    rw [ite_eq_left rfl, Finset.sum_eq_single f]
    · simp
    · intro h _ hne; simp [hne]
    · intro hf; exact absurd (mem_univ f) hf
  · rw [ite_eq_right hfg]
    exact sum_eq_zero fun h _ => by simp [hfg]

/-- **Full rank of `splitBilinearPoly`**: its relative-rank matrix has rank `w ^ k`. -/
theorem rank_relMatrix_splitBilinearPoly [Field K] (k w : ℕ) :
    (relMatrix (splitBlock k w) (splitLeftBlocks k) (splitRightBlocks k)
      (splitBilinearPoly K k w)).rank = w ^ k := by
  have h := congrArg Matrix.rank (relMatrix_splitBilinearPoly_submatrix (K := K) k w)
  rw [Matrix.rank_submatrix, Matrix.rank_one, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin] at h
  exact h

/-- **Maximum relative rank (`relRank = 1`)**: `splitBilinearPoly K k w` attains relative rank
equal to `1` whenever `0 < w ^ k` (for example, whenever `1 ≤ w`). -/
theorem relRank_splitBilinearPoly [Field K] {k w : ℕ} (hpos : 0 < w ^ k) :
    relRank (splitBlock k w) (splitLeftBlocks k) (splitRightBlocks k)
      (splitBilinearPoly K k w) = 1 := by
  rw [relRank, rank_relMatrix_splitBilinearPoly,
    Fintype.card_congr (leftBlockChoiceEquiv k w),
    Fintype.card_congr (rightBlockChoiceEquiv k w),
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hne : ((w ^ k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [Nat.cast_mul, Real.sqrt_mul_self (Nat.cast_nonneg _), div_self hne]

/-! #### Partial-derivative space lower bound and depth-3 vs. depth-4 separation -/

private theorem pderiv_bilinearBlock [CommSemiring K] (k w : ℕ) (i j : Fin k) (a : Fin w) :
    pderiv (false, i, a)
      (∑ b : Fin w, (X (false, j, b) * X (true, j, b) :
        MvPolynomial (Bool × Fin k × Fin w) K)) =
      if j = i then X (true, i, a) else 0 := by
  simp only [map_sum, Derivation.leibniz, pderiv_X, smul_eq_mul]
  by_cases hji : j = i
  · subst hji
    rw [ite_eq_left rfl, Finset.sum_eq_single a]
    · simp
    · intro b _ hba
      simp [hba]
    · intro ha; exact absurd (mem_univ a) ha
  · rw [ite_eq_right hji]
    refine sum_eq_zero fun b _ => ?_
    simp [hji]

private theorem pderiv_finset_prod' [CommSemiring K] {σ ι : Type*} [DecidableEq ι]
    (v : σ) (s : Finset ι) (f : ι → MvPolynomial σ K) :
    pderiv v (∏ j ∈ s, f j) = ∑ j ∈ s, pderiv v (f j) * ∏ j' ∈ s.erase j, f j' := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, Derivation.leibniz, ih, erase_insert ha]
    simp only [smul_eq_mul, mul_sum]
    rw [add_comm, mul_comm (∏ x ∈ s, f x)]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    have hne : j ≠ a := fun h => ha (h ▸ hj)
    rw [erase_insert_of_ne hne.symm, prod_insert (fun h => ha (mem_of_mem_erase h))]
    ring

/-- Differentiating `splitBilinearPoly K k w` along the left variables `(false, i, f i)` yields
the pure right monomial `∏ i, X (true, i, f i)`. -/
theorem iteratedPDeriv_splitBilinearPoly [CommSemiring K] (k w : ℕ) (f : Fin k → Fin w) :
    iteratedPDeriv (fun i : Fin k => (false, i, f i)) (splitBilinearPoly K k w) =
      ∏ i : Fin k, X (true, i, f i) := by
  classical
  let B : Fin k → MvPolynomial (Bool × Fin k × Fin w) K :=
    fun i => ∑ a : Fin w, X (false, i, a) * X (true, i, a)
  have hgen : ∀ {m : ℕ} (e : Fin m → Fin k) (_he : Function.Injective e) (S : Finset (Fin k)),
      (∀ t, e t ∈ S) →
      iteratedPDeriv (fun t : Fin m => (false, e t, f (e t))) (∏ i ∈ S, B i) =
        (∏ t : Fin m, X (true, e t, f (e t))) * ∏ i ∈ S \ univ.image e, B i := by
    intro m
    induction m with
    | zero =>
      intro e _ S _
      simp
    | succ m ih =>
      intro e he S hS
      have htail : Fin.tail (fun t : Fin (m + 1) => (false, e t, f (e t))) =
          fun t : Fin m => (false, (e ∘ Fin.succ) t, f ((e ∘ Fin.succ) t)) := rfl
      rw [iteratedPDeriv_succ_apply, htail,
        ih (e ∘ Fin.succ) (he.comp (Fin.succ_injective m)) S fun t => hS t.succ,
        Derivation.leibniz]
      have hleft0 :
          pderiv (false, e 0, f (e 0))
            (∏ t : Fin m, (X (true, (e ∘ Fin.succ) t, f ((e ∘ Fin.succ) t)) :
              MvPolynomial (Bool × Fin k × Fin w) K)) = 0 := by
        rw [pderiv_finset_prod']
        refine sum_eq_zero fun t _ => ?_
        rw [pderiv_X, Pi.single_eq_of_ne (by simp), zero_mul]
      rw [hleft0, smul_zero, add_zero, smul_eq_mul, pderiv_finset_prod']
      have he0_not : e 0 ∉ univ.image (e ∘ Fin.succ) := by
        simpa using fun t h => Fin.succ_ne_zero t (he h)
      have he0_mem : e 0 ∈ S \ univ.image (e ∘ Fin.succ) :=
        mem_sdiff.2 ⟨hS 0, he0_not⟩
      rw [Finset.sum_eq_single (e 0)]
      · rw [pderiv_bilinearBlock, ite_eq_left rfl]
        have himg : univ.image e = insert (e 0) (univ.image (e ∘ Fin.succ)) := by
          ext x
          simp [Fin.exists_fin_succ, eq_comm]
        have herase : (S \ univ.image (e ∘ Fin.succ)).erase (e 0) = S \ univ.image e := by
          rw [himg, sdiff_insert]
        rw [herase, Fin.prod_univ_succ]
        simp only [comp_apply]
        ring
      · intro j _ hjne
        rw [pderiv_bilinearBlock, ite_eq_right hjne, zero_mul]
      · intro hnot; exact absurd he0_mem hnot
  have h0 := hgen id injective_id univ fun _ => mem_univ _
  have hsdiff : (univ : Finset (Fin k)) \ univ.image id = ∅ := by simp
  simpa [splitBilinearPoly, B, hsdiff] using h0

/-- **Partial-derivative rank lower bound for `splitBilinearPoly`**: the order-`k` partial
derivatives of `splitBilinearPoly K k w` span a space of dimension at least `w ^ k` over any
field `K`. -/
theorem pow_le_rank_partialDerivatives_splitBilinearPoly [Field K] (k w : ℕ) :
    ((w ^ k : ℕ) : Cardinal) ≤ (partialDerivatives k (splitBilinearPoly K k w)).rank := by
  classical
  let pt (f : Fin k → Fin w) : Bool × Fin k × Fin w → K :=
    fun v => if v.1 = true ∧ v.2.2 = f v.2.1 then 1 else 0
  let E : MvPolynomial (Bool × Fin k × Fin w) K →ₗ[K] (Fin k → Fin w) → K :=
    LinearMap.pi fun f => (aeval (pt f)).toLinearMap
  have key (f g : Fin k → Fin w) :
      E (iteratedPDeriv (fun i : Fin k => (false, i, f i)) (splitBilinearPoly K k w)) g =
        if f = g then 1 else 0 := by
    change MvPolynomial.eval (pt g) _ = _
    rw [iteratedPDeriv_splitBilinearPoly, map_prod]
    simp only [eval_X, pt, true_and, prod_boole]
    by_cases hfg : f = g
    · subst hfg
      simp
    · rw [ite_eq_right hfg, ite_eq_right]
      intro hall
      exact hfg (funext fun i => hall i (mem_univ i))
  have htop : LinearMap.range (E ∘ₗ partialDerivatives k (splitBilinearPoly K k w)) = ⊤ := by
    refine eq_top_iff.2 (((Pi.basisFun K (Fin k → Fin w)).span_eq).symm.le.trans
      (Submodule.span_le.2 ?_))
    rintro _ ⟨f, rfl⟩
    refine ⟨Pi.single (fun i : Fin k => (false, i, f i)) (1 : K), funext fun g => ?_⟩
    simp only [LinearMap.comp_apply, partialDerivatives_apply,
      Fintype.linearCombination_apply_single, one_smul, key, Pi.basisFun_apply, Pi.single_apply]
    by_cases h : f = g
    · subst h; simp
    · simp [h, Ne.symm h]
  calc ((w ^ k : ℕ) : Cardinal) = Module.rank K ((Fin k → Fin w) → K) := by
        rw [rank_fun', Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    _ = (E ∘ₗ partialDerivatives k (splitBilinearPoly K k w)).rank := by
        rw [LinearMap.rank, htop, rank_top]
    _ ≤ _ := LinearMap.rank_comp_le_right _ _

/-- **Exponential depth-three lower bound for `splitBilinearPoly`**: every depth-three circuit of
product fan-in at most `d` computing `splitBilinearPoly K k w` over any field `K` satisfies
`w ^ k ≤ d.choose k * cost`. -/
theorem pow_le_mul_cost_splitBilinearPoly [Field K] {k w d m : ℕ}
    (c : Circuit (SumOfTerms.signature (DepthThree.Term K (Bool × Fin k × Fin w) d)) 0 m)
    (j : Fin m)
    (hcompute : c.eval (SumOfTerms.interpretation DepthThree.Term.polynomial) Fin.elim0 j =
      splitBilinearPoly K k w) :
    w ^ k ≤ d.choose k * c.program.cost SumOfTerms.termCost := by
  have h := DepthThree.rank_partialDerivatives_le_mul_cost c k j
  rw [hcompute] at h
  exact_mod_cast (pow_le_rank_partialDerivatives_splitBilinearPoly k w).trans h

/-- **Concrete exponential lower bound (`2 ^ k ≤ cost`)**: every homogeneous depth-three circuit
(product fan-in at most `2 * k`) computing `splitBilinearPoly K k 8` over any field `K` uses at
least `2 ^ k` product gates. -/
theorem two_pow_le_cost_splitBilinearPoly [Field K] {k m : ℕ}
    (c : Circuit (SumOfTerms.signature (DepthThree.Term K (Bool × Fin k × Fin 8) (2 * k))) 0 m)
    (j : Fin m)
    (hcompute : c.eval (SumOfTerms.interpretation DepthThree.Term.polynomial) Fin.elim0 j =
      splitBilinearPoly K k 8) :
    2 ^ k ≤ c.program.cost SumOfTerms.termCost := by
  have h := pow_le_mul_cost_splitBilinearPoly c j hcompute
  have hbin : (2 * k).choose k ≤ 4 ^ k := by
    calc (2 * k).choose k
        ≤ ∑ i ∈ range (2 * k + 1), (2 * k).choose i :=
          single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.2 (by omega))
      _ = 2 ^ (2 * k) := Nat.sum_range_choose (2 * k)
      _ = 4 ^ k := by rw [pow_mul]; norm_num
  have hmul : 2 ^ k * 4 ^ k ≤ 4 ^ k * c.program.cost SumOfTerms.termCost := by
    calc 2 ^ k * 4 ^ k = 8 ^ k := by rw [← mul_pow]; norm_num
      _ ≤ (2 * k).choose k * c.program.cost SumOfTerms.termCost := h
      _ ≤ 4 ^ k * c.program.cost SumOfTerms.termCost := Nat.mul_le_mul_right _ hbin
  rw [mul_comm (2 ^ k)] at hmul
  exact Nat.le_of_mul_le_mul_left hmul (by positivity)

/-- Numbering of the `2 * k * w` variables of `splitBilinearPoly K k w`. -/
@[expose] def splitVarEquiv (k w : ℕ) : Fin (2 * (k * w)) ≃ Bool × Fin k × Fin w :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr
      { toFun := fun b : Fin 2 => b = 1
        invFun := fun b => if b then 1 else 0
        left_inv := fun b => by fin_cases b <;> rfl
        right_inv := fun b => by cases b <;> rfl }
      finProdFinEquiv.symm)

/-- **Linear-size set-multilinear product-depth-two formula for `splitBilinearPoly`**:
`∏ i < k, ∑ a < w, X (false, i, a) * X (true, i, a)` has `k * (3 * w + 1) + 1` nodes and
product-depth at most `2`. -/
@[expose] def splitBilinearFormula (K : Type*) [One K] (k w : ℕ) :
    SPFormula K (2 * (k * w)) :=
  SPFormula.mul fun i : Fin k =>
    SPFormula.add (fun _ : Fin w => (1 : K)) fun a : Fin w =>
      SPFormula.mul fun b : Fin 2 =>
        .input ((splitVarEquiv k w).symm (b = 1, i, a))

/-- **Concrete witness and depth-3 vs. depth-4 separation**: for every `k` and `w`,
`splitBilinearFormula K k w` is syntactically (hence semantically) set-multilinear on all `2 * k`
blocks, has product-depth at most `2`, has exactly `k * (3 * w + 1) + 1` nodes, and computes
`splitBilinearPoly K k w` after variable renaming. -/
theorem splitBilinearFormula_witness [CommSemiring K] (k w : ℕ) :
    (splitBilinearFormula K k w).IsSetMultilinear
        (fun v => splitBlock k w (splitVarEquiv k w v)) univ ∧
      (splitBilinearFormula K k w).productDepth ≤ 2 ∧
      (splitBilinearFormula K k w).nodeCount = k * (3 * w + 1) + 1 ∧
      rename (splitVarEquiv k w) (splitBilinearFormula K k w).polynomial =
        splitBilinearPoly K k w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Syntactic set-multilinearity on all `2 * k` blocks.
    have hT : Pairwise (Disjoint on fun i : Fin k =>
        ({⟨i.1, by omega⟩, ⟨k + i.1, by omega⟩} : Finset (Fin (2 * k)))) := by
      intro i j hij
      change Disjoint _ _
      rw [disjoint_left]
      intro x hxi hxj
      simp only [mem_insert, mem_singleton] at hxi hxj
      rcases hxi with rfl | rfl <;> rcases hxj with h | h <;>
        have hv := congrArg Fin.val h <;> dsimp only at hv <;>
        exact hij (Fin.ext (by omega))
    have hunion : (univ : Finset (Fin k)).biUnion
        (fun i : Fin k => ({⟨i.1, by omega⟩, ⟨k + i.1, by omega⟩} : Finset (Fin (2 * k)))) =
        univ := by
      ext x
      simp only [mem_biUnion, mem_univ, true_and, mem_insert, mem_singleton, iff_true]
      by_cases hx : x.1 < k
      · exact ⟨⟨x.1, hx⟩, Or.inl (Fin.ext rfl)⟩
      · exact ⟨⟨x.1 - k, by omega⟩, Or.inr (Fin.ext (by dsimp only; omega))⟩
    rw [splitBilinearFormula, SPFormula.isSetMultilinear_mul_iff]
    refine ⟨fun i => {⟨i.1, by omega⟩, ⟨k + i.1, by omega⟩}, hT, fun i => ?_, hunion.symm⟩
    refine .add _ _ _ fun a => ?_
    rw [SPFormula.isSetMultilinear_mul_iff]
    refine ⟨fun b : Fin 2 => if b = 1 then {⟨k + i.1, by omega⟩} else {⟨i.1, by omega⟩},
      ?_, fun b => ?_, ?_⟩
    · intro b₁ b₂ hb
      change Disjoint _ _
      fin_cases b₁ <;> fin_cases b₂
      · exact absurd rfl hb
      · simp only [Fin.zero_eta, Fin.mk_one, show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte,
          disjoint_singleton]
        intro h; have hv := congrArg Fin.val h; dsimp only at hv; omega
      · simp only [Fin.mk_one, Fin.zero_eta, ↓reduceIte, show (0 : Fin 2) ≠ 1 by decide,
          disjoint_singleton]
        intro h; have hv := congrArg Fin.val h; dsimp only at hv; omega
      · exact absurd rfl hb
    · rw [SPFormula.isSetMultilinear_input_iff, Equiv.apply_symm_apply]
      fin_cases b <;> simp [splitBlock]
    · ext x
      simp only [mem_insert, mem_singleton, mem_biUnion, mem_univ, true_and, Fin.exists_fin_two,
        show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte]
  · -- Product-depth ≤ 2.
    rw [splitBilinearFormula, SPFormula.productDepth_mul]
    refine Nat.add_le_add_right (Finset.sup_le fun i _ => ?_) 1
    rw [SPFormula.productDepth_add]
    refine Finset.sup_le fun a _ => ?_
    rw [SPFormula.productDepth_mul]
    refine Nat.add_le_add_right (Finset.sup_le fun b _ => ?_) 1
    exact le_rfl
  · -- Exact node count `k * (3 * w + 1) + 1`.
    simp only [splitBilinearFormula, Formula.nodeCount_gate, Formula.nodeCount_input,
      sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  · -- Computed polynomial matches `splitBilinearPoly K k w`.
    simp only [splitBilinearFormula, SPFormula.polynomial_mul, SPFormula.polynomial_add,
      SPFormula.polynomial_input, map_prod, map_sum, map_mul, map_one, one_mul, rename_X,
      Equiv.apply_symm_apply, Fin.prod_univ_two, show decide ((0 : Fin 2) = 1) = false by decide,
      decide_true, splitBilinearPoly]

end SplitBilinear

end Cslib.Circuits.Arithmetic

end
