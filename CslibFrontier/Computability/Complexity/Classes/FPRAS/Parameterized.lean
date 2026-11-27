module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Computability.Complexity.Classes.FPRAS
public import CslibFrontier.Computability.Complexity.Classes.RP
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Completeness
public import CslibFrontier.Computability.Complexity.FineGrained.Randomized
public import CslibFrontier.Computability.Complexity.Parameterized
public import CslibFrontier.Computability.Complexity.Problems.SAT

import Cslib.Foundations.Data.Polynomial.Monotone
import CslibFrontier.Computability.Complexity.Classes.BPP.Amplification
import CslibFrontier.Computability.Complexity.Classes.NP.SelfReduction
import CslibFrontier.Computability.Complexity.Classes.Promise.Probabilistic
import CslibFrontier.Computability.Complexity.Classes.RP.Reduction
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Probabilistic.CoinTape
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Tactic.EncLen

/-!
# Parameterized Randomized Approximation Schemes (`FPTRAS`) and `FPRAS` Collapse Bridges

This module formalizes fixed-parameter tractable randomized approximation schemes (`FPTRAS`) on
multi-tape Turing machines, parsimonious and FPT-parsimonious reduction closure for `FPRAS` and
`FPTRAS`, positivity decision bridges from approximate counting to `BPP` and parameterized
bounded-error runtime (`SolvesWithErrorInTimeO`), and Ko's theorem (`SAT ∈ BPP → NP = RP`).

## Main definitions

* `Cslib.Complexity.IsFPTProbOn`: seeded probabilistic multi-tape computation running in
  fixed-parameter tractable time `F (κ b) * (|b| + 1) ^ d`.
* `Cslib.Complexity.IsFPTRAS`, `Cslib.Complexity.FPTRAS`: fixed-parameter tractable
  randomized approximation schemes for counting functions `f : α → ℕ` parameterized by `κ : α → ℕ`.
* `Cslib.Complexity.FPTParsimoniousReducible`: FPT-time parsimonious counting reductions with
  bounded output parameter.

## Main results

* `Cslib.Complexity.mem_BPP_pos_of_mem_FPRAS`: if `f ∈ FPRAS enc`, then
  `{x | 0 < f x} ∈ BPP enc`.
* `Cslib.Complexity.SAT_mem_RP_of_SAT_mem_BPP`,
  `Cslib.Complexity.NP_eq_RP_of_SAT_mem_BPP`,
  `Cslib.Complexity.NP_eq_RP_of_NP_subset_BPP`: Ko's self-reducibility collapse
  (`NP ⊆ BPP → NP = RP`).
* `Cslib.Complexity.mem_FPRAS_of_parsimoniousReducible`: `FPRAS` is closed under parsimonious
  polynomial-time reductions.
* `Cslib.Complexity.FPRAS_subset_FPTRAS`, `Cslib.Complexity.FPTRAS_eq_FPRAS_of_le`:
  `FPRAS ⊆ FPTRAS`, with equality on bounded parameters.
* `Cslib.Complexity.IsFPTRAS.approx`: `(ε, δ)` real-parameter guarantee for `FPTRAS`.
* `Cslib.Complexity.FPTParsimoniousReducible.mem_FPTRAS`: closure of `FPTRAS` under
  FPT-parsimonious reductions.
* `Cslib.Complexity.solvesWithErrorInTimeO_pos_of_mem_FPTRAS`: positivity decision for any
  `f ∈ FPTRAS enc κ` runs with bounded two-sided error in FPT time `F (κ x) * (|enc x| + 1) ^ d`.
-/

public section

namespace Cslib.Complexity

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

/-! ### Positivity Testing from `FPRAS` and Parsimonious Closure -/

section FPRASBridges

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}

/-- Within relative error `1 / 2`, any positive count `0 < c` forces a positive numerator
`0 < num`. -/
theorem pos_of_approxWithin_two {c num den : ℕ} (hc : 0 < c)
    (h : ApproxWithin c 2 num den) : 0 < num := by
  by_contra h0
  have hnum0 : num = 0 := Nat.eq_zero_of_not_pos h0
  obtain ⟨_, hle⟩ := h
  rw [hnum0] at hle
  simp only [Nat.cast_zero, zero_div, zero_sub, abs_neg] at hle
  have hc_pos : (0 : ℝ) < c := by exact_mod_cast hc
  rw [abs_of_pos hc_pos] at hle
  linarith

/-- **Dyer–Goldberg–Greenhill–Jerrum positivity decider**: if `A` is an `FPRAS` for `f : α → ℕ`,
then running `A x 2 2` and testing `0 < num` places `{x | 0 < f x}` in `BPP enc`. -/
theorem mem_BPP_pos_of_isFPRAS {f : α → ℕ} {A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)}
    (hA : IsFPRAS enc f A) : {x | 0 < f x} ∈ BPP enc := by
  rw [← ofSet_mem_PromiseBPP, mem_PromiseBPP_iff_exists_isPPTOn]
  let prep : α → α × (ℕ × ℕ) := fun x => (x, (2, 2))
  let post : ℕ × ℕ → Bool := fun out => !decide (out.1 = 0)
  have hprep : ComputableInPolyTime prep enc (encPair enc (encPair encUnary encUnary)) :=
    ComputableInPolyTime.id'.prod ((ComputableInPolyTime.const 2).prod
      (ComputableInPolyTime.const 2))
  have hpost : ComputableInPolyTime post (encPair encNat encNat) encBool :=
    ComputableInPolyTime.bool_not.comp
      (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.fst encNat encNat)
        (ComputableInPolyTime.const 0))
  refine ⟨fun x => post <$> A x 2 2, (hA.1.preprocess hprep).map hpost,
    fun x hx => ?_, fun x hx => ?_⟩
  · have hgood := hA.2 x 2 2 (by norm_num)
    have hnum : (1 : ℝ) - (1 / 2 : ℝ) ^ 2 = 3 / 4 := by norm_num
    rw [hnum] at hgood
    have hev : post = fun out : ℕ × ℕ => decide (out ∈ {o : ℕ × ℕ | o.1 ≠ 0}) := by
      ext out; simp [post]
    rw [hev, Cslib.ProbComp.probability_map_decide_mem]
    have hmono : ((ProbComp.eval (A x 2 2)).toOuterMeasure
        {out | ApproxWithin (f x) 2 out.1 out.2}).toReal ≤
        ((ProbComp.eval (A x 2 2)).toOuterMeasure {o : ℕ × ℕ | o.1 ≠ 0}).toReal :=
      Cslib.Probability.PMF.toOuterMeasure_toReal_mono _ fun out hout =>
        Nat.pos_iff_ne_zero.1 (pos_of_approxWithin_two hx hout)
    linarith
  · have hfx0 : f x = 0 := Nat.eq_zero_of_not_pos hx
    have hgood := hA.2 x 2 2 (by norm_num)
    have hnum : (1 : ℝ) - (1 / 2 : ℝ) ^ 2 = 3 / 4 := by norm_num
    rw [hnum, hfx0] at hgood
    have heq_eval : ProbComp.eval (Bool.not <$> (post <$> A x 2 2)) =
        ProbComp.eval ((fun out : ℕ × ℕ => decide (out ∈ {o : ℕ × ℕ | o.1 = 0})) <$> A x 2 2) := by
      rw [ProbComp.eval_map, ProbComp.eval_map, ProbComp.eval_map, _root_.PMF.map_comp]
      congr 1
      ext out; simp [post]
    have hpr_eq : Pr[Bool.not <$> (post <$> A x 2 2)] =
        Pr[(fun out : ℕ × ℕ => decide (out ∈ {o : ℕ × ℕ | o.1 = 0})) <$> A x 2 2] :=
      congrArg (fun μ => (μ true).toReal) heq_eval
    change 2 / 3 ≤ Pr[Bool.not <$> (post <$> A x 2 2)]
    rw [hpr_eq, Cslib.ProbComp.probability_map_decide_mem]
    have hmono : ((ProbComp.eval (A x 2 2)).toOuterMeasure
        {out | ApproxWithin 0 2 out.1 out.2}).toReal ≤
        ((ProbComp.eval (A x 2 2)).toOuterMeasure {o : ℕ × ℕ | o.1 = 0}).toReal :=
      Cslib.Probability.PMF.toOuterMeasure_toReal_mono _ fun out hout => hout.num_eq_zero
    linarith

/-- If a counting function `f` admits an `FPRAS`, its positivity decision problem lies in `BPP`. -/
theorem mem_BPP_pos_of_mem_FPRAS {f : α → ℕ} (hf : f ∈ FPRAS enc) :
    {x | 0 < f x} ∈ BPP enc := by
  obtain ⟨_, hA⟩ := hf
  exact mem_BPP_pos_of_isFPRAS hA

/-- **`FPRAS` is closed under parsimonious polynomial-time reductions.** -/
theorem mem_FPRAS_of_parsimoniousReducible {f : α → ℕ} {g : β → ℕ}
    (hred : ParsimoniousReducible enc encB f g) (hg : g ∈ FPRAS encB) : f ∈ FPRAS enc := by
  obtain ⟨r, hr, hfg⟩ := hred
  obtain ⟨A, hPPT, hprob⟩ := hg
  let mapIn : α × (ℕ × ℕ) → β × (ℕ × ℕ) := fun q => (r q.1, q.2)
  have hmap : ComputableInPolyTime mapIn
      (encPair enc (encPair encUnary encUnary))
      (encPair encB (encPair encUnary encUnary)) :=
    (hr.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _)
  refine ⟨fun x p t => A (r x) p t, hPPT.preprocess hmap, fun x p t hp => ?_⟩
  rw [hfg x]
  exact hprob (r x) p t hp

end FPRASBridges

/-! ### Ko's Theorem: `SAT ∈ BPP → NP = RP` -/

section KoCollapse

private theorem toOuterMeasure_take_wrong_le {α : Type} {enc : α ↪ List Bool}
    {q p : Polynomial ℕ} {V : α × List Bool → Bool} {A : Set α}
    (hV : DecidesWithErrorExponent enc q p V A) (a : α) [Decidable (a ∈ A)] {R : ℕ}
    (hR : p.eval (enc a).length ≤ R) :
    (BitString.uniformList R).toOuterMeasure
        {coins | V (a, coins.take (p.eval (enc a).length)) ≠ decide (a ∈ A)} ≤
      1 / 2 ^ q.eval (enc a).length := by
  set k := p.eval (enc a).length
  have hpre : {coins : List Bool | V (a, coins.take k) ≠ decide (a ∈ A)} =
      List.take k ⁻¹' ((fun coins => V (a, coins)) ⁻¹' {!decide (a ∈ A)}) := by
    ext coins
    cases V (a, coins.take k) <;> cases decide (a ∈ A) <;> simp
  rw [hpre, ← _root_.PMF.toOuterMeasure_map_apply, BitString.uniformList_take hR,
    ← _root_.PMF.toOuterMeasure_map_apply, _root_.PMF.toOuterMeasure_apply_singleton,
    BitString.uniformList_map_apply,
    ENNReal.div_le_iff (by simp) (by simp), one_div, ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (by simp) (by simp), mul_comm]
  by_cases ha : a ∈ A
  · exact_mod_cast (by simpa [ha] using (hV a).1 ha)
  · exact_mod_cast (by simpa [ha] using (hV a).2 ha)

/-- **Ko's Theorem for `SAT`**: if `SAT ∈ BPP encCNF`, then `SAT ∈ RP encCNF` by
amplifying the `BPP` solver to error `2 ^ (-(L + 1))`, running `SAT`'s downward self-reduction on
shared coins, and verifying the candidate certificate deterministically.
-/
theorem SAT_mem_RP_of_SAT_mem_BPP (h : SAT ∈ BPP encCNF) : SAT ∈ RP encCNF := by
  obtain ⟨p, V, hV, herr⟩ :=
    mem_BPP_iff_forall_decidesWithErrorExponent.1 h (Polynomial.X + 1)
  rw [← ofSet_mem_PromiseRP, mem_PromiseRP_iff_exists_isPPTOn]
  let qPoly : Polynomial ℕ :=
    Polynomial.X + (Polynomial.X + 1) * (8 * Polynomial.X + 11)
  let coinPoly : Polynomial ℕ := p.comp qPoly
  let coinLen : Logic.PL.CNF ℕ → ℕ := fun φ => coinPoly.eval (encCNF φ).length
  have hcoinLen : ComputableInPolyTime coinLen encCNF encUnary :=
    (ComputableInPolyTime.unary_eval coinPoly).comp (ComputableInPolyTime.encoding_length encCNF)
  let runDet : Logic.PL.CNF ℕ × List Bool → Bool := fun fc =>
    SAT.verifier (fc.1, SAT.search (fun ψ => V (ψ, fc.2.take (p.eval (encCNF ψ).length))) fc.1)
  have hrunDet : ComputableInPolyTime runDet (encPair encCNF encBits) encBool := by
    have hD : ComputableInPolyTime
        (fun q : (Logic.PL.CNF ℕ × List Bool) × Logic.PL.CNF ℕ =>
          V (q.2, q.1.2.take (p.eval (encCNF q.2).length)))
        (encPair (encPair encCNF encBits) encCNF) encBool :=
      hV.comp ((ComputableInPolyTime.snd _ _).prod
        (ComputableInPolyTime.bitsTakeWithInput (ComputableInPolyTime.fst _ _).snd'
          ((ComputableInPolyTime.unary_eval p).comp
            ((ComputableInPolyTime.encoding_length encCNF).comp (ComputableInPolyTime.snd _ _)))))
    have hsrch := SAT.computableInPolyTime_search
      (D := fun (fc : Logic.PL.CNF ℕ × List Bool) ψ => V (ψ, fc.2.take (p.eval (encCNF ψ).length)))
      hD (ComputableInPolyTime.fst encCNF encBits)
    exact SAT.computableInPolyTime_verifier.comp
      ((ComputableInPolyTime.fst encCNF encBits).prod hsrch)
  let M : Logic.PL.CNF ℕ → ProbComp Bool :=
    fun φ => (fun coins => runDet (φ, coins)) <$> BitString.sampleList (coinLen φ)
  refine ⟨M, hcoinLen.sampleList.map_with hrunDet, fun φ hφ => ?_, fun φ hφ hmem => ?_⟩
  · -- Completeness on `φ ∈ SAT`: union bound over the `k = φ.vars.length` exact self-reduction
    -- queries!
    classical
    let D_ex : Logic.PL.CNF ℕ → Bool := fun ψ => decide (ψ ∈ SAT)
    let k := φ.vars.length
    let L := (encCNF φ).length
    let ansAt (j : ℕ) : List (Logic.PL.Literal ℕ) :=
      (φ.vars.take j).foldl (SAT.selfReduceStep D_ex φ) []
    let queryAt (j : ℕ) : Logic.PL.CNF ℕ :=
      if hj : j < k then φ ++ SAT.units (ansAt j) ++ [[(φ.vars[j], true)]] else φ
    have hlen_ansAt (j : ℕ) (hj : j ≤ k) :
        (∀ l ∈ ansAt j, l.1 ∈ φ.vars) ∧ (ansAt j).length = j := by
      have hmap := SAT.map_fst_foldl_selfReduceStep D_ex φ (φ.vars.take j) []
      simp only [List.map_nil, List.nil_append] at hmap
      refine ⟨fun l hl => ?_, ?_⟩
      · have hfst : l.1 ∈ (ansAt j).map Prod.fst := List.mem_map.2 ⟨l, hl, rfl⟩
        rw [hmap] at hfst
        exact List.mem_of_mem_take hfst
      · have hlen := congrArg List.length hmap
        rw [List.length_map, List.length_take_of_le hj] at hlen
        exact hlen
    have hquery_bounds (j : ℕ) (hj : j < k) :
        L ≤ (encCNF (queryAt j)).length ∧ p.eval (encCNF (queryAt j)).length ≤ coinLen φ := by
      have hq_eq : queryAt j = φ ++ SAT.units (ansAt j) ++ [[(φ.vars[j], true)]] :=
        dite_eq_left hj
      rw [hq_eq]
      have h1 : L ≤ (encCNF (φ ++ SAT.units (ansAt j) ++ [[(φ.vars[j], true)]])).length := by
        rw [SAT.length_encCNF_append, SAT.length_encCNF_append]
        omega
      have h2 : (encCNF (φ ++ SAT.units (ansAt j) ++ [[(φ.vars[j], true)]])).length ≤
          SAT.queryBound L := by
        obtain ⟨hans_mem, hans_len⟩ := hlen_ansAt j hj.le
        have hunits := SAT.length_encCNF_units_le hans_mem
        have hv' := SAT.length_encCNF_unit_le (l := (φ.vars[j], true)) (List.getElem_mem hj)
        have hmul := Nat.mul_le_mul_right (8 * L + 11)
          ((hans_len.le.trans hj.le).trans (SAT.length_vars_le φ))
        rw [SAT.length_encCNF_append, SAT.length_encCNF_append, SAT.queryBound]
        nlinarith
      have hqPoly_eq : qPoly.eval L = SAT.queryBound L := by
        simp [qPoly, SAT.queryBound]
      refine ⟨h1, ?_⟩
      dsimp [coinLen, coinPoly]
      rw [Polynomial.eval_comp, hqPoly_eq]
      exact Polynomial.eval_mono p h2
    -- If `coins` answers every `queryAt j` (`j < k`) identically to `D_ex`, then `SAT.selfReduce`
    -- with `coins` equals `SAT.selfReduce D_ex φ`!
    let μ := BitString.uniformList (coinLen φ)
    let bad (j : ℕ) : Set (List Bool) :=
      {coins | V (queryAt j, coins.take (p.eval (encCNF (queryAt j)).length)) ≠ D_ex (queryAt j)}
    have hcongr_fold (coins : List Bool)
        (hgood : ∀ j < k, coins ∉ bad j) :
        ∀ j ≤ k, (φ.vars.take j).foldl
          (SAT.selfReduceStep (fun ψ => V (ψ, coins.take (p.eval (encCNF ψ).length))) φ) [] =
          ansAt j := by
      intro j hj
      induction j with
      | zero => simp [ansAt]
      | succ j ih =>
        have hlt : j < k := hj
        have htake_succ : φ.vars.take (j + 1) = φ.vars.take j ++ [φ.vars[j]] :=
          List.take_succ_eq_append_getElem hlt
        dsimp only [ansAt]
        rw [htake_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
          List.foldl_append, List.foldl_cons, List.foldl_nil, ih hlt.le]
        simp only [SAT.selfReduceStep]
        have hok : V (queryAt j, coins.take (p.eval (encCNF (queryAt j)).length)) =
            D_ex (queryAt j) := not_ne_iff.1 (hgood j hlt)
        have hq_eq : queryAt j = φ ++ SAT.units (ansAt j) ++ [[(φ.vars[j], true)]] :=
          dite_eq_left hlt
        rw [hq_eq] at hok
        rw [hok]
    have hfalse_sub : (fun coins => runDet (φ, coins)) ⁻¹' {false} ⊆
        ⋃ j ∈ Finset.range k, bad j := by
      intro coins hcoins
      by_contra hgood
      simp only [Set.mem_iUnion, Finset.mem_range, not_exists] at hgood
      have hsr : SAT.search (fun ψ => V (ψ, coins.take (p.eval (encCNF ψ).length))) φ =
          SAT.search D_ex φ := by
        unfold SAT.search SAT.selfReduce
        have htake_all : φ.vars.take k = φ.vars := List.take_length
        rw [← htake_all, hcongr_fold coins hgood k le_rfl]
      have hver_true : SAT.verifier (φ, SAT.search D_ex φ) = true :=
        SAT.verifier_search (fun ψ _ => decide_eq_true_iff) hφ
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hcoins
      dsimp only [runDet] at hcoins
      rw [hsr, hver_true] at hcoins
      cases hcoins
    have hbad_le (j : ℕ) (hj : j < k) : μ.toOuterMeasure (bad j) ≤ 1 / 2 ^ (L + 1) := by
      refine (toOuterMeasure_take_wrong_le herr (queryAt j) (hquery_bounds j hj).2).trans ?_
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      gcongr
      · norm_num
      · exact (hquery_bounds j hj).1
    have hfail : (μ.map fun coins => runDet (φ, coins)) false ≤ 1 / 2 := by
      rw [← _root_.PMF.toOuterMeasure_apply_singleton, _root_.PMF.toOuterMeasure_map_apply]
      calc μ.toOuterMeasure ((fun coins => runDet (φ, coins)) ⁻¹' {false})
          ≤ μ.toOuterMeasure (⋃ j ∈ Finset.range k, bad j) :=
            MeasureTheory.measure_mono hfalse_sub
        _ ≤ ∑ j ∈ Finset.range k, μ.toOuterMeasure (bad j) :=
            MeasureTheory.measure_biUnion_finset_le _ _
        _ ≤ ∑ _j ∈ Finset.range k, (1 / 2 ^ (L + 1) : ENNReal) :=
            Finset.sum_le_sum fun j hj => hbad_le j (Finset.mem_range.1 hj)
        _ ≤ 1 / 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_succ]
            have hkL : k ≤ L := SAT.length_vars_le φ
            have hk_pow : k ≤ 2 ^ L := hkL.trans Nat.lt_two_pow_self.le
            calc (k : ENNReal) * (1 / (2 ^ L * 2)) ≤ 2 ^ L * (1 / (2 ^ L * 2)) := by
                  gcongr; exact_mod_cast hk_pow
              _ = 1 / 2 := by
                  rw [← mul_div_assoc, ENNReal.mul_div_mul_left _ _ (by simp) (by simp)]
    -- Convert `(μ.map _) false ≤ 1 / 2` to `1 / 2 ≤ Pr[M φ]`
    have hlaw : ProbComp.eval (M φ) = μ.map fun coins => runDet (φ, coins) := by
      simp [M, μ, ProbComp.eval_map, BitString.eval_sampleList]
    have htrue_ge : (1 / 2 : ENNReal) ≤ (ProbComp.eval (M φ)) true := by
      rw [hlaw]
      calc (1 / 2 : ENNReal) = 1 - 1 / 2 := by rw [one_div, ENNReal.one_sub_inv_two]
        _ ≤ 1 - (μ.map fun coins => runDet (φ, coins)) false := tsub_le_tsub_left hfail 1
        _ = (μ.map fun coins => runDet (φ, coins)) true := by
            rw [← Cslib.Probability.PMF.apply_true_add_apply_false
              (μ.map fun coins => runDet (φ, coins)),
              ENNReal.add_sub_cancel_right (_root_.PMF.apply_ne_top _ _)]
    have hreal := ENNReal.toReal_mono (_root_.PMF.apply_ne_top _ _) htrue_ge
    simpa [one_div] using hreal
  · -- Soundness on `φ ∉ SAT`: `SAT.verifier` never accepts any certificate of an unsatisfiable CNF!
    simp only [M, ProbComp.eval_map, BitString.eval_sampleList,
      _root_.PMF.mem_support_map_iff] at hmem
    obtain ⟨coins, -, htrue⟩ := hmem
    exact hφ ⟨_, htrue⟩

/-- **Ko's Theorem (`SAT ∈ BPP → NP = RP`)**: if `SAT` lies in `BPP`, then `NP = RP` for every
instance encoding. -/
theorem NP_eq_RP_of_SAT_mem_BPP {α : Type} (h : SAT ∈ BPP encCNF) (enc : α ↪ List Bool) :
    NP enc = RP enc :=
  Set.Subset.antisymm
    (fun A hA => (CookLevin.SAT_npComplete.2 enc A hA).mem_RP (SAT_mem_RP_of_SAT_mem_BPP h))
    RP_subset_NP

/-- **Ko's Theorem (`NP ⊆ BPP → NP = RP`)**: if `NP ⊆ BPP` across encodings, then `NP = RP`. -/
theorem NP_eq_RP_of_NP_subset_BPP {α : Type}
    (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ BPP encB) (enc : α ↪ List Bool) :
    NP enc = RP enc :=
  NP_eq_RP_of_SAT_mem_BPP (h encCNF CookLevin.SAT_npComplete.1) enc

end KoCollapse

/-! ### Fixed-Parameter Tractable Randomized Approximation Schemes (`FPTRAS`) -/

section FPTRASDefs

variable {α β : Type}

/-- Seeded probabilistic program running in fixed-parameter tractable time with respect to `κ`:
both the unary coin-length function `ℓ` and the deterministic seeded evaluator `evalP` are
computable in FPT time (`Cslib.Complexity.ComputableInFPTTime`). -/
def IsFPTProbOn {γ δ : Type} (input : γ ↪ List Bool) (output : δ ↪ List Bool) (κ : γ → ℕ)
    (program : γ → ProbComp δ) : Prop :=
  ∃ (ℓ : γ → ℕ) (evalP : γ × List Bool → δ),
    ComputableInFPTTime ℓ input encUnary κ ∧
    ComputableInFPTTime evalP (encPair input encBits) output (fun p => κ p.1) ∧
    ∀ b, ProbComp.eval (program b) = (BitString.uniformList (ℓ b)).map (fun w => evalP (b, w))

/-- Every strict probabilistic polynomial-time program (`IsPPTOn`) runs in FPT time for every
parameter `κ`. -/
theorem IsFPTProbOn.of_isPPTOn {γ δ : Type} {input : γ ↪ List Bool} {output : δ ↪ List Bool}
    (κ : γ → ℕ) {program : γ → ProbComp δ} (h : IsPPTOn input output program) :
    IsFPTProbOn input output κ program := by
  obtain ⟨c, d, evaluate, heval, hlaw⟩ := h.exists_seeded_evaluator
  let ℓ : γ → ℕ := fun b => c * ((input b).length + 1) ^ d
  have hℓ : ComputableInPolyTime ℓ input encUnary := by
    dsimp [ℓ]; fun_prop
  exact ⟨ℓ, fun p => evaluate p.1 p.2, hℓ.computableInFPTTime κ,
    heval.computableInFPTTime (fun p => κ p.1), hlaw⟩

/-- When the parameter `κ` is bounded by a constant `K`, `IsFPTProbOn` collapses to `IsPPTOn`. -/
theorem IsFPTProbOn.isPPTOn_of_le {γ δ : Type} {input : γ ↪ List Bool} {output : δ ↪ List Bool}
    {κ : γ → ℕ} {K : ℕ} (hκ : ∀ b, κ b ≤ K) {program : γ → ProbComp δ}
    (h : IsFPTProbOn input output κ program) : IsPPTOn input output program := by
  obtain ⟨ℓ, evalP, ⟨F₁, c₁, hℓ⟩, ⟨F₂, c₂, heval⟩, hlaw⟩ := h
  let M₁ : ℕ := ∑ j ∈ Finset.range (K + 1), F₁ j
  let M₂ : ℕ := ∑ j ∈ Finset.range (K + 1), F₂ j
  have hle₁ (b : γ) : F₁ (κ b) ≤ M₁ :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le (hκ b)))
  have hle₂ (p : γ × List Bool) : F₂ (κ p.1) ≤ M₂ :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le (hκ p.1)))
  have hℓ_poly : ComputableInPolyTime ℓ input encUnary :=
    (hℓ.mono (fun b => Nat.mul_le_mul_right _ (hle₁ b))
      (fun b => Nat.mul_le_mul_right _ (hle₁ b))).computableInPolyTime
      (.of_forall_le M₁ c₁ fun _ => le_rfl)
  have heval_poly : ComputableInPolyTime evalP (encPair input encBits) output :=
    (heval.mono (fun p => Nat.mul_le_mul_right _ (hle₂ p))
      (fun p => Nat.mul_le_mul_right _ (hle₂ p))).computableInPolyTime
      (.of_forall_le M₂ c₂ fun _ => le_rfl)
  have hsample : IsPPTOn input output (fun b => (fun w => evalP (b,
    w)) <$> BitString.sampleList (ℓ b)) :=
    hℓ_poly.sampleList.map_with heval_poly
  exact hsample.congr fun b => by
    rw [ProbComp.eval_map, BitString.eval_sampleList, hlaw b]

/-- **A fixed-parameter tractable randomized approximation scheme (`FPTRAS`)** for the counting
function `f : α → ℕ` with respect to encoding `enc` and parameter `κ : α → ℕ`: `A x p t` runs in
probabilistic FPT time `F (κ x) * (|(x, p, t)| + 1) ^ d` (with `p, t` in unary, i.e., polynomial in
`|enc x|`, `1 / ε`, and `log (1 / δ)`) and outputs `(num, den)` within relative error `1 / p` of
`f x` with probability at least `1 - (1 / 2) ^ t` whenever `0 < p`. -/
def IsFPTRAS (enc : α ↪ List Bool) (κ : α → ℕ) (f : α → ℕ)
    (A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)) : Prop :=
  IsFPTProbOn (encPair enc (encPair encUnary encUnary)) (encPair encNat encNat)
      (fun q => κ q.1) (Function.uncurry fun x => Function.uncurry (A x)) ∧
    ∀ x p t, 0 < p → 1 - (1 / 2 : ℝ) ^ t ≤
      ((ProbComp.eval (A x p t)).toOuterMeasure
        {out | ApproxWithin (f x) p out.1 out.2}).toReal

/-- Counting functions `f : α → ℕ` admitting a fixed-parameter tractable randomized approximation
scheme with respect to `enc` and parameter `κ`. -/
@[expose] def FPTRAS (enc : α ↪ List Bool) (κ : α → ℕ) : Set (α → ℕ) :=
  {f | ∃ A, IsFPTRAS enc κ f A}

theorem mem_FPTRAS_iff {enc : α ↪ List Bool} {κ : α → ℕ} {f : α → ℕ} :
    f ∈ FPTRAS enc κ ↔ ∃ A, IsFPTRAS enc κ f A := by
  unfold FPTRAS; rfl

/-- Construct `f ∈ FPTRAS enc κ` directly from a seeded FPT coin-length map `ℓ` and deterministic
seeded evaluator `evalP`. -/
theorem mem_FPTRAS_of_seeded {enc : α ↪ List Bool} {κ : α → ℕ} {f : α → ℕ}
    (ℓ : α × (ℕ × ℕ) → ℕ) (evalP : (α × (ℕ × ℕ)) × List Bool → ℕ × ℕ)
    (hℓ : ComputableInFPTTime ℓ (encPair enc (encPair encUnary encUnary)) encUnary
      (fun q => κ q.1))
    (heval : ComputableInFPTTime evalP
      (encPair (encPair enc (encPair encUnary encUnary)) encBits)
      (encPair encNat encNat) (fun q => κ q.1.1))
    (hprob : ∀ x p t, 0 < p → 1 - (1 / 2 : ℝ) ^ t ≤
      (((BitString.uniformList (ℓ (x, (p, t)))).map (fun w => evalP ((x, (p, t)),
        w))).toOuterMeasure
        {out | ApproxWithin (f x) p out.1 out.2}).toReal) :
    f ∈ FPTRAS enc κ := by
  let A : α → ℕ → ℕ → ProbComp (ℕ × ℕ) := fun x p t =>
    (fun w => evalP ((x, (p, t)), w)) <$> BitString.sampleList (ℓ (x, (p, t)))
  refine ⟨A, ⟨ℓ, evalP, hℓ, heval, fun q => ?_⟩, fun x p t hp => ?_⟩
  · rcases q with ⟨x, p, t⟩
    simp [A, ProbComp.eval_map, BitString.eval_sampleList]
  · simp only [A, ProbComp.eval_map, BitString.eval_sampleList]
    exact hprob x p t hp

/-- **`FPRAS ⊆ FPTRAS`**, for every parameter `κ`. -/
theorem FPRAS_subset_FPTRAS {enc : α ↪ List Bool} {κ : α → ℕ} :
    FPRAS enc ⊆ FPTRAS enc κ := by
  intro _ ⟨A, hPPT, hprob⟩
  exact ⟨A, .of_isPPTOn _ hPPT, hprob⟩

/-- **Bounded parameters.** When `κ x ≤ K` for all instances `x`, `FPTRAS enc κ = FPRAS enc`. -/
theorem FPTRAS_eq_FPRAS_of_le {enc : α ↪ List Bool} {κ : α → ℕ} {K : ℕ}
    (hκ : ∀ x, κ x ≤ K) : FPTRAS enc κ = FPRAS enc := by
  exact Set.Subset.antisymm
    (fun _ ⟨A, hFPT, hprob⟩ => ⟨A, hFPT.isPPTOn_of_le (fun q => hκ q.1), hprob⟩)
    FPRAS_subset_FPTRAS

@[simp]
theorem FPTRAS_const_zero {enc : α ↪ List Bool} : FPTRAS enc (fun _ => 0) = FPRAS enc := by
  exact FPTRAS_eq_FPRAS_of_le fun _ => le_rfl

/-- **Real `(ε, δ)` approximation guarantee for `FPTRAS`**: running `A` at `p = ⌈ε⁻¹⌉₊` and
`t = Nat.clog 2 ⌈δ⁻¹⌉₊` achieves relative error `ε` with probability at least `1 - δ` in FPT time
`F (κ x) * poly(|enc x|, 1 / ε, log (1 / δ))`. -/
theorem IsFPTRAS.approx {enc : α ↪ List Bool} {κ : α → ℕ} {f : α → ℕ}
    {A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)} (hA : IsFPTRAS enc κ f A) (x : α) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    1 - δ ≤ ((ProbComp.eval (A x ⌈ε⁻¹⌉₊ (Nat.clog 2 ⌈δ⁻¹⌉₊))).toOuterMeasure
      {out | 0 < out.2 ∧ |(out.1 : ℝ) / out.2 - f x| ≤ ε * f x}).toReal := by
  have hp : 0 < ⌈ε⁻¹⌉₊ := Nat.ceil_pos.2 (inv_pos.2 hε)
  have hpow : (1 / 2 : ℝ) ^ Nat.clog 2 ⌈δ⁻¹⌉₊ ≤ δ := by
    have hle : (⌈δ⁻¹⌉₊ : ℝ) ≤ 2 ^ Nat.clog 2 ⌈δ⁻¹⌉₊ := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) _
    rw [one_div_pow, one_div]
    calc (2 ^ Nat.clog 2 ⌈δ⁻¹⌉₊ : ℝ)⁻¹ ≤ (δ⁻¹)⁻¹ :=
          inv_anti₀ (inv_pos.2 hδ) ((Nat.le_ceil _).trans hle)
      _ = δ := inv_inv δ
  have hinv : (1 : ℝ) / ⌈ε⁻¹⌉₊ ≤ ε := by
    rw [div_le_iff₀ (by exact_mod_cast hp), ← div_le_iff₀' hε, one_div]
    exact Nat.le_ceil _
  refine le_trans (sub_le_sub_left hpow 1) ((hA.2 x _ _ hp).trans ?_)
  apply Cslib.Probability.PMF.toOuterMeasure_toReal_mono
  rintro ⟨num, den⟩ ⟨hden, hle⟩
  refine ⟨hden, hle.trans ?_⟩
  rw [div_eq_mul_one_div, mul_comm]
  exact mul_le_mul_of_nonneg_right hinv (Nat.cast_nonneg _)

/-- **FPT-parsimonious counting reduction**: a map `r : α → β` computable in FPT time wrt `κA`
with `κB (r x) ≤ h (κA x)` and `f x = g (r x)` for all `x`. -/
@[expose] def FPTParsimoniousReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (κA : α → ℕ) (κB : β → ℕ) (f : α → ℕ) (g : β → ℕ) : Prop :=
  ∃ r : α → β, ComputableInFPTTime r encA encB κA ∧
    (∃ h : ℕ → ℕ, ∀ x, κB (r x) ≤ h (κA x)) ∧ ∀ x, f x = g (r x)

/-- **`FPTRAS` is closed under FPT-parsimonious reductions.** -/
theorem FPTParsimoniousReducible.mem_FPTRAS {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {κA : α → ℕ} {κB : β → ℕ} {f : α → ℕ} {g : β → ℕ}
    (hred : FPTParsimoniousReducible encA encB κA κB f g) (hg : g ∈ FPTRAS encB κB) :
    f ∈ FPTRAS encA κA := by
  obtain ⟨r, hr, ⟨h, hκ⟩, hfg⟩ := hred
  obtain ⟨A, ⟨ℓ, evalP, hℓ, heval, hlaw⟩, hprob⟩ := hg
  let encTA := encPair encA (encPair encUnary encUnary)
  let encTB := encPair encB (encPair encUnary encUnary)
  let mapT : α × (ℕ × ℕ) → β × (ℕ × ℕ) := fun q => (r q.1, q.2)
  -- `mapT` is computable in FPT time wrt `fun q => κA q.1`!
  have hmapT : ComputableInFPTTime mapT encTA encTB (fun q => κA q.1) := by
    have hfst_r : ComputableInFPTTime (fun q : α × (ℕ × ℕ) => r q.1) encTA encB
        (fun q => κA q.1) :=
      hr.comp ((ComputableInPolyTime.fst encA (encPair encUnary encUnary)).computableInFPTTime _)
        (h := id) (fun _ => le_rfl)
    have hsnd : ComputableInFPTTime (fun q : α × (ℕ × ℕ) => q.2) encTA
        (encPair encUnary encUnary) (fun q => κA q.1) :=
      (ComputableInPolyTime.snd encA (encPair encUnary encUnary)).computableInFPTTime _
    obtain ⟨F₁, c₁, h₁⟩ := hfst_r
    obtain ⟨F₂, c₂, h₂⟩ := hsnd
    have h1O := ComputableInO.of_bounds
      (T := fun q => F₁ (κA q.1) * ((encTA q).length + 1) ^ c₁)
      (S := fun q => F₁ (κA q.1) * ((encTA q).length + 1) ^ c₁)
      h₁ 1 (fun _ => by simp only [one_mul]; exact Nat.le_succ _)
      (fun _ => by simp only [one_mul]; exact Nat.le_succ _)
      fun a => (h₁.length_le a).trans (by simp only [one_mul]; exact Nat.le_succ _)
    have h2O := ComputableInO.of_bounds
      (T := fun q => F₂ (κA q.1) * ((encTA q).length + 1) ^ c₂)
      (S := fun q => F₂ (κA q.1) * ((encTA q).length + 1) ^ c₂)
      h₂ 1 (fun _ => by simp only [one_mul]; exact Nat.le_succ _)
      (fun _ => by simp only [one_mul]; exact Nat.le_succ _)
      fun a => (h₂.length_le a).trans (by simp only [one_mul]; exact Nat.le_succ _)
    have hprodO := h1O.prod h2O
    refine ComputableInO.computableInFPTTime (F := fun k => F₁ k + F₂ k + 2)
      (c := c₁ + c₂ + 1) (hprodO.mono_le (fun q => ?_) (fun q => ?_))
    all_goals
      have hp1 : ((encTA q).length + 1) ^ c₁ ≤ ((encTA q).length + 1) ^ (c₁ + c₂ + 1) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hp2 : ((encTA q).length + 1) ^ c₂ ≤ ((encTA q).length + 1) ^ (c₁ + c₂ + 1) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hm1 := Nat.mul_le_mul_left (F₁ (κA q.1)) hp1
      have hm2 := Nat.mul_le_mul_left (F₂ (κA q.1)) hp2
      rw [Nat.add_mul, Nat.add_mul]
      nlinarith [Nat.one_le_pow (c₁ + c₂ + 1) ((encTA q).length + 1) (Nat.succ_pos _)]
  have hℓ' : ComputableInFPTTime (ℓ ∘ mapT) encTA encUnary (fun q => κA q.1) :=
    hℓ.comp hmapT (fun q => hκ q.1)
  let mapSeed : (α × (ℕ × ℕ)) × List Bool → (β × (ℕ × ℕ)) × List Bool :=
    fun p => (mapT p.1, p.2)
  have hmapSeed : ComputableInFPTTime mapSeed (encPair encTA encBits) (encPair encTB encBits)
      (fun p => κA p.1.1) := by
    have hfst_m : ComputableInFPTTime (fun p : (α × (ℕ × ℕ)) × List Bool => mapT p.1)
        (encPair encTA encBits) encTB (fun p => κA p.1.1) :=
      hmapT.comp ((ComputableInPolyTime.fst encTA encBits).computableInFPTTime _)
        (h := id) (fun _ => le_rfl)
    have hsnd_m : ComputableInFPTTime (fun p : (α × (ℕ × ℕ)) × List Bool => p.2)
        (encPair encTA encBits) encBits (fun p => κA p.1.1) :=
      (ComputableInPolyTime.snd encTA encBits).computableInFPTTime _
    obtain ⟨F₁, c₁, h₁⟩ := hfst_m
    obtain ⟨F₂, c₂, h₂⟩ := hsnd_m
    have h1O := ComputableInO.of_bounds
      (T := fun p => F₁ (κA p.1.1) * ((encPair encTA encBits p).length + 1) ^ c₁)
      (S := fun p => F₁ (κA p.1.1) * ((encPair encTA encBits p).length + 1) ^ c₁)
      h₁ 1 (fun _ => by simp only [one_mul]; exact Nat.le_succ _)
      (fun _ => by simp only [one_mul]; exact Nat.le_succ _)
      fun a => (h₁.length_le a).trans (by simp only [one_mul]; exact Nat.le_succ _)
    have h2O := ComputableInO.of_bounds
      (T := fun p => F₂ (κA p.1.1) * ((encPair encTA encBits p).length + 1) ^ c₂)
      (S := fun p => F₂ (κA p.1.1) * ((encPair encTA encBits p).length + 1) ^ c₂)
      h₂ 1 (fun _ => by simp only [one_mul]; exact Nat.le_succ _)
      (fun _ => by simp only [one_mul]; exact Nat.le_succ _)
      fun a => (h₂.length_le a).trans (by simp only [one_mul]; exact Nat.le_succ _)
    refine ComputableInO.computableInFPTTime (F := fun k => F₁ k + F₂ k + 2)
      (c := c₁ + c₂ + 1) ((h1O.prod h2O).mono_le (fun p => ?_) (fun p => ?_))
    all_goals
      have hp1 : ((encPair encTA encBits p).length + 1) ^ c₁ ≤
          ((encPair encTA encBits p).length + 1) ^ (c₁ + c₂ + 1) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hp2 : ((encPair encTA encBits p).length + 1) ^ c₂ ≤
          ((encPair encTA encBits p).length + 1) ^ (c₁ + c₂ + 1) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hm1 := Nat.mul_le_mul_left (F₁ (κA p.1.1)) hp1
      have hm2 := Nat.mul_le_mul_left (F₂ (κA p.1.1)) hp2
      rw [Nat.add_mul, Nat.add_mul]
      nlinarith [Nat.one_le_pow (c₁ + c₂ + 1) ((encPair encTA encBits p).length + 1)
        (Nat.succ_pos _)]
  have heval' : ComputableInFPTTime (evalP ∘ mapSeed) (encPair encTA encBits)
      (encPair encNat encNat) (fun p => κA p.1.1) :=
    heval.comp hmapSeed (fun p => hκ p.1.1)
  refine ⟨fun x p t => A (r x) p t, ⟨ℓ ∘ mapT, evalP ∘ mapSeed, hℓ', heval',
    fun q => hlaw (mapT q)⟩,
    fun x p t hp => ?_⟩
  rw [hfg x]
  exact hprob (r x) p t hp

/-- **Parameter monotonicity for `FPTRAS`**: if `κ₁ x ≤ h (κ₂ x)` for all `x`, then
`FPTRAS enc κ₁ ⊆ FPTRAS enc κ₂`. -/
theorem FPTRAS_subset_FPTRAS_of_le_comp {enc : α ↪ List Bool} {κ₁ κ₂ : α → ℕ} {h : ℕ → ℕ}
    (hκ : ∀ x, κ₁ x ≤ h (κ₂ x)) : FPTRAS enc κ₁ ⊆ FPTRAS enc κ₂ := by
  intro f hf
  refine FPTParsimoniousReducible.mem_FPTRAS ?_ hf
  exact ⟨id, (ComputableInPolyTime.id' (encIn := enc)).computableInFPTTime κ₂, ⟨h, hκ⟩,
    fun _ => rfl⟩

/-- **Positivity decision from `FPTRAS` in randomized FPT time**: if `f ∈ FPTRAS enc κ`, then
deciding `{x | 0 < f x}` with bounded two-sided error (`ErrorModel.bounded`) runs in time
`O(F (κ x) * (|enc x| + 1) ^ d)` for some `F : ℕ → ℕ` and `d : ℕ`. -/
theorem solvesWithErrorInTimeO_pos_of_mem_FPTRAS {enc : α ↪ List Bool} {κ : α → ℕ} {f : α → ℕ}
    (hf : f ∈ FPTRAS enc κ) :
    ∃ (F : ℕ → ℕ) (d : ℕ),
      SolvesWithErrorInTimeO (PromiseProblem.ofSet {x | 0 < f x}) enc ErrorModel.bounded
        (fun x => (F (κ x) : ℝ) * ((enc x).length + 1) ^ d) := by
  obtain ⟨A, ⟨ℓ, evalP, hℓ, heval, hlaw⟩, hprob⟩ := hf
  let prep : α → α × (ℕ × ℕ) := fun x => (x, (2, 2))
  have hprep : ComputableInPolyTime prep enc (encPair enc (encPair encUnary encUnary)) :=
    ComputableInPolyTime.id'.prod ((ComputableInPolyTime.const 2).prod
      (ComputableInPolyTime.const 2))
  have hℓ_x : ComputableInFPTTime (ℓ ∘ prep) enc encUnary κ :=
    hℓ.comp (hprep.computableInFPTTime κ) (h := id) (fun _ => le_rfl)
  let post : ℕ × ℕ → Bool := fun out => !decide (out.1 = 0)
  have hpost : ComputableInPolyTime post (encPair encNat encNat) encBool :=
    ComputableInPolyTime.bool_not.comp
      (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.fst encNat encNat)
        (ComputableInPolyTime.const 0))
  let prepSeed : α × List Bool → (α × (ℕ × ℕ)) × List Bool := fun xw => (prep xw.1, xw.2)
  have hprepSeed : ComputableInPolyTime prepSeed (encPair enc encBits)
      (encPair (encPair enc (encPair encUnary encUnary)) encBits) :=
    (hprep.comp (ComputableInPolyTime.fst enc encBits)).prod (ComputableInPolyTime.snd enc encBits)
  let V : α × List Bool → Bool := post ∘ evalP ∘ prepSeed
  have hV_fpt : ComputableInFPTTime V (encPair enc encBits) encBool (fun xw => κ xw.1) :=
    (hpost.computableInFPTTime (fun _ => 0)).comp
      (heval.comp (hprepSeed.computableInFPTTime _) (h := id) (fun _ => le_rfl))
      (h := fun _ => 0) (fun _ => le_rfl)
  obtain ⟨F₁, c₁, hℓ_ts⟩ := hℓ_x
  obtain ⟨F₂, c₂, hV_ts⟩ := hV_fpt
  have hℓO := ComputableInO.of_bounds
    (T := fun x => F₁ (κ x) * ((enc x).length + 1) ^ c₁)
    (S := fun x => F₁ (κ x) * ((enc x).length + 1) ^ c₁)
    hℓ_ts 1 (fun _ => by simp only [one_mul]; exact Nat.le_succ _)
    (fun _ => by simp only [one_mul]; exact Nat.le_succ _)
    fun x => (hℓ_ts.length_le x).trans (by simp only [one_mul]; exact Nat.le_succ _)
  have hVO := ComputableInO.of_bounds
    (T := fun xw => F₂ (κ xw.1) * ((encPair enc encBits xw).length + 1) ^ c₂)
    (S := fun xw => F₂ (κ xw.1) * ((encPair enc encBits xw).length + 1) ^ c₂)
    hV_ts 1 (fun _ => by simp only [one_mul]; exact Nat.le_succ _)
    (fun _ => by simp only [one_mul]; exact Nat.le_succ _)
    fun p => (hV_ts.length_le p).trans (by simp only [one_mul]; exact Nat.le_succ _)
  -- Bound `|encPair enc encBits (x, w)|` when `w.length = (ℓ ∘ prep) x ≤ F₁ (κ x) * (|enc x| + 1) ^
  -- c₁`!
  let d : ℕ := (max c₁ 1) * (c₂ + 1)
  let F : ℕ → ℕ := fun k => 1 + F₁ k + F₂ k * (3 + F₁ k) ^ c₂
  refine ⟨F, d, ℓ ∘ prep, V, _, _, _, _, 1, hℓO, hVO, fun x w hw => ?_,
    fun x hx => ?_, fun x hx => ?_⟩
  · -- Runtime bound for `(x, w)` when `w.length = ℓ (prep x)`:
    have hlen_w : w.length ≤ F₁ (κ x) * ((enc x).length + 1) ^ c₁ := by
      have hlen_u := hℓ_ts.length_le x
      simpa [encUnary_apply, hw] using hlen_u
    set cM := max c₁ 1
    have hL1 : 1 ≤ ((enc x).length + 1) ^ cM := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hpow_c₁ : ((enc x).length + 1) ^ c₁ ≤ ((enc x).length + 1) ^ cM :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left c₁ 1)
    have hL_le : (enc x).length + 1 ≤ ((enc x).length + 1) ^ cM :=
      Nat.le_self_pow (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (le_max_right c₁ 1))) _
    have hpair_len : (encPair enc encBits (x, w)).length + 1 ≤
        (3 + F₁ (κ x)) * ((enc x).length + 1) ^ cM := by
      have hp : (encPair enc encBits (x, w)).length = 2 * (enc x).length + 1 + w.length := by
        enc_len
      have hw' : w.length ≤ F₁ (κ x) * ((enc x).length + 1) ^ cM :=
        hlen_w.trans (Nat.mul_le_mul_left _ hpow_c₁)
      have h2L : 2 * (enc x).length + 2 ≤ 3 * ((enc x).length + 1) ^ cM := by nlinarith
      nlinarith
    have hV_bound : F₂ (κ x) * ((encPair enc encBits (x, w)).length + 1) ^ c₂ ≤
        (F₂ (κ x) * (3 + F₁ (κ x)) ^ c₂) * ((enc x).length + 1) ^ (cM * c₂) := by
      calc F₂ (κ x) * ((encPair enc encBits (x, w)).length + 1) ^ c₂
          ≤ F₂ (κ x) * ((3 + F₁ (κ x)) * ((enc x).length + 1) ^ cM) ^ c₂ :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpair_len c₂)
        _ = (F₂ (κ x) * (3 + F₁ (κ x)) ^ c₂) * ((enc x).length + 1) ^ (cM * c₂) := by
            rw [Nat.mul_pow, Nat.pow_mul]; ring
    have hd1 : ((enc x).length + 1) ^ c₁ ≤ ((enc x).length + 1) ^ d :=
      hpow_c₁.trans (Nat.pow_le_pow_right (Nat.succ_pos _)
        (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
    have hd2 : ((enc x).length + 1) ^ (cM * c₂) ≤ ((enc x).length + 1) ^ d :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.mul_le_mul_left cM (Nat.le_succ c₂))
    have hdL : (enc x).length ≤ 1 * ((enc x).length + 1) ^ d := by
      rw [one_mul]
      exact (Nat.le_succ _).trans (hL_le.trans
        (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))))
    have hnat : (enc x).length + F₁ (κ x) * ((enc x).length + 1) ^ c₁ +
        F₂ (κ x) * ((encPair enc encBits (x, w)).length + 1) ^ c₂ ≤
        F (κ x) * ((enc x).length + 1) ^ d := by
      have hm1 := Nat.mul_le_mul_left (F₁ (κ x)) hd1
      have hm2 := hV_bound.trans (Nat.mul_le_mul_left _ hd2)
      exact (Nat.add_le_add (Nat.add_le_add hdL hm1) hm2).trans_eq (by dsimp [F]; ring)
    have hreal : (((enc x).length + F₁ (κ x) * ((enc x).length + 1) ^ c₁ +
        F₂ (κ x) * ((encPair enc encBits (x, w)).length + 1) ^ c₂ : ℕ) : ℝ) ≤
        ((F (κ x) * ((enc x).length + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hreal ⊢
    linarith
  · -- Yes-instance error (`0 < f x`): `acceptCount (!V) x m ≤ (1 / 3) * 2 ^ m`!
    set m := (ℓ ∘ prep) x
    have hgood := hprob x 2 2 (by norm_num)
    have h34 : (1 : ℝ) - (1 / 2 : ℝ) ^ 2 = 3 / 4 := by norm_num
    rw [h34] at hgood
    have hlaw_x : ProbComp.eval (A x 2 2) =
        (BitString.uniformList m).map (fun w => evalP (prep x, w)) := hlaw (prep x)
    have hacc : (3 / 4 : ℝ) ≤ (acceptCount V x m : ℝ) / (2 : ℝ) ^ m := by
      have hpr : Pr[(fun out => post out) <$> A x 2 2] = (acceptCount V x m : ℝ) / (2 : ℝ) ^ m := by
        have h1 := probability_sampleList_verifier V x m
        have heq_eval : ProbComp.eval ((fun w => V (x, w)) <$> BitString.sampleList m) =
            ProbComp.eval ((fun out => post out) <$> A x 2 2) := by
          rw [ProbComp.eval_map, BitString.eval_sampleList, ProbComp.eval_map, hlaw_x,
            _root_.PMF.map_comp]
          rfl
        rw [← h1]
        exact congrArg (fun μ => (μ true).toReal) heq_eval.symm
      have hev : post = fun out : ℕ × ℕ => decide (out ∈ {o : ℕ × ℕ | o.1 ≠ 0}) := by
        ext out; simp [post]
      rw [← hpr, hev, Cslib.ProbComp.probability_map_decide_mem]
      exact hgood.trans (Cslib.Probability.PMF.toOuterMeasure_toReal_mono _ fun out hout =>
        Nat.pos_iff_ne_zero.1 (pos_of_approxWithin_two hx hout))
    rw [le_div_iff₀ (by positivity)] at hacc
    have hsum : (acceptCount V x m : ℝ) + acceptCount (fun p => !V p) x m = (2 : ℝ) ^ m := by
      exact_mod_cast acceptCount_add_acceptCount_not V x m
    change (acceptCount (fun p => !V p) x m : ℝ) ≤ (1 / 3 : ℝ) * (2 : ℝ) ^ m
    linarith
  · -- No-instance error (`f x = 0`): `acceptCount V x m ≤ (1 / 3) * 2 ^ m`!
    set m := (ℓ ∘ prep) x
    have hfx0 : f x = 0 := Nat.eq_zero_of_not_pos hx
    have hgood := hprob x 2 2 (by norm_num)
    have h34 : (1 : ℝ) - (1 / 2 : ℝ) ^ 2 = 3 / 4 := by norm_num
    rw [h34, hfx0] at hgood
    have hlaw_x : ProbComp.eval (A x 2 2) =
        (BitString.uniformList m).map (fun w => evalP (prep x, w)) := hlaw (prep x)
    have hrej : (3 / 4 : ℝ) ≤ (acceptCount (fun p => !V p) x m : ℝ) / (2 : ℝ) ^ m := by
      have h1 := probability_sampleList_verifier (fun p => !V p) x m
      have heq_eval : ProbComp.eval ((fun w => !V (x, w)) <$> BitString.sampleList m) =
          ProbComp.eval ((fun out : ℕ × ℕ => decide (out ∈ {o : ℕ × ℕ | o.1 =
            0})) <$> A x 2 2) := by
        rw [ProbComp.eval_map, BitString.eval_sampleList, ProbComp.eval_map, hlaw_x,
          _root_.PMF.map_comp]
        congr 1
        ext w; simp [V, post, prepSeed]
      rw [← h1]
      have hpr_eq : Pr[(fun w => !V (x, w)) <$> BitString.sampleList m] =
          Pr[(fun out : ℕ × ℕ => decide (out ∈ {o : ℕ × ℕ | o.1 = 0})) <$> A x 2 2] :=
        congrArg (fun μ => (μ true).toReal) heq_eval
      rw [hpr_eq, Cslib.ProbComp.probability_map_decide_mem]
      exact hgood.trans (Cslib.Probability.PMF.toOuterMeasure_toReal_mono _ fun out hout =>
        hout.num_eq_zero)
    rw [le_div_iff₀ (by positivity)] at hrej
    have hsum : (acceptCount V x m : ℝ) + acceptCount (fun p => !V p) x m = (2 : ℝ) ^ m := by
      exact_mod_cast acceptCount_add_acceptCount_not V x m
    change (acceptCount V x m : ℝ) ≤ (1 / 3 : ℝ) * (2 : ℝ) ^ m
    linarith

end FPTRASDefs

end Cslib.Complexity
