/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Discrepancy
public import CslibFrontier.Computability.Communication.Distributional
public import CslibFrontier.Computability.Communication.Operations
import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pseudodeterministic communication complexity and plurality amplification

A public-coin communication protocol solves a two-party search relation `R : X → Y → Z → Prop`
*pseudodeterministically* with error `ε` when on every input pair `(x, y)` there exists a canonical
valid output `z` (`R x y z`) produced with failure probability at most `ε`
(`SolvesPseudodeterministically`). Equivalently, the protocol computes some total completion
`f : X → Y → Z` of `R` with worst-case error at most `ε`
(`solvesPseudodeterministically_iff_exists_completion`), so the least pseudodeterministic depth
`pseudodeterministicComplexity ε R` equals the infimum of `PublicCoin.ecomplexityFun ε f` over all
total completions `f` of `R` (`pseudodeterministicComplexity_eq_iInf_completion`).

Unlike general randomized search protocols, pseudodeterministic protocols support generic error
amplification over arbitrary output types: running `2 * r` independent copies (`PMF.iid`) via
`Protocol.runAll` and selecting the strict plurality output (`pluralityChoice`) reduces any error
`ε ≤ 1 / 2` to `(4 * ε * (1 - ε)) ^ r` while multiplying communication depth by at most `2 * r`
(`SolvesPseudodeterministically.amplify`, `pseudodeterministicComplexity_amplify_le`).

Combining plurality amplification with the discrepancy bound for the inner product modulo two yields
an unconditional separation between randomized and pseudodeterministic communication complexity for
explicit two-bit search relations: avoiding the pair of inner products on the two halves of `n`-bit
inputs (`twoBitAvoidDotProduct`) requires zero bits of public-coin communication at error `1 / 4`
(hence at error `1 / 3`), linear `Ω(n)` communication at error `1 / 10`, and therefore linear
`Ω(n)` pseudodeterministic communication at error `1 / 3`
(`twoBitAvoidDotProduct_pseudodeterministic_lower`).

## Main definitions

* `CslibFrontier.Computability.Communication.SolvesPseudodeterministically`: canonical-output
  correctness for public-coin search protocols.
* `CslibFrontier.Computability.Communication.pseudodeterministicComplexity`: least depth in `ℕ∞` of
  an `ε`-error pseudodeterministic public-coin protocol.
* `CslibFrontier.Computability.Communication.pluralityChoice`: strict plurality selector on `k`
  outputs.
* `CslibFrontier.Computability.Communication.twoBitAvoidDotProduct`: explicit `2`-bit search
  relation avoiding the inner products of the first and second halves of `n`-bit strings.

## Main results

* `CslibFrontier.Computability.Communication.solvesPseudodeterministically_iff_exists_completion`:
  equivalence between pseudodeterministic search and computing a total completion.
* `CslibFrontier.Computability.Communication.pseudodeterministicComplexity_eq_iInf_completion`:
  completion characterization of pseudodeterministic communication complexity.
* `CslibFrontier.Computability.Communication.pseudodeterministicComplexity_amplify_le`: `2 * r`-run
  plurality error amplification for pseudodeterministic protocols.
* `CslibFrontier.Computability.Communication.twoBitAvoidDotProduct_ecomplexity_quarter`,
  `CslibFrontier.Computability.Communication.twoBitAvoidDotProduct_ecomplexity_tenth_lower`,
  `CslibFrontier.Computability.Communication.twoBitAvoidDotProduct_pseudodeterministic_lower`:
  zero-communication `1 / 4`-error randomized upper bound vs. `Ω(n)` `1 / 10`-error randomized and
  `1 / 3`-error pseudodeterministic lower bounds.
-/

public section

namespace CslibFrontier.Computability.Communication

open Cslib Cslib.BitString Cslib.Communication Cslib.Probability Finset

/-! ### Pseudodeterministic protocols and completion characterization -/

section Pseudodeterminism

variable {X Y Z : Type*}

/-- A public-coin protocol `μ` solves `R : X → Y → Z → Prop` pseudodeterministically with error at
most `ε` when on every input pair `(x, y)` there exists a canonical valid answer `z` (`R x y z`)
from which `μ` deviates with probability at most `ε`. -/
@[expose] def SolvesPseudodeterministically (μ : PublicCoin X Y Z) (ε : ℝ) (R : X → Y → Z → Prop) :
    Prop :=
  ∀ x y, ∃ z, R x y z ∧ μ.errorProb (fun _ _ w => z = w) x y ≤ ε

/-- Solving `R` pseudodeterministically with error `ε` is equivalent to computing some total
completion `f : X → Y → Z` of `R` with error `ε`. -/
theorem solvesPseudodeterministically_iff_exists_completion {μ : PublicCoin X Y Z} {ε : ℝ}
    {R : X → Y → Z → Prop} :
    SolvesPseudodeterministically μ ε R ↔
      ∃ f : X → Y → Z, (∀ x y, R x y (f x y)) ∧
        μ.Solves ε (fun x y w => f x y = w) Set.univ Set.univ := by
  constructor
  · intro h
    choose f hfR hferr using fun q : X × Y => h q.1 q.2
    exact ⟨fun x y => f (x, y), fun x y => hfR (x, y), fun x _ y _ => hferr (x, y)⟩
  · rintro ⟨f, hfR, hfS⟩ x y
    exact ⟨f x y, hfR x y, hfS x trivial y trivial⟩

/-- Every pseudodeterministic protocol for `R` with error `ε` solves `R` with error `ε`. -/
theorem SolvesPseudodeterministically.solves {μ : PublicCoin X Y Z} {ε : ℝ}
    {R : X → Y → Z → Prop} (h : SolvesPseudodeterministically μ ε R) :
    μ.Solves ε R Set.univ Set.univ := by
  intro x _ y _
  obtain ⟨z, hzR, hzerr⟩ := h x y
  refine le_trans ?_ hzerr
  unfold PublicCoin.errorProb Cslib.Probability.PMF.errorProb
  refine Cslib.Probability.PMF.toOuterMeasure_toReal_mono μ fun p hp => ?_
  intro heq
  dsimp only at hp heq
  exact hp (heq ▸ hzR)

/-- When `ε < 1 / 2`, solving `R` with error `ε` while concentrating within error `ε` on a single
output per input pair forces that output to satisfy `R`. -/
theorem solvesPseudodeterministically_iff_solves_and_consistent {μ : PublicCoin X Y Z} {ε : ℝ}
    (hε : ε < 1 / 2) {R : X → Y → Z → Prop} :
    SolvesPseudodeterministically μ ε R ↔
      μ.Solves ε R Set.univ Set.univ ∧
        ∀ x y, ∃ z, μ.errorProb (fun _ _ w => z = w) x y ≤ ε := by
  refine ⟨fun h => ⟨h.solves, fun x y => let ⟨z, _, hz⟩ := h x y; ⟨z, hz⟩⟩, ?_⟩
  rintro ⟨hR, hcons⟩ x y
  obtain ⟨z, hz⟩ := hcons x y
  refine ⟨z, ?_, hz⟩
  by_contra hnotR
  have h1 : 1 ≤ μ.errorProb R x y + μ.errorProb (fun _ _ w => z = w) x y := by
    unfold PublicCoin.errorProb Cslib.Probability.PMF.errorProb
    let E : Set (Protocol X Y Z) := {p | ¬ z = p.run x y}
    have hadd := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl μ E
    have hsub : (μ.toOuterMeasure Eᶜ).toReal ≤
        (μ.toOuterMeasure {p | ¬ R x y (p.run x y)}).toReal := by
      refine Cslib.Probability.PMF.toOuterMeasure_toReal_mono μ fun p hp => ?_
      have hpz : z = p.run x y := not_not.mp hp
      exact show ¬ R x y (p.run x y) by rwa [← hpz]
    dsimp only [E] at hadd
    linarith
  have h2 := hR x trivial y trivial
  linarith

/-- Least depth in `ℕ∞` of a public-coin protocol solving `R` pseudodeterministically with error at
most `ε`, or `⊤` if none exists. -/
@[expose] noncomputable def pseudodeterministicComplexity (ε : ℝ) (R : X → Y → Z → Prop) : ℕ∞ :=
  ⨅ μ : {μ : PublicCoin X Y Z // SolvesPseudodeterministically μ ε R}, μ.1.depth

/-- Pseudodeterministic communication complexity equals the infimum of randomized function
complexities over all total completions of `R`. -/
theorem pseudodeterministicComplexity_eq_iInf_completion (ε : ℝ) (R : X → Y → Z → Prop) :
    pseudodeterministicComplexity ε R =
      ⨅ f : {f : X → Y → Z // ∀ x y, R x y (f x y)}, PublicCoin.ecomplexityFun ε f.1 := by
  apply le_antisymm
  · refine le_iInf fun ⟨f, hf⟩ => le_iInf fun μ => ?_
    have hps : SolvesPseudodeterministically μ.1 ε R :=
      solvesPseudodeterministically_iff_exists_completion.mpr ⟨f, hf, μ.2⟩
    exact iInf_le (fun ν : {ν : PublicCoin X Y Z // SolvesPseudodeterministically ν ε R} =>
      ν.1.depth) ⟨μ.1, hps⟩
  · refine le_iInf fun ⟨μ, hμ⟩ => ?_
    obtain ⟨f, hfR, hfS⟩ := solvesPseudodeterministically_iff_exists_completion.mp hμ
    exact (iInf_le (fun g : {g : X → Y → Z // ∀ x y, R x y (g x y)} =>
      PublicCoin.ecomplexityFun ε g.1) ⟨f, hfR⟩).trans (PublicCoin.ecomplexity_le_depth hfS)

/-- Public-coin randomized communication complexity never exceeds pseudodeterministic communication
complexity at the same error parameter. -/
theorem ecomplexity_le_pseudodeterministicComplexity (ε : ℝ) (R : X → Y → Z → Prop) :
    PublicCoin.ecomplexity ε R Set.univ Set.univ ≤ pseudodeterministicComplexity ε R :=
  le_iInf fun μ => PublicCoin.ecomplexity_le_depth μ.2.solves

/-- Allowing larger error cannot increase pseudodeterministic communication complexity. -/
theorem pseudodeterministicComplexity_anti {ε ε' : ℝ} (hε : ε ≤ ε') (R : X → Y → Z → Prop) :
    pseudodeterministicComplexity ε' R ≤ pseudodeterministicComplexity ε R := by
  rw [pseudodeterministicComplexity_eq_iInf_completion,
    pseudodeterministicComplexity_eq_iInf_completion]
  exact iInf_mono fun f => PublicCoin.ecomplexity_anti hε

end Pseudodeterminism

/-! ### Plurality error amplification -/

/-- Strict plurality selector on `Fin k → Z` with fallback `z₀`: returns the unique value occurring
strictly more than `k / 2` times if one exists, and `z₀` otherwise. -/
noncomputable def pluralityChoice {Z : Type*} (z₀ : Z) {k : ℕ} (v : Fin k → Z) : Z := by
  classical
  exact if h : ∃ z : Z, k < 2 * (Finset.univ.filter fun i => v i = z).card then
    Classical.choose h
  else
    z₀

private theorem card_ne_ge_of_pluralityChoice_ne {Z : Type*} [DecidableEq Z] (z₀ zstar : Z)
    {r : ℕ} {v : Fin (2 * r) → Z}
    (hne : pluralityChoice z₀ v ≠ zstar) :
    r ≤ (Finset.univ.filter fun i => decide (v i ≠ zstar) = true).card := by
  by_contra hlt
  have hlt' : (Finset.univ.filter fun i => ¬ v i = zstar).card < r := by
    simpa only [decide_eq_true_eq] using not_le.mp hlt
  have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * r))))
    (fun i => v i = zstar)
  rw [Finset.card_univ, Fintype.card_fin] at hpart
  have hgt_star : 2 * r < 2 * (Finset.univ.filter fun i => v i = zstar).card := by omega
  have hplur : pluralityChoice z₀ v = zstar := by
    unfold pluralityChoice
    have hex' : ∃ z : Z, 2 * r < 2 * (@Finset.filter (Fin (2 * r)) (fun i => v i = z)
        (fun _ => Classical.propDecidable _) Finset.univ).card := by
      refine ⟨zstar, ?_⟩
      convert hgt_star using 2
      congr 1; ext i; simp
    rw [dite_eq_left_of_eq_true (eq_true hex')]
    have hspec := Classical.choose_spec hex'
    set z' := Classical.choose hex'
    by_contra hzz'
    have hcard_z' : 2 * r < 2 * (Finset.univ.filter fun i => v i = z').card := by
      convert hspec using 2
      congr 1; ext i; simp
    have hdisj : Disjoint (Finset.univ.filter fun i => v i = z')
        (Finset.univ.filter fun i => v i = zstar) :=
      Finset.disjoint_left.mpr fun i h1 h2 =>
        hzz' ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hun_le : ((Finset.univ.filter fun i => v i = z') ∪
        (Finset.univ.filter fun i => v i = zstar)).card ≤ 2 * r :=
      (Finset.card_le_univ _).trans_eq (Fintype.card_fin (2 * r))
    rw [Finset.card_union_of_disjoint hdisj] at hun_le
    omega
  exact hne hplur

/-- Sequencing `2 * r` independent draws from a pseudodeterministic protocol `μ` (`ε ≤ 1 / 2`) with
`pluralityChoice` reduces the error to `(4 * ε * (1 - ε)) ^ r` at `2 * r` times the communication
depth. -/
theorem SolvesPseudodeterministically.amplify {X Y Z : Type*} (z₀ : Z)
    {μ : PublicCoin X Y Z} {ε : ℝ} {R : X → Y → Z → Prop}
    (hμ : SolvesPseudodeterministically μ ε R) (hε : ε ≤ 1 / 2) (r : ℕ) :
    let μ' : PublicCoin X Y Z :=
      (Cslib.Probability.PMF.iid μ (2 * r)).map fun ps => Protocol.runAll ps (pluralityChoice z₀)
    SolvesPseudodeterministically μ' ((4 * ε * (1 - ε)) ^ r) R ∧
      ∀ c : ℕ, μ.depth ≤ c → μ'.depth ≤ (2 * r * c : ℕ) := by
  classical
  intro μ'
  refine ⟨fun x y => ?_, fun c hc => ?_⟩
  · obtain ⟨zstar, hzR, hzerr⟩ := hμ x y
    refine ⟨zstar, hzR, ?_⟩
    let e : Protocol X Y Z → Bool := fun p => decide (p.run x y ≠ zstar)
    have he : ((μ.map e) true).toReal ≤ ε := by
      have hpre : e ⁻¹' {true} = {p | ¬ zstar = p.run x y} := by
        ext p; simp [e, ne_comm]
      rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply, hpre]
      exact hzerr
    refine le_trans ?_ (Cslib.Probability.PMF.iid_card_ge_le he hε r)
    unfold PublicCoin.errorProb Cslib.Probability.PMF.errorProb
    rw [PMF.toOuterMeasure_map_apply, Cslib.Probability.PMF.iid_map, PMF.toOuterMeasure_map_apply]
    refine Cslib.Probability.PMF.toOuterMeasure_toReal_mono _ fun ps hps => ?_
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Protocol.run_runAll] at hps ⊢
    exact card_ne_ge_of_pluralityChoice_ne z₀ zstar (Ne.symm hps)
  · refine PublicCoin.depth_le_iff.mpr fun p hp => ?_
    obtain ⟨ps, hps, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
    exact_mod_cast Protocol.depth_runAll_le fun i => by
      have hi := (Cslib.Probability.PMF.mem_support_iid_iff μ ps).mp hps i
      exact_mod_cast (PublicCoin.depth_le_depth hi).trans hc

/-- Plurality error reduction for `pseudodeterministicComplexity`: for `ε ≤ 1 / 2` and `r ≥ 1`,
reducing error to `(4 * ε * (1 - ε)) ^ r` multiplies pseudodeterministic complexity by at most
`2 * r`. -/
theorem pseudodeterministicComplexity_amplify_le {X Y Z : Type*} [Nonempty Z]
    {ε : ℝ} (hε : ε ≤ 1 / 2) {r : ℕ} (hr : 1 ≤ r) (R : X → Y → Z → Prop) :
    pseudodeterministicComplexity ((4 * ε * (1 - ε)) ^ r) R ≤
      2 * r * pseudodeterministicComplexity ε R := by
  obtain ⟨z₀⟩ := ‹Nonempty Z›
  cases h : pseudodeterministicComplexity ε R using ENat.recTopCoe with
  | top =>
    rw [ENat.mul_top (by exact_mod_cast (show 2 * r ≠ 0 by omega))]
    exact le_top
  | coe c =>
    have hex : ∃ μ : PublicCoin X Y Z, SolvesPseudodeterministically μ ε R ∧ μ.depth ≤ c := by
      by_contra hno
      push Not at hno
      have hge : ((c + 1 : ℕ) : ℕ∞) ≤ pseudodeterministicComplexity ε R := by
        refine le_iInf fun ⟨μ, hμ⟩ => ?_
        have hlt : (c : ℕ∞) < μ.depth := hno μ hμ
        cases hd : μ.depth using ENat.recTopCoe with
        | top => simp
        | coe d =>
          rw [hd] at hlt
          have hcd : c < d := by exact_mod_cast hlt
          exact_mod_cast (show c + 1 ≤ d by omega)
      rw [h] at hge
      exact absurd (show c + 1 ≤ c by exact_mod_cast hge) (by omega)
    obtain ⟨μ, hμ, hc⟩ := hex
    obtain ⟨hamp, hd⟩ := hμ.amplify z₀ hε r
    have hle : pseudodeterministicComplexity ((4 * ε * (1 - ε)) ^ r) R ≤ _ :=
      iInf_le (fun ν : {ν : PublicCoin X Y Z //
        SolvesPseudodeterministically ν ((4 * ε * (1 - ε)) ^ r) R} => ν.1.depth) ⟨_, hamp⟩
    refine hle.trans ((hd c hc).trans_eq ?_)
    push_cast; rfl

/-- Specialization of `pseudodeterministicComplexity_amplify_le` from error `1 / 3` to
`(8 / 9) ^ r` (`r ≥ 1`). -/
theorem pseudodeterministicComplexity_amplify_one_third {X Y Z : Type*} [Nonempty Z]
    {r : ℕ} (hr : 1 ≤ r) (R : X → Y → Z → Prop) :
    pseudodeterministicComplexity ((8 / 9 : ℝ) ^ r) R ≤
      2 * r * pseudodeterministicComplexity (1 / 3) R := by
  have h := pseudodeterministicComplexity_amplify_le (ε := 1 / 3) (by norm_num) hr R
  rwa [show (4 * (1 / 3) * (1 - 1 / 3) : ℝ) = 8 / 9 by norm_num] at h

/-! ### Explicit `O(1)` vs. `Ω(n)` separation for two-bit search relations -/

/-- Distributional lower bound for the inner product modulo two at error `2 / 5` under the uniform
distribution: `m ≤ 2 * D^{unif}_{2/5}(IP_m) + 4`. -/
theorem le_two_mul_distributionalComplexity_dotProduct_two_fifths_add_four (m : ℕ) :
    (m : ℕ∞) ≤ 2 * Protocol.distributionalComplexity (2 / 5)
      (fun x y : BitString m => fun b => (x ⬝ᵥ y) = b)
      (PMF.uniformOfFintype (BitString m × BitString m)) + 4 := by
  set μ := PMF.uniformOfFintype (BitString m × BitString m)
  cases hd : Protocol.distributionalComplexity (2 / 5)
      (fun x y : BitString m => fun b => (x ⬝ᵥ y) = b) μ using ENat.recTopCoe with
  | top => simp
  | coe d =>
    obtain ⟨p, herr, hp_depth⟩ := Protocol.distributionalComplexity_le_iff.mp hd.le
    have herr' : p.distributionalError μ (fun x y b => (x ⬝ᵥ y) = b) ≤ 1 / 2 - 1 / 10 :=
      herr.trans (by norm_num)
    have hdisc := p.two_mul_le_two_pow_mul_discrepancy herr'
    have hsq := pow_le_pow_left₀ (by norm_num) hdisc 2
    have h4 : ((2 : ℝ) ^ p.depth) ^ 2 = 4 ^ p.depth := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hbound : (2 * (1 / 10 : ℝ)) ^ 2 * (2 : ℝ) ^ m ≤ (4 : ℝ) ^ d := by
      calc (2 * (1 / 10 : ℝ)) ^ 2 * (2 : ℝ) ^ m
          ≤ (2 ^ p.depth * discrepancy μ (fun x y => x ⬝ᵥ y)) ^ 2 * (2 : ℝ) ^ m :=
            mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = (4 : ℝ) ^ p.depth * (discrepancy μ (fun x y => x ⬝ᵥ y) ^ 2 * (2 : ℝ) ^ m) := by
            rw [mul_pow, h4, mul_assoc]
        _ ≤ (4 : ℝ) ^ p.depth :=
            mul_le_of_le_one_right (by positivity) (discrepancy_dotProduct_sq_mul_two_pow_le m)
        _ ≤ (4 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hp_depth
    have hnat : 2 ^ m ≤ 25 * 4 ^ d := by
      exact_mod_cast (show (2 : ℝ) ^ m ≤ 25 * (4 : ℝ) ^ d by nlinarith)
    have hlt : 2 ^ m < 2 ^ (2 * d + 5) := by
      calc 2 ^ m ≤ 25 * 4 ^ d := hnat
        _ < 32 * 4 ^ d := by
            have hpos4 : 0 < 4 ^ d := pow_pos (by decide : 0 < 4) d
            omega
        _ = 2 ^ (2 * d + 5) := by rw [pow_add, pow_mul, mul_comm]; norm_num
    have hm_lt := (Nat.pow_lt_pow_iff_right one_lt_two).mp hlt
    exact_mod_cast (show m ≤ 2 * d + 4 by omega)

/-- First `n / 2`-bit block of an `n`-bit string. -/
@[expose] def firstHalf (n : ℕ) (x : BitString n) : BitString (n / 2) :=
  fun i => x ⟨i.1, by omega⟩

/-- Second `n / 2`-bit block of an `n`-bit string. -/
@[expose] def secondHalf (n : ℕ) (x : BitString n) : BitString (n / 2) :=
  fun i => x ⟨n / 2 + i.1, by omega⟩

/-- Explicit two-bit search relation on `n`-bit inputs accepting every pair `(u, v) ∈ Bool × Bool`
except the two inner products `(firstHalf n x ⬝ᵥ firstHalf n y, secondHalf n x ⬝ᵥ secondHalf n y)`.
-/
@[expose] def twoBitAvoidDotProduct (n : ℕ) (x y : BitString n) (uv : Bool × Bool) : Prop :=
  uv ≠ (firstHalf n x ⬝ᵥ firstHalf n y, secondHalf n x ⬝ᵥ secondHalf n y)

private def concatHalves (n : ℕ) (x : BitString (n / 2) × BitString (n / 2)) : BitString n :=
  fun k =>
    if h1 : k.1 < n / 2 then x.1 ⟨k.1, h1⟩
    else if h2 : k.1 < 2 * (n / 2) then x.2 ⟨k.1 - n / 2, by omega⟩
    else false

private theorem firstHalf_concatHalves (n : ℕ) (x : BitString (n / 2) × BitString (n / 2)) :
    firstHalf n (concatHalves n x) = x.1 := by
  funext i
  simp [firstHalf, concatHalves, i.2]

private theorem secondHalf_concatHalves (n : ℕ) (x : BitString (n / 2) × BitString (n / 2)) :
    secondHalf n (concatHalves n x) = x.2 := by
  funext i
  have h1 : ¬ n / 2 + i.1 < n / 2 := by omega
  have h2 : n / 2 + i.1 < 2 * (n / 2) := by omega
  simp only [secondHalf, concatHalves, h1, h2, ↓reduceDIte]
  exact congrArg x.2 (Fin.ext (Nat.add_sub_cancel_left (n / 2) i.1))

/-- Outputting a uniformly random pair of bits solves `twoBitAvoidDotProduct n` with error `1 / 4`
and zero communication. -/
theorem twoBitAvoidDotProduct_ecomplexity_quarter (n : ℕ) :
    PublicCoin.ecomplexity (1 / 4) (twoBitAvoidDotProduct n) Set.univ Set.univ = 0 := by
  classical
  refine nonpos_iff_eq_zero.mp ?_
  let μ : PublicCoin (BitString n) (BitString n) (Bool × Bool) :=
    (PMF.uniformOfFintype (Bool × Bool)).map Protocol.output
  have hd : μ.depth ≤ (0 : ℕ) :=
    Cslib.Probability.PMF.maxCost_map_le_of_le Protocol.depth _ _ fun _ _ => by simp
  have hsol : μ.Solves (1 / 4) (twoBitAvoidDotProduct n) Set.univ Set.univ := by
    intro x _ y _
    unfold PublicCoin.errorProb Cslib.Probability.PMF.errorProb μ
    rw [PMF.toOuterMeasure_map_apply, Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal,
      Fintype.card_prod, Fintype.card_bool]
    let bad := (firstHalf n x ⬝ᵥ firstHalf n y, secondHalf n x ⬝ᵥ secondHalf n y)
    have hfilt : (Finset.univ : Finset (Bool × Bool)).filter
        (fun uv => uv ∈ Protocol.output ⁻¹' {p | ¬ twoBitAvoidDotProduct n x y (p.run x y)}) =
        {bad} := by
      ext uv
      simp [twoBitAvoidDotProduct, bad]
    rw [hfilt, Finset.card_singleton]
    norm_num
  exact (PublicCoin.ecomplexity_le_depth hsol).trans hd

private theorem bool_not_eq_of_ne {a b : Bool} (h : a ≠ b) : (!a) = b := by
  cases a <;> cases b <;> simp_all

private theorem bool_ne_of_not_eq {a b : Bool} (h : (!a) = b) : a ≠ b := by
  cases a <;> cases b <;> simp_all

private theorem bool_not_xor_eq_of_ne_eq {a b x y : Bool}
    (h : (a ≠ x ∧ b = y) ∨ (a = x ∧ b ≠ y)) : (!(xor (xor a b) y)) = x := by
  cases a <;> cases b <;> cases x <;> cases y <;> simp_all

/-- Solving `twoBitAvoidDotProduct n` at error `1 / 10` requires `Ω(n)` public-coin communication:
`n / 2 ≤ 2 * ecomplexity (1 / 10) (twoBitAvoidDotProduct n) + 4`. -/
theorem twoBitAvoidDotProduct_ecomplexity_tenth_lower (n : ℕ) :
    ((n / 2 : ℕ) : ℕ∞) ≤
      2 * PublicCoin.ecomplexity (1 / 10) (twoBitAvoidDotProduct n) Set.univ Set.univ + 4 := by
  classical
  set m := n / 2
  cases hd : PublicCoin.ecomplexity (1 / 10) (twoBitAvoidDotProduct n) Set.univ Set.univ
      using ENat.recTopCoe with
  | top => simp
  | coe d =>
    obtain ⟨μ₀, hμ₀, hd₀⟩ := PublicCoin.ecomplexity_le_iff.mp hd.le
    let R_even : (BitString m × BitString m) → (BitString m × BitString m) →
        Bool × Bool → Prop :=
      fun x y uv => uv ≠ (x.1 ⬝ᵥ y.1, x.2 ⬝ᵥ y.2)
    let μ₁ : PublicCoin (BitString m × BitString m) (BitString m × BitString m) (Bool × Bool) :=
      μ₀.map (Protocol.comap (concatHalves n) (concatHalves n))
    have hd₁ : μ₁.depth ≤ (d : ℕ) :=
      Cslib.Probability.PMF.maxCost_map_le_of_le Protocol.depth _ μ₀ fun p hp =>
        (Protocol.depth_comap _ _ p).le.trans
          (by exact_mod_cast (PublicCoin.depth_le_depth hp).trans hd₀)
    have hsol₁ : μ₁.Solves (1 / 10) R_even Set.univ Set.univ := by
      intro x _ y _
      refine le_trans (le_of_eq ?_)
        (hμ₀ (concatHalves n x) trivial (concatHalves n y) trivial)
      unfold PublicCoin.errorProb Cslib.Probability.PMF.errorProb μ₁
      rw [PMF.toOuterMeasure_map_apply]
      congr 2; ext p
      simp [R_even, twoBitAvoidDotProduct, firstHalf_concatHalves, secondHalf_concatHalves]
    let Quad := (BitString m × BitString m) × (BitString m × BitString m)
    let νQ := PMF.uniformOfFintype Quad
    have hdistQ : Protocol.distributionalComplexity (1 / 10) R_even νQ ≤ d :=
      (PublicCoin.distributionalComplexity_le_ecomplexity fun _ _ => ⟨trivial, trivial⟩).trans
        ((PublicCoin.ecomplexity_le_depth hsol₁).trans hd₁)
    obtain ⟨proto, hproto_err, hproto_depth⟩ := Protocol.distributionalComplexity_le_iff.mp hdistQ
    set M := Fintype.card (BitString m × BitString m)
    have hM_pos : (0 : ℝ) < M := by exact_mod_cast Fintype.card_pos
    have hQuad_card : (Fintype.card Quad : ℝ) = (M : ℝ) * M := by
      have : Fintype.card Quad = M * M := Fintype.card_prod _ _
      exact_mod_cast this
    let S00 := (Finset.univ : Finset Quad).filter fun q =>
      (proto.run q.1 q.2).1 ≠ (q.1.1 ⬝ᵥ q.2.1) ∧ (proto.run q.1 q.2).2 ≠ (q.1.2 ⬝ᵥ q.2.2)
    let S01 := (Finset.univ : Finset Quad).filter fun q =>
      (proto.run q.1 q.2).1 ≠ (q.1.1 ⬝ᵥ q.2.1) ∧ (proto.run q.1 q.2).2 = (q.1.2 ⬝ᵥ q.2.2)
    let S10 := (Finset.univ : Finset Quad).filter fun q =>
      (proto.run q.1 q.2).1 = (q.1.1 ⬝ᵥ q.2.1) ∧ (proto.run q.1 q.2).2 ≠ (q.1.2 ⬝ᵥ q.2.2)
    let S11 := (Finset.univ : Finset Quad).filter fun q =>
      (proto.run q.1 q.2).1 = (q.1.1 ⬝ᵥ q.2.1) ∧ (proto.run q.1 q.2).2 = (q.1.2 ⬝ᵥ q.2.2)
    have hS11_le : (S11.card : ℝ) ≤ (1 / 10 : ℝ) * ((M : ℝ) * M) := by
      unfold Protocol.distributionalError Cslib.Probability.PMF.errorProb at hproto_err
      rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal, hQuad_card] at hproto_err
      have heq11 : (Finset.univ : Finset Quad).filter
          (fun q => q ∈ {q : Quad | ¬ R_even q.1 q.2 (proto.run q.1 q.2)}) = S11 := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, R_even,
          not_not, Prod.ext_iff, S11]
      rw [heq11] at hproto_err
      exact (div_le_iff₀ (by positivity)).mp hproto_err
    have hsum4 : (S00.card : ℝ) + S01.card + S10.card + S11.card = (M : ℝ) * M := by
      have hpart : S00.card + S01.card + S10.card + S11.card = Fintype.card Quad := by
        have h1 : S00 ∪ S01 ∪ S10 ∪ S11 = Finset.univ := by
          ext q
          simp only [S00, S01, S10, S11, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
            true_and, iff_true]
          by_cases a : (proto.run q.1 q.2).1 = (q.1.1 ⬝ᵥ q.2.1) <;>
            by_cases b : (proto.run q.1 q.2).2 = (q.1.2 ⬝ᵥ q.2.2) <;> tauto
        have d1 : Disjoint S00 S01 := Finset.disjoint_left.mpr fun q h0 h1 =>
          (Finset.mem_filter.mp h0).2.2 (Finset.mem_filter.mp h1).2.2
        have d2 : Disjoint (S00 ∪ S01) S10 := Finset.disjoint_left.mpr fun q h0 h1 => by
          rcases Finset.mem_union.mp h0 with h | h <;>
            exact (Finset.mem_filter.mp h).2.1 (Finset.mem_filter.mp h1).2.1
        have d3 : Disjoint (S00 ∪ S01 ∪ S10) S11 := Finset.disjoint_left.mpr fun q h0 h1 => by
          rcases Finset.mem_union.mp h0 with h01 | h
          · rcases Finset.mem_union.mp h01 with h | h <;>
              exact (Finset.mem_filter.mp h).2.1 (Finset.mem_filter.mp h1).2.1
          · exact (Finset.mem_filter.mp h).2.2 (Finset.mem_filter.mp h1).2.2
        calc S00.card + S01.card + S10.card + S11.card
            = (S00 ∪ S01 ∪ S10 ∪ S11).card := by
              rw [Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d2,
                Finset.card_union_of_disjoint d1]
          _ = Fintype.card Quad := by rw [h1, Finset.card_univ]
      exact (by exact_mod_cast hpart :
        (S00.card : ℝ) + S01.card + S10.card + S11.card = Fintype.card Quad).trans hQuad_card
    suffices ∃ proto' : Protocol (BitString m) (BitString m) Bool,
        proto'.distributionalError (PMF.uniformOfFintype (BitString m × BitString m))
          (fun x y b => (x ⬝ᵥ y) = b) ≤ 2 / 5 ∧ proto'.depth ≤ d by
      obtain ⟨proto', herr', hd'⟩ := this
      have hcg := le_two_mul_distributionalComplexity_dotProduct_two_fifths_add_four m
      have hle_d : Protocol.distributionalComplexity (2 / 5)
          (fun x y : BitString m => fun b => (x ⬝ᵥ y) = b)
          (PMF.uniformOfFintype (BitString m × BitString m)) ≤ d :=
        (Protocol.distributionalComplexity_le_depth herr').trans (by exact_mod_cast hd')
      exact hcg.trans (by gcongr)
    have hcases : (3 / 5 : ℝ) * ((M : ℝ) * M) ≤ (S00.card : ℝ) + S01.card ∨
        (3 / 5 : ℝ) * ((M : ℝ) * M) ≤ (S00.card : ℝ) + S10.card ∨
        (3 / 5 : ℝ) * ((M : ℝ) * M) ≤ (S01.card : ℝ) + S10.card := by
      by_contra hnone
      push Not at hnone
      obtain ⟨h1, h2, h3⟩ := hnone
      linarith
    let swapQ : Quad ≃ (BitString m × BitString m) × (BitString m × BitString m) :=
      { toFun := fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))
        invFun := fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have havg_snd
        (Q : Protocol (BitString m × BitString m) (BitString m × BitString m) (Bool × Bool))
        (hQ_depth : Q.depth ≤ d)
        (outFn : BitString m × BitString m → Bool × Bool → Bool)
        (hgood : (3 / 5 : ℝ) * ((M : ℝ) * M) ≤
          ((Finset.univ.filter fun q : Quad =>
            outFn (q.1.2, q.2.2) (Q.run q.1 q.2) = (q.1.1 ⬝ᵥ q.2.1)).card : ℝ)) :
        ∃ proto' : Protocol (BitString m) (BitString m) Bool,
          proto'.distributionalError (PMF.uniformOfFintype (BitString m × BitString m))
            (fun x y b => (x ⬝ᵥ y) = b) ≤ 2 / 5 ∧ proto'.depth ≤ d := by
      have hsum_eq : ((Finset.univ.filter fun q : Quad =>
          outFn (q.1.2, q.2.2) (Q.run q.1 q.2) = (q.1.1 ⬝ᵥ q.2.1)).card : ℝ) =
          ∑ xy₂ : BitString m × BitString m,
            ((Finset.univ.filter fun xy₁ : BitString m × BitString m =>
              outFn xy₂ (Q.run (xy₁.1, xy₂.1) (xy₁.2, xy₂.2)) = (xy₁.1 ⬝ᵥ xy₁.2)).card : ℝ) := by
        have hcard : (Finset.univ.filter fun q : Quad =>
            outFn (q.1.2, q.2.2) (Q.run q.1 q.2) = (q.1.1 ⬝ᵥ q.2.1)).card =
            ∑ xy₂ : BitString m × BitString m,
              (Finset.univ.filter fun xy₁ : BitString m × BitString m =>
                outFn xy₂ (Q.run (xy₁.1, xy₂.1) (xy₁.2, xy₂.2)) = (xy₁.1 ⬝ᵥ xy₁.2)).card := by
          have heq_map : (Finset.univ.filter fun q : Quad =>
              outFn (q.1.2, q.2.2) (Q.run q.1 q.2) = (q.1.1 ⬝ᵥ q.2.1)).card =
              (Finset.univ.filter fun p : (BitString m × BitString m) ×
                (BitString m × BitString m) =>
                outFn p.2 (Q.run (p.1.1, p.2.1) (p.1.2, p.2.2)) = (p.1.1 ⬝ᵥ p.1.2)).card :=
            Finset.card_nbij' swapQ swapQ.symm
              (fun q hq => by simpa [swapQ] using hq)
              (fun p hp => by simpa [swapQ] using hp)
              (fun _ _ => rfl) (fun _ _ => rfl)
          rw [heq_map]
          have hbi : (Finset.univ.filter fun p : (BitString m × BitString m) ×
              (BitString m × BitString m) =>
              outFn p.2 (Q.run (p.1.1, p.2.1) (p.1.2, p.2.2)) = (p.1.1 ⬝ᵥ p.1.2)) =
              Finset.univ.biUnion (fun xy₂ => (Finset.univ.filter fun xy₁ =>
                outFn xy₂ (Q.run (xy₁.1, xy₂.1) (xy₁.2, xy₂.2)) = (xy₁.1 ⬝ᵥ xy₁.2)).map
                ⟨fun xy₁ => (xy₁, xy₂), fun _ _ h => (Prod.mk.inj h).1⟩) := by
            ext ⟨xy₁, xy₂⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
              Finset.mem_map]
            exact ⟨fun h => ⟨xy₂, xy₁, h, rfl⟩,
              fun ⟨_, _, h, heq⟩ => by obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact h⟩
          rw [hbi, Finset.card_biUnion]
          · exact Finset.sum_congr rfl fun _ _ => Finset.card_map _
          · intro u _ v _ huv
            exact Finset.disjoint_left.mpr fun p h1 h2 => by
              obtain ⟨_, _, rfl⟩ := Finset.mem_map.mp h1
              obtain ⟨_, _, heq⟩ := Finset.mem_map.mp h2
              exact huv (Prod.mk.inj heq).2.symm
        exact_mod_cast hcard
      have hex_xy₂ : ∃ xy₂ : BitString m × BitString m,
          (3 / 5 : ℝ) * M ≤ ((Finset.univ.filter fun xy₁ : BitString m × BitString m =>
            outFn xy₂ (Q.run (xy₁.1, xy₂.1) (xy₁.2, xy₂.2)) = (xy₁.1 ⬝ᵥ xy₁.2)).card : ℝ) := by
        by_contra hall
        push Not at hall
        have hlt := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun xy₂ _ => hall xy₂
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
        dsimp only [M] at hgood hlt
        linarith [hsum_eq]
      obtain ⟨xy₂, hxy₂⟩ := hex_xy₂
      let proto' : Protocol (BitString m) (BitString m) Bool :=
        (Q.comap (fun x => (x, xy₂.1)) (fun y => (y, xy₂.2))).map (outFn xy₂)
      refine ⟨proto', ?_, by simp [proto', hQ_depth]⟩
      unfold Protocol.distributionalError Cslib.Probability.PMF.errorProb
      rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal, div_le_iff₀ hM_pos]
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (BitString m × BitString m)))
        (fun xy₁ => (xy₁.1 ⬝ᵥ xy₁.2) = proto'.run xy₁.1 xy₁.2)
      rw [Finset.card_univ] at hpart
      have hgood_eq : (Finset.univ.filter fun xy₁ : BitString m × BitString m =>
          (xy₁.1 ⬝ᵥ xy₁.2) = proto'.run xy₁.1 xy₁.2) =
          (Finset.univ.filter fun xy₁ : BitString m × BitString m =>
            outFn xy₂ (Q.run (xy₁.1, xy₂.1) (xy₁.2, xy₂.2)) = (xy₁.1 ⬝ᵥ xy₁.2)) := by
        ext xy₁
        simp [proto', eq_comm]
      rw [hgood_eq] at hpart
      have hpartR : ((Finset.univ.filter fun xy₁ : BitString m × BitString m =>
            outFn xy₂ (Q.run (xy₁.1, xy₂.1) (xy₁.2, xy₂.2)) = (xy₁.1 ⬝ᵥ xy₁.2)).card : ℝ) +
          ((Finset.univ.filter fun xy₁ : BitString m × BitString m =>
            ¬ (xy₁.1 ⬝ᵥ xy₁.2) = proto'.run xy₁.1 xy₁.2).card : ℝ) = M := by
        exact_mod_cast hpart
      have hfilt_eq : (Finset.univ.filter fun xy₁ : BitString m × BitString m =>
          xy₁ ∈ {q | ¬ (q.1 ⬝ᵥ q.2) = proto'.run q.1 q.2}) =
          (Finset.univ.filter fun xy₁ : BitString m × BitString m =>
            ¬ (xy₁.1 ⬝ᵥ xy₁.2) = proto'.run xy₁.1 xy₁.2) := rfl
      rw [hfilt_eq]
      linarith
    rcases hcases with h1 | h2 | h3
    · refine havg_snd proto hproto_depth (fun _ uv => !uv.1) (h1.trans ?_)
      have hdisj : Disjoint S00 S01 := Finset.disjoint_left.mpr fun q h0 h1 =>
        (Finset.mem_filter.mp h0).2.2 (Finset.mem_filter.mp h1).2.2
      rw [← Nat.cast_add, ← Finset.card_union_of_disjoint hdisj]
      exact_mod_cast Finset.card_le_card fun q hq => by
        have hne1 : (proto.run q.1 q.2).1 ≠ (q.1.1 ⬝ᵥ q.2.1) := by
          rcases Finset.mem_union.mp hq with h | h <;> exact (Finset.mem_filter.mp h).2.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, bool_not_eq_of_ne hne1⟩
    · let swapHalves (x : BitString m × BitString m) : BitString m × BitString m := (x.2, x.1)
      let proto_sw := proto.comap swapHalves swapHalves
      have hsum_eq : ((Finset.univ.filter fun q : Quad =>
          (!(proto_sw.run q.1 q.2).2) = (q.1.1 ⬝ᵥ q.2.1)).card : ℝ) =
          (S00.card : ℝ) + S10.card := by
        have hdisj : Disjoint S00 S10 := Finset.disjoint_left.mpr fun q h0 h1 =>
          (Finset.mem_filter.mp h0).2.1 (Finset.mem_filter.mp h1).2.1
        rw [← Nat.cast_add, ← Finset.card_union_of_disjoint hdisj]
        congr 1
        refine Finset.card_nbij'
          (fun q : Quad => (swapHalves q.1, swapHalves q.2))
          (fun q : Quad => (swapHalves q.1, swapHalves q.2))
          (fun q hq => by
            have h := (Finset.mem_filter.mp hq).2
            simp only [proto_sw, Protocol.run_comap, swapHalves] at h
            have hne2 : (proto.run (q.1.2, q.1.1) (q.2.2, q.2.1)).2 ≠ (q.1.1 ⬝ᵥ q.2.1) :=
              bool_ne_of_not_eq h
            rw [Finset.mem_coe, Finset.mem_union]
            by_cases h1 : (proto.run (q.1.2, q.1.1) (q.2.2, q.2.1)).1 = (q.1.2 ⬝ᵥ q.2.2)
            · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, hne2⟩)
            · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, hne2⟩))
          (fun q hq => by
            have hne2 : (proto.run q.1 q.2).2 ≠ (q.1.2 ⬝ᵥ q.2.2) := by
              rcases Finset.mem_union.mp hq with h | h <;> exact (Finset.mem_filter.mp h).2.2
            refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
            simp only [proto_sw, Protocol.run_comap, swapHalves]
            exact bool_not_eq_of_ne hne2)
          (fun _ _ => rfl) (fun _ _ => rfl)
      exact havg_snd proto_sw (by simp [proto_sw, hproto_depth]) (fun _ uv => !uv.2)
        (h2.trans_eq hsum_eq.symm)
    · refine havg_snd proto hproto_depth (fun xy₂ uv => !(xor (xor uv.1 uv.2) (xy₂.1 ⬝ᵥ xy₂.2)))
        (h3.trans ?_)
      have hdisj : Disjoint S01 S10 := Finset.disjoint_left.mpr fun q h0 h1 =>
        (Finset.mem_filter.mp h0).2.1 (Finset.mem_filter.mp h1).2.1
      rw [← Nat.cast_add, ← Finset.card_union_of_disjoint hdisj]
      exact_mod_cast Finset.card_le_card fun q hq => by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rcases Finset.mem_union.mp hq with h | h
        · exact bool_not_xor_eq_of_ne_eq (Or.inl (Finset.mem_filter.mp h).2)
        · exact bool_not_xor_eq_of_ne_eq (Or.inr (Finset.mem_filter.mp h).2)

/-- Linear `Ω(n)` lower bound on `1 / 3`-error pseudodeterministic communication complexity for
`twoBitAvoidDotProduct n`, contrasting with its `0`-bit `1 / 3`-error randomized complexity. -/
theorem twoBitAvoidDotProduct_pseudodeterministic_lower :
    (∀ n : ℕ, PublicCoin.ecomplexity (1 / 3) (twoBitAvoidDotProduct n) Set.univ Set.univ = 0) ∧
    (∀ n : ℕ, 20 ≤ n →
      (⌈(1 / 400 : ℝ) * n⌉₊ : ℕ∞) ≤ pseudodeterministicComplexity (1 / 3)
        (twoBitAvoidDotProduct n)) := by
  constructor
  · intro n
    refine nonpos_iff_eq_zero.mp ?_
    calc PublicCoin.ecomplexity (1 / 3) (twoBitAvoidDotProduct n) Set.univ Set.univ
        ≤ PublicCoin.ecomplexity (1 / 4) (twoBitAvoidDotProduct n) Set.univ Set.univ :=
          PublicCoin.ecomplexity_anti (by norm_num)
      _ = 0 := twoBitAvoidDotProduct_ecomplexity_quarter n
  · intro n hn
    cases hps : pseudodeterministicComplexity (1 / 3) (twoBitAvoidDotProduct n)
        using ENat.recTopCoe with
    | top => simp
    | coe c =>
      have h89 : ((8 / 9 : ℝ) ^ 24) ≤ 1 / 10 := by norm_num
      have hamp : PublicCoin.ecomplexity (1 / 10) (twoBitAvoidDotProduct n) Set.univ Set.univ ≤
          (48 * c : ℕ) := by
        calc PublicCoin.ecomplexity (1 / 10) (twoBitAvoidDotProduct n) Set.univ Set.univ
            ≤ pseudodeterministicComplexity (1 / 10) (twoBitAvoidDotProduct n) :=
              ecomplexity_le_pseudodeterministicComplexity _ _
          _ ≤ pseudodeterministicComplexity ((8 / 9 : ℝ) ^ 24) (twoBitAvoidDotProduct n) :=
              pseudodeterministicComplexity_anti h89 _
          _ ≤ 2 * 24 * pseudodeterministicComplexity (1 / 3) (twoBitAvoidDotProduct n) :=
              pseudodeterministicComplexity_amplify_one_third (by omega) _
          _ = ((48 * c : ℕ) : ℕ∞) := by rw [hps]; push_cast; ring
      have hlo : ((n / 2 : ℕ) : ℕ∞) ≤ ((96 * c + 4 : ℕ) : ℕ∞) := by
        calc ((n / 2 : ℕ) : ℕ∞)
            ≤ 2 * PublicCoin.ecomplexity (1 / 10) (twoBitAvoidDotProduct n) Set.univ Set.univ +
                4 :=
              twoBitAvoidDotProduct_ecomplexity_tenth_lower n
          _ ≤ 2 * ((48 * c : ℕ) : ℕ∞) + 4 := by gcongr
          _ = ((96 * c + 4 : ℕ) : ℕ∞) := by push_cast; ring
      have hnat : n / 2 ≤ 96 * c + 4 := by exact_mod_cast hlo
      have hc_ge : (1 / 400 : ℝ) * n ≤ c := by
        have hn2 : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
          have : n ≤ 2 * (n / 2) + 1 := by omega
          exact_mod_cast this
        have hnatR : ((n / 2 : ℕ) : ℝ) ≤ 96 * (c : ℝ) + 4 := by exact_mod_cast hnat
        have hnR : (20 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      exact_mod_cast Nat.ceil_le.mpr hc_ge

end CslibFrontier.Computability.Communication
