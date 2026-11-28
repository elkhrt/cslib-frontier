module

public import CslibFrontier.Computability.Communication.NOF.Discrepancy
public import CslibFrontier.Computability.Communication.NOF.Randomized
public import CslibFrontier.Foundations.Data.BitString.Sign
import CslibFrontier.Probability.PMF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Generalized Discrepancy Method and Protocol Pullbacks for NOF Communication

Extends multiparty number-on-the-forehead (NOF) communication discrepancy theory with:

* Per-player protocol pullbacks along local input maps `Γ i : X i → Y i`, showing that both
  deterministic and public-coin randomized NOF communication complexities are nonincreasing under
  per-player reductions.
* The generalized discrepancy method: if `f` has correlation at least `δ` with a Boolean function
  `g` under a distribution `μ`, then any public-coin NOF protocol computing `f` with error at most
  `1 / 2 - ε` and communication cost `c` satisfies `δ + 2 ε - 1 ≤ 2 ^ c · disc_μ(g)`.
* The `1 / (2 n + 1)` discrepancy lower bound for `k`-party set disjointness (`k ≥ 2`) under
  every input distribution `μ`, demonstrating the barrier of the classical discrepancy method on
  disjointness.

## Main definitions

* `CslibFrontier.Computability.Communication.NOF.pullbackProtocol`: pulls back a deterministic
  NOF protocol along per-player local conversions.
* `CslibFrontier.Computability.Communication.NOF.disjointness`: `k`-party set disjointness on
  `n`-bit strings.

## Main results

* `CslibFrontier.Computability.Communication.NOF.detComplexity_comp_le`,
  `CslibFrontier.Computability.Communication.NOF.randComplexity_comp_le`: monotonicity of NOF
  communication complexity under per-player input reductions.
* `CslibFrontier.Computability.Communication.NOF.protocol_generalized_discrepancy`,
  `CslibFrontier.Computability.Communication.NOF.publicCoin_generalized_discrepancy`:
  deterministic and public-coin generalized discrepancy lower bounds.
* `CslibFrontier.Computability.Communication.NOF.one_div_le_discrepancy_disjointness`:
  `1 / (2 n + 1) ≤ NOF.discrepancy μ (disjointness k n)` for every `k ≥ 2` and distribution `μ`.
-/

public section

namespace CslibFrontier.Computability.Communication.NOF

open Cslib Cslib.BitString Cslib.Communication Finset
open scoped BigOperators

section Pullback

variable {ι : Type*} {X Y : ι → Type*} {Z : Type*}

/-- Pulling back a deterministic NOF protocol along per-player local conversions `Γ i : X i → Y i`.
Each player `i` sees `x j` for all `j ≠ i` and privately applies `Γ j` before simulating `p`. -/
def pullbackProtocol (Γ : ∀ i, X i → Y i) : NOF.Protocol Y Z → NOF.Protocol X Z
  | .output z => .output z
  | .speak i send p₀ p₁ =>
      .speak i (fun v => send fun j => Γ j.1 (v j))
        (pullbackProtocol Γ p₀) (pullbackProtocol Γ p₁)

/-- Running a pulled-back protocol evaluates `p` on the locally transformed inputs. -/
@[simp]
theorem run_pullbackProtocol (Γ : ∀ i, X i → Y i) (p : NOF.Protocol Y Z) (x : ∀ i, X i) :
    (pullbackProtocol Γ p).run x = p.run (fun i => Γ i (x i)) := by
  induction p with
  | output z => rfl
  | speak i send p₀ p₁ ih₀ ih₁ =>
    simp only [pullbackProtocol, NOF.Protocol.run_speak, ih₀, ih₁]
    rfl

/-- Pulling back a protocol preserves its communication depth. -/
@[simp]
theorem depth_pullbackProtocol (Γ : ∀ i, X i → Y i) (p : NOF.Protocol Y Z) :
    (pullbackProtocol Γ p).depth = p.depth := by
  induction p with
  | output _ => rfl
  | speak _ _ _ _ ih₀ ih₁ =>
    simp only [pullbackProtocol, NOF.Protocol.depth_speak, ih₀, ih₁]

/-- Per-player reduction does not increase deterministic NOF communication complexity. -/
theorem detComplexity_comp_le (Γ : ∀ i, X i → Y i) (g : (∀ i, Y i) → Bool) :
    NOF.Protocol.ecomplexityFun (fun x => g fun i => Γ i (x i)) ≤
      NOF.Protocol.ecomplexityFun g := by
  rw [NOF.Protocol.le_ecomplexityFun_iff]
  intro p hp
  have hrun : (pullbackProtocol Γ p).run = fun x => g fun i => Γ i (x i) :=
    funext fun x => by rw [run_pullbackProtocol, hp]
  calc NOF.Protocol.ecomplexityFun (fun x => g fun i => Γ i (x i))
      ≤ (pullbackProtocol Γ p).depth := NOF.Protocol.ecomplexityFun_le_depth hrun
    _ = p.depth := by rw [depth_pullbackProtocol]

/-- Per-player reduction does not increase public-coin randomized NOF communication complexity. -/
theorem randComplexity_comp_le (Γ : ∀ i, X i → Y i) (η : ℝ) (g : (∀ i, Y i) → Bool) :
    NOF.PublicCoin.ecomplexityFun η (fun x => g fun i => Γ i (x i)) ≤
      NOF.PublicCoin.ecomplexityFun η g := by
  rw [NOF.PublicCoin.ecomplexityFun, NOF.PublicCoin.ecomplexityFun,
    RandomizedCost.ecomplexityFun, RandomizedCost.ecomplexityFun,
    ← NOF.PublicCoin.ecomplexity, ← NOF.PublicCoin.ecomplexity,
    NOF.PublicCoin.le_ecomplexity_iff]
  intro P hP
  let Q : NOF.PublicCoin X Bool := P.map (pullbackProtocol Γ)
  have hQ_depth : Q.depth ≤ P.depth := by
    rw [NOF.PublicCoin.depth_le_iff]
    intro q hq
    rw [PMF.mem_support_map_iff] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [depth_pullbackProtocol]
    exact NOF.PublicCoin.depth_le_depth hp
  have hQ_solves : Q.Solves η (fun x b => g (fun i => Γ i (x i)) = b) Set.univ := by
    intro x _
    have hpx := hP (fun i => Γ i (x i)) trivial
    have herr_eq : Q.errorProb (fun x b => g (fun i => Γ i (x i)) = b) x =
        P.errorProb (fun y b => g y = b) (fun i => Γ i (x i)) := by
      classical
      simp only [NOF.PublicCoin.errorProb, Probability.PMF.errorProb, Q,
        PMF.toOuterMeasure_map_apply]
      congr 2
      ext p
      simp [run_pullbackProtocol]
    rw [herr_eq]
    exact hpx
  exact (NOF.PublicCoin.ecomplexity_le_depth hQ_solves).trans hQ_depth

end Pullback

section GeneralizedDiscrepancy

variable {ι : Type*} {X : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]

/-- Deterministic protocol step of the generalized discrepancy method: if a deterministic NOF
protocol `p` errs on at most `1 / 2 - ε` fraction of inputs under `μ`, and
`δ ≤ |∑ x, (μ x).toReal * signVal (f x) * signVal (g x)|`, then
`δ + 2 ε - 1 ≤ 2 ^ p.depth · disc_μ(g)`. -/
theorem protocol_generalized_discrepancy {ε δ : ℝ} {f g : (∀ i, X i) → Bool}
    {μ : PMF (∀ i, X i)} (p : NOF.Protocol X Bool)
    (hp : p.distributionalError μ (fun x b => f x = b) ≤ 1 / 2 - ε)
    (hcorr : δ ≤ |∑ x, (μ x).toReal * signVal (f x) * signVal (g x)|) :
    δ + 2 * ε - 1 ≤ (2 : ℝ) ^ p.depth * NOF.discrepancy μ g := by
  classical
  have hdisc : |∑ x, (μ x).toReal * signVal (g x) * signVal (p.run x)| ≤
      (2 : ℝ) ^ p.depth * NOF.discrepancy μ g := by
    simpa [NOF.cylinderIntersection_true] using
      p.abs_sum_mul_signVal_le μ g (fun _ _ => true)
  have hsplit : ∑ x, (μ x).toReal * signVal (f x) * signVal (g x) =
      (∑ x, (μ x).toReal * signVal (g x) * signVal (p.run x)) +
        ∑ x, (μ x).toReal * (signVal (f x) - signVal (p.run x)) * signVal (g x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => by ring
  have herr_sum : |∑ x, (μ x).toReal * (signVal (f x) - signVal (p.run x)) * signVal (g x)| ≤
      2 * p.distributionalError μ (fun x b => f x = b) := by
    calc |∑ x, (μ x).toReal * (signVal (f x) - signVal (p.run x)) * signVal (g x)|
        ≤ ∑ x, |(μ x).toReal * (signVal (f x) - signVal (p.run x)) * signVal (g x)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, (μ x).toReal * |signVal (f x) - signVal (p.run x)| := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [abs_mul, abs_mul, abs_signVal, mul_one, abs_of_nonneg ENNReal.toReal_nonneg]
      _ = 2 * p.distributionalError μ (fun x b => f x = b) := by
            rw [NOF.Protocol.distributionalError, Probability.PMF.errorProb_eq_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            cases hf : f x <;> cases hpx : p.run x <;> simp [signVal] <;> ring
  have htri : δ ≤ |∑ x, (μ x).toReal * signVal (g x) * signVal (p.run x)| +
      |∑ x, (μ x).toReal * (signVal (f x) - signVal (p.run x)) * signVal (g x)| := by
    calc δ ≤ |∑ x, (μ x).toReal * signVal (f x) * signVal (g x)| := hcorr
      _ = |(∑ x, (μ x).toReal * signVal (g x) * signVal (p.run x)) +
            ∑ x, (μ x).toReal * (signVal (f x) - signVal (p.run x)) * signVal (g x)| := by
            rw [hsplit]
      _ ≤ _ := abs_add_le _ _
  linarith

/-- Public-coin generalized discrepancy method: if `f` has public-coin NOF communication complexity
at most `c` at error `1 / 2 - ε` and correlates with `g` under `μ` by at least `δ`, then
`δ + 2 ε - 1 ≤ 2 ^ c · disc_μ(g)`. -/
theorem publicCoin_generalized_discrepancy {ε δ : ℝ} {c : ℕ} {f g : (∀ i, X i) → Bool}
    {μ : PMF (∀ i, X i)} (h : NOF.PublicCoin.ecomplexityFun (1 / 2 - ε) f ≤ c)
    (hcorr : δ ≤ |∑ x, (μ x).toReal * signVal (f x) * signVal (g x)|) :
    δ + 2 * ε - 1 ≤ (2 : ℝ) ^ c * NOF.discrepancy μ g := by
  obtain ⟨P, hP, hc⟩ := NOF.PublicCoin.ecomplexity_le_iff.mp h
  obtain ⟨p, hp_supp, hp_err⟩ := hP.exists_distributionalError_le μ fun _ _ => trivial
  have hdepth : p.depth ≤ c := by exact_mod_cast (NOF.PublicCoin.depth_le_depth hp_supp).trans hc
  have hstep := protocol_generalized_discrepancy p hp_err hcorr
  exact hstep.trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hdepth) NOF.discrepancy_nonneg)

end GeneralizedDiscrepancy

section DisjointnessDiscrepancy

/-- `k`-party set disjointness on `n`-bit inputs: outputs `true` iff there exists a coordinate
`j : Fin n` where every player holds `true`. -/
def disjointness (k n : ℕ) (z : Fin k → BitString n) : Bool :=
  decide (∃ j : Fin n, ∀ i : Fin k, z i j = true)

/-- Classical discrepancy barrier for multiparty set disjointness: under every probability
distribution `μ` over `(BitString n)^k` (`k ≥ 2`), `disc_μ(disjointness k n) ≥ 1 / (2 n + 1)`. -/
theorem one_div_le_discrepancy_disjointness {k n : ℕ} (hk : 2 ≤ k)
    (μ : PMF (Fin k → BitString n)) :
    1 / (2 * (n : ℝ) + 1) ≤ NOF.discrepancy μ (disjointness k n) := by
  classical
  set D := NOF.discrepancy μ (disjointness k n)
  let Xneg : Finset (Fin k → BitString n) := univ.filter fun z => disjointness k n z = true
  have huniv : |∑ z, (μ z).toReal * signVal (disjointness k n z)| ≤ D := by
    simpa [NOF.cylinderIntersection_true] using
      NOF.abs_sum_le_discrepancy μ (disjointness k n) (fun _ _ => true)
  have hsum_split :
      ∑ z, (μ z).toReal * signVal (disjointness k n z) = 1 - 2 * ∑ z ∈ Xneg, (μ z).toReal := by
    rw [← Probability.PMF.sum_toReal μ]
    have hXneg : ∑ z ∈ Xneg, (μ z).toReal =
        ∑ z, if disjointness k n z = true then (μ z).toReal else 0 := by
      simp [Xneg, Finset.sum_filter]
    rw [hXneg, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    cases h : disjointness k n z
    · simp [signVal]
    · simp [signVal]; ring
  have hneg_lower : 1 - D ≤ 2 * ∑ z ∈ Xneg, (μ z).toReal := by
    have h1 : ∑ z, (μ z).toReal * signVal (disjointness k n z) ≤ D := (le_abs_self _).trans huniv
    linarith [hsum_split]
  let φ (j : Fin n) : ∀ i : Fin k, NOF.View (fun _ : Fin k => BitString n) i → Bool :=
    fun i v => decide (∀ r : {r : Fin k // r ≠ i}, v r j = true)
  have hmem_φ (j : Fin n) (z : Fin k → BitString n) :
      z ∈ NOF.cylinderIntersection (φ j) ↔ ∀ i : Fin k, z i j = true := by
    simp only [NOF.mem_cylinderIntersection, φ, NOF.view_apply]
    constructor
    · intro h i
      have hex : ∃ p : Fin k, p ≠ i := by
        by_cases hi : i.1 = 0
        · refine ⟨⟨1, by omega⟩, fun heq => ?_⟩
          have := congrArg Fin.val heq; dsimp at this; omega
        · refine ⟨⟨0, by omega⟩, fun heq => ?_⟩
          have := congrArg Fin.val heq; dsimp at this; omega
      obtain ⟨p, hp⟩ := hex
      exact of_decide_eq_true (h p) ⟨i, hp.symm⟩
    · intro h _
      exact decide_eq_true fun r => h r.1
  let C (j : Fin n) : Finset (Fin k → BitString n) :=
    univ.filter fun z => z ∈ NOF.cylinderIntersection (φ j)
  have hCj_le (j : Fin n) : ∑ z ∈ C j, (μ z).toReal ≤ D := by
    have hdisc := NOF.abs_sum_le_discrepancy μ (disjointness k n) (φ j)
    have hmono : ∑ z ∈ C j, (μ z).toReal * signVal (disjointness k n z) =
        -(∑ z ∈ C j, (μ z).toReal) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun z hz => ?_
      have hall : ∀ i : Fin k, z i j = true := (hmem_φ j z).mp (mem_filter.mp hz).2
      have hdisj : disjointness k n z = true := decide_eq_true ⟨j, hall⟩
      simp [hdisj, signVal]
    have heq : ∑ z with z ∈ NOF.cylinderIntersection (φ j),
        (μ z).toReal * signVal (disjointness k n z) = -(∑ z ∈ C j, (μ z).toReal) := hmono
    rw [heq, abs_neg, abs_of_nonneg (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)] at hdisc
    exact hdisc
  have hcov : Xneg ⊆ univ.biUnion C := by
    intro z hz
    have hdisj : disjointness k n z = true := (mem_filter.mp hz).2
    obtain ⟨j, hj⟩ := of_decide_eq_true hdisj
    exact mem_biUnion.mpr ⟨j, mem_univ j, mem_filter.mpr ⟨mem_univ z, (hmem_φ j z).mpr hj⟩⟩
  have hbiUnion (s : Finset (Fin n)) :
      ∑ z ∈ s.biUnion C, (μ z).toReal ≤ ∑ j ∈ s, ∑ z ∈ C j, (μ z).toReal := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hj]
      have hu := Finset.sum_union_inter (s₁ := C j) (s₂ := s.biUnion C)
        (f := fun z => (μ z).toReal)
      have hnn : 0 ≤ ∑ z ∈ C j ∩ s.biUnion C, (μ z).toReal :=
        Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
      linarith
  have hXneg_le : ∑ z ∈ Xneg, (μ z).toReal ≤ (n : ℝ) * D := by
    calc ∑ z ∈ Xneg, (μ z).toReal
        ≤ ∑ z ∈ univ.biUnion C, (μ z).toReal :=
            Finset.sum_le_sum_of_subset_of_nonneg hcov fun _ _ _ => ENNReal.toReal_nonneg
      _ ≤ ∑ j : Fin n, ∑ z ∈ C j, (μ z).toReal := hbiUnion univ
      _ ≤ ∑ _j : Fin n, D := Finset.sum_le_sum fun j _ => hCj_le j
      _ = (n : ℝ) * D := by simp
  have hpos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hpos]
  linarith

end DisjointnessDiscrepancy

end CslibFrontier.Computability.Communication.NOF
