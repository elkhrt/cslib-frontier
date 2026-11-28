module

public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Probability.IID
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Von Neumann Bit Extraction and Second-Moment Finite-Sample Selection

This module formalizes two reusable tools in discrete and measure-theoretic probability:
1. Exact multi-bit Von Neumann randomness extraction from i.i.d. biased Boolean coins (`vnBlock`,
   `vnExtract`, `vnBlock_law`, `vnExtract_law`), producing exact uniform bit strings conditioned on
   non-abortion with explicit geometric failure probability `(1 - 2 p (1 - p))^L`.
2. Second-moment finite-sample selection on arbitrary probability spaces
   (`exists_finite_average_le`), showing that any `m` measurable `[0, 1]`-valued observables with
   expectations at most `α` yield `T > m / γ²` sample points whose empirical averages are all
   strictly below `α + γ`.

## Main definitions

* `CslibFrontier.Probability.VonNeumann.vnBlock`: single-bit Von Neumann extractor on `L` pairs.
* `CslibFrontier.Probability.VonNeumann.vnExtract`: `s`-bit Von Neumann extractor on `s` blocks.

## Main results

* `CslibFrontier.Probability.VonNeumann.vnBlock_law`: exact output law of `vnBlock`.
* `CslibFrontier.Probability.VonNeumann.vnExtract_law`: exact uniform output law of `vnExtract`.
* `CslibFrontier.Probability.VonNeumann.exists_finite_average_le`: second-moment finite-sample
  averaging bound on arbitrary probability spaces.
-/

public section

namespace CslibFrontier.Probability.VonNeumann

open Finset MeasureTheory Cslib Cslib.Probability Cslib.Probability.PMF
open scoped BigOperators ENNReal NNReal

/-- Single-bit Von Neumann extractor on `L` pairs of Booleans: returns the first bit of the first
non-equal pair, or `none` if all pairs agree. -/
def vnBlock : {L : ℕ} → (Fin L → Bool × Bool) → Option Bool
  | 0, _ => none
  | _ + 1, v =>
      if (v 0).1 ≠ (v 0).2 then some (v 0).1
      else vnBlock (fun j => v j.succ)

/-- Exact law of `vnBlock` on `L` i.i.d. pairs from `q × q`: `Pr[none] = (1 - 2 p (1 - p))^L`,
and `Pr[some true] = Pr[some false] = (1 - (1 - 2 p (1 - p))^L) / 2`. -/
theorem vnBlock_law (q : PMF Bool) (L : ℕ) :
    let pairDist : PMF (Bool × Bool) := q.bind fun a => q.map (a, ·)
    let p : ℝ := (q true).toReal
    let tie : ℝ := 1 - 2 * p * (1 - p)
    (((PMF.iid pairDist L).map vnBlock) none).toReal = tie ^ L ∧
    ∀ b : Bool, (((PMF.iid pairDist L).map vnBlock) (some b)).toReal = (1 - tie ^ L) / 2 := by
  classical
  intro pairDist p tie
  have hpair (a b : Bool) : pairDist (a, b) = q a * q b :=
    bind_map_prodMk_apply q (fun _ => q) (a, b)
  have hqf : (q false).toReal = 1 - p := by
    have hsum : (q false).toReal + (q true).toReal = 1 := by
      have := sum_toReal q; simpa [Fintype.sum_bool, add_comm] using this
    linarith
  have htie_eq : (pairDist (true, true)).toReal + (pairDist (false, false)).toReal = tie := by
    simp only [hpair, ENNReal.toReal_mul, hqf, p, tie]
    ring
  have hnone : (((PMF.iid pairDist L).map vnBlock) none).toReal = tie ^ L := by
    induction L with
    | zero =>
        have heq : (PMF.iid pairDist 0).map vnBlock = PMF.pure none := by
          ext o; simp [vnBlock]
        simp [heq]
    | succ L ih =>
        have hsplit : PMF.iid pairDist (L + 1) =
            (pairDist.bind fun ab => (PMF.iid pairDist L).map fun rest => Fin.cons ab rest) := by
          ext v
          simp only [PMF.iid_apply, PMF.bind_apply, PMF.map_apply]
          rw [tsum_eq_single (v 0)]
          · rw [tsum_eq_single (Fin.tail v)]
            · have hcons : Fin.cons (v 0) (Fin.tail v) = v := Fin.cons_self_tail v
              rw [ite_eq_left hcons.symm, Fin.prod_univ_succ]
              rfl
            · intro rest hrest
              have : v ≠ Fin.cons (v 0) rest := fun h =>
                hrest (funext fun j => ((congrFun h j.succ).trans (Fin.cons_succ _ _ _)).symm)
              simp [this]
          · intro ab hab
            have : ∀ rest, v ≠ Fin.cons ab rest := fun _ h =>
              hab (by simpa using congrFun h.symm 0)
            simp [this]
        rw [hsplit, PMF.map_bind, PMF.bind_apply, tsum_fintype,
          ENNReal.toReal_sum fun _ _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
            (PMF.apply_ne_top _ _)]
        have hterm (ab : Bool × Bool) :
            (pairDist ab *
              (((PMF.iid pairDist L).map (fun rest => Fin.cons ab rest)).map vnBlock) none).toReal =
              if ab.1 = ab.2 then (pairDist ab).toReal * tie ^ L else 0 := by
          rw [ENNReal.toReal_mul, PMF.map_comp]
          by_cases heq : ab.1 = ab.2
          · have hfn :
                vnBlock ∘ (fun rest : Fin L → Bool × Bool => Fin.cons ab rest) = vnBlock := by
              funext rest; simp [vnBlock, heq]
            rw [hfn, ih, ite_eq_left heq]
          · have hfn : vnBlock ∘ (fun rest : Fin L → Bool × Bool => Fin.cons ab rest) =
                Function.const _ (some ab.1) := by
              funext rest; simp [vnBlock, heq]
            rw [hfn, PMF.map_const, PMF.pure_apply, ite_eq_right (by simp), ite_eq_right heq,
              ENNReal.toReal_zero, mul_zero]
        simp_rw [hterm, Fintype.sum_prod_type, Fintype.sum_bool]
        simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, add_zero, zero_add]
        rw [← add_mul, htie_eq, pow_succ']
  refine ⟨hnone, ?_⟩
  let swapAll : (Fin L → Bool × Bool) ≃ (Fin L → Bool × Bool) :=
    { toFun := fun v j => (v j).swap
      invFun := fun v j => (v j).swap
      left_inv := fun v => funext fun j => Prod.swap_swap (v j)
      right_inv := fun v => funext fun j => Prod.swap_swap (v j) }
  have hswap_meas : (PMF.iid pairDist L).map swapAll = PMF.iid pairDist L := by
    ext v
    rw [show v = swapAll (swapAll v) from (swapAll.left_inv v).symm,
      Cslib.Probability.PMF.map_apply_of_injective _ swapAll.injective]
    simp only [PMF.iid_apply, swapAll, Equiv.coe_fn_mk]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [hpair, Prod.swap_swap, mul_comm]
  have hswap_vn : ∀ (k : ℕ) (v : Fin k → Bool × Bool),
      vnBlock (fun j => (v j).swap) = (vnBlock v).map Bool.not := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
        intro v
        simp only [vnBlock, Prod.fst_swap, Prod.snd_swap]
        by_cases h : (v 0).1 ≠ (v 0).2
        · cases h1 : (v 0).1 <;> cases h2 : (v 0).2 <;> simp_all
        · have h' : ¬((v 0).2 ≠ (v 0).1) := fun hc => h hc.symm
          simp only [h, h', ↓reduceIte]
          exact ih (fun j => v j.succ)
  have hsym : ((PMF.iid pairDist L).map vnBlock) (some true) =
      ((PMF.iid pairDist L).map vnBlock) (some false) := by
    have hcomp : ((PMF.iid pairDist L).map swapAll).map vnBlock =
        ((PMF.iid pairDist L).map vnBlock).map (Option.map Bool.not) := by
      rw [PMF.map_comp, PMF.map_comp]
      congr 1; funext v; exact hswap_vn L v
    rw [hswap_meas] at hcomp
    have happ := congrArg (fun ν : PMF (Option Bool) => ν (some false)) hcomp
    have hinj : Function.Injective (Option.map Bool.not) :=
      Option.map_injective Bool.involutive_not.injective
    have hfl : some false = Option.map Bool.not (some true) := rfl
    rw [hfl, Cslib.Probability.PMF.map_apply_of_injective _ hinj] at happ
    exact happ.symm
  have htot : (((PMF.iid pairDist L).map vnBlock) none).toReal +
      (((PMF.iid pairDist L).map vnBlock) (some false)).toReal +
      (((PMF.iid pairDist L).map vnBlock) (some true)).toReal = 1 := by
    have hsum := sum_toReal ((PMF.iid pairDist L).map vnBlock)
    simp only [Fintype.sum_option, Fintype.sum_bool] at hsum
    linarith
  intro b
  cases b <;> linarith [congrArg ENNReal.toReal hsym]

/-- Multi-bit Von Neumann extractor on `s` independent blocks of `L` pairs, outputting
`some (bits : Cslib.BitString s)` when every block succeeds and `none` otherwise. -/
def vnExtract (s L : ℕ) (v : Fin s → Fin L → Bool × Bool) : Option (Cslib.BitString s) :=
  if h : ∀ u : Fin s, (vnBlock (v u)).isSome then
    some fun u => (vnBlock (v u)).get (h u)
  else
    none

/-- Exact uniformity and success-probability law for `vnExtract`. -/
theorem vnExtract_law (q : PMF Bool) (s L : ℕ) :
    let pairDist : PMF (Bool × Bool) := q.bind fun a => q.map (a, ·)
    let blockDist : PMF (Fin L → Bool × Bool) := PMF.iid pairDist L
    let p : ℝ := (q true).toReal
    let tie : ℝ := 1 - 2 * p * (1 - p)
    ∀ bits : Cslib.BitString s,
      (((PMF.iid blockDist s).map (vnExtract s L)) (some bits)).toReal =
        ((1 - tie ^ L) / 2) ^ s := by
  classical
  intro pairDist blockDist p tie bits
  have hpre :
      ((PMF.iid blockDist s).map (vnExtract s L)) (some bits) =
        ∏ u : Fin s, ((blockDist.map vnBlock) (some (bits u))) := by
    have hiff : ∀ v : Fin s → Fin L → Bool × Bool,
        vnExtract s L v = some bits ↔ ∀ u : Fin s, vnBlock (v u) = some (bits u) := fun v => by
      simp only [vnExtract]
      split_ifs with h
      · simp only [Option.some.injEq]
        constructor
        · intro heq u; subst heq; exact (Option.some_get (h u)).symm
        · intro hall; funext u; simp [hall u]
      · exact ⟨False.elim, fun hall => absurd (fun u => by simp [hall u]) h⟩
    simp only [PMF.map_apply, PMF.iid_apply, tsum_fintype]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : ∀ u : Fin s, vnBlock (v u) = some (bits u)
    · have h1 : some bits = vnExtract s L v := ((hiff v).mpr hv).symm
      rw [ite_eq_left h1]
      refine Finset.prod_congr rfl fun u _ => by rw [ite_eq_left (hv u).symm]
    · have h1 : some bits ≠ vnExtract s L v := fun h => hv ((hiff v).mp h.symm)
      rw [ite_eq_right h1]
      symm
      obtain ⟨u, hu⟩ := not_forall.mp hv
      exact Finset.prod_eq_zero (Finset.mem_univ u) (ite_eq_right fun h => hu h.symm)
  rw [hpre, ENNReal.toReal_prod]
  dsimp only [blockDist, pairDist]
  simp_rw [(vnBlock_law q L).2]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, p, tie]

/-- Second-moment finite-sample selection: given `m` measurable `[0, 1]`-valued functions on a
probability space `(Ω, ν)` with expectations at most `α`, and any `T ≥ 1`, `γ > 0` with
`(m : ℝ) < (T : ℝ) * γ ^ 2`, there exist `T` points `xs : Fin T → Ω` whose empirical average is
strictly below `α + γ` simultaneously for all `i : Fin m`. -/
theorem exists_finite_average_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] {m T : ℕ} (hT : 0 < T) (f : Fin m → Ω → ℝ)
    (hmeas : ∀ i, Measurable (f i)) (h01 : ∀ i ω, 0 ≤ f i ω ∧ f i ω ≤ 1)
    {α γ : ℝ} (hmean : ∀ i, ∫ ω, f i ω ∂ν ≤ α) (hγ : 0 < γ)
    (hcard : (m : ℝ) < (T : ℝ) * γ ^ 2) :
    ∃ xs : Fin T → Ω, ∀ i : Fin m, (∑ t : Fin T, f i (xs t)) / (T : ℝ) < α + γ := by
  classical
  let νT : Measure (Fin T → Ω) := Measure.pi fun _ : Fin T => ν
  have : IsProbabilityMeasure νT := by unfold νT; infer_instance
  let μ : Fin m → ℝ := fun i => ∫ ω, f i ω ∂ν
  let g : Fin m → (Fin T → Ω) → ℝ := fun i xs => ∑ t : Fin T, (f i (xs t) - μ i)
  have hint_f (i : Fin m) : Integrable (f i) ν :=
    Integrable.of_bound (hmeas i).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h01 i ω).1]; exact (h01 i ω).2)
  have hμ_bounds (i : Fin m) : 0 ≤ μ i ∧ μ i ≤ 1 := by
    constructor
    · exact integral_nonneg fun ω => (h01 i ω).1
    · calc μ i = ∫ ω, f i ω ∂ν := rfl
        _ ≤ ∫ _, (1 : ℝ) ∂ν := integral_mono (hint_f i) (integrable_const 1) fun ω => (h01 i ω).2
        _ = 1 := by simp
  have hcentered_bound (i : Fin m) (ω : Ω) : |f i ω - μ i| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [(h01 i ω).1, (h01 i ω).2, (hμ_bounds i).1, (hμ_bounds i).2]
  have hcentered_int (i : Fin m) : ∫ ω, (f i ω - μ i) ∂ν = 0 := by
    rw [integral_sub (hint_f i) (integrable_const (μ i))]
    simp [μ]
  have hvar (i : Fin m) : ∫ xs, (g i xs) ^ 2 ∂νT ≤ (T : ℝ) := by
    have hexp : ∀ xs : Fin T → Ω,
        (g i xs) ^ 2 = ∑ t₁ : Fin T, ∑ t₂ : Fin T, (f i (xs t₁) - μ i) * (f i (xs t₂) - μ i) := by
      intro xs
      dsimp only [g]
      rw [sq, Finset.sum_mul]
      exact Finset.sum_congr rfl fun t₁ _ => Finset.mul_sum _ _ _
    simp_rw [hexp]
    have hint_term (t₁ t₂ : Fin T) :
        Integrable (fun xs : Fin T → Ω => (f i (xs t₁) - μ i) * (f i (xs t₂) - μ i)) νT := by
      have hm : Measurable (fun xs : Fin T → Ω => (f i (xs t₁) - μ i) * (f i (xs t₂) - μ i)) :=
        (((hmeas i).comp (measurable_pi_apply t₁)).sub measurable_const).mul
          (((hmeas i).comp (measurable_pi_apply t₂)).sub measurable_const)
      refine Integrable.of_bound hm.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun xs => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      calc |f i (xs t₁) - μ i| * |f i (xs t₂) - μ i| ≤ 1 * 1 :=
            mul_le_mul (hcentered_bound i _) (hcentered_bound i _) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    rw [integral_finsetSum _ fun t₁ _ => integrable_finsetSum _ fun t₂ _ => hint_term t₁ t₂]
    have hinner (t₁ : Fin T) :
        ∫ xs, ∑ t₂ : Fin T, (f i (xs t₁) - μ i) * (f i (xs t₂) - μ i) ∂νT ≤ 1 := by
      rw [integral_finsetSum _ fun t₂ _ => hint_term t₁ t₂]
      rw [Finset.sum_eq_single t₁]
      · calc ∫ xs, (f i (xs t₁) - μ i) * (f i (xs t₁) - μ i) ∂νT
            ≤ ∫ _, (1 : ℝ) ∂νT := by
              refine integral_mono (hint_term t₁ t₁) (integrable_const 1) fun xs => ?_
              have hb := hcentered_bound i (xs t₁)
              nlinarith [abs_le.mp hb]
          _ = 1 := by simp
      · intro t₂ _ hne
        let h : Fin T → Ω → ℝ := fun t ω =>
          if t = t₁ ∨ t = t₂ then f i ω - μ i else 1
        have hprod : ∀ xs : Fin T → Ω,
            (f i (xs t₁) - μ i) * (f i (xs t₂) - μ i) = ∏ t : Fin T, h t (xs t) := fun xs => by
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t₁)]
          have hmem2 : t₂ ∈ Finset.univ.erase t₁ := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
          rw [← Finset.mul_prod_erase _ _ hmem2]
          have hrest : ∏ t ∈ (Finset.univ.erase t₁).erase t₂, h t (xs t) = 1 :=
            Finset.prod_eq_one fun t ht => by
              have ht2 : t ≠ t₂ := (Finset.mem_erase.mp ht).1
              have ht1 : t ≠ t₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
              simp [h, ht1, ht2]
          simp [h, hrest]
        simp_rw [hprod]
        rw [MeasureTheory.integral_fintype_prod_eq_prod h]
        refine Finset.prod_eq_zero (Finset.mem_univ t₁) ?_
        simp [h, hcentered_int i]
      · intro h; exact absurd (Finset.mem_univ t₁) h
    calc ∑ t₁ : Fin T, ∫ xs, ∑ t₂ : Fin T, (f i (xs t₁) - μ i) * (f i (xs t₂) - μ i) ∂νT
        ≤ ∑ _t₁ : Fin T, (1 : ℝ) := Finset.sum_le_sum fun t₁ _ => hinner t₁
      _ = (T : ℝ) := by simp
  have hint_g2 (i : Fin m) : Integrable (fun xs => (g i xs) ^ 2) νT := by
    have hm : Measurable (fun xs => (g i xs) ^ 2) :=
      (Finset.measurable_sum Finset.univ fun t _ =>
        ((hmeas i).comp (measurable_pi_apply t)).sub measurable_const).pow_const 2
    refine Integrable.of_bound hm.aestronglyMeasurable ((T : ℝ) ^ 2)
      (Filter.Eventually.of_forall fun xs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have habs : |g i xs| ≤ (T : ℝ) := by
      calc |g i xs| ≤ ∑ t : Fin T, |f i (xs t) - μ i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _t : Fin T, (1 : ℝ) := Finset.sum_le_sum fun t _ => hcentered_bound i (xs t)
        _ = (T : ℝ) := by simp
    nlinarith [abs_le.mp habs]
  have hsum_int : ∫ xs, ∑ i : Fin m, (g i xs) ^ 2 ∂νT ≤ (m : ℝ) * (T : ℝ) := by
    rw [integral_finsetSum _ fun i _ => hint_g2 i]
    calc ∑ i : Fin m, ∫ xs, (g i xs) ^ 2 ∂νT
        ≤ ∑ _i : Fin m, (T : ℝ) := Finset.sum_le_sum fun i _ => hvar i
      _ = (m : ℝ) * (T : ℝ) := by simp
  have hT_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
  have hlt_bound : (m : ℝ) * (T : ℝ) < ((T : ℝ) * γ) ^ 2 := by
    have hmul := mul_lt_mul_of_pos_right hcard hT_pos
    nlinarith
  have hex : ∃ xs : Fin T → Ω, ∑ i : Fin m, (g i xs) ^ 2 < ((T : ℝ) * γ) ^ 2 := by
    by_contra hall
    push Not at hall
    have hge : ((T : ℝ) * γ) ^ 2 ≤ ∫ xs, ∑ i : Fin m, (g i xs) ^ 2 ∂νT := by
      calc ((T : ℝ) * γ) ^ 2 = ∫ _, ((T : ℝ) * γ) ^ 2 ∂νT := by simp
        _ ≤ ∫ xs, ∑ i : Fin m, (g i xs) ^ 2 ∂νT :=
            integral_mono (integrable_const _) (integrable_finsetSum _ fun i _ => hint_g2 i) hall
    linarith
  obtain ⟨xs, hxs⟩ := hex
  refine ⟨xs, fun i => ?_⟩
  have hgi2 : (g i xs) ^ 2 < ((T : ℝ) * γ) ^ 2 :=
    lt_of_le_of_lt (Finset.single_le_sum (fun j _ => sq_nonneg (g j xs)) (Finset.mem_univ i)) hxs
  have hgi_lt : g i xs < (T : ℝ) * γ := by
    have hpos : 0 < (T : ℝ) * γ := mul_pos hT_pos hγ
    nlinarith
  have hsum_eq : ∑ t : Fin T, f i (xs t) = g i xs + (T : ℝ) * μ i := by
    simp only [g, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  rw [div_lt_iff₀ hT_pos, hsum_eq]
  have hμi : μ i ≤ α := hmean i
  nlinarith

end CslibFrontier.Probability.VonNeumann
