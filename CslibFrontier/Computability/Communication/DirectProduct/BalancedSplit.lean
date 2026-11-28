module

public import CslibFrontier.Computability.Communication.DirectProduct.IntersectionDist
import Cslib.Probability.StatisticalDistance
import CslibFrontier.Probability.PMF.Coin
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.Product
import CslibFrontier.Probability.ProductConditioning
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Balanced Partition Sampling and One-Side Product Conditioning

Combinatorial and probabilistic tools for fixed-weight intersection distributions on binary
strings of fixed Hamming weight `m`:

* Binomial mode lower bound and product-conditioning bad-coordinate bound on a single player's
  subset family.
* Balanced ordered splits `OrderedSplit n` (`point`, `left`, `right`) of `Fin n` into a
  distinguished coordinate and two disjoint halves of sizes `(n - 1) / 2` and `n / 2`.
* Exact sampling identities expressing `μ_{0,n,m}` and `μ_{1,n,m}` as uniform averages over
  balanced ordered splits, plus a small-`n` marginal union bound.
-/

public section

namespace CslibFrontier.Computability.Communication

open Cslib Finset

/-! ### Elementary binomial mode and product-conditioning bounds -/

/-- The binomial probability `C(s, m) * (m / s) ^ m * (1 - m / s) ^ (s - m)` at its mode `m` is at
least `1 / (s + 1)`. -/
private theorem binomial_mode_lower {s m : ℕ} (hm0 : 0 < m) (hms : m < s) :
    (1 : ℝ) / ((s : ℝ) + 1) ≤
      (s.choose m : ℝ) * ((m : ℝ) / (s : ℝ)) ^ m * (1 - (m : ℝ) / (s : ℝ)) ^ (s - m) := by
  set p : ℝ := (m : ℝ) / (s : ℝ)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (hm0.trans hms)
  have hp0 : 0 < p := div_pos (by exact_mod_cast hm0) hs0
  have h1p0 : 0 < 1 - p := by
    rw [sub_pos, div_lt_one hs0]
    exact_mod_cast hms
  set f : ℕ → ℝ := fun j => (s.choose j : ℝ) * p ^ j * (1 - p) ^ (s - j)
  have hstep_up : ∀ j, j < m → f j ≤ f (j + 1) := by
    intro j hj
    have hjs : j < s := hj.trans hms
    have hchoose : ((j + 1 : ℕ) : ℝ) * (s.choose (j + 1) : ℝ) =
        ((s - j : ℕ) : ℝ) * (s.choose j : ℝ) := by
      exact_mod_cast (by
        have h := Nat.choose_succ_right_eq s j
        linarith : (j + 1) * s.choose (j + 1) = (s - j) * s.choose j)
    have hpow1 : p ^ (j + 1) = p ^ j * p := pow_succ p j
    have hpow2 : (1 - p) ^ (s - j) = (1 - p) ^ (s - (j + 1)) * (1 - p) := by
      rw [← pow_succ, show s - (j + 1) + 1 = s - j by omega]
    have hratio : ((j + 1 : ℕ) : ℝ) * (1 - p) ≤ ((s - j : ℕ) : ℝ) * p := by
      have h1p_eq : 1 - p = ((s - m : ℕ) : ℝ) / (s : ℝ) := by
        dsimp only [p]
        rw [Nat.cast_sub hms.le]
        field_simp
      rw [h1p_eq]
      dsimp only [p]
      rw [mul_div_assoc', mul_div_assoc', div_le_div_iff_of_pos_right hs0]
      have hnat : (j + 1) * (s - m) ≤ (s - j) * m := by
        have hint : (((j + 1) * (s - m) : ℕ) : ℤ) ≤ (((s - j) * m : ℕ) : ℤ) := by
          zify [hms.le, hjs.le]
          have hjm : (j : ℤ) + 1 ≤ (m : ℤ) := by exact_mod_cast hj
          nlinarith
        exact_mod_cast hint
      exact_mod_cast hnat
    have hmul : ((j + 1 : ℕ) : ℝ) * f j ≤ ((j + 1 : ℕ) : ℝ) * f (j + 1) := by
      calc
        ((j + 1 : ℕ) : ℝ) * f j
          = (s.choose j : ℝ) * p ^ j * (1 - p) ^ (s - (j + 1)) *
              (((j + 1 : ℕ) : ℝ) * (1 - p)) := by
            dsimp only [f]; rw [hpow2]; ring
        _ ≤ (s.choose j : ℝ) * p ^ j * (1 - p) ^ (s - (j + 1)) *
              (((s - j : ℕ) : ℝ) * p) := by
            gcongr
        _ = (((s - j : ℕ) : ℝ) * (s.choose j : ℝ)) * (p ^ j * p) *
              (1 - p) ^ (s - (j + 1)) := by ring
        _ = ((j + 1 : ℕ) : ℝ) * f (j + 1) := by
            rw [← hchoose, ← hpow1]; dsimp only [f]; ring
    exact le_of_mul_le_mul_left hmul (by positivity)
  have hstep_dn : ∀ j, m ≤ j → j < s → f (j + 1) ≤ f j := by
    intro j hmj hjs
    have hchoose : ((j + 1 : ℕ) : ℝ) * (s.choose (j + 1) : ℝ) =
        ((s - j : ℕ) : ℝ) * (s.choose j : ℝ) := by
      exact_mod_cast (by
        have h := Nat.choose_succ_right_eq s j
        linarith : (j + 1) * s.choose (j + 1) = (s - j) * s.choose j)
    have hpow1 : p ^ (j + 1) = p ^ j * p := pow_succ p j
    have hpow2 : (1 - p) ^ (s - j) = (1 - p) ^ (s - (j + 1)) * (1 - p) := by
      rw [← pow_succ, show s - (j + 1) + 1 = s - j by omega]
    have hratio : ((s - j : ℕ) : ℝ) * p ≤ ((j + 1 : ℕ) : ℝ) * (1 - p) := by
      have h1p_eq : 1 - p = ((s - m : ℕ) : ℝ) / (s : ℝ) := by
        dsimp only [p]
        rw [Nat.cast_sub hms.le]
        field_simp
      rw [h1p_eq]
      dsimp only [p]
      rw [mul_div_assoc', mul_div_assoc', div_le_div_iff_of_pos_right hs0]
      have hnat : (s - j) * m ≤ (j + 1) * (s - m) := by
        zify [hms.le, hjs.le]
        nlinarith
      exact_mod_cast hnat
    have hmul : ((j + 1 : ℕ) : ℝ) * f (j + 1) ≤ ((j + 1 : ℕ) : ℝ) * f j := by
      calc
        ((j + 1 : ℕ) : ℝ) * f (j + 1)
          = (((j + 1 : ℕ) : ℝ) * (s.choose (j + 1) : ℝ)) * (p ^ j * p) *
              (1 - p) ^ (s - (j + 1)) := by
            dsimp only [f]; rw [hpow1]; ring
        _ = (s.choose j : ℝ) * p ^ j * (1 - p) ^ (s - (j + 1)) *
              (((s - j : ℕ) : ℝ) * p) := by rw [hchoose]; ring
        _ ≤ (s.choose j : ℝ) * p ^ j * (1 - p) ^ (s - (j + 1)) *
              (((j + 1 : ℕ) : ℝ) * (1 - p)) := by gcongr
        _ = ((j + 1 : ℕ) : ℝ) * f j := by
            dsimp only [f]; rw [hpow2]; ring
    exact le_of_mul_le_mul_left hmul (by positivity)
  have hup : ∀ d j, j + d ≤ m → f j ≤ f (j + d) := by
    intro d
    induction d with
    | zero => intro j _; simp
    | succ d ih =>
      intro j h
      exact (ih j (by omega)).trans (hstep_up (j + d) (by omega))
  have hdn : ∀ d j, m ≤ j → j + d ≤ s → f (j + d) ≤ f j := by
    intro d
    induction d with
    | zero => intro j _ _; simp
    | succ d ih =>
      intro j h1 h2
      exact (hstep_dn (j + d) (by omega) (by omega)).trans (ih j h1 (by omega))
  have hle_m : ∀ j, j ≤ s → f j ≤ f m := by
    intro j hjs
    rcases le_total j m with hjm | hmj
    · have := hup (m - j) j (by omega)
      rwa [show j + (m - j) = m by omega] at this
    · have := hdn (j - m) m le_rfl (by omega)
      rwa [show m + (j - m) = j by omega] at this
  have hsum : ∑ j ∈ range (s + 1), f j = 1 := by
    have hbinom := add_pow p (1 - p) s
    rw [add_sub_cancel, one_pow] at hbinom
    rw [hbinom]
    refine sum_congr rfl fun j _ => ?_
    dsimp only [f]
    ring
  have hbound : (1 : ℝ) ≤ ((s : ℝ) + 1) * f m := by
    calc
      (1 : ℝ) = ∑ j ∈ range (s + 1), f j := hsum.symm
      _ ≤ ∑ _j ∈ range (s + 1), f m := sum_le_sum fun j hj => hle_m j (by
          rw [mem_range] at hj; omega)
      _ = ((s : ℝ) + 1) * f m := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- Statistical distance between two Boolean `PMF`s is the absolute difference on `true`. -/
private theorem dist_pmf_bool (P Q : PMF Bool) :
    let _ := Cslib.Probability.PMF.instMetricSpace (α := Bool)
    dist P Q = |(P true).toReal - (Q true).toReal| := by
  let _ := Cslib.Probability.PMF.instMetricSpace (α := Bool)
  have hP : (P true).toReal + (P false).toReal = 1 := by
    have h := P.tsum_coe
    rw [tsum_fintype, Fintype.sum_bool] at h
    have h' := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_add (P.apply_ne_top true) (P.apply_ne_top false), ENNReal.toReal_one] at h'
    exact h'
  have hQ : (Q true).toReal + (Q false).toReal = 1 := by
    have h := Q.tsum_coe
    rw [tsum_fintype, Fintype.sum_bool] at h
    have h' := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_add (Q.apply_ne_top true) (Q.apply_ne_top false), ENNReal.toReal_one] at h'
    exact h'
  have hneg : (P false).toReal - (Q false).toReal = -((P true).toReal - (Q true).toReal) := by
    linarith
  change (∑ b : Bool, |(P b).toReal - (Q b).toReal|) / 2 = _
  rw [Fintype.sum_bool, hneg, abs_neg]
  ring

/-- For a nonempty family `AS` of `m`-subsets of `S` (`|S| = s`, `0 < m < s`), the `L¹` deviation of
coordinate marginals from `p = m / s` is bounded by `√(s * ln ((s + 1) / α))`, where
`α = |AS| / C(s, m)`. Proved via Raz's product-conditioning lemma. -/
private theorem sum_abs_marginal_sub_le {n m : ℕ} (S : Finset (Fin n))
    (hm0 : 0 < m) (hms : m < S.card) (AS : Finset (BitString n)) (hAS_ne : AS.Nonempty)
    (hAS : ∀ x ∈ AS, supportSet x ⊆ S ∧ (supportSet x).card = m) :
    ∑ i ∈ S, |(#{x ∈ AS | x i = true} : ℝ) / (AS.card : ℝ) - (m : ℝ) / (S.card : ℝ)| ≤
      Real.sqrt ((S.card : ℝ) *
        Real.log (((S.card : ℝ) + 1) / ((AS.card : ℝ) / (S.card.choose m : ℝ)))) := by
  classical
  let _ := Cslib.Probability.PMF.instMetricSpace (α := Bool)
  set s := S.card
  set p : ℝ := (m : ℝ) / (s : ℝ)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (hm0.trans hms)
  have hp0 : 0 < p := div_pos (by exact_mod_cast hm0) hs0
  have hp1 : p < 1 := (div_lt_one hs0).mpr (by exact_mod_cast hms)
  let pI : Set.Icc (0 : ℝ) 1 := ⟨p, hp0.le, hp1.le⟩
  let coinP : PMF Bool := Cslib.Probability.PMF.coin pI
  let ι := {i : Fin n // i ∈ S}
  let π : PMF (ι → Bool) := Cslib.Probability.PMF.pi (fun _ : ι => coinP)
  let ext0 : (ι → Bool) → BitString n := fun u i => if h : i ∈ S then u ⟨i, h⟩ else false
  let res : BitString n → (ι → Bool) := fun x j => x j.1
  let W : Set (ι → Bool) := {u | ext0 u ∈ AS}
  have hext_res : ∀ x ∈ AS, ext0 (res x) = x := by
    intro x hx
    funext i
    dsimp only [ext0, res]
    split_ifs with hi
    · rfl
    · cases hxi : x i
      · rfl
      · exact absurd ((hAS x hx).1 (mem_supportSet.mpr hxi)) hi
  have hres_ext : ∀ u : ι → Bool, res (ext0 u) = u := by
    intro u
    funext ⟨i, hi⟩
    simp [res, ext0, hi]
  have hcard_true : ∀ u ∈ W, #{j : ι | u j = true} = m := by
    intro u hu
    have hmem : ext0 u ∈ AS := hu
    have hcard : (supportSet (ext0 u)).card = m := (hAS (ext0 u) hmem).2
    rw [← hcard]
    refine Finset.card_bij (fun j _ => j.1) ?_ ?_ ?_
    · intro j hj
      have hj' : u j = true := (mem_filter.mp hj).2
      simp [mem_supportSet, ext0, j.2, hj']
    · intro j₁ _ j₂ _ heq
      exact Subtype.ext heq
    · intro i hi
      have hiS : i ∈ S := (hAS (ext0 u) hmem).1 hi
      refine ⟨⟨i, hiS⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      have hxi : ext0 u i = true := mem_supportSet.mp hi
      simpa [ext0, hiS] using hxi
  have hpi_const : ∀ u ∈ W, (π u).toReal = p ^ m * (1 - p) ^ (s - m) := by
    intro u hu
    rw [Cslib.Probability.PMF.pi_apply, ENNReal.toReal_prod]
    have hterm : ∀ j : ι, (coinP (u j)).toReal = if u j = true then p else 1 - p := fun j =>
      Cslib.Probability.PMF.coin_apply_toReal pI (u j)
    simp_rw [hterm, prod_ite, prod_const]
    have ht : #{j : ι | u j = true} = m := hcard_true u hu
    have hf : #{j : ι | ¬u j = true} = s - m := by
      have htot := card_filter_add_card_filter_not (s := (univ : Finset ι)) (fun j => u j = true)
      rw [card_univ, Fintype.card_coe, ht] at htot
      omega
    rw [ht, hf]
  have hc_pos : 0 < p ^ m * (1 - p) ^ (s - m) := by positivity
  obtain ⟨x₀, hx₀⟩ := hAS_ne
  have hW_ne : ∃ u ∈ W, u ∈ π.support := by
    refine ⟨res x₀, ?_, ?_⟩
    · change ext0 (res x₀) ∈ AS
      rw [hext_res x₀ hx₀]
      exact hx₀
    · rw [PMF.mem_support_iff]
      intro h0
      have htr : (π (res x₀)).toReal = 0 := by simp [h0]
      have hmemW : res x₀ ∈ W := by change ext0 (res x₀) ∈ AS; rwa [hext_res x₀ hx₀]
      rw [hpi_const (res x₀) hmemW] at htr
      linarith
  have hW_card : #{u : ι → Bool | u ∈ W} = AS.card := by
    refine Finset.card_bij (fun u _ => ext0 u)
      (fun u hu => (mem_filter.mp hu).2)
      (fun u₁ _ u₂ _ h => by have := congrArg res h; simpa [hres_ext] using this)
      (fun x hx => ⟨res x, mem_filter.mpr ⟨mem_univ _, by
        change ext0 (res x) ∈ AS; rwa [hext_res x hx]⟩, hext_res x hx⟩)
  have hW_prob : (π.toOuterMeasure W).toReal = (AS.card : ℝ) * (p ^ m * (1 - p) ^ (s - m)) := by
    rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
    calc
      _ = ∑ a ∈ univ.filter (· ∈ W), (π a).toReal := by
          rw [sum_filter]
          exact sum_congr rfl fun a _ => by by_cases ha : a ∈ W <;> simp [ha]
      _ = (AS.card : ℝ) * (p ^ m * (1 - p) ^ (s - m)) := by
          rw [sum_congr rfl fun u hu => hpi_const u (mem_filter.mp hu).2, sum_const, hW_card,
            nsmul_eq_mul]
  have hAS_pos : (0 : ℝ) < AS.card := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨x₀, hx₀⟩)
  have hchoose_pos : (0 : ℝ) < s.choose m := Nat.cast_pos.mpr (Nat.choose_pos hms.le)
  have hW_lower : ((AS.card : ℝ) / (s.choose m : ℝ)) / ((s : ℝ) + 1) ≤
      (π.toOuterMeasure W).toReal := by
    rw [hW_prob]
    have hmode := binomial_mode_lower hm0 hms
    calc
      ((AS.card : ℝ) / (s.choose m : ℝ)) / ((s : ℝ) + 1)
        = (AS.card : ℝ) / (s.choose m : ℝ) * (1 / ((s : ℝ) + 1)) := by ring
      _ ≤ (AS.card : ℝ) / (s.choose m : ℝ) *
            ((s.choose m : ℝ) * p ^ m * (1 - p) ^ (s - m)) := by gcongr
      _ = (AS.card : ℝ) * (p ^ m * (1 - p) ^ (s - m)) := by field_simp
  have hmarg : ∀ j : ι,
      (((π.filter W hW_ne).map fun u => u j) true).toReal =
        (#{x ∈ AS | x j.1 = true} : ℝ) / (AS.card : ℝ) := by
    intro j
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (fun u _ => by
      split_ifs
      · exact PMF.apply_ne_top (π.filter W hW_ne) u
      · exact ENNReal.zero_ne_top)]
    calc
      _ = ∑ u ∈ univ.filter (fun u : ι → Bool => u ∈ W ∧ u j = true), (AS.card : ℝ)⁻¹ := by
          rw [sum_filter]
          refine sum_congr rfl fun u _ => ?_
          by_cases hj : u j = true
          · simp only [hj, ↓reduceIte, Cslib.Probability.PMF.filter_apply_toReal]
            by_cases hu : u ∈ W
            · simp only [hu, and_self, ↓reduceIte, hpi_const u hu, hW_prob]
              field_simp
            · simp [hu]
          · simp [hj, eq_comm]
      _ = (#{x ∈ AS | x j.1 = true} : ℝ) / (AS.card : ℝ) := by
          rw [sum_const, nsmul_eq_mul, div_eq_mul_inv]
          congr 1
          exact_mod_cast (Finset.card_bij (fun u _ => ext0 u)
            (fun u hu => by
              obtain ⟨huW, huj⟩ := (mem_filter.mp hu).2
              exact mem_filter.mpr ⟨huW, by simp [ext0, j.2, huj]⟩)
            (fun u₁ _ u₂ _ h => by have := congrArg res h; simpa [hres_ext] using this)
            (fun x hx => by
              obtain ⟨hxAS, hxj⟩ := mem_filter.mp hx
              refine ⟨res x, mem_filter.mpr ⟨mem_univ _, ?_, hxj⟩, hext_res x hxAS⟩
              change ext0 (res x) ∈ AS
              rwa [hext_res x hxAS]) :
            #{u : ι → Bool | u ∈ W ∧ u j = true} = #{x ∈ AS | x j.1 = true})
  have hraz := Cslib.Probability.PMF.sum_dist_map_filter_pi_le (fun _ : ι => coinP) W hW_ne
  have hsum_eq :
      ∑ i ∈ S, |(#{x ∈ AS | x i = true} : ℝ) / (AS.card : ℝ) - p| =
        ∑ j : ι, dist (((π.filter W hW_ne).map fun u => u j)) coinP := by
    rw [← sum_attach S]
    refine sum_congr rfl fun j _ => ?_
    rw [dist_pmf_bool, hmarg j, Cslib.Probability.PMF.coin_apply_toReal]
    simp [pI]
  rw [hsum_eq]
  refine hraz.trans ?_
  rw [Fintype.card_coe]
  have hprob_pos : 0 < (π.toOuterMeasure W).toReal := by
    rw [hW_prob]; positivity
  have hinv_le : 1 / (π.toOuterMeasure W).toReal ≤
      ((s : ℝ) + 1) / ((AS.card : ℝ) / (s.choose m : ℝ)) := by
    rw [one_div, inv_le_comm₀ hprob_pos (by positivity)]
    simpa [one_div, div_eq_mul_inv] using hW_lower
  gcongr

/-! ### One-side bad-coordinate mass bound -/

/-- The fraction of `m`-subsets of `T` that belong to `A`. -/
@[expose] noncomputable def pSide {n : ℕ} (A : Finset (BitString n)) (T : Finset (Fin n))
    (m : ℕ) : ℝ :=
  (#{x ∈ A | supportSet x ⊆ T ∧ (supportSet x).card = m} : ℝ) / (T.card.choose m : ℝ)

/-- The fraction of `(m - 1)`-subsets `x'` of `T` such that `x' ∪ {i}` belongs to `A`. -/
@[expose] noncomputable def qSide {n : ℕ} (A : Finset (BitString n)) (T : Finset (Fin n))
    (i : Fin n) (m : ℕ) : ℝ :=
  (#{x ∈ A | i ∈ supportSet x ∧ supportSet x ⊆ insert i T ∧ (supportSet x).card = m} : ℝ) /
    (T.card.choose (m - 1) : ℝ)

/-- `pSide` is nonnegative. -/
theorem pSide_nonneg {n : ℕ} (A : Finset (BitString n)) (T : Finset (Fin n)) (m : ℕ) :
    0 ≤ pSide A T m := by
  unfold pSide; positivity

/-- `qSide` is nonnegative. -/
theorem qSide_nonneg {n : ℕ} (A : Finset (BitString n)) (T : Finset (Fin n)) (i : Fin n) (m : ℕ) :
    0 ≤ qSide A T i m := by
  unfold qSide; positivity

/-- `pSide` is at most `1`. -/
theorem pSide_le_one {n : ℕ} (A : Finset (BitString n)) (T : Finset (Fin n)) (m : ℕ) :
    pSide A T m ≤ 1 := by
  unfold pSide
  by_cases h0 : T.card.choose m = 0
  · simp [h0]
  have hpos : (0 : ℝ) < T.card.choose m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
  rw [div_le_one hpos]
  have hcard : #{x ∈ A | supportSet x ⊆ T ∧ (supportSet x).card = m} ≤ T.card.choose m := by
    rw [← card_powersetCard m T]
    refine Finset.card_le_card_of_injOn supportSet ?_ ?_
    · intro x hx
      obtain ⟨_, hsub, hc⟩ := mem_filter.mp hx
      exact mem_powersetCard.mpr ⟨hsub, hc⟩
    · intro x₁ _ x₂ _ h
      rw [← ofFinset_supportSet x₁, ← ofFinset_supportSet x₂, h]
  exact_mod_cast hcard

/-- Average of `pSide A (S.erase i) m` over `i ∈ S` equals `pSide A S m`. -/
theorem avg_pSide_erase {n m : ℕ} (A : Finset (BitString n)) (S : Finset (Fin n))
    (hms : m < S.card) :
    (∑ i ∈ S, pSide A (S.erase i) m) / (S.card : ℝ) = pSide A S m := by
  classical
  set AS := A.filter fun x => supportSet x ⊆ S ∧ (supportSet x).card = m
  have hs0 : (0 : ℝ) < S.card := Nat.cast_pos.mpr (by omega)
  have hchoose_eq : ∀ i ∈ S, (S.erase i).card.choose m = (S.card - 1).choose m := fun i hi => by
    rw [card_erase_of_mem hi]
  have hterm : ∀ i ∈ S,
      #{x ∈ A | supportSet x ⊆ S.erase i ∧ (supportSet x).card = m} =
        #{x ∈ AS | i ∉ supportSet x} := by
    intro i hi
    congr 1
    ext x
    simp only [AS, mem_filter, subset_erase]
    tauto
  have hsum_count : ∑ i ∈ S, #{x ∈ AS | i ∉ supportSet x} = (S.card - m) * AS.card := by
    have hswap_cnt : ∑ i ∈ S, #{x ∈ AS | i ∉ supportSet x} =
        ∑ x ∈ AS, #{i ∈ S | i ∉ supportSet x} := by
      simp_rw [card_eq_sum_ones, sum_filter]
      exact sum_comm
    rw [hswap_cnt]
    have hinner : ∀ x ∈ AS, #{i ∈ S | i ∉ supportSet x} = S.card - m := by
      intro x hx
      obtain ⟨_, hsub, hc⟩ := mem_filter.mp hx
      rw [← sdiff_eq_filter, card_sdiff_of_subset hsub, hc]
    rw [sum_congr rfl hinner, sum_const, smul_eq_mul, mul_comm]
  have hbin : (S.card - m) * S.card.choose m = S.card * (S.card - 1).choose m := by
    have h := Nat.choose_mul_succ_eq (S.card - 1) m
    have h1 : S.card - 1 + 1 = S.card := by omega
    rw [h1] at h
    linarith
  have hpos1 : (0 : ℝ) < (S.card - 1).choose m := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hpos2 : (0 : ℝ) < S.card.choose m := Nat.cast_pos.mpr (Nat.choose_pos hms.le)
  have hbinR : ((S.card - m : ℕ) : ℝ) * (S.card.choose m : ℝ) =
      (S.card : ℝ) * ((S.card - 1).choose m : ℝ) := by exact_mod_cast hbin
  unfold pSide
  rw [sum_congr rfl fun i hi => by rw [hterm i hi, hchoose_eq i hi], ← sum_div]
  have hcast : (∑ i ∈ S, (#{x ∈ AS | i ∉ supportSet x} : ℝ)) =
      ((S.card - m : ℕ) : ℝ) * (AS.card : ℝ) := by exact_mod_cast hsum_count
  rw [hcast]
  change (((S.card - m : ℕ) : ℝ) * (AS.card : ℝ) / ((S.card - 1).choose m : ℝ)) / (S.card : ℝ) =
    (AS.card : ℝ) / (S.card.choose m : ℝ)
  field_simp
  calc
    ((S.card - m : ℕ) : ℝ) * (AS.card : ℝ) * (S.card.choose m : ℝ)
      = ((S.card - m : ℕ) : ℝ) * (S.card.choose m : ℝ) * (AS.card : ℝ) := by ring
    _ = (S.card : ℝ) * ((S.card - 1).choose m : ℝ) * (AS.card : ℝ) := by rw [hbinR]
    _ = (AS.card : ℝ) * ((S.card - 1).choose m : ℝ) * (S.card : ℝ) := by ring

/-- Exact difference identity between `pSide A (S.erase i) m` and `qSide A (S.erase i) i m`. -/
private theorem pSide_sub_qSide {n m : ℕ} (A : Finset (BitString n)) (S : Finset (Fin n))
    (hm0 : 0 < m) (hms : m < S.card) {i : Fin n} (hi : i ∈ S) :
    let AS := A.filter fun x => supportSet x ⊆ S ∧ (supportSet x).card = m
    let p : ℝ := (m : ℝ) / (S.card : ℝ)
    pSide A (S.erase i) m - qSide A (S.erase i) i m =
      if AS.card = 0 then 0 else
        pSide A S m * (p - (#{x ∈ AS | x i = true} : ℝ) / (AS.card : ℝ)) / (p * (1 - p)) := by
  classical
  dsimp only
  set AS := A.filter fun x => supportSet x ⊆ S ∧ (supportSet x).card = m
  set s := S.card
  set p : ℝ := (m : ℝ) / (s : ℝ)
  have herase : (S.erase i).card = s - 1 := card_erase_of_mem hi
  have h1 : #{x ∈ A | supportSet x ⊆ S.erase i ∧ (supportSet x).card = m} =
      #{x ∈ AS | x i ≠ true} := by
    congr 1; ext x; simp only [AS, mem_filter, subset_erase, mem_supportSet]; tauto
  have h2 : #{x ∈ A | i ∈ supportSet x ∧ supportSet x ⊆ insert i (S.erase i) ∧
      (supportSet x).card = m} = #{x ∈ AS | x i = true} := by
    rw [insert_erase hi]
    congr 1; ext x; simp only [AS, mem_filter, mem_supportSet]; tauto
  by_cases hAS0 : AS.card = 0
  · have hAS_empty : AS = ∅ := card_eq_zero.mp hAS0
    simp only [pSide, qSide, h1, h2, hAS_empty, filter_empty, card_empty, Nat.cast_zero, zero_div,
      sub_self, ↓reduceIte]
  · simp only [hAS0, ↓reduceIte]
    have hsplit : #{x ∈ AS | x i = true} + #{x ∈ AS | x i ≠ true} = AS.card :=
      card_filter_add_card_filter_not _
    have hsplitR : (#{x ∈ AS | x i ≠ true} : ℝ) = (AS.card : ℝ) - (#{x ∈ AS | x i = true} : ℝ) := by
      have : (#{x ∈ AS | x i = true} : ℝ) + (#{x ∈ AS | x i ≠ true} : ℝ) = (AS.card : ℝ) := by
        exact_mod_cast hsplit
      linarith
    have hbin1 : ((s - 1).choose m : ℝ) = (1 - p) * (s.choose m : ℝ) := by
      have hs0 : (0 : ℝ) < s := Nat.cast_pos.mpr (by omega)
      have h1p : 1 - p = ((s - m : ℕ) : ℝ) / (s : ℝ) := by
        dsimp only [p]; rw [Nat.cast_sub hms.le]; field_simp
      have hnat : (s - m) * s.choose m = s * (s - 1).choose m := by
        have h := Nat.choose_mul_succ_eq (s - 1) m
        rw [show s - 1 + 1 = s by omega] at h; linarith
      have hR : ((s - m : ℕ) : ℝ) * (s.choose m : ℝ) = (s : ℝ) * ((s - 1).choose m : ℝ) := by
        exact_mod_cast hnat
      rw [h1p]; field_simp; linarith
    have hbin2 : ((s - 1).choose (m - 1) : ℝ) = p * (s.choose m : ℝ) := by
      have hs0 : (0 : ℝ) < s := Nat.cast_pos.mpr (by omega)
      have hnat : m * s.choose m = s * (s - 1).choose (m - 1) := by
        have h := Nat.add_one_mul_choose_eq (s - 1) (m - 1)
        rw [show s - 1 + 1 = s by omega, show m - 1 + 1 = m by omega] at h
        linarith
      have hR : (m : ℝ) * (s.choose m : ℝ) = (s : ℝ) * ((s - 1).choose (m - 1) : ℝ) := by
        exact_mod_cast hnat
      dsimp only [p]; field_simp; linarith
    have hs0 : (0 : ℝ) < s := Nat.cast_pos.mpr (by omega)
    have hp0 : 0 < p := div_pos (by exact_mod_cast hm0) hs0
    have h1p0 : 0 < 1 - p := by rw [sub_pos]; exact (div_lt_one hs0).mpr (by exact_mod_cast hms)
    have hch0 : (0 : ℝ) < s.choose m := Nat.cast_pos.mpr (Nat.choose_pos hms.le)
    have hASpos : (0 : ℝ) < AS.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hAS0)
    unfold pSide qSide
    rw [h1, h2, herase, hsplitR, hbin1, hbin2]
    change ((AS.card : ℝ) - (#{x ∈ AS | x i = true} : ℝ)) / ((1 - p) * (s.choose m : ℝ)) -
        (#{x ∈ AS | x i = true} : ℝ) / (p * (s.choose m : ℝ)) =
      ((AS.card : ℝ) / (s.choose m : ℝ)) *
        (p - (#{x ∈ AS | x i = true} : ℝ) / (AS.card : ℝ)) / (p * (1 - p))
    field_simp
    ring

/-- One-side bad-coordinate mass bound: for fixed `S` of size `s`, `0 < m < s`, `ε > 0`, and
`0 < τ ≤ 1`, the average of `pSide A (S.erase i) m` over `i ∈ S` with
`qSide A (S.erase i) i m < (1 - ε) * pSide A (S.erase i) m` is at most
`(1 / (ε * p * (1 - p)) * √(ln((s + 1) / τ) / s)) * pSide A S m + τ`. -/
theorem bad_coord_mass_bound {n m : ℕ} (A : Finset (BitString n)) (S : Finset (Fin n))
    (hm0 : 0 < m) (hms : m < S.card) {ε τ : ℝ} (hε : 0 < ε) (hτ0 : 0 < τ) :
    let p : ℝ := (m : ℝ) / (S.card : ℝ)
    (∑ i ∈ S with qSide A (S.erase i) i m < (1 - ε) * pSide A (S.erase i) m,
        pSide A (S.erase i) m) / (S.card : ℝ) ≤
      (1 / (ε * p * (1 - p)) * Real.sqrt (Real.log (((S.card : ℝ) + 1) / τ) / (S.card : ℝ))) *
        pSide A S m + τ := by
  classical
  dsimp only
  set s := S.card
  set p : ℝ := (m : ℝ) / (s : ℝ)
  set α : ℝ := pSide A S m
  have hs0 : (0 : ℝ) < s := Nat.cast_pos.mpr (by omega)
  have hp0 : 0 < p := div_pos (by exact_mod_cast hm0) hs0
  have h1p0 : 0 < 1 - p := by rw [sub_pos]; exact (div_lt_one hs0).mpr (by exact_mod_cast hms)
  have hα0 : 0 ≤ α := pSide_nonneg A S m
  have hcoeff0 : 0 ≤ 1 / (ε * p * (1 - p)) *
      Real.sqrt (Real.log (((s : ℝ) + 1) / τ) / (s : ℝ)) := by positivity
  by_cases hατ : α < τ
  · have hle_avg : (∑ i ∈ S with qSide A (S.erase i) i m < (1 - ε) * pSide A (S.erase i) m,
        pSide A (S.erase i) m) / (s : ℝ) ≤ α := by
      dsimp only [α]
      rw [← avg_pSide_erase A S hms]
      gcongr
      · exact fun i _ _ => pSide_nonneg A _ m
      · exact filter_subset _ S
    nlinarith
  · push Not at hατ
    set AS := A.filter fun x => supportSet x ⊆ S ∧ (supportSet x).card = m
    have hα_pos : 0 < α := hτ0.trans_le hατ
    have hAS_ne : AS.Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      have h0 : α = 0 := by simp [α, pSide, AS, hne]
      linarith
    have hAS_card_ne : AS.card ≠ 0 := (Finset.card_pos.mpr hAS_ne).ne'
    have hpt : ∀ i ∈ S.filter (fun i => qSide A (S.erase i) i m < (1 - ε) * pSide A (S.erase i) m),
        pSide A (S.erase i) m ≤
          α / (ε * p * (1 - p)) *
            |(#{x ∈ AS | x i = true} : ℝ) / (AS.card : ℝ) - p| := by
      intro i hi
      obtain ⟨hiS, hbad⟩ := mem_filter.mp hi
      have hdiff := pSide_sub_qSide A S hm0 hms hiS
      dsimp only at hdiff
      change pSide A (S.erase i) m - qSide A (S.erase i) i m =
        if AS.card = 0 then 0 else
          α * (p - (#{x ∈ AS | x i = true} : ℝ) / (AS.card : ℝ)) / (p * (1 - p)) at hdiff
      simp only [hAS_card_ne, ↓reduceIte] at hdiff
      have hεp : ε * pSide A (S.erase i) m ≤ pSide A (S.erase i) m - qSide A (S.erase i) i m := by
        linarith
      have hle_abs : pSide A (S.erase i) m - qSide A (S.erase i) i m ≤
          α / (p * (1 - p)) * |(#{x ∈ AS | x i = true} : ℝ) / (AS.card : ℝ) - p| := by
        rw [hdiff, abs_sub_comm]
        have : α * (p - (#{x ∈ AS | x i = true} : ℝ) / (AS.card : ℝ)) / (p * (1 - p)) =
            α / (p * (1 - p)) * (p - (#{x ∈ AS | x i = true} : ℝ) / (AS.card : ℝ)) := by ring
        rw [this]
        have hnn : (0 : ℝ) ≤ α / (p * (1 - p)) := by positivity
        exact mul_le_mul_of_nonneg_left (le_abs_self _) hnn
      have h1 : ε * pSide A (S.erase i) m ≤
          α / (p * (1 - p)) * |(#{x ∈ AS | x i = true} : ℝ) / (AS.card : ℝ) - p| :=
        hεp.trans hle_abs
      rw [show α / (ε * p * (1 - p)) *
          |(#{x ∈ AS | x i = true} : ℝ) / (AS.card : ℝ) - p| =
          (α / (p * (1 - p)) * |(#{x ∈ AS | x i = true} : ℝ) / (AS.card : ℝ) - p|) / ε by
        field_simp]
      exact (le_div_iff₀ hε).mpr (by linarith)
    have hsum1 : (∑ i ∈ S with qSide A (S.erase i) i m < (1 - ε) * pSide A (S.erase i) m,
        pSide A (S.erase i) m) ≤
        α / (ε * p * (1 - p)) *
          ∑ i ∈ S, |(#{x ∈ AS | x i = true} : ℝ) / (AS.card : ℝ) - p| := by
      calc
        (∑ i ∈ S with qSide A (S.erase i) i m < (1 - ε) * pSide A (S.erase i) m,
            pSide A (S.erase i) m)
          ≤ ∑ i ∈ S with qSide A (S.erase i) i m < (1 - ε) * pSide A (S.erase i) m,
              α / (ε * p * (1 - p)) *
                |(#{x ∈ AS | x i = true} : ℝ) / (AS.card : ℝ) - p| := sum_le_sum hpt
        _ = α / (ε * p * (1 - p)) *
              ∑ i ∈ S with qSide A (S.erase i) i m < (1 - ε) * pSide A (S.erase i) m,
                |(#{x ∈ AS | x i = true} : ℝ) / (AS.card : ℝ) - p| := by rw [← mul_sum]
        _ ≤ α / (ε * p * (1 - p)) *
              ∑ i ∈ S, |(#{x ∈ AS | x i = true} : ℝ) / (AS.card : ℝ) - p| := by
            gcongr
            exact filter_subset _ S
    have hdev := sum_abs_marginal_sub_le S hm0 hms AS hAS_ne (fun x hx => (mem_filter.mp hx).2)
    have hlog_le : Real.log (((s : ℝ) + 1) / α) ≤ Real.log (((s : ℝ) + 1) / τ) := by
      apply Real.log_le_log (by positivity)
      gcongr
    have hsqrt_le : Real.sqrt ((s : ℝ) * Real.log (((s : ℝ) + 1) / α)) / (s : ℝ) ≤
        Real.sqrt (Real.log (((s : ℝ) + 1) / τ) / (s : ℝ)) := by
      have hsq : Real.sqrt ((s : ℝ) * Real.log (((s : ℝ) + 1) / α)) / (s : ℝ) =
          Real.sqrt (Real.log (((s : ℝ) + 1) / α) / (s : ℝ)) := by
        have h1 : 1 ≤ ((s : ℝ) + 1) / α := by
          rw [one_le_div hα_pos]
          linarith [pSide_le_one A S m]
        have hlog_nn : 0 ≤ Real.log (((s : ℝ) + 1) / α) := Real.log_nonneg h1
        have hdiv_sq : Real.sqrt ((s : ℝ) ^ 2) = (s : ℝ) := Real.sqrt_sq hs0.le
        calc
          Real.sqrt ((s : ℝ) * Real.log (((s : ℝ) + 1) / α)) / (s : ℝ)
            = Real.sqrt ((s : ℝ) * Real.log (((s : ℝ) + 1) / α)) / Real.sqrt ((s : ℝ) ^ 2) := by
              rw [hdiv_sq]
          _ = Real.sqrt (((s : ℝ) * Real.log (((s : ℝ) + 1) / α)) / (s : ℝ) ^ 2) :=
              (Real.sqrt_div (mul_nonneg hs0.le hlog_nn) _).symm
          _ = Real.sqrt (Real.log (((s : ℝ) + 1) / α) / (s : ℝ)) := by
              congr 1; field_simp
      rw [hsq]
      gcongr
    have hfinal : (∑ i ∈ S with qSide A (S.erase i) i m < (1 - ε) * pSide A (S.erase i) m,
        pSide A (S.erase i) m) / (s : ℝ) ≤
        (1 / (ε * p * (1 - p)) * Real.sqrt (Real.log (((s : ℝ) + 1) / τ) / (s : ℝ))) * α := by
      calc
        (∑ i ∈ S with qSide A (S.erase i) i m < (1 - ε) * pSide A (S.erase i) m,
            pSide A (S.erase i) m) / (s : ℝ)
          ≤ (α / (ε * p * (1 - p)) *
              Real.sqrt ((s : ℝ) * Real.log (((s : ℝ) + 1) / α))) / (s : ℝ) := by
            gcongr
            exact hsum1.trans (mul_le_mul_of_nonneg_left hdev (by positivity))
        _ = (1 / (ε * p * (1 - p)) *
              (Real.sqrt ((s : ℝ) * Real.log (((s : ℝ) + 1) / α)) / (s : ℝ))) * α := by ring
        _ ≤ (1 / (ε * p * (1 - p)) *
              Real.sqrt (Real.log (((s : ℝ) + 1) / τ) / (s : ℝ))) * α := by gcongr
    linarith

/-! ### Balanced ordered splits of `Fin n` and exact sampling of `μ_{0,n,m}` and `μ_{1,n,m}` -/

/-- An ordered partition `⟨point, left, right⟩` of `Fin n` into a single point `point` and two
disjoint sets `left` and `right` of sizes `(n - 1) / 2` and `n / 2`. -/
@[ext] structure OrderedSplit (n : ℕ) where
  /-- The distinguished shared coordinate `i ∈ Fin n`. -/
  point : Fin n
  /-- The left coordinate block `Tx` of size `(n - 1) / 2`. -/
  left : Finset (Fin n)
  /-- The right coordinate block `Ty` of size `n / 2`. -/
  right : Finset (Fin n)
  deriving DecidableEq

/-- Equivalence between `OrderedSplit n` and triples `(point, left, right)`. -/
def OrderedSplit.equivTuple (n : ℕ) :
    OrderedSplit n ≃ Fin n × Finset (Fin n) × Finset (Fin n) where
  toFun T := (T.point, T.left, T.right)
  invFun | (p, l, r) => ⟨p, l, r⟩
  left_inv _ := rfl
  right_inv | (_, _, _) => rfl

/-- Fintype instance on `OrderedSplit n`. -/
instance instFintypeOrderedSplit (n : ℕ) : Fintype (OrderedSplit n) :=
  Fintype.ofEquiv _ (OrderedSplit.equivTuple n).symm

/-- All balanced ordered splits of `Fin n` with `|left| = (n - 1) / 2` and `|right| = n / 2`. -/
@[expose] def splits (n : ℕ) : Finset (OrderedSplit n) :=
  univ.filter fun T =>
    T.point ∉ T.left ∧ T.point ∉ T.right ∧ Disjoint T.left T.right ∧
      T.left.card = (n - 1) / 2 ∧ T.right.card = n / 2

private theorem mem_splits {n : ℕ} {T : OrderedSplit n} :
    T ∈ splits n ↔ T.point ∉ T.left ∧ T.point ∉ T.right ∧ Disjoint T.left T.right ∧
      T.left.card = (n - 1) / 2 ∧ T.right.card = n / 2 := by
  simp [splits]

private theorem left_eq_compl_insert_right {n : ℕ} (hn : 1 ≤ n) {T : OrderedSplit n}
    (hT : T ∈ splits n) : T.left = (insert T.point T.right)ᶜ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mem_splits.mp hT
  refine eq_of_subset_of_card_le (fun a ha => ?_) ?_
  · rw [mem_compl, mem_insert, not_or]
    exact ⟨fun h => h1 (h ▸ ha), fun h => disjoint_left.mp h3 ha h⟩
  · rw [card_compl, Fintype.card_fin, card_insert_of_notMem h2, h4, h5]
    omega

private theorem right_eq_compl_insert_left {n : ℕ} (hn : 1 ≤ n) {T : OrderedSplit n}
    (hT : T ∈ splits n) : T.right = (insert T.point T.left)ᶜ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mem_splits.mp hT
  refine eq_of_subset_of_card_le (fun a ha => ?_) ?_
  · rw [mem_compl, mem_insert, not_or]
    exact ⟨fun h => h2 (h ▸ ha), fun h => disjoint_right.mp h3 ha h⟩
  · rw [card_compl, Fintype.card_fin, card_insert_of_notMem h1, h4, h5]
    omega

/-- Summing over `splits n` by first choosing `right` (of size `n / 2`) and then `point ∈ rightᶜ`.
-/
theorem sum_splits_right {n : ℕ} (hn : 1 ≤ n) {M : Type*} [AddCommMonoid M]
    (F : OrderedSplit n → M) :
    ∑ T ∈ splits n, F T =
      ∑ Ty ∈ (univ : Finset (Fin n)).powersetCard (n / 2),
        ∑ i ∈ Tyᶜ, F ⟨i, Tyᶜ.erase i, Ty⟩ := by
  rw [sum_sigma']
  refine sum_nbij' (fun T => ⟨T.right, T.point⟩) (fun x => ⟨x.2, x.1ᶜ.erase x.2, x.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro T hT
    obtain ⟨_, h2, _, _, h5⟩ := mem_splits.mp hT
    exact mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, h5⟩, mem_compl.mpr h2⟩
  · rintro ⟨Ty, i⟩ hx
    obtain ⟨hTy, hi⟩ := mem_sigma.mp hx
    have hTyc : Ty.card = n / 2 := (mem_powersetCard.mp hTy).2
    have hi' : i ∉ Ty := mem_compl.mp hi
    refine mem_splits.mpr ⟨notMem_erase _ _, hi', ?_, ?_, hTyc⟩
    · exact disjoint_left.mpr fun a ha => mem_compl.mp (mem_of_mem_erase ha)
    · rw [card_erase_of_mem hi, card_compl, Fintype.card_fin, hTyc]; omega
  · intro T hT
    have hl : T.left = T.rightᶜ.erase T.point := by
      rw [left_eq_compl_insert_right hn hT]
      ext a; simp
    ext <;> simp [hl]
  · intro ⟨Ty, i⟩ _
    rfl
  · intro T hT
    have hl : T.left = T.rightᶜ.erase T.point := by
      rw [left_eq_compl_insert_right hn hT]
      ext a; simp
    congr 1
    ext <;> simp [hl]

/-- Summing over `splits n` by first choosing `left` (of size `(n - 1) / 2`) and then
`point ∈ leftᶜ`. -/
theorem sum_splits_left {n : ℕ} (hn : 1 ≤ n) {M : Type*} [AddCommMonoid M]
    (F : OrderedSplit n → M) :
    ∑ T ∈ splits n, F T =
      ∑ Tx ∈ (univ : Finset (Fin n)).powersetCard ((n - 1) / 2),
        ∑ i ∈ Txᶜ, F ⟨i, Tx, Txᶜ.erase i⟩ := by
  rw [sum_sigma']
  refine sum_nbij' (fun T => ⟨T.left, T.point⟩) (fun x => ⟨x.2, x.1, x.1ᶜ.erase x.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro T hT
    obtain ⟨h1, _, _, h4, _⟩ := mem_splits.mp hT
    exact mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, h4⟩, mem_compl.mpr h1⟩
  · rintro ⟨Tx, i⟩ hx
    obtain ⟨hTx, hi⟩ := mem_sigma.mp hx
    have hTxc : Tx.card = (n - 1) / 2 := (mem_powersetCard.mp hTx).2
    have hi' : i ∉ Tx := mem_compl.mp hi
    refine mem_splits.mpr ⟨hi', notMem_erase _ _, ?_, hTxc, ?_⟩
    · exact disjoint_right.mpr fun a ha => mem_compl.mp (mem_of_mem_erase ha)
    · rw [card_erase_of_mem hi, card_compl, Fintype.card_fin, hTxc]; omega
  · intro T hT
    have hr : T.right = T.leftᶜ.erase T.point := by
      rw [right_eq_compl_insert_left hn hT]
      ext a; simp
    ext <;> simp [hr]
  · intro ⟨Tx, i⟩ _
    rfl
  · intro T hT
    have hr : T.right = T.leftᶜ.erase T.point := by
      rw [right_eq_compl_insert_left hn hT]
      ext a; simp
    congr 1
    ext <;> simp [hr]

/-- Cardinality formula for `splits n`. -/
theorem card_splits {n : ℕ} (hn : 1 ≤ n) :
    (splits n).card = n.choose (n / 2) * ((n - 1) / 2 + 1) := by
  rw [card_eq_sum_ones, sum_splits_right hn]
  simp only [sum_const, smul_eq_mul, mul_one]
  rw [sum_congr rfl fun Ty hTy => by
      rw [card_compl, Fintype.card_fin, (mem_powersetCard.mp hTy).2],
    sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
  congr 1; omega

/-- `splits n` has positive cardinality for `n ≥ 1`. -/
theorem card_splits_pos {n : ℕ} (hn : 1 ≤ n) : 0 < (splits n).card := by
  rw [card_splits hn]
  exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.succ_pos _)

private theorem card_splits_mul_factorials {n : ℕ} (hn : 1 ≤ n) :
    (splits n).card * ((n - 1) / 2).factorial * (n / 2).factorial = n.factorial := by
  rw [card_splits hn]
  have h1 := Nat.choose_mul_factorial_mul_factorial (show n / 2 ≤ n by omega)
  have hsub : n - n / 2 = (n - 1) / 2 + 1 := by omega
  rw [hsub, Nat.factorial_succ] at h1
  linarith

/-- Exact sampling formula for `μ_{0,n,m}(A × B)` over balanced ordered splits. -/
theorem muRect_zero_eq_avg_splits {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ (n - 1) / 2)
    (A B : Finset (BitString n)) :
    muRect 0 n m A B =
      (∑ T ∈ splits n, pSide A T.left m * pSide B T.right m) / ((splits n).card : ℝ) := by
  classical
  set k₁ := (n - 1) / 2
  set k₂ := n / 2
  have hk2 : m ≤ k₂ := by omega
  have h2m : 2 * m ≤ n := by omega
  have hcard_l : ∀ T ∈ splits n, T.left.card = k₁ := fun T hT => (mem_splits.mp hT).2.2.2.1
  have hcard_r : ∀ T ∈ splits n, T.right.card = k₂ := fun T hT => (mem_splits.mp hT).2.2.2.2
  -- Rewrite the RHS as a double sum over `x ∈ A, y ∈ B` of the number of compatible splits.
  have hswap : (∑ T ∈ splits n, pSide A T.left m * pSide B T.right m) / ((splits n).card : ℝ) =
      ∑ x ∈ A, ∑ y ∈ B,
        (#{T ∈ splits n | (supportSet x ⊆ T.left ∧ (supportSet x).card = m) ∧
            (supportSet y ⊆ T.right ∧ (supportSet y).card = m)} : ℝ) /
          (((splits n).card : ℝ) * (k₁.choose m : ℝ) * (k₂.choose m : ℝ)) := by
    have hpt : ∀ T ∈ splits n,
        pSide A T.left m * pSide B T.right m =
          (∑ x ∈ A, ∑ y ∈ B,
            if (supportSet x ⊆ T.left ∧ (supportSet x).card = m) ∧
                (supportSet y ⊆ T.right ∧ (supportSet y).card = m) then (1 : ℝ) else 0) /
            ((k₁.choose m : ℝ) * (k₂.choose m : ℝ)) := by
      intro T hT
      unfold pSide
      rw [hcard_l T hT, hcard_r T hT, div_mul_div_comm]
      congr 1
      rw [← sum_boole, ← sum_boole, sum_mul_sum]
      refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
      split_ifs <;> simp_all
    rw [sum_congr rfl hpt, ← sum_div, div_div, mul_comm ((k₁.choose m : ℝ) * (k₂.choose m : ℝ)),
      ← mul_assoc]
    rw [sum_comm (s := splits n) (t := A)]
    rw [sum_congr rfl fun x _ => sum_comm (s := splits n) (t := B)]
    rw [sum_div]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun y _ => ?_
    congr 1
    rw [sum_boole]
  rw [hswap, muRect_eq_sum]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  by_cases hmem : (x, y) ∈ weightPairs 0 n m
  · obtain ⟨hx, hy, hxy⟩ := mem_weightPairs.mp hmem
    have hdisj : Disjoint (supportSet x) (supportSet y) := by
      rw [disjoint_iff_inter_eq_empty, ← interSet_eq_inter, ← card_eq_zero]
      exact hxy
    -- Count splits `T` with `supportSet x ⊆ T.left` and `supportSet y ⊆ T.right`.
    have hcount : #{T ∈ splits n | (supportSet x ⊆ T.left ∧ (supportSet x).card = m) ∧
        (supportSet y ⊆ T.right ∧ (supportSet y).card = m)} =
        (n - 2 * m).choose (k₁ - m) * (k₂ - m + 1) := by
      set U := (supportSet x ∪ supportSet y)ᶜ
      have hU : U.card = n - 2 * m := by
        rw [card_compl, Fintype.card_fin, card_union_of_disjoint hdisj, hx, hy]; omega
      have hbij : #{T ∈ splits n | (supportSet x ⊆ T.left ∧ (supportSet x).card = m) ∧
          (supportSet y ⊆ T.right ∧ (supportSet y).card = m)} =
          (U.powersetCard (k₁ - m)).sum fun L => (U \ L).card := by
        rw [← card_sigma]
        refine Finset.card_bij (fun T _ => ⟨T.left \ supportSet x, T.point⟩) ?_ ?_ ?_
        · intro T hT
          obtain ⟨hTs, ⟨hxL, _⟩, ⟨hyR, _⟩⟩ := mem_filter.mp hT
          obtain ⟨hpL, hpR, hLR, hLc, _⟩ := mem_splits.mp hTs
          refine mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
          · intro a ha
            obtain ⟨haL, hax⟩ := mem_sdiff.mp ha
            rw [mem_compl, mem_union, not_or]
            exact ⟨hax, fun hay => disjoint_left.mp hLR haL (hyR hay)⟩
          · rw [card_sdiff_of_subset hxL, hLc, hx]
          · rw [mem_sdiff, mem_compl, mem_union, not_or]
            exact ⟨⟨fun hpx => hpL (hxL hpx), fun hpy => hpR (hyR hpy)⟩,
              fun hp => hpL (mem_sdiff.mp hp).1⟩
        · intro T₁ hT₁ T₂ hT₂ heq
          obtain ⟨hT₁s, ⟨hxL₁, _⟩, _⟩ := mem_filter.mp hT₁
          obtain ⟨hT₂s, ⟨hxL₂, _⟩, _⟩ := mem_filter.mp hT₂
          have hLdiff : T₁.left \ supportSet x = T₂.left \ supportSet x :=
            congrArg Sigma.fst heq
          have hp : T₁.point = T₂.point := congrArg Sigma.snd heq
          have hL : T₁.left = T₂.left := by
            rw [← sdiff_union_of_subset hxL₁, ← sdiff_union_of_subset hxL₂, hLdiff]
          have hR : T₁.right = T₂.right := by
            rw [right_eq_compl_insert_left hn hT₁s, right_eq_compl_insert_left hn hT₂s, hp, hL]
          exact OrderedSplit.ext hp hL hR
        · rintro ⟨L, i⟩ hmem'
          obtain ⟨hL, hi⟩ := mem_sigma.mp hmem'
          obtain ⟨hLU, hLc⟩ := mem_powersetCard.mp hL
          obtain ⟨hiU, hiL⟩ := mem_sdiff.mp hi
          have hdisjLx : Disjoint L (supportSet x) := disjoint_left.mpr fun a haL hax =>
            (mem_compl.mp (hLU haL)) (mem_union_left _ hax)
          have hdisjLy : Disjoint L (supportSet y) := disjoint_left.mpr fun a haL hay =>
            (mem_compl.mp (hLU haL)) (mem_union_right _ hay)
          have hix : i ∉ supportSet x := fun h => (mem_compl.mp hiU) (mem_union_left _ h)
          have hiy : i ∉ supportSet y := fun h => (mem_compl.mp hiU) (mem_union_right _ h)
          let Tl := L ∪ supportSet x
          let Tr := (insert i Tl)ᶜ
          have hTlc : Tl.card = k₁ := by
            rw [card_union_of_disjoint hdisjLx, hLc, hx]; omega
          have hiTl : i ∉ Tl := by simp [Tl, hiL, hix]
          have hTrc : Tr.card = k₂ := by
            rw [card_compl, Fintype.card_fin, card_insert_of_notMem hiTl, hTlc]; omega
          refine ⟨⟨i, Tl, Tr⟩, mem_filter.mpr ⟨mem_splits.mpr ⟨hiTl, ?_, ?_, hTlc, hTrc⟩,
            ⟨subset_union_right, hx⟩, ⟨?_, hy⟩⟩, ?_⟩
          · simp [Tr]
          · exact disjoint_right.mpr fun a ha => fun haTl =>
              (mem_compl.mp ha) (mem_insert_of_mem haTl)
          · intro a hay
            rw [mem_compl, mem_insert, not_or]
            refine ⟨fun hai => hiy (hai ▸ hay), fun haTl => ?_⟩
            rcases mem_union.mp haTl with haL | hax
            · exact disjoint_left.mp hdisjLy haL hay
            · exact disjoint_left.mp hdisj hax hay
          · refine Sigma.ext ?_ (heq_of_eq rfl)
            simp [Tl, sdiff_eq_self_of_disjoint hdisjLx]
      rw [hbij]
      have hinner : ∀ L ∈ U.powersetCard (k₁ - m), (U \ L).card = k₂ - m + 1 := by
        intro L hL
        obtain ⟨hLU, hLc⟩ := mem_powersetCard.mp hL
        rw [card_sdiff_of_subset hLU, hU, hLc]
        omega
      rw [sum_congr rfl hinner, sum_const, card_powersetCard, hU, smul_eq_mul]
    rw [muWeight_of_mem hmem, hcount]
    have hpos_wc : (0 : ℝ) < weightCard 0 n m :=
      Nat.cast_pos.mpr (weightCard_pos_iff.mpr ⟨Nat.zero_le _, by omega⟩)
    have hpos_sp : (0 : ℝ) < (splits n).card := Nat.cast_pos.mpr (card_splits_pos hn)
    have hpos_c1 : (0 : ℝ) < k₁.choose m := Nat.cast_pos.mpr (Nat.choose_pos hm)
    have hpos_c2 : (0 : ℝ) < k₂.choose m := Nat.cast_pos.mpr (Nat.choose_pos hk2)
    have hnat : (n - 2 * m).choose (k₁ - m) * (k₂ - m + 1) * weightCard 0 n m =
        (splits n).card * k₁.choose m * k₂.choose m := by
      have h1 := weightCard_mul_factorials (k := 0) (n := n) (m := m) (Nat.zero_le _) (by omega)
      simp only [Nat.factorial_zero, Nat.sub_zero, Nat.add_zero, one_mul] at h1
      have h2 := card_splits_mul_factorials hn
      have hc1 := Nat.choose_mul_factorial_mul_factorial hm
      have hc2 := Nat.choose_mul_factorial_mul_factorial hk2
      have hc3 := Nat.choose_mul_factorial_mul_factorial (show k₁ - m ≤ n - 2 * m by omega)
      have hsub : n - 2 * m - (k₁ - m) = k₂ - m + 1 := by omega
      rw [hsub, Nat.factorial_succ] at hc3
      have hmul : ((n - 2 * m).choose (k₁ - m) * (k₂ - m + 1) * weightCard 0 n m) *
          ((k₁ - m).factorial * (k₂ - m).factorial * m.factorial * m.factorial *
            (n - 2 * m).factorial) =
          ((splits n).card * k₁.choose m * k₂.choose m) *
          ((k₁ - m).factorial * (k₂ - m).factorial * m.factorial * m.factorial *
            (n - 2 * m).factorial) := by
        calc
          ((n - 2 * m).choose (k₁ - m) * (k₂ - m + 1) * weightCard 0 n m) *
              ((k₁ - m).factorial * (k₂ - m).factorial * m.factorial * m.factorial *
                (n - 2 * m).factorial)
            = ((n - 2 * m).choose (k₁ - m) * (k₁ - m).factorial *
                ((k₂ - m + 1) * (k₂ - m).factorial)) *
              (weightCard 0 n m * (m.factorial * m.factorial * (n - 2 * m).factorial)) := by ring
          _ = (n - 2 * m).factorial * n.factorial := by rw [hc3, h1]
          _ = (n - 2 * m).factorial * ((splits n).card * k₁.factorial * k₂.factorial) := by
              rw [h2]
          _ = (n - 2 * m).factorial * ((splits n).card *
                (k₁.choose m * m.factorial * (k₁ - m).factorial) *
                (k₂.choose m * m.factorial * (k₂ - m).factorial)) := by rw [hc1, hc2]
          _ = ((splits n).card * k₁.choose m * k₂.choose m) *
              ((k₁ - m).factorial * (k₂ - m).factorial * m.factorial * m.factorial *
                (n - 2 * m).factorial) := by ring
      have hfac_pos : 0 < (k₁ - m).factorial * (k₂ - m).factorial * m.factorial * m.factorial *
          (n - 2 * m).factorial := by positivity
      exact Nat.eq_of_mul_eq_mul_right hfac_pos hmul
    have hR : ((n - 2 * m).choose (k₁ - m) : ℝ) * (((k₂ - m + 1 : ℕ) : ℝ)) *
        (weightCard 0 n m : ℝ) =
        ((splits n).card : ℝ) * (k₁.choose m : ℝ) * (k₂.choose m : ℝ) := by exact_mod_cast hnat
    field_simp
    push_cast at hR ⊢
    linarith
  · rw [muWeight_eq_zero_of_notMem hmem]
    have hzero : #{T ∈ splits n | (supportSet x ⊆ T.left ∧ (supportSet x).card = m) ∧
        (supportSet y ⊆ T.right ∧ (supportSet y).card = m)} = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      intro T hTs hcond
      obtain ⟨⟨hxL, hxc⟩, ⟨hyR, hyc⟩⟩ := hcond
      have hLR := (mem_splits.mp hTs).2.2.1
      have hdisj : Disjoint (supportSet x) (supportSet y) := hLR.mono hxL hyR
      have hxy : (interSet x y).card = 0 := by
        rw [interSet_eq_inter, Finset.disjoint_iff_inter_eq_empty.mp hdisj, card_empty]
      exact hmem (mem_weightPairs.mpr ⟨hxc, hyc, hxy⟩)
    simp [hzero]

/-- Exact sampling formula for `μ_{1,n,m}(A × B)` over balanced ordered splits. -/
theorem muRect_one_eq_avg_splits {n m : ℕ} (hn : 1 ≤ n) (hm0 : 1 ≤ m)
    (hm : m ≤ (n - 1) / 2 + 1) (A B : Finset (BitString n)) :
    muRect 1 n m A B =
      (∑ T ∈ splits n, qSide A T.left T.point m * qSide B T.right T.point m) /
        ((splits n).card : ℝ) := by
  classical
  set k₁ := (n - 1) / 2
  set k₂ := n / 2
  have hm1 : m - 1 ≤ k₁ := by omega
  have hm2 : m - 1 ≤ k₂ := by omega
  have hcard_l : ∀ T ∈ splits n, T.left.card = k₁ := fun T hT => (mem_splits.mp hT).2.2.2.1
  have hcard_r : ∀ T ∈ splits n, T.right.card = k₂ := fun T hT => (mem_splits.mp hT).2.2.2.2
  have hswap : (∑ T ∈ splits n, qSide A T.left T.point m * qSide B T.right T.point m) /
      ((splits n).card : ℝ) =
      ∑ x ∈ A, ∑ y ∈ B,
        (#{T ∈ splits n |
            (T.point ∈ supportSet x ∧ supportSet x ⊆ insert T.point T.left ∧
              (supportSet x).card = m) ∧
            (T.point ∈ supportSet y ∧ supportSet y ⊆ insert T.point T.right ∧
              (supportSet y).card = m)} : ℝ) /
          (((splits n).card : ℝ) * (k₁.choose (m - 1) : ℝ) * (k₂.choose (m - 1) : ℝ)) := by
    have hpt : ∀ T ∈ splits n,
        qSide A T.left T.point m * qSide B T.right T.point m =
          (∑ x ∈ A, ∑ y ∈ B,
            if (T.point ∈ supportSet x ∧ supportSet x ⊆ insert T.point T.left ∧
                  (supportSet x).card = m) ∧
                (T.point ∈ supportSet y ∧ supportSet y ⊆ insert T.point T.right ∧
                  (supportSet y).card = m) then (1 : ℝ) else 0) /
            ((k₁.choose (m - 1) : ℝ) * (k₂.choose (m - 1) : ℝ)) := by
      intro T hT
      unfold qSide
      rw [hcard_l T hT, hcard_r T hT, div_mul_div_comm]
      congr 1
      rw [← sum_boole, ← sum_boole, sum_mul_sum]
      refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
      split_ifs <;> simp_all
    rw [sum_congr rfl hpt, ← sum_div, div_div,
      mul_comm ((k₁.choose (m - 1) : ℝ) * (k₂.choose (m - 1) : ℝ)), ← mul_assoc]
    rw [sum_comm (s := splits n) (t := A)]
    rw [sum_congr rfl fun x _ => sum_comm (s := splits n) (t := B)]
    rw [sum_div]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun y _ => ?_
    congr 1
    rw [sum_boole]
  rw [hswap, muRect_eq_sum]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  by_cases hmem : (x, y) ∈ weightPairs 1 n m
  · obtain ⟨hx, hy, hxy⟩ := mem_weightPairs.mp hmem
    obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hxy
    have hi₀x : i₀ ∈ supportSet x := by
      have : i₀ ∈ interSet x y := by rw [hi₀]; exact mem_singleton_self i₀
      rw [interSet_eq_inter] at this; exact (mem_inter.mp this).1
    have hi₀y : i₀ ∈ supportSet y := by
      have : i₀ ∈ interSet x y := by rw [hi₀]; exact mem_singleton_self i₀
      rw [interSet_eq_inter] at this; exact (mem_inter.mp this).2
    have hdisj' : Disjoint (supportSet x \ {i₀}) (supportSet y \ {i₀}) := by
      refine disjoint_left.mpr fun a hax hay => ?_
      obtain ⟨ha1, hne⟩ := mem_sdiff.mp hax
      obtain ⟨ha2, _⟩ := mem_sdiff.mp hay
      have : a ∈ interSet x y := by rw [interSet_eq_inter]; exact mem_inter.mpr ⟨ha1, ha2⟩
      rw [hi₀, mem_singleton] at this
      exact hne (mem_singleton.mpr this)
    have hcount : #{T ∈ splits n |
        (T.point ∈ supportSet x ∧ supportSet x ⊆ insert T.point T.left ∧
          (supportSet x).card = m) ∧
        (T.point ∈ supportSet y ∧ supportSet y ⊆ insert T.point T.right ∧
          (supportSet y).card = m)} = (n + 1 - 2 * m).choose (k₁ - (m - 1)) := by
      set U := (supportSet x ∪ supportSet y)ᶜ
      have hU : U.card = n + 1 - 2 * m := by
        have hu : (supportSet x ∪ supportSet y).card = 2 * m - 1 := by
          have h := card_union_add_card_inter (supportSet x) (supportSet y)
          rw [← interSet_eq_inter, hx, hy, hxy] at h; omega
        rw [card_compl, Fintype.card_fin, hu]; omega
      rw [← hU, ← card_powersetCard (k₁ - (m - 1)) U]
      refine Finset.card_bij (fun T _ => T.left \ (supportSet x \ {i₀})) ?_ ?_ ?_
      · intro T hT
        obtain ⟨hTs, ⟨hp1, hsub1, _⟩, ⟨hp2, hsub2, _⟩⟩ := mem_filter.mp hT
        obtain ⟨hpL, hpR, hLR, hLc, _⟩ := mem_splits.mp hTs
        have hp_eq : T.point = i₀ := by
          have : T.point ∈ interSet x y := by rw [interSet_eq_inter]; exact mem_inter.mpr ⟨hp1, hp2⟩
          rw [hi₀, mem_singleton] at this; exact this
        have hxL : supportSet x \ {i₀} ⊆ T.left := by
          intro a ha
          obtain ⟨hax, hane⟩ := mem_sdiff.mp ha
          rcases mem_insert.mp (hsub1 hax) with rfl | haL
          · exact absurd (mem_singleton.mpr hp_eq) hane
          · exact haL
        have hyR : supportSet y \ {i₀} ⊆ T.right := by
          intro a ha
          obtain ⟨hay, hane⟩ := mem_sdiff.mp ha
          rcases mem_insert.mp (hsub2 hay) with rfl | haR
          · exact absurd (mem_singleton.mpr hp_eq) hane
          · exact haR
        refine mem_powersetCard.mpr ⟨?_, ?_⟩
        · intro a ha
          obtain ⟨haL, hax⟩ := mem_sdiff.mp ha
          rw [mem_compl, mem_union, not_or]
          have hane : a ≠ i₀ := fun h => hpL (hp_eq.symm ▸ h ▸ haL)
          refine ⟨fun h => hax (mem_sdiff.mpr ⟨h, by simp [hane]⟩), fun h => ?_⟩
          exact disjoint_left.mp hLR haL (hyR (mem_sdiff.mpr ⟨h, by simp [hane]⟩))
        · rw [card_sdiff_of_subset hxL, hLc, card_sdiff_of_subset (singleton_subset_iff.mpr hi₀x),
            hx, card_singleton]
      · intro T₁ hT₁ T₂ hT₂ heq
        obtain ⟨hT₁s, ⟨hp11, hsub11, _⟩, ⟨hp12, _, _⟩⟩ := mem_filter.mp hT₁
        obtain ⟨hT₂s, ⟨hp21, hsub21, _⟩, ⟨hp22, _, _⟩⟩ := mem_filter.mp hT₂
        have hp1 : T₁.point = i₀ := by
          have : T₁.point ∈ interSet x y := by
            rw [interSet_eq_inter]; exact mem_inter.mpr ⟨hp11, hp12⟩
          rw [hi₀, mem_singleton] at this; exact this
        have hp2 : T₂.point = i₀ := by
          have : T₂.point ∈ interSet x y := by
            rw [interSet_eq_inter]; exact mem_inter.mpr ⟨hp21, hp22⟩
          rw [hi₀, mem_singleton] at this; exact this
        have hxL1 : supportSet x \ {i₀} ⊆ T₁.left := fun a ha => by
          obtain ⟨hax, hane⟩ := mem_sdiff.mp ha
          rcases mem_insert.mp (hsub11 hax) with rfl | haL
          · exact absurd (mem_singleton.mpr hp1) hane
          · exact haL
        have hxL2 : supportSet x \ {i₀} ⊆ T₂.left := fun a ha => by
          obtain ⟨hax, hane⟩ := mem_sdiff.mp ha
          rcases mem_insert.mp (hsub21 hax) with rfl | haL
          · exact absurd (mem_singleton.mpr hp2) hane
          · exact haL
        have hL : T₁.left = T₂.left := by
          rw [← sdiff_union_of_subset hxL1, ← sdiff_union_of_subset hxL2, heq]
        have hp : T₁.point = T₂.point := hp1.trans hp2.symm
        have hR : T₁.right = T₂.right := by
          rw [right_eq_compl_insert_left hn hT₁s, right_eq_compl_insert_left hn hT₂s, hp, hL]
        exact OrderedSplit.ext hp hL hR
      · intro L hL
        obtain ⟨hLU, hLc⟩ := mem_powersetCard.mp hL
        have hdisjLx : Disjoint L (supportSet x \ {i₀}) := disjoint_left.mpr fun a haL hax =>
          (mem_compl.mp (hLU haL)) (mem_union_left _ (mem_sdiff.mp hax).1)
        have hdisjLy : Disjoint L (supportSet y \ {i₀}) := disjoint_left.mpr fun a haL hay =>
          (mem_compl.mp (hLU haL)) (mem_union_right _ (mem_sdiff.mp hay).1)
        have hi₀L : i₀ ∉ L := fun h => (mem_compl.mp (hLU h)) (mem_union_left _ hi₀x)
        let Tl := L ∪ (supportSet x \ {i₀})
        let Tr := (insert i₀ Tl)ᶜ
        have hTlc : Tl.card = k₁ := by
          rw [card_union_of_disjoint hdisjLx, hLc,
            card_sdiff_of_subset (singleton_subset_iff.mpr hi₀x), hx, card_singleton]
          omega
        have hi₀Tl : i₀ ∉ Tl := by simp [Tl, hi₀L]
        have hTrc : Tr.card = k₂ := by
          rw [card_compl, Fintype.card_fin, card_insert_of_notMem hi₀Tl, hTlc]; omega
        refine ⟨⟨i₀, Tl, Tr⟩, mem_filter.mpr ⟨mem_splits.mpr ⟨hi₀Tl, ?_, ?_, hTlc, hTrc⟩,
          ⟨hi₀x, ?_, hx⟩, ⟨hi₀y, ?_, hy⟩⟩, ?_⟩
        · simp [Tr]
        · exact disjoint_right.mpr fun a ha haTl => (mem_compl.mp ha) (mem_insert_of_mem haTl)
        · intro a hax
          by_cases hai : a = i₀
          · exact mem_insert.mpr (.inl hai)
          · exact mem_insert_of_mem (mem_union_right _ (mem_sdiff.mpr ⟨hax, by simp [hai]⟩))
        · intro a hay
          by_cases hai : a = i₀
          · exact mem_insert.mpr (.inl hai)
          · apply mem_insert_of_mem
            rw [mem_compl, mem_insert, not_or]
            refine ⟨hai, fun haTl => ?_⟩
            rcases mem_union.mp haTl with haL | hax
            · exact disjoint_left.mp hdisjLy haL (mem_sdiff.mpr ⟨hay, by simp [hai]⟩)
            · exact disjoint_left.mp hdisj' hax (mem_sdiff.mpr ⟨hay, by simp [hai]⟩)
        · simp [Tl, sdiff_eq_self_of_disjoint hdisjLx]
    rw [muWeight_of_mem hmem, hcount]
    have hpos_wc : (0 : ℝ) < weightCard 1 n m :=
      Nat.cast_pos.mpr (weightCard_pos_iff.mpr ⟨hm0, by omega⟩)
    have hpos_sp : (0 : ℝ) < (splits n).card := Nat.cast_pos.mpr (card_splits_pos hn)
    have hpos_c1 : (0 : ℝ) < k₁.choose (m - 1) := Nat.cast_pos.mpr (Nat.choose_pos hm1)
    have hpos_c2 : (0 : ℝ) < k₂.choose (m - 1) := Nat.cast_pos.mpr (Nat.choose_pos hm2)
    have hnat : (n + 1 - 2 * m).choose (k₁ - (m - 1)) * weightCard 1 n m =
        (splits n).card * k₁.choose (m - 1) * k₂.choose (m - 1) := by
      have h1 := weightCard_mul_factorials (k := 1) (n := n) (m := m) hm0 (by omega)
      simp only [Nat.factorial_one, one_mul] at h1
      have h2 := card_splits_mul_factorials hn
      have hc1 := Nat.choose_mul_factorial_mul_factorial hm1
      have hc2 := Nat.choose_mul_factorial_mul_factorial hm2
      have hc3 := Nat.choose_mul_factorial_mul_factorial
        (show k₁ - (m - 1) ≤ n + 1 - 2 * m by omega)
      have hsub : n + 1 - 2 * m - (k₁ - (m - 1)) = k₂ - (m - 1) := by omega
      rw [hsub] at hc3
      have hmul : ((n + 1 - 2 * m).choose (k₁ - (m - 1)) * weightCard 1 n m) *
          ((k₁ - (m - 1)).factorial * (k₂ - (m - 1)).factorial *
            (m - 1).factorial * (m - 1).factorial * (n + 1 - 2 * m).factorial) =
          ((splits n).card * k₁.choose (m - 1) * k₂.choose (m - 1)) *
          ((k₁ - (m - 1)).factorial * (k₂ - (m - 1)).factorial *
            (m - 1).factorial * (m - 1).factorial * (n + 1 - 2 * m).factorial) := by
        calc
          ((n + 1 - 2 * m).choose (k₁ - (m - 1)) * weightCard 1 n m) *
              ((k₁ - (m - 1)).factorial * (k₂ - (m - 1)).factorial *
                (m - 1).factorial * (m - 1).factorial * (n + 1 - 2 * m).factorial)
            = ((n + 1 - 2 * m).choose (k₁ - (m - 1)) * (k₁ - (m - 1)).factorial *
                (k₂ - (m - 1)).factorial) *
              (weightCard 1 n m * ((m - 1).factorial * (m - 1).factorial *
                (n + 1 - 2 * m).factorial)) := by ring
          _ = (n + 1 - 2 * m).factorial * n.factorial := by rw [hc3, h1]
          _ = (n + 1 - 2 * m).factorial * ((splits n).card * k₁.factorial * k₂.factorial) := by
              rw [h2]
          _ = (n + 1 - 2 * m).factorial * ((splits n).card *
                (k₁.choose (m - 1) * (m - 1).factorial * (k₁ - (m - 1)).factorial) *
                (k₂.choose (m - 1) * (m - 1).factorial * (k₂ - (m - 1)).factorial)) := by
              rw [hc1, hc2]
          _ = ((splits n).card * k₁.choose (m - 1) * k₂.choose (m - 1)) *
              ((k₁ - (m - 1)).factorial * (k₂ - (m - 1)).factorial *
                (m - 1).factorial * (m - 1).factorial * (n + 1 - 2 * m).factorial) := by ring
      have hfac_pos : 0 < (k₁ - (m - 1)).factorial * (k₂ - (m - 1)).factorial *
          (m - 1).factorial * (m - 1).factorial * (n + 1 - 2 * m).factorial := by positivity
      exact Nat.eq_of_mul_eq_mul_right hfac_pos hmul
    have hR : ((n + 1 - 2 * m).choose (k₁ - (m - 1)) : ℝ) * (weightCard 1 n m : ℝ) =
        ((splits n).card : ℝ) * (k₁.choose (m - 1) : ℝ) * (k₂.choose (m - 1) : ℝ) := by
      exact_mod_cast hnat
    field_simp
    linarith
  · rw [muWeight_eq_zero_of_notMem hmem]
    have hzero : #{T ∈ splits n |
        (T.point ∈ supportSet x ∧ supportSet x ⊆ insert T.point T.left ∧
          (supportSet x).card = m) ∧
        (T.point ∈ supportSet y ∧ supportSet y ⊆ insert T.point T.right ∧
          (supportSet y).card = m)} = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      intro T hTs hcond
      obtain ⟨⟨hp1, hsub1, hxc⟩, ⟨hp2, hsub2, hyc⟩⟩ := hcond
      have hLR := (mem_splits.mp hTs).2.2.1
      have hinter : interSet x y = {T.point} := by
        ext a
        rw [mem_interSet, mem_singleton]
        constructor
        · rintro ⟨hax, hay⟩
          rcases mem_insert.mp (hsub1 (mem_supportSet.mpr hax)) with rfl | haL
          · rfl
          · rcases mem_insert.mp (hsub2 (mem_supportSet.mpr hay)) with rfl | haR
            · rfl
            · exact absurd (disjoint_left.mp hLR haL haR) id
        · rintro rfl
          exact ⟨mem_supportSet.mp hp1, mem_supportSet.mp hp2⟩
      exact hmem (mem_weightPairs.mpr ⟨hxc, hyc, by rw [hinter, card_singleton]⟩)
    rw [hzero]
    simp

/-! ### Marginal union bound for small `n` -/

/-- Exact marginal of `μ_{k,n,m}` on `A × univ`: equals the fraction of weight-`m` strings in `A`.
-/
private theorem muRect_univ_right {k n m : ℕ} (hk : k ≤ m) (h2m : 2 * m ≤ n + k)
    (A : Finset (BitString n)) :
    muRect k n m A univ =
      (#{x ∈ A | (supportSet x).card = m} : ℝ) / (n.choose m : ℝ) := by
  classical
  have hpos_wc : (0 : ℝ) < weightCard k n m :=
    Nat.cast_pos.mpr (weightCard_pos_iff.mpr ⟨hk, h2m⟩)
  have hpos_ch : (0 : ℝ) < n.choose m := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  rw [muRect_eq_sum]
  have hinner : ∀ x : BitString n,
      ∑ y : BitString n, muWeight k n m x y =
        if (supportSet x).card = m then (n.choose m : ℝ)⁻¹ else 0 := by
    intro x
    by_cases hx : (supportSet x).card = m
    · simp only [hx, ↓reduceIte]
      have hcount : #{y : BitString n | (x, y) ∈ weightPairs k n m} =
          m.choose k * (n - m).choose (m - k) := by
        have hbij : #{y : BitString n | (x, y) ∈ weightPairs k n m} =
            ((supportSet x).powersetCard k).sum fun I =>
              ((supportSet x)ᶜ.powersetCard (m - k)).card := by
          rw [← card_sigma]
          refine Finset.card_bij
            (fun y _ => ⟨interSet x y, supportSet y \ supportSet x⟩) ?_ ?_ ?_
          · intro y hy
            obtain ⟨_, hyc, hxyc⟩ := mem_weightPairs.mp (mem_filter.mp hy).2
            refine mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨?_, hxyc⟩, mem_powersetCard.mpr ⟨?_, ?_⟩⟩
            · rw [interSet_eq_inter]; exact inter_subset_left
            · intro i hi; exact mem_compl.mpr (mem_sdiff.mp hi).2
            · dsimp only
              have h := card_sdiff_add_card_inter (supportSet y) (supportSet x)
              rw [inter_comm, ← interSet_eq_inter, hxyc, hyc] at h; omega
          · intro y₁ _ y₂ _ heq
            have h1 : interSet x y₁ = interSet x y₂ := congrArg Sigma.fst heq
            have h2 : supportSet y₁ \ supportSet x = supportSet y₂ \ supportSet x :=
              congrArg Sigma.snd heq
            have hs : supportSet y₁ = supportSet y₂ := by
              calc supportSet y₁
                  = (supportSet y₁ \ supportSet x) ∪ (supportSet x ∩ supportSet y₁) := by
                    rw [inter_comm, sdiff_union_inter]
                _ = (supportSet y₂ \ supportSet x) ∪ (supportSet x ∩ supportSet y₂) := by
                    rw [← interSet_eq_inter, ← interSet_eq_inter, h1, h2]
                _ = supportSet y₂ := by rw [inter_comm, sdiff_union_inter]
            rw [← ofFinset_supportSet y₁, ← ofFinset_supportSet y₂, hs]
          · rintro ⟨I, B⟩ hmem
            obtain ⟨hI, hB⟩ := mem_sigma.mp hmem
            obtain ⟨hIx, hIc⟩ := mem_powersetCard.mp hI
            obtain ⟨hBx, hBc⟩ := mem_powersetCard.mp hB
            have hdisj : Disjoint (supportSet x) B := disjoint_right.mpr fun i hi =>
              mem_compl.mp (hBx hi)
            have hdisjIB : Disjoint I B := hdisj.mono_left hIx
            refine ⟨ofFinset (I ∪ B), mem_filter.mpr ⟨mem_univ _, mem_weightPairs.mpr ⟨hx, ?_, ?_⟩⟩,
              ?_⟩
            · rw [supportSet_ofFinset, card_union_of_disjoint hdisjIB, hIc, hBc]; omega
            · rw [interSet_eq_inter, supportSet_ofFinset, inter_union_distrib_left,
                inter_eq_right.mpr hIx, Finset.disjoint_iff_inter_eq_empty.mp hdisj, union_empty,
                hIc]
            · refine Sigma.ext ?_ (heq_of_eq ?_)
              · rw [interSet_eq_inter, supportSet_ofFinset, inter_union_distrib_left,
                  inter_eq_right.mpr hIx, Finset.disjoint_iff_inter_eq_empty.mp hdisj, union_empty]
              · rw [supportSet_ofFinset, union_sdiff_distrib, sdiff_eq_empty_iff_subset.mpr hIx,
                  empty_union, sdiff_eq_self_of_disjoint hdisj.symm]
        rw [hbij, sum_const, card_powersetCard, hx, card_powersetCard, card_compl,
          Fintype.card_fin, hx, smul_eq_mul]
      calc
        ∑ y : BitString n, muWeight k n m x y
          = ∑ y : BitString n with (x, y) ∈ weightPairs k n m, ((weightCard k n m : ℝ))⁻¹ := by
            rw [sum_filter]
            refine sum_congr rfl fun y _ => ?_
            by_cases hy : (x, y) ∈ weightPairs k n m
            · simp only [hy, ↓reduceIte, muWeight_of_mem hy]
            · simp only [hy, ↓reduceIte, muWeight_eq_zero_of_notMem hy]
        _ = (#{y : BitString n | (x, y) ∈ weightPairs k n m} : ℝ) *
              ((weightCard k n m : ℝ))⁻¹ := by rw [sum_const, nsmul_eq_mul]
        _ = (n.choose m : ℝ)⁻¹ := by
            rw [hcount, weightCard_eq_choose]
            push_cast
            have h2pos : (0 : ℝ) < m.choose k * (n - m).choose (m - k) := by
              have h1 : 0 < m.choose k := Nat.choose_pos hk
              have h2 : 0 < (n - m).choose (m - k) := Nat.choose_pos (by omega)
              positivity
            have h2ne : (m.choose k : ℝ) * ((n - m).choose (m - k) : ℝ) ≠ 0 := h2pos.ne'
            field_simp
            exact div_self h2ne
    · simp only [hx, ↓reduceIte]
      exact sum_eq_zero fun y _ => muWeight_eq_zero_of_notMem fun h =>
        hx (mem_weightPairs.mp h).1
  rw [sum_congr rfl fun x _ => hinner x, ← sum_filter, sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- Marginal union bound: for any `1 ≤ m` with `2 * m ≤ n` and any rectangle `A × B`,
`μ_{1,n,m}(A × B) ≥ 2 * μ_{0,n,m}(A × B) - 1`. -/
theorem muRect_one_ge_two_mul_sub_one {n m : ℕ} (hm0 : 1 ≤ m) (h2m : 2 * m ≤ n)
    (A B : Finset (BitString n)) :
    2 * muRect 0 n m A B - 1 ≤ muRect 1 n m A B := by
  have h1 : muRect 1 n m A univ = muRect 0 n m A univ := by
    rw [muRect_univ_right hm0 (by omega), muRect_univ_right (Nat.zero_le m) (by omega)]
  have h2 : muRect 1 n m univ B = muRect 0 n m univ B := by
    rw [muRect_comm, muRect_comm 0, muRect_univ_right hm0 (by omega),
      muRect_univ_right (Nat.zero_le m) (by omega)]
  have hA : muRect 0 n m A B ≤ muRect 0 n m A univ := muRect_mono Subset.rfl (subset_univ B)
  have hB : muRect 0 n m A B ≤ muRect 0 n m univ B := muRect_mono (subset_univ A) Subset.rfl
  have hdecomp : muRect 1 n m A univ + muRect 1 n m univ B ≤
      muRect 1 n m A B + muRect 1 n m univ univ := by
    simp_rw [muRect_eq_sum]
    have hA_split : ∑ x ∈ A, ∑ y : BitString n, muWeight 1 n m x y =
        ∑ x ∈ A, ∑ y ∈ B, muWeight 1 n m x y + ∑ x ∈ A, ∑ y ∈ Bᶜ, muWeight 1 n m x y := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun x _ => (sum_add_sum_compl B _).symm
    have hB_split : ∑ x : BitString n, ∑ y ∈ B, muWeight 1 n m x y =
        ∑ x ∈ A, ∑ y ∈ B, muWeight 1 n m x y + ∑ x ∈ Aᶜ, ∑ y ∈ B, muWeight 1 n m x y :=
      (sum_add_sum_compl A _).symm
    have hU_split : ∑ x : BitString n, ∑ y : BitString n, muWeight 1 n m x y =
        ∑ x ∈ A, ∑ y ∈ B, muWeight 1 n m x y + ∑ x ∈ A, ∑ y ∈ Bᶜ, muWeight 1 n m x y +
        ∑ x ∈ Aᶜ, ∑ y ∈ B, muWeight 1 n m x y + ∑ x ∈ Aᶜ, ∑ y ∈ Bᶜ, muWeight 1 n m x y := by
      rw [← sum_add_sum_compl A (fun x => ∑ y : BitString n, muWeight 1 n m x y)]
      have hl : ∑ x ∈ A, ∑ y : BitString n, muWeight 1 n m x y =
          ∑ x ∈ A, ∑ y ∈ B, muWeight 1 n m x y + ∑ x ∈ A, ∑ y ∈ Bᶜ, muWeight 1 n m x y := hA_split
      have hr : ∑ x ∈ Aᶜ, ∑ y : BitString n, muWeight 1 n m x y =
          ∑ x ∈ Aᶜ, ∑ y ∈ B, muWeight 1 n m x y + ∑ x ∈ Aᶜ, ∑ y ∈ Bᶜ, muWeight 1 n m x y := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun x _ => (sum_add_sum_compl B _).symm
      rw [hl, hr]; ring
    have hnn : 0 ≤ ∑ x ∈ Aᶜ, ∑ y ∈ Bᶜ, muWeight 1 n m x y :=
      sum_nonneg fun _ _ => sum_nonneg fun _ _ => muWeight_nonneg _ _ _ _ _
    linarith
  rw [muRect_univ hm0 (by omega), h1, h2] at hdecomp
  linarith


end CslibFrontier.Computability.Communication
