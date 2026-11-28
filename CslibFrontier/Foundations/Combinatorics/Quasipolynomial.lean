module

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.PowerSeries.Basic

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quasipolynomials, Positivity Index, and Saturation Index

Develops rational quasipolynomials on `ℕ` together with their period-independent invariants:

- `CslibFrontier.Combinatorics.Quasipolynomial`: a function `ℕ → ℚ` given by polynomial
  constituents on each residue class modulo a positive period `l ≥ 1`, with shift and generating
  power series.
- `CslibFrontier.Combinatorics.Quasipolynomial.index`: the smallest positive residue class whose
  constituent polynomial is nonzero (or `0` for the identically zero quasipolynomial).
- `CslibFrontier.Combinatorics.Quasipolynomial.IsStrictlyPositive` and `positivityIndex`:
  nonnegativity of all constituent coefficients and the minimal shift achieving strict positivity,
  including existence whenever every nonzero constituent has positive leading coefficient.
- `CslibFrontier.Combinatorics.Quasipolynomial.IsStrictlySaturated` and `saturationIndex`:
  positivity of evaluations on nonzero residue classes for `n ≥ 1`, the minimal shift achieving
  strict saturation, and the inequality `saturationIndex ≤ positivityIndex`.
-/

public section

namespace CslibFrontier.Combinatorics

open scoped BigOperators Polynomial PowerSeries

/-- A quasipolynomial `f : ℕ → ℚ` of positive period `period`, specified by its constituent
polynomials `constituent r ∈ ℚ[X]` for each residue class `r : Fin period`. -/
@[ext]
structure Quasipolynomial where
  /-- A positive period of the quasipolynomial. -/
  period : ℕ
  /-- Positivity witness for the period. -/
  period_pos : 0 < period
  /-- Constituent polynomial `f_r(X) ∈ ℚ[X]` for the residue class `n ≡ r (mod period)`. -/
  constituent : Fin period → ℚ[X]

namespace Quasipolynomial

/-- Evaluate a quasipolynomial at `n : ℕ` via its `(n % period)`-th constituent polynomial. -/
def eval (f : Quasipolynomial) (n : ℕ) : ℚ :=
  (f.constituent ⟨n % f.period, Nat.mod_lt n f.period_pos⟩).eval (n : ℚ)

theorem eval_apply (f : Quasipolynomial) (n : ℕ) :
    f.eval n = (f.constituent ⟨n % f.period, Nat.mod_lt n f.period_pos⟩).eval (n : ℚ) := by rfl

/-- The formal generating series `∑_{n ≥ 0} f(n) X^n ∈ ℚ⟦X⟧`. -/
def genSeries (f : Quasipolynomial) : ℚ⟦X⟧ :=
  PowerSeries.mk f.eval

@[simp]
theorem coeff_genSeries (f : Quasipolynomial) (n : ℕ) :
    PowerSeries.coeff n f.genSeries = f.eval n := by
  simp [genSeries]

/-- The constituent polynomial indexed by `j ∈ ℕ` modulo `f.period`. -/
def constituentMod (f : Quasipolynomial) (j : ℕ) : ℚ[X] :=
  f.constituent ⟨j % f.period, Nat.mod_lt j f.period_pos⟩

theorem constituentMod_apply (f : Quasipolynomial) (j : ℕ) :
    f.constituentMod j = f.constituent ⟨j % f.period, Nat.mod_lt j f.period_pos⟩ := by rfl

theorem constituentMod_eq_of_mod_eq (f : Quasipolynomial) {j₁ j₂ : ℕ}
    (h : j₁ % f.period = j₂ % f.period) :
    f.constituentMod j₁ = f.constituentMod j₂ := by
  simp only [constituentMod, h]

theorem eval_eq_constituentMod_eval (f : Quasipolynomial) (n : ℕ) :
    f.eval n = (f.constituentMod n).eval (n : ℚ) := by
  simp [eval, constituentMod]

/-- Two quasipolynomials with identical evaluations on `ℕ` have identical constituent polynomials
on every residue class. -/
theorem constituentMod_eq_of_eval_eq {f g : Quasipolynomial} (h : ∀ n, f.eval n = g.eval n)
    (j : ℕ) : f.constituentMod j = g.constituentMod j := by
  set L := f.period * g.period
  have hL : 0 < L := Nat.mul_pos f.period_pos g.period_pos
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := Set.range fun k : ℕ ↦ ((j + k * L : ℕ) : ℚ)) ?_ ?_
  · rintro _ ⟨k, rfl⟩
    have h1 : (j + k * L) % f.period = j % f.period := by
      have : k * L = (k * g.period) * f.period := by simp only [L]; ring
      rw [this, Nat.add_mul_mod_self_right]
    have h2 : (j + k * L) % g.period = j % g.period := by
      have : k * L = (k * f.period) * g.period := by simp only [L]; ring
      rw [this, Nat.add_mul_mod_self_right]
    have hev := h (j + k * L)
    simp only [eval, constituentMod, h1, h2] at hev ⊢
    exact hev
  · refine Set.infinite_range_of_injective fun k₁ k₂ hk ↦ ?_
    have hnat : j + k₁ * L = j + k₂ * L := Nat.cast_injective hk
    exact Nat.eq_of_mul_eq_mul_right hL (Nat.add_left_cancel hnat)

theorem constituentMod_eq_zero_iff_forall_eval_eq_zero (f : Quasipolynomial) (j : ℕ) :
    f.constituentMod j = 0 ↔ ∀ k : ℕ, f.eval (j + k * f.period) = 0 := by
  constructor
  · intro h0 k
    have hmod : (j + k * f.period) % f.period = j % f.period := Nat.add_mul_mod_self_right _ _ _
    simp only [eval, hmod]
    change (f.constituentMod j).eval _ = 0
    rw [h0, Polynomial.eval_zero]
  · intro h0
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := Set.range fun k : ℕ ↦ ((j + k * f.period : ℕ) : ℚ)) ?_ ?_
    · rintro _ ⟨k, rfl⟩
      have hmod : (j + k * f.period) % f.period = j % f.period :=
        Nat.add_mul_mod_self_right _ _ _
      have hev := h0 k
      simp only [eval, hmod] at hev
      simpa [constituentMod] using hev
    · refine Set.infinite_range_of_injective fun k₁ k₂ hk ↦ ?_
      have hnat : j + k₁ * f.period = j + k₂ * f.period := Nat.cast_injective hk
      exact Nat.eq_of_mul_eq_mul_right f.period_pos (Nat.add_left_cancel hnat)

/-- The shifted quasipolynomial `n ↦ f(n + s)`. -/
noncomputable def shift (f : Quasipolynomial) (s : ℕ) : Quasipolynomial where
  period := f.period
  period_pos := f.period_pos
  constituent r := (f.constituentMod (r.1 + s)).comp (Polynomial.X + Polynomial.C (s : ℚ))

@[simp]
theorem eval_shift (f : Quasipolynomial) (s n : ℕ) :
    (f.shift s).eval n = f.eval (n + s) := by
  have hmod : (n % f.period + s) % f.period = (n + s) % f.period := by
    simp [Nat.add_mod]
  simp only [shift, eval, constituentMod, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, hmod, Nat.cast_add]

theorem constituentMod_shift (f : Quasipolynomial) (s j : ℕ) :
    (f.shift s).constituentMod j =
      (f.constituentMod (j + s)).comp (Polynomial.X + Polynomial.C (s : ℚ)) := by
  have hmod : (j % f.period + s) % f.period = (j + s) % f.period := by
    simp [Nat.add_mod]
  simp [shift, constituentMod, hmod]

theorem constituentMod_shift_ne_zero_iff (f : Quasipolynomial) (s j : ℕ) :
    (f.shift s).constituentMod j ≠ 0 ↔ f.constituentMod (j + s) ≠ 0 := by
  rw [constituentMod_shift]
  constructor
  · intro h h0
    rw [h0, Polynomial.zero_comp] at h
    exact h rfl
  · intro h h0
    apply h
    have hcomp :
        ((f.constituentMod (j + s)).comp (Polynomial.X + Polynomial.C (s : ℚ))).comp
          (Polynomial.X - Polynomial.C (s : ℚ)) = 0 := by
      rw [h0, Polynomial.zero_comp]
    rw [Polynomial.comp_assoc] at hcomp
    have hX : (Polynomial.X + Polynomial.C (s : ℚ)).comp (Polynomial.X - Polynomial.C (s : ℚ)) =
        Polynomial.X := by
      simp
    rw [hX, Polynomial.comp_X] at hcomp
    exact hcomp

/-- Degree `max_r deg(f_r)` of a quasipolynomial. -/
def degree (f : Quasipolynomial) : ℕ :=
  Finset.univ.sup fun r : Fin f.period ↦ (f.constituent r).natDegree

/-- The index of a quasipolynomial `f`: the smallest `j ≥ 1` such that the constituent polynomial
`f_j` is nonzero, or `0` if `f` is identically zero. -/
noncomputable def index (f : Quasipolynomial) : ℕ := by
  classical
  exact if h : ∃ j : ℕ, 0 < j ∧ f.constituentMod j ≠ 0 then Nat.find h else 0

theorem index_eq_zero_iff (f : Quasipolynomial) :
    f.index = 0 ↔ ∀ n : ℕ, f.eval n = 0 := by
  classical
  unfold index
  split_ifs with h
  · constructor
    · intro h0
      exact absurd h0 (Nat.ne_of_gt (Nat.find_spec h).1)
    · intro hall
      rcases h with ⟨j, _, hj⟩
      exact absurd ((f.constituentMod_eq_zero_iff_forall_eval_eq_zero j).2
        fun k ↦ hall _) hj
  · push Not at h
    simp only [true_iff]
    intro n
    have hmod : (n + f.period) % f.period = n % f.period := Nat.add_mod_right n f.period
    have hpos : 0 < n + f.period := Nat.add_pos_right n f.period_pos
    have h0 := h (n + f.period) hpos
    simp only [constituentMod, hmod] at h0
    simp [eval, h0]

theorem index_pos_of_exists_eval_ne_zero {f : Quasipolynomial} (h : ∃ n, f.eval n ≠ 0) :
    0 < f.index := by
  refine Nat.pos_of_ne_zero fun h0 ↦ ?_
  rcases h with ⟨n, hn⟩
  exact hn ((f.index_eq_zero_iff).1 h0 n)

theorem index_spec {f : Quasipolynomial} (h : 0 < f.index) :
    f.constituentMod f.index ≠ 0 := by
  classical
  unfold index at h ⊢
  split_ifs at h ⊢ with hex
  · exact (Nat.find_spec hex).2
  · omega

theorem constituentMod_eq_zero_of_lt_index {f : Quasipolynomial} {j : ℕ}
    (hj0 : 0 < j) (hj : j < f.index) : f.constituentMod j = 0 := by
  classical
  unfold index at hj
  split_ifs at hj with hex
  · by_contra hne
    exact Nat.not_lt.2 (Nat.find_min' hex ⟨hj0, hne⟩) hj
  · omega

theorem index_le_of_constituentMod_ne_zero {f : Quasipolynomial} {j : ℕ}
    (hj0 : 0 < j) (hj : f.constituentMod j ≠ 0) : f.index ≤ j := by
  classical
  have hex : ∃ k : ℕ, 0 < k ∧ f.constituentMod k ≠ 0 := ⟨j, hj0, hj⟩
  simp only [index, hex, ↓reduceDIte]
  exact Nat.find_min' hex ⟨hj0, hj⟩

theorem index_le_period (f : Quasipolynomial) : f.index ≤ f.period := by
  classical
  unfold index
  by_cases hex : ∃ j : ℕ, 0 < j ∧ f.constituentMod j ≠ 0
  · simp only [hex, ↓reduceDIte]
    have ⟨j, _, hj⟩ := hex
    by_cases hmod0 : j % f.period = 0
    · refine Nat.find_min' hex ⟨f.period_pos, ?_⟩
      simpa [constituentMod, hmod0, Nat.mod_self] using hj
    · refine le_trans (Nat.find_min' hex ⟨Nat.pos_of_ne_zero hmod0, ?_⟩)
        (le_of_lt (Nat.mod_lt j f.period_pos))
      simpa [constituentMod, Nat.mod_mod] using hj
  · simp [hex]

/-- The index depends only on the function `f.eval`, not on the choice of period. -/
theorem index_eq_of_eval_eq {f g : Quasipolynomial} (h : ∀ n, f.eval n = g.eval n) :
    f.index = g.index := by
  classical
  have hc : ∀ j, f.constituentMod j = g.constituentMod j := constituentMod_eq_of_eval_eq h
  simp only [index, hc]

/-- If `f(1) ≠ 0`, then `f.index = 1`. -/
theorem index_eq_one_of_eval_one_ne_zero {f : Quasipolynomial} (h1 : f.eval 1 ≠ 0) :
    f.index = 1 := by
  classical
  have hc1 : f.constituentMod 1 ≠ 0 := by
    intro h0
    apply h1
    rw [eval_eq_constituentMod_eval, h0, Polynomial.eval_zero]
  have hle : f.index ≤ 1 := f.index_le_of_constituentMod_ne_zero Nat.one_pos hc1
  have hpos : 0 < f.index := f.index_pos_of_exists_eval_ne_zero ⟨1, h1⟩
  omega

/-- A quasipolynomial is strictly positive if every coefficient of every constituent polynomial is
nonnegative. -/
def IsStrictlyPositive (f : Quasipolynomial) : Prop :=
  ∀ (r : Fin f.period) (k : ℕ), 0 ≤ (f.constituent r).coeff k

theorem isStrictlyPositive_iff_constituentMod (f : Quasipolynomial) :
    f.IsStrictlyPositive ↔ ∀ (j k : ℕ), 0 ≤ (f.constituentMod j).coeff k := by
  constructor
  · intro h j k
    exact h ⟨j % f.period, Nat.mod_lt j f.period_pos⟩ k
  · intro h r k
    have hmod : r.1 % f.period = r.1 := Nat.mod_eq_of_lt r.2
    simpa [constituentMod, hmod] using h r.1 k

theorem IsStrictlyPositive.of_eval_eq {f g : Quasipolynomial}
    (heq : ∀ n, f.eval n = g.eval n) (hf : f.IsStrictlyPositive) : g.IsStrictlyPositive := by
  rw [isStrictlyPositive_iff_constituentMod] at hf ⊢
  intro j k
  rw [← constituentMod_eq_of_eval_eq heq j]
  exact hf j k

/-- Existence of a finite positivity shift. -/
def HasPositivityIndex (f : Quasipolynomial) : Prop :=
  ∃ s : ℕ, (f.shift s).IsStrictlyPositive

/-- The positivity index of `f`: the smallest `s : ℕ` such that `f.shift s` is strictly positive,
or `0` if none exists. -/
noncomputable def positivityIndex (f : Quasipolynomial) : ℕ := by
  classical
  exact if h : f.HasPositivityIndex then Nat.find h else 0

theorem shift_positivityIndex_isStrictlyPositive {f : Quasipolynomial}
    (h : f.HasPositivityIndex) : (f.shift f.positivityIndex).IsStrictlyPositive := by
  classical
  simp only [positivityIndex, h, ↓reduceDIte]
  exact Nat.find_spec h

theorem positivityIndex_le {f : Quasipolynomial} {s : ℕ}
    (hs : (f.shift s).IsStrictlyPositive) : f.positivityIndex ≤ s := by
  classical
  have hex : f.HasPositivityIndex := ⟨s, hs⟩
  simp only [positivityIndex, hex, ↓reduceDIte]
  exact Nat.find_min' hex hs

theorem positivityIndex_eq_zero_iff {f : Quasipolynomial} (h : f.HasPositivityIndex) :
    f.positivityIndex = 0 ↔ f.IsStrictlyPositive := by
  constructor
  · intro h0
    have hs := f.shift_positivityIndex_isStrictlyPositive h
    rw [h0] at hs
    refine IsStrictlyPositive.of_eval_eq (fun n ↦ ?_) hs
    simp
  · intro hf
    have h0 : (f.shift 0).IsStrictlyPositive :=
      IsStrictlyPositive.of_eval_eq (fun n ↦ by simp) hf
    exact Nat.eq_zero_of_le_zero (f.positivityIndex_le h0)

private lemma exists_nat_eval_nonneg_of_leadingCoeff_pos {p : ℚ[X]}
    (hp : 0 < p.leadingCoeff) : ∃ N : ℕ, ∀ s : ℕ, N ≤ s → 0 ≤ p.eval (s : ℚ) := by
  by_cases hdeg : p.natDegree = 0
  · refine ⟨0, fun s _ ↦ ?_⟩
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, Polynomial.eval_C]
    rw [Polynomial.leadingCoeff, hdeg] at hp
    exact le_of_lt hp
  · have hdeg_pos : 0 < p.natDegree := Nat.pos_of_ne_zero hdeg
    set d := p.natDegree
    set c := p.leadingCoeff
    set B : ℚ := ∑ k ∈ Finset.range d, |p.coeff k|
    obtain ⟨N, hN⟩ := exists_nat_gt (B / c)
    refine ⟨max N 1, fun s hs ↦ ?_⟩
    have hs1 : 1 ≤ s := le_trans (le_max_right N 1) hs
    have hsN : (N : ℚ) ≤ (s : ℚ) := by exact_mod_cast le_trans (le_max_left N 1) hs
    have hs_pos : (0 : ℚ) < (s : ℚ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs1)
    have hs_ge1 : (1 : ℚ) ≤ (s : ℚ) := by exact_mod_cast hs1
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]
    have htail : ∑ k ∈ Finset.range d, p.coeff k * (s : ℚ) ^ k ≥ -(B * (s : ℚ) ^ (d - 1)) := by
      have h1 : |∑ k ∈ Finset.range d, p.coeff k * (s : ℚ) ^ k| ≤ B * (s : ℚ) ^ (d - 1) := by
        calc
          |∑ k ∈ Finset.range d, p.coeff k * (s : ℚ) ^ k|
              ≤ ∑ k ∈ Finset.range d, |p.coeff k * (s : ℚ) ^ k| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k ∈ Finset.range d, |p.coeff k| * (s : ℚ) ^ k := by
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            rw [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hs_pos) k)]
          _ ≤ ∑ k ∈ Finset.range d, |p.coeff k| * (s : ℚ) ^ (d - 1) := by
            refine Finset.sum_le_sum fun k hk ↦ ?_
            have hkd : k ≤ d - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.1 hk)
            exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hs_ge1 hkd) (abs_nonneg _)
          _ = B * (s : ℚ) ^ (d - 1) := by rw [← Finset.sum_mul]
      linarith [(abs_le.1 h1).1]
    have hlead : B * (s : ℚ) ^ (d - 1) ≤ c * (s : ℚ) ^ d := by
      have hBc : B ≤ c * (s : ℚ) := by
        have hlt : B / c < (s : ℚ) := lt_of_lt_of_le hN hsN
        have := (div_lt_iff₀ hp).1 hlt
        linarith
      calc
        B * (s : ℚ) ^ (d - 1) ≤ (c * (s : ℚ)) * (s : ℚ) ^ (d - 1) :=
          mul_le_mul_of_nonneg_right hBc (pow_nonneg (le_of_lt hs_pos) _)
        _ = c * ((s : ℚ) ^ (d - 1) * (s : ℚ)) := by ring
        _ = c * (s : ℚ) ^ d := by rw [← pow_succ, Nat.sub_add_cancel hdeg_pos]
    change 0 ≤ (∑ k ∈ Finset.range d, p.coeff k * (s : ℚ) ^ k) + c * (s : ℚ) ^ d
    linarith

private lemma coeff_comp_add_C (p : ℚ[X]) (a : ℚ) (k : ℕ) :
    (p.comp (Polynomial.X + Polynomial.C a)).coeff k =
      ∑ j ∈ Finset.range (p.natDegree + 1),
        if k ≤ j then p.coeff j * (j.choose k : ℚ) * a ^ (j - k) else 0 := by
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow p]
  rw [Polynomial.sum_comp, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
    add_pow, Polynomial.coeff_C_mul, Polynomial.finsetSum_coeff]
  have hterm : ∀ i : ℕ,
      ((Polynomial.X : ℚ[X]) ^ i * Polynomial.C a ^ (j - i) * (j.choose i : ℚ[X])).coeff k =
        if k = i then (j.choose i : ℚ) * a ^ (j - i) else 0 := by
    intro i
    have heq : (Polynomial.X : ℚ[X]) ^ i * Polynomial.C a ^ (j - i) * (j.choose i : ℚ[X]) =
        Polynomial.C ((j.choose i : ℚ) * a ^ (j - i)) * Polynomial.X ^ i := by
      rw [← Polynomial.C_pow, ← Polynomial.C_eq_natCast, Polynomial.C_mul]
      ring
    rw [heq, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs <;> ring
  simp_rw [hterm]
  by_cases hkj : k ≤ j
  · simp only [hkj, ↓reduceIte]
    have hmem : k ∈ Finset.range (j + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hkj)
    rw [Finset.sum_eq_single k]
    · simp only [↓reduceIte]; ring
    · intro i _ hik; simp [hik.symm]
    · intro hnot; exact absurd hmem hnot
  · simp only [hkj, ↓reduceIte]
    have hzero : ∀ i ∈ Finset.range (j + 1),
        (if k = i then (j.choose i : ℚ) * a ^ (j - i) else 0) = 0 := by
      intro i hi
      have hki : k ≠ i := by
        have := Finset.mem_range.1 hi
        omega
      simp [hki]
    rw [Finset.sum_eq_zero hzero, mul_zero]

private lemma exists_nat_comp_add_C_nonneg_coeffs (p : ℚ[X])
    (hp : p = 0 ∨ 0 < p.leadingCoeff) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s → ∀ k : ℕ,
      0 ≤ (p.comp (Polynomial.X + Polynomial.C (s : ℚ))).coeff k := by
  rcases hp with rfl | hpos
  · exact ⟨0, fun _ _ _ ↦ by simp⟩
  · set d := p.natDegree
    have hpoly : ∀ k ≤ d,
        ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
          0 ≤ (p.comp (Polynomial.X + Polynomial.C (s : ℚ))).coeff k := by
      intro k hk
      let Q : ℚ[X] := ∑ j ∈ Finset.range (d + 1),
        if k ≤ j then Polynomial.C (p.coeff j * (j.choose k : ℚ)) * Polynomial.X ^ (j - k) else 0
      have hQ_eval : ∀ s : ℕ, Q.eval (s : ℚ) =
          (p.comp (Polynomial.X + Polynomial.C (s : ℚ))).coeff k := by
        intro s
        rw [coeff_comp_add_C]
        change (Polynomial.evalRingHom (s : ℚ)) Q = _
        simp only [Q, map_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        split_ifs <;> simp
      have hQ_deg_le : Q.natDegree ≤ d - k := by
        refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj ↦ ?_
        have hjd : j ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        split_ifs
        · refine le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_
          omega
        · simp
      have hQ_coeff_top : Q.coeff (d - k) = p.leadingCoeff * (d.choose k : ℚ) := by
        simp only [Q, Polynomial.finsetSum_coeff]
        rw [Finset.sum_eq_single d]
        · simp only [hk, ↓reduceIte, Polynomial.coeff_C_mul_X_pow]
          rw [Polynomial.leadingCoeff]
        · intro j hj hjd
          split_ifs with hkj
          · have hlt : j < d := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) hjd
            have hne : d - k ≠ j - k := by omega
            simp only [Polynomial.coeff_C_mul_X_pow, hne, ↓reduceIte]
          · simp
        · intro hnot; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self d)) hnot
      have hQ_top_pos : 0 < Q.coeff (d - k) := by
        rw [hQ_coeff_top]
        exact mul_pos hpos (by exact_mod_cast Nat.choose_pos hk)
      have hQ_deg : Q.natDegree = d - k :=
        le_antisymm hQ_deg_le (Polynomial.le_natDegree_of_ne_zero (ne_of_gt hQ_top_pos))
      have hQ_lead : 0 < Q.leadingCoeff := by
        rw [Polynomial.leadingCoeff, hQ_deg]
        exact hQ_top_pos
      obtain ⟨N, hN⟩ := exists_nat_eval_nonneg_of_leadingCoeff_pos hQ_lead
      exact ⟨N, fun s hs ↦ by rw [← hQ_eval s]; exact hN s hs⟩
    choose N hN using hpoly
    refine ⟨(Finset.range (d + 1)).sup fun k ↦ if hk : k ≤ d then N k hk else 0, fun s hs k ↦ ?_⟩
    by_cases hk : k ≤ d
    · apply hN k hk s
      refine le_trans ?_ hs
      have hmem : k ∈ Finset.range (d + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hk)
      simpa [hk] using Finset.le_sup (f := fun j ↦ if hj : j ≤ d then N j hj else 0) hmem
    · rw [coeff_comp_add_C]
      refine le_of_eq (Finset.sum_eq_zero fun j hj ↦ ?_).symm
      have hjd : j ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hnot : ¬ k ≤ j := by omega
      simp [hnot]

/-- Every quasipolynomial whose nonzero constituent polynomials have positive leading coefficients
has a finite positivity index. -/
theorem hasPositivityIndex_of_leadingCoeff_pos (f : Quasipolynomial)
    (hlead : ∀ r : Fin f.period, f.constituent r = 0 ∨ 0 < (f.constituent r).leadingCoeff) :
    f.HasPositivityIndex := by
  have h1 : ∀ r : Fin f.period, ∃ N : ℕ, ∀ s : ℕ, N ≤ s → ∀ k : ℕ,
      0 ≤ ((f.constituent r).comp (Polynomial.X + Polynomial.C (s : ℚ))).coeff k :=
    fun r ↦ exists_nat_comp_add_C_nonneg_coeffs (f.constituent r) (hlead r)
  choose N hN using h1
  refine ⟨Finset.univ.sup N, fun r k ↦ ?_⟩
  set r' : Fin f.period := ⟨(r.1 + Finset.univ.sup N) % f.period, Nat.mod_lt _ f.period_pos⟩
  exact hN r' (Finset.univ.sup N) (Finset.le_sup (Finset.mem_univ r')) k

/-- A quasipolynomial is strictly saturated if on every residue class whose constituent polynomial
is nonzero, `f(n) > 0` for all `n ≥ 1`. -/
def IsStrictlySaturated (f : Quasipolynomial) : Prop :=
  ∀ n : ℕ, 1 ≤ n → f.constituentMod n ≠ 0 → 0 < f.eval n

theorem isStrictlySaturated_iff (f : Quasipolynomial) :
    f.IsStrictlySaturated ↔ ∀ n : ℕ, 1 ≤ n → f.constituentMod n ≠ 0 → 0 < f.eval n := by rfl

theorem IsStrictlySaturated.of_eval_eq {f g : Quasipolynomial}
    (heq : ∀ n, f.eval n = g.eval n) (hf : f.IsStrictlySaturated) : g.IsStrictlySaturated := by
  intro n hn hne
  rw [← heq n]
  apply hf n hn
  rwa [constituentMod_eq_of_eval_eq heq n]

/-- Strict positivity implies strict saturation. -/
theorem IsStrictlyPositive.isStrictlySaturated {f : Quasipolynomial}
    (hf : f.IsStrictlyPositive) : f.IsStrictlySaturated := by
  intro n hn hne
  rw [eval_eq_constituentMod_eval]
  set p := f.constituentMod n
  have hnonneg : ∀ k, 0 ≤ p.coeff k := fun k ↦ (f.isStrictlyPositive_iff_constituentMod.1 hf) n k
  have hne_coeff : ∃ k ∈ Finset.range (p.natDegree + 1), p.coeff k ≠ 0 :=
    ⟨p.natDegree, Finset.mem_range.2 (Nat.lt_succ_self _), Polynomial.leadingCoeff_ne_zero.2 hne⟩
  rcases hne_coeff with ⟨k₀, hk₀, hck₀⟩
  have hpos_term : 0 < p.coeff k₀ * (n : ℚ) ^ k₀ := by
    have hck₀_pos : 0 < p.coeff k₀ := lt_of_le_of_ne (hnonneg k₀) (Ne.symm hck₀)
    have hn_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
    exact mul_pos hck₀_pos (pow_pos hn_pos k₀)
  rw [Polynomial.eval_eq_sum_range]
  refine lt_of_lt_of_le hpos_term ?_
  exact Finset.single_le_sum (f := fun k ↦ p.coeff k * (n : ℚ) ^ k)
    (fun k _ ↦ mul_nonneg (hnonneg k) (pow_nonneg (Nat.cast_nonneg n) k)) hk₀

/-- Existence of a finite saturation shift. -/
def HasSaturationIndex (f : Quasipolynomial) : Prop :=
  ∃ s : ℕ, (f.shift s).IsStrictlySaturated

theorem hasSaturationIndex_iff (f : Quasipolynomial) :
    f.HasSaturationIndex ↔ ∃ s : ℕ, (f.shift s).IsStrictlySaturated := by rfl

/-- The saturation index of `f`: the smallest `s : ℕ` such that `f.shift s` is strictly saturated,
or `0` if none exists. -/
noncomputable def saturationIndex (f : Quasipolynomial) : ℕ := by
  classical
  exact if h : f.HasSaturationIndex then Nat.find h else 0

theorem shift_saturationIndex_isStrictlySaturated {f : Quasipolynomial}
    (h : f.HasSaturationIndex) : (f.shift f.saturationIndex).IsStrictlySaturated := by
  classical
  simp only [saturationIndex, h, ↓reduceDIte]
  exact Nat.find_spec h

theorem saturationIndex_le {f : Quasipolynomial} {s : ℕ}
    (hs : (f.shift s).IsStrictlySaturated) : f.saturationIndex ≤ s := by
  classical
  have hex : f.HasSaturationIndex := ⟨s, hs⟩
  simp only [saturationIndex, hex, ↓reduceDIte]
  exact Nat.find_min' hex hs

theorem saturationIndex_eq_zero_iff {f : Quasipolynomial} (h : f.HasSaturationIndex) :
    f.saturationIndex = 0 ↔ f.IsStrictlySaturated := by
  constructor
  · intro h0
    have hs := f.shift_saturationIndex_isStrictlySaturated h
    rw [h0] at hs
    refine IsStrictlySaturated.of_eval_eq (fun n ↦ ?_) hs
    simp
  · intro hf
    have h0 : (f.shift 0).IsStrictlySaturated :=
      IsStrictlySaturated.of_eval_eq (fun n ↦ by simp) hf
    exact Nat.eq_zero_of_le_zero (f.saturationIndex_le h0)

/-- The saturation index depends only on `f.eval`, not on the choice of period. -/
theorem saturationIndex_eq_of_eval_eq {f g : Quasipolynomial} (h : ∀ n, f.eval n = g.eval n) :
    f.saturationIndex = g.saturationIndex := by
  classical
  have hshift : ∀ s, (f.shift s).IsStrictlySaturated ↔ (g.shift s).IsStrictlySaturated :=
    fun s ↦ ⟨IsStrictlySaturated.of_eval_eq (fun n ↦ by simp [h]),
      IsStrictlySaturated.of_eval_eq (fun n ↦ by simp [h])⟩
  have hex : f.HasSaturationIndex ↔ g.HasSaturationIndex := exists_congr hshift
  by_cases hf : f.HasSaturationIndex
  · have hg : g.HasSaturationIndex := hex.1 hf
    simp only [saturationIndex, hf, hg, ↓reduceDIte]
    exact le_antisymm
      (Nat.find_min' hf ((hshift _).2 (Nat.find_spec hg)))
      (Nat.find_min' hg ((hshift _).1 (Nat.find_spec hf)))
  · have hg : ¬ g.HasSaturationIndex := mt hex.2 hf
    simp [saturationIndex, hf, hg]

/-- If `f.shift s` is strictly saturated, then `f(c) > 0` for every `c > s` on a nonzero residue
class. -/
theorem eval_pos_of_gt_saturationIndex {f : Quasipolynomial} {s c : ℕ}
    (hs : (f.shift s).IsStrictlySaturated) (hc : s < c) (hne : f.constituentMod c ≠ 0) :
    0 < f.eval c := by
  have h1 : 1 ≤ c - s := Nat.sub_pos_of_lt hc
  have hadd : c - s + s = c := Nat.sub_add_cancel (le_of_lt hc)
  have hne' : (f.shift s).constituentMod (c - s) ≠ 0 := by
    rw [constituentMod_shift_ne_zero_iff, hadd]
    exact hne
  have hpos := hs (c - s) h1 hne'
  simpa [eval_shift, hadd] using hpos

/-- The saturation index is bounded above by the positivity index. -/
theorem saturationIndex_le_positivityIndex {f : Quasipolynomial} (h : f.HasPositivityIndex) :
    f.saturationIndex ≤ f.positivityIndex :=
  f.saturationIndex_le (f.shift_positivityIndex_isStrictlyPositive h).isStrictlySaturated

end Quasipolynomial

end CslibFrontier.Combinatorics
