/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.ComputableAnalysis.ComputableRat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.MetricSpace.Basic

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Computable Real Numbers and Computable Sequences of Reals

Classical Turing and Pour-El–Richards effective dyadic convergence, computable real numbers, and
uniformly computable single and double sequences of real numbers under standard Lean axioms.

## Main definitions

* `CslibFrontier.ComputableAnalysis.EffectivelyConvergesTo`: convergence of a real sequence with a
  computable dyadic error modulus `|L - x n| < 2 ^ (-M)` for `n ≥ e M`.
* `CslibFrontier.ComputableAnalysis.IsComputableReal`: computable real numbers, defined as effective
  limits of computable rational sequences.
* `CslibFrontier.ComputableAnalysis.computableRealSubfield`: the subfield of computable real
  numbers in
  `ℝ`.
* `CslibFrontier.ComputableAnalysis.IsComputableRealSeq`,
  `CslibFrontier.ComputableAnalysis.IsComputableRealDoubleSeq`: uniformly computable single and
  double
  sequences of real numbers.

## Main results

* `CslibFrontier.ComputableAnalysis.mem_computableRealSubfield_iff`: computable real numbers form a
  subfield of `ℝ`, also closed under `|·|`, `max`, `min`, `Real.sqrt`, and effective limits.
* `CslibFrontier.ComputableAnalysis.IsComputableRealSeq.div`,
  `CslibFrontier.ComputableAnalysis.IsComputableRealSeq.sqrt`,
  `CslibFrontier.ComputableAnalysis.IsComputableRealDoubleSeq.sum_range`,
  `CslibFrontier.ComputableAnalysis.IsComputableRealDoubleSeq.sup'_range`,
  `CslibFrontier.ComputableAnalysis.IsComputableRealDoubleSeq.inf'_range`,
  `CslibFrontier.ComputableAnalysis.IsComputableRealDoubleSeq.effectiveLimit`: uniform field,
  lattice,
  square-root, power, finite-sum, finite-extremum, and effective-limit closure.
-/

public section

namespace CslibFrontier.ComputableAnalysis

/-! ### Effective convergence and computable real numbers -/

/-- A real sequence `x : ℕ → ℝ` effectively converges to `L : ℝ` if there exists a total computable
modulus `e : ℕ → ℕ` such that `|L - x n| < 2 ^ (-M)` whenever `n ≥ e M`. -/
@[expose] def EffectivelyConvergesTo (x : ℕ → ℝ) (L : ℝ) : Prop :=
  ∃ e : ℕ → ℕ, Computable e ∧ ∀ M n : ℕ, e M ≤ n → |L - x n| < (2 : ℝ) ^ (-(M : ℤ))

/-- Constructing `EffectivelyConvergesTo` from an explicit computable dyadic error modulus. -/
theorem EffectivelyConvergesTo.mk {x : ℕ → ℝ} {L : ℝ} {e : ℕ → ℕ} (he : Computable e)
    (h : ∀ M n : ℕ, e M ≤ n → |L - x n| < (2 : ℝ) ^ (-(M : ℤ))) :
    EffectivelyConvergesTo x L :=
  ⟨e, he, h⟩

/-- Effective convergence follows from a non-strict dyadic error bound `|L - x n| ≤ 2 ^ (-M)`. -/
theorem effectivelyConvergesTo_of_le {x : ℕ → ℝ} {L : ℝ} {e : ℕ → ℕ} (he : Computable e)
    (h : ∀ M n : ℕ, e M ≤ n → |L - x n| ≤ (2 : ℝ) ^ (-(M : ℤ))) :
    EffectivelyConvergesTo x L :=
  ⟨fun M ↦ e (M + 1), he.comp Computable.succ,
    fun M n hn ↦ (h (M + 1) n hn).trans_lt (zpow_lt_zpow_right₀ one_lt_two (by omega))⟩

/-- Every sequence that effectively converges to `L` converges to `L` topologically. -/
theorem EffectivelyConvergesTo.tendsto {x : ℕ → ℝ} {L : ℝ} (h : EffectivelyConvergesTo x L) :
    Filter.Tendsto x Filter.atTop (nhds L) := by
  obtain ⟨e, _, he⟩ := h
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlim : Filter.Tendsto (fun M : ℕ ↦ (2 : ℝ) ^ (-(M : ℤ))) Filter.atTop (nhds 0) := by
    simpa only [one_div, inv_pow, zpow_neg, zpow_natCast] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hlim ε hε
  refine ⟨e M, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  have hM' : (2 : ℝ) ^ (-(M : ℤ)) < ε := by
    have h0 := hM M le_rfl
    rwa [Real.dist_eq, sub_zero, abs_of_pos (zpow_pos two_pos _)] at h0
  exact (he M n hn).trans hM'

/-- A real number `x : ℝ` is computable if there exists a computable rational sequence that
effectively converges to `x`. -/
@[expose] def IsComputableReal (x : ℝ) : Prop :=
  ∃ r : ℕ → ℚ, IsComputableRatSeq r ∧ EffectivelyConvergesTo (fun n ↦ (r n : ℝ)) x

/-- Rapid dyadic rational approximation characterization of computable real numbers. -/
theorem isComputableReal_iff_exists_rat_approx {x : ℝ} :
    IsComputableReal x ↔
      ∃ q : ℕ → ℚ, IsComputableRatSeq q ∧ ∀ M : ℕ, |x - (q M : ℝ)| < (2 : ℝ) ^ (-(M : ℤ)) := by
  constructor
  · rintro ⟨r, hr, e, he, hconv⟩
    exact ⟨fun M ↦ r (e M), hr.comp he, fun M ↦ hconv M (e M) le_rfl⟩
  · rintro ⟨q, hq, hconv⟩
    refine ⟨q, hq, id, .id, fun M n hn ↦ ?_⟩
    dsimp only [id] at hn
    exact (hconv n).trans_le (zpow_le_zpow_right₀ one_le_two (by omega))

/-- Non-strict rapid rational approximation criterion for `IsComputableReal`. -/
theorem isComputableReal_of_rat_le {x : ℝ} {q : ℕ → ℚ} (hq : IsComputableRatSeq q)
    (h : ∀ M : ℕ, |x - (q M : ℝ)| ≤ (2 : ℝ) ^ (-(M : ℤ))) : IsComputableReal x :=
  isComputableReal_iff_exists_rat_approx.mpr
    ⟨fun M ↦ q (M + 1), hq.comp Computable.succ, fun M ↦
      (h (M + 1)).trans_lt (zpow_lt_zpow_right₀ one_lt_two (by omega))⟩

/-- Every rational number is a computable real number. -/
@[simp] theorem isComputableReal_rat (q : ℚ) : IsComputableReal (q : ℝ) :=
  isComputableReal_iff_exists_rat_approx.mpr
    ⟨fun _ ↦ q, .const q, fun _ ↦ by rw [sub_self, abs_zero]; exact zpow_pos two_pos _⟩

/-- `0 : ℝ` is computable. -/
@[simp] theorem isComputableReal_zero : IsComputableReal 0 := by
  simpa using isComputableReal_rat 0

/-- `1 : ℝ` is computable. -/
@[simp] theorem isComputableReal_one : IsComputableReal 1 := by
  simpa using isComputableReal_rat 1

/-- Every natural number cast into `ℝ` is computable. -/
@[simp] theorem isComputableReal_nat (n : ℕ) : IsComputableReal (n : ℝ) := by
  simpa using isComputableReal_rat n

/-- Every integer cast into `ℝ` is computable. -/
@[simp] theorem isComputableReal_int (z : ℤ) : IsComputableReal (z : ℝ) := by
  simpa using isComputableReal_rat z

/-! ### Uniformly computable single and double sequences of real numbers -/

/-- A sequence of real numbers `x : ℕ → ℝ` is computable if there exist a computable double
sequence `r : ℕ → ℕ → ℚ` of rationals and a computable modulus `e : ℕ → ℕ → ℕ` such that
`|x n - r n m| < 2 ^ (-M)` whenever `m ≥ e n M`. -/
@[expose] def IsComputableRealSeq (x : ℕ → ℝ) : Prop :=
  ∃ (r : ℕ → ℕ → ℚ) (e : ℕ → ℕ → ℕ),
    IsComputableRatMap₂ r ∧ Computable₂ e ∧
    ∀ n M m : ℕ, e n M ≤ m → |x n - (r n m : ℝ)| < (2 : ℝ) ^ (-(M : ℤ))

/-- A double sequence of real numbers `x : ℕ → ℕ → ℝ` is computable if its unpairing via
Cantor's pairing bijection `Nat.unpair : ℕ → ℕ × ℕ` is a computable sequence of real numbers. -/
abbrev IsComputableRealDoubleSeq (x : ℕ → ℕ → ℝ) : Prop :=
  IsComputableRealSeq (Nat.unpaired x)

/-- Rapid rational approximation characterization of computable sequences of real numbers. -/
theorem isComputableRealSeq_iff_exists_rat_approx {x : ℕ → ℝ} :
    IsComputableRealSeq x ↔
      ∃ q : ℕ → ℕ → ℚ, IsComputableRatMap₂ q ∧
        ∀ n M : ℕ, |x n - (q n M : ℝ)| < (2 : ℝ) ^ (-(M : ℤ)) := by
  constructor
  · rintro ⟨r, e, hr, he, hconv⟩
    exact ⟨fun n M ↦ r n (e n M), (hr.comp .fst he).to₂, fun n M ↦ hconv n M (e n M) le_rfl⟩
  · rintro ⟨q, hq, hconv⟩
    refine ⟨q, fun _ M ↦ M, hq, Computable.snd.to₂, fun n M m hm ↦ ?_⟩
    dsimp only at hm
    exact (hconv n m).trans_le (zpow_le_zpow_right₀ one_le_two (by omega))

/-- Non-strict rapid rational approximation criterion for `IsComputableRealSeq`. -/
theorem isComputableRealSeq_of_rat_le {x : ℕ → ℝ} {q : ℕ → ℕ → ℚ} (hq : IsComputableRatMap₂ q)
    (h : ∀ n M : ℕ, |x n - (q n M : ℝ)| ≤ (2 : ℝ) ^ (-(M : ℤ))) :
    IsComputableRealSeq x :=
  isComputableRealSeq_iff_exists_rat_approx.mpr
    ⟨fun n M ↦ q n (M + 1), (hq.comp .fst (Computable.succ.comp .snd)).to₂,
      fun n M ↦ (h n (M + 1)).trans_lt (zpow_lt_zpow_right₀ one_lt_two (by omega))⟩

/-- Rapid rational approximation characterization of computable double sequences of reals. -/
theorem isComputableRealDoubleSeq_iff_exists_rat_approx {x : ℕ → ℕ → ℝ} :
    IsComputableRealDoubleSeq x ↔
      ∃ q : ℕ × ℕ → ℕ → ℚ, IsComputableRatMap₂ q ∧
        ∀ n k M : ℕ, |x n k - (q (n, k) M : ℝ)| < (2 : ℝ) ^ (-(M : ℤ)) := by
  rw [IsComputableRealDoubleSeq, isComputableRealSeq_iff_exists_rat_approx]
  constructor
  · rintro ⟨q, hq, hconv⟩
    refine ⟨fun p M ↦ q (Nat.pair p.1 p.2) M,
      (hq.comp (Primrec₂.natPair.to_comp.comp (Computable.fst.comp .fst)
        (Computable.snd.comp .fst)) .snd).to₂,
      fun n k M ↦ ?_⟩
    simpa [Nat.unpaired, Nat.unpair_pair] using hconv (Nat.pair n k) M
  · rintro ⟨q, hq, hconv⟩
    exact ⟨fun i M ↦ q i.unpair M, (hq.comp (Computable.unpair.comp .fst) .snd).to₂,
      fun i M ↦ hconv i.unpair.1 i.unpair.2 M⟩

/-- Non-strict rapid rational approximation criterion for `IsComputableRealDoubleSeq`. -/
theorem isComputableRealDoubleSeq_of_rat_le {x : ℕ → ℕ → ℝ} {q : ℕ × ℕ → ℕ → ℚ}
    (hq : IsComputableRatMap₂ q)
    (h : ∀ n k M : ℕ, |x n k - (q (n, k) M : ℝ)| ≤ (2 : ℝ) ^ (-(M : ℤ))) :
    IsComputableRealDoubleSeq x :=
  isComputableRealDoubleSeq_iff_exists_rat_approx.mpr
    ⟨fun p M ↦ q p (M + 1), (hq.comp .fst (Computable.succ.comp .snd)).to₂,
      fun n k M ↦ (h n k (M + 1)).trans_lt (zpow_lt_zpow_right₀ one_lt_two (by omega))⟩

/-- A constant real sequence is computable if and only if its value is a computable real. -/
theorem isComputableRealSeq_const_iff {c : ℝ} :
    IsComputableRealSeq (fun _ ↦ c) ↔ IsComputableReal c := by
  rw [isComputableRealSeq_iff_exists_rat_approx, isComputableReal_iff_exists_rat_approx]
  exact ⟨fun ⟨q, hq, hc⟩ ↦ ⟨q 0, hq.comp (.const 0) .id, hc 0⟩,
    fun ⟨q, hq, hc⟩ ↦ ⟨fun _ M ↦ q M, (hq.comp .snd).to₂, fun _ ↦ hc⟩⟩

/-- Constant sequence of a computable real number. -/
theorem IsComputableReal.constSeq {c : ℝ} (hc : IsComputableReal c) :
    IsComputableRealSeq fun _ ↦ c :=
  isComputableRealSeq_const_iff.mpr hc

/-- Constant double sequence of a computable real number. -/
theorem IsComputableReal.constDoubleSeq {c : ℝ} (hc : IsComputableReal c) :
    IsComputableRealDoubleSeq fun _ _ ↦ c :=
  hc.constSeq

/-- Every entry of a computable sequence of real numbers is a computable real number. -/
theorem IsComputableRealSeq.apply {x : ℕ → ℝ} (hx : IsComputableRealSeq x) (n : ℕ) :
    IsComputableReal (x n) := by
  obtain ⟨q, hq, hconv⟩ := isComputableRealSeq_iff_exists_rat_approx.mp hx
  exact isComputableReal_iff_exists_rat_approx.mpr ⟨q n, hq.comp (.const n) .id, hconv n⟩

/-- Computable sequences of reals are closed under precomposition with computable index maps. -/
theorem IsComputableRealSeq.comp {x : ℕ → ℝ} (hx : IsComputableRealSeq x) {g : ℕ → ℕ}
    (hg : Computable g) : IsComputableRealSeq fun n ↦ x (g n) := by
  obtain ⟨q, hq, hconv⟩ := isComputableRealSeq_iff_exists_rat_approx.mp hx
  exact isComputableRealSeq_iff_exists_rat_approx.mpr
    ⟨fun n M ↦ q (g n) M, (hq.comp (hg.comp .fst) .snd).to₂, fun n M ↦ hconv (g n) M⟩

/-- Composing a computable real sequence with a binary computable index map yields a computable
double sequence. -/
theorem IsComputableRealSeq.comp₂ {x : ℕ → ℝ} (hx : IsComputableRealSeq x) {g : ℕ → ℕ → ℕ}
    (hg : Computable₂ g) : IsComputableRealDoubleSeq fun n k ↦ x (g n k) :=
  hx.comp (hg.comp (Computable.fst.comp .unpair) (Computable.snd.comp .unpair))

/-- Pointwise equality preserves `IsComputableRealSeq`. -/
theorem IsComputableRealSeq.of_eq {x y : ℕ → ℝ} (hx : IsComputableRealSeq x)
    (h : ∀ n, x n = y n) : IsComputableRealSeq y :=
  funext h ▸ hx

/-- Every row of a computable double sequence is a computable sequence. -/
theorem IsComputableRealDoubleSeq.row {x : ℕ → ℕ → ℝ} (hx : IsComputableRealDoubleSeq x) (n : ℕ) :
    IsComputableRealSeq (x n) :=
  (hx.comp (Primrec₂.natPair.to_comp.comp (.const n) .id)).of_eq fun k ↦ by
    simp [Nat.unpaired, Nat.unpair_pair]

/-- Every computable rational sequence defines a computable real sequence. -/
theorem isComputableRealSeq_rat {r : ℕ → ℚ} (hr : IsComputableRatSeq r) :
    IsComputableRealSeq fun n ↦ (r n : ℝ) :=
  isComputableRealSeq_iff_exists_rat_approx.mpr
    ⟨fun n _ ↦ r n, (hr.comp .fst).to₂,
      fun _ _ ↦ by rw [sub_self, abs_zero]; exact zpow_pos two_pos _⟩

/-- Every computable rational double sequence defines a computable real double sequence. -/
theorem isComputableRealDoubleSeq_rat {r : ℕ → ℕ → ℚ} (hr : IsComputableRatMap₂ r) :
    IsComputableRealDoubleSeq fun n k ↦ (r n k : ℝ) :=
  isComputableRealSeq_rat <| hr.comp (Computable.fst.comp .unpair) (Computable.snd.comp .unpair)

/-- Every computable natural-number sequence defines a computable real sequence. -/
theorem isComputableRealSeq_nat {f : ℕ → ℕ} (hf : Computable f) :
    IsComputableRealSeq fun n ↦ (f n : ℝ) := by
  simpa using isComputableRealSeq_rat (IsComputableRatMap.ofNat hf)

/-- Every computable natural-number double sequence defines a computable real double sequence. -/
theorem isComputableRealDoubleSeq_nat {f : ℕ → ℕ → ℕ} (hf : Computable₂ f) :
    IsComputableRealDoubleSeq fun n k ↦ (f n k : ℝ) :=
  isComputableRealDoubleSeq_rat (IsComputableRatMap.ofNat hf).to₂

/-- Every computable integer sequence defines a computable real sequence. -/
theorem isComputableRealSeq_int {f : ℕ → ℤ} (hf : Computable f) :
    IsComputableRealSeq fun n ↦ (f n : ℝ) := by
  simpa using isComputableRealSeq_rat (IsComputableRatMap.ofInt hf)

/-- A computable `{0, 1}`-valued indicator sequence is a computable real sequence. -/
theorem isComputableRealSeq_indicator {p : ℕ → Bool} (hp : Computable p) :
    IsComputableRealSeq fun n ↦ if p n = true then (1 : ℝ) else 0 :=
  (isComputableRealSeq_rat (IsComputableRatMap.ite hp (.const 1) (.const 0))).of_eq fun n ↦ by
    cases p n <;> simp

/-- A computable `{0, 1}`-valued binary indicator is a computable real double sequence. -/
theorem isComputableRealDoubleSeq_indicator {p : ℕ → ℕ → Bool} (hp : Computable₂ p) :
    IsComputableRealDoubleSeq fun n k ↦ if p n k = true then (1 : ℝ) else 0 :=
  (isComputableRealDoubleSeq_rat (IsComputableRatMap.ite hp (.const 1) (.const 0)).to₂).of_eq
    fun i ↦ by dsimp only [Nat.unpaired]; cases p i.unpair.1 i.unpair.2 <;> simp

/-- Prepending a computable real to a computable sequence yields a computable sequence. -/
theorem IsComputableRealSeq.cons {c : ℝ} {x : ℕ → ℝ} (hc : IsComputableReal c)
    (hx : IsComputableRealSeq x) :
    IsComputableRealSeq (fun n ↦ @Nat.casesOn (fun _ ↦ ℝ) n c x) := by
  obtain ⟨qc, hqc, hcc⟩ := isComputableReal_iff_exists_rat_approx.mp hc
  obtain ⟨qx, hqx, hcx⟩ := isComputableRealSeq_iff_exists_rat_approx.mp hx
  have hq : IsComputableRatMap₂ fun n M ↦ @Nat.casesOn (fun _ ↦ ℚ) n (qc M) (fun k ↦ qx k M) :=
    isComputableRatMap_iff_ratEncode.mpr <|
      (Computable.nat_casesOn .fst (hqc.ratEncode.comp .snd)
        ((IsComputableRatMap.ratEncode hqx).comp
          (.pair .snd (Computable.snd.comp .fst))).to₂).of_eq
        fun ⟨n, _⟩ ↦ by cases n <;> rfl
  exact isComputableRealSeq_iff_exists_rat_approx.mpr
    ⟨_, hq, fun n M ↦ by cases n with | zero => exact hcc M | succ k => exact hcx k M⟩

/-- Termwise negation of a computable real sequence is computable. -/
theorem IsComputableRealSeq.neg {x : ℕ → ℝ} (hx : IsComputableRealSeq x) :
    IsComputableRealSeq fun n ↦ -x n := by
  obtain ⟨q, hq, hc⟩ := isComputableRealSeq_iff_exists_rat_approx.mp hx
  refine isComputableRealSeq_iff_exists_rat_approx.mpr ⟨fun n M ↦ -q n M, hq.neg.to₂, fun n M ↦ ?_⟩
  push_cast; rw [show -x n - -(q n M : ℝ) = -(x n - (q n M : ℝ)) by ring, abs_neg]
  exact hc n M

private lemma zpow_neg_succ_add (M : ℕ) :
    (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) + (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) = (2 : ℝ) ^ (-(M : ℤ)) := by
  rw [← two_mul, show (2 : ℝ) * (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) =
    (2 : ℝ) ^ (1 : ℤ) * (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) by rw [zpow_one],
    ← zpow_add₀ two_ne_zero]
  congr 1; push_cast; omega

/-- Termwise addition of computable real sequences is computable. -/
theorem IsComputableRealSeq.add {x y : ℕ → ℝ} (hx : IsComputableRealSeq x)
    (hy : IsComputableRealSeq y) : IsComputableRealSeq fun n ↦ x n + y n := by
  obtain ⟨qx, hqx, hcx⟩ := isComputableRealSeq_iff_exists_rat_approx.mp hx
  obtain ⟨qy, hqy, hcy⟩ := isComputableRealSeq_iff_exists_rat_approx.mp hy
  have hm1 : Computable fun p : ℕ × ℕ ↦ p.2 + 1 := Computable.succ.comp .snd
  refine isComputableRealSeq_iff_exists_rat_approx.mpr
    ⟨fun n M ↦ qx n (M + 1) + qy n (M + 1),
      ((hqx.comp .fst hm1).add (hqy.comp .fst hm1)).to₂, fun n M ↦ ?_⟩
  push_cast
  calc |(x n + y n) - ((qx n (M + 1) : ℝ) + (qy n (M + 1) : ℝ))|
      = |(x n - (qx n (M + 1) : ℝ)) + (y n - (qy n (M + 1) : ℝ))| := by ring_nf
    _ ≤ |x n - (qx n (M + 1) : ℝ)| + |y n - (qy n (M + 1) : ℝ)| := abs_add_le _ _
    _ < (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) + (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) :=
        add_lt_add (hcx n (M + 1)) (hcy n (M + 1))
    _ = (2 : ℝ) ^ (-(M : ℤ)) := zpow_neg_succ_add M

/-- Termwise subtraction of computable real sequences is computable. -/
theorem IsComputableRealSeq.sub {x y : ℕ → ℝ} (hx : IsComputableRealSeq x)
    (hy : IsComputableRealSeq y) : IsComputableRealSeq fun n ↦ x n - y n := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

/-- Upper bound `|(q : ℝ)| ≤ q.num.natAbs` for any rational number. -/
theorem abs_rat_le_natAbs_num (q : ℚ) : |(q : ℝ)| ≤ (q.num.natAbs : ℝ) := by
  conv_lhs => rw [← q.num_div_den]
  push_cast
  have hpos : (0 : ℝ) < (q.den : ℝ) := Nat.cast_pos.mpr q.den_pos
  have hna : |(q.num : ℝ)| = (q.num.natAbs : ℝ) := by
    rcases le_or_gt 0 q.num with h0 | h0
    · rw [abs_of_nonneg (by exact_mod_cast h0)]
      simpa only [Int.cast_natCast] using congrArg (Int.cast : ℤ → ℝ) (Int.natAbs_of_nonneg h0).symm
    · rw [abs_of_neg (Int.cast_lt_zero.mpr h0)]
      simpa only [Int.cast_natCast, Int.cast_neg] using
        congrArg (Int.cast : ℤ → ℝ) (Int.ofNat_natAbs_of_nonpos h0.le).symm
  have hd1 : 1 ≤ q.den := q.den_pos
  rw [abs_div, abs_of_pos hpos, hna]
  exact div_le_self (Nat.cast_nonneg _) (Nat.one_le_cast.mpr hd1)

/-- Every computable sequence of reals admits a computable natural-number upper bound
`|x n| ≤ B n`. -/
theorem IsComputableRealSeq.exists_nat_bound {x : ℕ → ℝ} (hx : IsComputableRealSeq x) :
    ∃ B : ℕ → ℕ, Computable B ∧ ∀ n : ℕ, |x n| ≤ (B n : ℝ) := by
  obtain ⟨q, hq, hc⟩ := isComputableRealSeq_iff_exists_rat_approx.mp hx
  refine ⟨fun n ↦ (q n 0).num.natAbs + 1,
    Computable.succ.comp (primrec_int_natAbs.to_comp.comp (hq.comp .id (.const 0)).num),
    fun n ↦ ?_⟩
  have h0 : |x n - (q n 0 : ℝ)| < 1 := by simpa using hc n 0
  have h1 : |x n| ≤ |x n - (q n 0 : ℝ)| + |(q n 0 : ℝ)| := by
    simpa using abs_add_le (x n - (q n 0 : ℝ)) (q n 0 : ℝ)
  push_cast
  linarith [abs_rat_le_natAbs_num (q n 0)]

/-- Termwise multiplication of computable real sequences is computable. -/
theorem IsComputableRealSeq.mul {x y : ℕ → ℝ} (hx : IsComputableRealSeq x)
    (hy : IsComputableRealSeq y) : IsComputableRealSeq fun n ↦ x n * y n := by
  obtain ⟨qx, hqx, hcx⟩ := isComputableRealSeq_iff_exists_rat_approx.mp hx
  obtain ⟨qy, hqy, hcy⟩ := isComputableRealSeq_iff_exists_rat_approx.mp hy
  let B : ℕ → ℕ := fun n ↦ (qx n 0).num.natAbs + (qy n 0).num.natAbs + 2
  let K : ℕ → ℕ → ℕ := fun n M ↦ M + B n + 1
  have hB : Computable B :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp
        (primrec_int_natAbs.to_comp.comp (hqx.comp .id (.const 0)).num)
        (primrec_int_natAbs.to_comp.comp (hqy.comp .id (.const 0)).num))
      (.const 2)
  have hK : Computable fun p : ℕ × ℕ ↦ K p.1 p.2 :=
    Computable.succ.comp (Primrec.nat_add.to_comp.comp .snd (hB.comp .fst))
  refine isComputableRealSeq_iff_exists_rat_approx.mpr
    ⟨fun n M ↦ qx n (K n M) * qy n (K n M),
      ((hqx.comp .fst hK).mul (hqy.comp .fst hK)).to₂, fun n M ↦ ?_⟩
  have hBpow : (B n : ℝ) ≤ (2 : ℝ) ^ (B n) := by exact_mod_cast Nat.lt_two_pow_self.le
  have hBc : (B n : ℝ) = ((qx n 0).num.natAbs : ℝ) + ((qy n 0).num.natAbs : ℝ) + 2 := by
    dsimp [B]; push_cast; ring
  have hxB : |x n| ≤ (2 : ℝ) ^ (B n) := by
    have h0 : |x n - (qx n 0 : ℝ)| < 1 := by simpa using hcx n 0
    have h1 : |x n| ≤ |x n - (qx n 0 : ℝ)| + |(qx n 0 : ℝ)| := by
      simpa using abs_add_le (x n - (qx n 0 : ℝ)) (qx n 0 : ℝ)
    linarith [abs_rat_le_natAbs_num (qx n 0), Nat.cast_nonneg (α := ℝ) (qy n 0).num.natAbs]
  have hqyB : |(qy n (K n M) : ℝ)| ≤ (2 : ℝ) ^ (B n) := by
    have h0 : |y n - (qy n 0 : ℝ)| < 1 := by simpa using hcy n 0
    have hk : |y n - (qy n (K n M) : ℝ)| < 1 :=
      (hcy n (K n M)).trans_le (zpow_le_one_of_nonpos₀ one_le_two
        (neg_nonpos.mpr (Nat.cast_nonneg _)))
    have ht1 : |(qy n (K n M) : ℝ)| ≤ |(qy n (K n M) : ℝ) - y n| + |y n| := by
      simpa using abs_add_le ((qy n (K n M) : ℝ) - y n) (y n)
    have ht2 : |y n| ≤ |y n - (qy n 0 : ℝ)| + |(qy n 0 : ℝ)| := by
      simpa using abs_add_le (y n - (qy n 0 : ℝ)) (qy n 0 : ℝ)
    rw [abs_sub_comm] at ht1
    linarith [abs_rat_le_natAbs_num (qy n 0), Nat.cast_nonneg (α := ℝ) (qx n 0).num.natAbs]
  have hprod : (2 : ℝ) ^ (B n) * (2 : ℝ) ^ (-(K n M : ℤ)) = (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) := by
    rw [← zpow_natCast (2 : ℝ) (B n), ← zpow_add₀ two_ne_zero]
    congr 1; dsimp [K]; omega
  push_cast
  calc |x n * y n - (qx n (K n M) : ℝ) * (qy n (K n M) : ℝ)|
      = |x n * (y n - (qy n (K n M) : ℝ)) + (x n - (qx n (K n M) : ℝ)) * (qy n (K n M) : ℝ)| := by
        ring_nf
    _ ≤ |x n| * |y n - (qy n (K n M) : ℝ)| + |x n - (qx n (K n M) : ℝ)| * |(qy n (K n M) : ℝ)| := by
        simpa [abs_mul] using abs_add_le (x n * (y n - (qy n (K n M) : ℝ)))
          ((x n - (qx n (K n M) : ℝ)) * (qy n (K n M) : ℝ))
    _ < (2 : ℝ) ^ (B n) * (2 : ℝ) ^ (-(K n M : ℤ)) +
          (2 : ℝ) ^ (-(K n M : ℤ)) * (2 : ℝ) ^ (B n) := by
        have h2B : (0 : ℝ) < (2 : ℝ) ^ (B n) := pow_pos two_pos _
        exact add_lt_add
          (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hxB (abs_nonneg _))
            (mul_lt_mul_of_pos_left (hcy n (K n M)) h2B))
          (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hqyB (abs_nonneg _))
            (mul_lt_mul_of_pos_right (hcx n (K n M)) h2B))
    _ = (2 : ℝ) ^ (-(M : ℤ)) := by
      rw [mul_comm ((2 : ℝ) ^ (-(K n M : ℤ))), hprod, zpow_neg_succ_add]

/-- Termwise reciprocal of a nowhere-vanishing computable real sequence is computable. -/
theorem IsComputableRealSeq.inv {x : ℕ → ℝ} (hx : IsComputableRealSeq x) (hne : ∀ n, x n ≠ 0) :
    IsComputableRealSeq fun n ↦ (x n)⁻¹ := by
  obtain ⟨q, hq, hc⟩ := isComputableRealSeq_iff_exists_rat_approx.mp hx
  let sep : ℕ → ℕ → Bool := fun n k ↦ decide ((2 : ℚ) ^ (1 - (k : ℤ)) < |q n k|)
  have hsep : Computable₂ sep :=
    (((IsComputableRatMap.const (2 : ℚ)).zpow
      (primrec_int_sub.to_comp.comp (.const 1)
        (primrec_int_ofNat.to_comp.comp .snd))).decide_lt hq.abs).to₂
  have hex : ∀ n : ℕ, ∃ k : ℕ, sep n k = true := fun n ↦ by
    have hpos : 0 < |x n| := abs_pos.mpr (hne n)
    have hlim : Filter.Tendsto (fun k : ℕ ↦ (3 : ℝ) * (2 : ℝ) ^ (-(k : ℤ))) Filter.atTop
        (nhds 0) := by
      simpa only [mul_zero, one_div, inv_pow, zpow_neg, zpow_natCast] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / 2)
          (by norm_num)).const_mul 3
    obtain ⟨k, hk⟩ := Metric.tendsto_atTop.mp hlim |x n| hpos
    have hk' : (3 : ℝ) * (2 : ℝ) ^ (-(k : ℤ)) < |x n| := by
      have h0 := hk k le_rfl
      have h3p : 0 < (3 : ℝ) * (2 : ℝ) ^ (-(k : ℤ)) := mul_pos (by norm_num) (zpow_pos two_pos _)
      rwa [Real.dist_eq, sub_zero, abs_of_pos h3p] at h0
    refine ⟨k, decide_eq_true ?_⟩
    have hcast : ((2 : ℚ) ^ (1 - (k : ℤ)) : ℝ) < |(q n k : ℝ)| := by
      push_cast
      rw [show (1 - (k : ℤ)) = (1 : ℤ) + -(k : ℤ) by omega, zpow_add₀ two_ne_zero, zpow_one]
      have htri : |x n| ≤ |x n - (q n k : ℝ)| + |(q n k : ℝ)| := by
        simpa using abs_add_le (x n - (q n k : ℝ)) (q n k : ℝ)
      linarith [hc n k]
    exact_mod_cast hcast
  let k0 : ℕ → ℕ := fun n ↦ Nat.find (hex n)
  have hk0 : Computable k0 :=
    Partrec.of_eq_tot (Partrec.rfind hsep.partrec₂) fun n ↦ nat_find_mem_rfind (hex n)
  let K : ℕ → ℕ → ℕ := fun n M ↦ M + 2 * k0 n + 1
  have hK : Computable fun p : ℕ × ℕ ↦ K p.1 p.2 :=
    Computable.succ.comp (Primrec.nat_add.to_comp.comp .snd
      (Primrec.nat_double.to_comp.comp (hk0.comp .fst)))
  refine isComputableRealSeq_iff_exists_rat_approx.mpr
    ⟨fun n M ↦ (q n (K n M))⁻¹, (hq.comp .fst hK).inv.to₂, fun n M ↦ ?_⟩
  have hspec : (2 : ℝ) * (2 : ℝ) ^ (-(k0 n : ℤ)) < |(q n (k0 n) : ℝ)| := by
    have hs : (2 : ℚ) ^ (1 - (k0 n : ℤ)) < |q n (k0 n)| :=
      of_decide_eq_true (Nat.find_spec (hex n))
    have hsr : ((2 : ℚ) ^ (1 - (k0 n : ℤ)) : ℝ) < |(q n (k0 n) : ℝ)| := by exact_mod_cast hs
    push_cast at hsr
    rwa [show (1 - (k0 n : ℤ)) = (1 : ℤ) + -(k0 n : ℤ) by omega, zpow_add₀ two_ne_zero,
      zpow_one] at hsr
  have hx_lb : (2 : ℝ) ^ (-(k0 n : ℤ)) < |x n| := by
    have htri : |(q n (k0 n) : ℝ)| ≤ |(q n (k0 n) : ℝ) - x n| + |x n| := by
      simpa using abs_add_le ((q n (k0 n) : ℝ) - x n) (x n)
    rw [abs_sub_comm] at htri
    linarith [hc n (k0 n)]
  have hq_lb : (2 : ℝ) ^ (-((k0 n : ℤ) + 1)) < |(q n (K n M) : ℝ)| := by
    have htri : |x n| ≤ |x n - (q n (K n M) : ℝ)| + |(q n (K n M) : ℝ)| := by
      simpa using abs_add_le (x n - (q n (K n M) : ℝ)) (q n (K n M) : ℝ)
    have herr : |x n - (q n (K n M) : ℝ)| < (2 : ℝ) ^ (-((k0 n : ℤ) + 1)) :=
      (hc n (K n M)).trans_le (zpow_le_zpow_right₀ one_le_two (by dsimp [K]; omega))
    have hhalf : (2 : ℝ) ^ (-(k0 n : ℤ)) = 2 * (2 : ℝ) ^ (-((k0 n : ℤ) + 1)) := by
      rw [show -(k0 n : ℤ) = (1 : ℤ) + -((k0 n : ℤ) + 1) by omega, zpow_add₀ two_ne_zero, zpow_one]
    linarith
  have hq_ne : (q n (K n M) : ℝ) ≠ 0 := abs_pos.mp ((zpow_pos two_pos _).trans hq_lb)
  have hprod_lb : (2 : ℝ) ^ (-((2 * k0 n + 1 : ℕ) : ℤ)) < |x n| * |(q n (K n M) : ℝ)| := by
    calc (2 : ℝ) ^ (-((2 * k0 n + 1 : ℕ) : ℤ))
        = (2 : ℝ) ^ (-(k0 n : ℤ)) * (2 : ℝ) ^ (-((k0 n : ℤ) + 1)) := by
          rw [← zpow_add₀ two_ne_zero]; congr 1; push_cast; omega
      _ < |x n| * |(q n (K n M) : ℝ)| :=
          mul_lt_mul'' hx_lb hq_lb (zpow_pos two_pos _).le (zpow_pos two_pos _).le
  push_cast
  rw [inv_sub_inv (hne n) hq_ne, abs_div, abs_sub_comm, abs_mul]
  rw [div_lt_iff₀ (mul_pos (abs_pos.mpr (hne n)) (abs_pos.mpr hq_ne))]
  calc |x n - (q n (K n M) : ℝ)|
      < (2 : ℝ) ^ (-(K n M : ℤ)) := hc n (K n M)
    _ = (2 : ℝ) ^ (-(M : ℤ)) * (2 : ℝ) ^ (-((2 * k0 n + 1 : ℕ) : ℤ)) := by
        rw [← zpow_add₀ two_ne_zero]; congr 1; dsimp [K]; omega
    _ < (2 : ℝ) ^ (-(M : ℤ)) * (|x n| * |(q n (K n M) : ℝ)|) :=
        mul_lt_mul_of_pos_left hprod_lb (zpow_pos two_pos _)

/-- Termwise division of computable real sequences (with nowhere-vanishing denominator) is
computable. -/
theorem IsComputableRealSeq.div {x y : ℕ → ℝ} (hx : IsComputableRealSeq x)
    (hy : IsComputableRealSeq y) (hy0 : ∀ n, y n ≠ 0) :
    IsComputableRealSeq fun n ↦ x n / y n := by
  simpa only [div_eq_mul_inv] using hx.mul (hy.inv hy0)

/-- Termwise absolute value of a computable real sequence is computable. -/
theorem IsComputableRealSeq.abs {x : ℕ → ℝ} (hx : IsComputableRealSeq x) :
    IsComputableRealSeq fun n ↦ |x n| := by
  obtain ⟨q, hq, hc⟩ := isComputableRealSeq_iff_exists_rat_approx.mp hx
  refine isComputableRealSeq_iff_exists_rat_approx.mpr ⟨fun n M ↦ |q n M|, hq.abs.to₂, fun n M ↦ ?_⟩
  push_cast; exact (abs_abs_sub_abs_le_abs_sub (x n) (q n M : ℝ)).trans_lt (hc n M)

/-- Termwise maximum of computable real sequences is computable. -/
theorem IsComputableRealSeq.max {x y : ℕ → ℝ} (hx : IsComputableRealSeq x)
    (hy : IsComputableRealSeq y) : IsComputableRealSeq fun n ↦ Max.max (x n) (y n) := by
  have h := ((hx.add hy).add (hx.sub hy).abs).mul (isComputableReal_rat (1 / 2)).constSeq
  refine h.of_eq fun n ↦ ?_
  push_cast
  rcases le_total (x n) (y n) with hle | hle
  · rw [max_eq_right hle, abs_of_nonpos (sub_nonpos.mpr hle)]; ring
  · rw [max_eq_left hle, abs_of_nonneg (sub_nonneg.mpr hle)]; ring

/-- Termwise minimum of computable real sequences is computable. -/
theorem IsComputableRealSeq.min {x y : ℕ → ℝ} (hx : IsComputableRealSeq x)
    (hy : IsComputableRealSeq y) : IsComputableRealSeq fun n ↦ Min.min (x n) (y n) :=
  (hx.neg.max hy.neg).neg.of_eq fun n ↦ by
    rcases le_total (x n) (y n) with h | h
    · rw [min_eq_left h, max_eq_left (neg_le_neg h), neg_neg]
    · rw [min_eq_right h, max_eq_right (neg_le_neg h), neg_neg]

private lemma abs_sqrt_sub_sqrt_le_sqrt_abs {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  wlog hle : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]; exact this hb ha (le_of_not_ge hle)
  have hsub : 0 ≤ Real.sqrt a - Real.sqrt b := sub_nonneg.mpr (Real.sqrt_le_sqrt hle)
  rw [abs_of_nonneg hsub, abs_of_nonneg (sub_nonneg.mpr hle)]
  refine Real.le_sqrt_of_sq_le ?_
  have h1 : Real.sqrt a * Real.sqrt b ≥ Real.sqrt b * Real.sqrt b :=
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg b)
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- Termwise real square root of a computable real sequence is computable. -/
theorem IsComputableRealSeq.sqrt {x : ℕ → ℝ} (hx : IsComputableRealSeq x) :
    IsComputableRealSeq fun n ↦ Real.sqrt (x n) := by
  obtain ⟨q, hq, hc⟩ :=
    isComputableRealSeq_iff_exists_rat_approx.mp (hx.max isComputableReal_zero.constSeq)
  let r : ℕ → ℕ → ℚ := fun n M ↦ Max.max (0 : ℚ) (q n (2 * (M + 1)))
  let numScaled : ℕ → ℕ → ℕ := fun n M ↦
    ((r n M).num.natAbs * 2 ^ (2 * (M + 1))) / (r n M).den
  let out : ℕ → ℕ → ℚ := fun n M ↦ (Nat.sqrt (numScaled n M) : ℚ) / (2 ^ (M + 1) : ℚ)
  have h2m : Computable fun p : ℕ × ℕ ↦ 2 * (p.2 + 1) :=
    Primrec.nat_double.to_comp.comp (Computable.succ.comp .snd)
  have hr : IsComputableRatMap fun p : ℕ × ℕ ↦ r p.1 p.2 :=
    (IsComputableRatMap.const 0).max (hq.comp .fst h2m)
  have hscaled : Computable fun p : ℕ × ℕ ↦ numScaled p.1 p.2 :=
    Primrec.nat_div.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (primrec_int_natAbs.to_comp.comp hr.num)
        (primrec_nat_pow.to_comp.comp (.const 2) h2m))
      hr.den
  have hout : IsComputableRatMap₂ out :=
    ((IsComputableRatMap.ofNat (primrec_nat_sqrt.to_comp.comp hscaled)).div
      ((IsComputableRatMap.const 2).pow (Computable.succ.comp .snd))).to₂
  refine isComputableRealSeq_of_rat_le hout fun n M ↦ ?_
  set y := Max.max (x n) 0
  have hy_sqrt : Real.sqrt (x n) = Real.sqrt y := by
    dsimp only [y]
    rcases le_total (x n) 0 with hle | hle
    · rw [max_eq_right hle, Real.sqrt_eq_zero'.mpr hle, Real.sqrt_zero]
    · rw [max_eq_left hle]
  rw [hy_sqrt]
  have hy0 : 0 ≤ y := le_max_right _ _
  have hr0 : 0 ≤ (r n M : ℝ) := by dsimp [r]; exact_mod_cast le_max_left (0 : ℚ) _
  have hyr : |y - (r n M : ℝ)| ≤ (2 : ℝ) ^ (-((2 * (M + 1) : ℕ) : ℤ)) := by
    have hqerr : |y - (q n (2 * (M + 1)) : ℝ)| ≤ (2 : ℝ) ^ (-((2 * (M + 1) : ℕ) : ℤ)) :=
      (hc n (2 * (M + 1))).le
    have hrc : (r n M : ℝ) = Max.max (0 : ℝ) (q n (2 * (M + 1)) : ℝ) := by
      dsimp [r]; exact_mod_cast rfl
    rw [hrc]
    rcases le_total (0 : ℝ) (q n (2 * (M + 1)) : ℝ) with hq0 | hq0
    · rwa [max_eq_right hq0]
    · rw [max_eq_left hq0, sub_zero, abs_of_nonneg hy0]
      have : |y - (q n (2 * (M + 1)) : ℝ)| = y - (q n (2 * (M + 1)) : ℝ) :=
        abs_of_nonneg (by linarith)
      linarith
  have h1 : |Real.sqrt y - Real.sqrt (r n M : ℝ)| ≤ (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) := by
    refine (abs_sqrt_sub_sqrt_le_sqrt_abs hy0 hr0).trans ((Real.sqrt_le_sqrt hyr).trans_eq ?_)
    have hsq : (2 : ℝ) ^ (-((2 * (M + 1) : ℕ) : ℤ)) =
        ((2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ))) ^ 2 := by
      rw [sq, ← zpow_add₀ two_ne_zero]; congr 1; push_cast; omega
    rw [hsq, Real.sqrt_sq (zpow_pos two_pos _).le]
  set k := Nat.sqrt (numScaled n M)
  set N := numScaled n M
  have hna : ((r n M).num.natAbs : ℝ) = ((r n M).num : ℝ) := by
    have hz : ((r n M).num.natAbs : ℤ) = (r n M).num :=
      Int.natAbs_of_nonneg (Rat.num_nonneg.mpr (le_max_left (0 : ℚ) _))
    simpa only [Int.cast_natCast] using congrArg (Int.cast : ℤ → ℝ) hz
  set S : ℝ := (r n M : ℝ) * (2 : ℝ) ^ (2 * (M + 1))
  have hS_eq : S = (((r n M).num.natAbs * 2 ^ (2 * (M + 1)) : ℕ) : ℝ) / ((r n M).den : ℝ) := by
    dsimp [S]; conv_lhs => rw [← (r n M).num_div_den]
    push_cast; rw [hna, div_mul_eq_mul_div]
  have hNS_lo : (N : ℝ) ≤ S := by
    rw [hS_eq, le_div_iff₀ (Nat.cast_pos.mpr (r n M).den_pos)]
    exact_mod_cast Nat.div_mul_le_self _ _
  have hNS_hi : S < (N : ℝ) + 1 := by
    rw [hS_eq, div_lt_iff₀ (Nat.cast_pos.mpr (r n M).den_pos), add_mul, one_mul]
    exact_mod_cast Nat.lt_div_mul_add (r n M).den_pos
  have hk_lo : (k : ℝ) ^ 2 ≤ S := by
    rw [sq]; exact (by exact_mod_cast Nat.sqrt_le N : (k : ℝ) * (k : ℝ) ≤ (N : ℝ)).trans hNS_lo
  have hk_hi : S < ((k : ℝ) + 1) ^ 2 := by
    have hlt : N ≤ k * k + 2 * k := by have := Nat.lt_succ_sqrt N; linarith
    have hlt' : (N : ℝ) ≤ (k : ℝ) * (k : ℝ) + 2 * (k : ℝ) := by exact_mod_cast hlt
    linarith
  have hsqrtS : (k : ℝ) ≤ Real.sqrt S ∧ Real.sqrt S ≤ (k : ℝ) + 1 :=
    ⟨Real.le_sqrt_of_sq_le hk_lo, Real.sqrt_le_iff.mpr ⟨by positivity, hk_hi.le⟩⟩
  have hsqrtS_eq : Real.sqrt S = Real.sqrt (r n M : ℝ) * (2 : ℝ) ^ (M + 1) := by
    dsimp [S]
    rw [Real.sqrt_mul hr0, show (2 : ℝ) ^ (2 * (M + 1)) = ((2 : ℝ) ^ (M + 1)) ^ 2 by
      rw [← pow_mul]; ring, Real.sqrt_sq (pow_pos two_pos _).le]
  have h2 : |Real.sqrt (r n M : ℝ) - (out n M : ℝ)| ≤ (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_natCast, ← one_div]
    dsimp [out]; push_cast
    rw [abs_le]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (M + 1) := pow_pos two_pos _
    rw [hsqrtS_eq] at hsqrtS
    constructor
    · rw [neg_le_sub_iff_le_add, div_le_iff₀ hpos, add_mul, one_div_mul_cancel hpos.ne']
      linarith [hsqrtS.1]
    · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hpos]; linarith [hsqrtS.2]
  calc |Real.sqrt y - (out n M : ℝ)|
      ≤ |Real.sqrt y - Real.sqrt (r n M : ℝ)| + |Real.sqrt (r n M : ℝ) - (out n M : ℝ)| :=
        abs_sub_le _ _ _
    _ ≤ (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) + (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) := add_le_add h1 h2
    _ = (2 : ℝ) ^ (-(M : ℤ)) := zpow_neg_succ_add M

/-! ### Closure lemmas for `IsComputableReal` and `computableRealSubfield` -/

/-- Negation of a computable real is computable. -/
theorem IsComputableReal.neg {x : ℝ} (hx : IsComputableReal x) : IsComputableReal (-x) :=
  hx.constSeq.neg.apply 0

/-- Sum of computable reals is computable. -/
theorem IsComputableReal.add {x y : ℝ} (hx : IsComputableReal x) (hy : IsComputableReal y) :
    IsComputableReal (x + y) :=
  (hx.constSeq.add hy.constSeq).apply 0

/-- Difference of computable reals is computable. -/
theorem IsComputableReal.sub {x y : ℝ} (hx : IsComputableReal x) (hy : IsComputableReal y) :
    IsComputableReal (x - y) :=
  (hx.constSeq.sub hy.constSeq).apply 0

/-- Product of computable reals is computable. -/
theorem IsComputableReal.mul {x y : ℝ} (hx : IsComputableReal x) (hy : IsComputableReal y) :
    IsComputableReal (x * y) :=
  (hx.constSeq.mul hy.constSeq).apply 0

/-- Reciprocal of a computable real is computable. -/
theorem IsComputableReal.inv {x : ℝ} (hx : IsComputableReal x) : IsComputableReal x⁻¹ := by
  by_cases hx0 : x = 0
  · subst hx0; rw [inv_zero]; exact isComputableReal_zero
  · exact (hx.constSeq.inv fun _ ↦ hx0).apply 0

/-- Quotient of computable reals is computable. -/
theorem IsComputableReal.div {x y : ℝ} (hx : IsComputableReal x) (hy : IsComputableReal y) :
    IsComputableReal (x / y) := by
  simpa only [div_eq_mul_inv] using hx.mul (IsComputableReal.inv hy)

/-- Absolute value of a computable real is computable. -/
theorem IsComputableReal.abs {x : ℝ} (hx : IsComputableReal x) : IsComputableReal |x| :=
  hx.constSeq.abs.apply 0

/-- Maximum of computable reals is computable. -/
theorem IsComputableReal.max {x y : ℝ} (hx : IsComputableReal x) (hy : IsComputableReal y) :
    IsComputableReal (Max.max x y) :=
  (hx.constSeq.max hy.constSeq).apply 0

/-- Minimum of computable reals is computable. -/
theorem IsComputableReal.min {x y : ℝ} (hx : IsComputableReal x) (hy : IsComputableReal y) :
    IsComputableReal (Min.min x y) :=
  (hx.constSeq.min hy.constSeq).apply 0

/-- Real square root of a computable real is computable. -/
theorem IsComputableReal.sqrt {x : ℝ} (hx : IsComputableReal x) :
    IsComputableReal (Real.sqrt x) :=
  hx.constSeq.sqrt.apply 0

/-- Natural power of a computable real is computable. -/
theorem IsComputableReal.pow {x : ℝ} (hx : IsComputableReal x) (n : ℕ) :
    IsComputableReal (x ^ n) := by
  induction n with
  | zero => simp
  | succ k ih => simpa [pow_succ] using ih.mul hx

/-- The subfield of computable real numbers inside `ℝ`. -/
def computableRealSubfield : Subfield ℝ where
  carrier := { x : ℝ | IsComputableReal x }
  mul_mem' hx hy := hx.mul hy
  one_mem' := isComputableReal_one
  add_mem' hx hy := hx.add hy
  zero_mem' := isComputableReal_zero
  neg_mem' hx := hx.neg
  inv_mem' _ hx := IsComputableReal.inv hx

/-- Membership in `computableRealSubfield` is equivalent to `IsComputableReal`. -/
@[simp] theorem mem_computableRealSubfield_iff {x : ℝ} :
    x ∈ computableRealSubfield ↔ IsComputableReal x := Iff.rfl

/-! ### Finite sums, prefix extrema, and effective limits of computable real sequences -/

/-- Termwise natural-number power of a computable real sequence with a computable exponent is
computable. -/
theorem IsComputableRealSeq.pow {x : ℕ → ℝ} {d : ℕ → ℕ} (hx : IsComputableRealSeq x)
    (hd : Computable d) : IsComputableRealSeq fun n ↦ x n ^ d n := by
  obtain ⟨q, hq, hc⟩ := isComputableRealSeq_iff_exists_rat_approx.mp hx
  let B : ℕ → ℕ := fun n ↦ (q n 0).num.natAbs + 2
  let K : ℕ → ℕ → ℕ := fun n M ↦ M + d n * B n + d n + 1
  have hB : Computable B :=
    Primrec.nat_add.to_comp.comp
      (primrec_int_natAbs.to_comp.comp (hq.comp .id (.const 0)).num) (.const 2)
  have hK : Computable fun p : ℕ × ℕ ↦ K p.1 p.2 :=
    Computable.succ.comp (Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp .snd
        (Primrec.nat_mul.to_comp.comp (hd.comp .fst) (hB.comp .fst)))
      (hd.comp .fst))
  refine isComputableRealSeq_of_rat_le ((hq.comp .fst hK).pow (hd.comp .fst)).to₂ fun n M ↦ ?_
  push_cast
  have hB_bound : Max.max |x n| |(q n (K n M) : ℝ)| ≤ (2 : ℝ) ^ (B n) := by
    have hBpow : (B n : ℝ) ≤ (2 : ℝ) ^ (B n) := by exact_mod_cast Nat.lt_two_pow_self.le
    have h0 : |x n - (q n 0 : ℝ)| < 1 := by simpa using hc n 0
    have hk : |x n - (q n (K n M) : ℝ)| < 1 :=
      (hc n (K n M)).trans_le
        (zpow_le_one_of_nonpos₀ one_le_two (neg_nonpos.mpr (Nat.cast_nonneg _)))
    have hq0 := abs_rat_le_natAbs_num (q n 0)
    have hBc : (B n : ℝ) = ((q n 0).num.natAbs : ℝ) + 2 := by dsimp [B]; push_cast; ring
    have hx1 : |x n| ≤ ((q n 0).num.natAbs : ℝ) + 1 := by
      have ht : |x n| ≤ |x n - (q n 0 : ℝ)| + |(q n 0 : ℝ)| := by
        simpa using abs_add_le (x n - (q n 0 : ℝ)) (q n 0 : ℝ)
      linarith
    have hqkB : |(q n (K n M) : ℝ)| ≤ (B n : ℝ) := by
      have ht : |(q n (K n M) : ℝ)| ≤ |(q n (K n M) : ℝ) - x n| + |x n| := by
        simpa using abs_add_le ((q n (K n M) : ℝ) - x n) (x n)
      rw [abs_sub_comm] at ht; linarith
    exact max_le (by linarith) (hqkB.trans hBpow)
  have hR1 : (1 : ℝ) ≤ (2 : ℝ) ^ (B n) := one_le_pow₀ one_le_two
  have hpow_sub : ∀ k : ℕ, |x n ^ k - (q n (K n M) : ℝ) ^ k| ≤
      (k : ℝ) * ((2 : ℝ) ^ (B n)) ^ k * |x n - (q n (K n M) : ℝ)| := fun k ↦ by
    induction k with
    | zero => simp
    | succ m ih =>
      have ha : |x n| ≤ (2 : ℝ) ^ (B n) := (le_max_left _ _).trans hB_bound
      have hb : |(q n (K n M) : ℝ)| ≤ (2 : ℝ) ^ (B n) := (le_max_right _ _).trans hB_bound
      rw [pow_succ, pow_succ, show x n ^ m * x n - (q n (K n M) : ℝ) ^ m * (q n (K n M) : ℝ) =
        (x n ^ m - (q n (K n M) : ℝ) ^ m) * x n +
          (q n (K n M) : ℝ) ^ m * (x n - (q n (K n M) : ℝ)) by ring]
      calc |(x n ^ m - (q n (K n M) : ℝ) ^ m) * x n +
              (q n (K n M) : ℝ) ^ m * (x n - (q n (K n M) : ℝ))|
          ≤ |x n ^ m - (q n (K n M) : ℝ) ^ m| * |x n| +
              |(q n (K n M) : ℝ)| ^ m * |x n - (q n (K n M) : ℝ)| := by
            have ht := abs_add_le ((x n ^ m - (q n (K n M) : ℝ) ^ m) * x n)
              ((q n (K n M) : ℝ) ^ m * (x n - (q n (K n M) : ℝ)))
            rwa [abs_mul, abs_mul, abs_pow] at ht
        _ ≤ ((m : ℝ) * ((2 : ℝ) ^ (B n)) ^ m * |x n - (q n (K n M) : ℝ)|) * (2 : ℝ) ^ (B n) +
              ((2 : ℝ) ^ (B n)) ^ m * (2 : ℝ) ^ (B n) * |x n - (q n (K n M) : ℝ)| := by
            refine add_le_add (mul_le_mul ih ha (abs_nonneg _) (by positivity))
              (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
            exact (pow_le_pow_left₀ (abs_nonneg _) hb m).trans
              (le_mul_of_one_le_right (by positivity) hR1)
        _ = ((m + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (B n)) ^ (m + 1) * |x n - (q n (K n M) : ℝ)| := by
            push_cast; rw [pow_succ]; ring
  have hd_le : (d n : ℝ) ≤ (2 : ℝ) ^ (d n) := by exact_mod_cast Nat.lt_two_pow_self.le
  calc |x n ^ d n - (q n (K n M) : ℝ) ^ d n|
      ≤ (d n : ℝ) * ((2 : ℝ) ^ (B n)) ^ (d n) * |x n - (q n (K n M) : ℝ)| := hpow_sub (d n)
    _ ≤ (2 : ℝ) ^ (d n) * (2 : ℝ) ^ (B n * d n) * (2 : ℝ) ^ (-(K n M : ℤ)) := by
        rw [← pow_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hd_le (by positivity))
          (hc n (K n M)).le (abs_nonneg _) (by positivity)
    _ ≤ (2 : ℝ) ^ (-(M : ℤ)) := by
        rw [← zpow_natCast (2 : ℝ) (d n), ← zpow_natCast (2 : ℝ) (B n * d n),
          ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]
        refine zpow_le_zpow_right₀ one_le_two ?_
        dsimp [K]; linarith [mul_comm (B n : ℤ) (d n : ℤ)]

/-- Finite sums `n ↦ ∑ k ∈ Finset.range (d n), x n k` of a computable real double sequence up to
a computable bound `d : ℕ → ℕ` form a computable real sequence. -/
theorem IsComputableRealDoubleSeq.sum_range {x : ℕ → ℕ → ℝ} (hx : IsComputableRealDoubleSeq x)
    {d : ℕ → ℕ} (hd : Computable d) :
    IsComputableRealSeq fun n ↦ ∑ k ∈ Finset.range (d n), x n k := by
  obtain ⟨q, hq, hc⟩ := isComputableRealDoubleSeq_iff_exists_rat_approx.mp hx
  have hterm : IsComputableRatMap₂ fun (nM : ℕ × ℕ) (k : ℕ) ↦ q (nM.1, k) (nM.2 + d nM.1) :=
    (hq.comp (.pair (Computable.fst.comp .fst) .snd)
      (Primrec.nat_add.to_comp.comp (Computable.snd.comp .fst)
        (hd.comp (Computable.fst.comp .fst)))).to₂
  refine isComputableRealSeq_of_rat_le
    (IsComputableRatMap.sum_range (hd.comp .fst) hterm).to₂ fun n M ↦ ?_
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ Finset.range (d n), |x n k - (q (n, k) (M + d n) : ℝ)|
      ≤ ∑ _k ∈ Finset.range (d n), (2 : ℝ) ^ (-((M + d n : ℕ) : ℤ)) :=
        Finset.sum_le_sum fun k _ ↦ (hc n k (M + d n)).le
    _ = (d n : ℝ) * (2 : ℝ) ^ (-((M + d n : ℕ) : ℤ)) := by simp
    _ ≤ (2 : ℝ) ^ (d n) * (2 : ℝ) ^ (-((M + d n : ℕ) : ℤ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.lt_two_pow_self.le)
          (zpow_pos two_pos _).le
    _ = (2 : ℝ) ^ (-(M : ℤ)) := by
        rw [← zpow_natCast (2 : ℝ) (d n), ← zpow_add₀ two_ne_zero]; congr 1; push_cast; omega

/-- Finite suprema `n ↦ (Finset.range (d n + 1)).sup' _ (x n)` of a computable real double sequence
form a computable real sequence. -/
theorem IsComputableRealDoubleSeq.sup'_range {x : ℕ → ℕ → ℝ} (hx : IsComputableRealDoubleSeq x)
    {d : ℕ → ℕ} (hd : Computable d) :
    IsComputableRealSeq fun n ↦
      (Finset.range (d n + 1)).sup' Finset.nonempty_range_add_one (x n) := by
  obtain ⟨q, hq, hc⟩ := isComputableRealDoubleSeq_iff_exists_rat_approx.mp hx
  have hterm : IsComputableRatMap₂ fun (nM : ℕ × ℕ) (k : ℕ) ↦ q (nM.1, k) nM.2 :=
    (hq.comp (.pair (Computable.fst.comp .fst) .snd) (Computable.snd.comp .fst)).to₂
  refine isComputableRealSeq_of_rat_le
    (IsComputableRatMap.sup'_range (hd.comp .fst) hterm).to₂ fun n M ↦ ?_
  have hcast :
      (((Finset.range (d n + 1)).sup' Finset.nonempty_range_add_one
          (fun k ↦ q (n, k) M) : ℚ) : ℝ) =
        (Finset.range (d n + 1)).sup' Finset.nonempty_range_add_one
          fun k ↦ (q (n, k) M : ℝ) := by
    simpa using (Finset.apply_sup'_eq_sup'_comp (s := Finset.range (d n + 1))
      Finset.nonempty_range_add_one (f := fun k ↦ q (n, k) M) (g := ((↑) : ℚ → ℝ))
      (fun _ _ ↦ Rat.cast_max _ _))
  rw [hcast, abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    refine Finset.sup'_le _ _ fun k hk ↦ ?_
    have hle : (q (n, k) M : ℝ) ≤
        (Finset.range (d n + 1)).sup' Finset.nonempty_range_add_one
          fun j ↦ (q (n, j) M : ℝ) :=
      Finset.le_sup' (f := fun j ↦ (q (n, j) M : ℝ)) hk
    linarith [(abs_sub_le_iff.mp (hc n k M).le).1]
  · rw [sub_le_iff_le_add]
    refine Finset.sup'_le _ _ fun k hk ↦ ?_
    have hle : x n k ≤ (Finset.range (d n + 1)).sup' Finset.nonempty_range_add_one (x n) :=
      Finset.le_sup' (f := x n) hk
    linarith [(abs_sub_le_iff.mp (hc n k M).le).2]

/-- Finite infima `n ↦ (Finset.range (d n + 1)).inf' _ (x n)` of a computable real double sequence
form a computable real sequence. -/
theorem IsComputableRealDoubleSeq.inf'_range {x : ℕ → ℕ → ℝ} (hx : IsComputableRealDoubleSeq x)
    {d : ℕ → ℕ} (hd : Computable d) :
    IsComputableRealSeq fun n ↦
      (Finset.range (d n + 1)).inf' Finset.nonempty_range_add_one (x n) := by
  have hneg : IsComputableRealDoubleSeq fun n k ↦ -x n k := IsComputableRealSeq.neg hx
  refine (hneg.sup'_range hd).neg.of_eq fun n ↦ ?_
  change -((Finset.range (d n + 1)).sup' Finset.nonempty_range_add_one fun j ↦ -x n j) =
    (Finset.range (d n + 1)).inf' Finset.nonempty_range_add_one (x n)
  apply le_antisymm
  · refine Finset.le_inf' Finset.nonempty_range_add_one (x n) fun k hk ↦ ?_
    exact neg_le.mp (Finset.le_sup' (f := fun j ↦ -x n j) hk)
  · rw [le_neg]
    refine Finset.sup'_le Finset.nonempty_range_add_one (fun j ↦ -x n j) fun k hk ↦ ?_
    exact neg_le_neg (Finset.inf'_le (f := x n) hk)

/-- Prefix maximum `N ↦ max_{k ≤ N} x k` of a computable real sequence is computable. -/
theorem IsComputableRealSeq.prefixMax {x : ℕ → ℝ} (hx : IsComputableRealSeq x) :
    IsComputableRealSeq fun N ↦
      (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one x :=
  (hx.comp₂ Computable.snd.to₂).sup'_range .id

/-- Prefix minimum `N ↦ min_{k ≤ N} x k` of a computable real sequence is computable. -/
theorem IsComputableRealSeq.prefixMin {x : ℕ → ℝ} (hx : IsComputableRealSeq x) :
    IsComputableRealSeq fun N ↦
      (Finset.range (N + 1)).inf' Finset.nonempty_range_add_one x :=
  (hx.comp₂ Computable.snd.to₂).inf'_range .id

/-- Effective uniform limit of a computable real double sequence is a computable real sequence. -/
theorem IsComputableRealDoubleSeq.effectiveLimit {x : ℕ → ℕ → ℝ} {y : ℕ → ℝ}
    {e : ℕ → ℕ → ℕ} (hx : IsComputableRealDoubleSeq x) (he : Computable₂ e)
    (hconv : ∀ n M k : ℕ, e n M ≤ k → |x n k - y n| ≤ (2 : ℝ) ^ (-(M : ℤ))) :
    IsComputableRealSeq y := by
  obtain ⟨q, hq, hc⟩ := isComputableRealDoubleSeq_iff_exists_rat_approx.mp hx
  have hm1 : Computable fun p : ℕ × ℕ ↦ p.2 + 1 := Computable.succ.comp .snd
  have he1 : Computable fun p : ℕ × ℕ ↦ e p.1 (p.2 + 1) := he.comp .fst hm1
  refine isComputableRealSeq_iff_exists_rat_approx.mpr
    ⟨fun n M ↦ q (n, e n (M + 1)) (M + 1), (hq.comp (.pair .fst he1) hm1).to₂, fun n M ↦ ?_⟩
  calc |y n - (q (n, e n (M + 1)) (M + 1) : ℝ)|
      ≤ |y n - x n (e n (M + 1))| + |x n (e n (M + 1)) - (q (n, e n (M + 1)) (M + 1) : ℝ)| :=
        abs_sub_le _ _ _
    _ < (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) + (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) := by
        rw [abs_sub_comm]
        exact add_lt_add_of_le_of_lt (hconv n (M + 1) _ le_rfl) (hc n _ (M + 1))
    _ = (2 : ℝ) ^ (-(M : ℤ)) := zpow_neg_succ_add M

/-- The effective limit of a computable sequence of real numbers is a computable real number. -/
theorem IsComputableReal.of_effectivelyConvergesTo {x : ℕ → ℝ} {L : ℝ}
    (hx : IsComputableRealSeq x) (hconv : EffectivelyConvergesTo x L) :
    IsComputableReal L := by
  obtain ⟨e, he, hL⟩ := hconv
  refine ((hx.comp₂ Computable.snd.to₂).effectiveLimit (y := fun _ ↦ L)
    (e := fun _ M ↦ e M) (he.comp .snd).to₂ fun _ M k hk ↦ ?_).apply 0
  rw [abs_sub_comm]; exact (hL M k hk).le

/-- Double-sequence termwise negation is computable. -/
theorem IsComputableRealDoubleSeq.neg {x : ℕ → ℕ → ℝ} (hx : IsComputableRealDoubleSeq x) :
    IsComputableRealDoubleSeq fun n k ↦ -x n k :=
  IsComputableRealSeq.neg hx

/-- Double-sequence termwise addition is computable. -/
theorem IsComputableRealDoubleSeq.add {x y : ℕ → ℕ → ℝ} (hx : IsComputableRealDoubleSeq x)
    (hy : IsComputableRealDoubleSeq y) : IsComputableRealDoubleSeq fun n k ↦ x n k + y n k :=
  IsComputableRealSeq.add hx hy

/-- Double-sequence termwise subtraction is computable. -/
theorem IsComputableRealDoubleSeq.sub {x y : ℕ → ℕ → ℝ} (hx : IsComputableRealDoubleSeq x)
    (hy : IsComputableRealDoubleSeq y) : IsComputableRealDoubleSeq fun n k ↦ x n k - y n k :=
  IsComputableRealSeq.sub hx hy

/-- Double-sequence termwise multiplication is computable. -/
theorem IsComputableRealDoubleSeq.mul {x y : ℕ → ℕ → ℝ} (hx : IsComputableRealDoubleSeq x)
    (hy : IsComputableRealDoubleSeq y) : IsComputableRealDoubleSeq fun n k ↦ x n k * y n k :=
  IsComputableRealSeq.mul hx hy

/-- Double-sequence termwise division is computable when the denominator never vanishes. -/
theorem IsComputableRealDoubleSeq.div {x y : ℕ → ℕ → ℝ} (hx : IsComputableRealDoubleSeq x)
    (hy : IsComputableRealDoubleSeq y) (hy0 : ∀ n k, y n k ≠ 0) :
    IsComputableRealDoubleSeq fun n k ↦ x n k / y n k :=
  IsComputableRealSeq.div hx hy fun i ↦ hy0 i.unpair.1 i.unpair.2

/-- Double-sequence termwise absolute value is computable. -/
theorem IsComputableRealDoubleSeq.abs {x : ℕ → ℕ → ℝ} (hx : IsComputableRealDoubleSeq x) :
    IsComputableRealDoubleSeq fun n k ↦ |x n k| :=
  IsComputableRealSeq.abs hx

/-- Double-sequence termwise maximum is computable. -/
theorem IsComputableRealDoubleSeq.max {x y : ℕ → ℕ → ℝ} (hx : IsComputableRealDoubleSeq x)
    (hy : IsComputableRealDoubleSeq y) :
    IsComputableRealDoubleSeq fun n k ↦ Max.max (x n k) (y n k) :=
  IsComputableRealSeq.max hx hy

/-- Double-sequence termwise minimum is computable. -/
theorem IsComputableRealDoubleSeq.min {x y : ℕ → ℕ → ℝ} (hx : IsComputableRealDoubleSeq x)
    (hy : IsComputableRealDoubleSeq y) :
    IsComputableRealDoubleSeq fun n k ↦ Min.min (x n k) (y n k) :=
  IsComputableRealSeq.min hx hy

/-- Double-sequence termwise square root is computable. -/
theorem IsComputableRealDoubleSeq.sqrt {x : ℕ → ℕ → ℝ} (hx : IsComputableRealDoubleSeq x) :
    IsComputableRealDoubleSeq fun n k ↦ Real.sqrt (x n k) :=
  IsComputableRealSeq.sqrt hx

/-- Double-sequence termwise natural-number power is computable. -/
theorem IsComputableRealDoubleSeq.pow {x : ℕ → ℕ → ℝ} {d : ℕ → ℕ → ℕ}
    (hx : IsComputableRealDoubleSeq x) (hd : Computable₂ d) :
    IsComputableRealDoubleSeq fun n k ↦ x n k ^ d n k :=
  IsComputableRealSeq.pow hx (hd.comp (Computable.fst.comp .unpair) (Computable.snd.comp .unpair))

end CslibFrontier.ComputableAnalysis
