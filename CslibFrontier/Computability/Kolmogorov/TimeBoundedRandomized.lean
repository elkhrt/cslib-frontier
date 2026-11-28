/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Kolmogorov.Conditional
public import CslibFrontier.Computability.Kolmogorov.TimeBounded
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Probability.BitString
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.EReal.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal

/-!
# Randomized Time-Bounded Kolmogorov Complexity and Universal Distributions

This module defines randomized and probabilistic time-bounded Kolmogorov complexity measures
built on `Cslib.Kolmogorov.DescriptionMethod.condUniversalTM`, together with the time-bounded
universal distribution `universalRandDist`, its negative log-probability `qTimeBounded`, the
universal extrapolation distribution `universalExtrapolationDist`, computational depth
`computationalDepth`, and the `GapKtVsKInPrBPP` meta-complexity assumption.

## Main definitions

- `CslibFrontier.Computability.Kolmogorov.randUniversalTMRunFor`: clocked randomized universal
  execution $U^{\mathsf{r}}(M, y, r, 1^t)$ via `condUniversalTM` on the paired condition `(y, r)`.
- `CslibFrontier.Computability.Kolmogorov.padTruncate`: pad with `false` or truncate to a target
  bit length.
- `CslibFrontier.Computability.Kolmogorov.randUniversalOutput`: padded length-`len` output
  distribution of a randomized program executed for `t` steps.
- `CslibFrontier.Computability.Kolmogorov.rTimeBoundedAt`: randomized $t$-time-bounded Kolmogorov
  complexity $\mathsf{rK}^t_\lambda(x \mid y)$.
- `CslibFrontier.Computability.Kolmogorov.pTimeBoundedAt`: probabilistic $t$-time-bounded
  Kolmogorov complexity $\mathsf{pK}^t_\lambda(x \mid y)$.
- `CslibFrontier.Computability.Kolmogorov.rLevinKt`: randomized Levin complexity
  $\mathsf{rKt}_\lambda(x \mid y)$.
- `CslibFrontier.Computability.Kolmogorov.universalRandDist`: $t$-time-bounded universal
  distribution $\mathcal{Q}_{t, z}$ with advice $z$.
- `CslibFrontier.Computability.Kolmogorov.qTimeBounded`: negative base-2 log-probability
  $\mathsf{q}^t(x \mid z) = -\log_2 \mathcal{Q}_{t, z}(x)$ in `ℝ≥0∞`.
- `CslibFrontier.Computability.Kolmogorov.universalExtrapolationDist`: universal extrapolation
  distribution $\mathsf{Next}_n(y; \mathcal{Q}_{t, z})$.
- `CslibFrontier.Computability.Kolmogorov.computationalDepth`: computational depth
  $\mathsf{cd}^t(y \mid z) = \mathsf{q}^t(y \mid z) - \mathsf{K}(y \mid z)$ in `EReal`.
- `CslibFrontier.Computability.Kolmogorov.GapKtVsKInPrBPP`: the
  $\mathsf{GapK}^t\text{-}\mathsf{vs}\text{-}\mathsf{K} \in \mathsf{prBPP}$ promise-estimation
  condition.

## Main results

- `CslibFrontier.Computability.Kolmogorov.rTimeBoundedAt_le_natCast_iff`: witness characterization
  of $\mathsf{rK}^t_\lambda(x \mid y) \le k$.
- `CslibFrontier.Computability.Kolmogorov.pTimeBoundedAt_le_natCast_iff`: witness characterization
  of $\mathsf{pK}^t_\lambda(x \mid y) \le k$.
- `CslibFrontier.Computability.Kolmogorov.pTimeBoundedAt_le_rTimeBoundedAt`:
  $\mathsf{pK}^t_\lambda(x \mid y) \le \mathsf{rK}^t_\lambda(x \mid y)$.
- `CslibFrontier.Computability.Kolmogorov.rLevinKt_le_natCast_iff`: witness characterization of
  $\mathsf{rKt}_\lambda(x \mid y) \le k$.
- `CslibFrontier.Computability.Kolmogorov.rTimeBoundedAt_zero`,
  `CslibFrontier.Computability.Kolmogorov.pTimeBoundedAt_zero`: at step budget `0` and positive
  threshold `λ > 0`, both measures equal `⊤`.
- `CslibFrontier.Computability.Kolmogorov.length_of_mem_support_randUniversalOutput`: every
  supported output of `randUniversalOutput` has the requested bit length.
- `CslibFrontier.Computability.Kolmogorov.length_of_mem_support_universalExtrapolationDist`: every
  supported output of `universalExtrapolationDist` has length `n`.
-/

public section

namespace CslibFrontier.Computability.Kolmogorov

open scoped ENNReal
open Cslib Cslib.BitString Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod
open Cslib.Probability Turing.MultiTapeTM

/-- Clocked randomized universal execution $U^{\mathsf{r}}(p, y, r, 1^t)$: evaluates binary
program `p` on paired auxiliary input and random tape `(y, r)` for `t` steps under
`Cslib.Kolmogorov.DescriptionMethod.condUniversalTM`. -/
def randUniversalTMRunFor (p y r : List Bool) (t : ℕ) : Option (List Bool) :=
  ((condUniversalTM (encPair encBits encBits (y, r))).run p).runFor t

/-- Characterization of `randUniversalTMRunFor` via `condUniversalTM`. -/
theorem randUniversalTMRunFor_eq_runFor (p y r : List Bool) (t : ℕ) :
    randUniversalTMRunFor p y r t =
      ((condUniversalTM (encPair encBits encBits (y, r))).run p).runFor t := by rfl

/-- At step budget `0`, randomized universal execution never halts. -/
@[simp]
theorem randUniversalTMRunFor_zero (p y r : List Bool) :
    randUniversalTMRunFor p y r 0 = none := by
  simp [randUniversalTMRunFor, condUniversalTM]

/-- Randomized universal execution is monotone in the step budget `t`. -/
theorem randUniversalTMRunFor_mono (p y r : List Bool) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂)
    {x : List Bool} (h : x ∈ randUniversalTMRunFor p y r t₁) :
    x ∈ randUniversalTMRunFor p y r t₂ := by
  induction ht with
  | refl => exact h
  | step _ ih => exact ((condUniversalTM (encPair encBits encBits (y, r))).run p).2 ih

/-- Pad a bit string with `false` on the right (or truncate on the right) to length `len`. -/
def padTruncate (len : ℕ) (x : List Bool) : List Bool :=
  (x ++ List.replicate len false).take len

/-- Characterization of `padTruncate` as `(x ++ replicate len false).take len`. -/
theorem padTruncate_eq_take_append (len : ℕ) (x : List Bool) :
    padTruncate len x = (x ++ List.replicate len false).take len := by rfl

/-- `padTruncate len x` always has exact length `len`. -/
@[simp]
theorem length_padTruncate (len : ℕ) (x : List Bool) : (padTruncate len x).length = len := by
  simp only [padTruncate, List.length_take, List.length_append, List.length_replicate]
  omega

/-- `padTruncate` is the identity on words already of length `len`. -/
@[simp]
theorem padTruncate_of_length_eq {len : ℕ} {x : List Bool} (h : x.length = len) :
    padTruncate len x = x := by
  simp only [padTruncate]
  rw [List.take_append_of_le_length h.ge, List.take_of_length_le h.le]

/-- `padTruncate` is idempotent. -/
theorem padTruncate_padTruncate (len : ℕ) (x : List Bool) :
    padTruncate len (padTruncate len x) = padTruncate len x :=
  padTruncate_of_length_eq (length_padTruncate len x)

/-- For `x.length ≤ len`, `padTruncate len x` appends `len - x.length` copies of `false`. -/
theorem padTruncate_eq_append_replicate_sub {len : ℕ} {x : List Bool} (h : x.length ≤ len) :
    padTruncate len x = x ++ List.replicate (len - x.length) false := by
  simp only [padTruncate]
  rw [List.take_append, List.take_of_length_le h, List.take_replicate,
    Nat.min_eq_left (Nat.sub_le _ _)]

/-- Padded/truncated length-`len` output distribution of randomized program `p` with auxiliary
input `y` run for `t` steps on a uniform `t`-bit random string; non-halting runs map to `0^len`. -/
noncomputable def randUniversalOutput (p y : List Bool) (t len : ℕ) : PMF (List Bool) :=
  (uniformList t).map fun r =>
    match randUniversalTMRunFor p y r t with
    | some x => padTruncate len x
    | none => List.replicate len false

/-- Characterization of `randUniversalOutput` as a mapped uniform distribution. -/
theorem randUniversalOutput_eq_map (p y : List Bool) (t len : ℕ) :
    randUniversalOutput p y t len =
      (uniformList t).map (fun r =>
        match randUniversalTMRunFor p y r t with
        | some x => padTruncate len x
        | none => List.replicate len false) := by rfl

/-- Every word in the support of `randUniversalOutput p y t len` has exact length `len`. -/
theorem length_of_mem_support_randUniversalOutput {p y : List Bool} {t len : ℕ}
    {x : List Bool} (hx : x ∈ (randUniversalOutput p y t len).support) :
    x.length = len := by
  rw [randUniversalOutput, PMF.mem_support_map_iff] at hx
  obtain ⟨r, _, rfl⟩ := hx
  cases randUniversalTMRunFor p y r t <;> simp

/-- Acceptance probability of a fixed randomized program `p` outputting `x` given `y` in `t` steps
over a uniform `t`-bit random string. -/
noncomputable def randProgramSuccessProb (p y x : List Bool) (t : ℕ) : ℝ :=
  ((uniformList t).toOuterMeasure {r : List Bool | x ∈ randUniversalTMRunFor p y r t}).toReal

/-- `randProgramSuccessProb` lies in `[0, 1]`. -/
theorem randProgramSuccessProb_nonneg (p y x : List Bool) (t : ℕ) :
    0 ≤ randProgramSuccessProb p y x t :=
  ENNReal.toReal_nonneg

/-- `randProgramSuccessProb` is at most `1`. -/
theorem randProgramSuccessProb_le_one (p y x : List Bool) (t : ℕ) :
    randProgramSuccessProb p y x t ≤ 1 := by
  rw [randProgramSuccessProb]
  exact Cslib.Probability.PMF.toOuterMeasure_toReal_le_one _ _

/-- **Randomized $t$-time-bounded Kolmogorov complexity** $\mathsf{rK}^t_\lambda(x \mid y)$:
the minimum length of a program `p` outputting `x` given `y` within `t` steps with probability
at least `λ` over `r ~ U_t`. -/
noncomputable def rTimeBoundedAt (t : ℕ) (lam : ℝ) (x y : List Bool) : ℕ∞ :=
  ⨅ (p : List Bool) (_ : lam ≤ randProgramSuccessProb p y x t), (p.length : ℕ∞)

/-- **Probabilistic $t$-time-bounded Kolmogorov complexity** $\mathsf{pK}^t_\lambda(x \mid y)$:
the minimum `k` such that with probability at least `λ` over `r ~ U_t`, there exists a program
of length at most `k` outputting `x` given `y` and `r` within `t` steps. -/
noncomputable def pTimeBoundedAt (t : ℕ) (lam : ℝ) (x y : List Bool) : ℕ∞ :=
  ⨅ (k : ℕ)
    (_ : lam ≤
      ((uniformList t).toOuterMeasure
        {r : List Bool | ∃ p : List Bool, p.length ≤ k ∧
          x ∈ randUniversalTMRunFor p y r t}).toReal),
    (k : ℕ∞)

/-- **Randomized Levin complexity** $\mathsf{rKt}_\lambda(x \mid y)$:
$\inf_{t \in \mathbb{N}} (\mathsf{rK}^t_\lambda(x \mid y) + \lceil \log_2 t \rceil)$. -/
noncomputable def rLevinKt (lam : ℝ) (x y : List Bool) : ℕ∞ :=
  ⨅ t : ℕ, rTimeBoundedAt t lam x y + (Nat.clog 2 t : ℕ∞)

/-- Witness characterization of `rTimeBoundedAt t lam x y ≤ k`. -/
theorem rTimeBoundedAt_le_natCast_iff {t : ℕ} {lam : ℝ} {x y : List Bool} {k : ℕ} :
    rTimeBoundedAt t lam x y ≤ (k : ℕ∞) ↔
      ∃ p : List Bool, p.length ≤ k ∧ lam ≤ randProgramSuccessProb p y x t := by
  constructor
  · intro h
    by_contra hnone
    push Not at hnone
    have hge : ((k + 1 : ℕ) : ℕ∞) ≤ rTimeBoundedAt t lam x y := by
      refine le_iInf fun p => le_iInf fun hp => ?_
      have hlt : k < p.length := by
        by_contra hle
        exact not_lt.mpr hp (hnone p (not_lt.mp hle))
      exact_mod_cast Nat.succ_le_of_lt hlt
    have hcontr : ((k + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞) := hge.trans h
    exact absurd (Nat.cast_le.mp hcontr) (by omega)
  · rintro ⟨p, hlen, hp⟩
    exact (iInf_le_of_le p (iInf_le _ hp)).trans (by exact_mod_cast hlen)

/-- Witness characterization of `pTimeBoundedAt t lam x y ≤ k`. -/
theorem pTimeBoundedAt_le_natCast_iff {t : ℕ} {lam : ℝ} {x y : List Bool} {k : ℕ} :
    pTimeBoundedAt t lam x y ≤ (k : ℕ∞) ↔
      lam ≤
        ((uniformList t).toOuterMeasure
          {r : List Bool | ∃ p : List Bool, p.length ≤ k ∧
            x ∈ randUniversalTMRunFor p y r t}).toReal := by
  constructor
  · intro h
    by_contra hlt
    have hge : ((k + 1 : ℕ) : ℕ∞) ≤ pTimeBoundedAt t lam x y := by
      refine le_iInf fun j => le_iInf fun hj => ?_
      have hkj : k < j := by
        by_contra hle
        have hsub : {r : List Bool | ∃ p : List Bool, p.length ≤ j ∧
            x ∈ randUniversalTMRunFor p y r t} ⊆
            {r : List Bool | ∃ p : List Bool, p.length ≤ k ∧
              x ∈ randUniversalTMRunFor p y r t} := by
          rintro r ⟨p, hp, hrun⟩
          exact ⟨p, hp.trans (not_lt.mp hle), hrun⟩
        have hmono := Cslib.Probability.PMF.toOuterMeasure_toReal_mono (uniformList t) hsub
        exact hlt (hj.trans hmono)
      exact_mod_cast Nat.succ_le_of_lt hkj
    exact absurd (Nat.cast_le.mp (hge.trans h)) (by omega)
  · intro h
    exact iInf_le_of_le k (iInf_le _ h)

/-- **Probabilistic complexity never exceeds randomized complexity**:
$\mathsf{pK}^t_\lambda(x \mid y) \le \mathsf{rK}^t_\lambda(x \mid y)$. -/
theorem pTimeBoundedAt_le_rTimeBoundedAt (t : ℕ) (lam : ℝ) (x y : List Bool) :
    pTimeBoundedAt t lam x y ≤ rTimeBoundedAt t lam x y := by
  refine le_iInf fun p => le_iInf fun hp => ?_
  have hsub : {r : List Bool | x ∈ randUniversalTMRunFor p y r t} ⊆
      {r : List Bool | ∃ q : List Bool, q.length ≤ p.length ∧
        x ∈ randUniversalTMRunFor q y r t} := fun r hr => ⟨p, le_rfl, hr⟩
  have hmono := Cslib.Probability.PMF.toOuterMeasure_toReal_mono (uniformList t) hsub
  exact pTimeBoundedAt_le_natCast_iff.mpr (hp.trans hmono)

/-- Monotonicity of `rTimeBoundedAt` in the success threshold `lam`. -/
theorem rTimeBoundedAt_mono_lam (t : ℕ) {lam₁ lam₂ : ℝ} (h : lam₁ ≤ lam₂) (x y : List Bool) :
    rTimeBoundedAt t lam₁ x y ≤ rTimeBoundedAt t lam₂ x y :=
  le_iInf fun p => le_iInf fun hp => iInf_le_of_le p (iInf_le _ (h.trans hp))

/-- Monotonicity of `pTimeBoundedAt` in the success threshold `lam`. -/
theorem pTimeBoundedAt_mono_lam (t : ℕ) {lam₁ lam₂ : ℝ} (h : lam₁ ≤ lam₂) (x y : List Bool) :
    pTimeBoundedAt t lam₁ x y ≤ pTimeBoundedAt t lam₂ x y :=
  le_iInf fun k => le_iInf fun hk => iInf_le_of_le k (iInf_le _ (h.trans hk))

/-- At step budget `0` and any positive threshold `lam > 0`, `rTimeBoundedAt 0 lam x y = ⊤`. -/
theorem rTimeBoundedAt_zero {lam : ℝ} (hlam : 0 < lam) (x y : List Bool) :
    rTimeBoundedAt 0 lam x y = ⊤ := by
  rw [eq_top_iff]
  refine le_iInf fun p => le_iInf fun hp => ?_
  exfalso
  have hzero : randProgramSuccessProb p y x 0 = 0 := by simp [randProgramSuccessProb]
  linarith

/-- At step budget `0` and any positive threshold `lam > 0`, `pTimeBoundedAt 0 lam x y = ⊤`. -/
theorem pTimeBoundedAt_zero {lam : ℝ} (hlam : 0 < lam) (x y : List Bool) :
    pTimeBoundedAt 0 lam x y = ⊤ := by
  rw [eq_top_iff]
  refine le_iInf fun k => le_iInf fun hk => ?_
  exfalso
  have hzero : ((uniformList 0).toOuterMeasure
      {r : List Bool | ∃ p : List Bool, p.length ≤ k ∧
        x ∈ randUniversalTMRunFor p y r 0}).toReal = 0 := by simp
  linarith

/-- Witness characterization of `rLevinKt lam x y ≤ k`. -/
theorem rLevinKt_le_natCast_iff {lam : ℝ} {x y : List Bool} {k : ℕ} :
    rLevinKt lam x y ≤ (k : ℕ∞) ↔
      ∃ (p : List Bool) (t : ℕ),
        p.length + Nat.clog 2 t ≤ k ∧ lam ≤ randProgramSuccessProb p y x t := by
  constructor
  · intro h
    by_contra hnone
    push Not at hnone
    have hge : ((k + 1 : ℕ) : ℕ∞) ≤ rLevinKt lam x y := by
      refine le_iInf fun t => ?_
      by_cases hct : k < Nat.clog 2 t
      · have : ((k + 1 : ℕ) : ℕ∞) ≤ (Nat.clog 2 t : ℕ∞) := by
          exact_mod_cast Nat.succ_le_of_lt hct
        exact this.trans le_add_self
      · push Not at hct
        have hrt : ((k - Nat.clog 2 t + 1 : ℕ) : ℕ∞) ≤ rTimeBoundedAt t lam x y := by
          refine le_iInf fun p => le_iInf fun hp => ?_
          have hlt : k - Nat.clog 2 t < p.length := by
            have := hnone p t
            by_contra hle
            have hsum : p.length + Nat.clog 2 t ≤ k := by omega
            exact not_lt.mpr hp (this hsum)
          exact_mod_cast Nat.succ_le_of_lt hlt
        have hsum_eq : (k + 1 : ℕ) = (k - Nat.clog 2 t + 1) + Nat.clog 2 t := by omega
        rw [hsum_eq, Nat.cast_add]
        gcongr
    exact absurd (Nat.cast_le.mp (hge.trans h)) (by omega)
  · rintro ⟨p, t, hlen, hp⟩
    refine (iInf_le _ t).trans ?_
    have h1 : rTimeBoundedAt t lam x y ≤ (p.length : ℕ∞) :=
      rTimeBoundedAt_le_natCast_iff.mpr ⟨p, le_rfl, hp⟩
    calc rTimeBoundedAt t lam x y + (Nat.clog 2 t : ℕ∞)
        ≤ (p.length : ℕ∞) + (Nat.clog 2 t : ℕ∞) := by gcongr
      _ = ((p.length + Nat.clog 2 t : ℕ) : ℕ∞) := (Nat.cast_add _ _).symm
      _ ≤ (k : ℕ∞) := by exact_mod_cast hlen

/-- `rLevinKt` upper bound from any single step budget `t`. -/
theorem rLevinKt_le_rTimeBoundedAt_add (t : ℕ) (lam : ℝ) (x y : List Bool) :
    rLevinKt lam x y ≤ rTimeBoundedAt t lam x y + (Nat.clog 2 t : ℕ∞) :=
  iInf_le _ t

/-- **Time-bounded universal distribution with advice** $\mathcal{Q}_{t, z}$:
sample a uniform `t`-bit program `w` and uniform `t`-bit randomness `r`, and evaluate
$U^{\mathsf{r}}(w, z, r, 1^t)$. -/
noncomputable def universalRandDist (t : ℕ) (z : List Bool) : PMF (Option (List Bool)) :=
  (uniformList t).bind fun w =>
    (uniformList t).map fun r => randUniversalTMRunFor w z r t

/-- Point probability mass $\mathcal{Q}_{t, z}(x)$ of a halting output string `x`. -/
noncomputable def universalDistProb (t : ℕ) (z x : List Bool) : ℝ≥0∞ :=
  universalRandDist t z (some x)

/-- $\mathcal{Q}_{t, z}(x) \le 1$. -/
theorem universalDistProb_le_one (t : ℕ) (z x : List Bool) :
    universalDistProb t z x ≤ 1 :=
  PMF.coe_le_one _ _

/-- **Time-bounded universal log-probability**
$\mathsf{q}^t(x \mid z) = -\log_2 \mathcal{Q}_{t, z}(x)$
in `ℝ≥0∞` (taking value `⊤` when $\mathcal{Q}_{t, z}(x) = 0$). -/
noncomputable def qTimeBounded (t : ℕ) (x z : List Bool) : ℝ≥0∞ :=
  if universalDistProb t z x = 0 then ⊤
  else ENNReal.ofReal (-Real.logb 2 (universalDistProb t z x).toReal)

/-- `qTimeBounded t x z = ⊤` if and only if `universalDistProb t z x = 0`. -/
theorem qTimeBounded_eq_top_iff (t : ℕ) (x z : List Bool) :
    qTimeBounded t x z = ⊤ ↔ universalDistProb t z x = 0 := by
  unfold qTimeBounded
  split_ifs with h <;> simp [h]

/-- At step budget `0`, `universalDistProb 0 z x = 0` and `qTimeBounded 0 x z = ⊤`. -/
@[simp]
theorem qTimeBounded_zero (x z : List Bool) : qTimeBounded 0 x z = ⊤ := by
  rw [qTimeBounded_eq_top_iff]
  simp [universalDistProb, universalRandDist]

/-- Conditional `universalRandDist` restricted to outputs extending `y` by at least `n` bits. -/
private noncomputable def universalExtrapolationCond (n t : ℕ) (y z : List Bool)
    (h : (universalRandDist t z).toOuterMeasure
      {o | ∃ x : List Bool, o = some x ∧ y <+: x ∧ y.length + n ≤ x.length} ≠ 0) :
    PMF (Option (List Bool)) :=
  let E : Set (Option (List Bool)) :=
    {o | ∃ x : List Bool, o = some x ∧ y <+: x ∧ y.length + n ≤ x.length}
  let mass := (universalRandDist t z).toOuterMeasure E
  ⟨fun o => if o ∈ E then universalRandDist t z o / mass else 0, by
    have hmass_ne_top : mass ≠ ⊤ :=
      Cslib.Probability.PMF.toOuterMeasure_ne_top _ _
    have htsum : (∑' o : Option (List Bool),
        if o ∈ E then universalRandDist t z o / mass else 0) =
        (∑' o : Option (List Bool),
          Set.indicator E (fun o => universalRandDist t z o) o) / mass := by
      simp_rw [div_eq_mul_inv]
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun o => ?_
      by_cases ho : o ∈ E <;> simp [ho]
    have hsum_one : (∑' o : Option (List Bool),
        if o ∈ E then universalRandDist t z o / mass else 0) = 1 := by
      rw [htsum, ← PMF.toOuterMeasure_apply, ENNReal.div_self h hmass_ne_top]
    exact hsum_one ▸ CompleteLattice.summable.hasSum⟩

/-- **Universal extrapolation distribution** $\mathsf{Next}_n(y; \mathcal{Q}_{t, z})$:
the distribution of the next `n` bits after prefix `y` of a sample from `Q_{t,z}` conditioned on
extending `y` by at least `n` bits (falling back to `uniformList n` when the conditioning event
has zero probability). -/
noncomputable def universalExtrapolationDist (n t : ℕ) (y z : List Bool) : PMF (List Bool) :=
  if h : (universalRandDist t z).toOuterMeasure
      {o | ∃ x : List Bool, o = some x ∧ y <+: x ∧ y.length + n ≤ x.length} = 0 then
    uniformList n
  else
    (universalExtrapolationCond n t y z h).map fun o =>
      match o with
      | some x => (x.drop y.length).take n
      | none => List.replicate n false

/-- Every word in the support of `universalExtrapolationDist n t y z` has exact length `n`. -/
theorem length_of_mem_support_universalExtrapolationDist {n t : ℕ} {y z w : List Bool}
    (hw : w ∈ (universalExtrapolationDist n t y z).support) : w.length = n := by
  unfold universalExtrapolationDist at hw
  split_ifs at hw with h
  · exact length_of_mem_support_uniformList hw
  · rw [PMF.mem_support_map_iff] at hw
    obtain ⟨o, ho, rfl⟩ := hw
    rw [PMF.mem_support_iff] at ho
    cases o with
    | none => simp
    | some x =>
      by_cases hmem : (some x : Option (List Bool)) ∈
          {o | ∃ x' : List Bool, o = some x' ∧ y <+: x' ∧ y.length + n ≤ x'.length}
      · rcases hmem with ⟨x', hx', _, hlen⟩
        injection hx' with hx''
        subst hx''
        simp only [List.length_take, List.length_drop]
        omega
      · exfalso
        refine ho ?_
        change (if (some x : Option (List Bool)) ∈
            {o | ∃ x', o = some x' ∧ y <+: x' ∧ y.length + n ≤ x'.length} then _ else 0) = 0
        rw [ite_eq_right_iff]
        intro hm
        exact (hmem hm).elim

/-- **Computational depth**
$\mathsf{cd}^t(y \mid z) = \mathsf{q}^t(y \mid z) - \mathsf{K}(y \mid z)$
in `EReal` (equal to `⊤` whenever $\mathcal{Q}_{t, z}(y) = 0$). -/
noncomputable def computationalDepth (t : ℕ) (y z : List Bool) : EReal :=
  if universalDistProb t z y = 0 then ⊤
  else
    ((-Real.logb 2 (universalDistProb t z y).toReal - (condPlainNat y z : ℝ)) : ℝ)

/-- **`GapK^t-vs-K ∈ prBPP`**: there exist a constant `c : ℕ` and a uniform PPT algorithm `A`
that, on input `(x, 1^t)`, outputs an integer estimate `k` satisfying
`K(x) ≤ k ≤ K^t(x) + c * (log₂ |x| + 1)` with probability at least `2 / 3`. -/
def GapKtVsKInPrBPP : Prop :=
  ∃ (c : ℕ) (A : List Bool × ℕ → ProbComp ℕ),
    IsPPTOn (encPair encBits encUnary) encUnary A ∧
      ∀ (x : List Bool) (t : ℕ),
        (2 / 3 : ℝ) ≤
          ((ProbComp.eval (A (x, t))).toOuterMeasure
            {k : ℕ | plain x ≤ (k : ℕ∞) ∧
              (k : ℕ∞) ≤ timeBoundedAt t x +
                ((c * (Nat.log 2 x.length + 1) : ℕ) : ℕ∞)}).toReal

end CslibFrontier.Computability.Kolmogorov
