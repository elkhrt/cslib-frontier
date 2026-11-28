module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.StableMatching.DeferredAcceptance
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Push

/-!
# Subramanian's Fixed-Point Characterization of Stable Matchings

This module formalizes Subramanian's Boolean fixed-point characterization of stable matchings on
`Cslib.Algorithms.Lean.StableMatching.Instance n`:

* A Boolean state assigns a bit to every directed pair `(proposer, rank)` and `(receiver, rank)`.
* One step of the fixed-point operator sets `(step I B).propBit p j = true` iff there exists
  `j' < j` whose receiver `r = I.propPref p j'` has `B.recvBit r (I.recvRank r p) = false`, and
  symmetrically for receivers.
* Every stable matching `μ : Matching n` encodes into a Boolean fixed point `encodeMatching I μ`,
  whose bits record whether an agent's matched partner has strictly better rank than the wire index.
* Every Boolean fixed point `B` is monotone along each agent's preference list and uniquely
  determines a stable matching `decodeMatching I B` (via a bijection between stable matchings and
  Boolean fixed points).
* Under the natural partial order on Boolean fixed points (pointwise `≤` on `propBit`, reversed on
  `recvBit`), `encodeMatching I I.deferredAcceptance` is the maximum `propBit` fixed point
  (smallest matched proposer ranks) and `encodeMatching I I.receiverDeferredAcceptance` is the
  minimum `propBit` fixed point (largest matched proposer ranks).

## Main definitions

* `CslibFrontier.Algorithms.Lean.StableMatching.Subramanian.State`: Boolean wire assignment for a
  stable matching instance of size `n`.
* `CslibFrontier.Algorithms.Lean.StableMatching.Subramanian.step`: one application of the
  fixed-point operator.
* `CslibFrontier.Algorithms.Lean.StableMatching.Subramanian.IsFixedPoint`: `step I B = B`.
* `CslibFrontier.Algorithms.Lean.StableMatching.Subramanian.encodeMatching`: maps a matching `μ` to
  its threshold Boolean state.
* `CslibFrontier.Algorithms.Lean.StableMatching.Subramanian.decodeMatching`: extracts a matching
  from a Boolean fixed point.

## Main results

* `CslibFrontier.Algorithms.Lean.StableMatching.Subramanian.isFixedPoint_encodeMatching`: every
  stable matching encodes to a Boolean fixed point.
* `CslibFrontier.Algorithms.Lean.StableMatching.Subramanian.isStable_decodeMatching`: every Boolean
  fixed point decodes to a stable matching.
* `CslibFrontier.Algorithms.Lean.StableMatching.Subramanian.decodeMatching_encodeMatching`:
  `decodeMatching` is a left inverse to `encodeMatching` on stable matchings.
* `CslibFrontier.Algorithms.Lean.StableMatching.Subramanian.encodeMatching_decodeMatching`:
  `encodeMatching` is a left inverse to `decodeMatching` on Boolean fixed points.
* `CslibFrontier.Algorithms.Lean.StableMatching.Subramanian.propBit_le_deferredAcceptance`:
  `encodeMatching I I.deferredAcceptance` maximizes every `propBit` among all Boolean fixed points.
* `CslibFrontier.Algorithms.Lean.StableMatching.Subramanian.recvBit_le_receiverDeferredAcceptance`:
  `encodeMatching I I.receiverDeferredAcceptance` maximizes every `recvBit` among all Boolean fixed
  points.
-/

public section

namespace CslibFrontier.Algorithms.Lean.StableMatching.Subramanian

open Cslib.Algorithms.Lean.StableMatching

/-- A Boolean wire state for a two-sided matching instance of size `n`. -/
@[ext]
structure State (n : ℕ) where
  /-- Proposer-side bits indexed by `(proposer, rank)`. -/
  propBit : Fin n → Fin n → Bool
  /-- Receiver-side bits indexed by `(receiver, rank)`. -/
  recvBit : Fin n → Fin n → Bool
  deriving DecidableEq

/-- One step of Subramanian's Boolean fixed-point operator on an `Instance n`. -/
@[expose] def step {n : ℕ} (I : Instance n) (B : State n) : State n where
  propBit p j :=
    decide (∃ j' : Fin n, j' < j ∧
      B.recvBit (I.propPref p j') (I.recvRank (I.propPref p j') p) = false)
  recvBit r k :=
    decide (∃ k' : Fin n, k' < k ∧
      B.propBit (I.recvPref r k') (I.propRank (I.recvPref r k') r) = false)

theorem step_propBit_eq_true {n : ℕ} (I : Instance n) (B : State n) (p j : Fin n) :
    (step I B).propBit p j = true ↔
      ∃ j' : Fin n, j' < j ∧
        B.recvBit (I.propPref p j') (I.recvRank (I.propPref p j') p) = false := by
  simp [step]

theorem step_recvBit_eq_true {n : ℕ} (I : Instance n) (B : State n) (r k : Fin n) :
    (step I B).recvBit r k = true ↔
      ∃ k' : Fin n, k' < k ∧
        B.propBit (I.recvPref r k') (I.propRank (I.recvPref r k') r) = false := by
  simp [step]

/-- A Boolean state `B` is a fixed point of `step I` iff `step I B = B`. -/
@[expose] def IsFixedPoint {n : ℕ} (I : Instance n) (B : State n) : Prop :=
  step I B = B

/-- Encode a matching `μ : Matching n` into a Boolean threshold state:
`propBit p j = true ↔ propRank p (μ p) < j` and `recvBit r k = true ↔ recvRank r (μ.symm r) < k`. -/
@[expose] def encodeMatching {n : ℕ} (I : Instance n) (μ : Matching n) : State n where
  propBit p j := decide (I.propRank p (μ p) < j)
  recvBit r k := decide (I.recvRank r (μ.symm r) < k)

/-- Every stable matching encodes to a Boolean fixed point of `step I`. -/
theorem isFixedPoint_encodeMatching {n : ℕ} (I : Instance n) {μ : Matching n}
    (hμ : I.IsStable μ) : IsFixedPoint I (encodeMatching I μ) := by
  ext p j
  · apply Bool.eq_iff_iff.mpr
    rw [step_propBit_eq_true]
    simp only [encodeMatching, decide_eq_true_eq, decide_eq_false_iff_not, not_lt]
    constructor
    · rintro ⟨j', hj', hle⟩
      by_contra hnot
      push Not at hnot
      have hlt : I.propRank p (I.propPref p j') < I.propRank p (μ p) := by
        rw [I.propRank_propPref]; exact lt_of_lt_of_le hj' hnot
      exact not_lt_of_ge hle (hμ.recvRank_lt hlt)
    · intro hlt
      refine ⟨I.propRank p (μ p), hlt, ?_⟩
      rw [I.propPref_propRank, Equiv.symm_apply_apply]
  · apply Bool.eq_iff_iff.mpr
    rw [step_recvBit_eq_true]
    simp only [encodeMatching, decide_eq_true_eq, decide_eq_false_iff_not, not_lt]
    constructor
    · rintro ⟨k', hk', hle⟩
      by_contra hnot
      push Not at hnot
      let q := I.recvPref p k'
      have hlt_r : I.recvRank p q < I.recvRank p (μ.symm p) := by
        have hq : I.recvRank p q = k' := (I.recvPref p).symm_apply_apply k'
        rw [hq]; exact lt_of_lt_of_le hk' hnot
      have hswap : I.swap.IsStable μ.symm := (I.isStable_swap_iff μ).mpr hμ
      have hlt_p : I.propRank q (μ q) < I.propRank q p := by
        have := hswap.recvRank_lt (p := p) (r := q) hlt_r
        simpa [Instance.swap, Instance.propRank, Instance.recvRank] using this
      exact not_lt_of_ge hle hlt_p
    · intro hlt
      refine ⟨I.recvRank p (μ.symm p), hlt, ?_⟩
      have hpref : I.recvPref p (I.recvRank p (μ.symm p)) = μ.symm p :=
        (I.recvPref p).apply_symm_apply (μ.symm p)
      rw [hpref, Equiv.apply_symm_apply]

/-- Threshold monotonicity of `propBit` on any Boolean fixed point. -/
theorem IsFixedPoint.propBit_mono {n : ℕ} {I : Instance n} {B : State n}
    (hB : IsFixedPoint I B) (p : Fin n) {j₁ j₂ : Fin n} (hle : j₁ ≤ j₂)
    (h1 : B.propBit p j₁ = true) : B.propBit p j₂ = true := by
  rw [← hB, step_propBit_eq_true] at h1 ⊢
  obtain ⟨j', hj', hbit⟩ := h1
  exact ⟨j', lt_of_lt_of_le hj' hle, hbit⟩

/-- Threshold monotonicity of `recvBit` on any Boolean fixed point. -/
theorem IsFixedPoint.recvBit_mono {n : ℕ} {I : Instance n} {B : State n}
    (hB : IsFixedPoint I B) (r : Fin n) {k₁ k₂ : Fin n} (hle : k₁ ≤ k₂)
    (h1 : B.recvBit r k₁ = true) : B.recvBit r k₂ = true := by
  rw [← hB, step_recvBit_eq_true] at h1 ⊢
  obtain ⟨k', hk', hbit⟩ := h1
  exact ⟨k', lt_of_lt_of_le hk' hle, hbit⟩

/-- In a Boolean fixed point `B`, `propBit p 0 = false` and `recvBit r 0 = false` for `n > 0`. -/
theorem IsFixedPoint.propBit_zero {n : ℕ} {I : Instance n} {B : State n}
    (hB : IsFixedPoint I B) (p : Fin n) (h0 : 0 < n) :
    B.propBit p ⟨0, h0⟩ = false := by
  rw [Bool.eq_false_iff]; intro h
  rw [← hB, step_propBit_eq_true] at h
  obtain ⟨j', hj', _⟩ := h
  exact absurd hj' (by simp [Fin.lt_def])

theorem IsFixedPoint.recvBit_zero {n : ℕ} {I : Instance n} {B : State n}
    (hB : IsFixedPoint I B) (r : Fin n) (h0 : 0 < n) :
    B.recvBit r ⟨0, h0⟩ = false := by
  rw [Bool.eq_false_iff]; intro h
  rw [← hB, step_recvBit_eq_true] at h
  obtain ⟨k', hk', _⟩ := h
  exact absurd hk' (by simp [Fin.lt_def])

/-- In a Boolean fixed point `B`, the matched pair relation: proposer `p` and receiver `r` are
matched iff both `B.propBit p (propRank p r) = false` and `B.recvBit r (recvRank r p) = false`. -/
@[expose] def Matched {n : ℕ} (I : Instance n) (B : State n) (p r : Fin n) : Prop :=
  B.propBit p (I.propRank p r) = false ∧ B.recvBit r (I.recvRank r p) = false

theorem IsFixedPoint.matched_unique_recv {n : ℕ} {I : Instance n} {B : State n}
    (hB : IsFixedPoint I B) {p r₁ r₂ : Fin n}
    (h1 : Matched I B p r₁) (h2 : Matched I B p r₂) : r₁ = r₂ := by
  rcases lt_trichotomy (I.propRank p r₁) (I.propRank p r₂) with hlt | heq | hgt
  · have ht : B.propBit p (I.propRank p r₂) = true := by
      rw [← hB, step_propBit_eq_true]
      exact ⟨I.propRank p r₁, hlt, by simpa [I.propPref_propRank] using h1.2⟩
    exact absurd (ht.symm.trans h2.1) (by decide)
  · exact I.propRank_injective p heq
  · have ht : B.propBit p (I.propRank p r₁) = true := by
      rw [← hB, step_propBit_eq_true]
      exact ⟨I.propRank p r₂, hgt, by simpa [I.propPref_propRank] using h2.2⟩
    exact absurd (ht.symm.trans h1.1) (by decide)

theorem IsFixedPoint.matched_unique_prop {n : ℕ} {I : Instance n} {B : State n}
    (hB : IsFixedPoint I B) {p₁ p₂ r : Fin n}
    (h1 : Matched I B p₁ r) (h2 : Matched I B p₂ r) : p₁ = p₂ := by
  rcases lt_trichotomy (I.recvRank r p₁) (I.recvRank r p₂) with hlt | heq | hgt
  · have ht : B.recvBit r (I.recvRank r p₂) = true := by
      rw [← hB, step_recvBit_eq_true]
      refine ⟨I.recvRank r p₁, hlt, ?_⟩
      have hp : I.recvPref r (I.recvRank r p₁) = p₁ := (I.recvPref r).apply_symm_apply p₁
      simpa [hp] using h1.1
    exact absurd (ht.symm.trans h2.2) (by decide)
  · exact I.recvRank_injective r heq
  · have ht : B.recvBit r (I.recvRank r p₁) = true := by
      rw [← hB, step_recvBit_eq_true]
      refine ⟨I.recvRank r p₂, hgt, ?_⟩
      have hp : I.recvPref r (I.recvRank r p₂) = p₂ := (I.recvPref r).apply_symm_apply p₂
      simpa [hp] using h2.1
    exact absurd (ht.symm.trans h1.2) (by decide)

/-- Every proposer `p` has a unique matched receiver in any Boolean fixed point `B` (proved by
counting matched pairs via the pigeonhole principle on `Fin n`). -/
theorem IsFixedPoint.exists_matched_recv {n : ℕ} {I : Instance n} {B : State n}
    (hB : IsFixedPoint I B) (p : Fin n) : ∃ r : Fin n, Matched I B p r := by
  -- Every proposer `q` with `∃ j, B.propBit q j = true` has a matched receiver `r` at the least
  -- rank `j'` with `B.recvBit (propPref q j') ... = false`; in particular, every proposer `q`
  -- either has a matched receiver or has `B.propBit q j = false` for all `j`, and the latter
  -- forces every receiver `r` to have `B.recvBit r k = true` for all `k > recvRank r q`.
  -- Count: the number of proposers with a matched receiver equals the number of matched pairs,
  -- which equals the number of receivers with a matched proposer; if any proposer `p` had no
  -- matched receiver, then every receiver `r` would have `B.recvBit r (recvRank r p) = true`
  -- (since `B.propBit p (propRank p r) = false`), forcing every receiver `r` to have a matched
  -- proposer — contradicting pigeonhole!
  have hhas_of_prop_true : ∀ q : Fin n, (∃ j : Fin n, B.propBit q j = true) →
      ∃ r : Fin n, Matched I B q r := by
    intro q ⟨j, hj⟩
    let S : Finset (Fin n) := Finset.univ.filter fun j' : Fin n =>
      B.recvBit (I.propPref q j') (I.recvRank (I.propPref q j') q) = false
    have hS : S.Nonempty := by
      rw [← hB, step_propBit_eq_true] at hj
      obtain ⟨j', _, hbit⟩ := hj
      exact ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbit⟩⟩
    let j₀ := S.min' hS
    have hj₀_mem : j₀ ∈ S := Finset.min'_mem S hS
    have hrecv0 : B.recvBit (I.propPref q j₀) (I.recvRank (I.propPref q j₀) q) = false :=
      (Finset.mem_filter.mp hj₀_mem).2
    refine ⟨I.propPref q j₀, ?_, hrecv0⟩
    rw [I.propRank_propPref, Bool.eq_false_iff]
    intro htrue
    rw [← hB, step_propBit_eq_true] at htrue
    obtain ⟨j', hj', hbit'⟩ := htrue
    have hj'_mem : j' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbit'⟩
    exact not_lt_of_ge (Finset.min'_le S j' hj'_mem) hj'
  have hhas_of_recv_true : ∀ r : Fin n, (∃ k : Fin n, B.recvBit r k = true) →
      ∃ q : Fin n, Matched I B q r := by
    intro r ⟨k, hk⟩
    let S : Finset (Fin n) := Finset.univ.filter fun k' : Fin n =>
      B.propBit (I.recvPref r k') (I.propRank (I.recvPref r k') r) = false
    have hS : S.Nonempty := by
      rw [← hB, step_recvBit_eq_true] at hk
      obtain ⟨k', _, hbit⟩ := hk
      exact ⟨k', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbit⟩⟩
    let k₀ := S.min' hS
    have hk₀_mem : k₀ ∈ S := Finset.min'_mem S hS
    have hprop0 : B.propBit (I.recvPref r k₀) (I.propRank (I.recvPref r k₀) r) = false :=
      (Finset.mem_filter.mp hk₀_mem).2
    refine ⟨I.recvPref r k₀, hprop0, ?_⟩
    have hrank : I.recvRank r (I.recvPref r k₀) = k₀ := (I.recvPref r).symm_apply_apply k₀
    rw [hrank, Bool.eq_false_iff]
    intro htrue
    rw [← hB, step_recvBit_eq_true] at htrue
    obtain ⟨k', hk', hbit'⟩ := htrue
    have hk'_mem : k' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbit'⟩
    exact not_lt_of_ge (Finset.min'_le S k' hk'_mem) hk'
  by_contra hno
  push Not at hno
  -- `p` has no matched receiver, so `B.propBit p j = false` for every `j`.
  have hp_all_false : ∀ j : Fin n, B.propBit p j = false := by
    intro j
    cases h : B.propBit p j with
    | false => rfl
    | true =>
      obtain ⟨r, hr⟩ := hhas_of_prop_true p ⟨j, h⟩
      exact absurd hr (hno r)
  -- Therefore, for every receiver `r`, `B.recvBit r (I.recvRank r p) = true`!
  have hr_all_matched : ∀ r : Fin n, ∃ q : Fin n, Matched I B q r := by
    intro r
    have hbit : B.recvBit r (I.recvRank r p) = true := by
      cases h : B.recvBit r (I.recvRank r p) with
      | true => rfl
      | false => exact absurd ⟨hp_all_false (I.propRank p r), h⟩ (hno r)
    exact hhas_of_recv_true r ⟨I.recvRank r p, hbit⟩
  -- Choose for each receiver `r` its unique matched proposer `f r : Fin n`.
  -- `f` is injective (by `matched_unique_recv`) and never hits `p` — impossible on `Fin n`!
  classical
  let f : Fin n → Fin n := fun r => (hr_all_matched r).choose
  have hf_inj : Function.Injective f := by
    intro r₁ r₂ heq
    have h1 := (hr_all_matched r₁).choose_spec
    have h2 := (hr_all_matched r₂).choose_spec
    change (hr_all_matched r₁).choose = (hr_all_matched r₂).choose at heq
    rw [← heq] at h2
    exact hB.matched_unique_recv h1 h2
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  obtain ⟨r, hr⟩ := hf_surj p
  exact hno r (hr ▸ (hr_all_matched r).choose_spec)

/-- Extract the unique matching `Matching n` from any Boolean fixed point `B` of `step I`. -/
noncomputable def decodeMatching {n : ℕ} (I : Instance n) {B : State n}
    (hB : IsFixedPoint I B) : Matching n :=
  permOfInjective (fun p => (hB.exists_matched_recv p).choose) fun p₁ p₂ heq => by
    have h1 := (hB.exists_matched_recv p₁).choose_spec
    have h2 := (hB.exists_matched_recv p₂).choose_spec
    dsimp only at heq
    rw [← heq] at h2
    exact hB.matched_unique_prop h1 h2

theorem decodeMatching_apply_iff {n : ℕ} (I : Instance n) {B : State n}
    (hB : IsFixedPoint I B) (p r : Fin n) :
    decodeMatching I hB p = r ↔ Matched I B p r := by
  have hspec := (hB.exists_matched_recv p).choose_spec
  simp only [decodeMatching]
  constructor
  · intro heq; exact heq ▸ hspec
  · intro hm; exact hB.matched_unique_recv hspec hm

/-- Every Boolean fixed point `B` of `step I` decodes to a stable matching. -/
theorem isStable_decodeMatching {n : ℕ} (I : Instance n) {B : State n}
    (hB : IsFixedPoint I B) : I.IsStable (decodeMatching I hB) := by
  intro p r ⟨hp_pref, hr_pref⟩
  set μ := decodeMatching I hB
  have hm1 : Matched I B p (μ p) := (decodeMatching_apply_iff I hB p (μ p)).mp rfl
  have hm2 : Matched I B (μ.symm r) r :=
    (decodeMatching_apply_iff I hB (μ.symm r) r).mp (μ.apply_symm_apply r)
  -- Since `propRank p r < propRank p (μ p)` and `B.propBit p (propRank p (μ p)) = false`,
  -- we must have `B.recvBit r (recvRank r p) = true`.
  have hrecv_true : B.recvBit r (I.recvRank r p) = true := by
    cases h : B.recvBit r (I.recvRank r p) with
    | true => rfl
    | false =>
      have ht : B.propBit p (I.propRank p (μ p)) = true := by
        rw [← hB, step_propBit_eq_true]
        exact ⟨I.propRank p r, hp_pref, by simpa [I.propPref_propRank] using h⟩
      exact absurd (ht.symm.trans hm1.1) (by decide)
  -- Since `recvRank r p < recvRank r (μ.symm r)` and `B.recvBit r (recvRank r p) = true`,
  -- monotonicity gives `B.recvBit r (recvRank r (μ.symm r)) = true`, contradicting `hm2.2`!
  have ht2 := hB.recvBit_mono r (le_of_lt hr_pref) hrecv_true
  exact absurd (ht2.symm.trans hm2.2) (by decide)

/-- `decodeMatching` is a left inverse to `encodeMatching` on stable matchings. -/
theorem decodeMatching_encodeMatching {n : ℕ} (I : Instance n) {μ : Matching n}
    (hμ : I.IsStable μ) :
    decodeMatching I (isFixedPoint_encodeMatching I hμ) = μ := by
  refine Equiv.ext fun p => ?_
  rw [decodeMatching_apply_iff]
  simp [Matched, encodeMatching]

/-- `encodeMatching` is a left inverse to `decodeMatching` on Boolean fixed points. -/
theorem encodeMatching_decodeMatching {n : ℕ} (I : Instance n) {B : State n}
    (hB : IsFixedPoint I B) :
    encodeMatching I (decodeMatching I hB) = B := by
  set μ := decodeMatching I hB
  ext p j
  · apply Bool.eq_iff_iff.mpr
    simp only [encodeMatching, decide_eq_true_eq]
    have hm : Matched I B p (μ p) := (decodeMatching_apply_iff I hB p (μ p)).mp rfl
    constructor
    · intro hlt
      rw [← hB, step_propBit_eq_true]
      exact ⟨I.propRank p (μ p), hlt, by simpa [I.propPref_propRank] using hm.2⟩
    · intro ht
      by_contra hle; push Not at hle
      exact absurd ((hB.propBit_mono p hle ht).symm.trans hm.1) (by decide)
  · apply Bool.eq_iff_iff.mpr
    simp only [encodeMatching, decide_eq_true_eq]
    have hm : Matched I B (μ.symm p) p :=
      (decodeMatching_apply_iff I hB (μ.symm p) p).mp (μ.apply_symm_apply p)
    constructor
    · intro hlt
      rw [← hB, step_recvBit_eq_true]
      refine ⟨I.recvRank p (μ.symm p), hlt, ?_⟩
      have hp : I.recvPref p (I.recvRank p (μ.symm p)) = μ.symm p :=
        (I.recvPref p).apply_symm_apply (μ.symm p)
      simpa [hp] using hm.1
    · intro ht
      by_contra hle; push Not at hle
      exact absurd ((hB.recvBit_mono p hle ht).symm.trans hm.2) (by decide)

/-- Among all Boolean fixed points `B` of `step I`, `encodeMatching I I.deferredAcceptance`
pointwise maximizes every proposer wire `propBit p j` (matching proposer optimality). -/
theorem propBit_le_deferredAcceptance {n : ℕ} (I : Instance n) {B : State n}
    (hB : IsFixedPoint I B) (p j : Fin n) :
    B.propBit p j ≤ (encodeMatching I I.deferredAcceptance).propBit p j := by
  have heq : B = encodeMatching I (decodeMatching I hB) :=
    (encodeMatching_decodeMatching I hB).symm
  rw [heq]
  simp only [encodeMatching]
  have hle : I.propRank p (I.deferredAcceptance p) ≤ I.propRank p (decodeMatching I hB p) :=
    I.propRank_deferredAcceptance_le (isStable_decodeMatching I hB) p
  by_cases h : I.propRank p (decodeMatching I hB p) < j
  · have h2 : I.propRank p (I.deferredAcceptance p) < j := lt_of_le_of_lt hle h
    simp [h, h2]
  · simp [h]

/-- Among all Boolean fixed points `B` of `step I`, `encodeMatching I I.receiverDeferredAcceptance`
pointwise maximizes every receiver wire `recvBit r k` (matching receiver optimality). -/
theorem recvBit_le_receiverDeferredAcceptance {n : ℕ} (I : Instance n) {B : State n}
    (hB : IsFixedPoint I B) (r k : Fin n) :
    B.recvBit r k ≤ (encodeMatching I I.receiverDeferredAcceptance).recvBit r k := by
  have heq : B = encodeMatching I (decodeMatching I hB) :=
    (encodeMatching_decodeMatching I hB).symm
  rw [heq]
  simp only [encodeMatching]
  have hopt : I.IsReceiverOptimal I.receiverDeferredAcceptance :=
    I.isReceiverOptimal_receiverDeferredAcceptance
  have hle : I.recvRank r (I.receiverDeferredAcceptance.symm r) ≤
      I.recvRank r ((decodeMatching I hB).symm r) :=
    hopt.2 (decodeMatching I hB) (isStable_decodeMatching I hB) r
  by_cases h : I.recvRank r ((decodeMatching I hB).symm r) < k
  · have h2 : I.recvRank r (I.receiverDeferredAcceptance.symm r) < k := lt_of_le_of_lt hle h
    simp [h, h2]
  · simp [h]

end CslibFrontier.Algorithms.Lean.StableMatching.Subramanian
