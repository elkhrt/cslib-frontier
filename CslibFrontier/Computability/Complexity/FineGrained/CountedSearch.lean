/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Tactic.Linarith

/-!
# Counted Polynomial-Space Exhaustive Search

This module provides a reusable fine-grained time-and-space combinator for exhaustive search over
a countable search space whose size `count a` is computable in polynomial time (in binary) and
whose index-testing predicate `check (a, r)` is computable in polynomial time.

Using `Turing.MultiTapeTM.ComputableInO.iterate` with a binary loop counter, the existential search
problem `{ a | ∃ r < count a, check (a, r) = true }` is decided in:
- **Time**: `O((count a + 1) * ((encA a).length + 1) ^ e)`
- **Space**: `O(((encA a).length + 1) ^ e)` (polynomial workspace, never materializing a unary
  counter of length `count a`).

## Main results

* `Cslib.Complexity.decidableInTimeAndSpace_countedSearch`: general polynomial-space,
  `O*(count a)`-time decider for counted existential search.
* `Cslib.Complexity.decidableInTimeO_countedSearch`: `DecidableInTimeO` corollary.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- State update of a counted existential search: advances the binary index `r` and accumulates
`found || check (a, r)`. -/
private def countedSearchStep {α : Type} (check : α × ℕ → Bool) (s : (α × ℕ) × Bool) :
    (α × ℕ) × Bool :=
  ((s.1.1, s.1.2 + 1), s.2 || check s.1)

private theorem iterate_countedSearchStep {α : Type} (check : α × ℕ → Bool) (a : α) :
    ∀ k : ℕ, (countedSearchStep check)^[k] ((a, 0), false) =
      ((a, k), decide (∃ r < k, check (a, r) = true)) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [countedSearchStep]
    refine Prod.ext rfl ?_
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_iff]
    constructor
    · rintro (⟨r, hr, hcr⟩ | hck)
      · exact ⟨r, Nat.lt_succ_of_lt hr, hcr⟩
      · exact ⟨k, Nat.lt_succ_self k, hck⟩
    · rintro ⟨r, hr, hcr⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | rfl
      · exact Or.inl ⟨r, hlt, hcr⟩
      · exact Or.inr hcr

/-- **Counted polynomial-space search**: If `count : α → ℕ` (binary `encNat`) and
`check : α × ℕ → Bool` are computable in polynomial time, then the existential search language
`{ a | ∃ r < count a, check (a, r) = true }` is decidable simultaneously in
`O((count a + 1) * (|encA a| + 1)^e)` time and `O((|encA a| + 1)^e)` space. -/
public theorem decidableInTimeAndSpace_countedSearch {α : Type} [Inhabited α]
    {encA : α ↪ List Bool} {count : α → ℕ} {check : α × ℕ → Bool}
    (hcount : ComputableInPolyTime count encA encNat)
    (hcheck : ComputableInPolyTime check (encPair encA encNat) encBool) :
    ∃ e c : ℕ, DecidableInTimeAndSpace
      { a | ∃ r < count a, check (a, r) = true } encA
      (fun a => c * ((count a + 1) * ((encA a).length + 1) ^ e))
      (fun a => c * ((encA a).length + 1) ^ e) := by
  let encS := encPair (encPair encA encNat) encBool
  -- Step function is computable in polynomial time.
  have hstep_poly : ComputableInPolyTime (countedSearchStep check) encS encS := by
    unfold countedSearchStep
    have h1 : ComputableInPolyTime (fun s : (α × ℕ) × Bool => s.1.1) encS encA := by fun_prop
    have h2 : ComputableInPolyTime (fun s : (α × ℕ) × Bool => s.1.2 + 1) encS encNat :=
      ComputableInPolyTime.binary_add' (by fun_prop) (ComputableInPolyTime.const 1)
    have h3 : ComputableInPolyTime (fun s : (α × ℕ) × Bool => s.2 || check s.1) encS encBool :=
      ComputableInPolyTime.bool_or.comp
        ((by fun_prop : ComputableInPolyTime (fun s : (α × ℕ) × Bool => s.2) encS encBool).prod
          (hcheck.comp (by fun_prop)))
    exact (h1.prod h2).prod h3
  -- Extract degree/space bounds for `count` and `step`.
  obtain ⟨dc, _, hcount_deg⟩ := hcount.exists_degree
  obtain ⟨ds, _, hstep_deg⟩ := hstep_poly.exists_degree
  have hcount_inO := hcount_deg.inO
  have hstep_inO := hstep_deg.inO
  have hinit_poly : ComputableInPolyTime (fun a : α => ((a, 0), false)) encA encS :=
    ((by fun_prop : ComputableInPolyTime (fun a : α => a) encA encA).prod
      (ComputableInPolyTime.const 0)).prod (ComputableInPolyTime.const false)
  obtain ⟨di, _, hinit_deg⟩ := hinit_poly.exists_degree
  have hinit_inO := hinit_deg.inO
  -- Bound the binary encoding length of `count a` by a polynomial in `|encA a|`.
  have hcount_len : ∃ K : ℕ, ∀ a : α,
      (encNat (count a)).length ≤ K * ((encA a).length + 1) ^ dc := by
    obtain ⟨c₀, _, hlen⟩ := hcount_inO
    refine ⟨2 * c₀ + 1, fun a => ?_⟩
    have h1 := hlen a
    have hpos : 1 ≤ ((encA a).length + 1) ^ dc := Nat.one_le_pow _ _ (Nat.succ_pos _)
    nlinarith
  obtain ⟨Kc, hKc⟩ := hcount_len
  -- Bound intermediate state lengths `(encS (step^[k] (init a))).length` for `k ≤ count a`.
  have hstate_len : ∀ a : α, ∀ k ≤ count a,
      (encS ((countedSearchStep check)^[k] ((a, 0), false))).length ≤
        4 * (encA a).length + 2 * (Kc * ((encA a).length + 1) ^ dc) + 8 := by
    intro a k hk
    rw [iterate_countedSearchStep]
    have hlen_k : (encNat k).length ≤ (encNat (count a)).length :=
      length_encNat_mono hk
    have := hKc a
    simp only [encS, length_encPair, encBool_apply, List.length_singleton]
    omega
  let B (a : α) : ℕ := 4 * (encA a).length + 2 * (Kc * ((encA a).length + 1) ^ dc) + 8
  let R (a : α) : ℕ := (B a + 1) ^ ds
  have hiter := ComputableInO.iterate hcount_inO hinit_inO hstep_inO
    (fun a k hk => Nat.pow_le_pow_left (Nat.add_le_add_right (hstate_len a k hk) 1) ds)
    (fun a k hk => Nat.pow_le_pow_left (Nat.add_le_add_right (hstate_len a k hk) 1) ds)
    hstate_len
  have hdec := hiter.snd'
  -- Unpack `ComputableInO` to get explicit polynomial exponent `e` and constant `c`.
  obtain ⟨c0, htm, -⟩ := hdec
  let e : ℕ := max (max dc di) ((dc + 1) * ds + 2 * dc + 2) + 2
  have hL1 : ∀ a : α, 1 ≤ (encA a).length + 1 := fun _ => Nat.succ_pos _
  have hpow_mono : ∀ (a : α) {k : ℕ}, k ≤ e →
      ((encA a).length + 1) ^ k ≤ ((encA a).length + 1) ^ e :=
    fun a _ hk => Nat.pow_le_pow_right (hL1 a) hk
  let K : ℕ := 2 * Kc + 13
  have hB_le : ∀ a : α, B a + 1 ≤ K * ((encA a).length + 1) ^ (dc + 1) := by
    intro a
    dsimp only [B, K]
    have h1 : (encA a).length ≤ ((encA a).length + 1) ^ (dc + 1) :=
      le_trans (Nat.le_succ _) (Nat.le_self_pow (Nat.succ_ne_zero _) _)
    have h2 : ((encA a).length + 1) ^ dc ≤ ((encA a).length + 1) ^ (dc + 1) :=
      Nat.pow_le_pow_right (hL1 a) (Nat.le_succ _)
    have h3 : (1 : ℕ) ≤ ((encA a).length + 1) ^ (dc + 1) := Nat.one_le_pow _ _ (hL1 a)
    nlinarith
  have hR_le : ∀ a : α, R a ≤ K ^ ds * ((encA a).length + 1) ^ ((dc + 1) * ds) := by
    intro a
    calc R a = (B a + 1) ^ ds := rfl
      _ ≤ (K * ((encA a).length + 1) ^ (dc + 1)) ^ ds := Nat.pow_le_pow_left (hB_le a) ds
      _ = K ^ ds * ((encA a).length + 1) ^ ((dc + 1) * ds) := by rw [mul_pow, ← pow_mul]
  have hclen_le : ∀ a : α, ((encNat (count a)).length + 1) ^ 2 ≤
      (Kc + 1) ^ 2 * ((encA a).length + 1) ^ (2 * dc) := by
    intro a
    have h1 : (encNat (count a)).length + 1 ≤ (Kc + 1) * ((encA a).length + 1) ^ dc := by
      have := hKc a
      have hpos : (1 : ℕ) ≤ ((encA a).length + 1) ^ dc := Nat.one_le_pow _ _ (hL1 a)
      nlinarith
    calc ((encNat (count a)).length + 1) ^ 2
        ≤ ((Kc + 1) * ((encA a).length + 1) ^ dc) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = (Kc + 1) ^ 2 * ((encA a).length + 1) ^ (2 * dc) := by
          rw [mul_pow, ← pow_mul, mul_comm dc 2]
  have hA : ∀ a : α, a ∈ { a | ∃ r < count a, check (a, r) = true } ↔
      (((countedSearchStep check)^[count a] ((a, 0), false)).2) = true := by
    intro a
    rw [iterate_countedSearchStep]
    simp
  have h_e_dc : dc ≤ e := by dsimp only [e]; omega
  have h_e_di : di ≤ e := by dsimp only [e]; omega
  have h_e_dc1 : dc + 1 ≤ e := by dsimp only [e]; omega
  have h_e_ds : (dc + 1) * ds ≤ e := by dsimp only [e]; omega
  have h_e_2dc : 2 * dc ≤ e := by dsimp only [e]; omega
  let C : ℕ := c0 * (K ^ ds + K + (Kc + 1) ^ 2 + 10) + c0 + 1
  refine ⟨e, C, decidableInTimeAndSpace_iff.mpr ⟨_, ComputableInTimeAndSpace.mono htm
    (fun a => ?_) (fun a => ?_), hA⟩⟩
  · -- Time bound
    dsimp only [C]
    have h1 := hpow_mono a h_e_dc
    have h2 := hpow_mono a h_e_di
    have h3 := le_trans (hR_le a) (Nat.mul_le_mul_left _ (hpow_mono a h_e_ds))
    have h4 := le_trans (hB_le a) (Nat.mul_le_mul_left _ (hpow_mono a h_e_dc1))
    have h5 := le_trans (hclen_le a) (Nat.mul_le_mul_left _ (hpow_mono a h_e_2dc))
    have h6 : (1 : ℕ) ≤ ((encA a).length + 1) ^ e := Nat.one_le_pow _ _ (hL1 a)
    have h8 : ((encA a).length + 1) ^ e ≤ (count a + 1) * ((encA a).length + 1) ^ e :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    dsimp only [R, B] at h3 h4
    have hinner : ((encA a).length + 1) ^ dc + ((encA a).length + 1) ^ di +
        (count a + 1) *
          ((4 * (encA a).length + 2 * (Kc * ((encA a).length + 1) ^ dc) + 8 + 1) ^ ds +
            (4 * (encA a).length + 2 * (Kc * ((encA a).length + 1) ^ dc) + 8) +
            ((encNat (count a)).length + 1) ^ 2) + 1 ≤
        (K ^ ds + K + (Kc + 1) ^ 2 + 10) * ((count a + 1) * ((encA a).length + 1) ^ e) := by
      nlinarith
    have hmul := Nat.mul_le_mul_left c0 hinner
    have hge : c0 * ((K ^ ds + K + (Kc + 1) ^ 2 + 10) *
        ((count a + 1) * ((encA a).length + 1) ^ e)) ≤
        (c0 * (K ^ ds + K + (Kc + 1) ^ 2 + 10) + c0 + 1) *
          ((count a + 1) * ((encA a).length + 1) ^ e) := by
      rw [← mul_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    exact le_trans hmul hge
  · -- Space bound
    dsimp only [C]
    have h1 := hpow_mono a h_e_dc
    have h2 := hpow_mono a h_e_di
    have h3 := le_trans (hR_le a) (Nat.mul_le_mul_left _ (hpow_mono a h_e_ds))
    have h4 := le_trans (hB_le a) (Nat.mul_le_mul_left _ (hpow_mono a h_e_dc1))
    have h5 := le_trans (hKc a) (Nat.mul_le_mul_left _ (hpow_mono a h_e_dc))
    have h6 : (1 : ℕ) ≤ ((encA a).length + 1) ^ e := Nat.one_le_pow _ _ (hL1 a)
    dsimp only [R, B] at h3 h4
    have hinner : ((encA a).length + 1) ^ dc + ((encA a).length + 1) ^ di +
        (4 * (encA a).length + 2 * (Kc * ((encA a).length + 1) ^ dc) + 8 + 1) ^ ds +
        (4 * (encA a).length + 2 * (Kc * ((encA a).length + 1) ^ dc) + 8) +
        (encNat (count a)).length + 1 ≤
        (K ^ ds + K + (Kc + 1) ^ 2 + 10) * ((encA a).length + 1) ^ e := by
      nlinarith
    have hmul := Nat.mul_le_mul_left c0 hinner
    have hge : c0 * ((K ^ ds + K + (Kc + 1) ^ 2 + 10) * ((encA a).length + 1) ^ e) ≤
        (c0 * (K ^ ds + K + (Kc + 1) ^ 2 + 10) + c0 + 1) * ((encA a).length + 1) ^ e := by
      rw [← mul_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    exact le_trans hmul hge

/-- `DecidableInTimeO` corollary of `decidableInTimeAndSpace_countedSearch`. -/
public theorem decidableInTimeO_countedSearch {α : Type} [Inhabited α]
    {encA : α ↪ List Bool} {count : α → ℕ} {check : α × ℕ → Bool}
    (hcount : ComputableInPolyTime count encA encNat)
    (hcheck : ComputableInPolyTime check (encPair encA encNat) encBool) :
    ∃ e : ℕ, DecidableInTimeO
      { a | ∃ r < count a, check (a, r) = true } encA
      (fun a => ((count a + 1 : ℕ) : ℝ) * (((encA a).length + 1 : ℕ) : ℝ) ^ e) := by
  obtain ⟨e, c, h⟩ := decidableInTimeAndSpace_countedSearch hcount hcheck
  refine ⟨e, c, _, _, fun a => ?_, h⟩
  push_cast
  have h0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  nlinarith

end Cslib.Complexity
