/-
Copyright (c) 2026 The FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalPapers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.LabelCover

import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Rich 2-to-1 Label Cover and the Rich 2-to-1 Conjecture

Formalizes Rich 2-to-1 Label Cover instances, their
satisfaction value, the $1 / n$ constant-labelling lower bound, `GapRichTwoToOne`, the open
conjecture `RichTwoToOneConjecture : Prop`, and its arbitrarily-large-$n$ amplification.

## Main definitions

* `Cslib.Complexity.IsTwoToOne`, `Cslib.Complexity.halfProj`: 2-to-1 maps `Fin (2 * n) → Fin n`.
* `Cslib.Complexity.RichTwoToOneInstance`, `Cslib.Complexity.encRichTwoToOneInstance`: executable
  Rich 2-to-1 Label Cover instances and their binary encoding.
* `Cslib.Complexity.GapRichTwoToOne`: gap promise problem separating `value = 1` from `value < ε`.
* `Cslib.Complexity.RichTwoToOneConjecture`: Braverman–Khot–Minzer Rich 2-to-1 Conjecture (`Prop`).

## Main results

* `Cslib.Complexity.RichTwoToOneInstance.value_ge_one_div`: every valid Rich 2-to-1 instance with
  $n \ge 1$ has `1 / n ≤ value`.
* `Cslib.Complexity.RichTwoToOneConjecture.exists_gt`: `RichTwoToOneConjecture` implies that for
  every $\varepsilon > 0$ and $N_0 \in \mathbb{N}$ there exists $n > N_0$ with `GapRichTwoToOne n ε`
  NP-hard.
-/

public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM Cslib.PCP.Encoded

/-- Predicate that every fiber of `π : Fin (2 * n) → Fin n` has cardinality `2`. -/
def IsTwoToOne {n : ℕ} (π : Fin (2 * n) → Fin n) : Prop :=
  ∀ j : Fin n, (univ.filter fun i : Fin (2 * n) => π i = j).card = 2

instance instDecidableIsTwoToOne {n : ℕ} (π : Fin (2 * n) → Fin n) : Decidable (IsTwoToOne π) :=
  inferInstanceAs (Decidable (∀ j : Fin n, (univ.filter fun i : Fin (2 * n) => π i = j).card = 2))

/-- Canonical 2-to-1 projection `i ↦ i / 2`. -/
def halfProj (n : ℕ) : Fin (2 * n) → Fin n :=
  fun i => ⟨i.val / 2, by omega⟩

theorem isTwoToOne_halfProj (n : ℕ) : IsTwoToOne (halfProj n) := by
  intro j
  let i₀ : Fin (2 * n) := ⟨2 * j.val, by omega⟩
  let i₁ : Fin (2 * n) := ⟨2 * j.val + 1, by omega⟩
  have hne : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have hset : (univ.filter fun i : Fin (2 * n) => halfProj n i = j) = {i₀, i₁} := by
    ext i
    simp only [mem_filter, mem_univ, true_and, halfProj, i₀, i₁, Fin.ext_iff, mem_insert,
      mem_singleton]
    omega
  rw [hset, card_pair hne]

/-- Executable Rich 2-to-1 Label Cover candidate instance. -/
@[ext]
structure RichTwoToOneInstance (n : ℕ) where
  /-- Number of left vertices $|U|$ in unary. -/
  leftVertices : ℕ
  /-- Number of right vertices $|V|$ in unary. -/
  rightVertices : ℕ
  /-- Framed list of bipartite edges carrying projection tables `Fin (2 * n) → Fin n`. -/
  edges : List (Edge (Fin (2 * n) → Fin n))
  deriving DecidableEq

/-- Framed pair encoding of `RichTwoToOneInstance n` with unary vertex counts and `encPi` tables. -/
noncomputable abbrev encRichTwoToOneInstance (n : ℕ) : RichTwoToOneInstance n ↪ List Bool :=
  let encMap := encPi (Index := Fin (2 * n)) (encFinEnum (Fin n))
  ⟨fun Φ => encPair encUnary (encPair encUnary (encList (Edge.encoding encMap)))
      (Φ.leftVertices, Φ.rightVertices, Φ.edges),
    fun Φ Ψ h => by
      have hp := (encPair encUnary (encPair encUnary (encList (Edge.encoding encMap)))).injective h
      exact RichTwoToOneInstance.ext (congrArg Prod.fst hp)
        (congrArg (fun p => p.2.1) hp) (congrArg (fun p => p.2.2) hp)⟩

namespace RichTwoToOneInstance

/-- Bi-regularity, 2-to-1 edge projections, and per-left-vertex richness. -/
def IsRichRegular {n : ℕ} (Φ : RichTwoToOneInstance n) : Prop :=
  Φ.edges ≠ [] ∧
  0 < Φ.leftVertices ∧
  0 < Φ.rightVertices ∧
  (∀ e ∈ Φ.edges, e.src < Φ.leftVertices ∧ e.dst < Φ.rightVertices ∧ IsTwoToOne e.constraint) ∧
  (∃ dL > 0, ∀ u < Φ.leftVertices, (Φ.edges.filter fun e => e.src == u).length = dL) ∧
  (∃ dR > 0, ∀ v < Φ.rightVertices, (Φ.edges.filter fun e => e.dst == v).length = dR) ∧
  (∀ u < Φ.leftVertices, ∃ mult > 0, ∀ π : Fin (2 * n) → Fin n, IsTwoToOne π →
    (Φ.edges.filter fun e => (e.src == u) && decide (e.constraint = π)).length = mult)

/-- Fraction of edges satisfied by `(cU, cV)`. -/
noncomputable def labellingValue {n : ℕ} (Φ : RichTwoToOneInstance n)
    (cU : Fin Φ.leftVertices → Fin (2 * n)) (cV : Fin Φ.rightVertices → Fin n) : ℝ :=
  if Φ.edges = [] then 1
  else
    ((Φ.edges.filter fun e =>
      if h : e.src < Φ.leftVertices ∧ e.dst < Φ.rightVertices then
        decide (e.constraint (cU ⟨e.src, h.1⟩) = cV ⟨e.dst, h.2⟩)
      else false).length : ℝ) / (Φ.edges.length : ℝ)

/-- Maximum satisfaction value over all labellings `(cU, cV)`. -/
noncomputable def value {n : ℕ} (Φ : RichTwoToOneInstance n) : ℝ :=
  if h0 : 0 < Φ.leftVertices ∧ 0 < Φ.rightVertices ∧ 0 < n then
    have : Nonempty (Fin Φ.leftVertices → Fin (2 * n)) := ⟨fun _ => ⟨0, by omega⟩⟩
    have : Nonempty (Fin Φ.rightVertices → Fin n) := ⟨fun _ => ⟨0, h0.2.2⟩⟩
    (univ : Finset ((Fin Φ.leftVertices → Fin (2 * n)) ×
      (Fin Φ.rightVertices → Fin n))).sup' univ_nonempty fun p => Φ.labellingValue p.1 p.2
  else 0

theorem labellingValue_le_value {n : ℕ} (Φ : RichTwoToOneInstance n)
    (hL : 0 < Φ.leftVertices) (hR : 0 < Φ.rightVertices) (hn : 0 < n)
    (cU : Fin Φ.leftVertices → Fin (2 * n)) (cV : Fin Φ.rightVertices → Fin n) :
    Φ.labellingValue cU cV ≤ Φ.value := by
  have h0 : 0 < Φ.leftVertices ∧ 0 < Φ.rightVertices ∧ 0 < n := ⟨hL, hR, hn⟩
  rw [value, dite_eq_left_of_eq_true (eq_true h0)]
  exact Finset.le_sup'
    (fun p : (Fin Φ.leftVertices → Fin (2 * n)) × (Fin Φ.rightVertices → Fin n) =>
      Φ.labellingValue p.1 p.2)
    (mem_univ (cU, cV))

/-- Every valid `RichTwoToOneInstance n` with $n \ge 1$ has satisfaction value at least $1 / n$. -/
theorem value_ge_one_div {n : ℕ} {Φ : RichTwoToOneInstance n}
    (hvalid : Φ.IsRichRegular) (hn : 0 < n) :
    (1 : ℝ) / (n : ℝ) ≤ Φ.value := by
  obtain ⟨hne, hL, hR, hbounds, _⟩ := hvalid
  let zeroN : Fin n := ⟨0, hn⟩
  let cV : Fin Φ.rightVertices → Fin n := fun _ => zeroN
  have hlen_pos : 0 < Φ.edges.length := List.length_pos_iff.mpr hne
  have hedge_sum : ∀ (l : List (Edge (Fin (2 * n) → Fin n))),
      (∀ e ∈ l, e.src < Φ.leftVertices ∧ e.dst < Φ.rightVertices ∧ IsTwoToOne e.constraint) →
      ∑ a : Fin (2 * n), (l.filter fun e =>
        if h : e.src < Φ.leftVertices ∧ e.dst < Φ.rightVertices then
          decide (e.constraint a = zeroN)
        else false).length = 2 * l.length := by
    intro l hl
    induction l with
    | nil => simp
    | cons e tl ih =>
      have he := hl e List.mem_cons_self
      have htl := fun e' he' => hl e' (List.mem_cons_of_mem e he')
      have hb : e.src < Φ.leftVertices ∧ e.dst < Φ.rightVertices := ⟨he.1, he.2.1⟩
      have hsum_head : ∑ a : Fin (2 * n),
          (if decide (e.constraint a = zeroN) = true then 1 else 0) = 2 := by
        have h21 := he.2.2 zeroN
        simp only [decide_eq_true_eq]
        rwa [← Finset.card_filter]
      have hsplit : ∀ a : Fin (2 * n),
          ((e :: tl).filter fun e' =>
            if h : e'.src < Φ.leftVertices ∧ e'.dst < Φ.rightVertices then
              decide (e'.constraint a = zeroN)
            else false).length =
          (if decide (e.constraint a = zeroN) = true then 1 else 0) +
          (tl.filter fun e' =>
            if h : e'.src < Φ.leftVertices ∧ e'.dst < Φ.rightVertices then
              decide (e'.constraint a = zeroN)
            else false).length := by
        intro a
        simp only [List.filter_cons, hb]
        cases decide (e.constraint a = zeroN) <;> simp [Nat.add_comm]
      simp only [hsplit, Finset.sum_add_distrib, hsum_head, ih htl, List.length_cons]
      ring
  have htotal := hedge_sum Φ.edges hbounds
  have hsum_val : ∑ a : Fin (2 * n), Φ.labellingValue (fun _ => a) cV = 2 := by
    have hterm : ∀ a : Fin (2 * n), Φ.labellingValue (fun _ => a) cV =
        ((Φ.edges.filter fun e =>
          if h : e.src < Φ.leftVertices ∧ e.dst < Φ.rightVertices then
            decide (e.constraint a = zeroN)
          else false).length : ℝ) / (Φ.edges.length : ℝ) :=
      fun a => by dsimp [labellingValue]; exact ite_eq_right hne
    simp only [hterm, ← Finset.sum_div]
    have hcast : (∑ x : Fin (2 * n),
        ((List.filter (fun e =>
          if _ : e.src < Φ.leftVertices ∧ e.dst < Φ.rightVertices then
            decide (e.constraint x = zeroN)
          else false) Φ.edges).length : ℝ)) = (2 * Φ.edges.length : ℝ) := by
      exact_mod_cast htotal
    rw [hcast]
    have hne_len : (Φ.edges.length : ℝ) ≠ 0 := by positivity
    field_simp
  have hle_sum : ∑ a : Fin (2 * n), Φ.labellingValue (fun _ => a) cV ≤
      ∑ _a : Fin (2 * n), Φ.value :=
    Finset.sum_le_sum fun a _ => Φ.labellingValue_le_value hL hR hn (fun _ => a) cV
  rw [hsum_val, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,
    Nat.cast_ofNat] at hle_sum
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [div_le_iff₀ hn_pos]
  linarith

end RichTwoToOneInstance

/-- Gap Rich 2-to-1 Label Cover promise problem (`value = 1` vs. `value < min(ε, 1)`). -/
noncomputable def GapRichTwoToOne (n : ℕ) (ε : ℝ) :
    PromiseProblem (RichTwoToOneInstance n) where
  yes := {Φ | Φ.IsRichRegular ∧ Φ.value = 1}
  no := {Φ | Φ.IsRichRegular ∧ Φ.value < ε ∧ Φ.value < 1}
  disjoint := Set.disjoint_left.2 fun _ hyes hno => hno.2.2.ne hyes.2

/-- The Rich 2-to-1 Conjecture
.
-/
def RichTwoToOneConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧
    PromiseProblem.NPHard (encRichTwoToOneInstance n) (GapRichTwoToOne n ε)

/-- Arbitrarily-large-$n$ amplification of `RichTwoToOneConjecture`. -/
theorem RichTwoToOneConjecture.exists_gt (hconj : RichTwoToOneConjecture)
    {ε : ℝ} (hε : 0 < ε) (N₀ : ℕ) :
    ∃ n : ℕ, N₀ < n ∧
      PromiseProblem.NPHard (encRichTwoToOneInstance n) (GapRichTwoToOne n ε) := by
  let ε' : ℝ := min ε (1 / ((N₀ : ℝ) + 1))
  have hε'_pos : 0 < ε' := lt_min hε (by positivity)
  obtain ⟨n, hn_pos, hhard⟩ := hconj ε' hε'_pos
  have hempty_NP : (∅ : Set (List Bool)) ∈ NP encBits :=
    ⟨0, fun _ => false, ComputableInPolyTime.const false, fun a => by simp⟩
  obtain ⟨f, _, _, hno⟩ := hhard encBits ∅ hempty_NP
  have hmem_no : f [] ∈ (GapRichTwoToOne n ε').no := hno (by simp [PromiseProblem.ofSet])
  obtain ⟨hvalid, hlt, _⟩ := hmem_no
  have h1n : (1 : ℝ) / (n : ℝ) ≤ (f []).value := (f []).value_ge_one_div hvalid hn_pos
  have hlt_inv : (1 : ℝ) / (n : ℝ) < 1 / ((N₀ : ℝ) + 1) :=
    (h1n.trans_lt hlt).trans_le (min_le_right _ _)
  have hn_gt : N₀ < n := by
    have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    have hN_r : (0 : ℝ) < (N₀ : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ hn_r hN_r, one_mul, one_mul] at hlt_inv
    have hn1 : N₀ + 1 < n := by exact_mod_cast (by linarith : (N₀ : ℝ) + 1 < (n : ℝ))
    omega
  exact ⟨n, hn_gt, hhard.mono subset_rfl
    (fun _ ⟨hv, hlt', hlt1⟩ => ⟨hv, hlt'.trans_le (min_le_left _ _), hlt1⟩)⟩

end Cslib.Complexity
