/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.GraphProblems
public import CslibFrontier.Computability.Complexity.Problems.Clique
public import CslibFrontier.Computability.Complexity.Problems.Coloring
import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Tactic.EncLen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-!
# Fine-Grained $n^{o(k)}$ Lower Bound for $k$-Clique under ETH

This module proves the classical fine-grained lower bound for parameterized `Clique`
 directly from
`Cslib.Complexity.ETH.not_decidableInSubexpTime_ThreeColoring` (without using any refutation
of `ETH`):

* **Block-coloring reduction (`threeColoringToClique q G`)**: for any fixed constant `q ≥ 1`,
  partition the distinct declared vertices of `G` into `q` blocks `B_0, …, B_{q-1}` of size
  `b = ⌈|V|/q⌉ ≤ |V|/q + 1`. Each vertex of the reduced graph represents a block `r < q` and a
  proper 3-coloring `c < 4 ^ |B_r|` of `G[B_r]` (2 bits per vertex), with edges between distinct
  blocks whose colorings are compatible across all crossing edges of `G`.
* **Correctness (`threeColoringToClique_mem_iff`)**:
  `threeColoringToClique q G ∈ Clique ↔ G ∈ ThreeColoring`.
* **Unconditional transfer (`decidableInSubexpTime_ThreeColoring_of_clique_noq`)**: any algorithm
  deciding `Clique` in time `f(q) · (N + 2)^{o(q)} · L^{O(1)}` (for every `ε > 0`, some
  `f : ℕ → ℕ` and `e : ℕ` achieve `O(f(q) · (N + 2)^{ε q} · (L + 1)^e)`) implies
  `DecidableInSubexpTime ThreeColoring encGraph (fun G => G.vertices.length + G.edges.length)`.
* **ETH corollary (`ETH.not_decidableInTimeO_Clique_noq`)**: under `ETH`, `Clique` has no
  `f(q) · (N + 2)^{o(q)} · L^{O(1)}` algorithm.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Block Partitioning and 2-Bit 3-Coloring Encoding -/

/-- Two-bit color at position `i` of a bitmask `c`: returns `0, 1, 2`, or `3`. -/
@[expose] def color2Bit (c i : ℕ) : ℕ :=
  (if c.testBit (2 * i) then 1 else 0) + (if c.testBit (2 * i + 1) then 2 else 0)

theorem color2Bit_lt_four (c i : ℕ) : color2Bit c i < 4 := by
  unfold color2Bit; split_ifs <;> omega

/-- Block size `⌈n / q⌉` for `q` blocks. -/
@[expose] def blockSize (n q : ℕ) : ℕ := (n + q - 1) / q

/-- The `r`-th block (`0 ≤ r < q`) of the distinct vertices `V` of `G`. -/
@[expose] def vertexBlock (V : List ℕ) (q r : ℕ) : List ℕ :=
  let b := blockSize V.length q
  (V.drop (r * b)).take b

/-- Check whether `c` encodes a proper 3-coloring of `G` restricted to vertex list `B`:
every vertex gets color `< 3`, and adjacent vertices in `B` get distinct colors. -/
@[expose] def isProperBlockColoring (G : Graph) (B : List ℕ) (c : ℕ) : Bool :=
  (List.range B.length).all fun i =>
    decide (color2Bit c i < 3) &&
      (List.range B.length).all fun j =>
        !(G.adjBool (B.getD i 0) (B.getD j 0) && decide (color2Bit c i = color2Bit c j))

/-- Check whether coloring `c₁` on `B₁` and coloring `c₂` on `B₂` are compatible across all
edges of `G` between `B₁` and `B₂`. -/
@[expose] def areBlockColoringsCompat (G : Graph) (B₁ B₂ : List ℕ) (c₁ c₂ : ℕ) : Bool :=
  (List.range B₁.length).all fun i =>
    (List.range B₂.length).all fun j =>
      !(G.adjBool (B₁.getD i 0) (B₂.getD j 0) && decide (color2Bit c₁ i = color2Bit c₂ j))

/-- Encode a pair `(r, c)` with `r < q` as a single vertex ID `r + q * c`. -/
@[expose] def blockVertId (q r c : ℕ) : ℕ := r + q * c

/-- Generate the valid coloring vertices for block `r` by iterating `4 ^ |B_r| = 2 ^ (2 * |B_r|)`
times via a flat counter. -/
@[expose] def validBlockColorings (G : Graph) (B : List ℕ) : List ℕ :=
  let step : ℕ × List ℕ → ℕ × List ℕ := fun st =>
    (st.1 + 1, if isProperBlockColoring G B st.1 then st.1 :: st.2 else st.2)
  (step^[2 ^ (2 * B.length)] (0, [])).2

/-- The `q`-partite compatibility graph `H_q(G)` for reducing `ThreeColoring` to `q`-`Clique`. -/
@[expose] def threeColoringToCliqueGraph (q : ℕ) (G : Graph) : Graph :=
  let V := G.distinctVertices
  let blockVerts : List (ℕ × List ℕ) :=
    (List.range q).map fun r =>
      let B := vertexBlock V q r
      (r, validBlockColorings G B)
  let verts : List ℕ :=
    blockVerts.flatMap fun p => p.2.map fun c => blockVertId q p.1 c
  let edges : List (ℕ × ℕ) :=
    blockVerts.flatMap fun p₁ =>
      blockVerts.flatMap fun p₂ =>
        if p₁.1 == p₂.1 then []
        else
          p₁.2.flatMap fun c₁ =>
            (p₂.2.filter fun c₂ =>
              areBlockColoringsCompat G (vertexBlock V q p₁.1) (vertexBlock V q p₂.1) c₁ c₂).map
              fun c₂ => (blockVertId q p₁.1 c₁, blockVertId q p₂.1 c₂)
  ⟨verts, edges⟩

/-- The `q`-`Clique` instance produced from `G`. -/
@[expose] def threeColoringToClique (q : ℕ) (G : Graph) : CliqueInstance :=
  ⟨threeColoringToCliqueGraph q G, q⟩

/-! ### Correctness of `threeColoringToClique` -/

theorem validBlockColorings_mem_iff (G : Graph) (B : List ℕ) (c : ℕ) :
    c ∈ validBlockColorings G B ↔
      c < 2 ^ (2 * B.length) ∧ isProperBlockColoring G B c = true := by
  unfold validBlockColorings
  suffices ∀ (k : ℕ),
      let step := fun st : ℕ × List ℕ =>
        (st.1 + 1, if isProperBlockColoring G B st.1 then st.1 :: st.2 else st.2)
      (step^[k] (0, [])).1 = k ∧
        ∀ x, x ∈ (step^[k] (0, [])).2 ↔ x < k ∧ isProperBlockColoring G B x = true from
    (this (2 ^ (2 * B.length))).2 c
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    dsimp only
    rw [Function.iterate_succ_apply']
    refine ⟨by simp [ih.1], fun x => ?_⟩
    rw [ih.1]
    split_ifs with hk
    · simp only [List.mem_cons, ih.2, Nat.lt_succ_iff]
      exact ⟨fun h => h.elim (fun h => by subst h; exact ⟨le_rfl, hk⟩) fun ⟨hx, hok⟩ => ⟨hx.le,
        hok⟩,
        fun ⟨hx, hok⟩ => (eq_or_lt_of_le hx).elim (fun h => Or.inl h) fun h => Or.inr ⟨h, hok⟩⟩
    · simp only [ih.2, Nat.lt_succ_iff]
      exact ⟨fun ⟨hx, hok⟩ => ⟨hx.le, hok⟩,
        fun ⟨hx, hok⟩ => (eq_or_lt_of_le hx).elim (fun h => absurd (h ▸ hok) hk) fun h => ⟨h, hok⟩⟩

/-- Every proper 3-coloring `f : ℕ → ℕ` on `B` can be encoded as a 2-bit mask
`c < 2 ^ (2 * B.length)` such that `color2Bit c i = f (B[i])` for all `i < B.length`. -/
private theorem exists_mask_of_coloring (B : List ℕ) (f : ℕ → ℕ)
    (hf : ∀ v ∈ B, f v < 3) :
    ∃ c < 2 ^ (2 * B.length), ∀ i (hi : i < B.length), color2Bit c i = f (B[i]'hi) := by
  suffices ∀ (k : ℕ) (hk : k ≤ B.length),
      ∃ c < 2 ^ (2 * k), ∀ i (hi : i < k), color2Bit c i = f (B[i]'(hi.trans_le hk)) by
    exact this B.length le_rfl
  intro k hk
  induction k with
  | zero =>
    exact ⟨0, by simp, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ k ih =>
    obtain ⟨c₀, hc₀_lt, hc₀_eq⟩ := ih (by omega)
    have hfk : f (B[k]'(by omega)) < 3 := hf _ (List.getElem_mem _)
    let d := f (B[k]'(by omega))
    let c := c₀ ||| (d <<< (2 * k))
    have hpow : 2 ^ (2 * (k + 1)) = 4 * 2 ^ (2 * k) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]; norm_num; ring
    have hd_lt : d <<< (2 * k) < 2 ^ (2 * (k + 1)) := by
      rw [Nat.shiftLeft_eq, hpow]; dsimp [d]; nlinarith
    have hc₀_lt' : c₀ < 2 ^ (2 * (k + 1)) :=
      hc₀_lt.trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hlt : c < 2 ^ (2 * (k + 1)) := Nat.or_lt_two_pow hc₀_lt' hd_lt
    refine ⟨c, hlt, fun i hi => ?_⟩
    by_cases hik : i = k
    · subst hik
      have hb0 : c₀.testBit (2 * i) = false :=
        Nat.testBit_lt_two_pow (hc₀_lt.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have hb1 : c₀.testBit (2 * i + 1) = false :=
        Nat.testBit_lt_two_pow (hc₀_lt.trans (Nat.pow_lt_pow_right (by norm_num) (by omega)))
      simp only [color2Bit, c, Nat.testBit_or, hb0, hb1, Bool.false_or, Nat.testBit_shiftLeft,
        ge_iff_le, le_refl, decide_true, Nat.sub_self, Bool.true_and,
        show 2 * i ≤ 2 * i + 1 by omega, show 2 * i + 1 - 2 * i = 1 by omega]
      have hd3 : d < 3 := hfk
      have hd_eq : d = f (B[i]'(hi.trans_le hk)) := rfl
      rw [← hd_eq]
      rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with hd | hd | hd <;> rw [hd] <;> decide
    · have hilt : i < k := by omega
      have hsh0 : (d <<< (2 * k)).testBit (2 * i) = false := by
        simp [Nat.testBit_shiftLeft, show ¬ (2 * k ≤ 2 * i) by omega]
      have hsh1 : (d <<< (2 * k)).testBit (2 * i + 1) = false := by
        simp [Nat.testBit_shiftLeft, show ¬ (2 * k ≤ 2 * i + 1) by omega]
      have heq : color2Bit c i = color2Bit c₀ i := by
        simp [color2Bit, c, Nat.testBit_or, hsh0, hsh1]
      rw [heq, hc₀_eq i hilt]

private theorem blockVertId_inj {q r₁ r₂ c₁ c₂ : ℕ} (hr1 : r₁ < q) (hr2 : r₂ < q)
    (heq : blockVertId q r₁ c₁ = blockVertId q r₂ c₂) : r₁ = r₂ ∧ c₁ = c₂ := by
  unfold blockVertId at heq
  have hmod1 : (r₁ + q * c₁) % q = r₁ := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr1]
  have hmod2 : (r₂ + q * c₂) % q = r₂ := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr2]
  have hr : r₁ = r₂ := by rw [← hmod1, heq, hmod2]
  subst hr
  have hqpos : 0 < q := by omega
  have hc : c₁ = c₂ := Nat.eq_of_mul_eq_mul_left hqpos (by omega)
  exact ⟨rfl, hc⟩

private theorem mem_vertexBlock_partition {V : List ℕ} {q : ℕ} (hq : 1 ≤ q) :
    (∀ r < q, ∀ v ∈ vertexBlock V q r, v ∈ V) ∧
    (∀ v ∈ V, ∃ r < q, ∃ i : ℕ, ∃ hi : i < (vertexBlock V q r).length,
      (vertexBlock V q r)[i]'hi = v) := by
  refine ⟨fun r _ v hv => ?_, fun v hv => ?_⟩
  · exact (List.drop_sublist _ _).subset ((List.take_sublist _ _).subset hv)
  · obtain ⟨pos, hpos, rfl⟩ := List.getElem_of_mem hv
    let b := blockSize V.length q
    have hbpos : 1 ≤ b := by
      unfold b blockSize
      have h1 : q ≤ V.length + q - 1 := by omega
      exact (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using h1)
    have hqb : V.length ≤ q * b := by
      have hmod := Nat.div_add_mod (V.length + q - 1) q
      have hlt := Nat.mod_lt (V.length + q - 1) (show 0 < q by omega)
      change q * b + (V.length + q - 1) % q = V.length + q - 1 at hmod
      omega
    let r := pos / b
    let i := pos % b
    have hr_lt : r < q := by
      have : r * b ≤ pos := Nat.div_mul_le_self pos b
      nlinarith
    have hi_lt : i < b := Nat.mod_lt pos (by omega)
    have hpos_eq : r * b + i = pos := by
      have := Nat.div_add_mod pos b
      dsimp [r, i]; linarith
    have hlen_drop : (V.drop (r * b)).length = V.length - r * b := List.length_drop
    have hlen_blk : (vertexBlock V q r).length = min b (V.length - r * b) := by
      simp [vertexBlock, b, List.length_take, hlen_drop]
    have hi_blk : i < (vertexBlock V q r).length := by rw [hlen_blk]; omega
    refine ⟨r, hr_lt, i, hi_blk, ?_⟩
    simp only [vertexBlock, b, List.getElem_take, List.getElem_drop, hpos_eq]

private theorem isProperBlockColoring_iff (G : Graph) (B : List ℕ) (c : ℕ) :
    isProperBlockColoring G B c = true ↔
      (∀ i < B.length, color2Bit c i < 3) ∧
      ∀ i (hi : i < B.length) j (hj : j < B.length),
        G.toSimpleGraph.Adj (B[i]'hi) (B[j]'hj) → color2Bit c i ≠ color2Bit c j := by
  simp only [isProperBlockColoring, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff, Graph.adjBool_eq_false_iff,
    decide_eq_false_iff_not]
  refine ⟨fun h => ⟨fun i hi => (h i hi).1, fun i hi j hj hadj => ?_⟩, fun ⟨h1, h2⟩ i hi => ?_⟩
  · have h1 := (h i hi).2 j hj
    simp only [List.getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
      Option.getD_some] at h1
    exact h1.resolve_left (not_not.mpr hadj)
  · refine ⟨h1 i hi, fun j hj => ?_⟩
    simp only [List.getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
      Option.getD_some]
    exact (em (G.toSimpleGraph.Adj (B[i]'hi) (B[j]'hj))).elim (Or.inr ∘ h2 i hi j hj) Or.inl

private theorem areBlockColoringsCompat_iff (G : Graph) (B₁ B₂ : List ℕ) (c₁ c₂ : ℕ) :
    areBlockColoringsCompat G B₁ B₂ c₁ c₂ = true ↔
      ∀ i (hi : i < B₁.length) j (hj : j < B₂.length),
        G.toSimpleGraph.Adj (B₁[i]'hi) (B₂[j]'hj) → color2Bit c₁ i ≠ color2Bit c₂ j := by
  simp only [areBlockColoringsCompat, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    Bool.and_eq_false_iff, Graph.adjBool_eq_false_iff, decide_eq_false_iff_not]
  refine ⟨fun h i hi j hj hadj => ?_, fun h i hi j hj => ?_⟩
  · have h1 := h i hi j hj
    simp only [List.getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
      Option.getD_some] at h1
    exact h1.resolve_left (not_not.mpr hadj)
  · simp only [List.getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Option.getD_some]
    exact (em (G.toSimpleGraph.Adj (B₁[i]'hi) (B₂[j]'hj))).elim (Or.inr ∘ h i hi j hj) Or.inl

/-- **Correctness of the block-coloring reduction**: for any `q ≥ 1`,
`threeColoringToClique q G ∈ Clique ↔ G ∈ ThreeColoring`. -/
theorem threeColoringToClique_mem_iff {q : ℕ} (hq : 1 ≤ q) (G : Graph) :
    threeColoringToClique q G ∈ Clique ↔ G ∈ ThreeColoring := by
  classical
  let V := G.distinctVertices
  let H := threeColoringToCliqueGraph q G
  have hmemV : ∀ x, x ∈ H.vertices ↔
      ∃ r < q, ∃ c, c ∈ validBlockColorings G (vertexBlock V q r) ∧ x = blockVertId q r c := by
    intro x
    simp only [H, threeColoringToCliqueGraph, List.mem_flatMap, List.mem_map, List.mem_range, V]
    exact ⟨fun ⟨_, ⟨r, hr, rfl⟩, c, hc, hx⟩ => ⟨r, hr, c, hc, hx.symm⟩,
      fun ⟨r, hr, c, hc, hx⟩ =>
        ⟨(r, validBlockColorings G (vertexBlock V q r)), ⟨r, hr, rfl⟩, c, hc, hx.symm⟩⟩
  have hmemE : ∀ u v, (u, v) ∈ H.edges ↔
      ∃ r₁ < q, ∃ c₁ ∈ validBlockColorings G (vertexBlock V q r₁),
      ∃ r₂ < q, ∃ c₂ ∈ validBlockColorings G (vertexBlock V q r₂),
        r₁ ≠ r₂ ∧
        areBlockColoringsCompat G (vertexBlock V q r₁) (vertexBlock V q r₂) c₁ c₂ = true ∧
        u = blockVertId q r₁ c₁ ∧ v = blockVertId q r₂ c₂ := by
    intro u v
    simp only [H, threeColoringToCliqueGraph, List.mem_flatMap, List.mem_map, List.mem_range, V]
    constructor
    · rintro ⟨_, ⟨r₁, hr₁, rfl⟩, _, ⟨r₂, hr₂, rfl⟩, h⟩
      by_cases hrr : r₁ = r₂
      · simp [hrr] at h
      · simp only [beq_iff_eq, hrr, ite_false, List.mem_flatMap, List.mem_map, List.mem_filter,
          Prod.mk.injEq] at h
        obtain ⟨c₁, hc₁, c₂, ⟨hc₂, hcomp⟩, rfl, rfl⟩ := h
        exact ⟨r₁, hr₁, c₁, hc₁, r₂, hr₂, c₂, hc₂, hrr, hcomp, rfl, rfl⟩
    · rintro ⟨r₁, hr₁, c₁, hc₁, r₂, hr₂, c₂, hc₂, hne, hcomp, rfl, rfl⟩
      refine ⟨(r₁, validBlockColorings G (vertexBlock V q r₁)), ⟨r₁, hr₁, rfl⟩,
        (r₂, validBlockColorings G (vertexBlock V q r₂)), ⟨r₂, hr₂, rfl⟩, ?_⟩
      simp only [beq_iff_eq, hne, ite_false, List.mem_flatMap, List.mem_map, List.mem_filter,
        Prod.mk.injEq]
      exact ⟨c₁, hc₁, c₂, ⟨hc₂, hcomp⟩, rfl, rfl⟩
  rw [mem_Clique_iff, mem_KColoring_iff]
  constructor
  · -- From a `q`-clique `S` in `H`, extract `(r, c_r)` per block and assemble a 3-coloring.
    rintro ⟨S, hS_sub, hS_clq⟩
    have hS_card : S.card = q := hS_clq.2
    have hS_adj : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → H.toSimpleGraph.Adj u v := fun u hu v hv hne =>
      hS_clq.1 hu hv hne
    -- Every `x ∈ S` has a unique block `r < q` and coloring `c`, and no two `x ≠ y` in `S` share a
    -- block!
    have hex_rc : ∀ x ∈ S, ∃ r < q, ∃ c, c ∈ validBlockColorings G (vertexBlock V q r) ∧
        x = blockVertId q r c := fun x hx => (hmemV x).mp (hS_sub x hx)
    have hblock_inj : ∀ r < q, ∀ c₁ c₂, blockVertId q r c₁ ∈ S → blockVertId q r c₂ ∈ S →
        c₁ = c₂ := by
      intro r hr c₁ c₂ h1 h2
      by_contra hne
      have hvne : blockVertId q r c₁ ≠ blockVertId q r c₂ :=
        fun h => hne (blockVertId_inj hr hr h).2
      have hadj := hS_adj _ h1 _ h2 hvne
      rw [Graph.toSimpleGraph_adj] at hadj
      rcases hadj.2 with he | he <;>
        (rw [hmemE] at he;
          obtain ⟨r₁, hr₁, _, _, r₂, hr₂, _, _, hrne, _, he1, he2⟩ := he;
          have := (blockVertId_inj hr hr₁ he1).1;
          have := (blockVertId_inj hr hr₂ he2).1;
          exact hrne (by omega))
    have hfin_ex : ∀ r : Fin q, ∃ c, c ∈ validBlockColorings G (vertexBlock V q r.1) ∧
        blockVertId q r.1 c ∈ S := by
      let blkOf (x : S) : Fin q := ⟨x.1 % q, Nat.mod_lt _ (by omega)⟩
      have hblk_val : ∀ (x : S) r c, r < q → x.1 = blockVertId q r c → (blkOf x).1 = r :=
        fun _ r c hr hx => by
          simp only [blkOf, hx, blockVertId, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
      have hblk_inj : Function.Injective blkOf := by
        intro ⟨x, hx⟩ ⟨y, hy⟩ hxy; apply Subtype.ext
        obtain ⟨rx, hrx, cx, _, rfl⟩ := hex_rc x hx
        obtain ⟨ry, hry, cy, _, rfl⟩ := hex_rc y hy
        have h1 := hblk_val ⟨_, hx⟩ rx cx hrx rfl
        have h2 := hblk_val ⟨_, hy⟩ ry cy hry rfl
        have hr_eq : rx = ry := by have := congrArg Fin.val hxy; omega
        subst hr_eq; exact congrArg (blockVertId q rx) (hblock_inj rx hrx cx cy hx hy)
      have hsurj : Function.Surjective blkOf :=
        ((Fintype.bijective_iff_injective_and_card blkOf).mpr ⟨hblk_inj, by simp [hS_card]⟩).2
      intro r
      obtain ⟨⟨x, hx⟩, hxr⟩ := hsurj r
      obtain ⟨rx, hrx, cx, hcx, rfl⟩ := hex_rc x hx
      have hrx_eq : rx = r.1 := by
        have := congrArg Fin.val hxr; have := hblk_val ⟨_, hx⟩ rx cx hrx rfl; omega
      subst hrx_eq; exact ⟨cx, hcx, hx⟩
    choose colOf hcol_valid hcol_mem using hfin_ex
    let f : ℕ → ℕ := fun v =>
      if hv : v ∈ V then
        let ex := (mem_vertexBlock_partition hq).2 v hv
        color2Bit (colOf ⟨ex.choose, ex.choose_spec.1⟩) ex.choose_spec.2.choose
      else 0
    refine ⟨f, fun v hv => ?_, fun u hu v hv huv => ?_⟩
    · have hvV : v ∈ V := G.mem_distinctVertices.mpr hv
      simp only [f, hvV, dite_true]
      set ex := (mem_vertexBlock_partition hq).2 v hvV
      have hprop := ((validBlockColorings_mem_iff G _ _).mp (hcol_valid ⟨ex.choose,
        ex.choose_spec.1⟩)).2
      exact ((isProperBlockColoring_iff G _ _).mp hprop).1 _ ex.choose_spec.2.choose_spec.choose
    · have huV : u ∈ V := G.mem_distinctVertices.mpr hu
      have hvV : v ∈ V := G.mem_distinctVertices.mpr hv
      simp only [f, huV, hvV, dite_true]
      set exu := (mem_vertexBlock_partition hq).2 u huV
      set ru := exu.choose; have hru := exu.choose_spec.1
      set iu := exu.choose_spec.2.choose; have hiu := exu.choose_spec.2.choose_spec.choose
      have hgu := exu.choose_spec.2.choose_spec.choose_spec
      set exv := (mem_vertexBlock_partition hq).2 v hvV
      set rv := exv.choose; have hrv := exv.choose_spec.1
      set iv := exv.choose_spec.2.choose; have hiv := exv.choose_spec.2.choose_spec.choose
      have hgv := exv.choose_spec.2.choose_spec.choose_spec
      by_cases hrr : ru = rv
      · rw [show (⟨ru, hru⟩ : Fin q) = ⟨rv, hrv⟩ from Fin.ext hrr]
        have hprop := ((validBlockColorings_mem_iff G _ _).mp (hcol_valid ⟨rv, hrv⟩)).2
        have hiu' : iu < (vertexBlock V q rv).length := hrr ▸ hiu
        have hgu' : (vertexBlock V q rv)[iu]'hiu' = u := by
          have : ∀ {a b : ℕ} (h : a = b) (hi : iu < (vertexBlock V q a).length),
              (vertexBlock V q b)[iu]'(h ▸ hi) = (vertexBlock V q a)[iu]'hi := by
                rintro _ _ rfl _; rfl
          rw [this hrr hiu, hgu]
        exact ((isProperBlockColoring_iff G _ _).mp hprop).2 iu hiu' iv hiv
          (by rw [hgu', hgv]; exact huv)
      · have hvne : blockVertId q ru (colOf ⟨ru, hru⟩) ≠ blockVertId q rv (colOf ⟨rv, hrv⟩) :=
          fun h => hrr (blockVertId_inj hru hrv h).1
        have hadj := hS_adj _ (hcol_mem ⟨ru, hru⟩) _ (hcol_mem ⟨rv, hrv⟩) hvne
        rw [Graph.toSimpleGraph_adj] at hadj
        rcases hadj.2 with he | he
        · rw [hmemE] at he
          obtain ⟨r₁, hr₁, c₁, _, r₂, hr₂, c₂, _, _, hcomp, he1, he2⟩ := he
          obtain ⟨rfl, rfl⟩ := blockVertId_inj hru hr₁ he1
          obtain ⟨rfl, rfl⟩ := blockVertId_inj hrv hr₂ he2
          exact (areBlockColoringsCompat_iff G _ _ _ _).mp hcomp iu hiu iv hiv
            (by rw [hgu, hgv]; exact huv)
        · rw [hmemE] at he
          obtain ⟨r₁, hr₁, c₁, _, r₂, hr₂, c₂, _, _, hcomp, he1, he2⟩ := he
          obtain ⟨rfl, rfl⟩ := blockVertId_inj hrv hr₁ he1
          obtain ⟨rfl, rfl⟩ := blockVertId_inj hru hr₂ he2
          exact ((areBlockColoringsCompat_iff G _ _ _ _).mp hcomp iv hiv iu hiu
            (by rw [hgu, hgv]; exact huv.symm)).symm
  · -- From a proper 3-coloring `f` of `G`, build the `q`-clique `{blockVertId q r c_r | r < q}`.
    rintro ⟨f, hf_lt, hf_adj⟩
    have hblk_mask : ∀ r : Fin q, ∃ c < 2 ^ (2 * (vertexBlock V q r.1).length),
        ∀ i (hi : i < (vertexBlock V q r.1).length),
          color2Bit c i = f ((vertexBlock V q r.1)[i]'hi) := fun r =>
      exists_mask_of_coloring (vertexBlock V q r.1) f fun v hv =>
        hf_lt v (G.mem_distinctVertices.mp ((mem_vertexBlock_partition hq).1 r.1 r.2 v hv))
    choose cOf hc_lt hc_eq using hblk_mask
    have hmemG : ∀ (r : Fin q) {i : ℕ} (hi : i < (vertexBlock V q r.1).length),
        (vertexBlock V q r.1)[i]'hi ∈ G.vertices := fun r {_} hi =>
      G.mem_distinctVertices.mp ((mem_vertexBlock_partition hq).1 r.1 r.2 _ (List.getElem_mem hi))
    have hc_valid : ∀ r : Fin q, cOf r ∈ validBlockColorings G (vertexBlock V q r.1) := by
      intro r
      rw [validBlockColorings_mem_iff]
      refine ⟨hc_lt r, (isProperBlockColoring_iff G _ _).mpr ⟨fun i hi => ?_,
        fun i hi j hj hadj => ?_⟩⟩
      · rw [hc_eq r i hi]; exact hf_lt _ (hmemG r hi)
      · rw [hc_eq r i hi, hc_eq r j hj]; exact hf_adj _ (hmemG r hi) _ (hmemG r hj) hadj
    let emb : Fin q ↪ ℕ :=
      ⟨fun r => blockVertId q r.1 (cOf r), fun a b hab => Fin.ext (blockVertId_inj a.2 b.2 hab).1⟩
    let S : Finset ℕ := Finset.univ.map emb
    refine ⟨S, fun x hx => ?_,
      ⟨?_, by simp [S, threeColoringToClique, Finset.card_map, Finset.card_univ, Fintype.card_fin]⟩⟩
    · simp only [S, Finset.mem_map, Finset.mem_univ, true_and, emb] at hx
      obtain ⟨r, rfl⟩ := hx
      exact (hmemV _).mpr ⟨r.1, r.2, cOf r, hc_valid r, rfl⟩
    · intro u hu v hv hne
      simp only [S, Finset.mem_coe, Finset.mem_map, Finset.mem_univ, true_and, emb] at hu hv
      obtain ⟨r₁, rfl⟩ := hu
      obtain ⟨r₂, rfl⟩ := hv
      have hrne : r₁.1 ≠ r₂.1 := fun h => hne (by rw [Fin.ext h])
      rw [Graph.toSimpleGraph_adj]
      refine ⟨hne, Or.inl ((hmemE _ _).mpr ⟨r₁.1, r₁.2, cOf r₁, hc_valid r₁, r₂.1, r₂.2, cOf r₂,
        hc_valid r₂, hrne, (areBlockColoringsCompat_iff G _ _ _ _).mpr fun i hi j hj hadj => ?_,
        rfl, rfl⟩)⟩
      rw [hc_eq r₁ i hi, hc_eq r₂ j hj]
      exact hf_adj _ (hmemG r₁ hi) _ (hmemG r₂ hj) hadj

/-! ### Exponential Time Bound of `threeColoringToClique` and Unconditional Transfer -/

theorem validBlockColorings_length_le (G : Graph) (B : List ℕ) :
    (validBlockColorings G B).length ≤ 2 ^ (2 * B.length) := by
  unfold validBlockColorings
  suffices ∀ (k : ℕ),
      ((fun st : ℕ × List ℕ =>
        (st.1 + 1, if isProperBlockColoring G B st.1 then st.1 :: st.2 else st.2))^[k]
          (0, [])).2.length ≤ k from
    this (2 ^ (2 * B.length))
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply']; split_ifs <;> simp <;> omega

theorem length_encNat_le_of_lt_two_pow {n k : ℕ} (h : n < 2 ^ k) :
    (encNat n).length ≤ k := by
  simp only [encNat_apply, Nat.size_eq_bits_len]; exact Nat.size_le.mpr h

theorem length_encList_mono_sublist {α : Type*} {enc : α ↪ List Bool}
    {l₁ l₂ : List α} (h : l₁.Sublist l₂) :
    (encList enc l₁).length ≤ (encList enc l₂).length := by
  induction h with
  | slnil => exact le_rfl
  | cons _ _ ih => simp only [length_encList, List.map_cons, List.sum_cons] at ih ⊢; omega
  | cons_cons _ _ ih => simp only [length_encList, List.map_cons, List.sum_cons] at ih ⊢; omega

theorem length_encList_le_of_nodup_subset {α : Type*}
    {enc : α ↪ List Bool} {l₁ l₂ : List α} (hnd : l₁.Nodup) (hsub : ∀ x ∈ l₁, x ∈ l₂) :
    (encList enc l₁).length ≤ (encList enc l₂).length := by
  classical
  induction l₁ generalizing l₂ with
  | nil => simp [length_encList]
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    have ha : a ∈ l₂ := hsub a (by simp)
    have hperm : (encList enc (a :: l₂.erase a)).length = (encList enc l₂).length := by
      simp only [length_encList]
      exact (((List.perm_cons_erase ha).map (fun x => 2 * (enc x).length + 1)).sum_eq).symm
    have ht := ih hnd.2 fun x hx =>
      (List.mem_erase_of_ne (fun h => hnd.1 (by subst h; exact hx))).mpr (hsub x (by simp [hx]))
    rw [← hperm]; simp only [length_encList, List.map_cons, List.sum_cons] at ht ⊢; omega

theorem blockSize_le_encGraph_succ {q : ℕ} (hq : 1 ≤ q) (G : Graph) :
    blockSize G.distinctVertices.length q ≤ (encGraph G).length + 1 := by
  have hV : G.distinctVertices.length ≤ G.vertices.length :=
    G.length_distinctVertices.le.trans (List.toFinset_card_le G.vertices)
  have hGL : G.vertices.length ≤ (encGraph G).length := G.length_vertices_le_encGraph
  have hdiv := Nat.div_le_div_right (c := q)
    (show G.distinctVertices.length + q - 1 ≤ G.vertices.length + q by omega)
  rw [Nat.add_div_right _ (by omega)] at hdiv
  have := Nat.div_le_self G.vertices.length q; unfold blockSize; omega

/-- Size bound on `threeColoringToCliqueGraph q G`: vertex count `≤ q * 2 ^ (2 * b)` where
`b = blockSize |V| q`. -/
theorem length_threeColoringToCliqueGraph_vertices_le (q : ℕ) (G : Graph) :
    (threeColoringToCliqueGraph q G).vertices.length ≤
      q * 2 ^ (2 * blockSize G.distinctVertices.length q) := by
  simp only [threeColoringToCliqueGraph, List.length_flatMap, List.map_map, Function.comp_def,
    List.length_map]
  calc ((List.range q).map fun r =>
        (validBlockColorings G (vertexBlock G.distinctVertices q r)).length).sum
      ≤ ((List.range q).map fun _ => 2 ^ (2 * blockSize G.distinctVertices.length q)).sum := by
        refine List.sum_le_sum fun r _ =>
          (validBlockColorings_length_le G _).trans
            (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left 2 (List.length_take_le _ _)))
    _ = q * 2 ^ (2 * blockSize G.distinctVertices.length q) := by
        simp [List.sum_replicate, smul_eq_mul]

/-- Encoding length bound of `threeColoringToClique q G` in terms of `|G|` and `2 ^ (2 * b)`. -/
theorem length_encCliqueInstance_threeColoringToClique_le (q : ℕ) (G : Graph) :
    (encCliqueInstance (threeColoringToClique q G)).length ≤
      48 * (q + 1) ^ 2 * (2 ^ (2 * blockSize G.distinctVertices.length q)) ^ 2 *
        (blockSize G.distinctVertices.length q + q + 2) + 48 * (q + 1) := by
  -- Every vertex ID `r + q * c` with `r < q` and `c < 2 ^ (2 * b)` satisfies
  -- `r + q * c < q * 2 ^ (2 * b)` so `(encNat id).length ≤ q + 2 * b + 1`.
  have hv_len : ∀ x ∈ (threeColoringToCliqueGraph q G).vertices,
      (encNat x).length ≤ q + 2 * blockSize G.distinctVertices.length q + 1 := by
    intro x hx
    simp only [threeColoringToCliqueGraph, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨_, ⟨r, hr, rfl⟩, c, hc, rfl⟩ := hx
    have hclt := ((validBlockColorings_mem_iff G _ c).mp hc).1
    have hblt : (vertexBlock G.distinctVertices q r).length ≤
        blockSize G.distinctVertices.length q := List.length_take_le _ _
    have hid : blockVertId q r c < 2 ^ (q + 2 * blockSize G.distinctVertices.length q + 1) := by
      unfold blockVertId
      have h1 : c < 2 ^ (2 * blockSize G.distinctVertices.length q) :=
        hclt.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hq2 : q < 2 ^ q := Nat.lt_two_pow_self
      have h2 : r + q * c < q * 2 ^ (2 * blockSize G.distinctVertices.length q) := by nlinarith
      calc r + q * c < q * 2 ^ (2 * blockSize G.distinctVertices.length q) := h2
        _ ≤ 2 ^ q * 2 ^ (2 * blockSize G.distinctVertices.length q) :=
            Nat.mul_le_mul_right _ hq2.le
        _ = 2 ^ (q + 2 * blockSize G.distinctVertices.length q) := (pow_add 2 _ _).symm
        _ ≤ 2 ^ (q + 2 * blockSize G.distinctVertices.length q + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
    exact length_encNat_le_of_lt_two_pow hid
  have he_count : (threeColoringToCliqueGraph q G).edges.length ≤
      (q * 2 ^ (2 * blockSize G.distinctVertices.length q)) ^ 2 := by
    have hbound : ∀ r < q, (validBlockColorings G (vertexBlock G.distinctVertices q r)).length ≤
        2 ^ (2 * blockSize G.distinctVertices.length q) := fun r _ =>
      (validBlockColorings_length_le G _).trans
        (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left 2 (List.length_take_le _ _)))
    set M := 2 ^ (2 * blockSize G.distinctVertices.length q)
    simp only [threeColoringToCliqueGraph, List.length_flatMap, List.map_map, Function.comp_def,
      List.length_map, apply_ite List.length, List.length_nil]
    calc ((List.range q).map fun r₁ =>
            ((List.range q).map fun r₂ =>
              if r₁ == r₂ then 0
              else ((validBlockColorings G (vertexBlock G.distinctVertices q r₁)).map fun c₁ =>
                ((validBlockColorings G (vertexBlock G.distinctVertices q r₂)).filter fun c₂ =>
                  areBlockColoringsCompat G (vertexBlock G.distinctVertices q r₁)
                    (vertexBlock G.distinctVertices q r₂) c₁ c₂).length).sum).sum).sum
        ≤ ((List.range q).map fun _ => ((List.range q).map fun _ => M * M).sum).sum := by
          refine List.sum_le_sum fun r₁ hr₁ => List.sum_le_sum fun r₂ hr₂ => ?_
          split_ifs
          · exact Nat.zero_le _
          · calc ((validBlockColorings G (vertexBlock G.distinctVertices q r₁)).map fun c₁ =>
                ((validBlockColorings G
                    (vertexBlock G.distinctVertices q r₂)).filter _).length).sum
                ≤ ((validBlockColorings G
                    (vertexBlock G.distinctVertices q r₁)).map fun _ => M).sum := by
                  refine List.sum_le_sum fun c₁ _ =>
                    (List.length_filter_le _ _).trans (hbound r₂ (List.mem_range.mp hr₂))
              _ = (validBlockColorings G (vertexBlock G.distinctVertices q r₁)).length * M := by
                  simp [List.sum_replicate, smul_eq_mul]
              _ ≤ M * M := Nat.mul_le_mul_right M (hbound r₁ (List.mem_range.mp hr₁))
      _ = (q * M) ^ 2 := by simp [List.sum_replicate, smul_eq_mul]; ring
  have he_elem : ∀ e ∈ (threeColoringToCliqueGraph q G).edges,
      (encPair encNat encNat e).length ≤
        3 * (q + 2 * blockSize G.distinctVertices.length q + 1) + 2 := by
    intro e he
    -- Both endpoints of every edge in `H` are in `H.vertices`!
    have h1 : e.1 ∈ (threeColoringToCliqueGraph q G).vertices ∧
        e.2 ∈ (threeColoringToCliqueGraph q G).vertices := by
      simp only [threeColoringToCliqueGraph, List.mem_flatMap, List.mem_map, List.mem_range] at he ⊢
      obtain ⟨_, ⟨r₁, hr₁, rfl⟩, _, ⟨r₂, hr₂, rfl⟩, h⟩ := he
      split_ifs at h with hrr
      · simp at h
      · simp only [List.mem_flatMap, List.mem_map, List.mem_filter] at h
        obtain ⟨c₁, hc₁, c₂, ⟨hc₂, -⟩, rfl⟩ := h
        exact ⟨⟨_, ⟨r₁, hr₁, rfl⟩, c₁, hc₁, rfl⟩, ⟨_, ⟨r₂, hr₂, rfl⟩, c₂, hc₂, rfl⟩⟩
    have ha := hv_len e.1 h1.1
    have hb := hv_len e.2 h1.2
    simp only [length_encPair]; omega
  set B := blockSize G.distinctVertices.length q
  set M := 2 ^ (2 * B)
  have hV_enc := (length_encList_le encNat
    (threeColoringToCliqueGraph q G).vertices hv_len).trans
    (Nat.mul_le_mul_right _ (length_threeColoringToCliqueGraph_vertices_le q G))
  have hE_enc := (length_encList_le (encPair encNat encNat)
    (threeColoringToCliqueGraph q G).edges he_elem).trans
    (Nat.mul_le_mul_right _ he_count)
  have hq_enc : (encNat q).length ≤ q := length_encNat_le_of_lt_two_pow Nat.lt_two_pow_self
  have htot : (encCliqueInstance (threeColoringToClique q G)).length =
      2 * (2 * (encList encNat (threeColoringToCliqueGraph q G).vertices).length + 1 +
        (encList (encPair encNat encNat) (threeColoringToCliqueGraph q G).edges).length) + 1 +
        (encNat q).length := by
    change (encPair encGraph encNat (threeColoringToCliqueGraph q G, q)).length = _
    simp only [encGraph_apply, length_encPair]
  rw [htot]
  have hM1 : 1 ≤ M := Nat.one_le_two_pow
  have hV_enc' : (encList encNat (threeColoringToCliqueGraph q G).vertices).length ≤
      q * M * (2 * (q + 2 * B + 1) + 1) := hV_enc
  have hV_le : (encList encNat (threeColoringToCliqueGraph q G).vertices).length ≤
      (q + 1) ^ 2 * M ^ 2 * (B + q + 2) * 5 := by
    have hqM : q * M ≤ (q + 1) ^ 2 * M ^ 2 :=
      Nat.mul_le_mul (by nlinarith) (by nlinarith)
    have h5 : 2 * (q + 2 * B + 1) + 1 ≤ 5 * (B + q + 2) := by omega
    exact hV_enc'.trans ((Nat.mul_le_mul hqM h5).trans_eq (by ring))
  have hE_le : (encList (encPair encNat encNat) (threeColoringToCliqueGraph q G).edges).length ≤
      (q + 1) ^ 2 * M ^ 2 * (B + q + 2) * 13 := by
    have hqM2 : (q * M) ^ 2 ≤ (q + 1) ^ 2 * M ^ 2 := by
      rw [mul_pow]; exact Nat.mul_le_mul_right _ (by nlinarith)
    have h13 : 2 * (3 * (q + 2 * B + 1) + 2) + 1 ≤ 13 * (B + q + 2) := by omega
    exact hE_enc.trans ((Nat.mul_le_mul hqM2 h13).trans_eq (by ring))
  nlinarith

private theorem computableInPolyTime_color2Bit :
    ComputableInPolyTime (fun p : ℕ × ℕ => color2Bit p.1 p.2)
      (encPair encNat encUnary) encUnary := by
  unfold color2Bit
  have h2i := unary_mul.comp ((const 2).prod (snd encNat encUnary))
  have h2i1 := unary_add.comp (h2i.prod (const 1))
  have hb0 := binary_testBit (fst encNat encUnary) h2i
  have hb1 := binary_testBit (fst encNat encUnary) h2i1
  exact unary_add.comp ((hb0.ite' (const 1) (const 0)).prod (hb1.ite' (const 2) (const 0)))

theorem computableInPolyTime_isProperBlockColoring :
    ComputableInPolyTime
      (fun p : (Graph × List ℕ) × ℕ => isProperBlockColoring p.1.1 p.1.2 p.2)
      (encPair (encPair encGraph (encList encNat)) encNat) encBool := by
  unfold isProperBlockColoring
  let encGB := encPair encGraph (encList encNat)
  let encIn := encPair encGB encNat
  let encQ := encPair encIn encUnary
  have hG : ComputableInPolyTime (fun p : (Graph × List ℕ) × ℕ => p.1.1) encIn encGraph :=
    (fst encGraph (encList encNat)).comp (fst encGB encNat)
  have hB : ComputableInPolyTime (fun p : (Graph × List ℕ) × ℕ => p.1.2) encIn (encList encNat) :=
    (snd encGraph (encList encNat)).comp (fst encGB encNat)
  have hc : ComputableInPolyTime (fun p : (Graph × List ℕ) × ℕ => p.2) encIn encNat :=
    snd encGB encNat
  have hrng := range.comp ((length_list encNat).comp hB)
  have hinner : ComputableInPolyTime
      (fun q : ((Graph × List ℕ) × ℕ) × ℕ =>
        decide (color2Bit q.1.2 q.2 < 3) &&
          (List.range q.1.1.2.length).all fun j =>
            !(q.1.1.1.adjBool (q.1.1.2.getD q.2 0) (q.1.1.2.getD j 0) &&
              decide (color2Bit q.1.2 q.2 = color2Bit q.1.2 j))) encQ encBool := by
    have hci := computableInPolyTime_color2Bit.comp
      ((hc.comp (fst encIn encUnary)).prod (snd encIn encUnary))
    have htestj : ComputableInPolyTime
        (fun r : (((Graph × List ℕ) × ℕ) × ℕ) × ℕ =>
          !(r.1.1.1.1.adjBool (r.1.1.1.2.getD r.1.2 0) (r.1.1.1.2.getD r.2 0) &&
            decide (color2Bit r.1.1.2 r.1.2 =
              color2Bit r.1.1.2 r.2))) (encPair encQ encUnary) encBool := by
      have hp := fst encQ encUnary; have hB' := hB.comp ((fst encIn encUnary).comp hp)
      have hc' := hc.comp ((fst encIn encUnary).comp hp); have hi' := (snd encIn encUnary).comp hp
      have hj' := snd encQ encUnary
      have hadj := Graph.computableInPolyTime_adjBool_comp (hG.comp ((fst encIn encUnary).comp hp))
        (listGetDWithInput hB' hi' 0) (listGetDWithInput hB' hj' 0)
      exact bool_not.comp (bool_and.comp (hadj.prod (beq
        (computableInPolyTime_color2Bit.comp (hc'.prod hi'))
        (computableInPolyTime_color2Bit.comp (hc'.prod hj')))))
    exact bool_and.comp ((unary_lt.comp (hci.prod (const 3))).prod
      (allWith htestj ComputableInPolyTime.id' (hrng.comp (fst encIn encUnary))))
  exact allWith hinner ComputableInPolyTime.id' hrng

private theorem computableInPolyTime_blockSize :
    ComputableInPolyTime (fun p : ℕ × ℕ => blockSize p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
  unfold blockSize
  have hnum := unary_sub.comp ((unary_add.comp ((fst _ _).prod (snd _ _))).prod (const 1))
  have hdiv := binary_div.comp ((unary_to_binary.comp hnum).prod (unary_to_binary.comp (snd _ _)))
  have hmin := binary_min_unary.comp ((unary_add.comp ((fst _ _).prod (snd _ _))).prod hdiv)
  convert hmin using 1; funext p
  exact (Nat.min_eq_right ((Nat.div_le_self _ _).trans (Nat.sub_le _ _))).symm

theorem computableInPolyTime_vertexBlock :
    ComputableInPolyTime (fun p : (List ℕ × ℕ) × ℕ => vertexBlock p.1.1 p.1.2 p.2)
      (encPair (encPair (encList encNat) encUnary) encUnary) (encList encNat) := by
  unfold vertexBlock
  have hV := (fst (encList encNat) encUnary).comp (fst (encPair (encList encNat) encUnary) encUnary)
  have hq := (snd (encList encNat) encUnary).comp (fst (encPair (encList encNat) encUnary) encUnary)
  have hr := snd (encPair (encList encNat) encUnary) encUnary
  have hb := computableInPolyTime_blockSize.comp (((length_list encNat).comp hV).prod hq)
  exact (takeUnary encNat).comp ((listDropWithInput hV (unary_mul.comp (hr.prod hb))).prod hb)

private theorem computableInPolyTime_areBlockColoringsCompat :
    ComputableInPolyTime
      (fun p : (Graph × List ℕ × List ℕ) × (ℕ × ℕ) =>
        areBlockColoringsCompat p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2)
      (encPair (encPair encGraph (encPair (encList encNat) (encList encNat)))
        (encPair encNat encNat)) encBool := by
  unfold areBlockColoringsCompat
  let encP := encPair encGraph (encPair (encList encNat) (encList encNat))
  let encIn := encPair encP (encPair encNat encNat)
  let encQ := encPair encIn encUnary
  have hG : ComputableInPolyTime (fun p => p.1.1) encIn encGraph := (fst _ _).comp (fst _ _)
  have hB1 : ComputableInPolyTime (fun p => p.1.2.1) encIn (encList encNat) :=
    ((fst _ _).comp (snd _ _)).comp (fst _ _)
  have hB2 : ComputableInPolyTime (fun p => p.1.2.2) encIn (encList encNat) :=
    ((snd _ _).comp (snd _ _)).comp (fst _ _)
  have hc1 : ComputableInPolyTime (fun p => p.2.1) encIn encNat := (fst _ _).comp (snd _ _)
  have hc2 : ComputableInPolyTime (fun p => p.2.2) encIn encNat := (snd _ _).comp (snd _ _)
  have htestj : ComputableInPolyTime
      (fun r : (((Graph × List ℕ × List ℕ) × (ℕ × ℕ)) × ℕ) × ℕ =>
        !(r.1.1.1.1.adjBool (r.1.1.1.2.1.getD r.1.2 0) (r.1.1.1.2.2.getD r.2 0) &&
          decide (color2Bit r.1.1.2.1 r.1.2 =
            color2Bit r.1.1.2.2 r.2))) (encPair encQ encUnary) encBool := by
    have hp := (fst encIn encUnary).comp (fst encQ encUnary)
    have hi := (snd encIn encUnary).comp (fst encQ encUnary); have hj := snd encQ encUnary
    have hadj := Graph.computableInPolyTime_adjBool_comp (hG.comp hp)
      (listGetDWithInput (hB1.comp hp) hi 0) (listGetDWithInput (hB2.comp hp) hj 0)
    exact bool_not.comp (bool_and.comp (hadj.prod (beq
      (computableInPolyTime_color2Bit.comp ((hc1.comp hp).prod hi))
      (computableInPolyTime_color2Bit.comp ((hc2.comp hp).prod hj)))))
  exact allWith (allWith htestj ComputableInPolyTime.id'
      ((range.comp ((length_list encNat).comp hB2)).comp (fst encIn encUnary)))
    ComputableInPolyTime.id' (range.comp ((length_list encNat).comp hB1))

private theorem computableInPolyTime_blockVertId :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => blockVertId p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encNat) encNat :=
  binary_add.comp ((unary_to_binary.comp ((snd encUnary encUnary).comp (fst _ _))).prod
    (binary_mul.comp ((unary_to_binary.comp ((fst encUnary encUnary).comp (fst _ _))).prod
      (snd _ _))))

theorem computableInPolyTime_postClique :
    ComputableInPolyTime
      (fun p : (Graph × List ℕ) × (ℕ × List (ℕ × List ℕ)) =>
        let G := p.1.1; let V := p.1.2; let q := p.2.1; let bv := p.2.2
        let verts := bv.flatMap fun x => x.2.map fun c => blockVertId q x.1 c
        let edges := bv.flatMap fun p₁ => bv.flatMap fun p₂ =>
          if p₁.1 == p₂.1 then []
          else p₁.2.flatMap fun c₁ =>
            (p₂.2.filter fun c₂ =>
              areBlockColoringsCompat G (vertexBlock V q p₁.1) (vertexBlock V q p₂.1) c₁ c₂).map
              fun c₂ => (blockVertId q p₁.1 c₁, blockVertId q p₂.1 c₂)
        (⟨⟨verts, edges⟩, q⟩ : CliqueInstance))
      (encPair (encPair encGraph (encList encNat))
        (encPair encUnary (encList (encPair encUnary (encList encNat)))))
      encCliqueInstance := by
  let encGV := encPair encGraph (encList encNat)
  let encBV := encPair encUnary (encList encNat)
  let encIn := encPair encGV (encPair encUnary (encList encBV))
  have hq : ComputableInPolyTime (fun p => p.2.1) encIn encUnary := (fst _ _).comp (snd _ _)
  have hbv : ComputableInPolyTime (fun p => p.2.2) encIn (encList encBV) :=
    (snd _ _).comp (snd _ _)
  have hverts := flatMapWith
    (mapWith computableInPolyTime_blockVertId
      ((fst _ _).prod ((fst _ _).comp (snd _ _))) ((snd _ _).comp (snd _ _)))
    hq hbv
  have hpair_edges : ComputableInPolyTime
      (fun x : ((Graph × List ℕ) × ℕ × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
        let G := x.1.1.1; let V := x.1.1.2; let q := x.1.2.1; let p₁ := x.1.2.2; let p₂ := x.2
        if p₁.1 == p₂.1 then ([] : List (ℕ × ℕ))
        else p₁.2.flatMap fun c₁ =>
          (p₂.2.filter fun c₂ =>
            areBlockColoringsCompat G (vertexBlock V q p₁.1) (vertexBlock V q p₂.1) c₁ c₂).map
            fun c₂ => (blockVertId q p₁.1 c₁, blockVertId q p₂.1 c₂))
      (encPair (encPair encGV (encPair encUnary encBV)) encBV)
      (encList (encPair encNat encNat)) := by
    let encX := encPair (encPair encGV (encPair encUnary encBV)) encBV
    have hG : ComputableInPolyTime (fun x => x.1.1.1) encX encGraph :=
      ((fst _ _).comp (fst _ _)).comp (fst _ _)
    have hV : ComputableInPolyTime (fun x => x.1.1.2) encX (encList encNat) :=
      ((snd _ _).comp (fst _ _)).comp (fst _ _)
    have hq' : ComputableInPolyTime (fun x => x.1.2.1) encX encUnary :=
      ((fst _ _).comp (snd _ _)).comp (fst _ _)
    have hp1 : ComputableInPolyTime (fun x => x.1.2.2) encX encBV :=
      ((snd _ _).comp (snd _ _)).comp (fst _ _)
    have hp2 : ComputableInPolyTime (fun x => x.2) encX encBV := snd _ _
    have hcond := beq hp1.fst' hp2.fst'
    have hB1 := computableInPolyTime_vertexBlock.comp ((hV.prod hq').prod hp1.fst')
    have hB2 := computableInPolyTime_vertexBlock.comp ((hV.prod hq').prod hp2.fst')
    have hbranch : ComputableInPolyTime
        (fun x => x.1.2.2.2.flatMap fun c₁ =>
          (x.2.2.filter fun c₂ =>
            areBlockColoringsCompat x.1.1.1 (vertexBlock x.1.1.2 x.1.2.1 x.1.2.2.1)
              (vertexBlock x.1.1.2 x.1.2.1 x.2.1) c₁ c₂).map
            fun c₂ => (blockVertId x.1.2.1 x.1.2.2.1 c₁, blockVertId x.1.2.1 x.2.1 c₂))
        encX (encList (encPair encNat encNat)) := by
      let encP1 := encPair (encPair encGraph (encPair (encList encNat) (encList encNat)))
        (encPair encUnary (encPair encUnary (encPair encUnary (encList encNat))))
      have hbody : ComputableInPolyTime
          (fun y : ((Graph × List ℕ × List ℕ) × (ℕ × ℕ × ℕ × List ℕ)) × ℕ =>
            (y.1.2.2.2.2.filter fun c₂ =>
              areBlockColoringsCompat y.1.1.1 y.1.1.2.1 y.1.1.2.2 y.2 c₂).map
              fun c₂ => (blockVertId y.1.2.1 y.1.2.2.1 y.2, blockVertId y.1.2.1 y.1.2.2.2.1 c₂))
          (encPair encP1 encNat) (encList (encPair encNat encNat)) := by
        let encY := encPair encP1 encNat
        have hpar_y : ComputableInPolyTime
            (fun y => ((y.1.1.1, (y.1.1.2.1, y.1.1.2.2)), y.2))
            encY (encPair (encPair encGraph (encPair (encList encNat) (encList encNat))) encNat) :=
          ((fst _ _).comp (fst encP1 encNat)).prod (snd encP1 encNat)
        have hfilt := filterWith
          (computableInPolyTime_areBlockColoringsCompat.comp
            (((fst _ _).comp (fst _ _)).prod (((snd _ _).comp (fst _ _)).prod (snd _ _))))
          hpar_y
          ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (fst encP1 encNat)))))
        exact mapWith
          ((computableInPolyTime_blockVertId.comp
              (((fst _ _).comp (fst _ _)).prod ((fst _ _).comp ((snd _ _).comp (fst _ _))))).prod
            (computableInPolyTime_blockVertId.comp
              ((((fst _ _).comp ((fst _ _).comp (fst _ _))).prod
                ((snd _ _).comp ((snd _ _).comp (fst _ _)))).prod (snd _ _))))
          ((((fst _ _).comp ((snd _ _).comp (fst encP1 encNat))).prod
            ((fst _ _).comp ((snd _ _).comp ((snd _ _).comp (fst encP1 encNat))))).prod
            ((snd encP1 encNat).prod
              ((fst _ _).comp ((snd _ _).comp ((snd _ _).comp
                ((snd _ _).comp (fst encP1 encNat)))))))
          hfilt
      exact flatMapWith hbody
        ((hG.prod (hB1.prod hB2)).prod (hq'.prod (hp1.fst'.prod (hp2.fst'.prod hp2.snd'))))
        hp1.snd'
    exact hcond.ite' (const []) hbranch
  have hedges := flatMapWith
    (flatMapWith hpair_edges
      (((fst _ _).comp (fst _ _)).prod ((((fst _ _).comp (snd _ _)).comp (fst _ _)).prod (snd _ _)))
      (((snd _ _).comp (snd _ _)).comp (fst _ _)))
    ComputableInPolyTime.id' hbv
  have hG_mk : ComputableInPolyTime
      (fun p : (Graph × List ℕ) × (ℕ × List (ℕ × List ℕ)) =>
        (⟨p.2.2.flatMap fun x => x.2.map fun c => blockVertId p.2.1 x.1 c,
          p.2.2.flatMap fun p₁ => p.2.2.flatMap fun p₂ =>
            if p₁.1 == p₂.1 then []
            else p₁.2.flatMap fun c₁ =>
              (p₂.2.filter fun c₂ =>
                areBlockColoringsCompat p.1.1 (vertexBlock p.1.2 p.2.1 p₁.1)
                  (vertexBlock p.1.2 p.2.1 p₂.1) c₁ c₂).map
                fun c₂ => (blockVertId p.2.1 p₁.1 c₁, blockVertId p.2.1 p₂.1 c₂)⟩ : Graph))
      encIn encGraph :=
    (hverts.prod hedges).of_enc_eq fun _ => rfl
  exact (hG_mk.prod (unary_to_binary.comp hq)).of_enc_eq fun _ => rfl

end Cslib.Complexity
