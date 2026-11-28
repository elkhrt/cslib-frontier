module

public import CslibFrontier.Computability.Complexity.FineGrained.Reduction
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique
public import CslibFrontier.Computability.Complexity.Problems.IndependentSet
public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
import CslibFrontier.Computability.Complexity.Problems.Clique.OfAdj
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.PolyTime
import Mathlib.Data.List.GetD

/-!
# Multicolored Clique: NP-Hardness, W[1]-Hardness, and Linear-Size ETH Reduction

This module formalizes the **Multicolored Clique (MCC)** problem, its binary encoding
`encMulticoloredCliqueInstance`, polynomial-time and FPT reductions from `Clique` (establishing
`MulticoloredClique_npHard` and `MulticoloredClique_wHard`), a linear-size polynomial-time
reduction from `ThreeSAT` (`threeSATToMCC`), a polynomial-time well-formedness checker
(`isWellFormedBool`), and universal-vertex padding (`padUniversalMCC`).

## Main definitions

* `Cslib.Complexity.MulticoloredCliqueInstance`
* `Cslib.Complexity.encMulticoloredCliqueInstance`
* `Cslib.Complexity.MulticoloredClique`
* `Cslib.Complexity.cliqueToMCC`
* `Cslib.Complexity.threeSATToMCC`
* `Cslib.Complexity.isWellFormedBool`
* `Cslib.Complexity.padUniversalMCC`

## Main results

* `Cslib.Complexity.MulticoloredClique_npHard`
* `Cslib.Complexity.MulticoloredClique_wHard`
* `Cslib.Complexity.threeSATToMCC_mem_iff`
* `Cslib.Complexity.threeSATToMCC_numVertices_le`
* `Cslib.Complexity.padUniversalMCC_mem_iff`
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Multicolored Clique -/

/-- An instance of **Multicolored Clique (MCC)**: an undirected graph `graph`, a number of color
classes `k`, and a color assignment `colors` parallel to `graph.vertices` partitioning the declared
vertices into color classes `V_0, …, V_{k-1}`. -/
@[ext]
structure MulticoloredCliqueInstance where
  /-- The underlying undirected graph. -/
  graph : Cslib.Complexity.Graph
  /-- The number of color classes (target clique size). -/
  k : ℕ
  /-- The list of colors parallel to `graph.vertices`, assigning each declared vertex a color in
  `[0, k)`. -/
  colors : List ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Binary encoding of `MulticoloredCliqueInstance`. -/
enc_structure encMulticoloredCliqueInstance : MulticoloredCliqueInstance where
  graph : encGraph,
  k : encNat,
  colors : (encList encNat)

attribute [fun_prop] encMulticoloredCliqueInstance_graph_polyTime
  encMulticoloredCliqueInstance_k_polyTime encMulticoloredCliqueInstance_colors_polyTime
  encMulticoloredCliqueInstance_mk_polyTime

/-- Well-formedness of an MCC instance: `graph.vertices` has no duplicates, `colors` is parallel to
`graph.vertices` with values `< k`, and each color class is an independent set. -/
def MulticoloredCliqueInstance.IsWellFormed (x : MulticoloredCliqueInstance) : Prop :=
  x.graph.vertices.Nodup ∧
  x.colors.length = x.graph.vertices.length ∧
  (∀ c ∈ x.colors, c < x.k) ∧
  ∀ (i j : ℕ) (hi : i < x.graph.vertices.length) (hj : j < x.graph.vertices.length),
    x.colors[i]? = x.colors[j]? →
      ¬ x.graph.toSimpleGraph.Adj x.graph.vertices[i] x.graph.vertices[j]

theorem MulticoloredCliqueInstance.isWellFormed_iff (x : MulticoloredCliqueInstance) :
    x.IsWellFormed ↔
      x.graph.vertices.Nodup ∧
      x.colors.length = x.graph.vertices.length ∧
      (∀ c ∈ x.colors, c < x.k) ∧
      ∀ (i j : ℕ) (hi : i < x.graph.vertices.length) (hj : j < x.graph.vertices.length),
        x.colors[i]? = x.colors[j]? →
          ¬ x.graph.toSimpleGraph.Adj x.graph.vertices[i] x.graph.vertices[j] :=
  Iff.rfl

/-- **Multicolored Clique (MCC)**: well-formed instances admitting a clique of size `k`. -/
def MulticoloredClique : Set MulticoloredCliqueInstance :=
  {x | x.IsWellFormed ∧ (⟨x.graph, x.k⟩ : CliqueInstance) ∈ Clique}

theorem mem_MulticoloredClique_iff {x : MulticoloredCliqueInstance} :
    x ∈ MulticoloredClique ↔ x.IsWellFormed ∧ (⟨x.graph, x.k⟩ : CliqueInstance) ∈ Clique :=
  Iff.rfl


/-! ### Helper: `Clique` → `MulticoloredClique` -/

/-- Canonical YES-instance of `MulticoloredClique` (`k = 1`, single vertex `0` of color `0`). -/
def mccYesInstance : MulticoloredCliqueInstance :=
  ⟨⟨[0], []⟩, 1, [0]⟩

/-- Canonical well-formed NO-instance of `MulticoloredClique` with parameter `k ≥ 1`. -/
def mccNoInstanceOfK (k : ℕ) : MulticoloredCliqueInstance :=
  ⟨⟨[], []⟩, k, []⟩

/-- Canonical NO-instance of `MulticoloredClique` (`k = 1`, empty vertex set). -/
def mccNoInstance : MulticoloredCliqueInstance :=
  mccNoInstanceOfK 1

theorem mccNoInstanceOfK_isWellFormed (k : ℕ) : (mccNoInstanceOfK k).IsWellFormed := by
  rw [MulticoloredCliqueInstance.isWellFormed_iff]
  exact ⟨List.nodup_nil, rfl, fun _ hc => (List.not_mem_nil hc).elim,
    fun _ _ hi => (Nat.not_lt_zero _ hi).elim⟩

theorem mccNoInstanceOfK_notMem {k : ℕ} (hk : 1 ≤ k) :
    mccNoInstanceOfK k ∉ MulticoloredClique := by
  rw [mem_MulticoloredClique_iff]
  rintro ⟨_, hcl⟩
  rw [mem_Clique_iff_mk] at hcl
  obtain ⟨S, hS, hc⟩ := hcl
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by rw [hc.card_eq]; simp [mccNoInstanceOfK]; omega)
  exact List.not_mem_nil (hS v hv)

theorem mccYesInstance_mem : mccYesInstance ∈ MulticoloredClique := by
  rw [mem_MulticoloredClique_iff]
  refine ⟨?_, ?_⟩
  · rw [MulticoloredCliqueInstance.isWellFormed_iff]
    refine ⟨by simp [mccYesInstance], rfl, by simp [mccYesInstance], ?_⟩
    intro i j hi hj _
    simp only [mccYesInstance, List.length_singleton] at hi hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    exact SimpleGraph.irrefl _
  · rw [mem_Clique_iff_mk]
    refine ⟨{0}, by simp [mccYesInstance], ?_⟩
    simp [mccYesInstance, SimpleGraph.isNClique_iff, SimpleGraph.IsClique]

theorem mccNoInstance_notMem : mccNoInstance ∉ MulticoloredClique :=
  mccNoInstanceOfK_notMem le_rfl

/-- Construct the `k`-partite duplicated graph from a `Graph` and `k` (assuming `1 ≤ k ≤ n`):
vertex `(c, i)` is numbered `c * n + i` for `c < k` and `i < n = G.distinctVertices.length`. -/
def duplicateMCC (G : Cslib.Complexity.Graph) (k : ℕ) : MulticoloredCliqueInstance :=
  let vs := G.distinctVertices
  let n := vs.length
  let total := k * n
  let verts := List.range total
  let colors := (List.range total).map (fun x => x / n)
  let edges :=
    (List.range total).flatMap fun a =>
      ((List.range total).filter fun b =>
        decide (a / n ≠ b / n) && Graph.adjBool G (vs.getD (a % n) 0) (vs.getD (b % n) 0)).map
          fun b => (a, b)
  ⟨⟨verts, edges⟩, k, colors⟩

/-- Polynomial-time and fpt reduction from `Clique` to `MulticoloredClique`. -/
def cliqueToMCC (x : CliqueInstance) : MulticoloredCliqueInstance :=
  if x.m = 0 then mccYesInstance
  else if x.m ≤ x.graph.distinctVertices.length then duplicateMCC x.graph x.m
  else mccNoInstance

theorem duplicateMCC_isWellFormed (G : Cslib.Complexity.Graph) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ G.distinctVertices.length) :
    (duplicateMCC G k).IsWellFormed := by
  rw [MulticoloredCliqueInstance.isWellFormed_iff]
  set vs := G.distinctVertices
  set n := vs.length
  have hn : 0 < n := by omega
  refine ⟨List.nodup_range, by simp [duplicateMCC], ?_, ?_⟩
  · intro c hc
    simp only [duplicateMCC, List.mem_map, List.mem_range] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])
  · intro i j hi hj hcol hadj
    simp only [duplicateMCC, List.length_range] at hi hj
    simp only [duplicateMCC, List.getElem?_map, List.getElem?_range, hi, hj, Option.map_some,
      Option.some.injEq] at hcol
    rw [Graph.toSimpleGraph_adj] at hadj
    obtain ⟨_, hmem⟩ := hadj
    simp only [duplicateMCC, List.getElem_range, List.mem_flatMap, List.mem_map, List.mem_filter,
      List.mem_range, Bool.and_eq_true, decide_eq_true_eq, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, _, _, ⟨_, hne, _⟩, rfl, rfl⟩ | ⟨_, _, _, ⟨_, hne, _⟩, rfl, rfl⟩
    · exact hne hcol
    · exact hne hcol.symm

theorem duplicateMCC_adj_iff (G : Cslib.Complexity.Graph) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ G.distinctVertices.length) {a b : ℕ}
    (ha : a < k * G.distinctVertices.length) (hb : b < k * G.distinctVertices.length) :
    (duplicateMCC G k).graph.toSimpleGraph.Adj a b ↔
      a / G.distinctVertices.length ≠ b / G.distinctVertices.length ∧
      G.toSimpleGraph.Adj
        (G.distinctVertices.getD (a % G.distinctVertices.length) 0)
        (G.distinctVertices.getD (b % G.distinctVertices.length) 0) := by
  set vs := G.distinctVertices
  set n := vs.length
  have hn : 0 < n := by omega
  rw [Graph.toSimpleGraph_adj]
  have hedge : ∀ x y, (x, y) ∈ (duplicateMCC G k).graph.edges ↔
      x < k * n ∧ y < k * n ∧ x / n ≠ y / n ∧
      G.toSimpleGraph.Adj (vs.getD (x % n) 0) (vs.getD (y % n) 0) := by
    intro x y
    simp only [duplicateMCC, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq, Prod.mk.injEq, Graph.adjBool_eq_true_iff]
    constructor
    · rintro ⟨a', ha', b', ⟨hb', hdiv, hadj⟩, rfl, rfl⟩
      exact ⟨ha', hb', hdiv, hadj⟩
    · rintro ⟨hx, hy, hdiv, hadj⟩
      exact ⟨x, hx, y, ⟨hy, hdiv, hadj⟩, rfl, rfl⟩
  constructor
  · rintro ⟨_, h | h⟩
    · have := (hedge a b).mp h; exact ⟨this.2.2.1, this.2.2.2⟩
    · have := (hedge b a).mp h; exact ⟨this.2.2.1.symm, this.2.2.2.symm⟩
  · rintro ⟨hdiv, hadj⟩
    refine ⟨fun heq => hdiv (by rw [heq]), Or.inl ((hedge a b).mpr ⟨ha, hb, hdiv, hadj⟩)⟩

theorem duplicateMCC_mem_iff (G : Cslib.Complexity.Graph) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ G.distinctVertices.length) :
    duplicateMCC G k ∈ MulticoloredClique ↔ (⟨G, k⟩ : CliqueInstance) ∈ Clique := by
  classical
  set vs := G.distinctVertices
  set n := vs.length
  have hn : 0 < n := by omega
  rw [mem_MulticoloredClique_iff, mem_Clique_iff_mk, mem_Clique_iff_mk]
  constructor
  · rintro ⟨_, S, hS, hcl⟩
    have hlt : ∀ a ∈ S, a < k * n := fun a ha => by
      simpa [duplicateMCC] using hS a ha
    let f : ℕ → ℕ := fun a => vs.getD (a % n) 0
    refine ⟨S.image f, ?_, ?_, ?_⟩
    · intro v hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
      have hmod : a % n < vs.length := Nat.mod_lt a hn
      rw [← Graph.mem_distinctVertices]
      have hget : vs.getD (a % n) 0 = vs[a % n] := by
        simp [List.getD_eq_getElem?_getD, hmod]
      change vs.getD (a % n) 0 ∈ vs
      rw [hget]
      exact List.getElem_mem hmod
    · intro v hv w hw hvw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
      have hab : a ≠ b := fun h => hvw (by rw [h])
      exact ((duplicateMCC_adj_iff G hk hkn (hlt a ha) (hlt b hb)).mp
        (hcl.isClique ha hb hab)).2
    · rw [Finset.card_image_of_injOn]
      · simpa [duplicateMCC] using hcl.card_eq
      · intro a ha b hb hfab
        by_contra hab
        exact (((duplicateMCC_adj_iff G hk hkn (hlt a ha) (hlt b hb)).mp
          (hcl.isClique ha hb hab)).2.ne) hfab
  · rintro ⟨S, hS, hcl⟩
    refine ⟨duplicateMCC_isWellFormed G hk hkn, ?_⟩
    let e : Fin k ≃ S := (Fintype.equivFinOfCardEq (by simp [hcl.card_eq])).symm
    let g : Fin k → ℕ := fun c => c.1 * n + vs.idxOf (e c).1
    have hg_lt : ∀ c : Fin k, g c < k * n := fun c => by
      have hmem : (e c).1 ∈ vs := Graph.mem_distinctVertices.mpr (hS _ (e c).2)
      have hidx : vs.idxOf (e c).1 < n := List.idxOf_lt_length_of_mem hmem
      have h1 : (c.1 + 1) * n ≤ k * n := Nat.mul_le_mul_right n c.2
      have : c.1 * n + vs.idxOf (e c).1 < (c.1 + 1) * n := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      exact lt_of_lt_of_le this h1
    have hg_div : ∀ c : Fin k, g c / n = c.1 := fun c => by
      have hmem : (e c).1 ∈ vs := Graph.mem_distinctVertices.mpr (hS _ (e c).2)
      have hidx : vs.idxOf (e c).1 < n := List.idxOf_lt_length_of_mem hmem
      change (c.1 * n + vs.idxOf (e c).1) / n = c.1
      rw [Nat.mul_comm c.1 n, Nat.mul_add_div hn, Nat.div_eq_of_lt hidx, Nat.add_zero]
    have hg_mod : ∀ c : Fin k, g c % n = vs.idxOf (e c).1 := fun c => by
      have hmem : (e c).1 ∈ vs := Graph.mem_distinctVertices.mpr (hS _ (e c).2)
      have hidx : vs.idxOf (e c).1 < n := List.idxOf_lt_length_of_mem hmem
      change (c.1 * n + vs.idxOf (e c).1) % n = vs.idxOf (e c).1
      rw [Nat.mul_comm c.1 n, Nat.mul_add_mod, Nat.mod_eq_of_lt hidx]
    have hg_inj : Function.Injective g := fun c₁ c₂ h => by
      have := congrArg (· / n) h
      rw [hg_div, hg_div] at this
      exact Fin.ext this
    refine ⟨Finset.univ.image g, ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp ha
      simpa [duplicateMCC] using hg_lt c
    · intro a ha b hb hab
      obtain ⟨c₁, -, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨c₂, -, rfl⟩ := Finset.mem_image.mp hb
      have hc : c₁ ≠ c₂ := fun h => hab (by rw [h])
      rw [duplicateMCC_adj_iff G hk hkn (hg_lt c₁) (hg_lt c₂), hg_div, hg_div, hg_mod, hg_mod]
      have hm1 : (e c₁).1 ∈ vs := Graph.mem_distinctVertices.mpr (hS _ (e c₁).2)
      have hm2 : (e c₂).1 ∈ vs := Graph.mem_distinctVertices.mpr (hS _ (e c₂).2)
      have hget1 : vs.getD (vs.idxOf (e c₁).1) 0 = (e c₁).1 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_idxOf hm1]
      have hget2 : vs.getD (vs.idxOf (e c₂).1) 0 = (e c₂).1 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_idxOf hm2]
      rw [hget1, hget2]
      exact ⟨fun h => hc (Fin.ext h), hcl.isClique (e c₁).2 (e c₂).2 (fun h => hc (e.injective
        (Subtype.ext h)))⟩
    · simp only [duplicateMCC]
      rw [Finset.card_image_of_injective _ hg_inj, Finset.card_fin]

theorem cliqueToMCC_mem_iff (x : CliqueInstance) :
    cliqueToMCC x ∈ MulticoloredClique ↔ x ∈ Clique := by
  unfold cliqueToMCC
  split_ifs with h0 hle
  · constructor
    · intro _
      rw [mem_Clique_iff]
      exact ⟨∅, by simp, by simp [h0, SimpleGraph.isNClique_iff]⟩
    · intro _; exact mccYesInstance_mem
  · exact duplicateMCC_mem_iff x.graph (by omega) hle
  · constructor
    · intro h; exact (mccNoInstance_notMem h).elim
    · intro h
      have hcard : x.m ≤ x.graph.distinctVertices.length := by
        rw [mem_Clique_iff] at h
        obtain ⟨S, hS, hc⟩ := h
        calc x.m = S.card := hc.card_eq.symm
          _ ≤ x.graph.distinctVertices.toFinset.card :=
            Finset.card_le_card fun v hv =>
              List.mem_toFinset.mpr (Graph.mem_distinctVertices.mpr (hS v hv))
          _ ≤ x.graph.distinctVertices.length := List.toFinset_card_le _
      omega

theorem cliqueToMCC_k_le (x : CliqueInstance) : (cliqueToMCC x).k ≤ x.m + 1 := by
  unfold cliqueToMCC
  split_ifs with h0 hle
  · simp [mccYesInstance]
  · simp [duplicateMCC]
  · simp [mccNoInstance, mccNoInstanceOfK]

/-- Computing `duplicateMCC` is polynomial-time when `k` is in unary. -/
theorem computableInPolyTime_duplicateMCC :
    ComputableInPolyTime (fun p : Cslib.Complexity.Graph × ℕ => duplicateMCC p.1 p.2)
      (encPair encGraph encUnary) encMulticoloredCliqueInstance := by
  have htot : ComputableInPolyTime (fun p : Cslib.Complexity.Graph × ℕ =>
      p.2 * p.1.distinctVertices.length) (encPair encGraph encUnary) encUnary := by
    have hlen : ComputableInPolyTime (fun p : Cslib.Complexity.Graph × ℕ =>
        p.1.distinctVertices.length) (encPair encGraph encUnary) encUnary := by fun_prop
    have hm : ComputableInPolyTime (fun p : Cslib.Complexity.Graph × ℕ => p.2)
        (encPair encGraph encUnary) encUnary := by fun_prop
    exact ComputableInPolyTime.unary_mul.comp (hm.prod hlen)
  have hrange : ComputableInPolyTime (fun p : Cslib.Complexity.Graph × ℕ =>
      List.range (p.2 * p.1.distinctVertices.length))
      (encPair encGraph encUnary) (encList encUnary) :=
    (ComputableInPolyTime.range).comp htot
  have hrange_nat : ComputableInPolyTime (fun p : Cslib.Complexity.Graph × ℕ =>
      List.range (p.2 * p.1.distinctVertices.length))
      (encPair encGraph encUnary) (encList encNat) := by
    have hmap := ComputableInPolyTime.map (α := ℕ) (β := ℕ)
      (encA := encUnary) (encB := encNat) ComputableInPolyTime.unary_to_binary
    exact (hmap.comp hrange).of_enc_eq fun p => by simp
  have hcolors : ComputableInPolyTime (fun p : Cslib.Complexity.Graph × ℕ =>
      (List.range (p.2 * p.1.distinctVertices.length)).map
        fun x => x / p.1.distinctVertices.length)
      (encPair encGraph encUnary) (encList encNat) := by
    refine ComputableInPolyTime.mapWithInput hrange ?_
    have hdiv : ComputableInPolyTime (fun q : (Cslib.Complexity.Graph × ℕ) × ℕ =>
        q.2 / q.1.1.distinctVertices.length)
        (encPair (encPair encGraph encUnary) encUnary) encUnary := by
      fun_prop
    exact ComputableInPolyTime.unary_to_binary.comp hdiv
  have hedges : ComputableInPolyTime (fun p : Cslib.Complexity.Graph × ℕ =>
      (List.range (p.2 * p.1.distinctVertices.length)).flatMap fun a =>
        ((List.range (p.2 * p.1.distinctVertices.length)).filter fun b =>
          decide (a / p.1.distinctVertices.length ≠ b / p.1.distinctVertices.length) &&
            Graph.adjBool p.1
              (p.1.distinctVertices.getD (a % p.1.distinctVertices.length) 0)
              (p.1.distinctVertices.getD (b % p.1.distinctVertices.length) 0)).map
          fun b => (a, b))
      (encPair encGraph encUnary) (encList (encPair encNat encNat)) := by
    refine ComputableInPolyTime.flatMapWithInput hrange ?_
    have hfilt : ComputableInPolyTime (fun q : (Cslib.Complexity.Graph × ℕ) × ℕ =>
        (List.range (q.1.2 * q.1.1.distinctVertices.length)).filter fun b =>
          decide (q.2 / q.1.1.distinctVertices.length ≠ b / q.1.1.distinctVertices.length) &&
            Graph.adjBool q.1.1
              (q.1.1.distinctVertices.getD (q.2 % q.1.1.distinctVertices.length) 0)
              (q.1.1.distinctVertices.getD (b % q.1.1.distinctVertices.length) 0))
        (encPair (encPair encGraph encUnary) encUnary) (encList encUnary) := by
      refine ComputableInPolyTime.filterWithInput (hrange.comp (by fun_prop)) ?_
      polytime
    refine ComputableInPolyTime.mapWithInput hfilt ?_
    have ha : ComputableInPolyTime (fun r : ((Cslib.Complexity.Graph × ℕ) × ℕ) × ℕ => r.1.2)
        (encPair (encPair (encPair encGraph encUnary) encUnary) encUnary) encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
    have hb : ComputableInPolyTime (fun r : ((Cslib.Complexity.Graph × ℕ) × ℕ) × ℕ => r.2)
        (encPair (encPair (encPair encGraph encUnary) encUnary) encUnary) encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
    exact ha.prod hb
  have hk_nat : ComputableInPolyTime (fun p : Cslib.Complexity.Graph × ℕ => p.2)
      (encPair encGraph encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hgraph : ComputableInPolyTime (fun p : Cslib.Complexity.Graph × ℕ =>
      (⟨List.range (p.2 * p.1.distinctVertices.length),
        (List.range (p.2 * p.1.distinctVertices.length)).flatMap fun a =>
          ((List.range (p.2 * p.1.distinctVertices.length)).filter fun b =>
            decide (a / p.1.distinctVertices.length ≠ b / p.1.distinctVertices.length) &&
              Graph.adjBool p.1
                (p.1.distinctVertices.getD (a % p.1.distinctVertices.length) 0)
                (p.1.distinctVertices.getD (b % p.1.distinctVertices.length) 0)).map
            fun b => (a, b)⟩ : Cslib.Complexity.Graph))
      (encPair encGraph encUnary) encGraph :=
    encGraph_mk_polyTime hrange_nat hedges
  exact encMulticoloredCliqueInstance_mk_polyTime hgraph hk_nat hcolors

/-- `cliqueToMCC` is polynomial-time computable. -/
theorem computableInPolyTime_cliqueToMCC :
    ComputableInPolyTime cliqueToMCC encCliqueInstance encMulticoloredCliqueInstance := by
  have hid : ComputableInPolyTime (fun x : CliqueInstance => x)
      encCliqueInstance encCliqueInstance := ComputableInPolyTime.id'
  have hm_b : ComputableInPolyTime (fun x : CliqueInstance => x.m) encCliqueInstance encNat :=
    encCliqueInstance_m_polyTime hid
  have hlen_u : ComputableInPolyTime (fun x : CliqueInstance =>
      x.graph.distinctVertices.length) encCliqueInstance encUnary := by fun_prop
  have hmin : ComputableInPolyTime (fun x : CliqueInstance =>
      min x.m x.graph.distinctVertices.length) encCliqueInstance encUnary :=
    (ComputableInPolyTime.binary_min_unary' hlen_u hm_b).of_enc_eq fun x =>
      congrArg encUnary (Nat.min_comm _ _)
  have hdup : ComputableInPolyTime (fun x : CliqueInstance =>
      duplicateMCC x.graph (min x.m x.graph.distinctVertices.length))
      encCliqueInstance encMulticoloredCliqueInstance := by
    have h := computableInPolyTime_duplicateMCC.comp'
      ((encCliqueInstance_graph_polyTime hid).prod hmin)
    dsimp only at h
    exact h
  have hle : ComputableInPolyTime (fun x : CliqueInstance =>
      decide (x.m ≤ x.graph.distinctVertices.length)) encCliqueInstance encBool :=
    ComputableInPolyTime.binary_le' hm_b (ComputableInPolyTime.unary_to_binary.comp' hlen_u)
  have h0 : ComputableInPolyTime (fun x : CliqueInstance => decide (x.m = 0))
      encCliqueInstance encBool :=
    ComputableInPolyTime.decide_eq' hm_b
      (ComputableInPolyTime.const (encIn := encCliqueInstance) (encOut := encNat) 0)
  have hconst_yes : ComputableInPolyTime (fun _ : CliqueInstance => mccYesInstance)
      encCliqueInstance encMulticoloredCliqueInstance :=
    ComputableInPolyTime.const (encIn := encCliqueInstance)
      (encOut := encMulticoloredCliqueInstance) mccYesInstance
  have hconst_no : ComputableInPolyTime (fun _ : CliqueInstance => mccNoInstance)
      encCliqueInstance encMulticoloredCliqueInstance :=
    ComputableInPolyTime.const (encIn := encCliqueInstance)
      (encOut := encMulticoloredCliqueInstance) mccNoInstance
  exact (ComputableInPolyTime.ite_decide h0 hconst_yes
    (ComputableInPolyTime.ite_decide hle hdup hconst_no)).of_enc_eq fun x =>
    congrArg encMulticoloredCliqueInstance (by
      unfold cliqueToMCC
      split_ifs with ha hb
      · rfl
      · congr 1; omega
      · rfl)

/-- `Clique` reduces to `MulticoloredClique` in polynomial time. -/
theorem polyTimeReducible_Clique_MulticoloredClique :
    PolyTimeReducible encCliqueInstance encMulticoloredCliqueInstance Clique MulticoloredClique :=
  ⟨cliqueToMCC, computableInPolyTime_cliqueToMCC, fun x => (cliqueToMCC_mem_iff x).symm⟩

/-- `Clique` fpt-reduces to `MulticoloredClique` (parameterized by `k`). -/
theorem fptReducible_Clique_MulticoloredClique :
    FPTReducible encCliqueInstance encMulticoloredCliqueInstance (·.m) (·.k)
      Clique MulticoloredClique :=
  FPTReducible.of_computableInPolyTime (f := cliqueToMCC) (h := (· + 1))
    computableInPolyTime_cliqueToMCC cliqueToMCC_k_le fun x => (cliqueToMCC_mem_iff x).symm

/-- **Multicolored Clique is NP-hard.** -/
theorem MulticoloredClique_npHard : NPHard encMulticoloredCliqueInstance MulticoloredClique :=
  Clique_npHard.trans polyTimeReducible_Clique_MulticoloredClique

/-- **Multicolored Clique is W[1]-hard** parameterized by the number of color classes `k`. -/
theorem MulticoloredClique_wHard :
    WHard 1 encMulticoloredCliqueInstance (·.k) MulticoloredClique :=
  Clique_wHard.trans fptReducible_Clique_MulticoloredClique

/-! ### Linear-Size ETH Reduction: `ThreeSAT` → `MulticoloredClique` -/

/-- Build an MCC instance from a CNF formula `φ` by complementing `SAT.toIndependentSet φ` and
coloring each literal occurrence by its clause index. For empty `φ`, returns `mccYesInstance`. -/
def threeSATToMCC (φ : CNF ℕ) : MulticoloredCliqueInstance :=
  if φ.isEmpty then mccYesInstance
  else
    let occs := occurrences φ
    let verts := occs.map Occurrence.vertex
    let colors := occs.map Occurrence.clause
    let edges :=
      occs.flatMap fun o1 =>
        (occs.filter fun o2 => decide (o1.clause ≠ o2.clause ∧ ¬ o1.Conflict o2)).map
          fun o2 => (o1.vertex, o2.vertex)
    ⟨⟨verts, edges⟩, φ.length, colors⟩

/-- `occurrences φ` has no duplicate elements. -/
private theorem nodup_occurrences (φ : CNF ℕ) : (occurrences φ).Nodup := by
  have hzip : ∀ {α : Type} (l : List α) (base : ℕ),
      (l.zipIdx base).Pairwise (fun a b => a.2 ≠ b.2) := by
    intro α l
    induction l with
    | nil => intro _; simp
    | cons x xs ih =>
      intro base
      simp only [List.zipIdx_cons, List.pairwise_cons]
      refine ⟨fun p hp => ?_, ih (base + 1)⟩
      have hge := (List.mem_zipIdx hp).1
      omega
  have hmem : ∀ (i : ℕ) (c : Clause ℕ),
      (c.zipIdx.map fun p => (⟨i, p.2, p.1⟩ : Occurrence ℕ)).Nodup := by
    intro i c
    have hnd : (c.zipIdx (n := 0)).Nodup :=
      (hzip (α := Literal ℕ) c 0).imp fun h heq => h (congrArg Prod.snd heq)
    rw [List.nodup_map_iff_inj_on hnd]
    intro a _ b _ h
    have hc : a.2 = b.2 := by simpa using congrArg Occurrence.pos h
    have hl : a.1 = b.1 := by simpa using congrArg Occurrence.lit h
    exact Prod.ext hl hc
  unfold occurrences
  rw [List.nodup_flatMap]
  refine ⟨fun x _ => hmem x.2 x.1, ?_⟩
  refine (hzip (α := Clause ℕ) φ 0).imp fun {x y} hxy => ?_
  intro o ho1 ho2
  simp only [List.mem_map] at ho1 ho2
  obtain ⟨_, _, rfl⟩ := ho1
  obtain ⟨_, _, hb⟩ := ho2
  have hcl : y.2 = x.2 := by simpa using congrArg Occurrence.clause hb
  exact hxy hcl.symm

/-- Number of occurrences in `φ` is bounded by `3 * φ.length` when every clause has length `≤ 3`. -/
private theorem length_occurrences_le (φ : CNF ℕ) (h3 : ∀ c ∈ φ, c.length ≤ 3) :
    (occurrences φ).length ≤ 3 * φ.length := by
  have hsum : ∀ (ψ : CNF ℕ) (base : ℕ), (∀ c ∈ ψ, c.length ≤ 3) →
      ((ψ.zipIdx base).flatMap fun c => c.1.zipIdx.map fun p =>
        (⟨c.2, p.2, p.1⟩ : Occurrence ℕ)).length ≤ 3 * ψ.length := by
    intro ψ
    induction ψ with
    | nil => intro _ _; simp
    | cons c rest ih =>
      intro base hψ
      simp only [List.zipIdx_cons, List.flatMap_cons, List.length_append, List.length_map,
        List.length_zipIdx, List.length_cons]
      have hc : c.length ≤ 3 := hψ c List.mem_cons_self
      have hr := ih (base + 1) (fun d hd => hψ d (List.mem_cons_of_mem c hd))
      omega
  simpa [occurrences] using hsum φ 0 h3

/-- Number of vertices of `threeSATToMCC φ` is at most `3 * φ.length + 1` on 3-CNF formulas. -/
theorem threeSATToMCC_numVertices_le (φ : CNF ℕ) (h3 : ∀ c ∈ φ, c.length ≤ 3) :
    (threeSATToMCC φ).graph.vertices.length ≤ 3 * φ.length + 1 := by
  unfold threeSATToMCC
  split_ifs with hemp
  · simp [mccYesInstance]
  · simp only [List.length_map]
    have := length_occurrences_le φ h3
    omega

/-- Vertex-index injectivity of `Occurrence.vertex` on `occurrences φ`. -/
private theorem occurrence_vertex_inj {φ : CNF ℕ} {o1 o2 : Occurrence ℕ}
    (h1 : o1 ∈ occurrences φ) (h2 : o2 ∈ occurrences φ)
    (heq : o1.vertex = o2.vertex) : o1 = o2 := by
  obtain ⟨i, j, l⟩ := o1
  obtain ⟨i', j', l'⟩ := o2
  obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 heq
  obtain ⟨_, _, hl⟩ := mem_occurrences.1 h1
  obtain ⟨_, _, hl'⟩ := mem_occurrences.1 h2
  simp only at hl hl'
  rw [hl, hl']

private theorem threeSATToMCC_adj_iff {φ : CNF ℕ} (hne : φ.isEmpty = false)
    {o1 o2 : Occurrence ℕ} (h1 : o1 ∈ occurrences φ) (h2 : o2 ∈ occurrences φ) :
    (threeSATToMCC φ).graph.toSimpleGraph.Adj o1.vertex o2.vertex ↔
      o1.clause ≠ o2.clause ∧ ¬ o1.Conflict o2 := by
  have hedge : ∀ p q, p ∈ occurrences φ → q ∈ occurrences φ →
      ((p.vertex, q.vertex) ∈ (threeSATToMCC φ).graph.edges ↔
        p.clause ≠ q.clause ∧ ¬ p.Conflict q) := by
    intro p q hp hq
    simp only [threeSATToMCC, hne, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap, List.mem_map,
      List.mem_filter, decide_eq_true_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, b, ⟨hb, hcl, hnc⟩, hv1, hv2⟩
      exact occurrence_vertex_inj ha hp hv1 ▸ occurrence_vertex_inj hb hq hv2 ▸ ⟨hcl, hnc⟩
    · rintro ⟨hcl, hnc⟩
      exact ⟨p, hp, q, ⟨hq, hcl, hnc⟩, rfl, rfl⟩
  rw [Graph.toSimpleGraph_adj, hedge o1 o2 h1 h2, hedge o2 o1 h2 h1]
  constructor
  · rintro ⟨_, ⟨hcl, hnc⟩ | ⟨hcl, hnc⟩⟩
    · exact ⟨hcl, hnc⟩
    · exact ⟨hcl.symm, fun hc => hnc hc.symm⟩
  · rintro ⟨hcl, hnc⟩
    exact ⟨fun hv => hcl (congrArg Occurrence.clause (occurrence_vertex_inj h1 h2 hv)),
      Or.inl ⟨hcl, hnc⟩⟩

private theorem threeSATToMCC_isWellFormed {φ : CNF ℕ} (hne : φ.isEmpty = false) :
    (threeSATToMCC φ).IsWellFormed := by
  rw [MulticoloredCliqueInstance.isWellFormed_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [threeSATToMCC, hne, Bool.false_eq_true, ↓reduceIte]
    exact (nodup_occurrences φ).map_on fun a ha b hb h => occurrence_vertex_inj ha hb h
  · simp [threeSATToMCC, hne]
  · intro c hc
    simp only [threeSATToMCC, hne, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hc ⊢
    obtain ⟨o, ho, rfl⟩ := hc
    exact (mem_occurrences.1 ho).1
  · intro i j hi hj hcol hadj
    simp only [threeSATToMCC, hne, Bool.false_eq_true, ↓reduceIte, List.length_map] at hi hj
    simp only [threeSATToMCC, hne, Bool.false_eq_true, ↓reduceIte, List.getElem?_map,
      List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.map_some,
      Option.some.injEq] at hcol
    have h1 : (occurrences φ)[i] ∈ occurrences φ := List.getElem_mem hi
    have h2 : (occurrences φ)[j] ∈ occurrences φ := List.getElem_mem hj
    have hadj' : (threeSATToMCC φ).graph.toSimpleGraph.Adj
        (occurrences φ)[i].vertex (occurrences φ)[j].vertex := by
      simpa [threeSATToMCC, hne] using hadj
    exact ((threeSATToMCC_adj_iff hne h1 h2).mp hadj').1 hcol

/-- Correctness of `threeSATToMCC`: on any CNF formula, `threeSATToMCC φ ∈ MulticoloredClique`
if and only if `φ ∈ SAT`. -/
theorem threeSATToMCC_mem_iff (φ : CNF ℕ) :
    threeSATToMCC φ ∈ MulticoloredClique ↔ φ ∈ SAT := by
  cases hne : φ.isEmpty
  · have hwf := threeSATToMCC_isWellFormed hne
    rw [← SAT.toIndependentSet_mem_iff φ, mem_MulticoloredClique_iff, mem_Clique_iff_mk,
      mem_IndependentSet_iff]
    simp only [SimpleGraph.isNClique_iff, SimpleGraph.isNIndepSet_iff,
      SimpleGraph.IsClique, SimpleGraph.IsIndepSet]
    have hverts : (threeSATToMCC φ).graph.vertices = (SAT.toIndependentSet φ).graph.vertices := by
      simp [threeSATToMCC, SAT.toIndependentSet, hne]
    have hk : (threeSATToMCC φ).k = (SAT.toIndependentSet φ).m := by
      simp [threeSATToMCC, SAT.toIndependentSet, hne]
    constructor
    · rintro ⟨_, S, hSV, hcl, hcard⟩
      refine ⟨S, hverts ▸ hSV, fun u hu v hv huv hadj => ?_, hk ▸ hcard⟩
      have hu' : u ∈ (occurrences φ).map Occurrence.vertex := by
        simpa [threeSATToMCC, hne] using hSV u hu
      have hv' : v ∈ (occurrences φ).map Occurrence.vertex := by
        simpa [threeSATToMCC, hne] using hSV v hv
      obtain ⟨o1, ho1, rfl⟩ := List.mem_map.mp hu'
      obtain ⟨o2, ho2, rfl⟩ := List.mem_map.mp hv'
      have hnc := ((threeSATToMCC_adj_iff hne ho1 ho2).mp (hcl hu hv huv)).2
      exact hnc ((SAT.adj_toIndependentSet_iff ho1 ho2).mp hadj)
    · rintro ⟨S, hSV, hind, hcard⟩
      refine ⟨hwf, S, hverts.symm ▸ hSV, fun u hu v hv huv => ?_, hk.symm ▸ hcard⟩
      have hu' : u ∈ (occurrences φ).map Occurrence.vertex := by
        simpa [SAT.toIndependentSet] using hSV u hu
      have hv' : v ∈ (occurrences φ).map Occurrence.vertex := by
        simpa [SAT.toIndependentSet] using hSV v hv
      obtain ⟨o1, ho1, rfl⟩ := List.mem_map.mp hu'
      obtain ⟨o2, ho2, rfl⟩ := List.mem_map.mp hv'
      rw [threeSATToMCC_adj_iff hne ho1 ho2]
      have hnc : ¬ o1.Conflict o2 := fun hc =>
        hind hu hv huv ((SAT.adj_toIndependentSet_iff ho1 ho2).mpr hc)
      refine ⟨fun hcl => huv ?_, hnc⟩
      by_cases hpos : o1.pos = o2.pos
      · simp [Occurrence.vertex, hcl, hpos]
      · exact (hnc (Or.inl ⟨hcl, hpos⟩)).elim
  · have hnil : φ = [] := List.isEmpty_iff.mp hne
    subst hnil
    simp only [threeSATToMCC, List.isEmpty_nil, ↓reduceIte]
    exact ⟨fun _ => ⟨fun _ => false, by simp [CNF.eval]⟩, fun _ => mccYesInstance_mem⟩

/-- `threeSATToMCC` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_threeSATToMCC :
    ComputableInPolyTime threeSATToMCC encCNF encMulticoloredCliqueInstance := by
  have hclause_nat : ComputableInPolyTime Occurrence.clause SAT.encOccurrence encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hlen_nat : ComputableInPolyTime (fun φ : CNF ℕ => φ.length) encCNF encNat :=
    ComputableInPolyTime.unary_to_binary.comp (SAT.computableInPolyTime_length (by fun_prop))
  have hne : ComputableInPolyTime (fun φ : CNF ℕ => φ.isEmpty) encCNF encBool := by
    fun_prop
  unfold threeSATToMCC
  polytime

/-! ### Well-formedness check & Universal-Vertex Padding -/

/-- Decidable polynomial-time check for `MulticoloredCliqueInstance.IsWellFormed`. -/
def isWellFormedBool (x : MulticoloredCliqueInstance) : Bool :=
  let vs := x.graph.vertices
  let cs := x.colors
  decide (vs.length = cs.length) &&
    cs.all (fun c => decide (c < x.k)) &&
    (List.range vs.length).all fun i =>
      (List.range vs.length).all fun j =>
        (decide (i = j) || !decide (vs.getD i 0 = vs.getD j 0)) &&
        (!decide (cs.getD i 0 = cs.getD j 0) ||
          !Graph.adjBool x.graph (vs.getD i 0) (vs.getD j 0))

theorem isWellFormedBool_eq_true_iff (x : MulticoloredCliqueInstance) :
    isWellFormedBool x = true ↔ x.IsWellFormed := by
  rw [MulticoloredCliqueInstance.isWellFormed_iff]
  simp only [isWellFormedBool, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, List.all_eq_true, List.mem_range,
    Graph.adjBool_eq_false_iff]
  constructor
  · rintro ⟨⟨hlen, hlt⟩, hall⟩
    refine ⟨?_, hlen.symm, hlt, ?_⟩
    · rw [List.nodup_iff_injective_getElem]
      intro i j hij
      have h := (hall i.1 i.2 j.1 j.2).1
      have hvi : x.graph.vertices.getD i.1 0 = x.graph.vertices[i.1] := by
        simp [List.getD_eq_getElem?_getD]
      have hvj : x.graph.vertices.getD j.1 0 = x.graph.vertices[j.1] := by
        simp [List.getD_eq_getElem?_getD]
      rcases h with heq | hne
      · exact Fin.ext heq
      · exact (hne (by rw [hvi, hvj]; exact hij)).elim
    · intro i j hi hj hcol hadj
      have h := (hall i hi j hj).2
      have hci : x.colors.getD i 0 = x.colors[i]'(by omega) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < x.colors.length)]
      have hcj : x.colors.getD j 0 = x.colors[j]'(by omega) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : j < x.colors.length)]
      have hvi : x.graph.vertices.getD i 0 = x.graph.vertices[i] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      have hvj : x.graph.vertices.getD j 0 = x.graph.vertices[j] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      have hcol' : x.colors[i]'(by omega) = x.colors[j]'(by omega) := by
        simpa [List.getElem?_eq_getElem (by omega : i < x.colors.length),
          List.getElem?_eq_getElem (by omega : j < x.colors.length)] using hcol
      rcases h with hne | hna
      · exact hne (by rw [hci, hcj, hcol'])
      · exact hna (by rwa [hvi, hvj])
  · rintro ⟨hnd, hlen, hlt, hno⟩
    refine ⟨⟨hlen.symm, hlt⟩, fun i hi j hj => ⟨?_, ?_⟩⟩
    · by_cases hij : i = j
      · exact Or.inl hij
      · right
        have hvi : x.graph.vertices.getD i 0 = x.graph.vertices[i] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        have hvj : x.graph.vertices.getD j 0 = x.graph.vertices[j] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        rw [hvi, hvj]
        exact fun h => hij ((List.Nodup.getElem_inj_iff hnd).mp h)
    · by_cases hcol : x.colors.getD i 0 = x.colors.getD j 0
      · right
        have hi' : i < x.colors.length := by omega
        have hj' : j < x.colors.length := by omega
        have hcol' : x.colors[i]? = x.colors[j]? := by
          simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi',
            List.getElem?_eq_getElem hj'] using hcol
        have hvi : x.graph.vertices.getD i 0 = x.graph.vertices[i] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        have hvj : x.graph.vertices.getD j 0 = x.graph.vertices[j] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        rw [hvi, hvj]
        exact hno i j hi hj hcol'
      · exact Or.inl hcol

theorem computableInPolyTime_isWellFormedBool :
    ComputableInPolyTime isWellFormedBool encMulticoloredCliqueInstance encBool := by
  have hvs : ComputableInPolyTime (fun x : MulticoloredCliqueInstance => x.graph.vertices)
      encMulticoloredCliqueInstance (encList encNat) := by fun_prop
  have hcs : ComputableInPolyTime (fun x : MulticoloredCliqueInstance => x.colors)
      encMulticoloredCliqueInstance (encList encNat) :=
    encMulticoloredCliqueInstance_colors_polyTime ComputableInPolyTime.id'
  have hk : ComputableInPolyTime (fun x : MulticoloredCliqueInstance => x.k)
      encMulticoloredCliqueInstance encNat :=
    encMulticoloredCliqueInstance_k_polyTime ComputableInPolyTime.id'
  have hlen_v : ComputableInPolyTime (fun x : MulticoloredCliqueInstance => x.graph.vertices.length)
      encMulticoloredCliqueInstance encUnary := by fun_prop
  have hlen_c : ComputableInPolyTime (fun x : MulticoloredCliqueInstance => x.colors.length)
      encMulticoloredCliqueInstance encUnary := by fun_prop
  have hlen_eq : ComputableInPolyTime (fun x : MulticoloredCliqueInstance =>
      decide (x.graph.vertices.length = x.colors.length))
      encMulticoloredCliqueInstance encBool :=
    ComputableInPolyTime.decide_eq' hlen_v hlen_c
  have hall_lt : ComputableInPolyTime (fun x : MulticoloredCliqueInstance =>
      x.colors.all fun c => decide (c < x.k)) encMulticoloredCliqueInstance encBool := by
    refine ComputableInPolyTime.allWithInput hcs ?_
    exact ComputableInPolyTime.binary_lt' (by fun_prop) (hk.comp (by fun_prop))
  have hrange : ComputableInPolyTime (fun x : MulticoloredCliqueInstance =>
      List.range x.graph.vertices.length) encMulticoloredCliqueInstance (encList encUnary) :=
    ComputableInPolyTime.range.comp hlen_v
  have hnot_bool : ComputableInPolyTime (fun b : Bool => !b) encBool encBool :=
    ComputableInPolyTime.of_finite _
  have hall_pairs : ComputableInPolyTime (fun x : MulticoloredCliqueInstance =>
      (List.range x.graph.vertices.length).all fun i =>
        (List.range x.graph.vertices.length).all fun j =>
          (decide (i = j) || !decide (x.graph.vertices.getD i 0 = x.graph.vertices.getD j 0)) &&
          (!decide (x.colors.getD i 0 = x.colors.getD j 0) ||
            !Graph.adjBool x.graph (x.graph.vertices.getD i 0) (x.graph.vertices.getD j 0)))
      encMulticoloredCliqueInstance encBool := by
    refine ComputableInPolyTime.allWithInput hrange ?_
    refine ComputableInPolyTime.allWithInput (hrange.comp (by fun_prop)) ?_
    have hfst : ComputableInPolyTime
        (fun r : (MulticoloredCliqueInstance × ℕ) × ℕ => r.1.1)
        (encPair (encPair encMulticoloredCliqueInstance encUnary) encUnary)
        encMulticoloredCliqueInstance := by fun_prop
    have hi : ComputableInPolyTime
        (fun r : (MulticoloredCliqueInstance × ℕ) × ℕ => r.1.2)
        (encPair (encPair encMulticoloredCliqueInstance encUnary) encUnary) encUnary := by fun_prop
    have hj : ComputableInPolyTime
        (fun r : (MulticoloredCliqueInstance × ℕ) × ℕ => r.2)
        (encPair (encPair encMulticoloredCliqueInstance encUnary) encUnary) encUnary := by fun_prop
    have hvi : ComputableInPolyTime (fun r : (MulticoloredCliqueInstance × ℕ) × ℕ =>
        r.1.1.graph.vertices.getD r.1.2 0)
        (encPair (encPair encMulticoloredCliqueInstance encUnary) encUnary) encNat :=
      ComputableInPolyTime.listGetDWithInput (hvs.comp hfst) hi 0
    have hvj : ComputableInPolyTime (fun r : (MulticoloredCliqueInstance × ℕ) × ℕ =>
        r.1.1.graph.vertices.getD r.2 0)
        (encPair (encPair encMulticoloredCliqueInstance encUnary) encUnary) encNat :=
      ComputableInPolyTime.listGetDWithInput (hvs.comp hfst) hj 0
    have hci : ComputableInPolyTime (fun r : (MulticoloredCliqueInstance × ℕ) × ℕ =>
        r.1.1.colors.getD r.1.2 0)
        (encPair (encPair encMulticoloredCliqueInstance encUnary) encUnary) encNat :=
      ComputableInPolyTime.listGetDWithInput (hcs.comp hfst) hi 0
    have hcj : ComputableInPolyTime (fun r : (MulticoloredCliqueInstance × ℕ) × ℕ =>
        r.1.1.colors.getD r.2 0)
        (encPair (encPair encMulticoloredCliqueInstance encUnary) encUnary) encNat :=
      ComputableInPolyTime.listGetDWithInput (hcs.comp hfst) hj 0
    have hij := ComputableInPolyTime.decide_eq' hi hj
    have hveq := ComputableInPolyTime.decide_eq' hvi hvj
    have hceq := ComputableInPolyTime.decide_eq' hci hcj
    have hadj : ComputableInPolyTime (fun r : (MulticoloredCliqueInstance × ℕ) × ℕ =>
        Graph.adjBool r.1.1.graph (r.1.1.graph.vertices.getD r.1.2 0)
          (r.1.1.graph.vertices.getD r.2 0))
        (encPair (encPair encMulticoloredCliqueInstance encUnary) encUnary) encBool :=
      Graph.computableInPolyTime_adjBool_comp
        (encMulticoloredCliqueInstance_graph_polyTime hfst) hvi hvj
    exact ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.bool_or' hij (hnot_bool.comp' hveq))
      (ComputableInPolyTime.bool_or' (hnot_bool.comp' hceq) (hnot_bool.comp' hadj))
  exact ComputableInPolyTime.bool_and'
    (ComputableInPolyTime.bool_and' hlen_eq hall_lt) hall_pairs

/-- Add `p` fresh universal color classes (vertices `0, …, p - 1`, shifting existing vertices up by
`p`) to `x`. Preserves `IsWellFormed` and membership in `MulticoloredClique`. -/
def padUniversalMCC (x : MulticoloredCliqueInstance) (p : ℕ) : MulticoloredCliqueInstance :=
  let freshVerts := List.range p
  let oldVerts := x.graph.vertices.map (· + p)
  let freshColors := (List.range p).map (fun i => x.k + i)
  let crossEdges := freshVerts.flatMap fun u => oldVerts.map fun v => (u, v)
  let freshEdges :=
    freshVerts.flatMap fun u =>
      (freshVerts.filter fun v => decide (u ≠ v)).map fun v => (u, v)
  let oldEdges := x.graph.edges.map fun e => (e.1 + p, e.2 + p)
  ⟨⟨freshVerts ++ oldVerts, crossEdges ++ freshEdges ++ oldEdges⟩,
    x.k + p, freshColors ++ x.colors⟩

theorem padUniversalMCC_isWellFormed {x : MulticoloredCliqueInstance}
    (hx : x.IsWellFormed) (p : ℕ) : (padUniversalMCC x p).IsWellFormed := by
  rw [MulticoloredCliqueInstance.isWellFormed_iff] at hx ⊢
  set freshVerts := List.range p
  set oldVerts := x.graph.vertices.map (· + p)
  have hnd_old : oldVerts.Nodup := hx.1.map (fun _ _ h => Nat.add_right_cancel h)
  have hdisj : ∀ u ∈ freshVerts, u ∉ oldVerts := by
    intro u hu hv
    simp only [freshVerts, List.mem_range] at hu
    simp only [oldVerts, List.mem_map] at hv
    obtain ⟨_, _, rfl⟩ := hv
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact List.nodup_append.mpr ⟨List.nodup_range, hnd_old,
      fun u hu v hv heq => hdisj u hu (heq ▸ hv)⟩
  · simp [padUniversalMCC, hx.2.1]
  · intro c hc
    simp only [padUniversalMCC, List.mem_append, List.mem_map, List.mem_range] at hc ⊢
    rcases hc with ⟨i, hi, rfl⟩ | hc
    · omega
    · exact Nat.lt_of_lt_of_le (hx.2.2.1 c hc) (Nat.le_add_right _ _)
  · intro i j hi jlt hcol hadj
    simp only [padUniversalMCC, List.length_append, List.length_range, List.length_map] at hi jlt
    have hget_col : ∀ idx (hidx : idx < p + x.colors.length),
        (padUniversalMCC x p).colors[idx]? =
          if h : idx < p then some (x.k + idx) else x.colors[idx - p]? := by
      intro idx _
      simp only [padUniversalMCC, List.getElem?_append, List.length_map, List.length_range]
      split_ifs with h
      · simp [h]
      · rfl
    have hget_v : ∀ idx (hidx : idx < p + x.graph.vertices.length),
        (padUniversalMCC x p).graph.vertices[idx]'(by
          simp only [padUniversalMCC, List.length_append, List.length_range, List.length_map]
          exact hidx) =
          if h : idx < p then idx else x.graph.vertices[idx - p]'(by omega) + p := by
      intro idx _
      simp only [padUniversalMCC]
      split_ifs with h
      · rw [List.getElem_append_left (by simp [h])]; simp
      · rw [List.getElem_append_right (by simp; omega)]; simp
    rw [hget_col i (by rw [← hx.2.1] at hi; exact hi),
      hget_col j (by rw [← hx.2.1] at jlt; exact jlt)] at hcol
    rw [hget_v i hi, hget_v j jlt] at hadj
    split_ifs at hcol hadj with hi' hj'
    · simp only [Option.some.injEq] at hcol
      have : i = j := by omega
      subst this
      exact SimpleGraph.irrefl _ hadj
    · have hcj : j - p < x.colors.length := by rw [hx.2.1]; omega
      rw [List.getElem?_eq_getElem hcj] at hcol
      simp only [Option.some.injEq] at hcol
      have := hx.2.2.1 _ (List.getElem_mem hcj)
      omega
    · have hci : i - p < x.colors.length := by rw [hx.2.1]; omega
      rw [List.getElem?_eq_getElem hci] at hcol
      simp only [Option.some.injEq] at hcol
      have := hx.2.2.1 _ (List.getElem_mem hci)
      omega
    · rw [Graph.toSimpleGraph_adj] at hadj
      obtain ⟨hne, hmem⟩ := hadj
      have hold : ∀ a b, (a + p, b + p) ∈ (padUniversalMCC x p).graph.edges →
          (a, b) ∈ x.graph.edges := by
        intro a b hm
        simp only [padUniversalMCC, List.mem_append, List.mem_flatMap, List.mem_map,
          List.mem_filter, List.mem_range, decide_eq_true_eq, Prod.mk.injEq] at hm
        rcases hm with (⟨_, hu, _, _, heq, _⟩ | ⟨_, hu, _, _, heq, _⟩) | ⟨e, he, h1, h2⟩
        · omega
        · omega
        · have he1 : e.1 = a := by omega
          have he2 : e.2 = b := by omega
          have heq : e = (a, b) := Prod.ext he1 he2
          exact heq ▸ he
      have hi'' : i - p < x.graph.vertices.length := by omega
      have hj'' : j - p < x.graph.vertices.length := by omega
      have hadj_x : x.graph.toSimpleGraph.Adj
          x.graph.vertices[i - p] x.graph.vertices[j - p] := by
        rw [Graph.toSimpleGraph_adj]
        refine ⟨fun h => hne (by rw [h]), ?_⟩
        rcases hmem with h | h
        · exact Or.inl (hold _ _ h)
        · exact Or.inr (hold _ _ h)
      exact hx.2.2.2 (i - p) (j - p) hi'' hj'' hcol hadj_x

theorem padUniversalMCC_mem_iff {x : MulticoloredCliqueInstance}
    (hx : x.IsWellFormed) (p : ℕ) :
    padUniversalMCC x p ∈ MulticoloredClique ↔ x ∈ MulticoloredClique := by
  classical
  have hx' := (MulticoloredCliqueInstance.isWellFormed_iff x).mp hx
  set freshVerts := List.range p
  set oldVerts := x.graph.vertices.map (· + p)
  have hdisj : ∀ u ∈ freshVerts, u ∉ oldVerts := by
    intro u hu hv
    simp only [freshVerts, List.mem_range] at hu
    simp only [oldVerts, List.mem_map] at hv
    obtain ⟨_, _, rfl⟩ := hv
    omega
  have hfresh_adj : ∀ u ∈ freshVerts, ∀ v ∈ freshVerts ++ oldVerts, u ≠ v →
      (padUniversalMCC x p).graph.toSimpleGraph.Adj u v := by
    intro u hu v hv huv
    rw [Graph.toSimpleGraph_adj]
    refine ⟨huv, Or.inl ?_⟩
    simp only [padUniversalMCC, List.mem_append, List.mem_flatMap, List.mem_map,
      List.mem_filter, List.mem_range, decide_eq_true_eq, Prod.mk.injEq]
    rcases List.mem_append.mp hv with hvf | hvx
    · left; right; exact ⟨u, List.mem_range.mp hu, v, ⟨List.mem_range.mp hvf, huv⟩, rfl, rfl⟩
    · left; left
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hvx
      exact ⟨u, List.mem_range.mp hu, w + p, ⟨w, hw, rfl⟩, rfl, rfl⟩
  have hold_adj : ∀ a b, (padUniversalMCC x p).graph.toSimpleGraph.Adj (a + p) (b + p) ↔
      x.graph.toSimpleGraph.Adj a b := by
    intro a b
    simp only [Graph.toSimpleGraph_adj]
    have hnot : ∀ u v, ((u + p, v + p) ∈ (padUniversalMCC x p).graph.edges ↔
        (u, v) ∈ x.graph.edges) := by
      intro u v
      simp only [padUniversalMCC, List.mem_append, List.mem_flatMap, List.mem_map,
        List.mem_filter, List.mem_range, decide_eq_true_eq, Prod.mk.injEq]
      constructor
      · rintro ((⟨w, hw, _, _, heq, _⟩ | ⟨w, hw, _, _, heq, _⟩) | ⟨e, he, h1, h2⟩)
        · omega
        · omega
        · have : e = (u, v) := Prod.ext (by omega) (by omega)
          exact this ▸ he
      · intro h; exact Or.inr ⟨(u, v), h, rfl, rfl⟩
    rw [hnot a b, hnot b a]
    exact ⟨fun ⟨hne, h⟩ => ⟨fun heq => hne (by rw [heq]), h⟩,
      fun ⟨hne, h⟩ => ⟨fun heq => hne (Nat.add_right_cancel heq), h⟩⟩
  have hcard_fresh : freshVerts.toFinset.card = p := by
    rw [List.toFinset_card_of_nodup List.nodup_range]; simp
  rw [mem_MulticoloredClique_iff, mem_MulticoloredClique_iff, mem_Clique_iff_mk, mem_Clique_iff_mk]
  constructor
  · rintro ⟨_, S, hSV, hcl⟩
    let Sold : Finset ℕ := (S.filter (fun v => p ≤ v)).image (· - p)
    have hSold_mem : ∀ v ∈ Sold, v ∈ x.graph.vertices := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      have hw' := Finset.mem_filter.mp hw
      have hmem := List.mem_append.mp (hSV w hw'.1)
      rcases hmem with hlt | hold
      · have := List.mem_range.mp hlt; omega
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hold
        simpa using ha
    refine ⟨hx, Sold, hSold_mem, ?_, ?_⟩
    · intro u hu v hv huv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      have hab : a ≠ b := fun h => huv (by rw [h])
      have h1 : (a - p) + p = a := Nat.sub_add_cancel ha'.2
      have h2 : (b - p) + p = b := Nat.sub_add_cancel hb'.2
      exact (hold_adj (a - p) (b - p)).mp (by rw [h1, h2]; exact hcl.isClique ha'.1 hb'.1 hab)
    · have hcard_old : Sold.card = (S.filter (fun v => p ≤ v)).card := by
        refine Finset.card_image_of_injOn fun a ha b hb h => ?_
        have ha2 := (Finset.mem_filter.mp ha).2
        have hb2 := (Finset.mem_filter.mp hb).2
        omega
      have hsub : S \ S.filter (fun v => p ≤ v) ⊆ freshVerts.toFinset := by
        intro v hv
        rw [Finset.mem_sdiff, Finset.mem_filter] at hv
        have hnot : ¬ p ≤ v := fun h => hv.2 ⟨hv.1, h⟩
        exact List.mem_toFinset.mpr (List.mem_range.mpr (by omega))
      have hcard_diff : (S \ S.filter (fun v => p ≤ v)).card ≤ p :=
        (Finset.card_le_card hsub).trans (le_of_eq hcard_fresh)
      have hsum : (S.filter (fun v => p ≤ v)).card +
          (S \ S.filter (fun v => p ≤ v)).card = S.card := by
        rw [Nat.add_comm]
        exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
      have hScard : S.card = x.k + p := hcl.card_eq
      -- Since `Sold` is a clique in well-formed `x`, `Sold.card ≤ x.k`.
      have hle_k : Sold.card ≤ x.k := by
        let colOf : ℕ → ℕ := fun v => x.colors.getD (x.graph.vertices.idxOf v) 0
        have hinj : Set.InjOn colOf Sold := by
          intro u hu v hv hcol
          by_contra huv
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
          have ha' := Finset.mem_filter.mp ha
          have hb' := Finset.mem_filter.mp hb
          have hadj : x.graph.toSimpleGraph.Adj (a - p) (b - p) :=
            (hold_adj (a - p) (b - p)).mp (by
              rw [Nat.sub_add_cancel ha'.2, Nat.sub_add_cancel hb'.2]
              exact hcl.isClique ha'.1 hb'.1 (fun h => huv (by rw [h])))
          have hia := List.idxOf_lt_length_of_mem (hSold_mem _ hu)
          have hib := List.idxOf_lt_length_of_mem (hSold_mem _ hv)
          have hcia : x.colors.getD (x.graph.vertices.idxOf (a - p)) 0 =
              x.colors[x.graph.vertices.idxOf (a - p)]'(by rw [hx'.2.1]; exact hia) := by
            simp [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (by rw [hx'.2.1]; exact hia)]
          have hcib : x.colors.getD (x.graph.vertices.idxOf (b - p)) 0 =
              x.colors[x.graph.vertices.idxOf (b - p)]'(by rw [hx'.2.1]; exact hib) := by
            simp [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (by rw [hx'.2.1]; exact hib)]
          have hcol' : x.colors[x.graph.vertices.idxOf (a - p)]? =
              x.colors[x.graph.vertices.idxOf (b - p)]? := by
            rw [List.getElem?_eq_getElem (by rw [hx'.2.1]; exact hia),
              List.getElem?_eq_getElem (by rw [hx'.2.1]; exact hib), ← hcia, ← hcib]
            exact congrArg some hcol
          exact hx'.2.2.2 _ _ hia hib hcol'
            (by rwa [List.getElem_idxOf hia, List.getElem_idxOf hib])
        have hsub_range : Sold.image colOf ⊆ Finset.range x.k := by
          intro c hc
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
          have hiv : x.graph.vertices.idxOf v < x.colors.length := by
            rw [hx'.2.1]; exact List.idxOf_lt_length_of_mem (hSold_mem v hv)
          have hcv : colOf v = x.colors[x.graph.vertices.idxOf v] := by
            simp [colOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiv]
          rw [Finset.mem_range, hcv]
          exact hx'.2.2.1 _ (List.getElem_mem hiv)
        calc Sold.card = (Sold.image colOf).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.range x.k).card := Finset.card_le_card hsub_range
          _ = x.k := Finset.card_range x.k
      omega
  · rintro ⟨_, S, hSV, hcl⟩
    let S' : Finset ℕ := freshVerts.toFinset ∪ S.image (· + p)
    refine ⟨padUniversalMCC_isWellFormed hx p, S', ?_, ?_, ?_⟩
    · intro v hv
      rcases Finset.mem_union.mp hv with hvf | hvS
      · exact List.mem_append_left _ (List.mem_toFinset.mp hvf)
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hvS
        exact List.mem_append_right _ (List.mem_map.mpr ⟨w, hSV w hw, rfl⟩)
    · intro u hu v hv huv
      rcases Finset.mem_union.mp hu with huf | huS <;>
        rcases Finset.mem_union.mp hv with hvf | hvS
      · exact hfresh_adj u (List.mem_toFinset.mp huf) v
          (List.mem_append_left _ (List.mem_toFinset.mp hvf)) huv
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hvS
        exact hfresh_adj u (List.mem_toFinset.mp huf) (w + p)
          (List.mem_append_right _ (List.mem_map.mpr ⟨w, hSV w hw, rfl⟩)) huv
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp huS
        exact (hfresh_adj v (List.mem_toFinset.mp hvf) (w + p)
          (List.mem_append_right _ (List.mem_map.mpr ⟨w, hSV w hw, rfl⟩)) huv.symm).symm
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp huS
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hvS
        exact (hold_adj a b).mpr (hcl.isClique ha hb (fun h => huv (by rw [h])))
    · simp only [padUniversalMCC]
      rw [Finset.card_union_of_disjoint, hcard_fresh,
        Finset.card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h),
        hcl.card_eq, Nat.add_comm]
      rw [Finset.disjoint_left]
      intro v hvf hvS
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hvS
      exact hdisj (w + p) (List.mem_toFinset.mp hvf) (List.mem_map.mpr ⟨w, hSV w hw, rfl⟩)

/-- Computing `padUniversalMCC` is polynomial-time for unary `p`. -/
theorem computableInPolyTime_padUniversalMCC :
    ComputableInPolyTime (fun q : MulticoloredCliqueInstance × ℕ => padUniversalMCC q.1 q.2)
      (encPair encMulticoloredCliqueInstance encUnary) encMulticoloredCliqueInstance := by
  have hp_nat : ComputableInPolyTime (fun q : MulticoloredCliqueInstance × ℕ => q.2)
      (encPair encMulticoloredCliqueInstance encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hfresh : ComputableInPolyTime (fun q : MulticoloredCliqueInstance × ℕ => List.range q.2)
      (encPair encMulticoloredCliqueInstance encUnary) (encList encUnary) :=
    ComputableInPolyTime.range.comp (by fun_prop)
  have hfresh_nat : ComputableInPolyTime (fun q : MulticoloredCliqueInstance × ℕ => List.range q.2)
      (encPair encMulticoloredCliqueInstance encUnary) (encList encNat) := by
    have hmap := ComputableInPolyTime.map (α := ℕ) (β := ℕ)
      (encA := encUnary) (encB := encNat) ComputableInPolyTime.unary_to_binary
    exact (hmap.comp hfresh).of_enc_eq fun q => by simp
  have holdV : ComputableInPolyTime (fun q : MulticoloredCliqueInstance × ℕ =>
      q.1.graph.vertices.map (· + q.2))
      (encPair encMulticoloredCliqueInstance encUnary) (encList encNat) := by
    refine ComputableInPolyTime.mapWithInput (by fun_prop) ?_
    exact ComputableInPolyTime.binary_add' (by fun_prop) (hp_nat.comp (by fun_prop))
  have hfreshC : ComputableInPolyTime (fun q : MulticoloredCliqueInstance × ℕ =>
      (List.range q.2).map (fun i => q.1.k + i))
      (encPair encMulticoloredCliqueInstance encUnary) (encList encNat) := by
    refine ComputableInPolyTime.mapWithInput hfresh ?_
    have hk : ComputableInPolyTime (fun r : (MulticoloredCliqueInstance × ℕ) × ℕ => r.1.1.k)
        (encPair (encPair encMulticoloredCliqueInstance encUnary) encUnary) encNat := by fun_prop
    have hi : ComputableInPolyTime (fun r : (MulticoloredCliqueInstance × ℕ) × ℕ => r.2)
        (encPair (encPair encMulticoloredCliqueInstance encUnary) encUnary) encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
    exact ComputableInPolyTime.binary_add' hk hi
  have hcross : ComputableInPolyTime (fun q : MulticoloredCliqueInstance × ℕ =>
      (List.range q.2).flatMap fun u => (q.1.graph.vertices.map (· + q.2)).map fun v => (u, v))
      (encPair encMulticoloredCliqueInstance encUnary) (encList (encPair encNat encNat)) := by
    refine ComputableInPolyTime.flatMapWithInput hfresh_nat ?_
    refine ComputableInPolyTime.mapWithInput (holdV.comp (by fun_prop)) ?_
    fun_prop
  have hnot_bool : ComputableInPolyTime (fun b : Bool => !b) encBool encBool :=
    ComputableInPolyTime.of_finite _
  have hfreshE : ComputableInPolyTime (fun q : MulticoloredCliqueInstance × ℕ =>
      (List.range q.2).flatMap fun u =>
        ((List.range q.2).filter fun v => decide (u ≠ v)).map fun v => (u, v))
      (encPair encMulticoloredCliqueInstance encUnary) (encList (encPair encNat encNat)) := by
    refine ComputableInPolyTime.flatMapWithInput hfresh_nat ?_
    have hf : ComputableInPolyTime (fun r : (MulticoloredCliqueInstance × ℕ) × ℕ =>
        (List.range r.1.2).filter fun v => decide (r.2 ≠ v))
        (encPair (encPair encMulticoloredCliqueInstance encUnary) encNat) (encList encNat) := by
      refine ComputableInPolyTime.filterWithInput (hfresh_nat.comp (by fun_prop)) ?_
      have hr1 : ComputableInPolyTime
          (fun r : ((MulticoloredCliqueInstance × ℕ) × ℕ) × ℕ => r.1.2)
          (encPair (encPair (encPair encMulticoloredCliqueInstance encUnary) encNat) encNat)
          encNat := by fun_prop
      have hr2 : ComputableInPolyTime
          (fun r : ((MulticoloredCliqueInstance × ℕ) × ℕ) × ℕ => r.2)
          (encPair (encPair (encPair encMulticoloredCliqueInstance encUnary) encNat) encNat)
          encNat := by fun_prop
      exact (hnot_bool.comp (ComputableInPolyTime.decide_eq' hr1 hr2)).of_enc_eq
        fun r => by simp
    refine ComputableInPolyTime.mapWithInput hf ?_
    fun_prop
  have holdE : ComputableInPolyTime (fun q : MulticoloredCliqueInstance × ℕ =>
      q.1.graph.edges.map fun e => (e.1 + q.2, e.2 + q.2))
      (encPair encMulticoloredCliqueInstance encUnary) (encList (encPair encNat encNat)) := by
    refine ComputableInPolyTime.mapWithInput (by fun_prop) ?_
    have he1 : ComputableInPolyTime (fun r : (MulticoloredCliqueInstance × ℕ) × (ℕ × ℕ) =>
        r.2.1 + r.1.2)
        (encPair (encPair encMulticoloredCliqueInstance encUnary) (encPair encNat encNat)) encNat :=
      ComputableInPolyTime.binary_add' (by fun_prop) (hp_nat.comp (by fun_prop))
    have he2 : ComputableInPolyTime (fun r : (MulticoloredCliqueInstance × ℕ) × (ℕ × ℕ) =>
        r.2.2 + r.1.2)
        (encPair (encPair encMulticoloredCliqueInstance encUnary) (encPair encNat encNat)) encNat :=
      ComputableInPolyTime.binary_add' (by fun_prop) (hp_nat.comp (by fun_prop))
    exact he1.prod he2
  have hverts := ComputableInPolyTime.listAppend' hfresh_nat holdV
  have hedges1 := ComputableInPolyTime.listAppend' hcross hfreshE
  have hedges := ComputableInPolyTime.listAppend' hedges1 holdE
  have hgraph := encGraph_mk_polyTime hverts hedges
  have hq1 : ComputableInPolyTime (fun q : MulticoloredCliqueInstance × ℕ => q.1)
      (encPair encMulticoloredCliqueInstance encUnary) encMulticoloredCliqueInstance :=
    ComputableInPolyTime.fst _ _
  have hk := ComputableInPolyTime.binary_add' (encMulticoloredCliqueInstance_k_polyTime hq1) hp_nat
  have hcols := ComputableInPolyTime.listAppend' hfreshC
    (encMulticoloredCliqueInstance_colors_polyTime hq1)
  exact (encMulticoloredCliqueInstance_mk_polyTime hgraph hk hcols).of_enc_eq fun q =>
    congrArg encMulticoloredCliqueInstance (by dsimp only [padUniversalMCC])

/-! ### Specific Padding Reductions (`padOddMCC`, `padPosMCC`, `padAtLeast2MCC`) -/

end Cslib.Complexity
