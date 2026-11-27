/-
Copyright (c) 2026 The PanMath Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PanMath Contributors
-/
module

public import Cslib.Probability.PMF
public import Cslib.Probability.StatisticalDistance
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Planted Clique Distributions, Balanced Partitions, and $k$-BPC / $k$-HPC Conjectures

This module develops the formal complexity-theoretic and probabilistic infrastructure for the
$k$-part bipartite planted clique ($k$-$\mathrm{BPC}$) and $k$-partite $s$-uniform hypergraph
planted clique ($k$-$\mathrm{HPC}^s$) problems of Brennan and Bresler:

1. **Bipartite graphs, balanced partitions, and $k$-partite subsets**:
   `CslibFrontier.Computability.BipartiteGraph`, `CslibFrontier.Computability.BalancedPartition`,
   and
   `CslibFrontier.Computability.kPartiteSubsets`, including divisibility/cardinality bounds,
   constructive modular partitions (`CslibFrontier.Computability.modBalancedPartition`), and
   nonemptiness witnesses.
2. **Bipartite and hypergraph planted clique distributions**:
   `CslibFrontier.Computability.bipartiteGnpPMF`,
   `CslibFrontier.Computability.plantedBipartiteCliquePMF`,
   `CslibFrontier.Computability.hypergraphGnpPMF`,
   `CslibFrontier.Computability.plantedHypergraphCliquePMF` (together with their `.toMeasure` lifts
   parameterized by a `[MeasurableSpace...]` argument), built on
   `Cslib.Probability.PMF.uniformOfFintype` and `Cslib.Probability.PMF.uniformOfFinset`, with
   support characterizations exposing the planted cliques and exact equality to the null
   distribution in degenerate regimes (`k_m = 0` or `k < s`).
3. **Prefix-free instance encodings and randomized polynomial-time distinguishers**:
   `CslibFrontier.Computability.BPCInstance`, `CslibFrontier.Computability.HPCInstance`,
   `CslibFrontier.Computability.encodeBPCInstance`, `CslibFrontier.Computability.encodeHPCInstance`
   (both proved injective), and `CslibFrontier.Computability.RandPolyTimeDistinguisher`, backed by
   `Turing.MultiTapeTM.ComputableInPolyTime` on framed pair/bit-string encodings
   (`Turing.MultiTapeTM.encPair`, `encBits`, `encBool`) and `Cslib.Probability.StatisticalDistance`.
4. **Canonical open conjectures**: `CslibFrontier.Computability.kBPCConjecture` and
   `CslibFrontier.Computability.kHPCConjecture`, together with non-vacuity witness sequences
   (`CslibFrontier.Computability.nonempty_bpcParamSeq`,
   `CslibFrontier.Computability.nonempty_hpcParamSeq`)
   and unconditional indistinguishability when `k < s` eventually.

## Main definitions

- `CslibFrontier.Computability.UniformHypergraph`,
  `CslibFrontier.Computability.BipartiteGraph`,
  `CslibFrontier.Computability.BalancedPartition`,
  `CslibFrontier.Computability.modBalancedPartition`, `CslibFrontier.Computability.kPartiteSubsets`.
- `CslibFrontier.Computability.bipartiteGnpPMF`,
  `CslibFrontier.Computability.plantedBipartiteCliquePMF`,
  `CslibFrontier.Computability.bipartiteGnpMeasure`,
  `CslibFrontier.Computability.plantedBipartiteCliqueMeasure`,
  `CslibFrontier.Computability.hypergraphGnpPMF`,
  `CslibFrontier.Computability.plantedHypergraphCliquePMF`,
  `CslibFrontier.Computability.hypergraphGnpMeasure`,
  `CslibFrontier.Computability.plantedHypergraphCliqueMeasure`.
- `CslibFrontier.Computability.BPCInstance`, `CslibFrontier.Computability.encodeBPCInstance`,
  `CslibFrontier.Computability.encodeBPCInstanceEmb`, `CslibFrontier.Computability.HPCInstance`,
  `CslibFrontier.Computability.encodeHPCInstance`,
  `CslibFrontier.Computability.encodeHPCInstanceEmb`,
  `CslibFrontier.Computability.RandPolyTimeDistinguisher`.
- `CslibFrontier.Computability.BPCParamSeq`, `CslibFrontier.Computability.HPCParamSeq`,
  `CslibFrontier.Computability.kBPCConjecture`, `CslibFrontier.Computability.kHPCConjecture`.

## Main results

- `CslibFrontier.Computability.BalancedPartition.pos_of_pos`,
  `CslibFrontier.Computability.BalancedPartition.dvd`,
  `CslibFrontier.Computability.BalancedPartition.le_of_pos`,
  `CslibFrontier.Computability.card_eq_of_mem_kPartiteSubsets`,
  `CslibFrontier.Computability.kPartiteSubsets_nonempty`.
- `CslibFrontier.Computability.exists_complete_bipartite_of_mem_support_plantedBipartiteCliquePMF`,
  `CslibFrontier.Computability.plantedBipartiteCliquePMF_eq_of_km_zero`,
  `CslibFrontier.Computability.exists_clique_of_mem_support_plantedHypergraphCliquePMF`,
  `CslibFrontier.Computability.plantedHypergraphCliquePMF_eq_of_lt`.
- `CslibFrontier.Computability.encodeBPCInstance_injective`,
  `CslibFrontier.Computability.encodeHPCInstance_injective`,
  `CslibFrontier.Computability.RandPolyTimeDistinguisher.one_sub_dist_le_outputPMF_error_sum`.
- `CslibFrontier.Computability.nonempty_bpcParamSeq`,
  `CslibFrontier.Computability.nonempty_hpcParamSeq`,
  `CslibFrontier.Computability.kBPCConjecture_iff`,
  `CslibFrontier.Computability.kHPCConjecture_iff`,
  `CslibFrontier.Computability.no_distinguisher_hypergraph_of_eventually_lt`.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology Cslib.Probability.PMF

namespace CslibFrontier.Computability

/-- An `s`-uniform hypergraph on vertex type `V`: a finite set of `s`-element subsets. -/
@[ext]
structure UniformHypergraph (s : ℕ) (V : Type*) where
  /-- The finite set of hyperedges. -/
  edges : Finset (Finset V)
  /-- Every hyperedge has cardinality `s`. -/
  edge_card : ∀ e ∈ edges, e.card = s

/-! ### : Bipartite Graphs -/

section BipartiteGraphs

/-- A bipartite graph with left vertex set `V`, right vertex set `W`, and edge set
`edgeSet : Set (V × W)`. -/
@[ext]
structure BipartiteGraph (V : Type*) (W : Type*) where
  /-- Set of edges `(v, w)` between left vertices `V` and right vertices `W`. -/
  edgeSet : Set (V × W)

/-- Adjacency predicate of a `BipartiteGraph`. -/
def BipartiteGraph.Adj {V W : Type*} (G : BipartiteGraph V W) (a : V) (b : W) : Prop :=
  (a, b) ∈ G.edgeSet

/-- Construct a `BipartiteGraph` from an adjacency relation. -/
def BipartiteGraph.ofAdj {V W : Type*} (adj : V → W → Prop) : BipartiteGraph V W :=
  ⟨{p | adj p.1 p.2}⟩

@[simp]
theorem BipartiteGraph.ofAdj_adj {V W : Type*} (adj : V → W → Prop) (a : V) (b : W) :
    (BipartiteGraph.ofAdj adj).Adj a b ↔ adj a b := Iff.rfl

/-- Extensionality for `BipartiteGraph` in terms of `Adj`. -/
theorem BipartiteGraph.ext_adj {V W : Type*} {G₁ G₂ : BipartiteGraph V W}
    (h : ∀ a b, G₁.Adj a b ↔ G₂.Adj a b) : G₁ = G₂ := by
  ext ⟨a, b⟩
  exact h a b

end BipartiteGraphs

/-! ### : Balanced Partitions and $k$-Partite Subsets -/

section BalancedPartitions

/-- A balanced `k`-partition of `Fin n`: a part assignment `part : Fin n → Fin k` such that
every color class `part ⁻¹' {j}` has cardinality `n / k`, expressed multiplicatively as
`card * k = n`. -/
@[ext]
structure BalancedPartition (n k : ℕ) where
  /-- Assignment of each vertex `v : Fin n` to one of the `k` parts `Fin k`. -/
  part : Fin n → Fin k
  /-- Balance condition: every fiber has size `n / k` (`card * k = n`). -/
  card_eq : ∀ j : Fin k, (Finset.univ.filter (fun v ↦ part v = j)).card * k = n

namespace BalancedPartition

/-- A balanced `k`-partition of a nonempty vertex set `Fin n` (`0 < n`) forces `0 < k`. -/
theorem pos_of_pos {n k : ℕ} (E : BalancedPartition n k) (hn : 0 < n) : 0 < k :=
  Fin.pos (E.part ⟨0, hn⟩)

/-- Whenever `0 < n`, any balanced `k`-partition satisfies `k ∣ n`. -/
theorem dvd {n k : ℕ} (E : BalancedPartition n k) (hn : 0 < n) : k ∣ n :=
  ⟨(Finset.univ.filter (fun v ↦ E.part v = E.part ⟨0, hn⟩)).card,
    (E.card_eq (E.part ⟨0, hn⟩)).symm.trans (Nat.mul_comm _ _)⟩

/-- Whenever `0 < n`, every part fiber of a balanced partition is nonempty. -/
theorem partSize_pos {n k : ℕ} (E : BalancedPartition n k) (hn : 0 < n) (j : Fin k) :
    0 < (Finset.univ.filter (fun v ↦ E.part v = j)).card := by
  have hmul : (Finset.univ.filter (fun v ↦ E.part v = j)).card * k = n := E.card_eq j
  exact Nat.pos_of_ne_zero fun hz ↦ by rw [hz, zero_mul] at hmul; omega

/-- Whenever `0 < n`, the number of parts `k` of a balanced partition satisfies `k ≤ n`. -/
theorem le_of_pos {n k : ℕ} (E : BalancedPartition n k) (hn : 0 < n) : k ≤ n := by
  have hsum : ∑ j : Fin k, (Finset.univ.filter (fun v ↦ E.part v = j)).card = n := by
    rw [← Finset.card_biUnion]
    · have huniv : Finset.univ.biUnion (fun j : Fin k ↦
          Finset.univ.filter (fun v ↦ E.part v = j)) = (Finset.univ : Finset (Fin n)) := by
        ext v; simp
      rw [huniv, Finset.card_univ, Fintype.card_fin]
    · intro j₁ _ j₂ _ hne
      refine Finset.disjoint_left.mpr fun v hv₁ hv₂ ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
      exact hne (hv₁.symm.trans hv₂)
  calc
    k = ∑ _j : Fin k, 1 := by simp
    _ ≤ ∑ j : Fin k, (Finset.univ.filter (fun v ↦ E.part v = j)).card :=
        Finset.sum_le_sum fun j _ ↦ E.partSize_pos hn j
    _ = n := hsum

end BalancedPartition

/-- Constructive canonical balanced `k`-partition `v ↦ v % k` of `Fin n` whenever `0 < k` and
`k ∣ n`. -/
def modBalancedPartition {n k : ℕ} (hk : 0 < k) (hdvd : k ∣ n) : BalancedPartition n k where
  part v := ⟨v.1 % k, Nat.mod_lt v.1 hk⟩
  card_eq j := by
    let m := n / k
    have hmk : m * k = n := Nat.div_mul_cancel hdvd
    have hcard : (Finset.univ.filter (fun v : Fin n ↦
        (⟨v.1 % k, Nat.mod_lt v.1 hk⟩ : Fin k) = j)).card = m := by
      symm
      rw [← Finset.card_fin m]
      refine Finset.card_bij
        (fun (i : Fin m) _ ↦ (⟨i.1 * k + j.1, by nlinarith [i.2, j.2, hmk]⟩ : Fin n))
        ?_ ?_ ?_
      · intro i _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
        rw [Nat.mul_comm i.1 k, Nat.mul_add_mod, Nat.mod_eq_of_lt j.2]
      · intro i₁ _ i₂ _ h
        ext
        have h' : i₁.1 * k + j.1 = i₂.1 * k + j.1 := congrArg Fin.val h
        exact Nat.mul_right_cancel hk (by omega)
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff] at hv
        have hlt : v.1 / k < m := by
          have hdecomp : k * (v.1 / k) + v.1 % k = v.1 := Nat.div_add_mod v.1 k
          have hvlt : v.1 < m * k := hmk.symm ▸ v.2
          nlinarith [Nat.zero_le (v.1 % k)]
        refine ⟨⟨v.1 / k, hlt⟩, Finset.mem_univ _, ?_⟩
        ext
        dsimp only
        rw [Nat.mul_comm (v.1 / k) k, ← hv]
        exact Nat.div_add_mod v.1 k
    rw [hcard, hmk]

/-- The finite family of `k`-partite vertex subsets `S ⊆ Fin n` intersecting each part of `E`
in a single element: `∀ j : Fin k, (S.filter fun v ↦ E.part v = j).card = 1`. -/
def kPartiteSubsets {n k : ℕ} (E : BalancedPartition n k) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S ↦ ∀ j : Fin k, (S.filter fun v ↦ E.part v = j).card = 1

theorem mem_kPartiteSubsets_iff {n k : ℕ} (E : BalancedPartition n k) (S : Finset (Fin n)) :
    S ∈ kPartiteSubsets E ↔ ∀ j : Fin k, (S.filter fun v ↦ E.part v = j).card = 1 := by
  simp [kPartiteSubsets]

/-- Every `k`-partite subset `S ∈ kPartiteSubsets E` has cardinality `k`. -/
theorem card_eq_of_mem_kPartiteSubsets {n k : ℕ} {E : BalancedPartition n k} {S : Finset (Fin n)}
    (hS : S ∈ kPartiteSubsets E) : S.card = k := by
  have hdecomp : S = Finset.univ.biUnion fun j : Fin k ↦ S.filter fun v ↦ E.part v = j := by
    ext v
    simp
  conv_lhs => rw [hdecomp]
  rw [Finset.card_biUnion]
  · simp [(mem_kPartiteSubsets_iff E S).mp hS]
  · intro j₁ _ j₂ _ hne
    refine Finset.disjoint_left.mpr fun v hv₁ hv₂ ↦ ?_
    simp only [Finset.mem_filter] at hv₁ hv₂
    exact hne (hv₁.2.symm.trans hv₂.2)

/-- Whenever `0 < n`, `kPartiteSubsets E` is nonempty (constructed explicitly from the minimal
element of each color class). -/
theorem kPartiteSubsets_nonempty {n k : ℕ} (E : BalancedPartition n k) (hn : 0 < n) :
    (kPartiteSubsets E).Nonempty := by
  let rep : Fin k → Fin n := fun j ↦
    (Finset.univ.filter (fun v ↦ E.part v = j)).min'
      (Finset.card_pos.mp (E.partSize_pos hn j))
  have hrep_part : ∀ j : Fin k, E.part (rep j) = j := by
    intro j
    simpa [rep] using (Finset.mem_filter.mp (Finset.min'_mem
      (Finset.univ.filter (fun v ↦ E.part v = j))
      (Finset.card_pos.mp (E.partSize_pos hn j)))).2
  refine ⟨Finset.univ.image rep, (mem_kPartiteSubsets_iff E _).mpr fun j ↦ ?_⟩
  have hfilt : (Finset.univ.image rep).filter (fun v ↦ E.part v = j) = {rep j} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨j', hj'⟩, hv⟩
      subst hj'
      rw [hrep_part j'] at hv
      subst hv
      rfl
    · rintro rfl
      exact ⟨⟨j, rfl⟩, hrep_part j⟩
  rw [hfilt, Finset.card_singleton]

end BalancedPartitions

/-! ### : Uniform Finite PMFs and Planted Clique Distributions -/

section UniformAndPlantedDistributions

/-- The bipartite Erdős–Rényi random graph distribution $\mathcal{G}(m, n, 1/2)$ on
`BipartiteGraph (Fin m) (Fin n)`, including each edge `(a, b)` independently with probability
`1/2`. -/
noncomputable def bipartiteGnpPMF (m n : ℕ) : PMF (BipartiteGraph (Fin m) (Fin n)) :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin m × Fin n → Bool)).map fun f ↦
    BipartiteGraph.ofAdj fun a b ↦ f (a, b) = true

/-- Associated Borel/measurable-space measure for `bipartiteGnpPMF`. -/
noncomputable def bipartiteGnpMeasure (m n : ℕ)
    [MeasurableSpace (BipartiteGraph (Fin m) (Fin n))] :
    Measure (BipartiteGraph (Fin m) (Fin n)) :=
  (bipartiteGnpPMF m n).toMeasure

/-- The $k$-part bipartite planted clique distribution
$k\text{-}\mathrm{BPC}_E(m, n, k_m, k_n, 1/2)$: samples $G_0 \sim \mathcal{G}(m, n, 1/2)$,
a uniform $k_m$-subset $S \subseteq \mathrm{Fin}\,m$, a uniform $k_n$-partite subset
$T \in \mathcal{P}_E$, and plants all edges between $S$ and $T$. -/
noncomputable def plantedBipartiteCliquePMF (m n k_m k_n : ℕ) (hm : k_m ≤ m) (hn : 0 < n)
    (E : BalancedPartition n k_n) : PMF (BipartiteGraph (Fin m) (Fin n)) :=
  (Cslib.Probability.PMF.uniformOfFinset
      (Finset.univ.powersetCard k_m : Finset (Finset (Fin m)))
      (Finset.powersetCard_nonempty.mpr (by simpa using hm))).bind fun S ↦
    (Cslib.Probability.PMF.uniformOfFinset (kPartiteSubsets E)
      (kPartiteSubsets_nonempty E hn)).bind fun T ↦
      (bipartiteGnpPMF m n).map fun G ↦
        BipartiteGraph.ofAdj fun a b ↦ G.Adj a b ∨ (a ∈ S ∧ b ∈ T)

/-- Associated measure for `plantedBipartiteCliquePMF`. -/
noncomputable def plantedBipartiteCliqueMeasure (m n k_m k_n : ℕ) (hm : k_m ≤ m) (hn : 0 < n)
    (E : BalancedPartition n k_n) [MeasurableSpace (BipartiteGraph (Fin m) (Fin n))] :
    Measure (BipartiteGraph (Fin m) (Fin n)) :=
  (plantedBipartiteCliquePMF m n k_m k_n hm hn E).toMeasure

/-- Every bipartite graph in the support of `plantedBipartiteCliquePMF` contains a complete
bipartite subgraph `S × T` with `S.card = k_m` and `T ∈ kPartiteSubsets E`. -/
theorem exists_complete_bipartite_of_mem_support_plantedBipartiteCliquePMF {m n k_m k_n : ℕ}
    {hm : k_m ≤ m} {hn : 0 < n} {E : BalancedPartition n k_n}
    {G : BipartiteGraph (Fin m) (Fin n)}
    (hG : G ∈ (plantedBipartiteCliquePMF m n k_m k_n hm hn E).support) :
    ∃ (S : Finset (Fin m)) (T : Finset (Fin n)),
      S.card = k_m ∧ T ∈ kPartiteSubsets E ∧ ∀ a ∈ S, ∀ b ∈ T, G.Adj a b := by
  simp only [plantedBipartiteCliquePMF, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
    Cslib.Probability.PMF.mem_support_uniformOfFinset_iff, Set.mem_image,
    exists_prop] at hG
  rcases hG with ⟨S, hS, T, hT, G₀, _, rfl⟩
  rw [Finset.mem_powersetCard] at hS
  exact ⟨S, T, hS.2, hT, fun a ha b hb ↦ Or.inr ⟨ha, hb⟩⟩

private lemma pmf_bind_congr_on_support {α β : Type*} {p : PMF α} {f g : α → PMF β}
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext y
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun a ↦ ?_
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ((PMF.mem_support_iff p a).mpr ha)]

/-- When `k_m = 0`, no edges are planted so `plantedBipartiteCliquePMF` coincides with
`bipartiteGnpPMF`. -/
theorem plantedBipartiteCliquePMF_eq_of_km_zero (m n k_n : ℕ) (hn : 0 < n)
    (E : BalancedPartition n k_n) :
    plantedBipartiteCliquePMF m n 0 k_n (Nat.zero_le m) hn E = bipartiteGnpPMF m n := by
  have hmap : ∀ (S : Finset (Fin m)), S ∈ (Finset.univ.powersetCard 0 : Finset (Finset (Fin m))) →
      ∀ (T : Finset (Fin n)), ((bipartiteGnpPMF m n).map fun G ↦
        BipartiteGraph.ofAdj fun a b ↦ G.Adj a b ∨ (a ∈ S ∧ b ∈ T)) = bipartiteGnpPMF m n := by
    intro S hS T
    have hSe : S = ∅ := Finset.card_eq_zero.mp (Finset.mem_powersetCard.mp hS).2
    subst hSe
    have hfun : (fun G : BipartiteGraph (Fin m) (Fin n) ↦
        BipartiteGraph.ofAdj fun a b ↦ G.Adj a b ∨ (a ∈ (∅ : Finset (Fin m)) ∧ b ∈ T)) = id := by
      funext G
      exact BipartiteGraph.ext_adj fun a b ↦ by simp
    rw [hfun, PMF.map_id]
  simp only [plantedBipartiteCliquePMF]
  have hinner : ∀ S ∈ (Finset.univ.powersetCard 0 : Finset (Finset (Fin m))),
      ((Cslib.Probability.PMF.uniformOfFinset (kPartiteSubsets E)
        (kPartiteSubsets_nonempty E hn)).bind fun T ↦
        (bipartiteGnpPMF m n).map fun G ↦
          BipartiteGraph.ofAdj fun a b ↦ G.Adj a b ∨ (a ∈ S ∧ b ∈ T)) =
        bipartiteGnpPMF m n := fun S hS ↦ by
    rw [pmf_bind_congr_on_support (g := fun _ ↦ bipartiteGnpPMF m n) fun T _ ↦ hmap S hS T,
      PMF.bind_const]
  rw [pmf_bind_congr_on_support (g := fun _ ↦ bipartiteGnpPMF m n) fun S hS ↦ by
    rw [Cslib.Probability.PMF.mem_support_uniformOfFinset_iff] at hS
    exact hinner S hS, PMF.bind_const]

/-- The $s$-uniform Erdős–Rényi hypergraph distribution $\mathcal{G}^s(n, 1/2)$ on
`UniformHypergraph s (Fin n)`, including each `s`-element subset of `Fin n` independently
with probability `1/2`. -/
noncomputable def hypergraphGnpPMF (s n : ℕ) : PMF (UniformHypergraph s (Fin n)) :=
  (Cslib.Probability.PMF.uniformOfFintype (Finset (Fin n) → Bool)).map fun f ↦
    ⟨(Finset.univ.powersetCard s).filter (fun e ↦ f e = true),
      fun _ he ↦ (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2⟩

/-- Associated measure for `hypergraphGnpPMF`. -/
noncomputable def hypergraphGnpMeasure (s n : ℕ)
    [MeasurableSpace (UniformHypergraph s (Fin n))] :
    Measure (UniformHypergraph s (Fin n)) :=
  (hypergraphGnpPMF s n).toMeasure

/-- The $k$-partite hypergraph planted clique distribution $k\text{-}\mathrm{HPC}^s_E(n, k, 1/2)$:
samples $H_0 \sim \mathcal{G}^s(n, 1/2)$ and a uniform $k$-partite subset $S \in \mathcal{P}_E$,
and plants all $\binom{k}{s}$ hyperedges inside $S$. -/
noncomputable def plantedHypergraphCliquePMF (s n k : ℕ) (hn : 0 < n)
    (E : BalancedPartition n k) : PMF (UniformHypergraph s (Fin n)) :=
  (Cslib.Probability.PMF.uniformOfFinset (kPartiteSubsets E)
      (kPartiteSubsets_nonempty E hn)).bind fun S ↦
    (hypergraphGnpPMF s n).map fun H ↦
      ⟨H.edges ∪ S.powersetCard s, fun e he ↦ by
        rcases Finset.mem_union.mp he with h1 | h2
        · exact H.edge_card e h1
        · exact (Finset.mem_powersetCard.mp h2).2⟩

/-- Associated measure for `plantedHypergraphCliquePMF`. -/
noncomputable def plantedHypergraphCliqueMeasure (s n k : ℕ) (hn : 0 < n)
    (E : BalancedPartition n k) [MeasurableSpace (UniformHypergraph s (Fin n))] :
    Measure (UniformHypergraph s (Fin n)) :=
  (plantedHypergraphCliquePMF s n k hn E).toMeasure

/-- Every `s`-uniform hypergraph in the support of `plantedHypergraphCliquePMF` contains a
planted $s$-uniform clique on some `S ∈ kPartiteSubsets E`. -/
theorem exists_clique_of_mem_support_plantedHypergraphCliquePMF {s n k : ℕ} {hn : 0 < n}
    {E : BalancedPartition n k} {H : UniformHypergraph s (Fin n)}
    (hH : H ∈ (plantedHypergraphCliquePMF s n k hn E).support) :
    ∃ S ∈ kPartiteSubsets E, S.powersetCard s ⊆ H.edges := by
  simp only [plantedHypergraphCliquePMF, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
    Cslib.Probability.PMF.mem_support_uniformOfFinset_iff, Set.mem_image,
    exists_prop] at hH
  rcases hH with ⟨S, hS, H₀, _, rfl⟩
  exact ⟨S, hS, Finset.subset_union_right⟩

/-- When `k < s`, every `S ∈ kPartiteSubsets E` has `S.card = k < s`, so no hyperedges are
planted and `plantedHypergraphCliquePMF` coincides with `hypergraphGnpPMF`. -/
theorem plantedHypergraphCliquePMF_eq_of_lt (s n k : ℕ) (hn : 0 < n) (hks : k < s)
    (E : BalancedPartition n k) :
    plantedHypergraphCliquePMF s n k hn E = hypergraphGnpPMF s n := by
  simp only [plantedHypergraphCliquePMF]
  rw [pmf_bind_congr_on_support (g := fun _ ↦ hypergraphGnpPMF s n) fun S hS ↦ by
    rw [Cslib.Probability.PMF.mem_support_uniformOfFinset_iff] at hS
    have hcard : S.card < s := (card_eq_of_mem_kPartiteSubsets hS).trans_lt hks
    have hemp : S.powersetCard s = ∅ := Finset.powersetCard_eq_empty.mpr hcard
    have hid : (fun H : UniformHypergraph s (Fin n) ↦
        (⟨H.edges ∪ S.powersetCard s, fun e he ↦ by
          rcases Finset.mem_union.mp he with h1 | h2
          · exact H.edge_card e h1
          · exact (Finset.mem_powersetCard.mp h2).2⟩ :
            UniformHypergraph s (Fin n))) = id := by
      funext H
      exact UniformHypergraph.ext (Finset.ext fun e ↦ by simp [hemp])
    rw [hid, PMF.map_id], PMF.bind_const]

end UniformAndPlantedDistributions

/-! ### : Prefix-Free Instance Encodings and Randomized Poly-Time Distinguishers -/

section EncodingsAndDistinguishers

/-- Prefix-free unary bit-string encoding of a natural number: `k` `true` bits followed by a
terminating `false` bit. -/
def encodeUnaryPrefix (k : ℕ) : List Bool := List.replicate k true ++ [false]

@[simp, grind =]
lemma length_encodeUnaryPrefix (k : ℕ) : (encodeUnaryPrefix k).length = k + 1 := by
  simp [encodeUnaryPrefix]

lemma encodeUnaryPrefix_append_inj {a b : ℕ} {r₁ r₂ : List Bool}
    (h : encodeUnaryPrefix a ++ r₁ = encodeUnaryPrefix b ++ r₂) : a = b ∧ r₁ = r₂ := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa [encodeUnaryPrefix] using h
    | succ b => simp [encodeUnaryPrefix, List.replicate_succ] at h
  | succ a ih =>
    cases b with
    | zero => simp [encodeUnaryPrefix, List.replicate_succ] at h
    | succ b =>
      simp only [encodeUnaryPrefix, List.replicate_succ, List.cons_append,
        List.cons.injEq, true_and] at h
      obtain ⟨hab, hr⟩ := ih h
      exact ⟨congrArg Nat.succ hab, hr⟩

private lemma encodeUnaryPrefix_list_append_inj {l₁ l₂ : List ℕ} (hlen : l₁.length = l₂.length)
    {r₁ r₂ : List Bool}
    (h : l₁.flatMap encodeUnaryPrefix ++ r₁ = l₂.flatMap encodeUnaryPrefix ++ r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact ⟨rfl, by simpa using h⟩
    | cons _ _ => simp at hlen
  | cons a as ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨hab, hrest⟩ := encodeUnaryPrefix_append_inj h
      obtain ⟨has, hr⟩ := ih hlen hrest
      exact ⟨congrArg₂ List.cons hab has, hr⟩

private lemma eq_on_of_map_eq {α β : Type*} {l : List α} {f g : α → β}
    (h : l.map f = l.map g) : ∀ x ∈ l, f x = g x := by
  induction l with
  | nil => intro x hx; cases hx
  | cons a as ih =>
    intro x hx
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact h.1
    · exact ih h.2 x hx'

/-- Canonical exhaustive enumeration of all ordered `s`-tuples `Fin s → Fin n`. -/
def allTuples : (s n : ℕ) → List (Fin s → Fin n)
  | 0, _ => [Fin.elim0]
  | s + 1, n => (List.finRange n).flatMap fun a ↦
      (allTuples s n).map fun f ↦ Fin.cons a f

@[simp, grind =]
theorem length_allTuples (s n : ℕ) : (allTuples s n).length = n ^ s := by
  induction s with
  | zero => simp [allTuples]
  | succ s ih =>
    simp [allTuples, List.length_flatMap, ih, List.sum_replicate, Nat.pow_succ']

theorem mem_allTuples (s n : ℕ) (f : Fin s → Fin n) : f ∈ allTuples s n := by
  induction s with
  | zero =>
    have hf : f = Fin.elim0 := Subsingleton.elim _ _
    simp [allTuples, hf]
  | succ s ih =>
    have hf : Fin.cons (f 0) (fun j : Fin s ↦ f j.succ) = f := by
      ext i
      cases i using Fin.cases with
      | zero => simp
      | succ j => simp
    rw [← hf]
    simp only [allTuples, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
    exact ⟨f 0, fun j ↦ f j.succ, ih _, rfl⟩

/-- Canonical instance carrier for the $k$-part bipartite planted clique ($k$-$\mathrm{BPC}$)
distinguishing problem: dimensions `(m, n)`, clique sizes `(km, kn)`, released balanced
right-part partition `part`, and observed bipartite graph `graph`. -/
structure BPCInstance where
  /-- Cardinality of the left vertex part. -/
  m : ℕ
  /-- Cardinality of the right vertex part. -/
  n : ℕ
  /-- Planted clique cardinality on the left part. -/
  km : ℕ
  /-- Number of parts (and planted clique cardinality) on the right part. -/
  kn : ℕ
  /-- Balanced `kn`-partition of the right vertex part `Fin n`. -/
  part : BalancedPartition n kn
  /-- Observed bipartite graph on `(Fin m, Fin n)`. -/
  graph : BipartiteGraph (Fin m) (Fin n)

/-- Row-major Boolean adjacency bit-string of a `BipartiteGraph (Fin m) (Fin n)`. -/
noncomputable def encodeBipartiteAdj (m n : ℕ) (G : BipartiteGraph (Fin m) (Fin n)) :
    List Bool :=
  (List.finRange m).flatMap fun i ↦
    (List.finRange n).map fun j ↦
      @decide (G.Adj i j) (Classical.propDecidable _)

private lemma length_encodeBipartiteAdj (m n : ℕ) (G : BipartiteGraph (Fin m) (Fin n)) :
    (encodeBipartiteAdj m n G).length = m * n := by
  unfold encodeBipartiteAdj
  rw [List.length_flatMap]
  have hmap : ((List.finRange m).map fun i ↦
      ((List.finRange n).map fun j ↦
        @decide (G.Adj i j) (Classical.propDecidable _)).length) = List.replicate m n := by
    refine List.ext_getElem (by simp) fun k hk₁ hk₂ ↦ by simp
  rw [hmap, List.sum_replicate, smul_eq_mul]

private lemma encodeBipartiteAdj_getElem (m n : ℕ) (G : BipartiteGraph (Fin m) (Fin n))
    (i : Fin m) (j : Fin n) :
    (encodeBipartiteAdj m n G)[i.1 * n + j.1]'(by
        rw [length_encodeBipartiteAdj]; nlinarith [i.2, j.2]) =
      @decide (G.Adj i j) (Classical.propDecidable _) := by
  let f : Fin m → List Bool := fun a ↦
    (List.finRange n).map fun b ↦ @decide (G.Adj a b) (Classical.propDecidable _)
  have hlen : ∀ a, (f a).length = n := fun _ ↦ by simp [f]
  have haux : ∀ (L : List (Fin m)) (k : ℕ) (hk : k < L.length),
      (L.flatMap f)[k * n + j.1]'(by
          rw [List.length_flatMap, List.map_congr_left (fun a _ ↦ hlen a), List.map_const',
            List.sum_replicate, smul_eq_mul]
          nlinarith [j.2]) =
        (f (L[k]'hk))[j.1]'(by rw [hlen]; exact j.2) := by
    intro L
    induction L with
    | nil => intro _ hk; cases hk
    | cons a as ih =>
      intro k hk
      cases k with
      | zero =>
        simp only [List.flatMap_cons, zero_mul, zero_add, List.getElem_cons_zero]
        rw [List.getElem_append_left (by rw [hlen]; exact j.2)]
      | succ k =>
        simp only [List.flatMap_cons, List.getElem_cons_succ]
        rw [List.getElem_append_right (by rw [hlen]; nlinarith)]
        have hsub : (k + 1) * n + j.1 - (f a).length = k * n + j.1 := by
          rw [hlen, Nat.add_one_mul]; omega
        simp only [hsub]
        exact ih k (Nat.lt_of_succ_lt_succ hk)
  have hi : (List.finRange m)[i.1]'(by simp) = i := Fin.ext (by simp)
  have hj : (List.finRange n)[j.1]'(by simp) = j := Fin.ext (by simp)
  have h1 := haux (List.finRange m) i.1 (by simp)
  have h2a : ∀ x₁ y₁ x₂ y₂, x₁ = y₁ → x₂ = y₂ →
      @decide (G.Adj x₁ x₂) (Classical.propDecidable _) =
        @decide (G.Adj y₁ y₂) (Classical.propDecidable _) := by
    rintro _ _ _ _ rfl rfl; rfl
  have h2 : (f ((List.finRange m)[i.1]'(by simp)))[j.1]'(by rw [hlen]; exact j.2) =
      @decide (G.Adj i j) (Classical.propDecidable _) := by
    dsimp only [f]
    rw [List.getElem_map]
    exact h2a _ _ _ _ hi hj
  exact h1.trans h2

/-- Canonical bit-string encoding of a `BPCInstance`, concatenating prefix-free unary codes for
`(m, n, km, kn)` and the partition table with the row-major `m × n` adjacency bit-string. -/
noncomputable def encodeBPCInstance (I : BPCInstance) : List Bool :=
  encodeUnaryPrefix I.m ++ encodeUnaryPrefix I.n ++ encodeUnaryPrefix I.km ++
    encodeUnaryPrefix I.kn ++
    ((List.finRange I.n).map fun i ↦ (I.part.part i).1).flatMap encodeUnaryPrefix ++
    encodeBipartiteAdj I.m I.n I.graph

/-- `encodeBPCInstance` is injective on `BPCInstance`. -/
theorem encodeBPCInstance_injective : Function.Injective encodeBPCInstance := by
  rintro ⟨m₁, n₁, km₁, kn₁, E₁, G₁⟩ ⟨m₂, n₂, km₂, kn₂, E₂, G₂⟩ h
  simp only [encodeBPCInstance, List.append_assoc] at h
  rcases encodeUnaryPrefix_append_inj h with ⟨hm, h1⟩
  rcases encodeUnaryPrefix_append_inj h1 with ⟨hn, h2⟩
  rcases encodeUnaryPrefix_append_inj h2 with ⟨hkm, h3⟩
  rcases encodeUnaryPrefix_append_inj h3 with ⟨hkn, h4⟩
  cases hm; cases hn; cases hkm; cases hkn
  have hlen : ((List.finRange n₁).map fun i ↦ (E₁.part i).1).length =
      ((List.finRange n₁).map fun i ↦ (E₂.part i).1).length := by simp
  obtain ⟨hlist, hadj⟩ := encodeUnaryPrefix_list_append_inj hlen h4
  have hE : E₁ = E₂ := by
    ext v
    have hv := congrArg (fun l ↦ l[v.1]?) hlist
    simpa using hv
  cases hE
  have hG : G₁ = G₂ := by
    refine BipartiteGraph.ext_adj fun i j ↦ ?_
    have hidx : i.1 * n₁ + j.1 < (encodeBipartiteAdj m₁ n₁ G₁).length := by
      rw [length_encodeBipartiteAdj]; nlinarith [i.2, j.2]
    have hidx₂ : i.1 * n₁ + j.1 < (encodeBipartiteAdj m₁ n₁ G₂).length := by
      rw [length_encodeBipartiteAdj]; nlinarith [i.2, j.2]
    have hget : (encodeBipartiteAdj m₁ n₁ G₁)[i.1 * n₁ + j.1]? =
        (encodeBipartiteAdj m₁ n₁ G₂)[i.1 * n₁ + j.1]? :=
      congrArg (·[i.1 * n₁ + j.1]?) hadj
    rw [List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem hidx₂, Option.some.injEq,
      encodeBipartiteAdj_getElem, encodeBipartiteAdj_getElem] at hget
    have heq : (@decide (G₁.Adj i j) (Classical.propDecidable _) = true) =
        (@decide (G₂.Adj i j) (Classical.propDecidable _) = true) := congrArg (· = true) hget
    rw [@decide_eq_true_eq _ (Classical.propDecidable _),
      @decide_eq_true_eq _ (Classical.propDecidable _)] at heq
    exact eq_iff_iff.mp heq
  cases hG
  rfl

/-- Canonical embedding `BPCInstance ↪ List Bool` from `encodeBPCInstance`. -/
noncomputable def encodeBPCInstanceEmb : BPCInstance ↪ List Bool :=
  ⟨encodeBPCInstance, encodeBPCInstance_injective⟩

/-- Canonical instance carrier for the $k$-partite hypergraph planted clique ($k$-$\mathrm{HPC}^s$)
distinguishing problem. -/
structure HPCInstance where
  /-- Hyperedge uniformity `s`. -/
  s : ℕ
  /-- Number of vertices `n`. -/
  n : ℕ
  /-- Number of parts (and planted clique cardinality) `k`. -/
  k : ℕ
  /-- Balanced `k`-partition of `Fin n`. -/
  part : BalancedPartition n k
  /-- Observed `s`-uniform hypergraph on `Fin n`. -/
  hypergraph : UniformHypergraph s (Fin n)

/-- Ordered-tuple Boolean edge-indicator bit-string of `UniformHypergraph s (Fin n)`. -/
noncomputable def encodeHypergraphEdges (s n : ℕ) (H : UniformHypergraph s (Fin n)) :
    List Bool :=
  (allTuples s n).map fun f ↦
    @decide (Finset.univ.image f ∈ H.edges) (Classical.propDecidable _)

/-- Canonical bit-string encoding of an `HPCInstance`, concatenating prefix-free unary codes for
`(s, n, k)` and the partition table with the `n ^ s` ordered-tuple edge indicators. -/
noncomputable def encodeHPCInstance (I : HPCInstance) : List Bool :=
  encodeUnaryPrefix I.s ++ encodeUnaryPrefix I.n ++ encodeUnaryPrefix I.k ++
    ((List.finRange I.n).map fun i ↦ (I.part.part i).1).flatMap encodeUnaryPrefix ++
    encodeHypergraphEdges I.s I.n I.hypergraph

/-- `encodeHPCInstance` is injective on `HPCInstance`. -/
theorem encodeHPCInstance_injective : Function.Injective encodeHPCInstance := by
  rintro ⟨s₁, n₁, k₁, E₁, H₁⟩ ⟨s₂, n₂, k₂, E₂, H₂⟩ h
  simp only [encodeHPCInstance, List.append_assoc] at h
  rcases encodeUnaryPrefix_append_inj h with ⟨hs, h1⟩
  rcases encodeUnaryPrefix_append_inj h1 with ⟨hn, h2⟩
  rcases encodeUnaryPrefix_append_inj h2 with ⟨hk, h3⟩
  cases hs; cases hn; cases hk
  have hlen : ((List.finRange n₁).map fun i ↦ (E₁.part i).1).length =
      ((List.finRange n₁).map fun i ↦ (E₂.part i).1).length := by simp
  obtain ⟨hlist, hedges⟩ := encodeUnaryPrefix_list_append_inj hlen h3
  have hE : E₁ = E₂ := by
    ext v
    have hv := congrArg (fun l ↦ l[v.1]?) hlist
    simpa using hv
  cases hE
  have hmem : ∀ e : Finset (Fin n₁), e.card = s₁ → (e ∈ H₁.edges ↔ e ∈ H₂.edges) := by
    intro e he
    let φ := (e.equivFinOfCardEq he).symm
    let f : Fin s₁ → Fin n₁ := fun i ↦ (φ i).1
    have himg : Finset.univ.image f = e := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, f]
      constructor
      · rintro ⟨i, rfl⟩
        exact (φ i).2
      · intro hx
        refine ⟨φ.symm ⟨x, hx⟩, ?_⟩
        simp
    have hbit := eq_on_of_map_eq hedges f (mem_allTuples s₁ n₁ f)
    rw [himg] at hbit
    have heq : (@decide (e ∈ H₁.edges) (Classical.propDecidable _) = true) =
        (@decide (e ∈ H₂.edges) (Classical.propDecidable _) = true) := congrArg (· = true) hbit
    rw [@decide_eq_true_eq _ (Classical.propDecidable _),
      @decide_eq_true_eq _ (Classical.propDecidable _)] at heq
    exact eq_iff_iff.mp heq
  have hH : H₁ = H₂ := by
    refine UniformHypergraph.ext (Finset.ext fun e ↦ ?_)
    constructor
    · intro he1
      exact (hmem e (H₁.edge_card e he1)).mp he1
    · intro he2
      exact (hmem e (H₂.edge_card e he2)).mpr he2
  cases hH
  rfl

/-- Canonical embedding `HPCInstance ↪ List Bool` from `encodeHPCInstance`. -/
noncomputable def encodeHPCInstanceEmb : HPCInstance ↪ List Bool :=
  ⟨encodeHPCInstance, encodeHPCInstance_injective⟩

/-- A randomized polynomial-time distinguisher relative to an injective bit-string encoding
`ea : α ↪ List Bool`, backed by a genuine deterministic multi-tape Turing machine
(`Turing.MultiTapeTM.ComputableInPolyTime`) taking an input `x : α` together with a binary random
tape of polynomial length `randPoly.eval (ea x).length`. -/
structure RandPolyTimeDistinguisher {α : Type} (ea : α ↪ List Bool) where
  /-- Deterministic evaluation function on input `x` and binary random tape `r`. -/
  run : α → List Bool → Bool
  /-- Polynomial bounding the number of random coin flips consumed on input `x`. -/
  randPoly : Polynomial ℕ
  /-- Multi-tape polynomial-time computability of `(x, r) ↦ run x r`. -/
  computable : Turing.MultiTapeTM.ComputableInPolyTime (fun p : α × List Bool ↦ run p.1 p.2)
    (Turing.MultiTapeTM.encPair ea Turing.MultiTapeTM.encBits) Turing.MultiTapeTM.encBool

/-- The Boolean output distribution of `D : RandPolyTimeDistinguisher ea` when executed on a
random input drawn from `P : PMF α` and a fresh uniform binary tape of length
`D.randPoly.eval (ea x).length`. -/
noncomputable def RandPolyTimeDistinguisher.outputPMF {α : Type} {ea : α ↪ List Bool}
    (D : RandPolyTimeDistinguisher ea) (P : PMF α) : PMF Bool :=
  P.bind fun x ↦
    (Cslib.Probability.PMF.uniformOfFintype
        (Fin (D.randPoly.eval (ea x).length) → Bool)).map fun r ↦
      D.run x (List.ofFn r)

/-- The probabilities of outputting `true` and `false` under `D.outputPMF P` sum to `1`. -/
theorem RandPolyTimeDistinguisher.outputPMF_true_add_false_eq_one {α : Type}
    {ea : α ↪ List Bool} (D : RandPolyTimeDistinguisher ea) (P : PMF α) :
    (D.outputPMF P true).toReal + (D.outputPMF P false).toReal = 1 := by
  have hsum : D.outputPMF P true + D.outputPMF P false = 1 := by
    have htsum := (D.outputPMF P).tsum_coe
    rw [tsum_fintype, Fintype.sum_bool] at htsum
    exact htsum
  rw [← ENNReal.toReal_add ((D.outputPMF P).apply_ne_top true)
    ((D.outputPMF P).apply_ne_top false), hsum, ENNReal.toReal_one]

/-- When two input distributions coincide (`P = Q`), any randomized distinguisher has Type I plus
Type II error sum equal to `1`. -/
theorem RandPolyTimeDistinguisher.outputPMF_error_sum_eq_one_of_eq {α : Type}
    {ea : α ↪ List Bool} (D : RandPolyTimeDistinguisher ea) {P Q : PMF α} (hPQ : P = Q) :
    (D.outputPMF P true).toReal + (D.outputPMF Q false).toReal = 1 := by
  rw [hPQ]
  exact D.outputPMF_true_add_false_eq_one Q

/-- When `[Fintype α]`, the Type I plus Type II error sum of any randomized distinguisher is at
least `1 - dist P Q` (in `Cslib.Probability.StatisticalDistance`). -/
theorem RandPolyTimeDistinguisher.one_sub_dist_le_outputPMF_error_sum
    {α : Type} [Fintype α] {ea : α ↪ List Bool} (D : RandPolyTimeDistinguisher ea)
    (P Q : PMF α) :
    1 - dist P Q ≤
      (D.outputPMF P true).toReal + (D.outputPMF Q false).toReal := by
  let K : α → PMF Bool := fun x ↦
    (Cslib.Probability.PMF.uniformOfFintype
        (Fin (D.randPoly.eval (ea x).length) → Bool)).map fun r ↦
      D.run x (List.ofFn r)
  have hbind : dist (P.bind K) (Q.bind K) ≤ dist P Q :=
    Cslib.Probability.PMF.dist_bind_le P Q K
  have hbool : |(D.outputPMF P true).toReal - (D.outputPMF Q true).toReal| ≤
      dist (P.bind K) (Q.bind K) := by
    have hP : (D.outputPMF P true).toReal + (D.outputPMF P false).toReal = 1 :=
      D.outputPMF_true_add_false_eq_one P
    have hQ : (D.outputPMF Q true).toReal + (D.outputPMF Q false).toReal = 1 :=
      D.outputPMF_true_add_false_eq_one Q
    change |(P.bind K true).toReal - (Q.bind K true).toReal| ≤ _
    rw [Cslib.Probability.PMF.dist_eq, Fintype.sum_bool]
    have hfalse : (P.bind K false).toReal - (Q.bind K false).toReal =
        -((P.bind K true).toReal - (Q.bind K true).toReal) := by
      change (D.outputPMF P false).toReal - (D.outputPMF Q false).toReal =
        -((D.outputPMF P true).toReal - (D.outputPMF Q true).toReal)
      linarith
    rw [hfalse, abs_neg]
    linarith
  have hQ : (D.outputPMF Q true).toReal + (D.outputPMF Q false).toReal = 1 :=
    D.outputPMF_true_add_false_eq_one Q
  have hsub := (abs_le.mp (hbool.trans hbind)).1
  linarith

/-- Lift of `bipartiteGnpPMF` to `BPCInstance`. -/
noncomputable def bipartiteGnpInstancePMF (m n k_m k_n : ℕ) (E : BalancedPartition n k_n) :
    PMF BPCInstance :=
  (bipartiteGnpPMF m n).map fun G ↦ ⟨m, n, k_m, k_n, E, G⟩

/-- Lift of `plantedBipartiteCliquePMF` to `BPCInstance`. -/
noncomputable def plantedBipartiteCliqueInstancePMF (m n k_m k_n : ℕ) (hm : k_m ≤ m) (hn : 0 < n)
    (E : BalancedPartition n k_n) : PMF BPCInstance :=
  (plantedBipartiteCliquePMF m n k_m k_n hm hn E).map fun G ↦ ⟨m, n, k_m, k_n, E, G⟩

/-- Lift of `hypergraphGnpPMF` to `HPCInstance`. -/
noncomputable def hypergraphGnpInstancePMF (s n k : ℕ) (E : BalancedPartition n k) :
    PMF HPCInstance :=
  (hypergraphGnpPMF s n).map fun H ↦ ⟨s, n, k, E, H⟩

/-- Lift of `plantedHypergraphCliquePMF` to `HPCInstance`. -/
noncomputable def plantedHypergraphCliqueInstancePMF (s n k : ℕ) (hn : 0 < n)
    (E : BalancedPartition n k) : PMF HPCInstance :=
  (plantedHypergraphCliquePMF s n k hn E).map fun H ↦ ⟨s, n, k, E, H⟩

end EncodingsAndDistinguishers

/-! ### : The $k$-BPC and $k$-HPC Conjectures and Non-Vacuity Witnesses -/

section Conjectures

/-- Admissible asymptotic parameter sequence for the $k$-$\mathrm{BPC}$ conjecture: positive
polynomially-related graph dimensions `(m t, n t)` with `n t → ∞`, balanced right-side
partitions `part t`, and sub-Kneser clique sizes `km t = o(√(m t))`, `kn t = o(√(n t))`. -/
structure BPCParamSeq where
  /-- Left vertex count sequence `m t`. -/
  m : ℕ → ℕ
  /-- Right vertex count sequence `n t`. -/
  n : ℕ → ℕ
  /-- Left planted clique size sequence `km t`. -/
  km : ℕ → ℕ
  /-- Right part/clique count sequence `kn t`. -/
  kn : ℕ → ℕ
  /-- Released balanced `kn t`-partition of `Fin (n t)` at index `t`. -/
  part : ∀ t, BalancedPartition (n t) (kn t)
  /-- Positivity of left vertex counts. -/
  m_pos : ∀ t, 0 < m t
  /-- Positivity of right vertex counts. -/
  n_pos : ∀ t, 0 < n t
  /-- Positivity of left clique sizes. -/
  km_pos : ∀ t, 0 < km t
  /-- Clique size bound `km t ≤ m t`. -/
  km_le : ∀ t, km t ≤ m t
  /-- Divergence `n t → ∞`. -/
  n_tendsto : Tendsto n atTop atTop
  /-- Polynomial relatedness between `m t` and `n t`. -/
  poly_rel : ∃ C : ℕ, 1 ≤ C ∧ ∀ t, m t ≤ C * (n t + 1) ^ C ∧ n t ≤ C * (m t + 1) ^ C
  /-- Sub-polynomial clique condition `km t = o(√(m t))`. -/
  km_sublinear : Tendsto (fun t ↦ (km t : ℝ) / Real.sqrt (m t)) atTop (nhds 0)
  /-- Sub-polynomial clique condition `kn t = o(√(n t))`. -/
  kn_sublinear : Tendsto (fun t ↦ (kn t : ℝ) / Real.sqrt (n t)) atTop (nhds 0)

private lemma tendsto_add_one_div_sqrt_cube :
    Tendsto (fun t : ℕ ↦ ((t + 1 : ℕ) : ℝ) / Real.sqrt (((t + 1) ^ 3 : ℕ) : ℝ))
      atTop (nhds 0) := by
  have hrew : (fun t : ℕ ↦ ((t + 1 : ℕ) : ℝ) / Real.sqrt (((t + 1) ^ 3 : ℕ) : ℝ)) =
      fun t : ℕ ↦ (1 : ℝ) / Real.sqrt ((t : ℝ) + 1) := by
    funext t
    have hpos : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have hpow : (((t + 1) ^ 3 : ℕ) : ℝ) = ((t : ℝ) + 1) ^ 2 * ((t : ℝ) + 1) := by
      push_cast; ring
    rw [hpow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos.le]
    push_cast
    field_simp
  rw [hrew]
  refine tendsto_const_nhds.div_atTop ?_
  exact Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

/-- Non-vacuity witness: `BPCParamSeq` is inhabited (e.g., `m t = n t = (t + 1) ^ 3` and
`km t = kn t = t + 1`). -/
theorem nonempty_bpcParamSeq : Nonempty BPCParamSeq := by
  refine ⟨⟨fun t ↦ (t + 1) ^ 3, fun t ↦ (t + 1) ^ 3, fun t ↦ t + 1, fun t ↦ t + 1,
    fun t ↦ modBalancedPartition (Nat.succ_pos t) ⟨(t + 1) ^ 2, by ring⟩,
    fun _ ↦ by positivity, fun _ ↦ by positivity, fun _ ↦ Nat.succ_pos _,
    fun t ↦ ?_, ?_, ⟨1, le_rfl, fun t ↦ ⟨by ring_nf; omega, by ring_nf; omega⟩⟩,
    tendsto_add_one_div_sqrt_cube, tendsto_add_one_div_sqrt_cube⟩⟩
  · exact Nat.le_self_pow (by norm_num) _
  · refine Filter.tendsto_atTop_atTop.mpr fun b ↦ ⟨b, fun t ht ↦ ?_⟩
    exact ht.trans (Nat.le_self_pow (by norm_num) _ |>.trans' (Nat.le_succ t))

/-- The **$k$-part bipartite planted clique ($k$-$\mathrm{BPC}$) conjecture**
: for every admissible parameter sequence `(m_t, n_t, k_{m,t}, k_{n,t}, E_t)` with
`k_{m,t} = o(√m_t)` and `k_{n,t} = o(√n_t)`, no randomized polynomial-time distinguisher achieves
asymptotic total-variation / hypothesis-testing error sum `≤ 1 - c` for any constant `c > 0`.
-/
def kBPCConjecture : Prop :=
  ∀ seq : BPCParamSeq,
    ¬ ∃ (D : RandPolyTimeDistinguisher encodeBPCInstanceEmb) (c : ℝ),
      0 < c ∧
      ∀ᶠ t in atTop,
        (D.outputPMF (bipartiteGnpInstancePMF (seq.m t) (seq.n t) (seq.km t) (seq.kn t)
          (seq.part t)) true).toReal +
        (D.outputPMF (plantedBipartiteCliqueInstancePMF (seq.m t) (seq.n t) (seq.km t)
          (seq.kn t) (seq.km_le t) (seq.n_pos t) (seq.part t)) false).toReal ≤ 1 - c

/-- Characterization of `CslibFrontier.Computability.kBPCConjecture`. -/
theorem kBPCConjecture_iff :
    kBPCConjecture ↔
      ∀ seq : BPCParamSeq,
        ¬ ∃ (D : RandPolyTimeDistinguisher encodeBPCInstanceEmb) (c : ℝ),
          0 < c ∧
          ∀ᶠ t in atTop,
            (D.outputPMF (bipartiteGnpInstancePMF (seq.m t) (seq.n t) (seq.km t) (seq.kn t)
              (seq.part t)) true).toReal +
            (D.outputPMF (plantedBipartiteCliqueInstancePMF (seq.m t) (seq.n t) (seq.km t)
              (seq.kn t) (seq.km_le t) (seq.n_pos t) (seq.part t)) false).toReal ≤ 1 - c :=
  Iff.rfl

/-- Admissible asymptotic parameter sequence for the $k$-$\mathrm{HPC}^s$ conjecture: positive
vertex counts `n t → ∞`, balanced `k t`-partitions `part t`, and `k t = o(√(n t))`. -/
structure HPCParamSeq where
  /-- Vertex count sequence `n t`. -/
  n : ℕ → ℕ
  /-- Number of parts (and planted clique size) `k t`. -/
  k : ℕ → ℕ
  /-- Released balanced `k t`-partition of `Fin (n t)` at index `t`. -/
  part : ∀ t, BalancedPartition (n t) (k t)
  /-- Positivity of vertex counts. -/
  n_pos : ∀ t, 0 < n t
  /-- Divergence `n t → ∞`. -/
  n_tendsto : Tendsto n atTop atTop
  /-- Sub-polynomial clique condition `k t = o(√(n t))`. -/
  k_sublinear : Tendsto (fun t ↦ (k t : ℝ) / Real.sqrt (n t)) atTop (nhds 0)

/-- Non-vacuity witness: `HPCParamSeq` is inhabited (e.g., `n t = (t + 1) ^ 3`, `k t = t + 1`). -/
theorem nonempty_hpcParamSeq : Nonempty HPCParamSeq := by
  refine ⟨⟨fun t ↦ (t + 1) ^ 3, fun t ↦ t + 1,
    fun t ↦ modBalancedPartition (Nat.succ_pos t) ⟨(t + 1) ^ 2, by ring⟩,
    fun _ ↦ by positivity, ?_, tendsto_add_one_div_sqrt_cube⟩⟩
  refine Filter.tendsto_atTop_atTop.mpr fun b ↦ ⟨b, fun t ht ↦ ?_⟩
  exact ht.trans (Nat.le_self_pow (by norm_num) _ |>.trans' (Nat.le_succ t))

/-- The **$k$-partite hypergraph planted clique ($k$-$\mathrm{HPC}^s$) conjecture**
: for `s ≥ 3` and every admissible parameter sequence `(n_t, k_t, E_t)` with
`k_t = o(√n_t)`, no randomized polynomial-time distinguisher achieves asymptotic hypothesis-testing
error sum `≤ 1 - c` for any constant `c > 0`.
-/
def kHPCConjecture (s : ℕ) : Prop :=
  3 ≤ s →
  ∀ seq : HPCParamSeq,
    ¬ ∃ (D : RandPolyTimeDistinguisher encodeHPCInstanceEmb) (c : ℝ),
      0 < c ∧
      ∀ᶠ t in atTop,
        (D.outputPMF (hypergraphGnpInstancePMF s (seq.n t) (seq.k t) (seq.part t)) true).toReal +
        (D.outputPMF (plantedHypergraphCliqueInstancePMF s (seq.n t) (seq.k t) (seq.n_pos t)
          (seq.part t)) false).toReal ≤ 1 - c

/-- Characterization of `CslibFrontier.Computability.kHPCConjecture`. -/
theorem kHPCConjecture_iff (s : ℕ) :
    kHPCConjecture s ↔
      (3 ≤ s →
      ∀ seq : HPCParamSeq,
        ¬ ∃ (D : RandPolyTimeDistinguisher encodeHPCInstanceEmb) (c : ℝ),
          0 < c ∧
          ∀ᶠ t in atTop,
            (D.outputPMF (hypergraphGnpInstancePMF s (seq.n t) (seq.k t) (seq.part t))
              true).toReal +
            (D.outputPMF (plantedHypergraphCliqueInstancePMF s (seq.n t) (seq.k t) (seq.n_pos t)
              (seq.part t)) false).toReal ≤ 1 - c) :=
  Iff.rfl

/-- Unconditional indistinguishability sanity theorem: if `seq.k t < s` eventually, then every
randomized polynomial-time distinguisher has asymptotic Type I + Type II error sum equal to `1`,
and hence cannot achieve constant advantage `c > 0`. -/
theorem no_distinguisher_hypergraph_of_eventually_lt (s : ℕ) (seq : HPCParamSeq)
    (hlt : ∀ᶠ t in atTop, seq.k t < s) :
    ¬ ∃ (D : RandPolyTimeDistinguisher encodeHPCInstanceEmb) (c : ℝ),
      0 < c ∧
      ∀ᶠ t in atTop,
        (D.outputPMF (hypergraphGnpInstancePMF s (seq.n t) (seq.k t) (seq.part t)) true).toReal +
        (D.outputPMF (plantedHypergraphCliqueInstancePMF s (seq.n t) (seq.k t) (seq.n_pos t)
          (seq.part t)) false).toReal ≤ 1 - c := by
  rintro ⟨D, c, hc, hadv⟩
  obtain ⟨t, htlt, htle⟩ := (hlt.and hadv).exists
  have heq : hypergraphGnpInstancePMF s (seq.n t) (seq.k t) (seq.part t) =
      plantedHypergraphCliqueInstancePMF s (seq.n t) (seq.k t) (seq.n_pos t) (seq.part t) := by
    simp only [hypergraphGnpInstancePMF, plantedHypergraphCliqueInstancePMF,
      plantedHypergraphCliquePMF_eq_of_lt s (seq.n t) (seq.k t) (seq.n_pos t) htlt (seq.part t)]
  have hone := D.outputPMF_error_sum_eq_one_of_eq heq
  linarith

end Conjectures

end CslibFrontier.Computability
