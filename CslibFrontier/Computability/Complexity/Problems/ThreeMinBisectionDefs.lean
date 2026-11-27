/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Computability.Complexity.Problems.MinBisection
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.List.GetD

/-!
# Cubic Torus Gadget Definitions and Poly-Time Reduction

Defines the 4-vertex-cell cubic torus gadget `torusGadgetEdges`, the reduction graph
`torusReductionGraph`, and the polynomial-time reduction `toThreeMinBisection` from
`MinBisection` to `ThreeMinBisection`, together with basic vertex-encoding lemmas and
polynomial-time computability.

## Main definitions

* `CslibFrontier.Complexity.MinBisection.torusVid`: vertex identifier `(u, r, c, t)` in gadget
  `H_u`.
* `CslibFrontier.Complexity.MinBisection.torusGadgetEdges`: edges of gadget `H_u` with `degU` ports.
* `CslibFrontier.Complexity.MinBisection.torusReductionGraph`: the cubic graph built from `G`.
* `CslibFrontier.Complexity.MinBisection.toThreeMinBisection`: reduction `MinBisection →
  ThreeMinBisection`.

## Main results

* `CslibFrontier.Complexity.MinBisection.computableInPolyTime_toThreeMinBisection`: poly-time
  computability.
-/

public section

namespace CslibFrontier.Complexity.MinBisection

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-- Vertex ID of cell `(r, c)` and subvertex `t ∈ {0, 1, 2, 3}` in gadget `u` of side `K`. -/
@[expose]
def torusVid (K u r c t : ℕ) : ℕ := ((u * K + r) * K + c) * 4 + t

/-- Edges of cell `(r, c)` in the 3-regular toroidal gadget `H_u` of side `K`. -/
@[expose]
def torusCellEdges (K u degU r c : ℕ) : List (ℕ × ℕ) :=
  let a := torusVid K u r c 0
  let b := torusVid K u r c 1
  let cv := torusVid K u r c 2
  let d := torusVid K u r c 3
  let aNext := torusVid K u r ((c + 1) % K) 0
  let bNext := torusVid K u ((r + 1) % K) c 1
  let base := [(a, cv), (cv, aNext), (b, d), (d, bNext), (cv, d)]
  if decide (r == c && r < degU) then base else (a, b) :: base

/-- Edges of the 3-regular toroidal gadget `H_u` of side `K` with `degU` diagonal ports
deleted (`(a_{i,i}, b_{i,i})` removed for `i < degU`). -/
@[expose]
def torusGadgetEdges (K u degU : ℕ) : List (ℕ × ℕ) :=
  (List.range K).flatMap fun r =>
    (List.range K).flatMap fun c =>
      torusCellEdges K u degU r c

/-- Fixed YES-instance of `ThreeMinBisection`: `K₄` with bound `4`. -/
@[expose]
def threeYesInstance : MinBisectionInstance :=
  ⟨⟨[0, 1, 2, 3], [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]⟩, 4⟩

/-- Fixed NO-instance of `ThreeMinBisection`: `K₄` with bound `0`. -/
@[expose]
def threeNoInstance : MinBisectionInstance :=
  ⟨⟨[0, 1, 2, 3], [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]⟩, 0⟩

theorem threeYesInstance_mem : threeYesInstance ∈ ThreeMinBisection := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro ⟨v, hv⟩
    have h0123 : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by simpa [threeYesInstance] using hv
    have hdeg_eq : threeYesInstance.graph.induced.degree ⟨v, hv⟩ =
        (threeYesInstance.graph.vertices.filter fun u =>
          threeYesInstance.graph.adjBool v u).length := by
      rw [SimpleGraph.degree,
        ← List.toFinset_card_of_nodup ((by decide : threeYesInstance.graph.vertices.Nodup).filter
          _)]
      rw [← Finset.card_map (Function.Embedding.subtype (· ∈ threeYesInstance.graph.vertices))]
      congr 1; ext u
      simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, Graph.induced_adj,
        Function.Embedding.coe_subtype, List.mem_toFinset, List.mem_filter,
        Graph.adjBool_eq_true_iff]
      exact ⟨fun ⟨⟨w, hw⟩, hadj, heq⟩ => ⟨heq ▸ hw, heq ▸ hadj⟩,
        fun ⟨hu, hadj⟩ => ⟨⟨u, hu⟩, hadj, rfl⟩⟩
    rw [hdeg_eq]
    rcases h0123 with rfl | rfl | rfl | rfl <;> decide
  · rw [mem_MinBisection_iff]
    refine ⟨{0, 1}, by intro v hv; simp [threeYesInstance] at hv ⊢; omega, ?_, ?_⟩
    · rw [Graph.length_distinctVertices]; simp [threeYesInstance]
    · have hle : (threeYesInstance.graph.induced.interedges
          (({0, 1} : Finset ℕ).subtype (· ∈ threeYesInstance.graph.vertices))
          (({0, 1} : Finset ℕ).subtype (· ∈ threeYesInstance.graph.vertices))ᶜ).card ≤ 4 := by
        have hsub : threeYesInstance.graph.induced.interedges
            (({0, 1} : Finset ℕ).subtype (· ∈ threeYesInstance.graph.vertices))
            (({0, 1} : Finset ℕ).subtype (· ∈ threeYesInstance.graph.vertices))ᶜ ⊆
            (({0, 1} : Finset ℕ).subtype (· ∈ threeYesInstance.graph.vertices)) ×ˢ
            (({0, 1} : Finset ℕ).subtype (· ∈ threeYesInstance.graph.vertices))ᶜ := by
          intro ⟨a, b⟩ h; rw [SimpleGraph.mem_interedges_iff] at h
          exact Finset.mem_product.mpr ⟨h.1, h.2.1⟩
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_product] at h1
        have hca : (({0, 1} : Finset ℕ).subtype (· ∈ threeYesInstance.graph.vertices)).card =
          2 := by
          refine Finset.card_eq_two.mpr ⟨⟨0, by simp [threeYesInstance]⟩,
            ⟨1, by simp [threeYesInstance]⟩, by simp [Subtype.ext_iff], ?_⟩
          ext ⟨w, hw⟩
          simp only [Finset.mem_subtype, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨fun h => by rcases h with rfl | rfl <;> simp,
            fun h => by rcases h with h | h <;> simp [Subtype.ext_iff] at h <;> omega⟩
        have hcb : (({0, 1} : Finset ℕ).subtype (· ∈ threeYesInstance.graph.vertices))ᶜ.card =
          2 := by
          have := Finset.card_compl (({0, 1} : Finset ℕ).subtype
            (· ∈ threeYesInstance.graph.vertices))
          have hv : Fintype.card {v // v ∈ threeYesInstance.graph.vertices} = 4 := by
            rw [card_subtype_eq_distinctVertices]; decide
          omega
        rw [hca, hcb] at h1; exact h1
      exact hle

theorem threeNoInstance_notMem : threeNoInstance ∉ ThreeMinBisection := by
  rintro ⟨_, _, _, S, hcard, hcut⟩
  have hS2 : S.card = 2 := by
    have hv : Fintype.card {v // v ∈ threeNoInstance.graph.vertices} = 4 := by
      rw [card_subtype_eq_distinctVertices]; decide
    omega
  have hSc : Sᶜ.card = 2 := by
    have := Finset.card_compl S
    have hv : Fintype.card {v // v ∈ threeNoInstance.graph.vertices} = 4 := by
      rw [card_subtype_eq_distinctVertices]; decide
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < Sᶜ.card)
  have hne : u ≠ v := fun h => (Finset.mem_compl.mp hv) (h ▸ hu)
  have hadj : threeNoInstance.graph.induced.Adj u v := by
    rw [Graph.induced_adj, Graph.toSimpleGraph_adj]
    refine ⟨fun h => hne (Subtype.ext h), ?_⟩
    have hu4 : u.1 = 0 ∨ u.1 = 1 ∨ u.1 = 2 ∨ u.1 = 3 := by simpa [threeNoInstance] using u.2
    have hv4 : v.1 = 0 ∨ v.1 = 1 ∨ v.1 = 2 ∨ v.1 = 3 := by simpa [threeNoInstance] using v.2
    have hne' : u.1 ≠ v.1 := fun h => hne (Subtype.ext h)
    rcases hu4 with h1 | h1 | h1 | h1 <;> rcases hv4 with h2 | h2 | h2 | h2 <;>
      simp [threeNoInstance, h1, h2] at hne' ⊢
  have hpos : 0 < (threeNoInstance.graph.induced.interedges S Sᶜ).card :=
    Finset.card_pos.mpr ⟨(u, v), by rw [SimpleGraph.mem_interedges_iff]; exact ⟨hu, hv, hadj⟩⟩
  change (threeNoInstance.graph.induced.interedges S Sᶜ).card ≤ 0 at hcut
  omega

/-- Reduction from `MinBisection` to `ThreeMinBisection`. -/
@[expose]
def toThreeMinBisection (x : MinBisectionInstance) : MinBisectionInstance :=
  let V := x.graph.distinctVertices
  let n := V.length
  if n == 0 then
    threeYesInstance
  else if !(n % 2 == 0) then
    threeNoInstance
  else if decide (n * n ≤ x.bound) then
    threeYesInstance
  else
    let K := 4 * n * n + 8
    let nbrs := fun u =>
      (List.range n).filter fun v => x.graph.adjBool (V.getD u 0) (V.getD v 0)
    let internalEdges := (List.range n).flatMap fun u =>
      torusGadgetEdges K u (nbrs u).length
    let crossEdges := (List.range n).flatMap fun u =>
      ((List.range n).filter fun v =>
        decide (u < v) && x.graph.adjBool (V.getD u 0) (V.getD v 0)).flatMap fun v =>
          let i := (nbrs u).idxOf v
          let j := (nbrs v).idxOf u
          [(torusVid K u i i 0, torusVid K v j j 0),
           (torusVid K u i i 1, torusVid K v j j 1)]
    ⟨⟨List.range (4 * K * K * n), internalEdges ++ crossEdges⟩, 2 * x.bound⟩

theorem torusVid_injective {K : ℕ} (hK : 0 < K)
    {u1 r1 c1 t1 u2 r2 c2 t2 : ℕ}
    (hr1 : r1 < K) (hc1 : c1 < K) (ht1 : t1 < 4)
    (hr2 : r2 < K) (hc2 : c2 < K) (ht2 : t2 < 4)
    (heq : torusVid K u1 r1 c1 t1 = torusVid K u2 r2 c2 t2) :
    u1 = u2 ∧ r1 = r2 ∧ c1 = c2 ∧ t1 = t2 := by
  unfold torusVid at heq
  have ht : t1 = t2 := by omega
  have h1 : (u1 * K + r1) * K + c1 = (u2 * K + r2) * K + c2 := by omega
  have hc : c1 = c2 := by
    have := congrArg (· % K) h1
    rw [Nat.mul_comm (u1 * K + r1) K, Nat.mul_comm (u2 * K + r2) K, Nat.mul_add_mod,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hc2] at this
    exact this
  have h2 : u1 * K + r1 = u2 * K + r2 := by
    have := congrArg (· / K) h1
    rw [Nat.mul_comm (u1 * K + r1) K, Nat.mul_comm (u2 * K + r2) K, Nat.mul_add_div hK,
      Nat.mul_add_div hK, Nat.div_eq_of_lt hc1, Nat.div_eq_of_lt hc2] at this
    omega
  have hr : r1 = r2 := by
    have := congrArg (· % K) h2
    rw [Nat.mul_comm _ K, Nat.mul_comm _ K, Nat.mul_add_mod, Nat.mul_add_mod,
      Nat.mod_eq_of_lt hr1, Nat.mod_eq_of_lt hr2] at this
    exact this
  have hu : u1 = u2 := by
    have := congrArg (· / K) h2
    rw [Nat.mul_comm _ K, Nat.mul_comm _ K, Nat.mul_add_div hK, Nat.mul_add_div hK,
      Nat.div_eq_of_lt hr1, Nat.div_eq_of_lt hr2] at this
    omega
  exact ⟨hu, hr, hc, ht⟩

theorem torusVid_lt {K n u r c t : ℕ} (hu : u < n) (hr : r < K) (hc : c < K) (ht : t < 4) :
    torusVid K u r c t < 4 * K * K * n := by
  unfold torusVid
  have h1 : u * K + r < n * K := by
    have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hu); nlinarith
  have h2 : (u * K + r) * K + c < n * K * K := by
    have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt h1); nlinarith
  nlinarith

/-- On any cycle of length `2 * K` (`a_0 - c_0 - a_1 - c_1 - ... - a_0`), if a subset `A`
neither contains all `2 * K` vertices nor is empty, then at least 2 cycle edges cross `A`. -/
theorem cycle_cut_ge_two {K : ℕ} (hK : 2 ≤ K) (A : ℕ → Bool)
    (h1 : ∃ i < K, A (2 * i) = true ∨ A (2 * i + 1) = true)
    (h2 : ∃ j < K, A (2 * j) = false ∨ A (2 * j + 1) = false) :
    2 ≤ ((List.range K).filter fun c => A (2 * c) != A (2 * c + 1)).length +
        ((List.range K).filter fun c => A (2 * c + 1) != A (2 * ((c + 1) % K))).length := by
  -- Model as a single cycle of length 2*K via `B (k : ℕ) := A k` for `k < 2*K`
  have hcycle : ∀ (m : ℕ) (B : ℕ → Bool), 2 ≤ m →
      (∃ i < m, B i = true) → (∃ j < m, B j = false) →
      2 ≤ ((List.range m).filter fun k => B k != B ((k + 1) % m)).length := by
    intro m B hm ⟨i, hi, hBi⟩ ⟨j, hj, hBj⟩
    -- Count transitions from true→false (at least 1) and false→true (at least 1)
    have htf : ∃ k < m, B k = true ∧ B ((k + 1) % m) = false := by
      by_contra hnone; push Not at hnone
      have hall : ∀ d, B ((i + d) % m) = true := by
        intro d; induction d with
        | zero => simpa [Nat.mod_eq_of_lt hi] using hBi
        | succ d' ih =>
          have hstep := hnone ((i + d') % m) (Nat.mod_lt _ (by omega)) ih
          have hmod : ((i + d') % m + 1) % m = (i + (d' + 1)) % m := by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
          rw [hmod] at hstep
          cases hB : B ((i + (d' + 1)) % m)
          · exact absurd hB hstep
          · rfl
      have hdiff := hall (j + m - i)
      have hmod : (i + (j + m - i)) % m = j := by
        rw [show i + (j + m - i) = j + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
      rw [hmod] at hdiff; rw [hBj] at hdiff; exact Bool.false_ne_true hdiff
    have hft : ∃ k < m, B k = false ∧ B ((k + 1) % m) = true := by
      by_contra hnone; push Not at hnone
      have hall : ∀ d, B ((j + d) % m) = false := by
        intro d; induction d with
        | zero => simpa [Nat.mod_eq_of_lt hj] using hBj
        | succ d' ih =>
          have hstep := hnone ((j + d') % m) (Nat.mod_lt _ (by omega)) ih
          have hmod : ((j + d') % m + 1) % m = (j + (d' + 1)) % m := by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
          rw [hmod] at hstep
          cases hB : B ((j + (d' + 1)) % m)
          · rfl
          · exact absurd hB hstep
      have hdiff := hall (i + m - j)
      have hmod : (j + (i + m - j)) % m = i := by
        rw [show j + (i + m - j) = i + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      rw [hmod] at hdiff; rw [hBi] at hdiff; exact Bool.noConfusion hdiff
    obtain ⟨k1, hk1, h1a, h1b⟩ := htf
    obtain ⟨k2, hk2, h2a, h2b⟩ := hft
    have hne : k1 ≠ k2 := fun h => by rw [h, h2a] at h1a; exact Bool.noConfusion h1a
    have hsub : ({k1, k2} : Finset ℕ) ⊆
        ((List.range m).filter fun k => B k != B ((k + 1) % m)).toFinset := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range]
      rcases hk with rfl | rfl
      · exact ⟨hk1, by simp [h1a, h1b]⟩
      · exact ⟨hk2, by simp [h2a, h2b]⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair hne, List.toFinset_card_of_nodup (List.nodup_range.filter _)] at hcard
    exact hcard
  have h1' : ∃ i < 2 * K, A i = true := by
    obtain ⟨i, hi, h | h⟩ := h1
    · exact ⟨2 * i, by omega, h⟩
    · exact ⟨2 * i + 1, by omega, h⟩
  have h2' : ∃ j < 2 * K, A j = false := by
    obtain ⟨j, hj, h | h⟩ := h2
    · exact ⟨2 * j, by omega, h⟩
    · exact ⟨2 * j + 1, by omega, h⟩
  have h2K := hcycle (2 * K) A (by omega) h1' h2'
  -- Partition `List.range (2 * K)` into even and odd indices
  have hsplit : ((List.range (2 * K)).filter fun k => A k != A ((k + 1) % (2 * K))).length =
      ((List.range K).filter fun c => A (2 * c) != A (2 * c + 1)).length +
      ((List.range K).filter fun c => A (2 * c + 1) != A (2 * ((c + 1) % K))).length := by
    set L := (List.range (2 * K)).filter fun k => A k != A ((k + 1) % (2 * K))
    set E := (List.range K).filter fun c => A (2 * c) != A (2 * c + 1)
    set O := (List.range K).filter fun c => A (2 * c + 1) != A (2 * ((c + 1) % K))
    rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _),
        ← List.toFinset_card_of_nodup (List.nodup_range.filter _),
        ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
    have hdisj : Disjoint (E.toFinset.image (2 * ·)) (O.toFinset.image (fun c => 2 * c + 1)) := by
      rw [Finset.disjoint_left]; intro x hx hy
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, _, h⟩ := Finset.mem_image.mp hy
      omega
    have hunion : L.toFinset =
      E.toFinset.image (2 * ·) ∪ O.toFinset.image (fun c => 2 * c + 1) := by
      ext k
      simp only [L, E, O, Finset.mem_union, Finset.mem_image, List.mem_toFinset, List.mem_filter,
        List.mem_range]
      constructor
      · rintro ⟨hk, htr⟩
        by_cases hev : k % 2 = 0
        · left; refine ⟨k / 2, ⟨by omega, ?_⟩, by omega⟩
          have h1e : 2 * (k / 2) = k := by omega
          have h2e : (k + 1) % (2 * K) = k + 1 := Nat.mod_eq_of_lt (by omega)
          rwa [h1e, ← h2e]
        · right; refine ⟨k / 2, ⟨by omega, ?_⟩, by omega⟩
          have h1o : 2 * (k / 2) + 1 = k := by omega
          have h2o : 2 * ((k / 2 + 1) % K) = (k + 1) % (2 * K) := by
            by_cases hlast : k / 2 + 1 = K
            · rw [hlast, Nat.mod_self, show k + 1 = 2 * K by omega, Nat.mod_self]
            · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
          rwa [h1o, h2o]
      · rintro (⟨c, ⟨hc, htr⟩, rfl⟩ | ⟨c, ⟨hc, htr⟩, rfl⟩)
        · refine ⟨by omega, ?_⟩
          rwa [Nat.mod_eq_of_lt (by omega)]
        · refine ⟨by omega, ?_⟩
          have h2o : 2 * ((c + 1) % K) = (2 * c + 1 + 1) % (2 * K) := by
            by_cases hlast : c + 1 = K
            · rw [hlast, Nat.mod_self, show 2 * c + 1 + 1 = 2 * K by omega, Nat.mod_self]
            · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
          rwa [← h2o]
    rw [hunion, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun _ _ h => by omega),
      Finset.card_image_of_injective _ (fun _ _ h => by omega)]
  omega


/-- The cubic torus-gadget graph `G'` built from `G` in the main case of `toThreeMinBisection`. -/
@[expose]
def torusReductionGraph (G : Graph) : Graph :=
  let V := G.distinctVertices
  let n := V.length
  let K := 4 * n * n + 8
  let nbrs := fun u => (List.range n).filter fun v => G.adjBool (V.getD u 0) (V.getD v 0)
  let internalEdges := (List.range n).flatMap fun u => torusGadgetEdges K u (nbrs u).length
  let crossEdges := (List.range n).flatMap fun u =>
    ((List.range n).filter fun v =>
      decide (u < v) && G.adjBool (V.getD u 0) (V.getD v 0)).flatMap fun v =>
        let i := (nbrs u).idxOf v
        let j := (nbrs v).idxOf u
        [(torusVid K u i i 0, torusVid K v j j 0),
         (torusVid K u i i 1, torusVid K v j j 1)]
  ⟨List.range (4 * K * K * n), internalEdges ++ crossEdges⟩

/-- Helper relating `Finset.range` sums to `List.range` sums. -/
theorem sum_range_eq_list_sum {α : Type*} [AddCommMonoid α] (m : ℕ) (f : ℕ → α) :
    ∑ i ∈ Finset.range m, f i = ((List.range m).map f).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]; simp

attribute [local irreducible] encMinBisection encGraph encNat encUnary in
private theorem computableInPolyTime_torusVid_comp {α : Type} {enc : α ↪ List Bool}
    {K u r c t : α → ℕ}
    (hK : ComputableInPolyTime K enc encUnary) (hu : ComputableInPolyTime u enc encUnary)
    (hr : ComputableInPolyTime r enc encUnary) (hc : ComputableInPolyTime c enc encUnary)
    (ht : ComputableInPolyTime t enc encUnary) :
    ComputableInPolyTime (fun x => torusVid (K x) (u x) (r x) (c x) (t x)) enc encNat := by
  unfold torusVid
  have hKb := ComputableInPolyTime.unary_to_binary.comp' hK
  have hub := ComputableInPolyTime.unary_to_binary.comp' hu
  have hrb := ComputableInPolyTime.unary_to_binary.comp' hr
  have hcb := ComputableInPolyTime.unary_to_binary.comp' hc
  have htb := ComputableInPolyTime.unary_to_binary.comp' ht
  fun_prop

attribute [local irreducible] encMinBisection encGraph encNat encUnary in
private theorem computableInPolyTime_torusCellEdges :
    ComputableInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => torusCellEdges q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.1.2 q.2)
      (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary)
      (encList (encPair encNat encNat)) := by
  unfold torusCellEdges
  have hK : ComputableInPolyTime (fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.1)
      (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary)
      encUnary := by fun_prop
  have hu : ComputableInPolyTime (fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.2)
      (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary)
      encUnary := by fun_prop
  have hr : ComputableInPolyTime (fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => q.1.2)
      (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary)
      encUnary := by fun_prop
  have hc : ComputableInPolyTime (fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => q.2)
      (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary)
      encUnary := by fun_prop
  have hc1 : ComputableInPolyTime (fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => (q.2 + 1) % q.1.1.1.1)
      (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary)
      encUnary := by
    have hplus : ComputableInPolyTime (fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => q.2 + 1)
        (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary)
        encUnary := by fun_prop
    have hmod : ComputableInPolyTime (fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => (q.2 + 1) % q.1.1.1.1)
        (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary)
        encNat :=
      ComputableInPolyTime.binary_mod.comp'
        ((ComputableInPolyTime.unary_to_binary.comp' hplus).prod
          (ComputableInPolyTime.unary_to_binary.comp' hK))
    exact (ComputableInPolyTime.binary_min_unary' hplus hmod).of_enc_eq fun q => by
      simp [Nat.min_eq_right (Nat.mod_le _ _)]
  have hr1 : ComputableInPolyTime (fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => (q.1.2 + 1) % q.1.1.1.1)
      (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary)
      encUnary := by
    have hplus : ComputableInPolyTime (fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => q.1.2 + 1)
        (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary)
        encUnary := by fun_prop
    have hmod : ComputableInPolyTime (fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ =>
        (q.1.2 + 1) % q.1.1.1.1)
        (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary)
        encNat :=
      ComputableInPolyTime.binary_mod.comp'
        ((ComputableInPolyTime.unary_to_binary.comp' hplus).prod
          (ComputableInPolyTime.unary_to_binary.comp' hK))
    exact (ComputableInPolyTime.binary_min_unary' hplus hmod).of_enc_eq fun q => by
      simp [Nat.min_eq_right (Nat.mod_le _ _)]
  have hconst (c : ℕ) : ComputableInPolyTime (fun _ : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => c)
      (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary)
      encUnary := ComputableInPolyTime.const c
  have ha := computableInPolyTime_torusVid_comp hK hu hr hc (hconst 0)
  have hb := computableInPolyTime_torusVid_comp hK hu hr hc (hconst 1)
  have hcv := computableInPolyTime_torusVid_comp hK hu hr hc (hconst 2)
  have hd := computableInPolyTime_torusVid_comp hK hu hr hc (hconst 3)
  have haN := computableInPolyTime_torusVid_comp hK hu hr hc1 (hconst 0)
  have hbN := computableInPolyTime_torusVid_comp hK hu hr1 hc (hconst 1)
  have hbase := ComputableInPolyTime.cons' (ha.prod hcv)
    (ComputableInPolyTime.cons' (hcv.prod haN)
      (ComputableInPolyTime.cons' (hb.prod hd)
        (ComputableInPolyTime.cons' (hd.prod hbN)
          (ComputableInPolyTime.cons' (hcv.prod hd) (ComputableInPolyTime.const [])))))
  have hcond : ComputableInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => decide (q.1.2 == q.2 && q.1.2 < q.1.1.2))
      (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary)
      encBool := by
    have heq : ComputableInPolyTime (fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => q.1.2 == q.2)
        (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary)
        encBool :=
      (ComputableInPolyTime.decide_eq' hr hc).of_enc_eq fun q => by
        cases h : (q.1.2 == q.2) <;> simp_all
    have hlt : ComputableInPolyTime (fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => decide (q.1.2 < q.1.1.2))
        (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary)
        encBool := by fun_prop
    exact (ComputableInPolyTime.bool_and.comp' (heq.prod hlt)).of_enc_eq fun q => by
      cases (q.1.2 == q.2) <;> cases h : decide (q.1.2 < q.1.1.2) <;> simp_all
  exact ComputableInPolyTime.ite hcond hbase (ComputableInPolyTime.cons' (ha.prod hb) hbase)

attribute [local irreducible] encMinBisection encGraph encNat encUnary in
private theorem computableInPolyTime_torusGadgetEdges_comp {α : Type} {enc : α ↪ List Bool}
    {K u degU : α → ℕ}
    (hK : ComputableInPolyTime K enc encUnary) (hu : ComputableInPolyTime u enc encUnary)
    (hdeg : ComputableInPolyTime degU enc encUnary) :
    ComputableInPolyTime (fun x => torusGadgetEdges (K x) (u x) (degU x)) enc
      (encList (encPair encNat encNat)) := by
  have hbase : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => torusGadgetEdges p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encUnary) (encList (encPair encNat encNat)) := by
    unfold torusGadgetEdges
    refine ComputableInPolyTime.flatMapWithInput (by fun_prop) ?_
    refine ComputableInPolyTime.flatMapWithInput (by fun_prop) ?_
    exact computableInPolyTime_torusCellEdges
  exact hbase.comp' ((hK.prod hu).prod hdeg)

attribute [local irreducible] encMinBisection encGraph encNat encUnary in
theorem computableInPolyTime_toThreeMinBisection :
    ComputableInPolyTime toThreeMinBisection encMinBisection encMinBisection := by
  have hmain : ComputableInPolyTime
      (fun x : MinBisectionInstance =>
        let V := x.graph.distinctVertices
        let n := V.length
        let K := 4 * n * n + 8
        let nbrs := fun u => (List.range n).filter fun v => x.graph.adjBool (V.getD u 0)
          (V.getD v 0)
        let internalEdges := (List.range n).flatMap fun u => torusGadgetEdges K u (nbrs u).length
        let crossEdges := (List.range n).flatMap fun u =>
          ((List.range n).filter fun v =>
            decide (u < v) && x.graph.adjBool (V.getD u 0) (V.getD v 0)).flatMap fun v =>
              let i := (nbrs u).idxOf v
              let j := (nbrs v).idxOf u
              [(torusVid K u i i 0, torusVid K v j j 0),
               (torusVid K u i i 1, torusVid K v j j 1)]
        (⟨⟨List.range (4 * K * K * n), internalEdges ++ crossEdges⟩,
          2 * x.bound⟩ : MinBisectionInstance))
      encMinBisection encMinBisection := by
    have hV : ComputableInPolyTime (fun x : MinBisectionInstance => x.graph.distinctVertices)
        encMinBisection (encList encNat) := by fun_prop
    have hn : ComputableInPolyTime (fun x : MinBisectionInstance => x.graph.distinctVertices.length)
        encMinBisection encUnary := by fun_prop
    have hK : ComputableInPolyTime (fun x : MinBisectionInstance =>
        4 * x.graph.distinctVertices.length * x.graph.distinctVertices.length + 8)
        encMinBisection encUnary := by fun_prop
    have hverts : ComputableInPolyTime
        (fun x : MinBisectionInstance =>
          List.range (4 * (4 * x.graph.distinctVertices.length * x.graph.distinctVertices.length +
            8) *
            (4 * x.graph.distinctVertices.length * x.graph.distinctVertices.length + 8) *
            x.graph.distinctVertices.length))
        encMinBisection (encList encNat) := by
      have hr : ComputableInPolyTime
          (fun x : MinBisectionInstance =>
            List.range (4 * (4 * x.graph.distinctVertices.length * x.graph.distinctVertices.length +
              8) *
              (4 * x.graph.distinctVertices.length * x.graph.distinctVertices.length + 8) *
              x.graph.distinctVertices.length))
          encMinBisection (encList encUnary) := by fun_prop
      exact ((ComputableInPolyTime.map ComputableInPolyTime.unary_to_binary).comp hr).of_enc_eq
        fun _ => by simp only [Function.comp_apply, List.map_id']
    have hnbrs : ComputableInPolyTime
        (fun p : MinBisectionInstance × ℕ =>
          (List.range p.1.graph.distinctVertices.length).filter fun v =>
            p.1.graph.adjBool (p.1.graph.distinctVertices.getD p.2 0)
              (p.1.graph.distinctVertices.getD v 0))
        (encPair encMinBisection encUnary) (encList encUnary) := by
      refine ComputableInPolyTime.filterWithInput (by fun_prop) ?_
      have hget1 : ComputableInPolyTime
          (fun q : (MinBisectionInstance × ℕ) × ℕ => q.1.1.graph.distinctVertices.getD q.1.2 0)
          (encPair (encPair encMinBisection encUnary) encUnary) encNat := by fun_prop
      have hget2 : ComputableInPolyTime
          (fun q : (MinBisectionInstance × ℕ) × ℕ => q.1.1.graph.distinctVertices.getD q.2 0)
          (encPair (encPair encMinBisection encUnary) encUnary) encNat := by fun_prop
      exact Graph.computableInPolyTime_adjBool_comp (by fun_prop) hget1 hget2
    have hint : ComputableInPolyTime
        (fun x : MinBisectionInstance =>
          (List.range x.graph.distinctVertices.length).flatMap fun u =>
            torusGadgetEdges (4 * x.graph.distinctVertices.length *
              x.graph.distinctVertices.length + 8) u
              ((List.range x.graph.distinctVertices.length).filter fun v =>
                x.graph.adjBool (x.graph.distinctVertices.getD u 0)
                  (x.graph.distinctVertices.getD v 0)).length)
        encMinBisection (encList (encPair encNat encNat)) := by
      refine ComputableInPolyTime.flatMapWithInput (by fun_prop) ?_
      have hlen : ComputableInPolyTime
          (fun p : MinBisectionInstance × ℕ =>
            ((List.range p.1.graph.distinctVertices.length).filter fun v =>
              p.1.graph.adjBool (p.1.graph.distinctVertices.getD p.2 0)
                (p.1.graph.distinctVertices.getD v 0)).length)
          (encPair encMinBisection encUnary) encUnary :=
        (ComputableInPolyTime.length_list encUnary).comp' hnbrs
      exact computableInPolyTime_torusGadgetEdges_comp
        (hK.comp' (ComputableInPolyTime.fst encMinBisection encUnary))
        (ComputableInPolyTime.snd encMinBisection encUnary) hlen
    have hcross : ComputableInPolyTime
        (fun x : MinBisectionInstance =>
          (List.range x.graph.distinctVertices.length).flatMap fun u =>
            ((List.range x.graph.distinctVertices.length).filter fun v =>
              decide (u < v) && x.graph.adjBool (x.graph.distinctVertices.getD u 0)
                (x.graph.distinctVertices.getD v 0)).flatMap fun v =>
                let i := ((List.range x.graph.distinctVertices.length).filter fun w =>
                  x.graph.adjBool (x.graph.distinctVertices.getD u 0)
                    (x.graph.distinctVertices.getD w 0)).idxOf v
                let j := ((List.range x.graph.distinctVertices.length).filter fun w =>
                  x.graph.adjBool (x.graph.distinctVertices.getD v 0)
                    (x.graph.distinctVertices.getD w 0)).idxOf u
                [(torusVid (4 * x.graph.distinctVertices.length * x.graph.distinctVertices.length +
                  8) u i i 0,
                  torusVid (4 * x.graph.distinctVertices.length * x.graph.distinctVertices.length +
                    8) v j j 0),
                 (torusVid (4 * x.graph.distinctVertices.length * x.graph.distinctVertices.length +
                   8) u i i 1,
                  torusVid (4 * x.graph.distinctVertices.length * x.graph.distinctVertices.length +
                    8) v j j 1)])
        encMinBisection (encList (encPair encNat encNat)) := by
      refine ComputableInPolyTime.flatMapWithInput (by fun_prop) ?_
      have hfilt : ComputableInPolyTime
          (fun p : MinBisectionInstance × ℕ =>
            (List.range p.1.graph.distinctVertices.length).filter fun v =>
              decide (p.2 < v) && p.1.graph.adjBool (p.1.graph.distinctVertices.getD p.2 0)
                (p.1.graph.distinctVertices.getD v 0))
          (encPair encMinBisection encUnary) (encList encUnary) := by
        refine ComputableInPolyTime.filterWithInput (by fun_prop) ?_
        have hget1 : ComputableInPolyTime
            (fun q : (MinBisectionInstance × ℕ) × ℕ => q.1.1.graph.distinctVertices.getD q.1.2 0)
            (encPair (encPair encMinBisection encUnary) encUnary) encNat := by fun_prop
        have hget2 : ComputableInPolyTime
            (fun q : (MinBisectionInstance × ℕ) × ℕ => q.1.1.graph.distinctVertices.getD q.2 0)
            (encPair (encPair encMinBisection encUnary) encUnary) encNat := by fun_prop
        have hg : ComputableInPolyTime (fun q : (MinBisectionInstance × ℕ) × ℕ => q.1.1.graph)
            (encPair (encPair encMinBisection encUnary) encUnary) encGraph := by fun_prop
        have hadj := Graph.computableInPolyTime_adjBool_comp hg hget1 hget2
        fun_prop
      refine ComputableInPolyTime.flatMapWithInput hfilt ?_
      let encQ := encPair (encPair encMinBisection encUnary) encUnary
      have hK' : ComputableInPolyTime (fun q : (MinBisectionInstance × ℕ) × ℕ =>
          4 * q.1.1.graph.distinctVertices.length * q.1.1.graph.distinctVertices.length +
            8) encQ encUnary := by dsimp [encQ]; fun_prop
      have hu' : ComputableInPolyTime (fun q : (MinBisectionInstance × ℕ) × ℕ =>
        q.1.2) encQ encUnary := by dsimp [encQ]; fun_prop
      have hv' : ComputableInPolyTime (fun q : (MinBisectionInstance × ℕ) × ℕ => q.2)
        encQ encUnary := by dsimp [encQ]; fun_prop
      have hi : ComputableInPolyTime
          (fun q : (MinBisectionInstance × ℕ) × ℕ =>
            ((List.range q.1.1.graph.distinctVertices.length).filter fun w =>
              q.1.1.graph.adjBool (q.1.1.graph.distinctVertices.getD q.1.2 0)
                (q.1.1.graph.distinctVertices.getD w 0)).idxOf q.2) encQ encUnary :=
        ComputableInPolyTime.idxOfWithInput
          (hnbrs.comp (ComputableInPolyTime.fst (encPair encMinBisection encUnary) encUnary)) hv'
      have hj : ComputableInPolyTime
          (fun q : (MinBisectionInstance × ℕ) × ℕ =>
            ((List.range q.1.1.graph.distinctVertices.length).filter fun w =>
              q.1.1.graph.adjBool (q.1.1.graph.distinctVertices.getD q.2 0)
                (q.1.1.graph.distinctVertices.getD w 0)).idxOf q.1.2) encQ encUnary :=
        ComputableInPolyTime.idxOfWithInput
          (hnbrs.comp
            (((ComputableInPolyTime.fst encMinBisection encUnary).comp
              (ComputableInPolyTime.fst (encPair encMinBisection encUnary) encUnary)).prod hv'))
          hu'
      have hconst0 : ComputableInPolyTime (fun _ : (MinBisectionInstance × ℕ) × ℕ => 0)
          (encPair (encPair encMinBisection encUnary) encUnary) encUnary :=
        ComputableInPolyTime.const 0
      have hconst1 : ComputableInPolyTime (fun _ : (MinBisectionInstance × ℕ) × ℕ => 1)
          (encPair (encPair encMinBisection encUnary) encUnary) encUnary :=
        ComputableInPolyTime.const 1
      have ha_u := computableInPolyTime_torusVid_comp hK' hu' hi hi hconst0
      have ha_v := computableInPolyTime_torusVid_comp hK' hv' hj hj hconst0
      have hb_u := computableInPolyTime_torusVid_comp hK' hu' hi hi hconst1
      have hb_v := computableInPolyTime_torusVid_comp hK' hv' hj hj hconst1
      have hpair1 := ha_u.prod ha_v
      have hpair2 := hb_u.prod hb_v
      exact ComputableInPolyTime.cons' hpair1
        (ComputableInPolyTime.cons' hpair2 (ComputableInPolyTime.const []))
    have hgraph := encGraph_mk_polyTime hverts (ComputableInPolyTime.listAppend' hint hcross)
    have hbound : ComputableInPolyTime (fun x : MinBisectionInstance => 2 * x.bound)
        encMinBisection encNat := by fun_prop
    exact encMinBisection_mk_polyTime hgraph hbound
  unfold toThreeMinBisection
  have hn_u : ComputableInPolyTime (fun x : MinBisectionInstance => x.graph.distinctVertices.length)
      encMinBisection encUnary := by fun_prop
  have hn_b : ComputableInPolyTime (fun x : MinBisectionInstance => x.graph.distinctVertices.length)
      encMinBisection encNat := ComputableInPolyTime.unary_to_binary.comp hn_u
  have hc1 : ComputableInPolyTime (fun x : MinBisectionInstance =>
    x.graph.distinctVertices.length == 0)
      encMinBisection encBool := by
    exact (ComputableInPolyTime.decide_eq' hn_u (ComputableInPolyTime.const 0)).of_enc_eq fun x =>
      by cases h : (x.graph.distinctVertices.length == 0) <;> simp_all
  have hc2 : ComputableInPolyTime (fun x : MinBisectionInstance =>
    !(x.graph.distinctVertices.length % 2 == 0))
      encMinBisection encBool := by
    have hm : ComputableInPolyTime (fun x : MinBisectionInstance =>
      x.graph.distinctVertices.length % 2)
        encMinBisection encNat :=
      ComputableInPolyTime.binary_mod.comp' (hn_b.prod (ComputableInPolyTime.const 2))
    have heq : ComputableInPolyTime (fun x : MinBisectionInstance =>
        x.graph.distinctVertices.length % 2 == 0) encMinBisection encBool :=
      (ComputableInPolyTime.decide_eq' hm (ComputableInPolyTime.const 0)).of_enc_eq fun x => by
        cases h : (x.graph.distinctVertices.length % 2 == 0) <;> simp_all
    exact ComputableInPolyTime.bool_not.comp heq
  have hc3 : ComputableInPolyTime
      (fun x : MinBisectionInstance =>
        decide (x.graph.distinctVertices.length * x.graph.distinctVertices.length ≤ x.bound))
      encMinBisection encBool := by fun_prop
  exact ComputableInPolyTime.ite hc1 (ComputableInPolyTime.const threeYesInstance)
    (ComputableInPolyTime.ite hc2 (ComputableInPolyTime.const threeNoInstance)
      (ComputableInPolyTime.ite hc3 (ComputableInPolyTime.const threeYesInstance) hmain))




/-- Minority-set size and port-count bounds on a single cubic torus gadget `H_u`. -/
theorem torus_gadget_minority_bounds {K u degU : ℕ} (hK_ge : 8 ≤ K) (hdeg : degU < K)
    (A : Finset ℕ)
    (hA_sub : ∀ w ∈ A, w ∈ (Finset.range (4 * K * K)).image fun m => u * (4 * K * K) + m)
    (hA_le : A.card ≤ 2 * K * K)
    (hint_lt :
      let isInA (w : ℕ) : Bool := decide (w ∈ A)
      let rowCut (r : ℕ) : ℕ :=
        ((List.range K).filter fun c =>
          isInA (torusVid K u r c 0) != isInA (torusVid K u r c 2)).length +
        ((List.range K).filter fun c =>
          isInA (torusVid K u r c 2) != isInA (torusVid K u r ((c + 1) % K) 0)).length
      let colCut (c : ℕ) : ℕ :=
        ((List.range K).filter fun r =>
          isInA (torusVid K u r c 1) != isInA (torusVid K u r c 3)).length +
        ((List.range K).filter fun r =>
          isInA (torusVid K u r c 3) != isInA (torusVid K u ((r + 1) % K) c 1)).length
      let cdCut : ℕ :=
        ((List.range K).flatMap fun r => (List.range K).filter fun c =>
          isInA (torusVid K u r c 2) != isInA (torusVid K u r c 3)).length
      ((List.range K).map rowCut).sum + ((List.range K).map colCut).sum + cdCut < K / 2) :
    let isInA (w : ℕ) : Bool := decide (w ∈ A)
    let rowCut (r : ℕ) : ℕ :=
      ((List.range K).filter fun c =>
        isInA (torusVid K u r c 0) != isInA (torusVid K u r c 2)).length +
      ((List.range K).filter fun c =>
        isInA (torusVid K u r c 2) != isInA (torusVid K u r ((c + 1) % K) 0)).length
    let colCut (c : ℕ) : ℕ :=
      ((List.range K).filter fun r =>
        isInA (torusVid K u r c 1) != isInA (torusVid K u r c 3)).length +
      ((List.range K).filter fun r =>
        isInA (torusVid K u r c 3) != isInA (torusVid K u ((r + 1) % K) c 1)).length
    let cdCut : ℕ :=
      ((List.range K).flatMap fun r => (List.range K).filter fun c =>
        isInA (torusVid K u r c 2) != isInA (torusVid K u r c 3)).length
    let intCut := ((List.range K).map rowCut).sum + ((List.range K).map colCut).sum + cdCut
    A.card ≤ K * intCut ∧
      (((Finset.range degU).filter fun i => isInA (torusVid K u i i 0) = true).card +
       ((Finset.range degU).filter fun i => isInA (torusVid K u i i 1) = true).card ≤ intCut) := by
  classical
  dsimp only at hint_lt ⊢
  have hK_pos : 0 < K := by omega
  let Hu : Finset ℕ := (Finset.range (4 * K * K)).image fun m => u * (4 * K * K) + m
  let isInA (w : ℕ) : Bool := decide (w ∈ A)
  let rowCut (r : ℕ) : ℕ :=
    ((List.range K).filter fun c =>
      isInA (torusVid K u r c 0) != isInA (torusVid K u r c 2)).length +
    ((List.range K).filter fun c =>
      isInA (torusVid K u r c 2) != isInA (torusVid K u r ((c + 1) % K) 0)).length
  let colCut (c : ℕ) : ℕ :=
    ((List.range K).filter fun r =>
      isInA (torusVid K u r c 1) != isInA (torusVid K u r c 3)).length +
    ((List.range K).filter fun r =>
      isInA (torusVid K u r c 3) != isInA (torusVid K u ((r + 1) % K) c 1)).length
  let cdCut : ℕ :=
    ((List.range K).flatMap fun r => (List.range K).filter fun c =>
      isInA (torusVid K u r c 2) != isInA (torusVid K u r c 3)).length
  let intCut := ((List.range K).map rowCut).sum + ((List.range K).map colCut).sum + cdCut
  -- Classify rows and columns as full (in A), empty (outside A), or split
  let rowFull (r : ℕ) : Prop :=
    ∀ c < K, isInA (torusVid K u r c 0) = true ∧ isInA (torusVid K u r c 2) = true
  let rowEmpty (r : ℕ) : Prop :=
    ∀ c < K, isInA (torusVid K u r c 0) = false ∧ isInA (torusVid K u r c 2) = false
  let colFull (c : ℕ) : Prop :=
    ∀ r < K, isInA (torusVid K u r c 1) = true ∧ isInA (torusVid K u r c 3) = true
  let colEmpty (c : ℕ) : Prop :=
    ∀ r < K, isInA (torusVid K u r c 1) = false ∧ isInA (torusVid K u r c 3) = false
  let fR := ((Finset.range K).filter rowFull).card
  let eR := ((Finset.range K).filter rowEmpty).card
  let sR := ((Finset.range K).filter fun r => ¬ rowFull r ∧ ¬ rowEmpty r).card
  let fC := ((Finset.range K).filter colFull).card
  let eC := ((Finset.range K).filter colEmpty).card
  let sC := ((Finset.range K).filter fun c => ¬ colFull c ∧ ¬ colEmpty c).card
  have hpartR : fR + eR + sR = K := by
    have hdisj1 : Disjoint ((Finset.range K).filter rowFull)
      ((Finset.range K).filter rowEmpty) := by
      rw [Finset.disjoint_left]; intro r hr1 hr2
      have h0 := ((Finset.mem_filter.mp hr1).2 0 hK_pos).1
      have h1 := ((Finset.mem_filter.mp hr2).2 0 hK_pos).1
      rw [h0] at h1; exact Bool.noConfusion h1
    have hdisj2 : Disjoint (((Finset.range K).filter rowFull) ∪ ((Finset.range K).filter rowEmpty))
        ((Finset.range K).filter fun r => ¬ rowFull r ∧ ¬ rowEmpty r) := by
      rw [Finset.disjoint_left]; intro r hr1 hr2
      have hn := (Finset.mem_filter.mp hr2).2
      rcases Finset.mem_union.mp hr1 with h | h
      · exact hn.1 (Finset.mem_filter.mp h).2
      · exact hn.2 (Finset.mem_filter.mp h).2
    have hunion : ((Finset.range K).filter rowFull) ∪ ((Finset.range K).filter rowEmpty) ∪
        ((Finset.range K).filter fun r => ¬ rowFull r ∧
          ¬ rowEmpty r) = Finset.range K := by
      ext r; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro h; by_cases hf : rowFull r
        · exact Or.inl (Or.inl ⟨h, hf⟩)
        · by_cases he : rowEmpty r
          · exact Or.inl (Or.inr ⟨h, he⟩)
          · exact Or.inr ⟨h, hf, he⟩
    rw [← Finset.card_union_of_disjoint hdisj1, ← Finset.card_union_of_disjoint hdisj2,
      hunion, Finset.card_range]
  have hpartC : fC + eC + sC = K := by
    have hdisj1 : Disjoint ((Finset.range K).filter colFull)
      ((Finset.range K).filter colEmpty) := by
      rw [Finset.disjoint_left]; intro c hc1 hc2
      have h0 := ((Finset.mem_filter.mp hc1).2 0 hK_pos).1
      have h1 := ((Finset.mem_filter.mp hc2).2 0 hK_pos).1
      rw [h0] at h1; exact Bool.noConfusion h1
    have hdisj2 : Disjoint (((Finset.range K).filter colFull) ∪ ((Finset.range K).filter colEmpty))
        ((Finset.range K).filter fun c => ¬ colFull c ∧ ¬ colEmpty c) := by
      rw [Finset.disjoint_left]; intro c hc1 hc2
      have hn := (Finset.mem_filter.mp hc2).2
      rcases Finset.mem_union.mp hc1 with h | h
      · exact hn.1 (Finset.mem_filter.mp h).2
      · exact hn.2 (Finset.mem_filter.mp h).2
    have hunion : ((Finset.range K).filter colFull) ∪ ((Finset.range K).filter colEmpty) ∪
        ((Finset.range K).filter fun c => ¬ colFull c ∧
          ¬ colEmpty c) = Finset.range K := by
      ext c; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro h; by_cases hf : colFull c
        · exact Or.inl (Or.inl ⟨h, hf⟩)
        · by_cases he : colEmpty c
          · exact Or.inl (Or.inr ⟨h, he⟩)
          · exact Or.inr ⟨h, hf, he⟩
    rw [← Finset.card_union_of_disjoint hdisj1, ← Finset.card_union_of_disjoint hdisj2,
      hunion, Finset.card_range]
  have hsR_bound : 2 * sR ≤ ((List.range K).map (rowCut)).sum := by
    have hsum : ((List.range K).map (rowCut)).sum =
      ∑ r ∈ Finset.range K, rowCut r := by
      rw [sum_range_eq_list_sum]
    rw [hsum]
    have hge2 : ∀ r ∈ (Finset.range K).filter (fun r => ¬ rowFull r ∧
      ¬ rowEmpty r), 2 ≤ rowCut r := by
      intro r hr
      obtain ⟨hnotF, hnotE⟩ := (Finset.mem_filter.mp hr).2
      have h1 : ∃ c < K, isInA (torusVid K u r c 0) = false ∨
        isInA (torusVid K u r c 2) = false := by
        by_contra h; push Not at h
        exact hnotF fun c hc => ⟨Bool.eq_true_of_not_eq_false (h c hc).1,
          Bool.eq_true_of_not_eq_false (h c hc).2⟩
      have h2 : ∃ c < K, isInA (torusVid K u r c 0) = true ∨
        isInA (torusVid K u r c 2) = true := by
        by_contra h; push Not at h
        exact hnotE fun c hc => ⟨Bool.eq_false_of_not_eq_true (h c hc).1,
          Bool.eq_false_of_not_eq_true (h c hc).2⟩
      let A := fun k => if k % 2 =
        0 then isInA (torusVid K u r (k / 2) 0) else isInA (torusVid K u r (k / 2) 2)
      have hA1 : ∃ c < K, A (2 * c) = true ∨ A (2 * c + 1) = true := by
        obtain ⟨c, hc, h | h⟩ := h2
        · exact ⟨c, hc, Or.inl (by simp [A, h])⟩
        · exact ⟨c, hc, Or.inr (by simp [A, show (2 * c + 1) % 2 =
          1 by omega, show (2 * c + 1) / 2 = c by omega, h])⟩
      have hA2 : ∃ c < K, A (2 * c) = false ∨ A (2 * c + 1) = false := by
        obtain ⟨c, hc, h | h⟩ := h1
        · exact ⟨c, hc, Or.inl (by simp [A, h])⟩
        · exact ⟨c, hc, Or.inr (by simp [A, show (2 * c + 1) % 2 =
          1 by omega, show (2 * c + 1) / 2 = c by omega, h])⟩
      have hcut := cycle_cut_ge_two (by omega) A hA1 hA2
      have hEq : rowCut r =
          ((List.range K).filter fun c => A (2 * c) != A (2 * c + 1)).length +
          ((List.range K).filter fun c => A (2 * c + 1) != A (2 * ((c +
            1) % K))).length := by
        simp only [rowCut, A]; congr 2 <;> refine List.filter_congr fun c _ => ?_ <;>
          simp [show (2 * c + 1) % 2 = 1 by omega, show (2 * c + 1) / 2 = c by omega]
      omega
    calc
      2 * sR = ∑ _ ∈ (Finset.range K).filter (fun r => ¬ rowFull r ∧
        ¬ rowEmpty r), 2 := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ r ∈ (Finset.range K).filter (fun r => ¬ rowFull r ∧
        ¬ rowEmpty r), rowCut r :=
        Finset.sum_le_sum hge2
      _ ≤ ∑ r ∈ Finset.range K, rowCut r :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hsC_bound : 2 * sC ≤ ((List.range K).map (colCut)).sum := by
    have hsum : ((List.range K).map (colCut)).sum =
      ∑ c ∈ Finset.range K, colCut c := by
      rw [sum_range_eq_list_sum]
    rw [hsum]
    have hge2 : ∀ c ∈ (Finset.range K).filter (fun c => ¬ colFull c ∧
      ¬ colEmpty c), 2 ≤ colCut c := by
      intro c hc
      obtain ⟨hnotF, hnotE⟩ := (Finset.mem_filter.mp hc).2
      have h1 : ∃ r < K, isInA (torusVid K u r c 1) = false ∨
        isInA (torusVid K u r c 3) = false := by
        by_contra h; push Not at h
        exact hnotF fun r hr => ⟨Bool.eq_true_of_not_eq_false (h r hr).1,
          Bool.eq_true_of_not_eq_false (h r hr).2⟩
      have h2 : ∃ r < K, isInA (torusVid K u r c 1) = true ∨
        isInA (torusVid K u r c 3) = true := by
        by_contra h; push Not at h
        exact hnotE fun r hr => ⟨Bool.eq_false_of_not_eq_true (h r hr).1,
          Bool.eq_false_of_not_eq_true (h r hr).2⟩
      let A := fun k => if k % 2 =
        0 then isInA (torusVid K u (k / 2) c 1) else isInA (torusVid K u (k / 2) c 3)
      have hA1 : ∃ r < K, A (2 * r) = true ∨ A (2 * r + 1) = true := by
        obtain ⟨r, hr, h | h⟩ := h2
        · exact ⟨r, hr, Or.inl (by simp [A, h])⟩
        · exact ⟨r, hr, Or.inr (by simp [A, show (2 * r + 1) % 2 =
          1 by omega, show (2 * r + 1) / 2 = r by omega, h])⟩
      have hA2 : ∃ r < K, A (2 * r) = false ∨ A (2 * r + 1) = false := by
        obtain ⟨r, hr, h | h⟩ := h1
        · exact ⟨r, hr, Or.inl (by simp [A, h])⟩
        · exact ⟨r, hr, Or.inr (by simp [A, show (2 * r + 1) % 2 =
          1 by omega, show (2 * r + 1) / 2 = r by omega, h])⟩
      have hcut := cycle_cut_ge_two (by omega) A hA1 hA2
      have hEq : colCut c =
          ((List.range K).filter fun r => A (2 * r) != A (2 * r + 1)).length +
          ((List.range K).filter fun r => A (2 * r + 1) != A (2 * ((r +
            1) % K))).length := by
        simp only [colCut, A]; congr 2 <;> refine List.filter_congr fun r _ => ?_ <;>
          simp [show (2 * r + 1) % 2 = 1 by omega, show (2 * r + 1) / 2 = r by omega]
      omega
    calc
      2 * sC = ∑ _ ∈ (Finset.range K).filter (fun c => ¬ colFull c ∧
        ¬ colEmpty c), 2 := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ c ∈ (Finset.range K).filter (fun c => ¬ colFull c ∧
        ¬ colEmpty c), colCut c :=
        Finset.sum_le_sum hge2
      _ ≤ ∑ c ∈ Finset.range K, colCut c :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hcd_fe : fR * eC ≤ cdCut ∧ eR * fC ≤ cdCut := by
    have hprod_le : ∀ (P1 P2 : ℕ → Prop) [DecidablePred P1] [DecidablePred P2],
        (∀ r < K, ∀ c < K, P1 r → P2 c →
          (isInA (torusVid K u r c 2) != isInA (torusVid K u r c 3)) = true) →
        ((Finset.range K).filter P1).card * ((Finset.range K).filter P2).card ≤
          cdCut := by
      intro P1 P2 _ _ hP
      rw [← Finset.card_product]
      have hcd_eq : cdCut =
          ((List.range K).flatMap fun r =>
            ((List.range K).filter fun c =>
              isInA (torusVid K u r c 2) != isInA (torusVid K u r c 3)).map fun c => (r,
                c)).length := by
        unfold cdCut
        rw [List.length_flatMap, List.length_flatMap]
        congr 1; refine List.map_congr_left fun r _ => by simp
      rw [hcd_eq]
      have hnd_cd : ((List.range K).flatMap fun r =>
          ((List.range K).filter fun c =>
            isInA (torusVid K u r c 2) != isInA (torusVid K u r c 3)).map fun c => (r,
              c)).Nodup := by
        rw [List.nodup_flatMap]
        refine ⟨fun r _ => (List.nodup_range.filter _).map (fun _ _ h => (Prod.mk.inj h).2), ?_⟩
        rw [List.pairwise_iff_getElem]
        intro i j hi hj hij p hp1 hp2
        simp only [List.mem_map, List.mem_filter, List.getElem_range] at hp1 hp2
        obtain ⟨_, _, rfl⟩ := hp1; obtain ⟨_, _, h2⟩ := hp2
        have := (Prod.mk.inj h2).1; omega
      rw [← List.toFinset_card_of_nodup hnd_cd]
      refine Finset.card_le_card fun ⟨r, c⟩ hrc => ?_
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hrc
      simp only [List.mem_toFinset, List.mem_flatMap, List.mem_map, List.mem_filter,
        List.mem_range, Prod.mk.injEq]
      exact ⟨r, hrc.1.1, c, ⟨hrc.2.1, hP r hrc.1.1 c hrc.2.1 hrc.1.2 hrc.2.2⟩, rfl, rfl⟩
    refine ⟨hprod_le rowFull colEmpty fun r hr c hc h1 h2 => by simp [(h1 c hc).2,
      (h2 r hr).2],
            hprod_le rowEmpty colFull fun r hr c hc h1 h2 => by simp [(h1 c hc).2,
              (h2 r hr).2]⟩
  -- Prove `fR = 0 ∧ fC = 0`!
  have hcd_lt : cdCut < K / 2 := by
    have : (List.map rowCut (List.range K)).sum + (List.map colCut (List.range K)).sum + cdCut <
        K / 2 := hint_lt
    omega
  have hsR_lt : 2 * sR < K / 2 := by
    have : (List.map rowCut (List.range K)).sum + (List.map colCut (List.range K)).sum + cdCut <
        K / 2 := hint_lt
    omega
  have hsC_lt : 2 * sC < K / 2 := by
    have : (List.map rowCut (List.range K)).sum + (List.map colCut (List.range K)).sum + cdCut <
        K / 2 := hint_lt
    omega
  have hfR_zero : fR = 0 ∧ fC = 0 := by
    by_contra hne0
    have hboth : 0 < fR ∧ 0 < fC := by
      by_cases hfR : 0 < fR
      · have heC_lt : eC < K / 2 := by
          have : 1 * eC ≤ fR * eC := Nat.mul_le_mul_right eC hfR
          omega
        have : 0 < fC := by omega
        exact ⟨hfR, this⟩
      · have hfC : 0 < fC := by omega
        have heR_lt : eR < K / 2 := by
          have : 1 * eR ≤ eR * fC := by have := Nat.mul_le_mul_left eR hfC; linarith
          omega
        have : 0 < fR := by omega
        exact ⟨this, hfC⟩
    have heC_lt : eC < K / 2 := by
      have := Nat.mul_le_mul_right eC hboth.1; omega
    have hfC_big : K / 4 < fC := by omega
    have heR_le1 : eR ≤ 1 := by
      by_contra h2
      have : 2 * (K / 4 + 1) ≤ eR * fC := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hfR_big : K / 4 < fR := by omega
    have heC_le1 : eC ≤ 1 := by
      by_contra h2
      have : (K / 4 + 1) * 2 ≤ fR * eC := Nat.mul_le_mul (by omega) (by omega)
      omega
    -- Now count vertices in A: at least `2 * K * fR + 2 * K * fC > 2 * K * K`!
    let rowVerts := ((Finset.range K).filter rowFull).biUnion fun r =>
      (Finset.range K).biUnion fun c => {torusVid K u r c 0, torusVid K u r c 2}
    let colVerts := ((Finset.range K).filter colFull).biUnion fun c =>
      (Finset.range K).biUnion fun r => {torusVid K u r c 1, torusVid K u r c 3}
    have hdisj_rc : Disjoint rowVerts colVerts := by
      rw [Finset.disjoint_left]; intro w hw1 hw2
      simp only [rowVerts, colVerts, Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_range,
        Finset.mem_insert, Finset.mem_singleton] at hw1 hw2
      obtain ⟨r1, ⟨hr1, _⟩, c1, hc1, rfl | rfl⟩ := hw1 <;>
        obtain ⟨c2, ⟨hc2, _⟩, r2, hr2, h2 | h2⟩ := hw2 <;>
        (have := (torusVid_injective hK_pos hr1 hc1 (by omega) hr2 hc2 (by omega) h2).2.2.2; omega)
    have hsub_A : rowVerts ∪ colVerts ⊆ A := by
      intro w hw
      simp only [Finset.mem_union, rowVerts, colVerts, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
          Finset.mem_singleton] at hw
      rcases hw with ⟨r, ⟨hr, hrf⟩, c, hc, rfl | rfl⟩ | ⟨c, ⟨hc, hcf⟩, r, hr, rfl | rfl⟩
      · exact of_decide_eq_true (hrf c hc).1
      · exact of_decide_eq_true (hrf c hc).2
      · exact of_decide_eq_true (hcf r hr).1
      · exact of_decide_eq_true (hcf r hr).2
    have hrow_card : rowVerts.card = 2 * K * fR := by
      rw [Finset.card_biUnion]
      · have hper : ∀ r ∈ (Finset.range K).filter rowFull,
            ((Finset.range K).biUnion fun c => {torusVid K u r c 0,
              torusVid K u r c 2}).card = 2 * K := by
          intro r hr
          have hr' := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
          rw [Finset.card_biUnion]
          · have h2 : ∀ c ∈ Finset.range K, ({torusVid K u r c 0,
            torusVid K u r c 2} : Finset ℕ).card = 2 := by
              intro c hc
              exact Finset.card_pair fun h => by
                have := (torusVid_injective hK_pos hr' (Finset.mem_range.mp hc) (by omega)
                  hr' (Finset.mem_range.mp hc) (by omega) h).2.2.2; omega
            rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range,
              smul_eq_mul]; ring
          · intro c1 hc1 c2 hc2 hne
            change Disjoint _ _; rw [Finset.disjoint_left]; intro w hw1 hw2
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw1 hw2
            rcases hw1 with rfl | rfl <;> rcases hw2 with h | h <;>
              exact hne (torusVid_injective hK_pos hr' (Finset.mem_range.mp hc1)
                (by omega)
                hr' (Finset.mem_range.mp hc2) (by omega) h).2.2.1
        rw [Finset.sum_congr rfl hper, Finset.sum_const, smul_eq_mul, mul_comm]
      · intro r1 hr1 r2 hr2 hne
        change Disjoint _ _; rw [Finset.disjoint_left]; intro w hw1 hw2
        have hr1' := Finset.mem_range.mp (Finset.mem_filter.mp hr1).1
        have hr2' := Finset.mem_range.mp (Finset.mem_filter.mp hr2).1
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_insert,
          Finset.mem_singleton] at hw1 hw2
        obtain ⟨c1, hc1, rfl | rfl⟩ := hw1 <;> obtain ⟨c2, hc2, h | h⟩ := hw2 <;>
          exact hne (torusVid_injective hK_pos hr1' hc1 (by omega) hr2' hc2 (by omega) h).2.1
    have hcol_card : colVerts.card = 2 * K * fC := by
      rw [Finset.card_biUnion]
      · have hper : ∀ c ∈ (Finset.range K).filter colFull,
            ((Finset.range K).biUnion fun r => {torusVid K u r c 1,
              torusVid K u r c 3}).card = 2 * K := by
          intro c hc
          have hc' := Finset.mem_range.mp (Finset.mem_filter.mp hc).1
          rw [Finset.card_biUnion]
          · have h2 : ∀ r ∈ Finset.range K, ({torusVid K u r c 1,
            torusVid K u r c 3} : Finset ℕ).card = 2 := by
              intro r hr
              exact Finset.card_pair fun h => by
                have := (torusVid_injective hK_pos (Finset.mem_range.mp hr) hc' (by omega)
                  (Finset.mem_range.mp hr) hc' (by omega) h).2.2.2; omega
            rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range,
              smul_eq_mul]; ring
          · intro r1 hr1 r2 hr2 hne
            change Disjoint _ _; rw [Finset.disjoint_left]; intro w hw1 hw2
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw1 hw2
            rcases hw1 with rfl | rfl <;> rcases hw2 with h | h <;>
              exact hne (torusVid_injective hK_pos (Finset.mem_range.mp hr1) hc' (by omega)
                (Finset.mem_range.mp hr2) hc' (by omega) h).2.1
        rw [Finset.sum_congr rfl hper, Finset.sum_const, smul_eq_mul, mul_comm]
      · intro c1 hc1 c2 hc2 hne
        change Disjoint _ _; rw [Finset.disjoint_left]; intro w hw1 hw2
        have hc1' := Finset.mem_range.mp (Finset.mem_filter.mp hc1).1
        have hc2' := Finset.mem_range.mp (Finset.mem_filter.mp hc2).1
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_insert,
          Finset.mem_singleton] at hw1 hw2
        obtain ⟨r1, hr1, rfl | rfl⟩ := hw1 <;> obtain ⟨r2, hr2, h | h⟩ := hw2 <;>
          exact hne (torusVid_injective hK_pos hr1 hc1' (by omega) hr2 hc2' (by omega) h).2.2.1
    have hcard_big := Finset.card_le_card hsub_A
    rw [Finset.card_union_of_disjoint hdisj_rc, hrow_card, hcol_card] at hcard_big
    have hsum_gt : K < fR + fC := by omega
    have hmul_gt : 2 * K * (K + 1) ≤ 2 * K * (fR + fC) := Nat.mul_le_mul_left (2 * K) hsum_gt
    have hlin : 2 * K * (fR + fC) = 2 * K * fR + 2 * K * fC := by ring
    have hlt_k : 2 * K * K < 2 * K * (K + 1) := by nlinarith
    omega
  -- Since fR = 0 and fC = 0, every vertex of A lies in a split row or split column!
  have hA_sub_split : A ⊆
      (((Finset.range K).filter fun r => ¬ rowFull r ∧ ¬ rowEmpty r).biUnion fun r =>
        (Finset.range K).biUnion fun c => {torusVid K u r c 0, torusVid K u r c 2}) ∪
      (((Finset.range K).filter fun c => ¬ colFull c ∧ ¬ colEmpty c).biUnion fun c =>
        (Finset.range K).biUnion fun r => {torusVid K u r c 1, torusVid K u r c 3}) := by
    intro w hw
    have hwH : w ∈ Hu := hA_sub w hw
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hwH
    rw [Finset.mem_range] at hm
    set t := m % 4; set q1 := m / 4; set c := q1 % K; set r := q1 / K
    have ht : t < 4 := Nat.mod_lt _ (by omega)
    have hc : c < K := Nat.mod_lt _ hK_pos
    have hr : r < K := by
      have hq1 : q1 < K * K := Nat.div_lt_of_lt_mul (by linarith : m < 4 * (K * K))
      exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hq1)
    have hm_eq : u * (4 * K * K) + m = torusVid K u r c t := by
      unfold torusVid
      have h1 : m = q1 * 4 + t := by omega
      have h2 : q1 = r * K + c := by
        dsimp only [r, c]
        have := Nat.div_add_mod q1 K; rw [Nat.mul_comm] at this; exact this.symm
      rw [h1, h2]; ring
    rw [hm_eq] at hw ⊢
    have hwA : isInA (torusVid K u r c t) = true := decide_eq_true hw
    have ht4 : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
    rcases ht4 with h | h | h | h
    · rw [h] at hwA ⊢
      rw [Finset.mem_union]; left
      have hnotF : ¬ rowFull r := fun h => by
        have : r ∈ (Finset.range K).filter rowFull :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, h⟩
        have := Finset.card_pos.mpr ⟨r, this⟩; omega
      have hnotE : ¬ rowEmpty r := fun h => by
        have := (h c hc).1; rw [hwA] at this; exact Bool.noConfusion this
      exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr,
        hnotF, hnotE⟩,
        Finset.mem_biUnion.mpr ⟨c, Finset.mem_range.mpr hc, by simp⟩⟩
    · rw [h] at hwA ⊢
      rw [Finset.mem_union]; right
      have hnotF : ¬ colFull c := fun h => by
        have : c ∈ (Finset.range K).filter colFull :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc, h⟩
        have := Finset.card_pos.mpr ⟨c, this⟩; omega
      have hnotE : ¬ colEmpty c := fun h => by
        have := (h r hr).1; rw [hwA] at this; exact Bool.noConfusion this
      exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc,
        hnotF, hnotE⟩,
        Finset.mem_biUnion.mpr ⟨r, Finset.mem_range.mpr hr, by simp⟩⟩
    · rw [h] at hwA ⊢
      rw [Finset.mem_union]; left
      have hnotF : ¬ rowFull r := fun h => by
        have : r ∈ (Finset.range K).filter rowFull :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, h⟩
        have := Finset.card_pos.mpr ⟨r, this⟩; omega
      have hnotE : ¬ rowEmpty r := fun h => by
        have := (h c hc).2; rw [hwA] at this; exact Bool.noConfusion this
      exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr,
        hnotF, hnotE⟩,
        Finset.mem_biUnion.mpr ⟨c, Finset.mem_range.mpr hc, by simp⟩⟩
    · rw [h] at hwA ⊢
      rw [Finset.mem_union]; right
      have hnotF : ¬ colFull c := fun h => by
        have : c ∈ (Finset.range K).filter colFull :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc, h⟩
        have := Finset.card_pos.mpr ⟨c, this⟩; omega
      have hnotE : ¬ colEmpty c := fun h => by
        have := (h r hr).2; rw [hwA] at this; exact Bool.noConfusion this
      exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc,
        hnotF, hnotE⟩,
        Finset.mem_biUnion.mpr ⟨r, Finset.mem_range.mpr hr, by simp⟩⟩
  have hA_card : (A).card ≤ K * intCut := by
    have h1 := Finset.card_le_card hA_sub_split
    have h2 := Finset.card_union_le
      (((Finset.range K).filter fun r => ¬ rowFull r ∧ ¬ rowEmpty r).biUnion fun r =>
        (Finset.range K).biUnion fun c => {torusVid K u r c 0, torusVid K u r c 2})
      (((Finset.range K).filter fun c => ¬ colFull c ∧ ¬ colEmpty c).biUnion fun c =>
        (Finset.range K).biUnion fun r => {torusVid K u r c 1, torusVid K u r c 3})
    have h3 : (((Finset.range K).filter fun r => ¬ rowFull r ∧
      ¬ rowEmpty r).biUnion fun r =>
        (Finset.range K).biUnion fun c => {torusVid K u r c 0, torusVid K u r c 2}).card ≤
          2 * K * sR := by
      refine (Finset.card_biUnion_le).trans ?_
      have : ∀ r ∈ (Finset.range K).filter (fun r => ¬ rowFull r ∧ ¬ rowEmpty r),
          ((Finset.range K).biUnion fun c => ({torusVid K u r c 0,
            torusVid K u r c 2} : Finset ℕ)).card ≤ 2 * K := fun r _ => by
        refine (Finset.card_biUnion_le).trans ?_
        calc
          ∑ c ∈ Finset.range K, ({torusVid K u r c 0, torusVid K u r c 2} : Finset ℕ).card
              ≤ ∑ _ ∈ Finset.range K, 2 := Finset.sum_le_sum fun _ _ => Finset.card_le_two
          _ = 2 * K := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring
      calc
        ∑ r ∈ (Finset.range K).filter (fun r => ¬ rowFull r ∧ ¬ rowEmpty r),
            ((Finset.range K).biUnion fun c => ({torusVid K u r c 0,
              torusVid K u r c 2} : Finset ℕ)).card
            ≤ ∑ _ ∈ (Finset.range K).filter (fun r => ¬ rowFull r ∧
              ¬ rowEmpty r), 2 * K :=
          Finset.sum_le_sum this
        _ = 2 * K * sR := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have h4 : (((Finset.range K).filter fun c => ¬ colFull c ∧
      ¬ colEmpty c).biUnion fun c =>
        (Finset.range K).biUnion fun r => {torusVid K u r c 1, torusVid K u r c 3}).card ≤
          2 * K * sC := by
      refine (Finset.card_biUnion_le).trans ?_
      have : ∀ c ∈ (Finset.range K).filter (fun c => ¬ colFull c ∧ ¬ colEmpty c),
          ((Finset.range K).biUnion fun r => ({torusVid K u r c 1,
            torusVid K u r c 3} : Finset ℕ)).card ≤ 2 * K := fun c _ => by
        refine (Finset.card_biUnion_le).trans ?_
        calc
          ∑ r ∈ Finset.range K, ({torusVid K u r c 1, torusVid K u r c 3} : Finset ℕ).card
              ≤ ∑ _ ∈ Finset.range K, 2 := Finset.sum_le_sum fun _ _ => Finset.card_le_two
          _ = 2 * K := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring
      calc
        ∑ c ∈ (Finset.range K).filter (fun c => ¬ colFull c ∧ ¬ colEmpty c),
            ((Finset.range K).biUnion fun r => ({torusVid K u r c 1,
              torusVid K u r c 3} : Finset ℕ)).card
            ≤ ∑ _ ∈ (Finset.range K).filter (fun c => ¬ colFull c ∧
              ¬ colEmpty c), 2 * K :=
          Finset.sum_le_sum this
        _ = 2 * K * sC := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have h5 : 2 * sR + 2 * sC ≤ intCut := by omega
    nlinarith
  have hports_le :
      ((Finset.range degU).filter fun i => isInA (torusVid K u i i 0) =
        true).card +
      ((Finset.range degU).filter fun i => isInA (torusVid K u i i 1) =
        true).card ≤ intCut := by
    have hpa : ((Finset.range degU).filter fun i => isInA (torusVid K u i i 0) =
      true).card ≤ sR := by
      refine Finset.card_le_card fun i hi => ?_
      simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
      have hiK : i < K := hi.1.trans (hdeg)
      refine ⟨hiK, fun hF => ?_, fun hE => ?_⟩
      · have := Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hiK,
        hF⟩⟩; omega
      · have := (hE i hiK).1; rw [hi.2] at this; exact Bool.noConfusion this
    have hpb : ((Finset.range degU).filter fun i => isInA (torusVid K u i i 1) =
      true).card ≤ sC := by
      refine Finset.card_le_card fun i hi => ?_
      simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
      have hiK : i < K := hi.1.trans (hdeg)
      refine ⟨hiK, fun hF => ?_, fun hE => ?_⟩
      · have := Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hiK,
        hF⟩⟩; omega
      · have := (hE i hiK).1; rw [hi.2] at this; exact Bool.noConfusion this
    omega
  exact ⟨hA_card, hports_le⟩

end CslibFrontier.Complexity.MinBisection
