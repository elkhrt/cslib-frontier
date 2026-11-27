module

public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing
public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Logics.Propositional.CNF.ModelCount
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD

/-!
# 3-Dimensional Matching and Planar 3-Dimensional Matching

This module defines the classical decision problems **3-Dimensional Matching** (`3-DM`) and
**Planar 3-Dimensional Matching** (`Planar 3-DM`) and proves that `3-DM` is NP-complete under
standard Lean axioms via Karp's / Garey–Johnson's polynomial-time reduction from `3-SAT`.

An instance `x : Cslib.Complexity.ThreeDMInstance` specifies a common cardinality `x.size`
(encoded in unary, matching the explicit listing of finite sets `X`, `Y`, `Z` of size `α`) and a
list of triples `x.triples` with coordinates in `ℕ` (encoded in binary). A finite subset
`M : Finset ThreeDMTriple` is a valid 3-dimensional matching
(`Cslib.Complexity.IsThreeDMatching`) when every triple in `M` belongs to `x.triples`, has all
three coordinates strictly below `x.size`, `M.card = x.size`, and distinct triples in `M` disagree
in all three coordinates.

The bipartite incidence graph `x.incidenceGraph` has `3 * x.size` element vertices (`X`, `Y`, `Z`)
and `x.triples.length` triple vertices, with an edge joining each element to every triple
containing it. An instance belongs to `Cslib.Complexity.PlanarThreeDM` when it is a yes-instance
of `3-DM` whose incidence graph admits a planar orthogonal drawing
(`Cslib.Complexity.Graph.IsPlanarOrthogonalDrawing`).

## Main definitions

* `Cslib.Complexity.ThreeDMTriple`, `Cslib.Complexity.encThreeDMTriple`: triples `(x, y, z)`
  and their binary encoding.
* `Cslib.Complexity.ThreeDMInstance`, `Cslib.Complexity.encThreeDM`: `3-DM` instances and
  their encoding (unary set size, binary triple list).
* `Cslib.Complexity.IsThreeDMatching`, `Cslib.Complexity.ThreeDM`: valid 3-dimensional
  matchings and the `3-DM` decision problem.
* `Cslib.Complexity.ThreeDMInstance.incidenceGraph`, `Cslib.Complexity.PlanarThreeDM`:
  the bipartite element-triple incidence graph and Planar `3-DM`.
* `Cslib.Complexity.ThreeDM.ofThreeSAT`: the polynomial-time reduction from `3-SAT` to `3-DM`.

## Main results

* `Cslib.Complexity.ThreeDM_mem_NP`: `3-DM` belongs to `NP`.
* `Cslib.Complexity.ThreeDM.ofThreeSAT_mem_iff`: correctness of the reduction from `3-SAT`.
* `Cslib.Complexity.polyTimeReducible_ThreeSAT_ThreeDM`: `ThreeSAT` reduces to `ThreeDM` in
  polynomial time.
* `Cslib.Complexity.ThreeDM_npHard`, `Cslib.Complexity.ThreeDM_npComplete`: **`3-DM` is
  NP-complete** under standard Lean axioms.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-- A triple `(x, y, z)` of natural-number element indices in a `3-DM` instance. -/
@[ext]
structure ThreeDMTriple where
  /-- Element index in the first set `X`. -/
  x : ℕ
  /-- Element index in the second set `Y`. -/
  y : ℕ
  /-- Element index in the third set `Z`. -/
  z : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Binary encoding of a `ThreeDMTriple` as `(x, (y, z))`. -/
enc_structure encThreeDMTriple : ThreeDMTriple where
  x : encNat, y : encNat, z : encNat

/-- An instance of `3-Dimensional Matching`: finite sets `X`, `Y`, `Z` of common cardinality
`size` (identified with `Fin size`) and a list of candidate triples `triples ⊆ X × Y × Z`. -/
@[ext]
structure ThreeDMInstance where
  /-- The common cardinality `α = |X| = |Y| = |Z|`. -/
  size : ℕ
  /-- Candidate triples `(x, y, z)` with `x, y, z < size`. -/
  triples : List ThreeDMTriple
  deriving DecidableEq, Repr, Inhabited

/-- Encoding of a `ThreeDMInstance`: unary `size` (reflecting the explicit finite sets `X, Y, Z`)
followed by binary-encoded triples. -/
enc_structure encThreeDM : ThreeDMInstance where
  size : encUnary, triples : (encList encThreeDMTriple)

/-- `M` is a valid 3-dimensional matching for `inst`: `M` is a subset of `inst.triples` of
cardinality `inst.size`, every triple in `M` has coordinates `< inst.size`, and distinct triples
in `M` are pairwise disjoint in all three coordinates. -/
def IsThreeDMatching (inst : ThreeDMInstance) (M : Finset ThreeDMTriple) : Prop :=
  (∀ t ∈ M, t ∈ inst.triples ∧ t.x < inst.size ∧ t.y < inst.size ∧ t.z < inst.size) ∧
    M.card = inst.size ∧
    ∀ t₁ ∈ M, ∀ t₂ ∈ M, t₁ ≠ t₂ → t₁.x ≠ t₂.x ∧ t₁.y ≠ t₂.y ∧ t₁.z ≠ t₂.z

/-- Characterization of `IsThreeDMatching`. -/
theorem isThreeDMatching_iff (inst : ThreeDMInstance) (M : Finset ThreeDMTriple) :
    IsThreeDMatching inst M ↔
      (∀ t ∈ M, t ∈ inst.triples ∧ t.x < inst.size ∧ t.y < inst.size ∧ t.z < inst.size) ∧
        M.card = inst.size ∧
        ∀ t₁ ∈ M, ∀ t₂ ∈ M, t₁ ≠ t₂ → t₁.x ≠ t₂.x ∧ t₁.y ≠ t₂.y ∧ t₁.z ≠ t₂.z :=
  Iff.rfl

/-- In a valid 3-dimensional matching, every element of `X`, `Y`, and `Z` is covered at most once
(in fact, by a bijection with `Fin inst.size`). -/
theorem IsThreeDMatching.x_injOn {inst : ThreeDMInstance} {M : Finset ThreeDMTriple}
    (hM : IsThreeDMatching inst M) : Set.InjOn ThreeDMTriple.x (M : Set ThreeDMTriple) := by
  intro t₁ ht₁ t₂ ht₂ hx
  by_contra hne
  exact (hM.2.2 t₁ ht₁ t₂ ht₂ hne).1 hx

/-- Distinct triples in a valid matching have distinct `y`-coordinates. -/
theorem IsThreeDMatching.y_injOn {inst : ThreeDMInstance} {M : Finset ThreeDMTriple}
    (hM : IsThreeDMatching inst M) : Set.InjOn ThreeDMTriple.y (M : Set ThreeDMTriple) := by
  intro t₁ ht₁ t₂ ht₂ hy
  by_contra hne
  exact (hM.2.2 t₁ ht₁ t₂ ht₂ hne).2.1 hy

/-- Distinct triples in a valid matching have distinct `z`-coordinates. -/
theorem IsThreeDMatching.z_injOn {inst : ThreeDMInstance} {M : Finset ThreeDMTriple}
    (hM : IsThreeDMatching inst M) : Set.InjOn ThreeDMTriple.z (M : Set ThreeDMTriple) := by
  intro t₁ ht₁ t₂ ht₂ hz
  by_contra hne
  exact (hM.2.2 t₁ ht₁ t₂ ht₂ hne).2.2 hz

/-- Every valid 3-dimensional matching covers every `x < inst.size` by a unique triple. -/
theorem IsThreeDMatching.existsUnique_x {inst : ThreeDMInstance} {M : Finset ThreeDMTriple}
    (hM : IsThreeDMatching inst M) {a : ℕ} (ha : a < inst.size) :
    ∃! t ∈ M, t.x = a := by
  have hsub : M.image ThreeDMTriple.x ⊆ Finset.range inst.size := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_range.mpr (hM.1 t ht).2.1
  have hcard : (M.image ThreeDMTriple.x).card = (Finset.range inst.size).card := by
    rw [Finset.card_image_of_injOn hM.x_injOn, hM.2.1, Finset.card_range]
  have heq : M.image ThreeDMTriple.x = Finset.range inst.size :=
    Finset.eq_of_subset_of_card_le hsub hcard.ge
  obtain ⟨t, ht, htx⟩ := Finset.mem_image.mp (heq ▸ Finset.mem_range.mpr ha)
  exact ⟨t, ⟨ht, htx⟩, fun t' ⟨ht', ht'x⟩ => hM.x_injOn ht' ht (ht'x.trans htx.symm)⟩

/-- Every valid 3-dimensional matching covers every `y < inst.size` by a unique triple. -/
theorem IsThreeDMatching.existsUnique_y {inst : ThreeDMInstance} {M : Finset ThreeDMTriple}
    (hM : IsThreeDMatching inst M) {b : ℕ} (hb : b < inst.size) :
    ∃! t ∈ M, t.y = b := by
  have hsub : M.image ThreeDMTriple.y ⊆ Finset.range inst.size := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_range.mpr (hM.1 t ht).2.2.1
  have hcard : (M.image ThreeDMTriple.y).card = (Finset.range inst.size).card := by
    rw [Finset.card_image_of_injOn hM.y_injOn, hM.2.1, Finset.card_range]
  have heq : M.image ThreeDMTriple.y = Finset.range inst.size :=
    Finset.eq_of_subset_of_card_le hsub hcard.ge
  obtain ⟨t, ht, hty⟩ := Finset.mem_image.mp (heq ▸ Finset.mem_range.mpr hb)
  exact ⟨t, ⟨ht, hty⟩, fun t' ⟨ht', ht'y⟩ => hM.y_injOn ht' ht (ht'y.trans hty.symm)⟩

/-- Every valid 3-dimensional matching covers every `z < inst.size` by a unique triple. -/
theorem IsThreeDMatching.existsUnique_z {inst : ThreeDMInstance} {M : Finset ThreeDMTriple}
    (hM : IsThreeDMatching inst M) {c : ℕ} (hc : c < inst.size) :
    ∃! t ∈ M, t.z = c := by
  have hsub : M.image ThreeDMTriple.z ⊆ Finset.range inst.size := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_range.mpr (hM.1 t ht).2.2.2
  have hcard : (M.image ThreeDMTriple.z).card = (Finset.range inst.size).card := by
    rw [Finset.card_image_of_injOn hM.z_injOn, hM.2.1, Finset.card_range]
  have heq : M.image ThreeDMTriple.z = Finset.range inst.size :=
    Finset.eq_of_subset_of_card_le hsub hcard.ge
  obtain ⟨t, ht, htz⟩ := Finset.mem_image.mp (heq ▸ Finset.mem_range.mpr hc)
  exact ⟨t, ⟨ht, htz⟩, fun t' ⟨ht', ht'z⟩ => hM.z_injOn ht' ht (ht'z.trans htz.symm)⟩

/-- The **3-Dimensional Matching** (`3-DM`) decision problem: instances admitting a valid
3-dimensional matching of size `inst.size`. -/
def ThreeDM : Set ThreeDMInstance :=
  {inst | ∃ M : Finset ThreeDMTriple, IsThreeDMatching inst M}

/-- Membership in `ThreeDM`. -/
theorem mem_ThreeDM_iff (inst : ThreeDMInstance) :
    inst ∈ ThreeDM ↔ ∃ M : Finset ThreeDMTriple, IsThreeDMatching inst M :=
  Iff.rfl

/-- The bipartite element-triple incidence graph of a `3-DM` instance:
vertices `0 .. size - 1` represent `X`, `size .. 2 * size - 1` represent `Y`,
`2 * size .. 3 * size - 1` represent `Z`, and `3 * size + k` represents the `k`-th triple in
`inst.triples`, with edges joining each in-bounds coordinate of a triple to its triple vertex. -/
def ThreeDMInstance.incidenceGraph (inst : ThreeDMInstance) : Graph :=
  ⟨List.range (3 * inst.size + inst.triples.length),
    inst.triples.zipIdx.flatMap fun (t, k) =>
      (if t.x < inst.size then [(t.x, 3 * inst.size + k)] else []) ++
      (if t.y < inst.size then [(inst.size + t.y, 3 * inst.size + k)] else []) ++
      (if t.z < inst.size then [(2 * inst.size + t.z, 3 * inst.size + k)] else [])⟩

/-- Every edge in `inst.incidenceGraph` joins an element vertex (`< 3 * inst.size`) to a triple
vertex (`∈ [3 * inst.size, 3 * inst.size + inst.triples.length)`). -/
theorem ThreeDMInstance.incidenceGraph_bipartite {inst : ThreeDMInstance} {e : ℕ × ℕ}
    (he : e ∈ inst.incidenceGraph.edges) :
    e.1 < 3 * inst.size ∧ 3 * inst.size ≤ e.2 ∧
      e.2 < 3 * inst.size + inst.triples.length := by
  simp only [incidenceGraph, List.mem_flatMap, List.mem_append] at he
  obtain ⟨⟨t, k⟩, hmem, hcase⟩ := he
  have hk : k < inst.triples.length := by
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
    simp only [List.length_zipIdx] at hi
    simp only [List.getElem_zipIdx, Nat.zero_add, Prod.mk.injEq] at hget
    omega
  rcases hcase with (hx | hy) | hz
  · dsimp only at hx; split_ifs at hx with hlt
    · simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by omega, by omega⟩
    · simp at hx
  · dsimp only at hy; split_ifs at hy with hlt
    · simp only [List.mem_singleton] at hy; subst hy; exact ⟨by omega, by omega, by omega⟩
    · simp at hy
  · dsimp only at hz; split_ifs at hz with hlt
    · simp only [List.mem_singleton] at hz; subst hz; exact ⟨by omega, by omega, by omega⟩
    · simp at hz

/-- Every edge endpoint of `inst.incidenceGraph` is a declared vertex. -/
theorem ThreeDMInstance.incidenceGraph_endpoints {inst : ThreeDMInstance} {e : ℕ × ℕ}
    (he : e ∈ inst.incidenceGraph.edges) :
    e.1 ∈ inst.incidenceGraph.vertices ∧ e.2 ∈ inst.incidenceGraph.vertices := by
  obtain ⟨h1, _, h2⟩ := inst.incidenceGraph_bipartite he
  simp only [incidenceGraph, List.mem_range]
  exact ⟨by omega, h2⟩

/-- `inst.incidenceGraph` is loopless. -/
theorem ThreeDMInstance.incidenceGraph_loopless {inst : ThreeDMInstance} {e : ℕ × ℕ}
    (he : e ∈ inst.incidenceGraph.edges) : e.1 ≠ e.2 := by
  obtain ⟨h1, h2, _⟩ := inst.incidenceGraph_bipartite he
  omega

/-- **Planar 3-Dimensional Matching** (`Planar 3-DM`): yes-instances of `3-DM` whose bipartite
element-triple incidence graph admits a planar orthogonal drawing. -/
def PlanarThreeDM : Set ThreeDMInstance :=
  {inst | inst ∈ ThreeDM ∧ ∃ d, Graph.IsPlanarOrthogonalDrawing inst.incidenceGraph d}

/-- Characterization of `PlanarThreeDM`. -/
theorem mem_PlanarThreeDM_iff (inst : ThreeDMInstance) :
    inst ∈ PlanarThreeDM ↔
      inst ∈ ThreeDM ∧ ∃ d, Graph.IsPlanarOrthogonalDrawing inst.incidenceGraph d :=
  Iff.rfl

/-! ### Membership of `3-DM` in `NP` -/

private def checkMatching (p : ThreeDMInstance × List ThreeDMTriple) : Bool :=
  decide (p.2.length = p.1.size) &&
  p.2.all (fun t =>
    decide (t.x < p.1.size) && decide (t.y < p.1.size) && decide (t.z < p.1.size)) &&
  (p.2.map ThreeDMTriple.x).Nodup &&
  (p.2.map ThreeDMTriple.y).Nodup &&
  (p.2.map ThreeDMTriple.z).Nodup

private theorem computableInPolyTime_checkMatching :
    ComputableInPolyTime checkMatching
      (encWithEntries encThreeDM encThreeDMTriple) encBool := by
  unfold checkMatching
  have hnodup : ComputableInPolyTime (fun l : List ℕ => decide l.Nodup)
      (encList encNat) encBool := by
    have h : (fun l : List ℕ => decide l.Nodup) =
        fun l => l.all (fun a => decide (l.count a ≤ 1)) := by
      funext l
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, List.all_eq_true, List.nodup_iff_count_le_one]
      exact ⟨fun h a _ => h a, fun h a => if ha : a ∈ l then h a ha else by
        rw [List.count_eq_zero.mpr ha]; omega⟩
    rw [h]
    fun_prop
  have hlen : ComputableInPolyTime
      (fun p : ThreeDMInstance × List ThreeDMTriple => decide (p.2.length = p.1.size))
      (encWithEntries encThreeDM encThreeDMTriple) encBool := by
    have h : (fun p : ThreeDMInstance × List ThreeDMTriple => decide (p.2.length = p.1.size)) =
        fun p => (p.2.length == p.1.size) := rfl
    rw [h]
    fun_prop
  have hall : ComputableInPolyTime
      (fun p : ThreeDMInstance × List ThreeDMTriple =>
        p.2.all (fun t =>
          decide (t.x < p.1.size) && decide (t.y < p.1.size) && decide (t.z < p.1.size)))
      (encWithEntries encThreeDM encThreeDMTriple) encBool := by
    apply allWithInput (by fun_prop)
    have hb : ∀ (f : (ThreeDMInstance × List ThreeDMTriple) × ThreeDMTriple → ℕ),
        ComputableInPolyTime f
          (encPair (encWithEntries encThreeDM encThreeDMTriple) encThreeDMTriple) encNat →
        ComputableInPolyTime
          (fun q : (ThreeDMInstance × List ThreeDMTriple) × ThreeDMTriple =>
            decide (f q < q.1.1.size))
          (encPair (encWithEntries encThreeDM encThreeDMTriple) encThreeDMTriple) encBool := by
      intro f hf
      have hs : ComputableInPolyTime
          (fun q : (ThreeDMInstance × List ThreeDMTriple) × ThreeDMTriple => q.1.1.size)
          (encPair (encWithEntries encThreeDM encThreeDMTriple) encThreeDMTriple) encNat :=
        unary_to_binary.comp (by fun_prop)
      exact binary_lt' hf hs
    exact bool_and' (bool_and' (hb _ (by fun_prop)) (hb _ (by fun_prop))) (hb _ (by fun_prop))
  have hx : ComputableInPolyTime
      (fun p : ThreeDMInstance × List ThreeDMTriple => decide (p.2.map ThreeDMTriple.x).Nodup)
      (encWithEntries encThreeDM encThreeDMTriple) encBool :=
    hnodup.comp (by fun_prop)
  have hy : ComputableInPolyTime
      (fun p : ThreeDMInstance × List ThreeDMTriple => decide (p.2.map ThreeDMTriple.y).Nodup)
      (encWithEntries encThreeDM encThreeDMTriple) encBool :=
    hnodup.comp (by fun_prop)
  have hz : ComputableInPolyTime
      (fun p : ThreeDMInstance × List ThreeDMTriple => decide (p.2.map ThreeDMTriple.z).Nodup)
      (encWithEntries encThreeDM encThreeDMTriple) encBool :=
    hnodup.comp (by fun_prop)
  exact bool_and' (bool_and' (bool_and' (bool_and' hlen hall) hx) hy) hz

private theorem checkMatching_iff (inst : ThreeDMInstance) (l : List ThreeDMTriple)
    (hl : l.Nodup) (hsub : ∀ t ∈ l, t ∈ inst.triples) :
    checkMatching (inst, l) = true ↔ IsThreeDMatching inst l.toFinset := by
  simp only [checkMatching, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    isThreeDMatching_iff, List.mem_toFinset, List.toFinset_card_of_nodup hl]
  constructor
  · rintro ⟨⟨⟨⟨hlen, hbounds⟩, hnx⟩, hny⟩, hnz⟩
    refine ⟨fun t ht => ⟨hsub t ht, (hbounds t ht).1.1, (hbounds t ht).1.2, (hbounds t ht).2⟩,
      hlen, fun t₁ ht₁ t₂ ht₂ hne => ?_⟩
    have hinj := fun (f : ThreeDMTriple → ℕ) (hnf : (l.map f).Nodup) (heq : f t₁ = f t₂) =>
      hne ((List.nodup_map_iff_inj_on hl).mp hnf t₁ ht₁ t₂ ht₂ heq)
    exact ⟨hinj _ hnx, hinj _ hny, hinj _ hnz⟩
  · rintro ⟨hmem, hcard, hdisj⟩
    refine ⟨⟨⟨⟨hcard, fun t ht => ⟨⟨(hmem t ht).2.1, (hmem t ht).2.2.1⟩, (hmem t ht).2.2.2⟩⟩,
      (List.nodup_map_iff_inj_on hl).mpr fun t₁ ht₁ t₂ ht₂ heq => ?_⟩,
      (List.nodup_map_iff_inj_on hl).mpr fun t₁ ht₁ t₂ ht₂ heq => ?_⟩,
      (List.nodup_map_iff_inj_on hl).mpr fun t₁ ht₁ t₂ ht₂ heq => ?_⟩
    · by_contra hne; exact (hdisj t₁ ht₁ t₂ ht₂ hne).1 heq
    · by_contra hne; exact (hdisj t₁ ht₁ t₂ ht₂ hne).2.1 heq
    · by_contra hne; exact (hdisj t₁ ht₁ t₂ ht₂ hne).2.2 heq

/-- **`3-DM` belongs to `NP`**: a certificate selects the subset of triples forming a matching. -/
theorem ThreeDM_mem_NP : ThreeDM ∈ NP encThreeDM := by
  convert mem_NP_of_subsetWitness (enc := encThreeDM) (encγ := encThreeDMTriple)
    (vs := ThreeDMInstance.triples) (check := checkMatching)
    (P := IsThreeDMatching)
    (by fun_prop) computableInPolyTime_checkMatching
    (fun inst l hl hsub => checkMatching_iff inst l hl hsub) using 1
  ext inst
  simp only [ThreeDM, Set.mem_ofPred_eq, IsThreeDMatching]
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M, fun t ht => (hM.1 t ht).1, hM⟩
  · rintro ⟨M, -, hM⟩
    exact ⟨M, hM⟩

/-! ### Polynomial-time reduction from `3-SAT` to `3-DM` -/

namespace ThreeDM

/-- Fixed yes-instance of `3-DM` (empty sets, `size = 0`). -/
private def yesInstance : ThreeDMInstance := ⟨0, []⟩

/-- Fixed no-instance of `3-DM` (`size = 1`, no triples). -/
private def noInstance : ThreeDMInstance := ⟨1, []⟩

private theorem yesInstance_mem : yesInstance ∈ ThreeDM :=
  ⟨∅, by simp [IsThreeDMatching, yesInstance]⟩

private theorem noInstance_notMem : noInstance ∉ ThreeDM := by
  rintro ⟨M, hsub_M, hcard, -⟩
  have hsub : M = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun t ht => by
    have := (hsub_M t ht).1
    simp [noInstance] at this
  simp [noInstance, hsub] at hcard

/-- Check whether `φ` has width `≤ 3` and every clause is nonempty. -/
private def syntaxOK (φ : CNF ℕ) : Bool :=
  φ.all fun c => decide (1 ≤ c.length) && decide (c.length ≤ 3)

private theorem syntaxOK_iff (φ : CNF ℕ) :
    syntaxOK φ = true ↔ ∀ c ∈ φ, 1 ≤ c.length ∧ c.length ≤ 3 := by
  simp [syntaxOK]

/-- Core reduction from a nonempty `3-CNF` formula `φ` with `n = φ.distinctVars.length ≥ 1`
variables and `m = φ.length ≥ 1` clauses to a `3-DM` instance of size `2 * n * m`:

* `X`: `n * m` variable-core elements `i * m + j`, `m` clause-core elements `n * m + j`, and
  `(n - 1) * m` garbage-core elements `n * m + m + k`.
* `Y`: same layout as `X`.
* `Z`: `2 * n * m` literal-tip elements: `2 * (i * m + j)` (true-tip `u_i[j]`) and
  `2 * (i * m + j) + 1` (false-tip `ū_i[j]`).
* Variable triples: for each `i < n, j < m`, true triple `(i*m + j, i*m + j, 2*(i*m + j))` and
  false triple `(i*m + (j + 1) % m, i*m + j, 2*(i*m + j) + 1)`.
* Clause triples: for each clause `j < m` and literal `(v, pos)` in `φ[j]` with `i = idxOf v`,
  triple `(n*m + j, n*m + j, 2*(i*m + j) + (if pos then 1 else 0))`.
* Garbage triples: for each `k < (n - 1) * m` and `w < 2 * n * m`, triple
  `(n*m + m + k, n*m + m + k, w)`. -/
private def buildCore (φ : CNF ℕ) : ThreeDMInstance :=
  let vs := φ.distinctVars
  let n := vs.length
  let m := φ.length
  let nm := n * m
  let size := 2 * nm
  let varTriples : List ThreeDMTriple :=
    (List.range n).flatMap fun i =>
      (List.range m).flatMap fun j =>
        [⟨i * m + j, i * m + j, 2 * (i * m + j)⟩,
         ⟨i * m + (j + 1) % m, i * m + j, 2 * (i * m + j) + 1⟩]
  let clauseTriples : List ThreeDMTriple :=
    φ.zipIdx.flatMap fun (c, j) =>
      c.map fun l =>
        let i := vs.idxOf l.1
        ⟨nm + j, nm + j, 2 * (i * m + j) + if l.2 then 1 else 0⟩
  let garbageTriples : List ThreeDMTriple :=
    (List.range ((n - 1) * m)).flatMap fun k =>
      (List.range size).map fun w =>
        ⟨nm + m + k, nm + m + k, w⟩
  ⟨size, varTriples ++ clauseTriples ++ garbageTriples⟩

/-- The polynomial-time reduction `ThreeSAT → ThreeDM`. -/
def ofThreeSAT (φ : CNF ℕ) : ThreeDMInstance :=
  if φ.isEmpty then yesInstance
  else if syntaxOK φ then buildCore φ
  else noInstance

private theorem computableInPolyTime_syntaxOK :
    ComputableInPolyTime syntaxOK encCNF encBool := by
  unfold syntaxOK encCNF
  fun_prop

private theorem computableInPolyTime_buildCore :
    ComputableInPolyTime buildCore encCNF encThreeDM := by
  have hvs : ComputableInPolyTime (CNF.distinctVars (V := ℕ)) encCNF (encList encNat) :=
    CNF.computableInPolyTime_distinctVars encNat
  have hn : ComputableInPolyTime (fun φ : CNF ℕ => φ.distinctVars.length) encCNF encUnary := by
    have h := CNF.computableInPolyTime_numVars encNat
    have heq : (fun φ : CNF ℕ => φ.distinctVars.length) = fun φ => φ.numVars :=
      funext CNF.length_distinctVars
    rw [heq]; exact h
  have hm : ComputableInPolyTime (fun φ : CNF ℕ => φ.length) encCNF encUnary := by
    unfold encCNF; fun_prop
  have hnm : ComputableInPolyTime (fun φ : CNF ℕ => φ.distinctVars.length * φ.length)
      encCNF encUnary :=
    unary_mul' hn hm
  have hsz : ComputableInPolyTime (fun φ : CNF ℕ => 2 * (φ.distinctVars.length * φ.length))
      encCNF encUnary :=
    unary_mul' (const 2) hnm
  -- Build unary triple lists first, then convert coordinates to binary
  have hvarU : ComputableInPolyTime
      (fun φ : CNF ℕ =>
        let n := φ.distinctVars.length
        let m := φ.length
        (List.range n).flatMap fun i =>
          (List.range m).flatMap fun j =>
            [⟨i * m + j, i * m + j, 2 * (i * m + j)⟩,
             ⟨i * m + (j + 1) % m, i * m + j, 2 * (i * m + j) + 1⟩])
      encCNF (encList encThreeDMTriple) := by
    have hinner : ComputableInPolyTime
        (fun q : (CNF ℕ × ℕ) × ℕ =>
          let m := q.1.1.length
          let i := q.1.2
          let j := q.2
          ([⟨i * m + j, i * m + j, 2 * (i * m + j)⟩,
            ⟨i * m + (j + 1) % m, i * m + j, 2 * (i * m + j) + 1⟩] : List ThreeDMTriple))
        (encPair (encPair encCNF encUnary) encUnary) (encList encThreeDMTriple) := by
      have hm' : ComputableInPolyTime
          (fun q : (CNF ℕ × ℕ) × ℕ => q.1.1.length)
          (encPair (encPair encCNF encUnary) encUnary) encUnary :=
        hm.comp (fst _ _).fst'
      have hi' : ComputableInPolyTime
          (fun q : (CNF ℕ × ℕ) × ℕ => q.1.2)
          (encPair (encPair encCNF encUnary) encUnary) encUnary :=
        (fst _ _).snd'
      have hj' : ComputableInPolyTime
          (fun q : (CNF ℕ × ℕ) × ℕ => q.2)
          (encPair (encPair encCNF encUnary) encUnary) encUnary :=
        snd _ _
      have himj : ComputableInPolyTime
          (fun q : (CNF ℕ × ℕ) × ℕ => q.1.2 * q.1.1.length + q.2)
          (encPair (encPair encCNF encUnary) encUnary) encUnary :=
        unary_add' (unary_mul' hi' hm') hj'
      have hmod : ComputableInPolyTime
          (fun q : (CNF ℕ × ℕ) × ℕ => q.1.2 * q.1.1.length + (q.2 + 1) % q.1.1.length)
          (encPair (encPair encCNF encUnary) encUnary) encNat :=
        binary_add' (binary_mul' (unary_to_binary.comp hi') (unary_to_binary.comp hm'))
          (binary_mod' (unary_to_binary.comp (unary_add' hj' (const 1)))
            (unary_to_binary.comp hm'))
      have h2 : ComputableInPolyTime
          (fun q : (CNF ℕ × ℕ) × ℕ => 2 * (q.1.2 * q.1.1.length + q.2))
          (encPair (encPair encCNF encUnary) encUnary) encUnary :=
        unary_mul' (const 2) himj
      have h2p1 : ComputableInPolyTime
          (fun q : (CNF ℕ × ℕ) × ℕ => 2 * (q.1.2 * q.1.1.length + q.2) + 1)
          (encPair (encPair encCNF encUnary) encUnary) encUnary :=
        unary_add' h2 (const 1)
      have ht1 : ComputableInPolyTime
          (fun q : (CNF ℕ × ℕ) × ℕ =>
            (⟨q.1.2 * q.1.1.length + q.2, q.1.2 * q.1.1.length + q.2,
              2 * (q.1.2 * q.1.1.length + q.2)⟩ : ThreeDMTriple))
          (encPair (encPair encCNF encUnary) encUnary) encThreeDMTriple :=
        encThreeDMTriple_mk_polyTime (unary_to_binary.comp himj) (unary_to_binary.comp himj)
          (unary_to_binary.comp h2)
      have ht2 : ComputableInPolyTime
          (fun q : (CNF ℕ × ℕ) × ℕ =>
            (⟨q.1.2 * q.1.1.length + (q.2 + 1) % q.1.1.length, q.1.2 * q.1.1.length + q.2,
              2 * (q.1.2 * q.1.1.length + q.2) + 1⟩ : ThreeDMTriple))
          (encPair (encPair encCNF encUnary) encUnary) encThreeDMTriple :=
        encThreeDMTriple_mk_polyTime hmod (unary_to_binary.comp himj)
          (unary_to_binary.comp h2p1)
      exact cons' ht1 (cons' ht2 (const []))
    have hmid : ComputableInPolyTime
        (fun p : CNF ℕ × ℕ =>
          (List.range p.1.length).flatMap fun j =>
            [⟨p.2 * p.1.length + j, p.2 * p.1.length + j, 2 * (p.2 * p.1.length + j)⟩,
             ⟨p.2 * p.1.length + (j + 1) % p.1.length, p.2 * p.1.length + j,
              2 * (p.2 * p.1.length + j) + 1⟩])
        (encPair encCNF encUnary) (encList encThreeDMTriple) :=
      flatMapWithInput (range.comp (hm.comp (fst _ _))) hinner
    exact flatMapWithInput (range.comp hn) hmid
  have hclU : ComputableInPolyTime
      (fun φ : CNF ℕ =>
        let vs := φ.distinctVars
        let m := φ.length
        let nm := vs.length * m
        φ.zipIdx.flatMap fun (c, j) =>
          c.map fun l =>
            let i := vs.idxOf l.1
            ⟨nm + j, nm + j, 2 * (i * m + j) + if l.2 then 1 else 0⟩)
      encCNF (encList encThreeDMTriple) := by
    have hlit : ComputableInPolyTime
        (fun q : (CNF ℕ × (Clause ℕ × ℕ)) × Literal ℕ =>
          let φ := q.1.1
          let j := q.1.2.2
          let l := q.2
          let vs := φ.distinctVars
          let m := φ.length
          let nm := vs.length * m
          let i := vs.idxOf l.1
          (⟨nm + j, nm + j, 2 * (i * m + j) + if l.2 then 1 else 0⟩ : ThreeDMTriple))
        (encPair (encPair encCNF (encPair (encList (encPair encNat encBool)) encUnary))
          (encPair encNat encBool))
        encThreeDMTriple := by
      have hφ : ComputableInPolyTime
          (fun q : (CNF ℕ × (Clause ℕ × ℕ)) × Literal ℕ => q.1.1)
          (encPair (encPair encCNF (encPair (encList (encPair encNat encBool)) encUnary))
            (encPair encNat encBool)) encCNF :=
        (fst _ _).fst'
      have hj : ComputableInPolyTime
          (fun q : (CNF ℕ × (Clause ℕ × ℕ)) × Literal ℕ => q.1.2.2)
          (encPair (encPair encCNF (encPair (encList (encPair encNat encBool)) encUnary))
            (encPair encNat encBool)) encUnary :=
        (fst _ _).snd'.snd'
      have hi : ComputableInPolyTime
          (fun q : (CNF ℕ × (Clause ℕ × ℕ)) × Literal ℕ => q.1.1.distinctVars.idxOf q.2.1)
          (encPair (encPair encCNF (encPair (encList (encPair encNat encBool)) encUnary))
            (encPair encNat encBool)) encUnary :=
        idxOfWithInput (hvs.comp hφ) ((fst encNat encBool).comp (snd _ _))
      have hnmj : ComputableInPolyTime
          (fun q : (CNF ℕ × (Clause ℕ × ℕ)) × Literal ℕ =>
            q.1.1.distinctVars.length * q.1.1.length + q.1.2.2)
          (encPair (encPair encCNF (encPair (encList (encPair encNat encBool)) encUnary))
            (encPair encNat encBool)) encUnary :=
        unary_add' (hnm.comp hφ) hj
      have hpos : ComputableInPolyTime
          (fun q : (CNF ℕ × (Clause ℕ × ℕ)) × Literal ℕ => if q.2.2 then (1 : ℕ) else 0)
          (encPair (encPair encCNF (encPair (encList (encPair encNat encBool)) encUnary))
            (encPair encNat encBool)) encUnary :=
        ite ((snd encNat encBool).comp (snd _ _)) (const 1) (const 0)
      have hz : ComputableInPolyTime
          (fun q : (CNF ℕ × (Clause ℕ × ℕ)) × Literal ℕ =>
            2 * (q.1.1.distinctVars.idxOf q.2.1 * q.1.1.length + q.1.2.2) +
              if q.2.2 then 1 else 0)
          (encPair (encPair encCNF (encPair (encList (encPair encNat encBool)) encUnary))
            (encPair encNat encBool)) encUnary :=
        unary_add' (unary_mul' (const 2) (unary_add' (unary_mul' hi (hm.comp hφ)) hj)) hpos
      exact encThreeDMTriple_mk_polyTime (unary_to_binary.comp hnmj) (unary_to_binary.comp hnmj)
        (unary_to_binary.comp hz)
    have hzip : ComputableInPolyTime (fun φ : CNF ℕ => φ.zipIdx)
        encCNF (encList (encPair (encList (encPair encNat encBool)) encUnary)) := by
      unfold encCNF
      exact zipIdx _
    exact flatMapWithInput hzip (mapWithInput ((fst _ _).comp (snd _ _)) hlit)
  have hgarbU : ComputableInPolyTime
      (fun φ : CNF ℕ =>
        let n := φ.distinctVars.length
        let m := φ.length
        let nm := n * m
        let size := 2 * nm
        (List.range ((n - 1) * m)).flatMap fun k =>
          (List.range size).map fun w =>
            ⟨nm + m + k, nm + m + k, w⟩)
      encCNF (encList encThreeDMTriple) := by
    have hinner : ComputableInPolyTime
        (fun q : (CNF ℕ × ℕ) × ℕ =>
          let nm := q.1.1.distinctVars.length * q.1.1.length
          let m := q.1.1.length
          (⟨nm + m + q.1.2, nm + m + q.1.2, q.2⟩ : ThreeDMTriple))
        (encPair (encPair encCNF encUnary) encUnary) encThreeDMTriple := by
      have hcoord : ComputableInPolyTime
          (fun q : (CNF ℕ × ℕ) × ℕ =>
            q.1.1.distinctVars.length * q.1.1.length + q.1.1.length + q.1.2)
          (encPair (encPair encCNF encUnary) encUnary) encUnary :=
        unary_add' (unary_add' (hnm.comp (fst _ _).fst') (hm.comp (fst _ _).fst')) (fst _ _).snd'
      exact encThreeDMTriple_mk_polyTime (unary_to_binary.comp hcoord)
        (unary_to_binary.comp hcoord) (unary_to_binary.comp (snd _ _))
    have hmid : ComputableInPolyTime
        (fun p : CNF ℕ × ℕ =>
          (List.range (2 * (p.1.distinctVars.length * p.1.length))).map fun w =>
            ⟨p.1.distinctVars.length * p.1.length + p.1.length + p.2,
             p.1.distinctVars.length * p.1.length + p.1.length + p.2, w⟩)
        (encPair encCNF encUnary) (encList encThreeDMTriple) :=
      mapWithInput (range.comp (hsz.comp (fst _ _))) hinner
    exact flatMapWithInput (range.comp (unary_mul' (unary_sub' hn (const 1)) hm)) hmid
  exact encThreeDM_mk_polyTime hsz (listAppend' (listAppend' hvarU hclU) hgarbU)

/-- `ThreeDM.ofThreeSAT` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_ofThreeSAT :
    ComputableInPolyTime ofThreeSAT encCNF encThreeDM := by
  unfold ofThreeSAT
  have hemp : ComputableInPolyTime (fun φ : CNF ℕ => φ.isEmpty) encCNF encBool := by
    unfold encCNF; fun_prop
  exact ite hemp (const yesInstance)
    (ite computableInPolyTime_syntaxOK computableInPolyTime_buildCore (const noInstance))

/-- Helper: in a valid matching of `buildCore φ`, every variable core `i * m + j` is covered by
either its true triple or its false triple, and for a fixed variable `i`, the choice is uniform
across all `j < m`. -/
private theorem mem_buildCore_var_cases {φ : CNF ℕ} {t : ThreeDMTriple}
    (ht : t ∈ (buildCore φ).triples) (hi : t.y < φ.distinctVars.length * φ.length) :
    ∃ i < φ.distinctVars.length, ∃ j < φ.length,
      (t = ⟨i * φ.length + j, i * φ.length + j, 2 * (i * φ.length + j)⟩) ∨
      (t = ⟨i * φ.length + (j + 1) % φ.length, i * φ.length + j,
            2 * (i * φ.length + j) + 1⟩) := by
  simp only [buildCore, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at ht
  rcases ht with (⟨i, hi', j, hj', hcase⟩ | ⟨⟨c, j⟩, -, l, -, hcl⟩) | ⟨k, -, w, -, hg⟩
  · exact ⟨i, hi', j, hj', hcase⟩
  · subst hcl; dsimp only at hi; omega
  · subst hg; dsimp only at hi; omega

/-- Helper: every triple of `buildCore φ` covering clause-core `y = n * m + j` comes from a literal
of clause `j`. -/
private theorem mem_buildCore_clause_cases {φ : CNF ℕ} {j : ℕ} (hj : j < φ.length)
    {t : ThreeDMTriple} (ht : t ∈ (buildCore φ).triples)
    (hy : t.y = φ.distinctVars.length * φ.length + j) :
    ∃ l ∈ φ[j], t = ⟨φ.distinctVars.length * φ.length + j,
      φ.distinctVars.length * φ.length + j,
      2 * (φ.distinctVars.idxOf l.1 * φ.length + j) + if l.2 then 1 else 0⟩ := by
  simp only [buildCore, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at ht
  rcases ht with (⟨i, hi', j', hj', hcase⟩ | ⟨⟨c, j'⟩, hmem, l, hl, hcl⟩) | ⟨k, -, w, -, hg⟩
  · rcases hcase with rfl | rfl <;>
    · dsimp only at hy
      have : i * φ.length + j' < φ.distinctVars.length * φ.length := by
        calc i * φ.length + j' < i * φ.length + φ.length := by omega
          _ = (i + 1) * φ.length := by ring
          _ ≤ φ.distinctVars.length * φ.length := Nat.mul_le_mul_right _ (by omega)
      omega
  · subst hcl; dsimp only at hy
    have hjj : j = j' := by omega
    subst hjj
    have hcj : c = φ[j] := by
      obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hmem
      simp only [List.length_zipIdx] at hidx
      simp only [List.getElem_zipIdx, Nat.zero_add, Prod.mk.injEq] at hget
      obtain ⟨hcj, hidx_eq⟩ := hget
      subst hidx_eq
      exact hcj.symm
    subst hcj
    exact ⟨l, hl, rfl⟩
  · subst hg; dsimp only at hy; omega

/-- Backward correctness: a valid `3-DM` of `buildCore φ` yields a satisfying assignment of `φ`. -/
private theorem satisfiable_of_buildCore_mem {φ : CNF ℕ} (hne : φ ≠ [])
    (hsyn : ∀ c ∈ φ, 1 ≤ c.length ∧ c.length ≤ 3)
    (hmem : buildCore φ ∈ ThreeDM) : φ.Satisfiable := by
  classical
  obtain ⟨M, hM⟩ := hmem
  set vs := φ.distinctVars
  set n := vs.length
  set m := φ.length
  have hm_pos : 0 < m := List.length_pos_of_ne_nil hne
  have h0_mem : φ[0] ∈ φ := List.getElem_mem hm_pos
  have hn_pos : 0 < n := by
    obtain ⟨l, hl⟩ := List.exists_mem_of_length_pos (show 0 < φ[0].length by
      linarith [(hsyn _ h0_mem).1])
    exact List.length_pos_of_mem (CNF.mem_distinctVars.mpr (CNF.mem_vars.mpr ⟨_, h0_mem, l.2, hl⟩))
  -- Define `σ v := decide (∃ t ∈ M, t.y = vs.idxOf v * m + 0 ∧ t.z = 2 * (vs.idxOf v * m + 0))`
  let σ : ℕ → Bool := fun v =>
    decide (⟨vs.idxOf v * m, vs.idxOf v * m, 2 * (vs.idxOf v * m)⟩ ∈ M)
  have hmul_div_mod : ∀ {a b c d : ℕ}, b < m → d < m → a * m + b = c * m + d → a = c ∧ b = d := by
    intro a b c d hb hd heq
    have hq := congrArg (· / m) heq
    have hr := congrArg (· % m) heq
    rw [Nat.mul_comm a m, Nat.mul_comm c m, Nat.mul_add_div hm_pos, Nat.mul_add_div hm_pos,
      Nat.div_eq_of_lt hb, Nat.div_eq_of_lt hd] at hq
    rw [Nat.mul_comm a m, Nat.mul_comm c m, Nat.mul_add_mod, Nat.mul_add_mod,
      Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hd] at hr
    exact ⟨by omega, hr⟩
  -- If any `j₀ < m` has the false triple in `M`, then every `j < m` has the false triple in `M`.
  have hfalse_prop : ∀ i < n, ∀ j₀ < m,
      ⟨i * m + (j₀ + 1) % m, i * m + j₀, 2 * (i * m + j₀) + 1⟩ ∈ M →
      ∀ j < m, ⟨i * m + (j + 1) % m, i * m + j, 2 * (i * m + j) + 1⟩ ∈ M := by
    intro i hi j₀ hj₀ hstart
    have hlt_nm : ∀ j < m, i * m + j < n * m := fun j hj => by
      calc i * m + j < (i + 1) * m := by ring_nf; omega
        _ ≤ n * m := Nat.mul_le_mul_right _ (by omega)
    have hlt_sz : ∀ j < m, i * m + j < 2 * (n * m) := fun j hj => by
      have := hlt_nm j hj; omega
    have hstep_y : ∀ j < m,
        ⟨i * m + j, i * m + j, 2 * (i * m + j)⟩ ∈ M ∨
        ⟨i * m + (j + 1) % m, i * m + j, 2 * (i * m + j) + 1⟩ ∈ M := by
      intro j hj
      obtain ⟨t, ⟨htM, hty⟩, -⟩ := hM.existsUnique_y (hlt_sz j hj)
      obtain ⟨i', hi', j', hj', hcase⟩ := mem_buildCore_var_cases (hM.1 t htM).1 (hty ▸ hlt_nm j hj)
      have hij : i' * m + j' = i * m + j := by rcases hcase with rfl | rfl <;> exact hty
      obtain ⟨rfl, rfl⟩ := hmul_div_mod hj' hj hij
      rcases hcase with rfl | rfl
      · exact Or.inl htM
      · exact Or.inr htM
    -- Stepping `(j₀ + d) % m` for `d = 0, 1, ..., m - 1` visits all `j < m`.
    have hwalk : ∀ d : ℕ,
        ⟨i * m + ((j₀ + d) % m + 1) % m, i * m + (j₀ + d) % m,
          2 * (i * m + (j₀ + d) % m) + 1⟩ ∈ M := by
      intro d
      induction d with
      | zero => simpa [Nat.mod_eq_of_lt hj₀] using hstart
      | succ k ih =>
        set r := (j₀ + k) % m
        have hr : r < m := Nat.mod_lt _ hm_pos
        set r' := (r + 1) % m
        have hr' : r' < m := Nat.mod_lt _ hm_pos
        have hreq : (j₀ + (k + 1)) % m = r' := by
          simp only [r', r, ← Nat.add_assoc, Nat.mod_add_mod]
        rw [hreq]
        rcases hstep_y r' hr' with hT | hF
        · exfalso
          have hne : (⟨i * m + r', i * m + r, 2 * (i * m + r) + 1⟩ : ThreeDMTriple) ≠
              ⟨i * m + r', i * m + r', 2 * (i * m + r')⟩ := by
            intro heq
            have h1 := congrArg ThreeDMTriple.z heq
            dsimp at h1; omega
          exact (hM.2.2 _ ih _ hT hne).1 rfl
        · exact hF
    intro j hj
    have hd : (j₀ + (m + j - j₀)) % m = j := by
      rw [show j₀ + (m + j - j₀) = m + j by omega, Nat.add_mod_left, Nat.mod_eq_of_lt hj]
    simpa [hd] using hwalk (m + j - j₀)
  have hvar_alt : ∀ i < n,
      (∀ j < m, ⟨i * m + j, i * m + j, 2 * (i * m + j)⟩ ∈ M) ∨
      (∀ j < m, ⟨i * m + (j + 1) % m, i * m + j, 2 * (i * m + j) + 1⟩ ∈ M) := by
    intro i hi
    by_cases hex : ∃ j₀ < m, ⟨i * m + (j₀ + 1) % m, i * m + j₀, 2 * (i * m + j₀) + 1⟩ ∈ M
    · obtain ⟨j₀, hj₀, hstart⟩ := hex
      exact Or.inr (hfalse_prop i hi j₀ hj₀ hstart)
    · left
      intro j hj
      have hlt_nm : i * m + j < n * m := by
        calc i * m + j < (i + 1) * m := by ring_nf; omega
          _ ≤ n * m := Nat.mul_le_mul_right _ (by omega)
      obtain ⟨t, ⟨htM, hty⟩, -⟩ := hM.existsUnique_y (show i * m + j < 2 * (n * m) by omega)
      obtain ⟨i', hi', j', hj', hcase⟩ := mem_buildCore_var_cases (hM.1 t htM).1 (hty ▸ hlt_nm)
      have hij : i' * m + j' = i * m + j := by rcases hcase with rfl | rfl <;> exact hty
      obtain ⟨rfl, rfl⟩ := hmul_div_mod hj hj' hij.symm
      rcases hcase with rfl | rfl
      · exact htM
      · exact absurd ⟨j, hj, htM⟩ hex
  -- Now verify `σ` satisfies every clause of `φ`!
  refine ⟨σ, ?_⟩
  simp only [CNF.eval, List.all_eq_true, Clause.eval, List.any_eq_true]
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  have hcl_sz : n * m + j < 2 * (n * m) := by
    have : 1 * m ≤ n * m := Nat.mul_le_mul_right m (by omega)
    omega
  obtain ⟨t, ⟨htM, hty⟩, -⟩ := hM.existsUnique_y hcl_sz
  obtain ⟨l, hl, rfl⟩ := mem_buildCore_clause_cases hj (hM.1 t htM).1 hty
  refine ⟨l, hl, ?_⟩
  set i := vs.idxOf l.1
  have hi : i < n := List.idxOf_lt_length_of_mem
    (CNF.mem_distinctVars.mpr (CNF.mem_vars.mpr ⟨_, hc, l.2, hl⟩))
  rcases hvar_alt i hi with hTrue | hFalse
  · -- Variable `i` chose all true triples, so `σ l.1 = true` and `2*(i*m+j)` is used;
    -- hence `l.2` MUST be `true` (otherwise `t.z = 2*(i*m+j)` collides with the true triple!).
    have hσ : σ l.1 = true := by simp only [σ, decide_eq_true_eq]; simpa [i] using hTrue 0 hm_pos
    cases hpol : l.2
    · exfalso
      have hT := hTrue j hj
      have hne : (⟨n * m + j, n * m + j, 2 * (i * m + j) + 0⟩ : ThreeDMTriple) ≠
          ⟨i * m + j, i * m + j, 2 * (i * m + j)⟩ := by
        intro heq
        have h1 := congrArg ThreeDMTriple.x heq
        dsimp at h1
        have : i * m + j < n * m := by
          calc i * m + j < (i + 1) * m := by ring_nf; omega
            _ ≤ n * m := Nat.mul_le_mul_right _ (by omega)
        omega
      have hz_eq := (hM.2.2 _ (by simpa [hpol] using htM) _ hT hne).2.2
      exact hz_eq rfl
    · simp [Literal.eval, hσ, hpol]
  · -- Variable `i` chose all false triples, so `σ l.1 = false` and `2*(i*m+j)+1` is used;
    -- hence `l.2` MUST be `false`!
    have hσ : σ l.1 = false := by
      simp only [σ, decide_eq_false_iff_not]
      intro hT0
      have hF0 := hFalse 0 hm_pos
      have hne : (⟨i * m + 0, i * m + 0, 2 * (i * m + 0)⟩ : ThreeDMTriple) ≠
          ⟨i * m + (0 + 1) % m, i * m + 0, 2 * (i * m + 0) + 1⟩ := by
        intro heq
        have h1 := congrArg ThreeDMTriple.z heq
        dsimp at h1; omega
      exact (hM.2.2 _ (by simpa [i] using hT0) _ hF0 hne).2.1 rfl
    cases hpol : l.2
    · simp [Literal.eval, hσ, hpol]
    · exfalso
      have hF := hFalse j hj
      have hne : (⟨n * m + j, n * m + j, 2 * (i * m + j) + 1⟩ : ThreeDMTriple) ≠
          ⟨i * m + (j + 1) % m, i * m + j, 2 * (i * m + j) + 1⟩ := by
        intro heq
        have h1 := congrArg ThreeDMTriple.y heq
        dsimp at h1
        have : i * m + j < n * m := by
          calc i * m + j < (i + 1) * m := by ring_nf; omega
            _ ≤ n * m := Nat.mul_le_mul_right _ (by omega)
        omega
      exact (hM.2.2 _ (by simpa [hpol] using htM) _ hF hne).2.2 rfl

/-- Helper: assemble a valid `3-DM` of size `2 * (n * m)` from three coordinate-separated pieces. -/
private theorem isThreeDMatching_of_three_parts {inst : ThreeDMInstance} {n m : ℕ}
    (hn : 0 < n) (hsz : inst.size = 2 * (n * m))
    {A B C : Finset ThreeDMTriple}
    (hmem : ∀ t ∈ A ∪ B ∪ C,
      t ∈ inst.triples ∧ t.x < inst.size ∧ t.y < inst.size ∧ t.z < inst.size)
    (hAx : ∀ t ∈ A, t.x < n * m) (hBx : ∀ t ∈ B, n * m ≤ t.x ∧ t.x < n * m + m)
    (hCx : ∀ t ∈ C, n * m + m ≤ t.x)
    (hAy : ∀ t ∈ A, t.y < n * m) (hBy : ∀ t ∈ B, n * m ≤ t.y ∧ t.y < n * m + m)
    (hCy : ∀ t ∈ C, n * m + m ≤ t.y)
    (hA_x : Set.InjOn ThreeDMTriple.x (A : Set _))
    (hB_x : Set.InjOn ThreeDMTriple.x (B : Set _))
    (hC_x : Set.InjOn ThreeDMTriple.x (C : Set _))
    (hA_y : Set.InjOn ThreeDMTriple.y (A : Set _))
    (hB_y : Set.InjOn ThreeDMTriple.y (B : Set _))
    (hC_y : Set.InjOn ThreeDMTriple.y (C : Set _))
    (hA_z : Set.InjOn ThreeDMTriple.z (A : Set _))
    (hB_z : Set.InjOn ThreeDMTriple.z (B : Set _))
    (hC_z : Set.InjOn ThreeDMTriple.z (C : Set _))
    (hAB_z : Disjoint (A.image ThreeDMTriple.z) (B.image ThreeDMTriple.z))
    (hABC_z : Disjoint ((A ∪ B).image ThreeDMTriple.z) (C.image ThreeDMTriple.z))
    (hAc : A.card = n * m) (hBc : B.card = m) (hCc : C.card = (n - 1) * m) :
    IsThreeDMatching inst (A ∪ B ∪ C) := by
  have hdisj_AB : Disjoint A B :=
    Finset.disjoint_left.mpr fun t htA htB =>
      Finset.disjoint_left.mp hAB_z (Finset.mem_image_of_mem _ htA) (Finset.mem_image_of_mem _ htB)
  have hdisj_ABC : Disjoint (A ∪ B) C :=
    Finset.disjoint_left.mpr fun t htAB htC =>
      Finset.disjoint_left.mp hABC_z (Finset.mem_image_of_mem _ htAB)
        (Finset.mem_image_of_mem _ htC)
  have hcard : (A ∪ B ∪ C).card = inst.size := by
    rw [Finset.card_union_of_disjoint hdisj_ABC, Finset.card_union_of_disjoint hdisj_AB,
      hAc, hBc, hCc, Nat.sub_mul, one_mul, hsz]
    have : 1 * m ≤ n * m := Nat.mul_le_mul_right m (by omega)
    omega
  have hx_inj : Set.InjOn ThreeDMTriple.x ((A ∪ B ∪ C : Finset _) : Set _) := by
    intro t₁ ht₁ t₂ ht₂ hx
    rcases Finset.mem_union.mp ht₁ with ht₁ | ht₁ <;>
      rcases Finset.mem_union.mp ht₂ with ht₂ | ht₂
    · rcases Finset.mem_union.mp ht₁ with ht₁ | ht₁ <;>
        rcases Finset.mem_union.mp ht₂ with ht₂ | ht₂
      · exact hA_x ht₁ ht₂ hx
      · have := hAx t₁ ht₁; have := (hBx t₂ ht₂).1; omega
      · have := (hBx t₁ ht₁).1; have := hAx t₂ ht₂; omega
      · exact hB_x ht₁ ht₂ hx
    · rcases Finset.mem_union.mp ht₁ with ht₁ | ht₁
      · have := hAx t₁ ht₁; have := hCx t₂ ht₂; omega
      · have := (hBx t₁ ht₁).2; have := hCx t₂ ht₂; omega
    · rcases Finset.mem_union.mp ht₂ with ht₂ | ht₂
      · have := hCx t₁ ht₁; have := hAx t₂ ht₂; omega
      · have := hCx t₁ ht₁; have := (hBx t₂ ht₂).2; omega
    · exact hC_x ht₁ ht₂ hx
  have hy_inj : Set.InjOn ThreeDMTriple.y ((A ∪ B ∪ C : Finset _) : Set _) := by
    intro t₁ ht₁ t₂ ht₂ hy
    rcases Finset.mem_union.mp ht₁ with ht₁ | ht₁ <;>
      rcases Finset.mem_union.mp ht₂ with ht₂ | ht₂
    · rcases Finset.mem_union.mp ht₁ with ht₁ | ht₁ <;>
        rcases Finset.mem_union.mp ht₂ with ht₂ | ht₂
      · exact hA_y ht₁ ht₂ hy
      · have := hAy t₁ ht₁; have := (hBy t₂ ht₂).1; omega
      · have := (hBy t₁ ht₁).1; have := hAy t₂ ht₂; omega
      · exact hB_y ht₁ ht₂ hy
    · rcases Finset.mem_union.mp ht₁ with ht₁ | ht₁
      · have := hAy t₁ ht₁; have := hCy t₂ ht₂; omega
      · have := (hBy t₁ ht₁).2; have := hCy t₂ ht₂; omega
    · rcases Finset.mem_union.mp ht₂ with ht₂ | ht₂
      · have := hCy t₁ ht₁; have := hAy t₂ ht₂; omega
      · have := hCy t₁ ht₁; have := (hBy t₂ ht₂).2; omega
    · exact hC_y ht₁ ht₂ hy
  have hz_inj : Set.InjOn ThreeDMTriple.z ((A ∪ B ∪ C : Finset _) : Set _) := by
    intro t₁ ht₁ t₂ ht₂ hz
    rcases Finset.mem_union.mp ht₁ with ht₁ | ht₁ <;>
      rcases Finset.mem_union.mp ht₂ with ht₂ | ht₂
    · rcases Finset.mem_union.mp ht₁ with ht₁ | ht₁ <;>
        rcases Finset.mem_union.mp ht₂ with ht₂ | ht₂
      · exact hA_z ht₁ ht₂ hz
      · exfalso; exact Finset.disjoint_left.mp hAB_z (Finset.mem_image_of_mem _ ht₁)
          (hz ▸ Finset.mem_image_of_mem _ ht₂)
      · exfalso; exact Finset.disjoint_left.mp hAB_z (hz ▸ Finset.mem_image_of_mem _ ht₂)
          (Finset.mem_image_of_mem _ ht₁)
      · exact hB_z ht₁ ht₂ hz
    · exfalso; exact Finset.disjoint_left.mp hABC_z (Finset.mem_image_of_mem _ ht₁)
        (hz ▸ Finset.mem_image_of_mem _ ht₂)
    · exfalso; exact Finset.disjoint_left.mp hABC_z (hz ▸ Finset.mem_image_of_mem _ ht₂)
        (Finset.mem_image_of_mem _ ht₁)
    · exact hC_z ht₁ ht₂ hz
  refine ⟨hmem, hcard, fun t₁ ht₁ t₂ ht₂ hne => ?_⟩
  exact ⟨fun h => hne (hx_inj ht₁ ht₂ h), fun h => hne (hy_inj ht₁ ht₂ h),
    fun h => hne (hz_inj ht₁ ht₂ h)⟩

/-- Forward correctness: a satisfying assignment of `φ` yields a valid `3-DM` of `buildCore φ`. -/
private theorem buildCore_mem_of_satisfiable {φ : CNF ℕ} (hne : φ ≠ [])
    (hsyn : ∀ c ∈ φ, 1 ≤ c.length ∧ c.length ≤ 3)
    (hsat : φ.Satisfiable) : buildCore φ ∈ ThreeDM := by
  classical
  obtain ⟨σ, hσ⟩ := hsat
  set vs := φ.distinctVars
  set n := vs.length
  set m := φ.length
  have hm_pos : 0 < m := List.length_pos_of_ne_nil hne
  have h0_mem : φ[0] ∈ φ := List.getElem_mem hm_pos
  have hn_pos : 0 < n := by
    obtain ⟨l, hl⟩ := List.exists_mem_of_length_pos (show 0 < φ[0].length by
      linarith [(hsyn _ h0_mem).1])
    exact List.length_pos_of_mem (CNF.mem_distinctVars.mpr (CNF.mem_vars.mpr ⟨_, h0_mem, l.2, hl⟩))
  have hmul_div_mod : ∀ {a b c d : ℕ}, b < m → d < m → a * m + b = c * m + d → a = c ∧ b = d := by
    intro a b c d hb hd heq
    have hq := congrArg (· / m) heq
    have hr := congrArg (· % m) heq
    rw [Nat.mul_comm a m, Nat.mul_comm c m, Nat.mul_add_div hm_pos, Nat.mul_add_div hm_pos,
      Nat.div_eq_of_lt hb, Nat.div_eq_of_lt hd] at hq
    rw [Nat.mul_comm a m, Nat.mul_comm c m, Nat.mul_add_mod, Nat.mul_add_mod,
      Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hd] at hr
    exact ⟨by omega, hr⟩
  -- For each clause `j < m`, choose a true literal `clLit j ∈ φ[j]`
  have hex_lit : ∀ j : Fin m, ∃ l ∈ φ[j.1], Literal.eval σ l = true := fun j => by
    have := List.all_eq_true.mp hσ _ (List.getElem_mem j.2)
    simpa [Clause.eval, List.any_eq_true] using this
  let clLit (j : Fin m) : Literal ℕ := (hex_lit j).choose
  have hclLit_mem (j : Fin m) : clLit j ∈ φ[j.1] := (hex_lit j).choose_spec.1
  have hclLit_eval (j : Fin m) : Literal.eval σ (clLit j) = true := (hex_lit j).choose_spec.2
  -- Variable triples: for each `(i, j)`, pick true triple if `σ (vs[i]) = true`, else false triple
  let varChoice (i : Fin n) (j : Fin m) : ThreeDMTriple :=
    if σ vs[i.1] then ⟨i.1 * m + j.1, i.1 * m + j.1, 2 * (i.1 * m + j.1)⟩
    else ⟨i.1 * m + (j.1 + 1) % m, i.1 * m + j.1, 2 * (i.1 * m + j.1) + 1⟩
  -- Clause triples: for each `j`, pick the triple for `clLit j`
  let clChoice (j : Fin m) : ThreeDMTriple :=
    let l := clLit j
    let i := vs.idxOf l.1
    ⟨n * m + j.1, n * m + j.1, 2 * (i * m + j.1) + if l.2 then 1 else 0⟩
  -- Collect the `n * m + m` chosen `Z`-tips
  let varSet : Finset ThreeDMTriple :=
    Finset.univ.image fun p : Fin n × Fin m => varChoice p.1 p.2
  let clSet : Finset ThreeDMTriple := Finset.univ.image clChoice
  let usedZ : Finset ℕ := (varSet ∪ clSet).image ThreeDMTriple.z
  -- All chosen `Z`-tips are `< 2 * n * m`, and `varSet` and `clSet` have disjoint `Z`-tips!
  have hvar_z_lt : ∀ p : Fin n × Fin m, (varChoice p.1 p.2).z < 2 * (n * m) := fun ⟨i, j⟩ => by
    have : i.1 * m + j.1 < n * m := by
      calc i.1 * m + j.1 < (i.1 + 1) * m := by ring_nf; omega
        _ ≤ n * m := Nat.mul_le_mul_right _ (by omega)
    dsimp only [varChoice]; split_ifs <;> dsimp only <;> omega
  have hcl_z_lt : ∀ j : Fin m, (clChoice j).z < 2 * (n * m) := fun j => by
    have hi : vs.idxOf (clLit j).1 < n := List.idxOf_lt_length_of_mem
      (CNF.mem_distinctVars.mpr (CNF.mem_vars.mpr
        ⟨_, List.getElem_mem j.2, (clLit j).2, hclLit_mem j⟩))
    have : vs.idxOf (clLit j).1 * m + j.1 < n * m := by
      calc vs.idxOf (clLit j).1 * m + j.1 < (vs.idxOf (clLit j).1 + 1) * m := by ring_nf; omega
        _ ≤ n * m := Nat.mul_le_mul_right _ (by omega)
    dsimp only [clChoice]; split_ifs <;> omega
  have hvar_inj_z : Function.Injective fun p : Fin n × Fin m => (varChoice p.1 p.2).z := by
    rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ heq
    have hdiv : i₁.1 * m + j₁.1 = i₂.1 * m + j₂.1 := by
      dsimp only [varChoice] at heq; split_ifs at heq <;> dsimp only at heq <;> omega
    obtain ⟨hi, hj⟩ := hmul_div_mod j₁.2 j₂.2 hdiv
    exact Prod.ext (Fin.ext hi) (Fin.ext hj)
  have hcl_inj_z : Function.Injective fun j : Fin m => (clChoice j).z := by
    intro j₁ j₂ heq
    have hdiv : vs.idxOf (clLit j₁).1 * m + j₁.1 = vs.idxOf (clLit j₂).1 * m + j₂.1 := by
      dsimp only [clChoice] at heq; split_ifs at heq <;> omega
    exact Fin.ext (hmul_div_mod j₁.2 j₂.2 hdiv).2
  have hdisj_z : Disjoint (varSet.image ThreeDMTriple.z) (clSet.image ThreeDMTriple.z) := by
    rw [Finset.disjoint_left]
    intro z hzV hzC
    obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_image.mp hzV
    obtain ⟨⟨i, j₁⟩, -, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨t₂, ht₂, hzeq⟩ := Finset.mem_image.mp hzC
    obtain ⟨j₂, -, rfl⟩ := Finset.mem_image.mp ht₂
    have hmem_l : (clLit j₂).1 ∈ vs :=
      CNF.mem_distinctVars.mpr (CNF.mem_vars.mpr
        ⟨_, List.getElem_mem j₂.2, (clLit j₂).2, hclLit_mem j₂⟩)
    have hidx : vs[vs.idxOf (clLit j₂).1]'(List.idxOf_lt_length_of_mem hmem_l) = (clLit j₂).1 :=
      List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem_l)
    have hsame : i.1 * m + j₁.1 = vs.idxOf (clLit j₂).1 * m + j₂.1 := by
      dsimp only [varChoice, clChoice] at hzeq; split_ifs at hzeq <;> dsimp only at hzeq <;> omega
    have hi_eq : i.1 = vs.idxOf (clLit j₂).1 := (hmul_div_mod j₁.2 j₂.2 hsame).1
    have hpol := hclLit_eval j₂
    have hidx' : vs[i.1] = (clLit j₂).1 := by
      rw [← hidx]; congr 1
    rw [Literal.eval, ← hidx'] at hpol
    dsimp only [varChoice, clChoice] at hzeq
    rw [← hi_eq] at hzeq
    cases hσv : σ vs[i.1] <;> cases hlb : (clLit j₂).2 <;> simp_all
  -- Compute `usedZ.card = n * m + m`, leaving `(n - 1) * m` uncovered `Z`-elements!
  have husedZ_sub : usedZ ⊆ Finset.range (2 * (n * m)) := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_range.mpr (hvar_z_lt (i, j))
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_range.mpr (hcl_z_lt j)
  have hvarZ_card : (varSet.image ThreeDMTriple.z).card = n * m := by
    have h1 : varSet.image ThreeDMTriple.z =
        Finset.univ.image fun p : Fin n × Fin m => (varChoice p.1 p.2).z := by
      simp [varSet, Finset.image_image, Function.comp_def]
    rw [h1, Finset.card_image_of_injective _ hvar_inj_z]
    simp
  have hclZ_card : (clSet.image ThreeDMTriple.z).card = m := by
    have h1 : clSet.image ThreeDMTriple.z = Finset.univ.image fun j : Fin m => (clChoice j).z := by
      simp [clSet, Finset.image_image, Function.comp_def]
    rw [h1, Finset.card_image_of_injective _ hcl_inj_z]
    simp
  have husedZ_card : usedZ.card = n * m + m := by
    rw [show usedZ = varSet.image ThreeDMTriple.z ∪ clSet.image ThreeDMTriple.z by
      simp [usedZ, Finset.image_union],
      Finset.card_union_of_disjoint hdisj_z, hvarZ_card, hclZ_card]
  let remZ : Finset ℕ := Finset.range (2 * (n * m)) \ usedZ
  have hremZ_card : remZ.card = (n - 1) * m := by
    rw [Finset.card_sdiff_of_subset husedZ_sub, Finset.card_range, husedZ_card]
    have : 1 * m ≤ n * m := Nat.mul_le_mul_right m (by omega)
    rw [Nat.sub_mul, one_mul]
    omega
  -- Enumerate `remZ` by `Fin ((n - 1) * m)` using `Finset.orderIsoOfFin`, then abstract `remEnum`
  -- to keep `whnf` fast.
  have hrem_ex : ∃ f : Fin ((n - 1) * m) → ℕ,
      Function.Injective f ∧ (∀ k, f k < 2 * (n * m)) ∧ (∀ k, f k ∉ usedZ) := by
    let e : Fin ((n - 1) * m) ↪o ℕ :=
      (remZ.orderIsoOfFin hremZ_card).toOrderEmbedding.trans (OrderEmbedding.subtype _)
    refine ⟨e, e.injective, fun k => ?_, fun k => ?_⟩
    · exact Finset.mem_range.mp (Finset.mem_sdiff.mp (remZ.orderIsoOfFin hremZ_card k).2).1
    · exact (Finset.mem_sdiff.mp (remZ.orderIsoOfFin hremZ_card k).2).2
  obtain ⟨remEnum, hrem_inj, hrem_lt, hrem_notMem⟩ := hrem_ex
  let garbSet : Finset ThreeDMTriple :=
    Finset.univ.image fun k : Fin ((n - 1) * m) =>
      ⟨n * m + m + k.1, n * m + m + k.1, remEnum k⟩
  -- Combine `varSet ∪ clSet ∪ garbSet` and verify `IsThreeDMatching`!
  let M : Finset ThreeDMTriple := varSet ∪ clSet ∪ garbSet
  have hvar_in : ∀ t ∈ varSet, t ∈ (buildCore φ).triples ∧
      t.x < 2 * (n * m) ∧ t.y < 2 * (n * m) ∧ t.z < 2 * (n * m) := by
    intro t ht
    obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.mp ht
    have hlt_nm : i.1 * m + j.1 < n * m := by
      calc i.1 * m + j.1 < (i.1 + 1) * m := by ring_nf; omega
        _ ≤ n * m := Nat.mul_le_mul_right _ (by omega)
    have hlt_mod : i.1 * m + (j.1 + 1) % m < n * m := by
      have := Nat.mod_lt (j.1 + 1) hm_pos
      calc i.1 * m + (j.1 + 1) % m < i.1 * m + m := by omega
        _ = (i.1 + 1) * m := by ring
        _ ≤ n * m := Nat.mul_le_mul_right _ (by omega)
    refine ⟨?_, ?_, ?_, hvar_z_lt (i, j)⟩
    · simp only [buildCore, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
        List.not_mem_nil, or_false]
      left; left
      refine ⟨i.1, i.2, j.1, j.2, ?_⟩
      dsimp only [varChoice]; split_ifs <;> simp [m]
    · dsimp only [varChoice]; split_ifs <;> dsimp only <;> omega
    · dsimp only [varChoice]; split_ifs <;> dsimp only <;> omega
  have hcl_in : ∀ t ∈ clSet, t ∈ (buildCore φ).triples ∧
      t.x < 2 * (n * m) ∧ t.y < 2 * (n * m) ∧ t.z < 2 * (n * m) := by
    intro t ht
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ht
    have h1m : 1 * m ≤ n * m := Nat.mul_le_mul_right m (by omega)
    refine ⟨?_, by dsimp [clChoice]; omega, by dsimp [clChoice]; omega, hcl_z_lt j⟩
    simp only [buildCore, List.mem_append, List.mem_flatMap, List.mem_map]
    left; right
    refine ⟨(φ[j.1], j.1), ?_, clLit j, hclLit_mem j, rfl⟩
    rw [List.mem_iff_getElem]
    exact ⟨j.1, by simp only [List.length_zipIdx]; exact j.2, by simp⟩
  have hgarb_in : ∀ t ∈ garbSet, t ∈ (buildCore φ).triples ∧
      t.x < 2 * (n * m) ∧ t.y < 2 * (n * m) ∧ t.z < 2 * (n * m) := by
    intro t ht
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ht
    have hklt : n * m + m + k.1 < 2 * (n * m) := by
      have hk2 : k.1 < (n - 1) * m := k.2
      have hsub : (n - 1) * m = n * m - m := by rw [Nat.sub_mul, one_mul]
      have : 1 * m ≤ n * m := Nat.mul_le_mul_right m (by omega)
      omega
    refine ⟨?_, hklt, hklt, hrem_lt k⟩
    simp only [buildCore, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map]
    right
    exact ⟨k.1, k.2, remEnum k, hrem_lt k, rfl⟩
  have hM_mem : ∀ t ∈ M, t ∈ (buildCore φ).triples ∧
      t.x < (buildCore φ).size ∧ t.y < (buildCore φ).size ∧ t.z < (buildCore φ).size := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_union.mp ht with ht | ht
      · exact hvar_in t ht
      · exact hcl_in t ht
    · exact hgarb_in t ht
  -- Apply `isThreeDMatching_of_three_parts` to `varSet ∪ clSet ∪ garbSet`.
  refine ⟨varSet ∪ clSet ∪ garbSet,
      isThreeDMatching_of_three_parts (n := n) (m := m) hn_pos rfl hM_mem ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hdisj_z ?_ ?_ ?_ ?_⟩
  · intro t ht; obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.mp ht
    have h1 : i.1 * m + j.1 < n * m := by
      calc i.1 * m + j.1 < (i.1 + 1) * m := by ring_nf; omega
        _ ≤ n * m := Nat.mul_le_mul_right _ (by omega)
    have h2 : i.1 * m + (j.1 + 1) % m < n * m := by
      have := Nat.mod_lt (j.1 + 1) hm_pos
      calc i.1 * m + (j.1 + 1) % m < i.1 * m + m := by omega
        _ = (i.1 + 1) * m := by ring
        _ ≤ n * m := Nat.mul_le_mul_right _ (by omega)
    dsimp only [varChoice]; split_ifs <;> dsimp only <;> omega
  · intro t ht; obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ht; dsimp [clChoice]; omega
  · intro t ht; obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ht; dsimp; omega
  · intro t ht; obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.mp ht
    have h1 : i.1 * m + j.1 < n * m := by
      calc i.1 * m + j.1 < (i.1 + 1) * m := by ring_nf; omega
        _ ≤ n * m := Nat.mul_le_mul_right _ (by omega)
    dsimp only [varChoice]; split_ifs <;> exact h1
  · intro t ht; obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ht; dsimp [clChoice]; omega
  · intro t ht; obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ht; dsimp; omega
  · intro t₁ ht₁ t₂ ht₂ hx
    obtain ⟨⟨i₁, j₁⟩, -, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨⟨i₂, j₂⟩, -, rfl⟩ := Finset.mem_image.mp ht₂
    have hdiv : (if σ vs[i₁.1] then i₁.1 * m + j₁.1 else i₁.1 * m + (j₁.1 + 1) % m) =
        (if σ vs[i₂.1] then i₂.1 * m + j₂.1 else i₂.1 * m + (j₂.1 + 1) % m) := by
      dsimp only [varChoice] at hx; split_ifs at hx ⊢ <;> exact hx
    have hmod1 : (j₁.1 + 1) % m < m := Nat.mod_lt _ hm_pos
    have hmod2 : (j₂.1 + 1) % m < m := Nat.mod_lt _ hm_pos
    have hi_eq : i₁ = i₂ := by
      apply Fin.ext
      split_ifs at hdiv
      · exact (hmul_div_mod j₁.2 j₂.2 hdiv).1
      · exact (hmul_div_mod j₁.2 hmod2 hdiv).1
      · exact (hmul_div_mod hmod1 j₂.2 hdiv).1
      · exact (hmul_div_mod hmod1 hmod2 hdiv).1
    subst hi_eq
    have hj_eq : j₁ = j₂ := by
      apply Fin.ext
      cases hσi : σ vs[i₁.1]
      · simp only [hσi, Bool.false_eq_true, ↓reduceIte] at hdiv
        have hrm : (j₁.1 + 1) % m = (j₂.1 + 1) % m := (hmul_div_mod hmod1 hmod2 hdiv).2
        have h1 : j₁.1 + 1 = m ∨ j₁.1 + 1 < m := by omega
        have h2 : j₂.1 + 1 = m ∨ j₂.1 + 1 < m := by omega
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · omega
        · rw [h1, Nat.mod_self, Nat.mod_eq_of_lt h2] at hrm; omega
        · rw [h2, Nat.mod_self, Nat.mod_eq_of_lt h1] at hrm; omega
        · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hrm; omega
      · simp only [hσi, ↓reduceIte] at hdiv
        exact (hmul_div_mod j₁.2 j₂.2 hdiv).2
    rw [hj_eq]
  · intro t₁ ht₁ t₂ ht₂ hx
    obtain ⟨j₁, -, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨j₂, -, rfl⟩ := Finset.mem_image.mp ht₂
    dsimp [clChoice] at hx; exact congrArg clChoice (Fin.ext (by omega))
  · intro t₁ ht₁ t₂ ht₂ hx
    obtain ⟨k₁, -, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨k₂, -, rfl⟩ := Finset.mem_image.mp ht₂
    dsimp at hx; have hk : k₁ = k₂ := Fin.ext (by omega); rw [hk]
  · intro t₁ ht₁ t₂ ht₂ hy
    obtain ⟨⟨i₁, j₁⟩, -, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨⟨i₂, j₂⟩, -, rfl⟩ := Finset.mem_image.mp ht₂
    have hdiv : i₁.1 * m + j₁.1 = i₂.1 * m + j₂.1 := by
      dsimp only [varChoice] at hy; split_ifs at hy <;> dsimp only at hy <;> exact hy
    obtain ⟨hi, hj⟩ := hmul_div_mod j₁.2 j₂.2 hdiv
    exact congrArg₂ varChoice (Fin.ext hi) (Fin.ext hj)
  · intro t₁ ht₁ t₂ ht₂ hy
    obtain ⟨j₁, -, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨j₂, -, rfl⟩ := Finset.mem_image.mp ht₂
    dsimp [clChoice] at hy; exact congrArg clChoice (Fin.ext (by omega))
  · intro t₁ ht₁ t₂ ht₂ hy
    obtain ⟨k₁, -, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨k₂, -, rfl⟩ := Finset.mem_image.mp ht₂
    dsimp at hy; have hk : k₁ = k₂ := Fin.ext (by omega); rw [hk]
  · intro t₁ ht₁ t₂ ht₂ hz
    obtain ⟨⟨i₁, j₁⟩, -, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨⟨i₂, j₂⟩, -, rfl⟩ := Finset.mem_image.mp ht₂
    have := hvar_inj_z hz; cases this; rfl
  · intro t₁ ht₁ t₂ ht₂ hz
    obtain ⟨j₁, -, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨j₂, -, rfl⟩ := Finset.mem_image.mp ht₂
    exact congrArg clChoice (hcl_inj_z hz)
  · intro t₁ ht₁ t₂ ht₂ hz
    obtain ⟨k₁, -, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨k₂, -, rfl⟩ := Finset.mem_image.mp ht₂
    have hk : k₁ = k₂ := hrem_inj hz; rw [hk]
  · rw [Finset.disjoint_left]
    intro z hzU hzG
    obtain ⟨t, htG, rfl⟩ := Finset.mem_image.mp hzG
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp htG
    exact hrem_notMem k hzU
  · have : Function.Injective (fun p : Fin n × Fin m => varChoice p.1 p.2) :=
      fun p₁ p₂ h => hvar_inj_z (congrArg ThreeDMTriple.z h)
    rw [Finset.card_image_of_injective _ this]; simp
  · have : Function.Injective clChoice :=
      fun j₁ j₂ h => hcl_inj_z (congrArg ThreeDMTriple.z h)
    rw [Finset.card_image_of_injective _ this]; simp
  · have : Function.Injective (fun k : Fin ((n - 1) * m) =>
        (⟨n * m + m + k.1, n * m + m + k.1, remEnum k⟩ : ThreeDMTriple)) :=
      fun k₁ k₂ h => hrem_inj (congrArg ThreeDMTriple.z h)
    rw [Finset.card_image_of_injective _ this]; simp

/-- **Correctness of the reduction `ThreeSAT → ThreeDM`.** -/
theorem ofThreeSAT_mem_iff (φ : CNF ℕ) : ofThreeSAT φ ∈ ThreeDM ↔ φ ∈ ThreeSAT := by
  unfold ofThreeSAT
  by_cases hemp : φ.isEmpty = true
  · simp only [hemp, ↓reduceIte, yesInstance_mem, true_iff]
    obtain rfl : φ = [] := List.isEmpty_iff.mp hemp
    exact ⟨by simp, ⟨fun _ => false, by simp [CNF.eval]⟩⟩
  · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
    have hne : φ ≠ [] := fun h => hemp (by simp [h])
    by_cases hsyn : syntaxOK φ = true
    · simp only [hsyn, ↓reduceIte]
      have hs := (syntaxOK_iff φ).mp hsyn
      exact ⟨fun h => ⟨fun c hc => (hs c hc).2, satisfiable_of_buildCore_mem hne hs h⟩,
        fun h => buildCore_mem_of_satisfiable hne hs h.2⟩
    · simp only [hsyn, Bool.false_eq_true, ↓reduceIte, noInstance_notMem, false_iff]
      rintro ⟨hw, σ, hσ⟩
      apply hsyn
      rw [syntaxOK_iff]
      intro c hc
      refine ⟨?_, hw c hc⟩
      have hev := List.all_eq_true.mp hσ c hc
      simp only [Clause.eval, List.any_eq_true] at hev
      obtain ⟨l, hl, -⟩ := hev
      exact List.length_pos_of_mem hl

end ThreeDM

/-- **`3-SAT` reduces to `3-DM` in polynomial time.** -/
theorem polyTimeReducible_ThreeSAT_ThreeDM :
    PolyTimeReducible encCNF encThreeDM ThreeSAT ThreeDM :=
  ⟨ThreeDM.ofThreeSAT, ThreeDM.computableInPolyTime_ofThreeSAT,
    fun φ => (ThreeDM.ofThreeSAT_mem_iff φ).symm⟩

/-- **`3-DM` is NP-hard.** -/
theorem ThreeDM_npHard : NPHard encThreeDM ThreeDM :=
  ThreeSAT_npHard.trans polyTimeReducible_ThreeSAT_ThreeDM

/-- **`3-Dimensional Matching` (`3-DM`) is NP-complete** under standard Lean axioms
.
-/
theorem ThreeDM_npComplete : NPComplete encThreeDM ThreeDM :=
  ⟨ThreeDM_mem_NP, ThreeDM_npHard⟩

end Cslib.Complexity
