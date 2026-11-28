module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Order
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Ring
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith

/-!
# Maximum Cut on Represented Permutation Graphs

Defines the decision problem `CslibFrontier.Complexity.PermutationMaxCut` for maximum cut on
represented permutation graphs under canonical binary encoding, defines the represented
permutation graph `permListGraph` directly from inversions, and proves under standard Lean axioms
that `PermutationMaxCut` belongs to `Cslib.Complexity.NP`.

## Main definitions

* `CslibFrontier.Complexity.PermutationMaxCutInstance`: instance `(perm, bound)` consisting of a
  candidate permutation list `perm : List ℕ` and a cut-size threshold `bound : ℕ`.
* `CslibFrontier.Complexity.encPermutationMaxCut`: canonical binary encoding of
  `PermutationMaxCutInstance` as `encPair (encList encNat) encNat`.
* `CslibFrontier.Complexity.IsPermList`: predicate asserting that `perm` is a permutation of
  `List.range perm.length`.
* `CslibFrontier.Complexity.permListGraph`: permutation graph on `Fin perm.length` whose edges are
  inversions `{i, j}` with `i < j` and `perm[j] < perm[i]`.
* `CslibFrontier.Complexity.PermutationMaxCut`: set of valid instances admitting a cut of size at
  least `bound`.

## Main results

* `CslibFrontier.Complexity.permListGraph_adj_iff`: inversion characterization of adjacency in
  `permListGraph`.
* `CslibFrontier.Complexity.mem_permutationMaxCut_iff_minMonoEdges`: threshold reformulation in
  terms of minimum monochromatic edges `g(G) + bound ≤ |E(G)|`.
* `CslibFrontier.Complexity.permutationMaxCut_mem_NP`: `PermutationMaxCut` belongs to
  `Cslib.Complexity.NP encPermutationMaxCut` under standard Lean axioms.
-/

public section

namespace CslibFrontier.Complexity

universe u v

section EdgePred

variable {V : Type u}

/-- Predicate on `Sym2 V` testing whether both endpoints receive the same Boolean colour under
`x`. Well-defined on unordered pairs by symmetry of equality. -/
def edgeIsMono (x : V → Bool) (e : Sym2 V) : Prop :=
  Sym2.lift ⟨fun u v => x u = x v, fun _ _ => propext eq_comm⟩ e

@[simp]
theorem edgeIsMono_mk (x : V → Bool) (u v : V) :
    edgeIsMono x s(u, v) ↔ x u = x v :=
  Iff.rfl

instance instDecidablePredEdgeIsMono (x : V → Bool) : DecidablePred (edgeIsMono x) :=
  fun e => Sym2.recOnSubsingleton e fun u v => inferInstanceAs (Decidable (x u = x v))

end EdgePred

section Counts

variable {V : Type u} [Fintype V] (G : _root_.SimpleGraph V)

/-- Number of monochromatic edges of a finite simple graph `G` under a 2-colouring `x : V → Bool`
(counted as unordered edges). -/
noncomputable def monoEdgeCount (x : V → Bool) : ℕ := by
  classical
  exact (G.edgeFinset.filter (edgeIsMono x)).card

/-- Number of bichromatic (cut) edges of a finite simple graph `G` under a 2-colouring
`x : V → Bool` (counted as unordered edges). -/
noncomputable def cutEdgeCount (x : V → Bool) : ℕ := by
  classical
  exact (G.edgeFinset.filter (fun e => ¬ edgeIsMono x e)).card

/-- Every edge of `G` is either monochromatic or in the cut induced by `x`. -/
theorem monoEdgeCount_add_cutEdgeCount (x : V → Bool) :
    monoEdgeCount G x + cutEdgeCount G x = G.edgeSet.ncard := by
  classical
  unfold monoEdgeCount cutEdgeCount
  rw [Finset.card_filter_add_card_filter_not (edgeIsMono x),
    _root_.SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card' G.edgeSet]

/-- Twice `monoEdgeCount G x` equals the number of ordered adjacent pairs `(u, v)` with
`x u = x v`. -/
theorem two_mul_monoEdgeCount (x : V → Bool) :
    2 * monoEdgeCount G x =
      by classical
        exact ((Finset.univ : Finset (V × V)).filter
          (fun p : V × V => G.Adj p.1 p.2 ∧ x p.1 = x p.2)).card := by
  classical
  unfold monoEdgeCount
  set S := (Finset.univ : Finset (V × V)).filter (fun p : V × V => G.Adj p.1 p.2 ∧ x p.1 = x p.2)
  set M := G.edgeFinset.filter (edgeIsMono x)
  have hfib : ∀ e ∈ M, (S.filter (fun p => s(p.1, p.2) = e)).card = 2 := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      simp only [M, Finset.mem_filter, _root_.SimpleGraph.mem_edgeFinset,
        _root_.SimpleGraph.mem_edgeSet, edgeIsMono_mk] at he
      have hne : u ≠ v := he.1.ne
      have hset : S.filter (fun p => s(p.1, p.2) = s(u, v)) = {(u, v), (v, u)} := by
        ext ⟨a, b⟩
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Sym2.eq, Sym2.rel_iff',
          Prod.mk.injEq, Prod.swap_prod_mk, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨_, h⟩; exact h
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact ⟨⟨he.1, he.2⟩, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨⟨he.1.symm, he.2.symm⟩, Or.inr ⟨rfl, rfl⟩⟩
      rw [hset, Finset.card_pair]
      intro h
      exact hne (congrArg Prod.fst h)
  have hmaps : ∀ p ∈ S, s(p.1, p.2) ∈ M := by
    intro ⟨a, b⟩ hp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [M, Finset.mem_filter, _root_.SimpleGraph.mem_edgeFinset,
      _root_.SimpleGraph.mem_edgeSet, edgeIsMono_mk]
    exact hp
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_congr rfl hfib, Finset.sum_const,
    smul_eq_mul, mul_comm]

/-- Twice `cutEdgeCount G x` equals the number of ordered adjacent pairs `(u, v)` with
`x u ≠ x v`. -/
theorem two_mul_cutEdgeCount (x : V → Bool) :
    2 * cutEdgeCount G x =
      by classical
        exact ((Finset.univ : Finset (V × V)).filter
          (fun p : V × V => G.Adj p.1 p.2 ∧ x p.1 ≠ x p.2)).card := by
  classical
  unfold cutEdgeCount
  set S := (Finset.univ : Finset (V × V)).filter (fun p : V × V => G.Adj p.1 p.2 ∧ x p.1 ≠ x p.2)
  set M := G.edgeFinset.filter (fun e => ¬ edgeIsMono x e)
  have hfib : ∀ e ∈ M, (S.filter (fun p => s(p.1, p.2) = e)).card = 2 := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      simp only [M, Finset.mem_filter, _root_.SimpleGraph.mem_edgeFinset,
        _root_.SimpleGraph.mem_edgeSet, edgeIsMono_mk] at he
      have hne : u ≠ v := he.1.ne
      have hset : S.filter (fun p => s(p.1, p.2) = s(u, v)) = {(u, v), (v, u)} := by
        ext ⟨a, b⟩
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Sym2.eq, Sym2.rel_iff',
          Prod.mk.injEq, Prod.swap_prod_mk, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨_, h⟩; exact h
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact ⟨⟨he.1, he.2⟩, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨⟨he.1.symm, Ne.symm he.2⟩, Or.inr ⟨rfl, rfl⟩⟩
      rw [hset, Finset.card_pair]
      intro h
      exact hne (congrArg Prod.fst h)
  have hmaps : ∀ p ∈ S, s(p.1, p.2) ∈ M := by
    intro ⟨a, b⟩ hp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [M, Finset.mem_filter, _root_.SimpleGraph.mem_edgeFinset,
      _root_.SimpleGraph.mem_edgeSet, edgeIsMono_mk]
    exact hp
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_congr rfl hfib, Finset.sum_const,
    smul_eq_mul, mul_comm]

/-- Global colour complementation `v ↦ !x v` preserves `monoEdgeCount`. -/
@[simp]
theorem monoEdgeCount_compl (x : V → Bool) :
    monoEdgeCount G (fun v => !x v) = monoEdgeCount G x := by
  classical
  have h : 2 * monoEdgeCount G (fun v => !x v) = 2 * monoEdgeCount G x := by
    rw [two_mul_monoEdgeCount, two_mul_monoEdgeCount]
    congr 1
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_inj_iff]
  omega


/-- Minimum number of monochromatic edges over all 2-colourings `x : V → Bool` of `G`. -/
noncomputable def minMonoEdges : ℕ :=
  sInf (Set.range (monoEdgeCount G))

/-- Maximum number of cut edges over all 2-colourings `x : V → Bool` of `G`. -/
noncomputable def maxCutEdges : ℕ :=
  sSup (Set.range (cutEdgeCount G))

/-- `minMonoEdges G` is at most the monochromatic count of any 2-colouring `x`. -/
theorem minMonoEdges_le (x : V → Bool) : minMonoEdges G ≤ monoEdgeCount G x :=
  Nat.sInf_le ⟨x, rfl⟩

/-- There exists an optimal 2-colouring attaining `minMonoEdges G`. -/
theorem exists_monoEdgeCount_eq_minMonoEdges :
    ∃ x : V → Bool, monoEdgeCount G x = minMonoEdges G :=
  Nat.sInf_mem (Set.range_nonempty (monoEdgeCount G))

private theorem bddAbove_range_cutEdgeCount : BddAbove (Set.range (cutEdgeCount G)) := by
  refine ⟨G.edgeSet.ncard, ?_⟩
  rintro _ ⟨x, rfl⟩
  have := monoEdgeCount_add_cutEdgeCount G x
  omega

/-- The cut size of any 2-colouring `x` is at most `maxCutEdges G`. -/
theorem le_maxCutEdges (x : V → Bool) : cutEdgeCount G x ≤ maxCutEdges G :=
  le_csSup (bddAbove_range_cutEdgeCount G) ⟨x, rfl⟩

/-- There exists an optimal 2-colouring attaining `maxCutEdges G`. -/
theorem exists_cutEdgeCount_eq_maxCutEdges :
    ∃ x : V → Bool, cutEdgeCount G x = maxCutEdges G :=
  Nat.sSup_mem (Set.range_nonempty (cutEdgeCount G)) (bddAbove_range_cutEdgeCount G)

/-- A lower bound on every 2-colouring yields a lower bound on `minMonoEdges G`. -/
theorem le_minMonoEdges {k : ℕ} (h : ∀ x : V → Bool, k ≤ monoEdgeCount G x) :
    k ≤ minMonoEdges G := by
  obtain ⟨x, hx⟩ := exists_monoEdgeCount_eq_minMonoEdges G
  exact hx ▸ h x

/-- An upper bound on every 2-colouring yields an upper bound on `maxCutEdges G`. -/
theorem maxCutEdges_le {k : ℕ} (h : ∀ x : V → Bool, cutEdgeCount G x ≤ k) :
    maxCutEdges G ≤ k := by
  obtain ⟨x, hx⟩ := exists_cutEdgeCount_eq_maxCutEdges G
  exact hx ▸ h x

/-- Exact duality between minimum monochromatic edges and maximum cut size:
`minMonoEdges G + maxCutEdges G = |E(G)|`. -/
theorem minMonoEdges_add_maxCutEdges :
    minMonoEdges G + maxCutEdges G = G.edgeSet.ncard := by
  obtain ⟨x, hx⟩ := exists_monoEdgeCount_eq_minMonoEdges G
  obtain ⟨y, hy⟩ := exists_cutEdgeCount_eq_maxCutEdges G
  have h1 := monoEdgeCount_add_cutEdgeCount G x
  have h2 := monoEdgeCount_add_cutEdgeCount G y
  have hcx := le_maxCutEdges G x
  have hmy := minMonoEdges_le G y
  omega

end Counts

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

/-- An instance of **MaxCut on represented permutation graphs**: a candidate permutation list
`perm` of `{0, ..., n - 1}` and a target cut-size threshold `bound`. -/
@[ext]
structure PermutationMaxCutInstance where
  /-- List representing a permutation of `{0, ..., perm.length - 1}`. -/
  perm : List ℕ
  /-- Target minimum cut size. -/
  bound : ℕ
  deriving DecidableEq, Repr

/-- Canonical binary encoding of `PermutationMaxCutInstance` as the framed pair of the binary
list encoding of `perm` and the binary natural encoding of `bound`. -/
@[expose] def encPermutationMaxCut : PermutationMaxCutInstance ↪ List Bool where
  toFun x := encPair (encList encNat) encNat (x.perm, x.bound)
  inj' a b h := by
    have hp := (encPair (encList encNat) encNat).injective h
    exact PermutationMaxCutInstance.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)

@[simp]
theorem encPermutationMaxCut_apply (x : PermutationMaxCutInstance) :
    encPermutationMaxCut x = encPair (encList encNat) encNat (x.perm, x.bound) :=
  rfl

/-- `perm` is a valid representation of a permutation of `Fin perm.length`. -/
def IsPermList (perm : List ℕ) : Prop :=
  perm.Perm (List.range perm.length)

/-- Boolean decision procedure checking `IsPermList perm`. -/
def isPermListBool (perm : List ℕ) : Bool :=
  (List.range perm.length).all fun i => perm.any fun a => a == i

/-- `isPermListBool` decides `IsPermList`. -/
theorem isPermListBool_eq_true_iff (perm : List ℕ) :
    isPermListBool perm = true ↔ IsPermList perm := by
  unfold isPermListBool IsPermList
  simp only [List.all_eq_true, List.any_eq_true, beq_iff_eq]
  constructor
  · intro h
    have hsub : List.range perm.length ⊆ perm := by
      intro i hi
      obtain ⟨a, ha, rfl⟩ := h i hi
      exact ha
    have hsp : (List.range perm.length).Subperm perm :=
      (List.nodup_range (n := perm.length)).subperm hsub
    obtain ⟨l, hlperm, hlsub⟩ := hsp
    have hlen : l.length = perm.length := hlperm.length_eq.trans List.length_range
    exact (hlperm.symm.trans (hlsub.eq_of_length hlen ▸ List.Perm.refl _)).symm
  · intro h i hi
    exact ⟨i, h.symm.subset hi, rfl⟩

instance instDecidablePredIsPermList : DecidablePred IsPermList :=
  fun perm => decidable_of_iff (isPermListBool perm = true) (isPermListBool_eq_true_iff _)

/-- Every entry of a valid permutation list is strictly less than `perm.length`. -/
theorem IsPermList.getElem_lt {perm : List ℕ} (h : IsPermList perm)
    (i : Fin perm.length) : perm[i.val] < perm.length :=
  List.mem_range.mp (h.subset (List.getElem_mem i.isLt))

/-- A valid permutation list has no duplicate elements. -/
theorem IsPermList.nodup {perm : List ℕ} (h : IsPermList perm) : perm.Nodup :=
  h.nodup_iff.mpr List.nodup_range

/-- Equivalence `Equiv.Perm (Fin perm.length)` induced by a valid permutation list. -/
noncomputable def equivPermOfValid {perm : List ℕ} (h : IsPermList perm) :
    Equiv.Perm (Fin perm.length) :=
  Equiv.ofBijective
    (fun i : Fin perm.length => ⟨perm[i.val], h.getElem_lt i⟩)
    ((Finite.injective_iff_bijective).mp fun i j hij => by
      have hv : perm[i.val] = perm[j.val] := congrArg Fin.val hij
      exact Fin.ext ((List.Nodup.getElem_inj_iff h.nodup).mp hv))

/-- Permutation graph on `Fin perm.length` determined by inversions of `perm`. -/
def permListGraph (perm : List ℕ) : _root_.SimpleGraph (Fin perm.length) where
  Adj i j := (i < j ∧ perm[j.val] < perm[i.val]) ∨ (j < i ∧ perm[i.val] < perm[j.val])
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with ⟨hlt, _⟩ | ⟨hlt, _⟩ <;> exact lt_irrefl _ hlt⟩

instance instDecidableRelPermListGraphAdj (perm : List ℕ) :
    DecidableRel (permListGraph perm).Adj :=
  fun i j =>
    inferInstanceAs (Decidable ((i < j ∧ perm[j.val] < perm[i.val]) ∨
      (j < i ∧ perm[i.val] < perm[j.val])))

/-- Inversion characterization of adjacency in `permListGraph`. -/
theorem permListGraph_adj_iff (perm : List ℕ) (i j : Fin perm.length) :
    (permListGraph perm).Adj i j ↔
      (i < j ∧ perm[j.val] < perm[i.val]) ∨ (j < i ∧ perm[i.val] < perm[j.val]) :=
  Iff.rfl

/-- For a valid permutation list, `permListGraph` has edge `(i, j)` iff `i` and `j` are inverted
by the induced permutation `equivPermOfValid h`. -/
theorem permListGraph_adj_equivPerm_iff {perm : List ℕ} (h : IsPermList perm)
    (i j : Fin perm.length) :
    (permListGraph perm).Adj i j ↔
      (i < j ∧ equivPermOfValid h j < equivPermOfValid h i) ∨
        (j < i ∧ equivPermOfValid h i < equivPermOfValid h j) :=
  Iff.rfl

/-- The decision problem **MaxCut on represented permutation graphs**: valid permutation
representations `(perm, bound)` whose permutation graph admits a cut of size at least `bound`. -/
def PermutationMaxCut : Set PermutationMaxCutInstance :=
  {x | IsPermList x.perm ∧ x.bound ≤ maxCutEdges (permListGraph x.perm)}

/-- Semantic membership characterization of `PermutationMaxCut`. -/
theorem mem_permutationMaxCut_iff (x : PermutationMaxCutInstance) :
    x ∈ PermutationMaxCut ↔
      IsPermList x.perm ∧ x.bound ≤ maxCutEdges (permListGraph x.perm) :=
  Iff.rfl

/-- Threshold reformulation of `PermutationMaxCut` via minimum monochromatic edges `g(G)`. -/
theorem mem_permutationMaxCut_iff_minMonoEdges (x : PermutationMaxCutInstance) :
    x ∈ PermutationMaxCut ↔
      IsPermList x.perm ∧
        minMonoEdges (permListGraph x.perm) + x.bound ≤ (permListGraph x.perm).edgeSet.ncard := by
  simp only [PermutationMaxCut, Set.mem_ofPred_eq]
  have h := minMonoEdges_add_maxCutEdges (permListGraph x.perm)
  constructor <;> rintro ⟨hv, hb⟩ <;> exact ⟨hv, by omega⟩

/-- Direct witness characterization of `PermutationMaxCut`. -/
theorem mem_permutationMaxCut_iff_exists_colouring (x : PermutationMaxCutInstance) :
    x ∈ PermutationMaxCut ↔
      IsPermList x.perm ∧
        ∃ c : Fin x.perm.length → Bool, x.bound ≤ cutEdgeCount (permListGraph x.perm) c := by
  simp only [PermutationMaxCut, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hv, hb⟩
    obtain ⟨c, hc⟩ := exists_cutEdgeCount_eq_maxCutEdges (permListGraph x.perm)
    exact ⟨hv, c, hc ▸ hb⟩
  · rintro ⟨hv, c, hc⟩
    exact ⟨hv, hc.trans (le_maxCutEdges _ c)⟩

/-- Direct list-based cut counter for `permListGraph perm` with respect to a vertex subset `S`. -/
def permCutCount (perm : List ℕ) (S : List ℕ) : ℕ :=
  ((List.range perm.length).map fun i =>
    ((List.range perm.length).filter fun j =>
      decide (i < j) && decide (perm.getD j 0 < perm.getD i 0) &&
        (decide (i ∈ S) != decide (j ∈ S))).length).sum

private theorem permCutCount_eq_cutEdgeCount (perm : List ℕ) (S : List ℕ) :
    permCutCount perm S = cutEdgeCount (permListGraph perm) (fun i => decide (i.val ∈ S)) := by
  classical
  set G := permListGraph perm
  set c : Fin perm.length → Bool := fun i => decide (i.val ∈ S)
  suffices h2 : 2 * permCutCount perm S = 2 * cutEdgeCount G c by omega
  rw [two_mul_cutEdgeCount]
  let P (i j : Fin perm.length) : Prop :=
    i < j ∧ perm[j.val] < perm[i.val] ∧ c i ≠ c j
  have hupper : permCutCount perm S =
      ((Finset.univ : Finset (Fin perm.length × Fin perm.length)).filter
        (fun p => P p.1 p.2)).card := by
    unfold permCutCount
    have hinner : ∀ i : Fin perm.length,
        ((List.range perm.length).filter fun j =>
          decide (i.val < j) && decide (perm.getD j 0 < perm.getD i.val 0) &&
            (decide (i.val ∈ S) != decide (j ∈ S))).length =
        ((Finset.univ : Finset (Fin perm.length)).filter
          (fun j : Fin perm.length => P i j)).card := by
      intro i
      rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
      refine Finset.card_bij (fun (j : ℕ) hj =>
            ⟨j, List.mem_range.mp (List.mem_filter.mp (List.mem_toFinset.mp hj)).1⟩) ?_ ?_ ?_
      · intro j hj
        have hm := List.mem_filter.mp (List.mem_toFinset.mp hj)
        have hjlt : j < perm.length := List.mem_range.mp hm.1
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, c, Fin.lt_def]
        have hcond := hm.2
        simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlt,
          List.getElem?_eq_getElem i.isLt, Option.getD_some] at hcond
        exact ⟨hcond.1.1, hcond.1.2, hcond.2⟩
      · intro j₁ _ j₂ _ heq
        exact congrArg Fin.val heq
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, c, Fin.lt_def] at hj
        refine ⟨j.val, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_range.mpr j.isLt, ?_⟩),
          rfl⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt,
          List.getElem?_eq_getElem i.isLt, Option.getD_some]
        exact ⟨⟨hj.1, hj.2.1⟩, hj.2.2⟩
    have hlist_sum : ∀ (n : ℕ) (f : ℕ → ℕ),
        ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
      intro n
      induction n with
      | zero => intro f; simp
      | succ n ih => intro f; simp [List.range_succ, Finset.sum_range_succ, ih]
    have hsum :
        ((List.range perm.length).map fun i =>
          ((List.range perm.length).filter fun j =>
            decide (i < j) && decide (perm.getD j 0 < perm.getD i 0) &&
              (decide (i ∈ S) != decide (j ∈ S))).length).sum =
        ∑ i : Fin perm.length,
          ((Finset.univ : Finset (Fin perm.length)).filter
            (fun j : Fin perm.length => P i j)).card := by
      rw [hlist_sum, ← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun i _ => hinner i
    rw [hsum]
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.card_filter]
  let A := (Finset.univ : Finset (Fin perm.length × Fin perm.length)).filter
    (fun p => P p.1 p.2)
  have hAeq : permCutCount perm S = A.card := hupper
  rw [hAeq]
  let B := (Finset.univ : Finset (Fin perm.length × Fin perm.length)).filter
    (fun p => P p.2 p.1)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_filter]
    rintro ⟨i, j⟩ _ h1 h2
    exact lt_asymm h1.1 h2.1
  have hunion : (Finset.univ : Finset (Fin perm.length × Fin perm.length)).filter
      (fun p => G.Adj p.1 p.2 ∧ c p.1 ≠ c p.2) = A ∪ B := by
    ext ⟨i, j⟩
    simp only [A, B, P, G, permListGraph, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨(⟨h1, h2⟩ | ⟨h1, h2⟩), hne⟩
      · exact Or.inl ⟨h1, h2, hne⟩
      · exact Or.inr ⟨h1, h2, Ne.symm hne⟩
    · rintro (⟨h1, h2, hne⟩ | ⟨h1, h2, hne⟩)
      · exact ⟨Or.inl ⟨h1, h2⟩, hne⟩
      · exact ⟨Or.inr ⟨h1, h2⟩, Ne.symm hne⟩
  have hcardB : B.card = A.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · rintro ⟨i, j⟩ h; simpa [A, B] using h
    · rintro ⟨i₁, j₁⟩ _ ⟨i₂, j₂⟩ _ h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
    · rintro ⟨i, j⟩ h; exact ⟨(j, i), by simpa [A, B] using h, rfl⟩
  have hcard_eq : ∀ {inst : DecidablePred (fun p : Fin perm.length × Fin perm.length =>
      G.Adj p.1 p.2 ∧ c p.1 ≠ c p.2)},
      (@Finset.filter _ _ inst Finset.univ).card = (A ∪ B).card := by
    intro inst
    rw [← hunion]
    congr 1
    ext p
    simp
  rw [hcard_eq, Finset.card_union_of_disjoint hdisj, hcardB]
  omega

/-- Deterministic polynomial-time check of a candidate vertex subset `S` for
`PermutationMaxCut`. -/
def checkPermCut (x : PermutationMaxCutInstance) (S : List ℕ) : Bool :=
  isPermListBool x.perm && decide (x.bound ≤ permCutCount x.perm S)

/-- Polynomial-time verifier for `PermutationMaxCut` built via `Cslib.Complexity.subsetVerifier`. -/
def verifier : PermutationMaxCutInstance × List Bool → Bool :=
  Cslib.Complexity.subsetVerifier (fun x => List.range x.perm.length)
    (Function.uncurry checkPermCut)

private def toPair (x : PermutationMaxCutInstance) : List ℕ × ℕ := (x.perm, x.bound)

private theorem computableInPolyTime_toPair :
    ComputableInPolyTime toPair encPermutationMaxCut (encPair (encList encNat) encNat) :=
  of_eq fun _ => rfl

/-- Projecting `perm` from a `PermutationMaxCutInstance` is computable in polynomial time. -/
theorem computableInPolyTime_perm_proj :
    ComputableInPolyTime PermutationMaxCutInstance.perm encPermutationMaxCut (encList encNat) :=
  (fst (encList encNat) encNat).comp computableInPolyTime_toPair

/-- Projecting `bound` from a `PermutationMaxCutInstance` is computable in polynomial time. -/
theorem computableInPolyTime_bound_proj :
    ComputableInPolyTime PermutationMaxCutInstance.bound encPermutationMaxCut encNat :=
  (snd (encList encNat) encNat).comp computableInPolyTime_toPair

private theorem computableInPolyTime_unaryToBinary :
    ComputableInPolyTime (fun n : ℕ => n) encUnary encNat := by
  have hid : ComputableInPolyTime (fun n : ℕ => n) encUnary encUnary := by fun_prop
  have hrep : ComputableInPolyTime (fun n : ℕ => List.replicate n (1 : ℕ))
      encUnary (encList encNat) :=
    replicate hid (const 1)
  exact (binary_sum.comp hrep).of_enc_eq fun n => by simp

/-- Checking validity of a permutation list is computable in deterministic polynomial time. -/
theorem computableInPolyTime_isPermListBool :
    ComputableInPolyTime isPermListBool (encList encNat) encBool := by
  unfold isPermListBool
  have hlen : ComputableInPolyTime (fun p : List ℕ => p.length) (encList encNat) encUnary :=
    length encNat
  have hrange : ComputableInPolyTime (fun p : List ℕ => List.range p.length)
      (encList encNat) (encList encUnary) :=
    (range.comp hlen).of_enc_eq fun _ => rfl
  have hfst := fst (encList encNat) encUnary
  have hsnd := computableInPolyTime_unaryToBinary.comp (snd (encList encNat) encUnary)
  have hmem : ComputableInPolyTime (fun q : List ℕ × ℕ => q.1.any fun a => a == q.2)
      (encPair (encList encNat) encUnary) encBool :=
    (decide_mem hfst hsnd).of_enc_eq fun q => congrArg encBool <| by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, beq_iff_eq, decide_eq_true_eq, Function.comp_apply]
      exact ⟨fun ⟨a, ha, h⟩ => h ▸ ha, fun h => ⟨q.2, h, rfl⟩⟩
  exact allWithInput hrange hmem

private theorem computableInPolyTime_permCutCount :
    ComputableInPolyTime (Function.uncurry permCutCount)
      (encPair (encList encNat) (encList encUnary)) encNat := by
  unfold Function.uncurry permCutCount
  let encL := encPair (encList encNat) (encList encUnary)
  let encI := encPair encL encUnary
  let encJ := encPair encI encUnary
  have hlen : ComputableInPolyTime (fun q : List ℕ × List ℕ => q.1.length) encL encUnary :=
    ((length encNat).comp (fst (encList encNat) (encList encUnary))).of_enc_eq fun _ => rfl
  have hrange : ComputableInPolyTime (fun q : List ℕ × List ℕ => List.range q.1.length)
      encL (encList encUnary) :=
    (range.comp hlen).of_enc_eq fun _ => rfl
  have hpermJ : ComputableInPolyTime (fun r : ((List ℕ × List ℕ) × ℕ) × ℕ => r.1.1.1)
      encJ (encList encNat) :=
    ((fst (encList encNat) (encList encUnary)).comp ((fst encL encUnary).comp (fst encI encUnary)))
  have hSJ : ComputableInPolyTime (fun r : ((List ℕ × List ℕ) × ℕ) × ℕ => r.1.1.2)
      encJ (encList encUnary) :=
    ((snd (encList encNat) (encList encUnary)).comp ((fst encL encUnary).comp (fst encI encUnary)))
  have hiJ : ComputableInPolyTime (fun r : ((List ℕ × List ℕ) × ℕ) × ℕ => r.1.2)
      encJ encUnary :=
    ((snd encL encUnary).comp (fst encI encUnary))
  have hjJ : ComputableInPolyTime (fun r : ((List ℕ × List ℕ) × ℕ) × ℕ => r.2)
      encJ encUnary :=
    snd encI encUnary
  have hlt1 : ComputableInPolyTime
      (fun r : ((List ℕ × List ℕ) × ℕ) × ℕ => decide (r.1.2 < r.2)) encJ encBool :=
    (unary_lt.comp (hiJ.prod hjJ)).of_enc_eq fun _ => rfl
  have hget1 : ComputableInPolyTime
      (fun r : ((List ℕ × List ℕ) × ℕ) × ℕ => r.1.1.1.getD r.2 0) encJ encNat :=
    listGetDWithInput hpermJ hjJ 0
  have hget2 : ComputableInPolyTime
      (fun r : ((List ℕ × List ℕ) × ℕ) × ℕ => r.1.1.1.getD r.1.2 0) encJ encNat :=
    listGetDWithInput hpermJ hiJ 0
  have hlt2 : ComputableInPolyTime
      (fun r : ((List ℕ × List ℕ) × ℕ) × ℕ =>
        decide (r.1.1.1.getD r.2 0 < r.1.1.1.getD r.1.2 0)) encJ encBool :=
    binary_lt' hget1 hget2
  have hmem1 : ComputableInPolyTime
      (fun r : ((List ℕ × List ℕ) × ℕ) × ℕ => decide (r.1.2 ∈ r.1.1.2)) encJ encBool :=
    decide_mem hSJ hiJ
  have hmem2 : ComputableInPolyTime
      (fun r : ((List ℕ × List ℕ) × ℕ) × ℕ => decide (r.2 ∈ r.1.1.2)) encJ encBool :=
    decide_mem hSJ hjJ
  have hbne : ComputableInPolyTime
      (fun r : ((List ℕ × List ℕ) × ℕ) × ℕ =>
        decide (r.1.2 ∈ r.1.1.2) != decide (r.2 ∈ r.1.1.2)) encJ encBool :=
    (bool_xor.comp (hmem1.prod hmem2)).of_enc_eq fun r => congrArg encBool <| by
      cases h1 : decide (r.1.2 ∈ r.1.1.2) <;> cases h2 : decide (r.2 ∈ r.1.1.2) <;> simp [h1, h2]
  have hpred : ComputableInPolyTime
      (fun r : ((List ℕ × List ℕ) × ℕ) × ℕ =>
        decide (r.1.2 < r.2) && decide (r.1.1.1.getD r.2 0 < r.1.1.1.getD r.1.2 0) &&
          (decide (r.1.2 ∈ r.1.1.2) != decide (r.2 ∈ r.1.1.2))) encJ encBool :=
    (bool_and.comp ((bool_and.comp (hlt1.prod hlt2)).prod hbne)).of_enc_eq fun _ => rfl
  have hinner : ComputableInPolyTime
      (fun r : (List ℕ × List ℕ) × ℕ =>
        ((List.range r.1.1.length).filter fun j =>
          decide (r.2 < j) && decide (r.1.1.getD j 0 < r.1.1.getD r.2 0) &&
            (decide (r.2 ∈ r.1.2) != decide (j ∈ r.1.2))).length) encI encNat := by
    have hfilt := filterWithInput
      (test := fun (r : (List ℕ × List ℕ) × ℕ) (j : ℕ) =>
        decide (r.2 < j) && decide (r.1.1.getD j 0 < r.1.1.getD r.2 0) &&
          (decide (r.2 ∈ r.1.2) != decide (j ∈ r.1.2)))
      (hrange.comp (fst encL encUnary)) hpred
    have hlenF := ((length encUnary).comp hfilt).of_enc_eq fun _ => rfl
    exact (computableInPolyTime_unaryToBinary.comp hlenF).of_enc_eq fun _ => rfl
  exact (binary_sum.comp (mapWithInput hrange hinner)).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_checkPermCut :
    ComputableInPolyTime (Function.uncurry checkPermCut)
      (encPair encPermutationMaxCut (encList encUnary)) encBool := by
  unfold Function.uncurry checkPermCut
  have hx := fst encPermutationMaxCut (encList encUnary)
  have hS := snd encPermutationMaxCut (encList encUnary)
  have hv := computableInPolyTime_isPermListBool.comp (computableInPolyTime_perm_proj.comp hx)
  have hc := computableInPolyTime_permCutCount.comp
    ((computableInPolyTime_perm_proj.comp hx).prod hS)
  have hle := binary_le.comp ((computableInPolyTime_bound_proj.comp hx).prod hc)
  exact (bool_and.comp (hv.prod hle)).of_enc_eq fun _ => rfl

/-- `PermutationMaxCut` belongs to `Cslib.Complexity.NP` under standard Lean axioms. -/
theorem permutationMaxCut_mem_NP :
    PermutationMaxCut ∈ Cslib.Complexity.NP encPermutationMaxCut := by
  have hlen : ComputableInPolyTime (fun x : PermutationMaxCutInstance => x.perm.length)
      encPermutationMaxCut encUnary :=
    ((length encNat).comp computableInPolyTime_perm_proj).of_enc_eq fun _ => rfl
  have hrange : ComputableInPolyTime (fun x : PermutationMaxCutInstance => List.range x.perm.length)
      encPermutationMaxCut (encList encUnary) :=
    (range.comp hlen).of_enc_eq fun _ => rfl
  have hverif : ComputableInPolyTime verifier (encPair encPermutationMaxCut encBits) encBool :=
    Cslib.Complexity.computableInPolyTime_subsetVerifier (encγ := encUnary)
      hrange computableInPolyTime_checkPermCut
  refine ⟨Polynomial.X, verifier, hverif, ?_⟩
  have hset : PermutationMaxCut =
      {x : PermutationMaxCutInstance |
        ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ List.range x.perm.length) ∧
          IsPermList x.perm ∧
            x.bound ≤ cutEdgeCount (permListGraph x.perm) (fun i => decide (i.val ∈ S))} := by
    ext x
    rw [mem_permutationMaxCut_iff_exists_colouring]
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hv, c, hc⟩
      let S : Finset ℕ :=
        (Finset.univ : Finset (Fin x.perm.length)).filter (fun i => c i = true) |>.image Fin.val
      refine ⟨S, ?_, hv, ?_⟩
      · intro v hvS
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hvS
        exact List.mem_range.mpr i.isLt
      · have hceq : (fun i : Fin x.perm.length => decide (i.val ∈ S)) = c := by
          funext i
          simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          cases hci : c i
          · simp only [decide_eq_false_iff_not, not_exists, not_and]
            intro j hj hval
            have : j = i := Fin.ext hval
            subst this; simp [hci] at hj
          · simp only [decide_eq_true_eq]
            exact ⟨i, hci, rfl⟩
        rwa [hceq]
    · rintro ⟨S, _, hv, hc⟩
      exact ⟨hv, fun i => decide (i.val ∈ S), hc⟩
  rw [hset]
  refine Cslib.Complexity.isVerifier_subsetVerifier (fun x => ?_) fun x S _ _ => ?_
  · rw [List.length_range, encPermutationMaxCut_apply, Polynomial.eval_X]
    exact (length_le_length_encList encNat x.perm).trans
      (length_le_encPair_left (encList encNat) encNat (x.perm, x.bound))
  · simp only [Function.uncurry_apply_pair, checkPermCut, Bool.and_eq_true,
      isPermListBool_eq_true_iff, decide_eq_true_eq, permCutCount_eq_cutEdgeCount,
      List.mem_toFinset]

/-! ### Base cases and carrier sharpness (standard Lean axioms) -/

/-- Empty permutation instance membership holds iff `bound = 0`. -/
theorem mem_permutationMaxCut_nil_iff (k : ℕ) :
    (⟨[], k⟩ : PermutationMaxCutInstance) ∈ PermutationMaxCut ↔ k = 0 := by
  classical
  have h0 : maxCutEdges (permListGraph []) = 0 := by
    have hsum := minMonoEdges_add_maxCutEdges (permListGraph [])
    have he : (permListGraph []).edgeSet.ncard = 0 := by
      rw [Set.ncard_eq_zero]
      ext e
      induction e using Sym2.ind with | _ a _ => exact Fin.elim0 a
    omega
  simp [PermutationMaxCut, IsPermList, h0]

/-- Invalid permutation lists are rejected from `PermutationMaxCut` regardless of `bound`. -/
theorem not_mem_permutationMaxCut_of_not_valid {x : PermutationMaxCutInstance}
    (h : ¬ IsPermList x.perm) : x ∉ PermutationMaxCut :=
  fun hx => h hx.1

/-- Non-degenerate positive and negative witnesses on the 2-vertex transposition `[1, 0]`:
`K_2` has `maxCutEdges = 1`. -/
theorem mem_permutationMaxCut_two_swap :
    (⟨[1, 0], 1⟩ : PermutationMaxCutInstance) ∈ PermutationMaxCut ∧
      (⟨[1, 0], 2⟩ : PermutationMaxCutInstance) ∉ PermutationMaxCut := by
  classical
  have hv : IsPermList [1, 0] := by
    unfold IsPermList
    change [1, 0].Perm [0, 1]
    exact List.Perm.swap 0 1 []
  have h1 : 1 ≤ maxCutEdges (permListGraph [1, 0]) := by
    have hcut : 1 ≤ cutEdgeCount (permListGraph [1, 0]) (fun i => decide (i.val = 0)) := by
      have heq := (permCutCount_eq_cutEdgeCount [1, 0] [0]).symm
      simp only [List.mem_singleton] at heq
      have hval : permCutCount [1, 0] [0] = 1 := by decide
      rw [heq, hval]
    exact hcut.trans (le_maxCutEdges _ _)
  have hle1 : maxCutEdges (permListGraph [1, 0]) ≤ 1 := by
    have hsum := minMonoEdges_add_maxCutEdges (permListGraph [1, 0])
    have hcard : (permListGraph [1, 0]).edgeSet.ncard ≤ 1 := by
      rw [Set.ncard_eq_toFinset_card' (permListGraph [1, 0]).edgeSet]
      have hsub : (permListGraph [1, 0]).edgeSet.toFinset ⊆ {s((0 : Fin 2), (1 : Fin 2))} := by
        intro e he
        induction e using Sym2.ind with
        | _ a b =>
          simp only [Set.mem_toFinset, _root_.SimpleGraph.mem_edgeSet] at he
          fin_cases a <;> fin_cases b <;> simp_all [permListGraph, Sym2.eq_swap]
      exact (Finset.card_le_card hsub).trans (by simp)
    omega
  exact ⟨⟨hv, h1⟩, fun hx => by linarith [hx.2]⟩

/-- Negative carrier sharpness: duplicate entry `[0, 0]` is rejected by `IsPermList`. -/
theorem not_isPermList_duplicate : ¬ IsPermList [0, 0] := by
  intro h
  have h1 : (1 : ℕ) ∈ ([0, 0] : List ℕ) := h.symm.subset (by decide)
  simp at h1

end CslibFrontier.Complexity
