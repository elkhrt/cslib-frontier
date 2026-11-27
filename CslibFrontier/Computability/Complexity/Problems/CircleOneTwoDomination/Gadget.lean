module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.EUThreeSAT
public import CslibFrontier.Computability.Complexity.Problems.Graph
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Card

import Mathlib.Data.Finset.Max
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push

/-!
# Circle-Graph Clause-and-Consistency Gadget Construction

Discrete circle-chord graph representations, canonical `[0, 2|V|)` endpoint compression, and the
34-vertex clause gadget with 5-vertex claw-anchored connection blocks reducing `EUThreeSAT` to
`[1, 2]`-domination on circle graphs.

## Main definitions

* `Cslib.Complexity.CircleOneTwoDomination.ChordsAlternate`,
  `Cslib.Complexity.CircleOneTwoDomination.IsCircleChordPlacement`,
  `Cslib.Complexity.CircleOneTwoDomination.IsCircleChordGraph`: discrete circle-chord graphs.
* `Cslib.Complexity.CircleOneTwoDomination.reductionGraph`,
  `Cslib.Complexity.CircleOneTwoDomination.reductionBound`: the circle-graph reduction instance.

## Main results

* `Cslib.Complexity.CircleOneTwoDomination.exists_canonical_circleChordPlacement`: canonical
  compression of any finite circle-chord placement into `[0, 2|V|)`.
* `Cslib.Complexity.CircleOneTwoDomination.reductionGraph_isCircleChordGraph`: every
  `IsExactThreeDistinct` formula maps to a circle graph.
-/

public section

namespace Cslib.Complexity.CircleOneTwoDomination

open Cslib.Logic.PL Cslib.Complexity

/-! ### 1. Discrete Circle-Chord Graphs -/

/-- Two chords `(a, b)` and `(c, d)` (with `a < b`, `c < d`) alternate around a circle iff
`a < c < b < d` or `c < a < d < b`. -/
@[expose]
def ChordsAlternate (a b c d : ℕ) : Prop :=
  (a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b)

/-- Executable Boolean test for `ChordsAlternate`. -/
@[expose]
def chordsAlternateBool (a b c d : ℕ) : Bool :=
  (decide (a < c) && decide (c < b) && decide (b < d)) ||
  (decide (c < a) && decide (a < d) && decide (d < b))

theorem chordsAlternateBool_eq_true_iff (a b c d : ℕ) :
    chordsAlternateBool a b c d = true ↔ ChordsAlternate a b c d := by
  simp [chordsAlternateBool, ChordsAlternate, and_assoc]

theorem chordsAlternate_symm {a b c d : ℕ} :
    ChordsAlternate a b c d ↔ ChordsAlternate c d a b :=
  or_comm

theorem chordsAlternate_irrefl (a b : ℕ) : ¬ ChordsAlternate a b a b := by
  rintro (⟨h, _, _⟩ | ⟨h, _, _⟩) <;> exact lt_irrefl _ h

theorem chordsAlternate_add_left (k a b c d : ℕ) :
    ChordsAlternate (k + a) (k + b) (k + c) (k + d) ↔ ChordsAlternate a b c d := by
  simp only [ChordsAlternate, Nat.add_lt_add_iff_left]

/-- A discrete circle-chord placement of `G` in `[0, M)`: every vertex `v` gets a chord
`(l v, r v)` with `l v < r v < M`, all `2 |V|` endpoints are pairwise distinct, and distinct
vertices are adjacent iff their chords alternate. -/
@[expose]
def IsCircleChordPlacement {V : Type*} (G : SimpleGraph V) (l r : V → ℕ) (M : ℕ) : Prop :=
  (∀ v : V, l v < r v ∧ r v < M) ∧
  (∀ u v : V, u ≠ v → l u ≠ l v ∧ l u ≠ r v ∧ r u ≠ l v ∧ r u ≠ r v) ∧
  (∀ u v : V, u ≠ v → (G.Adj u v ↔ ChordsAlternate (l u) (r u) (l v) (r v)))

/-- A simple graph is a **circle graph** if it admits a discrete circle-chord placement. -/
@[expose]
def IsCircleChordGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (M : ℕ) (l r : V → ℕ), IsCircleChordPlacement G l r M

/-- Every finite circle graph admits a canonical placement into `[0, 2 * |V|)`. -/
theorem exists_canonical_circleChordPlacement {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : IsCircleChordGraph G) :
    ∃ l r : V → ℕ, IsCircleChordPlacement G l r (2 * Fintype.card V) := by
  classical
  obtain ⟨M, l, r, hlr, hdisj, hadj⟩ := hG
  let S : Finset ℕ := (Finset.univ.image l) ∪ (Finset.univ.image r)
  have hdisj_img : Disjoint (Finset.univ.image l) (Finset.univ.image r) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hx2
    by_cases huv : u = v
    · subst huv; exact ne_of_lt (hlr u).1 hv.symm
    · exact (hdisj u v huv).2.1 hv.symm
  have hScard : S.card = 2 * Fintype.card V := by
    rw [Finset.card_union_of_disjoint hdisj_img,
      Finset.card_image_of_injective _ (fun u v h ↦ by
        by_contra hne; exact (hdisj u v hne).1 h),
      Finset.card_image_of_injective _ (fun u v h ↦ by
        by_contra hne; exact (hdisj u v hne).2.2.2 h),
      Finset.card_univ, two_mul]
  let rank (x : ℕ) : ℕ := (S.filter (· < x)).card
  have hrank_lt : ∀ x ∈ S, rank x < S.card := fun x hx ↦
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.filter_subset _ _, fun heq ↦ by
        have : x ∈ S.filter (· < x) := heq.symm ▸ hx
        exact lt_irrefl x (Finset.mem_filter.mp this).2⟩)
  have hrank_mono : ∀ x ∈ S, ∀ y ∈ S, x < y → rank x < rank y := fun x hx y _ hxy ↦
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨fun z hz ↦ Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2.trans hxy⟩,
       fun heq ↦ by
         have : x ∈ S.filter (· < x) := heq.symm ▸ Finset.mem_filter.mpr ⟨hx, hxy⟩
         exact lt_irrefl x (Finset.mem_filter.mp this).2⟩)
  have hrank_inj : ∀ x ∈ S, ∀ y ∈ S, rank x = rank y → x = y := fun x hx y hy heq ↦ by
    rcases lt_trichotomy x y with hlt | rfl | hgt
    · exact absurd heq (ne_of_lt (hrank_mono x hx y hy hlt))
    · rfl
    · exact absurd heq.symm (ne_of_lt (hrank_mono y hy x hx hgt))
  have hlS : ∀ v, l v ∈ S := fun v ↦
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))
  have hrS : ∀ v, r v ∈ S := fun v ↦
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))
  refine ⟨rank ∘ l, rank ∘ r, fun v ↦ ⟨hrank_mono _ (hlS v) _ (hrS v) (hlr v).1,
    hScard ▸ hrank_lt _ (hrS v)⟩, fun u v huv ↦ ?_, fun u v huv ↦ ?_⟩
  · have hd := hdisj u v huv
    exact ⟨fun h ↦ hd.1 (hrank_inj _ (hlS u) _ (hlS v) h),
      fun h ↦ hd.2.1 (hrank_inj _ (hlS u) _ (hrS v) h),
      fun h ↦ hd.2.2.1 (hrank_inj _ (hrS u) _ (hlS v) h),
      fun h ↦ hd.2.2.2 (hrank_inj _ (hrS u) _ (hrS v) h)⟩
  · rw [hadj u v huv]
    have hlt_iff : ∀ x ∈ S, ∀ y ∈ S, rank x < rank y ↔ x < y := fun x hx y hy ↦
      ⟨fun h ↦ by
        rcases lt_trichotomy x y with hlt | rfl | hgt
        · exact hlt
        · exact absurd h (lt_irrefl _)
        · exact absurd (hrank_mono y hy x hx hgt) (not_lt.mpr h.le),
       hrank_mono x hx y hy⟩
    simp only [Function.comp_apply, ChordsAlternate,
      hlt_iff _ (hlS u) _ (hlS v), hlt_iff _ (hlS v) _ (hrS u), hlt_iff _ (hrS u) _ (hrS v),
      hlt_iff _ (hlS v) _ (hlS u), hlt_iff _ (hlS u) _ (hrS v), hlt_iff _ (hrS v) _ (hrS u)]

/-! ### 2. The 34-Vertex Clause Gadget (128-Slot Block) -/

/-- Left endpoints of the 34 vertices of a clause gadget inside `[0, 128)`. -/
@[expose]
def baseL (g : Fin 34) : ℕ :=
  match g.1 with
  | 0 => 0   | 1 => 11  | 2 => 12  | 3 => 13  | 4 => 14  | 5 => 15
  | 6 => 30  | 7 => 41  | 8 => 42  | 9 => 43  | 10 => 44 | 11 => 45
  | 12 => 60 | 13 => 71 | 14 => 72 | 15 => 73 | 16 => 74 | 17 => 75
  | 18 => 90 | 19 => 91 | 20 => 92 | 21 => 93 | 22 => 97 | 23 => 99
  | 24 => 100 | 25 => 103 | 26 => 105 | 27 => 106 | 28 => 110
  | 29 => 113 | 30 => 119 | 31 => 121 | 32 => 122 | _ => 123

/-- Right endpoints of the 34 vertices of a clause gadget inside `[0, 128)`. -/
@[expose]
def baseR (g : Fin 34) : ℕ :=
  match g.1 with
  | 0 => 16  | 1 => 102 | 2 => 101 | 3 => 18  | 4 => 17  | 5 => 29
  | 6 => 46  | 7 => 109 | 8 => 108 | 9 => 48  | 10 => 47 | 11 => 59
  | 12 => 76 | 13 => 116 | 14 => 115 | 15 => 78 | 16 => 77 | 17 => 89
  | 18 => 96 | 19 => 95 | 20 => 94 | 21 => 98 | 22 => 104 | 23 => 107
  | 24 => 114 | 25 => 117 | 26 => 111 | 27 => 112 | 28 => 118
  | 29 => 120 | 30 => 124 | 31 => 127 | 32 => 126 | _ => 125

/-- Adjacency inside the 34-vertex clause gadget. -/
@[expose]
def clauseAdj (g h : Fin 34) : Bool :=
  chordsAlternateBool (baseL g) (baseR g) (baseL h) (baseR h)

/-- Start offset of the 10-point truth or false interval for literal `r ∈ {0, 1, 2}`. -/
@[expose]
def slotBase (r : ℕ) (isTrue : Bool) : ℕ :=
  30 * r + (if isTrue then 1 else 19)

/-- Canonical size-7 `[1, 2]`-dominating set of a clause gadget for `(b0, b1, b2) ≠ (0, 0, 0)`. -/
@[expose]
def clauseDomList (b0 b1 b2 : Bool) : List (Fin 34) :=
  let lit0 : Fin 34 := if b0 then 0 else 5
  let lit1 : Fin 34 := if b1 then 6 else 11
  let lit2 : Fin 34 := if b2 then 12 else 17
  let uw : List (Fin 34) :=
    if b1 then [23, 28]
    else if b0 then [25, 26]
    else [24, 27]
  [lit0, lit1, lit2, 21, 30] ++ uw

theorem baseL_lt_baseR (g : Fin 34) : baseL g < baseR g ∧ baseR g < 128 := by
  revert g; decide

theorem base_endpoints_disjoint (g h : Fin 34) (hne : g ≠ h) :
    baseL g ≠ baseL h ∧ baseL g ≠ baseR h ∧ baseR g ≠ baseL h ∧ baseR g ≠ baseR h := by
  revert g h hne; decide

theorem base_outside_slots (g : Fin 34) (r : Fin 3) (isTrue : Bool) (off : Fin 10) :
    baseL g ≠ slotBase r.1 isTrue + off.1 ∧ baseR g ≠ slotBase r.1 isTrue + off.1 := by
  revert g r isTrue off; decide

theorem clauseDomList_valid (b0 b1 b2 : Bool) (hsat : b0 = true ∨ b1 = true ∨ b2 = true) :
    (clauseDomList b0 b1 b2).Nodup ∧
    (clauseDomList b0 b1 b2).length = 7 ∧
    ∀ v : Fin 34, v ∉ clauseDomList b0 b1 b2 →
      let c := ((clauseDomList b0 b1 b2).filter (clauseAdj v)).length
      1 ≤ c ∧ c ≤ 2 := by
  revert b0 b1 b2 hsat; decide

theorem clauseDomList_no_a (b0 b1 b2 : Bool) (s : Fin 3) (q : Fin 2) :
    (⟨6 * s.1 + 1 + q.1, by omega⟩ : Fin 34) ∉ clauseDomList b0 b1 b2 := by
  revert b0 b1 b2 s q; decide

theorem clause_no_single_dom_uw :
    ∀ g : Fin 34,
      ∃ u ∈ ([23, 24, 25, 26, 27, 28] : List (Fin 34)), u ≠ g ∧ clauseAdj u g = false := by
  decide

theorem clause_uw_neighbors_in_B5 :
    ∀ u ∈ ([23, 24, 25, 26, 27, 28] : List (Fin 34)), ∀ g : Fin 34,
      clauseAdj u g = true →
      g ∈ ([1, 2, 7, 8, 13, 14, 22, 23, 24, 25, 26, 27, 28, 29] : List (Fin 34)) := by
  decide

theorem clause_p_neighbors (r : Fin 3) (q : Fin 2) (g : Fin 34) :
    clauseAdj ⟨6 * r.1 + 3 + q.1, by omega⟩ g = true →
      g.1 = 6 * r.1 ∨ g.1 = 6 * r.1 + 5 := by
  revert r q g; decide

theorem clause_c_leaves_only :
    (∀ l ∈ ([18, 19, 20] : List (Fin 34)), ∀ g : Fin 34, clauseAdj l g = true ↔ g = 21) ∧
    (∀ l ∈ ([31, 32, 33] : List (Fin 34)), ∀ g : Fin 34, clauseAdj l g = true ↔ g = 30) := by
  decide

theorem clause_all_false_forces_a1 :
    let B5 : List (Fin 34) := [1, 2, 7, 8, 13, 14, 22, 23, 24, 25, 26, 27, 28, 29]
    ∀ x ∈ B5, ∀ y ∈ B5,
      (∀ v : Fin 34, v ∉ ([5, 11, 17, 21, 30, x, y] : List (Fin 34)) →
        let c := (([5, 11, 17, 21, 30, x, y] : List (Fin 34)).filter (clauseAdj v)).length
        1 ≤ c ∧ c ≤ 2) →
      x = 7 ∨ x = 8 ∨ y = 7 ∨ y = 8 := by
  decide

theorem base_contains_slot_point (g : Fin 34) (r : Fin 3) (isTrue : Bool) (b : Bool) :
    let pos := slotBase r.1 isTrue + (if b then 8 else 0)
    (baseL g < pos ∧ pos < baseR g) ↔
      (g.1 = 6 * r.1 + (if isTrue then 0 else 5)) ∨
      ∃ s : Fin 3, (if isTrue then s.1 < r.1 else s.1 ≤ r.1) ∧
        (g.1 = 6 * s.1 + 1 ∨ g.1 = 6 * s.1 + 2) := by
  revert g r isTrue b; decide

theorem base_not_in_claw (g : Fin 34) (r : Fin 3) (isTrue : Bool) :
    ¬ (slotBase r.1 isTrue + 1 ≤ baseL g ∧ baseL g ≤ slotBase r.1 isTrue + 9) ∧
    ¬ (slotBase r.1 isTrue + 1 ≤ baseR g ∧ baseR g ≤ slotBase r.1 isTrue + 9) := by
  revert g r isTrue; decide

theorem slotBase_disjoint (r1 r2 : Fin 3) (b1 b2 : Bool) (o1 o2 : Fin 10)
    (h : slotBase r1.1 b1 + o1.1 = slotBase r2.1 b2 + o2.1) :
    r1 = r2 ∧ b1 = b2 ∧ o1 = o2 := by
  revert r1 r2 b1 b2 o1 o2 h; decide

theorem slotBase_lt_128 (r : Fin 3) (b : Bool) (o : Fin 10) :
    slotBase r.1 b + o.1 < 128 := by
  revert r b o; decide

/-! ### 3. Full Reduction Graph `G(φ)` for `EUThreeSAT` -/

/-- Literal `(var, pol)` at occurrence `idx = 3 * j + r` of `φ`. -/
@[expose]
def literalAt (φ : CNF ℕ) (idx : ℕ) : Literal ℕ :=
  (φ.getD (idx / 3) []).getD (idx % 3) (0, false)

/-- Next occurrence index `idx' > idx` (`idx' < 3 * φ.length`) of the same variable as `idx`. -/
@[expose]
def nextOcc (φ : CNF ℕ) (idx : ℕ) : Option ℕ :=
  (List.range (3 * φ.length)).find? fun idx' ↦
    decide (idx < idx') && decide ((literalAt φ idx').1 = (literalAt φ idx).1)

/-- Number of variable repetitions `t = ∑_x (occ(x) - 1)` in `φ`. -/
@[expose]
def repetitionCount (φ : CNF ℕ) : ℕ :=
  (List.range (3 * φ.length)).countP fun idx ↦ (nextOcc φ idx).isSome

/-- Target `[1, 2]`-domination bound `k = 7m + 2t`. -/
@[expose]
def reductionBound (φ : CNF ℕ) : ℕ :=
  7 * φ.length + 2 * repetitionCount φ

/-- Active vertex IDs of `G(φ)`. -/
@[expose]
def redVertices (φ : CNF ℕ) : List ℕ :=
  let m := φ.length
  List.range (34 * m) ++
    ((List.range (3 * m)).filter fun idx ↦ (nextOcc φ idx).isSome).flatMap fun idx ↦
      [0, 1].flatMap fun b ↦
        let s := 2 * idx + b
        (List.range 5).map fun q ↦ 34 * m + 5 * s + q

/-- Left endpoint of vertex `v` in `G(φ)` (within `[0, 128 * m)`). -/
@[expose]
def chordL (φ : CNF ℕ) (v : ℕ) : ℕ :=
  let m := φ.length
  if v < 34 * m then
    128 * (v / 34) + baseL ⟨v % 34, Nat.mod_lt _ (by decide)⟩
  else
    let off := v - 34 * m
    let s := off / 5
    let q := off % 5
    let idx := s / 2
    let isTrue := decide (s % 2 = 0)
    let sb := 128 * (idx / 3) + slotBase (idx % 3) isTrue
    match q with
    | 0 => sb + 8
    | 1 => sb + 4
    | 2 => sb + 1
    | 3 => sb + 2
    | _ => sb + 3

/-- Right endpoint of vertex `v` in `G(φ)` (within `[0, 128 * m)`). -/
@[expose]
def chordR (φ : CNF ℕ) (v : ℕ) : ℕ :=
  let m := φ.length
  if v < 34 * m then
    128 * (v / 34) + baseR ⟨v % 34, Nat.mod_lt _ (by decide)⟩
  else
    let off := v - 34 * m
    let s := off / 5
    let q := off % 5
    let idx := s / 2
    let isTrue := decide (s % 2 = 0)
    let sb := 128 * (idx / 3) + slotBase (idx % 3) isTrue
    match q with
    | 0 =>
      match nextOcc φ idx with
      | some idx' =>
        let samePol := decide ((literalAt φ idx).2 = (literalAt φ idx').2)
        let isTrue' := if samePol then !isTrue else isTrue
        128 * (idx' / 3) + slotBase (idx' % 3) isTrue'
      | none => sb + 9
    | 1 => sb + 9
    | 2 => sb + 7
    | 3 => sb + 6
    | _ => sb + 5

/-- Edges of `G(φ)`: all pairs `(u, v)` with `u, v ∈ redVertices φ`, `u < v`, and alternating
chords. -/
@[expose]
def redEdges (φ : CNF ℕ) : List (ℕ × ℕ) :=
  let V := redVertices φ
  V.flatMap fun u ↦
    (V.filter fun v ↦
      decide (u < v) && chordsAlternateBool (chordL φ u) (chordR φ u) (chordL φ v) (chordR φ v)).map
      fun v ↦ (u, v)

/-- The circle graph `G(φ)` of the reduction (`Cslib.Complexity.Graph`). -/
@[expose]
def reductionGraph (φ : CNF ℕ) : Graph :=
  ⟨redVertices φ, redEdges φ⟩

/-! ### 4. Structural Properties & Circle-Chord Placement -/

theorem mem_redVertices_iff {φ : CNF ℕ} {v : ℕ} :
    v ∈ redVertices φ ↔
      v < 34 * φ.length ∨
      ∃ idx < 3 * φ.length, (nextOcc φ idx).isSome ∧
        ∃ b < 2, ∃ q < 5, v = 34 * φ.length + 5 * (2 * idx + b) + q := by
  simp only [redVertices, List.mem_append, List.mem_range, List.mem_flatMap, List.mem_filter,
    List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (h | ⟨idx, ⟨hidx, hnext⟩, b, hb, q, hq, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨idx, hidx, hnext, b, by rcases hb with rfl | rfl <;> omega, q, hq, rfl⟩
  · rintro (h | ⟨idx, hidx, hnext, b, hb, q, hq, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨idx, ⟨hidx, hnext⟩, b, by omega, q, hq, rfl⟩

theorem nodup_redVertices (φ : CNF ℕ) : (redVertices φ).Nodup := by
  unfold redVertices
  refine List.nodup_append.mpr ⟨List.nodup_range, ?_, ?_⟩
  · refine List.nodup_flatMap.mpr ⟨fun idx _ ↦ ?_, (List.nodup_range.filter _).imp_of_mem ?_⟩
    · refine List.nodup_flatMap.mpr ⟨fun b _ ↦ List.nodup_range.map fun q1 q2 h ↦ by omega,
        (by decide : ([0, 1] : List ℕ).Nodup).imp ?_⟩
      intro b1 b2 hne a ha1 ha2
      simp only [List.mem_map, List.mem_range] at ha1 ha2
      obtain ⟨q1, hq1, rfl⟩ := ha1; obtain ⟨q2, hq2, h⟩ := ha2; omega
    · intro idx1 idx2 _ _ hne a ha1 ha2
      simp only [List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at ha1 ha2
      obtain ⟨b1, hb1, q1, hq1, rfl⟩ := ha1; obtain ⟨b2, hb2, q2, hq2, h⟩ := ha2
      rcases hb1 with rfl | rfl <;> rcases hb2 with rfl | rfl <;> omega
  · intro u hu v hv heq; subst heq
    simp only [List.mem_range, List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false] at hu hv
    obtain ⟨_, _, _, _, _, _, rfl⟩ := hv; omega

theorem reductionGraph_adj_iff {φ : CNF ℕ} {u v : ℕ}
    (hu : u ∈ redVertices φ) (hv : v ∈ redVertices φ) (hne : u ≠ v) :
    (reductionGraph φ).toSimpleGraph.Adj u v ↔
      ChordsAlternate (chordL φ u) (chordR φ u) (chordL φ v) (chordR φ v) := by
  rw [Graph.toSimpleGraph_adj]
  simp only [reductionGraph, redEdges, List.mem_flatMap, List.mem_map, List.mem_filter,
    Bool.and_eq_true, decide_eq_true_eq, chordsAlternateBool_eq_true_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨_, ⟨a, _, b, ⟨_, _, halt⟩, rfl, rfl⟩ | ⟨a, _, b, ⟨_, _, halt⟩, rfl, rfl⟩⟩
    · exact halt
    · exact chordsAlternate_symm.mp halt
  · intro halt
    refine ⟨hne, ?_⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨u, hu, v, ⟨hv, hlt, halt⟩, rfl, rfl⟩
    · exact Or.inr ⟨v, hv, u, ⟨hu, hgt, chordsAlternate_symm.mp halt⟩, rfl, rfl⟩

/-- Exact characterization of `nextOcc` on an `IsExactThreeDistinct` formula. -/
theorem nextOcc_spec {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct) {idx idx' : ℕ}
    (h : nextOcc φ idx = some idx') :
    idx < idx' ∧ idx' < 3 * φ.length ∧
    (literalAt φ idx').1 = (literalAt φ idx).1 ∧
    idx / 3 < idx' / 3 ∧
    (∀ mid, idx < mid → mid < idx' → (literalAt φ mid).1 ≠ (literalAt φ idx).1) := by
  unfold nextOcc at h
  have hmem := List.mem_of_find?_eq_some h
  have hpred := List.find?_some h
  simp only [List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hmem hpred
  have hfirst : ∀ mid, idx < mid → mid < idx' → (literalAt φ mid).1 ≠ (literalAt φ idx).1 := by
    intro mid h1 h2 heq
    obtain ⟨_, xs, ys, hsplit, hnone⟩ := List.find?_eq_some_iff_append.mp h
    have hlen_xs : xs.length = idx' := by
      have hidx_eq : (List.range (3 * φ.length))[xs.length]'(by
          rw [hsplit]; simp) = idx' := by
        simp [hsplit]
      rw [List.getElem_range] at hidx_eq
      exact hidx_eq
    have hmid_mem : mid ∈ xs := by
      have hget : (List.range (3 * φ.length))[mid]'(by simp; omega) = mid := List.getElem_range _
      rw [← hget]
      have hlt_xs : mid < xs.length := by omega
      have : (xs ++ idx' :: ys)[mid]'(by simp; omega) = xs[mid]'hlt_xs :=
        List.getElem_append_left hlt_xs
      have hsplit_get : (List.range (3 * φ.length))[mid]'(by simp; omega) = xs[mid]'hlt_xs := by
        simpa [hsplit] using this
      rw [hsplit_get]; exact List.getElem_mem hlt_xs
    have hbf := hnone mid hmid_mem
    simp [h1, heq] at hbf
  have hclause_lt : idx / 3 < idx' / 3 := by
    have hle : idx / 3 ≤ idx' / 3 := Nat.div_le_div_right hpred.1.le
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      have hj : idx / 3 < φ.length := by omega
      have hc := hφ (φ[idx / 3]) (List.getElem_mem hj)
      have hlen : (φ[idx / 3]).length = 3 := hc.1
      have hnd : ((φ[idx / 3]).map Prod.fst).Nodup := hc.2
      have hget1 : literalAt φ idx = (φ[idx / 3])[idx % 3]'(by omega) := by
        simp [literalAt, hj, hlen, Nat.mod_lt idx (by decide : 0 < 3)]
      have hget2 : literalAt φ idx' = (φ[idx / 3])[idx' % 3]'(by omega) := by
        simp [literalAt, heq.symm, hj, hlen, Nat.mod_lt idx' (by decide : 0 < 3)]
      have hmod_ne : idx % 3 ≠ idx' % 3 := by omega
      have hvar_eq : ((φ[idx / 3]).map Prod.fst)[idx' % 3]'(by simp [hlen]; omega) =
          ((φ[idx / 3]).map Prod.fst)[idx % 3]'(by simp [hlen]; omega) := by
        simp only [List.getElem_map, ← hget1, ← hget2, hpred.2]
      exact hmod_ne.symm ((List.Nodup.getElem_inj_iff hnd).mp hvar_eq)
  exact ⟨hpred.1, hmem, hpred.2, hclause_lt, hfirst⟩

theorem nextOcc_injective {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct) {a b c : ℕ}
    (ha : nextOcc φ a = some c) (hb : nextOcc φ b = some c) : a = b := by
  obtain ⟨hac, _, hva, _, hfa⟩ := nextOcc_spec hφ ha
  obtain ⟨hbc, _, hvb, _, hfb⟩ := nextOcc_spec hφ hb
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · exact absurd (hvb.symm.trans hva) (hfa b hlt hbc)
  · rfl
  · exact absurd (hva.symm.trans hvb) (hfb a hgt hac)

private def connOff (s : Bool) (q : ℕ) : ℕ :=
  if s then match q with | 0 => 8 | 1 => 4 | 2 => 1 | 3 => 2 | _ => 3
  else match q with | 0 => 0 | 1 => 9 | 2 => 7 | 3 => 6 | _ => 5

private lemma connOff_lt_10 (s : Bool) (q : ℕ) : connOff s q < 10 := by
  cases s <;> (rcases q with _ | _ | _ | _ | _ <;>
    simp only [connOff, Bool.false_eq_true, ↓reduceIte] <;> omega)

private lemma connOff_pos {s : Bool} {q : ℕ} (h : s = true ∨ q ≠ 0) : 0 < connOff s q := by
  cases s <;> rcases q with _ | _ | _ | _ | _
  · exfalso; rcases h with h | h <;> simp at h
  all_goals simp only [connOff, Bool.false_eq_true, ↓reduceIte]; omega

private lemma connOff_injective {s1 s2 : Bool} {q1 q2 : ℕ}
    (hq1 : q1 < 5) (hq2 : q2 < 5)
    (h1 : s1 = true ∨ q1 ≠ 0) (h2 : s2 = true ∨ q2 ≠ 0)
    (heq : connOff s1 q1 = connOff s2 q2) : q1 = q2 ∧ s1 = s2 := by
  cases s1 <;> cases s2 <;>
    rcases (show q1 = 0 ∨ q1 = 1 ∨ q1 = 2 ∨ q1 = 3 ∨ q1 = 4 by omega) with
      rfl | rfl | rfl | rfl | rfl <;>
    rcases (show q2 = 0 ∨ q2 = 1 ∨ q2 = 2 ∨ q2 = 3 ∨ q2 = 4 by omega) with
      rfl | rfl | rfl | rfl | rfl <;>
    simp_all [connOff]

/-- Exact chord endpoint bounds and pairwise disjointness for `reductionGraph φ`. -/
theorem reductionGraph_isCircleChordPlacement {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct) :
    IsCircleChordPlacement (reductionGraph φ).induced
      (fun v ↦ chordL φ v.1) (fun v ↦ chordR φ v.1) (128 * φ.length) := by
  have hbounds : ∀ v ∈ redVertices φ, chordL φ v < chordR φ v ∧ chordR φ v < 128 * φ.length := by
    intro v hv
    rcases mem_redVertices_iff.mp hv with hcl | ⟨idx, hidx, hnext, b, hb, q, hq, rfl⟩
    · simp only [chordL, chordR, hcl, ↓reduceIte]
      have hlt := baseL_lt_baseR ⟨v % 34, Nat.mod_lt _ (by decide)⟩
      have hdiv : v / 34 < φ.length := by omega
      omega
    · have hge : ¬ (34 * φ.length + 5 * (2 * idx + b) + q < 34 * φ.length) := by omega
      have hoff : (34 * φ.length + 5 * (2 * idx + b) + q - 34 * φ.length) / 5 = 2 * idx + b := by
        omega
      have hmod5 : (34 * φ.length + 5 * (2 * idx + b) + q - 34 * φ.length) % 5 = q := by omega
      have hdiv2 : (2 * idx + b) / 2 = idx := by omega
      simp only [chordL, chordR, hge, ↓reduceIte, hoff, hmod5, hdiv2]
      have hsb9 : slotBase (idx % 3) (decide ((2 * idx + b) % 2 = 0)) + 9 < 128 :=
        slotBase_lt_128 ⟨idx % 3, Nat.mod_lt _ (by decide)⟩ (decide ((2 * idx + b) % 2 = 0)) 9
      have hj_lt : idx / 3 < φ.length := by omega
      rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 by omega) with rfl | rfl | rfl | rfl | rfl
      · obtain ⟨idx', hnext_eq⟩ := Option.isSome_iff_exists.mp hnext
        rw [hnext_eq]
        obtain ⟨_, hidx', _, hcl_lt, _⟩ := nextOcc_spec hφ hnext_eq
        have hj'_lt : idx' / 3 < φ.length := by omega
        have hsb'0 : slotBase (idx' % 3)
            (if decide ((literalAt φ idx).2 = (literalAt φ idx').2)
             then !decide ((2 * idx + b) % 2 = 0) else decide ((2 * idx + b) % 2 = 0)) + 0 < 128 :=
          slotBase_lt_128 ⟨idx' % 3, Nat.mod_lt _ (by decide)⟩ _ 0
        simp only at *; omega
      all_goals simp only at *; omega
  -- Helper: decompose any endpoint of `v ∈ redVertices φ` into `(clause, slot_or_base)`
  -- and prove injectivity across distinct vertices.
  have hdisj : ∀ u ∈ redVertices φ, ∀ v ∈ redVertices φ, u ≠ v →
      chordL φ u ≠ chordL φ v ∧ chordL φ u ≠ chordR φ v ∧
      chordR φ u ≠ chordL φ v ∧ chordR φ u ≠ chordR φ v := by
    have htag : ∀ u ∈ redVertices φ, ∀ v ∈ redVertices φ,
        (∀ su sv : Bool,
          (if su then chordL φ u else chordR φ u) = (if sv then chordL φ v else chordR φ v) →
          u = v ∧ su = sv) := by
      intro u hu v hv
      have hmod_clause : ∀ w ∈ redVertices φ, ∀ sw : Bool,
          let p := if sw then chordL φ w else chordR φ w
          p / 128 < φ.length ∧
          (w < 34 * φ.length →
            p / 128 = w / 34 ∧
              p % 128 = (if sw then baseL else baseR) ⟨w % 34, Nat.mod_lt _ (by decide)⟩) ∧
          (∀ idx b q, w = 34 * φ.length + 5 * (2 * idx + b) + q → idx < 3 * φ.length → b < 2 →
            q < 5 →
            (sw = true ∨ q ≠ 0) →
            p / 128 = idx / 3 ∧
            p % 128 = slotBase (idx % 3) (decide (b = 0)) + connOff sw q) := by
        intro w hw sw
        rcases mem_redVertices_iff.mp hw with hcl | ⟨idx, hidx, hnext, b, hb, q, hq, rfl⟩
        · have hlt := baseL_lt_baseR ⟨w % 34, Nat.mod_lt _ (by decide)⟩
          cases sw <;> simp only [chordL, chordR, hcl, Bool.false_eq_true, ↓reduceIte]
          · refine ⟨by omega, fun _ ↦ ⟨by omega, by omega⟩, fun _ _ _ h _ _ _ _ ↦ by omega⟩
          · refine ⟨by omega, fun _ ↦ ⟨by omega, by omega⟩, fun _ _ _ h _ _ _ _ ↦ by omega⟩
        · have hge : ¬ (34 * φ.length + 5 * (2 * idx + b) + q < 34 * φ.length) := by omega
          have hoff : (34 * φ.length + 5 * (2 * idx + b) + q - 34 * φ.length) / 5 =
            2 * idx + b := by omega
          have hmod5 : (34 * φ.length + 5 * (2 * idx + b) + q - 34 * φ.length) % 5 = q := by omega
          have hdiv2 : (2 * idx + b) / 2 = idx := by omega
          have hmod2 : decide ((2 * idx + b) % 2 = 0) = decide (b = 0) := by
            by_cases hb0 : b = 0 <;> simp [hb0]; omega
          have hsb9 : slotBase (idx % 3) (decide (b = 0)) + 9 < 128 :=
            slotBase_lt_128 ⟨idx % 3, Nat.mod_lt _ (by decide)⟩ (decide (b = 0)) 9
          cases sw
          · refine ⟨?_, fun h ↦ by omega, fun idx2 b2 q2 heq _ hb2 hq2 hne ↦ ?_⟩
            · simp only [chordR, hge, Bool.false_eq_true, ↓reduceIte, hoff, hmod5, hdiv2, hmod2]
              rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨
                q = 4 by omega) with rfl | rfl | rfl | rfl | rfl
              · obtain ⟨idx', hnext_eq⟩ := Option.isSome_iff_exists.mp hnext
                rw [hnext_eq]
                obtain ⟨_, hidx', _, _, _⟩ := nextOcc_spec hφ hnext_eq
                have hsb'0 : slotBase (idx' % 3)
                    (if decide ((literalAt φ idx).2 = (literalAt φ idx').2) then !decide (b = 0)
                     else decide (b = 0)) + 0 < 128 :=
                  slotBase_lt_128 ⟨idx' % 3, Nat.mod_lt _ (by decide)⟩ _ 0
                simp only at *; omega
              all_goals simp only at *; omega
            · have hq0 : q2 ≠ 0 := hne.resolve_left (by decide)
              have hidx_eq : idx2 = idx := by omega
              have hb_eq : b2 = b := by omega
              have hq_eq : q2 = q := by omega
              subst hidx_eq hb_eq hq_eq
              simp only [chordR, hge, Bool.false_eq_true, ↓reduceIte, hoff, hmod5, hdiv2, hmod2,
                connOff]
              rcases (show q2 = 1 ∨ q2 = 2 ∨ q2 = 3 ∨ q2 = 4 by omega) with rfl | rfl | rfl | rfl
              all_goals simp only at *; exact ⟨by omega, by omega⟩
          · refine ⟨?_, fun h ↦ by omega, fun idx2 b2 q2 heq _ hb2 hq2 _ ↦ ?_⟩
            · simp only [chordL, hge, ↓reduceIte, hoff, hmod5, hdiv2, hmod2]
              rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨
                q = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> (simp only at *; omega)
            · have hidx_eq : idx2 = idx := by omega
              have hb_eq : b2 = b := by omega
              have hq_eq : q2 = q := by omega
              subst hidx_eq hb_eq hq_eq
              simp only [chordL, hge, ↓reduceIte, hoff, hmod5, hdiv2, hmod2, connOff]
              rcases (show q2 = 0 ∨ q2 = 1 ∨ q2 = 2 ∨ q2 = 3 ∨
                q2 = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
                (simp only at *; exact ⟨by omega, by omega⟩)
      intro su sv heq
      have hdiv_eq : (if su then chordL φ u else chordR φ u) / 128 =
          (if sv then chordL φ v else chordR φ v) / 128 := by rw [heq]
      have hmod_eq : (if su then chordL φ u else chordR φ u) % 128 =
          (if sv then chordL φ v else chordR φ v) % 128 := by rw [heq]
      have hRe : ∀ idx b, b < 2 → (nextOcc φ idx).isSome →
          let w := 34 * φ.length + 5 * (2 * idx + b) + 0
          ∃ idx' isTrue', nextOcc φ idx = some idx' ∧
            isTrue' = (if decide ((literalAt φ idx).2 = (literalAt φ idx').2) then !decide (b = 0)
              else decide (b = 0)) ∧
            (chordR φ w) / 128 = idx' / 3 ∧
            (chordR φ w) % 128 = slotBase (idx' % 3) isTrue' + 0 := by
        intro idx b hb hnext
        obtain ⟨idx', hnext_eq⟩ := Option.isSome_iff_exists.mp hnext
        have hge : ¬ (34 * φ.length + 5 * (2 * idx + b) + 0 < 34 * φ.length) := by omega
        have hoff : (34 * φ.length + 5 * (2 * idx + b) + 0 - 34 * φ.length) / 5 = 2 * idx + b := by
          omega
        have hmod5 : (34 * φ.length + 5 * (2 * idx + b) + 0 - 34 * φ.length) % 5 = 0 := by omega
        have hdiv2 : (2 * idx + b) / 2 = idx := by omega
        have hmod2 : decide ((2 * idx + b) % 2 = 0) = decide (b = 0) := by
          by_cases hb0 : b = 0 <;> simp [hb0]; omega
        let isTrue' := if decide ((literalAt φ idx).2 = (literalAt φ idx').2) then !decide (b = 0)
          else decide (b = 0)
        have hsb' : slotBase (idx' % 3) isTrue' + 0 < 128 :=
          slotBase_lt_128 ⟨idx' % 3, Nat.mod_lt _ (by decide)⟩ isTrue' 0
        refine ⟨idx', isTrue', hnext_eq, rfl, ?_, ?_⟩ <;>
          (simp only [chordR, hge, ↓reduceIte, hoff, hmod5, hdiv2, hmod2, hnext_eq];
            dsimp only [isTrue'] at hsb' ⊢; omega)
      rcases mem_redVertices_iff.mp hu with hu_cl | ⟨iu, hiu, hnu, bu, hbu, qu, hqu, rfl⟩ <;>
      rcases mem_redVertices_iff.mp hv with hv_cl | ⟨iv, hiv, hnv, bv, hbv, qv, hqv, rfl⟩
      · -- Both clause vertices
        obtain ⟨_, hu1, _⟩ := hmod_clause u hu su
        obtain ⟨_, hv1, _⟩ := hmod_clause v hv sv
        obtain ⟨hud, hum⟩ := hu1 hu_cl; obtain ⟨hvd, hvm⟩ := hv1 hv_cl
        have hj_eq : u / 34 = v / 34 := by omega
        have hbmod : (if su then baseL else baseR) ⟨u % 34, Nat.mod_lt _ (by decide)⟩ =
            (if sv then baseL else baseR) ⟨v % 34, Nat.mod_lt _ (by decide)⟩ := by omega
        by_cases hg_eq : (⟨u % 34, Nat.mod_lt _ (by decide)⟩ : Fin 34) =
          ⟨v % 34, Nat.mod_lt _ (by decide)⟩
        · have huv : u = v := by have := congrArg Fin.val hg_eq; dsimp at this; omega
          refine ⟨huv, ?_⟩
          subst huv; cases su <;> cases sv
          · rfl
          · exfalso; exact ne_of_gt (baseL_lt_baseR _).1 hbmod
          · exfalso; exact ne_of_lt (baseL_lt_baseR _).1 hbmod
          · rfl
        · exfalso
          have hd := base_endpoints_disjoint _ _ hg_eq
          cases su <;> cases sv <;> simp only [Bool.false_eq_true, ↓reduceIte] at hbmod
          · exact hd.2.2.2 hbmod
          · exact hd.2.2.1 hbmod
          · exact hd.2.1 hbmod
          · exact hd.1 hbmod
      · -- `u` clause, `v` connection
        exfalso
        obtain ⟨_, hu1, _⟩ := hmod_clause u hu su; obtain ⟨_, hum⟩ := hu1 hu_cl
        by_cases hR : sv = false ∧ qv = 0
        · rcases hR with ⟨rfl, rfl⟩
          obtain ⟨iv', isT', _, _, _, hvm⟩ := hRe iv bv hbv hnv
          have hbo := base_outside_slots ⟨u % 34, Nat.mod_lt _ (by decide)⟩
            ⟨iv' % 3, Nat.mod_lt _ (by decide)⟩ isT' ⟨0, by decide⟩
          dsimp only [Fin.val] at hbo
          cases su
          · simp only [Bool.false_eq_true, ↓reduceIte] at hum hmod_eq; exact hbo.2 (by omega)
          · simp only [Bool.false_eq_true, ↓reduceIte] at hum hmod_eq; exact hbo.1 (by omega)
        · obtain ⟨_, _, hv2⟩ := hmod_clause _ hv sv
          obtain ⟨_, hvm⟩ := hv2 iv bv qv rfl hiv hbv hqv (by cases sv <;> simp at hR ⊢; omega)
          have hbo := base_outside_slots ⟨u % 34, Nat.mod_lt _ (by decide)⟩
            ⟨iv % 3, Nat.mod_lt _ (by decide)⟩ (decide (bv = 0))
            ⟨connOff sv qv, connOff_lt_10 sv qv⟩
          dsimp only [Fin.val] at hbo
          cases su
          · simp only [Bool.false_eq_true, ↓reduceIte] at hum hmod_eq; exact hbo.2 (by omega)
          · simp only [↓reduceIte] at hum hmod_eq; exact hbo.1 (by omega)
      · -- `u` connection, `v` clause
        exfalso
        obtain ⟨_, hv1, _⟩ := hmod_clause v hv sv; obtain ⟨_, hvm⟩ := hv1 hv_cl
        by_cases hR : su = false ∧ qu = 0
        · rcases hR with ⟨rfl, rfl⟩
          obtain ⟨iu', isT', _, _, _, hum⟩ := hRe iu bu hbu hnu
          have hbo := base_outside_slots ⟨v % 34, Nat.mod_lt _ (by decide)⟩
            ⟨iu' % 3, Nat.mod_lt _ (by decide)⟩ isT' ⟨0, by decide⟩
          dsimp only [Fin.val] at hbo
          cases sv
          · simp only [Bool.false_eq_true, ↓reduceIte] at hvm hmod_eq; exact hbo.2 (by omega)
          · simp only [Bool.false_eq_true, ↓reduceIte] at hvm hmod_eq; exact hbo.1 (by omega)
        · obtain ⟨_, _, hu2⟩ := hmod_clause _ hu su
          obtain ⟨_, hum⟩ := hu2 iu bu qu rfl hiu hbu hqu (by cases su <;> simp at hR ⊢; omega)
          have hbo := base_outside_slots ⟨v % 34, Nat.mod_lt _ (by decide)⟩
            ⟨iu % 3, Nat.mod_lt _ (by decide)⟩ (decide (bu = 0))
            ⟨connOff su qu, connOff_lt_10 su qu⟩
          dsimp only [Fin.val] at hbo
          cases sv
          · simp only [Bool.false_eq_true, ↓reduceIte] at hvm hmod_eq; exact hbo.2 (by omega)
          · simp only [↓reduceIte] at hvm hmod_eq; exact hbo.1 (by omega)
      · -- Both connection vertices
        by_cases hRu : su = false ∧ qu = 0 <;> by_cases hRv : sv = false ∧ qv = 0
        · rcases hRu with ⟨rfl, rfl⟩; rcases hRv with ⟨rfl, rfl⟩
          simp only [Bool.false_eq_true, ↓reduceIte] at hdiv_eq hmod_eq
          obtain ⟨iu', isTu', hnu_eq, hisTu, hud, hum⟩ := hRe iu bu hbu hnu
          obtain ⟨iv', isTv', hnv_eq, hisTv, hvd, hvm⟩ := hRe iv bv hbv hnv
          have hsd := slotBase_disjoint ⟨iu' % 3, Nat.mod_lt _ (by decide)⟩
            ⟨iv' % 3, Nat.mod_lt _ (by decide)⟩ isTu' isTv' ⟨0, by decide⟩ ⟨0, by decide⟩
            (by dsimp [Fin.val]; omega)
          have hi'_eq : iu' = iv' := by
            have := congrArg Fin.val hsd.1; dsimp at this; omega
          subst hi'_eq
          have hi_eq : iu = iv := nextOcc_injective hφ hnu_eq hnv_eq
          subst hi_eq
          have hb_eq : bu = bv := by
            have h := hsd.2.1; rw [hisTu, hisTv] at h
            by_cases hbu0 : bu = 0 <;> by_cases hbv0 : bv = 0 <;>
              cases hp : decide ((literalAt φ iu).2 =
                (literalAt φ iu').2) <;> simp [hbu0, hbv0, hp] at h <;> omega
          subst hb_eq; exact ⟨rfl, rfl⟩
        · exfalso
          rcases hRu with ⟨rfl, rfl⟩
          simp only [Bool.false_eq_true, ↓reduceIte] at hmod_eq
          obtain ⟨iu', isTu', _, _, _, hum⟩ := hRe iu bu hbu hnu
          obtain ⟨_, _, hv2⟩ := hmod_clause _ hv sv
          have hsvq : sv = true ∨ qv ≠ 0 := by cases sv <;> simp at hRv ⊢; omega
          obtain ⟨_, hvm⟩ := hv2 iv bv qv rfl hiv hbv hqv hsvq
          have hsd := slotBase_disjoint ⟨iu' % 3, Nat.mod_lt _ (by decide)⟩
            ⟨iv % 3, Nat.mod_lt _ (by decide)⟩ isTu' (decide (bv = 0)) ⟨0, by decide⟩
            ⟨connOff sv qv, connOff_lt_10 sv qv⟩ (by dsimp [Fin.val]; omega)
          have hpos := connOff_pos hsvq
          have := congrArg Fin.val hsd.2.2; dsimp at this; omega
        · exfalso
          rcases hRv with ⟨rfl, rfl⟩
          simp only [Bool.false_eq_true, ↓reduceIte] at hmod_eq
          obtain ⟨iv', isTv', _, _, _, hvm⟩ := hRe iv bv hbv hnv
          obtain ⟨_, _, hu2⟩ := hmod_clause _ hu su
          have hsuq : su = true ∨ qu ≠ 0 := by cases su <;> simp at hRu ⊢; omega
          obtain ⟨_, hum⟩ := hu2 iu bu qu rfl hiu hbu hqu hsuq
          have hsd := slotBase_disjoint ⟨iu % 3, Nat.mod_lt _ (by decide)⟩
            ⟨iv' % 3, Nat.mod_lt _ (by decide)⟩ (decide (bu = 0)) isTv'
            ⟨connOff su qu, connOff_lt_10 su qu⟩ ⟨0, by decide⟩ (by dsimp [Fin.val]; omega)
          have hpos := connOff_pos hsuq
          have := congrArg Fin.val hsd.2.2; dsimp at this; omega
        · obtain ⟨_, _, hu2⟩ := hmod_clause _ hu su
          obtain ⟨_, _, hv2⟩ := hmod_clause _ hv sv
          have hsuq : su = true ∨ qu ≠ 0 := by cases su <;> simp at hRu ⊢; omega
          have hsvq : sv = true ∨ qv ≠ 0 := by cases sv <;> simp at hRv ⊢; omega
          obtain ⟨hud, hum⟩ := hu2 iu bu qu rfl hiu hbu hqu hsuq
          obtain ⟨hvd, hvm⟩ := hv2 iv bv qv rfl hiv hbv hqv hsvq
          have hsd := slotBase_disjoint ⟨iu % 3, Nat.mod_lt _ (by decide)⟩
            ⟨iv % 3, Nat.mod_lt _ (by decide)⟩ (decide (bu = 0)) (decide (bv = 0))
            ⟨connOff su qu, connOff_lt_10 su qu⟩ ⟨connOff sv qv, connOff_lt_10 sv qv⟩
            (by dsimp [Fin.val]; omega)
          have hi_eq : iu = iv := by have := congrArg Fin.val hsd.1; dsimp at this; omega
          have hb_eq : bu = bv := by
            have h := hsd.2.1; by_cases hbu0 : bu = 0 <;> by_cases hbv0 : bv =
              0 <;> simp [hbu0, hbv0] at h <;> omega
          have hoff_eq := congrArg Fin.val hsd.2.2; dsimp at hoff_eq
          obtain ⟨hq_eq, hs_eq⟩ := connOff_injective hqu hqv hsuq hsvq hoff_eq
          subst hi_eq hb_eq hq_eq hs_eq; exact ⟨rfl, rfl⟩
    intro u hu v hv hne
    refine ⟨fun h ↦ hne (htag u hu v hv true true h).1,
      fun h ↦ hne (htag u hu v hv true false h).1,
      fun h ↦ hne (htag u hu v hv false true h).1,
      fun h ↦ hne (htag u hu v hv false false h).1⟩
  refine ⟨fun v ↦ hbounds v.1 v.2, fun u v huv ↦ hdisj u.1 u.2 v.1 v.2 (Subtype.coe_ne_coe.mpr huv),
    fun u v huv ↦ ?_⟩
  rw [Graph.induced_adj, reductionGraph_adj_iff u.2 v.2 (Subtype.coe_ne_coe.mpr huv)]

/-- The reduction graph `G(φ)` is a circle graph. -/
theorem reductionGraph_isCircleChordGraph {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct) :
    IsCircleChordGraph (reductionGraph φ).induced :=
  ⟨128 * φ.length, fun v ↦ chordL φ v.1, fun v ↦ chordR φ v.1,
    reductionGraph_isCircleChordPlacement hφ⟩

/-! ### 5. Adjacency Characterization Lemmas -/

lemma adj_clause_clause {φ : CNF ℕ} {j1 j2 : ℕ} (hj1 : j1 < φ.length) (hj2 : j2 < φ.length)
    (g1 g2 : Fin 34) (hne : 34 * j1 + g1.1 ≠ 34 * j2 + g2.1) :
    (reductionGraph φ).toSimpleGraph.Adj (34 * j1 + g1.1) (34 * j2 + g2.1) ↔
      j1 = j2 ∧ clauseAdj g1 g2 = true := by
  have hu : 34 * j1 + g1.1 ∈ redVertices φ := mem_redVertices_iff.mpr (Or.inl (by omega))
  have hv : 34 * j2 + g2.1 ∈ redVertices φ := mem_redVertices_iff.mpr (Or.inl (by omega))
  rw [reductionGraph_adj_iff hu hv hne]
  have hL1 : chordL φ (34 * j1 + g1.1) = 128 * j1 + baseL g1 := by
    simp [chordL, show 34 * j1 + g1.1 < 34 * φ.length by omega,
      show (34 * j1 + g1.1) / 34 = j1 by omega, show (34 * j1 + g1.1) % 34 = g1.1 by omega]
  have hR1 : chordR φ (34 * j1 + g1.1) = 128 * j1 + baseR g1 := by
    simp [chordR, show 34 * j1 + g1.1 < 34 * φ.length by omega,
      show (34 * j1 + g1.1) / 34 = j1 by omega, show (34 * j1 + g1.1) % 34 = g1.1 by omega]
  have hL2 : chordL φ (34 * j2 + g2.1) = 128 * j2 + baseL g2 := by
    simp [chordL, show 34 * j2 + g2.1 < 34 * φ.length by omega,
      show (34 * j2 + g2.1) / 34 = j2 by omega, show (34 * j2 + g2.1) % 34 = g2.1 by omega]
  have hR2 : chordR φ (34 * j2 + g2.1) = 128 * j2 + baseR g2 := by
    simp [chordR, show 34 * j2 + g2.1 < 34 * φ.length by omega,
      show (34 * j2 + g2.1) / 34 = j2 by omega, show (34 * j2 + g2.1) % 34 = g2.1 by omega]
  rw [hL1, hR1, hL2, hR2]
  have hb1 := baseL_lt_baseR g1; have hb2 := baseL_lt_baseR g2
  constructor
  · intro halt
    have hjeq : j1 = j2 := by
      rcases halt with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
    subst hjeq
    exact ⟨rfl, (chordsAlternateBool_eq_true_iff _ _ _ _).mpr
      ((chordsAlternate_add_left _ _ _ _ _).mp halt)⟩
  · rintro ⟨rfl, hca⟩
    exact (chordsAlternate_add_left _ _ _ _ _).mpr
      ((chordsAlternateBool_eq_true_iff _ _ _ _).mp hca)

/-- Helper: a claw vertex (`s_e` or `l1, l2, l3`) at `(idx, b)` has its endpoints strictly inside
`[sb + 1, sb + 9]` and therefore NEVER crosses any clause vertex or any other connection block's
vertex! -/
lemma claw_adj_iff {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct)
    {idx b q : ℕ} (hidx : idx < 3 * φ.length) (hnext : (nextOcc φ idx).isSome)
    (hb : b < 2) (hq1 : 1 ≤ q) (hq5 : q < 5) {u : ℕ} (hu : u ∈ redVertices φ) :
    let v := 34 * φ.length + 5 * (2 * idx + b) + q
    (reductionGraph φ).toSimpleGraph.Adj u v ↔
      (if q = 1 then u = 34 * φ.length + 5 * (2 * idx + b) + 0 ∨
          u = 34 * φ.length + 5 * (2 * idx + b) + 2 ∨
          u = 34 * φ.length + 5 * (2 * idx + b) + 3 ∨
          u = 34 * φ.length + 5 * (2 * idx + b) + 4
       else u = 34 * φ.length + 5 * (2 * idx + b) + 1) := by
  intro v
  have hv : v ∈ redVertices φ :=
    mem_redVertices_iff.mpr (Or.inr ⟨idx, hidx, hnext, b, hb, q, hq5, rfl⟩)
  have hge : ¬ (v < 34 * φ.length) := by omega
  have hoff : (v - 34 * φ.length) / 5 = 2 * idx + b := by omega
  have hmod5 : (v - 34 * φ.length) % 5 = q := by omega
  have hdiv2 : (2 * idx + b) / 2 = idx := by omega
  have hmod2 : decide ((2 * idx + b) % 2 = 0) = decide (b = 0) := by
    by_cases hb0 : b = 0 <;> simp [hb0]; omega
  let sb := 128 * (idx / 3) + slotBase (idx % 3) (decide (b = 0))
  have hLv : chordL φ v = sb + connOff true q := by
    simp only [chordL, hge, ↓reduceIte, hoff, hmod5, hdiv2, hmod2, sb, connOff]
    rcases (show q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 by omega) with rfl | rfl | rfl | rfl <;> rfl
  have hRv : chordR φ v = sb + connOff false q := by
    simp only [chordR, hge, ↓reduceIte, hoff, hmod5, hdiv2, hmod2, sb, connOff]
    rcases (show q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 by omega) with rfl | rfl | rfl | rfl <;> rfl
  -- Any `u` whose endpoints both lie outside `(sb + 1, sb + 9)` cannot alternate with `v`.
  have hsb_lt := slotBase_lt_128 ⟨idx % 3, Nat.mod_lt _ (by decide)⟩ (decide (b = 0))
  have hsb9 := hsb_lt 9; dsimp at hsb9
  constructor
  · intro hadj
    have hne : u ≠ v := (reductionGraph φ).toSimpleGraph.ne_of_adj hadj
    have halt := (reductionGraph_adj_iff hu hv hne).mp hadj
    rw [hLv, hRv] at halt
    -- Show `u` must lie in the SAME connection block `(idx, b)`!
    rcases mem_redVertices_iff.mp hu with hu_cl | ⟨iu, _, hnu, bu, hbu, qu, hqu, rfl⟩
    · exfalso
      have hLu : chordL φ u = 128 * (u / 34) + baseL ⟨u % 34, Nat.mod_lt _ (by decide)⟩ := by
        simp [chordL, hu_cl]
      have hRu : chordR φ u = 128 * (u / 34) + baseR ⟨u % 34, Nat.mod_lt _ (by decide)⟩ := by
        simp [chordR, hu_cl]
      rw [hLu, hRu] at halt
      have hnot := base_not_in_claw ⟨u % 34, Nat.mod_lt _ (by decide)⟩
        ⟨idx % 3, Nat.mod_lt _ (by decide)⟩ (decide (b = 0))
      have hb_lt := baseL_lt_baseR ⟨u % 34, Nat.mod_lt _ (by decide)⟩
      dsimp at hnot hb_lt
      have hLge : 1 ≤ connOff true q := by
        rcases (show q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 by omega) with rfl | rfl | rfl | rfl <;> decide
      have hRle : connOff false q ≤ 9 := by
        rcases (show q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 by omega) with rfl | rfl | rfl | rfl <;> decide
      rcases halt with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
    · by_cases hsame : iu = idx ∧ bu = b
      · rcases hsame with ⟨rfl, rfl⟩
        let u0 := 34 * φ.length + 5 * (2 * iu + bu) + qu
        have hge_u : ¬ (u0 < 34 * φ.length) := by omega
        have hoff_u : (u0 - 34 * φ.length) / 5 = 2 * iu + bu := by omega
        have hmod5_u : (u0 - 34 * φ.length) % 5 = qu := by omega
        have hLu : chordL φ u0 = sb + connOff true qu := by
          simp only [chordL, hge_u, ↓reduceIte, hoff_u, hmod5_u, hdiv2, hmod2, sb, connOff]
          rcases (show qu = 0 ∨ qu = 1 ∨ qu = 2 ∨ qu = 3 ∨
            qu = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> rfl
        change ChordsAlternate (chordL φ u0) (chordR φ u0) _ _ at halt
        rw [hLu] at halt
        by_cases hqu0 : qu = 0
        · subst hqu0
          obtain ⟨idx', hnext_eq⟩ := Option.isSome_iff_exists.mp hnu
          obtain ⟨_, _, _, hcl_lt, _⟩ := nextOcc_spec hφ hnext_eq
          have hRu : chordR φ u0 = 128 * (idx' / 3) + slotBase (idx' % 3)
              (if decide ((literalAt φ iu).2 = (literalAt φ idx').2) then !decide (bu =
                0) else decide (bu = 0)) := by
            simp only [chordR, hge_u, ↓reduceIte, hoff_u, hmod5_u, hdiv2, hmod2, hnext_eq]
          rw [hRu] at halt
          rcases (show q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 by omega) with rfl | rfl | rfl | rfl
          · simp
          all_goals
            exfalso; simp only [connOff, Bool.false_eq_true, ↓reduceIte] at halt
            rcases halt with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
        · have hRu : chordR φ u0 = sb + connOff false qu := by
            simp only [chordR, hge_u, ↓reduceIte, hoff_u, hmod5_u, hdiv2, hmod2, sb, connOff]
            rcases (show qu = 1 ∨ qu = 2 ∨ qu = 3 ∨
              qu = 4 by omega) with rfl | rfl | rfl | rfl <;> rfl
          rw [hRu] at halt
          rcases (show q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 by omega) with rfl | rfl | rfl | rfl <;>
          rcases (show qu = 1 ∨ qu = 2 ∨ qu = 3 ∨ qu = 4 by omega) with rfl | rfl | rfl | rfl <;>
            simp_all [ChordsAlternate, connOff]
      · exfalso
        let u0 := 34 * φ.length + 5 * (2 * iu + bu) + qu
        have hge_u : ¬ (u0 < 34 * φ.length) := by omega
        have hoff_u : (u0 - 34 * φ.length) / 5 = 2 * iu + bu := by omega
        have hmod5_u : (u0 - 34 * φ.length) % 5 = qu := by omega
        have hdiv2_u : (2 * iu + bu) / 2 = iu := by omega
        have hmod2_u : decide ((2 * iu + bu) % 2 = 0) = decide (bu = 0) := by
          by_cases hb0 : bu = 0 <;> simp [hb0]; omega
        let sbu := 128 * (iu / 3) + slotBase (iu % 3) (decide (bu = 0))
        have hsbu_lt := slotBase_lt_128 ⟨iu % 3, Nat.mod_lt _ (by decide)⟩ (decide (bu = 0)) 9
        dsimp at hsbu_lt
        have hdisj_slot : sbu + 9 < sb ∨ sb + 9 < sbu := by
          by_cases hcl_eq : iu / 3 = idx / 3
          · have hnot_both : ¬ (iu % 3 = idx % 3 ∧ decide (bu = 0) = decide (b = 0)) := by
              rintro ⟨hm, hbd⟩
              have hi_eq : iu = idx := by omega
              have hb_eq : bu = b := by
                by_cases hbu0 : bu = 0 <;> by_cases hb0 : b =
                  0 <;> simp [hbu0, hb0] at hbd <;> omega
              exact hsame ⟨hi_eq, hb_eq⟩
            have h1 : slotBase (iu % 3) (decide (bu = 0)) + 9 < slotBase (idx % 3) (decide (b =
              0)) ∨
                slotBase (idx % 3) (decide (b = 0)) + 9 < slotBase (iu % 3) (decide (bu = 0)) := by
              have hne1 : (⟨iu % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) ≠
                ⟨idx % 3, Nat.mod_lt _ (by decide)⟩ ∨
                  decide (bu = 0) ≠ decide (b = 0) := by
                by_contra hc; push Not at hc; exact hnot_both ⟨congrArg Fin.val hc.1, hc.2⟩
              have : ∀ r1 r2 : Fin 3, ∀ b1 b2 : Bool, (r1 ≠ r2 ∨ b1 ≠ b2) →
                  slotBase r1.1 b1 + 9 < slotBase r2.1 b2 ∨
                    slotBase r2.1 b2 + 9 < slotBase r1.1 b1 := by decide
              exact this _ _ _ _ hne1
            dsimp [sbu, sb]; omega
          · dsimp [sbu, sb]; omega
        have hLu : chordL φ u0 = sbu + connOff true qu := by
          simp only [chordL, hge_u, ↓reduceIte, hoff_u, hmod5_u, hdiv2_u, hmod2_u, sbu, connOff]
          rcases (show qu = 0 ∨ qu = 1 ∨ qu = 2 ∨ qu = 3 ∨
            qu = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> rfl
        change ChordsAlternate (chordL φ u0) (chordR φ u0) _ _ at halt
        rw [hLu] at halt
        by_cases hqu0 : qu = 0
        · subst hqu0
          obtain ⟨idx', hnext_eq⟩ := Option.isSome_iff_exists.mp hnu
          obtain ⟨_, _, _, hcl_lt, _⟩ := nextOcc_spec hφ hnext_eq
          have hRu : chordR φ u0 = 128 * (idx' / 3) + slotBase (idx' % 3)
              (if decide ((literalAt φ iu).2 = (literalAt φ idx').2) then !decide (bu =
                0) else decide (bu = 0)) := by
            simp only [chordR, hge_u, ↓reduceIte, hoff_u, hmod5_u, hdiv2_u, hmod2_u, hnext_eq]
          rw [hRu] at halt
          have hsb'9 := slotBase_lt_128 ⟨idx' % 3, Nat.mod_lt _ (by decide)⟩
            (if decide ((literalAt φ iu).2 = (literalAt φ idx').2) then !decide (bu =
              0) else decide (bu = 0)) 0
          dsimp at hsb'9
          have hRu_out : chordR φ u0 ≤ sb ∨ sb + 9 < chordR φ u0 := by
            rw [hRu]
            by_cases hcl' : idx' / 3 = idx / 3
            · by_cases hsame' : idx' % 3 = idx % 3 ∧
                  (if decide ((literalAt φ iu).2 = (literalAt φ idx').2) then !decide (bu =
                    0) else decide (bu = 0)) =
                  decide (b = 0)
              · left; dsimp [sb]; rw [hcl', hsame'.1, hsame'.2]
              · have : ∀ r1 r2 : Fin 3, ∀ b1 b2 : Bool, (r1 ≠ r2 ∨ b1 ≠ b2) →
                    slotBase r1.1 b1 ≤ slotBase r2.1 b2 ∨
                      slotBase r2.1 b2 + 9 < slotBase r1.1 b1 := by decide
                have hne' : (⟨idx' % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) ≠
                  ⟨idx % 3, Nat.mod_lt _ (by decide)⟩ ∨
                    (if decide ((literalAt φ iu).2 = (literalAt φ idx').2) then !decide (bu =
                      0) else decide (bu = 0)) ≠
                    decide (b = 0) := by
                  by_contra hc; push Not at hc; exact hsame' ⟨congrArg Fin.val hc.1, hc.2⟩
                rcases this _ _ _ _ hne' with h1 | h2
                · left; dsimp [sb, Fin.val] at h1 ⊢; omega
                · right; dsimp [sb, Fin.val] at h2 ⊢; omega
            · dsimp [sb]; omega
          rw [hRu] at hRu_out
          rcases (show q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 by omega) with rfl | rfl | rfl | rfl <;>
            (simp only [connOff, Bool.false_eq_true, ↓reduceIte] at halt;
              rcases halt with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega)
        · have hRu : chordR φ u0 = sbu + connOff false qu := by
            simp only [chordR, hge_u, ↓reduceIte, hoff_u, hmod5_u, hdiv2_u, hmod2_u, sbu, connOff]
            rcases (show qu = 1 ∨ qu = 2 ∨ qu = 3 ∨
              qu = 4 by omega) with rfl | rfl | rfl | rfl <;> rfl
          rw [hRu] at halt
          rcases (show q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 by omega) with rfl | rfl | rfl | rfl <;>
          rcases (show qu = 1 ∨ qu = 2 ∨ qu = 3 ∨ qu = 4 by omega) with rfl | rfl | rfl | rfl <;>
            (simp only [connOff, Bool.false_eq_true, ↓reduceIte] at halt;
              rcases halt with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega)
  · -- Reverse direction: verify the explicit neighbors of `v` alternate with `v`.
    intro hu_eq
    have hne : u ≠ v := by split_ifs at hu_eq <;> rcases hu_eq with rfl | rfl | rfl | rfl <;> omega
    rw [reductionGraph_adj_iff hu hv hne, hLv, hRv]
    have hL_q : ∀ r : ℕ, r < 5 →
        chordL φ (34 * φ.length + 5 * (2 * idx + b) + r) = sb + connOff true r := by
      intro r hr
      have hge_r : ¬ (34 * φ.length + 5 * (2 * idx + b) + r < 34 * φ.length) := by omega
      have hoff_r : (34 * φ.length + 5 * (2 * idx + b) + r - 34 * φ.length) / 5 = 2 * idx + b :=
        by omega
      have hmod5_r : (34 * φ.length + 5 * (2 * idx + b) + r - 34 * φ.length) % 5 = r := by omega
      simp only [chordL, hge_r, ↓reduceIte, hoff_r, hmod5_r, hdiv2, hmod2, sb, connOff]
      rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨
        r = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> rfl
    have hR_q : ∀ r : ℕ, 1 ≤ r → r < 5 →
        chordR φ (34 * φ.length + 5 * (2 * idx + b) + r) = sb + connOff false r := by
      intro r hr1 hr5
      have hge_r : ¬ (34 * φ.length + 5 * (2 * idx + b) + r < 34 * φ.length) := by omega
      have hoff_r : (34 * φ.length + 5 * (2 * idx + b) + r - 34 * φ.length) / 5 = 2 * idx + b :=
        by omega
      have hmod5_r : (34 * φ.length + 5 * (2 * idx + b) + r - 34 * φ.length) % 5 = r := by omega
      simp only [chordR, hge_r, ↓reduceIte, hoff_r, hmod5_r, hdiv2, hmod2, sb, connOff]
      rcases (show r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 by omega) with rfl | rfl | rfl | rfl <;> rfl
    split_ifs at hu_eq with hq_eq
    · subst hq_eq
      rcases hu_eq with rfl | rfl | rfl | rfl
      · obtain ⟨idx', hnext_eq⟩ := Option.isSome_iff_exists.mp hnext
        obtain ⟨_, _, _, hcl_lt, _⟩ := nextOcc_spec hφ hnext_eq
        have hRu : chordR φ (34 * φ.length + 5 * (2 * idx + b) + 0) = 128 * (idx' / 3) +
            slotBase (idx' % 3) (if decide ((literalAt φ idx).2 = (literalAt φ idx').2)
              then !decide (b = 0) else decide (b = 0)) := by
          have hge_r : ¬ (34 * φ.length + 5 * (2 * idx + b) + 0 < 34 * φ.length) := by omega
          have hoff_r : (34 * φ.length + 5 * (2 * idx + b) + 0 - 34 * φ.length) / 5 =
            2 * idx + b := by omega
          have hmod5_r : (34 * φ.length + 5 * (2 * idx + b) + 0 - 34 * φ.length) % 5 = 0 := by
            omega
          simp only [chordR, hge_r, ↓reduceIte, hoff_r, hmod5_r, hdiv2, hmod2, hnext_eq]
        rw [hL_q 0 (by decide), hRu]
        simp only [connOff, Bool.false_eq_true, ↓reduceIte]
        exact Or.inr ⟨by omega, by omega, by omega⟩
      · rw [hL_q 2 (by decide), hR_q 2 (by decide) (by decide)]
        simp only [connOff, Bool.false_eq_true, ↓reduceIte]
        exact Or.inl ⟨by omega, by omega, by omega⟩
      · rw [hL_q 3 (by decide), hR_q 3 (by decide) (by decide)]
        simp only [connOff, Bool.false_eq_true, ↓reduceIte]
        exact Or.inl ⟨by omega, by omega, by omega⟩
      · rw [hL_q 4 (by decide), hR_q 4 (by decide) (by decide)]
        simp only [connOff, Bool.false_eq_true, ↓reduceIte]
        exact Or.inl ⟨by omega, by omega, by omega⟩
    · subst hu_eq
      rw [hL_q 1 (by decide), hR_q 1 (by decide) (by decide)]
      rcases (show q = 2 ∨ q = 3 ∨ q = 4 by omega) with rfl | rfl | rfl <;>
        (simp only [connOff, Bool.false_eq_true, ↓reduceIte];
          exact Or.inr ⟨by omega, by omega, by omega⟩)

/-- Adjacency between a connection chord `e` (from `(idx, b)` to `(idx', isTrue')`) and a clause
vertex `34 * j + g`. -/
lemma adj_conn_clause_iff {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct)
    {idx b idx' j : ℕ} (hidx : idx < 3 * φ.length) (hnext : nextOcc φ idx = some idx')
    (hb : b < 2) (hj : j < φ.length) (g : Fin 34) :
    let e := 34 * φ.length + 5 * (2 * idx + b) + 0
    let isTrue := decide (b = 0)
    let isTrue' := if decide ((literalAt φ idx).2 = (literalAt φ idx').2) then !isTrue else isTrue
    (reductionGraph φ).toSimpleGraph.Adj e (34 * j + g.1) ↔
      (j = idx / 3 ∧
        (g.1 = 6 * (idx % 3) + (if isTrue then 0 else 5) ∨
          ∃ s : Fin 3, (if isTrue then s.1 < idx % 3 else s.1 ≤ idx % 3) ∧
            (g.1 = 6 * s.1 + 1 ∨ g.1 = 6 * s.1 + 2))) ∨
      (j = idx' / 3 ∧
        (g.1 = 6 * (idx' % 3) + (if isTrue' then 0 else 5) ∨
          ∃ s : Fin 3, (if isTrue' then s.1 < idx' % 3 else s.1 ≤ idx' % 3) ∧
            (g.1 = 6 * s.1 + 1 ∨ g.1 = 6 * s.1 + 2))) := by
  intro e isTrue isTrue'
  have he : e ∈ redVertices φ :=
    mem_redVertices_iff.mpr (Or.inr ⟨idx, hidx, by simp [hnext], b, hb, 0, by decide, rfl⟩)
  have hv : 34 * j + g.1 ∈ redVertices φ := mem_redVertices_iff.mpr (Or.inl (by omega))
  have hne : e ≠ 34 * j + g.1 := by omega
  rw [reductionGraph_adj_iff he hv hne]
  have hge : ¬ (e < 34 * φ.length) := by omega
  have hoff : (e - 34 * φ.length) / 5 = 2 * idx + b := by omega
  have hmod5 : (e - 34 * φ.length) % 5 = 0 := by omega
  have hdiv2 : (2 * idx + b) / 2 = idx := by omega
  have hmod2 : decide ((2 * idx + b) % 2 = 0) = isTrue := by
    by_cases hb0 : b = 0 <;> simp [isTrue, hb0]; omega
  have hLe : chordL φ e = 128 * (idx / 3) + slotBase (idx % 3) isTrue + 8 := by
    simp only [chordL, hge, ↓reduceIte, hoff, hmod5, hdiv2, hmod2]
  have hRe : chordR φ e = 128 * (idx' / 3) + slotBase (idx' % 3) isTrue' := by
    simp only [chordR, hge, ↓reduceIte, hoff, hmod5, hdiv2, hmod2, hnext]; rfl
  have hLv : chordL φ (34 * j + g.1) = 128 * j + baseL g := by
    simp [chordL, show 34 * j + g.1 < 34 * φ.length by omega,
      show (34 * j + g.1) / 34 = j by omega, show (34 * j + g.1) % 34 = g.1 by omega]
  have hRv : chordR φ (34 * j + g.1) = 128 * j + baseR g := by
    simp [chordR, show 34 * j + g.1 < 34 * φ.length by omega,
      show (34 * j + g.1) / 34 = j by omega, show (34 * j + g.1) % 34 = g.1 by omega]
  rw [hLe, hRe, hLv, hRv]
  obtain ⟨_, _, _, hcl_lt, _⟩ := nextOcc_spec hφ hnext
  have hbg := baseL_lt_baseR g
  have hsb := slotBase_lt_128 ⟨idx % 3, Nat.mod_lt _ (by decide)⟩ isTrue 8
  have hsb' := slotBase_lt_128 ⟨idx' % 3, Nat.mod_lt _ (by decide)⟩ isTrue' 0
  dsimp at hsb hsb'
  have : 128 * (idx / 3) + slotBase (idx % 3) isTrue + 8 <
      128 * (idx' / 3) + slotBase (idx' % 3) isTrue' := by omega
  -- `ChordsAlternate` holds iff `j = idx / 3` with `L(e)` inside `(baseL g, baseR g)`
  -- OR `j = idx' / 3` with `R(e)` inside `(baseL g, baseR g)`!
  have hcross : ChordsAlternate (128 * (idx / 3) + slotBase (idx % 3) isTrue + 8)
      (128 * (idx' / 3) + slotBase (idx' % 3) isTrue') (128 * j + baseL g) (128 * j + baseR g) ↔
      (j = idx / 3 ∧ baseL g < slotBase (idx % 3) isTrue + 8 ∧
        slotBase (idx % 3) isTrue + 8 < baseR g) ∨
      (j = idx' / 3 ∧ baseL g < slotBase (idx' % 3) isTrue' ∧
        slotBase (idx' % 3) isTrue' < baseR g) := by
    constructor
    · rintro (⟨_, _, _⟩ | ⟨_, _, _⟩)
      · right; refine ⟨by omega, ?_, ?_⟩ <;> omega
      · left; refine ⟨by omega, ?_, ?_⟩ <;> omega
    · rintro (⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩)
      · exact Or.inr ⟨by omega, by omega, by omega⟩
      · exact Or.inl ⟨by omega, by omega, by omega⟩
  rw [hcross]
  have h1 := base_contains_slot_point g ⟨idx % 3, Nat.mod_lt _ (by decide)⟩ isTrue true
  have h2 := base_contains_slot_point g ⟨idx' % 3, Nat.mod_lt _ (by decide)⟩ isTrue' false
  dsimp at h1 h2
  rw [h1, h2]


/-- Explicit formula for `chordsAlternateBool`. -/
theorem chordsAlternateBool_eq (a b c d : ℕ) :
    chordsAlternateBool a b c d =
      ((decide (a < c) && decide (c < b) && decide (b < d)) ||
       (decide (c < a) && decide (a < d) && decide (d < b))) := rfl

/-- Explicit formula for `slotBase`. -/
theorem slotBase_eq (r : ℕ) (isTrue : Bool) :
    slotBase r isTrue = 30 * r + (if isTrue then 1 else 19) := rfl

/-- Explicit `List.getD` formula for `literalAt`. -/
theorem literalAt_eq_getD (φ : CNF ℕ) (idx : ℕ) :
    literalAt φ idx = (φ.getD (idx / 3) []).getD (idx % 3) (0, false) := rfl

/-- Indexing `literalAt` at `3 * j + r` recovers `(φ[j])[r]`. -/
theorem literalAt_getElem (φ : CNF ℕ) {j r : ℕ} (hj : j < φ.length) (hr3 : r < 3)
    (hr : r < (φ[j]).length) :
    literalAt φ (3 * j + r) = (φ[j])[r] := by
  simp only [literalAt, show (3 * j + r) / 3 = j by omega, show (3 * j + r) % 3 = r by omega,
    List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hr]

/-- Explicit `List.find?` formula for `nextOcc`. -/
theorem nextOcc_eq_find? (φ : CNF ℕ) (idx : ℕ) :
    nextOcc φ idx =
      (List.range (3 * φ.length)).find? fun idx' ↦
        decide (idx < idx') && decide ((literalAt φ idx').1 = (literalAt φ idx).1) := rfl

/-- Explicit `List.countP` formula for `repetitionCount`. -/
theorem repetitionCount_eq_countP (φ : CNF ℕ) :
    repetitionCount φ = (List.range (3 * φ.length)).countP fun idx ↦ (nextOcc φ idx).isSome := rfl

/-- Cardinality of active indices equals `repetitionCount φ`. -/
theorem repetitionCount_eq_card_filter (φ : CNF ℕ) :
    repetitionCount φ =
      ((Finset.range (3 * φ.length)).filter fun idx ↦ (nextOcc φ idx).isSome).card := by
  simp only [repetitionCount, List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  congr 1; ext x; simp

/-- Explicit formula for `reductionBound`. -/
theorem reductionBound_eq (φ : CNF ℕ) :
    reductionBound φ = 7 * φ.length + 2 * repetitionCount φ := rfl

/-- Explicit list-append formula for `redVertices`. -/
theorem redVertices_eq_append (φ : CNF ℕ) :
    redVertices φ =
      List.range (34 * φ.length) ++
      ((List.range (3 * φ.length)).filter fun idx ↦ (nextOcc φ idx).isSome).flatMap
        (fun idx ↦ [0, 1].flatMap fun b ↦
          (List.range 5).map fun q ↦ 34 * φ.length + 5 * (2 * idx + b) + q) := rfl

/-- Explicit formula for `chordL`. -/
theorem chordL_eq_ite (φ : CNF ℕ) (v : ℕ) :
    chordL φ v =
      if v < 34 * φ.length then
        128 * (v / 34) + baseL ⟨v % 34, Nat.mod_lt _ (by decide)⟩
      else
        let off := v - 34 * φ.length
        let s := off / 5
        let q := off % 5
        let idx := s / 2
        let isTrue := decide (s % 2 = 0)
        let sb := 128 * (idx / 3) + slotBase (idx % 3) isTrue
        match q with
        | 0 => sb + 8
        | 1 => sb + 4
        | 2 => sb + 1
        | 3 => sb + 2
        | _ => sb + 3 := rfl

/-- Explicit formula for `chordR`. -/
theorem chordR_eq_ite (φ : CNF ℕ) (v : ℕ) :
    chordR φ v =
      if v < 34 * φ.length then
        128 * (v / 34) + baseR ⟨v % 34, Nat.mod_lt _ (by decide)⟩
      else
        let off := v - 34 * φ.length
        let s := off / 5
        let q := off % 5
        let idx := s / 2
        let isTrue := decide (s % 2 = 0)
        let sb := 128 * (idx / 3) + slotBase (idx % 3) isTrue
        match q with
        | 0 =>
          match nextOcc φ idx with
          | some idx' =>
            let samePol := decide ((literalAt φ idx).2 = (literalAt φ idx').2)
            let isTrue' := if samePol then !isTrue else isTrue
            128 * (idx' / 3) + slotBase (idx' % 3) isTrue'
          | none => sb + 9
        | 1 => sb + 9
        | 2 => sb + 7
        | 3 => sb + 6
        | _ => sb + 5 := rfl

/-- Explicit `flatMap` formula for `redEdges`. -/
theorem redEdges_eq_flatMap (φ : CNF ℕ) :
    redEdges φ =
      (redVertices φ).flatMap fun u ↦
        ((redVertices φ).filter fun v ↦
          decide (u < v) &&
          chordsAlternateBool (chordL φ u) (chordR φ u) (chordL φ v) (chordR φ v)).map
          fun v ↦ (u, v) := rfl

end Cslib.Complexity.CircleOneTwoDomination
