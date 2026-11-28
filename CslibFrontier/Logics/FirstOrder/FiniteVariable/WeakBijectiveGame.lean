module

public import CslibFrontier.Init
public import CslibFrontier.Logics.FirstOrder.FiniteVariable.BijectiveGame
public import CslibFrontier.Foundations.ModelTheory.Graph
import CslibFrontier.Logics.FirstOrder.FiniteVariable.ColorRefinement
import CslibFrontier.Foundations.Order.AntitoneSwap
import CslibFrontier.Foundations.Data.Fintype.FiberEquiv
import Mathlib.Tactic.FinCases

/-!
# Weak Bijective Pebble Games on Finite Graphs

The weak bijective `k`-pebble game is played on finite simple graphs `G` and `H` with set-valued
positions `p : Finset (V × W)` of size at most `k - 1`. In each round, if `|p| = k - 1` then
Spoiler selects one pair `(a, b) ∈ p` to remove; Duplicator responds with a bijection `f : V ≃ W`;
and Spoiler selects `a' : V`, advancing to `insert (a', f a') (p.erase (a, b))` (or
`insert (a', f a') p` when `|p| < k - 1`) provided `insert (a', f a') p` is a local isomorphism.

This module defines the `n`-round and infinite weak bijective `k`-pebble games on graphs, proves
their equivalence-relation laws and alternating-step zig-zag closure, characterizes one-step
extensions by counting bijections across equivalence classes, and proves the sandwich comparison
with Hella's bijective `k`-pebble game (`C^k → C^{<k} → C^{k-1}` for `k ≥ 3`, with exact
equivalence `C^2 ↔ C^{<2}` at `k = 2`).

## Main definitions

* `CslibFrontier.Logics.FirstOrder.FiniteVariable.IsLocalBijection`,
  `CslibFrontier.Logics.FirstOrder.FiniteVariable.IsLocalIso`,
  `CslibFrontier.Logics.FirstOrder.FiniteVariable.swapPos`,
  `CslibFrontier.Logics.FirstOrder.FiniteVariable.tuplePos`,
  `CslibFrontier.Logics.FirstOrder.FiniteVariable.finsetPos`: set-based positions and local
  isomorphisms on simple graphs.
* `CslibFrontier.Logics.FirstOrder.FiniteVariable.GraphGraphCkPosEquiv`,
  `CslibFrontier.Logics.FirstOrder.FiniteVariable.GraphGraphCkEquiv`: bijective `k`-pebble game
  equivalence on graphs.
* `CslibFrontier.Logics.FirstOrder.FiniteVariable.WeakBijPebbleWins`,
  `CslibFrontier.Logics.FirstOrder.FiniteVariable.IsWeakBijPebbleBackAndForth`,
  `CslibFrontier.Logics.FirstOrder.FiniteVariable.WeakBijPebbleWinsForever`,
  `CslibFrontier.Logics.FirstOrder.FiniteVariable.WeakCkEquiv`: the weak bijective `k`-pebble
  game.

## Main results

* `CslibFrontier.Logics.FirstOrder.FiniteVariable.WeakBijPebbleWins.symm`,
  `CslibFrontier.Logics.FirstOrder.FiniteVariable.WeakBijPebbleWins.trans_tuple`,
  `CslibFrontier.Logics.FirstOrder.FiniteVariable.WeakBijPebbleWins.insert_zig_zag`: symmetry,
  transitivity, and alternating-step closure.
* `CslibFrontier.Logics.FirstOrder.FiniteVariable.weakBijPebbleWinsForever_step_iff_card_eq`:
  counting characterization of one-step moves from full positions.
* `CslibFrontier.Logics.FirstOrder.FiniteVariable.weakCkEquiv_sandwich`: sandwich comparison
  between `GraphGraphCkEquiv` and `WeakCkEquiv` (`k = 2` equivalence and `k ≥ 3` implications).
-/

public section

open FirstOrder Cslib.Logic.FO

namespace CslibFrontier.Logics.FirstOrder.FiniteVariable

/-- `C^k`-equivalence of pebble positions `(S, a)` in `G` and `(S, b)` in `H` via the infinite
bijective `k`-pebble game. -/
abbrev GraphCkPosEquiv {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ)
    (S : Set (Fin k)) (a : Fin k → V) (b : Fin k → W) : Prop :=
  let _ := G.structure
  let _ := H.structure
  BijPebbleWinsForever Language.graph S a b

/-- `C^k`-equivalence of simple graphs `G` and `H` (`G ≡_C^k H`). -/
structure GraphCkEquiv {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) : Prop where
  /-- Both vertex sets are nonempty iff the other is. -/
  nonempty_iff : Nonempty V ↔ Nonempty W
  /-- Duplicator wins the infinite bijective `k`-pebble game from the empty pebble position. -/
  pos : ∀ (a : Fin k → V) (b : Fin k → W), GraphCkPosEquiv G H k ∅ a b


theorem graphCkPosEquiv_iff_exists_isBijPebbleBackAndForth {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ}
    {S : Set (Fin k)} {a : Fin k → V} {b : Fin k → W} :
    GraphCkPosEquiv G H k S a b ↔
      let _ := G.structure; let _ := H.structure
      ∃ I, IsBijPebbleBackAndForth Language.graph I ∧ I S a b := by
  let _ := G.structure; let _ := H.structure
  exact bijPebbleWinsForever_iff_exists_isBijPebbleBackAndForth


/-! ### Set-based positions and local isomorphisms -/

/-- A finite set `p : Finset (V × W)` is a *local bijection* if `a = a' ↔ b = b'` for all
`(a, b), (a', b') ∈ p`. -/
@[expose] def IsLocalBijection {V W : Type*} (p : Finset (V × W)) : Prop :=
  ∀ x ∈ p, ∀ y ∈ p, x.1 = y.1 ↔ x.2 = y.2

/-- A finite set `p : Finset (V × W)` is a *local isomorphism* between `G` and `H` if it is a
local bijection preserving adjacency and non-adjacency. -/
structure IsLocalIso {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (p : Finset (V × W)) : Prop where
  /-- The set of pairs is a partial bijection. -/
  bijection : IsLocalBijection p
  /-- Adjacency and non-adjacency are preserved across all pairs in `p`. -/
  adj_iff : ∀ x ∈ p, ∀ y ∈ p, G.Adj x.1 y.1 ↔ H.Adj x.2 y.2

theorem isLocalBijection_empty {V W : Type*} : IsLocalBijection (∅ : Finset (V × W)) :=
  fun _ hx => (Finset.notMem_empty _ hx).elim

theorem isLocalIso_empty {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    IsLocalIso G H (∅ : Finset (V × W)) :=
  ⟨isLocalBijection_empty, fun _ hx => (Finset.notMem_empty _ hx).elim⟩

theorem IsLocalBijection.subset {V W : Type*} {p q : Finset (V × W)}
    (hq : q ⊆ p) (hp : IsLocalBijection p) : IsLocalBijection q :=
  fun x hx y hy => hp x (hq hx) y (hq hy)

theorem IsLocalIso.subset {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {p q : Finset (V × W)} (hq : q ⊆ p) (hp : IsLocalIso G H p) : IsLocalIso G H q :=
  ⟨hp.1.subset hq, fun x hx y hy => hp.2 x (hq hx) y (hq hy)⟩

/-- Flipping a set position `p ⊆ V × W` to `p⁻¹ ⊆ W × V`. -/
def swapPos {V W : Type*} [DecidableEq V] [DecidableEq W] (p : Finset (V × W)) :
    Finset (W × V) :=
  p.image Prod.swap

theorem mem_swapPos {V W : Type*} [DecidableEq V] [DecidableEq W]
    {p : Finset (V × W)} {x : W × V} :
    x ∈ swapPos p ↔ (x.2, x.1) ∈ p := by
  simp only [swapPos, Finset.mem_image]
  exact ⟨fun ⟨y, hy, hyx⟩ => by subst hyx; exact hy, fun h => ⟨(x.2, x.1), h, rfl⟩⟩

theorem swapPos_card {V W : Type*} [DecidableEq V] [DecidableEq W] (p : Finset (V × W)) :
    (swapPos p).card = p.card :=
  Finset.card_image_of_injective p Prod.swap_injective

theorem swapPos_insert {V W : Type*} [DecidableEq V] [DecidableEq W]
    (a : V) (b : W) (p : Finset (V × W)) :
    swapPos (insert (a, b) p) = insert (b, a) (swapPos p) := by
  simp [swapPos]

theorem swapPos_erase {V W : Type*} [DecidableEq V] [DecidableEq W]
    (ab : V × W) (p : Finset (V × W)) :
    swapPos (p.erase ab) = (swapPos p).erase ab.swap := by
  ext ⟨b, a⟩
  simp [mem_swapPos, Prod.ext_iff, and_comm]

theorem IsLocalIso.swap {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {p : Finset (V × W)} (hp : IsLocalIso G H p) :
    IsLocalIso H G (swapPos p) := by
  refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_⟩
  · rw [mem_swapPos] at hx hy
    exact (hp.1 _ hx _ hy).symm
  · rw [mem_swapPos] at hx hy
    exact (hp.2 _ hx _ hy).symm

/-- The set position `{(a i, b i) | i : Fin r}` induced by a pair of tuples. -/
def tuplePos {V W : Type*} [DecidableEq V] [DecidableEq W] {r : ℕ}
    (a : Fin r → V) (b : Fin r → W) : Finset (V × W) :=
  Finset.univ.image fun i : Fin r => (a i, b i)

theorem mem_tuplePos {V W : Type*} [DecidableEq V] [DecidableEq W] {r : ℕ}
    {a : Fin r → V} {b : Fin r → W} {x : V × W} :
    x ∈ tuplePos a b ↔ ∃ i : Fin r, (a i, b i) = x := by
  simp [tuplePos]

theorem tuplePos_snoc {V W : Type*} [DecidableEq V] [DecidableEq W] {r : ℕ}
    (a : Fin r → V) (b : Fin r → W) (a' : V) (b' : W) :
    tuplePos (Fin.snoc a a') (Fin.snoc b b') = insert (a', b') (tuplePos a b) := by
  ext ⟨x, y⟩
  simp only [mem_tuplePos, Finset.mem_insert, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi⟩
    refine Fin.lastCases ?_ (fun j => ?_) i hi
    · intro h; left; simp only [Fin.snoc_last] at h; exact ⟨h.1.symm, h.2.symm⟩
    · intro h; right; exact ⟨j, by simpa using h⟩
  · rintro (⟨rfl, rfl⟩ | ⟨j, h⟩)
    · exact ⟨Fin.last r, by simp⟩
    · exact ⟨j.castSucc, by simpa using h⟩

theorem swapPos_tuplePos {V W : Type*} [DecidableEq V] [DecidableEq W] {r : ℕ}
    (a : Fin r → V) (b : Fin r → W) :
    swapPos (tuplePos a b) = tuplePos b a := by
  ext ⟨y, x⟩
  simp [mem_swapPos, mem_tuplePos, Prod.mk.injEq, and_comm]

theorem isLocalIso_tuplePos_iff_partialIsoOn {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {r : ℕ} (a : Fin r → V) (b : Fin r → W) :
    IsLocalIso G H (tuplePos a b) ↔
      (let _ := G.structure; let _ := H.structure; PartialIsoOn Language.graph Set.univ a b) := by
  rw [partialIsoOn_graph_iff]
  constructor
  · rintro ⟨hbij, hadj⟩ i _ j _
    exact ⟨hbij (a i, b i) (mem_tuplePos.2 ⟨i, rfl⟩) (a j, b j) (mem_tuplePos.2 ⟨j, rfl⟩),
      hadj (a i, b i) (mem_tuplePos.2 ⟨i, rfl⟩) (a j, b j) (mem_tuplePos.2 ⟨j, rfl⟩)⟩
  · intro h
    refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_⟩
    · obtain ⟨i, rfl⟩ := mem_tuplePos.1 hx
      obtain ⟨j, rfl⟩ := mem_tuplePos.1 hy
      exact (h i (Set.mem_univ _) j (Set.mem_univ _)).1
    · obtain ⟨i, rfl⟩ := mem_tuplePos.1 hx
      obtain ⟨j, rfl⟩ := mem_tuplePos.1 hy
      exact (h i (Set.mem_univ _) j (Set.mem_univ _)).2

theorem isLocalIso_tuplePos_trans {U V W : Type*}
    [DecidableEq U] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph U} {H : SimpleGraph V} {K : SimpleGraph W} {r : ℕ}
    {a : Fin r → U} {b : Fin r → V} {c : Fin r → W}
    (h1 : IsLocalIso G H (tuplePos a b)) (h2 : IsLocalIso H K (tuplePos b c)) :
    IsLocalIso G K (tuplePos a c) := by
  rw [isLocalIso_tuplePos_iff_partialIsoOn] at h1 h2 ⊢
  let _ := G.structure; let _ := H.structure; let _ := K.structure
  exact h1.trans h2

/-- Every finite set `p : Finset (V × W)` is `tuplePos a b` for tuples of length `p.card`. -/
theorem exists_tuplePos_eq {V W : Type*} [DecidableEq V] [DecidableEq W] (p : Finset (V × W)) :
    ∃ (a : Fin p.card → V) (b : Fin p.card → W), tuplePos a b = p := by
  let e := p.equivFin
  refine ⟨fun i => (e.symm i).1.1, fun i => (e.symm i).1.2, ?_⟩
  ext x
  simp only [mem_tuplePos]
  constructor
  · rintro ⟨i, rfl⟩; exact (e.symm i).2
  · intro hx; exact ⟨e ⟨x, hx⟩, by simp⟩

/-- Set position induced by restricting tuples `(a, b)` to a finset of placed pebbles `S`. -/
@[expose] def finsetPos {V W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (S : Finset (Fin k)) (a : Fin k → V) (b : Fin k → W) : Finset (V × W) :=
  S.image fun i => (a i, b i)

theorem isLocalIso_finsetPos_iff_partialIsoOn {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ}
    (S : Finset (Fin k)) (a : Fin k → V) (b : Fin k → W) :
    IsLocalIso G H (finsetPos S a b) ↔
      (let _ := G.structure; let _ := H.structure; PartialIsoOn Language.graph (↑S) a b) := by
  rw [partialIsoOn_graph_iff]
  constructor
  · rintro ⟨hbij, hadj⟩ i hi j hj
    exact ⟨hbij (a i, b i) (Finset.mem_image_of_mem _ hi) (a j, b j) (Finset.mem_image_of_mem _ hj),
      hadj (a i, b i) (Finset.mem_image_of_mem _ hi) (a j, b j) (Finset.mem_image_of_mem _ hj)⟩
  · intro h
    refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
      exact (h i hi j hj).1
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
      exact (h i hi j hj).2


/-! ### Helper lemmas for tuple positions -/

private theorem card_tuplePos_eq_of_isLocalBijection {U V W : Type*}
    [DecidableEq U] [DecidableEq V] [DecidableEq W] {r : ℕ}
    {a : Fin r → U} {b : Fin r → V} {c : Fin r → W}
    (hab : IsLocalBijection (tuplePos a b)) (hbc : IsLocalBijection (tuplePos b c)) :
    (tuplePos a b).card = (tuplePos a c).card ∧ (tuplePos b c).card = (tuplePos a c).card := by
  have heq : ∀ i j : Fin r, (a i, b i) = (a j, b j) ↔ (a i, c i) = (a j, c j) := fun i j => by
    have h1 := hab (a i, b i) (mem_tuplePos.2 ⟨i, rfl⟩) (a j, b j) (mem_tuplePos.2 ⟨j, rfl⟩)
    have h2 := hbc (b i, c i) (mem_tuplePos.2 ⟨i, rfl⟩) (b j, c j) (mem_tuplePos.2 ⟨j, rfl⟩)
    simp only [Prod.mk.injEq] at h1 h2 ⊢
    exact ⟨fun ⟨ha, hb⟩ => ⟨ha, h2.1 hb⟩, fun ⟨ha, _⟩ => ⟨ha, h1.1 ha⟩⟩
  have heq2 : ∀ i j : Fin r, (b i, c i) = (b j, c j) ↔ (a i, c i) = (a j, c j) := fun i j => by
    have h1 := hab (a i, b i) (mem_tuplePos.2 ⟨i, rfl⟩) (a j, b j) (mem_tuplePos.2 ⟨j, rfl⟩)
    have h2 := hbc (b i, c i) (mem_tuplePos.2 ⟨i, rfl⟩) (b j, c j) (mem_tuplePos.2 ⟨j, rfl⟩)
    simp only [Prod.mk.injEq] at h1 h2 ⊢
    exact ⟨fun ⟨hb, hc⟩ => ⟨h1.2 hb, hc⟩, fun ⟨_, hc⟩ => ⟨h2.2 hc, hc⟩⟩
  constructor
  · apply Finset.card_bij (fun x hx => let i := (mem_tuplePos.1 hx).choose; (a i, c i))
    · intro x hx; exact mem_tuplePos.2 ⟨(mem_tuplePos.1 hx).choose, rfl⟩
    · intro x₁ hx₁ x₂ hx₂ h
      have h1 := (mem_tuplePos.1 hx₁).choose_spec
      have h2 := (mem_tuplePos.1 hx₂).choose_spec
      rw [← h1, ← h2]
      exact (heq _ _).2 h
    · intro y hy
      obtain ⟨i, rfl⟩ := mem_tuplePos.1 hy
      refine ⟨(a i, b i), mem_tuplePos.2 ⟨i, rfl⟩, ?_⟩
      exact (heq _ _).1 (mem_tuplePos.1 (mem_tuplePos.2 ⟨i, rfl⟩)).choose_spec
  · apply Finset.card_bij (fun x hx => let i := (mem_tuplePos.1 hx).choose; (a i, c i))
    · intro x hx; exact mem_tuplePos.2 ⟨(mem_tuplePos.1 hx).choose, rfl⟩
    · intro x₁ hx₁ x₂ hx₂ h
      have h1 := (mem_tuplePos.1 hx₁).choose_spec
      have h2 := (mem_tuplePos.1 hx₂).choose_spec
      rw [← h1, ← h2]
      exact (heq2 _ _).2 h
    · intro y hy
      obtain ⟨i, rfl⟩ := mem_tuplePos.1 hy
      refine ⟨(b i, c i), mem_tuplePos.2 ⟨i, rfl⟩, ?_⟩
      exact (heq2 _ _).1 (mem_tuplePos.1 (mem_tuplePos.2 ⟨i, rfl⟩)).choose_spec

private theorem tuplePos_replace {α β : Type*} [DecidableEq α] [DecidableEq β] {r : ℕ}
    {a : Fin r → α} {b : Fin r → β} (hbij : IsLocalBijection (tuplePos a b))
    (i₀ : Fin r) (a' : α) (b' : β) :
    tuplePos (fun j => if a j = a i₀ then a' else a j)
      (fun j => if b j = b i₀ then b' else b j) =
      insert (a', b') ((tuplePos a b).erase (a i₀, b i₀)) := by
  have hrel : ∀ j : Fin r, a j = a i₀ ↔ b j = b i₀ := fun j =>
    hbij (a j, b j) (mem_tuplePos.2 ⟨j, rfl⟩) (a i₀, b i₀) (mem_tuplePos.2 ⟨i₀, rfl⟩)
  ext ⟨x, y⟩
  simp only [mem_tuplePos, Finset.mem_insert, Finset.mem_erase, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hji : a j = a i₀
    · left
      simp only [hji, (hrel j).1 hji, ↓reduceIte] at hj
      exact ⟨hj.1.symm, hj.2.symm⟩
    · right
      have hbne : b j ≠ b i₀ := mt (hrel j).2 hji
      simp only [hji, hbne, ↓reduceIte] at hj
      refine ⟨fun h => hji (hj.1.trans (congrArg Prod.fst h)), j, hj⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hne, j, hja, hjb⟩)
    · exact ⟨i₀, by simp⟩
    · have hji : a j ≠ a i₀ := fun h => hne (Prod.ext (hja.symm.trans h)
        (hjb.symm.trans ((hrel j).1 h)))
      have hbne : b j ≠ b i₀ := mt (hrel j).2 hji
      exact ⟨j, by simp only [hji, hbne, ↓reduceIte]; exact ⟨hja, hjb⟩⟩

private theorem isLocalIso_of_diag {V : Type*} (G : SimpleGraph V) {p : Finset (V × V)}
    (hdiag : ∀ x ∈ p, x.1 = x.2) : IsLocalIso G G p :=
  ⟨fun x hx y hy => by rw [hdiag x hx, hdiag y hy],
   fun x hx y hy => by rw [hdiag x hx, hdiag y hy]⟩

/-! ### The weak bijective `k`-pebble game (`≡_C^{<k}`) -/

/-- Duplicator wins `n` rounds of the weak bijective `k`-pebble game
starting from position `p : Finset (V × W)` of size at most `k - 1`. -/
@[expose] def WeakBijPebbleWins {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) :
    ℕ → Finset (V × W) → Prop
  | 0, p => p.card ≤ k - 1 ∧ IsLocalIso G H p
  | n + 1, p =>
      p.card ≤ k - 1 ∧ IsLocalIso G H p ∧
      if p.card = k - 1 then
        ∀ ab ∈ p, ∃ f : V ≃ W, ∀ a',
          IsLocalIso G H (insert (a', f a') p) ∧
          WeakBijPebbleWins G H k n (insert (a', f a') (p.erase ab))
      else
        ∃ f : V ≃ W, ∀ a',
          IsLocalIso G H (insert (a', f a') p) ∧
          WeakBijPebbleWins G H k n (insert (a', f a') p)

/-- Back-and-forth invariant for the weak bijective `k`-pebble game. -/
structure IsWeakBijPebbleBackAndForth {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) (I : Finset (V × W) → Prop) : Prop where
  /-- Every position in `I` has size at most `k - 1`. -/
  card_le : ∀ {p}, I p → p.card ≤ k - 1
  /-- Every position in `I` is a local isomorphism. -/
  localIso : ∀ {p}, I p → IsLocalIso G H p
  /-- Move from a full position `|p| = k - 1` after Spoiler drops `ab ∈ p`. -/
  moveFull : ∀ {p}, I p → p.card = k - 1 → ∀ ab ∈ p, ∃ f : V ≃ W, ∀ a',
    IsLocalIso G H (insert (a', f a') p) ∧ I (insert (a', f a') (p.erase ab))
  /-- Move from a partial position `|p| < k - 1`. -/
  movePartial : ∀ {p}, I p → p.card < k - 1 → ∃ f : V ≃ W, ∀ a',
    IsLocalIso G H (insert (a', f a') p) ∧ I (insert (a', f a') p)

/-- Duplicator wins the infinite weak bijective `k`-pebble game from position `p`. -/
@[expose] def WeakBijPebbleWinsForever {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) (p : Finset (V × W)) : Prop :=
  ∃ I : Finset (V × W) → Prop, IsWeakBijPebbleBackAndForth G H k I ∧ I p

/-- Weak `C^{<k}`-equivalence of simple graphs `G` and `H` (`G ≡_C^{<k} H`). -/
@[expose] def WeakCkEquiv {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) : Prop :=
  WeakBijPebbleWinsForever G H k ∅

theorem WeakBijPebbleWins.card_le {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k n : ℕ} {p : Finset (V × W)}
    (h : WeakBijPebbleWins G H k n p) : p.card ≤ k - 1 := by
  cases n <;> exact h.1

theorem WeakBijPebbleWins.localIso {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k n : ℕ} {p : Finset (V × W)}
    (h : WeakBijPebbleWins G H k n p) : IsLocalIso G H p := by
  cases n with
  | zero => exact h.2
  | succ _ => exact h.2.1

theorem WeakBijPebbleWins.mono {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ} :
    ∀ {m n : ℕ} {p : Finset (V × W)}, m ≤ n →
      WeakBijPebbleWins G H k n p → WeakBijPebbleWins G H k m p
  | 0, _, _, _, h => ⟨h.card_le, h.localIso⟩
  | _ + 1, 0, _, hmn, _ => absurd hmn (Nat.not_succ_le_zero _)
  | m + 1, n + 1, p, hmn, ⟨hcard, hiso, hstep⟩ => by
    refine ⟨hcard, hiso, ?_⟩
    split_ifs at hstep ⊢ with hfull
    · intro ab hab
      obtain ⟨f, hf⟩ := hstep ab hab
      exact ⟨f, fun a' => ⟨(hf a').1, mono (Nat.le_of_succ_le_succ hmn) (hf a').2⟩⟩
    · obtain ⟨f, hf⟩ := hstep
      exact ⟨f, fun a' => ⟨(hf a').1, mono (Nat.le_of_succ_le_succ hmn) (hf a').2⟩⟩

theorem WeakBijPebbleWins.of_subset {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ} :
    ∀ {n : ℕ} {p q : Finset (V × W)}, q ⊆ p →
      WeakBijPebbleWins G H k n p → WeakBijPebbleWins G H k n q
  | 0, p, q, hqp, ⟨hcard, hiso⟩ =>
    ⟨(Finset.card_le_card hqp).trans hcard, hiso.subset hqp⟩
  | n + 1, p, q, hqp, ⟨hcard, hiso, hstep⟩ => by
    have hqcard : q.card ≤ k - 1 := (Finset.card_le_card hqp).trans hcard
    refine ⟨hqcard, hiso.subset hqp, ?_⟩
    split_ifs with hqfull
    · have hpq : q = p := Finset.eq_of_subset_of_card_le hqp (by omega)
      subst hpq
      simp only [hqfull, ↓reduceIte] at hstep
      exact hstep
    · split_ifs at hstep with hpfull
      · have hss : q ⊂ p := Finset.ssubset_iff_subset_ne.2
          ⟨hqp, fun h => hqfull (by rw [h, hpfull])⟩
        obtain ⟨ab, habp, habq⟩ := Finset.exists_of_ssubset hss
        obtain ⟨f, hf⟩ := hstep ab habp
        refine ⟨f, fun a' => ⟨(hf a').1.subset (Finset.insert_subset_insert _ hqp), ?_⟩⟩
        have hsub : insert (a', f a') q ⊆ insert (a', f a') (p.erase ab) :=
          Finset.insert_subset_insert _ (Finset.subset_erase.2 ⟨hqp, habq⟩)
        exact of_subset hsub (hf a').2
      · obtain ⟨f, hf⟩ := hstep
        exact ⟨f, fun a' => ⟨(hf a').1.subset (Finset.insert_subset_insert _ hqp),
          of_subset (Finset.insert_subset_insert _ hqp) (hf a').2⟩⟩

theorem IsWeakBijPebbleBackAndForth.weakBijPebbleWins {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ} {I : Finset (V × W) → Prop}
    (hI : IsWeakBijPebbleBackAndForth G H k I) :
    ∀ {n : ℕ} {p : Finset (V × W)}, I p → WeakBijPebbleWins G H k n p
  | 0, _, hp => ⟨hI.card_le hp, hI.localIso hp⟩
  | n + 1, p, hp => by
    refine ⟨hI.card_le hp, hI.localIso hp, ?_⟩
    split_ifs with hfull
    · intro ab hab
      obtain ⟨f, hf⟩ := hI.moveFull hp hfull ab hab
      exact ⟨f, fun a' => ⟨(hf a').1, hI.weakBijPebbleWins (hf a').2⟩⟩
    · obtain ⟨f, hf⟩ := hI.movePartial hp (lt_of_le_of_ne (hI.card_le hp) hfull)
      exact ⟨f, fun a' => ⟨(hf a').1, hI.weakBijPebbleWins (hf a').2⟩⟩

theorem WeakBijPebbleWinsForever.weakBijPebbleWins {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ} {p : Finset (V × W)}
    (h : WeakBijPebbleWinsForever G H k p) (n : ℕ) : WeakBijPebbleWins G H k n p :=
  let ⟨_, hI, hp⟩ := h
  hI.weakBijPebbleWins hp

theorem weakBijPebbleWinsForever_iff_forall_weakBijPebbleWins
    {V W : Type*} [Finite V] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ} {p : Finset (V × W)} :
    WeakBijPebbleWinsForever G H k p ↔ ∀ n, WeakBijPebbleWins G H k n p := by
  refine ⟨WeakBijPebbleWinsForever.weakBijPebbleWins, fun h =>
    ⟨fun q => ∀ n, WeakBijPebbleWins G H k n q,
      ⟨fun hq => (hq 0).card_le, fun hq => (hq 0).localIso, ?_, ?_⟩, h⟩⟩
  · intro q hq hfull ab hab
    have hstep : ∀ n, ∃ f : V ≃ W, ∀ a',
        IsLocalIso G H (insert (a', f a') q) ∧
        WeakBijPebbleWins G H k n (insert (a', f a') (q.erase ab)) := fun n => by
      have hn := (hq (n + 1)).2.2
      simp only [hfull, ↓reduceIte] at hn
      exact hn ab hab
    obtain ⟨f, hf⟩ := (Finite.forall_exists_iff_exists_forall_of_antitone
      (p := fun (f : V ≃ W) n => ∀ a',
        IsLocalIso G H (insert (a', f a') q) ∧
        WeakBijPebbleWins G H k n (insert (a', f a') (q.erase ab)))
      fun _ _ _ hmn hf a' => ⟨(hf a').1, (hf a').2.mono hmn⟩).1 hstep
    exact ⟨f, fun a' => ⟨(hf 0 a').1, fun n => (hf n a').2⟩⟩
  · intro q hq hlt
    have hne : q.card ≠ k - 1 := ne_of_lt hlt
    have hstep : ∀ n, ∃ f : V ≃ W, ∀ a',
        IsLocalIso G H (insert (a', f a') q) ∧
        WeakBijPebbleWins G H k n (insert (a', f a') q) := fun n => by
      have hn := (hq (n + 1)).2.2
      simp only [hne, ↓reduceIte] at hn
      exact hn
    obtain ⟨f, hf⟩ := (Finite.forall_exists_iff_exists_forall_of_antitone
      (p := fun (f : V ≃ W) n => ∀ a',
        IsLocalIso G H (insert (a', f a') q) ∧
        WeakBijPebbleWins G H k n (insert (a', f a') q))
      fun _ _ _ hmn hf a' => ⟨(hf a').1, (hf a').2.mono hmn⟩).1 hstep
    exact ⟨f, fun a' => ⟨(hf 0 a').1, fun n => (hf n a').2⟩⟩

theorem WeakBijPebbleWinsForever.of_subset {V W : Type*} [Finite V] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ} {p q : Finset (V × W)}
    (hqp : q ⊆ p) (hp : WeakBijPebbleWinsForever G H k p) :
    WeakBijPebbleWinsForever G H k q :=
  weakBijPebbleWinsForever_iff_forall_weakBijPebbleWins.2 fun n =>
    (hp.weakBijPebbleWins n).of_subset hqp

theorem WeakBijPebbleWins.refl_diag {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) :
    ∀ (n : ℕ) {p : Finset (V × V)}, p.card ≤ k - 1 → (∀ x ∈ p, x.1 = x.2) →
      WeakBijPebbleWins G G k n p
  | 0, p, hcard, hdiag => ⟨hcard, isLocalIso_of_diag G hdiag⟩
  | n + 1, p, hcard, hdiag => by
    refine ⟨hcard, isLocalIso_of_diag G hdiag, ?_⟩
    split_ifs with hfull
    · intro ab hab
      refine ⟨Equiv.refl V, fun a' => ?_⟩
      have hdiag' : ∀ x ∈ insert (a', a') p, x.1 = x.2 := fun x hx =>
        (Finset.mem_insert.1 hx).elim (fun h => by subst h; rfl) (hdiag x)
      have hcard' : (insert (a', a') (p.erase ab)).card ≤ k - 1 := by
        have h1 := Finset.card_insert_le (a', a') (p.erase ab)
        have h2 : (p.erase ab).card + 1 = p.card := Finset.card_erase_add_one hab
        omega
      refine ⟨isLocalIso_of_diag G hdiag', refl_diag G k n hcard' fun x hx => ?_⟩
      exact (Finset.mem_insert.1 hx).elim (fun h => by subst h; rfl) fun h =>
        hdiag x (Finset.mem_of_mem_erase h)
    · refine ⟨Equiv.refl V, fun a' => ?_⟩
      have hdiag' : ∀ x ∈ insert (a', a') p, x.1 = x.2 := fun x hx =>
        (Finset.mem_insert.1 hx).elim (fun h => by subst h; rfl) (hdiag x)
      have hcard' : (insert (a', a') p).card ≤ k - 1 := by
        have h1 := Finset.card_insert_le (a', a') p
        omega
      exact ⟨isLocalIso_of_diag G hdiag', refl_diag G k n hcard' hdiag'⟩

theorem WeakBijPebbleWins.symm {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ} :
    ∀ {n : ℕ} {p : Finset (V × W)},
      WeakBijPebbleWins G H k n p → WeakBijPebbleWins H G k n (swapPos p)
  | 0, p, ⟨hcard, hiso⟩ => ⟨by rw [swapPos_card]; exact hcard, hiso.swap⟩
  | n + 1, p, ⟨hcard, hiso, hstep⟩ => by
    refine ⟨by rw [swapPos_card]; exact hcard, hiso.swap, ?_⟩
    rw [swapPos_card]
    split_ifs at hstep ⊢ with hfull
    · rintro ⟨b, a⟩ hba
      have hab : (a, b) ∈ p := mem_swapPos.1 hba
      obtain ⟨f, hf⟩ := hstep (a, b) hab
      refine ⟨f.symm, fun b' => ?_⟩
      have h1 := hf (f.symm b')
      rw [Equiv.apply_symm_apply] at h1
      exact ⟨by simpa only [swapPos_insert] using h1.1.swap,
        by simpa only [swapPos_insert, swapPos_erase, Prod.swap_prod_mk] using symm h1.2⟩
    · obtain ⟨f, hf⟩ := hstep
      refine ⟨f.symm, fun b' => ?_⟩
      have h1 := hf (f.symm b')
      rw [Equiv.apply_symm_apply] at h1
      exact ⟨by simpa only [swapPos_insert] using h1.1.swap,
        by simpa only [swapPos_insert] using symm h1.2⟩

theorem WeakBijPebbleWinsForever.symm {V W : Type*} [Finite W]
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ} {p : Finset (V × W)}
    (h : WeakBijPebbleWinsForever G H k p) :
    WeakBijPebbleWinsForever H G k (swapPos p) :=
  weakBijPebbleWinsForever_iff_forall_weakBijPebbleWins.2 fun n =>
    (h.weakBijPebbleWins n).symm

/-- Round-by-round transitivity of the weak bijective `k`-pebble game on tuple positions. -/
theorem WeakBijPebbleWins.trans_tuple {U V W : Type*}
    [DecidableEq U] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph U} {H : SimpleGraph V} {K : SimpleGraph W} {k : ℕ} :
    ∀ {n r : ℕ} {a : Fin r → U} {b : Fin r → V} {c : Fin r → W},
      WeakBijPebbleWins G H k n (tuplePos a b) →
      WeakBijPebbleWins H K k n (tuplePos b c) →
      WeakBijPebbleWins G K k n (tuplePos a c)
  | 0, _, _, _, _, h1, h2 => by
    have hcard := (card_tuplePos_eq_of_isLocalBijection h1.localIso.1 h2.localIso.1).1
    exact ⟨hcard ▸ h1.card_le, isLocalIso_tuplePos_trans h1.localIso h2.localIso⟩
  | n + 1, r, a, b, c, h1, h2 => by
    have hcards := card_tuplePos_eq_of_isLocalBijection h1.localIso.1 h2.localIso.1
    have hiso := isLocalIso_tuplePos_trans h1.localIso h2.localIso
    refine ⟨hcards.1 ▸ h1.card_le, hiso, ?_⟩
    have hs1 := h1.2.2
    have hs2 := h2.2.2
    split_ifs with hfull
    · have hfull1 : (tuplePos a b).card = k - 1 := hcards.1.trans hfull
      have hfull2 : (tuplePos b c).card = k - 1 := hcards.2.trans hfull
      simp only [hfull1, ↓reduceIte] at hs1
      simp only [hfull2, ↓reduceIte] at hs2
      intro ac hac
      obtain ⟨i₀, rfl⟩ := mem_tuplePos.1 hac
      obtain ⟨f, hf⟩ := hs1 (a i₀, b i₀) (mem_tuplePos.2 ⟨i₀, rfl⟩)
      obtain ⟨g, hg⟩ := hs2 (b i₀, c i₀) (mem_tuplePos.2 ⟨i₀, rfl⟩)
      refine ⟨f.trans g, fun a' => ?_⟩
      have hf' := hf a'
      have hg' := hg (f a')
      have hf1 : IsLocalIso G H (tuplePos (Fin.snoc a a') (Fin.snoc b (f a'))) := by
        rw [tuplePos_snoc]; exact hf'.1
      have hg1 : IsLocalIso H K (tuplePos (Fin.snoc b (f a')) (Fin.snoc c (g (f a')))) := by
        rw [tuplePos_snoc]; exact hg'.1
      have hiso' : IsLocalIso G K (insert (a', g (f a')) (tuplePos a c)) := by
        rw [← tuplePos_snoc]; exact isLocalIso_tuplePos_trans hf1 hg1
      refine ⟨hiso', ?_⟩
      have hpos_ab := tuplePos_replace h1.localIso.1 i₀ a' (f a')
      have hpos_bc := tuplePos_replace h2.localIso.1 i₀ (f a') (g (f a'))
      have hpos_ac := tuplePos_replace hiso.1 i₀ a' (g (f a'))
      dsimp only [Equiv.trans_apply]
      rw [← hpos_ac]
      exact trans_tuple (hpos_ab.symm ▸ hf'.2) (hpos_bc.symm ▸ hg'.2)
    · have hne1 : (tuplePos a b).card ≠ k - 1 := fun h => hfull (hcards.1.symm.trans h)
      have hne2 : (tuplePos b c).card ≠ k - 1 := fun h => hfull (hcards.2.symm.trans h)
      simp only [hne1, ↓reduceIte] at hs1
      simp only [hne2, ↓reduceIte] at hs2
      obtain ⟨f, hf⟩ := hs1
      obtain ⟨g, hg⟩ := hs2
      refine ⟨f.trans g, fun a' => ?_⟩
      have hf' := hf a'
      have hg' := hg (f a')
      have hf1 : IsLocalIso G H (tuplePos (Fin.snoc a a') (Fin.snoc b (f a'))) := by
        rw [tuplePos_snoc]; exact hf'.1
      have hg1 : IsLocalIso H K (tuplePos (Fin.snoc b (f a')) (Fin.snoc c (g (f a')))) := by
        rw [tuplePos_snoc]; exact hg'.1
      have hf2 : WeakBijPebbleWins G H k n (tuplePos (Fin.snoc a a') (Fin.snoc b (f a'))) := by
        rw [tuplePos_snoc]; exact hf'.2
      have hg2 :
          WeakBijPebbleWins H K k n (tuplePos (Fin.snoc b (f a')) (Fin.snoc c (g (f a')))) := by
        rw [tuplePos_snoc]; exact hg'.2
      exact ⟨by rw [← tuplePos_snoc]; exact isLocalIso_tuplePos_trans hf1 hg1,
        by rw [← tuplePos_snoc]; exact trans_tuple hf2 hg2⟩

/-- Transitivity of `WeakBijPebbleWinsForever` on tuple positions. -/
theorem WeakBijPebbleWinsForever.trans_tuple {U V W : Type*}
    [Finite U] [DecidableEq U] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph U} {H : SimpleGraph V} {K : SimpleGraph W} {k r : ℕ}
    {a : Fin r → U} {b : Fin r → V} {c : Fin r → W}
    (h1 : WeakBijPebbleWinsForever G H k (tuplePos a b))
    (h2 : WeakBijPebbleWinsForever H K k (tuplePos b c)) :
    WeakBijPebbleWinsForever G K k (tuplePos a c) :=
  weakBijPebbleWinsForever_iff_forall_weakBijPebbleWins.2 fun n =>
    (h1.weakBijPebbleWins n).trans_tuple (h2.weakBijPebbleWins n)

/-- Alternating-step closure for `WeakBijPebbleWins` at a fixed prefix `p`: if `(a₀, b₀)`,
`(a₁, b₀)`, and `(a₁, b₁)` each extend `p` to an `n`-round winning position, then so does
`(a₀, b₁)`. -/
theorem WeakBijPebbleWins.insert_zig_zag {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k n : ℕ} {p : Finset (V × W)}
    {a₀ a₁ : V} {b₀ b₁ : W}
    (h1 : WeakBijPebbleWins G H k n (insert (a₀, b₀) p))
    (h2 : WeakBijPebbleWins G H k n (insert (a₁, b₀) p))
    (h3 : WeakBijPebbleWins G H k n (insert (a₁, b₁) p)) :
    WeakBijPebbleWins G H k n (insert (a₀, b₁) p) := by
  obtain ⟨u, v, huv⟩ := exists_tuplePos_eq p
  rw [← huv] at h1 h2 h3 ⊢
  rw [← tuplePos_snoc] at h1 h2 h3 ⊢
  have h2' : WeakBijPebbleWins H G k n (tuplePos (Fin.snoc v b₀) (Fin.snoc u a₁)) := by
    simpa only [swapPos_tuplePos] using h2.symm
  exact (h1.trans_tuple h2').trans_tuple h3

/-- Counting characterization of `WeakBijPebbleWinsForever` for one step from a full position
`p` by cardinality matching. -/
theorem weakBijPebbleWinsForever_step_iff_card_eq {V W : Type*}
    [Finite V] [Finite W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ} {p : Finset (V × W)}
    (hcard : p.card = k - 1) (hiso : IsLocalIso G H p) (ab : V × W) (hab : ab ∈ p) :
    (∃ f : V ≃ W, ∀ a',
      IsLocalIso G H (insert (a', f a') p) ∧
      WeakBijPebbleWinsForever G H k (insert (a', f a') (p.erase ab))) ↔
    (let q := p.erase ab
     let qR : Finset (W × W) := q.image fun x => (x.2, x.2)
     let tagL : V → Set W × Bool × Bool := fun a' =>
       ({b'' : W | WeakBijPebbleWinsForever G H k (insert (a', b'') q)},
        decide (a' = ab.1), by classical exact decide (G.Adj ab.1 a'))
     let tagR : W → Set W × Bool × Bool := fun b' =>
       ({b'' : W | WeakBijPebbleWinsForever H H k (insert (b', b'') qR)},
        decide (b' = ab.2), by classical exact decide (H.Adj ab.2 b'))
     ∀ c : Set W × Bool × Bool,
       Nat.card {a' : V // tagL a' = c} = Nat.card {b' : W // tagR b' = c}) := by
  classical
  dsimp only
  set q := p.erase ab
  set qR : Finset (W × W) := q.image fun x => (x.2, x.2)
  set tagL : V → Set W × Bool × Bool := fun a' =>
    ({b'' : W | WeakBijPebbleWinsForever G H k (insert (a', b'') q)},
     decide (a' = ab.1), decide (G.Adj ab.1 a'))
  set tagR : W → Set W × Bool × Bool := fun b' =>
    ({b'' : W | WeakBijPebbleWinsForever H H k (insert (b', b'') qR)},
     decide (b' = ab.2), decide (H.Adj ab.2 b'))
  have hqcard : q.card + 1 = k - 1 := by
    rw [← hcard]; exact Finset.card_erase_add_one hab
  have htag_iff : ∀ (a' : V) (b' : W),
      tagL a' = tagR b' ↔
        IsLocalIso G H (insert (a', b') p) ∧
        WeakBijPebbleWinsForever G H k (insert (a', b') q) := by
    intro a' b'
    obtain ⟨u, v, huv⟩ := exists_tuplePos_eq q
    have hqR_eq : qR = tuplePos v v := by
      ext ⟨y₁, y₂⟩
      simp only [qR, ← huv, Finset.mem_image, mem_tuplePos]
      constructor
      · rintro ⟨⟨x, y⟩, ⟨i, hi⟩, hxy⟩
        have hy : v i = y := congrArg Prod.snd hi
        exact ⟨i, Prod.ext (hy.trans (congrArg Prod.fst hxy)) (hy.trans (congrArg Prod.snd hxy))⟩
      · rintro ⟨i, hi⟩
        exact ⟨(u i, v i), ⟨i, rfl⟩, hi⟩
    have hset_iff :
        ({b'' : W | WeakBijPebbleWinsForever G H k (insert (a', b'') q)} =
          {b'' : W | WeakBijPebbleWinsForever H H k (insert (b', b'') qR)}) ↔
        WeakBijPebbleWinsForever G H k (insert (a', b') q) := by
      constructor
      · intro hset
        have hrefl : WeakBijPebbleWinsForever H H k (insert (b', b') qR) := by
          rw [weakBijPebbleWinsForever_iff_forall_weakBijPebbleWins]
          intro n
          refine WeakBijPebbleWins.refl_diag H k n ?_ ?_
          · have h1 := Finset.card_insert_le (b', b') qR
            have h2 : qR.card ≤ q.card := Finset.card_image_le
            omega
          · intro x hx
            rcases Finset.mem_insert.1 hx with rfl | hx
            · rfl
            · obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hx; rfl
        have hmem : b' ∈ {b'' : W | WeakBijPebbleWinsForever H H k (insert (b', b'') qR)} := hrefl
        rw [← hset] at hmem
        exact hmem
      · intro hwin
        ext b''
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro hL
          rw [← huv, ← tuplePos_snoc] at hwin hL
          rw [hqR_eq, ← tuplePos_snoc]
          have hwinS :
              WeakBijPebbleWinsForever H G k (tuplePos (Fin.snoc v b') (Fin.snoc u a')) := by
            simpa only [swapPos_tuplePos] using hwin.symm
          exact hwinS.trans_tuple hL
        · intro hR
          rw [← huv, ← tuplePos_snoc] at hwin ⊢
          rw [hqR_eq, ← tuplePos_snoc] at hR
          exact hwin.trans_tuple hR
    have hiso_iff : WeakBijPebbleWinsForever G H k (insert (a', b') q) →
        ((a' = ab.1 ↔ b' = ab.2) ∧ (G.Adj ab.1 a' ↔ H.Adj ab.2 b') ↔
          IsLocalIso G H (insert (a', b') p)) := by
      intro hwin
      have hqiso : IsLocalIso G H (insert (a', b') q) := (hwin.weakBijPebbleWins 0).localIso
      constructor
      · rintro ⟨heq, hadj⟩
        have hpair : ∀ x ∈ p, (x.1 = a' ↔ x.2 = b') ∧ (G.Adj x.1 a' ↔ H.Adj x.2 b') := by
          intro x hx
          by_cases hxab : x = ab
          · subst hxab
            exact ⟨by simp [eq_comm, heq], hadj⟩
          · have hxq : x ∈ insert (a', b') q :=
              Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hxab, hx⟩)
            have ha' : (a', b') ∈ insert (a', b') q := Finset.mem_insert_self _ _
            exact ⟨hqiso.1 x hxq (a', b') ha', hqiso.2 x hxq (a', b') ha'⟩
        refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_⟩
        · rcases Finset.mem_insert.1 hx with rfl | hx <;>
            rcases Finset.mem_insert.1 hy with rfl | hy
          · simp
          · simpa only [eq_comm] using (hpair y hy).1
          · exact (hpair x hx).1
          · exact hiso.1 x hx y hy
        · rcases Finset.mem_insert.1 hx with rfl | hx <;>
            rcases Finset.mem_insert.1 hy with rfl | hy
          · simp
          · simpa only [G.adj_comm, H.adj_comm] using (hpair y hy).2
          · exact (hpair x hx).2
          · exact hiso.2 x hx y hy
      · intro hpiso
        have hab' : ab ∈ insert (a', b') p := Finset.mem_insert_of_mem hab
        have ha' : (a', b') ∈ insert (a', b') p := Finset.mem_insert_self _ _
        exact ⟨hpiso.1 (a', b') ha' ab hab', hpiso.2 ab hab' (a', b') ha'⟩
    simp only [tagL, tagR, Prod.mk.injEq, decide_eq_decide]
    rw [hset_iff]
    constructor
    · rintro ⟨hwin, heq, hadj⟩
      exact ⟨(hiso_iff hwin).1 ⟨heq, hadj⟩, hwin⟩
    · rintro ⟨hpiso, hwin⟩
      obtain ⟨heq, hadj⟩ := (hiso_iff hwin).2 hpiso
      exact ⟨hwin, heq, hadj⟩
  rw [← Equiv.exists_apply_eq_iff_card_fiber_eq]
  exact exists_congr fun f => forall_congr' fun a' =>
    ⟨fun h => ((htag_iff a' (f a')).2 h).symm, fun h => (htag_iff a' (f a')).1 h.symm⟩

/-! ### The weak non-counting `k`-pebble game (`≡_L^{<k}`) -/

/-! ### Comparison of strong and weak bijective pebble games -/

private theorem exists_subset_injective_image {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) :
    ∃ T ⊆ S, T.image f = S.image f ∧ T.card = (S.image f).card := by
  classical
  let g : S.image f → α := fun y => (Finset.mem_image.1 y.2).choose
  have hg_mem : ∀ y : S.image f, g y ∈ S := fun y => (Finset.mem_image.1 y.2).choose_spec.1
  have hg_eq : ∀ y : S.image f, f (g y) = y.1 := fun y => (Finset.mem_image.1 y.2).choose_spec.2
  have hg_inj : Function.Injective g := fun y₁ y₂ h =>
    Subtype.ext (by rw [← hg_eq y₁, ← hg_eq y₂, h])
  let T : Finset α := Finset.univ.image g
  refine ⟨T, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hx
    exact hg_mem y
  · ext b
    simp only [T, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨y, _, rfl⟩, rfl⟩
      rw [hg_eq y]; exact Finset.mem_image.1 y.2
    · intro hb
      exact ⟨g ⟨b, Finset.mem_image.2 hb⟩, ⟨⟨b, Finset.mem_image.2 hb⟩, Finset.mem_univ _, rfl⟩,
        hg_eq _⟩
  · rw [Finset.card_image_of_injective _ hg_inj, Finset.card_univ, Fintype.card_coe]

private theorem finsetPos_insert_update {V W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    {S : Finset (Fin k)} {iFree : Fin k} (hiFree : iFree ∉ S)
    (a : Fin k → V) (b : Fin k → W) (a' : V) (b' : W) :
    finsetPos (insert iFree S) (Function.update a iFree a') (Function.update b iFree b') =
      insert (a', b') (finsetPos S a b) := by
  ext x
  simp only [finsetPos, Finset.mem_image, Finset.mem_insert]
  constructor
  · rintro ⟨i, rfl | hiS, rfl⟩
    · left; simp
    · right; have hne : i ≠ iFree := fun h => hiFree (h ▸ hiS)
      exact ⟨i, hiS, by simp [hne]⟩
  · rintro (rfl | ⟨i, hiS, rfl⟩)
    · exact ⟨iFree, Or.inl rfl, by simp⟩
    · have hne : i ≠ iFree := fun h => hiFree (h ▸ hiS)
      exact ⟨i, Or.inr hiS, by simp [hne]⟩

private theorem finsetPos_erase_insert_update {V W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    {S : Finset (Fin k)} {iFree iDrop : Fin k} (hiFree : iFree ∉ S) (hiDropS : iDrop ∈ S)
    {a : Fin k → V} {b : Fin k → W} {ab : V × W} (hiDropEq : (a iDrop, b iDrop) = ab)
    (hinj : Set.InjOn (fun i => (a i, b i)) (↑S)) (a' : V) (b' : W) :
    finsetPos ((insert iFree S).erase iDrop) (Function.update a iFree a')
        (Function.update b iFree b') =
      insert (a', b') ((finsetPos S a b).erase ab) := by
  ext x
  simp only [finsetPos, Finset.mem_image, Finset.mem_erase, Finset.mem_insert]
  constructor
  · rintro ⟨i, ⟨hneDrop, rfl | hiS⟩, rfl⟩
    · left; simp
    · right
      have hneFree : i ≠ iFree := fun h => hiFree (h ▸ hiS)
      have hneAb : (a i, b i) ≠ ab := fun h =>
        hneDrop (hinj hiS hiDropS (h.trans hiDropEq.symm))
      simp only [Function.update_of_ne hneFree]
      exact ⟨hneAb, i, hiS, rfl⟩
  · rintro (rfl | ⟨hneAb, i, hiS, rfl⟩)
    · have hne : iFree ≠ iDrop := fun h => hiFree (h ▸ hiDropS)
      exact ⟨iFree, ⟨hne, Or.inl rfl⟩, by simp⟩
    · have hneFree : i ≠ iFree := fun h => hiFree (h ▸ hiS)
      have hneDrop : i ≠ iDrop := fun h => hneAb (by rw [h, hiDropEq])
      exact ⟨i, ⟨hneDrop, Or.inr hiS⟩, by simp [hneFree]⟩

private theorem exists_notMem_fin_of_card_lt {k : ℕ} {S : Finset (Fin k)} (hS : S.card < k) :
    ∃ i : Fin k, i ∉ S := by
  by_contra hall; push Not at hall
  have hcard := Finset.card_univ (α := Fin k)
  rw [← Finset.eq_univ_iff_forall.2 hall, Fintype.card_fin] at hcard; omega

/-- `C^k`-equivalence implies weak `C^{<k}`-equivalence for all `k ≥ 2`. -/
theorem GraphCkEquiv.weakCkEquiv {V W : Type*} [Finite V] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ} (hk : 2 ≤ k) (h : GraphCkEquiv G H k) :
    WeakCkEquiv G H k := by
  classical
  let _ := G.structure; let _ := H.structure
  by_cases hV : Nonempty V
  · have hW : Nonempty W := h.1.1 hV
    obtain ⟨v₀⟩ := hV; obtain ⟨w₀⟩ := hW
    let I : Finset (V × W) → Prop := fun p =>
      p.card ≤ k - 1 ∧
      ∃ (S : Finset (Fin k)) (a : Fin k → V) (b : Fin k → W),
        S.card = p.card ∧ finsetPos S a b = p ∧ GraphCkPosEquiv G H k (↑S) a b
    refine ⟨I, ⟨fun hp => hp.1, ?_, ?_, ?_⟩, ?_⟩
    · rintro p ⟨_, S, a, b, -, rfl, hpos⟩
      rw [isLocalIso_finsetPos_iff_partialIsoOn]
      exact (hpos.bijPebbleWins 0).partialIsoOn
    · rintro p ⟨_, S, a, b, hScard, rfl, hpos⟩ hfull ab hab
      obtain ⟨iFree, hiFree⟩ := exists_notMem_fin_of_card_lt (S := S) (by omega)
      obtain ⟨iDrop, hiDropS, hiDropEq⟩ := Finset.mem_image.1 hab
      have hinj : Set.InjOn (fun i => (a i, b i)) (↑S) :=
        Finset.injOn_of_card_image_eq hScard.symm
      obtain ⟨J, hJ, hJS⟩ := graphCkPosEquiv_iff_exists_isBijPebbleBackAndForth.1 hpos
      obtain ⟨f, hf⟩ := hJ.move hJS iFree
      refine ⟨f, fun a' => ?_⟩
      let S₁ : Finset (Fin k) := insert iFree S
      let a₁ := Function.update a iFree a'
      let b₁ := Function.update b iFree (f a')
      have hS₁pos : GraphCkPosEquiv G H k (↑S₁) a₁ b₁ := by
        have hcoe : (↑S₁ : Set (Fin k)) = insert iFree (↑S : Set (Fin k)) := by simp [S₁]
        rw [hcoe]; exact hJ.bijPebbleWinsForever (hf a')
      have hS₁img := finsetPos_insert_update hiFree a b a' (f a')
      have hiso₁ : IsLocalIso G H (insert (a', f a') (finsetPos S a b)) := by
        rw [← hS₁img, isLocalIso_finsetPos_iff_partialIsoOn]
        exact (hS₁pos.bijPebbleWins 0).partialIsoOn
      refine ⟨hiso₁, ?_⟩
      let S₂ : Finset (Fin k) := S₁.erase iDrop
      have hS₂img := finsetPos_erase_insert_update hiFree hiDropS hiDropEq hinj a' (f a')
      obtain ⟨T, hTS₂, hTimg, hTcard⟩ := exists_subset_injective_image S₂ (fun i => (a₁ i, b₁ i))
      have hcard₂ : (insert (a', f a') ((finsetPos S a b).erase ab)).card ≤ k - 1 := by
        have h1 := Finset.card_insert_le (a', f a') ((finsetPos S a b).erase ab)
        have h2 := Finset.card_erase_add_one hab; omega
      refine ⟨hcard₂, T, a₁, b₁, by rw [hTcard]; exact congrArg Finset.card hS₂img,
        hTimg.trans hS₂img, bijPebbleWinsForever_iff_forall_bijPebbleWins.2 fun n =>
          (hS₁pos.bijPebbleWins n).of_subset
            (Finset.coe_subset.2 (hTS₂.trans (Finset.erase_subset _ _)))⟩
    · rintro p ⟨_, S, a, b, hScard, rfl, hpos⟩ hlt
      obtain ⟨iFree, hiFree⟩ := exists_notMem_fin_of_card_lt (S := S) (by omega)
      obtain ⟨J, hJ, hJS⟩ := graphCkPosEquiv_iff_exists_isBijPebbleBackAndForth.1 hpos
      obtain ⟨f, hf⟩ := hJ.move hJS iFree
      refine ⟨f, fun a' => ?_⟩
      let S₁ : Finset (Fin k) := insert iFree S
      let a₁ := Function.update a iFree a'
      let b₁ := Function.update b iFree (f a')
      have hS₁pos : GraphCkPosEquiv G H k (↑S₁) a₁ b₁ := by
        have hcoe : (↑S₁ : Set (Fin k)) = insert iFree (↑S : Set (Fin k)) := by simp [S₁]
        rw [hcoe]; exact hJ.bijPebbleWinsForever (hf a')
      have hS₁img := finsetPos_insert_update hiFree a b a' (f a')
      have hiso₁ : IsLocalIso G H (insert (a', f a') (finsetPos S a b)) := by
        rw [← hS₁img, isLocalIso_finsetPos_iff_partialIsoOn]
        exact (hS₁pos.bijPebbleWins 0).partialIsoOn
      obtain ⟨T, hTS₁, hTimg, hTcard⟩ := exists_subset_injective_image S₁ (fun i => (a₁ i, b₁ i))
      have hcard₁ : (insert (a', f a') (finsetPos S a b)).card ≤ k - 1 := by
        have h1 := Finset.card_insert_le (a', f a') (finsetPos S a b); omega
      refine ⟨hiso₁, hcard₁, T, a₁, b₁, by rw [hTcard]; exact congrArg Finset.card hS₁img,
        hTimg.trans hS₁img, bijPebbleWinsForever_iff_forall_bijPebbleWins.2 fun n =>
          (hS₁pos.bijPebbleWins n).of_subset (Finset.coe_subset.2 hTS₁)⟩
    · refine ⟨by simp, ∅, fun _ => v₀, fun _ => w₀, by simp, by simp [finsetPos], ?_⟩
      simpa using h.2 (fun _ => v₀) (fun _ => w₀)
  · have hW : ¬ Nonempty W := mt h.1.2 hV
    rw [not_nonempty_iff] at hV hW
    refine ⟨fun p => p = ∅, ⟨?_, ?_, ?_, ?_⟩, rfl⟩
    · rintro _ rfl; simp
    · rintro _ rfl; exact isLocalIso_empty G H
    · rintro _ rfl h0; simp at h0; omega
    · rintro _ rfl _; exact ⟨Equiv.equivOfIsEmpty _ _, fun a' => isEmptyElim a'⟩

private theorem finsetPos_update_subset_erase {V W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    {S : Finset (Fin (k - 1))} {a : Fin (k - 1) → V} {b : Fin (k - 1) → W}
    (hfull : (finsetPos S a b).card = k - 1) (j : Fin (k - 1)) (c : V) (d : W) :
    (a j, b j) ∈ finsetPos S a b ∧
    finsetPos (insert j S) (Function.update a j c) (Function.update b j d) ⊆
      insert (c, d) ((finsetPos S a b).erase (a j, b j)) := by
  have hSfull : S = Finset.univ := by
    apply Finset.eq_univ_of_card
    have h1 : (finsetPos S a b).card ≤ S.card := Finset.card_image_le
    have h2 : S.card ≤ Fintype.card (Fin (k - 1)) := Finset.card_le_univ _
    have h3 : Fintype.card (Fin (k - 1)) = k - 1 := Fintype.card_fin _
    omega
  have hinj : Set.InjOn (fun i => (a i, b i)) (↑S) :=
    Finset.injOn_of_card_image_eq (by
      rw [hSfull, Finset.card_univ, Fintype.card_fin]
      simpa [finsetPos, hSfull] using hfull)
  refine ⟨Finset.mem_image_of_mem _ (by rw [hSfull]; exact Finset.mem_univ j), fun x hx => ?_⟩
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx
  by_cases hij : i = j
  · subst hij; simp
  · refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨?_, ?_⟩)
    · simp only [Function.update_of_ne hij]
      intro heq
      exact hij (hinj (by rw [hSfull]; exact Finset.mem_univ i)
        (by rw [hSfull]; exact Finset.mem_univ j) heq)
    · simp only [Function.update_of_ne hij]
      exact Finset.mem_image_of_mem _ (by rw [hSfull]; exact Finset.mem_univ i)

private theorem finsetPos_update_subset_insert {V W : Type*} [DecidableEq V] [DecidableEq W]
    {k : ℕ} (S : Finset (Fin (k - 1))) (a : Fin (k - 1) → V) (b : Fin (k - 1) → W)
    (j : Fin (k - 1)) (c : V) (d : W) :
    finsetPos (insert j S) (Function.update a j c) (Function.update b j d) ⊆
      insert (c, d) (finsetPos S a b) := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
  by_cases hij : i = j
  · subst hij; simp
  · simp only [Function.update_of_ne hij]
    have hiS : i ∈ S := (Finset.mem_insert.1 hi).resolve_left hij
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hiS)

private theorem filter_insert_eq {α : Type*} [Fintype α] [DecidableEq α]
    (j : α) (S : Set α) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ insert j S)] :
    Finset.univ.filter (· ∈ insert j S) = insert j (Finset.univ.filter (· ∈ S)) := by
  ext x; simp

/-- Weak `C^{<k}`-equivalence implies `C^{k-1}`-equivalence for all `k ≥ 2`. -/
theorem WeakCkEquiv.graphCkEquiv_pred {V W : Type*} [Finite V]
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ} (hk : 2 ≤ k) (h : WeakCkEquiv G H k) :
    GraphCkEquiv G H (k - 1) := by
  classical
  let _ := G.structure; let _ := H.structure
  have hbij0 : Nonempty (V ≃ W) := by
    have h1 := (h.weakBijPebbleWins 1).2.2
    have hne : (∅ : Finset (V × W)).card ≠ k - 1 := by simp; omega
    simp only [hne, ↓reduceIte] at h1
    exact ⟨h1.choose⟩
  refine ⟨⟨fun ⟨v⟩ => ⟨hbij0.some v⟩, fun ⟨w⟩ => ⟨hbij0.some.symm w⟩⟩, fun a b => ?_⟩
  let I : Set (Fin (k - 1)) → (Fin (k - 1) → V) → (Fin (k - 1) → W) → Prop :=
    fun S a b => WeakBijPebbleWinsForever G H k (finsetPos (Finset.univ.filter (· ∈ S)) a b)
  refine IsBijPebbleBackAndForth.bijPebbleWinsForever (I := I) ⟨?_, ?_⟩ ?_
  · intro S a b hS
    have hiso := (hS.weakBijPebbleWins 0).localIso
    rw [isLocalIso_finsetPos_iff_partialIsoOn] at hiso
    have hcoe : (↑(Finset.univ.filter (· ∈ S)) : Set (Fin (k - 1))) = S := by ext i; simp
    rwa [hcoe] at hiso
  · intro S a b hS j
    set F := Finset.univ.filter (· ∈ S)
    set p := finsetPos F a b
    obtain ⟨J, hJ, hJp⟩ := hS
    by_cases hfull : p.card = k - 1
    · have hjmem := (finsetPos_update_subset_erase (k := k) hfull j (a j) (b j)).1
      obtain ⟨f, hf⟩ := hJ.moveFull hJp hfull (a j, b j) hjmem
      refine ⟨f, fun c => ?_⟩
      dsimp only [I]; rw [filter_insert_eq]
      exact WeakBijPebbleWinsForever.of_subset
        (finsetPos_update_subset_erase (k := k) hfull j c (f c)).2 ⟨J, hJ, (hf c).2⟩
    · obtain ⟨f, hf⟩ := hJ.movePartial hJp (lt_of_le_of_ne (hJ.card_le hJp) hfull)
      refine ⟨f, fun c => ?_⟩
      dsimp only [I]; rw [filter_insert_eq]
      exact WeakBijPebbleWinsForever.of_subset
        (finsetPos_update_subset_insert F a b j c (f c)) ⟨J, hJ, (hf c).2⟩
  · dsimp only [I]; unfold WeakCkEquiv at h; convert h using 1; ext x; simp [finsetPos]

/-- At `k = 2`, weak `C^{<2}`-equivalence coincides with `C^2`-equivalence. -/
theorem weakCkEquiv_two_iff_graphCkEquiv_two {V W : Type*} [Finite V]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W} :
    WeakCkEquiv G H 2 ↔ GraphCkEquiv G H 2 := by
  classical
  let _ := G.structure; let _ := H.structure
  refine ⟨fun h => ?_, fun h => h.weakCkEquiv le_rfl⟩
  have hbij0 : Nonempty (V ≃ W) := by
    have h1 := (h.weakBijPebbleWins 1).2.2
    simp at h1
    exact ⟨h1.choose⟩
  refine ⟨⟨fun ⟨v⟩ => ⟨hbij0.some v⟩, fun ⟨w⟩ => ⟨hbij0.some.symm w⟩⟩, fun a b => ?_⟩
  let I : Set (Fin 2) → (Fin 2 → V) → (Fin 2 → W) → Prop := fun S a b =>
    PartialIsoOn Language.graph S a b ∧
    ∀ i ∈ S, WeakBijPebbleWinsForever G H 2 {(a i, b i)}
  refine IsBijPebbleBackAndForth.bijPebbleWinsForever (I := I) ⟨fun hI => hI.1, ?_⟩
    ⟨partialIsoOn_empty _ _, fun _ hi => (Set.notMem_empty _ hi).elim⟩
  intro S a b ⟨_, hsingle⟩ j
  let j' : Fin 2 := if j = 0 then 1 else 0
  have hne : j' ≠ j := by fin_cases j <;> decide
  have hall : ∀ i : Fin 2, i = j ∨ i = j' := fun i => by fin_cases j <;> fin_cases i <;> simp [j']
  by_cases hj' : j' ∈ S
  · obtain ⟨J, hJ, hJp⟩ := hsingle j' hj'
    obtain ⟨f, hf⟩ := hJ.moveFull hJp (by simp) (a j', b j') (Finset.mem_singleton_self _)
    refine ⟨f, fun c => ⟨?_, ?_⟩⟩
    · have hiso : IsLocalIso G H (insert (c, f c) {(a j', b j')}) := (hf c).1
      rw [partialIsoOn_graph_iff]
      have hmem : ∀ u : Fin 2,
          (Function.update a j c u, Function.update b j (f c) u) ∈
            insert (c, f c) {(a j', b j')} := fun u => by
        rcases hall u with rfl | hu
        · simp only [Function.update_self]; exact Finset.mem_insert_self _ _
        · rw [hu, Function.update_of_ne hne, Function.update_of_ne hne]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact fun i _ r _ => ⟨hiso.1 _ (hmem i) _ (hmem r), hiso.2 _ (hmem i) _ (hmem r)⟩
    · intro i _
      rcases hall i with rfl | hi
      · have h2 : J {(c, f c)} := by simpa using (hf c).2
        simp only [Function.update_self]
        exact ⟨J, hJ, h2⟩
      · rw [hi, Function.update_of_ne hne, Function.update_of_ne hne]; exact hsingle j' hj'
  · obtain ⟨J, hJ, hJp⟩ := h
    obtain ⟨f, hf⟩ := hJ.movePartial hJp (by simp)
    refine ⟨f, fun c => ⟨?_, ?_⟩⟩
    · have hSsub : insert j S = {j} := by
        ext i; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact ⟨fun h => h.elim id fun hi => (hall i).resolve_right fun h => hj' (h ▸ hi),
          fun h => Or.inl h⟩
      rw [hSsub, partialIsoOn_graph_iff]
      intro i hi r hr
      rw [Set.mem_singleton_iff.1 hi, Set.mem_singleton_iff.1 hr]
      exact ⟨by simp, by simp⟩
    · intro i hi
      rcases hall i with rfl | hi'
      · have h2 : J {(c, f c)} := by simpa using (hf c).2
        simp only [Function.update_self]
        exact ⟨J, hJ, h2⟩
      · rw [hi'] at hi; exact absurd (hi.resolve_left hne) hj'

/-- Sandwich comparison between bijective and weak bijective pebble games:
`G ≡_C^2 H ↔ G ≡_C^{<2} H`, and for every `k ≥ 3`, `G ≡_C^k H → G ≡_C^{<k} H → G ≡_C^{k-1} H`. -/
theorem weakCkEquiv_sandwich {V W : Type*} [Finite V] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} :
    (GraphCkEquiv G H 2 ↔ WeakCkEquiv G H 2) ∧
    ∀ k ≥ 3, (GraphCkEquiv G H k → WeakCkEquiv G H k) ∧
      (WeakCkEquiv G H k → GraphCkEquiv G H (k - 1)) :=
  ⟨weakCkEquiv_two_iff_graphCkEquiv_two.symm,
    fun _ hk => ⟨fun h => h.weakCkEquiv (by omega), fun h => h.graphCkEquiv_pred (by omega)⟩⟩


end CslibFrontier.Logics.FirstOrder.FiniteVariable
