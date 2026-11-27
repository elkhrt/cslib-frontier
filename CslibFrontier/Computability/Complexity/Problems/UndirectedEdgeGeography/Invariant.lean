module

public import CslibFrontier.Computability.Complexity.Problems.UndirectedEdgeGeography.Gadget

/-!
# Edge-Set Invariants for Undirected Edge Geography

Defines the normal Phase-1 edge lists (`normalBranchEdges`, `bridgeEdges`, `normalUsed`) and the
`ValidUsed` invariant (including `EvenEntryOk` for the 3-edge chord loop in even variable gadgets)
for the Fraenkel–Scheinerman–Ullman reduction graph `formulaGraph`.

## Main definitions

* `Cslib.Complexity.UndirectedEdgeGeography.normalBranchEdges`, `bridgeEdges`, `normalUsed`:
  normal edge lists traversed during Phase 1.
* `Cslib.Complexity.UndirectedEdgeGeography.EvenEntryOk`, `ValidUsed`: invariant on used edges
  after a prefix of variable choices `z`.

## Main results

* `Cslib.Complexity.UndirectedEdgeGeography.normalBranchEdges_idx`, `bridgeEdges_idx`: concise
  membership characterizations for normal branch and bridge edges.
* `Cslib.Complexity.UndirectedEdgeGeography.validUsed_normalUsed`, `validUsed_not_mem_branch`,
  `validUsed_extend`: preservation and disjointness properties of `ValidUsed`.
-/

public section

namespace Cslib.Complexity

open Cslib.Complexity Cslib.Logic.PL

namespace UndirectedEdgeGeography

/-! ### Normal used edges and the `ValidUsed` invariant -/

/-- Edges of branch `b` of diamond `j` traversed in a normal pass (excluding even chords). -/
@[expose]
def normalBranchEdges (xs : List ℕ) (ψ : CNF ℕ) (j : ℕ) (b : Bool) : List (Sym2 ℕ) :=
  let r := segCount xs ψ j b
  (if j % 2 == 0 then
    [s(topNode j, aNode j b), s(aNode j b, wNode j b),
      s(wNode j b, cNode j b), s(cNode j b, u1Node j b 0)]
  else [s(topNode j, u1Node j b 0)]) ++
  ((List.range r).flatMap fun k => [s(u1Node j b k, mNode j b k), s(mNode j b k, u2Node j b k)]) ++
  ((List.range (r - 1)).flatMap fun k =>
      [s(u2Node j b k, vNode j b k), s(vNode j b k, u1Node j b (k + 1))]) ++
  [s(u2Node j b (r - 1), botNode j)]

/-- Bridge edges after diamond `j`. -/
@[expose]
def bridgeEdges (j : ℕ) : List (Sym2 ℕ) :=
  if j % 2 == 0 then [s(botNode j, midNode j), s(midNode j, topNode (j + 1))]
  else [s(botNode j, topNode (j + 1))]

/-- Normal used-edge list after choices `z` (length `≤ xs.length`). -/
@[expose]
def normalUsed (xs : List ℕ) (ψ : CNF ℕ) (z : List Bool) : List (Sym2 ℕ) :=
  z.zipIdx.flatMap fun p => normalBranchEdges xs ψ p.2 p.1 ++ bridgeEdges p.2

@[simp]
theorem normalUsed_nil (xs : List ℕ) (ψ : CNF ℕ) : normalUsed xs ψ [] = [] := rfl

@[simp]
theorem bridgeEdges_even {j : ℕ} (h : j % 2 = 0) :
    bridgeEdges j = [s(botNode j, midNode j), s(midNode j, topNode (j + 1))] := by
  simp [bridgeEdges, h]

@[simp]
theorem bridgeEdges_odd {j : ℕ} (h : j % 2 = 1) :
    bridgeEdges j = [s(botNode j, topNode (j + 1))] := by
  simp [bridgeEdges, h]

theorem normalBranchEdges_eq_append (xs : List ℕ) (ψ : CNF ℕ) (j : ℕ) (b : Bool) :
    normalBranchEdges xs ψ j b =
      (if j % 2 == 0 then
        [s(topNode j, aNode j b), s(aNode j b, wNode j b),
          s(wNode j b, cNode j b), s(cNode j b, u1Node j b 0)]
      else [s(topNode j, u1Node j b 0)]) ++
      ((List.range (segCount xs ψ j b)).flatMap fun k =>
          [s(u1Node j b k, mNode j b k), s(mNode j b k, u2Node j b k)]) ++
      ((List.range (segCount xs ψ j b - 1)).flatMap fun k =>
          [s(u2Node j b k, vNode j b k), s(vNode j b k, u1Node j b (k + 1))]) ++
      [s(u2Node j b (segCount xs ψ j b - 1), botNode j)] := rfl

theorem bridgeEdges_eq_ite (j : ℕ) :
    bridgeEdges j =
      if j % 2 == 0 then [s(botNode j, midNode j), s(midNode j, topNode (j + 1))]
      else [s(botNode j, topNode (j + 1))] := rfl

theorem normalUsed_eq_flatMap (xs : List ℕ) (ψ : CNF ℕ) (z : List Bool) :
    normalUsed xs ψ z =
      z.zipIdx.flatMap fun p => normalBranchEdges xs ψ p.2 p.1 ++ bridgeEdges p.2 := rfl

/-- Even-diamond entry/bridge invariant on `used` for chosen branch `b = z[j]`. -/
@[expose]
def EvenEntryOk (j : ℕ) (b : Bool) (used : List (Sym2 ℕ)) : Prop :=
  s(wNode j b, cNode j b) ∈ used ∧ s(cNode j b, u1Node j b 0) ∈ used ∧
  s(botNode j, midNode j) ∈ used ∧ s(midNode j, topNode (j + 1)) ∈ used ∧
  ((s(topNode j, aNode j b) ∈ used ∧ s(aNode j b, wNode j b) ∈ used ∧
      s(topNode j, wNode j b) ∉ used) ∨
   (s(topNode j, wNode j b) ∈ used ∧ s(topNode j, aNode j b) ∉ used ∧
      s(aNode j b, wNode j b) ∉ used)) ∧
  s(topNode j, aNode j (!b)) ∉ used ∧ s(aNode j (!b), wNode j (!b)) ∉ used ∧
  s(topNode j, wNode j (!b)) ∉ used ∧
  s(wNode j (!b), cNode j (!b)) ∉ used ∧ s(cNode j (!b), u1Node j (!b) 0) ∉ used

/-- A used-edge list `used` is **valid for prefix `z`** (`z.length ≤ xs.length`). -/
@[expose]
def ValidUsed (xs : List ℕ) (ψ : CNF ℕ) (z : List Bool) (used : List (Sym2 ℕ)) : Prop :=
  (∀ j, (hj : j < z.length) →
    let b := z[j]
    (j % 2 = 0 → EvenEntryOk j b used) ∧
    (j % 2 = 1 →
      s(topNode j, u1Node j b 0) ∈ used ∧ s(botNode j, topNode (j + 1)) ∈ used) ∧
    (∀ k < segCount xs ψ j b - 1,
      s(u2Node j b k, vNode j b k) ∈ used ∧ s(vNode j b k, u1Node j b (k + 1)) ∈ used) ∧
    s(u2Node j b (segCount xs ψ j b - 1), botNode j) ∈ used ∧
    (∀ k < segCount xs ψ j b,
      (s(u1Node j b k, mNode j b k) ∈ used ∧ s(mNode j b k, u2Node j b k) ∈ used) ∨
      (∃ hk : k < (occClauses xs ψ j b).length,
        let i := (occClauses xs ψ j b)[k]
        s(clauseNode i, u1Node j b k) ∈ used ∧ s(clauseNode i, u2Node j b k) ∈ used))) ∧
  (∀ e ∈ used,
    ∃ j, ∃ hj : j < z.length,
      let b := z[j]
      e ∈ normalBranchEdges xs ψ j b ∨ e ∈ bridgeEdges j ∨
      (j % 2 = 0 ∧
        (e = s(topNode j, wNode j b) ∨ e = s(topNode j, aNode j (!b)) ∨
         e = s(aNode j (!b), wNode j (!b)) ∨ e = s(topNode j, wNode j (!b)))) ∨
      (∃ k, ∃ hk : k < (occClauses xs ψ j b).length,
        let i := (occClauses xs ψ j b)[k]
        e = s(clauseNode i, u1Node j b k) ∨ e = s(clauseNode i, u2Node j b k)))

/-! ### Concise membership characterizations for `normalBranchEdges` and `bridgeEdges` -/

theorem not_mem_normalBranchEdges_of_tag {xs : List ℕ} {ψ : CNF ℕ} {j t arg w : ℕ}
    {b : Bool} (h0 : t ≠ 0) (h1 : t ≠ 1) (h3 : t ≠ 3) (h4 : t ≠ 4) (h5 : t ≠ 5)
    (h6 : t ≠ 6) (h7 : t ≠ 7) (h8 : t ≠ 8) (h9 : t ≠ 9) :
    s(Nat.pair t arg, w) ∉ normalBranchEdges xs ψ j b := by
  simp only [normalBranchEdges, List.mem_append, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro (((h | ⟨k, _, h | h⟩) | ⟨k, _, h | h⟩) | h)
  · split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    · rcases h with h | h | h | h
      · exact sym2_ne_of_tag h0 h3 h
      · exact sym2_ne_of_tag h3 h4 h
      · exact sym2_ne_of_tag h4 h5 h
      · exact sym2_ne_of_tag h5 h6 h
    · exact sym2_ne_of_tag h0 h6 h
  · exact sym2_ne_of_tag h6 h7 h
  · exact sym2_ne_of_tag h7 h8 h
  · exact sym2_ne_of_tag h8 h9 h
  · exact sym2_ne_of_tag h9 h6 h
  · exact sym2_ne_of_tag h8 h1 h

theorem not_mem_bridgeEdges_of_tag {j t arg w : ℕ}
    (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) :
    s(Nat.pair t arg, w) ∉ bridgeEdges j := by
  unfold bridgeEdges
  split_ifs <;> simp only [List.mem_cons, List.not_mem_nil, or_false]
  · rintro (h | h)
    · exact sym2_ne_of_tag h1 h2 h
    · exact sym2_ne_of_tag h2 h0 h
  · exact sym2_ne_of_tag h1 h0

/-- Exact index extraction from `normalBranchEdges` for every edge family. -/
private theorem bool_toNat_inj {b₁ b₂ : Bool} (h : b₁.toNat = b₂.toNat) : b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> simp_all

/-- Generalized disjoint-tag elimination for `Sym2` pairs when neither orientation matches. -/
theorem sym2_ne_of_tags {a x b y c z d w : ℕ}
    (h : (a ≠ c ∨ b ≠ d) ∧ (a ≠ d ∨ b ≠ c)) :
    s(Nat.pair a x, Nat.pair b y) ≠ s(Nat.pair c z, Nat.pair d w) := by
  intro heq
  rcases pair_sym2_eq heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases h.1 with hc | hd
    · exact pair_ne_of_ne hc h1
    · exact pair_ne_of_ne hd h2
  · rcases h.2 with hd | hc
    · exact pair_ne_of_ne hd h1
    · exact pair_ne_of_ne hc h2

theorem normalBranchEdges_idx {xs : List ℕ} {ψ : CNF ℕ} {j j' : ℕ} {b b' : Bool} :
    (s(topNode j, aNode j b) ∈ normalBranchEdges xs ψ j' b' → j' = j ∧ b' = b) ∧
    (s(aNode j b, wNode j b) ∈ normalBranchEdges xs ψ j' b' → j' = j ∧ b' = b) ∧
    (s(topNode j, wNode j b) ∉ normalBranchEdges xs ψ j' b') ∧
    (s(wNode j b, cNode j b) ∈ normalBranchEdges xs ψ j' b' → j' = j ∧ b' = b) ∧
    (s(cNode j b, u1Node j b 0) ∈ normalBranchEdges xs ψ j' b' → j' = j ∧ b' = b) ∧
    (s(topNode j, u1Node j b 0) ∈ normalBranchEdges xs ψ j' b' → j' = j ∧ b' = b) ∧
    (∀ k, s(u1Node j b k, mNode j b k) ∈ normalBranchEdges xs ψ j' b' → j' = j ∧ b' = b) ∧
    (∀ k, s(mNode j b k, u2Node j b k) ∈ normalBranchEdges xs ψ j' b' → j' = j ∧ b' = b) ∧
    (∀ k, s(u2Node j b k, vNode j b k) ∈ normalBranchEdges xs ψ j' b' → j' = j ∧ b' = b) ∧
    (∀ k, s(vNode j b k, u1Node j b (k + 1)) ∈ normalBranchEdges xs ψ j' b' → j' = j ∧ b' = b) ∧
    (∀ k, s(u2Node j b k, botNode j) ∈ normalBranchEdges xs ψ j' b' → j' = j ∧ b' = b) := by
  have hmem : ∀ {e : Sym2 ℕ}, e ∈ normalBranchEdges xs ψ j' b' →
      e = s(topNode j', aNode j' b') ∨ e = s(aNode j' b', wNode j' b') ∨
      e = s(wNode j' b', cNode j' b') ∨ e = s(cNode j' b', u1Node j' b' 0) ∨
      e = s(topNode j', u1Node j' b' 0) ∨
      (∃ k, e = s(u1Node j' b' k, mNode j' b' k) ∨ e = s(mNode j' b' k, u2Node j' b' k) ∨
        e = s(u2Node j' b' k, vNode j' b' k) ∨ e = s(vNode j' b' k, u1Node j' b' (k + 1))) ∨
      e = s(u2Node j' b' (segCount xs ψ j' b' - 1), botNode j') := by
    intro e he
    simp only [normalBranchEdges, List.mem_append, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with (((h | ⟨k, _, h | h⟩) | ⟨k, _, h | h⟩) | h)
    · split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      · rcases h with rfl | rfl | rfl | rfl <;> simp
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, Or.inl h⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, Or.inr (Or.inl h)⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, Or.inr (Or.inr (Or.inl h))⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, Or.inr (Or.inr (Or.inr h))⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  -- Each of the 11 clauses reduces to matching tags by `pair_sym2_eq`!
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro he
    rcases hmem he with h | h | h | h | h | ⟨k, h | h | h | h⟩ | h
    · rcases pair_sym2_eq h with ⟨ha, hb⟩ | ⟨ha, _⟩
      · simp only [topNode_eq_pair, aNode_eq_pair, Nat.pair_eq_pair, true_and] at ha hb
        exact ⟨ha.symm, (bool_toNat_inj hb.2).symm⟩
      · exact absurd ha (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tags (by decide))
    · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
      · exact absurd hb (pair_ne_of_ne (by decide))
      · exact absurd ha (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · intro he
    rcases hmem he with h | h | h | h | h | ⟨k, h | h | h | h⟩ | h
    · exact absurd h (sym2_ne_of_tags (by decide))
    · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
      · simp only [aNode_eq_pair, Nat.pair_eq_pair, true_and] at ha
        exact ⟨ha.1.symm, (bool_toNat_inj ha.2).symm⟩
      · exact absurd ha (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · intro he
    rcases hmem he with h | h | h | h | h | ⟨k, h | h | h | h⟩ | h
    · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
      · exact pair_ne_of_ne (by decide) hb
      · exact pair_ne_of_ne (by decide) ha
    · exact sym2_ne_of_tag (by decide) (by decide) h
    · exact sym2_ne_of_tags (by decide) h
    · exact sym2_ne_of_tag (by decide) (by decide) h
    · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
      · exact pair_ne_of_ne (by decide) hb
      · exact pair_ne_of_ne (by decide) ha
    · exact sym2_ne_of_tag (by decide) (by decide) h
    · exact sym2_ne_of_tag (by decide) (by decide) h
    · exact sym2_ne_of_tag (by decide) (by decide) h
    · exact sym2_ne_of_tag (by decide) (by decide) h
    · exact sym2_ne_of_tag (by decide) (by decide) h
  · intro he
    rcases hmem he with h | h | h | h | h | ⟨k, h | h | h | h⟩ | h
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact absurd ha (pair_ne_of_ne (by decide))
      · exact absurd hb (pair_ne_of_ne (by decide))
    · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
      · simp only [wNode_eq_pair, Nat.pair_eq_pair, true_and] at ha
        exact ⟨ha.1.symm, (bool_toNat_inj ha.2).symm⟩
      · exact absurd ha (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · intro he
    rcases hmem he with h | h | h | h | h | ⟨k, h | h | h | h⟩ | h
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tags (by decide))
    · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
      · simp only [cNode_eq_pair, Nat.pair_eq_pair, true_and] at ha
        exact ⟨ha.1.symm, (bool_toNat_inj ha.2).symm⟩
      · exact absurd ha (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · intro he
    rcases hmem he with h | h | h | h | h | ⟨k, h | h | h | h⟩ | h
    · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
      · exact absurd hb (pair_ne_of_ne (by decide))
      · exact absurd ha (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases pair_sym2_eq h with ⟨ha, hb⟩ | ⟨ha, _⟩
      · simp only [topNode_eq_pair, u1Node_eq_pair, Nat.pair_eq_pair, true_and] at ha hb
        exact ⟨ha.symm, (bool_toNat_inj hb.2.1).symm⟩
      · exact absurd ha (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · intro k he
    rcases hmem he with h | h | h | h | h | ⟨k', h | h | h | h⟩ | h
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact absurd ha (pair_ne_of_ne (by decide))
      · exact absurd hb (pair_ne_of_ne (by decide))
    · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact absurd ha (pair_ne_of_ne (by decide))
      · exact absurd hb (pair_ne_of_ne (by decide))
    · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
      · simp only [u1Node_eq_pair, Nat.pair_eq_pair, true_and] at ha
        exact ⟨ha.1.symm, (bool_toNat_inj ha.2.1).symm⟩
      · exact absurd ha (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact absurd ha (pair_ne_of_ne (by decide))
      · exact absurd hb (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · intro k he
    rcases hmem he with h | h | h | h | h | ⟨k', h | h | h | h⟩ | h
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact absurd ha (pair_ne_of_ne (by decide))
      · exact absurd hb (pair_ne_of_ne (by decide))
    · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
      · simp only [mNode_eq_pair, Nat.pair_eq_pair, true_and] at ha
        exact ⟨ha.1.symm, (bool_toNat_inj ha.2.1).symm⟩
      · exact absurd ha (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · intro k he
    rcases hmem he with h | h | h | h | h | ⟨k', h | h | h | h⟩ | h
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tags (by decide))
    · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
      · simp only [u2Node_eq_pair, Nat.pair_eq_pair, true_and] at ha
        exact ⟨ha.1.symm, (bool_toNat_inj ha.2.1).symm⟩
      · exact absurd ha (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
      · exact absurd hb (pair_ne_of_ne (by decide))
      · exact absurd ha (pair_ne_of_ne (by decide))
  · intro k he
    rcases hmem he with h | h | h | h | h | ⟨k', h | h | h | h⟩ | h
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact absurd ha (pair_ne_of_ne (by decide))
      · exact absurd hb (pair_ne_of_ne (by decide))
    · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
      · simp only [vNode_eq_pair, Nat.pair_eq_pair, true_and] at ha
        exact ⟨ha.1.symm, (bool_toNat_inj ha.2.1).symm⟩
      · exact absurd ha (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · intro k he
    rcases hmem he with h | h | h | h | h | ⟨k', h | h | h | h⟩ | h
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tags (by decide))
    · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
      · exact absurd hb (pair_ne_of_ne (by decide))
      · exact absurd ha (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tags (by decide))
    · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
      · simp only [u2Node_eq_pair, Nat.pair_eq_pair, true_and] at ha
        exact ⟨ha.1.symm, (bool_toNat_inj ha.2.1).symm⟩
      · exact absurd ha (pair_ne_of_ne (by decide))

theorem bridgeEdges_idx {j j' : ℕ} :
    (s(botNode j, midNode j) ∈ bridgeEdges j' → j' = j) ∧
    (s(midNode j, topNode (j + 1)) ∈ bridgeEdges j' → j' = j) ∧
    (s(botNode j, topNode (j + 1)) ∈ bridgeEdges j' → j' = j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; unfold bridgeEdges at h
    split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    · rcases h with h | h
      · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
        · simp only [botNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; exact ha.symm
        · exact absurd ha (pair_ne_of_ne (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
      · exact absurd hb (pair_ne_of_ne (by decide))
      · exact absurd ha (pair_ne_of_ne (by decide))
  · intro h; unfold bridgeEdges at h
    split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    · rcases h with h | h
      · exact absurd h (sym2_ne_of_tags (by decide))
      · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
        · simp only [midNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; exact ha.symm
        · exact absurd ha (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · intro h; unfold bridgeEdges at h
    split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    · rcases h with h | h
      · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
        · exact absurd hb (pair_ne_of_ne (by decide))
        · exact absurd ha (pair_ne_of_ne (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
      · simp only [botNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; exact ha.symm
      · exact absurd ha (pair_ne_of_ne (by decide))

theorem chooser_edge_not_mem_validUsed {xs : List ℕ} {ψ : CNF ℕ} {z : List Bool}
    {used : List (Sym2 ℕ)} (hV : ValidUsed xs ψ z used) (w : ℕ) :
    s(chooserNode, w) ∉ used := by
  intro hmem
  obtain ⟨j, _, h⟩ := hV.2 _ hmem
  rcases h with h | h | ⟨_, h | h | h | h⟩ | ⟨k, _, h | h⟩
  · exact not_mem_normalBranchEdges_of_tag (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) h
  · exact not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide) h
  · exact sym2_ne_of_tag (by decide) (by decide) h
  · exact sym2_ne_of_tag (by decide) (by decide) h
  · exact sym2_ne_of_tag (by decide) (by decide) h
  · exact sym2_ne_of_tag (by decide) (by decide) h
  · exact sym2_ne_of_tag (by decide) (by decide) h
  · exact sym2_ne_of_tag (by decide) (by decide) h

theorem clause_edge_not_mem_normalUsed {xs : List ℕ} {ψ : CNF ℕ} {z : List Bool}
    {i w : ℕ} : s(clauseNode i, w) ∉ normalUsed xs ψ z := by
  simp only [normalUsed, List.mem_flatMap, List.mem_append]
  rintro ⟨⟨b, j⟩, -, h | h⟩
  · exact not_mem_normalBranchEdges_of_tag (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) h
  · exact not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide) h

/-- Any edge `e` whose `normalBranchEdges` occurrences force `(j', b') = (j, b)` and which
never lies in `bridgeEdges`, even-entry extras, or clause edges is absent from `used`. -/
private theorem validUsed_not_mem_of_idx {xs : List ℕ} {ψ : CNF ℕ} {z : List Bool}
    {used : List (Sym2 ℕ)} (hV : ValidUsed xs ψ z used) {j : ℕ} {b : Bool} {e : Sym2 ℕ}
    (hjb : ∀ hj : j < z.length, b ≠ z[j])
    (hnb : ∀ j' b', e ∈ normalBranchEdges xs ψ j' b' → j' = j ∧ b' = b)
    (hbr : ∀ j', e ∉ bridgeEdges j')
    (hev : ∀ j' b', e = s(topNode j', wNode j' b') ∨ e = s(topNode j', aNode j' (!b')) ∨
      e = s(aNode j' (!b'), wNode j' (!b')) ∨ e = s(topNode j', wNode j' (!b')) → False)
    (hcl : ∀ j' b' k i, e ≠ s(clauseNode i, u1Node j' b' k) ∧
      e ≠ s(clauseNode i, u2Node j' b' k)) :
    e ∉ used := by
  intro hmem
  obtain ⟨j', hj', h⟩ := hV.2 e hmem
  rcases h with h | h | ⟨_, h⟩ | ⟨k, _, h | h⟩
  · obtain ⟨rfl, rfl⟩ := hnb j' z[j'] h; exact hjb hj' rfl
  · exact hbr j' h
  · exact hev j' z[j'] h
  · exact (hcl j' z[j'] k _).1 h
  · exact (hcl j' z[j'] k _).2 h

theorem validUsed_normalUsed (xs : List ℕ) (ψ : CNF ℕ) (z : List Bool) :
    ValidUsed xs ψ z (normalUsed xs ψ z) := by
  have hmem_nb : ∀ {j : ℕ} (hj : j < z.length) {e : Sym2 ℕ},
      e ∈ normalBranchEdges xs ψ j z[j] → e ∈ normalUsed xs ψ z := by
    intro j hj e he
    simp only [normalUsed, List.mem_flatMap, List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff, List.mem_append]
    exact ⟨(z[j], j), ⟨hj, rfl⟩, Or.inl he⟩
  have hmem_br : ∀ {j : ℕ} (hj : j < z.length) {e : Sym2 ℕ},
      e ∈ bridgeEdges j → e ∈ normalUsed xs ψ z := by
    intro j hj e he
    simp only [normalUsed, List.mem_flatMap, List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff, List.mem_append]
    exact ⟨(z[j], j), ⟨hj, rfl⟩, Or.inr he⟩
  have hno : ∀ {j : ℕ} {b : Bool} {e : Sym2 ℕ},
      (∀ j' b', e ∈ normalBranchEdges xs ψ j' b' → j' = j ∧ b' = b) →
      (∀ j', e ∉ bridgeEdges j') →
      ∀ (hj : j < z.length), b ≠ z[j] → e ∉ normalUsed xs ψ z := by
    intro j b e hnb hbr _ hne hmem
    simp only [normalUsed, List.mem_flatMap, List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff, List.mem_append] at hmem
    obtain ⟨⟨b', j'⟩, ⟨hj', hb'⟩, h1 | h2⟩ := hmem
    · dsimp only at hj' hb' h1; subst hb'; obtain ⟨rfl, rfl⟩ := hnb j' z[j'] h1; exact hne rfl
    · dsimp only at h2; exact hbr j' h2
  have hno_chord : ∀ j b, s(topNode j, wNode j b) ∉ normalUsed xs ψ z := by
    intro j b hmem
    simp only [normalUsed, List.mem_flatMap, List.mem_append] at hmem
    obtain ⟨⟨b', j'⟩, -, h1 | h2⟩ := hmem
    · exact normalBranchEdges_idx.2.2.1 h1
    · have h2' : s(wNode j b, topNode j) ∈ bridgeEdges j' := Sym2.eq_swap ▸ h2
      exact not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide) h2'
  refine ⟨fun j hj => ?_, fun e he => ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hpar
      refine ⟨hmem_nb hj (by simp [normalBranchEdges, hpar]),
        hmem_nb hj (by simp [normalBranchEdges, hpar]),
        hmem_br hj (by simp [bridgeEdges, hpar]),
        hmem_br hj (by simp [bridgeEdges, hpar]),
        Or.inl ⟨hmem_nb hj (by simp [normalBranchEdges, hpar]),
          hmem_nb hj (by simp [normalBranchEdges, hpar]), hno_chord _ _⟩,
        hno (fun _ _ => normalBranchEdges_idx.1) (fun _ =>
            not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide) ∘ (Sym2.eq_swap ▸ ·))
            hj (by simp),
        hno (fun _ _ => normalBranchEdges_idx.2.1) (fun _ =>
            not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide)) hj (by simp),
        hno_chord _ _,
        hno (fun _ _ => normalBranchEdges_idx.2.2.2.1) (fun _ =>
          not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide)) hj (by simp),
        hno (fun _ _ => normalBranchEdges_idx.2.2.2.2.1) (fun _ =>
          not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide)) hj (by simp)⟩
    · intro hpar
      exact ⟨hmem_nb hj (by simp [normalBranchEdges, hpar]),
        hmem_br hj (by simp [bridgeEdges, hpar])⟩
    · intro k hk
      exact ⟨hmem_nb hj (by simp only [normalBranchEdges, List.mem_append, List.mem_flatMap,
          List.mem_range, List.mem_cons]; exact Or.inl (Or.inr ⟨k, hk, Or.inl rfl⟩)),
        hmem_nb hj (by simp only [normalBranchEdges, List.mem_append, List.mem_flatMap,
          List.mem_range, List.mem_cons]; exact Or.inl (Or.inr ⟨k, hk, Or.inr (Or.inl rfl)⟩))⟩
    · exact hmem_nb hj (by simp [normalBranchEdges])
    · intro k hk
      left
      exact ⟨hmem_nb hj (by simp only [normalBranchEdges, List.mem_append, List.mem_flatMap,
          List.mem_range, List.mem_cons]; exact Or.inl (Or.inl (Or.inr ⟨k, hk, Or.inl rfl⟩))),
        hmem_nb hj (by
          simp only [normalBranchEdges, List.mem_append, List.mem_flatMap,
            List.mem_range, List.mem_cons]
          exact Or.inl (Or.inl (Or.inr ⟨k, hk, Or.inr (Or.inl rfl)⟩)))⟩
  · simp only [normalUsed, List.mem_flatMap, List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff, List.mem_append] at he
    obtain ⟨⟨b, j⟩, ⟨hj, hb⟩, hmem⟩ := he
    dsimp only at hj hb hmem; subst hb
    rcases hmem with h1 | h2
    · exact ⟨j, hj, Or.inl h1⟩
    · exact ⟨j, hj, Or.inr (Or.inl h2)⟩

theorem validUsed_not_mem_branch {xs : List ℕ} {ψ : CNF ℕ} {z : List Bool}
    {used : List (Sym2 ℕ)} (hV : ValidUsed xs ψ z used) {j : ℕ} {b : Bool}
    (hjb : ∀ hj : j < z.length, b ≠ z[j]) :
    (∀ k, s(u1Node j b k, mNode j b k) ∉ used ∧ s(mNode j b k, u2Node j b k) ∉ used ∧
      s(u2Node j b k, vNode j b k) ∉ used ∧ s(vNode j b k, u1Node j b (k + 1)) ∉ used) ∧
    s(u2Node j b (segCount xs ψ j b - 1), botNode j) ∉ used ∧
    (j % 2 = 0 → s(wNode j b, cNode j b) ∉ used ∧ s(cNode j b, u1Node j b 0) ∉ used) ∧
    (j % 2 = 1 → s(topNode j, u1Node j b 0) ∉ used) := by
  refine ⟨fun k => ⟨
    validUsed_not_mem_of_idx hV hjb (fun _ _ => normalBranchEdges_idx.2.2.2.2.2.2.1 k)
      (fun _ => not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide))
      (fun _ _ h => by rcases h with h | h | h | h <;> exact sym2_ne_of_tags (by decide) h)
      (fun _ _ _ _ => ⟨(sym2_ne_of_tag (by decide) (by decide)).symm,
        (sym2_ne_of_tag (by decide) (by decide)).symm⟩),
    validUsed_not_mem_of_idx hV hjb (fun _ _ => normalBranchEdges_idx.2.2.2.2.2.2.2.1 k)
      (fun _ => not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide))
      (fun _ _ h => by rcases h with h | h | h | h <;> exact sym2_ne_of_tags (by decide) h)
      (fun _ _ _ _ => ⟨(sym2_ne_of_tag (by decide) (by decide)).symm,
        (sym2_ne_of_tag (by decide) (by decide)).symm⟩),
    validUsed_not_mem_of_idx hV hjb (fun _ _ => normalBranchEdges_idx.2.2.2.2.2.2.2.2.1 k)
      (fun _ => not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide))
      (fun _ _ h => by rcases h with h | h | h | h <;> exact sym2_ne_of_tags (by decide) h)
      (fun _ _ _ _ => ⟨(sym2_ne_of_tag (by decide) (by decide)).symm,
        (sym2_ne_of_tag (by decide) (by decide)).symm⟩),
    validUsed_not_mem_of_idx hV hjb (fun _ _ => normalBranchEdges_idx.2.2.2.2.2.2.2.2.2.1 k)
      (fun _ => not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide))
      (fun _ _ h => by rcases h with h | h | h | h <;> exact sym2_ne_of_tags (by decide) h)
      (fun _ _ _ _ => ⟨(sym2_ne_of_tag (by decide) (by decide)).symm,
        (sym2_ne_of_tag (by decide) (by decide)).symm⟩)⟩,
    validUsed_not_mem_of_idx hV hjb (fun _ _ => normalBranchEdges_idx.2.2.2.2.2.2.2.2.2.2 _)
      (fun _ => not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide))
      (fun _ _ h => by rcases h with h | h | h | h <;> exact sym2_ne_of_tags (by decide) h)
      (fun _ _ _ _ => ⟨(sym2_ne_of_tag (by decide) (by decide)).symm,
        (sym2_ne_of_tag (by decide) (by decide)).symm⟩),
    fun _ => ⟨
      validUsed_not_mem_of_idx hV hjb (fun _ _ => normalBranchEdges_idx.2.2.2.1)
        (fun _ => not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide))
        (fun _ _ h => by rcases h with h | h | h | h <;> exact sym2_ne_of_tags (by decide) h)
        (fun _ _ _ _ => ⟨(sym2_ne_of_tag (by decide) (by decide)).symm,
          (sym2_ne_of_tag (by decide) (by decide)).symm⟩),
      validUsed_not_mem_of_idx hV hjb (fun _ _ => normalBranchEdges_idx.2.2.2.2.1)
        (fun _ => not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide))
        (fun _ _ h => by rcases h with h | h | h | h <;> exact sym2_ne_of_tags (by decide) h)
        (fun _ _ _ _ => ⟨(sym2_ne_of_tag (by decide) (by decide)).symm,
          (sym2_ne_of_tag (by decide) (by decide)).symm⟩)⟩,
    fun _ => validUsed_not_mem_of_idx hV hjb (fun _ _ => normalBranchEdges_idx.2.2.2.2.2.1)
      (fun _ => not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide) ∘ (Sym2.eq_swap ▸ ·))
      (fun _ _ h => by rcases h with h | h | h | h <;> exact sym2_ne_of_tags (by decide) h)
      (fun _ _ _ _ => ⟨(sym2_ne_of_tag (by decide) (by decide)).symm,
        (sym2_ne_of_tag (by decide) (by decide)).symm⟩)⟩

/-- Extending `ValidUsed` after crossing diamond `j = z.length`. -/
theorem validUsed_extend {xs : List ℕ} {ψ : CNF ℕ} {z : List Bool} {used used' : List (Sym2 ℕ)}
    {b : Bool} (hV : ValidUsed xs ψ z used)
    (hsub : ∀ e ∈ used, e ∈ used')
    (hnew : ∀ e ∈ used', e ∈ used ∨
      e ∈ normalBranchEdges xs ψ z.length b ∨ e ∈ bridgeEdges z.length ∨
      (z.length % 2 = 0 ∧
        (e = s(topNode z.length, wNode z.length b) ∨
         e = s(topNode z.length, aNode z.length (!b)) ∨
         e = s(aNode z.length (!b), wNode z.length (!b)) ∨
         e = s(topNode z.length, wNode z.length (!b)))) ∨
      (∃ k, ∃ hk : k < (occClauses xs ψ z.length b).length,
        let i := (occClauses xs ψ z.length b)[k]
        e = s(clauseNode i, u1Node z.length b k) ∨ e = s(clauseNode i, u2Node z.length b k)))
    (hev_ok : z.length % 2 = 0 → EvenEntryOk z.length b used')
    (hodd_ok : z.length % 2 = 1 →
      s(topNode z.length, u1Node z.length b 0) ∈ used' ∧
      s(botNode z.length, topNode (z.length + 1)) ∈ used')
    (hconn : ∀ k < segCount xs ψ z.length b - 1,
      s(u2Node z.length b k, vNode z.length b k) ∈ used' ∧
      s(vNode z.length b k, u1Node z.length b (k + 1)) ∈ used')
    (hbot : s(u2Node z.length b (segCount xs ψ z.length b - 1), botNode z.length) ∈ used')
    (hseg : ∀ k < segCount xs ψ z.length b,
      (s(u1Node z.length b k, mNode z.length b k) ∈ used' ∧
       s(mNode z.length b k, u2Node z.length b k) ∈ used') ∨
      (∃ hk : k < (occClauses xs ψ z.length b).length,
        let i := (occClauses xs ψ z.length b)[k]
        s(clauseNode i, u1Node z.length b k) ∈ used' ∧
        s(clauseNode i, u2Node z.length b k) ∈ used')) :
    ValidUsed xs ψ (z ++ [b]) used' := by
  have hkeep : ∀ {j : ℕ} {e : Sym2 ℕ}, j < z.length →
      (∀ b', e ∈ normalBranchEdges xs ψ z.length b' → False) →
      e ∉ bridgeEdges z.length →
      (∀ b', e = s(topNode z.length, wNode z.length b') ∨
        e = s(topNode z.length, aNode z.length b') ∨
        e = s(aNode z.length b', wNode z.length b') → False) →
      (∀ k i, e ≠ s(clauseNode i, u1Node z.length b k) ∧
              e ≠ s(clauseNode i, u2Node z.length b k)) →
      e ∉ used → e ∉ used' := by
    intro j e _ h1 h2 h3 h4 h5 hm
    rcases hnew e hm with h | h | h | ⟨_, h | h | h | h⟩ | ⟨k, _, h | h⟩
    · exact h5 h
    · exact h1 b h
    · exact h2 h
    · exact h3 b (Or.inl h)
    · exact h3 (!b) (Or.inr (Or.inl h))
    · exact h3 (!b) (Or.inr (Or.inr h))
    · exact h3 (!b) (Or.inl h)
    · exact (h4 k _).1 h
    · exact (h4 k _).2 h
  refine ⟨fun j hj => ?_, fun e he => ?_⟩
  · simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < z.length
    · have hget : (z ++ [b])[j] = z[j] := List.getElem_append_left hlt
      simp only [hget]
      obtain ⟨hev, hodd, hc, hb, hs⟩ := hV.1 j hlt
      refine ⟨fun hpar => ?_, fun hpar => ⟨hsub _ (hodd hpar).1, hsub _ (hodd hpar).2⟩,
        fun k hk => ⟨hsub _ (hc k hk).1, hsub _ (hc k hk).2⟩, hsub _ hb,
        fun k hk => (hs k hk).imp (fun h => ⟨hsub _ h.1, hsub _ h.2⟩)
          (fun ⟨hko, h1, h2⟩ => ⟨hko, hsub _ h1, hsub _ h2⟩)⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hev hpar
      have hntw : ∀ bb : Bool, s(topNode j, wNode j bb) ∉ used →
          s(topNode j, wNode j bb) ∉ used' := fun bb =>
        hkeep hlt (fun _ h => normalBranchEdges_idx.2.2.1 h)
          (not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide) ∘ (Sym2.eq_swap ▸ ·))
          (fun _ h => by
            rcases h with h | h | h
            · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
              · simp only [topNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; omega
              · exact pair_ne_of_ne (by decide) ha
            · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
              · exact pair_ne_of_ne (by decide) hb
              · exact pair_ne_of_ne (by decide) ha
            · exact sym2_ne_of_tag (by decide) (by decide) h)
          (fun _ _ => ⟨(sym2_ne_of_tag (by decide) (by decide)).symm,
            (sym2_ne_of_tag (by decide) (by decide)).symm⟩)
      have hnta : ∀ bb : Bool, s(topNode j, aNode j bb) ∉ used →
          s(topNode j, aNode j bb) ∉ used' := fun bb =>
        hkeep hlt (fun _ h => by have := (normalBranchEdges_idx.1 h).1; omega)
          (not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide) ∘ (Sym2.eq_swap ▸ ·))
          (fun _ h => by
            rcases h with h | h | h
            · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
              · exact pair_ne_of_ne (by decide) hb
              · exact pair_ne_of_ne (by decide) ha
            · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
              · simp only [topNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; omega
              · exact pair_ne_of_ne (by decide) ha
            · exact sym2_ne_of_tag (by decide) (by decide) h)
          (fun _ _ => ⟨(sym2_ne_of_tag (by decide) (by decide)).symm,
            (sym2_ne_of_tag (by decide) (by decide)).symm⟩)
      have hnaw : ∀ bb : Bool, s(aNode j bb, wNode j bb) ∉ used →
          s(aNode j bb, wNode j bb) ∉ used' := fun bb =>
        hkeep hlt (fun _ h => by have := (normalBranchEdges_idx.2.1 h).1; omega)
          (not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide))
          (fun _ h => by
            rcases h with h | h | h
            · exact sym2_ne_of_tags (by decide) h
            · exact sym2_ne_of_tags (by decide) h
            · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
              · simp only [aNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; omega
              · exact pair_ne_of_ne (by decide) ha)
          (fun _ _ => ⟨(sym2_ne_of_tag (by decide) (by decide)).symm,
            (sym2_ne_of_tag (by decide) (by decide)).symm⟩)
      have hnwc : ∀ bb : Bool, s(wNode j bb, cNode j bb) ∉ used →
          s(wNode j bb, cNode j bb) ∉ used' := fun bb =>
        hkeep hlt (fun _ h => by have := (normalBranchEdges_idx.2.2.2.1 h).1; omega)
          (not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide))
          (fun _ h => by
            rcases h with h | h | h
            · exact (sym2_ne_of_tag (by decide) (by decide)).symm h
            · exact sym2_ne_of_tag (by decide) (by decide) h
            · exact (sym2_ne_of_tag (by decide) (by decide)).symm h)
          (fun _ _ => ⟨(sym2_ne_of_tag (by decide) (by decide)).symm,
            (sym2_ne_of_tag (by decide) (by decide)).symm⟩)
      have hncu : ∀ bb : Bool, s(cNode j bb, u1Node j bb 0) ∉ used →
          s(cNode j bb, u1Node j bb 0) ∉ used' := fun bb =>
        hkeep hlt (fun _ h => by have := (normalBranchEdges_idx.2.2.2.2.1 h).1; omega)
          (not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide))
          (fun _ h => by rcases h with h | h | h <;> exact sym2_ne_of_tag (by decide) (by decide) h)
          (fun _ _ => ⟨(sym2_ne_of_tag (by decide) (by decide)).symm,
            (sym2_ne_of_tag (by decide) (by decide)).symm⟩)
      exact ⟨hsub _ h1, hsub _ h2, hsub _ h3, hsub _ h4,
        h5.imp (fun ⟨a, b, c⟩ => ⟨hsub _ a, hsub _ b, hntw _ c⟩)
          (fun ⟨a, b, c⟩ => ⟨hsub _ a, hnta _ b, hnaw _ c⟩),
        hnta _ h6, hnaw _ h7, hntw _ h8.1, hnwc _ h8.2.1, hncu _ h8.2.2⟩
    · have hjeq : j = z.length := by omega
      subst hjeq
      have hget : (z ++ [b])[z.length] = b := by simp
      simp only [hget]
      exact ⟨hev_ok, hodd_ok, hconn, hbot, hseg⟩
  · rcases hnew e he with h | h
    · obtain ⟨j, hj, hm⟩ := hV.2 e h
      have hlt : j < (z ++ [b]).length := by simp; omega
      have hget : (z ++ [b])[j] = z[j] := List.getElem_append_left hj
      exact ⟨j, hlt, by simpa only [hget] using hm⟩
    · exact ⟨z.length, by simp, by simp [h]⟩


end UndirectedEdgeGeography

end Cslib.Complexity
