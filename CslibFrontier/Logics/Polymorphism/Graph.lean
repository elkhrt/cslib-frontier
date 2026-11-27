/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.ZMod.Defs
public import CslibFrontier.Logics.Polymorphism.GraphCore
public import CslibFrontier.Logics.Polymorphism.Partial

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Graph Polymorphisms, Projectivity, Świerczkowski's Lemma, and Rosenberg's Theorem

This module develops the structural theory of finite simple graph polymorphisms on top of
`CslibFrontier.Logics.Polymorphism.Partial`: projectivity, semiprojections,
Świerczkowski's lemma, the minimum-degree bound for semiprojections on core graphs, projectivity
of cliques $K_k$ ($k \ge 3$), and Rosenberg's classification of minimal clones condensed for
simple graphs.

## Main definitions

* `Cslib.Logic.SimpleGraph.edgeRel`: the binary edge relation of a simple graph.
* `Cslib.Logic.SimpleGraph.IsIdempotent`, `Cslib.Logic.SimpleGraph.IsProjection`,
  `Cslib.Logic.SimpleGraph.IsProjective`: idempotent operations, projections, and projective graphs.
* `Cslib.Logic.SimpleGraph.IsSemiprojectionOn`, `Cslib.Logic.SimpleGraph.IsSemiprojection`,
  `Cslib.Logic.SimpleGraph.IsMajority`, `Cslib.Logic.SimpleGraph.IsAffineF2`: the three operation
  types in Rosenberg's graph theorem.

## Main results

* `Cslib.Logic.SimpleGraph.swierczkowski_lemma`: Świerczkowski's lemma for arities $m \ge 4$.
* `Cslib.Logic.SimpleGraph.no_semiprojection_of_minDegree`: a finite core graph with minimum degree
  $\delta > 0$ has no $m$-ary semiprojection whenever $1 + (m - 1)\delta > |V|$.
* `Cslib.Logic.SimpleGraph.isProjective_top`: cliques $K_k$ ($k \ge 3$) are projective.
* `Cslib.Logic.SimpleGraph.exists_rosenberg_polymorphism_of_not_isProjective`: Rosenberg's
  classification condensed for finite simple graphs.
* `Cslib.Logic.SimpleGraph.isProjective_of_isHomCore_of_no_semiprojection`: every finite core graph
  on at least $3$ vertices with no semiprojection is projective.
-/

public section

namespace Cslib.Logic.SimpleGraph

open Cslib.Logic

variable {V : Type*}

/-- The binary edge relation of a simple graph `G`. -/
@[expose] def edgeRel (G : _root_.SimpleGraph V) : Set (Fin 2 → V) :=
  {t | G.Adj (t 0) (t 1)}

/-- Membership in `edgeRel G` is adjacency in `G`. -/
theorem mem_edgeRel_iff (G : _root_.SimpleGraph V) (t : Fin 2 → V) :
    t ∈ edgeRel G ↔ G.Adj (t 0) (t 1) :=
  Iff.rfl

/-- Coordinatewise preservation of `edgeRel G` written directly in terms of `G.Adj`. -/
theorem isPolymorphism_edgeRel_iff {J : Type*} (G : _root_.SimpleGraph V) (f : (J → V) → V) :
    Cslib.Logic.IsPolymorphism f (edgeRel G) ↔
      ∀ a b : J → V, (∀ j, G.Adj (a j) (b j)) → G.Adj (f a) (f b) := by
  constructor
  · intro hf a b hab
    let M : J → Fin 2 → V := fun j => ![a j, b j]
    have hM : ∀ j, M j ∈ edgeRel G := fun j => hab j
    simpa [M, mem_edgeRel_iff] using hf M hM
  · intro hf M hM
    exact hf (fun j => M j 0) (fun j => M j 1) hM

/-- An operation `f : (J → V) → V` is idempotent if `f (x, ..., x) = x` for every `x`. -/
@[expose] def IsIdempotent {J : Type*} (f : (J → V) → V) : Prop :=
  ∀ x : V, f (fun _ => x) = x

/-- An operation `f : (J → V) → V` is a projection if `f = π_j` for some coordinate `j`. -/
@[expose] def IsProjection {J : Type*} (f : (J → V) → V) : Prop :=
  ∃ j : J, ∀ a : J → V, f a = a j

/-- A simple graph `G` is *projective* if every positive-arity idempotent polymorphism of `G` is a
projection. -/
@[expose] def IsProjective (G : _root_.SimpleGraph V) : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (f : (Fin m → V) → V),
    Cslib.Logic.IsPolymorphism f (edgeRel G) → IsIdempotent f → IsProjection f

/-- `f` is a semiprojection on coordinate `i` if `f` is not a projection and `f a = a i` whenever
`a` has a repeated entry. -/
@[expose] def IsSemiprojectionOn {m : ℕ} (f : (Fin m → V) → V) (i : Fin m) : Prop :=
  ¬ IsProjection f ∧ ∀ a : Fin m → V, ¬ Function.Injective a → f a = a i

/-- `f` is a semiprojection of arity `m ≥ 2`. -/
@[expose] def IsSemiprojection {m : ℕ} (f : (Fin m → V) → V) : Prop :=
  2 ≤ m ∧ ∃ i : Fin m, IsSemiprojectionOn f i

/-- `f : (Fin 3 → V) → V` is a ternary majority operation. -/
@[expose] def IsMajority (f : (Fin 3 → V) → V) : Prop :=
  ∀ x y : V, f ![x, x, y] = x ∧ f ![x, y, x] = x ∧ f ![y, x, x] = x

/-- `f : (Fin 3 → V) → V` is the affine operation `x + y + z` of an $\mathbb{F}_2$-vector space on
`V`. -/
@[expose] def IsAffineF2 (f : (Fin 3 → V) → V) : Prop :=
  ∃ (_ : AddCommGroup V) (_ : Module (ZMod 2) V), ∀ x y z : V, f ![x, y, z] = x + y + z

/-- Every positive-arity polymorphism of a projective core is essentially at most unary
(`σ ∘ π_i` for a graph automorphism `σ`). -/
theorem isPolymorphism_eq_comp_proj_of_isProjective_of_isHomCore
    {G : _root_.SimpleGraph V} (hproj : IsProjective G) (hcore : IsHomCore G)
    {m : ℕ} (hm : 0 < m) {f : (Fin m → V) → V}
    (hf : Cslib.Logic.IsPolymorphism f (edgeRel G)) :
    ∃ (σ : G ≃g G) (i : Fin m), ∀ a : Fin m → V, f a = σ (a i) := by
  let u : G →g G :=
    ⟨fun x => f (fun _ => x), fun {x y} hxy =>
      (isPolymorphism_edgeRel_iff G f).mp hf (fun _ => x) (fun _ => y) (fun _ => hxy)⟩
  obtain ⟨σ, hσ⟩ := hcore u
  let g : (Fin m → V) → V := fun a => σ.symm (f a)
  have hg_poly : Cslib.Logic.IsPolymorphism g (edgeRel G) := by
    rw [isPolymorphism_edgeRel_iff]
    intro a b hab
    exact σ.symm.map_adj_iff.mpr ((isPolymorphism_edgeRel_iff G f).mp hf a b hab)
  have hg_idem : IsIdempotent g := by
    intro x
    have hx : f (fun _ => x) = σ x := hσ x
    dsimp [g]
    rw [hx, σ.symm_apply_apply]
  obtain ⟨i, hi⟩ := hproj m hm g hg_poly hg_idem
  refine ⟨σ, i, fun a => ?_⟩
  have := hi a
  dsimp [g] at this
  exact σ.symm_apply_eq.mp this

/-! ### Odd walks, odd-walk powers, and refutations of majority and Maltsev polymorphisms -/

/-- The `k`-walk relation of `G`: vertices joined by a walk of length `k`. -/
private def walkRel (G : _root_.SimpleGraph V) (k : ℕ) (u v : V) : Prop :=
  Nonempty (G.Walk u v) ∧ ∃ p : G.Walk u v, p.length = k

/-- Any polymorphism of `G` preserves `walkRel G k`. -/
private theorem isPolymorphism_walkRel {J : Type*} {G : _root_.SimpleGraph V}
    {f : (J → V) → V} (hf : Cslib.Logic.IsPolymorphism f (edgeRel G)) :
    ∀ (k : ℕ) (a b : J → V), (∀ j, ∃ p : G.Walk (a j) (b j), p.length = k) →
      ∃ p : G.Walk (f a) (f b), p.length = k := by
  intro k
  induction k with
  | zero =>
    intro a b hab
    have hEq : a = b := by
      funext j
      rcases hab j with ⟨p, hp⟩
      exact _root_.SimpleGraph.Walk.eq_of_length_eq_zero hp
    subst hEq
    exact ⟨.nil, rfl⟩
  | succ k ih =>
    intro a b hab
    have hstep : ∀ j, ∃ c : V, G.Adj (a j) c ∧ ∃ q : G.Walk c (b j), q.length = k := by
      intro j
      rcases hab j with ⟨p, hp⟩
      generalize ha : a j = x at p
      generalize hb : b j = y at p
      cases p with
      | nil => simp at hp
      | @cons _ w _ hadj q =>
        refine ⟨w, ha ▸ hadj, hb ▸ q, ?_⟩
        cases hb
        simpa using hp
    choose c hc hq using hstep
    obtain ⟨q', hq'⟩ := ih c b hq
    have hadj' : G.Adj (f a) (f c) := (isPolymorphism_edgeRel_iff G f).mp hf a c hc
    exact ⟨.cons hadj' q', by simp [hq']⟩

/-- The `k`-walk simple graph (loopless whenever `G` has no closed walk of length `k`). -/
private def walkGraph (G : _root_.SimpleGraph V) (k : ℕ)
    (hloopless : ∀ v : V, ∀ p : G.Walk v v, p.length ≠ k) : _root_.SimpleGraph V where
  Adj u v := ∃ p : G.Walk u v, p.length = k
  symm := ⟨fun _ _ ⟨p, hp⟩ => ⟨p.reverse, by simpa using hp⟩⟩
  loopless := ⟨fun v ⟨p, hp⟩ => hloopless v p hp⟩

/-- Every polymorphism of `G` is a polymorphism of `walkGraph G k`. -/
private theorem isPolymorphism_walkGraph {J : Type*} {G : _root_.SimpleGraph V}
    {f : (J → V) → V} (hf : Cslib.Logic.IsPolymorphism f (edgeRel G))
    (k : ℕ) (hloopless : ∀ v : V, ∀ p : G.Walk v v, p.length ≠ k) :
    Cslib.Logic.IsPolymorphism f (edgeRel (walkGraph G k hloopless)) := by
  rw [isPolymorphism_edgeRel_iff]
  intro a b hab
  exact isPolymorphism_walkRel hf k a b hab

/-- A non-bipartite graph contains an odd closed walk. -/
private theorem exists_odd_closedWalk_of_not_isBipartite {G : _root_.SimpleGraph V}
    (hnb : ¬ G.IsBipartite) : ∃ (v : V) (p : G.Walk v v), Odd p.length := by
  classical
  by_contra hno
  push Not at hno
  have heven : ∀ {u : V} (p : G.Walk u u), Even p.length := fun p => hno _ p
  -- Pick a base vertex in each connected component and color by walk-length parity.
  let base (C : G.ConnectedComponent) : V := C.exists_rep.choose
  have hbase (C : G.ConnectedComponent) : G.connectedComponentMk (base C) = C :=
    C.exists_rep.choose_spec
  have hreach (v : V) : G.Reachable (base (G.connectedComponentMk v)) v :=
    _root_.SimpleGraph.ConnectedComponent.exact (hbase (G.connectedComponentMk v))
  let col : V → Fin 2 := fun v =>
    ⟨(hreach v).some.length % 2, Nat.mod_lt _ (by decide)⟩
  apply hnb
  refine ⟨_root_.SimpleGraph.Coloring.mk col fun {u v} huv => ?_⟩
  have hcomp : G.connectedComponentMk u = G.connectedComponentMk v :=
    _root_.SimpleGraph.ConnectedComponent.eq.mpr huv.reachable
  let b := base (G.connectedComponentMk u)
  let pu : G.Walk b u := (hreach u).some
  have hv_eq : base (G.connectedComponentMk v) = b := congrArg base hcomp.symm
  let pv : G.Walk b v := hv_eq ▸ (hreach v).some
  have hclosed :
      Even (pu.append ((_root_.SimpleGraph.Walk.cons huv .nil).append pv.reverse)).length :=
    heven _
  have hlen : (pu.append ((_root_.SimpleGraph.Walk.cons huv .nil).append pv.reverse)).length =
      pu.length + 1 + pv.length := by
    simp only [_root_.SimpleGraph.Walk.length_append, _root_.SimpleGraph.Walk.length_cons,
      _root_.SimpleGraph.Walk.length_nil, _root_.SimpleGraph.Walk.length_reverse]
    omega
  rw [hlen] at hclosed
  have hcol_u : (col u).val = pu.length % 2 := rfl
  have hcol_v : (col v).val = pv.length % 2 := by
    have hlen_pv : ∀ {x : V} (h : x = b) (w : G.Walk x v), (h ▸ w).length = w.length := by
      rintro _ rfl _
      rfl
    change ((hreach v).some.length % 2) = pv.length % 2
    rw [show pv.length = (hreach v).some.length from hlen_pv hv_eq (hreach v).some]
  intro hEq
  have hval : pu.length % 2 = pv.length % 2 := by
    rw [← hcol_u, ← hcol_v, hEq]
  rcases hclosed with ⟨t, ht⟩
  omega

/-- A finite graph with a ternary majority polymorphism cannot contain a triangle. -/
private theorem not_isMajority_of_triangle [Finite V] {G : _root_.SimpleGraph V}
    {f : (Fin 3 → V) → V} (hf : Cslib.Logic.IsPolymorphism f (edgeRel G))
    (hmaj : IsMajority f) {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (hwu : G.Adj w u) :
    False := by
  have : Fintype V := Fintype.ofFinite V
  classical
  have hgrow : ∀ (S : Finset V), 3 ≤ S.card → (S : Set V).Pairwise G.Adj →
      ∃ z : V, z ∉ S ∧ ∀ s ∈ S, G.Adj s z := by
    intro S hScard hScliq
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hScard
    obtain ⟨a, b, c, hab, hac, hbc, hTeq⟩ := Finset.card_eq_three.mp hTcard
    have haS : a ∈ S := hTS (by simp [hTeq])
    have hbS : b ∈ S := hTS (by simp [hTeq])
    have hcS : c ∈ S := hTS (by simp [hTeq])
    let z := f ![a, b, c]
    have hadj : ∀ s ∈ S, G.Adj s z := by
      intro s hs
      by_cases hsa : s = a
      · have h1 := (isPolymorphism_edgeRel_iff G f).mp hf ![b, a, a] ![a, b, c] (by
          intro j; fin_cases j
          · exact hScliq hbS haS hab.symm
          · exact hScliq haS hbS hab
          · exact hScliq haS hcS hac)
        rw [hsa]
        simpa [z, (hmaj a b).2.2] using h1
      · by_cases hsb : s = b
        · have h1 := (isPolymorphism_edgeRel_iff G f).mp hf ![b, a, b] ![a, b, c] (by
            intro j; fin_cases j
            · exact hScliq hbS haS hab.symm
            · exact hScliq haS hbS hab
            · exact hScliq hbS hcS hbc)
          rw [hsb]
          simpa [z, (hmaj b a).2.1] using h1
        · by_cases hsc : s = c
          · have h1 := (isPolymorphism_edgeRel_iff G f).mp hf ![c, c, b] ![a, b, c] (by
              intro j; fin_cases j
              · exact hScliq hcS haS hac.symm
              · exact hScliq hcS hbS hbc.symm
              · exact hScliq hbS hcS hbc)
            rw [hsc]
            simpa [z, (hmaj c b).1] using h1
          · have h1 := (isPolymorphism_edgeRel_iff G f).mp hf ![s, s, s] ![a, b, c] (by
              intro j; fin_cases j
              · exact hScliq hs haS hsa
              · exact hScliq hs hbS hsb
              · exact hScliq hs hcS hsc)
            simpa [z, (hmaj s s).1] using h1
    refine ⟨z, fun hz => G.loopless.irrefl z (hadj z hz), hadj⟩
  have hcl : ∀ r : ℕ, 3 ≤ r → ∃ S : Finset V, S.card = r ∧ (S : Set V).Pairwise G.Adj := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base =>
      refine ⟨{u, v, w}, ?_, ?_⟩
      · rw [Finset.card_eq_three]
        exact ⟨u, v, w, huv.ne, hwu.ne.symm, hvw.ne, rfl⟩
      · intro x hx y hy hxy
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        · exact (hxy rfl).elim
        · exact huv
        · exact hwu.symm
        · exact huv.symm
        · exact (hxy rfl).elim
        · exact hvw
        · exact hwu
        · exact hvw.symm
        · exact (hxy rfl).elim
    | succ r hr ih =>
      rcases ih with ⟨S, hScard, hScliq⟩
      obtain ⟨z, hz, hadj⟩ := hgrow S (hScard.symm ▸ hr) hScliq
      refine ⟨insert z S, by rw [Finset.card_insert_of_notMem hz, hScard], ?_⟩
      intro x hx y hy hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact (hxy rfl).elim
      · exact (hadj y hy).symm
      · exact hadj x hx
      · exact hScliq hx hy hxy
  obtain ⟨S, hScard, _⟩ := hcl (Fintype.card V + 1) (by
    have h3 : 3 ≤ Fintype.card V := by
      have hcard : ({u, v, w} : Finset V).card = 3 := by
        rw [Finset.card_eq_three]
        exact ⟨u, v, w, huv.ne, hwu.ne.symm, hvw.ne, rfl⟩
      exact hcard ▸ Finset.card_le_univ _
    omega)
  have := Finset.card_le_univ S
  omega

/-- A finite non-bipartite simple graph admits no ternary majority polymorphism. -/
theorem not_isMajority_of_not_isBipartite [Finite V] {G : _root_.SimpleGraph V}
    (hnb : ¬ G.IsBipartite) {f : (Fin 3 → V) → V}
    (hf : Cslib.Logic.IsPolymorphism f (edgeRel G)) : ¬ IsMajority f := by
  intro hmaj
  have haux : ∀ (k : ℕ) (H : _root_.SimpleGraph V), Odd k →
      Cslib.Logic.IsPolymorphism f (edgeRel H) →
      (∃ (v : V) (p : H.Walk v v), p.length = k) → False := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro H hkOdd hfH ⟨v, p, hp⟩
      by_cases htri : ∃ (a b c : V), H.Adj a b ∧ H.Adj b c ∧ H.Adj c a
      · rcases htri with ⟨a, b, c, hab, hbc, hca⟩
        exact not_isMajority_of_triangle hfH hmaj hab hbc hca
      · have hno3 : ∀ u : V, ∀ q : H.Walk u u, q.length ≠ 3 := by
          intro u q hq
          rcases q with _ | ⟨hab, q1⟩
          · simp at hq
          · rcases q1 with _ | ⟨hbc, q2⟩
            · simp at hq
            · rcases q2 with _ | ⟨hca, q3⟩
              · simp at hq
              · have hq3 : q3.length = 0 := by simpa using hq
                have hEq := _root_.SimpleGraph.Walk.eq_of_length_eq_zero hq3
                subst hEq
                exact htri ⟨_, _, _, hab, hbc, hca⟩
        have hk5 : 5 ≤ k := by
          rcases hkOdd with ⟨t, rfl⟩
          have h1 : t ≠ 0 := by
            rintro rfl
            rcases p with _ | ⟨hab, q⟩
            · simp at hp
            · have hq : q.length = 0 := by simpa using hp
              have hEq := _root_.SimpleGraph.Walk.eq_of_length_eq_zero hq
              subst hEq
              exact H.loopless.irrefl _ hab
          have h2 : t ≠ 1 := by
            rintro rfl
            exact hno3 v p hp
          omega
        -- Take `H' = walkGraph H 3`: loopless, preserves `f`, and shortens `p` by 2.
        let H' := walkGraph H 3 hno3
        have hfH' : Cslib.Logic.IsPolymorphism f (edgeRel H') :=
          isPolymorphism_walkGraph hfH 3 hno3
        have hstep : ∀ {x y : V} (q : H.Walk x y) (m : ℕ), q.length = m + 3 →
            ∃ (z : V) (q' : H.Walk z y), H'.Adj x z ∧ q'.length = m := by
          intro x y q m hq
          rcases q with _ | ⟨h1, q1⟩
          · simp at hq
          · rcases q1 with _ | ⟨h2, q2⟩
            · simp at hq
            · rcases q2 with _ | ⟨h3, q3⟩
              · simp at hq
              · refine ⟨_, q3, ⟨.cons h1 (.cons h2 (.cons h3 .nil)), rfl⟩, by simpa using hq⟩
        have hlift : ∀ {x y : V} (q : H.Walk x y) (r : ℕ), q.length = r →
            ∃ q' : H'.Walk x y, q'.length = r := by
          intro x y q
          induction q with
          | nil => exact fun r hr => ⟨.nil, hr⟩
          | @cons a b c hab q ihq =>
            have hab' : H'.Adj a b := ⟨.cons hab (.cons hab.symm (.cons hab .nil)), rfl⟩
            intro r hr
            cases r with
            | zero => simp at hr
            | succ r =>
              obtain ⟨q', hq'⟩ := ihq r (by simpa using hr)
              exact ⟨.cons hab' q', by simp [hq']⟩
        obtain ⟨z, q, hxz, hq⟩ := hstep p (k - 3) (by omega)
        obtain ⟨q', hq'⟩ := hlift q (k - 3) hq
        let hp' : H'.Walk v v := .cons hxz q'
        have hlen' : hp'.length = k - 2 := by
          simp only [hp', _root_.SimpleGraph.Walk.length_cons, hq']
          omega
        have hk2_odd : Odd (k - 2) := by
          rcases hkOdd with ⟨t, rfl⟩
          exact ⟨t - 1, by omega⟩
        exact ih (k - 2) (by omega) H' hk2_odd hfH' ⟨v, hp', hlen'⟩
  obtain ⟨v, p, hp⟩ := exists_odd_closedWalk_of_not_isBipartite hnb
  exact haux p.length G hp hf ⟨v, p, rfl⟩

/-- A finite non-bipartite simple graph admits no Maltsev-like polymorphism `f(x,x,y) = y` and
`f(y,x,x) = y`. -/
private theorem not_maltsev_of_not_isBipartite {G : _root_.SimpleGraph V}
    (hnb : ¬ G.IsBipartite) {f : (Fin 3 → V) → V}
    (hf : Cslib.Logic.IsPolymorphism f (edgeRel G))
    (hL : ∀ x y : V, f ![x, x, y] = y) (hR : ∀ x y : V, f ![y, x, x] = y) : False := by
  have haux : ∀ (k : ℕ), Odd k → (∃ (v : V) (p : G.Walk v v), p.length = k) → False := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hkOdd ⟨v, p, hp⟩
      rcases p with _ | ⟨h01, p1⟩
      · rcases hkOdd with ⟨t, ht⟩; simp at hp; omega
      · rcases p1 with _ | ⟨h12, p2⟩
        · exact G.loopless.irrefl v h01
        · rcases p2 with _ | ⟨h23, p3⟩
          · rcases hkOdd with ⟨t, ht⟩; simp at hp; omega
          · -- `k ≥ 3`: apply Maltsev to `(c0, c1), (c2, c1), (c2, c3)` to get `c0 ~ c3`!
            rename_i c1 c2 c3
            have h03 : G.Adj v c3 := by
              have hadj := (isPolymorphism_edgeRel_iff G f).mp hf ![v, c2, c2] ![c1, c1, c3]
                (fun j => match j with | 0 => h01 | 1 => h12.symm | 2 => h23)
              simpa [hR, hL] using hadj
            cases hk3 : p3.length with
            | zero =>
              have hEq := _root_.SimpleGraph.Walk.eq_of_length_eq_zero hk3
              subst hEq
              exact G.loopless.irrefl _ h03
            | succ r =>
              let hp' : G.Walk v v := .cons h03 p3
              have hk_ge3 : 3 ≤ k := by
                simp only [_root_.SimpleGraph.Walk.length_cons] at hp
                omega
              have hlen' : hp'.length = k - 2 := by
                simp only [hp', _root_.SimpleGraph.Walk.length_cons] at hp ⊢
                omega
              have hk2_odd : Odd (k - 2) := by
                rcases hkOdd with ⟨t, ht⟩
                exact ⟨t - 1, by omega⟩
              exact ih (k - 2) (by omega) hk2_odd ⟨v, hp', hlen'⟩
  obtain ⟨v, p, hp⟩ := exists_odd_closedWalk_of_not_isBipartite hnb
  exact haux p.length hp ⟨v, p, rfl⟩

/-! ### Świerczkowski's Lemma and the minimum-degree semiprojection bound -/

/-- Identify coordinates `i` and `j` of an `m`-ary operation (`i ≠ j`), yielding an `m`-ary
operation whose `i`-th coordinate is ignored (used to pass to `Fin (m - 1)`). -/
private theorem isPolymorphism_comp_reindex {m k : ℕ} {G : _root_.SimpleGraph V}
    {f : (Fin m → V) → V} (hf : Cslib.Logic.IsPolymorphism f (edgeRel G))
    (φ : Fin m → Fin k) :
    Cslib.Logic.IsPolymorphism (fun a : Fin k → V => f (a ∘ φ)) (edgeRel G) := by
  rw [isPolymorphism_edgeRel_iff] at hf ⊢
  intro a b hab
  exact hf (a ∘ φ) (b ∘ φ) (fun j => hab (φ j))

/-- **Świerczkowski's Lemma**: for `m ≥ 4`, if an idempotent operation `f : (Fin m → V) → V`
collapses to a projection whenever any two coordinates are identified, then there exists a single
coordinate `i : Fin m` such that `f a = a i` for every non-injective tuple `a`. -/
theorem swierczkowski_lemma {m : ℕ} (hm : 4 ≤ m) (f : (Fin m → V) → V)
    (hcollapse : ∀ (i j : Fin m), i ≠ j →
      ∃ k : Fin m, ∀ a : Fin m → V, a i = a j → f a = a k) :
    ∃ i : Fin m, ∀ a : Fin m → V, ¬ Function.Injective a → f a = a i := by
  classical
  -- For `|V| ≤ 1`, every operation is a projection.
  by_cases hsub : Subsingleton V
  · exact ⟨⟨0, by omega⟩, fun a _ => Subsingleton.elim _ _⟩
  have htwo : ∃ u v : V, u ≠ v := by
    by_contra h
    push Not at h
    exact hsub ⟨fun a b => h a b⟩
  obtain ⟨u, v, huv⟩ := htwo
  -- For each unordered pair `i ≠ j`, define a canonical witness coordinate `k(i, j)` such that
  -- `a i = a j → f a = a (k i j)`. Note that if `k i j = i` or `j`, both give the same value!
  have hpick : ∀ i j : Fin m, i ≠ j →
      ∃ k : Fin m, (k ≠ j) ∧ ∀ a : Fin m → V, a i = a j → f a = a k := by
    intro i j hij
    obtain ⟨k, hk⟩ := hcollapse i j hij
    by_cases hkj : k = j
    · refine ⟨i, hij, fun a ha => (hk a ha).trans (by rw [hkj, ha])⟩
    · exact ⟨k, hkj, hk⟩
  -- Pick two distinct indices `0, 1` and see what `f` projects onto when `a 0 = a 1`.
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  let i2 : Fin m := ⟨2, by omega⟩
  let i3 : Fin m := ⟨3, by omega⟩
  have h01 : i0 ≠ i1 := Fin.ne_of_val_ne (by dsimp [i0, i1]; omega)
  -- Test on indicator tuples `ind r x = if x = r then v else u`.
  let ind (r : Fin m) : Fin m → V := fun x => if x = r then v else u
  by_cases hex : ∃ r : Fin m, f (ind r) = v
  · obtain ⟨r, hr⟩ := hex
    refine ⟨r, fun a ha => ?_⟩
    have hpair : ∃ p q : Fin m, p ≠ q ∧ a p = a q := by
      by_contra h
      push Not at h
      exact ha (fun p q hpq => by by_contra hne; exact h p q hne hpq)
    obtain ⟨p, q, hpq, hapq⟩ := hpair
    by_cases hrp : r = p
    · subst hrp
      obtain ⟨k, hkq, hk⟩ := hpick r q hpq
      by_cases hkr : k = r
      · rw [hk a hapq, hkr]
      · have hex_s : ∃ s : Fin m, s ≠ r ∧ s ≠ q ∧ s ≠ k := by
          by_contra hno
          push Not at hno
          have hsub' : (Finset.univ : Finset (Fin m)) ⊆ {r, q, k} := by
            intro x _
            by_cases h1 : x = r
            · simp [h1]
            · by_cases h2 : x = q
              · simp [h2]
              · simp [hno x h1 h2]
          have hle := Finset.card_le_card hsub'
          have h3 : ({r, q, k} : Finset (Fin m)).card ≤ 3 :=
            (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_le_two) 1)
          simp only [Finset.card_univ, Fintype.card_fin] at hle
          omega
        obtain ⟨s, hsr, hsq, hsk⟩ := hex_s
        let b' : Fin m → V := fun x => if x = r ∨ x = q then v else u
        have h1 : f b' = u := by
          have := hk b' (by simp [b'])
          simpa [b', hkr, hkq] using this
        obtain ⟨k', _, hk'⟩ := hpick k s (Ne.symm hsk)
        have hk'_eq : k' = r := by
          have h_ind : f (ind r) = (ind r) k' := hk' (ind r) (by simp [ind, hkr, hsr])
          rw [hr] at h_ind
          by_contra hne
          simp only [ind, hne, ↓reduceIte] at h_ind
          exact huv h_ind.symm
        have h2 : f b' = v := by
          have := hk' b' (by simp [b', hkr, hkq, hsr, hsq])
          simpa [b', hk'_eq] using this
        exact absurd (h1.symm.trans h2) huv
    · by_cases hrq : r = q
      · subst hrq
        obtain ⟨k, hkp, hk⟩ := hpick r p hpq.symm
        by_cases hkr : k = r
        · rw [hk a hapq.symm, hkr]
        · have hex_s : ∃ s : Fin m, s ≠ r ∧ s ≠ p ∧ s ≠ k := by
            by_contra hno
            push Not at hno
            have hsub' : (Finset.univ : Finset (Fin m)) ⊆ {r, p, k} := by
              intro x _
              by_cases h1 : x = r
              · simp [h1]
              · by_cases h2 : x = p
                · simp [h2]
                · simp [hno x h1 h2]
            have hle := Finset.card_le_card hsub'
            have h3 : ({r, p, k} : Finset (Fin m)).card ≤ 3 :=
              (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_le_two) 1)
            simp only [Finset.card_univ, Fintype.card_fin] at hle
            omega
          obtain ⟨s, hsr, hsp, hsk⟩ := hex_s
          let b' : Fin m → V := fun x => if x = r ∨ x = p then v else u
          have h1 : f b' = u := by
            have := hk b' (by simp [b'])
            simpa [b', hkr, hkp] using this
          obtain ⟨k', _, hk'⟩ := hpick k s (Ne.symm hsk)
          have hk'_eq : k' = r := by
            have h_ind : f (ind r) = (ind r) k' := hk' (ind r) (by simp [ind, hkr, hsr])
            rw [hr] at h_ind
            by_contra hne
            simp only [ind, hne, ↓reduceIte] at h_ind
            exact huv h_ind.symm
          have h2 : f b' = v := by
            have := hk' b' (by simp [b', hkr, hkp, hsr, hsp])
            simpa [b', hk'_eq] using this
          exact absurd (h1.symm.trans h2) huv
      · obtain ⟨k, _, hk⟩ := hpick p q hpq
        have hk_eq : k = r := by
          have h_ind : f (ind r) = (ind r) k := hk (ind r) (by simp [ind, Ne.symm hrp, Ne.symm hrq])
          rw [hr] at h_ind
          by_contra hne
          simp only [ind, hne, ↓reduceIte] at h_ind
          exact huv h_ind.symm
        rw [hk a hapq, hk_eq]
  · -- Case B: `∀ r, f (ind r) = u`, giving a contradiction on `{i0, i1}` vs `{i2, i3}`.
    push Not at hex
    have hmem : ∀ p q : Fin m, p ≠ q →
        ∃ k : Fin m, (k = p ∨ k = q) ∧ ∀ a : Fin m → V, a p = a q → f a = a k := by
      intro p q hpq
      obtain ⟨k, hk⟩ := hcollapse p q hpq
      refine ⟨k, ?_, hk⟩
      by_contra hnot
      push Not at hnot
      have h_ind : f (ind k) = (ind k) k :=
        hk (ind k) (by simp [ind, Ne.symm hnot.1, Ne.symm hnot.2])
      simp only [ind, ite_true] at h_ind
      exact hex k h_ind
    obtain ⟨k1, hk1, hf1⟩ := hmem i0 i1 h01
    have h23 : i2 ≠ i3 := Fin.ne_of_val_ne (by dsimp [i2, i3]; omega)
    obtain ⟨k2, hk2, hf2⟩ := hmem i2 i3 h23
    let b : Fin m → V := fun x => if x = i0 ∨ x = i1 then u else v
    have hb1 : f b = u := by
      rw [hf1 b (by simp [b])]
      rcases hk1 with rfl | rfl <;> simp [b]
    have hb2 : f b = v := by
      have h20 : i2 ≠ i0 := Fin.ne_of_val_ne (by dsimp [i2, i0]; omega)
      have h21 : i2 ≠ i1 := Fin.ne_of_val_ne (by dsimp [i2, i1]; omega)
      have h30 : i3 ≠ i0 := Fin.ne_of_val_ne (by dsimp [i3, i0]; omega)
      have h31 : i3 ≠ i1 := Fin.ne_of_val_ne (by dsimp [i3, i1]; omega)
      rw [hf2 b (by simp [b, h20, h21, h30, h31])]
      rcases hk2 with rfl | rfl <;> simp [b, h20, h21, h30, h31]
    exact absurd (hb1.symm.trans hb2) huv

/-- In a finite core graph, distinct vertices cannot have nested open neighborhoods. -/
theorem not_neighborSet_subset_of_isHomCore [Finite V] {G : _root_.SimpleGraph V}
    (hcore : IsHomCore G) {u v : V} (huv : u ≠ v) : ¬ (G.neighborSet u ⊆ G.neighborSet v) := by
  classical
  intro hsub
  let h : G →g G :=
    { toFun := fun x => if x = u then v else x
      map_rel' := by
        intro x y hxy
        by_cases hxu : x = u
        · subst hxu
          have hyx : y ≠ x := hxy.ne.symm
          simp only [ite_true, hyx, ite_false]
          exact hsub hxy
        · by_cases hyu : y = u
          · subst hyu
            simp only [hxu, ite_false, ite_true]
            exact (hsub hxy.symm).symm
          · simp only [hxu, hyu, ite_false]
            exact hxy }
  have hinj : Function.Injective h :=
    (isHomCore_iff_forall_injective.mp hcore) h
  have heq : h u = h v := by simp [h, huv.symm]
  exact huv (hinj heq)

/-- **Minimum-degree bound for semiprojections** (Lemma `lem:mindegree_semiprojections`):
a finite core graph `G` with minimum degree `δ` (`∀ v, δ ≤ G.degree v`) has no `m`-ary
semiprojection whenever `1 + (m - 1) * δ > Fintype.card V`. -/
theorem no_semiprojection_of_minDegree [Fintype V] {G : _root_.SimpleGraph V}
    [DecidableRel G.Adj] (hcore : IsHomCore G) {δ : ℕ} (hδ : ∀ v : V, δ ≤ G.degree v)
    {m : ℕ} (hbound : Fintype.card V < 1 + (m - 1) * δ)
    {f : (Fin m → V) → V} (hf : Cslib.Logic.IsPolymorphism f (edgeRel G)) :
    ¬ IsSemiprojection f := by
  classical
  rintro ⟨hm2, i0, hnotproj, hsemi⟩
  -- Since `f` is not a projection, there exists `a` with `f a ≠ a i0`.
  have hex : ∃ a : Fin m → V, f a ≠ a i0 := by
    by_contra h
    push Not at h
    exact hnotproj ⟨i0, h⟩
  obtain ⟨a, ha⟩ := hex
  -- Since `G` is a core, `N(a i0) ⊄ N(f a)`.
  have hnsub := not_neighborSet_subset_of_isHomCore hcore (Ne.symm ha)
  rw [Set.not_subset] at hnsub
  obtain ⟨x0, hx0_mem, hx0_not⟩ := hnsub
  -- Consider the `m` sets: `{x0}` (for `i0`) and `neighborFinset (a j)` (for `j ≠ i0`).
  let S : Fin m → Finset V := fun j => if j = i0 then {x0} else G.neighborFinset (a j)
  have hS_ne : ∀ j : Fin m, (S j).Nonempty := by
    intro j
    by_cases hj : j = i0
    · simp [S, hj]
    · simp only [S, hj, ite_false]
      have hpos : 0 < (G.neighborFinset (a j)).card := by
        rw [_root_.SimpleGraph.card_neighborFinset_eq_degree]
        have hδpos : 0 < δ := by
          by_contra h0
          have : δ = 0 := by omega
          subst this
          simp at hbound
          have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x0⟩
          omega
        exact lt_of_lt_of_le hδpos (hδ (a j))
      exact Finset.card_pos.mp hpos
  -- Show the sets `S j` cannot be pairwise disjoint by cardinality.
  have hnot_disj : ¬ Pairwise (fun j k => Disjoint (S j) (S k)) := by
    intro hdisj
    have hsum : ∑ j : Fin m, (S j).card = (Finset.univ.biUnion S).card := by
      rw [Finset.card_biUnion]
      intro j _ k _ hjk
      exact hdisj hjk
    have hle : (Finset.univ.biUnion S).card ≤ Fintype.card V := Finset.card_le_univ _
    have hge : 1 + (m - 1) * δ ≤ ∑ j : Fin m, (S j).card := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
      have h1 : (S i0).card = 1 := by simp [S]
      have hrest : (m - 1) * δ ≤ ∑ j ∈ Finset.univ.erase i0, (S j).card := by
        calc (m - 1) * δ
            = ∑ _j ∈ Finset.univ.erase i0, δ := by
                rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i0),
                  Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          _ ≤ ∑ j ∈ Finset.univ.erase i0, (S j).card := by
                refine Finset.sum_le_sum fun j hj => ?_
                have hne : j ≠ i0 := (Finset.mem_erase.mp hj).1
                simp only [S, hne, ite_false, _root_.SimpleGraph.card_neighborFinset_eq_degree]
                exact hδ (a j)
      omega
    omega
  -- Extract two distinct indices `j1 ≠ j2` and a common element `y ∈ S j1 ∩ S j2`.
  have hoverlap : ∃ j1 j2 : Fin m, j1 ≠ j2 ∧ ∃ y : V, y ∈ S j1 ∧ y ∈ S j2 := by
    by_contra h
    push Not at h
    apply hnot_disj
    intro j1 j2 hne
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    exact h j1 j2 hne y hy1 hy2
  obtain ⟨j1, j2, hj12, y, hy1, hy2⟩ := hoverlap
  -- Build a tuple `x : Fin m → V` with `x j ∈ S j` for all `j`, `x i0 = x0`, and `x j1 = x j2 = y`.
  let x : Fin m → V := fun j =>
    if j = j1 then y else if j = j2 then y else (hS_ne j).choose
  have hx_mem : ∀ j : Fin m, x j ∈ S j := by
    intro j
    dsimp [x]
    split_ifs with h1 h2
    · exact h1 ▸ hy1
    · exact h2 ▸ hy2
    · exact (hS_ne j).choose_spec
  have hx_i0 : x i0 = x0 := by
    have := hx_mem i0
    simpa [S] using this
  have hx_not_inj : ¬ Function.Injective x := by
    intro hinj
    have : x j1 = x j2 := by simp [x, hj12.symm]
    exact hj12 (hinj this)
  have hfx : f x = x0 := (hsemi x hx_not_inj).trans hx_i0
  have hadj_all : ∀ j : Fin m, G.Adj (a j) (x j) := by
    intro j
    have hm := hx_mem j
    by_cases hj : j = i0
    · subst hj
      rw [hx_i0]
      exact hx0_mem
    · simp only [S, hj, ite_false, _root_.SimpleGraph.mem_neighborFinset] at hm
      exact hm
  have hfax : G.Adj (f a) (f x) := (isPolymorphism_edgeRel_iff G f).mp hf a x hadj_all
  rw [hfx] at hfax
  exact hx0_not hfax

/-! ### Projectivity of cliques and Rosenberg's condensed graph theorem -/

/-- **Clique Projectivity** (`thm:CliqueProjective`): for `3 ≤ Fintype.card V`, the complete graph
`⊤ : SimpleGraph V` is projective. -/
theorem isProjective_top [Fintype V] (hcard : 3 ≤ Fintype.card V) :
    IsProjective (⊤ : _root_.SimpleGraph V) := by
  classical
  -- Strong induction on the arity `m`.
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro hm f hf hidem
    -- Wait: prove for `m = 1`, `m = 2`, `m = 3`, `m ≥ 4`.
    by_cases hm1 : m = 1
    · subst hm1
      refine ⟨0, fun a => ?_⟩
      have hEq : a = fun _ => a 0 := by funext i; fin_cases i; rfl
      rw [hEq, hidem (a 0)]
    · by_cases hm2 : m = 2
      · subst hm2
        -- First show `f ![x, y] ∈ {x, y}` for all `x, y`.
        have hxy : ∀ x y : V, f ![x, y] = x ∨ f ![x, y] = y := by
          intro x y
          by_contra hne
          push Not at hne
          -- Since `|V| ≥ 3`, pick `z` distinct from `x` and `y`? Wait: what if `x = y`?
          by_cases hxeq : x = y
          · subst hxeq
            have := hidem x
            have hEq : (![x, x] : Fin 2 → V) = fun _ => x := by funext i; fin_cases i <;> rfl
            rw [hEq] at hne
            exact hne.1 this
          · -- `x ≠ y`: since `f ![x, y] ≠ x` and `f ![x, y] ≠ y`,
            -- `(x, f![x,y])` and `(y, f![x,y])` are edges.
            -- Wait: apply `f` to `![x, y]` and `![f ![x,y], f ![x,y]]`!
            have hadj := (isPolymorphism_edgeRel_iff (⊤ : _root_.SimpleGraph V) f).mp hf
              ![x, y] (fun _ => f ![x, y]) (by
                intro j; fin_cases j
                · exact Ne.symm hne.1
                · exact Ne.symm hne.2)
            rw [hidem (f ![x, y])] at hadj
            exact hadj rfl
        -- Next show `f = π_0` or `f = π_1`.
        by_contra hnotproj
        have h0 : ∃ x y : V, f ![x, y] ≠ x := by
          by_contra h; push Not at h
          exact hnotproj ⟨0, fun a => by
            have hEq : a = ![a 0, a 1] := by funext i; fin_cases i <;> rfl
            rw [hEq]; exact h (a 0) (a 1)⟩
        have h1 : ∃ x y : V, f ![x, y] ≠ y := by
          by_contra h; push Not at h
          exact hnotproj ⟨1, fun a => by
            have hEq : a = ![a 0, a 1] := by funext i; fin_cases i <;> rfl
            rw [hEq]; exact h (a 0) (a 1)⟩
        obtain ⟨x1, y1, hne1⟩ := h0
        obtain ⟨x2, y2, hne2⟩ := h1
        have hfy1 : f ![x1, y1] = y1 := (hxy x1 y1).resolve_left hne1
        have hfx2 : f ![x2, y2] = x2 := (hxy x2 y2).resolve_right hne2
        have hx1y1 : x1 ≠ y1 := fun h => hne1 (h ▸ hfy1)
        have hx2y2 : x2 ≠ y2 := fun h => hne2 (h ▸ hfx2)
        -- Pick `z` distinct from `y1` and `x2` (since `|V| ≥ 3`).
        have hexz : ∃ z : V, z ≠ y1 ∧ z ≠ x2 := by
          by_contra h; push Not at h
          have hsub : (Finset.univ : Finset V) ⊆ {y1, x2} := by
            intro z _
            by_cases h1 : z = y1
            · simp [h1]
            · simp [h z h1]
          have := Finset.card_le_card hsub
          have h2 : ({y1, x2} : Finset V).card ≤ 2 := Finset.card_le_two
          simp only [Finset.card_univ] at this
          omega
        obtain ⟨z, hzy1, hzx2⟩ := hexz
        have hstep : ∀ a b : V, f ![a, b] = b → a ≠ b → ∀ c : V, c ≠ a → c ≠ b → f ![b, c] = c := by
          intro a b hfab hab c hca hcb
          have hne := (isPolymorphism_edgeRel_iff (⊤ : _root_.SimpleGraph V) f).mp hf
            ![a, b] ![b, c] (fun j => match j with | 0 => hab | 1 => hcb.symm)
          rw [hfab] at hne
          exact (hxy b c).resolve_left hne.symm
        have hstep' : ∀ a b : V, f ![a, b] = a → a ≠ b → ∀ c : V, c ≠ a → c ≠ b →
          f ![c, a] = c := by
          intro a b hfab hab c hca hcb
          have hne := (isPolymorphism_edgeRel_iff (⊤ : _root_.SimpleGraph V) f).mp hf
            ![a, b] ![c, a] (fun j => match j with | 0 => hca.symm | 1 => hab.symm)
          rw [hfab] at hne
          exact (hxy c a).resolve_right hne.symm
        by_cases hyx : y1 = x2
        · -- `y1 = x2`: pick `w ∉ {x1, y1}` (possible since `|V| ≥ 3`).
          have hexw : ∃ w : V, w ≠ x1 ∧ w ≠ y1 := by
            by_contra h; push Not at h
            have hsub : (Finset.univ : Finset V) ⊆ {x1, y1} := by
              intro w _
              by_cases h1 : w = x1
              · simp [h1]
              · simp [h w h1]
            have := Finset.card_le_card hsub
            have h2 : ({x1, y1} : Finset V).card ≤ 2 := Finset.card_le_two
            simp only [Finset.card_univ] at this
            omega
          obtain ⟨w, hwx1, hwy1⟩ := hexw
          have hfw1 : f ![y1, w] = w := hstep x1 y1 hfy1 hx1y1 w hwx1 hwy1
          -- Now `f ![y1, w] = w` and `f ![y1, y2] = y1` (`x2 = y1`).
          -- Pick `w' ∉ {y1, y2}`? Better: we have `f ![w, y1] = w` (from `f ![y1, y2] = y1`, need
          -- `w ≠ y2`)!
          by_cases hwy2 : w = y2
          · subst hwy2
            rw [← hyx] at hfx2
            exact hwy1 (hfw1.symm.trans hfx2)
          · have hfw2 : f ![w, y1] = w := hstep' y1 y2 (hyx ▸ hfx2) (hyx ▸ hx2y2) w hwy1 hwy2
            have hne := (isPolymorphism_edgeRel_iff (⊤ : _root_.SimpleGraph V) f).mp hf
              ![y1, w] ![w, y1] (fun j => match j with | 0 => hwy1.symm | 1 => hwy1)
            rw [hfw1, hfw2] at hne
            exact hne rfl
        · -- `y1 ≠ x2`: `(y1, x2)` is adjacent to BOTH `(x1, y1)` and `(x2, y2)`!
          have hne_a := (isPolymorphism_edgeRel_iff (⊤ : _root_.SimpleGraph V) f).mp hf
            ![x1, y1] ![y1, x2] (fun j => match j with | 0 => hx1y1 | 1 => hyx)
          have hne_b := (isPolymorphism_edgeRel_iff (⊤ : _root_.SimpleGraph V) f).mp hf
            ![x2, y2] ![y1, x2] (fun j => match j with | 0 => Ne.symm hyx | 1 => hx2y2.symm)
          rw [hfy1] at hne_a
          rw [hfx2] at hne_b
          rcases hxy y1 x2 with h | h
          · exact hne_a h.symm
          · exact hne_b h.symm
      · by_cases hm3 : m = 3
        · subst hm3
          -- Every binary identification is a projection (by `ih 2`).
          have hbin : ∀ (φ : Fin 3 → Fin 2), ∃ k : Fin 2, ∀ a : Fin 2 → V, f (a ∘ φ) = a k := by
            intro φ
            exact ih 2 (by omega) (by omega) (fun a => f (a ∘ φ))
              (isPolymorphism_comp_reindex hf φ) (fun x => hidem x)
          -- Extract the 3 binary identifications: `f(x,x,y)`, `f(x,y,x)`, `f(y,x,x)`.
          obtain ⟨k12, hk12⟩ := hbin ![0, 0, 1]
          obtain ⟨k13, hk13⟩ := hbin ![0, 1, 0]
          obtain ⟨k23, hk23⟩ := hbin ![1, 0, 0]
          have h12 : ∀ x y : V, f ![x, x, y] = if k12 = 0 then x else y := fun x y => by
            have := hk12 ![x, y]
            have hEq : (![x, y] ∘ (![0, 0, 1] : Fin 3 → Fin 2)) = ![x, x, y] := by
              funext i; fin_cases i <;> rfl
            rw [hEq] at this
            fin_cases k12 <;> simpa using this
          have h13 : ∀ x y : V, f ![x, y, x] = if k13 = 0 then x else y := fun x y => by
            have := hk13 ![x, y]
            have hEq : (![x, y] ∘ (![0, 1, 0] : Fin 3 → Fin 2)) = ![x, y, x] := by
              funext i; fin_cases i <;> rfl
            rw [hEq] at this
            fin_cases k13 <;> simpa using this
          have h23 : ∀ x y : V, f ![y, x, x] = if k23 = 0 then x else y := fun x y => by
            have := hk23 ![x, y]
            have hEq : (![x, y] ∘ (![1, 0, 0] : Fin 3 → Fin 2)) = ![y, x, x] := by
              funext i; fin_cases i <;> rfl
            rw [hEq] at this
            fin_cases k23 <;> simpa using this
          have hnb : ¬ (⊤ : _root_.SimpleGraph V).IsBipartite := by
            intro hb
            rcases hb with ⟨c⟩
            have hcard_fin : Fintype.card V ≤ 2 := by
              have hinj : Function.Injective c := fun x y hxy => by
                by_contra hne
                exact c.valid hne hxy
              exact (Fintype.card_le_of_injective c hinj).trans (by simp)
            omega
          -- Case split on the 8 values of `(k12, k13, k23)`!
          -- Note: `k = 0` means majority-side (`x`), `k = 1` means minority-side (`y`).
          have hsemi_contra : ∀ i0 : Fin 3,
              (∀ a : Fin 3 → V, ¬ Function.Injective a → f a = a i0) → IsProjection f := by
            intro i0 hsemi
            by_contra hnot
            -- `⊤` is a core of min degree `|V| - 1 ≥ 2`.
            have hcore : IsHomCore (⊤ : _root_.SimpleGraph V) :=
              isHomCore_top
            have hdeg : ∀ v : V, (Fintype.card V - 1) ≤ (⊤ : _root_.SimpleGraph V).degree v := by
              intro v
              rw [← _root_.SimpleGraph.card_neighborFinset_eq_degree]
              have hnf : (⊤ : _root_.SimpleGraph V).neighborFinset v = Finset.univ.erase v := by
                ext x; simp [ne_comm]
              rw [hnf, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
            have hbound : Fintype.card V < 1 + (3 - 1) * (Fintype.card V - 1) := by omega
            exact no_semiprojection_of_minDegree hcore hdeg hbound hf ⟨by omega, i0, hnot, hsemi⟩
          fin_cases k12 <;> fin_cases k13 <;> fin_cases k23
          · -- `(0, 0, 0)`: Majority!
            exact (not_isMajority_of_not_isBipartite hnb hf
              (fun x y => ⟨by simpa using h12 x y, by simpa using h13 x y,
                by simpa using h23 x y⟩)).elim
          · -- `(0, 0, 1)`: Semiprojection on coord 0!
            exact hsemi_contra 0 (fun a ha => by
              by_cases h01 : a 0 = a 1
              · have hEq : a = ![a 0, a 0, a 2] := by funext i; fin_cases i <;> simp [h01]
                rw [hEq]; simpa using h12 (a 0) (a 2)
              · by_cases h02 : a 0 = a 2
                · have hEq : a = ![a 0, a 1, a 0] := by funext i; fin_cases i <;> simp [h02]
                  rw [hEq]; simpa using h13 (a 0) (a 1)
                · by_cases h12' : a 1 = a 2
                  · have hEq : a = ![a 0, a 1, a 1] := by funext i; fin_cases i <;> simp [h12']
                    rw [hEq]; simpa using h23 (a 1) (a 0)
                  · exfalso; apply ha; intro i j hij
                    fin_cases i <;> fin_cases j <;> simp_all)
          · -- `(0, 1, 0)`: Semiprojection on coord 1!
            exact hsemi_contra 1 (fun a ha => by
              by_cases h01 : a 0 = a 1
              · have hEq : a = ![a 1, a 1, a 2] := by funext i; fin_cases i <;> simp [h01]
                rw [hEq]; simpa using h12 (a 1) (a 2)
              · by_cases h02 : a 0 = a 2
                · have hEq : a = ![a 0, a 1, a 0] := by funext i; fin_cases i <;> simp [h02]
                  rw [hEq]; simpa using h13 (a 0) (a 1)
                · by_cases h12' : a 1 = a 2
                  · have hEq : a = ![a 0, a 1, a 1] := by funext i; fin_cases i <;> simp [h12']
                    rw [hEq]; simpa using h23 (a 1) (a 0)
                  · exfalso; apply ha; intro i j hij
                    fin_cases i <;> fin_cases j <;> simp_all)
          · -- `(0, 1, 1)`: permute `g(a,b,c) = f(a,c,b)`.
            let g : (Fin 3 → V) → V := fun a => f (a ∘ ![0, 2, 1])
            have hg : Cslib.Logic.IsPolymorphism g (edgeRel (⊤ : _root_.SimpleGraph V)) :=
              isPolymorphism_comp_reindex hf ![0, 2, 1]
            exact (not_maltsev_of_not_isBipartite hnb hg
              (fun x y => by
                have hEq : (![x, x, y] ∘ (![0, 2, 1] : Fin 3 → Fin 3)) = ![x, y, x] := by
                  funext i; fin_cases i <;> rfl
                dsimp [g]; rw [hEq]; simpa using h13 x y)
              (fun x y => by
                have hEq : (![y, x, x] ∘ (![0, 2, 1] : Fin 3 → Fin 3)) = ![y, x, x] := by
                  funext i; fin_cases i <;> rfl
                dsimp [g]; rw [hEq]; simpa using h23 x y)).elim
          · -- `(1, 0, 0)`: Semiprojection on coord 2!
            exact hsemi_contra 2 (fun a ha => by
              by_cases h01 : a 0 = a 1
              · have hEq : a = ![a 0, a 0, a 2] := by funext i; fin_cases i <;> simp [h01]
                rw [hEq]; simpa using h12 (a 0) (a 2)
              · by_cases h02 : a 0 = a 2
                · have hEq : a = ![a 2, a 1, a 2] := by funext i; fin_cases i <;> simp [h02]
                  rw [hEq]; simpa using h13 (a 2) (a 1)
                · by_cases h12' : a 1 = a 2
                  · have hEq : a = ![a 0, a 2, a 2] := by funext i; fin_cases i <;> simp [h12']
                    rw [hEq]; simpa using h23 (a 2) (a 0)
                  · exfalso; apply ha; intro i j hij
                    fin_cases i <;> fin_cases j <;> simp_all)
          · -- `(1, 0, 1)`: Maltsev directly! `f(x,x,y)=y`, `f(y,x,x)=y`!
            exact (not_maltsev_of_not_isBipartite hnb hf
              (fun x y => by simpa using h12 x y)
              (fun x y => by simpa using h23 x y)).elim
          · -- `(1, 1, 0)`: permute `g(a,b,c) = f(b,a,c)`.
            let g : (Fin 3 → V) → V := fun a => f (a ∘ ![1, 0, 2])
            have hg : Cslib.Logic.IsPolymorphism g (edgeRel (⊤ : _root_.SimpleGraph V)) :=
              isPolymorphism_comp_reindex hf ![1, 0, 2]
            exact (not_maltsev_of_not_isBipartite hnb hg
              (fun x y => by
                have hEq : (![x, x, y] ∘ (![1, 0, 2] : Fin 3 → Fin 3)) = ![x, x, y] := by
                  funext i; fin_cases i <;> rfl
                dsimp [g]; rw [hEq]; simpa using h12 x y)
              (fun x y => by
                have hEq : (![y, x, x] ∘ (![1, 0, 2] : Fin 3 → Fin 3)) = ![x, y, x] := by
                  funext i; fin_cases i <;> rfl
                dsimp [g]; rw [hEq]; simpa using h13 x y)).elim
          · -- `(1, 1, 1)`: Minority (satisfies Maltsev directly)!
            exact (not_maltsev_of_not_isBipartite hnb hf
              (fun x y => by simpa using h12 x y)
              (fun x y => by simpa using h23 x y)).elim
        · -- `m ≥ 4`: every binary identification is a projection, so Świerczkowski gives
          -- a semiprojection, contradicting `no_semiprojection_of_minDegree`!
          have hm4 : 4 ≤ m := by omega
          have hcollapse : ∀ (i j : Fin m), i ≠ j →
              ∃ k : Fin m, ∀ a : Fin m → V, a i = a j → f a = a k := by
            intro i j hij
            -- Map `Fin m → Fin (m - 1)` identifying `i` and `j` via `Fin.predAbove`!
            -- Simpler: pick an equivalence `Fin (m - 1) ≃ {x : Fin m // x ≠ j}`!
            have hcard_sub : Fintype.card {x : Fin m // x ≠ j} = m - 1 := by
              rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
            let e := (Fintype.equivFinOfCardEq hcard_sub).symm
            let φ : Fin m → Fin (m - 1) := fun x =>
              if hx : x = j then e.symm ⟨i, hij⟩ else e.symm ⟨x, hx⟩
            have hφ_ij : φ i = φ j := by simp [φ, hij]
            obtain ⟨k0, hk0⟩ := ih (m - 1) (by omega) (by omega) (fun b => f (b ∘ φ))
              (isPolymorphism_comp_reindex hf φ) (fun x => hidem x)
            refine ⟨(e k0).1, fun a haij => ?_⟩
            let b : Fin (m - 1) → V := fun t => a (e t).1
            have hab : b ∘ φ = a := by
              funext x
              by_cases hx : x = j
              · subst hx
                simp [b, φ, haij]
              · simp [b, φ, hx]
            have := hk0 b
            dsimp only at this
            rw [hab] at this
            exact this
          obtain ⟨i0, hi0⟩ := swierczkowski_lemma hm4 f hcollapse
          by_contra hnot
          have hcore : IsHomCore (⊤ : _root_.SimpleGraph V) := isHomCore_top
          have hdeg : ∀ v : V, (Fintype.card V - 1) ≤ (⊤ : _root_.SimpleGraph V).degree v := by
            intro v
            rw [← _root_.SimpleGraph.card_neighborFinset_eq_degree]
            have hnf : (⊤ : _root_.SimpleGraph V).neighborFinset v = Finset.univ.erase v := by
              ext x; simp [ne_comm]
            rw [hnf, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
          have hbound : Fintype.card V < 1 + (m - 1) * (Fintype.card V - 1) := by
            have hmul : 3 * (Fintype.card V - 1) ≤ (m - 1) * (Fintype.card V - 1) :=
              Nat.mul_le_mul_right _ (by omega)
            omega
          exact no_semiprojection_of_minDegree hcore hdeg hbound hf ⟨by omega, i0, hnot, hi0⟩

/-- **Rosenberg's Condensed Graph Theorem**: if a finite simple graph `G` is not projective, then
`Pol(G)` contains a polymorphism of one of three types: (1) an $\mathbb{F}_2$-vector space affine
operation `x + y + z`, (2) a ternary majority operation, or (3) a semiprojection of arity `m ≥ 2`.
-/
theorem exists_rosenberg_polymorphism_of_not_isProjective [Finite V]
    {G : _root_.SimpleGraph V} (hnotproj : ¬ IsProjective G) :
    (∃ f : (Fin 3 → V) → V, Cslib.Logic.IsPolymorphism f (edgeRel G) ∧ IsAffineF2 f) ∨
    (∃ f : (Fin 3 → V) → V, Cslib.Logic.IsPolymorphism f (edgeRel G) ∧ IsMajority f) ∨
    (∃ (m : ℕ) (f : (Fin m → V) → V),
      Cslib.Logic.IsPolymorphism f (edgeRel G) ∧ IsSemiprojection f) := by
  have : Fintype V := Fintype.ofFinite V
  classical
  -- First observe `2 ≤ Fintype.card V` (empty and singleton graphs are vacuously projective).
  have hcard2 : 2 ≤ Fintype.card V := by
    by_contra hlt
    apply hnotproj
    intro m hm f _ hidem
    by_cases h0 : Fintype.card V = 0
    · have : IsEmpty V := Fintype.card_eq_zero_iff.mp h0
      exact ⟨⟨0, hm⟩, fun a => isEmptyElim (a ⟨0, hm⟩)⟩
    · have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      exact ⟨⟨0, hm⟩, fun a => Subsingleton.elim _ _⟩
  by_cases hbip : G.IsBipartite
  · -- Bipartite case: three clean subcases (`G = ⊥`, `|V| = 2 ∧ G ≠ ⊥`, `|V| ≥ 3 ∧ G ≠ ⊥`).
    by_cases hbot : G = ⊥
    · -- No edges: any ternary majority function preserves `⊥` vacuously (Type 2).
      right; left
      let f : (Fin 3 → V) → V := fun a =>
        if a 0 = a 1 then a 0 else if a 0 = a 2 then a 0 else if a 1 = a 2 then a 1 else a 0
      refine ⟨f, ?_, fun x y => ?_⟩
      · rw [isPolymorphism_edgeRel_iff, hbot]
        intro a b hab
        exact absurd (hab 0) (by simp)
      · refine ⟨?_, ?_, ?_⟩
        · by_cases hxy : x = y <;> simp [f, hxy]
        · by_cases hxy : x = y <;> simp [f, hxy]
        · by_cases hxy : x = y
          · simp [f, hxy]
          · simp [f, Ne.symm hxy]
    · have hedge : ∃ u v : V, G.Adj u v := by
        by_contra h; push Not at h
        apply hbot; ext u v; simp [h u v]
      obtain ⟨u0, v0, huv0⟩ := hedge
      by_cases hcard3 : 3 ≤ Fintype.card V
      · -- `|V| ≥ 3` and `G ≠ ⊥`: `f(x, y) = if c x = c y then x else y` is a 2-ary semiprojection!
        right; right
        rcases hbip with ⟨c⟩
        let f : (Fin 2 → V) → V := fun a => if c (a 0) = c (a 1) then a 0 else a 1
        refine ⟨2, f, ?_, le_rfl, 0, ?_, ?_⟩
        · rw [isPolymorphism_edgeRel_iff]
          intro a b hab
          have h0 : c (a 0) ≠ c (b 0) := c.valid (hab 0)
          have h1 : c (a 1) ≠ c (b 1) := c.valid (hab 1)
          have hiff : c (a 0) = c (a 1) ↔ c (b 0) = c (b 1) := by
            have hc0 := (c (a 0)).isLt
            have hc1 := (c (a 1)).isLt
            have hd0 := (c (b 0)).isLt
            have hd1 := (c (b 1)).isLt
            have h0' : (c (a 0)).val ≠ (c (b 0)).val := fun h => h0 (Fin.ext h)
            have h1' : (c (a 1)).val ≠ (c (b 1)).val := fun h => h1 (Fin.ext h)
            constructor <;> intro hEq
            · apply Fin.ext; have := congrArg Fin.val hEq; omega
            · apply Fin.ext; have := congrArg Fin.val hEq; omega
          dsimp [f]
          by_cases h : c (a 0) = c (a 1)
          · simp [h, hiff.mp h, hab 0]
          · simp [h, mt hiff.mpr h, hab 1]
        · rintro ⟨i, hi⟩
          fin_cases i
          · have hneq : c u0 ≠ c v0 := c.valid huv0
            have hEq : v0 = u0 := by simpa [f, hneq] using hi ![u0, v0]
            exact huv0.ne hEq.symm
          · -- By pigeonhole on `c : V → Fin 2` and `|V| ≥ 3`, pick `x ≠ y` with `c x = c y`.
            have hnotinj : ¬ Function.Injective c := fun hinj => by
              have := Fintype.card_le_of_injective c hinj
              simp only [Fintype.card_fin] at this
              omega
            rw [Function.Injective] at hnotinj
            push Not at hnotinj
            obtain ⟨x, y, hxy_c, hxy_ne⟩ := hnotinj
            have hEq : x = y := by simpa [f, hxy_c] using hi ![x, y]
            exact hxy_ne hEq
        · intro a ha
          have h01 : a 0 = a 1 := by
            by_contra hne
            apply ha
            intro i j hij
            fin_cases i <;> fin_cases j <;> simp_all
          simp [f, h01]
      · -- `|V| = 2` and `G ≠ ⊥`: `V ≃ ZMod 2` gives Type 1 (`x + y + z`)!
        left
        have hcard_eq : Fintype.card V = 2 := by omega
        let e : V ≃ ZMod 2 := Fintype.equivFinOfCardEq hcard_eq
        let instAdd : AddCommGroup V := e.addCommGroup
        let instMod : Module (ZMod 2) V :=
          { smul := fun c x => e.symm (c * e x)
            one_smul := fun x => by change e.symm (1 * e x) = x; simp
            mul_smul := fun c d x => by
              change e.symm (c * d * e x) = e.symm (c * e (e.symm (d * e x)))
              simp [mul_assoc]
            smul_zero := fun c => by
              change e.symm (c * e (e.symm 0)) = e.symm 0
              simp
            smul_add := fun c x y => by
              change e.symm (c * e (e.symm (e x + e y))) =
                e.symm (e (e.symm (c * e x)) + e (e.symm (c * e y)))
              simp [mul_add]
            add_smul := fun c d x => by
              change e.symm ((c + d) * e x) =
                e.symm (e (e.symm (c * e x)) + e (e.symm (d * e x)))
              simp [add_mul]
            zero_smul := fun x => by
              change e.symm (0 * e x) = e.symm 0
              simp }
        let f : (Fin 3 → V) → V := fun a => a 0 + a 1 + a 2
        refine ⟨f, ?_, ⟨instAdd, instMod, fun x y z => rfl⟩⟩
        rw [isPolymorphism_edgeRel_iff]
        intro a b hab
        have hne_z : ∀ j : Fin 2 → V, G.Adj (j 0) (j 1) → e (j 0) ≠ e (j 1) :=
          fun j hj => e.injective.ne hj.ne
        -- On `ZMod 2`, any two distinct elements satisfy `x + y = 1`.
        have hsum1 : ∀ x y : ZMod 2, x ≠ y → x + y = 1 := by decide
        have hsum_ne : ∀ x y : ZMod 2, x + y = 1 → x ≠ y := by decide
        have h1 : ∀ j : Fin 3, e (a j) + e (b j) = 1 :=
          fun j => hsum1 (e (a j)) (e (b j)) (e.injective.ne (hab j).ne)
        have hadd_e : ∀ x y : V, e (x + y) = e x + e y := fun x y => by
          change e (e.symm (e x + e y)) = e x + e y
          exact e.apply_symm_apply _
        have htot : e (f a) + e (f b) = 1 := by
          dsimp [f]
          rw [hadd_e, hadd_e, hadd_e, hadd_e]
          have ha0 := h1 0; have ha1 := h1 1; have ha2 := h1 2
          -- In `ZMod 2`, `(a0+a1+a2)+(b0+b1+b2) = (a0+b0)+(a1+b1)+(a2+b2) = 1+1+1 = 1`!
          have hring : e (a 0) + e (a 1) + e (a 2) + (e (b 0) + e (b 1) + e (b 2)) =
              (e (a 0) + e (b 0)) + (e (a 1) + e (b 1)) + (e (a 2) + e (b 2)) := by ring
          rw [hring, ha0, ha1, ha2]
          decide
        have hfab_ne : f a ≠ f b := fun h => hsum_ne _ _ htot (congrArg e h)
        -- Since `|V| = 2` and `G` has an edge `(u0, v0)`, ANY two distinct vertices are adjacent!
        have heq_or : ∀ x : V, x = u0 ∨ x = v0 := by
          intro x
          have h1 : e x = e u0 ∨ e x = e v0 := by
            have hu : e u0 ≠ e v0 := e.injective.ne huv0.ne
            revert hu; generalize e x = ax; generalize e u0 = au; generalize e v0 = av
            decide +revert
          exact h1.imp (fun h => e.injective h) (fun h => e.injective h)
        rcases heq_or (f a) with hfa | hfa <;> rcases heq_or (f b) with hfb | hfb
        · exact (hfab_ne (hfa.trans hfb.symm)).elim
        · rw [hfa, hfb]; exact huv0
        · rw [hfa, hfb]; exact huv0.symm
        · exact (hfab_ne (hfa.trans hfb.symm)).elim
  · -- Non-bipartite case: pick minimal arity `m` admitting an idempotent non-projection!
    have hex_m : ∃ m : ℕ, 0 < m ∧ ∃ f : (Fin m → V) → V,
        Cslib.Logic.IsPolymorphism f (edgeRel G) ∧ IsIdempotent f ∧ ¬ IsProjection f := by
      unfold IsProjective at hnotproj
      push Not at hnotproj
      exact hnotproj
    have hmin_ex : ∃ m : ℕ, 0 < m ∧
        (∃ f : (Fin m → V) → V,
          Cslib.Logic.IsPolymorphism f (edgeRel G) ∧ IsIdempotent f ∧ ¬ IsProjection f) ∧
        (∀ k < m, 0 < k → ∀ g : (Fin k → V) → V,
          Cslib.Logic.IsPolymorphism g (edgeRel G) → IsIdempotent g → IsProjection g) :=
      ⟨Nat.find hex_m, (Nat.find_spec hex_m).1, (Nat.find_spec hex_m).2,
        fun k hkm hkpos g hg hgid => by
          by_contra hgn
          exact Nat.find_min hex_m hkm ⟨hkpos, g, hg, hgid, hgn⟩⟩
    obtain ⟨m, hm_pos, ⟨f, hf, hidem, hnotproj_f⟩, hmin⟩ := hmin_ex
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have hm1 : m = 1 := by omega
      subst hm1
      apply hnotproj_f
      refine ⟨0, fun a => ?_⟩
      have hEq : a = fun _ => a 0 := by funext i; fin_cases i; rfl
      rw [hEq, hidem (a 0)]
    by_cases hmeq2 : m = 2
    · subst hmeq2
      right; right
      refine ⟨2, f, hf, le_rfl, 0, hnotproj_f, fun a ha => ?_⟩
      have h01 : a 0 = a 1 := by
        by_contra hne
        apply ha; intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      have hEq : a = fun _ => a 0 := by funext i; fin_cases i <;> simp [h01]
      rw [hEq, hidem (a 0)]
    · by_cases hmeq3 : m = 3
      · subst hmeq3
        have hbin : ∀ (φ : Fin 3 → Fin 2), ∃ k : Fin 2, ∀ a : Fin 2 → V, f (a ∘ φ) = a k := by
          intro φ
          exact hmin 2 (by omega) (by omega) (fun a => f (a ∘ φ))
            (isPolymorphism_comp_reindex hf φ) (fun x => hidem x)
        obtain ⟨k12, hk12⟩ := hbin ![0, 0, 1]
        obtain ⟨k13, hk13⟩ := hbin ![0, 1, 0]
        obtain ⟨k23, hk23⟩ := hbin ![1, 0, 0]
        have h12 : ∀ x y : V, f ![x, x, y] = if k12 = 0 then x else y := fun x y => by
          have := hk12 ![x, y]
          have hEq : (![x, y] ∘ (![0, 0, 1] : Fin 3 → Fin 2)) = ![x, x, y] := by
            funext i; fin_cases i <;> rfl
          rw [hEq] at this
          fin_cases k12 <;> simpa using this
        have h13 : ∀ x y : V, f ![x, y, x] = if k13 = 0 then x else y := fun x y => by
          have := hk13 ![x, y]
          have hEq : (![x, y] ∘ (![0, 1, 0] : Fin 3 → Fin 2)) = ![x, y, x] := by
            funext i; fin_cases i <;> rfl
          rw [hEq] at this
          fin_cases k13 <;> simpa using this
        have h23 : ∀ x y : V, f ![y, x, x] = if k23 = 0 then x else y := fun x y => by
          have := hk23 ![x, y]
          have hEq : (![x, y] ∘ (![1, 0, 0] : Fin 3 → Fin 2)) = ![y, x, x] := by
            funext i; fin_cases i <;> rfl
          rw [hEq] at this
          fin_cases k23 <;> simpa using this
        fin_cases k12 <;> fin_cases k13 <;> fin_cases k23
        · right; left
          exact ⟨f, hf, fun x y => ⟨by simpa using h12 x y, by simpa using h13 x y,
            by simpa using h23 x y⟩⟩
        · right; right
          refine ⟨3, f, hf, by omega, 0, hnotproj_f, fun a ha => ?_⟩
          by_cases h01 : a 0 = a 1
          · have hEq : a = ![a 0, a 0, a 2] := by funext i; fin_cases i <;> simp [h01]
            rw [hEq]; simpa using h12 (a 0) (a 2)
          · by_cases h02 : a 0 = a 2
            · have hEq : a = ![a 0, a 1, a 0] := by funext i; fin_cases i <;> simp [h02]
              rw [hEq]; simpa using h13 (a 0) (a 1)
            · by_cases h12' : a 1 = a 2
              · have hEq : a = ![a 0, a 1, a 1] := by funext i; fin_cases i <;> simp [h12']
                rw [hEq]; simpa using h23 (a 1) (a 0)
              · exfalso; apply ha; intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
        · right; right
          refine ⟨3, f, hf, by omega, 1, hnotproj_f, fun a ha => ?_⟩
          by_cases h01 : a 0 = a 1
          · have hEq : a = ![a 1, a 1, a 2] := by funext i; fin_cases i <;> simp [h01]
            rw [hEq]; simpa using h12 (a 1) (a 2)
          · by_cases h02 : a 0 = a 2
            · have hEq : a = ![a 0, a 1, a 0] := by funext i; fin_cases i <;> simp [h02]
              rw [hEq]; simpa using h13 (a 0) (a 1)
            · by_cases h12' : a 1 = a 2
              · have hEq : a = ![a 0, a 1, a 1] := by funext i; fin_cases i <;> simp [h12']
                rw [hEq]; simpa using h23 (a 1) (a 0)
              · exfalso; apply ha; intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
        · exact (not_maltsev_of_not_isBipartite hbip (isPolymorphism_comp_reindex hf ![0, 2, 1])
            (fun x y => by
              have hEq : (![x, x, y] ∘ (![0, 2, 1] : Fin 3 → Fin 3)) = ![x, y, x] := by
                funext i; fin_cases i <;> rfl
              rw [hEq]; simpa using h13 x y)
            (fun x y => by
              have hEq : (![y, x, x] ∘ (![0, 2, 1] : Fin 3 → Fin 3)) = ![y, x, x] := by
                funext i; fin_cases i <;> rfl
              rw [hEq]; simpa using h23 x y)).elim
        · right; right
          refine ⟨3, f, hf, by omega, 2, hnotproj_f, fun a ha => ?_⟩
          by_cases h01 : a 0 = a 1
          · have hEq : a = ![a 0, a 0, a 2] := by funext i; fin_cases i <;> simp [h01]
            rw [hEq]; simpa using h12 (a 0) (a 2)
          · by_cases h02 : a 0 = a 2
            · have hEq : a = ![a 2, a 1, a 2] := by funext i; fin_cases i <;> simp [h02]
              rw [hEq]; simpa using h13 (a 2) (a 1)
            · by_cases h12' : a 1 = a 2
              · have hEq : a = ![a 0, a 2, a 2] := by funext i; fin_cases i <;> simp [h12']
                rw [hEq]; simpa using h23 (a 2) (a 0)
              · exfalso; apply ha; intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
        · exact (not_maltsev_of_not_isBipartite hbip hf
            (fun x y => by simpa using h12 x y)
            (fun x y => by simpa using h23 x y)).elim
        · exact (not_maltsev_of_not_isBipartite hbip (isPolymorphism_comp_reindex hf ![1, 0, 2])
            (fun x y => by
              have hEq : (![x, x, y] ∘ (![1, 0, 2] : Fin 3 → Fin 3)) = ![x, x, y] := by
                funext i; fin_cases i <;> rfl
              rw [hEq]; simpa using h12 x y)
            (fun x y => by
              have hEq : (![y, x, x] ∘ (![1, 0, 2] : Fin 3 → Fin 3)) = ![x, y, x] := by
                funext i; fin_cases i <;> rfl
              rw [hEq]; simpa using h13 x y)).elim
        · exact (not_maltsev_of_not_isBipartite hbip hf
            (fun x y => by simpa using h12 x y)
            (fun x y => by simpa using h23 x y)).elim
      · -- `m ≥ 4`: every binary identification is a projection, so Świerczkowski gives Type 3!
        have hm4 : 4 ≤ m := by omega
        have hcollapse : ∀ (i j : Fin m), i ≠ j →
            ∃ k : Fin m, ∀ a : Fin m → V, a i = a j → f a = a k := by
          intro i j hij
          have hcard_sub : Fintype.card {x : Fin m // x ≠ j} = m - 1 := by
            rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
          let e := (Fintype.equivFinOfCardEq hcard_sub).symm
          let φ : Fin m → Fin (m - 1) := fun x =>
            if hx : x = j then e.symm ⟨i, hij⟩ else e.symm ⟨x, hx⟩
          obtain ⟨k0, hk0⟩ := hmin (m - 1) (by omega) (by omega) (fun b => f (b ∘ φ))
            (isPolymorphism_comp_reindex hf φ) (fun x => hidem x)
          refine ⟨(e k0).1, fun a haij => ?_⟩
          let b : Fin (m - 1) → V := fun t => a (e t).1
          have hab : b ∘ φ = a := by
            funext x
            by_cases hx : x = j
            · subst hx; simp [b, φ, haij]
            · simp [b, φ, hx]
          have := hk0 b
          dsimp only at this
          rw [hab] at this
          exact this
        obtain ⟨i0, hi0⟩ := swierczkowski_lemma hm4 f hcollapse
        right; right
        exact ⟨m, f, hf, by omega, i0, hnotproj_f, hi0⟩

/-- Every finite core graph on at least `3` vertices is non-bipartite. -/
theorem not_isBipartite_of_isHomCore [Fintype V] {G : _root_.SimpleGraph V}
    (hcore : IsHomCore G) (hcard : 3 ≤ Fintype.card V) : ¬ G.IsBipartite := by
  intro hbip
  rcases hbip with ⟨c⟩
  by_cases hbot : G = ⊥
  · -- Empty graph on `≥ 3` vertices retracts to a single vertex, contradicting core.
    obtain ⟨v0⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    let h : G →g G := ⟨fun _ => v0, fun {x y} hxy => by rw [hbot] at hxy; exact hxy.elim⟩
    have hinj := (isHomCore_iff_forall_injective.mp hcore) h
    have hle := Fintype.card_le_of_injective (fun _ : V => (0 : Fin 1))
      (fun x y _ => hinj (rfl : h x = h y))
    simp only [Fintype.card_fin] at hle
    omega
  · -- Nonempty bipartite graph retracts to a single edge, contradicting `|V| ≥ 3`.
    have hedge : ∃ u v : V, G.Adj u v := by
      by_contra h; push Not at h
      apply hbot; ext u v; simp [h u v]
    obtain ⟨u0, v0, huv0⟩ := hedge
    have hcu : c u0 ≠ c v0 := c.valid huv0
    let h : G →g G :=
      { toFun := fun x => if c x = c u0 then u0 else v0
        map_rel' := by
          intro x y hxy
          have hcxy : c x ≠ c y := c.valid hxy
          by_cases hx : c x = c u0
          · have hy : c y ≠ c u0 := fun h => hcxy (hx.trans h.symm)
            simp [hx, hy, huv0]
          · have hy : c y = c u0 := by
              have h1 := (c x).isLt; have h2 := (c y).isLt; have h3 := (c u0).isLt
              have hx' : (c x).val ≠ (c u0).val := fun h => hx (Fin.ext h)
              have hcxy' : (c x).val ≠ (c y).val := fun h => hcxy (Fin.ext h)
              exact Fin.ext (by omega)
            simp [hx, hy, huv0.symm] }
    have hinj := (isHomCore_iff_forall_injective.mp hcore) h
    have hle : Fintype.card V ≤ 2 := by
      let g : V → Fin 2 := fun x => if c x = c u0 then 0 else 1
      refine (Fintype.card_le_of_injective g fun x y hxy => hinj ?_).trans (by simp)
      dsimp [g] at hxy
      dsimp [h]
      split_ifs at hxy ⊢ with hx hy hy'
      · rfl
      · simp at hxy
      · simp at hxy
      · rfl
    omega

/-- **Corollary `cor:semiprojection_projectivity`**: every finite core graph on at least `3`
vertices whose total polymorphisms contain no semiprojection is projective. -/
theorem isProjective_of_isHomCore_of_no_semiprojection [Fintype V] {G : _root_.SimpleGraph V}
    (hcore : IsHomCore G) (hcard : 3 ≤ Fintype.card V)
    (hno : ∀ (m : ℕ) (f : (Fin m → V) → V),
      Cslib.Logic.IsPolymorphism f (edgeRel G) → ¬ IsSemiprojection f) :
    IsProjective G := by
  have hnb : ¬ G.IsBipartite := not_isBipartite_of_isHomCore hcore hcard
  by_contra hnotproj
  rcases exists_rosenberg_polymorphism_of_not_isProjective hnotproj with
    ⟨f, hf, ⟨_, _, haff⟩⟩ | ⟨f, hf, hmaj⟩ | ⟨m, f, hf, hsemi⟩
  · -- Type 1 (`x + y + z` in an `𝔽₂`-vector space) is Maltsev, impossible on non-bipartite `G`.
    have h2 : ∀ x : V, x + x = 0 := fun x => by
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      have := add_smul (1 : ZMod 2) 1 x
      rw [h11, zero_smul, one_smul] at this
      exact this.symm
    refine not_maltsev_of_not_isBipartite hnb hf (fun x y => ?_) (fun x y => ?_)
    · rw [haff, h2, zero_add]
    · rw [haff, add_assoc, h2, add_zero]
  · exact not_isMajority_of_not_isBipartite hnb hf hmaj
  · exact hno m f hf hsemi

end Cslib.Logic.SimpleGraph
