/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Finset.Lattice.Fold

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Find

/-!
# Bar-Hillel Pumping Lemma for Context-Free Languages

This module proves the Bar-Hillel pumping lemma for context-free grammars and context-free
languages (`CslibFrontier.ContextFreeGrammar.pumping_lemma` and
`CslibFrontier.Language.exists_pumping_of_isContextFree`) directly via minimal-node-count parse
trees and single-hole tree contexts, without requiring `[Fintype G.NT]` on
`G : ContextFreeGrammar T` (bounding repeated nonterminals via
`G.rules.image ContextFreeRule.input`).

## Main results

* `CslibFrontier.ContextFreeGrammar.pumping_lemma`: for every `G : ContextFreeGrammar T`, setting
  `p = (max 2 (G.rules.sup fun r ↦ r.output.length)) ^ (G.rules.card + 1)`, every word
  `w ∈ G.language` with `p ≤ w.length` decomposes as `w = u ++ v ++ x ++ y ++ z` with
  `1 ≤ (v ++ y).length`, `(v ++ x ++ y).length ≤ p`, and
  `u ++ (List.replicate m v).flatten ++ x ++ (List.replicate m y).flatten ++ z ∈ G.language` for
  all `m : ℕ`.
* `CslibFrontier.Language.exists_pumping_of_isContextFree`: the Bar-Hillel pumping lemma for any
  `L : Language T` satisfying `L.IsContextFree`.
-/

public section

universe u

namespace CslibFrontier

namespace ContextFreeGrammar

section Pumping

variable {T : Type u}

private inductive CFParseTree (G : ContextFreeGrammar T) : Symbol T G.NT → Type u
  | terminal (a : T) : CFParseTree G (.terminal a)
  | nonterminal {A : G.NT} {rhs : List (Symbol T G.NT)} (hrule : ⟨A, rhs⟩ ∈ G.rules)
      (children : (i : Fin rhs.length) → CFParseTree G rhs[i]) : CFParseTree G (.nonterminal A)

private def CFParseTree.yield {G : ContextFreeGrammar T} :
    ∀ {s : Symbol T G.NT}, CFParseTree G s → List T
  | _, .terminal a => [a]
  | _, .nonterminal _ children => (List.ofFn fun i ↦ (children i).yield).flatten

private def CFParseTree.height {G : ContextFreeGrammar T} :
    ∀ {s : Symbol T G.NT}, CFParseTree G s → ℕ
  | _, .terminal _ => 0
  | _, .nonterminal (rhs := rhs) _ children =>
    1 + (Finset.univ : Finset (Fin rhs.length)).sup fun i ↦ (children i).height

private def CFParseTree.nodeCount {G : ContextFreeGrammar T} :
    ∀ {s : Symbol T G.NT}, CFParseTree G s → ℕ
  | _, .terminal _ => 1
  | _, .nonterminal (rhs := rhs) _ children =>
    1 + (Finset.univ : Finset (Fin rhs.length)).sum fun i ↦ (children i).nodeCount

private inductive CFTreeList (G : ContextFreeGrammar T) : List (Symbol T G.NT) → Type u
  | nil : CFTreeList G []
  | cons {s : Symbol T G.NT} {ss : List (Symbol T G.NT)} :
      CFParseTree G s → CFTreeList G ss → CFTreeList G (s :: ss)

private def CFTreeList.ofChildren {G : ContextFreeGrammar T} :
    ∀ (l : List (Symbol T G.NT)), ((i : Fin l.length) → CFParseTree G l[i]) → CFTreeList G l
  | [], _ => .nil
  | _ :: ss, ch => .cons (ch ⟨0, Nat.zero_lt_succ _⟩) (ofChildren ss fun i ↦ ch i.succ)

private def CFTreeList.get {G : ContextFreeGrammar T} :
    ∀ {l : List (Symbol T G.NT)}, CFTreeList G l → (i : Fin l.length) → CFParseTree G l[i]
  | [], .nil, i => i.elim0
  | _ :: _, .cons hd _, ⟨0, _⟩ => hd
  | _ :: _, .cons _ tl, ⟨i + 1, hi⟩ => tl.get ⟨i, Nat.lt_of_succ_lt_succ hi⟩

private theorem CFTreeList.get_ofChildren {G : ContextFreeGrammar T} :
    ∀ (l : List (Symbol T G.NT)) (ch : (i : Fin l.length) → CFParseTree G l[i]),
      (ofChildren l ch).get = ch
  | [], ch => funext fun i ↦ i.elim0
  | _ :: ss, ch => by
    funext ⟨i, hi⟩
    cases i with
    | zero => rfl
    | succ j =>
      exact congrFun (get_ofChildren ss fun k ↦ ch k.succ) ⟨j, Nat.lt_of_succ_lt_succ hi⟩

private def CFTreeList.yield {G : ContextFreeGrammar T} {l : List (Symbol T G.NT)} :
    CFTreeList G l → List T
  | .nil => []
  | .cons hd tl => hd.yield ++ tl.yield

@[simp]
private theorem CFTreeList.yield_nil {G : ContextFreeGrammar T} :
    (CFTreeList.nil : CFTreeList G []).yield = [] := rfl

@[simp]
private theorem CFTreeList.yield_cons {G : ContextFreeGrammar T} {s : Symbol T G.NT}
    {ss : List (Symbol T G.NT)} (hd : CFParseTree G s) (tl : CFTreeList G ss) :
    (CFTreeList.cons hd tl).yield = hd.yield ++ tl.yield := rfl

private theorem CFTreeList.ofFn_get_yield {G : ContextFreeGrammar T} :
    ∀ {l : List (Symbol T G.NT)} (ts : CFTreeList G l),
      (List.ofFn fun i ↦ (ts.get i).yield).flatten = ts.yield
  | [], .nil => rfl
  | _ :: _, .cons hd tl => by
    rw [List.ofFn_succ, List.flatten_cons]
    exact congrArg (hd.yield ++ ·) tl.ofFn_get_yield

private def CFTreeList.maxHeight {G : ContextFreeGrammar T} {l : List (Symbol T G.NT)} :
    CFTreeList G l → ℕ
  | .nil => 0
  | .cons hd tl => max hd.height tl.maxHeight

@[simp]
private theorem CFTreeList.maxHeight_nil {G : ContextFreeGrammar T} :
    (CFTreeList.nil : CFTreeList G []).maxHeight = 0 := rfl

@[simp]
private theorem CFTreeList.maxHeight_cons {G : ContextFreeGrammar T} {s : Symbol T G.NT}
    {ss : List (Symbol T G.NT)} (hd : CFParseTree G s) (tl : CFTreeList G ss) :
    (CFTreeList.cons hd tl).maxHeight = max hd.height tl.maxHeight := rfl

private theorem CFTreeList.sup_get_height {G : ContextFreeGrammar T} :
    ∀ {l : List (Symbol T G.NT)} (ts : CFTreeList G l),
      (Finset.univ : Finset (Fin l.length)).sup (fun i ↦ (ts.get i).height) = ts.maxHeight
  | [], .nil => Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ ↦ i.elim0)
  | s :: ss, .cons hd tl => by
    rw [CFTreeList.maxHeight_cons, ← tl.sup_get_height]
    apply le_antisymm
    · apply Finset.sup_le
      intro idx _
      rcases idx with ⟨k, hk⟩
      cases k with
      | zero => exact le_max_left _ _
      | succ j =>
        exact le_trans
          (Finset.le_sup (f := fun m : Fin ss.length ↦ (tl.get m).height)
            (Finset.mem_univ (⟨j, Nat.lt_of_succ_lt_succ hk⟩ : Fin ss.length)))
          (le_max_right _ _)
    · rw [max_le_iff]
      have h0 : hd.height ≤
          (Finset.univ : Finset (Fin (s :: ss).length)).sup
            (fun i ↦ ((CFTreeList.cons hd tl).get i).height) :=
        Finset.le_sup
          (f := fun k : Fin (s :: ss).length ↦ ((CFTreeList.cons hd tl).get k).height)
          (Finset.mem_univ (⟨0, Nat.zero_lt_succ _⟩ : Fin (s :: ss).length))
      refine ⟨h0, Finset.sup_le fun j _ ↦ ?_⟩
      exact Finset.le_sup
        (f := fun k : Fin (s :: ss).length ↦ ((CFTreeList.cons hd tl).get k).height)
        (Finset.mem_univ j.succ)

private def CFTreeList.nodeSum {G : ContextFreeGrammar T} {l : List (Symbol T G.NT)} :
    CFTreeList G l → ℕ
  | .nil => 0
  | .cons hd tl => hd.nodeCount + tl.nodeSum

@[simp]
private theorem CFTreeList.nodeSum_nil {G : ContextFreeGrammar T} :
    (CFTreeList.nil : CFTreeList G []).nodeSum = 0 := rfl

@[simp]
private theorem CFTreeList.nodeSum_cons {G : ContextFreeGrammar T} {s : Symbol T G.NT}
    {ss : List (Symbol T G.NT)} (hd : CFParseTree G s) (tl : CFTreeList G ss) :
    (CFTreeList.cons hd tl).nodeSum = hd.nodeCount + tl.nodeSum := rfl

private theorem CFTreeList.sum_get_nodeCount {G : ContextFreeGrammar T} :
    ∀ {l : List (Symbol T G.NT)} (ts : CFTreeList G l),
      (Finset.univ : Finset (Fin l.length)).sum (fun i ↦ (ts.get i).nodeCount) = ts.nodeSum
  | [], .nil => rfl
  | _ :: ss, .cons hd tl => by
    change ((Finset.univ : Finset (Fin (ss.length + 1))).sum
      fun i ↦ ((CFTreeList.cons hd tl).get i).nodeCount) = hd.nodeCount + tl.nodeSum
    rw [Fin.sum_univ_succ]
    exact congrArg (hd.nodeCount + ·) tl.sum_get_nodeCount

private def CFTreeList.append {G : ContextFreeGrammar T} :
    ∀ {l₁ l₂ : List (Symbol T G.NT)},
      CFTreeList G l₁ → CFTreeList G l₂ → CFTreeList G (l₁ ++ l₂)
  | [], _, .nil, t₂ => t₂
  | _ :: _, _, .cons hd tl, t₂ => .cons hd (tl.append t₂)

private theorem CFTreeList.yield_append {G : ContextFreeGrammar T} :
    ∀ {l₁ l₂ : List (Symbol T G.NT)} (t₁ : CFTreeList G l₁) (t₂ : CFTreeList G l₂),
      (t₁.append t₂).yield = t₁.yield ++ t₂.yield
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons hd tl, t₂ => by
    change hd.yield ++ (tl.append t₂).yield = (hd.yield ++ tl.yield) ++ t₂.yield
    rw [tl.yield_append t₂, List.append_assoc]

private def CFTreeList.split {G : ContextFreeGrammar T} :
    ∀ (l₁ : List (Symbol T G.NT)) {l₂ : List (Symbol T G.NT)},
      CFTreeList G (l₁ ++ l₂) → CFTreeList G l₁ × CFTreeList G l₂
  | [], _, ts => (.nil, ts)
  | _ :: ss, _, .cons hd tl =>
    let sp := split ss tl
    (.cons hd sp.1, sp.2)

private theorem CFTreeList.yield_split {G : ContextFreeGrammar T} :
    ∀ (l₁ : List (Symbol T G.NT)) {l₂ : List (Symbol T G.NT)} (ts : CFTreeList G (l₁ ++ l₂)),
      ts.yield = (split l₁ ts).1.yield ++ (split l₁ ts).2.yield
  | [], _, _ => rfl
  | _ :: ss, _, .cons hd tl => by
    change hd.yield ++ tl.yield = (hd.yield ++ (split ss tl).1.yield) ++ (split ss tl).2.yield
    rw [yield_split ss tl, List.append_assoc]

private theorem CFParseTree.derives_yield {G : ContextFreeGrammar T} :
    ∀ {s : Symbol T G.NT} (t : CFParseTree G s), G.Derives [s] (t.yield.map .terminal)
  | _, .terminal _ => .refl _
  | _, .nonterminal (rhs := rhs) hrule children => by
    have hfirst : G.Produces [.nonterminal _] rhs := ⟨_, hrule, .input_output⟩
    have ih : ∀ i : Fin rhs.length, G.Derives [rhs[i]] ((children i).yield.map .terminal) :=
      fun i ↦ (children i).derives_yield
    suffices ∀ (l : List (Symbol T G.NT)) (ch : (i : Fin l.length) → CFParseTree G l[i]),
        (∀ i, G.Derives [l[i]] ((ch i).yield.map .terminal)) →
        G.Derives l ((List.ofFn fun i ↦ (ch i).yield).flatten.map .terminal) from
      hfirst.trans_derives (this rhs children ih)
    intro l
    induction l with
    | nil => intro _ _; exact .refl _
    | cons x xs ihl =>
      intro ch hch
      rw [List.ofFn_succ, List.flatten_cons, List.map_append]
      have h0 : G.Derives [x] ((ch 0).yield.map .terminal) := hch 0
      have htl := ihl (fun i ↦ ch i.succ) (fun i ↦ hch i.succ)
      simpa using (h0.append_right xs).trans (htl.append_left ((ch 0).yield.map .terminal))

private theorem exists_parseTree_of_mem_language {G : ContextFreeGrammar T} {w : List T}
    (hw : w ∈ G.language) :
    ∃ t : CFParseTree G (.nonterminal G.initial), t.yield = w := by
  rw [G.mem_language_iff w] at hw
  let HasTrees (u : List (Symbol T G.NT)) : Prop :=
    ∃ ts : CFTreeList G u, ts.yield = w
  have hbase : HasTrees (w.map .terminal) := by
    suffices ∀ v : List T, ∃ ts : CFTreeList G (v.map .terminal), ts.yield = v from this w
    intro v
    induction v with
    | nil => exact ⟨.nil, rfl⟩
    | cons a vs ih =>
      obtain ⟨ts_vs, hy_vs⟩ := ih
      exact ⟨.cons (.terminal a) ts_vs, congrArg ([a] ++ ·) hy_vs⟩
  have hstep : ∀ {x y : List (Symbol T G.NT)}, G.Produces x y → HasTrees y → HasTrees x := by
    intro x y ⟨r, hr, hrew⟩ ⟨tsy, hy_eq⟩
    obtain ⟨p, q, rfl, rfl⟩ := hrew.exists_parts
    let sp1 := CFTreeList.split (p ++ r.output) tsy
    let sp2 := CFTreeList.split p sp1.1
    let trA : CFParseTree G (.nonterminal r.input) := .nonterminal hr sp2.2.get
    let tsA : CFTreeList G [.nonterminal r.input] := .cons trA .nil
    refine ⟨(sp2.1.append tsA).append sp1.2, ?_⟩
    rw [CFTreeList.yield_append, CFTreeList.yield_append]
    have htrA_y : tsA.yield = sp2.2.yield := by
      change (List.ofFn fun i ↦ (sp2.2.get i).yield).flatten ++ [] = sp2.2.yield
      rw [List.append_nil, sp2.2.ofFn_get_yield]
    rw [htrA_y, ← CFTreeList.yield_split p sp1.1, ← CFTreeList.yield_split (p ++ r.output) tsy,
      hy_eq]
  have hder : ∀ {x y : List (Symbol T G.NT)}, G.Derives x y → HasTrees y → HasTrees x := by
    intro x y hxy
    induction hxy using Relation.ReflTransGen.head_induction_on with
    | refl => exact id
    | head hp _ ih => exact fun hy ↦ hstep hp (ih hy)
  obtain ⟨ts0, hy0⟩ := hder hw hbase
  cases ts0 with
  | cons t tl0 =>
    cases tl0 with
    | nil =>
      refine ⟨t, ?_⟩
      simpa using hy0

private theorem yield_length_le_pow_height {G : ContextFreeGrammar T} {M : ℕ}
    (hM_rules : ∀ r ∈ G.rules, r.output.length ≤ M) :
    ∀ {s : Symbol T G.NT} (t : CFParseTree G s), t.yield.length ≤ M ^ t.height
  | _, .terminal _ => by simp [CFParseTree.yield, CFParseTree.height]
  | _, .nonterminal (rhs := rhs) hrule children => by
    let H : ℕ := (Finset.univ : Finset (Fin rhs.length)).sup fun i ↦ (children i).height
    have hch_le : ∀ i : Fin rhs.length, (children i).yield.length ≤ M ^ H := by
      intro i
      have hi_ht : (children i).height ≤ H :=
        Finset.le_sup (f := fun j : Fin rhs.length ↦ (children j).height) (Finset.mem_univ i)
      by_cases hM0 : M = 0
      · subst hM0
        have hrhs0 : rhs.length = 0 := Nat.eq_zero_of_le_zero (hM_rules _ hrule)
        exact Fin.elim0 (hrhs0 ▸ i)
      · exact (yield_length_le_pow_height hM_rules (children i)).trans
          (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hM0) hi_ht)
    have hsum_le : ((List.ofFn fun i : Fin rhs.length ↦ (children i).yield).flatten).length ≤
        rhs.length * M ^ H := by
      suffices ∀ {k : ℕ} (f : Fin k → List T), (∀ i, (f i).length ≤ M ^ H) →
          (List.ofFn f).flatten.length ≤ k * M ^ H from this _ hch_le
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        intro f hf
        rw [List.ofFn_succ, List.flatten_cons, List.length_append, Nat.succ_mul, Nat.add_comm]
        exact Nat.add_le_add (ih (fun i ↦ f i.succ) (fun i ↦ hf i.succ)) (hf 0)
    calc (CFParseTree.nonterminal hrule children).yield.length
      _ ≤ rhs.length * M ^ H := hsum_le
      _ ≤ M * M ^ H := Nat.mul_le_mul_right _ (hM_rules _ hrule)
      _ = M ^ (1 + H) := by rw [Nat.add_comm, Nat.pow_succ, Nat.mul_comm]
      _ = M ^ (CFParseTree.nonterminal hrule children).height := rfl

private structure TreeCtx (G : ContextFreeGrammar T) (A B : G.NT) : Type u where
  plug : CFParseTree G (.nonterminal B) → CFParseTree G (.nonterminal A)
  left : List T
  right : List T
  extraNodes : ℕ
  yield_plug : ∀ t, (plug t).yield = left ++ t.yield ++ right
  nodeCount_plug : ∀ t, (plug t).nodeCount = extraNodes + t.nodeCount

private def TreeCtx.id (G : ContextFreeGrammar T) (A : G.NT) : TreeCtx G A A where
  plug := fun t ↦ t
  left := []
  right := []
  extraNodes := 0
  yield_plug := fun _ ↦ by simp
  nodeCount_plug := fun _ ↦ by simp

private def TreeCtx.comp {G : ContextFreeGrammar T} {A B C : G.NT}
    (c₁ : TreeCtx G A B) (c₂ : TreeCtx G B C) : TreeCtx G A C where
  plug := fun t ↦ c₁.plug (c₂.plug t)
  left := c₁.left ++ c₂.left
  right := c₂.right ++ c₁.right
  extraNodes := c₁.extraNodes + c₂.extraNodes
  yield_plug := fun t ↦ by simp [c₁.yield_plug, c₂.yield_plug, List.append_assoc]
  nodeCount_plug := fun t ↦ by simp [c₁.nodeCount_plug, c₂.nodeCount_plug, Nat.add_assoc]

private theorem exists_child_split {G : ContextFreeGrammar T} :
    ∀ {l : List (Symbol T G.NT)} (ts : CFTreeList G l),
      1 ≤ ts.maxHeight →
      ∃ (B : G.NT) (child : CFParseTree G (.nonterminal B))
        (plugL : CFParseTree G (.nonterminal B) → CFTreeList G l)
        (left right : List T) (extra : ℕ),
        child.height = ts.maxHeight ∧
        plugL child = ts ∧
        (∀ t, (plugL t).yield = left ++ t.yield ++ right) ∧
        (∀ t, (plugL t).nodeSum = extra + t.nodeCount)
  | [], .nil, hge => by rw [CFTreeList.maxHeight_nil] at hge; omega
  | .terminal a :: _, .cons hd tl, hge => by
    have hhd0 : hd.height = 0 := by cases hd; rfl
    have hmax : (CFTreeList.cons hd tl).maxHeight = tl.maxHeight := by
      rw [CFTreeList.maxHeight_cons, hhd0, Nat.zero_max]
    obtain ⟨B, child, plugTl, leftTl, rightTl, extraTl, hch_ht, hplugTl, hyTl, hncTl⟩ :=
      exists_child_split tl (by omega)
    refine ⟨B, child, fun t ↦ .cons hd (plugTl t), hd.yield ++ leftTl, rightTl,
      hd.nodeCount + extraTl, hch_ht.trans hmax.symm, congrArg (CFTreeList.cons hd) hplugTl,
      fun t ↦ ?_, fun t ↦ ?_⟩
    · simp only [CFTreeList.yield_cons, hyTl t, List.append_assoc]
    · rw [CFTreeList.nodeSum_cons, hncTl t, Nat.add_assoc]
  | .nonterminal B₀ :: _, .cons hd tl, hge => by
    by_cases hcmp : tl.maxHeight ≤ hd.height
    · have hmax : hd.height = (CFTreeList.cons hd tl).maxHeight := by
        rw [CFTreeList.maxHeight_cons]; exact (max_eq_left hcmp).symm
      refine ⟨B₀, hd, fun t ↦ .cons t tl, [], tl.yield, tl.nodeSum, hmax, rfl,
        fun t ↦ by simp,
        fun t ↦ by rw [CFTreeList.nodeSum_cons]; exact Nat.add_comm _ _⟩
    · have hmax : tl.maxHeight = (CFTreeList.cons hd tl).maxHeight := by
        rw [CFTreeList.maxHeight_cons]; exact (max_eq_right (Nat.le_of_not_ge hcmp)).symm
      have htl_ge : 1 ≤ tl.maxHeight := by
        rw [CFTreeList.maxHeight_cons] at hge; omega
      obtain ⟨B, child, plugTl, leftTl, rightTl, extraTl, hch_ht, hplugTl, hyTl, hncTl⟩ :=
        exists_child_split tl htl_ge
      refine ⟨B, child, fun t ↦ .cons hd (plugTl t), hd.yield ++ leftTl, rightTl,
        hd.nodeCount + extraTl, hch_ht.trans hmax, congrArg (CFTreeList.cons hd) hplugTl,
        fun t ↦ ?_, fun t ↦ ?_⟩
      · simp only [CFTreeList.yield_cons, hyTl t, List.append_assoc]
      · rw [CFTreeList.nodeSum_cons, hncTl t, Nat.add_assoc]

private theorem exists_max_step {G : ContextFreeGrammar T} {A : G.NT}
    {rhs : List (Symbol T G.NT)} (hrule : ⟨A, rhs⟩ ∈ G.rules)
    (children : (i : Fin rhs.length) → CFParseTree G rhs[i])
    (hge : 2 ≤ (CFParseTree.nonterminal hrule children).height) :
    ∃ (B : G.NT) (ctx : TreeCtx G A B) (child : CFParseTree G (.nonterminal B)),
      1 ≤ ctx.extraNodes ∧
      ctx.plug child = .nonterminal hrule children ∧
      (CFParseTree.nonterminal hrule children).height = 1 + child.height := by
  let ts := CFTreeList.ofChildren rhs children
  have hts_get : ts.get = children := CFTreeList.get_ofChildren rhs children
  have hsup_eq : (Finset.univ : Finset (Fin rhs.length)).sup (fun k ↦ (children k).height) =
      ts.maxHeight := by
    rw [← hts_get, ts.sup_get_height]
  have hmax_ge : 1 ≤ ts.maxHeight := by
    dsimp [CFParseTree.height] at hge; omega
  obtain ⟨B, child, plugL, left, right, extra, hch_ht, hplugL, hyL, hncL⟩ :=
    exists_child_split ts hmax_ge
  let ctx : TreeCtx G A B :=
    { plug := fun t ↦ .nonterminal hrule (plugL t).get
      left := left
      right := right
      extraNodes := 1 + extra
      yield_plug := fun t ↦ by
        change (List.ofFn fun i ↦ ((plugL t).get i).yield).flatten = _
        rw [(plugL t).ofFn_get_yield, hyL t]
      nodeCount_plug := fun t ↦ by
        dsimp [CFParseTree.nodeCount]
        rw [(plugL t).sum_get_nodeCount, hncL t, Nat.add_assoc] }
  refine ⟨B, ctx, child, by dsimp [ctx]; omega, ?_, ?_⟩
  · dsimp [ctx]; rw [hplugL, hts_get]
  · dsimp [CFParseTree.height]; omega

private theorem rep_flatten_comm {α : Type*} (l : List α) (m : ℕ) :
    l ++ (List.replicate m l).flatten = (List.replicate m l).flatten ++ l := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc l ++ (List.replicate (m + 1) l).flatten
      _ = l ++ (l ++ (List.replicate m l).flatten) := by
          rw [List.replicate_succ, List.flatten_cons]
      _ = l ++ ((List.replicate m l).flatten ++ l) := by rw [ih]
      _ = (l ++ (List.replicate m l).flatten) ++ l := (List.append_assoc _ _ _).symm
      _ = (List.replicate (m + 1) l).flatten ++ l := by
          rw [List.replicate_succ, List.flatten_cons]

private def TreeCtx.iter {G : ContextFreeGrammar T} {A : G.NT}
    (c : TreeCtx G A A) : ℕ → TreeCtx G A A
  | 0 => TreeCtx.id G A
  | m + 1 => c.comp (c.iter m)

private theorem TreeCtx.left_iter {G : ContextFreeGrammar T} {A : G.NT}
    (c : TreeCtx G A A) (m : ℕ) :
    (c.iter m).left = (List.replicate m c.left).flatten := by
  induction m with
  | zero => rfl
  | succ m ih => simp [TreeCtx.iter, TreeCtx.comp, List.replicate_succ, ih]

private theorem TreeCtx.right_iter {G : ContextFreeGrammar T} {A : G.NT}
    (c : TreeCtx G A A) (m : ℕ) :
    (c.iter m).right = (List.replicate m c.right).flatten := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [TreeCtx.iter, TreeCtx.comp, ih, List.replicate_succ, List.flatten_cons]
    exact (rep_flatten_comm c.right m).symm

private inductive Spine (G : ContextFreeGrammar T) : ℕ → G.NT → Type u
  | zero {B : G.NT} (t : CFParseTree G (.nonterminal B)) : Spine G 0 B
  | succ {d : ℕ} {B C : G.NT} (ctx : TreeCtx G B C) (hpos : 1 ≤ ctx.extraNodes)
      (tail : Spine G d C) : Spine G (d + 1) B

private def Spine.tree {G : ContextFreeGrammar T} :
    ∀ {d : ℕ} {B : G.NT}, Spine G d B → CFParseTree G (.nonterminal B)
  | 0, _, .zero t => t
  | _ + 1, _, .succ ctx _ tail => ctx.plug tail.tree

private def Spine.atIdx {G : ContextFreeGrammar T} :
    ∀ {d : ℕ} {B : G.NT}, Spine G d B → Fin (d + 1) → G.NT
  | 0, B, .zero _, _ => B
  | _ + 1, B, .succ _ _ tail, i => Fin.cases B (fun k ↦ tail.atIdx k) i

private def Spine.prefixSplit {G : ContextFreeGrammar T} :
    ∀ {d : ℕ} {B : G.NT} (sp : Spine G d B) (k : Fin (d + 1)),
      { pair : TreeCtx G B (sp.atIdx k) × CFParseTree G (.nonterminal (sp.atIdx k)) //
        pair.1.plug pair.2 = sp.tree ∧ (0 < k.val → 1 ≤ pair.1.extraNodes) }
  | 0, B, .zero t, ⟨0, _⟩ => ⟨(TreeCtx.id G B, t), rfl, fun h ↦ (Nat.lt_irrefl 0 h).elim⟩
  | _ + 1, B, .succ ctx _ tail, ⟨0, _⟩ =>
    ⟨(TreeCtx.id G B, ctx.plug tail.tree), rfl, fun h ↦ (Nat.lt_irrefl 0 h).elim⟩
  | d + 1, _, .succ ctx _ tail, ⟨k + 1, hk⟩ => by
    let k' : Fin (d + 1) := ⟨k, Nat.lt_of_succ_lt_succ hk⟩
    obtain ⟨⟨ctx_tl, sub_tl⟩, hplug_tl, _⟩ := tail.prefixSplit k'
    dsimp only at hplug_tl
    exact ⟨(ctx.comp ctx_tl, sub_tl), congrArg ctx.plug hplug_tl,
      fun _ ↦ by dsimp [TreeCtx.comp]; omega⟩

private theorem Spine.extractLoop {G : ContextFreeGrammar T} :
    ∀ {d : ℕ} {B : G.NT} (sp : Spine G d B) (i j : Fin (d + 1)),
      i < j → sp.atIdx i = sp.atIdx j →
      ∃ (A : G.NT) (outer : TreeCtx G B A) (loop : TreeCtx G A A)
        (inner : CFParseTree G (.nonterminal A)),
        1 ≤ loop.extraNodes ∧ outer.plug (loop.plug inner) = sp.tree
  | 0, _, _, i, j, hij, _ => by exfalso; omega
  | d + 1, B, .succ ctx hpos tail, ⟨0, _⟩, ⟨j + 1, hj⟩, _, heq => by
    let j' : Fin (d + 1) := ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    obtain ⟨⟨ctx_mid, inner⟩, hplug_mid, _⟩ := tail.prefixSplit j'
    dsimp only at hplug_mid
    obtain rfl : B = tail.atIdx j' := heq
    exact ⟨tail.atIdx j', TreeCtx.id G (tail.atIdx j'), ctx.comp ctx_mid, inner,
      by dsimp [TreeCtx.comp]; omega, congrArg ctx.plug hplug_mid⟩
  | d + 1, _, .succ ctx _ tail, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hij, heq => by
    let i' : Fin (d + 1) := ⟨i, Nat.lt_of_succ_lt_succ hi⟩
    let j' : Fin (d + 1) := ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    have hij' : i' < j' := Nat.lt_of_succ_lt_succ hij
    obtain ⟨A, outer', loop, inner, hloop_pos, hplug'⟩ := tail.extractLoop i' j' hij' heq
    exact ⟨A, ctx.comp outer', loop, inner, hloop_pos, congrArg ctx.plug hplug'⟩

private theorem extractSpine {G : ContextFreeGrammar T} :
    ∀ (d : ℕ) {B : G.NT} (t : CFParseTree G (.nonterminal B)),
      d + 1 ≤ t.height → ∃ sp : Spine G d B, sp.tree = t
  | 0, _, t, _ => ⟨.zero t, rfl⟩
  | d + 1, _, .nonterminal hrule children, hht => by
    obtain ⟨C, step0, childC, hstep0_pos, hstep0_eq, hht_eq⟩ :=
      exists_max_step hrule children (by omega)
    obtain ⟨sp_tl, hsp_tl⟩ := extractSpine d childC (by omega)
    exact ⟨.succ step0 hstep0_pos sp_tl, (congrArg step0.plug hsp_tl).trans hstep0_eq⟩

/-- **Bar-Hillel Pumping Lemma for Context-Free Grammars**: for any `G : ContextFreeGrammar T`,
let `p = (max 2 (G.rules.sup fun r ↦ r.output.length)) ^ (G.rules.card + 1)`. Every word
`w ∈ G.language` of length `≥ p` admits a decomposition `w = u ++ v ++ x ++ y ++ z` with
`1 ≤ (v ++ y).length`, `(v ++ x ++ y).length ≤ p`, and
`u ++ (List.replicate m v).flatten ++ x ++ (List.replicate m y).flatten ++ z ∈ G.language` for
every `m : ℕ`. -/
theorem pumping_lemma (G : ContextFreeGrammar T) :
    let M := max 2 (G.rules.sup fun r ↦ r.output.length)
    let p := M ^ (G.rules.card + 1)
    1 ≤ p ∧
    ∀ w ∈ G.language, p ≤ w.length →
      ∃ u v x y z : List T,
        w = u ++ v ++ x ++ y ++ z ∧
        1 ≤ (v ++ y).length ∧
        (v ++ x ++ y).length ≤ p ∧
        ∀ m : ℕ,
          u ++ (List.replicate m v).flatten ++ x ++ (List.replicate m y).flatten ++ z ∈
            G.language := by
  classical
  let M : ℕ := max 2 (G.rules.sup fun r ↦ r.output.length)
  let N : ℕ := G.rules.card
  let p : ℕ := M ^ (N + 1)
  have hM2 : 2 ≤ M := le_max_left _ _
  have hM_rules : ∀ r ∈ G.rules, r.output.length ≤ M := fun r hr ↦
    le_trans (Finset.le_sup (f := fun r ↦ r.output.length) hr) (le_max_right _ _)
  have hp_pos : 1 ≤ p := Nat.one_le_pow _ _ (by omega)
  refine ⟨hp_pos, fun w hw hpw ↦ ?_⟩
  change M ^ (N + 1) ≤ w.length at hpw
  let HasYieldOfSize (k : ℕ) : Prop :=
    ∃ t : CFParseTree G (.nonterminal G.initial), t.yield = w ∧ t.nodeCount = k
  have hne : ∃ k, HasYieldOfSize k := by
    obtain ⟨t, ht⟩ := exists_parseTree_of_mem_language hw
    exact ⟨t.nodeCount, t, ht, rfl⟩
  obtain ⟨t₀, ht₀_y, ht₀_min_eq⟩ := Nat.find_spec hne
  let IsMinTree : ∀ {A : G.NT}, CFParseTree G (.nonterminal A) → Prop :=
    fun {A} t ↦ ∀ t' : CFParseTree G (.nonterminal A),
      t'.yield = t.yield → t.nodeCount ≤ t'.nodeCount
  have ht₀_isMin : IsMinTree t₀ := fun t' ht' ↦
    ht₀_min_eq ▸ Nat.find_min' hne ⟨t', ht'.trans ht₀_y, rfl⟩
  have hmin_plug : ∀ {A B : G.NT} (ctx : TreeCtx G A B) (sub : CFParseTree G (.nonterminal B)),
      IsMinTree (ctx.plug sub) → IsMinTree sub := by
    intro A B ctx sub hmin t' ht'
    have h1 := hmin (ctx.plug t') (by simp [ctx.yield_plug, ht'])
    rw [ctx.nodeCount_plug, ctx.nodeCount_plug] at h1
    omega
  have hdescend : ∀ (h : ℕ) {B : G.NT} (sub : CFParseTree G (.nonterminal B)),
      sub.height = h → N + 1 ≤ h →
      ∃ (C : G.NT) (ctx : TreeCtx G B C) (target : CFParseTree G (.nonterminal C)),
        ctx.plug target = sub ∧ target.height = N + 1 := by
    intro h
    induction h using Nat.strong_induction_on with
    | _ h ih =>
      intro B sub hht hge
      by_cases heq : h = N + 1
      · exact ⟨B, TreeCtx.id G B, sub, rfl, hht.trans heq⟩
      · have hgt : N + 1 < h := by omega
        cases sub with
        | nonterminal hrule children =>
          obtain ⟨B', step0, chB', _, hstep0_eq, hht_step⟩ :=
            exists_max_step hrule children (by omega)
          have hchB'_ht : chB'.height = h - 1 := by omega
          obtain ⟨C, ctx_tl, target, hplug_tl, htgt_ht⟩ :=
            ih (h - 1) (by omega) chB' hchB'_ht (by omega)
          exact ⟨C, step0.comp ctx_tl, target,
            (congrArg step0.plug hplug_tl).trans hstep0_eq, htgt_ht⟩
  have ht₀_ht_ge : N + 1 ≤ t₀.height := by
    by_contra hlt
    have hw_le := ht₀_y ▸ yield_length_le_pow_height hM_rules t₀
    have hpow_lt : M ^ t₀.height < M ^ (N + 1) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  obtain ⟨C, topCtx, target, htop_plug, htgt_ht⟩ := hdescend t₀.height t₀ rfl ht₀_ht_ge
  have htgt_min : IsMinTree target := hmin_plug topCtx target (htop_plug.symm ▸ ht₀_isMin)
  have htgt_len_le : target.yield.length ≤ p := by
    have h1 := yield_length_le_pow_height hM_rules target
    rwa [htgt_ht] at h1
  obtain ⟨sp, hsp_tree⟩ := extractSpine N target (by omega)
  let activeNT : Finset G.NT := G.rules.image ContextFreeRule.input
  have hactive_tree : ∀ {B : G.NT} (tr : CFParseTree G (.nonterminal B)), B ∈ activeNT := by
    intro B tr
    cases tr with
    | nonterminal hrule _ => exact Finset.mem_image.mpr ⟨_, hrule, rfl⟩
  have hactive_sp : ∀ k : Fin (N + 1), sp.atIdx k ∈ activeNT := fun k ↦
    hactive_tree (sp.prefixSplit k).val.2
  let fAt : Fin (N + 1) → activeNT := fun k ↦ ⟨sp.atIdx k, hactive_sp k⟩
  have hlt_card : Fintype.card activeNT < Fintype.card (Fin (N + 1)) := by
    have hle : Fintype.card activeNT ≤ N := by
      rw [Fintype.card_coe]
      exact Finset.card_image_le
    rw [Fintype.card_fin]
    omega
  obtain ⟨i, j, hne_ij, hf_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt fAt hlt_card
  have hat_eq : sp.atIdx i = sp.atIdx j := congrArg Subtype.val hf_eq
  wlog hij : i < j generalizing i j
  · exact this j i hne_ij.symm hf_eq.symm hat_eq.symm
      (lt_of_le_of_ne (le_of_not_gt hij) hne_ij.symm)
  obtain ⟨A, midCtx, loop, inner, hloop_pos, hloop_plug⟩ := sp.extractLoop i j hij hat_eq
  have hfull_target : midCtx.plug (loop.plug inner) = target := hloop_plug.trans hsp_tree
  have hloop_min : IsMinTree (loop.plug inner) :=
    hmin_plug midCtx (loop.plug inner) (hfull_target.symm ▸ htgt_min)
  let u := topCtx.left ++ midCtx.left
  let v := loop.left
  let x := inner.yield
  let y := loop.right
  let z := midCtx.right ++ topCtx.right
  have hvy_pos : 1 ≤ (v ++ y).length := by
    by_contra h0
    rw [List.length_append] at h0
    have hv0 : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy0 : y = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy_same : inner.yield = (loop.plug inner).yield := by
      rw [loop.yield_plug]
      change x = v ++ x ++ y
      rw [hv0, hy0]; simp
    have hnc_le := hloop_min inner hy_same
    rw [loop.nodeCount_plug] at hnc_le
    omega
  have hvxy_le : (v ++ x ++ y).length ≤ p := by
    have h1 : target.yield = midCtx.left ++ (v ++ x ++ y) ++ midCtx.right := by
      rw [← hfull_target, midCtx.yield_plug, loop.yield_plug]
    have h2 := congrArg List.length h1
    simp only [List.length_append] at h2 ⊢
    omega
  have hw_decomp : w = u ++ v ++ x ++ y ++ z := by
    rw [← ht₀_y, ← htop_plug, topCtx.yield_plug, ← hfull_target, midCtx.yield_plug,
      loop.yield_plug]
    simp [u, v, x, y, z, List.append_assoc]
  refine ⟨u, v, x, y, z, hw_decomp, hvy_pos, hvxy_le, fun m ↦ ?_⟩
  let pumpedTree : CFParseTree G (.nonterminal G.initial) :=
    topCtx.plug (midCtx.plug ((loop.iter m).plug inner))
  have hpumped_y : pumpedTree.yield =
      u ++ (List.replicate m v).flatten ++ x ++ (List.replicate m y).flatten ++ z := by
    dsimp [pumpedTree]
    rw [topCtx.yield_plug, midCtx.yield_plug, (loop.iter m).yield_plug,
      loop.left_iter m, loop.right_iter m]
    simp [u, v, x, y, z, List.append_assoc]
  rw [← hpumped_y, G.mem_language_iff]
  exact pumpedTree.derives_yield

end Pumping

end ContextFreeGrammar

namespace Language

/-- **Bar-Hillel Pumping Lemma for Context-Free Languages**: every context-free language `L` admits
a pumping length `p ≥ 1` such that every `w ∈ L` with `p ≤ w.length` factors as
`w = u ++ v ++ x ++ y ++ z` with `1 ≤ (v ++ y).length`, `(v ++ x ++ y).length ≤ p`, and
`u ++ (List.replicate m v).flatten ++ x ++ (List.replicate m y).flatten ++ z ∈ L` for all
`m : ℕ`. -/
theorem exists_pumping_of_isContextFree {T : Type u} {L : _root_.Language T}
    (hL : L.IsContextFree) :
    ∃ p ≥ 1, ∀ w ∈ L, p ≤ w.length →
      ∃ u v x y z : List T,
        w = u ++ v ++ x ++ y ++ z ∧
        1 ≤ (v ++ y).length ∧
        (v ++ x ++ y).length ≤ p ∧
        ∀ m : ℕ,
          u ++ (List.replicate m v).flatten ++ x ++ (List.replicate m y).flatten ++ z ∈ L := by
  obtain ⟨G, rfl⟩ := hL
  obtain ⟨hp1, hpump⟩ := CslibFrontier.ContextFreeGrammar.pumping_lemma G
  exact ⟨_, hp1, hpump⟩

end Language

end CslibFrontier
