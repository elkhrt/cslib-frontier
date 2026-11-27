/-
Copyright (c) 2026 The FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Problems.UGraph
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.Set.Card

/-!
# Bounded-Degree Local CSP to Binary CSP Reduction

This module formalizes the textbook polynomial-time many-one reduction
(`Cslib.Complexity.PolyTimeReducible`) on `CslibFrontier` multi-tape Turing machines from
bounded-degree Local Constraint Satisfaction Problems to fixed-alphabet Binary Constraint
Satisfaction Problems via the classic dual/overlap neighborhood-coloring encoding:

1. **Certified self-delimiting unary header & runtime radix combinators**:
   `encodeUnaryHeader`, `nthUnaryHeader`, `computableInPolyTime_nthUnaryHeader'`,
   `computableInPolyTime_encodeUnaryHeader'`, and `computableInPolyTime_divPow'` (`a / c ^ r`).
2. **Bounded-Degree Local CSP & Binary CSP (`BoundedDegreeLocalCSP`, `BinaryCSP`)**:
   canonical finite problem instances on `Cslib.Complexity.UGraphInstance` with injective binary
   encodings `encBoundedDegreeLocalCSP` and `encBinaryCSP`.
3. **Polynomial-time Local-to-Binary CSP reduction
   (`polyTimeReducible_boundedDegreeLocalCSP_BinaryCSP`)**: for any closed-neighborhood size bound
   `1 ≤ maxClosedDeg` and alphabet size `c : ℕ`, `BoundedDegreeLocalCSP maxClosedDeg c` reduces in
   polynomial time to `BinaryCSP (c ^ maxClosedDeg)` (preserving the underlying graph whenever all
   local constraint sets are nonempty).

All results are proved under standard Lean axioms.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity SimpleGraph Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

/-! ### 1. Self-Delimiting Unary Header and Runtime Radix Combinators -/

/-- Self-delimiting unary encoding `1^k 0` of a natural number `k`. -/
@[expose]
def encodeUnaryHeader (k : ℕ) : List Bool :=
  List.replicate k true ++ [false]

@[simp]
theorem length_encodeUnaryHeader (k : ℕ) :
    (encodeUnaryHeader k).length = k + 1 := by
  simp [encodeUnaryHeader]

/-- Reads the `idx`-th `false`-delimited unary run length from a bit list `L`. -/
@[expose]
def nthUnaryHeader : List Bool → ℕ → ℕ
  | [], _ => 0
  | true :: rest, 0 => nthUnaryHeader rest 0 + 1
  | false :: _, 0 => 0
  | true :: rest, idx + 1 => nthUnaryHeader rest (idx + 1)
  | false :: rest, idx + 1 => nthUnaryHeader rest idx

@[simp]
theorem nthUnaryHeader_nil (idx : ℕ) : nthUnaryHeader [] idx = 0 := rfl

@[simp]
theorem nthUnaryHeader_true_zero (rest : List Bool) :
    nthUnaryHeader (true :: rest) 0 = nthUnaryHeader rest 0 + 1 := rfl

@[simp]
theorem nthUnaryHeader_false_zero (rest : List Bool) :
    nthUnaryHeader (false :: rest) 0 = 0 := rfl

@[simp]
theorem nthUnaryHeader_true_succ (rest : List Bool) (idx : ℕ) :
    nthUnaryHeader (true :: rest) (idx + 1) = nthUnaryHeader rest (idx + 1) := rfl

@[simp]
theorem nthUnaryHeader_false_succ (rest : List Bool) (idx : ℕ) :
    nthUnaryHeader (false :: rest) (idx + 1) = nthUnaryHeader rest idx := rfl

@[simp]
theorem nthUnaryHeader_encodeUnaryHeader_zero (k : ℕ) (rest : List Bool) :
    nthUnaryHeader (encodeUnaryHeader k ++ rest) 0 = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [encodeUnaryHeader, List.replicate_succ, List.cons_append, nthUnaryHeader]
    exact congrArg (· + 1) ih

@[simp]
theorem nthUnaryHeader_encodeUnaryHeader_succ (k idx : ℕ) (rest : List Bool) :
    nthUnaryHeader (encodeUnaryHeader k ++ rest) (idx + 1) = nthUnaryHeader rest idx := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [encodeUnaryHeader, List.replicate_succ, List.cons_append, nthUnaryHeader]
    exact ih

@[fun_prop]
theorem bool_not_comp {α : Type} {input : α ↪ List Bool} {f : α → Bool}
    (hf : ComputableInPolyTime f input encBool) :
    ComputableInPolyTime (fun x ↦ !(f x)) input encBool :=
  bool_not.comp hf

@[fun_prop]
theorem bool_and_comp {α : Type} {input : α ↪ List Bool} {f g : α → Bool}
    (hf : ComputableInPolyTime f input encBool)
    (hg : ComputableInPolyTime g input encBool) :
    ComputableInPolyTime (fun x ↦ f x && g x) input encBool :=
  bool_and.comp (hf.prod hg)

@[fun_prop]
theorem bool_or_comp {α : Type} {input : α ↪ List Bool} {f g : α → Bool}
    (hf : ComputableInPolyTime f input encBool)
    (hg : ComputableInPolyTime g input encBool) :
    ComputableInPolyTime (fun x ↦ f x || g x) input encBool :=
  bool_or.comp (hf.prod hg)

@[fun_prop]
theorem allWithInput_comp {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun p : γ × α ↦ test p.1 p.2)
      (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun x ↦ (list x).all (test x)) encIn encBool :=
  allWith htest id' hlist

@[fun_prop]
theorem unary_decide_eq_comp {α : Type} {input : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) :
    ComputableInPolyTime (fun x ↦ decide (f x = g x)) input encBool :=
  hf.decide_eq' hg

theorem nthUnaryHeader_zero_eq_idxOf (L : List Bool) :
    nthUnaryHeader L 0 = L.idxOf false := by
  induction L with
  | nil => simp
  | cons b xs ih =>
    cases b
    · simp
    · simp [ih]

/-- Single-header drop step `s ↦ s.drop (s.idxOf false + 1)`. -/
def dropHeaderStep (s : List Bool) : List Bool :=
  s.drop (s.idxOf false + 1)

private lemma nthUnaryHeader_dropHeaderStep (s : List Bool) (r : ℕ) :
    nthUnaryHeader (dropHeaderStep s) r = nthUnaryHeader s (r + 1) := by
  induction s with
  | nil => simp [dropHeaderStep]
  | cons b xs ih =>
    cases b
    · simp [dropHeaderStep]
    · have hidx : (true :: xs).idxOf false = xs.idxOf false + 1 := by simp
      simp only [dropHeaderStep, hidx, List.drop_succ_cons, nthUnaryHeader_true_succ]
      exact ih

theorem nthUnaryHeader_eq_iterate_idxOf (L : List Bool) (r : ℕ) :
    nthUnaryHeader L r = (dropHeaderStep^[r] L).idxOf false := by
  induction r generalizing L with
  | zero => exact nthUnaryHeader_zero_eq_idxOf L
  | succ r ih =>
    rw [Function.iterate_succ_apply, ← ih (dropHeaderStep L), nthUnaryHeader_dropHeaderStep]

private lemma length_iterate_dropHeaderStep_le (L : List Bool) (i : ℕ) :
    (dropHeaderStep^[i] L).length ≤ L.length := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (List.length_drop).trans_le ((Nat.sub_le _ _).trans ih)

@[fun_prop]
theorem computableInPolyTime_idxOf_false :
    ComputableInPolyTime (fun L : List Bool ↦ L.idxOf false) encBits encUnary :=
  idxOfWithInput (bits_encList_polyTime encBool).1 (const false)

@[fun_prop]
theorem computableInPolyTime_nthUnaryHeader :
    ComputableInPolyTime (fun p : List Bool × ℕ ↦ nthUnaryHeader p.1 p.2)
      (encPair encBits encUnary) encUnary := by
  have hstep : ComputableInPolyTime dropHeaderStep encBits encBits := by
    unfold dropHeaderStep
    exact bitsDropWithInput id' (unary_add' computableInPolyTime_idxOf_false (const 1))
  have hiter : ComputableInPolyTime
      (fun p : List Bool × ℕ ↦ dropHeaderStep^[p.2] p.1)
      (encPair encBits encUnary) encBits :=
    iterate (snd encBits encUnary) (fst encBits encUnary) hstep
      (bound := fun p ↦ (encPair encBits encUnary p).length) PolyBounded.self
      fun p i _ ↦ by
        simp only [encBits_apply, length_encPair]
        exact (length_iterate_dropHeaderStep_le p.1 i).trans (by omega)
  exact (computableInPolyTime_idxOf_false.comp hiter).of_enc_eq fun p ↦ by
    congr 1
    exact nthUnaryHeader_eq_iterate_idxOf p.1 p.2

@[fun_prop]
theorem computableInPolyTime_nthUnaryHeader' {α : Type} {input : α ↪ List Bool}
    {L : α → List Bool} {r : α → ℕ}
    (hL : ComputableInPolyTime L input encBits)
    (hr : ComputableInPolyTime r input encUnary) :
    ComputableInPolyTime (fun x ↦ nthUnaryHeader (L x) (r x)) input encUnary :=
  computableInPolyTime_nthUnaryHeader.comp (hL.prod hr)

@[fun_prop]
theorem computableInPolyTime_encodeUnaryHeader :
    ComputableInPolyTime encodeUnaryHeader encUnary encBits := by
  have hrep : ComputableInPolyTime (fun k : ℕ ↦ List.replicate k true) encUnary encBits :=
    of_eq fun _ ↦ rfl
  exact bitsAppend hrep (const [false])

@[fun_prop]
theorem computableInPolyTime_encodeUnaryHeader' {α : Type} {input : α ↪ List Bool} {k : α → ℕ}
    (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun x ↦ encodeUnaryHeader (k x)) input encBits :=
  computableInPolyTime_encodeUnaryHeader.comp hk

private lemma iterate_div_const (c a i : ℕ) :
    ((fun x : ℕ ↦ x / c)^[i] a) = a / c ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Nat.div_div_eq_div_mul, pow_succ]

@[fun_prop]
theorem computableInPolyTime_divPow (c : ℕ) :
    ComputableInPolyTime (fun p : ℕ × ℕ ↦ p.1 / c ^ p.2)
      (encPair encUnary encUnary) encUnary := by
  have hiter := iterate (snd encUnary encUnary) (fst encUnary encUnary) (unary_div_const c)
    (bound := fun p ↦ (encPair encUnary encUnary p).length) PolyBounded.self
    fun p i _ ↦ by
      simp only [encUnary_apply, List.length_replicate, length_encPair, iterate_div_const]
      have := Nat.div_le_self p.1 (c ^ i)
      omega
  exact hiter.of_enc_eq fun p ↦ by
    congr 1
    exact (iterate_div_const c p.1 p.2).symm

@[fun_prop]
theorem computableInPolyTime_divPow' (c : ℕ) {α : Type} {input : α ↪ List Bool}
    {f g : α → ℕ}
    (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) :
    ComputableInPolyTime (fun x ↦ f x / c ^ g x) input encUnary :=
  (computableInPolyTime_divPow c).comp (hf.prod hg)

/-! ### 2. Closed Neighborhoods, Binary CSP, and Bounded-Degree Local CSP -/

/-- Closed neighborhood `{u | u = v ∨ G.Adj v u}` of a vertex `v` in a simple graph `G`. -/
def closedNbrSet {V : Type*} (G : SimpleGraph V) (v : V) : Set V :=
  {u | u = v ∨ G.Adj v u}

@[simp]
theorem mem_closedNbrSet_iff {V : Type*} {G : SimpleGraph V} {v u : V} :
    u ∈ closedNbrSet G v ↔ u = v ∨ G.Adj v u := Iff.rfl

theorem mem_closedNbrSet_self {V : Type*} (G : SimpleGraph V) (v : V) :
    v ∈ closedNbrSet G v := Or.inl rfl

/-- Sorted vertex list of the closed neighborhood of `v` in `G : UGraphInstance`. -/
def closedNbrList (G : UGraphInstance) (v : Fin G.n) : List (Fin G.n) :=
  (List.finRange G.n).filter fun u ↦ decide (u = v) || G.adj v u

@[simp]
theorem mem_closedNbrList_iff {G : UGraphInstance} {v u : Fin G.n} :
    u ∈ closedNbrList G v ↔ u ∈ closedNbrSet G.graph v := by
  simp [closedNbrList, mem_closedNbrSet_iff]

theorem nodup_closedNbrList (G : UGraphInstance) (v : Fin G.n) :
    (closedNbrList G v).Nodup :=
  (List.nodup_finRange G.n).filter _

/-- Decode a natural number `idx` in base `c` (`0 < c`) as a local assignment on
`closedNbrSet G.graph v`. -/
def decodeLocalAssign (G : UGraphInstance) (v : Fin G.n) {c : ℕ}
    (hc : 0 < c) (idx : ℕ) (u : closedNbrSet G.graph v) : Fin c :=
  ⟨(idx / c ^ ((closedNbrList G v).idxOf u.1)) % c, Nat.mod_lt _ hc⟩

/-- Encode a local assignment `φ : closedNbrSet G.graph v → Fin c` as a base-`c` natural number. -/
def encodeLocalAssign (G : UGraphInstance) (v : Fin G.n) {c : ℕ}
    (φ : closedNbrSet G.graph v → Fin c) : ℕ :=
  ∑ j : Fin (closedNbrList G v).length,
    (φ ⟨(closedNbrList G v)[j.1]'j.2, mem_closedNbrList_iff.mp (List.getElem_mem j.2)⟩).1 *
      c ^ j.1

private lemma sum_digits_lt_pow {c m : ℕ} (d : Fin m → ℕ) (hd : ∀ j, d j < c) :
    ∑ j : Fin m, d j * c ^ j.1 < c ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc, pow_succ]
    have hlt := ih (fun i ↦ d i.castSucc) (fun i ↦ hd i.castSucc)
    have hmul : (d (Fin.last m) + 1) * c ^ m ≤ c * c ^ m :=
      Nat.mul_le_mul_right _ (hd (Fin.last m))
    simp only [Fin.val_castSucc, Fin.val_last] at hlt ⊢
    nlinarith

private lemma sum_digits_div_mod {c m : ℕ} (d : Fin m → ℕ) (hd : ∀ j, d j < c) (j : Fin m) :
    ((∑ i : Fin m, d i * c ^ i.1) / c ^ j.1) % c = d j := by
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    cases j using Fin.cases with
    | zero =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, Nat.div_one, mul_one, Fin.val_succ]
      have hdiv : c ∣ ∑ i : Fin m, d i.succ * c ^ (i.1 + 1) :=
        Finset.dvd_sum fun i _ ↦ by rw [pow_succ]; exact dvd_mul_of_dvd_right (dvd_mul_left c _) _
      rcases hdiv with ⟨q, hq⟩
      rw [hq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd 0)]
    | succ j =>
      have hc : 0 < c := Nat.pos_of_ne_zero fun h0 ↦ by have := hd 0; omega
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
      have hfactor : ∑ i : Fin m, d i.succ * c ^ (i.1 + 1) =
          c * ∑ i : Fin m, d i.succ * c ^ i.1 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ ↦ ?_; rw [pow_succ]; ring
      rw [hfactor, pow_succ', ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ hc, Nat.div_eq_of_lt (hd 0), zero_add]
      exact ih (fun i ↦ d i.succ) (fun i ↦ hd i.succ) j

theorem encodeLocalAssign_lt (G : UGraphInstance) (v : Fin G.n) {c : ℕ}
    (φ : closedNbrSet G.graph v → Fin c) :
    encodeLocalAssign G v φ < c ^ (closedNbrList G v).length :=
  sum_digits_lt_pow _ fun _ ↦ (φ _).2

theorem decodeLocalAssign_encodeLocalAssign (G : UGraphInstance) (v : Fin G.n)
    {c : ℕ} (hc : 0 < c) (φ : closedNbrSet G.graph v → Fin c) :
    decodeLocalAssign G v hc (encodeLocalAssign G v φ) = φ := by
  funext u; ext
  simp only [decodeLocalAssign, encodeLocalAssign]
  have hmem : u.1 ∈ closedNbrList G v := mem_closedNbrList_iff.mpr u.2
  set j : Fin (closedNbrList G v).length :=
    ⟨(closedNbrList G v).idxOf u.1, List.idxOf_lt_length_of_mem hmem⟩
  have hval := sum_digits_div_mod
    (fun i : Fin (closedNbrList G v).length ↦
      (φ ⟨(closedNbrList G v)[i.1]'i.2, mem_closedNbrList_iff.mp (List.getElem_mem i.2)⟩).1)
    (fun _ ↦ (φ _).2) j
  rw [hval]; congr 2; exact Subtype.ext (List.getElem_idxOf j.2)

/-- Finite `k`-color Binary CSP instance on an undirected graph `G : UGraphInstance` with symmetric
allowed color tables on edges. -/
@[ext]
structure BinaryCSPInstance (k : ℕ) where
  /-- Underlying constraint graph. -/
  graph : UGraphInstance
  /-- Allowed ordered color pairs `(a, b)` for each pair `(u, v)` (`false` off edges). -/
  allow : Fin graph.n → Fin graph.n → Fin k → Fin k → Bool
  /-- Non-edges carry `false` entries so the binary table is canonical. -/
  allow_of_not_adj : ∀ u v a b, ¬graph.graph.Adj u v → allow u v a b = false
  /-- Symmetry across undirected edges. -/
  allow_symm : ∀ u v a b, allow u v a b = allow v u b a

/-- A `BinaryCSPInstance k` is satisfiable if there is a `k`-coloring satisfying every edge. -/
def BinaryCSPInstance.IsSatisfiable {k : ℕ} (inst : BinaryCSPInstance k) : Prop :=
  ∃ col : Fin inst.graph.n → Fin k,
    ∀ u v : Fin inst.graph.n, inst.graph.graph.Adj u v → inst.allow u v (col u) (col v) = true

/-- Decision language of satisfiable `k`-color Binary CSP instances. -/
def BinaryCSP (k : ℕ) : Set (BinaryCSPInstance k) :=
  {inst | inst.IsSatisfiable}

/-- Computable bit-string encoding of `BinaryCSPInstance k`. -/
def encodeBinaryCSP {k : ℕ} (inst : BinaryCSPInstance k) : List Bool :=
  inst.graph.encode ++
    (List.finRange inst.graph.n).flatMap fun u ↦
      (List.finRange inst.graph.n).flatMap fun v ↦
        (List.finRange k).flatMap fun a ↦
          (List.finRange k).map fun b ↦ inst.allow u v a b

private lemma getD_append_left_of_lt {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α)
    (hi : i < l₁.length) : (l₁ ++ l₂).getD i d = l₁.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, Option.getD_some,
    List.getElem_append_left hi]

private lemma getD_append_right_of_le {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α)
    (hi : l₁.length ≤ i) : (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  by_cases hlt : i < (l₁ ++ l₂).length
  · have hlt2 : i - l₁.length < l₂.length := by simp at hlt; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt2, Option.getD_some,
      Option.getD_some, List.getElem_append_right hi]
  · have hge2 : l₂.length ≤ i - l₁.length := by simp at hlt; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]

private lemma flatMap_getD_of_const_length {α β : Type*} (L : List α) (f : α → List β)
    (m : ℕ) (hlen : ∀ a ∈ L, (f a).length = m) (i j : ℕ) (d : β)
    (hi : i < L.length) (hj : j < m) :
    (L.flatMap f).getD (i * m + j) d = (f (L[i]'hi)).getD j d := by
  induction L generalizing i with
  | nil => cases hi
  | cons a as ih =>
    have ha : (f a).length = m := hlen a List.mem_cons_self
    cases i with
    | zero =>
      simp only [List.flatMap_cons, zero_mul, zero_add, List.getElem_cons_zero]
      exact getD_append_left_of_lt _ _ _ _ (by rw [ha]; exact hj)
    | succ i =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [getD_append_right_of_le _ _ _ _ (by rw [ha]; nlinarith)]
      rw [show (i + 1) * m + j - (f a).length = i * m + j by rw [ha, Nat.add_one_mul]; omega]
      exact ih (fun b hb ↦ hlen b (List.mem_cons_of_mem a hb)) i (Nat.lt_of_succ_lt_succ hi)

private lemma nthUnaryHeader_ugraph_encode_append (G : UGraphInstance) (rest : List Bool) :
    nthUnaryHeader (G.encode ++ rest) 0 = G.n := by
  have heq : G.encode = encodeUnaryHeader G.n ++ adjacencyMatrix G.adj := by
    change List.replicate G.n true ++ false :: adjacencyMatrix G.adj = _
    rw [encodeUnaryHeader, List.append_assoc]; rfl
  rw [heq, List.append_assoc, nthUnaryHeader_encodeUnaryHeader_zero]

private lemma getD_ugraph_encode (G : UGraphInstance) (a b : Fin G.n) :
    G.encode.getD (G.n + 1 + (a.1 * G.n + b.1)) false = G.adj a b := by
  rw [List.getD_eq_getElem?_getD, G.getElem?_encode_matrix a.2 b.2, Option.getD_some]

theorem encodeBinaryCSP_injective (k : ℕ) : Function.Injective (encodeBinaryCSP (k := k)) := by
  intro i₁ i₂ h
  have hn : i₁.graph.n = i₂.graph.n := by
    have := congrArg (fun L ↦ nthUnaryHeader L 0) h
    simpa [encodeBinaryCSP, nthUnaryHeader_ugraph_encode_append] using this
  have hlen : i₁.graph.encode.length = i₂.graph.encode.length := by
    rw [i₁.graph.length_encode, i₂.graph.length_encode, hn]
  obtain ⟨hg_enc, hbits⟩ := List.append_inj h hlen
  have hg : i₁.graph = i₂.graph := UGraphInstance.encode_injective hg_enc
  rcases i₁ with ⟨G₁, al₁, hna₁, hsym₁⟩
  rcases i₂ with ⟨G₂, al₂, hna₂, hsym₂⟩
  dsimp only at hg hbits
  subst hg
  suffices hal : al₁ = al₂ by subst hal; rfl
  funext u v a b
  let f₃ (al : Fin G₁.n → Fin G₁.n → Fin k → Fin k → Bool) (u' v' : Fin G₁.n) (a' : Fin k) :=
    (List.finRange k).map fun b' ↦ al u' v' a' b'
  let f₂ (al : Fin G₁.n → Fin G₁.n → Fin k → Fin k → Bool) (u' v' : Fin G₁.n) :=
    (List.finRange k).flatMap (f₃ al u' v')
  let f₁ (al : Fin G₁.n → Fin G₁.n → Fin k → Fin k → Bool) (u' : Fin G₁.n) :=
    (List.finRange G₁.n).flatMap (f₂ al u')
  have hget : ∀ (al : Fin G₁.n → Fin G₁.n → Fin k → Fin k → Bool),
      ((List.finRange G₁.n).flatMap (f₁ al)).getD
        (((u.1 * G₁.n + v.1) * k + a.1) * k + b.1) false = al u v a b := fun al ↦ by
    have hb3 : a.1 * k + b.1 < k * k := by nlinarith [a.2, b.2]
    have hb2 : v.1 * (k * k) + (a.1 * k + b.1) < G₁.n * (k * k) := by nlinarith [v.2]
    rw [show ((u.1 * G₁.n + v.1) * k + a.1) * k + b.1 =
        u.1 * (G₁.n * (k * k)) + (v.1 * (k * k) + (a.1 * k + b.1)) by ring]
    rw [flatMap_getD_of_const_length _ (f₁ al) (G₁.n * (k * k))
      (fun _ _ ↦ by simp [f₁, f₂, f₃, List.length_flatMap, List.sum_replicate])
      u.1 _ false (by simp) hb2]
    have hfu : (List.finRange G₁.n)[u.1]'(by simp) = u := by ext; simp
    rw [hfu]
    rw [flatMap_getD_of_const_length _ (f₂ al u) (k * k)
      (fun _ _ ↦ by simp [f₂, f₃, List.length_flatMap, List.sum_replicate])
      v.1 _ false (by simp) hb3]
    have hfv : (List.finRange G₁.n)[v.1]'(by simp) = v := by ext; simp
    rw [hfv]
    rw [flatMap_getD_of_const_length _ (f₃ al u v) k (fun _ _ ↦ by simp [f₃])
      a.1 b.1 false (by simp) b.2]
    have hfa : (List.finRange k)[a.1]'(by simp) = a := by ext; simp
    rw [hfa]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [f₃, b.2]), Option.getD_some]
    simp only [f₃, List.getElem_map]
    have hfb : (List.finRange k)[b.1]'(by simp) = b := by ext; simp
    rw [hfb]
  have hcongr := congrArg
    (fun L ↦ L.getD (((u.1 * G₁.n + v.1) * k + a.1) * k + b.1) false) hbits
  rwa [hget al₁, hget al₂] at hcongr

/-- Computable binary embedding `BinaryCSPInstance k ↪ List Bool`. -/
@[expose]
def encBinaryCSP (k : ℕ) : BinaryCSPInstance k ↪ List Bool :=
  ⟨encodeBinaryCSP, encodeBinaryCSP_injective k⟩

/-- Instance of `c`-color Local CSP on graphs whose closed neighborhoods have size at most
`maxClosedDeg`. -/
structure BoundedDegreeLocalCSPInstance (maxClosedDeg c : ℕ) where
  /-- Underlying constraint graph. -/
  graph : UGraphInstance
  /-- Every closed neighborhood has size at most `maxClosedDeg`. -/
  closedDeg_le : ∀ v : Fin graph.n, (closedNbrList graph v).length ≤ maxClosedDeg
  /-- Allowed local colorings on each vertex's closed neighborhood. -/
  allow : ∀ v : Fin graph.n, Set (closedNbrSet graph.graph v → Fin c)

/-- Satisfiability of a `BoundedDegreeLocalCSPInstance`. -/
def BoundedDegreeLocalCSPInstance.IsSatisfiable {maxClosedDeg c : ℕ}
    (inst : BoundedDegreeLocalCSPInstance maxClosedDeg c) : Prop :=
  ∃ col : Fin inst.graph.n → Fin c,
    ∀ v : Fin inst.graph.n,
      (fun u : closedNbrSet inst.graph.graph v ↦ col u.1) ∈ inst.allow v

/-- Decision language of satisfiable `(maxClosedDeg, c)`-Local CSP instances. -/
def BoundedDegreeLocalCSP (maxClosedDeg c : ℕ) :
    Set (BoundedDegreeLocalCSPInstance maxClosedDeg c) :=
  {inst | inst.IsSatisfiable}

noncomputable def encodeBoundedDegreeLocalCSPBits {maxClosedDeg c : ℕ}
    (inst : BoundedDegreeLocalCSPInstance maxClosedDeg c) : List Bool :=
  (List.finRange inst.graph.n).flatMap fun v ↦
    (List.range (c ^ maxClosedDeg)).map fun idx ↦
      if hc : 0 < c then
        if idx < c ^ (closedNbrList inst.graph v).length then
          @decide (decodeLocalAssign inst.graph v hc idx ∈ inst.allow v)
            (Classical.propDecidable _)
        else false
      else false

noncomputable def encodeBoundedDegreeLocalCSP {maxClosedDeg c : ℕ}
    (inst : BoundedDegreeLocalCSPInstance maxClosedDeg c) : List Bool :=
  inst.graph.encode ++ encodeBoundedDegreeLocalCSPBits inst

theorem encodeBoundedDegreeLocalCSP_injective (maxClosedDeg c : ℕ) :
    Function.Injective (encodeBoundedDegreeLocalCSP (maxClosedDeg := maxClosedDeg) (c := c)) := by
  intro i₁ i₂ h
  have hn : i₁.graph.n = i₂.graph.n := by
    have := congrArg (fun L ↦ nthUnaryHeader L 0) h
    simpa [encodeBoundedDegreeLocalCSP, nthUnaryHeader_ugraph_encode_append] using this
  have hlen : i₁.graph.encode.length = i₂.graph.encode.length := by
    rw [i₁.graph.length_encode, i₂.graph.length_encode, hn]
  obtain ⟨hg_enc, hbits⟩ := List.append_inj h hlen
  have hg : i₁.graph = i₂.graph := UGraphInstance.encode_injective hg_enc
  rcases i₁ with ⟨G₁, hd₁, al₁⟩
  rcases i₂ with ⟨G₂, hd₂, al₂⟩
  dsimp only at hg hbits
  subst hg
  suffices hal : al₁ = al₂ by subst hal; rfl
  funext v
  ext φ
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · exact (φ ⟨v, mem_closedNbrSet_self _ v⟩).elim0
  · let idx := encodeLocalAssign G₁ v φ
    have hlt_len : idx < c ^ (closedNbrList G₁ v).length := encodeLocalAssign_lt G₁ v φ
    have hlt_bd : idx < c ^ maxClosedDeg :=
      lt_of_lt_of_le hlt_len (Nat.pow_le_pow_right hc (hd₁ v))
    have hget : ∀ (al : ∀ w : Fin G₁.n, Set (closedNbrSet G₁.graph w → Fin c)),
        (encodeBoundedDegreeLocalCSPBits ⟨G₁, hd₁, al⟩).getD
          (v.1 * c ^ maxClosedDeg + idx) false = true ↔
          decodeLocalAssign G₁ v hc idx ∈ al v := fun al ↦ by
      let f : Fin G₁.n → List Bool := fun w ↦
        (List.range (c ^ maxClosedDeg)).map fun j ↦
          if hc' : 0 < c then
            if j < c ^ (closedNbrList G₁ w).length then
              @decide (decodeLocalAssign G₁ w hc' j ∈ al w) (Classical.propDecidable _)
            else false
          else false
      change ((List.finRange G₁.n).flatMap f).getD (v.1 * c ^ maxClosedDeg + idx) false = true ↔ _
      rw [flatMap_getD_of_const_length _ f (c ^ maxClosedDeg)
        (fun _ _ ↦ by simp [f]) v.1 idx false (by simp) hlt_bd]
      have hfv : (List.finRange G₁.n)[v.1]'(by simp) = v := by ext; simp
      rw [hfv]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [f, hlt_bd]),
        Option.getD_some]
      simp [f, hc, hlt_len]
    have hbit := congrArg
      (fun L ↦ L.getD (v.1 * c ^ maxClosedDeg + idx) false = true) hbits
    have h1 := hget al₁
    have h2 := hget al₂
    rw [h1, h2, decodeLocalAssign_encodeLocalAssign G₁ v hc φ] at hbit
    exact hbit ▸ Iff.rfl

/-- Injective binary embedding `BoundedDegreeLocalCSPInstance maxClosedDeg c ↪ List Bool`. -/
@[expose]
noncomputable def encBoundedDegreeLocalCSP (maxClosedDeg c : ℕ) :
    BoundedDegreeLocalCSPInstance maxClosedDeg c ↪ List Bool :=
  ⟨encodeBoundedDegreeLocalCSP, encodeBoundedDegreeLocalCSP_injective maxClosedDeg c⟩

/-! ### 3. Polynomial-Time Reduction from Bounded-Degree Local CSP to Binary CSP -/

/-- Fixed unsatisfiable `K₂` `BinaryCSPInstance k`. -/
@[expose]
def unsatK2BinaryCSP (k : ℕ) : BinaryCSPInstance k where
  graph :=
    { n := 2
      adj := fun u v ↦ decide (u ≠ v)
      symm := fun u v ↦ by simp [ne_comm]
      loopless := fun u ↦ by simp }
  allow _ _ _ _ := false
  allow_of_not_adj _ _ _ _ _ := rfl
  allow_symm _ _ _ _ := rfl

theorem not_isSatisfiable_unsatK2BinaryCSP (k : ℕ) :
    ¬(unsatK2BinaryCSP k).IsSatisfiable := by
  rintro ⟨_, hcol⟩
  let u0 : Fin (unsatK2BinaryCSP k).graph.n := ⟨0, by dsimp [unsatK2BinaryCSP]; omega⟩
  let u1 : Fin (unsatK2BinaryCSP k).graph.n := ⟨1, by dsimp [unsatK2BinaryCSP]; omega⟩
  have hadj : (unsatK2BinaryCSP k).graph.graph.Adj u0 u1 := by
    rw [UGraphInstance.graph_adj]
    dsimp [unsatK2BinaryCSP, u0, u1]
    decide
  have hf := hcol u0 u1 hadj
  cases hf

/-- Same-graph `BinaryCSPInstance (c ^ maxClosedDeg)` induced by a `BoundedDegreeLocalCSPInstance`
(`0 < c`). -/
noncomputable def sameGraphBinaryCSP {maxClosedDeg c : ℕ} (hc : 0 < c)
    (inst : BoundedDegreeLocalCSPInstance maxClosedDeg c) :
    BinaryCSPInstance (c ^ maxClosedDeg) where
  graph := inst.graph
  allow u v a b :=
    inst.graph.adj u v &&
      @decide (a.1 < c ^ (closedNbrList inst.graph u).length ∧
        decodeLocalAssign inst.graph u hc a.1 ∈ inst.allow u) (Classical.propDecidable _) &&
      @decide (b.1 < c ^ (closedNbrList inst.graph v).length ∧
        decodeLocalAssign inst.graph v hc b.1 ∈ inst.allow v) (Classical.propDecidable _) &&
      @decide (∀ (z : Fin inst.graph.n)
        (hzu : z ∈ closedNbrSet inst.graph.graph u)
        (hzv : z ∈ closedNbrSet inst.graph.graph v),
        decodeLocalAssign inst.graph u hc a.1 ⟨z, hzu⟩ =
          decodeLocalAssign inst.graph v hc b.1 ⟨z, hzv⟩) (Classical.propDecidable _)
  allow_of_not_adj u v _ _ hna := by
    have hf : inst.graph.adj u v = false := Bool.eq_false_iff.mpr hna
    simp [hf]
  allow_symm u v a b := by
    rw [inst.graph.symm u v]
    by_cases hadj : inst.graph.adj v u = true
    · simp only [hadj, Bool.true_and]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, @decide_eq_true_eq _ (Classical.propDecidable _)]
      refine ⟨fun ⟨⟨ha, hb⟩, hagr⟩ ↦ ⟨⟨hb, ha⟩, fun z hzv hzu ↦ (hagr z hzu hzv).symm⟩,
        fun ⟨⟨hb, ha⟩, hagr⟩ ↦ ⟨⟨ha, hb⟩, fun z hzu hzv ↦ (hagr z hzv hzu).symm⟩⟩
    · have hf : inst.graph.adj v u = false := Bool.eq_false_iff.mpr hadj
      simp [hf]

/-- Exact satisfiability equivalence for `sameGraphBinaryCSP` when all local constraint sets are
nonempty. -/
theorem sameGraphBinaryCSP_isSatisfiable_iff {maxClosedDeg c : ℕ} (hc : 0 < c)
    (inst : BoundedDegreeLocalCSPInstance maxClosedDeg c)
    (hne : ∀ v : Fin inst.graph.n, (inst.allow v).Nonempty) :
    (sameGraphBinaryCSP hc inst).IsSatisfiable ↔ inst.IsSatisfiable := by
  constructor
  · rintro ⟨col', hcol'⟩
    let hasNbr (v : Fin inst.graph.n) : Prop := ∃ w, inst.graph.graph.Adj v w
    let _ := Classical.decPred hasNbr
    let col : Fin inst.graph.n → Fin c := fun v ↦
      if hasNbr v then
        decodeLocalAssign inst.graph v hc (col' v).1 ⟨v, mem_closedNbrSet_self _ v⟩
      else
        Classical.choose (hne v) ⟨v, mem_closedNbrSet_self _ v⟩
    refine ⟨col, fun v ↦ ?_⟩
    by_cases hv : hasNbr v
    · rcases hv with ⟨w₀, hvw₀⟩
      have hedge0 := hcol' v w₀ hvw₀
      dsimp only [sameGraphBinaryCSP] at hedge0
      simp only [Bool.and_eq_true, @decide_eq_true_eq _ (Classical.propDecidable _)] at hedge0
      have heq : (fun u : closedNbrSet inst.graph.graph v ↦ col u.1) =
          decodeLocalAssign inst.graph v hc (col' v).1 := by
        funext ⟨u, hu⟩
        rcases mem_closedNbrSet_iff.mp hu with rfl | hvu
        · simp [col, show hasNbr u from ⟨w₀, hvw₀⟩]
        · have hu_nbr : hasNbr u := ⟨v, hvu.symm⟩
          have hedge := hcol' v u hvu
          dsimp only [sameGraphBinaryCSP] at hedge
          simp only [Bool.and_eq_true, @decide_eq_true_eq _ (Classical.propDecidable _)] at hedge
          have hagr := hedge.2 u hu (mem_closedNbrSet_self _ u)
          simpa [col, hu_nbr] using hagr.symm
      rw [heq]; exact hedge0.1.1.2.2
    · have heq : (fun u : closedNbrSet inst.graph.graph v ↦ col u.1) =
          Classical.choose (hne v) := by
        funext ⟨u, hu⟩
        rcases mem_closedNbrSet_iff.mp hu with rfl | hvu
        · simp [col, hv]
        · exact (hv ⟨u, hvu⟩).elim
      rw [heq]; exact Classical.choose_spec (hne v)
  · rintro ⟨col, hcol⟩
    change ∃ col' : Fin inst.graph.n → Fin (c ^ maxClosedDeg),
      ∀ u v : Fin inst.graph.n, inst.graph.graph.Adj u v →
        (sameGraphBinaryCSP hc inst).allow u v (col' u) (col' v) = true
    let col' : Fin inst.graph.n → Fin (c ^ maxClosedDeg) := fun v ↦
      ⟨encodeLocalAssign inst.graph v (fun u ↦ col u.1),
        (encodeLocalAssign_lt inst.graph v _).trans_le
          (Nat.pow_le_pow_right hc (inst.closedDeg_le v))⟩
    refine ⟨col', fun u v huv ↦ ?_⟩
    dsimp only [sameGraphBinaryCSP, col']
    have hadj_b : inst.graph.adj u v = true := huv
    simp only [hadj_b, Bool.true_and, Bool.and_eq_true,
      @decide_eq_true_eq _ (Classical.propDecidable _)]
    refine ⟨⟨⟨encodeLocalAssign_lt _ _ _, ?_⟩, ⟨encodeLocalAssign_lt _ _ _, ?_⟩⟩, fun z _ _ ↦ ?_⟩
    · rw [decodeLocalAssign_encodeLocalAssign]; exact hcol u
    · rw [decodeLocalAssign_encodeLocalAssign]; exact hcol v
    · rw [decodeLocalAssign_encodeLocalAssign, decodeLocalAssign_encodeLocalAssign]

/-- Full reduction mapping `BoundedDegreeLocalCSPInstance maxClosedDeg c` (`0 < c`) to
`BinaryCSPInstance (c ^ maxClosedDeg)`. -/
noncomputable def localToBinaryCSP {maxClosedDeg c : ℕ} (hc : 0 < c)
    (inst : BoundedDegreeLocalCSPInstance maxClosedDeg c) :
    BinaryCSPInstance (c ^ maxClosedDeg) :=
  let _ := Classical.propDecidable (∀ v : Fin inst.graph.n, (inst.allow v).Nonempty)
  if ∀ v : Fin inst.graph.n, (inst.allow v).Nonempty then
    sameGraphBinaryCSP hc inst
  else
    unsatK2BinaryCSP (c ^ maxClosedDeg)

private lemma idxOf_filter_eq_length_filter_take {α : Type*} [BEq α] [LawfulBEq α]
    {l : List α} {p : α → Bool} {i : ℕ} (hi : i < l.length) (hnd : l.Nodup)
    (hp : p (l[i]'hi) = true) :
    (l.filter p).idxOf (l[i]'hi) = ((l.take i).filter p).length := by
  induction l generalizing i with
  | nil => cases hi
  | cons a xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hp ⊢
      simp [hp]
    | succ j =>
      simp only [List.getElem_cons_succ, List.take_succ_cons] at hp ⊢
      rw [List.nodup_cons] at hnd
      have hne : a ≠ xs[j]'(Nat.lt_of_succ_lt_succ hi) := fun h ↦
        hnd.1 (h ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hi))
      have hih := ih (Nat.lt_of_succ_lt_succ hi) hnd.2 hp
      cases hpa : p a with
      | false => simpa [List.filter_cons, hpa] using hih
      | true =>
        simp only [List.filter_cons, hpa, ↓reduceIte, List.length_cons, List.idxOf_cons]
        have hbeq : (a == xs[j]'(Nat.lt_of_succ_lt_succ hi)) = false := beq_false_of_ne hne
        simp [hbeq, hih]

private lemma idxOf_closedNbrList_eq_countP_range (G : UGraphInstance) (v w : Fin G.n)
    (hw : w ∈ closedNbrSet G.graph v) (q : ℕ → Bool)
    (hq : ∀ z : Fin G.n, q z.1 = true ↔ z = v ∨ G.graph.Adj v z) :
    (closedNbrList G v).idxOf w = (List.range w.1).countP q := by
  let p : Fin G.n → Bool := fun u ↦ decide (u = v) || G.adj v u
  have hpq : ∀ z : Fin G.n, p z = q z.1 := fun z ↦ by
    apply Bool.eq_iff_iff.mpr
    simp only [p, Bool.or_eq_true, decide_eq_true_eq, hq z]
    rfl
  have hget : (List.finRange G.n)[w.1]'(by simp) = w := by simp
  have hp : p ((List.finRange G.n)[w.1]'(by simp)) = true := by
    rw [hget]
    simp only [p, Bool.or_eq_true, decide_eq_true_eq]
    exact mem_closedNbrSet_iff.mp hw
  have hidx := idxOf_filter_eq_length_filter_take (l := List.finRange G.n) (p := p) (i := w.1)
    (by simp) (List.nodup_finRange G.n) hp
  rw [hget] at hidx
  dsimp only [closedNbrList]
  rw [hidx, ← List.countP_eq_length_filter]
  have hmap : ((List.finRange G.n).take w.1).map Fin.val = List.range w.1 :=
    List.ext_getElem (by simp) fun i hi _ ↦ by simp
  rw [← hmap, List.countP_map]
  exact List.countP_congr fun z _ ↦ by rw [Function.comp_apply, hpq z]

private lemma flatMap_finRange_eq_range {β : Type*} (n : ℕ) (f : Fin n → List β)
    (g : ℕ → List β) (h : ∀ i : Fin n, f i = g i.1) :
    (List.finRange n).flatMap f = (List.range n).flatMap g := by
  have hfin : (List.finRange n).map Fin.val = List.range n :=
    List.ext_getElem (by simp) fun i hi _ ↦ by simp
  rw [← hfin, List.flatMap_map]
  exact List.flatMap_congr fun i _ ↦ h i

private lemma map_finRange_eq_range {β : Type*} (n : ℕ) (f : Fin n → β) (g : ℕ → β)
    (h : ∀ i : Fin n, f i = g i.1) :
    (List.finRange n).map f = (List.range n).map g := by
  have hfin : (List.finRange n).map Fin.val = List.range n :=
    List.ext_getElem (by simp) fun i hi _ ↦ by simp
  rw [← hfin, List.map_map]
  exact List.map_congr_left fun i _ ↦ h i

/-- **Main Reduction Theorem**: for any positive closed-neighborhood size bound `1 ≤ maxClosedDeg`
and alphabet size `c : ℕ`, `BoundedDegreeLocalCSP maxClosedDeg c` is polynomial-time many-one
reducible to `BinaryCSP (c ^ maxClosedDeg)`. -/
theorem polyTimeReducible_boundedDegreeLocalCSP_BinaryCSP {maxClosedDeg : ℕ}
    (hd : 1 ≤ maxClosedDeg) (c : ℕ) :
    PolyTimeReducible (encBoundedDegreeLocalCSP maxClosedDeg c)
      (encBinaryCSP (c ^ maxClosedDeg))
      (BoundedDegreeLocalCSP maxClosedDeg c) (BinaryCSP (c ^ maxClosedDeg)) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · have hpow : 0 ^ maxClosedDeg = 0 := Nat.zero_pow (by omega)
    rw [hpow]
    let f0 : BoundedDegreeLocalCSPInstance maxClosedDeg 0 → BinaryCSPInstance 0 :=
      fun inst ↦ ⟨inst.graph, fun _ _ a _ ↦ a.elim0, fun _ _ a _ _ ↦ a.elim0,
        fun _ _ a _ ↦ a.elim0⟩
    let encFn : List Bool → List Bool := fun L ↦
      let n := nthUnaryHeader L 0
      L.take (n + 1 + n * n)
    have hEnc : ComputableInPolyTime encFn encBits encBits := by dsimp only [encFn]; fun_prop
    have hraw : ComputableInPolyTime (encBoundedDegreeLocalCSP maxClosedDeg 0)
        (encBoundedDegreeLocalCSP maxClosedDeg 0) encBits := of_eq fun _ ↦ rfl
    have hf0 : ComputableInPolyTime f0 (encBoundedDegreeLocalCSP maxClosedDeg 0)
        (encBinaryCSP 0) :=
      (hEnc.comp hraw).of_enc_eq fun inst ↦ by
        have hnil : ((List.finRange inst.graph.n).flatMap fun u ↦
            (List.finRange inst.graph.n).flatMap fun v ↦
              (List.finRange 0).flatMap fun a ↦
                (List.finRange 0).map fun b ↦ (f0 inst).allow u v a b) = [] :=
          List.eq_nil_of_length_eq_zero (by simp [List.length_flatMap, List.sum_replicate])
        change encodeBinaryCSP (f0 inst) = encFn (encodeBoundedDegreeLocalCSP inst)
        dsimp only [encodeBinaryCSP, f0, encFn, encodeBoundedDegreeLocalCSP]
        rw [hnil, List.append_nil, nthUnaryHeader_ugraph_encode_append,
          ← inst.graph.length_encode, List.take_left]
    refine ⟨f0, hf0, fun inst ↦ ?_⟩
    change inst.IsSatisfiable ↔ (f0 inst).IsSatisfiable
    simp only [BoundedDegreeLocalCSPInstance.IsSatisfiable, BinaryCSPInstance.IsSatisfiable, f0]
    exact ⟨fun ⟨col, _⟩ ↦ ⟨col, fun u _ _ ↦ (col u).elim0⟩,
      fun ⟨col, _⟩ ↦ ⟨col, fun v ↦ (col v).elim0⟩⟩
  · set k : ℕ := c ^ maxClosedDeg
    let getN : List Bool → ℕ := fun L ↦ nthUnaryHeader L 0
    let adjBit : List Bool → ℕ → ℕ → Bool := fun L u v ↦
      L.getD (getN L + 1 + (u * getN L + v)) false
    let allowBit : List Bool → ℕ → ℕ → Bool := fun L v idx ↦
      L.getD (getN L + 1 + getN L * getN L + (v * k + idx)) false
    let inNbr : List Bool → ℕ → ℕ → Bool := fun L x w ↦ decide (w = x) || adjBit L x w
    let rank : List Bool → ℕ → ℕ → ℕ := fun L x w ↦
      (List.range w).countP fun z ↦ inNbr L x z
    let digit : List Bool → ℕ → ℕ → ℕ → ℕ := fun L x a w ↦ (a / c ^ rank L x w) % c
    let agreeBit : List Bool → ℕ → ℕ → ℕ → ℕ → Bool := fun L u v a b ↦
      (List.range (getN L)).all fun w ↦
        !(inNbr L u w && inNbr L v w) || decide (digit L u a w = digit L v b w)
    let edgeBit : List Bool → ℕ → ℕ → ℕ → ℕ → Bool := fun L u v a b ↦
      adjBit L u v && allowBit L u a && allowBit L v b && agreeBit L u v a b
    let hasEmpty : List Bool → Bool := fun L ↦
      (List.range (getN L)).any fun v ↦ (List.range k).all fun idx ↦ !(allowBit L v idx)
    let graphBits : List Bool → List Bool := fun L ↦
      L.take (getN L + 1 + getN L * getN L)
    let binBits : List Bool → List Bool := fun L ↦
      (List.range (getN L)).flatMap fun u ↦
        (List.range (getN L)).flatMap fun v ↦
          (List.range k).flatMap fun a ↦
            (List.range k).map fun b ↦ edgeBit L u v a b
    let encFn : List Bool → List Bool := fun L ↦
      if hasEmpty L then encodeBinaryCSP (unsatK2BinaryCSP k)
      else graphBits L ++ binBits L
    have hHasEmpty : ComputableInPolyTime hasEmpty encBits encBool := by
      dsimp only [hasEmpty]
      have hN0 : ComputableInPolyTime getN encBits encUnary :=
        computableInPolyTime_nthUnaryHeader' id' (const 0)
      refine anyWithInput (range.comp hN0) ?_
      refine allWithInput_comp (range.comp (const k)) ?_
      let encE1 := encPair encBits encUnary
      let encE2 := encPair encE1 encUnary
      have hLE : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ ↦ q.1.1) encE2 encBits :=
        (fst encE1 encUnary).fst'
      have hVE : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ ↦ q.1.2) encE2 encUnary :=
        (fst encE1 encUnary).snd'
      have hIdxE : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ ↦ q.2) encE2 encUnary :=
        snd encE1 encUnary
      have hNE : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ ↦ getN q.1.1) encE2 encUnary :=
        hN0.comp hLE
      exact bool_not_comp <| bitsGetDWithInput hLE
        (unary_add' (unary_add' (unary_add' hNE (const 1)) (unary_mul' hNE hNE))
          (unary_add' (unary_mul' hVE (const k)) hIdxE)) false
    have hGraphBits : ComputableInPolyTime graphBits encBits encBits := by
      dsimp only [graphBits, getN]; fun_prop
    have hBinList : ComputableInPolyTime binBits encBits (encList encBool) := by
      dsimp only [binBits]
      let enc1 := encPair encBits encUnary
      let enc2 := encPair enc1 encUnary
      let enc3 := encPair enc2 encUnary
      let enc4 := encPair enc3 encUnary
      have hN0 : ComputableInPolyTime getN encBits encUnary :=
        computableInPolyTime_nthUnaryHeader' id' (const 0)
      have hL1 : ComputableInPolyTime (fun p : List Bool × ℕ ↦ p.1) enc1 encBits :=
        fst encBits encUnary
      have hN1 : ComputableInPolyTime (fun p : List Bool × ℕ ↦ getN p.1) enc1 encUnary :=
        hN0.comp hL1
      refine flatMapWithInput (range.comp hN0) ?_
      refine flatMapWithInput (range.comp hN1) ?_
      refine flatMapConst (List.range k) fun a _ ↦ ?_
      refine mapConst (List.range k) fun b _ ↦ ?_
      have hP2_1 : ComputableInPolyTime (fun p : (List Bool × ℕ) × ℕ ↦ p.1) enc2 enc1 :=
        fst enc1 encUnary
      have hL2 : ComputableInPolyTime (fun p : (List Bool × ℕ) × ℕ ↦ p.1.1) enc2 encBits :=
        hL1.comp hP2_1
      have hU2 : ComputableInPolyTime (fun p : (List Bool × ℕ) × ℕ ↦ p.1.2) enc2 encUnary :=
        (snd encBits encUnary).comp hP2_1
      have hV2 : ComputableInPolyTime (fun p : (List Bool × ℕ) × ℕ ↦ p.2) enc2 encUnary :=
        snd enc1 encUnary
      have hN2 : ComputableInPolyTime (fun p : (List Bool × ℕ) × ℕ ↦ getN p.1.1) enc2 encUnary :=
        hN0.comp hL2
      have hAdj : ComputableInPolyTime
          (fun p : (List Bool × ℕ) × ℕ ↦ adjBit p.1.1 p.1.2 p.2) enc2 encBool :=
        bitsGetDWithInput hL2
          (unary_add' (unary_add' hN2 (const 1)) (unary_add' (unary_mul' hU2 hN2) hV2)) false
      have hAllowU : ComputableInPolyTime
          (fun p : (List Bool × ℕ) × ℕ ↦ allowBit p.1.1 p.1.2 a) enc2 encBool :=
        bitsGetDWithInput hL2
          (unary_add' (unary_add' (unary_add' hN2 (const 1)) (unary_mul' hN2 hN2))
            (unary_add' (unary_mul' hU2 (const k)) (const a))) false
      have hAllowV : ComputableInPolyTime
          (fun p : (List Bool × ℕ) × ℕ ↦ allowBit p.1.1 p.2 b) enc2 encBool :=
        bitsGetDWithInput hL2
          (unary_add' (unary_add' (unary_add' hN2 (const 1)) (unary_mul' hN2 hN2))
            (unary_add' (unary_mul' hV2 (const k)) (const b))) false
      have hQ3_1 : ComputableInPolyTime
          (fun q : ((List Bool × ℕ) × ℕ) × ℕ ↦ q.1) enc3 enc2 := fst enc2 encUnary
      have hL3 := hL2.comp hQ3_1
      have hU3 := hU2.comp hQ3_1
      have hV3 := hV2.comp hQ3_1
      have hN3 := hN2.comp hQ3_1
      have hW3 : ComputableInPolyTime
          (fun q : ((List Bool × ℕ) × ℕ) × ℕ ↦ q.2) enc3 encUnary := snd enc2 encUnary
      have hInU : ComputableInPolyTime
          (fun q : ((List Bool × ℕ) × ℕ) × ℕ ↦ inNbr q.1.1.1 q.1.1.2 q.2) enc3 encBool :=
        bool_or_comp (unary_decide_eq_comp hW3 hU3)
          (bitsGetDWithInput hL3
            (unary_add' (unary_add' hN3 (const 1)) (unary_add' (unary_mul' hU3 hN3) hW3)) false)
      have hInV : ComputableInPolyTime
          (fun q : ((List Bool × ℕ) × ℕ) × ℕ ↦ inNbr q.1.1.1 q.1.2 q.2) enc3 encBool :=
        bool_or_comp (unary_decide_eq_comp hW3 hV3)
          (bitsGetDWithInput hL3
            (unary_add' (unary_add' hN3 (const 1)) (unary_add' (unary_mul' hV3 hN3) hW3)) false)
      have hR4_1 : ComputableInPolyTime
          (fun r : (((List Bool × ℕ) × ℕ) × ℕ) × ℕ ↦ r.1) enc4 enc3 := fst enc3 encUnary
      have hL4 := hL3.comp hR4_1
      have hU4 := hU3.comp hR4_1
      have hV4 := hV3.comp hR4_1
      have hN4 := hN3.comp hR4_1
      have hZ4 : ComputableInPolyTime
          (fun r : (((List Bool × ℕ) × ℕ) × ℕ) × ℕ ↦ r.2) enc4 encUnary := snd enc3 encUnary
      have hRankU : ComputableInPolyTime
          (fun q : ((List Bool × ℕ) × ℕ) × ℕ ↦ rank q.1.1.1 q.1.1.2 q.2) enc3 encUnary :=
        countPWithInput (range.comp hW3)
          (bool_or_comp (unary_decide_eq_comp hZ4 hU4)
            (bitsGetDWithInput hL4
              (unary_add' (unary_add' hN4 (const 1)) (unary_add' (unary_mul' hU4 hN4) hZ4)) false))
      have hRankV : ComputableInPolyTime
          (fun q : ((List Bool × ℕ) × ℕ) × ℕ ↦ rank q.1.1.1 q.1.2 q.2) enc3 encUnary :=
        countPWithInput (range.comp hW3)
          (bool_or_comp (unary_decide_eq_comp hZ4 hV4)
            (bitsGetDWithInput hL4
              (unary_add' (unary_add' hN4 (const 1)) (unary_add' (unary_mul' hV4 hN4) hZ4)) false))
      have hDigU : ComputableInPolyTime
          (fun q : ((List Bool × ℕ) × ℕ) × ℕ ↦ digit q.1.1.1 q.1.1.2 a q.2) enc3 encUnary :=
        unary_mod' (computableInPolyTime_divPow' c (const a) hRankU) (const c)
      have hDigV : ComputableInPolyTime
          (fun q : ((List Bool × ℕ) × ℕ) × ℕ ↦ digit q.1.1.1 q.1.2 b q.2) enc3 encUnary :=
        unary_mod' (computableInPolyTime_divPow' c (const b) hRankV) (const c)
      have hAgree : ComputableInPolyTime
          (fun p : (List Bool × ℕ) × ℕ ↦ agreeBit p.1.1 p.1.2 p.2 a b) enc2 encBool :=
        allWithInput_comp (range.comp hN2)
          (bool_or_comp (bool_not_comp (bool_and_comp hInU hInV))
            (unary_decide_eq_comp hDigU hDigV))
      exact bool_and_comp (bool_and_comp (bool_and_comp hAdj hAllowU) hAllowV) hAgree
    have hEncFn : ComputableInPolyTime encFn encBits encBits :=
      ComputableInPolyTime.ite hHasEmpty (const (encodeBinaryCSP (unsatK2BinaryCSP k)))
        (bitsAppend hGraphBits ((bits_encList_polyTime encBool).2.comp hBinList))
    have hraw : ComputableInPolyTime (encBoundedDegreeLocalCSP maxClosedDeg c)
        (encBoundedDegreeLocalCSP maxClosedDeg c) encBits := of_eq fun _ ↦ rfl
    have hf : ComputableInPolyTime (localToBinaryCSP hc)
        (encBoundedDegreeLocalCSP maxClosedDeg c) (encBinaryCSP k) := by
      refine (hEncFn.comp hraw).of_enc_eq fun inst ↦ ?_
      let L := encodeBoundedDegreeLocalCSP inst
      have hgetN : getN L = inst.graph.n := nthUnaryHeader_ugraph_encode_append inst.graph _
      have hadj_eq : ∀ u v : Fin inst.graph.n, adjBit L u.1 v.1 = inst.graph.adj u v :=
        fun u v ↦ by
          dsimp only [adjBit]
          rw [hgetN]
          dsimp only [L, encodeBoundedDegreeLocalCSP]
          rw [getD_append_left_of_lt _ _ _ _
            (by rw [inst.graph.length_encode]; nlinarith [u.2, v.2])]
          exact getD_ugraph_encode inst.graph u v
      have hallow_iff : ∀ (v : Fin inst.graph.n) (idx : ℕ), idx < k →
          (allowBit L v.1 idx = true ↔
            idx < c ^ (closedNbrList inst.graph v).length ∧
              decodeLocalAssign inst.graph v hc idx ∈ inst.allow v) := fun v idx hidx ↦ by
        dsimp only [allowBit]
        rw [hgetN]
        dsimp only [L, encodeBoundedDegreeLocalCSP]
        rw [getD_append_right_of_le _ _ _ _ (by rw [inst.graph.length_encode]; omega),
          inst.graph.length_encode, Nat.add_sub_cancel_left]
        let f : Fin inst.graph.n → List Bool := fun w ↦
          (List.range k).map fun j ↦
            if hc' : 0 < c then
              if j < c ^ (closedNbrList inst.graph w).length then
                @decide (decodeLocalAssign inst.graph w hc' j ∈ inst.allow w)
                  (Classical.propDecidable _)
              else false
            else false
        change ((List.finRange inst.graph.n).flatMap f).getD (v.1 * k + idx) false = true ↔ _
        rw [flatMap_getD_of_const_length _ f k (fun _ _ ↦ by simp [f]) v.1 idx false
          (by simp) hidx]
        have hfv : (List.finRange inst.graph.n)[v.1]'(by simp) = v := by ext; simp
        rw [hfv]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [f, hidx]),
          Option.getD_some]
        by_cases hlt : idx < c ^ (closedNbrList inst.graph v).length <;> simp [f, hc, hlt]
      have hEmpty_iff : hasEmpty L = true ↔ ¬∀ v : Fin inst.graph.n, (inst.allow v).Nonempty := by
        simp only [hasEmpty, hgetN, List.any_eq_true, List.mem_range, List.all_eq_true,
          Bool.not_eq_true', not_forall]
        constructor
        · rintro ⟨v, hv, hall⟩
          refine ⟨⟨v, hv⟩, fun ⟨φ, hφ⟩ ↦ ?_⟩
          have hlt : encodeLocalAssign inst.graph ⟨v, hv⟩ φ < k :=
            (encodeLocalAssign_lt inst.graph ⟨v, hv⟩ φ).trans_le
              (Nat.pow_le_pow_right hc (inst.closedDeg_le ⟨v, hv⟩))
          have ht : allowBit L v (encodeLocalAssign inst.graph ⟨v, hv⟩ φ) = true :=
            (hallow_iff ⟨v, hv⟩ _ hlt).mpr
              ⟨encodeLocalAssign_lt _ _ _,
                by simpa [decodeLocalAssign_encodeLocalAssign] using hφ⟩
          rw [hall _ hlt] at ht; cases ht
        · rintro ⟨v, hv⟩
          refine ⟨v.1, v.2, fun idx hidx ↦ Bool.eq_false_iff.mpr fun ht ↦ ?_⟩
          exact hv ⟨_, ((hallow_iff v idx hidx).mp ht).2⟩
      change encodeBinaryCSP (localToBinaryCSP hc inst) = encFn L
      dsimp only [localToBinaryCSP, encFn]
      split_ifs with hne hEf hEf'
      · exact absurd (hEmpty_iff.mp hEf) (not_not.mpr hne)
      · dsimp only [encodeBinaryCSP, sameGraphBinaryCSP]
        congr 1
        · dsimp only [graphBits]
          rw [hgetN]
          dsimp only [L, encodeBoundedDegreeLocalCSP]
          rw [← inst.graph.length_encode, List.take_left]
        · dsimp only [binBits]
          rw [hgetN]
          refine flatMap_finRange_eq_range inst.graph.n _ _ fun u ↦ ?_
          refine flatMap_finRange_eq_range inst.graph.n _ _ fun v ↦ ?_
          refine flatMap_finRange_eq_range k _ _ fun a ↦ ?_
          refine map_finRange_eq_range k _ _ fun b ↦ ?_
          apply Bool.eq_iff_iff.mpr
          have hrank_eq : ∀ (x w : Fin inst.graph.n), w ∈ closedNbrSet inst.graph.graph x →
              rank L x.1 w.1 = (closedNbrList inst.graph x).idxOf w := fun x w hw ↦
            (idxOf_closedNbrList_eq_countP_range inst.graph x w hw (inNbr L x.1) fun z ↦ by
              simp only [inNbr, Bool.or_eq_true, decide_eq_true_eq, hadj_eq, Fin.ext_iff]
              rfl).symm
          have hdigit_eq : ∀ (x w : Fin inst.graph.n) (hw : w ∈ closedNbrSet inst.graph.graph x)
              (idx : ℕ),
              digit L x.1 idx w.1 = (decodeLocalAssign inst.graph x hc idx ⟨w, hw⟩).1 :=
            fun x w hw idx ↦ by simp [digit, decodeLocalAssign, hrank_eq x w hw]
          have hagree_iff : agreeBit L u.1 v.1 a.1 b.1 = true ↔
              ∀ (z : Fin inst.graph.n) (hzu : z ∈ closedNbrSet inst.graph.graph u)
                (hzv : z ∈ closedNbrSet inst.graph.graph v),
                decodeLocalAssign inst.graph u hc a.1 ⟨z, hzu⟩ =
                  decodeLocalAssign inst.graph v hc b.1 ⟨z, hzv⟩ := by
            simp only [agreeBit, hgetN, List.all_eq_true, List.mem_range, Bool.or_eq_true,
              Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_true_eq]
            constructor
            · intro h z hzu hzv
              have hzw := h z.1 z.2
              have hu_in : inNbr L u.1 z.1 = true := by
                simp only [inNbr, Bool.or_eq_true, decide_eq_true_eq, hadj_eq]
                rcases mem_closedNbrSet_iff.mp hzu with rfl | h1
                · exact Or.inl rfl
                · exact Or.inr h1
              have hv_in : inNbr L v.1 z.1 = true := by
                simp only [inNbr, Bool.or_eq_true, decide_eq_true_eq, hadj_eq]
                rcases mem_closedNbrSet_iff.mp hzv with rfl | h1
                · exact Or.inl rfl
                · exact Or.inr h1
              rcases hzw with (hf | hf) | heq
              · rw [hu_in] at hf; cases hf
              · rw [hv_in] at hf; cases hf
              · exact Fin.ext (by rw [← hdigit_eq u z hzu a.1, ← hdigit_eq v z hzv b.1]; exact heq)
            · intro h w hw
              by_cases hu_in : inNbr L u.1 w = true
              · by_cases hv_in : inNbr L v.1 w = true
                · right
                  have hzu : (⟨w, hw⟩ : Fin inst.graph.n) ∈ closedNbrSet inst.graph.graph u := by
                    simp only [inNbr, Bool.or_eq_true, decide_eq_true_eq] at hu_in
                    rcases hu_in with h1 | h1
                    · exact Or.inl (Fin.ext h1)
                    · rw [show w = (⟨w, hw⟩ : Fin inst.graph.n).1 from rfl, hadj_eq u ⟨w, hw⟩] at h1
                      exact Or.inr ((UGraphInstance.graph_adj inst.graph).mpr h1)
                  have hzv : (⟨w, hw⟩ : Fin inst.graph.n) ∈ closedNbrSet inst.graph.graph v := by
                    simp only [inNbr, Bool.or_eq_true, decide_eq_true_eq] at hv_in
                    rcases hv_in with h1 | h1
                    · exact Or.inl (Fin.ext h1)
                    · rw [show w = (⟨w, hw⟩ : Fin inst.graph.n).1 from rfl, hadj_eq v ⟨w, hw⟩] at h1
                      exact Or.inr ((UGraphInstance.graph_adj inst.graph).mpr h1)
                  rw [hdigit_eq u ⟨w, hw⟩ hzu a.1, hdigit_eq v ⟨w, hw⟩ hzv b.1]
                  exact congrArg Fin.val (h ⟨w, hw⟩ hzu hzv)
                · exact Or.inl (Or.inr (Bool.eq_false_iff.mpr hv_in))
              · exact Or.inl (Or.inl (Bool.eq_false_iff.mpr hu_in))
          dsimp only [edgeBit]
          simp only [Bool.and_eq_true, @decide_eq_true_eq _ (Classical.propDecidable _),
            hadj_eq u v, hallow_iff u a.1 a.2, hallow_iff v b.1 b.2, hagree_iff]
      · rfl
      · exact absurd (hEmpty_iff.mpr hne) hEf'
    refine ⟨localToBinaryCSP hc, hf, fun inst ↦ ?_⟩
    change inst.IsSatisfiable ↔ (localToBinaryCSP hc inst).IsSatisfiable
    dsimp only [localToBinaryCSP]
    split_ifs with hne
    · exact (sameGraphBinaryCSP_isSatisfiable_iff hc inst hne).symm
    · refine ⟨fun ⟨col, hcol⟩ ↦ (hne fun v ↦ ⟨fun u ↦ col u.1, hcol v⟩).elim,
        fun h ↦ (not_isSatisfiable_unsatK2BinaryCSP _ h).elim⟩

end CslibFrontier.Complexity
