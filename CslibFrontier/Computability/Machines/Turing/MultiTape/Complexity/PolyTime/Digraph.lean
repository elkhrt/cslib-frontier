/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.StronglyConnected
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Foundations.NumberTheory.PrimeCounting
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial-Time Digraph, Boolean Matrix, and Prime-List Primitives

Reusable polynomial-time combinators for `Cslib.Complexity.DigraphInstance` (`encDigraph`),
raw bit-string Boolean matrix algebra and repeated squaring, transitive reachability,
Bellman–Ford shortest-path distance vectors, list GCD/LCM/sum/product, and unary prime
enumeration under `Turing.MultiTapeTM.ComputableInPolyTime`.

## Main definitions

* `CslibFrontier.Computability.PolyTime.Digraph.WalkLen`: fixed-length directed walks.
* `CslibFrontier.Computability.PolyTime.Digraph.boolMatGet`, `boolMatId`, `boolMatOr`,
  `boolMatMul`, `matPowStep`, `boolMatPow`: raw bit-string Boolean matrix algebra and
  repeated squaring.
* `CslibFrontier.Computability.PolyTime.Digraph.reachStep`, `reachMat`, `reachMatPos`:
  reflexive-transitive and transitive reachability matrices.
* `CslibFrontier.Computability.PolyTime.Digraph.bfStep`, `distVec`: Bellman–Ford
  shortest-path distance vector.
* `CslibFrontier.Computability.PolyTime.Digraph.listGcd`, `listLcm`, `listSumUnary`,
  `listProd`, `isPrimeBool`, `firstNPrimes`: polynomial-time list arithmetic and prime
  enumeration.

## Main results

* `computableInPolyTime_encDigraph_n`, `computableInPolyTime_encDigraph_matrix`,
  `computableInPolyTime_encDigraph_mk`: polynomial-time accessors and constructors for
  `Cslib.Complexity.encDigraph`.
* `boolMatGet_boolMatPow`, `computableInPolyTime_boolMatPow`: correctness and polynomial-time
  computability of Boolean matrix repeated squaring.
* `boolMatGet_reachMat`, `boolMatGet_reachMatPos`, `computableInPolyTime_reachMat`,
  `computableInPolyTime_reachMatPos`: correctness and polynomial-time computability of
  directed reachability.
* `computableInPolyTime_distVec`: polynomial-time computability of Bellman–Ford.
* `computableInPolyTime_binary_lcm`, `computableInPolyTime_listGcd`,
  `computableInPolyTime_listLcm`, `computableInPolyTime_listSumUnary`,
  `computableInPolyTime_listProd`, `isPrimeBool_eq_true_iff`,
  `computableInPolyTime_isPrimeBool`, `firstNPrimes_spec`,
  `computableInPolyTime_firstNPrimes`: polynomial-time list arithmetic and prime generation.
-/

public section

namespace CslibFrontier.Computability.PolyTime.Digraph

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-! ### Fixed-length walks -/

/-- A directed walk of exact length `k` from `u` to `v` along relation `R`. -/
inductive WalkLen {V : Type*} (R : V → V → Prop) : V → V → ℕ → Prop where
  | nil (u : V) : WalkLen R u u 0
  | cons {u v w : V} {k : ℕ} : R u v → WalkLen R v w k → WalkLen R u w (k + 1)

theorem WalkLen.trans {V : Type*} {R : V → V → Prop} {u v w : V} {k₁ k₂ : ℕ}
    (h₁ : WalkLen R u v k₁) (h₂ : WalkLen R v w k₂) : WalkLen R u w (k₁ + k₂) := by
  induction h₁ with
  | nil _ => simpa using h₂
  | cons hr _ ih =>
    rw [Nat.succ_add]
    exact .cons hr (ih h₂)

theorem WalkLen.snoc {V : Type*} {R : V → V → Prop} {u v w : V} {k : ℕ}
    (h : WalkLen R u v k) (hr : R v w) : WalkLen R u w (k + 1) :=
  h.trans (.cons hr (.nil w))

private theorem walkLen_succ_right {V : Type*} {R : V → V → Prop} {u v : V} {k : ℕ} :
    WalkLen R u v (k + 1) ↔ ∃ w : V, WalkLen R u w k ∧ R w v := by
  constructor
  · intro hw
    induction k generalizing u with
    | zero =>
      cases hw with
      | cons h1 h2 =>
        cases h2
        exact ⟨u, .nil u, h1⟩
    | succ k ih =>
      cases hw with
      | cons h1 h2 =>
        obtain ⟨w, hw1, hw2⟩ := ih h2
        exact ⟨w, .cons h1 hw1, hw2⟩
  · rintro ⟨w, hw1, hw2⟩
    exact hw1.snoc hw2

private theorem reflTransGen_iff_exists_walkLen {V : Type*} {R : V → V → Prop} {u v : V} :
    Relation.ReflTransGen R u v ↔ ∃ k : ℕ, WalkLen R u v k := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, .nil u⟩
    | tail _ hstep ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, hk.snoc hstep⟩
  · rintro ⟨k, hk⟩
    induction hk with
    | nil _ => exact .refl
    | cons hr _ ih => exact .head hr ih

/-! ### Polynomial-time accessors and constructor for `encDigraph` -/

private theorem idxOf_false_replicate_true_append_false (n : ℕ) (tail : List Bool) :
    (List.replicate n true ++ false :: tail).idxOf false = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, List.idxOf_cons]
    simp [ih]

/-- Extracting the vertex count `G.n` in unary from `encDigraph` takes polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_encDigraph_n :
    ComputableInPolyTime DigraphInstance.n encDigraph encUnary := by
  have hraw : ComputableInPolyTime (fun G : DigraphInstance => encDigraph G)
      encDigraph encBits := of_eq fun _ => rfl
  have hlist : ComputableInPolyTime (fun G : DigraphInstance => encDigraph G)
      encDigraph (encList encBool) := bitsToList.comp hraw
  have hidx : ComputableInPolyTime (fun G : DigraphInstance => (encDigraph G).idxOf false)
      encDigraph encUnary := (idxOf (enc := encBool)).comp (hlist.prod (const false))
  refine hidx.of_enc_eq fun G => ?_
  simp only [encDigraph_apply, DigraphInstance.encode,
    idxOf_false_replicate_true_append_false]

/-- Extracting the row-major `adjacencyMatrix G.adj` from `encDigraph` takes polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_encDigraph_matrix :
    ComputableInPolyTime (fun G : DigraphInstance => adjacencyMatrix G.adj)
      encDigraph encBits := by
  have hraw : ComputableInPolyTime (fun G : DigraphInstance => encDigraph G)
      encDigraph encBits := of_eq fun _ => rfl
  have hdrop := bitsDropWithInput hraw (unary_add' computableInPolyTime_encDigraph_n (const 1))
  refine hdrop.of_enc_eq fun G => ?_
  simp only [encDigraph_apply, DigraphInstance.encode, encBits_apply]
  rw [List.drop_append, List.length_replicate, List.drop_replicate]
  simp

/-- Constructing a `DigraphInstance` from a unary vertex count `n` and a polynomial-time edge
predicate `g` takes polynomial time in `encDigraph`. -/
theorem computableInPolyTime_encDigraph_mk {α : Type} {encIn : α ↪ List Bool}
    {n : α → ℕ} {g : α → ℕ → ℕ → Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hg : ComputableInPolyTime (fun p : (α × ℕ) × ℕ => g p.1.1 p.1.2 p.2)
      (encPair (encPair encIn encUnary) encUnary) encBool) :
    ComputableInPolyTime
      (fun a => ({ n := n a, adj := fun i j => g a i.val j.val } : DigraphInstance))
      encIn encDigraph := by
  have hmat : ComputableInPolyTime
      (fun a => (List.range (n a)).flatMap (fun u => (List.range (n a)).map (fun v => g a u v)))
      encIn encBits := by
    refine flatMapToBitsWithInput (range.comp hn) ?_
    exact mapToBitsWithInput (range.comp (hn.comp (fst encIn encUnary))) hg
  have hword : ComputableInPolyTime
      (fun a => List.replicate (n a) true ++ false ::
        ((List.range (n a)).flatMap (fun u => (List.range (n a)).map (fun v => g a u v))))
      encIn encBits := by
    have hcons : ComputableInPolyTime
        (fun a => [false] ++
          ((List.range (n a)).flatMap (fun u => (List.range (n a)).map (fun v => g a u v))))
        encIn encBits := bitsAppend (const [false]) hmat
    simpa only [Function.comp_def, List.singleton_append] using
      bitsAppend ((bitsReplicate true).comp hn) hcons
  refine hword.of_enc_eq fun a => ?_
  simp only [encDigraph_apply, DigraphInstance.encode, encBits_apply]
  rw [adjacencyMatrix_eq_flatMap _ (g a) (fun _ _ => rfl)]

/-! ### Boolean matrix algebra on raw bit strings -/

/-- Entry `(i, j)` of an `n × n` row-major Boolean matrix stored in a raw bit string. -/
@[expose] def boolMatGet (n : ℕ) (M : List Bool) (i j : ℕ) : Bool :=
  M.getD (i * n + j) false

/-- `n × n` identity Boolean matrix as a raw bit string. -/
@[expose] def boolMatId (n : ℕ) : List Bool :=
  (List.range n).flatMap fun i => (List.range n).map fun j => i == j

/-- Entrywise Boolean OR of two `n × n` Boolean matrices. -/
@[expose] def boolMatOr (n : ℕ) (A B : List Bool) : List Bool :=
  (List.range n).flatMap fun i => (List.range n).map fun j =>
    boolMatGet n A i j || boolMatGet n B i j

/-- Boolean matrix multiplication of two `n × n` row-major Boolean matrices. -/
@[expose] def boolMatMul (n : ℕ) (A B : List Bool) : List Bool :=
  (List.range n).flatMap fun i => (List.range n).map fun j =>
    (List.range n).any fun k => boolMatGet n A i k && boolMatGet n B k j

theorem length_flatMap_range_map (n : ℕ) (f : ℕ → ℕ → Bool) :
    ((List.range n).flatMap fun i => (List.range n).map fun j => f i j).length = n * n := by
  simp [List.length_flatMap]

theorem getD_flatMap_range_map (n : ℕ) (f : ℕ → ℕ → Bool) {i j : ℕ} (hi : i < n) (hj : j < n) :
    ((List.range n).flatMap fun a => (List.range n).map fun b => f a b).getD (i * n + j) false =
      f i j := by
  have heq : (List.range n).flatMap (fun a => (List.range n).map (fun b => f a b)) =
      adjacencyMatrix (fun a b : Fin n => f a.val b.val) :=
    (adjacencyMatrix_eq_flatMap _ f (fun _ _ => rfl)).symm
  rw [heq]
  exact getD_adjacencyMatrix (fun a b : Fin n => f a.val b.val) ⟨i, hi⟩ ⟨j, hj⟩

@[simp] theorem length_boolMatId (n : ℕ) : (boolMatId n).length = n * n :=
  length_flatMap_range_map n _

@[simp] theorem length_boolMatOr (n : ℕ) (A B : List Bool) : (boolMatOr n A B).length = n * n :=
  length_flatMap_range_map n _

@[simp] theorem length_boolMatMul (n : ℕ) (A B : List Bool) : (boolMatMul n A B).length = n * n :=
  length_flatMap_range_map n _

theorem boolMatGet_boolMatId {n i j : ℕ} (hi : i < n) (hj : j < n) :
    boolMatGet n (boolMatId n) i j = (i == j) :=
  getD_flatMap_range_map n _ hi hj

theorem boolMatGet_boolMatOr {n i j : ℕ} (A B : List Bool) (hi : i < n) (hj : j < n) :
    boolMatGet n (boolMatOr n A B) i j = (boolMatGet n A i j || boolMatGet n B i j) :=
  getD_flatMap_range_map n _ hi hj

theorem boolMatGet_boolMatMul {n i j : ℕ} (A B : List Bool) (hi : i < n) (hj : j < n) :
    boolMatGet n (boolMatMul n A B) i j =
      (List.range n).any fun k => boolMatGet n A i k && boolMatGet n B k j :=
  getD_flatMap_range_map n _ hi hj

@[fun_prop]
theorem computableInPolyTime_boolMatGet {α : Type} {encIn : α ↪ List Bool}
    {n i j : α → ℕ} {M : α → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hM : ComputableInPolyTime M encIn encBits)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun a => boolMatGet (n a) (M a) (i a) (j a)) encIn encBool := by
  unfold boolMatGet
  exact bitsGetDWithInput hM (unary_add' (unary_mul' hi hn) hj) false

@[fun_prop]
theorem computableInPolyTime_boolMatId :
    ComputableInPolyTime boolMatId encUnary encBits := by
  unfold boolMatId
  refine flatMapToBitsWithInput (range.comp id') ?_
  refine mapToBitsWithInput (range.comp (fst encUnary encUnary)) ?_
  fun_prop

@[fun_prop]
theorem computableInPolyTime_boolMatOr :
    ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => boolMatOr p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  unfold boolMatOr
  refine flatMapToBitsWithInput (range.comp (fst encUnary (encPair encBits encBits))) ?_
  refine mapToBitsWithInput
    (range.comp ((fst encUnary (encPair encBits encBits)).comp (fst _ _))) ?_
  unfold boolMatGet
  fun_prop

@[fun_prop]
theorem computableInPolyTime_boolMatMul :
    ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => boolMatMul p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  unfold boolMatMul
  refine flatMapToBitsWithInput (range.comp (fst encUnary (encPair encBits encBits))) ?_
  refine mapToBitsWithInput
    (range.comp ((fst encUnary (encPair encBits encBits)).comp (fst _ _))) ?_
  refine anyWithInput (range.comp ((fst encUnary (encPair encBits encBits)).comp
    ((fst _ _).comp (fst _ _)))) ?_
  unfold boolMatGet
  fun_prop

/-! ### Repeated squaring and directed reachability -/

/-- One repeated-squaring step over the binary digits (LSB-first) of `k`. -/
@[expose] def matPowStep (n : ℕ) (state : List Bool × List Bool) (bit : Bool) :
    List Bool × List Bool :=
  (if bit then boolMatMul n state.1 state.2 else state.1, boolMatMul n state.2 state.2)

/-- `A^k` (Boolean matrix power for binary `k : ℕ`). -/
@[expose] def boolMatPow (n : ℕ) (A : List Bool) (k : ℕ) : List Bool :=
  (k.bits.foldl (matPowStep n) (boolMatId n, A)).1

theorem boolMatGet_walkLen_iff {G : DigraphInstance} :
    ∀ {t : ℕ} {M : List Bool},
      (∀ i j : Fin G.n, boolMatGet G.n M i.val j.val = true ↔
        WalkLen (fun a b => G.adj a b = true) i j t) →
      ∀ {t' : ℕ} {M' : List Bool},
      (∀ i j : Fin G.n, boolMatGet G.n M' i.val j.val = true ↔
        WalkLen (fun a b => G.adj a b = true) i j t') →
      ∀ i j : Fin G.n, boolMatGet G.n (boolMatMul G.n M M') i.val j.val = true ↔
        WalkLen (fun a b => G.adj a b = true) i j (t + t') := by
  intro t M hM t' M' hM' i j
  rw [boolMatGet_boolMatMul M M' i.isLt j.isLt, List.any_eq_true]
  constructor
  · rintro ⟨k, hk, hboth⟩
    rw [List.mem_range] at hk
    rw [Bool.and_eq_true] at hboth
    exact ((hM i ⟨k, hk⟩).mp hboth.1).trans ((hM' ⟨k, hk⟩ j).mp hboth.2)
  · intro hw
    have hsplit : ∀ {a b : Fin G.n} {p q : ℕ},
        WalkLen (fun x y => G.adj x y = true) a b (p + q) →
        ∃ z : Fin G.n, WalkLen (fun x y => G.adj x y = true) a z p ∧
          WalkLen (fun x y => G.adj x y = true) z b q := by
      intro a b p q h
      induction p generalizing a with
      | zero => simp only [Nat.zero_add] at h; exact ⟨a, .nil a, h⟩
      | succ p ih =>
        rw [Nat.succ_add] at h
        cases h with
        | cons h1 h2 =>
          obtain ⟨z, hz1, hz2⟩ := ih h2
          exact ⟨z, .cons h1 hz1, hz2⟩
    obtain ⟨z, hz1, hz2⟩ := hsplit hw
    exact ⟨z.val, List.mem_range.mpr z.isLt,
      (Bool.and_eq_true _ _).mpr ⟨(hM i z).mpr hz1, (hM' z j).mpr hz2⟩⟩

theorem boolMatGet_boolMatPow (G : DigraphInstance) (k : ℕ) (i j : Fin G.n) :
    boolMatGet G.n (boolMatPow G.n (adjacencyMatrix G.adj) k) i.val j.val = true ↔
      WalkLen (fun a b => G.adj a b = true) i j k := by
  have hA : ∀ a b : Fin G.n, boolMatGet G.n (adjacencyMatrix G.adj) a.val b.val = G.adj a b :=
    fun a b => getD_adjacencyMatrix G.adj a b
  have hId : ∀ a b : Fin G.n,
      boolMatGet G.n (boolMatId G.n) a.val b.val = true ↔
        WalkLen (fun x y => G.adj x y = true) a b 0 := by
    intro a b
    rw [boolMatGet_boolMatId a.isLt b.isLt]
    simp only [beq_iff_eq, Fin.val_eq_val]
    exact ⟨fun h => h ▸ .nil a, fun h => by cases h; rfl⟩
  have hA_walk : ∀ a b : Fin G.n,
      boolMatGet G.n (adjacencyMatrix G.adj) a.val b.val = true ↔
        WalkLen (fun x y => G.adj x y = true) a b 1 := by
    intro a b
    rw [hA a b]
    constructor
    · intro h; exact .cons h (.nil b)
    · intro h; cases h with | cons h1 h2 => cases h2; exact h1
  have hinv : ∀ (l : List Bool),
      let st := l.foldl (matPowStep G.n) (boolMatId G.n, adjacencyMatrix G.adj)
      (∀ a b : Fin G.n, boolMatGet G.n st.1 a.val b.val = true ↔
        WalkLen (fun x y => G.adj x y = true) a b (ofBits l)) ∧
      (∀ a b : Fin G.n, boolMatGet G.n st.2 a.val b.val = true ↔
        WalkLen (fun x y => G.adj x y = true) a b (2 ^ l.length)) := by
    intro l
    induction l using List.reverseRecOn with
    | nil =>
      simp only [List.foldl_nil, ofBits, List.foldr_nil, List.length_nil, pow_zero]
      exact ⟨hId, hA_walk⟩
    | append_singleton l bit ih =>
      obtain ⟨h1, h2⟩ := ih
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, matPowStep]
      have hof : ofBits (l ++ [bit]) = ofBits l + if bit then 2 ^ l.length else 0 := by
        have hlen : ∀ (w : List Bool) (acc : ℕ),
            w.foldr (fun b n => Nat.bit b n) acc = ofBits w + 2 ^ w.length * acc := by
          intro w
          induction w with
          | nil => intro acc; simp [ofBits]
          | cons b w ihw =>
            intro acc
            simp only [ofBits, List.foldr_cons, List.length_cons] at ihw ⊢
            rw [ihw, ihw 0, Nat.add_zero]
            cases b <;> simp [Nat.bit, pow_succ] <;> ring
        simp only [ofBits, List.foldr_append, List.foldr_cons, List.foldr_nil]
        rw [hlen l (Nat.bit bit 0)]
        cases bit <;> simp [ofBits, Nat.bit_val]
      constructor
      · intro a b
        rw [hof]
        cases bit
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          exact h1 a b
        · simp only [↓reduceIte]
          exact boolMatGet_walkLen_iff h1 h2 a b
      · intro a b
        simp only [List.length_append, List.length_singleton, pow_succ, mul_two]
        exact boolMatGet_walkLen_iff h2 h2 a b
  have h := (hinv k.bits).1 i j
  simpa [boolMatPow, ofBits] using h

theorem computableInPolyTime_boolMatPow {α : Type} {encIn : α ↪ List Bool}
    {n k : α → ℕ} {A : α → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hA : ComputableInPolyTime A encIn encBits)
    (hk : ComputableInPolyTime k encIn encNat)
    (hAlen : ∀ a, (A a).length = n a * n a) :
    ComputableInPolyTime (fun a => boolMatPow (n a) (A a) (k a)) encIn encBits := by
  unfold boolMatPow
  have hbits : ComputableInPolyTime (fun a => (k a).bits) encIn encBits :=
    (of_eq (f := encNat) (encOut := encBits) fun _ => rfl).comp hk
  have hinit : ComputableInPolyTime (fun a => (boolMatId (n a), A a)) encIn
      (encPair encBits encBits) := (computableInPolyTime_boolMatId.comp hn).prod hA
  have hstep : ComputableInPolyTime
      (fun p : (ℕ × (List Bool × List Bool)) × Bool => matPowStep p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary (encPair encBits encBits)) encBool)
      (encPair encBits encBits) := by
    unfold matPowStep
    have hmul1 : ComputableInPolyTime
        (fun p : (ℕ × (List Bool × List Bool)) × Bool => boolMatMul p.1.1 p.1.2.1 p.1.2.2)
        (encPair (encPair encUnary (encPair encBits encBits)) encBool) encBits :=
      computableInPolyTime_boolMatMul.comp ((fst _ _).fst'.prod (fst _ _).snd')
    have hmul2 : ComputableInPolyTime
        (fun p : (ℕ × (List Bool × List Bool)) × Bool => boolMatMul p.1.1 p.1.2.2 p.1.2.2)
        (encPair (encPair encUnary (encPair encBits encBits)) encBool) encBits :=
      computableInPolyTime_boolMatMul.comp
        ((fst _ _).fst'.prod ((fst _ _).snd'.snd'.prod (fst _ _).snd'.snd'))
    exact ((snd _ _).ite' hmul1 (fst _ _).snd'.fst').prod hmul2
  have hlen_inv : ∀ a (l : List Bool),
      let st := l.foldl (matPowStep (n a)) (boolMatId (n a), A a)
      st.1.length = n a * n a ∧ st.2.length = n a * n a := by
    intro a l
    induction l using List.reverseRecOn with
    | nil => exact ⟨length_boolMatId (n a), hAlen a⟩
    | append_singleton l bit ih =>
      obtain ⟨h1, h2⟩ := ih
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, matPowStep]
      refine ⟨?_, length_boolMatMul _ _ _⟩
      cases bit <;> simp [h1, length_boolMatMul]
  have hB : PolyBounded (fun a => (encIn a).length) (fun a => 3 * (n a * n a) + 1) := by
    have hnn := (unary_mul' hn hn).polyBounded
    obtain ⟨c, d, hcd⟩ := hnn.exists_le
    refine PolyBounded.of_forall_le (3 * c + 1) d fun a => ?_
    have h := hcd a
    have hpow : 1 ≤ ((encIn a).length + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hfold := foldlWith (encA := encBool) (encL := encBits) (encB := encPair encBits encBits)
    (encP := encUnary) (par := n) (list := fun a => (k a).bits)
    (init := fun a => (boolMatId (n a), A a)) (step := matPowStep)
    hn hbits hinit hstep hB (fun a i _ => by
      obtain ⟨h1, h2⟩ := hlen_inv a ((k a).bits.take i)
      simp only [length_encPair, encBits_apply, h1, h2]
      omega)
  exact hfold.fst'

/-- One reachability-closure step: `M ↦ M ∨ (M * A)`. -/
def reachStep (n : ℕ) (A : List Bool) (M : List Bool) : List Bool :=
  boolMatOr n M (boolMatMul n M A)

/-- Reflexive-transitive reachability matrix of an `n × n` adjacency matrix `A`. -/
def reachMat (n : ℕ) (A : List Bool) : List Bool :=
  (reachStep n A)^[n] (boolMatId n)

/-- Transitive (positive-length) reachability matrix `A * reachMat n A`. -/
def reachMatPos (n : ℕ) (A : List Bool) : List Bool :=
  boolMatMul n A (reachMat n A)

theorem length_reachMat (n : ℕ) (A : List Bool) : (reachMat n A).length = n * n := by
  unfold reachMat
  suffices ∀ t, ((reachStep n A)^[t] (boolMatId n)).length = n * n from this n
  intro t
  induction t with
  | zero => exact length_boolMatId n
  | succ t _ => rw [Function.iterate_succ_apply']; exact length_boolMatOr _ _ _

theorem boolMatGet_reachMat (G : DigraphInstance) (i j : Fin G.n) :
    boolMatGet G.n (reachMat G.n (adjacencyMatrix G.adj)) i.val j.val = true ↔
      Relation.ReflTransGen (fun a b => G.adj a b = true) i j := by
  have hA : ∀ a b : Fin G.n, boolMatGet G.n (adjacencyMatrix G.adj) a.val b.val = G.adj a b :=
    fun a b => getD_adjacencyMatrix G.adj a b
  have hstep : ∀ (t : ℕ) (a b : Fin G.n),
      boolMatGet G.n ((reachStep G.n (adjacencyMatrix G.adj))^[t] (boolMatId G.n)) a.val b.val =
        true ↔ ∃ r ≤ t, WalkLen (fun x y => G.adj x y = true) a b r := by
    intro t
    induction t with
    | zero =>
      intro a b
      rw [Function.iterate_zero, id_eq, boolMatGet_boolMatId a.isLt b.isLt]
      simp only [beq_iff_eq, Fin.val_eq_val, Nat.le_zero, exists_eq_left]
      exact ⟨fun h => h ▸ .nil a, fun h => by cases h; rfl⟩
    | succ t ih =>
      intro a b
      rw [Function.iterate_succ_apply', reachStep, boolMatGet_boolMatOr _ _ a.isLt b.isLt,
          Bool.or_eq_true, ih a b, boolMatGet_boolMatMul _ _ a.isLt b.isLt, List.any_eq_true]
      constructor
      · rintro (⟨r, hr, hw⟩ | ⟨k, hk, hboth⟩)
        · exact ⟨r, by omega, hw⟩
        · rw [List.mem_range] at hk
          rw [Bool.and_eq_true] at hboth
          obtain ⟨r, hr, hw⟩ := (ih a ⟨k, hk⟩).mp hboth.1
          have hadj : G.adj ⟨k, hk⟩ b = true := by
            have := hA ⟨k, hk⟩ b; rw [hboth.2] at this; exact this.symm
          exact ⟨r + 1, by omega, hw.snoc hadj⟩
      · rintro ⟨r, hr, hw⟩
        by_cases hle : r ≤ t
        · exact Or.inl ⟨r, hle, hw⟩
        · have hreq : r = t + 1 := by omega
          subst hreq
          obtain ⟨w, hw1, hw2⟩ := walkLen_succ_right.mp hw
          refine Or.inr ⟨w.val, List.mem_range.mpr w.isLt, (Bool.and_eq_true _ _).mpr ⟨?_, ?_⟩⟩
          · exact (ih a w).mpr ⟨t, le_rfl, hw1⟩
          · rw [hA w b]; exact hw2
  rw [reachMat, hstep G.n i j, reflTransGen_iff_exists_walkLen]
  constructor
  · rintro ⟨r, -, hw⟩; exact ⟨r, hw⟩
  · rintro ⟨r, hw⟩
    have hex : ∃ m, WalkLen (fun a b => G.adj a b = true) i j m := ⟨r, hw⟩
    classical
    let d := Nat.find hex
    have hd : WalkLen (fun a b => G.adj a b = true) i j d := Nat.find_spec hex
    refine ⟨d, ?_, hd⟩
    by_contra hgt
    have hge : G.n ≤ d := by omega
    have hshort : ∃ d' < d, WalkLen (fun a b => G.adj a b = true) i j d' := by
      have hlist : ∀ {m : ℕ} {a b : Fin G.n}, WalkLen (fun x y => G.adj x y = true) a b m →
          ∃ (l : List (Fin G.n)) (hlen : l.length = m + 1), l[0]'(by omega) = a ∧
            l[m]'(by omega) = b ∧
            ∀ k : ℕ, (hk : k + 1 < l.length) → G.adj l[k] l[k + 1] = true := by
        intro m a b h
        induction h with
        | nil u => exact ⟨[u], rfl, rfl, rfl, fun _ hk => by simp at hk⟩
        | @cons x y z n hxy hyz ih =>
          obtain ⟨l, hlen, h0, hlast, hadj⟩ := ih
          refine ⟨x :: l, by simp [hlen], rfl, by simpa using hlast, fun k hk => ?_⟩
          cases k with
          | zero => simp only [List.getElem_cons_zero, List.getElem_cons_succ]; rw [h0]; exact hxy
          | succ k' =>
            simp only [List.getElem_cons_succ]
            exact hadj k' (by simp only [List.length_cons] at hk; omega)
      have hsub : ∀ {l : List (Fin G.n)},
          (∀ k : ℕ, (hk : k + 1 < l.length) → G.adj l[k] l[k + 1] = true) →
          ∀ {p q : ℕ} (hp : p ≤ q) (hq : q < l.length),
            WalkLen (fun x y => G.adj x y = true) (l[p]'(by omega)) (l[q]'hq) (q - p) := by
        intro l hadj p q hpq hq
        obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hpq
        induction s with
        | zero => simp only [add_zero, tsub_self]; exact .nil _
        | succ s ihs =>
          simpa [Nat.add_assoc] using (ihs (by omega) (by omega)).snoc (hadj (p + s) (by omega))
      obtain ⟨l, hlen, hl0, hld, hadj⟩ := hlist hd
      have hni : ¬Function.Injective (fun k : Fin (G.n + 1) => l[k.val]'(by omega)) :=
        fun hinj => by
          have := Fintype.card_le_of_injective _ hinj; simp at this
      rw [Function.Injective] at hni; push Not at hni
      obtain ⟨a, b, hab, hne⟩ := hni
      have hpair : ∃ (p q : ℕ) (_ : p < q) (_ : q ≤ d), l[p]'(by omega) = l[q]'(by omega) := by
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
        · exact ⟨a.val, b.val, h, by omega, hab⟩
        · exact ⟨b.val, a.val, h, by omega, hab.symm⟩
      obtain ⟨p, q, hpq, hqd, hlpq⟩ := hpair
      have h1 : WalkLen (fun x y => G.adj x y = true) i (l[p]'(by omega)) p := by
        simpa [hl0] using hsub hadj (Nat.zero_le p) (by omega)
      have h2 : WalkLen (fun x y => G.adj x y = true) (l[p]'(by omega)) j (d - q) := by
        rw [hlpq]; simpa [hld] using hsub hadj hqd (by omega)
      exact ⟨p + (d - q), by omega, h1.trans h2⟩
    obtain ⟨d', hd'lt, hd'w⟩ := hshort
    exact Nat.find_min hex hd'lt hd'w

theorem boolMatGet_reachMatPos (G : DigraphInstance) (i j : Fin G.n) :
    boolMatGet G.n (reachMatPos G.n (adjacencyMatrix G.adj)) i.val j.val = true ↔
      Relation.TransGen (fun a b => G.adj a b = true) i j := by
  rw [reachMatPos, boolMatGet_boolMatMul _ _ i.isLt j.isLt, List.any_eq_true]
  constructor
  · rintro ⟨k, hk, hboth⟩
    rw [List.mem_range] at hk; rw [Bool.and_eq_true] at hboth
    have hadj : G.adj i ⟨k, hk⟩ = true := by
      have := getD_adjacencyMatrix G.adj i ⟨k, hk⟩
      rw [← boolMatGet, hboth.1] at this; exact this.symm
    exact Relation.TransGen.head' hadj ((boolMatGet_reachMat G ⟨k, hk⟩ j).mp hboth.2)
  · intro htr
    cases htr using Relation.TransGen.head_induction_on with
    | single h =>
      refine ⟨j.val, List.mem_range.mpr j.isLt, (Bool.and_eq_true _ _).mpr ⟨?_, ?_⟩⟩
      · rw [boolMatGet, getD_adjacencyMatrix]; exact h
      · exact (boolMatGet_reachMat G j j).mpr .refl
    | @head _ c h1 h2 _ =>
      refine ⟨c.val, List.mem_range.mpr c.isLt, (Bool.and_eq_true _ _).mpr ⟨?_, ?_⟩⟩
      · rw [boolMatGet, getD_adjacencyMatrix]; exact h1
      · exact (boolMatGet_reachMat G c j).mpr h2.to_reflTransGen

private theorem computableInPolyTime_reachStep :
    ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => reachStep p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encBits) encBits) encBits := by
  have pN : ComputableInPolyTime (fun p : (ℕ × List Bool) × List Bool => p.1.1)
      (encPair (encPair encUnary encBits) encBits) encUnary :=
    (fst encUnary encBits).comp (fst (encPair encUnary encBits) encBits)
  have pA : ComputableInPolyTime (fun p : (ℕ × List Bool) × List Bool => p.1.2)
      (encPair (encPair encUnary encBits) encBits) encBits :=
    (snd encUnary encBits).comp (fst (encPair encUnary encBits) encBits)
  have pR : ComputableInPolyTime (fun p : (ℕ × List Bool) × List Bool => p.2)
      (encPair (encPair encUnary encBits) encBits) encBits :=
    snd (encPair encUnary encBits) encBits
  have hmul : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => boolMatMul p.1.1 p.2 p.1.2)
      (encPair (encPair encUnary encBits) encBits) encBits :=
    computableInPolyTime_boolMatMul.comp (pN.prod (pR.prod pA))
  exact computableInPolyTime_boolMatOr.comp (pN.prod (pR.prod hmul))

theorem computableInPolyTime_reachMat {α : Type} {encIn : α ↪ List Bool}
    {n : α → ℕ} {A : α → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hA : ComputableInPolyTime A encIn encBits) :
    ComputableInPolyTime (fun a => reachMat (n a) (A a)) encIn encBits := by
  unfold reachMat
  have hB : PolyBounded (fun a => (encIn a).length) (fun a => n a * n a) :=
    (unary_mul' hn hn).polyBounded
  have hinit : ComputableInPolyTime (fun a => boolMatId (n a)) encIn encBits :=
    computableInPolyTime_boolMatId.comp hn
  have hlen : ∀ a i, i ≤ n a →
      (encBits ((reachStep (n a) (A a))^[i] (boolMatId (n a)))).length ≤ n a * n a := by
    intro a i _
    rw [encBits_apply]
    suffices ∀ t, ((reachStep (n a) (A a))^[t] (boolMatId (n a))).length = n a * n a by
      rw [this i]
    intro t
    induction t with
    | zero => exact length_boolMatId (n a)
    | succ t _ => rw [Function.iterate_succ_apply']; exact length_boolMatOr _ _ _
  exact iterateWith (par := fun a => (n a, A a)) (count := n)
    (init := fun a => boolMatId (n a)) (step := fun p b => reachStep p.1 p.2 b)
    (hn.prod hA) hn hinit computableInPolyTime_reachStep hB hlen

theorem computableInPolyTime_reachMatPos {α : Type} {encIn : α ↪ List Bool}
    {n : α → ℕ} {A : α → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hA : ComputableInPolyTime A encIn encBits) :
    ComputableInPolyTime (fun a => reachMatPos (n a) (A a)) encIn encBits := by
  unfold reachMatPos
  exact computableInPolyTime_boolMatMul.comp
    (hn.prod (hA.prod (computableInPolyTime_reachMat hn hA)))

/-! ### Bellman–Ford shortest-path distance vectors -/

/-- One Bellman–Ford relaxation step over an `n × n` Boolean adjacency matrix `A`. -/
@[expose] def bfStep (n : ℕ) (A : List Bool) (dist : List ℕ) : List ℕ :=
  (List.range n).map fun v =>
    (List.range n).foldl (fun acc u =>
      if boolMatGet n A u v then min acc (dist.getD u (n + 1) + 1) else acc)
      (dist.getD v (n + 1))

/-- Bellman–Ford shortest-path distance vector from root `r` (capped at `n + 1`). -/
@[expose] def distVec (n : ℕ) (A : List Bool) (r : ℕ) : List ℕ :=
  (bfStep n A)^[n] ((List.range n).map fun v => if v == r then 0 else n + 1)

theorem computableInPolyTime_distVec {α : Type} {encIn : α ↪ List Bool}
    {n r : α → ℕ} {A : α → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hA : ComputableInPolyTime A encIn encBits)
    (hr : ComputableInPolyTime r encIn encUnary) :
    ComputableInPolyTime (fun a => distVec (n a) (A a) (r a)) encIn (encList encUnary) := by
  unfold distVec
  have hinit : ComputableInPolyTime
      (fun a => (List.range (n a)).map fun v => if v == r a then 0 else n a + 1)
      encIn (encList encUnary) := by
    refine mapWithInput (range.comp hn) ?_
    exact (unary_beq (snd _ _) (hr.comp (fst _ _))).ite' (const 0)
      (unary_add' (hn.comp (fst _ _)) (const 1))
  have hstep : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List ℕ => bfStep p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encBits) (encList encUnary)) (encList encUnary) := by
    unfold bfStep
    refine mapWithInput (range.comp (fst _ _).fst') ?_
    have hinner : ComputableInPolyTime
        (fun q : ((ℕ × List Bool) × List ℕ) × ℕ =>
          (List.range q.1.1.1).foldl (fun acc u =>
            if boolMatGet q.1.1.1 q.1.1.2 u q.2 then min acc (q.1.2.getD u (q.1.1.1 + 1) + 1)
            else acc) (q.1.2.getD q.2 (q.1.1.1 + 1)))
        (encPair (encPair (encPair encUnary encBits) (encList encUnary)) encUnary) encUnary := by
      have hfold_le : ∀ (q : ((ℕ × List Bool) × List ℕ) × ℕ) (k : ℕ),
          ((List.range q.1.1.1).take k).foldl (fun acc u =>
            if boolMatGet q.1.1.1 q.1.1.2 u q.2 then min acc (q.1.2.getD u (q.1.1.1 + 1) + 1)
            else acc) (q.1.2.getD q.2 (q.1.1.1 + 1)) ≤ q.1.2.getD q.2 (q.1.1.1 + 1) := by
        intro q k
        suffices ∀ (l : List ℕ) (init : ℕ),
            l.foldl (fun acc u =>
              if boolMatGet q.1.1.1 q.1.1.2 u q.2 then min acc (q.1.2.getD u (q.1.1.1 + 1) + 1)
              else acc) init ≤ init from this _ _
        intro l
        induction l with
        | nil => intro _; exact le_rfl
        | cons a l ih =>
          intro init
          simp only [List.foldl_cons]
          refine (ih _).trans ?_
          split_ifs
          · exact min_le_left _ _
          · exact le_rfl
      have hinit_inner : ComputableInPolyTime
          (fun q : ((ℕ × List Bool) × List ℕ) × ℕ => q.1.2.getD q.2 (q.1.1.1 + 1))
          (encPair (encPair (encPair encUnary encBits) (encList encUnary)) encUnary) encUnary := by
        have heq : (fun q : ((ℕ × List Bool) × List ℕ) × ℕ => q.1.2.getD q.2 (q.1.1.1 + 1)) =
            fun q => if decide (q.2 < q.1.2.length) then q.1.2.getD q.2 0 else q.1.1.1 + 1 := by
          funext q
          by_cases h : q.2 < q.1.2.length
          · simp [h]
          · simp [h, List.getD_eq_getElem?_getD]
        rw [heq]
        let eQ := encPair (encPair encUnary encBits) (encList encUnary)
        have hlt : ComputableInPolyTime
            (fun q : ((ℕ × List Bool) × List ℕ) × ℕ => decide (q.2 < q.1.2.length))
            (encPair eQ encUnary) encBool :=
          unary_lt' (snd eQ encUnary)
            ((length_list encUnary).comp ((snd (encPair encUnary encBits) (encList encUnary)).comp
              (fst eQ encUnary)))
        exact hlt.ite' (listGetDWithInput (fst eQ encUnary).snd' (snd eQ encUnary) 0)
          (unary_add' ((fst eQ encUnary).fst'.fst') (const 1))
      have hB : PolyBounded
          (fun q : ((ℕ × List Bool) × List ℕ) × ℕ =>
            (encPair (encPair (encPair encUnary encBits) (encList encUnary)) encUnary q).length)
          (fun q => q.1.2.getD q.2 (q.1.1.1 + 1)) :=
        hinit_inner.polyBounded
      have hstep_inner : ComputableInPolyTime
          (fun s : ((((ℕ × List Bool) × List ℕ) × ℕ) × ℕ) × ℕ =>
            if boolMatGet s.1.1.1.1.1 s.1.1.1.1.2 s.2 s.1.1.2 then
              min s.1.2 (s.1.1.1.2.getD s.2 (s.1.1.1.1.1 + 1) + 1)
            else s.1.2)
          (encPair (encPair (encPair (encPair (encPair encUnary encBits) (encList encUnary))
            encUnary) encUnary) encUnary) encUnary := by
        let e1 := encPair encUnary encBits
        let e2 := encPair e1 (encList encUnary)
        let e3 := encPair e2 encUnary
        let e4 := encPair e3 encUnary
        let p3 : ComputableInPolyTime (fun s : ((((ℕ × List Bool) × List ℕ) × ℕ) × ℕ) × ℕ => s.1.1)
            (encPair e4 encUnary) e3 := (fst e3 encUnary).comp (fst e4 encUnary)
        let p2 : ComputableInPolyTime
            (fun s : ((((ℕ × List Bool) × List ℕ) × ℕ) × ℕ) × ℕ => s.1.1.1)
            (encPair e4 encUnary) e2 := (fst e2 encUnary).comp p3
        let p1 : ComputableInPolyTime
            (fun s : ((((ℕ × List Bool) × List ℕ) × ℕ) × ℕ) × ℕ => s.1.1.1.1)
            (encPair e4 encUnary) e1 := (fst e1 (encList encUnary)).comp p2
        let pN := (fst encUnary encBits).comp p1
        let pA := (snd encUnary encBits).comp p1
        let pD := (snd e1 (encList encUnary)).comp p2
        let pV := (snd e2 encUnary).comp p3
        let pAcc := (snd e3 encUnary).comp (fst e4 encUnary)
        let pU := snd e4 encUnary
        have hget_u : ComputableInPolyTime
            (fun s : ((((ℕ × List Bool) × List ℕ) × ℕ) × ℕ) × ℕ =>
              s.1.1.1.2.getD s.2 (s.1.1.1.1.1 + 1))
            (encPair e4 encUnary) encUnary := by
          have heq : (fun s : ((((ℕ × List Bool) × List ℕ) × ℕ) × ℕ) × ℕ =>
              s.1.1.1.2.getD s.2 (s.1.1.1.1.1 + 1)) =
              fun s => if decide (s.2 < s.1.1.1.2.length) then s.1.1.1.2.getD s.2 0
                else s.1.1.1.1.1 + 1 := by
            funext s
            by_cases h : s.2 < s.1.1.1.2.length
            · simp [h]
            · simp [h, List.getD_eq_getElem?_getD]
          rw [heq]
          exact (unary_lt' pU ((length_list encUnary).comp pD)).ite'
            (listGetDWithInput pD pU 0) (unary_add' pN (const 1))
        have hcond : ComputableInPolyTime
            (fun s : ((((ℕ × List Bool) × List ℕ) × ℕ) × ℕ) × ℕ =>
              boolMatGet s.1.1.1.1.1 s.1.1.1.1.2 s.2 s.1.1.2)
            (encPair e4 encUnary) encBool :=
          computableInPolyTime_boolMatGet pN pA pU pV
        exact hcond.ite' (unary_min.comp (pAcc.prod (unary_add' hget_u (const 1)))) pAcc
      have hN_q : ComputableInPolyTime
          (fun q : ((ℕ × List Bool) × List ℕ) × ℕ => q.1.1.1)
          (encPair (encPair (encPair encUnary encBits) (encList encUnary)) encUnary) encUnary :=
        (fst encUnary encBits).comp
          ((fst (encPair encUnary encBits) (encList encUnary)).comp
            (fst (encPair (encPair encUnary encBits) (encList encUnary)) encUnary))
      have hlist_q : ComputableInPolyTime
          (fun q : ((ℕ × List Bool) × List ℕ) × ℕ => List.range q.1.1.1)
          (encPair (encPair (encPair encUnary encBits) (encList encUnary)) encUnary)
          (encList encUnary) :=
        ComputableInPolyTime.comp (f := List.range)
          (g := fun q : ((ℕ × List Bool) × List ℕ) × ℕ => q.1.1.1) range hN_q
      exact foldlWith (encA := encUnary) (encL := encList encUnary) (encB := encUnary)
        (par := id) (list := fun q => List.range q.1.1.1)
        (init := fun q => q.1.2.getD q.2 (q.1.1.1 + 1))
        (step := fun q acc u =>
          if boolMatGet q.1.1.1 q.1.1.2 u q.2 then min acc (q.1.2.getD u (q.1.1.1 + 1) + 1)
          else acc)
        id' hlist_q hinit_inner hstep_inner hB
        (fun q i _ => by
          simpa only [encUnary_apply, List.length_replicate, id_eq] using hfold_le q i)
    exact hinner
  have hlen_bf : ∀ a i,
      (encList encUnary ((bfStep (n a) (A a))^[i]
        ((List.range (n a)).map fun v => if v == r a then 0 else n a + 1))).length ≤
        n a * (2 * (n a + 1) + 1) := by
    intro a i
    have hinv : ∀ t,
        let d := (bfStep (n a) (A a))^[t]
          ((List.range (n a)).map fun v => if v == r a then 0 else n a + 1)
        d.length = n a ∧ ∀ x ∈ d, x ≤ n a + 1 := by
      intro t
      induction t with
      | zero =>
        refine ⟨by simp, fun x hx => ?_⟩
        simp only [Function.iterate_zero, id_eq, List.mem_map] at hx
        obtain ⟨_, _, rfl⟩ := hx
        split_ifs <;> omega
      | succ t ih =>
        obtain ⟨hl, hb⟩ := ih
        set d_t := (bfStep (n a) (A a))^[t]
          ((List.range (n a)).map fun v => if v == r a then 0 else n a + 1)
        rw [Function.iterate_succ_apply']
        refine ⟨by simp [bfStep], fun x hx => ?_⟩
        simp only [bfStep, List.mem_map, List.mem_range] at hx
        obtain ⟨v, hv, rfl⟩ := hx
        have hfold_le : ∀ (l : List ℕ) (acc : ℕ), acc ≤ n a + 1 →
            l.foldl (fun acc u =>
              if boolMatGet (n a) (A a) u v then min acc (d_t.getD u (n a + 1) + 1)
              else acc) acc ≤ n a + 1 := by
          intro l
          induction l with
          | nil => intro acc hacc; exact hacc
          | cons u l ih_l =>
            intro acc hacc
            simp only [List.foldl_cons]
            apply ih_l
            split_ifs
            · exact (min_le_left _ _).trans hacc
            · exact hacc
        apply hfold_le
        by_cases hlt : v < d_t.length
        · rw [List.getD_eq_getElem _ _ hlt]
          exact hb _ (List.getElem_mem hlt)
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt)]
          rfl
    obtain ⟨hl, hb⟩ := hinv i
    refine (length_encList_le encUnary _ (fun x hx => by
      simpa only [encUnary_apply, List.length_replicate] using hb x hx)).trans ?_
    rw [hl]
  have hB_bf : PolyBounded (fun a => (encIn a).length) (fun a => n a * (2 * (n a + 1) + 1)) := by
    have hp : ComputableInPolyTime (fun a => n a * (2 * (n a + 1) + 1)) encIn encUnary := by
      have h2 := unary_add' (unary_mul' (const 2) (unary_add' hn (const 1))) (const 1)
      exact unary_mul' hn h2
    exact hp.polyBounded
  exact iterateWith (step := fun p d => bfStep p.1 p.2 d)
    (hn.prod hA) hn hinit hstep hB_bf (fun a i _ => hlen_bf a i)

/-! ### Polynomial-time list arithmetic and prime enumeration -/

/-- List GCD on binary naturals (`l.foldl Nat.gcd 0`). -/
@[expose] def listGcd (l : List ℕ) : ℕ :=
  l.foldl Nat.gcd 0

/-- List LCM on binary naturals (`l.foldl Nat.lcm 1`). -/
@[expose] def listLcm (l : List ℕ) : ℕ :=
  l.foldl Nat.lcm 1

/-- Sum of a list of unary naturals. -/
@[expose] def listSumUnary (l : List ℕ) : ℕ :=
  l.foldl (· + ·) 0

/-- Product of a list of binary naturals. -/
@[expose] def listProd (l : List ℕ) : ℕ :=
  l.foldl (· * ·) 1

theorem listGcd_dvd_iff (d : ℕ) (l : List ℕ) :
    d ∣ listGcd l ↔ ∀ x ∈ l, d ∣ x := by
  unfold listGcd
  suffices ∀ (acc : ℕ), d ∣ l.foldl Nat.gcd acc ↔ d ∣ acc ∧ ∀ x ∈ l, d ∣ x by
    simpa [dvd_zero] using this 0
  induction l with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    simp only [List.foldl_cons, ih, Nat.dvd_gcd_iff, List.mem_cons, forall_eq_or_imp]
    tauto

theorem listSumUnary_append (l₁ l₂ : List ℕ) :
    listSumUnary (l₁ ++ l₂) = listSumUnary l₁ + listSumUnary l₂ := by
  unfold listSumUnary
  suffices ∀ (m : List ℕ) (acc : ℕ), m.foldl (· + ·) acc = acc + m.foldl (· + ·) 0 by
    rw [List.foldl_append, this l₂ (l₁.foldl (· + ·) 0)]
  intro m
  induction m with
  | nil => intro acc; simp
  | cons a m ih =>
    intro acc
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (acc + a), ih a]
    omega

theorem listProd_eq_prod (l : List ℕ) : listProd l = l.prod := by
  unfold listProd
  suffices ∀ (m : List ℕ) (acc : ℕ), m.foldl (· * ·) acc = acc * m.prod by
    simpa using this l 1
  intro m
  induction m with
  | nil => intro acc; simp
  | cons a m ih =>
    intro acc
    simp only [List.foldl_cons, List.prod_cons]
    rw [ih (acc * a), mul_assoc]

@[fun_prop]
theorem computableInPolyTime_binary_lcm :
    ComputableInPolyTime (fun p : ℕ × ℕ => Nat.lcm p.1 p.2) (encPair encNat encNat) encNat := by
  have heq : (fun p : ℕ × ℕ => Nat.lcm p.1 p.2) = fun p => (p.1 * p.2) / Nat.gcd p.1 p.2 := by
    funext p; exact Nat.lcm_eq_mul_div p.1 p.2
  rw [heq]
  exact binary_div' (binary_mul' (fst encNat encNat) (snd encNat encNat))
    (binary_gcd' (fst encNat encNat) (snd encNat encNat))

@[fun_prop]
theorem computableInPolyTime_listGcd :
    ComputableInPolyTime listGcd (encList encNat) encNat := by
  unfold listGcd
  have hbound : ∀ (l : List ℕ) (acc : ℕ),
      (encNat (l.foldl Nat.gcd acc)).length ≤
        max (encNat acc).length (encList encNat l).length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons a l ih =>
      intro acc
      simp only [List.foldl_cons, encList_cons, List.length_append, length_frame]
      refine (ih (Nat.gcd acc a)).trans ?_
      have hgcd_size : (encNat (Nat.gcd acc a)).length ≤
          max (encNat acc).length (encNat a).length := by
        simp only [encNat_apply, Nat.size_eq_bits_len]
        rcases Nat.eq_zero_or_pos acc with rfl | ha
        · simp
        · rcases Nat.eq_zero_or_pos a with rfl | hb
          · simp
          · exact le_trans (Nat.size_le_size (Nat.gcd_le_left a ha)) (le_max_left _ _)
      have ha_le : (encNat a).length ≤ 2 * (encNat a).length + 1 + (encList encNat l).length := by
        omega
      have hl_le : (encList encNat l).length ≤
          2 * (encNat a).length + 1 + (encList encNat l).length := by omega
      omega
  refine foldl' (encA := encNat) (encL := encList encNat) (encB := encNat)
    id' (const 0) binary_gcd (B := fun l => (encList encNat l).length) PolyBounded.self ?_
  intro l i _
  have h1 := hbound (l.take i) 0
  have h0 : (encNat 0).length = 0 := by simp [encNat_apply]
  rw [h0, Nat.zero_max] at h1
  exact h1.trans (by
    have htake : (encList encNat (l.take i)).length ≤ (encList encNat l).length := by
      conv_rhs => rw [← List.take_append_drop i l, encList_append, List.length_append]
      exact Nat.le_add_right _ _
    exact htake)

@[fun_prop]
theorem computableInPolyTime_listLcm :
    ComputableInPolyTime listLcm (encList encNat) encNat := by
  unfold listLcm
  have hstep : ∀ a b : ℕ, (Nat.lcm a b).size ≤ a.size + b.size := fun a b =>
    (Nat.size_le_size (by
      rw [Nat.lcm_eq_mul_div]; exact Nat.div_le_self _ _)).trans (Nat.size_mul_le a b)
  have hbound : ∀ (l : List ℕ) (acc : ℕ),
      (l.foldl Nat.lcm acc).size ≤ acc.size + (encList encNat l).length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons a l ih =>
      intro acc
      simp only [List.foldl_cons, encList_cons, List.length_append, length_frame,
        encNat_apply, Nat.size_eq_bits_len]
      have h1 := ih (Nat.lcm acc a)
      have h2 := hstep acc a
      omega
  refine foldl' (encA := encNat) (encL := encList encNat) (encB := encNat)
    id' (const 1) computableInPolyTime_binary_lcm
    (B := fun l => 1 + (encList encNat l).length)
    ((PolyBounded.const 1).add .self) ?_
  intro l i _
  simp only [encNat_apply, Nat.size_eq_bits_len]
  have h1 := hbound (l.take i) 1
  have hsz1 : (1 : ℕ).size = 1 := by decide
  rw [hsz1] at h1
  refine h1.trans ?_
  have htake : (encList encNat (l.take i)).length ≤ (encList encNat l).length := by
    conv_rhs => rw [← List.take_append_drop i l, encList_append, List.length_append]
    exact Nat.le_add_right _ _
  omega

@[fun_prop]
theorem computableInPolyTime_listSumUnary :
    ComputableInPolyTime listSumUnary (encList encUnary) encUnary := by
  unfold listSumUnary
  have hbound : ∀ (l : List ℕ) (acc : ℕ),
      l.foldl (· + ·) acc ≤ acc + (encList encUnary l).length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons a l ih =>
      intro acc
      simp only [List.foldl_cons, encList_cons, List.length_append, length_frame,
        encUnary_apply, List.length_replicate]
      have := ih (acc + a)
      omega
  refine foldl' (encA := encUnary) (encL := encList encUnary) (encB := encUnary)
    id' (const 0) unary_add (B := fun l => (encList encUnary l).length) PolyBounded.self ?_
  intro l i _
  simp only [encUnary_apply, List.length_replicate]
  have h1 := hbound (l.take i) 0
  rw [Nat.zero_add] at h1
  refine h1.trans ?_
  conv_rhs => rw [← List.take_append_drop i l, encList_append, List.length_append]
  exact Nat.le_add_right _ _

@[fun_prop]
theorem computableInPolyTime_listProd :
    ComputableInPolyTime listProd (encList encNat) encNat := by
  unfold listProd
  have hbound : ∀ (l : List ℕ) (acc : ℕ),
      (l.foldl (· * ·) acc).size ≤ acc.size + (encList encNat l).length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons a l ih =>
      intro acc
      simp only [List.foldl_cons, encList_cons, List.length_append, length_frame,
        encNat_apply, Nat.size_eq_bits_len]
      have h1 := ih (acc * a)
      have h2 := Nat.size_mul_le acc a
      omega
  refine foldl' (encA := encNat) (encL := encList encNat) (encB := encNat)
    id' (const 1) binary_mul (B := fun l => 1 + (encList encNat l).length)
    ((PolyBounded.const 1).add .self) ?_
  intro l i _
  simp only [encNat_apply, Nat.size_eq_bits_len]
  have h1 := hbound (l.take i) 1
  have hsz1 : (1 : ℕ).size = 1 := by decide
  rw [hsz1] at h1
  refine h1.trans ?_
  have htake : (encList encNat (l.take i)).length ≤ (encList encNat l).length := by
    conv_rhs => rw [← List.take_append_drop i l, encList_append, List.length_append]
    exact Nat.le_add_right _ _
  omega

/-- Unary trial-division primality test (via multiplication, avoiding division). -/
@[expose] def isPrimeBool (p : ℕ) : Bool :=
  decide (2 ≤ p) &&
  (List.range p).all fun d =>
    decide (d < 2) || (List.range p).all fun q => !(d * q == p)

theorem isPrimeBool_eq_true_iff (p : ℕ) : isPrimeBool p = true ↔ Nat.Prime p := by
  simp only [isPrimeBool, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, beq_iff_eq]
  constructor
  · rintro ⟨hp2, h⟩
    rw [Nat.prime_def_lt']
    refine ⟨hp2, fun d hd2 hdp hdvd => ?_⟩
    obtain ⟨q, hq⟩ := hdvd
    have hqp : q < p := by
      by_contra hge
      have : 2 * p ≤ d * q := Nat.mul_le_mul hd2 (Nat.le_of_not_lt hge)
      omega
    rcases h d hdp with hlt | hne
    · omega
    · exact hne q hqp hq.symm
  · intro hp
    refine ⟨hp.two_le, fun d hdp => ?_⟩
    by_cases hd2 : d < 2
    · exact Or.inl hd2
    · right
      intro q _ hmul
      have hdvd : d ∣ p := ⟨q, hmul.symm⟩
      rcases hp.eq_one_or_self_of_dvd d hdvd with rfl | rfl <;> omega

@[fun_prop]
theorem computableInPolyTime_isPrimeBool :
    ComputableInPolyTime isPrimeBool encUnary encBool := by
  unfold isPrimeBool
  have h1 : ComputableInPolyTime (fun p : ℕ => decide (2 ≤ p)) encUnary encBool :=
    unary_le' (const 2) id'
  have h2 : ComputableInPolyTime
      (fun p : ℕ => (List.range p).all fun d =>
        decide (d < 2) || (List.range p).all fun q => !(d * q == p))
      encUnary encBool := by
    refine allWithInput (range.comp id') ?_
    have hlt : ComputableInPolyTime (fun x : ℕ × ℕ => decide (x.2 < 2))
        (encPair encUnary encUnary) encBool :=
      unary_lt' (snd encUnary encUnary) (const 2)
    have hinner : ComputableInPolyTime
        (fun x : ℕ × ℕ => (List.range x.1).all fun q => !(x.2 * q == x.1))
        (encPair encUnary encUnary) encBool := by
      refine allWithInput (range.comp (fst encUnary encUnary)) ?_
      let e := encPair encUnary encUnary
      let pP := (fst encUnary encUnary).comp (fst e encUnary)
      let pD := (snd encUnary encUnary).comp (fst e encUnary)
      let pQ := snd e encUnary
      exact bool_not.comp (unary_beq (unary_mul' pD pQ) pP)
    exact bool_or' hlt hinner
  exact bool_and' h1 h2

/-- Generate the first `N` primes in unary. -/
def firstNPrimes (N : ℕ) : List ℕ :=
  let allP := (List.range ((N + 1) * (2 * N + 4) + 1)).filter isPrimeBool
  (List.range N).map fun i => allP.getD i 2

theorem firstNPrimes_spec (N : ℕ) :
    (firstNPrimes N).length = N ∧
    (∀ i : ℕ, i < N → Nat.Prime ((firstNPrimes N).getD i 2)) ∧
    (firstNPrimes N).Nodup := by
  let M := (N + 1) * (2 * N + 4)
  let allP := (List.range (M + 1)).filter isPrimeBool
  have hallP_nodup : allP.Nodup := (List.nodup_range).filter _
  have hcard_le : N ≤ allP.length := by
    have h1 := Nat.le_card_primesLE_mul_log N
    have hlog : Nat.log 2 (N + 1) ≤ N := by
      have := Nat.log_lt_of_lt_pow (by omega : N + 1 ≠ 0) (Nat.lt_two_pow_self (n := N + 1))
      omega
    have hm_le : (N + 1) * (2 * Nat.log 2 (N + 1) + 4) ≤ M :=
      Nat.mul_le_mul_left (N + 1) (by omega)
    have hsub : Nat.primesLE ((N + 1) * (2 * Nat.log 2 (N + 1) + 4)) ⊆ Nat.primesLE M :=
      Nat.primesLE_mono hm_le
    have h2 : N ≤ (Nat.primesLE M).card := h1.trans (Finset.card_le_card hsub)
    have hset : allP.toFinset = Nat.primesLE M := by
      rw [Nat.primesLE_eq_filter_range]
      ext x
      simp only [allP, List.mem_toFinset, List.mem_filter, List.mem_range,
        isPrimeBool_eq_true_iff, Finset.mem_filter, Finset.mem_range]
    rw [← List.toFinset_card_of_nodup hallP_nodup, hset]
    exact h2
  have hget : ∀ (i : ℕ) (hi : i < N), allP.getD i 2 = allP[i]'(lt_of_lt_of_le hi hcard_le) :=
    fun i hi => List.getD_eq_getElem allP 2 (lt_of_lt_of_le hi hcard_le)
  have hlen : (firstNPrimes N).length = N := by simp [firstNPrimes]
  refine ⟨hlen, fun i hi => ?_, ?_⟩
  · have hEq : (firstNPrimes N).getD i 2 = allP[i]'(lt_of_lt_of_le hi hcard_le) := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp only [firstNPrimes, List.getElem_map, List.getElem_range]
      exact hget i hi
    rw [hEq]
    have hmem : allP[i]'(lt_of_lt_of_le hi hcard_le) ∈ allP := List.getElem_mem _
    simp only [allP, List.mem_filter, isPrimeBool_eq_true_iff] at hmem
    exact hmem.2
  · rw [List.nodup_iff_injective_getElem]
    intro a b hab
    simp only [firstNPrimes, List.getElem_map, List.getElem_range] at hab
    have ha : a.val < N := by simpa [firstNPrimes] using a.isLt
    have hb : b.val < N := by simpa [firstNPrimes] using b.isLt
    rw [hget a.val ha, hget b.val hb] at hab
    have heq : (⟨a.val, lt_of_lt_of_le ha hcard_le⟩ : Fin allP.length) =
        ⟨b.val, lt_of_lt_of_le hb hcard_le⟩ :=
      (List.nodup_iff_injective_getElem.mp hallP_nodup) hab
    exact Fin.ext (congrArg (Fin.val : Fin allP.length → ℕ) heq)

@[fun_prop]
theorem computableInPolyTime_firstNPrimes :
    ComputableInPolyTime firstNPrimes encUnary (encList encUnary) := by
  unfold firstNPrimes
  have hbound : ComputableInPolyTime (fun N : ℕ => (N + 1) * (2 * N + 4) + 1) encUnary encUnary :=
    unary_add' (unary_mul' (unary_add' id' (const 1))
      (unary_add' (unary_mul' (const 2) id') (const 4))) (const 1)
  have hallP : ComputableInPolyTime
      (fun N : ℕ => (List.range ((N + 1) * (2 * N + 4) + 1)).filter isPrimeBool)
      encUnary (encList encUnary) :=
    (filter computableInPolyTime_isPrimeBool).comp (range.comp hbound)
  refine mapWithInput (range.comp id') ?_
  exact listGetDWithInput (hallP.comp (fst encUnary encUnary)) (snd encUnary encUnary) 2

end CslibFrontier.Computability.PolyTime.Digraph
