/-
Copyright (c) 2026 The FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalPapers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Pigeonhole

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Relational Promise Constraint Satisfaction Problems and Reconfigurability

General relational Promise Constraint Satisfaction Problems (`PCSP`), homomorphism sandwiching
reductions, symmetric hypergraph templates ($R_{k:\ell}^{(c)}$, $\mathrm{NAE}_r^{(d)}$,
$m\text{-in-}\ell$, $\mathrm{LO}_c^{(r)}$), single-coordinate reconfigurability, BKLM prefix-suffix
connectivity, and Affine Integer Programming threshold rounding.

## Main definitions

* `Cslib.Complexity.PolyTimeEquivalent`: mutual polynomial-time promise reducibility.
* `Cslib.Complexity.RelAtom`, `Cslib.Complexity.FinRelStruct`, `Cslib.Complexity.RelTemplate`:
  executable finite relational structures and semantic templates.
* `Cslib.Complexity.PCSP`, `Cslib.Complexity.CSP`: Promise CSP and CSP promise problems.
* `Cslib.Complexity.boundedOccRel`, `Cslib.Complexity.naeRel`, `Cslib.Complexity.kInLRel`,
  `Cslib.Complexity.loRel`: bounded-occurrence, NAE, exact-weight, and linearly ordered relations.
* `Cslib.Complexity.IsSymmetricRel`, `Cslib.Complexity.IsReconfigurable`,
  `Cslib.Complexity.bklmGraph`, `Cslib.Complexity.IsBKLMConnected`: reconfigurability and BKLM
  prefix-suffix connectivity.

## Main results

* `Cslib.Complexity.pcsp_sandwich`: homomorphism sandwiching $\mathbb{A} \to \mathbb{B} \to
  \mathbb{C} \to \mathbb{D}$ induces $\mathrm{PCSP}(\mathbb{A}, \mathbb{D}) \le_p
  \mathrm{PCSP}(\mathbb{B}, \mathbb{C})$.
* `Cslib.Complexity.isBKLMConnected_of_isReconfigurable`: nonempty reconfigurable relations are
  BKLM-connected.
* `Cslib.Complexity.aip_threshold_mem_naeRel`: integer $m$-in-$\ell$ equations ($0 < m < \ell$)
  threshold-round into $\mathrm{NAE}_\ell^{(2)}$.
-/

public section

namespace Cslib.Complexity

open Finset Function Turing.MultiTapeTM

/-- Two promise problems `X` and `Y` are polynomial-time equivalent when each reduces to the other
in polynomial time. -/
def PolyTimeEquivalent {α β : Type*} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (X : PromiseProblem α) (Y : PromiseProblem β) : Prop :=
  PromiseProblem.PolyTimeReducible encA encB X Y ∧
    PromiseProblem.PolyTimeReducible encB encA Y X

@[refl]
theorem PolyTimeEquivalent.refl {α : Type*} (encA : α ↪ List Bool) (X : PromiseProblem α) :
    PolyTimeEquivalent encA encA X X :=
  ⟨.refl encA X, .refl encA X⟩

@[symm]
theorem PolyTimeEquivalent.symm {α β : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {X : PromiseProblem α} {Y : PromiseProblem β} (h : PolyTimeEquivalent encA encB X Y) :
    PolyTimeEquivalent encB encA Y X :=
  ⟨h.2, h.1⟩

@[trans]
theorem PolyTimeEquivalent.trans {α β γ : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {X : PromiseProblem α} {Y : PromiseProblem β} {Z : PromiseProblem γ}
    (hXY : PolyTimeEquivalent encA encB X Y) (hYZ : PolyTimeEquivalent encB encC Y Z) :
    PolyTimeEquivalent encA encC X Z :=
  ⟨hXY.1.trans hYZ.1, hYZ.2.trans hXY.2⟩

/-- A ground relational atom over relation alphabet `σ`. -/
@[ext]
structure RelAtom (σ : Type*) where
  /-- Relation symbol. -/
  rel : σ
  /-- Ordered list of unary vertex indices. -/
  args : List ℕ
  deriving DecidableEq, Repr

/-- Framed pair encoding of `RelAtom σ` using unary argument lists. -/
abbrev encRelAtom {σ : Type} (encRel : σ ↪ List Bool) : RelAtom σ ↪ List Bool :=
  ⟨fun a => encPair encRel (encList encUnary) (a.rel, a.args), fun a b h => by
    have hp := (encPair encRel (encList encUnary)).injective h
    exact RelAtom.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)⟩

/-- An explicit finite relational structure over `σ` with unary vertex count and atom list. -/
@[ext]
structure FinRelStruct (σ : Type*) where
  /-- Number of domain elements (`Fin vertices`). -/
  vertices : ℕ
  /-- Framed list of ground relational atoms. -/
  atoms : List (RelAtom σ)
  deriving DecidableEq, Repr

/-- Framed encoding of `FinRelStruct σ` with unary vertex count. -/
abbrev encFinRelStruct {σ : Type} (encRel : σ ↪ List Bool) : FinRelStruct σ ↪ List Bool :=
  ⟨fun I => encPair encUnary (encList (encRelAtom encRel)) (I.vertices, I.atoms),
    fun I J h => by
      have hp := (encPair encUnary (encList (encRelAtom encRel))).injective h
      exact FinRelStruct.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)⟩

namespace FinRelStruct

/-- Arity and vertex-bound well-formedness of a `FinRelStruct`. -/
def WellFormed {σ : Type*} (ar : σ → ℕ) (I : FinRelStruct σ) : Prop :=
  ∀ a ∈ I.atoms, a.args.length = ar a.rel ∧ ∀ v ∈ a.args, v < I.vertices

end FinRelStruct

/-- A semantic relational template on carrier `A` with arities `ar`. -/
@[ext]
structure RelTemplate (σ : Type*) (ar : σ → ℕ) (A : Type*) where
  /-- Interpretation of each relation symbol `R : σ`. -/
  rel : (R : σ) → Set (Fin (ar R) → A)

namespace RelTemplate

/-- Coordinatewise template homomorphism `φ : A → B`. -/
def IsHom {σ : Type*} {ar : σ → ℕ} {A B : Type*}
    (T₁ : RelTemplate σ ar A) (T₂ : RelTemplate σ ar B) (φ : A → B) : Prop :=
  ∀ R : σ, ∀ t ∈ T₁.rel R, (φ ∘ t) ∈ T₂.rel R

/-- Existence of a template homomorphism $T_1 \to T_2$. -/
def HasHom {σ : Type*} {ar : σ → ℕ} {A B : Type*}
    (T₁ : RelTemplate σ ar A) (T₂ : RelTemplate σ ar B) : Prop :=
  ∃ φ : A → B, IsHom T₁ T₂ φ

@[refl]
theorem HasHom.refl {σ : Type*} {ar : σ → ℕ} {A : Type*} (T : RelTemplate σ ar A) :
    HasHom T T :=
  ⟨id, fun _ _ ht => ht⟩

@[trans]
theorem HasHom.trans {σ : Type*} {ar : σ → ℕ} {A B C : Type*}
    {T₁ : RelTemplate σ ar A} {T₂ : RelTemplate σ ar B} {T₃ : RelTemplate σ ar C}
    (h₁₂ : HasHom T₁ T₂) (h₂₃ : HasHom T₂ T₃) : HasHom T₁ T₃ :=
  let ⟨φ, hφ⟩ := h₁₂
  let ⟨ψ, hψ⟩ := h₂₃
  ⟨ψ ∘ φ, fun R t ht => hψ R (φ ∘ t) (hφ R t ht)⟩

end RelTemplate

namespace FinRelStruct

/-- Homomorphism from `I : FinRelStruct σ` to `T : RelTemplate σ ar A`. -/
def HomTo {σ : Type*} (ar : σ → ℕ) (I : FinRelStruct σ) {A : Type*}
    (T : RelTemplate σ ar A) (h : Fin I.vertices → A) : Prop :=
  ∀ a ∈ I.atoms, ∀ ha : a.args.length = ar a.rel ∧ ∀ v ∈ a.args, v < I.vertices,
    (fun k : Fin (ar a.rel) =>
      h ⟨a.args[k.val]'(by omega), ha.2 _ (List.getElem_mem _)⟩) ∈ T.rel a.rel

/-- Existence of a homomorphism from `I` to `T`. -/
def AdmitsHom {σ : Type*} (ar : σ → ℕ) (I : FinRelStruct σ) {A : Type*}
    (T : RelTemplate σ ar A) : Prop :=
  ∃ h : Fin I.vertices → A, I.HomTo ar T h

theorem AdmitsHom.mono {σ : Type*} {ar : σ → ℕ} {I : FinRelStruct σ} {A B : Type*}
    {T₁ : RelTemplate σ ar A} {T₂ : RelTemplate σ ar B}
    (hI : I.AdmitsHom ar T₁) (hT : RelTemplate.HasHom T₁ T₂) :
    I.AdmitsHom ar T₂ :=
  let ⟨h, hh⟩ := hI
  let ⟨φ, hφ⟩ := hT
  ⟨φ ∘ h, fun a ha hwf => hφ a.rel _ (hh a ha hwf)⟩

end FinRelStruct

/-- The Promise Constraint Satisfaction Problem $\mathrm{PCSP}(\mathbb{A}, \mathbb{B})$. -/
def PCSP {σ : Type*} (ar : σ → ℕ) {A B : Type*}
    (T₁ : RelTemplate σ ar A) (T₂ : RelTemplate σ ar B)
    (hAB : RelTemplate.HasHom T₁ T₂) : PromiseProblem (FinRelStruct σ) where
  yes := {I | I.WellFormed ar ∧ I.AdmitsHom ar T₁}
  no := {I | I.WellFormed ar ∧ ¬ I.AdmitsHom ar T₂}
  disjoint := Set.disjoint_left.2 fun _ hyes hno => hno.2 (hyes.2.mono hAB)

/-- The Constraint Satisfaction Problem $\mathrm{CSP}(\mathbb{B}) = \mathrm{PCSP}(\mathbb{B},
\mathbb{B})$. -/
def CSP {σ : Type*} (ar : σ → ℕ) {B : Type*} (T : RelTemplate σ ar B) :
    PromiseProblem (FinRelStruct σ) :=
  PCSP ar T T (.refl T)

/-- Homomorphism sandwiching $\mathbb{A} \to \mathbb{B} \to \mathbb{C} \to \mathbb{D}$ induces a
polynomial-time promise reduction via the identity map. -/
theorem pcsp_sandwich {σ : Type} (encRel : σ ↪ List Bool) (ar : σ → ℕ)
    {A B C D : Type*}
    {TA : RelTemplate σ ar A} {TB : RelTemplate σ ar B}
    {TC : RelTemplate σ ar C} {TD : RelTemplate σ ar D}
    (hAB : RelTemplate.HasHom TA TB) (hBC : RelTemplate.HasHom TB TC)
    (hCD : RelTemplate.HasHom TC TD) :
    PromiseProblem.PolyTimeReducible (encFinRelStruct encRel) (encFinRelStruct encRel)
      (PCSP ar TA TD (hAB.trans (hBC.trans hCD))) (PCSP ar TB TC hBC) :=
  PromiseProblem.PolyTimeReducible.of_subset
    (fun _ ⟨hwf, hA⟩ => ⟨hwf, hA.mono hAB⟩)
    (fun _ ⟨hwf, hnD⟩ => ⟨hwf, fun hC => hnD (hC.mono hCD)⟩)

/-- Bounded-occurrence hypergraph relation $R_{k:\ell}^{(c)}$. -/
def boundedOccRel (c k ℓ : ℕ) : Set (Fin ℓ → Fin c) :=
  {t | ∀ a : Fin c, (univ.filter fun i : Fin ℓ => t i = a).card < k}

/-- Not-All-Equal hypergraph relation $\mathrm{NAE}_r^{(d)}$. -/
def naeRel (d r : ℕ) : Set (Fin r → Fin d) :=
  {t | ¬ ∀ i j : Fin r, t i = t j}

/-- Exact-weight Boolean relation $m\text{-in-}\ell$. -/
def kInLRel (m ℓ : ℕ) : Set (Fin ℓ → Fin 2) :=
  {t | (univ.filter fun i : Fin ℓ => t i = 1).card = m}

/-- Linearly Ordered hypergraph relation $\mathrm{LO}_c^{(r)}$. -/
def loRel (c r : ℕ) : Set (Fin r → Fin c) :=
  {t | ∃ i : Fin r, ∀ j : Fin r, j ≠ i → t j < t i}

/-- Affine Integer Programming threshold rounding from $\mathbb{Z}^\ell$ to
$\mathrm{NAE}_\ell^{(2)}$. -/
theorem aip_threshold_mem_naeRel {m ℓ : ℕ} (hm0 : 0 < m) (hmℓ : m < ℓ)
    (x : Fin ℓ → ℤ) (hsum : ∑ i : Fin ℓ, x i = (m : ℤ)) :
    (fun i : Fin ℓ => if 1 ≤ x i then (1 : Fin 2) else 0) ∈ naeRel 2 ℓ := by
  intro hall
  have hℓ0 : 0 < ℓ := Nat.lt_trans hm0 hmℓ
  let i₀ : Fin ℓ := ⟨0, hℓ0⟩
  by_cases hx₀ : 1 ≤ x i₀
  · have hall1 : ∀ i : Fin ℓ, 1 ≤ x i := by
      intro i
      have hi := hall i i₀
      simp only [hx₀, ↓reduceIte] at hi
      by_contra hni
      simp [hni] at hi
    have hge : (ℓ : ℤ) ≤ ∑ i : Fin ℓ, x i := by
      calc (ℓ : ℤ) = ∑ _i : Fin ℓ, (1 : ℤ) := by simp
        _ ≤ ∑ i : Fin ℓ, x i := Finset.sum_le_sum fun i _ => hall1 i
    omega
  · have hall0 : ∀ i : Fin ℓ, x i ≤ 0 := by
      intro i
      have hi := hall i i₀
      simp only [hx₀, ↓reduceIte] at hi
      by_cases h1 : 1 ≤ x i
      · simp [h1] at hi
      · omega
    have hle : ∑ i : Fin ℓ, x i ≤ 0 := Finset.sum_nonpos fun i _ => hall0 i
    omega

/-- Symmetry under coordinate permutations. -/
def IsSymmetricRel {r : ℕ} {A : Type*} (R : Set (Fin r → A)) : Prop :=
  ∀ σ : Equiv.Perm (Fin r), ∀ t ∈ R, (t ∘ σ) ∈ R

/-- Single-coordinate reconfiguration graph on `R`. -/
def reconfigGraph {r : ℕ} {A : Type*} (R : Set (Fin r → A)) : SimpleGraph R where
  Adj u v := ∃! i : Fin r, u.1 i ≠ v.1 i
  symm := ⟨fun _ _ ⟨i, hi, huniq⟩ => ⟨i, hi.symm, fun j hj => huniq j hj.symm⟩⟩
  loopless := ⟨fun _ ⟨_, hi, _⟩ => hi rfl⟩

/-- Single-coordinate reconfigurability of `R`. -/
def IsReconfigurable {r : ℕ} {A : Type*} (R : Set (Fin r → A)) : Prop :=
  ∀ u : R, ∀ v : R, (reconfigGraph R).Reachable u v

/-- Prefix of length `i` of an `r`-tuple (`i ≤ r`). -/
def tuplePrefix {r i : ℕ} {A : Type*} (hi : i ≤ r) (t : Fin r → A) : Fin i → A :=
  fun k => t ⟨k.val, Nat.lt_of_lt_of_le k.isLt hi⟩

/-- Suffix of length `r - i` of an `r`-tuple. -/
def tupleSuffix {r : ℕ} (i : ℕ) {A : Type*} (t : Fin r → A) : Fin (r - i) → A :=
  fun k => t ⟨i + k.val, by omega⟩

/-- Gluing a prefix and suffix into `Fin r → A`. -/
def gluePrefixSuffix {r i : ℕ} {A : Type*} (hi : i ≤ r) (p : Fin i → A) (s : Fin (r - i) → A) :
    Fin r → A :=
  fun k => if hk : k.val < i then p ⟨k.val, hk⟩ else s ⟨k.val - i, by omega⟩

/-- Left part of $\mathbb{G}_i^R$. -/
def BKLMPrefix {r i : ℕ} {A : Type*} (hi : i ≤ r) (R : Set (Fin r → A)) : Set (Fin i → A) :=
  tuplePrefix hi '' R

/-- Right part of $\mathbb{G}_i^R$. -/
def BKLMSuffix {r : ℕ} (i : ℕ) {A : Type*} (R : Set (Fin r → A)) : Set (Fin (r - i) → A) :=
  tupleSuffix i '' R

/-- BKLM prefix-suffix bipartite graph $\mathbb{G}_i^R$. -/
def bklmGraph {r i : ℕ} {A : Type*} (hi : i ≤ r) (R : Set (Fin r → A)) :
    SimpleGraph (BKLMPrefix hi R ⊕ BKLMSuffix i R) where
  Adj x y := match x, y with
    | Sum.inl p, Sum.inr s => gluePrefixSuffix hi p.1 s.1 ∈ R
    | Sum.inr s, Sum.inl p => gluePrefixSuffix hi p.1 s.1 ∈ R
    | _, _ => False
  symm := ⟨fun x y => by cases x <;> cases y <;> simp⟩
  loopless := ⟨fun x => by cases x <;> simp⟩

/-- BKLM connectivity of $R \subseteq A^r$. -/
def IsBKLMConnected {r : ℕ} {A : Type*} (R : Set (Fin r → A)) : Prop :=
  R.Nonempty ∧ ∀ (i : ℕ) (_hi1 : 1 ≤ i) (hir : i < r), (bklmGraph hir.le R).Connected

/-- Every nonempty reconfigurable relation is BKLM-connected. -/
theorem isBKLMConnected_of_isReconfigurable {r : ℕ} {A : Type*} {R : Set (Fin r → A)}
    (hne : R.Nonempty) (hrec : IsReconfigurable R) :
    IsBKLMConnected R := by
  have hglue : ∀ {i : ℕ} (hle : i ≤ r) (t : Fin r → A),
      gluePrefixSuffix hle (tuplePrefix hle t) (tupleSuffix i t) = t := by
    intro i hle t
    ext k
    by_cases hk : k.val < i
    · simp [gluePrefixSuffix, tuplePrefix, hk]
    · have hadd : i + (k.val - i) = k.val := by omega
      simp [gluePrefixSuffix, tupleSuffix, hk, hadd]
  refine ⟨hne, fun i _ hir => ?_⟩
  let hi := hir.le
  obtain ⟨t₀, ht₀⟩ := hne
  let p₀ : BKLMPrefix hi R := ⟨tuplePrefix hi t₀, t₀, ht₀, rfl⟩
  have hstep : ∀ u v : R, (reconfigGraph R).Adj u v →
      (bklmGraph hi R).Reachable
        (Sum.inl ⟨tuplePrefix hi u.1, u.1, u.2, rfl⟩)
        (Sum.inl ⟨tuplePrefix hi v.1, v.1, v.2, rfl⟩) := by
    intro u v ⟨k₀, _, huniq⟩
    have huv_eq : ∀ k : Fin r, k ≠ k₀ → u.1 k = v.1 k := fun k hk => by
      by_contra hne'
      exact hk (huniq k hne')
    by_cases hlt : k₀.val < i
    · have hsuf : tupleSuffix i u.1 = tupleSuffix i v.1 := by
        ext k; apply huv_eq; intro heq; have hv := congrArg Fin.val heq; dsimp at hv; omega
      let su : BKLMSuffix i R := ⟨tupleSuffix i u.1, u.1, u.2, rfl⟩
      have hadj1 : (bklmGraph hi R).Adj
          (Sum.inl ⟨tuplePrefix hi u.1, u.1, u.2, rfl⟩) (Sum.inr su) := by
        dsimp [bklmGraph, su]; rw [hglue hi u.1]; exact u.2
      have hadj2 : (bklmGraph hi R).Adj
          (Sum.inr su) (Sum.inl ⟨tuplePrefix hi v.1, v.1, v.2, rfl⟩) := by
        dsimp [bklmGraph, su]; rw [hsuf, hglue hi v.1]; exact v.2
      exact hadj1.reachable.trans hadj2.reachable
    · have hpre : tuplePrefix hi u.1 = tuplePrefix hi v.1 := by
        ext k; apply huv_eq; intro heq; have hv := congrArg Fin.val heq; dsimp at hv; omega
      have hsub : (⟨tuplePrefix hi u.1, u.1, u.2, rfl⟩ : BKLMPrefix hi R) =
          ⟨tuplePrefix hi v.1, v.1, v.2, rfl⟩ := Subtype.ext hpre
      rw [hsub]
  have hwalk_inl : ∀ u v : R, (reconfigGraph R).Walk u v →
      (bklmGraph hi R).Reachable
        (Sum.inl ⟨tuplePrefix hi u.1, u.1, u.2, rfl⟩)
        (Sum.inl ⟨tuplePrefix hi v.1, v.1, v.2, rfl⟩) := by
    intro u v w
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b _ hadj _ ih => exact (hstep a b hadj).trans ih
  have hreach_inl : ∀ p : BKLMPrefix hi R, (bklmGraph hi R).Reachable (Sum.inl p₀) (Sum.inl p) := by
    rintro ⟨_, t, ht, rfl⟩
    obtain ⟨w⟩ := hrec ⟨t₀, ht₀⟩ ⟨t, ht⟩
    exact hwalk_inl ⟨t₀, ht₀⟩ ⟨t, ht⟩ w
  have hreach_all : ∀ x : BKLMPrefix hi R ⊕ BKLMSuffix i R,
      (bklmGraph hi R).Reachable (Sum.inl p₀) x := by
    rintro (p | ⟨_, t, ht, rfl⟩)
    · exact hreach_inl p
    · let pt : BKLMPrefix hi R := ⟨tuplePrefix hi t, t, ht, rfl⟩
      have hadj : (bklmGraph hi R).Adj (Sum.inl pt) (Sum.inr ⟨tupleSuffix i t, t, ht, rfl⟩) := by
        dsimp [bklmGraph, pt]; rw [hglue hi t]; exact ht
      exact (hreach_inl pt).trans hadj.reachable
  have : Nonempty (BKLMPrefix hi R ⊕ BKLMSuffix i R) := ⟨Sum.inl p₀⟩
  exact ⟨fun x y => (hreach_all x).symm.trans (hreach_all y)⟩

end Cslib.Complexity
