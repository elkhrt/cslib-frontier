/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.QuantifierRank
public import Mathlib.ModelTheory.Complexity
public import Mathlib.ModelTheory.Semantics

/-!
# Total Quantifier Count and Prenex Normal Form

This module defines the total syntactic quantifier count `Cslib.Logic.FO.quantifierCount` (additive
across `imp`, `inf`, and `sup`, in contrast to `Cslib.Logic.FO.quantifierRank` which takes `max`) on
`FirstOrder.Language.BoundedFormula`, together with explicit quantifier-prefix prenex formulas
`Cslib.Logic.FO.PrenexFormula` (`Q₀ … Q_{r-1} θ` with `θ.IsQF`). Every bounded formula `φ` converts
to an equivalent `PrenexFormula` of exact prefix length `quantifierCount φ` across all nonempty
structures (`PrenexFormula.ofBoundedFormula`, `PrenexFormula.realize_ofBoundedFormula`), and pads to
any target length `r ≥ quantifierCount φ` (`PrenexFormula.padTo`).

## Main definitions

* `Cslib.Logic.FO.quantifierCount`: total number of quantifiers in a bounded formula.
* `Cslib.Logic.FO.Quantifier`: first-order quantifier tag (`ex` or `all`) with De Morgan dual
  `Quantifier.dual` and syntactic action `Cslib.Logic.FO.applyQuant`.
* `Cslib.Logic.FO.PrenexFormula`, `Cslib.Logic.FO.PrenexSentence`: prenex formulas and sentences
  with explicit quantifier prefix and quantifier-free matrix.
* `Cslib.Logic.FO.PrenexFormula.ofBoundedFormula`, `Cslib.Logic.FO.PrenexFormula.padTo`:
  quantifier-count-preserving prenex conversion and padding.

## Main results

* `Cslib.Logic.FO.quantifierCount_eq_zero_iff_isQF`: quantifier count is `0` iff
  `BoundedFormula.IsQF`.
* `Cslib.Logic.FO.quantifierRank_le_quantifierCount`: quantifier rank is at most quantifier count.
* `Cslib.Logic.FO.PrenexFormula.quantifierCount_toFormula`,
  `Cslib.Logic.FO.PrenexFormula.realize_ofBoundedFormula`,
  `Cslib.Logic.FO.PrenexFormula.exists_prenexSentence_of_quantifierCount_le`.
-/

public section

universe u v w

open FirstOrder FirstOrder.Language

namespace Cslib.Logic.FO

section QuantifierCount

variable {L : Language.{u, v}}

/-- Total number of quantifiers appearing in a bounded first-order formula. -/
def quantifierCount {α : Type*} : ∀ {n : ℕ}, L.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => quantifierCount φ + quantifierCount ψ
  | _, .all φ => quantifierCount φ + 1

@[simp, grind =]
theorem quantifierCount_falsum {α : Type*} {n : ℕ} :
    quantifierCount (L := L) (α := α) (n := n) .falsum = 0 := by
  rw [quantifierCount]

@[simp, grind =]
theorem quantifierCount_bot {α : Type*} {n : ℕ} :
    quantifierCount (⊥ : L.BoundedFormula α n) = 0 :=
  quantifierCount_falsum

@[simp, grind =]
theorem quantifierCount_equal {α : Type*} {n : ℕ} (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    quantifierCount (L := L) (n := n) (.equal t₁ t₂) = 0 := by
  rw [quantifierCount]

@[simp, grind =]
theorem quantifierCount_bdEqual {α : Type*} {n : ℕ} (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    quantifierCount (t₁.bdEqual t₂) = 0 :=
  quantifierCount_equal t₁ t₂

@[simp, grind =]
theorem quantifierCount_rel {α : Type*} {n m : ℕ} (R : L.Relations m)
    (ts : Fin m → L.Term (α ⊕ Fin n)) :
    quantifierCount (L := L) (n := n) (.rel R ts) = 0 := by
  rw [quantifierCount]

@[simp, grind =]
theorem quantifierCount_relations_boundedFormula {α : Type*} {n m : ℕ} (R : L.Relations m)
    (ts : Fin m → L.Term (α ⊕ Fin n)) :
    quantifierCount (R.boundedFormula ts) = 0 :=
  quantifierCount_rel R ts

@[simp, grind =]
theorem quantifierCount_imp {α : Type*} {n : ℕ} (φ ψ : L.BoundedFormula α n) :
    quantifierCount (φ.imp ψ) = quantifierCount φ + quantifierCount ψ := by
  rw [quantifierCount]

@[simp, grind =]
theorem quantifierCount_not {α : Type*} {n : ℕ} (φ : L.BoundedFormula α n) :
    quantifierCount (∼φ) = quantifierCount φ := by
  simp [BoundedFormula.not]

@[simp, grind =]
theorem quantifierCount_top {α : Type*} {n : ℕ} :
    quantifierCount (⊤ : L.BoundedFormula α n) = 0 := by
  simp [Top.top]

@[simp, grind =]
theorem quantifierCount_sup {α : Type*} {n : ℕ} (φ ψ : L.BoundedFormula α n) :
    quantifierCount (φ ⊔ ψ) = quantifierCount φ + quantifierCount ψ := by
  change quantifierCount (φ.not.imp ψ) = quantifierCount φ + quantifierCount ψ
  rw [quantifierCount_imp, quantifierCount_not]

@[simp, grind =]
theorem quantifierCount_inf {α : Type*} {n : ℕ} (φ ψ : L.BoundedFormula α n) :
    quantifierCount (φ ⊓ ψ) = quantifierCount φ + quantifierCount ψ := by
  change quantifierCount (φ.imp ψ.not).not = quantifierCount φ + quantifierCount ψ
  rw [quantifierCount_not, quantifierCount_imp, quantifierCount_not]

@[simp, grind =]
theorem quantifierCount_all {α : Type*} {n : ℕ} (φ : L.BoundedFormula α (n + 1)) :
    quantifierCount φ.all = quantifierCount φ + 1 := by
  rw [quantifierCount]

@[simp, grind =]
theorem quantifierCount_ex {α : Type*} {n : ℕ} (φ : L.BoundedFormula α (n + 1)) :
    quantifierCount φ.ex = quantifierCount φ + 1 := by
  rw [BoundedFormula.ex, quantifierCount_not, quantifierCount_all, quantifierCount_not]

@[simp, grind =]
theorem quantifierCount_castLE {α : Type*} :
    ∀ {m n : ℕ} (h : m ≤ n) (φ : L.BoundedFormula α m),
      quantifierCount (φ.castLE h) = quantifierCount φ
  | _, _, _, .falsum => by simp only [BoundedFormula.castLE, quantifierCount_falsum]
  | _, _, _, .equal _ _ => by simp only [BoundedFormula.castLE, quantifierCount_equal]
  | _, _, _, .rel _ _ => by simp only [BoundedFormula.castLE, quantifierCount_rel]
  | _, _, h, .imp φ ψ => by
    simp only [BoundedFormula.castLE, quantifierCount_imp, quantifierCount_castLE h φ,
      quantifierCount_castLE h ψ]
  | _, _, h, .all φ => by
    simp only [BoundedFormula.castLE, quantifierCount_all,
      quantifierCount_castLE (Nat.succ_le_succ h) φ]

private theorem quantifierCount_mapTermRel {L' : Language.{u, v}} {α β : Type*} {g : ℕ → ℕ}
    (ft : ∀ n, L.Term (α ⊕ Fin n) → L'.Term (β ⊕ Fin (g n)))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (h : ∀ n, L'.BoundedFormula β (g (n + 1)) → L'.BoundedFormula β (g n + 1))
    (hh : ∀ n (ψ : L'.BoundedFormula β (g (n + 1))),
      quantifierCount (h n ψ) = quantifierCount ψ) :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n),
      quantifierCount (φ.mapTermRel ft fr h) = quantifierCount φ
  | _, .falsum => rfl
  | _, .equal _ _ => rfl
  | _, .rel _ _ => rfl
  | _, .imp φ ψ => by
    simp only [BoundedFormula.mapTermRel, quantifierCount_imp,
      quantifierCount_mapTermRel ft fr h hh φ, quantifierCount_mapTermRel ft fr h hh ψ]
  | n, .all φ => by
    simp only [BoundedFormula.mapTermRel, quantifierCount_all, hh n,
      quantifierCount_mapTermRel ft fr h hh φ]

@[simp, grind =]
theorem quantifierCount_liftAt {α : Type*} {n : ℕ} (k m : ℕ) (φ : L.BoundedFormula α n) :
    quantifierCount (φ.liftAt k m) = quantifierCount φ :=
  quantifierCount_mapTermRel _ _ _ (fun _ ψ => quantifierCount_castLE _ ψ) φ

/-- A bounded formula has quantifier count `0` if and only if it is quantifier-free. -/
theorem quantifierCount_eq_zero_iff_isQF {α : Type*} :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n), quantifierCount φ = 0 ↔ φ.IsQF
  | _, .falsum => ⟨fun _ => .falsum, fun _ => rfl⟩
  | _, .equal _ _ => ⟨fun _ => (BoundedFormula.IsAtomic.equal _ _).isQF, fun _ => rfl⟩
  | _, .rel _ _ => ⟨fun _ => (BoundedFormula.IsAtomic.rel _ _).isQF, fun _ => rfl⟩
  | _, .imp φ ψ => by
    rw [quantifierCount_imp, Nat.add_eq_zero_iff,
      quantifierCount_eq_zero_iff_isQF φ, quantifierCount_eq_zero_iff_isQF ψ]
    exact ⟨fun ⟨h₁, h₂⟩ => h₁.imp h₂, fun h => by
      cases h with
      | of_isAtomic hAt => cases hAt
      | imp h₁ h₂ => exact ⟨h₁, h₂⟩⟩
  | _, .all _ => by
    simp only [quantifierCount_all, Nat.add_one_ne_zero, false_iff]
    intro h
    cases h with
    | of_isAtomic hAt => cases hAt

/-- The quantifier rank of a bounded formula never exceeds its total quantifier count. -/
theorem quantifierRank_le_quantifierCount {α : Type*} :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n),
      quantifierRank φ ≤ quantifierCount φ
  | _, .falsum => by simp
  | _, .equal _ _ => by simp
  | _, .rel _ _ => by simp
  | _, .imp φ ψ => by
    rw [quantifierRank_imp, quantifierCount_imp, max_le_iff]
    exact ⟨(quantifierRank_le_quantifierCount φ).trans (Nat.le_add_right _ _),
      (quantifierRank_le_quantifierCount ψ).trans (Nat.le_add_left _ _)⟩
  | _, .all φ => by
    rw [quantifierRank_all, quantifierCount_all]
    exact Nat.succ_le_succ (quantifierRank_le_quantifierCount φ)

end QuantifierCount

section Prenex

variable {L : Language.{u, v}}

/-- A first-order quantifier symbol (`∃` or `∀`). -/
inductive Quantifier : Type
  /-- Existential quantifier `∃`. -/
  | ex : Quantifier
  /-- Universal quantifier `∀`. -/
  | all : Quantifier
  deriving DecidableEq, Repr

/-- De Morgan dual of a first-order quantifier (`∃ ↔ ∀`). -/
@[expose] def Quantifier.dual : Quantifier → Quantifier
  | .ex => .all
  | .all => .ex

@[simp] theorem Quantifier.dual_ex : Quantifier.ex.dual = .all := rfl
@[simp] theorem Quantifier.dual_all : Quantifier.all.dual = .ex := rfl
@[simp] theorem Quantifier.dual_dual (q : Quantifier) : q.dual.dual = q := by cases q <;> rfl

/-- Apply a single quantifier symbol to the outermost bound variable of a bounded formula. -/
@[expose] def applyQuant {α : Type*} {n : ℕ} :
    Quantifier → L.BoundedFormula α (n + 1) → L.BoundedFormula α n
  | .ex, φ => φ.ex
  | .all, φ => φ.all

@[simp] theorem applyQuant_ex {α : Type*} {n : ℕ} (φ : L.BoundedFormula α (n + 1)) :
    applyQuant .ex φ = φ.ex := rfl
@[simp] theorem applyQuant_all {α : Type*} {n : ℕ} (φ : L.BoundedFormula α (n + 1)) :
    applyQuant .all φ = φ.all := rfl

@[simp]
theorem quantifierCount_applyQuant {α : Type*} {n : ℕ} (q : Quantifier)
    (φ : L.BoundedFormula α (n + 1)) :
    quantifierCount (applyQuant q φ) = quantifierCount φ + 1 := by
  cases q <;> simp

/-- A prenex `L`-formula with free variables `α`, `n` outer bound variables, and `r` explicit
quantifiers `Q₀ … Q_{r-1}` wrapping a quantifier-free matrix `θ`. -/
@[ext]
structure PrenexFormula (L : Language.{u, v}) (α : Type*) (n r : ℕ) where
  /-- The sequence of `r` quantifiers from outermost (`0`) to innermost (`r - 1`). -/
  prefixQ : Fin r → Quantifier
  /-- The inner matrix in `n + r` bound variables. -/
  matrix : L.BoundedFormula α (n + r)
  /-- Proof that `matrix` is quantifier-free. -/
  matrix_isQF : matrix.IsQF

/-- A prenex `L`-sentence with `r` quantifiers. -/
abbrev PrenexSentence (L : Language.{u, v}) (r : ℕ) := PrenexFormula L Empty 0 r

namespace PrenexFormula

/-- Semantic evaluation of a quantifier prefix `Q : Fin r → Quantifier`. -/
@[expose] def evalPrefix (M : Type w) :
    ∀ {r : ℕ}, (Fin r → Quantifier) → ((Fin r → M) → Prop) → Prop
  | 0, _, P => P Fin.elim0
  | _ + 1, Q, P => match Q 0 with
    | .ex => ∃ y : M, evalPrefix M (Q ∘ Fin.succ) (fun ys => P (Fin.cons y ys))
    | .all => ∀ y : M, evalPrefix M (Q ∘ Fin.succ) (fun ys => P (Fin.cons y ys))

@[simp]
theorem evalPrefix_zero (M : Type w) (Q : Fin 0 → Quantifier) (P : (Fin 0 → M) → Prop) :
    evalPrefix M Q P = P Fin.elim0 := rfl

theorem evalPrefix_succ_ex (M : Type w) {r : ℕ} (Q : Fin (r + 1) → Quantifier)
    (hQ : Q 0 = .ex) (P : (Fin (r + 1) → M) → Prop) :
    evalPrefix M Q P ↔ ∃ y : M, evalPrefix M (Q ∘ Fin.succ) (fun ys => P (Fin.cons y ys)) := by
  simp only [evalPrefix, hQ]

theorem evalPrefix_succ_all (M : Type w) {r : ℕ} (Q : Fin (r + 1) → Quantifier)
    (hQ : Q 0 = .all) (P : (Fin (r + 1) → M) → Prop) :
    evalPrefix M Q P ↔ ∀ y : M, evalPrefix M (Q ∘ Fin.succ) (fun ys => P (Fin.cons y ys)) := by
  simp only [evalPrefix, hQ]

theorem evalPrefix_congr (M : Type w) :
    ∀ {r : ℕ} (Q : Fin r → Quantifier) {P₁ P₂ : (Fin r → M) → Prop},
      (∀ ys, P₁ ys ↔ P₂ ys) → (evalPrefix M Q P₁ ↔ evalPrefix M Q P₂)
  | 0, _, _, _, h => h Fin.elim0
  | _ + 1, Q, _, _, h => by
    cases hQ : Q 0
    · rw [evalPrefix_succ_ex M Q hQ, evalPrefix_succ_ex M Q hQ]
      exact exists_congr fun y => evalPrefix_congr M (Q ∘ Fin.succ) fun ys => h (Fin.cons y ys)
    · rw [evalPrefix_succ_all M Q hQ, evalPrefix_succ_all M Q hQ]
      exact forall_congr' fun y => evalPrefix_congr M (Q ∘ Fin.succ) fun ys => h (Fin.cons y ys)

/-- Wrap a quantifier prefix around a bounded formula in `n + r` bound variables. -/
@[expose] def wrapPrefix {α : Type*} :
    ∀ {n r : ℕ}, (Fin r → Quantifier) → L.BoundedFormula α (n + r) → L.BoundedFormula α n
  | _, 0, _, θ => θ
  | n, r + 1, Q, θ =>
    applyQuant (Q 0) (wrapPrefix (n := n + 1) (r := r) (Q ∘ Fin.succ) (θ.castLE (by omega)))

/-- The underlying `L.BoundedFormula` represented by a `PrenexFormula`. -/
@[expose] def toFormula {α : Type*} {n r : ℕ} (ψ : PrenexFormula L α n r) :
    L.BoundedFormula α n :=
  wrapPrefix ψ.prefixQ ψ.matrix

theorem isPrenex_wrapPrefix {α : Type*} :
    ∀ {n r : ℕ} (Q : Fin r → Quantifier) (θ : L.BoundedFormula α (n + r)),
      θ.IsQF → (wrapPrefix Q θ).IsPrenex
  | _, 0, _, _, hθ => hθ.isPrenex
  | n, r + 1, Q, θ, hθ => by
    have ih := isPrenex_wrapPrefix (n := n + 1) (r := r)
      (Q ∘ Fin.succ) (θ.castLE (by omega)) hθ.castLE
    cases hQ : Q 0
    · simpa only [wrapPrefix, hQ, applyQuant_ex] using ih.ex
    · simpa only [wrapPrefix, hQ, applyQuant_all] using ih.all

theorem isPrenex_toFormula {α : Type*} {n r : ℕ} (ψ : PrenexFormula L α n r) :
    ψ.toFormula.IsPrenex :=
  isPrenex_wrapPrefix ψ.prefixQ ψ.matrix ψ.matrix_isQF

theorem quantifierCount_wrapPrefix {α : Type*} :
    ∀ {n r : ℕ} (Q : Fin r → Quantifier) (θ : L.BoundedFormula α (n + r)),
      θ.IsQF → quantifierCount (wrapPrefix Q θ) = r
  | _, 0, _, θ, hθ => (quantifierCount_eq_zero_iff_isQF θ).mpr hθ
  | _, _ + 1, Q, θ, hθ => by
    simp only [wrapPrefix, quantifierCount_applyQuant]
    rw [quantifierCount_wrapPrefix (Q ∘ Fin.succ) _ hθ.castLE]

@[simp]
theorem quantifierCount_toFormula {α : Type*} {n r : ℕ} (ψ : PrenexFormula L α n r) :
    quantifierCount ψ.toFormula = r :=
  quantifierCount_wrapPrefix ψ.prefixQ ψ.matrix ψ.matrix_isQF

/-- Concatenate `xs : Fin n → M` and `ys : Fin r → M` into `Fin (n + r) → M`. -/
@[expose] def appendVec {M : Type w} {n r : ℕ} (xs : Fin n → M) (ys : Fin r → M) :
    Fin (n + r) → M :=
  Fin.addCases xs ys

@[simp]
theorem appendVec_zero {M : Type w} {n : ℕ} (xs : Fin n → M) (ys : Fin 0 → M) :
    appendVec xs ys = xs := by
  ext i
  simp only [appendVec, Fin.addCases]
  split_ifs with h
  · exact congrArg xs (Fin.ext rfl)
  · exfalso; exact h i.isLt

theorem appendVec_snoc_cons {M : Type w} {n r : ℕ} (xs : Fin n → M) (y : M) (ys : Fin r → M) :
    appendVec (Fin.snoc xs y) ys ∘ Fin.cast (by omega : n + (r + 1) = n + 1 + r) =
      appendVec xs (Fin.cons y ys) := by
  ext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · have hcast : Fin.cast (by omega : n + (r + 1) = n + 1 + r) (Fin.castAdd (r + 1) a) =
        Fin.castAdd r a.castSucc := by ext; rfl
    simp only [Function.comp_apply, hcast, appendVec, Fin.addCases_left, Fin.snoc_castSucc]
  · refine Fin.cases ?_ (fun b' => ?_) b
    · have hcast : Fin.cast (by omega : n + (r + 1) = n + 1 + r) (Fin.natAdd n 0) =
          Fin.castAdd r (Fin.last n) := by ext; simp
      simp only [Function.comp_apply, hcast, appendVec, Fin.addCases_left, Fin.snoc_last,
        Fin.addCases_right, Fin.cons_zero]
    · have hcast : Fin.cast (by omega : n + (r + 1) = n + 1 + r) (Fin.natAdd n b'.succ) =
          Fin.natAdd (n + 1) b' := by ext; simp [Nat.add_assoc, Nat.add_comm 1]
      simp only [Function.comp_apply, hcast, appendVec, Fin.addCases_right, Fin.cons_succ]

theorem appendVec_snoc_cons_symm {M : Type w} {n r : ℕ} (xs : Fin n → M) (y : M)
    (ys : Fin r → M) :
    appendVec xs (Fin.cons y ys) ∘ Fin.cast (by omega : n + 1 + r = n + (r + 1)) =
      appendVec (Fin.snoc xs y) ys := by
  ext i
  have h := congrFun (appendVec_snoc_cons xs y ys)
    (Fin.cast (by omega : n + 1 + r = n + (r + 1)) i)
  simpa using h.symm

theorem realize_wrapPrefix_iff {α : Type*} {M : Type w} [L.Structure M] (v : α → M) :
    ∀ {n r : ℕ} (Q : Fin r → Quantifier) (θ : L.BoundedFormula α (n + r)) (xs : Fin n → M),
      (wrapPrefix Q θ).Realize v xs ↔ evalPrefix M Q (fun ys => θ.Realize v (appendVec xs ys))
  | _, 0, _, θ, xs => by simp only [wrapPrefix, evalPrefix_zero, appendVec_zero]
  | n, r + 1, Q, θ, xs => by
    simp only [wrapPrefix]
    have hstep : ∀ y : M,
        (wrapPrefix (n := n + 1) (Q ∘ Fin.succ) (θ.castLE (by omega))).Realize v
          (Fin.snoc xs y) ↔
        evalPrefix M (Q ∘ Fin.succ)
          (fun ys => θ.Realize v (appendVec xs (Fin.cons y ys))) := by
      intro y
      rw [realize_wrapPrefix_iff v (Q ∘ Fin.succ) (θ.castLE (by omega)) (Fin.snoc xs y)]
      refine evalPrefix_congr M (Q ∘ Fin.succ) fun ys => ?_
      rw [BoundedFormula.realize_castLE_of_eq (by omega : n + (r + 1) = n + 1 + r),
        appendVec_snoc_cons]
    cases hQ : Q 0
    · rw [applyQuant_ex, BoundedFormula.realize_ex, evalPrefix_succ_ex M Q hQ]
      exact exists_congr hstep
    · rw [applyQuant_all, BoundedFormula.realize_all, evalPrefix_succ_all M Q hQ]
      exact forall_congr' hstep

theorem realize_toFormula_iff {α : Type*} {n r : ℕ} (ψ : PrenexFormula L α n r)
    {M : Type w} [L.Structure M] (v : α → M) (xs : Fin n → M) :
    ψ.toFormula.Realize v xs ↔
      evalPrefix M ψ.prefixQ (fun ys => ψ.matrix.Realize v (appendVec xs ys)) :=
  realize_wrapPrefix_iff v ψ.prefixQ ψ.matrix xs

/-- Re-index the prefix length of a `PrenexFormula` along `r₁ = r₂`. -/
def castPrefix {α : Type*} {n r₁ r₂ : ℕ} (h : r₁ = r₂)
    (ψ : PrenexFormula L α n r₁) : PrenexFormula L α n r₂ :=
  h ▸ ψ

@[simp]
theorem realize_castPrefix {α : Type*} {n r₁ r₂ : ℕ} (h : r₁ = r₂)
    (ψ : PrenexFormula L α n r₁) {M : Type w} [L.Structure M] (v : α → M) (xs : Fin n → M) :
    (ψ.castPrefix h).toFormula.Realize v xs ↔ ψ.toFormula.Realize v xs := by
  subst h; rfl

/-- Prepend an outer quantifier `q` to a `PrenexFormula`. -/
def cons {α : Type*} {n r : ℕ} (q : Quantifier) (ψ : PrenexFormula L α (n + 1) r) :
    PrenexFormula L α n (r + 1) where
  prefixQ := Fin.cases q ψ.prefixQ
  matrix := ψ.matrix.castLE (by omega)
  matrix_isQF := ψ.matrix_isQF.castLE

theorem realize_cons {α : Type*} {n r : ℕ} (q : Quantifier) (ψ : PrenexFormula L α (n + 1) r)
    {M : Type w} [L.Structure M] (v : α → M) (xs : Fin n → M) :
    (ψ.cons q).toFormula.Realize v xs ↔
      (applyQuant q ψ.toFormula).Realize v xs := by
  rw [realize_toFormula_iff]
  have hcast : ∀ y : M,
      evalPrefix M ψ.prefixQ (fun ys =>
        (ψ.matrix.castLE (by omega : n + 1 + r ≤ n + (r + 1))).Realize v
          (appendVec xs (Fin.cons y ys))) ↔
      ψ.toFormula.Realize v (Fin.snoc xs y) := by
    intro y
    rw [realize_toFormula_iff]
    refine evalPrefix_congr M ψ.prefixQ fun ys => ?_
    rw [BoundedFormula.realize_castLE_of_eq (by omega : n + 1 + r = n + (r + 1))]
    exact iff_of_eq (congrArg (ψ.matrix.Realize v) (appendVec_snoc_cons_symm xs y ys))
  cases q
  · simp only [cons, evalPrefix, Fin.cases_zero, applyQuant_ex, BoundedFormula.realize_ex]
    exact exists_congr fun y => by simpa [Function.comp_def] using hcast y
  · simp only [cons, evalPrefix, Fin.cases_zero, applyQuant_all, BoundedFormula.realize_all]
    exact forall_congr' fun y => by simpa [Function.comp_def] using hcast y

/-- Peel off the outermost quantifier from a `PrenexFormula` of prefix length `r + 1`. -/
def tail {α : Type*} {n r : ℕ} (ψ : PrenexFormula L α n (r + 1)) :
    PrenexFormula L α (n + 1) r where
  prefixQ := ψ.prefixQ ∘ Fin.succ
  matrix := ψ.matrix.castLE (by omega)
  matrix_isQF := ψ.matrix_isQF.castLE

theorem realize_tail_iff {α : Type*} {n r : ℕ} (ψ : PrenexFormula L α n (r + 1))
    {M : Type w} [L.Structure M] (v : α → M) (xs : Fin n → M) :
    ψ.toFormula.Realize v xs ↔ (applyQuant (ψ.prefixQ 0) ψ.tail.toFormula).Realize v xs := by
  rw [realize_toFormula_iff]
  have hcast : ∀ y : M,
      evalPrefix M (ψ.prefixQ ∘ Fin.succ)
        (fun ys => ψ.matrix.Realize v (appendVec xs (Fin.cons y ys))) ↔
      ψ.tail.toFormula.Realize v (Fin.snoc xs y) := by
    intro y
    rw [realize_toFormula_iff]
    refine evalPrefix_congr M (ψ.prefixQ ∘ Fin.succ) fun ys => ?_
    simp only [tail]
    rw [BoundedFormula.realize_castLE_of_eq (by omega : n + (r + 1) = n + 1 + r),
      appendVec_snoc_cons]
  cases hQ : ψ.prefixQ 0
  · rw [evalPrefix_succ_ex _ _ hQ, applyQuant_ex, BoundedFormula.realize_ex]
    exact exists_congr hcast
  · rw [evalPrefix_succ_all _ _ hQ, applyQuant_all, BoundedFormula.realize_all]
    exact forall_congr' hcast

/-- Insert an unused bound variable at slot `n` inside a `PrenexFormula`. -/
def liftOne {α : Type*} {n r : ℕ} (ψ : PrenexFormula L α n r) :
    PrenexFormula L α (n + 1) r where
  prefixQ := ψ.prefixQ
  matrix := (ψ.matrix.liftAt 1 n).castLE (by omega)
  matrix_isQF := ψ.matrix_isQF.liftAt.castLE

theorem realize_liftOne {α : Type*} {n r : ℕ} (ψ : PrenexFormula L α n r)
    {M : Type w} [L.Structure M] (v : α → M) (xs : Fin (n + 1) → M) :
    ψ.liftOne.toFormula.Realize v xs ↔ ψ.toFormula.Realize v (xs ∘ Fin.castSucc) := by
  rw [realize_toFormula_iff, realize_toFormula_iff]
  refine evalPrefix_congr M ψ.prefixQ fun ys => ?_
  simp only [liftOne]
  rw [BoundedFormula.realize_castLE_of_eq (by omega : n + r + 1 = n + 1 + r),
    BoundedFormula.realize_liftAt_one (by omega : n ≤ n + r)]
  refine iff_of_eq (congrArg (ψ.matrix.Realize v) ?_)
  ext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp only [Function.comp_apply, appendVec, Fin.addCases_left]
    split_ifs with h
    · have h1 : Fin.cast (by omega : n + r + 1 = n + 1 + r)
          (Fin.castAdd r a).castSucc = Fin.castAdd r a.castSucc := by ext; rfl
      rw [h1, Fin.addCases_left]
    · exfalso; exact h a.isLt
  · simp only [Function.comp_apply, appendVec, Fin.addCases_right]
    split_ifs with h
    · exfalso; have : n + b.1 < n := h; omega
    · have h1 : Fin.cast (by omega : n + r + 1 = n + 1 + r)
          (Fin.natAdd n b).succ = Fin.natAdd (n + 1) b := by
        ext; simp [Nat.add_assoc, Nat.add_comm 1]
      rw [h1, Fin.addCases_right]

/-- Combine two prenex formulas under implication while preserving total quantifier count
`q₁ + q₂` across all nonempty structures. -/
def prenexImp {α : Type*} :
    ∀ {n q₁ q₂ : ℕ}, PrenexFormula L α n q₁ → PrenexFormula L α n q₂ →
      PrenexFormula L α n (q₁ + q₂)
  | _, 0, 0, p₁, p₂ => ⟨Fin.elim0, p₁.matrix.imp p₂.matrix, p₁.matrix_isQF.imp p₂.matrix_isQF⟩
  | _, q₁ + 1, q₂, p₁, p₂ =>
    ((prenexImp p₁.tail p₂.liftOne).cons (p₁.prefixQ 0).dual).castPrefix (by omega)
  | _, 0, q₂ + 1, p₁, p₂ =>
    ((prenexImp p₁.liftOne p₂.tail).cons (p₂.prefixQ 0)).castPrefix (by omega)

theorem realize_prenexImp {α : Type*} {M : Type w} [L.Structure M] [Nonempty M] (v : α → M) :
    ∀ {n q₁ q₂ : ℕ} (p₁ : PrenexFormula L α n q₁) (p₂ : PrenexFormula L α n q₂)
      (xs : Fin n → M),
      (prenexImp p₁ p₂).toFormula.Realize v xs ↔
        (p₁.toFormula.Realize v xs → p₂.toFormula.Realize v xs)
  | _, 0, 0, p₁, p₂, xs => by
    simp only [prenexImp, toFormula, wrapPrefix, BoundedFormula.realize_imp]
  | _, q₁ + 1, q₂, p₁, p₂, xs => by
    simp only [prenexImp, realize_castPrefix, realize_cons]
    rw [realize_tail_iff p₁]
    have ih : ∀ y : M, (prenexImp p₁.tail p₂.liftOne).toFormula.Realize v (Fin.snoc xs y) ↔
        (p₁.tail.toFormula.Realize v (Fin.snoc xs y) → p₂.toFormula.Realize v xs) := by
      intro y
      rw [realize_prenexImp v p₁.tail p₂.liftOne (Fin.snoc xs y), realize_liftOne]
      have hcomp : (Fin.snoc xs y ∘ Fin.castSucc) = xs := by ext i; simp
      rw [hcomp]
    cases hQ : p₁.prefixQ 0
    · simp only [Quantifier.dual_ex, applyQuant_all, applyQuant_ex, BoundedFormula.realize_all,
        BoundedFormula.realize_ex, exists_imp]
      exact forall_congr' fun y => ih y
    · simp only [Quantifier.dual_all, applyQuant_ex, applyQuant_all, BoundedFormula.realize_ex,
        BoundedFormula.realize_all]
      constructor
      · rintro ⟨y, hy⟩ hall; exact (ih y).mp hy (hall y)
      · intro himp
        by_cases hall : ∀ y : M, p₁.tail.toFormula.Realize v (Fin.snoc xs y)
        · obtain ⟨y₀⟩ := ‹Nonempty M›; exact ⟨y₀, (ih y₀).mpr fun _ => himp hall⟩
        · push Not at hall; obtain ⟨y₀, hy₀⟩ := hall
          exact ⟨y₀, (ih y₀).mpr fun h => absurd h hy₀⟩
  | _, 0, q₂ + 1, p₁, p₂, xs => by
    simp only [prenexImp, realize_castPrefix, realize_cons]
    rw [realize_tail_iff p₂]
    have ih : ∀ y : M, (prenexImp p₁.liftOne p₂.tail).toFormula.Realize v (Fin.snoc xs y) ↔
        (p₁.toFormula.Realize v xs → p₂.tail.toFormula.Realize v (Fin.snoc xs y)) := by
      intro y
      rw [realize_prenexImp v p₁.liftOne p₂.tail (Fin.snoc xs y), realize_liftOne]
      have hcomp : (Fin.snoc xs y ∘ Fin.castSucc) = xs := by ext i; simp
      rw [hcomp]
    cases hQ : p₂.prefixQ 0
    · simp only [applyQuant_ex, BoundedFormula.realize_ex]
      constructor
      · rintro ⟨y, hy⟩ hp₁; exact ⟨y, (ih y).mp hy hp₁⟩
      · intro himp
        by_cases hp₁ : p₁.toFormula.Realize v xs
        · obtain ⟨y₀, hy₀⟩ := himp hp₁; exact ⟨y₀, (ih y₀).mpr fun _ => hy₀⟩
        · obtain ⟨y₀⟩ := ‹Nonempty M›; exact ⟨y₀, (ih y₀).mpr fun h => absurd h hp₁⟩
    · simp only [applyQuant_all, BoundedFormula.realize_all]
      exact ⟨fun h hp₁ y => (ih y).mp (h y) hp₁, fun h y => (ih y).mpr fun hp₁ => h hp₁ y⟩

/-- Convert any bounded formula `φ` into an equivalent `PrenexFormula` of exact prefix length
`quantifierCount φ`. -/
def ofBoundedFormula {α : Type*} :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n), PrenexFormula L α n (quantifierCount φ)
  | _, .falsum => ⟨Fin.elim0, .falsum, .falsum⟩
  | _, .equal t₁ t₂ => ⟨Fin.elim0, .equal t₁ t₂, (BoundedFormula.IsAtomic.equal t₁ t₂).isQF⟩
  | _, .rel R ts => ⟨Fin.elim0, .rel R ts, (BoundedFormula.IsAtomic.rel R ts).isQF⟩
  | _, .imp φ ψ => prenexImp (ofBoundedFormula φ) (ofBoundedFormula ψ)
  | _, .all φ => (ofBoundedFormula φ).cons .all

theorem realize_ofBoundedFormula {α : Type*} {M : Type w} [L.Structure M] [Nonempty M]
    (v : α → M) :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (xs : Fin n → M),
      (ofBoundedFormula φ).toFormula.Realize v xs ↔ φ.Realize v xs
  | _, .falsum, _ => by rw [ofBoundedFormula, toFormula]; rfl
  | _, .equal _ _, _ => by rw [ofBoundedFormula, toFormula]; rfl
  | _, .rel _ _, _ => by rw [ofBoundedFormula, toFormula]; rfl
  | _, .imp φ ψ, xs => by
    change (prenexImp (ofBoundedFormula φ) (ofBoundedFormula ψ)).toFormula.Realize v xs ↔ _
    rw [realize_prenexImp, realize_ofBoundedFormula v φ xs, realize_ofBoundedFormula v ψ xs,
      BoundedFormula.realize_imp]
  | _, .all φ, xs => by
    change ((ofBoundedFormula φ).cons .all).toFormula.Realize v xs ↔ _
    rw [realize_cons, applyQuant_all, BoundedFormula.realize_all]
    exact forall_congr' fun y => realize_ofBoundedFormula v φ (Fin.snoc xs y)

/-- Pad a `PrenexFormula` with `d` dummy universal quantifiers. -/
def padAdd {α : Type*} {n q : ℕ} (d : ℕ) (ψ : PrenexFormula L α n q) :
    PrenexFormula L α n (q + d) :=
  match d with
  | 0 => ψ
  | d + 1 => (padAdd d ψ).liftOne.cons .all

theorem realize_padAdd {α : Type*} {M : Type w} [L.Structure M] [Nonempty M] (v : α → M) :
    ∀ {n q : ℕ} (d : ℕ) (ψ : PrenexFormula L α n q) (xs : Fin n → M),
      (padAdd d ψ).toFormula.Realize v xs ↔ ψ.toFormula.Realize v xs
  | _, _, 0, _, _ => Iff.rfl
  | _, _, d + 1, ψ, xs => by
    simp only [padAdd, realize_cons, applyQuant_all, BoundedFormula.realize_all, realize_liftOne]
    have hcomp : ∀ y : M, (Fin.snoc xs y ∘ Fin.castSucc) = xs := fun _ => by ext i; simp
    simp only [hcomp, realize_padAdd v d ψ xs]
    exact forall_const M

/-- Pad a `PrenexFormula` of prefix length `q` to target length `r` given `q ≤ r`. -/
def padTo {α : Type*} {n q r : ℕ} (h : q ≤ r) (ψ : PrenexFormula L α n q) :
    PrenexFormula L α n r :=
  (ψ.padAdd (r - q)).castPrefix (Nat.add_sub_of_le h)

theorem realize_padTo {α : Type*} {n q r : ℕ} (h : q ≤ r) (ψ : PrenexFormula L α n q)
    {M : Type w} [L.Structure M] [Nonempty M] (v : α → M) (xs : Fin n → M) :
    (ψ.padTo h).toFormula.Realize v xs ↔ ψ.toFormula.Realize v xs := by
  rw [padTo, realize_castPrefix, realize_padAdd]

/-- Every sentence `φ` with `quantifierCount φ ≤ r` is equivalent across all nonempty
`L`-structures to a `PrenexSentence L r` of exact quantifier count `r`. -/
theorem exists_prenexSentence_of_quantifierCount_le {r : ℕ} (φ : L.Sentence)
    (hφ : quantifierCount φ ≤ r) :
    ∃ ψ : PrenexSentence L r,
      ∀ (M : Type w) [L.Structure M] [Nonempty M], M ⊨ ψ.toFormula ↔ M ⊨ φ := by
  refine ⟨(ofBoundedFormula φ).padTo hφ, fun M _ _ => ?_⟩
  simp only [Sentence.Realize, Formula.Realize]
  exact (realize_padTo hφ (ofBoundedFormula φ) default default).trans
    (realize_ofBoundedFormula default φ default)

end PrenexFormula

end Prenex

end Cslib.Logic.FO
