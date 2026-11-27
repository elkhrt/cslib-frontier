/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.WeightedCircuit
public import CslibFrontier.Foundations.LinearAlgebra.FreeAlgebraMinDegree

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Tactic.Linarith

/-!
# Palindrome Polynomial, $X,Y$-Decomposition, and Coefficient Spaces

This module formalizes the palindrome polynomial $\mathrm{Pal}_{n,d}(X,Y) \in F\langle X, Y\rangle$,
the five-part monomial decomposition $\widehat g = \widehat g_1 + \widehat g_X + \widehat g_Y +
\widehat g_{XY} + \widehat g_{\mathrm{other}}$, its exact product identities,
the coefficient map $\mathrm{coeff}_m$ and set $\mathrm{Coeff}_X(f)$, and the
dimension identity $\dim_F \mathrm{span}(\mathrm{Coeff}_X(\mathrm{Pal}_{n,n}(X,Y))) = n^n$.

## Main definitions

* `CslibFrontier.Circuits.Arithmetic.Noncommutative.palPoly`: the palindrome polynomial
  $\mathrm{Pal}_{n,d}(X, Y)$.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.WordKind`, `wordKind`: five-way classification
  of monomials in
  `FreeMonoid (Fin n ⊕ Fin n)`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.partKind`, `partOne`, `partX`, `partY`,
  `partXY`, `partOther`:
  the five linear projections on `FreeAlgebra F (Fin n ⊕ Fin n)`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.embedX`, `extractX`: canonical embedding of
  `FreeAlgebra F (Fin n)`
  and extraction of the `X`-only part as an element of `FreeAlgebra F (Fin n)`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.coeffY`, `coeffXSet`: the $Y$-monomial
  coefficient linear map
  $\mathrm{coeff}_m$ and the coefficient set $\mathrm{Coeff}_X(f)$.

## Main results

* `CslibFrontier.Circuits.Arithmetic.Noncommutative.partOne_mul`, `partX_mul`, `partY_mul`,
  `partXY_mul`: exact
  product identities for the five-part decomposition.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.finrank_span_coeffXSet_palPoly`:
  $\dim_F \mathrm{span}(\mathrm{Coeff}_X(\mathrm{Pal}_{n,n}(X,Y))) = n^n$.
-/

public section

namespace CslibFrontier.Circuits.Arithmetic.Noncommutative

open _root_.FreeAlgebra

section Palindrome

variable (F : Type*) [CommSemiring F]

/-- The palindrome polynomial $\mathrm{Pal}_{n,d}(X,Y) \in F\langle X, Y\rangle$, where `Sum.inl i`
denotes $x_i$ and `Sum.inr i` denotes $y_i$. -/
@[expose] noncomputable def palPoly (n d : ℕ) : FreeAlgebra F (Fin n ⊕ Fin n) :=
  ∑ u : Fin d → Fin n,
    FreeMonoid.lift (ι F)
      (FreeMonoid.ofFn (Sum.inl ∘ u) * FreeMonoid.ofFn (Sum.inr ∘ (u ∘ Fin.rev)))

/-- `palPoly F n 0 = 1`. -/
@[simp]
theorem palPoly_zero (n : ℕ) : palPoly F n 0 = 1 := by
  simp [palPoly]

/-- Recursive identity $\mathrm{Pal}_{n,d+1}(X,Y) = \sum_{i} x_i \mathrm{Pal}_{n,d}(X,Y) y_i$. -/
theorem palPoly_succ (n d : ℕ) :
    palPoly F n (d + 1) =
      ∑ i : Fin n, ι F (Sum.inl i) * palPoly F n d * ι F (Sum.inr i) := by
  rw [palPoly, palPoly]
  rw [← (Fin.consEquiv fun _ ↦ Fin n).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  have hL : (Sum.inl : Fin n → Fin n ⊕ Fin n) ∘ (Fin.cons i u : Fin (d + 1) → Fin n) =
      Fin.cons (Sum.inl i) ((Sum.inl : Fin n → Fin n ⊕ Fin n) ∘ u) := by
    funext j
    refine Fin.cases rfl (fun _ ↦ rfl) j
  have hR : (Sum.inr : Fin n → Fin n ⊕ Fin n) ∘
        ((Fin.cons i u : Fin (d + 1) → Fin n) ∘ Fin.rev) =
      (Fin.cons (Sum.inr i) ((Sum.inr : Fin n → Fin n ⊕ Fin n) ∘ u)) ∘ Fin.rev := by
    funext j
    simp only [Function.comp_apply]
    refine Fin.cases rfl (fun _ ↦ rfl) j.rev
  simp only [Fin.consEquiv_apply, hL, hR, FreeMonoid.ofFn_cons, FreeMonoid.ofFn_cons_comp_rev,
    map_mul, FreeMonoid.lift_eval_of, mul_assoc]
  rfl

/-- The coefficient of `u · rev(v)` (with `u` in `X` and `v` in `Y`, both of length `d`) in
`palPoly F n d` is `1` if `u = v` and `0` otherwise. -/
theorem coeff_palPoly_ofFn (n d : ℕ) (a b : Fin d → Fin n) :
    FreeAlgebra.coeff (FreeMonoid.ofFn (Sum.inl ∘ a) * FreeMonoid.ofFn (Sum.inr ∘ b))
      (palPoly F n d) = if a ∘ Fin.rev = b then 1 else 0 := by
  classical
  rw [palPoly, map_sum, Finset.sum_eq_single a]
  · rw [coeff_lift_ι]
    split_ifs with h
    · simp [h]
    · refine Finsupp.single_eq_of_ne' fun h' ↦ h ?_
      have hinj := (FreeMonoid.ofFn_mul_ofFn_injective h').2
      funext j
      simpa using congrFun hinj j
  · intro u _ hu
    rw [coeff_lift_ι]
    refine Finsupp.single_eq_of_ne' fun h' ↦ hu ?_
    have hinj := (FreeMonoid.ofFn_mul_ofFn_injective h').1
    funext j
    simpa using congrFun hinj j
  · simp

end Palindrome

section WordClassification

/-- Five-way classification of monomials in $F\langle X, Y\rangle$. -/
inductive WordKind where
  /-- The empty word `1`. -/
  | one
  /-- Nonempty word containing only `X`-variables. -/
  | onlyX
  /-- Nonempty word containing only `Y`-variables. -/
  | onlyY
  /-- Nonempty word containing both `X` and `Y` with every `X` before every `Y`. -/
  | xy
  /-- Any word containing some `Y`-variable before some `X`-variable. -/
  | other
  deriving DecidableEq

/-- `WordKind` has 5 elements and is a `Fintype`. -/
instance instFintypeWordKind : Fintype WordKind where
  elems := {.one, .onlyX, .onlyY, .xy, .other}
  complete := fun k ↦ by cases k <;> simp

private theorem freeMonoid_ext {γ : Type*} {u v : FreeMonoid γ} (h : u.toList = v.toList) :
    u = v := by
  rw [← FreeMonoid.ofList_toList u, ← FreeMonoid.ofList_toList v, h]

private theorem freeMonoid_eq_one_of_toList {γ : Type*} {u : FreeMonoid γ} (h : u.toList = []) :
    u = 1 :=
  freeMonoid_ext h

/-- Check whether every letter of a list is an `X`-variable (`Sum.inl`). -/
def isAllX {α β : Type*} : List (α ⊕ β) → Bool
  | [] => true
  | .inl _ :: t => isAllX t
  | .inr _ :: _ => false

/-- Check whether every letter of a list is a `Y`-variable (`Sum.inr`). -/
def isAllY {α β : Type*} : List (α ⊕ β) → Bool
  | [] => true
  | .inl _ :: _ => false
  | .inr _ :: t => isAllY t

/-- Check whether a list has all `X`-variables before all `Y`-variables. -/
def isSeparatedList {α β : Type*} : List (α ⊕ β) → Bool
  | [] => true
  | .inl _ :: t => isSeparatedList t
  | .inr _ :: t => isAllY t

@[simp]
private theorem isAllX_append {α β : Type*} (l₁ l₂ : List (α ⊕ β)) :
    isAllX (l₁ ++ l₂) = (isAllX l₁ && isAllX l₂) := by
  induction l₁ with
  | nil => simp [isAllX]
  | cons x t ih => cases x <;> simp [isAllX, ih]

@[simp]
private theorem isAllY_append {α β : Type*} (l₁ l₂ : List (α ⊕ β)) :
    isAllY (l₁ ++ l₂) = (isAllY l₁ && isAllY l₂) := by
  induction l₁ with
  | nil => simp [isAllY]
  | cons x t ih => cases x <;> simp [isAllY, ih]

private theorem isSeparatedList_of_isAllY {α β : Type*} {l : List (α ⊕ β)}
    (h : isAllY l = true) : isSeparatedList l = true := by
  cases l with
  | nil => rfl
  | cons x t =>
    cases x with
    | inl _ => simp [isAllY] at h
    | inr _ => simpa [isSeparatedList, isAllY] using h

private theorem isSeparatedList_append {α β : Type*} (l₁ l₂ : List (α ⊕ β)) :
    isSeparatedList (l₁ ++ l₂) =
      if isAllX l₁ then isSeparatedList l₂ else (isSeparatedList l₁ && isAllY l₂) := by
  induction l₁ with
  | nil => simp [isAllX]
  | cons x t ih =>
    cases x with
    | inl _ =>
      simp only [List.cons_append, isSeparatedList, isAllX, ih]
      by_cases h : isAllX t = true <;> simp [h]
    | inr _ =>
      simp [List.cons_append, isSeparatedList, isAllX]

private theorem not_isAllX_and_isAllY {α β : Type*} {l : List (α ⊕ β)} (hne : l ≠ [])
    (hx : isAllX l = true) (hy : isAllY l = true) : False := by
  cases l with
  | nil => exact hne rfl
  | cons x _ => cases x <;> simp [isAllX, isAllY] at hx hy

/-- The `WordKind` of a word in `FreeMonoid (α ⊕ β)`. -/
def wordKind {α β : Type*} (w : FreeMonoid (α ⊕ β)) : WordKind :=
  match w.toList with
  | [] => .one
  | l =>
    if isAllX l then .onlyX
    else if isAllY l then .onlyY
    else if isSeparatedList l then .xy
    else .other

/-- Multiplication table on `WordKind`. -/
def mulWordKind : WordKind → WordKind → WordKind
  | .one, k => k
  | k, .one => k
  | .onlyX, .onlyX => .onlyX
  | .onlyX, .onlyY => .xy
  | .onlyX, .xy => .xy
  | .onlyX, .other => .other
  | .onlyY, .onlyY => .onlyY
  | .onlyY, .onlyX => .other
  | .onlyY, .xy => .other
  | .onlyY, .other => .other
  | .xy, .onlyY => .xy
  | .xy, .onlyX => .other
  | .xy, .xy => .other
  | .xy, .other => .other
  | .other, .onlyX => .other
  | .other, .onlyY => .other
  | .other, .xy => .other
  | .other, .other => .other

/-- `wordKind` is a monoid homomorphism into `mulWordKind`. -/
theorem wordKind_mul {α β : Type*} (u v : FreeMonoid (α ⊕ β)) :
    wordKind (u * v) = mulWordKind (wordKind u) (wordKind v) := by
  unfold wordKind
  rw [FreeMonoid.toList_mul]
  cases hu : u.toList with
  | nil => simp [mulWordKind]
  | cons x t =>
    cases hv : v.toList with
    | nil =>
      rw [List.append_nil]
      cases hx : isAllX (x :: t) <;> cases hy : isAllY (x :: t) <;>
        cases hs : isSeparatedList (x :: t) <;> simp [mulWordKind, hx, hy, hs]
    | cons y s =>
      have hne_app : (x :: t) ++ (y :: s) ≠ [] := by simp
      have hmatch :
          (match (x :: t) ++ (y :: s) with
            | [] => WordKind.one
            | l =>
              if isAllX l = true then WordKind.onlyX
              else if isAllY l = true then WordKind.onlyY
              else if isSeparatedList l = true then WordKind.xy
              else WordKind.other) =
          (if isAllX ((x :: t) ++ (y :: s)) = true then WordKind.onlyX
            else if isAllY ((x :: t) ++ (y :: s)) = true then WordKind.onlyY
            else if isSeparatedList ((x :: t) ++ (y :: s)) = true then WordKind.xy
            else WordKind.other) := by
        cases hm : (x :: t) ++ (y :: s) with
        | nil => exact absurd hm hne_app
        | cons _ _ => rfl
      rw [hmatch]
      have hne1 : x :: t ≠ [] := List.cons_ne_nil _ _
      have hne2 : y :: s ≠ [] := List.cons_ne_nil _ _
      have hsep_x : isAllX (x :: t) = true → isSeparatedList (x :: t) = true := by
        intro hx
        rw [← List.append_nil (x :: t), isSeparatedList_append, hx]
        rfl
      have hsep_x2 : isAllX (y :: s) = true → isSeparatedList (y :: s) = true := by
        intro hx
        rw [← List.append_nil (y :: s), isSeparatedList_append, hx]
        rfl
      rw [isAllX_append, isAllY_append, isSeparatedList_append]
      cases hx1 : isAllX (x :: t) <;> cases hy1 : isAllY (x :: t) <;>
        cases hs1 : isSeparatedList (x :: t) <;>
        cases hx2 : isAllX (y :: s) <;> cases hy2 : isAllY (y :: s) <;>
        cases hs2 : isSeparatedList (y :: s)
      all_goals
        first
        | exact False.elim (not_isAllX_and_isAllY hne1 hx1 hy1)
        | exact False.elim (not_isAllX_and_isAllY hne2 hx2 hy2)
        | exact absurd (isSeparatedList_of_isAllY hy1) (by rw [hs1]; decide)
        | exact absurd (isSeparatedList_of_isAllY hy2) (by rw [hs2]; decide)
        | exact absurd (hsep_x hx1) (by rw [hs1]; decide)
        | exact absurd (hsep_x2 hx2) (by rw [hs2]; decide)
        | simp [mulWordKind, hx1, hy1, hs1, hx2, hy2, hs2]

/-- Map a word in `FreeMonoid α` to `FreeMonoid (α ⊕ β)` via `Sum.inl`. -/
def wordInl {α β : Type*} : FreeMonoid α →* FreeMonoid (α ⊕ β) :=
  FreeMonoid.map Sum.inl

/-- Map a word in `FreeMonoid β` to `FreeMonoid (α ⊕ β)` via `Sum.inr`. -/
def wordInr {α β : Type*} : FreeMonoid β →* FreeMonoid (α ⊕ β) :=
  FreeMonoid.map Sum.inr

private theorem isAllX_wordInl {α β : Type*} (u : FreeMonoid α) :
    isAllX (wordInl (β := β) u).toList = true := by
  have h : (wordInl (β := β) u).toList = u.toList.map Sum.inl := by
    simp [wordInl]
  rw [h]
  induction u.toList with
  | nil => rfl
  | cons a t ih => simpa [isAllX] using ih

private theorem isAllY_wordInr {α β : Type*} (v : FreeMonoid β) :
    isAllY (wordInr (α := α) v).toList = true := by
  have h : (wordInr (α := α) v).toList = v.toList.map Sum.inr := by
    simp [wordInr]
  rw [h]
  induction v.toList with
  | nil => rfl
  | cons b t ih => simpa [isAllY] using ih

private theorem wordKind_wordInl_ne_one {α β : Type*} {u : FreeMonoid α} (hu : u ≠ 1) :
    wordKind (wordInl (β := β) u) = .onlyX := by
  unfold wordKind
  have hne : (wordInl (β := β) u).toList ≠ [] := by
    intro h
    apply hu
    have hmap : u.toList.map (Sum.inl : α → α ⊕ β) = [] := by simpa [wordInl] using h
    have hu0 : u.toList = [] := List.map_eq_nil_iff.mp hmap
    exact freeMonoid_eq_one_of_toList hu0
  have hall := isAllX_wordInl (β := β) u
  cases hl : (wordInl (β := β) u).toList with
  | nil => exact absurd hl hne
  | cons a t =>
    rw [hl] at hall
    simp [hall]

private theorem wordKind_wordInr_ne_one {α β : Type*} {v : FreeMonoid β} (hv : v ≠ 1) :
    wordKind (wordInr (α := α) v) = .onlyY := by
  unfold wordKind
  have hne : (wordInr (α := α) v).toList ≠ [] := by
    intro h
    apply hv
    have hmap : v.toList.map (Sum.inr : β → α ⊕ β) = [] := by simpa [wordInr] using h
    have hv0 : v.toList = [] := List.map_eq_nil_iff.mp hmap
    exact freeMonoid_eq_one_of_toList hv0
  have hall := isAllY_wordInr (α := α) v
  cases hl : (wordInr (α := α) v).toList with
  | nil => exact absurd hl hne
  | cons b t =>
    rw [hl] at hall
    have hnotx : isAllX (b :: t) = false := by
      cases h : isAllX (b :: t)
      · rfl
      · exact False.elim (not_isAllX_and_isAllY (List.cons_ne_nil _ _) h hall)
    simp [hnotx, hall]

private theorem wordKind_wordInl_mul_wordInr {α β : Type*} {u : FreeMonoid α} {v : FreeMonoid β}
    (hu : u ≠ 1) (hv : v ≠ 1) :
    wordKind (wordInl u * wordInr v) = .xy := by
  rw [wordKind_mul, wordKind_wordInl_ne_one hu, wordKind_wordInr_ne_one hv]
  rfl

private theorem exists_wordInl_of_wordKind_onlyX {α β : Type*} {w : FreeMonoid (α ⊕ β)}
    (hw : wordKind w = .onlyX) : ∃ u : FreeMonoid α, u ≠ 1 ∧ wordInl u = w := by
  have haux : ∀ l : List (α ⊕ β), isAllX l = true → ∃ l' : List α, l'.map Sum.inl = l := by
    intro l
    induction l with
    | nil => intro _; exact ⟨[], rfl⟩
    | cons x t ih =>
      cases x with
      | inl a =>
        intro hx
        obtain ⟨l', hl'⟩ := ih hx
        exact ⟨a :: l', by simp [hl']⟩
      | inr _ => intro hx; simp [isAllX] at hx
  unfold wordKind at hw
  cases hl : w.toList with
  | nil => rw [hl] at hw; cases hw
  | cons x t =>
    rw [hl] at hw
    by_cases hx : isAllX (x :: t) = true
    · obtain ⟨l', hl'⟩ := haux (x :: t) hx
      refine ⟨FreeMonoid.ofList l', ?_, ?_⟩
      · intro h0
        have hl0 : l' = [] := by simpa using congrArg FreeMonoid.toList h0
        rw [hl0] at hl'
        exact List.cons_ne_nil _ _ hl'.symm
      · apply freeMonoid_ext
        simpa [wordInl, hl] using hl'
    · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hw
      split_ifs at hw

private theorem exists_wordInr_of_wordKind_onlyY {α β : Type*} {w : FreeMonoid (α ⊕ β)}
    (hw : wordKind w = .onlyY) : ∃ v : FreeMonoid β, v ≠ 1 ∧ wordInr v = w := by
  have haux : ∀ l : List (α ⊕ β), isAllY l = true → ∃ l' : List β, l'.map Sum.inr = l := by
    intro l
    induction l with
    | nil => intro _; exact ⟨[], rfl⟩
    | cons x t ih =>
      cases x with
      | inl _ => intro hy; simp [isAllY] at hy
      | inr b =>
        intro hy
        obtain ⟨l', hl'⟩ := ih hy
        exact ⟨b :: l', by simp [hl']⟩
  unfold wordKind at hw
  cases hl : w.toList with
  | nil => rw [hl] at hw; cases hw
  | cons x t =>
    rw [hl] at hw
    by_cases hx : isAllX (x :: t) = true
    · simp [hx] at hw
    · by_cases hy : isAllY (x :: t) = true
      · obtain ⟨l', hl'⟩ := haux (x :: t) hy
        refine ⟨FreeMonoid.ofList l', ?_, ?_⟩
        · intro h0
          have hl0 : l' = [] := by simpa using congrArg FreeMonoid.toList h0
          rw [hl0] at hl'
          exact List.cons_ne_nil _ _ hl'.symm
        · apply freeMonoid_ext
          simpa [wordInr, hl] using hl'
      · simp only [hx, hy, Bool.false_eq_true, ↓reduceIte] at hw
        split_ifs at hw

private theorem exists_wordInl_wordInr_of_wordKind_xy {α β : Type*} {w : FreeMonoid (α ⊕ β)}
    (hw : wordKind w = .xy) :
    ∃ (u : FreeMonoid α) (v : FreeMonoid β), u ≠ 1 ∧ v ≠ 1 ∧ wordInl u * wordInr v = w := by
  have haux : ∀ l : List (α ⊕ β), isSeparatedList l = true →
      ∃ (l₁ : List α) (l₂ : List β), l₁.map Sum.inl ++ l₂.map Sum.inr = l := by
    intro l
    induction l with
    | nil => intro _; exact ⟨[], [], rfl⟩
    | cons x t ih =>
      cases x with
      | inl a =>
        intro hs
        obtain ⟨l₁, l₂, hl⟩ := ih hs
        exact ⟨a :: l₁, l₂, by simp [hl]⟩
      | inr b =>
        intro hs
        have hy : isAllY t = true := hs
        have hY : ∀ s : List (α ⊕ β), isAllY s = true → ∃ l₂ : List β, l₂.map Sum.inr = s := by
          intro s
          induction s with
          | nil => intro _; exact ⟨[], rfl⟩
          | cons y r ihr =>
            cases y with
            | inl _ => intro h; simp [isAllY] at h
            | inr c =>
              intro h
              obtain ⟨l₂, hl₂⟩ := ihr h
              exact ⟨c :: l₂, by simp [hl₂]⟩
        obtain ⟨l₂, hl₂⟩ := hY t hy
        exact ⟨[], b :: l₂, by simp [hl₂]⟩
  unfold wordKind at hw
  cases hl : w.toList with
  | nil => rw [hl] at hw; cases hw
  | cons x t =>
    rw [hl] at hw
    by_cases hx : isAllX (x :: t) = true
    · simp [hx] at hw
    · by_cases hy : isAllY (x :: t) = true
      · simp [hx, hy] at hw
      · by_cases hs : isSeparatedList (x :: t) = true
        · obtain ⟨l₁, l₂, hsplit⟩ := haux (x :: t) hs
          refine ⟨FreeMonoid.ofList l₁, FreeMonoid.ofList l₂, ?_, ?_, ?_⟩
          · intro h0
            have hl1 : l₁ = [] := by simpa using congrArg FreeMonoid.toList h0
            rw [hl1] at hsplit
            have : isAllY (x :: t) = true := by
              rw [← hsplit]
              have h := isAllY_wordInr (α := α) (FreeMonoid.ofList l₂)
              simpa [wordInr] using h
            exact hy this
          · intro h0
            have hl2 : l₂ = [] := by simpa using congrArg FreeMonoid.toList h0
            rw [hl2] at hsplit
            have : isAllX (x :: t) = true := by
              rw [← hsplit]
              have h := isAllX_wordInl (β := β) (FreeMonoid.ofList l₁)
              simpa [wordInl] using h
            exact hx this
          · apply freeMonoid_ext
            simpa [wordInl, wordInr, hl] using hsplit
        · simp [hx, hy, hs] at hw

private theorem wordInl_mul_wordInr_inj {α β : Type*} {u₁ u₂ : FreeMonoid α}
    {v₁ v₂ : FreeMonoid β} (h : wordInl u₁ * wordInr v₁ = wordInl u₂ * wordInr v₂) :
    u₁ = u₂ ∧ v₁ = v₂ := by
  have hl := congrArg FreeMonoid.toList h
  simp only [FreeMonoid.toList_mul, wordInl, wordInr, FreeMonoid.toList_map] at hl
  have haux : ∀ (a₁ a₂ : List α) (b₁ b₂ : List β),
      a₁.map Sum.inl ++ b₁.map Sum.inr = a₂.map Sum.inl ++ b₂.map Sum.inr →
        a₁ = a₂ ∧ b₁ = b₂ := by
    intro a₁
    induction a₁ with
    | nil =>
      intro a₂ b₁ b₂ heq
      cases a₂ with
      | nil =>
        simp only [List.map_nil, List.nil_append] at heq
        exact ⟨rfl, List.map_injective_iff.mpr Sum.inr_injective heq⟩
      | cons a t =>
        cases b₁ with
        | nil => simp at heq
        | cons b s => simp at heq
    | cons a t ih =>
      intro a₂ b₁ b₂ heq
      cases a₂ with
      | nil =>
        cases b₂ with
        | nil => simp at heq
        | cons b s => simp at heq
      | cons a' t' =>
        simp only [List.map_cons, List.cons_append, List.cons.injEq, Sum.inl.injEq] at heq
        obtain ⟨rfl, hrest⟩ := heq
        obtain ⟨ht, hb⟩ := ih t' b₁ b₂ hrest
        exact ⟨congrArg (List.cons a) ht, hb⟩
  obtain ⟨hu, hv⟩ := haux _ _ _ _ hl
  exact ⟨freeMonoid_ext hu, freeMonoid_ext hv⟩

end WordClassification

section FivePartDecomposition

variable {F : Type*} [CommSemiring F] {n : ℕ}

/-- Linear projection onto monomials of a given `WordKind`. -/
noncomputable def partKind (k : WordKind) :
    FreeAlgebra F (Fin n ⊕ Fin n) →ₗ[F] FreeAlgebra F (Fin n ⊕ Fin n) :=
  (basisFreeMonoid F (Fin n ⊕ Fin n)).constr F fun w ↦
    if wordKind w = k then basisFreeMonoid F (Fin n ⊕ Fin n) w else 0

/-- Coefficient of `w` in `partKind k f`. -/
@[simp]
theorem coeff_partKind (k : WordKind) (w : FreeMonoid (Fin n ⊕ Fin n))
    (f : FreeAlgebra F (Fin n ⊕ Fin n)) :
    FreeAlgebra.coeff w (partKind k f) =
      if wordKind w = k then FreeAlgebra.coeff w f else 0 := by
  let lhs : FreeAlgebra F (Fin n ⊕ Fin n) →ₗ[F] F :=
    (FreeAlgebra.coeff w).comp (partKind k)
  let rhs : FreeAlgebra F (Fin n ⊕ Fin n) →ₗ[F] F :=
    if wordKind w = k then FreeAlgebra.coeff w else 0
  have h : lhs = rhs := by
    apply (basisFreeMonoid F (Fin n ⊕ Fin n)).ext
    intro u
    change FreeAlgebra.coeff w (partKind k (basisFreeMonoid F (Fin n ⊕ Fin n) u)) = rhs _
    rw [partKind, Module.Basis.constr_basis]
    by_cases hu : wordKind u = k <;> by_cases hw : wordKind w = k
    · simp [rhs, hu, hw]
    · simp only [rhs, hu, hw, ↓reduceIte, LinearMap.zero_apply]
      rw [basisFreeMonoid_apply, coeff_lift_ι]
      exact Finsupp.single_eq_of_ne (fun h' ↦ hw (h' ▸ hu))
    · simp only [rhs, hu, hw, ↓reduceIte, map_zero]
      rw [basisFreeMonoid_apply, coeff_lift_ι]
      symm
      exact Finsupp.single_eq_of_ne (by rintro rfl; exact hu hw)
    · simp [rhs, hu, hw]
  have hf := DFunLike.congr_fun h f
  change FreeAlgebra.coeff w (partKind k f) = rhs f at hf
  rw [hf]
  by_cases hw : wordKind w = k <;> simp [rhs, hw]

/-- Constant part $\widehat g_1$. -/
noncomputable abbrev partOne :
    FreeAlgebra F (Fin n ⊕ Fin n) →ₗ[F] FreeAlgebra F (Fin n ⊕ Fin n) :=
  partKind .one

/-- Non-constant $X$-only part $\widehat g_X$. -/
noncomputable abbrev partX :
    FreeAlgebra F (Fin n ⊕ Fin n) →ₗ[F] FreeAlgebra F (Fin n ⊕ Fin n) :=
  partKind .onlyX

/-- Non-constant $Y$-only part $\widehat g_Y$. -/
noncomputable abbrev partY :
    FreeAlgebra F (Fin n ⊕ Fin n) →ₗ[F] FreeAlgebra F (Fin n ⊕ Fin n) :=
  partKind .onlyY

/-- Separated $XY$ part $\widehat g_{XY}$. -/
noncomputable abbrev partXY :
    FreeAlgebra F (Fin n ⊕ Fin n) →ₗ[F] FreeAlgebra F (Fin n ⊕ Fin n) :=
  partKind .xy

/-- Remaining monomials $\widehat g_{\mathrm{other}}$. -/
noncomputable abbrev partOther :
    FreeAlgebra F (Fin n ⊕ Fin n) →ₗ[F] FreeAlgebra F (Fin n ⊕ Fin n) :=
  partKind .other

/-- Five-part direct-sum decomposition $\widehat g = \widehat g_1 + \widehat g_X + \widehat g_Y +
\widehat g_{XY} + \widehat g_{\mathrm{other}}$. -/
theorem part_decomposition (f : FreeAlgebra F (Fin n ⊕ Fin n)) :
    partOne f + partX f + partY f + partXY f + partOther f = f := by
  apply ext_coeff
  intro w
  simp only [map_add, coeff_partKind]
  cases wordKind w <;> simp

/-- `partOne f` is a scalar multiple of `1` (namely `(coeff 1 f) • 1`). -/
theorem partOne_eq_smul_one (f : FreeAlgebra F (Fin n ⊕ Fin n)) :
    partOne f = FreeAlgebra.coeff (1 : FreeMonoid (Fin n ⊕ Fin n)) f • 1 := by
  apply ext_coeff
  intro w
  rw [coeff_partKind, map_smul, coeff_one, smul_eq_mul]
  by_cases hw : w = 1
  · subst hw
    simp [wordKind]
  · have hwk : wordKind w ≠ .one := by
      unfold wordKind
      cases hl : w.toList with
      | nil => exact absurd (freeMonoid_eq_one_of_toList hl) hw
      | cons x t =>
        dsimp only
        split_ifs <;> simp
    simp [hwk, Ne.symm hw]

/-- Product rule for `partKind`: `partKind k (a * b)` is the sum of `partKind k₁ a * partKind k₂ b`
over all pairs `(k₁, k₂)` with `mulWordKind k₁ k₂ = k`. -/
theorem partKind_mul (k : WordKind) (a b : FreeAlgebra F (Fin n ⊕ Fin n)) :
    partKind k (a * b) =
      ∑ p ∈ (Finset.univ : Finset (WordKind × WordKind)).filter
        (fun p ↦ mulWordKind p.1 p.2 = k),
        partKind p.1 a * partKind p.2 b := by
  classical
  have hdecomp : a * b =
      ∑ p ∈ (Finset.univ : Finset (WordKind × WordKind)),
        partKind p.1 a * partKind p.2 b := by
    have ha : a = partOne a + partX a + partY a + partXY a + partOther a :=
      (part_decomposition a).symm
    have hb : b = partOne b + partX b + partY b + partXY b + partOther b :=
      (part_decomposition b).symm
    have hsum : ∀ x : FreeAlgebra F (Fin n ⊕ Fin n),
        ∑ k' ∈ (Finset.univ : Finset WordKind), partKind k' x = x := by
      intro x
      have huniv : (Finset.univ : Finset WordKind) =
          {.one, .onlyX, .onlyY, .xy, .other} := by
        ext k'; cases k' <;> simp
      rw [huniv]
      simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
        reduceCtorEq, or_self, not_false_eq_true, Finset.sum_singleton]
      have := part_decomposition x
      abel_nf at this ⊢
      exact this
    conv_lhs => rw [← hsum a, ← hsum b]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Fintype.sum_prod_type']
  apply ext_coeff
  intro w
  rw [coeff_partKind]
  conv_lhs => rw [hdecomp]
  rw [map_sum, map_sum]
  split_ifs with hwk
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    split_ifs with hp
    · rfl
    · rw [coeff_mul]
      apply Finset.sum_eq_zero
      intro i _
      rw [coeff_partKind, coeff_partKind]
      split_ifs with h1 h2
      · exfalso
        apply hp
        have hmul :
            FreeMonoid.ofList (w.toList.take i) * FreeMonoid.ofList (w.toList.drop i) = w := by
          apply freeMonoid_ext
          simp
        have := wordKind_mul (FreeMonoid.ofList (w.toList.take i))
          (FreeMonoid.ofList (w.toList.drop i))
        rw [hmul, h1, h2, hwk] at this
        exact this.symm
      · simp
      · simp
      · simp
  · symm
    apply Finset.sum_eq_zero
    intro p hp
    have hpm : mulWordKind p.1 p.2 = k := (Finset.mem_filter.mp hp).2
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro i _
    rw [coeff_partKind, coeff_partKind]
    split_ifs with h1 h2
    · exfalso
      apply hwk
      have hmul :
          FreeMonoid.ofList (w.toList.take i) * FreeMonoid.ofList (w.toList.drop i) = w := by
        apply freeMonoid_ext
        simp
      have := wordKind_mul (FreeMonoid.ofList (w.toList.take i))
        (FreeMonoid.ofList (w.toList.drop i))
      rw [hmul, h1, h2, hpm] at this
      exact this
    · simp
    · simp
    · simp

private theorem filter_mulWordKind_one :
    (Finset.univ : Finset (WordKind × WordKind)).filter (fun p ↦ mulWordKind p.1 p.2 = .one) =
      {(.one, .one)} := by
  ext ⟨k₁, k₂⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Prod.mk.injEq]; cases k₁ <;> cases k₂ <;> decide

private theorem filter_mulWordKind_onlyX :
    (Finset.univ : Finset (WordKind × WordKind)).filter (fun p ↦ mulWordKind p.1 p.2 = .onlyX) =
      {(.onlyX, .onlyX), (.onlyX, .one), (.one, .onlyX)} := by
  ext ⟨k₁, k₂⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]; cases k₁ <;> cases k₂ <;> decide

private theorem filter_mulWordKind_onlyY :
    (Finset.univ : Finset (WordKind × WordKind)).filter (fun p ↦ mulWordKind p.1 p.2 = .onlyY) =
      {(.onlyY, .onlyY), (.onlyY, .one), (.one, .onlyY)} := by
  ext ⟨k₁, k₂⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]; cases k₁ <;> cases k₂ <;> decide

private theorem filter_mulWordKind_xy :
    (Finset.univ : Finset (WordKind × WordKind)).filter (fun p ↦ mulWordKind p.1 p.2 = .xy) =
      {(.onlyX, .onlyY), (.xy, .onlyY), (.onlyX, .xy), (.xy, .one), (.one, .xy)} := by
  ext ⟨k₁, k₂⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]; cases k₁ <;> cases k₂ <;> decide

/-- Product formula for the constant part: $(ab)_1 = a_1 b_1$. -/
theorem partOne_mul (a b : FreeAlgebra F (Fin n ⊕ Fin n)) :
    partOne (a * b) = partOne a * partOne b := by
  rw [partOne, partKind_mul, filter_mulWordKind_one, Finset.sum_singleton]

/-- Product formula for the $X$-only part: $(ab)_X = a_X b_X + a_X b_1 + a_1 b_X$. -/
theorem partX_mul (a b : FreeAlgebra F (Fin n ⊕ Fin n)) :
    partX (a * b) = partX a * partX b + partX a * partOne b + partOne a * partX b := by
  rw [partX, partKind_mul, filter_mulWordKind_onlyX]
  have h1 : (WordKind.onlyX, WordKind.onlyX) ∉
      ({(WordKind.onlyX, WordKind.one), (WordKind.one, WordKind.onlyX)} :
        Finset (WordKind × WordKind)) := by decide
  have h2 : (WordKind.onlyX, WordKind.one) ∉
      ({(WordKind.one, WordKind.onlyX)} : Finset (WordKind × WordKind)) := by decide
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton, ← add_assoc]

/-- Product formula for the $Y$-only part: $(ab)_Y = a_Y b_Y + a_Y b_1 + a_1 b_Y$. -/
theorem partY_mul (a b : FreeAlgebra F (Fin n ⊕ Fin n)) :
    partY (a * b) = partY a * partY b + partY a * partOne b + partOne a * partY b := by
  rw [partY, partKind_mul, filter_mulWordKind_onlyY]
  have h1 : (WordKind.onlyY, WordKind.onlyY) ∉
      ({(WordKind.onlyY, WordKind.one), (WordKind.one, WordKind.onlyY)} :
        Finset (WordKind × WordKind)) := by decide
  have h2 : (WordKind.onlyY, WordKind.one) ∉
      ({(WordKind.one, WordKind.onlyY)} : Finset (WordKind × WordKind)) := by decide
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton, ← add_assoc]

/-- Product formula for the $XY$ part:
$(ab)_{XY} = a_X b_Y + a_{XY} b_Y + a_X b_{XY} + a_{XY} b_1 + a_1 b_{XY}$. -/
theorem partXY_mul (a b : FreeAlgebra F (Fin n ⊕ Fin n)) :
    partXY (a * b) =
      partX a * partY b + partXY a * partY b + partX a * partXY b +
        partXY a * partOne b + partOne a * partXY b := by
  rw [partXY, partKind_mul, filter_mulWordKind_xy]
  have h1 : (WordKind.onlyX, WordKind.onlyY) ∉
      ({(.xy, .onlyY), (.onlyX, .xy), (.xy, .one), (.one, .xy)} :
        Finset (WordKind × WordKind)) := by decide
  have h2 : (WordKind.xy, WordKind.onlyY) ∉
      ({(.onlyX, .xy), (.xy, .one), (.one, .xy)} : Finset (WordKind × WordKind)) := by decide
  have h3 : (WordKind.onlyX, WordKind.xy) ∉
      ({(.xy, .one), (.one, .xy)} : Finset (WordKind × WordKind)) := by decide
  have h4 : (WordKind.xy, WordKind.one) ∉
      ({(.one, .xy)} : Finset (WordKind × WordKind)) := by decide
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3, Finset.sum_insert h4,
    Finset.sum_singleton]
  simp only [add_assoc]

end FivePartDecomposition

section CoefficientSpace

variable {F : Type*} [CommSemiring F] {n : ℕ}

/-- The canonical algebra embedding $F\langle X\rangle \hookrightarrow F\langle X, Y\rangle$. -/
noncomputable def embedX : FreeAlgebra F (Fin n) →ₐ[F] FreeAlgebra F (Fin n ⊕ Fin n) :=
  FreeAlgebra.lift F (fun i ↦ ι F (Sum.inl i))

/-- Coefficient of `wordInl u` in `embedX p` equals `coeff u p`. -/
@[simp]
theorem coeff_wordInl_embedX (u : FreeMonoid (Fin n)) (p : FreeAlgebra F (Fin n)) :
    FreeAlgebra.coeff (wordInl u) (embedX p) = FreeAlgebra.coeff u p := by
  let lhs : FreeAlgebra F (Fin n) →ₗ[F] F :=
    (FreeAlgebra.coeff (wordInl u)).comp embedX.toLinearMap
  have h : lhs = FreeAlgebra.coeff u := by
    apply (basisFreeMonoid F (Fin n)).ext
    intro v
    change FreeAlgebra.coeff (wordInl u) (embedX (basisFreeMonoid F (Fin n) v)) =
      FreeAlgebra.coeff u (basisFreeMonoid F (Fin n) v)
    simp only [basisFreeMonoid_apply]
    have hmap : embedX (FreeMonoid.lift (ι F) v) =
        FreeMonoid.lift (ι F) (wordInl v) := by
      have hcomp :
          ((embedX (F := F) (n := n)).toMonoidHom.comp (FreeMonoid.lift (ι F))) =
            (FreeMonoid.lift (ι F)).comp wordInl := by
        ext i
        simp [embedX, wordInl]
      exact DFunLike.congr_fun hcomp v
    rw [hmap, coeff_lift_ι, coeff_lift_ι]
    by_cases hvu : v = u
    · subst hvu; simp
    · have hne : wordInl (β := Fin n) v ≠ wordInl u := fun h' ↦ hvu (by
        have h'2 : wordInl v * wordInr (1 : FreeMonoid (Fin n)) = wordInl u * wordInr 1 := by
          simpa using h'
        exact (wordInl_mul_wordInr_inj h'2).1)
      simp [hne, hvu]
  exact DFunLike.congr_fun h p

/-- For any word `w` not of the form `wordInl u`, `coeff w (embedX p) = 0`. -/
theorem coeff_embedX_eq_zero_of_not_allX {w : FreeMonoid (Fin n ⊕ Fin n)}
    (hw : isAllX w.toList = false) (p : FreeAlgebra F (Fin n)) :
    FreeAlgebra.coeff w (embedX p) = 0 := by
  let lhs : FreeAlgebra F (Fin n) →ₗ[F] F := (FreeAlgebra.coeff w).comp embedX.toLinearMap
  have h : lhs = 0 := by
    apply (basisFreeMonoid F (Fin n)).ext
    intro v
    change FreeAlgebra.coeff w (embedX (basisFreeMonoid F (Fin n) v)) = 0
    rw [basisFreeMonoid_apply]
    have hmap : embedX (FreeMonoid.lift (ι F) v) = FreeMonoid.lift (ι F) (wordInl v) := by
      have hcomp :
          ((embedX (F := F) (n := n)).toMonoidHom.comp (FreeMonoid.lift (ι F))) =
            (FreeMonoid.lift (ι F)).comp wordInl := by
        ext i; simp [embedX, wordInl]
      exact DFunLike.congr_fun hcomp v
    rw [hmap, coeff_lift_ι]
    refine Finsupp.single_eq_of_ne fun h' ↦ ?_
    have hall := isAllX_wordInl (β := Fin n) v
    rw [← h', hw] at hall
    cases hall
  exact DFunLike.congr_fun h p

/-- The linear map extracting the coefficient in $F\langle X\rangle$ of a $Y$-monomial
$m \in Y^*$, i.e. $\mathrm{coeff}_m(f) = \sum_{u \in X^*} \mathrm{coeff}_{u \cdot m}(f)\, u$. -/
noncomputable def coeffY (m : FreeMonoid (Fin n)) :
    FreeAlgebra F (Fin n ⊕ Fin n) →ₗ[F] FreeAlgebra F (Fin n) := by
  classical
  exact (basisFreeMonoid F (Fin n ⊕ Fin n)).constr F fun w ↦
    if h : ∃ u : FreeMonoid (Fin n), wordInl u * wordInr m = w then
      basisFreeMonoid F (Fin n) h.choose
    else 0

/-- Coordinate formula for `coeffY`: `coeff u (coeffY m f) = coeff (u · m) f`. -/
@[simp]
theorem coeff_coeffY (m u : FreeMonoid (Fin n)) (f : FreeAlgebra F (Fin n ⊕ Fin n)) :
    FreeAlgebra.coeff u (coeffY m f) = FreeAlgebra.coeff (wordInl u * wordInr m) f := by
  classical
  let lhs : FreeAlgebra F (Fin n ⊕ Fin n) →ₗ[F] F :=
    (FreeAlgebra.coeff u).comp (coeffY m)
  have h : lhs = FreeAlgebra.coeff (wordInl u * wordInr m) := by
    apply (basisFreeMonoid F (Fin n ⊕ Fin n)).ext
    intro w
    change FreeAlgebra.coeff u (coeffY m (basisFreeMonoid F (Fin n ⊕ Fin n) w)) =
      FreeAlgebra.coeff (wordInl u * wordInr m) (basisFreeMonoid F (Fin n ⊕ Fin n) w)
    rw [coeffY, Module.Basis.constr_basis]
    split_ifs with hex
    · have hch := hex.choose_spec
      simp only [basisFreeMonoid_apply, coeff_lift_ι]
      by_cases hcu : hex.choose = u
      · subst hcu; simp [hch]
      · have hne : w ≠ wordInl u * wordInr m := fun hw ↦
          hcu (wordInl_mul_wordInr_inj (hch.trans hw)).1
        simp [hcu, hne]
    · rw [map_zero, basisFreeMonoid_apply, coeff_lift_ι]
      symm
      exact Finsupp.single_eq_of_ne fun hw ↦ hex ⟨u, hw⟩
  exact DFunLike.congr_fun h f

/-- Extract the `X`-only part of `f` as an element of `FreeAlgebra F (Fin n)`:
`extractX f = coeffY 1 (partX f)`. -/
noncomputable def extractX :
    FreeAlgebra F (Fin n ⊕ Fin n) →ₗ[F] FreeAlgebra F (Fin n) :=
  (coeffY 1).comp partX

/-- `embedX (extractX f) = partX f`. -/
@[simp]
theorem embedX_extractX (f : FreeAlgebra F (Fin n ⊕ Fin n)) :
    embedX (extractX f) = partX f := by
  apply ext_coeff
  intro w
  rw [coeff_partKind]
  by_cases hwx : wordKind w = .onlyX
  · obtain ⟨u, hu, rfl⟩ := exists_wordInl_of_wordKind_onlyX hwx
    rw [coeff_wordInl_embedX, extractX, LinearMap.comp_apply, coeff_coeffY, map_one, mul_one,
      coeff_partKind]
  · simp only [hwx, ↓reduceIte]
    by_cases hw1 : w = 1
    · subst hw1
      have h1 : wordInl (β := Fin n) 1 = (1 : FreeMonoid (Fin n ⊕ Fin n)) := map_one _
      rw [← h1, coeff_wordInl_embedX, extractX, LinearMap.comp_apply, coeff_coeffY, map_one,
        map_one, mul_one, coeff_partKind]
      simp [hwx]
    · have hnotx : isAllX w.toList = false := by
        cases hx : isAllX w.toList
        · rfl
        · exfalso
          apply hwx
          unfold wordKind
          cases hl : w.toList with
          | nil => exact absurd (freeMonoid_eq_one_of_toList hl) hw1
          | cons a t => rw [hl] at hx; simp [hx]
      exact coeff_embedX_eq_zero_of_not_allX hnotx _

/-- For every `f`, `coeff 1 (extractX f) = 0`, so `extractX f` has no constant term. -/
@[simp]
theorem coeff_one_extractX (f : FreeAlgebra F (Fin n ⊕ Fin n)) :
    FreeAlgebra.coeff (1 : FreeMonoid (Fin n)) (extractX f) = 0 := by
  rw [extractX, LinearMap.comp_apply, coeff_coeffY, map_one, map_one, mul_one, coeff_partKind]
  have h1 : wordKind (1 : FreeMonoid (Fin n ⊕ Fin n)) = .one := rfl
  simp [h1]

/-- For every `f`, either `extractX f = 0` or `1 ≤ minDeg (extractX f)`. -/
theorem extractX_eq_zero_or_one_le_minDeg (f : FreeAlgebra F (Fin n ⊕ Fin n)) :
    extractX f = 0 ∨ 1 ≤ CslibFrontier.FreeAlgebra.minDeg (extractX f) := by
  by_cases h : extractX f = 0
  · exact Or.inl h
  · right
    rw [CslibFrontier.FreeAlgebra.le_minDeg_iff h]
    intro w hw
    by_contra hlt
    have hw0 : w.toList.length = 0 := by omega
    have hw1 : w = 1 := freeMonoid_eq_one_of_toList (List.eq_nil_of_length_eq_zero hw0)
    rw [hw1, coeff_one_extractX] at hw
    exact hw rfl

/-- The coefficient set $\mathrm{Coeff}_X(f) = \{\mathrm{coeff}_m(f) \mid m \in Y^*,\
\mathrm{coeff}_m(f) \neq 0\} \subseteq F\langle X\rangle$. -/
def coeffXSet (f : FreeAlgebra F (Fin n ⊕ Fin n)) : Set (FreeAlgebra F (Fin n)) :=
  { c | ∃ m : FreeMonoid (Fin n), coeffY m f = c ∧ c ≠ 0 }

/-- `coeffY m f ∈ Submodule.span F (coeffXSet f)` for all `m` and `f`. -/
theorem coeffY_mem_span_coeffXSet (m : FreeMonoid (Fin n))
    (f : FreeAlgebra F (Fin n ⊕ Fin n)) :
    coeffY m f ∈ Submodule.span F (coeffXSet f) := by
  by_cases h0 : coeffY m f = 0
  · rw [h0]; exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨m, rfl, h0⟩

/-- `coeffXSet f ⊆ S` iff `∀ m, coeffY m f ∈ S` for any submodule `S`. -/
theorem coeffXSet_subset_submodule_iff {f : FreeAlgebra F (Fin n ⊕ Fin n)}
    {S : Submodule F (FreeAlgebra F (Fin n))} :
    coeffXSet f ⊆ (S : Set (FreeAlgebra F (Fin n))) ↔ ∀ m, coeffY m f ∈ S := by
  constructor
  · intro h m
    by_cases h0 : coeffY m f = 0
    · rw [h0]; exact S.zero_mem
    · exact h ⟨m, rfl, h0⟩
  · rintro h c ⟨m, rfl, -⟩
    exact h m

/-- `coeffY m (partOne f)` is always a scalar multiple of `1`. -/
theorem coeffY_partOne_eq_smul_one (m : FreeMonoid (Fin n))
    (f : FreeAlgebra F (Fin n ⊕ Fin n)) :
    ∃ c : F, coeffY m (partOne f) = c • (1 : FreeAlgebra F (Fin n)) := by
  by_cases hm : m = 1
  · refine ⟨FreeAlgebra.coeff (1 : FreeMonoid (Fin n ⊕ Fin n)) f, ?_⟩
    subst hm
    apply ext_coeff; intro u
    rw [coeff_coeffY, coeff_partKind, map_smul, coeff_one, smul_eq_mul, map_one, mul_one]
    by_cases hu : u = 1
    · subst hu
      have h1 : wordInl (β := Fin n) 1 = (1 : FreeMonoid (Fin n ⊕ Fin n)) := map_one _
      simp [h1, wordKind]
    · have hwk : wordKind (wordInl (β := Fin n) u) = .onlyX := wordKind_wordInl_ne_one hu
      simp [hwk, Ne.symm hu]
  · refine ⟨0, ?_⟩
    rw [zero_smul]
    apply ext_coeff; intro u
    rw [coeff_coeffY, coeff_partKind, map_zero]
    have hwk : wordKind (wordInl u * wordInr m) ≠ .one := by
      rw [wordKind_mul, wordKind_wordInr_ne_one hm]
      cases wordKind (wordInl (β := Fin n) u) <;> decide
    simp [hwk]

/-- `coeffY 1 (partX f) = extractX f`. -/
theorem coeffY_one_partX (f : FreeAlgebra F (Fin n ⊕ Fin n)) :
    coeffY 1 (partX f) = extractX f := by
  rfl

/-- `coeffY m (partX f) = 0` for every `m ≠ 1`. -/
theorem coeffY_partX_of_ne_one {m : FreeMonoid (Fin n)} (hm : m ≠ 1)
    (f : FreeAlgebra F (Fin n ⊕ Fin n)) :
    coeffY m (partX f) = 0 := by
  apply ext_coeff; intro u
  rw [coeff_coeffY, coeff_partKind, map_zero]
  have hwk : wordKind (wordInl u * wordInr m) ≠ .onlyX := by
    rw [wordKind_mul, wordKind_wordInr_ne_one hm]
    cases wordKind (wordInl (β := Fin n) u) <;> decide
  simp [hwk]

/-- `coeffY m (partY f)` is always a scalar multiple of `1`. -/
theorem coeffY_partY_eq_smul_one (m : FreeMonoid (Fin n))
    (f : FreeAlgebra F (Fin n ⊕ Fin n)) :
    ∃ c : F, coeffY m (partY f) = c • (1 : FreeAlgebra F (Fin n)) := by
  by_cases hm : m = 1
  · refine ⟨0, ?_⟩
    subst hm
    rw [zero_smul]
    apply ext_coeff; intro u
    rw [coeff_coeffY, coeff_partKind, map_zero, map_one, mul_one]
    have hwk : wordKind (wordInl (β := Fin n) u) ≠ .onlyY := by
      by_cases hu : u = 1
      · subst hu; simp [wordInl, wordKind]
      · rw [wordKind_wordInl_ne_one hu]; decide
    simp [hwk]
  · refine ⟨FreeAlgebra.coeff (wordInr m) f, ?_⟩
    apply ext_coeff; intro u
    rw [coeff_coeffY, coeff_partKind, map_smul, coeff_one, smul_eq_mul]
    by_cases hu : u = 1
    · subst hu
      rw [map_one, one_mul, wordKind_wordInr_ne_one hm]
      simp
    · rw [wordKind_wordInl_mul_wordInr hu hm]
      simp [Ne.symm hu]

/-- Helper: `coeffY m (partX a * partY b)` is a scalar multiple of `extractX a`. -/
theorem coeffY_partX_mul_partY_eq_smul (m : FreeMonoid (Fin n))
    (a b : FreeAlgebra F (Fin n ⊕ Fin n)) :
    ∃ c : F, coeffY m (partX a * partY b) = c • extractX a := by
  by_cases hm : m = 1
  · refine ⟨0, ?_⟩
    subst hm
    rw [zero_smul]
    apply ext_coeff; intro u
    rw [coeff_coeffY, coeff_mul, map_zero, map_one, mul_one]
    apply Finset.sum_eq_zero
    intro i _
    rw [coeff_partKind, coeff_partKind]
    split_ifs with h1 h2
    · exfalso
      have hmul :
          FreeMonoid.ofList ((wordInl (β := Fin n) u).toList.take i) *
            FreeMonoid.ofList ((wordInl (β := Fin n) u).toList.drop i) = wordInl u := by
        apply freeMonoid_ext; simp
      have hwk := wordKind_mul (FreeMonoid.ofList ((wordInl (β := Fin n) u).toList.take i))
        (FreeMonoid.ofList ((wordInl (β := Fin n) u).toList.drop i))
      rw [hmul, h1, h2] at hwk
      have hne : wordKind (wordInl (β := Fin n) u) ≠ .xy := by
        by_cases hu : u = 1
        · subst hu; simp [wordInl, wordKind]
        · rw [wordKind_wordInl_ne_one hu]; decide
      exact hne hwk
    · simp
    · simp
    · simp
  · refine ⟨FreeAlgebra.coeff (wordInr m) b, ?_⟩
    apply ext_coeff; intro u
    rw [coeff_coeffY, coeff_mul, map_smul, smul_eq_mul, extractX, LinearMap.comp_apply,
      coeff_coeffY, coeff_partKind, map_one, mul_one]
    by_cases hu : u = 1
    · subst hu
      rw [map_one, one_mul]
      have hwk1 : wordKind (1 : FreeMonoid (Fin n ⊕ Fin n)) ≠ .onlyX := by simp [wordKind]
      simp only [hwk1, ↓reduceIte, mul_zero]
      apply Finset.sum_eq_zero
      intro i _
      rw [coeff_partKind, coeff_partKind]
      split_ifs with h1 h2
      · exfalso
        have hmul :
            FreeMonoid.ofList ((wordInr (α := Fin n) m).toList.take i) *
              FreeMonoid.ofList ((wordInr (α := Fin n) m).toList.drop i) = wordInr m := by
          apply freeMonoid_ext; simp
        have hwk := wordKind_mul (FreeMonoid.ofList ((wordInr (α := Fin n) m).toList.take i))
          (FreeMonoid.ofList ((wordInr (α := Fin n) m).toList.drop i))
        rw [hmul, h1, h2, wordKind_wordInr_ne_one hm] at hwk
        cases hwk
      · simp
      · simp
      · simp
    · simp only [wordKind_wordInl_ne_one hu, ↓reduceIte]
      have hlen : (wordInl u * wordInr m).toList.length = u.toList.length + m.toList.length := by
        simp [wordInl, wordInr]
      rw [Finset.sum_eq_single u.toList.length]
      · have htake : FreeMonoid.ofList ((wordInl u * wordInr m).toList.take u.toList.length) =
            wordInl u := by
          apply freeMonoid_ext
          have hl : (wordInl (β := Fin n) u).toList.length = u.toList.length := by
            simp [wordInl]
          rw [FreeMonoid.toList_ofList, FreeMonoid.toList_mul, ← hl, List.take_left]
        have hdrop : FreeMonoid.ofList ((wordInl u * wordInr m).toList.drop u.toList.length) =
            wordInr m := by
          apply freeMonoid_ext
          have hl : (wordInl (β := Fin n) u).toList.length = u.toList.length := by
            simp [wordInl]
          rw [FreeMonoid.toList_ofList, FreeMonoid.toList_mul, ← hl, List.drop_left]
        rw [htake, hdrop, coeff_partKind, coeff_partKind]
        simp only [wordKind_wordInl_ne_one hu, wordKind_wordInr_ne_one hm, ↓reduceIte, mul_comm]
      · intro i hi hne
        rw [coeff_partKind, coeff_partKind]
        split_ifs with h1 h2
        · exfalso
          obtain ⟨u', -, hu'⟩ := exists_wordInl_of_wordKind_onlyX h1
          obtain ⟨v', -, hv'⟩ := exists_wordInr_of_wordKind_onlyY h2
          have hmul :
              FreeMonoid.ofList ((wordInl u * wordInr m).toList.take i) *
                FreeMonoid.ofList ((wordInl u * wordInr m).toList.drop i) =
                wordInl u * wordInr m := by
            apply freeMonoid_ext; simp
          rw [← hu', ← hv'] at hmul
          have hu_eq := (wordInl_mul_wordInr_inj hmul).1
          have hli : (wordInl (β := Fin n) u').toList.length = i := by
            rw [hu']
            simp only [List.length_take]
            simp only [Finset.mem_range] at hi
            omega
          have hlu : (wordInl (β := Fin n) u').toList.length = u.toList.length := by
            rw [hu_eq]
            simp [wordInl]
          exact hne (hli.symm.trans hlu)
        · simp
        · simp
        · simp
      · intro hnot
        exfalso
        apply hnot
        rw [Finset.mem_range, hlen]
        omega

/-- Helper: `coeffY m (partX a * partXY b) = extractX a * coeffY m (partXY b)`. -/
theorem coeffY_partX_mul_partXY (m : FreeMonoid (Fin n))
    (a b : FreeAlgebra F (Fin n ⊕ Fin n)) :
    coeffY m (partX a * partXY b) = extractX a * coeffY m (partXY b) := by
  apply ext_coeff
  intro u
  rw [coeff_coeffY, coeff_mul, coeff_mul]
  have hlen : (wordInl u * wordInr m).toList.length = u.toList.length + m.toList.length := by
    simp [wordInl, wordInr]
  have hsub : Finset.range (u.toList.length + 1) ⊆
      Finset.range ((wordInl u * wordInr m).toList.length + 1) := by
    rw [hlen]
    exact Finset.range_mono (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi_le : i ≤ u.toList.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hi_le' : i ≤ (wordInl (β := Fin n) u).toList.length := by simpa [wordInl] using hi_le
    have htake : FreeMonoid.ofList ((wordInl u * wordInr m).toList.take i) =
        wordInl (FreeMonoid.ofList (u.toList.take i)) := by
      apply freeMonoid_ext
      rw [FreeMonoid.toList_ofList, FreeMonoid.toList_mul, List.take_append_of_le_length hi_le']
      simp [wordInl]
    have hdrop : FreeMonoid.ofList ((wordInl u * wordInr m).toList.drop i) =
        wordInl (FreeMonoid.ofList (u.toList.drop i)) * wordInr m := by
      apply freeMonoid_ext
      rw [FreeMonoid.toList_ofList, FreeMonoid.toList_mul, List.drop_append_of_le_length hi_le']
      simp [wordInl]
    rw [htake, hdrop, coeff_coeffY, extractX, LinearMap.comp_apply, coeff_coeffY, map_one, mul_one]
  · intro i hi hnot
    have hi_gt : u.toList.length < i := by
      simp only [Finset.mem_range] at hi hnot
      omega
    rw [coeff_partKind]
    have hwk : wordKind (FreeMonoid.ofList ((wordInl u * wordInr m).toList.take i)) ≠ .onlyX := by
      intro h1
      obtain ⟨u', -, hu'⟩ := exists_wordInl_of_wordKind_onlyX h1
      have hlen_tot : i ≤ (wordInl u * wordInr m).toList.length := by
        simp only [Finset.mem_range] at hi; omega
      have hmem_inr :
          ∃ b', Sum.inr b' ∈ (wordInl u * wordInr m).toList.take i := by
        have hidx : u.toList.length < ((wordInl u * wordInr m).toList.take i).length := by
          rw [List.length_take]
          omega
        have hget : ((wordInl u * wordInr m).toList.take i)[u.toList.length]'hidx =
            (wordInr m).toList[0]'(by
              have : 0 < m.toList.length := by omega
              simpa [wordInr] using this) := by
          rw [List.getElem_take]
          simp [wordInl, wordInr]
        have hmem_m : (wordInr (α := Fin n) m).toList[0]'(by
            have : 0 < m.toList.length := by omega
            simpa [wordInr] using this) ∈ (wordInr (α := Fin n) m).toList :=
          List.getElem_mem _
        have hm_eq : (wordInr (α := Fin n) m).toList = m.toList.map Sum.inr := by
          simp [wordInr]
        have hmem_map : ((wordInl u * wordInr m).toList.take i)[u.toList.length]'hidx ∈
            m.toList.map (Sum.inr : Fin n → Fin n ⊕ Fin n) := by
          rw [hget, ← hm_eq]; exact hmem_m
        obtain ⟨b', -, hb'⟩ := List.mem_map.mp hmem_map
        exact ⟨b', hb' ▸ List.getElem_mem _⟩
      obtain ⟨b', hb'⟩ := hmem_inr
      have hax := isAllX_wordInl (β := Fin n) u'
      rw [hu'] at hax
      have hfalse : ∀ l : List (Fin n ⊕ Fin n), isAllX l = true → Sum.inr b' ∉ l := by
        intro l
        induction l with
        | nil => intro _; exact List.not_mem_nil
        | cons x t ih =>
          cases x with
          | inl _ => intro hx hmem; exact ih hx ((List.mem_cons.mp hmem).resolve_left (by simp))
          | inr _ => intro hx; simp [isAllX] at hx
      exact hfalse _ hax hb'
    simp only [hwk, ↓reduceIte, zero_mul]

/-- Helper: `coeffY m (partXY a * partY b)` is an `F`-linear combination of `coeffY m' (partXY a)`
as `m'` ranges over prefixes of `m`. -/
theorem coeffY_partXY_mul_partY (m : FreeMonoid (Fin n))
    (a b : FreeAlgebra F (Fin n ⊕ Fin n)) :
    coeffY m (partXY a * partY b) =
      ∑ j ∈ Finset.range (m.toList.length + 1),
        FreeAlgebra.coeff (wordInr (FreeMonoid.ofList (m.toList.drop j))) (partY b) •
          coeffY (FreeMonoid.ofList (m.toList.take j)) (partXY a) := by
  apply ext_coeff
  intro u
  rw [coeff_coeffY, coeff_mul, map_sum]
  have hlen : (wordInl u * wordInr m).toList.length = u.toList.length + m.toList.length := by
    simp [wordInl, wordInr]
  rw [hlen, add_assoc, Finset.sum_range_add]
  have hzero_left :
      ∑ i ∈ Finset.range u.toList.length,
        FreeAlgebra.coeff (FreeMonoid.ofList ((wordInl u * wordInr m).toList.take i)) (partXY a) *
          FreeAlgebra.coeff (FreeMonoid.ofList ((wordInl u * wordInr m).toList.drop i))
            (partY b) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hil : i ≤ u.toList.length := le_of_lt (Finset.mem_range.mp hi)
    have hil' : i ≤ (wordInl (β := Fin n) u).toList.length := by simpa [wordInl] using hil
    have htake : FreeMonoid.ofList ((wordInl u * wordInr m).toList.take i) =
        wordInl (FreeMonoid.ofList (u.toList.take i)) := by
      apply freeMonoid_ext
      rw [FreeMonoid.toList_ofList, FreeMonoid.toList_mul, List.take_append_of_le_length hil']
      simp [wordInl]
    rw [htake, coeff_partKind]
    have hnot : wordKind (wordInl (β := Fin n) (FreeMonoid.ofList (u.toList.take i))) ≠ .xy := by
      by_cases hu0 : FreeMonoid.ofList (u.toList.take i) = 1
      · rw [hu0]; simp [wordInl, wordKind]
      · rw [wordKind_wordInl_ne_one hu0]; decide
    simp only [hnot, ↓reduceIte, zero_mul]
  rw [hzero_left, zero_add]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have htake :
      FreeMonoid.ofList ((wordInl u * wordInr m).toList.take (u.toList.length + j)) =
        wordInl u * wordInr (FreeMonoid.ofList (m.toList.take j)) := by
    apply freeMonoid_ext
    have hl : (wordInl (β := Fin n) u).toList.length = u.toList.length := by simp [wordInl]
    rw [FreeMonoid.toList_ofList, FreeMonoid.toList_mul, FreeMonoid.toList_mul,
      List.take_append, hl, Nat.add_sub_cancel_left]
    simp [wordInl, wordInr]
  have hdrop :
      FreeMonoid.ofList ((wordInl u * wordInr m).toList.drop (u.toList.length + j)) =
        wordInr (FreeMonoid.ofList (m.toList.drop j)) := by
    apply freeMonoid_ext
    have hl : (wordInl (β := Fin n) u).toList.length = u.toList.length := by simp [wordInl]
    rw [FreeMonoid.toList_ofList, FreeMonoid.toList_mul, List.drop_append, hl,
      List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]
    simp [wordInr]
  rw [htake, hdrop, map_smul, coeff_coeffY, smul_eq_mul, mul_comm]

/-- Helper: `coeffY m (partXY a * partOne b)` is a scalar multiple of `coeffY m (partXY a)`. -/
theorem coeffY_partXY_mul_partOne (m : FreeMonoid (Fin n))
    (a b : FreeAlgebra F (Fin n ⊕ Fin n)) :
    coeffY m (partXY a * partOne b) =
      FreeAlgebra.coeff (1 : FreeMonoid (Fin n ⊕ Fin n)) b • coeffY m (partXY a) := by
  rw [partOne_eq_smul_one, mul_smul_comm, mul_one, map_smul]

/-- Helper: `coeffY m (partOne a * partXY b)` is a scalar multiple of `coeffY m (partXY b)`. -/
theorem coeffY_partOne_mul_partXY (m : FreeMonoid (Fin n))
    (a b : FreeAlgebra F (Fin n ⊕ Fin n)) :
    coeffY m (partOne a * partXY b) =
      FreeAlgebra.coeff (1 : FreeMonoid (Fin n ⊕ Fin n)) a • coeffY m (partXY b) := by
  rw [partOne_eq_smul_one, smul_mul_assoc, one_mul, map_smul]

end CoefficientSpace

section PalindromeDimension

variable (F : Type*) [Field F]

private theorem wordInl_ofFn {n d : ℕ} (u : Fin d → Fin n) :
    wordInl (β := Fin n) (FreeMonoid.ofFn u) = FreeMonoid.ofFn (Sum.inl ∘ u) := by
  apply freeMonoid_ext
  simp [wordInl, FreeMonoid.ofFn]

private theorem wordInr_ofFn {n d : ℕ} (u : Fin d → Fin n) :
    wordInr (α := Fin n) (FreeMonoid.ofFn u) = FreeMonoid.ofFn (Sum.inr ∘ u) := by
  apply freeMonoid_ext
  simp [wordInr, FreeMonoid.ofFn]

/-- Every coefficient in `coeffXSet (palPoly F n n)` is a degree-`n` monomial in `X`. -/
theorem coeffXSet_palPoly (n : ℕ) :
    coeffXSet (palPoly F n n) =
      Set.range fun u : Fin n → Fin n ↦
        FreeMonoid.lift (ι F) (FreeMonoid.ofFn u) := by
  classical
  ext c
  constructor
  · rintro ⟨m, rfl, hne⟩
    have hex : ∃ u : Fin n → Fin n, FreeMonoid.ofFn u = m := by
      by_contra hnot
      apply hne
      apply ext_coeff
      intro w
      rw [coeff_coeffY, map_zero, palPoly, map_sum]
      apply Finset.sum_eq_zero
      intro u _
      rw [coeff_lift_ι]
      refine Finsupp.single_eq_of_ne' fun heq ↦ hnot ?_
      have heq' : wordInl (FreeMonoid.ofFn u) * wordInr (FreeMonoid.ofFn (u ∘ Fin.rev)) =
          wordInl w * wordInr m := by
        rw [wordInl_ofFn, wordInr_ofFn]; exact heq
      exact ⟨u ∘ Fin.rev, (wordInl_mul_wordInr_inj heq').2⟩
    obtain ⟨v, rfl⟩ := hex
    refine ⟨v ∘ Fin.rev, ?_⟩
    apply ext_coeff
    intro u
    rw [coeff_coeffY, coeff_lift_ι]
    by_cases hlen : u.toList.length = n
    · obtain ⟨a, rfl⟩ := FreeMonoid.exists_ofFn_eq u hlen
      rw [wordInl_ofFn, wordInr_ofFn, coeff_palPoly_ofFn]
      by_cases hrev : a ∘ Fin.rev = v
      · have hav : v ∘ Fin.rev = a := by
          rw [← hrev]; funext j; simp
        simp [hrev, hav]
      · have hav : FreeMonoid.ofFn (v ∘ Fin.rev) ≠ FreeMonoid.ofFn a := fun h' ↦ by
          apply hrev
          have hlist := congrArg FreeMonoid.toList h'
          simp only [FreeMonoid.ofFn, FreeMonoid.toList_ofList] at hlist
          have hfn := List.ofFn_injective hlist
          funext j
          have hj := congrFun hfn (Fin.rev j)
          simpa using hj.symm
        simp only [hrev, ↓reduceIte]
        exact Finsupp.single_eq_of_ne' hav
    · rw [Finsupp.single_eq_of_ne' (fun h' ↦ hlen (by rw [← h']; simp))]
      rw [palPoly, map_sum]
      symm
      apply Finset.sum_eq_zero
      intro a _
      rw [coeff_lift_ι]
      refine Finsupp.single_eq_of_ne' fun heq ↦ hlen ?_
      have heq' : wordInl (FreeMonoid.ofFn a) * wordInr (FreeMonoid.ofFn (a ∘ Fin.rev)) =
          wordInl u * wordInr (FreeMonoid.ofFn v) := by
        rw [wordInl_ofFn, wordInr_ofFn]; exact heq
      rw [← (wordInl_mul_wordInr_inj heq').1]
      simp
  · rintro ⟨u, rfl⟩
    refine ⟨FreeMonoid.ofFn (u ∘ Fin.rev), ?_, ?_⟩
    · apply ext_coeff
      intro w
      rw [coeff_coeffY, coeff_lift_ι]
      by_cases hlen : w.toList.length = n
      · obtain ⟨a, rfl⟩ := FreeMonoid.exists_ofFn_eq w hlen
        rw [wordInl_ofFn, wordInr_ofFn, coeff_palPoly_ofFn]
        by_cases hrev : a ∘ Fin.rev = u ∘ Fin.rev
        · have hau : u = a := by
            funext j
            have := congrFun hrev (Fin.rev j)
            simpa using this.symm
          simp [hrev, hau]
        · have hau : FreeMonoid.ofFn u ≠ FreeMonoid.ofFn a := fun h' ↦ by
            apply hrev
            have hlist := congrArg FreeMonoid.toList h'
            simp only [FreeMonoid.ofFn, FreeMonoid.toList_ofList] at hlist
            rw [List.ofFn_injective hlist]
          simp only [hrev, ↓reduceIte]
          symm
          exact Finsupp.single_eq_of_ne' hau
      · rw [Finsupp.single_eq_of_ne' (fun h' ↦ hlen (by rw [← h']; simp))]
        rw [palPoly, map_sum]
        apply Finset.sum_eq_zero
        intro a _
        rw [coeff_lift_ι]
        refine Finsupp.single_eq_of_ne' fun heq ↦ hlen ?_
        have heq' : wordInl (FreeMonoid.ofFn a) * wordInr (FreeMonoid.ofFn (a ∘ Fin.rev)) =
            wordInl w * wordInr (FreeMonoid.ofFn (u ∘ Fin.rev)) := by
          rw [wordInl_ofFn, wordInr_ofFn]; exact heq
        rw [← (wordInl_mul_wordInr_inj heq').1]
        simp
    · intro h0
      have := congrArg (FreeAlgebra.coeff (FreeMonoid.ofFn u)) h0
      simp [coeff_lift_ι] at this

/-- Every element of `coeffXSet (palPoly F n n)` is homogeneous of degree `n`. -/
theorem isHomogeneous_of_mem_coeffXSet_palPoly (n : ℕ) {c : FreeAlgebra F (Fin n)}
    (hc : c ∈ coeffXSet (palPoly F n n)) : c.IsHomogeneous n := by
  rw [coeffXSet_palPoly] at hc
  obtain ⟨u, rfl⟩ := hc
  simpa using isHomogeneous_lift_ι (R := F) (FreeMonoid.ofFn u)

/-- $\dim_F \mathrm{span}(\mathrm{Coeff}_X(\mathrm{Pal}_{n,n}(X,Y))) = n^n$. -/
theorem finrank_span_coeffXSet_palPoly (n : ℕ) :
    Module.finrank F (Submodule.span F (coeffXSet (palPoly F n n))) = n ^ n := by
  rw [coeffXSet_palPoly]
  let f : (Fin n → Fin n) → FreeAlgebra F (Fin n) :=
    fun u ↦ FreeMonoid.lift (ι F) (FreeMonoid.ofFn u)
  have hli : LinearIndependent F f := by
    have hinj : Function.Injective (fun u : Fin n → Fin n ↦ FreeMonoid.ofFn u) := by
      intro u v h
      have hlist := congrArg FreeMonoid.toList h
      simp only [FreeMonoid.ofFn, FreeMonoid.toList_ofList] at hlist
      exact List.ofFn_injective hlist
    have hcomp : f = (basisFreeMonoid F (Fin n)) ∘ (fun u : Fin n → Fin n ↦ FreeMonoid.ofFn u) :=
      funext fun u ↦ (basisFreeMonoid_apply (FreeMonoid.ofFn u)).symm
    rw [hcomp]
    exact (basisFreeMonoid F (Fin n)).linearIndependent.comp _ hinj
  rw [Module.finrank_eq_card_basis (Module.Basis.span hli), Fintype.card_fun, Fintype.card_fin]

/-- `extractX` vanishes on scalars. -/
theorem extractX_algebraMap {n : ℕ} (c : F) :
    extractX (algebraMap F (FreeAlgebra F (Fin n ⊕ Fin n)) c) = 0 := by
  apply ext_coeff; intro u
  rw [extractX, LinearMap.comp_apply, coeff_coeffY, map_one, mul_one, coeff_partKind,
    coeff_algebraMap, map_zero]
  by_cases hu : u = 1
  · subst hu; simp [wordInl, wordKind]
  · have hne : (1 : FreeMonoid (Fin n ⊕ Fin n)) ≠ wordInl u := fun h' ↦ by
      have hw := wordKind_wordInl_ne_one (β := Fin n) hu
      rw [← h'] at hw; simp [wordKind] at hw
    simp [wordKind_wordInl_ne_one hu, Finsupp.single_eq_of_ne' hne]

/-- `extractX` maps `X`-variables to themselves. -/
theorem extractX_iota_inl {n : ℕ} (i : Fin n) :
    extractX (ι F (Sum.inl i : Fin n ⊕ Fin n)) = ι F i := by
  apply ext_coeff; intro u
  rw [extractX, LinearMap.comp_apply, coeff_coeffY, map_one, mul_one, coeff_partKind,
    coeff_ι, coeff_ι]
  have hwk : wordKind (FreeMonoid.of (Sum.inl i : Fin n ⊕ Fin n)) = .onlyX := by
    simpa [wordInl] using wordKind_wordInl_ne_one (β := Fin n) (FreeMonoid.of_ne_one i)
  by_cases hu : u = FreeMonoid.of i
  · subst hu
    have hof : wordInl (β := Fin n) (FreeMonoid.of i) = FreeMonoid.of (Sum.inl i) := rfl
    rw [hof]; simp [hwk]
  · have hne : FreeMonoid.of (Sum.inl i : Fin n ⊕ Fin n) ≠ wordInl u := fun h' ↦ hu <| by
      have hlist := congrArg FreeMonoid.toList h'
      simp only [wordInl, FreeMonoid.toList_of, FreeMonoid.toList_map] at hlist
      apply freeMonoid_ext
      obtain ⟨a, ha, hai⟩ := List.map_eq_singleton_iff.mp hlist.symm
      rw [ha, Sum.inl.inj hai]; rfl
    simp [Finsupp.single_eq_of_ne' hne, Finsupp.single_eq_of_ne' (Ne.symm hu)]

/-- `extractX` vanishes on `Y`-variables. -/
theorem extractX_iota_inr {n : ℕ} (i : Fin n) :
    extractX (ι F (Sum.inr i : Fin n ⊕ Fin n)) = 0 := by
  apply ext_coeff; intro u
  rw [extractX, LinearMap.comp_apply, coeff_coeffY, map_one, mul_one, coeff_partKind,
    coeff_ι, map_zero]
  split_ifs with hwk
  · refine Finsupp.single_eq_of_ne fun h' ↦ ?_
    have hwk' : wordKind (FreeMonoid.of (Sum.inr i : Fin n ⊕ Fin n)) = .onlyY := by
      simpa [wordInr] using wordKind_wordInr_ne_one (α := Fin n) (FreeMonoid.of_ne_one i)
    rw [h', hwk'] at hwk; cases hwk
  · rfl

/-- `partXY` vanishes on scalars. -/
theorem partXY_algebraMap {n : ℕ} (c : F) :
    partXY (algebraMap F (FreeAlgebra F (Fin n ⊕ Fin n)) c) = 0 := by
  apply ext_coeff; intro w
  rw [coeff_partKind, map_zero, coeff_algebraMap]
  by_cases hw : w = 1
  · subst hw; simp [wordKind]
  · simp [Ne.symm hw]

/-- `partXY` vanishes on single variables. -/
theorem partXY_iota {n : ℕ} (x : Fin n ⊕ Fin n) :
    partXY (ι F x) = 0 := by
  apply ext_coeff; intro w
  rw [coeff_partKind, map_zero, coeff_ι]
  split_ifs with hwk
  · refine Finsupp.single_eq_of_ne fun h' ↦ ?_
    cases x with
    | inl i =>
      have hwk' : wordKind (FreeMonoid.of (Sum.inl i : Fin n ⊕ Fin n)) = .onlyX := by
        simpa [wordInl] using wordKind_wordInl_ne_one (β := Fin n) (FreeMonoid.of_ne_one i)
      rw [h', hwk'] at hwk; cases hwk
    | inr i =>
      have hwk' : wordKind (FreeMonoid.of (Sum.inr i : Fin n ⊕ Fin n)) = .onlyY := by
        simpa [wordInr] using wordKind_wordInr_ne_one (α := Fin n) (FreeMonoid.of_ne_one i)
      rw [h', hwk'] at hwk; cases hwk
  · rfl

/-- `partOther` vanishes on the palindrome polynomial. -/
theorem partOther_palPoly (n d : ℕ) : partOther (palPoly F n d) = 0 := by
  apply ext_coeff; intro w
  rw [coeff_partKind, map_zero, palPoly, map_sum]
  split_ifs with hwk
  · apply Finset.sum_eq_zero; intro u _
    rw [coeff_lift_ι]
    refine Finsupp.single_eq_of_ne fun heq ↦ ?_
    have hsep : wordKind (FreeMonoid.ofFn (Sum.inl ∘ u) *
        FreeMonoid.ofFn (Sum.inr ∘ (u ∘ Fin.rev))) ≠ .other := by
      rw [← wordInl_ofFn, ← wordInr_ofFn]
      cases d with
      | zero =>
        have h1 : FreeMonoid.ofFn u = 1 := rfl
        have h2 : FreeMonoid.ofFn (u ∘ Fin.rev) = 1 := rfl
        rw [h1, h2, map_one, map_one, mul_one]; simp [wordKind]
      | succ d' =>
        have hne : ∀ v : Fin (d' + 1) → Fin n, FreeMonoid.ofFn v ≠ 1 := fun v h0 ↦ by
          have := congrArg (List.length ∘ FreeMonoid.toList) h0; simp at this
        rw [wordKind_wordInl_mul_wordInr (hne u) (hne _)]; decide
    rw [← heq, hwk] at hsep; exact hsep rfl
  · rfl

end PalindromeDimension

end CslibFrontier.Circuits.Arithmetic.Noncommutative
