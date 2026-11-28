/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.Polymorphism
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Prod
import Mathlib.Tactic.FinCases

/-!
# Minority, Majority, and Dual Discriminator Polymorphisms

This module develops the universal-algebraic structure theory of relations preserved by ternary
minority, majority, and dual discriminator polymorphisms on arbitrary domains under standard Lean
axioms, built directly on `Cslib.Logic.IsPolymorphism`:

1. Ternary minority, majority, and dual discriminator operations, including uniqueness of the dual
   discriminator on any domain and uniqueness of minority on any two-element domain.
2. The Baker–Pixley binary decomposability theorem for finite-arity relations preserved by a
   majority polymorphism: a tuple belongs to `R` if and only if every pair of its coordinates
   extends to a member of `R`.
3. The Jeavons–Cohen–Cooper three-type classification of binary relations preserved by the dual
   discriminator: a binary relation on an arbitrary domain is preserved by the dual discriminator
   if and only if it is a permutation (partial bijection), a complete Cartesian product, or a
   two-fan (including degenerate one-fans).
4. Global solvability and exact binary projection recovery for path-consistent (3-consistent)
   binary constraint networks preserved by a majority polymorphism.

## Main definitions

* `Cslib.Logic.IsMinorityOp`: ternary operation satisfying
  `f(a, a, b) = f(a, b, a) = f(b, a, a) = b`.
* `Cslib.Logic.IsMajorityOp`: ternary operation satisfying
  `f(a, a, b) = f(a, b, a) = f(b, a, a) = a`.
* `Cslib.Logic.IsDualDiscriminatorOp`: majority operation satisfying `f(a, b, c) = a` for
  pairwise distinct `a, b, c`.
* `Cslib.Logic.dualDiscriminator`: the canonical dual discriminator operation
  `fun v ↦ if v 1 = v 2 then v 1 else v 0`.
* `Cslib.Logic.IsBinaryPolymorphism`: coordinatewise preservation of a binary relation
  `R : Set (D × D)` by a ternary operation.
* `Cslib.Logic.IsPermutationBinaryRel`, `Cslib.Logic.IsCompleteBinaryRel`,
  `Cslib.Logic.IsTwoFanBinaryRel`: the three structural classes of binary relations
  preserved by the dual discriminator.
* `Cslib.Logic.IsPathConsistentNetwork`: reflexive, symmetric, 3-consistent binary
  constraint network over a variable type `V`.

## Main results

* `Cslib.Logic.IsMinorityOp.eq_of_card_two`: uniqueness of minority operations on any
  two-element domain.
* `Cslib.Logic.isDualDiscriminatorOp_dualDiscriminator` and
  `Cslib.Logic.IsDualDiscriminatorOp.eq_dualDiscriminator`: existence and uniqueness of
  the dual discriminator on every domain.
* `Cslib.Logic.IsMajorityOp.mem_iff_pairwise_proj`: Baker–Pixley binary decomposability
  for finite-arity relations preserved by a majority operation.
* `Cslib.Logic.IsDualDiscriminatorOp.fiber_eq_sndProj_of_two` and
  `Cslib.Logic.IsDualDiscriminatorOp.cofiber_eq_fstProj_of_two`: fiber dichotomy for
  dual-discriminator-preserved binary relations.
* `Cslib.Logic.IsDualDiscriminatorOp.isBinaryPolymorphism_iff`: exact equivalence between
  dual-discriminator preservation of a binary relation and being a permutation, complete, or
  two-fan relation.
* `Cslib.Logic.IsMajorityOp.isBinaryPolymorphism_relComp`: preservation of majority
  closure under relational composition.
* `Cslib.Logic.IsMajorityOp.exists_solution_extending_pair`: in a finite path-consistent
  majority-closed binary network, every consistent pair `(a, b) ∈ B p q` extends to a global
  solution.
-/

public section

namespace Cslib.Logic


section Operations

variable {D : Type*}

/-- A ternary operation `f : (Fin 3 → D) → D` is a *minority operation* if
`f(a, a, b) = f(a, b, a) = f(b, a, a) = b` for all `a, b : D`. -/
@[expose] def IsMinorityOp (f : (Fin 3 → D) → D) : Prop :=
  ∀ a b : D, f ![a, a, b] = b ∧ f ![a, b, a] = b ∧ f ![b, a, a] = b

/-- Every minority operation is idempotent (`f(a, a, a) = a`). -/
theorem IsMinorityOp.idempotent {f : (Fin 3 → D) → D} (hf : IsMinorityOp f) (a : D) :
    f ![a, a, a] = a :=
  (hf a a).1

private theorem vec3_eq (v : Fin 3 → D) : ![v 0, v 1, v 2] = v := by
  ext i
  fin_cases i <;> rfl

/-- On any domain of cardinality `2`, there is at most one minority operation. -/
theorem IsMinorityOp.eq_of_card_two [Fintype D] (hD : Fintype.card D = 2)
    {f g : (Fin 3 → D) → D} (hf : IsMinorityOp f) (hg : IsMinorityOp g) :
    f = g := by
  funext v
  have hnotinj : ¬ Function.Injective v := fun hinj ↦ by
    have hle := Fintype.card_le_of_injective v hinj
    simp [hD] at hle
  simp only [Function.Injective, not_forall] at hnotinj
  obtain ⟨i, j, hij, hne⟩ := hnotinj
  rw [← vec3_eq v]
  fin_cases i <;> fin_cases j
  · exact absurd rfl hne
  · dsimp at hij
    rw [hij, (hf (v 1) (v 2)).1, (hg (v 1) (v 2)).1]
  · dsimp at hij
    rw [hij, (hf (v 2) (v 1)).2.1, (hg (v 2) (v 1)).2.1]
  · dsimp at hij
    rw [hij, (hf (v 0) (v 2)).1, (hg (v 0) (v 2)).1]
  · exact absurd rfl hne
  · dsimp at hij
    rw [hij, (hf (v 2) (v 0)).2.2, (hg (v 2) (v 0)).2.2]
  · dsimp at hij
    rw [hij, (hf (v 0) (v 1)).2.1, (hg (v 0) (v 1)).2.1]
  · dsimp at hij
    rw [hij, (hf (v 1) (v 0)).2.2, (hg (v 1) (v 0)).2.2]
  · exact absurd rfl hne

/-- A ternary operation `f : (Fin 3 → D) → D` is a *majority operation* if
`f(a, a, b) = f(a, b, a) = f(b, a, a) = a` for all `a, b : D`. -/
def IsMajorityOp (f : (Fin 3 → D) → D) : Prop :=
  ∀ a b : D, f ![a, a, b] = a ∧ f ![a, b, a] = a ∧ f ![b, a, a] = a

/-- Every majority operation is idempotent (`f(a, a, a) = a`). -/
theorem IsMajorityOp.idempotent {f : (Fin 3 → D) → D} (hf : IsMajorityOp f) (a : D) :
    f ![a, a, a] = a :=
  (hf a a).1

/-- A ternary operation `f : (Fin 3 → D) → D` is the *dual discriminator* on `D` if it is a
majority operation such that `f(a, b, c) = a` whenever `a, b, c` are pairwise distinct. -/
def IsDualDiscriminatorOp (f : (Fin 3 → D) → D) : Prop :=
  IsMajorityOp f ∧ ∀ a b c : D, a ≠ b → a ≠ c → b ≠ c → f ![a, b, c] = a

/-- Every dual discriminator operation is a majority operation. -/
theorem IsDualDiscriminatorOp.isMajorityOp {f : (Fin 3 → D) → D}
    (hf : IsDualDiscriminatorOp f) : IsMajorityOp f :=
  hf.1

/-- Characterization of the dual discriminator by a single two-case rule: `f(a, b, b) = b`, and
`f(a, b, c) = a` whenever `b ≠ c`. -/
theorem isDualDiscriminatorOp_iff {f : (Fin 3 → D) → D} :
    IsDualDiscriminatorOp f ↔
      (∀ a b : D, f ![a, b, b] = b) ∧ (∀ a b c : D, b ≠ c → f ![a, b, c] = a) := by
  classical
  constructor
  · rintro ⟨hmaj, hdist⟩
    refine ⟨fun a b ↦ (hmaj b a).2.2, fun a b c hbc ↦ ?_⟩
    by_cases hab : a = b
    · subst hab
      exact (hmaj a c).1
    · by_cases hac : a = c
      · subst hac
        exact (hmaj a b).2.1
      · exact hdist a b c hab hac hbc
  · rintro ⟨heq, hne⟩
    refine ⟨fun a b ↦ ⟨?_, ?_, heq b a⟩, fun a b c _ _ hbc ↦ hne a b c hbc⟩
    · by_cases hab : a = b
      · subst hab
        exact heq a a
      · exact hne a a b hab
    · by_cases hab : a = b
      · subst hab
        exact heq a a
      · exact hne a b a (Ne.symm hab)

/-- The canonical dual discriminator operation on `D`, returning `v 1` when `v 1 = v 2` and `v 0`
otherwise. -/
def dualDiscriminator [DecidableEq D] (v : Fin 3 → D) : D :=
  if v 1 = v 2 then v 1 else v 0

/-- `dualDiscriminator` satisfies `IsDualDiscriminatorOp`. -/
theorem isDualDiscriminatorOp_dualDiscriminator [DecidableEq D] :
    IsDualDiscriminatorOp (dualDiscriminator (D := D)) :=
  isDualDiscriminatorOp_iff.2 ⟨fun a b ↦ by simp [dualDiscriminator],
    fun a b c hbc ↦ by simp [dualDiscriminator, hbc]⟩

/-- Uniqueness of the dual discriminator: every operation satisfying `IsDualDiscriminatorOp`
equals `dualDiscriminator`. -/
theorem IsDualDiscriminatorOp.eq_dualDiscriminator [DecidableEq D]
    {f : (Fin 3 → D) → D} (hf : IsDualDiscriminatorOp f) :
    f = dualDiscriminator := by
  obtain ⟨heq, hne⟩ := isDualDiscriminatorOp_iff.1 hf
  funext v
  rw [← vec3_eq v]
  by_cases h12 : v 1 = v 2
  · simp [dualDiscriminator, h12, heq]
  · simp [dualDiscriminator, h12, hne _ _ _ h12]

/-- On any domain of cardinality at most `2`, every majority operation is the dual discriminator. -/
theorem IsMajorityOp.isDualDiscriminatorOp_of_card_le_two [Fintype D] (hD : Fintype.card D ≤ 2)
    {f : (Fin 3 → D) → D} (hf : IsMajorityOp f) :
    IsDualDiscriminatorOp f := by
  refine ⟨hf, fun a b c hab hac hbc ↦ ?_⟩
  have hinj : Function.Injective ![a, b, c] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp at hij
    · rfl
    · exact absurd hij hab
    · exact absurd hij hac
    · exact absurd hij.symm hab
    · rfl
    · exact absurd hij hbc
    · exact absurd hij.symm hac
    · exact absurd hij.symm hbc
    · rfl
  have hle := Fintype.card_le_of_injective ![a, b, c] hinj
  simp at hle
  omega

/-- Value of a dual discriminator always belongs to its first two arguments `{v 0, v 1}`. -/
theorem IsDualDiscriminatorOp.apply_eq_first_or_second {f : (Fin 3 → D) → D}
    (hf : IsDualDiscriminatorOp f) (v : Fin 3 → D) :
    f v = v 0 ∨ f v = v 1 := by
  classical
  obtain ⟨heq, hne⟩ := isDualDiscriminatorOp_iff.1 hf
  rw [← vec3_eq v]
  by_cases h12 : v 1 = v 2
  · right
    simpa [← h12] using heq (v 0) (v 1)
  · left
    exact hne _ _ _ h12

end Operations

section BakerPixley

variable {D I : Type*}

private theorem exists_three_distinct_of_two_lt_card {α : Type*} {s : Finset α}
    (hs : 2 < s.card) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (by omega : 0 < s.card)
  have h1 : 1 < (s.erase a).card := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.1 h1
  exact ⟨a, ha, b, Finset.mem_of_mem_erase hb, c, Finset.mem_of_mem_erase hc,
    (Finset.ne_of_mem_erase hb).symm, (Finset.ne_of_mem_erase hc).symm, hbc⟩

private theorem IsMajorityOp.apply_of_two_eq {f : (Fin 3 → D) → D} (hf : IsMajorityOp f)
    {x a b c : D} {p q r : Prop} (h1 : p → a = x) (h2 : q → b = x) (h3 : r → c = x)
    (htwo : (p ∧ q) ∨ (p ∧ r) ∨ (q ∧ r)) :
    f ![a, b, c] = x := by
  rcases htwo with ⟨hp, hq⟩ | ⟨hp, hr⟩ | ⟨hq, hr⟩
  · rw [h1 hp, h2 hq, (hf x c).1]
  · rw [h1 hp, h3 hr, (hf x b).2.1]
  · rw [h2 hq, h3 hr, (hf x a).2.2]

private theorem IsMajorityOp.exists_agree_on_finset {f : (Fin 3 → D) → D} (hf : IsMajorityOp f)
    {R : Set (I → D)} (hR : IsPolymorphism f R) {x : I → D}
    (hpair : ∀ i j : I, ∃ y ∈ R, y i = x i ∧ y j = x j) :
    ∀ s : Finset I, s.Nonempty → ∃ y ∈ R, ∀ i ∈ s, y i = x i := by
  classical
  intro s hs
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | ind n ih =>
    subst hn
    by_cases hle : s.card ≤ 2
    · obtain ⟨a, ha⟩ := hs
      by_cases h1 : (s.erase a).Nonempty
      · obtain ⟨b, hb⟩ := h1
        obtain ⟨y, hyR, hya, hyb⟩ := hpair a b
        refine ⟨y, hyR, fun k hk ↦ ?_⟩
        by_cases hka : k = a
        · exact hka ▸ hya
        · by_cases hkb : k = b
          · exact hkb ▸ hyb
          · have hsub : ({a, b, k} : Finset I) ⊆ s := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl
              · exact ha
              · exact Finset.mem_of_mem_erase hb
              · exact hk
            have hcard : ({a, b, k} : Finset I).card = 3 := by
              have hab : a ≠ b := (Finset.ne_of_mem_erase hb).symm
              rw [Finset.card_insert_of_notMem (by simp [hab, Ne.symm hka]),
                Finset.card_insert_of_notMem (by simp [Ne.symm hkb]), Finset.card_singleton]
            have := Finset.card_le_card hsub
            omega
      · obtain ⟨y, hyR, hya, -⟩ := hpair a a
        refine ⟨y, hyR, fun k hk ↦ ?_⟩
        by_cases hka : k = a
        · exact hka ▸ hya
        · exact absurd ⟨k, Finset.mem_erase.2 ⟨hka, hk⟩⟩ h1
    · obtain ⟨i₁, hi₁, i₂, hi₂, i₃, hi₃, h12, h13, h23⟩ :=
        exists_three_distinct_of_two_lt_card (lt_of_not_ge hle)
      have hlt : ∀ j ∈ s, (s.erase j).card < s.card := fun j hj ↦
        Finset.card_erase_lt_of_mem hj
      obtain ⟨y₁, hy₁R, hy₁⟩ := ih _ (hlt i₁ hi₁) (s.erase i₁)
        ⟨i₂, Finset.mem_erase.2 ⟨h12.symm, hi₂⟩⟩ rfl
      obtain ⟨y₂, hy₂R, hy₂⟩ := ih _ (hlt i₂ hi₂) (s.erase i₂)
        ⟨i₁, Finset.mem_erase.2 ⟨h12, hi₁⟩⟩ rfl
      obtain ⟨y₃, hy₃R, hy₃⟩ := ih _ (hlt i₃ hi₃) (s.erase i₃)
        ⟨i₁, Finset.mem_erase.2 ⟨h13, hi₁⟩⟩ rfl
      refine ⟨fun k ↦ f (fun t ↦ ![y₁, y₂, y₃] t k),
        hR ![y₁, y₂, y₃] (fun t ↦ by fin_cases t <;> assumption), fun k hk ↦ ?_⟩
      change f (fun t ↦ (![y₁, y₂, y₃] t) k) = x k
      have hvec : (fun t : Fin 3 ↦ (![y₁, y₂, y₃] t) k) = ![y₁ k, y₂ k, y₃ k] := by
        ext t
        fin_cases t <;> rfl
      rw [hvec]
      refine hf.apply_of_two_eq (p := k ≠ i₁) (q := k ≠ i₂) (r := k ≠ i₃)
        (fun h ↦ hy₁ k (Finset.mem_erase.2 ⟨h, hk⟩))
        (fun h ↦ hy₂ k (Finset.mem_erase.2 ⟨h, hk⟩))
        (fun h ↦ hy₃ k (Finset.mem_erase.2 ⟨h, hk⟩)) ?_
      by_cases hk1 : k = i₁
      · subst hk1
        exact Or.inr (Or.inr ⟨h12, h13⟩)
      · by_cases hk2 : k = i₂
        · subst hk2
          exact Or.inr (Or.inl ⟨hk1, h23⟩)
        · exact Or.inl ⟨hk1, hk2⟩

/-- **Baker–Pixley binary decomposability.** Let `R : Set (I → D)` be a relation on a finite index
type `I` preserved by a majority polymorphism `f`. A tuple `x : I → D` lies in `R` if and only if
`R` is nonempty and every pair of coordinates `(x i, x j)` agrees with some member of `R`. -/
theorem IsMajorityOp.mem_iff_pairwise_proj [Finite I] {f : (Fin 3 → D) → D} (hf : IsMajorityOp f)
    {R : Set (I → D)} (hR : IsPolymorphism f R) {x : I → D} :
    x ∈ R ↔ R.Nonempty ∧ ∀ i j : I, ∃ y ∈ R, y i = x i ∧ y j = x j := by
  classical
  cases nonempty_fintype I
  refine ⟨fun hx ↦ ⟨⟨x, hx⟩, fun i j ↦ ⟨x, hx, rfl, rfl⟩⟩, fun ⟨hne, hpair⟩ ↦ ?_⟩
  by_cases hI : Nonempty I
  · obtain ⟨y, hyR, hy⟩ := hf.exists_agree_on_finset hR hpair Finset.univ Finset.univ_nonempty
    have hyx : y = x := funext fun i ↦ hy i (Finset.mem_univ i)
    exact hyx ▸ hyR
  · have : IsEmpty I := not_nonempty_iff.1 hI
    obtain ⟨y, hyR⟩ := hne
    have hyx : y = x := funext fun i ↦ isEmptyElim i
    exact hyx ▸ hyR

/-- **Baker–Pixley binary decomposability (nonempty arity).** When `I` is finite and nonempty and
`R : Set (I → D)` is preserved by a majority polymorphism, `x ∈ R` if and only if every pair of
coordinates of `x` extends to an element of `R`. -/
theorem IsMajorityOp.mem_iff_pairwise_proj_of_nonempty [Finite I] [Nonempty I]
    {f : (Fin 3 → D) → D} (hf : IsMajorityOp f)
    {R : Set (I → D)} (hR : IsPolymorphism f R) {x : I → D} :
    x ∈ R ↔ ∀ i j : I, ∃ y ∈ R, y i = x i ∧ y j = x j := by
  rw [hf.mem_iff_pairwise_proj hR]
  refine ⟨And.right, fun hpair ↦ ⟨?_, hpair⟩⟩
  obtain ⟨i⟩ := ‹Nonempty I›
  obtain ⟨y, hyR, -⟩ := hpair i i
  exact ⟨y, hyR⟩

end BakerPixley

section BinaryClassification

variable {D : Type*}

/-- Coordinatewise preservation of a binary relation `R : Set (D × D)` by a ternary operation
`f : (Fin 3 → D) → D`. -/
@[expose] def IsBinaryPolymorphism (f : (Fin 3 → D) → D) (R : Set (D × D)) : Prop :=
  ∀ u v w : D × D, u ∈ R → v ∈ R → w ∈ R → (f ![u.1, v.1, w.1], f ![u.2, v.2, w.2]) ∈ R

/-- Equivalence between `IsBinaryPolymorphism f R` and `Cslib.Logic.IsPolymorphism f` on the
corresponding set of `Fin 2 → D` tuples. -/
theorem isBinaryPolymorphism_iff_isPolymorphism {f : (Fin 3 → D) → D} {R : Set (D × D)} :
    IsBinaryPolymorphism f R ↔ IsPolymorphism f {t : Fin 2 → D | (t 0, t 1) ∈ R} := by
  constructor
  · intro h a ha
    have hv0 : (fun j : Fin 3 ↦ a j 0) = ![a 0 0, a 1 0, a 2 0] := (vec3_eq _).symm
    have hv1 : (fun j : Fin 3 ↦ a j 1) = ![a 0 1, a 1 1, a 2 1] := (vec3_eq _).symm
    change (f (fun j ↦ a j 0), f (fun j ↦ a j 1)) ∈ R
    rw [hv0, hv1]
    exact h (a 0 0, a 0 1) (a 1 0, a 1 1) (a 2 0, a 2 1) (ha 0) (ha 1) (ha 2)
  · intro h u v w hu hv hw
    let a : Fin 3 → Fin 2 → D := ![![u.1, u.2], ![v.1, v.2], ![w.1, w.2]]
    have ha : ∀ j : Fin 3, (a j 0, a j 1) ∈ R := fun j ↦ by
      fin_cases j <;> assumption
    have hres := h a ha
    have hv0 : (fun j : Fin 3 ↦ a j 0) = ![u.1, v.1, w.1] := by ext j; fin_cases j <;> rfl
    have hv1 : (fun j : Fin 3 ↦ a j 1) = ![u.2, v.2, w.2] := by ext j; fin_cases j <;> rfl
    change (f (fun j ↦ a j 0), f (fun j ↦ a j 1)) ∈ R at hres
    rwa [hv0, hv1] at hres

/-- Swapping coordinates preserves `IsBinaryPolymorphism`. -/
theorem IsBinaryPolymorphism.swap {f : (Fin 3 → D) → D} {R : Set (D × D)}
    (h : IsBinaryPolymorphism f R) : IsBinaryPolymorphism f (Prod.swap '' R) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ ⟨⟨x₁, y₁⟩, h1, he1⟩ ⟨⟨x₂, y₂⟩, h2, he2⟩
    ⟨⟨x₃, y₃⟩, h3, he3⟩
  cases he1
  cases he2
  cases he3
  exact ⟨_, h _ _ _ h1 h2 h3, rfl⟩

/-- Intersection of two `IsBinaryPolymorphism`-closed binary relations is closed. -/
theorem IsBinaryPolymorphism.inter {f : (Fin 3 → D) → D} {R₁ R₂ : Set (D × D)}
    (h₁ : IsBinaryPolymorphism f R₁) (h₂ : IsBinaryPolymorphism f R₂) :
    IsBinaryPolymorphism f (R₁ ∩ R₂) :=
  fun u v w hu hv hw ↦ ⟨h₁ u v w hu.1 hv.1 hw.1, h₂ u v w hu.2 hv.2 hw.2⟩

/-- Relational composition `{(a, c) | ∃ b, (a, b) ∈ R₁ ∧ (b, c) ∈ R₂}` preserves binary
polymorphisms. -/
theorem IsBinaryPolymorphism.relComp {f : (Fin 3 → D) → D} {R₁ R₂ : Set (D × D)}
    (h₁ : IsBinaryPolymorphism f R₁) (h₂ : IsBinaryPolymorphism f R₂) :
    IsBinaryPolymorphism f {p : D × D | ∃ b, (p.1, b) ∈ R₁ ∧ (b, p.2) ∈ R₂} := by
  rintro ⟨a₁, c₁⟩ ⟨a₂, c₂⟩ ⟨a₃, c₃⟩ ⟨b₁, h1l, h1r⟩ ⟨b₂, h2l, h2r⟩ ⟨b₃, h3l, h3r⟩
  exact ⟨f ![b₁, b₂, b₃], h₁ _ _ _ h1l h2l h3l, h₂ _ _ _ h1r h2r h3r⟩

/-- The first-coordinate projection `{a | ∃ b, (a, b) ∈ R}` of a binary relation. -/
@[expose] def fstProj (R : Set (D × D)) : Set D := Prod.fst '' R

/-- The first projection of the empty binary relation is empty. -/
@[simp]
theorem fstProj_empty : fstProj (∅ : Set (D × D)) = ∅ :=
  Set.image_empty Prod.fst

/-- The second-coordinate projection `{b | ∃ a, (a, b) ∈ R}` of a binary relation. -/
@[expose] def sndProj (R : Set (D × D)) : Set D := Prod.snd '' R

/-- The second projection of the empty binary relation is empty. -/
@[simp]
theorem sndProj_empty : sndProj (∅ : Set (D × D)) = ∅ :=
  Set.image_empty Prod.snd

/-- A binary relation `R ⊆ D × D` is a *permutation relation* (partial bijection) if every first
coordinate determines a unique second coordinate and vice versa. -/
@[expose] def IsPermutationBinaryRel (R : Set (D × D)) : Prop :=
  (∀ a b₁ b₂, (a, b₁) ∈ R → (a, b₂) ∈ R → b₁ = b₂) ∧
    (∀ a₁ a₂ b, (a₁, b) ∈ R → (a₂, b) ∈ R → a₁ = a₂)

/-- Every permutation binary relation is the graph of a bijection `fstProj R ≃ sndProj R`. -/
theorem isPermutationBinaryRel_iff_exists_equiv {R : Set (D × D)} :
    IsPermutationBinaryRel R ↔
      ∃ e : fstProj R ≃ sndProj R,
        ∀ a b, (a, b) ∈ R ↔ ∃ ha : a ∈ fstProj R, (e ⟨a, ha⟩ : D) = b := by
  classical
  constructor
  · rintro ⟨hl, hr⟩
    have hfwd : ∀ x : fstProj R, ∃ y : sndProj R, (x.1, y.1) ∈ R := by
      rintro ⟨a, ⟨⟨a', b⟩, hab, rfl⟩⟩
      exact ⟨⟨b, ⟨(a', b), hab, rfl⟩⟩, hab⟩
    have hbwd : ∀ y : sndProj R, ∃ x : fstProj R, (x.1, y.1) ∈ R := by
      rintro ⟨b, ⟨⟨a, b'⟩, hab, rfl⟩⟩
      exact ⟨⟨a, ⟨(a, b'), hab, rfl⟩⟩, hab⟩
    choose f hf using hfwd
    choose g hg using hbwd
    refine ⟨{ toFun := f
              invFun := g
              left_inv := fun x ↦ Subtype.ext (hr _ _ _ (hg (f x)) (hf x))
              right_inv := fun y ↦ Subtype.ext (hl _ _ _ (hf (g y)) (hg y)) },
      fun a b ↦ ?_⟩
    constructor
    · intro hab
      have ha : a ∈ fstProj R := ⟨(a, b), hab, rfl⟩
      exact ⟨ha, hl a _ b (hf ⟨a, ha⟩) hab⟩
    · rintro ⟨ha, rfl⟩
      exact hf ⟨a, ha⟩
  · rintro ⟨e, he⟩
    refine ⟨fun a b₁ b₂ h1 h2 ↦ ?_, fun a₁ a₂ b h1 h2 ↦ ?_⟩
    · obtain ⟨ha1, rfl⟩ := (he a b₁).1 h1
      obtain ⟨_, rfl⟩ := (he a b₂).1 h2
      rfl
    · obtain ⟨ha1, hb1⟩ := (he a₁ b).1 h1
      obtain ⟨ha2, hb2⟩ := (he a₂ b).1 h2
      have hinj : (⟨a₁, ha1⟩ : fstProj R) = ⟨a₂, ha2⟩ :=
        e.injective (Subtype.ext (hb1.trans hb2.symm))
      exact congrArg Subtype.val hinj

/-- A binary relation `R ⊆ D × D` is a *complete relation* if it equals the full Cartesian product
`fstProj R ×ˢ sndProj R` of its two projections. -/
@[expose] def IsCompleteBinaryRel (R : Set (D × D)) : Prop :=
  R = fstProj R ×ˢ sndProj R

/-- Characterization of complete binary relations as Cartesian products of their projections. -/
theorem isCompleteBinaryRel_iff {R : Set (D × D)} :
    IsCompleteBinaryRel R ↔ R = fstProj R ×ˢ sndProj R :=
  Iff.rfl

/-- A binary relation `R ⊆ D × D` is a *two-fan relation* (including degenerate one-fans) if there
exist pivot elements `a ∈ fstProj R` and `b ∈ sndProj R` such that
`R = ({a} ×ˢ sndProj R) ∪ (fstProj R ×ˢ {b})`. -/
@[expose] def IsTwoFanBinaryRel (R : Set (D × D)) : Prop :=
  ∃ a ∈ fstProj R, ∃ b ∈ sndProj R, R = ({a} ×ˢ sndProj R) ∪ (fstProj R ×ˢ {b})

/-- **Left fiber dichotomy.** If `R` is preserved by the dual discriminator and `a` is related to
two distinct elements `b₁ ≠ b₂`, then `a` is related to every element of `sndProj R`. -/
theorem IsDualDiscriminatorOp.fiber_eq_sndProj_of_two {f : (Fin 3 → D) → D}
    (hf : IsDualDiscriminatorOp f) {R : Set (D × D)} (hR : IsBinaryPolymorphism f R)
    {a b₁ b₂ : D} (h1 : (a, b₁) ∈ R) (h2 : (a, b₂) ∈ R) (hne : b₁ ≠ b₂) :
    ∀ y ∈ sndProj R, (a, y) ∈ R := by
  obtain ⟨heq, hdist⟩ := isDualDiscriminatorOp_iff.1 hf
  rintro y ⟨⟨x, y'⟩, hxy, rfl⟩
  have hmem := hR (x, y') (a, b₁) (a, b₂) hxy h1 h2
  rwa [heq x a, hdist y' b₁ b₂ hne] at hmem

/-- **Right fiber dichotomy.** If `R` is preserved by the dual discriminator and `b` is related to
two distinct elements `a₁ ≠ a₂`, then every element of `fstProj R` is related to `b`. -/
theorem IsDualDiscriminatorOp.cofiber_eq_fstProj_of_two {f : (Fin 3 → D) → D}
    (hf : IsDualDiscriminatorOp f) {R : Set (D × D)} (hR : IsBinaryPolymorphism f R)
    {a₁ a₂ b : D} (h1 : (a₁, b) ∈ R) (h2 : (a₂, b) ∈ R) (hne : a₁ ≠ a₂) :
    ∀ x ∈ fstProj R, (x, b) ∈ R := by
  obtain ⟨heq, hdist⟩ := isDualDiscriminatorOp_iff.1 hf
  rintro x ⟨⟨x', y⟩, hxy, rfl⟩
  have hmem := hR (x', y) (a₁, b) (a₂, b) hxy h1 h2
  rwa [hdist x' a₁ a₂ hne, heq y b] at hmem

private theorem classify_of_left_branch {f : (Fin 3 → D) → D} (hf : IsDualDiscriminatorOp f)
    {R : Set (D × D)} (hR : IsBinaryPolymorphism f R)
    {a b₁ b₂ : D} (h1 : (a, b₁) ∈ R) (h2 : (a, b₂) ∈ R) (hne : b₁ ≠ b₂) :
    IsCompleteBinaryRel R ∨ IsTwoFanBinaryRel R := by
  classical
  have ha_full : ∀ y ∈ sndProj R, (a, y) ∈ R := hf.fiber_eq_sndProj_of_two hR h1 h2 hne
  have ha_mem : a ∈ fstProj R := ⟨(a, b₁), h1, rfl⟩
  have hb₁_mem : b₁ ∈ sndProj R := ⟨(a, b₁), h1, rfl⟩
  by_cases hother : ∃ a' c₁ c₂, a' ≠ a ∧ (a', c₁) ∈ R ∧ (a', c₂) ∈ R ∧ c₁ ≠ c₂
  · left
    obtain ⟨a', c₁, c₂, hne_a, hc1, hc2, hne_c⟩ := hother
    have ha'_full : ∀ y ∈ sndProj R, (a', y) ∈ R := hf.fiber_eq_sndProj_of_two hR hc1 hc2 hne_c
    refine Set.Subset.antisymm
      (fun ⟨x, y⟩ hxy ↦ ⟨⟨(x, y), hxy, rfl⟩, ⟨(x, y), hxy, rfl⟩⟩) ?_
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact hf.cofiber_eq_fstProj_of_two hR (ha'_full y hy) (ha_full y hy) hne_a x hx
  · right
    push Not at hother
    by_cases hex : ∃ x₁ b, x₁ ≠ a ∧ (x₁, b) ∈ R
    · obtain ⟨x₁, b, hx₁a, hx₁b⟩ := hex
      have hb_mem : b ∈ sndProj R := ⟨(x₁, b), hx₁b, rfl⟩
      have hb_full : ∀ x ∈ fstProj R, (x, b) ∈ R :=
        hf.cofiber_eq_fstProj_of_two hR hx₁b (ha_full b hb_mem) hx₁a
      refine ⟨a, ha_mem, b, hb_mem, Set.Subset.antisymm ?_ ?_⟩
      · rintro ⟨x, y⟩ hxy
        by_cases hxa : x = a
        · exact Or.inl ⟨hxa, ⟨(x, y), hxy, rfl⟩⟩
        · exact Or.inr ⟨⟨(x, y), hxy, rfl⟩,
            hother x y b hxa hxy (hb_full x ⟨(x, y), hxy, rfl⟩)⟩
      · rintro ⟨x, y⟩ (⟨hxa, hy⟩ | ⟨hx, hyb⟩)
        · dsimp only at hxa hy
          rw [Set.mem_singleton_iff.1 hxa]
          exact ha_full y hy
        · dsimp only at hx hyb
          rw [Set.mem_singleton_iff.1 hyb]
          exact hb_full x hx
    · push Not at hex
      refine ⟨a, ha_mem, b₁, hb₁_mem, Set.Subset.antisymm ?_ ?_⟩
      · rintro ⟨x, y⟩ hxy
        by_cases hxa : x = a
        · exact Or.inl ⟨hxa, ⟨(x, y), hxy, rfl⟩⟩
        · exact absurd hxy (hex x y hxa)
      · rintro ⟨x, y⟩ (⟨hxa, hy⟩ | ⟨⟨⟨x', y'⟩, hxy', rfl⟩, hyb⟩)
        · dsimp only at hxa hy
          rw [Set.mem_singleton_iff.1 hxa]
          exact ha_full y hy
        · dsimp only at hyb
          have hxa : x' = a := by
            by_contra hne'
            exact hex x' y' hne' hxy'
          rw [hxa, Set.mem_singleton_iff.1 hyb]
          exact h1

/-- **Jeavons–Cohen–Cooper three-type classification of dual-discriminator-preserved binary
relations.** A binary relation `R ⊆ D × D` on an arbitrary domain `D` is preserved by a dual
discriminator operation `f` if and only if `R` is a permutation relation, a complete relation, or
a two-fan relation. -/
theorem IsDualDiscriminatorOp.isBinaryPolymorphism_iff {f : (Fin 3 → D) → D}
    (hf : IsDualDiscriminatorOp f) {R : Set (D × D)} :
    IsBinaryPolymorphism f R ↔
      IsPermutationBinaryRel R ∨ IsCompleteBinaryRel R ∨ IsTwoFanBinaryRel R := by
  classical
  obtain ⟨heq, hdist⟩ := isDualDiscriminatorOp_iff.1 hf
  constructor
  · intro hR
    by_cases hperm : IsPermutationBinaryRel R
    · exact Or.inl hperm
    · right
      simp only [IsPermutationBinaryRel, not_and_or] at hperm
      rcases hperm with hleft | hright
      · push Not at hleft
        obtain ⟨a, b₁, b₂, h1, h2, hne⟩ := hleft
        exact classify_of_left_branch hf hR h1 h2 hne
      · push Not at hright
        obtain ⟨a₁, a₂, b, h1, h2, hne⟩ := hright
        have hswap1 : (b, a₁) ∈ Prod.swap '' R := ⟨(a₁, b), h1, rfl⟩
        have hswap2 : (b, a₂) ∈ Prod.swap '' R := ⟨(a₂, b), h2, rfl⟩
        have hfst_swap : fstProj (Prod.swap '' R) = sndProj R := by
          ext y
          simp [fstProj, sndProj]
        have hsnd_swap : sndProj (Prod.swap '' R) = fstProj R := by
          ext x
          simp [fstProj, sndProj]
        rcases classify_of_left_branch hf hR.swap hswap1 hswap2 hne with hcomp | hfan
        · left
          rw [IsCompleteBinaryRel, hfst_swap, hsnd_swap] at hcomp
          ext ⟨x, y⟩
          have hmem : (y, x) ∈ Prod.swap '' R ↔ (y, x) ∈ sndProj R ×ˢ fstProj R := by rw [hcomp]
          simpa [and_comm] using hmem
        · right
          obtain ⟨b₀, hb₀, a₀, ha₀, heq_swap⟩ := hfan
          rw [hfst_swap] at hb₀
          rw [hsnd_swap] at ha₀
          refine ⟨a₀, ha₀, b₀, hb₀, ?_⟩
          ext ⟨x, y⟩
          have hmem : (y, x) ∈ Prod.swap '' R ↔
              (y, x) ∈ ({b₀} ×ˢ fstProj R) ∪ (sndProj R ×ˢ {a₀}) := by
            rw [heq_swap, hfst_swap, hsnd_swap]
          simpa [or_comm, and_comm] using hmem
  · rintro (⟨hl, hr⟩ | hcomp | ⟨a, _, b, _, hfan⟩)
    · intro u v w hu hv hw
      by_cases hv1 : v.1 = w.1
      · have hv2 : v.2 = w.2 := hl v.1 v.2 w.2 hv (hv1 ▸ hw)
        rw [hv1, hv2, heq, heq]
        exact hw
      · have hv2 : v.2 ≠ w.2 := fun h2 ↦ hv1 (hr v.1 w.1 v.2 hv (h2 ▸ hw))
        rw [hdist _ _ _ hv1, hdist _ _ _ hv2]
        exact hu
    · intro u v w hu hv _
      rw [hcomp] at hu hv ⊢
      refine ⟨?_, ?_⟩
      · rcases hf.apply_eq_first_or_second ![u.1, v.1, w.1] with h | h <;> rw [h]
        · exact hu.1
        · exact hv.1
      · rcases hf.apply_eq_first_or_second ![u.2, v.2, w.2] with h | h <;> rw [h]
        · exact hu.2
        · exact hv.2
    · intro u v w hu hv hw
      have hproj : ∀ p ∈ R, p.1 ∈ fstProj R ∧ p.2 ∈ sndProj R :=
        fun p hp ↦ ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
      have hfst : f ![u.1, v.1, w.1] ∈ fstProj R := by
        rcases hf.apply_eq_first_or_second ![u.1, v.1, w.1] with h | h <;> rw [h]
        · exact (hproj u hu).1
        · exact (hproj v hv).1
      have hsnd : f ![u.2, v.2, w.2] ∈ sndProj R := by
        rcases hf.apply_eq_first_or_second ![u.2, v.2, w.2] with h | h <;> rw [h]
        · exact (hproj u hu).2
        · exact (hproj v hv).2
      have hmem_fan : ∀ p ∈ R, p.1 = a ∨ p.2 = b := by
        intro p hp
        rw [hfan] at hp
        rcases hp with ⟨hpa, _⟩ | ⟨_, hpb⟩
        · exact Or.inl (Set.mem_singleton_iff.1 hpa)
        · exact Or.inr (Set.mem_singleton_iff.1 hpb)
      rw [hfan]
      by_cases hv2 : v.2 = w.2
      · by_cases hvb : v.2 = b
        · right
          refine ⟨hfst, ?_⟩
          rw [← hv2, heq, hvb]
          rfl
        · have hva : v.1 = a := (hmem_fan v hv).resolve_right hvb
          have hwa : w.1 = a := (hmem_fan w hw).resolve_right (hv2 ▸ hvb)
          left
          refine ⟨?_, hsnd⟩
          rw [hva, hwa, heq]
          rfl
      · rw [hdist _ _ _ hv2]
        by_cases hv1 : v.1 = w.1
        · have hva : v.1 = a := by
            rcases hmem_fan v hv with hva | hvb
            · exact hva
            · rcases hmem_fan w hw with hwa | hwb
              · exact hv1.trans hwa
              · exact absurd (hvb.trans hwb.symm) hv2
          left
          rw [hv1, heq, ← hv1, hva]
          exact ⟨rfl, (hproj u hu).2⟩
        · rw [hdist _ _ _ hv1, ← hfan]
          exact hu

end BinaryClassification

section PathConsistency

variable {V D : Type*}

/-- A binary constraint network `B : V → V → Set (D × D)` is *path-consistent* (3-consistent) if
its diagonal relations are contained in the equality diagonal, its constraints are symmetric, and
every pair `(a, c) ∈ B i k` extends through every third variable `j` to some `b : D` with
`(a, b) ∈ B i j` and `(b, c) ∈ B j k`. -/
structure IsPathConsistentNetwork (B : V → V → Set (D × D)) : Prop where
  /-- Diagonal constraints enforce equality. -/
  diag : ∀ i a b, (a, b) ∈ B i i → a = b
  /-- Constraints are symmetric under variable and coordinate swap. -/
  symm : ∀ i j a b, (a, b) ∈ B i j → (b, a) ∈ B j i
  /-- Every consistent pair implies diagonal membership of its first coordinate. -/
  fst_diag : ∀ i j a b, (a, b) ∈ B i j → (a, a) ∈ B i i
  /-- Path consistency (3-consistency): every pair in `B i k` composes through `B i j` and
  `B j k`. -/
  comp : ∀ i j k a c, (a, c) ∈ B i k → ∃ b, (a, b) ∈ B i j ∧ (b, c) ∈ B j k

/-- In a path-consistent network, every consistent pair `(a, b) ∈ B i j` also implies diagonal
membership `(b, b) ∈ B j j`. -/
theorem IsPathConsistentNetwork.snd_diag {B : V → V → Set (D × D)}
    (hB : IsPathConsistentNetwork B) {i j : V} {a b : D} (h : (a, b) ∈ B i j) :
    (b, b) ∈ B j j :=
  hB.fst_diag j i b a (hB.symm i j a b h)

private theorem IsMajorityOp.exists_one_step_extension {f : (Fin 3 → D) → D} (hf : IsMajorityOp f)
    {B : V → V → Set (D × D)} (hB : IsPathConsistentNetwork B)
    (hmaj : ∀ i j, IsBinaryPolymorphism f (B i j))
    {s : Finset V} {x : V → D} (hx : ∀ i ∈ s, ∀ j ∈ s, (x i, x j) ∈ B i j) (r : V) :
    ∀ t : Finset V, t.Nonempty → t ⊆ s → ∃ c : D, ∀ i ∈ t, (x i, c) ∈ B i r := by
  classical
  intro t ht hts
  induction hn : t.card using Nat.strong_induction_on generalizing t with
  | ind n ih =>
    subst hn
    by_cases hle : t.card ≤ 2
    · obtain ⟨i, hi⟩ := ht
      by_cases h1 : (t.erase i).Nonempty
      · obtain ⟨k, hk⟩ := h1
        have hks : k ∈ s := hts (Finset.mem_of_mem_erase hk)
        obtain ⟨c, hic, hck⟩ := hB.comp i r k (x i) (x k) (hx i (hts hi) k hks)
        refine ⟨c, fun u hu ↦ ?_⟩
        by_cases hui : u = i
        · exact hui ▸ hic
        · by_cases huk : u = k
          · exact huk ▸ hB.symm r k c (x k) hck
          · have hik : i ≠ k := (Finset.ne_of_mem_erase hk).symm
            have hsub : ({i, k, u} : Finset V) ⊆ t := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl
              · exact hi
              · exact Finset.mem_of_mem_erase hk
              · exact hu
            have hcard : ({i, k, u} : Finset V).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [hik, Ne.symm hui]),
                Finset.card_insert_of_notMem (by simp [Ne.symm huk]), Finset.card_singleton]
            have := Finset.card_le_card hsub
            omega
      · obtain ⟨c, hic, -⟩ := hB.comp i r i (x i) (x i) (hx i (hts hi) i (hts hi))
        refine ⟨c, fun u hu ↦ ?_⟩
        by_cases hui : u = i
        · exact hui ▸ hic
        · exact absurd ⟨u, Finset.mem_erase.2 ⟨hui, hu⟩⟩ h1
    · obtain ⟨i₁, hi₁, i₂, hi₂, i₃, hi₃, h12, h13, h23⟩ :=
        exists_three_distinct_of_two_lt_card (lt_of_not_ge hle)
      obtain ⟨c₁, hc₁⟩ := ih _ (Finset.card_erase_lt_of_mem hi₁) (t.erase i₁)
        ⟨i₂, Finset.mem_erase.2 ⟨h12.symm, hi₂⟩⟩ ((Finset.erase_subset i₁ t).trans hts) rfl
      obtain ⟨c₂, hc₂⟩ := ih _ (Finset.card_erase_lt_of_mem hi₂) (t.erase i₂)
        ⟨i₁, Finset.mem_erase.2 ⟨h12, hi₁⟩⟩ ((Finset.erase_subset i₂ t).trans hts) rfl
      obtain ⟨c₃, hc₃⟩ := ih _ (Finset.card_erase_lt_of_mem hi₃) (t.erase i₃)
        ⟨i₁, Finset.mem_erase.2 ⟨h13, hi₁⟩⟩ ((Finset.erase_subset i₃ t).trans hts) rfl
      have hc₁_diag : (c₁, c₁) ∈ B r r :=
        hB.snd_diag (hc₁ i₂ (Finset.mem_erase.2 ⟨h12.symm, hi₂⟩))
      have hc₂_diag : (c₂, c₂) ∈ B r r :=
        hB.snd_diag (hc₂ i₁ (Finset.mem_erase.2 ⟨h12, hi₁⟩))
      have hc₃_diag : (c₃, c₃) ∈ B r r :=
        hB.snd_diag (hc₃ i₁ (Finset.mem_erase.2 ⟨h13, hi₁⟩))
      refine ⟨f ![c₁, c₂, c₃], fun i hi ↦ ?_⟩
      by_cases hk1 : i = i₁
      · subst hk1
        obtain ⟨u, -, hur⟩ := hB.comp r i r c₁ c₁ hc₁_diag
        have hm := hmaj i r (u, c₁) (x i, c₂) (x i, c₃) hur
          (hc₂ i (Finset.mem_erase.2 ⟨h12, hi⟩))
          (hc₃ i (Finset.mem_erase.2 ⟨h13, hi⟩))
        rwa [(hf (x i) u).2.2] at hm
      · by_cases hk2 : i = i₂
        · subst hk2
          obtain ⟨u, -, hur⟩ := hB.comp r i r c₂ c₂ hc₂_diag
          have hm := hmaj i r (x i, c₁) (u, c₂) (x i, c₃)
            (hc₁ i (Finset.mem_erase.2 ⟨hk1, hi⟩)) hur
            (hc₃ i (Finset.mem_erase.2 ⟨h23, hi⟩))
          rwa [(hf (x i) u).2.1] at hm
        · by_cases hk3 : i = i₃
          · subst hk3
            obtain ⟨u, -, hur⟩ := hB.comp r i r c₃ c₃ hc₃_diag
            have hm := hmaj i r (x i, c₁) (x i, c₂) (u, c₃)
              (hc₁ i (Finset.mem_erase.2 ⟨hk1, hi⟩))
              (hc₂ i (Finset.mem_erase.2 ⟨hk2, hi⟩)) hur
            rwa [(hf (x i) u).1] at hm
          · have hm := hmaj i r (x i, c₁) (x i, c₂) (x i, c₃)
              (hc₁ i (Finset.mem_erase.2 ⟨hk1, hi⟩))
              (hc₂ i (Finset.mem_erase.2 ⟨hk2, hi⟩))
              (hc₃ i (Finset.mem_erase.2 ⟨hk3, hi⟩))
            rwa [hf.idempotent (x i)] at hm

/-- **Exact binary projection recovery via path consistency.** In a finite path-consistent binary
constraint network `B` whose relations are preserved by a majority polymorphism `f`, every pair
`(a, b) ∈ B p q` extends to a global solution `x : V → D` with `x p = a`, `x q = b`, and
`∀ i j, (x i, x j) ∈ B i j`. -/
theorem IsMajorityOp.exists_solution_extending_pair [Finite V]
    {f : (Fin 3 → D) → D} (hf : IsMajorityOp f)
    {B : V → V → Set (D × D)} (hB : IsPathConsistentNetwork B)
    (hmaj : ∀ i j, IsBinaryPolymorphism f (B i j))
    {p q : V} {a b : D} (hab : (a, b) ∈ B p q) :
    ∃ x : V → D, x p = a ∧ x q = b ∧ ∀ i j, (x i, x j) ∈ B i j := by
  classical
  cases nonempty_fintype V
  have hfin : ∀ s : Finset V, p ∈ s → q ∈ s →
      ∃ x : V → D, x p = a ∧ x q = b ∧ ∀ i ∈ s, ∀ j ∈ s, (x i, x j) ∈ B i j := by
    intro s hps hqs
    induction hn : s.card using Nat.strong_induction_on generalizing s with
    | ind n ih =>
      subst hn
      by_cases hex : ∃ r ∈ s, r ≠ p ∧ r ≠ q
      · obtain ⟨r, hrs, hrp, hrq⟩ := hex
        let s' := s.erase r
        have hps' : p ∈ s' := Finset.mem_erase.2 ⟨hrp.symm, hps⟩
        have hqs' : q ∈ s' := Finset.mem_erase.2 ⟨hrq.symm, hqs⟩
        obtain ⟨x₀, hxp, hxq, hx₀⟩ :=
          ih s'.card (Finset.card_erase_lt_of_mem hrs) s' hps' hqs' rfl
        obtain ⟨c, hc⟩ := hf.exists_one_step_extension hB hmaj hx₀ r s' ⟨p, hps'⟩
          (Finset.Subset.refl s')
        let x : V → D := Function.update x₀ r c
        refine ⟨x, ?_, ?_, fun i hi j hj ↦ ?_⟩
        · simp [x, hrp.symm, hxp]
        · simp [x, hrq.symm, hxq]
        · by_cases hir : i = r <;> by_cases hjr : j = r
          · subst hir
            subst hjr
            simpa [x] using hB.snd_diag (hc p hps')
          · subst hir
            have hjs' : j ∈ s' := Finset.mem_erase.2 ⟨hjr, hj⟩
            simpa [x, hjr] using hB.symm j i (x₀ j) c (hc j hjs')
          · subst hjr
            have his' : i ∈ s' := Finset.mem_erase.2 ⟨hir, hi⟩
            simpa [x, hir] using hc i his'
          · have his' : i ∈ s' := Finset.mem_erase.2 ⟨hir, hi⟩
            have hjs' : j ∈ s' := Finset.mem_erase.2 ⟨hjr, hj⟩
            simpa [x, hir, hjr] using hx₀ i his' j hjs'
      · push Not at hex
        have hmem : ∀ i ∈ s, i = p ∨ i = q := fun i hi ↦ by
          by_cases hip : i = p
          · exact Or.inl hip
          · exact Or.inr (hex i hi hip)
        let x : V → D := fun i ↦ if i = p then a else b
        have hxq : x q = b := by
          by_cases hqp : q = p
          · subst hqp
            simp [x, hB.diag q a b hab]
          · simp [x, hqp]
        have hxp : x p = a := by simp [x]
        have hpp : (a, a) ∈ B p p := hB.fst_diag p q a b hab
        have hqq : (b, b) ∈ B q q := hB.snd_diag hab
        have hqp : (b, a) ∈ B q p := hB.symm p q a b hab
        refine ⟨x, hxp, hxq, fun j₁ hj₁ j₂ hj₂ ↦ ?_⟩
        rcases hmem j₁ hj₁ with h1 | h1 <;> rcases hmem j₂ hj₂ with h2 | h2 <;>
          simp only [h1, h2, hxp, hxq]
        exacts [hpp, hab, hqp, hqq]
  obtain ⟨x, hxp, hxq, hx⟩ := hfin Finset.univ (Finset.mem_univ p) (Finset.mem_univ q)
  exact ⟨x, hxp, hxq, fun i j ↦ hx i (Finset.mem_univ i) j (Finset.mem_univ j)⟩

end PathConsistency

-- Non-vacuity check: on `Fin 3`, a non-identity permutation relation and a genuine two-fan
-- relation are both preserved by `dualDiscriminator`.
example :
    let Rperm : Set (Fin 3 × Fin 3) := {(0, 1), (1, 2), (2, 0)}
    let Rfan : Set (Fin 3 × Fin 3) := ({0} ×ˢ Set.univ) ∪ (Set.univ ×ˢ {2})
    IsBinaryPolymorphism dualDiscriminator Rperm ∧
      IsBinaryPolymorphism dualDiscriminator Rfan := by
  refine ⟨?_, ?_⟩
  · refine (isDualDiscriminatorOp_dualDiscriminator.isBinaryPolymorphism_iff).2 (Or.inl ⟨?_, ?_⟩)
    · intro a b₁ b₂ h1 h2
      rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
        cases h1 <;> cases h2 <;> rfl
    · intro a₁ a₂ b h1 h2
      rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
        cases h1 <;> cases h2 <;> rfl
  · refine (isDualDiscriminatorOp_dualDiscriminator.isBinaryPolymorphism_iff).2
      (Or.inr (Or.inr ?_))
    have hfst : fstProj (({0} ×ˢ Set.univ) ∪ (Set.univ ×ˢ {2}) : Set (Fin 3 × Fin 3)) =
        Set.univ := by
      ext x
      exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨(x, 2), Or.inr ⟨trivial, rfl⟩, rfl⟩⟩
    have hsnd : sndProj (({0} ×ˢ Set.univ) ∪ (Set.univ ×ˢ {2}) : Set (Fin 3 × Fin 3)) =
        Set.univ := by
      ext y
      exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨(0, y), Or.inl ⟨rfl, trivial⟩, rfl⟩⟩
    exact ⟨0, hfst.symm ▸ Set.mem_univ 0, 2, hsnd.symm ▸ Set.mem_univ 2, by rw [hfst, hsnd]⟩

end Cslib.Logic
