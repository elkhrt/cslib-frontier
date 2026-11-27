/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Computability.Reduce

import Mathlib.Computability.Primrec.List

/-!
# Lightface Analytical Hierarchy Classes $\Pi^1_1$ and $\Sigma^1_1$

This module develops the Kleene normal form characterization of the first level of the lightface
analytical hierarchy ($\Pi^1_1$ and $\Sigma^1_1$ subsets of $\mathbb{N}$) together with closure
properties and many-one $\Pi^1_1$- / $\Sigma^1_1$-hardness and completeness under standard Lean
axioms.

## Main definitions

* `CslibFrontier.Computability.Complexity.Classes.IsLightfacePi11`: effective coanalytic subsets
  of `ℕ` via Kleene prefix trees (`n ∈ S ↔ ∀ α : ℕ → ℕ, ∃ m, R (n, [α 0..., α (m - 1)]) = true`).
* `CslibFrontier.Computability.Complexity.Classes.IsLightfaceSigma11`: effective analytic subsets
  of `ℕ` (`n ∈ S ↔ ∃ α : ℕ → ℕ, ∀ m, R (n, [α 0..., α (m - 1)]) = true`).
* `CslibFrontier.Computability.Complexity.Classes.IsPi11Hard`,
  `CslibFrontier.Computability.Complexity.Classes.IsPi11Complete`,
  `CslibFrontier.Computability.Complexity.Classes.IsSigma11Hard`,
  `CslibFrontier.Computability.Complexity.Classes.IsSigma11Complete`: many-one hardness and
  completeness for $\Pi^1_1$ and $\Sigma^1_1$.

## Main results

* `IsLightfacePi11.of_computablePred`, `IsLightfacePi11.of_manyOneReducible`,
  `IsLightfacePi11.inter`, `IsLightfacePi11.union`: computable containment and closure of
  lightface $\Pi^1_1$ sets under many-one preimages, binary intersection, and binary union.
* `isLightfaceSigma11_compl_iff`, `isLightfacePi11_compl_iff`: complementation duality between
  $\Pi^1_1$ and $\Sigma^1_1$.
* `IsPi11Hard.of_manyOneReducible`, `IsPi11Complete.of_manyOneReducible`,
  `isSigma11Complete_compl_iff`: transfer of hardness and completeness along many-one reductions
  and complementation.
-/

public section

namespace CslibFrontier.Computability.Complexity.Classes

/-- A subset `S : Set ℕ` is lightface $\Pi^1_1$ (effectively coanalytic) if it admits a Kleene
normal form via a computable Boolean predicate on finite sequence prefixes: `n ∈ S` iff every
infinite sequence `α : ℕ → ℕ` has a finite prefix accepted by `R`. -/
def IsLightfacePi11 (S : Set ℕ) : Prop :=
  ∃ R : ℕ × List ℕ → Bool, Computable R ∧
    ∀ n : ℕ, n ∈ S ↔ ∀ α : ℕ → ℕ, ∃ m : ℕ,
      R (n, List.ofFn (fun i : Fin m ↦ α i)) = true

/-- Kleene normal form characterization of `IsLightfacePi11`. -/
theorem isLightfacePi11_iff {S : Set ℕ} :
    IsLightfacePi11 S ↔
      ∃ R : ℕ × List ℕ → Bool, Computable R ∧
        ∀ n : ℕ, n ∈ S ↔ ∀ α : ℕ → ℕ, ∃ m : ℕ,
          R (n, List.ofFn (fun i : Fin m ↦ α i)) = true :=
  Iff.rfl

/-- Extensionality transfer for `IsLightfacePi11`. -/
theorem IsLightfacePi11.of_eq {S T : Set ℕ} (hS : IsLightfacePi11 S)
    (h : ∀ n : ℕ, n ∈ S ↔ n ∈ T) : IsLightfacePi11 T := by
  rcases hS with ⟨R, hR, hSR⟩
  exact ⟨R, hR, fun n ↦ (h n).symm.trans (hSR n)⟩

/-- Every computable subset of `ℕ` is lightface $\Pi^1_1$. -/
theorem IsLightfacePi11.of_computablePred {S : Set ℕ} (hS : ComputablePred (· ∈ S)) :
    IsLightfacePi11 S := by
  obtain ⟨f, hf, hEq⟩ := ComputablePred.computable_iff.mp hS
  refine ⟨fun p ↦ f p.1, hf.comp Computable.fst, fun n ↦ ?_⟩
  have hn : (n ∈ S) ↔ f n = true := Iff.of_eq (congrFun hEq n)
  rw [hn]
  exact ⟨fun h _ ↦ ⟨0, h⟩, fun h ↦ let ⟨_, hm⟩ := h (fun _ ↦ 0); hm⟩

/-- Lightface $\Pi^1_1$ sets are closed downward under many-one reducibility. -/
theorem IsLightfacePi11.of_manyOneReducible {A B : Set ℕ}
    (hred : ManyOneReducible (· ∈ A) (· ∈ B)) (hB : IsLightfacePi11 B) :
    IsLightfacePi11 A := by
  rcases hred with ⟨f, hf, hiff⟩
  rcases hB with ⟨R, hR, hBR⟩
  refine ⟨fun p ↦ R (f p.1, p.2), hR.comp ((hf.comp Computable.fst).pair Computable.snd),
    fun n ↦ (hiff n).trans (hBR (f n))⟩

private lemma take_ofFn {A : Type*} (α : ℕ → A) {k m : ℕ} (hkm : k ≤ m) :
    (List.ofFn (fun i : Fin m ↦ α i)).take k = List.ofFn (fun i : Fin k ↦ α i) :=
  List.ext_getElem (by simp [min_eq_left hkm]) fun i hi _ ↦ by
    have : i < k := by simpa [min_eq_left hkm] using hi
    simp

private lemma computable_exists_le_bool {α : Type*} [Primcodable α] {f : α × ℕ → Bool}
    (hf : Computable f) {b : α → ℕ} (hb : Computable b) :
    ∃ g : α → Bool, Computable g ∧ ∀ a : α, g a = true ↔ ∃ y ≤ b a, f (a, y) = true := by
  let g : α → Bool := fun a ↦ Nat.rec false (fun y acc ↦ acc || f (a, y)) (b a).succ
  have hstep : Computable fun x : α × (ℕ × Bool) ↦ x.2.2 || f (x.1, x.2.1) :=
    Primrec.or.to_comp.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)))
  have hmem (a : α) : ∀ m : ℕ,
      @Nat.rec (fun _ ↦ Bool) false (fun y acc ↦ acc || f (a, y)) m ∈
        @Nat.rec (fun _ ↦ Part Bool) ((fun _ : α ↦ false) a : Part Bool)
          (fun y IH ↦ IH.bind fun i ↦
            ((fun b : ℕ × Bool ↦ b.2 || f (a, b.1)) : ℕ × Bool →. Bool) (y, i)) m := by
    intro m
    induction m with
    | zero => exact Part.mem_some false
    | succ m ih => exact Part.mem_bind_iff.mpr ⟨_, ih, Part.mem_some _⟩
  have hg : Computable g :=
    (Partrec.nat_rec (Computable.succ.comp hb) (Computable.const false).partrec
      hstep.to₂.partrec₂).of_eq_tot fun a ↦ hmem a (b a).succ
  have hspec (a : α) : ∀ m : ℕ,
      Nat.rec false (fun y acc ↦ acc || f (a, y)) m = true ↔ ∃ y < m, f (a, y) = true := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      change (Nat.rec false (fun y acc ↦ acc || f (a, y)) m || f (a, m)) = true ↔
        ∃ y < m + 1, f (a, y) = true
      rw [Bool.or_eq_true, ih]
      refine ⟨fun h ↦ h.elim (fun ⟨y, hy, hfy⟩ ↦ ⟨y, Nat.lt_succ_of_lt hy, hfy⟩)
        (fun hfm ↦ ⟨m, Nat.lt_succ_self m, hfm⟩), ?_⟩
      rintro ⟨y, hy, hfy⟩
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hy) with hlt | rfl
      · exact Or.inl ⟨y, hlt, hfy⟩
      · exact Or.inr hfy
  refine ⟨g, hg, fun a ↦ ?_⟩
  dsimp only [g]
  rw [hspec a (b a).succ]
  simp only [Nat.succ_eq_add_one, Nat.lt_succ_iff]

/-- Lightface $\Pi^1_1$ sets are closed under binary intersection. -/
theorem IsLightfacePi11.inter {A B : Set ℕ} (hA : IsLightfacePi11 A)
    (hB : IsLightfacePi11 B) : IsLightfacePi11 (A ∩ B) := by
  rcases hA with ⟨RA, hRA, hA_iff⟩
  rcases hB with ⟨RB, hRB, hB_iff⟩
  have hTake (R : ℕ × List ℕ → Bool) (hR : Computable R) :
      ∃ g : ℕ × List ℕ → Bool, Computable g ∧
        ∀ p : ℕ × List ℕ, g p = true ↔ ∃ k ≤ p.2.length, R (p.1, p.2.take k) = true :=
    computable_exists_le_bool
      (hR.comp ((Computable.fst.comp Computable.fst).pair
        (Primrec.list_take.to_comp.comp Computable.snd (Computable.snd.comp Computable.fst))))
      (Computable.list_length.comp Computable.snd)
  obtain ⟨gA, hgA, hgA_iff⟩ := hTake RA hRA
  obtain ⟨gB, hgB, hgB_iff⟩ := hTake RB hRB
  refine ⟨fun p ↦ gA p && gB p, Primrec.and.to_comp.comp hgA hgB, fun n ↦ ?_⟩
  have hR_iff (u : List ℕ) : (gA (n, u) && gB (n, u)) = true ↔
      (∃ k₁ ≤ u.length, RA (n, u.take k₁) = true) ∧
      (∃ k₂ ≤ u.length, RB (n, u.take k₂) = true) := by
    rw [Bool.and_eq_true, hgA_iff (n, u), hgB_iff (n, u)]
  rw [Set.mem_inter_iff, hA_iff n, hB_iff n]
  refine ⟨fun ⟨hnA, hnB⟩ α ↦ ?_, fun h ↦ ⟨fun α ↦ ?_, fun α ↦ ?_⟩⟩
  · obtain ⟨m₁, hm₁⟩ := hnA α
    obtain ⟨m₂, hm₂⟩ := hnB α
    refine ⟨max m₁ m₂, (hR_iff _).mpr ⟨⟨m₁, by simp, ?_⟩, ⟨m₂, by simp, ?_⟩⟩⟩
    · simpa [take_ofFn α (le_max_left m₁ m₂)] using hm₁
    · simpa [take_ofFn α (le_max_right m₁ m₂)] using hm₂
  · obtain ⟨m, hm⟩ := h α
    obtain ⟨⟨k₁, hk₁, h₁⟩, -⟩ := (hR_iff _).mp hm
    exact ⟨k₁, by simpa [take_ofFn α (by simpa using hk₁)] using h₁⟩
  · obtain ⟨m, hm⟩ := h α
    obtain ⟨-, ⟨k₂, hk₂, h₂⟩⟩ := (hR_iff _).mp hm
    exact ⟨k₂, by simpa [take_ofFn α (by simpa using hk₂)] using h₂⟩

/-- Lightface $\Pi^1_1$ sets are closed under binary union. -/
theorem IsLightfacePi11.union {A B : Set ℕ} (hA : IsLightfacePi11 A)
    (hB : IsLightfacePi11 B) : IsLightfacePi11 (A ∪ B) := by
  rcases hA with ⟨RA, hRA, hA_iff⟩
  rcases hB with ⟨RB, hRB, hB_iff⟩
  have hPair (R : ℕ × List ℕ → Bool) (hR : Computable R) (proj : ℕ → ℕ) (hp : Primrec proj) :
      ∃ g : ℕ × List ℕ → Bool, Computable g ∧
        ∀ p : ℕ × List ℕ, g p = true ↔
          ∃ k ≤ p.2.length, R (p.1, (p.2.take k).map proj) = true :=
    computable_exists_le_bool
      (hR.comp ((Computable.fst.comp Computable.fst).pair
        ((Primrec.list_map Primrec.id (hp.comp Primrec.snd).to₂).to_comp.comp
          (Primrec.list_take.to_comp.comp Computable.snd (Computable.snd.comp Computable.fst)))))
      (Computable.list_length.comp Computable.snd)
  obtain ⟨g₁, hg₁, hg₁_iff⟩ := hPair RA hRA (fun z ↦ z.unpair.1) (Primrec.fst.comp Primrec.unpair)
  obtain ⟨g₂, hg₂, hg₂_iff⟩ := hPair RB hRB (fun z ↦ z.unpair.2) (Primrec.snd.comp Primrec.unpair)
  refine ⟨fun p ↦ g₁ p || g₂ p, Primrec.or.to_comp.comp hg₁ hg₂, fun n ↦ ?_⟩
  have hR_iff (u : List ℕ) : (g₁ (n, u) || g₂ (n, u)) = true ↔
      (∃ k ≤ u.length, RA (n, (u.take k).map (fun z ↦ z.unpair.1)) = true) ∨
      (∃ k ≤ u.length, RB (n, (u.take k).map (fun z ↦ z.unpair.2)) = true) := by
    rw [Bool.or_eq_true, hg₁_iff (n, u), hg₂_iff (n, u)]
  rw [Set.mem_union, hA_iff n, hB_iff n]
  constructor
  · rintro (hnA | hnB) γ
    · obtain ⟨m, hm⟩ := hnA (fun i ↦ (γ i).unpair.1)
      refine ⟨m, (hR_iff _).mpr (Or.inl ⟨m, by simp, ?_⟩)⟩
      simpa [take_ofFn γ le_rfl, List.map_ofFn, Function.comp_def] using hm
    · obtain ⟨m, hm⟩ := hnB (fun i ↦ (γ i).unpair.2)
      refine ⟨m, (hR_iff _).mpr (Or.inr ⟨m, by simp, ?_⟩)⟩
      simpa [take_ofFn γ le_rfl, List.map_ofFn, Function.comp_def] using hm
  · intro h
    by_contra hnot
    rcases not_or.mp hnot with ⟨hnotA, hnotB⟩
    simp only [not_forall, not_exists, Bool.not_eq_true] at hnotA hnotB
    obtain ⟨α, hα⟩ := hnotA
    obtain ⟨β, hβ⟩ := hnotB
    obtain ⟨m, hm⟩ := h (fun i ↦ Nat.pair (α i) (β i))
    rcases (hR_iff _).mp hm with ⟨k, hk, hkA⟩ | ⟨k, hk, hkB⟩
    · rw [take_ofFn (fun i ↦ Nat.pair (α i) (β i)) (by simpa using hk), List.map_ofFn] at hkA
      simp only [Function.comp_def, Nat.unpair_pair] at hkA
      exact Bool.false_ne_true ((hα k).symm.trans hkA)
    · rw [take_ofFn (fun i ↦ Nat.pair (α i) (β i)) (by simpa using hk), List.map_ofFn] at hkB
      simp only [Function.comp_def, Nat.unpair_pair] at hkB
      exact Bool.false_ne_true ((hβ k).symm.trans hkB)

/-- A subset `S : Set ℕ` is lightface $\Sigma^1_1$ (effectively analytic) if there exists a
computable Boolean predicate `R` on finite sequence prefixes such that `n ∈ S` holds iff some
infinite branch `α : ℕ → ℕ` has every finite prefix accepted by `R`. -/
def IsLightfaceSigma11 (S : Set ℕ) : Prop :=
  ∃ R : ℕ × List ℕ → Bool, Computable R ∧
    ∀ n : ℕ, n ∈ S ↔ ∃ α : ℕ → ℕ, ∀ m : ℕ,
      R (n, List.ofFn (fun i : Fin m ↦ α i)) = true

/-- Complementation duality: `Sᶜ` is lightface $\Sigma^1_1$ iff `S` is lightface $\Pi^1_1$. -/
theorem isLightfaceSigma11_compl_iff {S : Set ℕ} :
    IsLightfaceSigma11 Sᶜ ↔ IsLightfacePi11 S := by
  constructor
  · rintro ⟨R, hR, hiff⟩
    refine ⟨fun p ↦ !R p, Primrec.not.to_comp.comp hR, fun n ↦ ?_⟩
    have hn := (hiff n).not
    simp only [Set.mem_compl_iff, Classical.not_not, not_exists, not_forall,
      Bool.not_eq_true] at hn
    simpa only [Bool.not_eq_true'] using hn
  · rintro ⟨R, hR, hiff⟩
    refine ⟨fun p ↦ !R p, Primrec.not.to_comp.comp hR, fun n ↦ ?_⟩
    rw [Set.mem_compl_iff, hiff n]
    simp only [not_forall, not_exists, Bool.not_eq_true, Bool.not_eq_true']

/-- Complementation duality: `Sᶜ` is lightface $\Pi^1_1$ iff `S` is lightface $\Sigma^1_1$. -/
theorem isLightfacePi11_compl_iff {S : Set ℕ} :
    IsLightfacePi11 Sᶜ ↔ IsLightfaceSigma11 S := by
  rw [← isLightfaceSigma11_compl_iff, compl_compl]

/-- Lightface $\Sigma^1_1$ sets are closed downward under many-one reducibility. -/
theorem IsLightfaceSigma11.of_manyOneReducible {A B : Set ℕ}
    (hred : ManyOneReducible (· ∈ A) (· ∈ B)) (hB : IsLightfaceSigma11 B) :
    IsLightfaceSigma11 A := by
  rcases hred with ⟨f, hf, hiff⟩
  have hred_compl : ManyOneReducible (· ∈ Aᶜ) (· ∈ Bᶜ) :=
    ⟨f, hf, fun n ↦ not_congr (hiff n)⟩
  rw [← isLightfacePi11_compl_iff] at hB ⊢
  exact hB.of_manyOneReducible hred_compl

/-- A subset `A : Set ℕ` is $\Pi^1_1$-hard if every lightface $\Pi^1_1$ subset `B : Set ℕ` is
many-one reducible to `A`. -/
def IsPi11Hard (A : Set ℕ) : Prop :=
  ∀ B : Set ℕ, IsLightfacePi11 B → ManyOneReducible (· ∈ B) (· ∈ A)

/-- $\Pi^1_1$-hardness transfers upward along many-one reductions. -/
theorem IsPi11Hard.of_manyOneReducible {A C : Set ℕ}
    (hred : ManyOneReducible (· ∈ A) (· ∈ C)) (hA : IsPi11Hard A) : IsPi11Hard C :=
  fun B hB ↦ (hA B hB).trans hred

/-- A subset `A : Set ℕ` is $\Pi^1_1$-complete if it is both lightface $\Pi^1_1$ and
$\Pi^1_1$-hard. -/
def IsPi11Complete (A : Set ℕ) : Prop :=
  IsLightfacePi11 A ∧ IsPi11Hard A

/-- Transfer of $\Pi^1_1$-completeness along many-one reductions into a $\Pi^1_1$ set. -/
theorem IsPi11Complete.of_manyOneReducible {A C : Set ℕ}
    (hred : ManyOneReducible (· ∈ A) (· ∈ C)) (hA : IsPi11Complete A)
    (hC : IsLightfacePi11 C) : IsPi11Complete C :=
  ⟨hC, hA.2.of_manyOneReducible hred⟩

/-- A subset `A : Set ℕ` is $\Sigma^1_1$-hard if every lightface $\Sigma^1_1$ subset `B : Set ℕ`
is many-one reducible to `A`. -/
def IsSigma11Hard (A : Set ℕ) : Prop :=
  ∀ B : Set ℕ, IsLightfaceSigma11 B → ManyOneReducible (· ∈ B) (· ∈ A)

/-- A subset `A : Set ℕ` is $\Sigma^1_1$-complete if it is both lightface $\Sigma^1_1$ and
$\Sigma^1_1$-hard. -/
def IsSigma11Complete (A : Set ℕ) : Prop :=
  IsLightfaceSigma11 A ∧ IsSigma11Hard A

/-- Complementation duality between $\Sigma^1_1$-hardness and $\Pi^1_1$-hardness. -/
theorem isSigma11Hard_compl_iff {A : Set ℕ} :
    IsSigma11Hard Aᶜ ↔ IsPi11Hard A := by
  constructor
  · intro h B hB
    obtain ⟨f, hf, hiff⟩ := h Bᶜ (isLightfaceSigma11_compl_iff.mpr hB)
    exact ⟨f, hf, fun n ↦
      ⟨fun hnB ↦ Classical.byContradiction fun hnA ↦ (hiff n).mpr hnA hnB,
       fun hnA ↦ Classical.byContradiction fun hnB ↦ (hiff n).mp hnB hnA⟩⟩
  · intro h B hB
    obtain ⟨f, hf, hiff⟩ := h Bᶜ (isLightfacePi11_compl_iff.mpr hB)
    exact ⟨f, hf, fun n ↦ ⟨fun hnB hnA ↦ (hiff n).mpr hnA hnB,
      fun hnA ↦ Classical.byContradiction fun hnB ↦ hnA ((hiff n).mp hnB)⟩⟩

/-- Complementation duality between $\Sigma^1_1$-completeness and $\Pi^1_1$-completeness. -/
theorem isSigma11Complete_compl_iff {A : Set ℕ} :
    IsSigma11Complete Aᶜ ↔ IsPi11Complete A :=
  and_congr isLightfaceSigma11_compl_iff isSigma11Hard_compl_iff

end CslibFrontier.Computability.Complexity.Classes
