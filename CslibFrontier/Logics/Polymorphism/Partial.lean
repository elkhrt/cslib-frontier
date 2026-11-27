/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.Polymorphism
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Finite.Basic

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# Relational Partial Polymorphisms and Pöschel's Galois Connection

This module formalizes finite-domain partial and total polymorphisms, quantifier-free and
existential primitive-positive definability, and Pöschel's Galois connection characterizing
qfpp-definability via partial polymorphisms and pp-definability via total polymorphisms.

## Main definitions

* `Cslib.Logic.IsPartialPolymorphism`: preservation of a relation by a partial operation.
* `Cslib.Logic.PolSubset`, `Cslib.Logic.PPolSubset`: inclusion of positive-arity total and
  partial polymorphism sets.
* `Cslib.Logic.IsQFPPDefinable`, `Cslib.Logic.IsPPDefinable`: quantifier-free and existential
  primitive-positive definability using relation atoms and equality atoms.

## Main results

* `Cslib.Logic.poschel_galois_qfpp`, `Cslib.Logic.poschel_galois_pp`: Pöschel's Galois
  connection characterizing qfpp-definability via partial polymorphisms and pp-definability via
  total polymorphisms (under the sharp condition that the target relation is nonempty or the
  source relation contains no constant tuple).
-/

public section

namespace Cslib.Logic

variable {D I J : Type*}

/-- A partial operation `f : (J → D) → Option D` preserves a relation `R : Set (I → D)` when for
every family of tuples `a j ∈ R`, if `f` is defined on every coordinate row `fun j => a j i` with
value `out i`, then `out ∈ R`. -/
@[expose] def IsPartialPolymorphism (f : (J → D) → Option D) (R : Set (I → D)) : Prop :=
  ∀ (a : J → I → D), (∀ j, a j ∈ R) →
    ∀ (out : I → D), (∀ i, f (fun j => a j i) = some (out i)) → out ∈ R

/-- A total operation preserves `R` iff its lift `some ∘ f` is a partial polymorphism of `R`. -/
@[simp]
theorem isPartialPolymorphism_some_iff (f : (J → D) → D) (R : Set (I → D)) :
    IsPartialPolymorphism (fun x => some (f x)) R ↔ IsPolymorphism f R := by
  constructor
  · intro h a ha
    exact h a ha (fun i => f (fun j => a j i)) (fun _ => rfl)
  · intro h a ha out hout
    have hEq : out = fun i => f (fun j => a j i) := by
      funext i
      exact (Option.some.inj (hout i)).symm
    rw [hEq]
    exact h a ha

/-- Inclusion of positive-arity total polymorphism sets: `Pol(R) ⊆ Pol(R')`. -/
@[expose] def PolSubset {n n' : ℕ} (R : Set (Fin n → D)) (R' : Set (Fin n' → D)) : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (f : (Fin m → D) → D),
    IsPolymorphism f R → IsPolymorphism f R'

/-- Inclusion of positive-arity partial polymorphism sets: `pPol(R) ⊆ pPol(R')`. -/
@[expose] def PPolSubset {n n' : ℕ} (R : Set (Fin n → D)) (R' : Set (Fin n' → D)) : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (f : (Fin m → D) → Option D),
    IsPartialPolymorphism f R → IsPartialPolymorphism f R'

/-- Inclusion of partial polymorphisms implies inclusion of total polymorphisms. -/
theorem PPolSubset.polSubset {n n' : ℕ} {R : Set (Fin n → D)} {R' : Set (Fin n' → D)}
    (h : PPolSubset R R') : PolSubset R R' := by
  intro m hm f hf
  exact (isPartialPolymorphism_some_iff f R').mp
    (h m hm (fun x => some (f x)) ((isPartialPolymorphism_some_iff f R).mpr hf))

@[simp]
theorem PolSubset.refl {n : ℕ} (R : Set (Fin n → D)) : PolSubset R R :=
  fun _ _ _ h => h

theorem PolSubset.trans {n₁ n₂ n₃ : ℕ} {R₁ : Set (Fin n₁ → D)} {R₂ : Set (Fin n₂ → D)}
    {R₃ : Set (Fin n₃ → D)} (h₁₂ : PolSubset R₁ R₂) (h₂₃ : PolSubset R₂ R₃) : PolSubset R₁ R₃ :=
  fun m hm f hf => h₂₃ m hm f (h₁₂ m hm f hf)

@[simp]
theorem PPolSubset.refl {n : ℕ} (R : Set (Fin n → D)) : PPolSubset R R :=
  fun _ _ _ h => h

theorem PPolSubset.trans {n₁ n₂ n₃ : ℕ} {R₁ : Set (Fin n₁ → D)} {R₂ : Set (Fin n₂ → D)}
    {R₃ : Set (Fin n₃ → D)} (h₁₂ : PPolSubset R₁ R₂) (h₂₃ : PPolSubset R₂ R₃) :
    PPolSubset R₁ R₃ :=
  fun m hm f hf => h₂₃ m hm f (h₁₂ m hm f hf)

/-- Quantifier-free primitive-positive definability: `R'` is defined by a finite conjunction of
`R`-atoms and equality atoms over its free variables. -/
@[expose] def IsQFPPDefinable {n n' : ℕ} (R : Set (Fin n → D)) (R' : Set (Fin n' → D)) : Prop :=
  ∃ (atoms : List (Fin n → Fin n')) (eqs : List (Fin n' × Fin n')),
    ∀ t : Fin n' → D, t ∈ R' ↔ (∀ α ∈ atoms, t ∘ α ∈ R) ∧ (∀ p ∈ eqs, t p.1 = t p.2)

/-- Primitive-positive definability: `R'` is defined by existentially quantifying `q` auxiliary
variables over a finite conjunction of `R`-atoms and equality atoms. -/
@[expose] def IsPPDefinable {n n' : ℕ} (R : Set (Fin n → D)) (R' : Set (Fin n' → D)) : Prop :=
  ∃ (q : ℕ) (atoms : List (Fin n → Fin (n' + q))) (eqs : List (Fin (n' + q) × Fin (n' + q))),
    ∀ t : Fin n' → D, t ∈ R' ↔
      ∃ e : Fin q → D,
        (∀ α ∈ atoms, Fin.append t e ∘ α ∈ R) ∧ (∀ p ∈ eqs, Fin.append t e p.1 = Fin.append t e p.2)

/-- Every qfpp-definable relation is pp-definable. -/
theorem IsQFPPDefinable.isPPDefinable {n n' : ℕ} {R : Set (Fin n → D)} {R' : Set (Fin n' → D)}
    (h : IsQFPPDefinable R R') : IsPPDefinable R R' := by
  rcases h with ⟨atoms, eqs, hdef⟩
  refine ⟨0, atoms.map (fun α i => Fin.castAdd 0 (α i)),
    eqs.map (fun p => (Fin.castAdd 0 p.1, Fin.castAdd 0 p.2)), fun t => ?_⟩
  rw [hdef]
  constructor
  · rintro ⟨ha, he⟩
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro α hα
      rcases List.mem_map.mp hα with ⟨α₀, hα₀, rfl⟩
      simpa [Function.comp_def] using ha α₀ hα₀
    · intro p hp
      rcases List.mem_map.mp hp with ⟨p₀, hp₀, rfl⟩
      simpa using he p₀ hp₀
  · rintro ⟨e, ha, he⟩
    refine ⟨fun α hα => ?_, fun p hp => ?_⟩
    · have := ha (fun i => Fin.castAdd 0 (α i)) (List.mem_map.mpr ⟨α, hα, rfl⟩)
      have hEq : Fin.append t e ∘ (fun i => Fin.castAdd 0 (α i)) = t ∘ α := by
        funext i
        exact Fin.append_left t e (α i)
      rwa [hEq] at this
    · have := he (Fin.castAdd 0 p.1, Fin.castAdd 0 p.2) (List.mem_map.mpr ⟨p, hp, rfl⟩)
      simpa only [Fin.append_left] using this

/-- Every qfpp-definable relation is preserved by every partial polymorphism of `R`. -/
theorem IsQFPPDefinable.ppolSubset {n n' : ℕ} {R : Set (Fin n → D)} {R' : Set (Fin n' → D)}
    (h : IsQFPPDefinable R R') : PPolSubset R R' := by
  rcases h with ⟨atoms, eqs, hdef⟩
  intro m _ f hf a ha out hout
  rw [hdef]
  constructor
  · intro α hα
    exact hf (fun j => a j ∘ α) (fun j => ((hdef (a j)).mp (ha j)).1 α hα)
      (out ∘ α) (fun i => hout (α i))
  · intro p hp
    have h1 := hout p.1
    have h2 := hout p.2
    have hrow : (fun j => a j p.1) = (fun j => a j p.2) := by
      funext j
      exact ((hdef (a j)).mp (ha j)).2 p hp
    rw [hrow, h2] at h1
    exact (Option.some.inj h1).symm

/-- Every pp-definable relation is preserved by every total polymorphism of `R`. -/
theorem IsPPDefinable.polSubset {n n' : ℕ} {R : Set (Fin n → D)} {R' : Set (Fin n' → D)}
    (h : IsPPDefinable R R') : PolSubset R R' := by
  rcases h with ⟨q, atoms, eqs, hdef⟩
  intro m _ f hf a ha
  rw [hdef]
  have hex : ∀ j : Fin m, ∃ e : Fin q → D,
      (∀ α ∈ atoms, Fin.append (a j) e ∘ α ∈ R) ∧
      (∀ p ∈ eqs, Fin.append (a j) e p.1 = Fin.append (a j) e p.2) :=
    fun j => (hdef (a j)).mp (ha j)
  choose e he using hex
  refine ⟨fun k => f (fun j => e j k), ?_, ?_⟩
  · intro α hα
    have hmem : ∀ j, Fin.append (a j) (e j) ∘ α ∈ R := fun j => (he j).1 α hα
    have hres := hf (fun j => Fin.append (a j) (e j) ∘ α) hmem
    have hEq : Fin.append (fun i => f (fun j => a j i)) (fun k => f (fun j => e j k)) ∘ α =
        (fun i => f (fun j => (Fin.append (a j) (e j) ∘ α) i)) := by
      funext i
      simp only [Function.comp_apply]
      refine Fin.addCases (fun i₀ => ?_) (fun k₀ => ?_) (α i) <;>
        simp [Fin.append_left, Fin.append_right]
    rw [hEq]
    exact hres
  · intro p hp
    have hrow :
        (fun j => Fin.append (a j) (e j) p.1) = (fun j => Fin.append (a j) (e j) p.2) := by
      funext j
      exact (he j).2 p hp
    have hval : ∀ u : Fin (n' + q),
        Fin.append (fun i => f (fun j => a j i)) (fun k => f (fun j => e j k)) u =
          f (fun j => Fin.append (a j) (e j) u) := by
      intro u
      refine Fin.addCases (fun i₀ => ?_) (fun k₀ => ?_) u <;>
        simp [Fin.append_left, Fin.append_right]
    rw [hval, hval, hrow]

/-- **Pöschel's Galois connection (qfpp / partial polymorphisms)**: on a finite domain, if `R'` is
nonempty, or `0 < n'` and `R` contains no constant tuple, then `pPol(R) ⊆ pPol(R')` iff `R'` is
qfpp-definable from `R`. -/
theorem poschel_galois_qfpp [Finite D] {n n' : ℕ}
    {R : Set (Fin n → D)} {R' : Set (Fin n' → D)}
    (hguard : R'.Nonempty ∨ (0 < n' ∧ ∀ a : D, (fun _ => a) ∉ R)) :
    PPolSubset R R' ↔ IsQFPPDefinable R R' := by
  have : Fintype D := Fintype.ofFinite D
  classical
  refine ⟨fun hppol => ?_, IsQFPPDefinable.ppolSubset⟩
  by_cases hne : R'.Nonempty
  · let M : List (Fin n' → D) := (Set.toFinite R').toFinset.toList
    have hM_mem : ∀ t, t ∈ M ↔ t ∈ R' := by intro t; simp [M]
    have hM_pos : 0 < M.length := by
      rcases hne with ⟨t, ht⟩
      exact List.length_pos_of_mem ((hM_mem t).mpr ht)
    let row : Fin n' → (Fin M.length → D) := fun i j => M[j] i
    let atoms : List (Fin n → Fin n') :=
      (Finset.univ : Finset (Fin n → Fin n')).toList.filter fun α =>
        decide (∀ j : Fin M.length, M[j] ∘ α ∈ R)
    let eqs : List (Fin n' × Fin n') :=
      (Finset.univ : Finset (Fin n' × Fin n')).toList.filter fun p =>
        decide (row p.1 = row p.2)
    refine ⟨atoms, eqs, fun t => ?_⟩
    constructor
    · intro ht
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((hM_mem t).mpr ht)
      have hj' : M[j] = t := by simpa using hj
      subst hj'
      refine ⟨fun α hα => ?_, fun p hp => ?_⟩
      · have hα' : ∀ j' : Fin M.length, M[j'] ∘ α ∈ R := by simpa [atoms] using hα
        exact hα' j
      · have hp' : row p.1 = row p.2 := by simpa [eqs] using hp
        exact congrFun hp' j
    · rintro ⟨ha, he⟩
      let f : (Fin M.length → D) → Option D := fun x =>
        if h : ∃ i : Fin n', row i = x then some (t h.choose) else none
      have hf_row : ∀ i : Fin n', f (row i) = some (t i) := by
        intro i
        have hex : ∃ i' : Fin n', row i' = row i := ⟨i, rfl⟩
        simp only [f, hex, ↓reduceDIte]
        congr 1
        have hreq : row hex.choose = row i := hex.choose_spec
        have hmem : (hex.choose, i) ∈ eqs := by simp [eqs, hreq]
        exact he (hex.choose, i) hmem
      have hfR : IsPartialPolymorphism f R := by
        intro a haR out hout
        have hex : ∀ k : Fin n, ∃ i : Fin n', row i = (fun j => a j k) := by
          intro k
          have hk := hout k
          by_contra hno
          simp [f, hno] at hk
        choose α hα using hex
        have hα_mem : α ∈ atoms := by
          simp only [atoms, List.mem_filter, Finset.mem_toList, Finset.mem_univ, true_and,
            decide_eq_true_eq]
          intro j
          have hEq : M[j] ∘ α = a j := by funext k; exact congrFun (hα k) j
          rw [hEq]
          exact haR j
        have hout_eq : out = t ∘ α := by
          funext k
          have h1 := hout k
          rw [← hα k, hf_row (α k)] at h1
          exact (Option.some.inj h1).symm
        rw [hout_eq]
        exact ha α hα_mem
      have hfR' := hppol M.length hM_pos f hfR
      exact hfR' (fun j => M[j]) (fun j => (hM_mem M[j]).mp (List.get_mem M j)) t hf_row
  · rcases hguard with hne' | ⟨hn', hnoconst⟩
    · exact (hne hne').elim
    · have hEmpty : R' = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      subst hEmpty
      refine ⟨[fun _ => ⟨0, hn'⟩], [], fun t => ?_⟩
      simp only [Set.mem_empty_iff_false, List.mem_singleton, forall_eq, List.not_mem_nil,
        IsEmpty.forall_iff, imp_true_iff, and_true, false_iff]
      intro hmem
      exact hnoconst (t ⟨0, hn'⟩) hmem

/-- **Pöschel's Galois connection (pp / total polymorphisms)**: on a finite domain, if `R'` is
nonempty or `R` contains no constant tuple, then `Pol(R) ⊆ Pol(R')` iff `R'` is pp-definable
from `R`. -/
theorem poschel_galois_pp [Finite D] {n n' : ℕ}
    {R : Set (Fin n → D)} {R' : Set (Fin n' → D)}
    (hguard : R'.Nonempty ∨ ∀ a : D, (fun _ => a) ∉ R) :
    PolSubset R R' ↔ IsPPDefinable R R' := by
  have : Fintype D := Fintype.ofFinite D
  classical
  refine ⟨fun hpol => ?_, IsPPDefinable.polSubset⟩
  by_cases hne : R'.Nonempty
  · let M : List (Fin n' → D) := (Set.toFinite R').toFinset.toList
    have hM_mem : ∀ t, t ∈ M ↔ t ∈ R' := by intro t; simp [M]
    have hM_pos : 0 < M.length := by
      rcases hne with ⟨t, ht⟩
      exact List.length_pos_of_mem ((hM_mem t).mpr ht)
    let q : ℕ := Fintype.card (Fin M.length → D)
    let e : Fin q ≃ (Fin M.length → D) := Fintype.equivFinOfCardEq rfl |>.symm
    let row : Fin n' → (Fin M.length → D) := fun i j => M[j] i
    let r : Fin (n' + q) → (Fin M.length → D) := Fin.append row (fun k => e k)
    let atoms : List (Fin n → Fin (n' + q)) :=
      (Finset.univ : Finset (Fin n → Fin (n' + q))).toList.filter fun α =>
        decide (∀ j : Fin M.length, (fun i => r (α i) j) ∈ R)
    let eqs : List (Fin (n' + q) × Fin (n' + q)) :=
      (Finset.univ : Finset (Fin (n' + q) × Fin (n' + q))).toList.filter fun p =>
        decide (r p.1 = r p.2)
    refine ⟨q, atoms, eqs, fun t => ?_⟩
    constructor
    · intro ht
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((hM_mem t).mpr ht)
      have hj' : M[j] = t := by simpa using hj
      subst hj'
      refine ⟨fun k => e k j, fun α hα => ?_, fun p hp => ?_⟩
      · have hα' : ∀ j' : Fin M.length, (fun i => r (α i) j') ∈ R := by simpa [atoms] using hα
        have hEq : Fin.append (M[j]) (fun k => e k j) ∘ α = (fun i => r (α i) j) := by
          funext i
          simp only [Function.comp_apply, r]
          refine Fin.addCases (fun i₀ => ?_) (fun k₀ => ?_) (α i) <;>
            simp [Fin.append_left, Fin.append_right, row]
        rw [hEq]
        exact hα' j
      · have hp' : r p.1 = r p.2 := by simpa [eqs] using hp
        have hval : ∀ u : Fin (n' + q), Fin.append (M[j]) (fun k => e k j) u = r u j := by
          intro u
          refine Fin.addCases (fun i₀ => ?_) (fun k₀ => ?_) u <;>
            simp [r, row, Fin.append_left, Fin.append_right]
        rw [hval, hval, hp']
    · rintro ⟨ext, ha, he⟩
      let f : (Fin M.length → D) → D := fun x => ext (e.symm x)
      have hf_row : ∀ i : Fin n', f (row i) = t i := by
        intro i
        have hreq : r (Fin.castAdd q i) = r (Fin.natAdd n' (e.symm (row i))) := by
          simp [r, Fin.append_left, Fin.append_right]
        have hmem : (Fin.castAdd q i, Fin.natAdd n' (e.symm (row i))) ∈ eqs := by
          simp [eqs, hreq]
        have hEq := he _ hmem
        simpa [f, Fin.append_left, Fin.append_right] using hEq.symm
      have hfR : IsPolymorphism f R := by
        intro a haR
        let α : Fin n → Fin (n' + q) := fun k => Fin.natAdd n' (e.symm (fun j => a j k))
        have hα_mem : α ∈ atoms := by
          simp only [atoms, List.mem_filter, Finset.mem_toList, Finset.mem_univ, true_and,
            decide_eq_true_eq]
          intro j
          have hEq : (fun k => r (α k) j) = a j := by
            funext k; simp [α, r, Fin.append_right]
          rw [hEq]
          exact haR j
        have hEq : (fun k => f (fun j => a j k)) = Fin.append t ext ∘ α := by
          funext k; simp [f, α, Fin.append_right]
        rw [hEq]
        exact ha α hα_mem
      have hfR' := hpol M.length hM_pos f hfR (fun j => M[j])
        (fun j => (hM_mem M[j]).mp (List.get_mem M j))
      have hEq : t = fun i => f (row i) := by funext i; exact (hf_row i).symm
      rw [hEq]
      exact hfR'
  · rcases hguard with hne' | hnoconst
    · exact (hne hne').elim
    · have hEmpty : R' = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      subst hEmpty
      refine ⟨1, [fun _ => Fin.natAdd n' 0], [], fun t => ?_⟩
      simp only [Set.mem_empty_iff_false, List.mem_singleton, forall_eq, List.not_mem_nil,
        IsEmpty.forall_iff, imp_true_iff, and_true, false_iff, not_exists]
      intro e hmem
      have hEq : Fin.append t e ∘ (fun _ : Fin n => Fin.natAdd n' 0) = fun _ => e 0 := by
        funext i; simp [Fin.append_right]
      rw [hEq] at hmem
      exact hnoconst (e 0) hmem

end Cslib.Logic
