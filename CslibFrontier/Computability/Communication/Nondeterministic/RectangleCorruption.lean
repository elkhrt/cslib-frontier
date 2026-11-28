module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Probability.ProbabilityMassFunction.Basic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Entropy-Based Rectangle Corruption for Nonnegative Rank-1 Functions

For `n ≡ 3 (mod 4)` and `ℓ = (n + 1) / 4`, let `A` be the set of disjoint pairs of `ℓ`-subsets of
`Fin n` and `B` the set of pairs of `ℓ`-subsets meeting in exactly one element. For nonnegative
functions `f, g : Finset (Fin n) → ℝ` and `0 < ε`, this module proves an entropy-based rectangle
corruption inequality relating the average of `f(a) * g(b)` over `A` and over `B`:
```
  (1 - ε) * avgOn A (f · g) - avgOn B (f · g)
    ≤ maxOn (A ∪ B) (f · g) * (2 * (2 * ℓ + 1)) * 2 ^ (-(ε ^ 2 / (16 * log 2)) * ℓ).
```

## Main definitions

* `CslibFrontier.Communication.Nondeterministic.disjointPairs`, `uniqueInterPairs`: disjoint and
  unique-intersection pairs of `ℓ`-subsets of `Fin n`.
* `CslibFrontier.Communication.Nondeterministic.avgOn`, `condExpectPMF`, `maxOn`,
  `IsRazborovDist`: uniform averages, conditional expectations, and distributions uniform on `A`
  and on `B`.

## Main results

* `razborov_corruption_explicit`: explicit finite-`ℓ` corruption inequality for all `ℓ ≥ 1`.
* `razborov_corruption_lemma`: asymptotic corruption inequality for any `IsRazborovDist` (`ℓ ≥ 2`).
-/

public section

namespace CslibFrontier.Communication.Nondeterministic

open Finset
open scoped NNReal ENNReal

/-! ### Sets `A`, `B`, uniform averages, and distributions `μ` -/

section BasicDefs

/-- The set `A` of disjoint pairs `(a, b)` of `ℓ`-element subsets of `Fin n`. -/
def disjointPairs (n ℓ : ℕ) : Finset (Finset (Fin n) × Finset (Fin n)) :=
  (powersetCard ℓ (univ : Finset (Fin n)) ×ˢ powersetCard ℓ (univ : Finset (Fin n))).filter
    fun p => Disjoint p.1 p.2

/-- The set `B` of barely intersecting pairs `(a, b)` of `ℓ`-element subsets of `Fin n`
(`|a ∩ b| = 1`). -/
def uniqueInterPairs (n ℓ : ℕ) : Finset (Finset (Fin n) × Finset (Fin n)) :=
  (powersetCard ℓ (univ : Finset (Fin n)) ×ˢ powersetCard ℓ (univ : Finset (Fin n))).filter
    fun p => (p.1 ∩ p.2).card = 1

/-- Uniform average of a real-valued function over a finite set `S`. -/
noncomputable def avgOn {α : Type*} (S : Finset α) (X : α → ℝ) : ℝ :=
  (∑ x ∈ S, X x) / (S.card : ℝ)

/-- Linearity of `avgOn` under finite sums. -/
theorem sum_avgOn {α β : Type*} (t : Finset β) (S : Finset α) (F : β → α → ℝ) :
    ∑ k ∈ t, avgOn S (F k) = avgOn S (fun x => ∑ k ∈ t, F k x) := by
  simp only [avgOn, ← sum_div]
  rw [sum_comm]

/-- `avgOn` of a constant function over a nonempty set equals the constant. -/
theorem avgOn_const {α : Type*} {S : Finset α} (hS : S.Nonempty) (c : ℝ) :
    avgOn S (fun _ => c) = c := by
  have hne : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  simp only [avgOn, sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hne]

/-- Congruence for `avgOn`. -/
theorem avgOn_congr {α : Type*} {S : Finset α} {X Y : α → ℝ} (h : ∀ x ∈ S, X x = Y x) :
    avgOn S X = avgOn S Y := by
  simp only [avgOn, sum_congr rfl h]

/-- Conditional expectation `E_μ[X | S]` of `X` given a finite event `S` under a `PMF` `μ`. -/
noncomputable def condExpectPMF {α : Type*} (μ : PMF α) (S : Finset α) (X : α → ℝ) : ℝ :=
  (∑ x ∈ S, (μ x).toReal * X x) / (∑ x ∈ S, (μ x).toReal)

/-- A probability distribution `μ` on pairs of subsets of `Fin n` supported on `A ∪ B`, assigning
positive probability to both `A` and `B`, and uniform when conditioned on `A` or on `B`
. -/
def IsRazborovDist (n ℓ : ℕ) (μ : PMF (Finset (Fin n) × Finset (Fin n))) : Prop :=
  (∀ p, μ p ≠ 0 → p ∈ disjointPairs n ℓ ∪ uniqueInterPairs n ℓ) ∧
    (0 < ∑ p ∈ disjointPairs n ℓ, (μ p).toReal) ∧
    (0 < ∑ p ∈ uniqueInterPairs n ℓ, (μ p).toReal) ∧
    (∀ p ∈ disjointPairs n ℓ, ∀ q ∈ disjointPairs n ℓ, μ p = μ q) ∧
    (∀ p ∈ uniqueInterPairs n ℓ, ∀ q ∈ uniqueInterPairs n ℓ, μ p = μ q)

/-- Characterization of `IsRazborovDist` without unfolding across modules. -/
theorem isRazborovDist_iff {n ℓ : ℕ} {μ : PMF (Finset (Fin n) × Finset (Fin n))} :
    IsRazborovDist n ℓ μ ↔
      (∀ p, μ p ≠ 0 → p ∈ disjointPairs n ℓ ∪ uniqueInterPairs n ℓ) ∧
        (0 < ∑ p ∈ disjointPairs n ℓ, (μ p).toReal) ∧
        (0 < ∑ p ∈ uniqueInterPairs n ℓ, (μ p).toReal) ∧
        (∀ p ∈ disjointPairs n ℓ, ∀ q ∈ disjointPairs n ℓ, μ p = μ q) ∧
        (∀ p ∈ uniqueInterPairs n ℓ, ∀ q ∈ uniqueInterPairs n ℓ, μ p = μ q) :=
  Iff.rfl

/-- Maximum value of a nonnegative function `X` on a finite set `S` (`0` if `S` is empty). -/
noncomputable def maxOn {α : Type*} (S : Finset α) (X : α → ℝ) : ℝ :=
  if h : S.Nonempty then S.sup' h X else 0

theorem le_maxOn {α : Type*} {S : Finset α} {X : α → ℝ} {x : α} (hx : x ∈ S) :
    X x ≤ maxOn S X := by
  have hne : S.Nonempty := ⟨x, hx⟩
  simp only [maxOn, hne, ↓reduceDIte]
  exact Finset.le_sup' X hx

theorem maxOn_nonneg {α : Type*} {S : Finset α} {X : α → ℝ} (hX : ∀ x ∈ S, 0 ≤ X x) :
    0 ≤ maxOn S X := by
  by_cases hne : S.Nonempty
  · obtain ⟨x, hx⟩ := hne
    exact (hX x hx).trans (le_maxOn hx)
  · simp [maxOn, hne]

theorem maxOn_le_of_forall_le {α : Type*} {S : Finset α} {X : α → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x ∈ S, X x ≤ M) : maxOn S X ≤ M := by
  by_cases hne : S.Nonempty
  · simp only [maxOn, hne, ↓reduceDIte]
    exact Finset.sup'_le hne X h
  · simpa [maxOn, hne] using hM

/-- When `μ` assigns equal mass to every element of `S` and positive total mass to `S`,
`condExpectPMF μ S X` equals the uniform average `avgOn S X`. -/
theorem condExpectPMF_eq_avgOn {α : Type*} {μ : PMF α} {S : Finset α} (X : α → ℝ)
    (hpos : 0 < ∑ x ∈ S, (μ x).toReal) (hunif : ∀ x ∈ S, ∀ y ∈ S, μ x = μ y) :
    condExpectPMF μ S X = avgOn S X := by
  have hne : S.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    simp [hempty] at hpos
  obtain ⟨x₀, hx₀⟩ := hne
  set c : ℝ := (μ x₀).toReal
  have hsum_eq : ∑ x ∈ S, (μ x).toReal = (S.card : ℝ) * c := by
    calc ∑ x ∈ S, (μ x).toReal = ∑ _x ∈ S, c :=
          sum_congr rfl fun x hx => congrArg ENNReal.toReal (hunif x hx x₀ hx₀)
      _ = (S.card : ℝ) * c := by rw [sum_const, nsmul_eq_mul]
  have hc_ne : c ≠ 0 := by
    intro hc0
    rw [hc0, mul_zero] at hsum_eq
    linarith
  have hnum : ∑ x ∈ S, (μ x).toReal * X x = c * ∑ x ∈ S, X x := by
    rw [mul_sum]
    exact sum_congr rfl fun x hx => by rw [hunif x hx x₀ hx₀]
  rw [condExpectPMF, avgOn, hnum, hsum_eq]
  field_simp

theorem mem_disjointPairs_iff {n ℓ : ℕ} {p : Finset (Fin n) × Finset (Fin n)} :
    p ∈ disjointPairs n ℓ ↔ p.1.card = ℓ ∧ p.2.card = ℓ ∧ Disjoint p.1 p.2 := by
  simp only [disjointPairs, mem_filter, mem_product, mem_powersetCard, subset_univ, true_and,
    and_assoc]

theorem mem_uniqueInterPairs_iff {n ℓ : ℕ} {p : Finset (Fin n) × Finset (Fin n)} :
    p ∈ uniqueInterPairs n ℓ ↔ p.1.card = ℓ ∧ p.2.card = ℓ ∧ (p.1 ∩ p.2).card = 1 := by
  simp only [uniqueInterPairs, mem_filter, mem_product, mem_powersetCard, subset_univ, true_and,
    and_assoc]

/-- `disjointPairs n ℓ` is nonempty when `2 * ℓ ≤ n`. -/
theorem disjointPairs_nonempty {n ℓ : ℕ} (h : 2 * ℓ ≤ n) : (disjointPairs n ℓ).Nonempty := by
  let fa : Fin ℓ ↪ Fin n := ⟨fun k => ⟨k.1, by omega⟩, fun x y hxy =>
    Fin.ext (by have := congrArg Fin.val hxy; simpa using this)⟩
  let fb : Fin ℓ ↪ Fin n := ⟨fun k => ⟨ℓ + k.1, by omega⟩, fun x y hxy =>
    Fin.ext (by have := congrArg Fin.val hxy; dsimp at this; omega)⟩
  let a : Finset (Fin n) := univ.map fa
  let b : Finset (Fin n) := univ.map fb
  have hdisj : Disjoint a b := disjoint_left.2 fun i hia hib => by
    obtain ⟨x, -, rfl⟩ := mem_map.1 hia
    obtain ⟨y, -, hy⟩ := mem_map.1 hib
    have hval : ℓ + y.1 = x.1 := congrArg Fin.val hy
    omega
  exact ⟨(a, b), mem_disjointPairs_iff.2 ⟨by simp [a], by simp [b], hdisj⟩⟩

/-- `uniqueInterPairs n ℓ` is nonempty when `1 ≤ ℓ` and `2 * ℓ - 1 ≤ n`. -/
theorem uniqueInterPairs_nonempty {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (h : 2 * ℓ - 1 ≤ n) :
    (uniqueInterPairs n ℓ).Nonempty := by
  let fa : Fin ℓ ↪ Fin n := ⟨fun k => ⟨k.1, by omega⟩, fun x y hxy =>
    Fin.ext (by have := congrArg Fin.val hxy; simpa using this)⟩
  let fb : Fin ℓ ↪ Fin n := ⟨fun k => ⟨ℓ - 1 + k.1, by omega⟩, fun x y hxy =>
    Fin.ext (by have := congrArg Fin.val hxy; dsimp at this; omega)⟩
  let a : Finset (Fin n) := univ.map fa
  let b : Finset (Fin n) := univ.map fb
  have hinter : a ∩ b = {⟨ℓ - 1, by omega⟩} := by
    ext i
    simp only [a, b, mem_inter, mem_map, mem_univ, true_and, mem_singleton, Fin.ext_iff]
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      have hx' : x.1 = i.1 := hx
      have hy' : ℓ - 1 + y.1 = i.1 := hy
      omega
    · intro hi
      exact ⟨⟨⟨ℓ - 1, by omega⟩, hi.symm⟩, ⟨⟨0, by omega⟩, by change ℓ - 1 + 0 = i.1; omega⟩⟩
  exact ⟨(a, b), mem_uniqueInterPairs_iff.2 ⟨by simp [a], by simp [b], by rw [hinter,
    card_singleton]⟩⟩

end BasicDefs

/-! ### Partitions, Row/Col averages, and Step 1 double-counting -/

section Partitions

/-- An ordered partition candidate `(left, right, pivot)` of `Fin n`. -/
@[ext] private structure RazPartition (n : ℕ) where
  left : Finset (Fin n)
  right : Finset (Fin n)
  pivot : Fin n
  deriving DecidableEq

private def RazPartition.equivTuple (n : ℕ) :
    RazPartition n ≃ Finset (Fin n) × Finset (Fin n) × Fin n where
  toFun T := (T.left, T.right, T.pivot)
  invFun | (l, r, i) => ⟨l, r, i⟩
  left_inv _ := rfl
  right_inv | (_, _, _) => rfl

private local instance instFintypeRazPartition (n : ℕ) : Fintype (RazPartition n) :=
  Fintype.ofEquiv _ (RazPartition.equivTuple n).symm

/-- Valid partitions `(T₁, T₂, i)` of `Fin n` with `|T₁| = |T₂| = 2 * ℓ - 1`. -/
private def razParts (n ℓ : ℕ) : Finset (RazPartition n) :=
  univ.filter fun T =>
    T.pivot ∉ T.left ∧ T.pivot ∉ T.right ∧ Disjoint T.left T.right ∧
      T.left.card = 2 * ℓ - 1 ∧ T.right.card = 2 * ℓ - 1

private theorem mem_razParts {n ℓ : ℕ} {T : RazPartition n} :
    T ∈ razParts n ℓ ↔ T.pivot ∉ T.left ∧ T.pivot ∉ T.right ∧ Disjoint T.left T.right ∧
      T.left.card = 2 * ℓ - 1 ∧ T.right.card = 2 * ℓ - 1 := by
  simp only [razParts, mem_filter, mem_univ, true_and]

private theorem razParts_left_eq_compl {n ℓ : ℕ} (hn : n + 1 = 4 * ℓ)
    {T : RazPartition n} (hT : T ∈ razParts n ℓ) :
    T.left = (insert T.pivot T.right)ᶜ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mem_razParts.1 hT
  refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
  · rw [mem_compl, mem_insert, not_or]
    exact ⟨fun h => h1 (h ▸ hx), fun h => disjoint_left.1 h3 hx h⟩
  · rw [card_compl, card_insert_of_notMem h2, Fintype.card_fin, h4, h5]
    omega

private theorem razParts_insert_left_eq_compl {n ℓ : ℕ} (hn : n + 1 = 4 * ℓ)
    {T : RazPartition n} (hT : T ∈ razParts n ℓ) :
    insert T.pivot T.left = T.rightᶜ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mem_razParts.1 hT
  refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
  · rw [mem_compl]
    rcases mem_insert.1 hx with rfl | hx
    · exact h2
    · exact fun h => disjoint_left.1 h3 hx h
  · rw [card_compl, card_insert_of_notMem h1, Fintype.card_fin, h4, h5]
    omega

private theorem razParts_insert_right_eq_compl {n ℓ : ℕ} (hn : n + 1 = 4 * ℓ)
    {T : RazPartition n} (hT : T ∈ razParts n ℓ) :
    insert T.pivot T.right = T.leftᶜ := by
  rw [razParts_left_eq_compl hn hT, compl_compl]

private theorem mem_razParts_of_right {n ℓ : ℕ} (hn : n + 1 = 4 * ℓ)
    {T₂ : Finset (Fin n)} (hT₂ : T₂.card = 2 * ℓ - 1) {i : Fin n} (hi : i ∈ T₂ᶜ) :
    (⟨(insert i T₂)ᶜ, T₂, i⟩ : RazPartition n) ∈ razParts n ℓ := by
  rw [mem_compl] at hi
  refine mem_razParts.2 ⟨by simp, hi,
    disjoint_left.2 fun _ hx h2 => (mem_compl.1 hx) (mem_insert_of_mem h2), ?_, hT₂⟩
  rw [card_compl, card_insert_of_notMem hi, Fintype.card_fin, hT₂]
  omega

/-- Summing over `razParts n ℓ` by fixing `T₂` of size `2 * ℓ - 1` and `i ∈ T₂ᶜ`. -/
private theorem sum_razParts_by_right {n ℓ : ℕ} {M : Type*} [AddCommMonoid M]
    (hn : n + 1 = 4 * ℓ) (F : RazPartition n → M) :
    ∑ T ∈ razParts n ℓ, F T =
      ∑ T₂ ∈ powersetCard (2 * ℓ - 1) (univ : Finset (Fin n)),
        ∑ i ∈ T₂ᶜ, F ⟨(insert i T₂)ᶜ, T₂, i⟩ := by
  rw [sum_sigma']
  refine sum_nbij' (fun T => ⟨T.right, T.pivot⟩) (fun x => ⟨(insert x.2 x.1)ᶜ, x.1, x.2⟩)
    ?_ ?_ ?_ (fun _ _ => rfl) ?_
  · intro T hT
    obtain ⟨_, h2, _, _, h5⟩ := mem_razParts.1 hT
    exact mem_sigma.2 ⟨mem_powersetCard.2 ⟨subset_univ _, h5⟩, mem_compl.2 h2⟩
  · rintro ⟨T₂, i⟩ hx
    exact mem_razParts_of_right hn (mem_powersetCard.1 (mem_sigma.1 hx).1).2 (mem_sigma.1 hx).2
  · intro T hT
    ext <;> simp only [razParts_left_eq_compl hn hT]
  · intro T hT
    congr 1
    ext <;> simp only [razParts_left_eq_compl hn hT]

/-- Swapping `T₁` and `T₂` is an involution on `razParts n ℓ`. -/
private theorem sum_razParts_swap {n ℓ : ℕ} {M : Type*} [AddCommMonoid M]
    (F : RazPartition n → M) :
    ∑ T ∈ razParts n ℓ, F T = ∑ T ∈ razParts n ℓ, F ⟨T.right, T.left, T.pivot⟩ := by
  refine sum_nbij' (fun T => ⟨T.right, T.left, T.pivot⟩) (fun T => ⟨T.right, T.left, T.pivot⟩)
    ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) <;>
  · intro T hT
    obtain ⟨h1, h2, h3, h4, h5⟩ := mem_razParts.1 hT
    exact mem_razParts.2 ⟨h2, h1, h3.symm, h5, h4⟩

private theorem razParts_nonempty {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hn : n + 1 = 4 * ℓ) :
    (razParts n ℓ).Nonempty := by
  have h1 : 2 * ℓ - 1 ≤ (univ : Finset (Fin n)).card := by simp; omega
  obtain ⟨T₂, hT₂⟩ := Finset.exists_subset_card_eq h1
  have hc : T₂ᶜ.Nonempty := by
    rw [← card_pos, card_compl, Fintype.card_fin, hT₂.2]; omega
  obtain ⟨i, hi⟩ := hc
  exact ⟨⟨(insert i T₂)ᶜ, T₂, i⟩, mem_razParts_of_right hn hT₂.2 hi⟩

private theorem choose_two_mul_sub_one_eq (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (2 * ℓ - 1).choose ℓ = (2 * ℓ - 1).choose (ℓ - 1) := by
  have hsub : 2 * ℓ - 1 - ℓ = ℓ - 1 := by omega
  rw [← hsub]
  exact (Nat.choose_symm (by omega)).symm

private theorem two_mul_choose_two_mul_sub_one (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    2 * (2 * ℓ - 1).choose ℓ = (2 * ℓ).choose ℓ := by
  have h1 : 2 * ℓ = (2 * ℓ - 1) + 1 := by omega
  have h2 : ℓ = (ℓ - 1) + 1 := by omega
  conv_rhs => rw [h1, h2]
  rw [Nat.choose_succ_succ, Nat.succ_eq_add_one, ← h2, choose_two_mul_sub_one_eq ℓ hℓ]
  ring

private noncomputable def row0 {n : ℕ} (ℓ : ℕ) (f : Finset (Fin n) → ℝ) (T : RazPartition n) :
    ℝ :=
  (∑ a ∈ powersetCard ℓ T.left, f a) / ((2 * ℓ - 1).choose ℓ : ℝ)

private noncomputable def row1 {n : ℕ} (ℓ : ℕ) (f : Finset (Fin n) → ℝ) (T : RazPartition n) :
    ℝ :=
  (∑ a ∈ (powersetCard ℓ T.rightᶜ).filter (T.pivot ∈ ·), f a) / ((2 * ℓ - 1).choose (ℓ - 1) : ℝ)

private noncomputable def col0 {n : ℕ} (ℓ : ℕ) (g : Finset (Fin n) → ℝ) (T : RazPartition n) :
    ℝ :=
  (∑ b ∈ powersetCard ℓ T.right, g b) / ((2 * ℓ - 1).choose ℓ : ℝ)

private noncomputable def col1 {n : ℕ} (ℓ : ℕ) (g : Finset (Fin n) → ℝ) (T : RazPartition n) :
    ℝ :=
  (∑ b ∈ (powersetCard ℓ T.leftᶜ).filter (T.pivot ∈ ·), g b) / ((2 * ℓ - 1).choose (ℓ - 1) : ℝ)

private theorem row0_nonneg {n ℓ : ℕ} {f : Finset (Fin n) → ℝ} (hf : ∀ a, 0 ≤ f a)
    (T : RazPartition n) : 0 ≤ row0 ℓ f T :=
  div_nonneg (sum_nonneg fun a _ => hf a) (Nat.cast_nonneg _)

private theorem row1_nonneg {n ℓ : ℕ} {f : Finset (Fin n) → ℝ} (hf : ∀ a, 0 ≤ f a)
    (T : RazPartition n) : 0 ≤ row1 ℓ f T :=
  div_nonneg (sum_nonneg fun a _ => hf a) (Nat.cast_nonneg _)

private theorem col0_nonneg {n ℓ : ℕ} {g : Finset (Fin n) → ℝ} (hg : ∀ b, 0 ≤ g b)
    (T : RazPartition n) : 0 ≤ col0 ℓ g T :=
  div_nonneg (sum_nonneg fun b _ => hg b) (Nat.cast_nonneg _)

private theorem col1_nonneg {n ℓ : ℕ} {g : Finset (Fin n) → ℝ} (hg : ∀ b, 0 ≤ g b)
    (T : RazPartition n) : 0 ≤ col1 ℓ g T :=
  div_nonneg (sum_nonneg fun b _ => hg b) (Nat.cast_nonneg _)

/-- For a fixed `(a, b) ∈ A`, the number of partitions `T ∈ razParts n ℓ` with `a ⊆ T.left` and
`b ⊆ T.right` equals `(2 * ℓ - 1) * (2 * ℓ - 2).choose (ℓ - 1)`. -/
private theorem card_razParts_containing_disjoint {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hn : n + 1 = 4 * ℓ)
    {a b : Finset (Fin n)} (hp : (a, b) ∈ disjointPairs n ℓ) :
    (razParts n ℓ |>.filter fun T => a ⊆ T.left ∧ b ⊆ T.right).card =
      (2 * ℓ - 1) * (2 * ℓ - 2).choose (ℓ - 1) := by
  obtain ⟨ha, hb, hdisj⟩ := mem_disjointPairs_iff.1 hp
  have hab_card : (a ∪ b).card = 2 * ℓ := by rw [card_union_of_disjoint hdisj, ha, hb]; omega
  have hcompl_card : (a ∪ b)ᶜ.card = 2 * ℓ - 1 := by
    rw [card_compl, Fintype.card_fin, hab_card]; omega
  let S := (a ∪ b)ᶜ.sigma fun i => powersetCard (ℓ - 1) (insert i (a ∪ b))ᶜ
  have hS_card : S.card = (2 * ℓ - 1) * (2 * ℓ - 2).choose (ℓ - 1) := by
    rw [card_sigma]
    calc ∑ i ∈ (a ∪ b)ᶜ, (powersetCard (ℓ - 1) (insert i (a ∪ b))ᶜ).card
        = ∑ _i ∈ (a ∪ b)ᶜ, (2 * ℓ - 2).choose (ℓ - 1) := by
          refine sum_congr rfl fun i hi => ?_
          rw [card_powersetCard, card_compl, card_insert_of_notMem (mem_compl.1 hi),
            Fintype.card_fin, hab_card]
          congr 1; omega
      _ = (2 * ℓ - 1) * (2 * ℓ - 2).choose (ℓ - 1) := by
          rw [sum_const, smul_eq_mul, hcompl_card]
  rw [← hS_card]
  refine Finset.card_nbij' (fun T => ⟨T.pivot, T.left \ a⟩)
    (fun x => ⟨a ∪ x.2, (insert x.1 (a ∪ x.2))ᶜ, x.1⟩) ?_ ?_ ?_ ?_
  · intro T hT
    simp only [mem_coe, mem_filter] at hT
    obtain ⟨h1, h2, h3, h4, h5⟩ := mem_razParts.1 hT.1
    obtain ⟨haL, hbR⟩ := hT.2
    have hpiv : T.pivot ∈ (a ∪ b)ᶜ := by
      rw [mem_compl, mem_union, not_or]
      exact ⟨fun h => h1 (haL h), fun h => h2 (hbR h)⟩
    refine mem_coe.2 <| mem_sigma.2 ⟨hpiv, mem_powersetCard.2 ⟨fun y hy => ?_, ?_⟩⟩
    · rw [mem_sdiff] at hy
      rw [mem_compl, mem_insert, mem_union, not_or, not_or]
      exact ⟨fun h => by dsimp only at h; exact h1 (h ▸ hy.1), hy.2,
        fun h => disjoint_left.1 h3 hy.1 (hbR h)⟩
    · rw [card_sdiff_of_subset haL, h4, ha]; omega
  · rintro ⟨i, s⟩ hx
    obtain ⟨hi, hs⟩ := mem_sigma.1 (mem_coe.1 hx)
    obtain ⟨hs_sub, hs_card⟩ := mem_powersetCard.1 hs
    have hi_ab : i ∉ a ∪ b := mem_compl.1 hi
    have hdisj_as : Disjoint a s := disjoint_left.2 fun y hya hys =>
      (mem_compl.1 (hs_sub hys)) (mem_insert_of_mem (mem_union_left b hya))
    have hdisj_bs : Disjoint b s := disjoint_left.2 fun y hyb hys =>
      (mem_compl.1 (hs_sub hys)) (mem_insert_of_mem (mem_union_right a hyb))
    have hi_a : i ∉ a := fun h => hi_ab (mem_union_left b h)
    have hi_s : i ∉ s := fun h => (mem_compl.1 (hs_sub h)) (mem_insert_self i _)
    have hL_card : (a ∪ s).card = 2 * ℓ - 1 := by
      rw [card_union_of_disjoint hdisj_as, ha, hs_card]; omega
    have hR_card : (insert i (a ∪ s))ᶜ.card = 2 * ℓ - 1 := by
      rw [card_compl, card_insert_of_notMem (by simp [hi_a, hi_s]), Fintype.card_fin, hL_card]
      omega
    refine mem_coe.2 <| mem_filter.2 ⟨mem_razParts.2 ⟨by simp [hi_a, hi_s], by simp,
      disjoint_left.2 fun y hy hy' => (mem_compl.1 hy') (mem_insert_of_mem hy),
      hL_card, hR_card⟩, subset_union_left, fun y hyb => ?_⟩
    rw [mem_compl, mem_insert, mem_union, not_or, not_or]
    exact ⟨fun h => by dsimp only at h; subst h; exact hi_ab (mem_union_right a hyb),
      fun h => disjoint_left.1 hdisj h hyb, fun h => disjoint_left.1 hdisj_bs hyb h⟩
  · intro T hT
    simp only [mem_coe, mem_filter] at hT
    have hunion : a ∪ T.left \ a = T.left := union_sdiff_of_subset hT.2.1
    ext1
    · exact hunion
    · dsimp only; rw [hunion, razParts_insert_left_eq_compl hn hT.1, compl_compl]
    · rfl
  · rintro ⟨i, s⟩ hx
    obtain ⟨_, hs⟩ := mem_sigma.1 (mem_coe.1 hx)
    obtain ⟨hs_sub, _⟩ := mem_powersetCard.1 hs
    have hdisj_as : Disjoint a s := disjoint_left.2 fun y hya hys =>
      (mem_compl.1 (hs_sub hys)) (mem_insert_of_mem (mem_union_left b hya))
    refine Sigma.ext rfl (heq_of_eq ?_)
    exact union_sdiff_cancel_left hdisj_as

/-- For a fixed `(a, b) ∈ B`, the number of partitions `T ∈ razParts n ℓ` with
`a ⊆ T.rightᶜ, T.pivot ∈ a, b ⊆ T.leftᶜ, T.pivot ∈ b` equals `(2 * ℓ).choose ℓ`. -/
private theorem card_razParts_containing_uniqueInter {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hn : n + 1 = 4 * ℓ)
    {a b : Finset (Fin n)} (hp : (a, b) ∈ uniqueInterPairs n ℓ) :
    (razParts n ℓ |>.filter fun T =>
      a ⊆ T.rightᶜ ∧ T.pivot ∈ a ∧ b ⊆ T.leftᶜ ∧ T.pivot ∈ b).card = (2 * ℓ).choose ℓ := by
  obtain ⟨ha, hb, hinter⟩ := mem_uniqueInterPairs_iff.1 hp
  obtain ⟨i₀, hi₀_eq⟩ := card_eq_one.1 hinter
  have hi₀a : i₀ ∈ a := (mem_inter.1 (hi₀_eq ▸ mem_singleton_self i₀)).1
  have hi₀b : i₀ ∈ b := (mem_inter.1 (hi₀_eq ▸ mem_singleton_self i₀)).2
  have hab_card : (a ∪ b).card = 2 * ℓ - 1 := by
    have := card_union_add_card_inter a b
    rw [ha, hb, hinter] at this; omega
  have hcompl_card : (a ∪ b)ᶜ.card = 2 * ℓ := by
    rw [card_compl, Fintype.card_fin, hab_card]; omega
  rw [← hcompl_card, ← card_powersetCard ℓ (a ∪ b)ᶜ]
  refine Finset.card_nbij' (fun T => T.left \ a)
    (fun s => ⟨a.erase i₀ ∪ s, (insert i₀ (a.erase i₀ ∪ s))ᶜ, i₀⟩) ?_ ?_ ?_ ?_
  · intro T hT
    simp only [mem_coe, mem_filter] at hT
    obtain ⟨h1, h2, h3, h4, _⟩ := mem_razParts.1 hT.1
    obtain ⟨haR, hpa, hbL, hpb⟩ := hT.2
    have hpiv : T.pivot = i₀ := by
      have : T.pivot ∈ a ∩ b := mem_inter.2 ⟨hpa, hpb⟩
      rw [hi₀_eq, mem_singleton] at this; exact this
    have ha_erase_sub : a.erase i₀ ⊆ T.left := by
      intro x hx
      have hxa : x ∈ a := mem_of_mem_erase hx
      have hne : x ≠ i₀ := ne_of_mem_erase hx
      have hx_ins : x ∈ insert T.pivot T.left :=
        (razParts_insert_left_eq_compl hn hT.1).symm ▸ haR hxa
      exact (mem_insert.1 hx_ins).resolve_left (hpiv ▸ hne)
    refine mem_coe.2 <| mem_powersetCard.2 ⟨fun y hy => ?_, ?_⟩
    · rw [mem_sdiff] at hy
      rw [mem_compl, mem_union, not_or]
      exact ⟨hy.2, fun hyb => (mem_compl.1 (hbL hyb)) hy.1⟩
    · have hsdiff : T.left \ a = T.left \ a.erase i₀ := by
        ext y; simp only [mem_sdiff, mem_erase, not_and]
        exact ⟨fun ⟨hL, hna⟩ => ⟨hL, fun _ => hna⟩,
          fun ⟨hL, h⟩ => ⟨hL, fun hya => h (fun heq => h1 (hpiv.symm ▸ heq ▸ hL)) hya⟩⟩
      dsimp only
      rw [hsdiff, card_sdiff_of_subset ha_erase_sub, h4, card_erase_of_mem hi₀a, ha]; omega
  · intro s hs
    obtain ⟨hs_sub, hs_card⟩ := mem_powersetCard.1 (mem_coe.1 hs)
    have hdisj_as : Disjoint (a.erase i₀) s := disjoint_left.2 fun y hya hys =>
      (mem_compl.1 (hs_sub hys)) (mem_union_left b (mem_of_mem_erase hya))
    have hdisj_bs : Disjoint (b.erase i₀) s := disjoint_left.2 fun y hyb hys =>
      (mem_compl.1 (hs_sub hys)) (mem_union_right a (mem_of_mem_erase hyb))
    have hi₀_s : i₀ ∉ s := fun h =>
      (mem_compl.1 (hs_sub h)) (mem_union_left b hi₀a)
    have hL_card : (a.erase i₀ ∪ s).card = 2 * ℓ - 1 := by
      rw [card_union_of_disjoint hdisj_as, card_erase_of_mem hi₀a, ha, hs_card]; omega
    have hR_card : (insert i₀ (a.erase i₀ ∪ s))ᶜ.card = 2 * ℓ - 1 := by
      rw [card_compl, card_insert_of_notMem (by simp [hi₀_s]), Fintype.card_fin, hL_card]; omega
    refine mem_coe.2 <| mem_filter.2 ⟨mem_razParts.2 ⟨by simp [hi₀_s], by simp,
      disjoint_left.2 fun y hy hy' => (mem_compl.1 hy') (mem_insert_of_mem hy),
      hL_card, hR_card⟩, ?_, hi₀a, ?_, hi₀b⟩
    · intro x hxa
      rw [compl_compl]
      by_cases hxi : x = i₀
      · subst hxi; exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_union_left _ (mem_erase.2 ⟨hxi, hxa⟩))
    · intro x hxb
      rw [mem_compl, mem_union, not_or]
      refine ⟨fun hxa => ?_, fun hxs => (mem_compl.1 (hs_sub hxs)) (mem_union_right a hxb)⟩
      have hxab : x ∈ a ∩ b := mem_inter.2 ⟨mem_of_mem_erase hxa, hxb⟩
      rw [hi₀_eq, mem_singleton] at hxab
      exact (ne_of_mem_erase hxa) hxab
  · intro T hT
    simp only [mem_coe, mem_filter] at hT
    obtain ⟨h1, _, _, _, _⟩ := mem_razParts.1 hT.1
    obtain ⟨haR, hpa, _, hpb⟩ := hT.2
    have hpiv : T.pivot = i₀ := by
      have : T.pivot ∈ a ∩ b := mem_inter.2 ⟨hpa, hpb⟩
      rw [hi₀_eq, mem_singleton] at this; exact this
    have hL_eq : a.erase i₀ ∪ T.left \ a = T.left := by
      ext y
      simp only [mem_union, mem_erase, mem_sdiff]
      constructor
      · rintro (⟨hne, hya⟩ | ⟨hL, _⟩)
        · have hy := (razParts_insert_left_eq_compl hn hT.1).symm ▸ haR hya
          exact (mem_insert.1 hy).resolve_left (hpiv ▸ hne)
        · exact hL
      · intro hL
        by_cases hya : y ∈ a
        · exact .inl ⟨fun h => h1 (hpiv.symm ▸ h ▸ hL), hya⟩
        · exact .inr ⟨hL, hya⟩
    ext1
    · exact hL_eq
    · dsimp only; rw [hL_eq, ← hpiv, razParts_insert_left_eq_compl hn hT.1, compl_compl]
    · exact hpiv.symm
  · intro s hs
    obtain ⟨hs_sub, _⟩ := mem_powersetCard.1 (mem_coe.1 hs)
    ext y
    simp only [mem_sdiff, mem_union, mem_erase]
    constructor
    · rintro ⟨(⟨_, hya⟩ | hys), hna⟩
      · exact absurd hya hna
      · exact hys
    · intro hys
      exact ⟨.inr hys, fun hya => (mem_compl.1 (hs_sub hys)) (mem_union_left b hya)⟩

/-- Double-counting identity for `A`: `E[Row₀(T) * Col₀(T)] = E[f(a) * g(b) | A]`. -/
private theorem avg_row0_mul_col0_eq_avg_A {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hn : n + 1 = 4 * ℓ)
    (f g : Finset (Fin n) → ℝ) :
    avgOn (razParts n ℓ) (fun T => row0 ℓ f T * col0 ℓ g T) =
      avgOn (disjointPairs n ℓ) (fun p => f p.1 * g p.2) := by
  have hden_pos : (0 : ℝ) < ((2 * ℓ - 1).choose ℓ : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : ℓ ≤ 2 * ℓ - 1)
  have hsum_general : ∀ F G : Finset (Fin n) → ℝ,
      ∑ T ∈ razParts n ℓ, row0 ℓ F T * col0 ℓ G T =
        (((2 * ℓ - 1) * (2 * ℓ - 2).choose (ℓ - 1) : ℕ) : ℝ) /
          (((2 * ℓ - 1).choose ℓ : ℝ) ^ 2) *
          ∑ p ∈ disjointPairs n ℓ, F p.1 * G p.2 := by
    intro F G
    have hrw : ∑ T ∈ razParts n ℓ, row0 ℓ F T * col0 ℓ G T =
        (∑ T ∈ razParts n ℓ, ∑ a ∈ powersetCard ℓ T.left, ∑ b ∈ powersetCard ℓ T.right,
          F a * G b) / (((2 * ℓ - 1).choose ℓ : ℝ) ^ 2) := by
      rw [sum_div]
      refine sum_congr rfl fun T _ => ?_
      simp only [row0, col0, sum_mul_sum, div_mul_div_comm, sq]
    rw [hrw, div_mul_eq_mul_div]
    congr 1
    have hswap : ∑ T ∈ razParts n ℓ, ∑ a ∈ powersetCard ℓ T.left, ∑ b ∈ powersetCard ℓ T.right,
          F a * G b =
        ∑ p ∈ disjointPairs n ℓ,
          ∑ _T ∈ (razParts n ℓ).filter (fun T => p.1 ⊆ T.left ∧ p.2 ⊆ T.right), F p.1 * G p.2 := by
      calc ∑ T ∈ razParts n ℓ, ∑ a ∈ powersetCard ℓ T.left, ∑ b ∈ powersetCard ℓ T.right,
            F a * G b
          = ∑ T ∈ razParts n ℓ, ∑ p ∈ disjointPairs n ℓ,
              if p.1 ⊆ T.left ∧ p.2 ⊆ T.right then F p.1 * G p.2 else 0 := by
            refine sum_congr rfl fun T hT => ?_
            rw [← sum_product', ← sum_filter]
            refine sum_congr (ext fun ⟨a, b⟩ => ?_) fun _ _ => rfl
            simp only [mem_product, mem_powersetCard, mem_filter, mem_disjointPairs_iff]
            have hdisj := (mem_razParts.1 hT).2.2.1
            exact ⟨fun ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ => ⟨⟨h2, h4, hdisj.mono h1 h3⟩, h1, h3⟩,
              fun ⟨⟨h2, h4, _⟩, h1, h3⟩ => ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩⟩
        _ = ∑ p ∈ disjointPairs n ℓ, ∑ T ∈ razParts n ℓ,
              if p.1 ⊆ T.left ∧ p.2 ⊆ T.right then F p.1 * G p.2 else 0 := sum_comm
        _ = _ := sum_congr rfl fun p _ => (sum_filter _ _).symm
    rw [hswap, mul_sum]
    refine sum_congr rfl fun p hp => ?_
    rw [sum_const, nsmul_eq_mul, card_razParts_containing_disjoint hℓ hn hp]
  have h1 := hsum_general (fun _ => 1) (fun _ => 1)
  have hone_lhs : ∑ T ∈ razParts n ℓ, row0 ℓ (fun _ => 1) T * col0 ℓ (fun _ => 1) T =
      ((razParts n ℓ).card : ℝ) := by
    calc _ = ∑ _T ∈ razParts n ℓ, (1 : ℝ) := by
          refine sum_congr rfl fun T hT => ?_
          obtain ⟨_, _, _, h4, h5⟩ := mem_razParts.1 hT
          simp only [row0, col0, sum_const, nsmul_eq_mul, mul_one, card_powersetCard, h4, h5,
            div_self hden_pos.ne', mul_one]
      _ = ((razParts n ℓ).card : ℝ) := by simp
  have hone_rhs : ∑ _p ∈ disjointPairs n ℓ, (1 : ℝ) * 1 = ((disjointPairs n ℓ).card : ℝ) := by simp
  rw [hone_lhs, hone_rhs] at h1
  have hApos : (0 : ℝ) < ((disjointPairs n ℓ).card : ℝ) := by
    exact_mod_cast (disjointPairs_nonempty (by omega : 2 * ℓ ≤ n)).card_pos
  have hPpos : (0 : ℝ) < ((razParts n ℓ).card : ℝ) := by
    exact_mod_cast (razParts_nonempty hℓ hn).card_pos
  rw [avgOn, avgOn, hsum_general f g]
  have hcoeff : (((2 * ℓ - 1) * (2 * ℓ - 2).choose (ℓ - 1) : ℕ) : ℝ) /
      (((2 * ℓ - 1).choose ℓ : ℝ) ^ 2) =
      ((razParts n ℓ).card : ℝ) / ((disjointPairs n ℓ).card : ℝ) := by
    rw [eq_div_iff hApos.ne']
    exact h1.symm
  rw [hcoeff, div_mul_eq_mul_div, div_div, mul_comm ((disjointPairs n ℓ).card : ℝ), ← div_div,
    mul_div_cancel_left₀ _ hPpos.ne']

/-- Double-counting identity for `B`: `E[Row₁(T) * Col₁(T)] = E[f(a) * g(b) | B]`. -/
private theorem avg_row1_mul_col1_eq_avg_B {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hn : n + 1 = 4 * ℓ)
    (f g : Finset (Fin n) → ℝ) :
    avgOn (razParts n ℓ) (fun T => row1 ℓ f T * col1 ℓ g T) =
      avgOn (uniqueInterPairs n ℓ) (fun p => f p.1 * g p.2) := by
  have hden_pos : (0 : ℝ) < ((2 * ℓ - 1).choose (ℓ - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : ℓ - 1 ≤ 2 * ℓ - 1)
  have hcard_filter : ∀ {S : Finset (Fin n)} {i : Fin n},
      S.card = 2 * ℓ → i ∈ S →
      ((powersetCard ℓ S).filter (i ∈ ·)).card = (2 * ℓ - 1).choose (ℓ - 1) := by
    intro S i hS hi
    have hcard : (S.erase i).card = 2 * ℓ - 1 := by rw [card_erase_of_mem hi, hS]
    rw [← hcard, ← card_powersetCard (ℓ - 1) (S.erase i)]
    refine Finset.card_nbij' (fun a => a.erase i) (fun s => insert i s) ?_ ?_ ?_ ?_
    · intro a ha
      obtain ⟨ha_mem, hia⟩ := mem_filter.1 (mem_coe.1 ha)
      obtain ⟨haS, hac⟩ := mem_powersetCard.1 ha_mem
      exact mem_coe.2 <| mem_powersetCard.2 ⟨erase_subset_erase i haS,
        by rw [card_erase_of_mem hia, hac]⟩
    · intro s hs
      obtain ⟨hs_sub, hs_c⟩ := mem_powersetCard.1 (mem_coe.1 hs)
      have his : i ∉ s := fun h => (mem_erase.1 (hs_sub h)).1 rfl
      refine mem_coe.2 <| mem_filter.2 ⟨mem_powersetCard.2 ⟨insert_subset hi
        (hs_sub.trans (erase_subset _ _)), by rw [card_insert_of_notMem his, hs_c]; omega⟩,
        mem_insert_self i s⟩
    · intro a ha; exact insert_erase (mem_filter.1 (mem_coe.1 ha)).2
    · intro s hs
      have his : i ∉ s := fun h => (mem_erase.1 ((mem_powersetCard.1 (mem_coe.1 hs)).1 h)).1 rfl
      exact erase_insert his
  have hsum_general : ∀ F G : Finset (Fin n) → ℝ,
      ∑ T ∈ razParts n ℓ, row1 ℓ F T * col1 ℓ G T =
        ((2 * ℓ).choose ℓ : ℝ) / (((2 * ℓ - 1).choose (ℓ - 1) : ℝ) ^ 2) *
          ∑ p ∈ uniqueInterPairs n ℓ, F p.1 * G p.2 := by
    intro F G
    have hrw : ∑ T ∈ razParts n ℓ, row1 ℓ F T * col1 ℓ G T =
        (∑ T ∈ razParts n ℓ,
          ∑ a ∈ (powersetCard ℓ T.rightᶜ).filter (T.pivot ∈ ·),
          ∑ b ∈ (powersetCard ℓ T.leftᶜ).filter (T.pivot ∈ ·), F a * G b) /
          (((2 * ℓ - 1).choose (ℓ - 1) : ℝ) ^ 2) := by
      rw [sum_div]
      refine sum_congr rfl fun T _ => ?_
      simp only [row1, col1, sum_mul_sum, div_mul_div_comm, sq]
    rw [hrw, div_mul_eq_mul_div]
    congr 1
    have hswap : ∑ T ∈ razParts n ℓ,
          ∑ a ∈ (powersetCard ℓ T.rightᶜ).filter (T.pivot ∈ ·),
          ∑ b ∈ (powersetCard ℓ T.leftᶜ).filter (T.pivot ∈ ·), F a * G b =
        ∑ p ∈ uniqueInterPairs n ℓ,
          ∑ _T ∈ (razParts n ℓ).filter (fun T =>
            p.1 ⊆ T.rightᶜ ∧ T.pivot ∈ p.1 ∧ p.2 ⊆ T.leftᶜ ∧ T.pivot ∈ p.2), F p.1 * G p.2 := by
      calc _ = ∑ T ∈ razParts n ℓ, ∑ p ∈ uniqueInterPairs n ℓ,
              if p.1 ⊆ T.rightᶜ ∧ T.pivot ∈ p.1 ∧ p.2 ⊆ T.leftᶜ ∧ T.pivot ∈ p.2
              then F p.1 * G p.2 else 0 := by
            refine sum_congr rfl fun T hT => ?_
            rw [← sum_product', ← sum_filter]
            refine sum_congr (ext fun ⟨a, b⟩ => ?_) fun _ _ => rfl
            simp only [mem_product, mem_filter, mem_powersetCard, mem_uniqueInterPairs_iff]
            constructor
            · rintro ⟨⟨⟨haS, hac⟩, hpa⟩, ⟨⟨hbS, hbc⟩, hpb⟩⟩
              have hinter : a ∩ b = {T.pivot} := by
                ext x; simp only [mem_inter, mem_singleton]
                refine ⟨fun ⟨hxa, hxb⟩ => ?_, fun hx => hx ▸ ⟨hpa, hpb⟩⟩
                have h1 := (razParts_insert_left_eq_compl hn hT).symm ▸ haS hxa
                have h2 := (razParts_insert_right_eq_compl hn hT).symm ▸ hbS hxb
                rcases mem_insert.1 h1 with rfl | hxL
                · rfl
                · rcases mem_insert.1 h2 with rfl | hxR
                  · rfl
                  · exact absurd hxR (disjoint_left.1 (mem_razParts.1 hT).2.2.1 hxL)
              exact ⟨⟨hac, hbc, by rw [hinter, card_singleton]⟩, haS, hpa, hbS, hpb⟩
            · rintro ⟨⟨hac, hbc, _⟩, haS, hpa, hbS, hpb⟩
              exact ⟨⟨⟨haS, hac⟩, hpa⟩, ⟨⟨hbS, hbc⟩, hpb⟩⟩
        _ = ∑ p ∈ uniqueInterPairs n ℓ, ∑ T ∈ razParts n ℓ,
              if p.1 ⊆ T.rightᶜ ∧ T.pivot ∈ p.1 ∧ p.2 ⊆ T.leftᶜ ∧ T.pivot ∈ p.2
              then F p.1 * G p.2 else 0 := sum_comm
        _ = _ := sum_congr rfl fun p _ => (sum_filter _ _).symm
    rw [hswap, mul_sum]
    refine sum_congr rfl fun p hp => ?_
    rw [sum_const, nsmul_eq_mul, card_razParts_containing_uniqueInter hℓ hn hp]
  have h1 := hsum_general (fun _ => 1) (fun _ => 1)
  have hone_lhs : ∑ T ∈ razParts n ℓ, row1 ℓ (fun _ => 1) T * col1 ℓ (fun _ => 1) T =
      ((razParts n ℓ).card : ℝ) := by
    calc _ = ∑ _T ∈ razParts n ℓ, (1 : ℝ) := by
          refine sum_congr rfl fun T hT => ?_
          obtain ⟨h1, h2, _, h4, h5⟩ := mem_razParts.1 hT
          have hc1 : T.rightᶜ.card = 2 * ℓ := by rw [card_compl, Fintype.card_fin, h5]; omega
          have hc2 : T.leftᶜ.card = 2 * ℓ := by rw [card_compl, Fintype.card_fin, h4]; omega
          simp only [row1, col1, sum_const, nsmul_eq_mul, mul_one,
            hcard_filter hc1 (mem_compl.2 h2), hcard_filter hc2 (mem_compl.2 h1),
            div_self hden_pos.ne', mul_one]
      _ = ((razParts n ℓ).card : ℝ) := by simp
  have hone_rhs : ∑ _p ∈ uniqueInterPairs n ℓ, (1 : ℝ) * 1 =
      ((uniqueInterPairs n ℓ).card : ℝ) := by simp
  rw [hone_lhs, hone_rhs] at h1
  have hBpos : (0 : ℝ) < ((uniqueInterPairs n ℓ).card : ℝ) := by
    exact_mod_cast (uniqueInterPairs_nonempty hℓ (by omega : 2 * ℓ - 1 ≤ n)).card_pos
  have hPpos : (0 : ℝ) < ((razParts n ℓ).card : ℝ) := by
    exact_mod_cast (razParts_nonempty hℓ hn).card_pos
  rw [avgOn, avgOn, hsum_general f g]
  have hcoeff : ((2 * ℓ).choose ℓ : ℝ) / (((2 * ℓ - 1).choose (ℓ - 1) : ℝ) ^ 2) =
      ((razParts n ℓ).card : ℝ) / ((uniqueInterPairs n ℓ).card : ℝ) := by
    rw [eq_div_iff hBpos.ne']
    exact h1.symm
  rw [hcoeff, div_mul_eq_mul_div, div_div, mul_comm ((uniqueInterPairs n ℓ).card : ℝ), ← div_div,
    mul_div_cancel_left₀ _ hPpos.ne']

end Partitions

/-! ### Step 2: Pointwise rectangle estimate -/

section Step2

/-- Pointwise rectangle trick:
`r₀ * c₀ - r₁ * c₁ ≤ r₀ * |c₀ - c₁| + |r₀ - r₁| * c₀` for nonnegative reals. -/
private theorem rectangle_diff_le {r₀ r₁ c₀ c₁ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) :
    r₀ * c₀ - r₁ * c₁ ≤ r₀ * |c₀ - c₁| + |r₀ - r₁| * c₀ := by
  rcases le_total r₀ r₁ with hr | hr <;> rcases le_total c₀ c₁ with hc | hc
  · nlinarith [abs_nonneg (c₀ - c₁), abs_nonneg (r₀ - r₁)]
  · have : |c₀ - c₁| = c₀ - c₁ := abs_of_nonneg (sub_nonneg.2 hc)
    nlinarith [abs_nonneg (r₀ - r₁)]
  · have : |r₀ - r₁| = r₀ - r₁ := abs_of_nonneg (sub_nonneg.2 hr)
    nlinarith [abs_nonneg (c₀ - c₁)]
  · have hc' : |c₀ - c₁| = c₀ - c₁ := abs_of_nonneg (sub_nonneg.2 hc)
    have hr' : |r₀ - r₁| = r₀ - r₁ := abs_of_nonneg (sub_nonneg.2 hr)
    nlinarith

end Step2

/-! ### Step 3: Entropy + Bernoulli Pinsker one-sided error estimate -/

section Step3

/-- Elementary central binomial lower bound: `4 ^ ℓ ≤ (2 * ℓ + 1) * (2 * ℓ).choose ℓ`. -/
private theorem four_pow_le_mul_choose (ℓ : ℕ) :
    (4 : ℝ) ^ ℓ ≤ (2 * (ℓ : ℝ) + 1) * ((2 * ℓ).choose ℓ : ℝ) := by
  have hnat : 4 ^ ℓ ≤ (2 * ℓ + 1) * (2 * ℓ).choose ℓ := by
    calc 4 ^ ℓ = 2 ^ (2 * ℓ) := by rw [pow_mul]; norm_num
      _ = ∑ k ∈ range (2 * ℓ + 1), (2 * ℓ).choose k := (Nat.sum_range_choose (2 * ℓ)).symm
      _ ≤ ∑ _k ∈ range (2 * ℓ + 1), (2 * ℓ).choose ℓ :=
          sum_le_sum fun k _ => by
            simpa only [Nat.centralBinom_eq_two_mul_choose] using Nat.choose_le_centralBinom k ℓ
      _ = (2 * ℓ + 1) * (2 * ℓ).choose ℓ := by simp
  exact_mod_cast hnat

/-- Quadratic lower bound on the binary KL divergence from `1/2` (in nats):
for `t ∈ [0, 1]`, `(1 - 2 * t) ^ 2 / 2 ≤ log 2 + t * log t + (1 - t) * log (1 - t)`.
Equivalently, `1 - H₂(t) ≥ (1 - 2 * t) ^ 2 / (2 * log 2)`
. -/
private theorem one_sub_two_mul_sq_div_two_le_kl_half {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - 2 * t) ^ 2 / 2 ≤ Real.log 2 + t * Real.log t + (1 - t) * Real.log (1 - t) := by
  let g : ℝ → ℝ := fun x => Real.log 2 + x * Real.log x + (1 - x) * Real.log (1 - x) -
    (1 - 2 * x) ^ 2 / 2
  let g' : ℝ → ℝ := fun x => Real.log x - Real.log (1 - x) + 2 * (1 - 2 * x)
  have hg_cont : Continuous g := by
    have h1 : Continuous fun x : ℝ => x * Real.log x := Real.continuous_mul_log
    have h2 : Continuous fun x : ℝ => (1 - x) * Real.log (1 - x) :=
      Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
    have h3 : Continuous fun x : ℝ => (1 - 2 * x) ^ 2 / 2 := by fun_prop
    exact ((continuous_const.add h1).add h2).sub h3
  have hg_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (g' x) x := by
    intro x ⟨hx0, hx1⟩
    have h1x : 1 - x ≠ 0 := (sub_pos.2 hx1).ne'
    have hd1 : HasDerivAt (fun y => y * Real.log y) (Real.log x + 1) x :=
      Real.hasDerivAt_mul_log hx0.ne'
    have hd2 : HasDerivAt (fun y => (1 - y) * Real.log (1 - y)) (-(Real.log (1 - x) + 1)) x := by
      have hcomp : HasDerivAt (fun y => (1 - y) * Real.log (1 - y))
          ((Real.log (1 - x) + 1) * -1) x :=
        (Real.hasDerivAt_mul_log h1x).comp x ((hasDerivAt_id x).const_sub 1)
      convert hcomp using 1; ring
    have hd3 : HasDerivAt (fun y => (1 - 2 * y) ^ 2 / 2) (-2 * (1 - 2 * x)) x := by
      have hlin : HasDerivAt (fun y => 1 - 2 * y) (-2) x := by
        simpa using ((hasDerivAt_id x).const_mul 2).const_sub 1
      have hsq := (hlin.pow 2).div_const 2
      convert hsq using 1; ring
    have htot := (((hasDerivAt_const x (Real.log 2)).add hd1).add hd2).sub hd3
    convert htot using 1
    simp only [g']; ring
  have hg'_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt g' ((1 - 2 * x) ^ 2 / (x * (1 - x))) x := by
    intro x ⟨hx0, hx1⟩
    have h1x : 1 - x ≠ 0 := (sub_pos.2 hx1).ne'
    have hd1 := Real.hasDerivAt_log hx0.ne'
    have hd2 : HasDerivAt (fun y => Real.log (1 - y)) (-(1 - x)⁻¹) x := by
      have hcomp : HasDerivAt (fun y => Real.log (1 - y)) ((1 - x)⁻¹ * -1) x :=
        (Real.hasDerivAt_log h1x).comp x ((hasDerivAt_id x).const_sub 1)
      convert hcomp using 1; ring
    have hd3 : HasDerivAt (fun y => 2 * (1 - 2 * y)) (-4) x := by
      have hlin : HasDerivAt (fun y => 2 * (1 - 2 * y)) (2 * -(2 * 1)) x :=
        (((hasDerivAt_id x).const_mul 2).const_sub 1).const_mul 2
      convert hlin using 1; ring
    have htot := (hd1.sub hd2).add hd3
    convert htot using 1
    field_simp; ring
  have hg'_mono : MonotoneOn g' (Set.Ioo (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
      (fun x hx => (hg'_deriv x hx).continuousAt.continuousWithinAt)
      (fun x hx =>
        (hg'_deriv x (by simpa [interior_Ioo] using hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ioo] using hx
        rw [(hg'_deriv x hx').deriv]
        have hpos : 0 < x * (1 - x) := mul_pos hx'.1 (sub_pos.2 hx'.2)
        exact div_nonneg (sq_nonneg _) hpos.le)
  have hg'_half : g' (1 / 2) = 0 := by
    have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    simp only [g', h12, sub_self, zero_add]; norm_num
  have hg_half : g (1 / 2) = 0 := by
    simp only [g]
    have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [h12, one_div, Real.log_inv]
    ring
  have hgoal : 0 ≤ g t := by
    rcases le_total t (1 / 2) with hle | hge
    · have hanti : AntitoneOn g (Set.Icc (0 : ℝ) (1 / 2)) :=
        antitoneOn_of_deriv_nonpos (convex_Icc 0 (1 / 2)) hg_cont.continuousOn
          (fun x hx => by
            rw [interior_Icc] at hx
            exact (hg_deriv x ⟨hx.1, by linarith [hx.2]⟩).differentiableAt.differentiableWithinAt)
          (fun x hx => by
            rw [interior_Icc] at hx
            rw [(hg_deriv x ⟨hx.1, by linarith [hx.2]⟩).deriv]
            have := hg'_mono ⟨hx.1, by linarith [hx.2]⟩ ⟨by norm_num, by norm_num⟩ hx.2.le
            linarith [hg'_half])
      have := hanti ⟨ht0, hle⟩ ⟨by norm_num, le_rfl⟩ hle
      linarith [hg_half]
    · have hmono : MonotoneOn g (Set.Icc (1 / 2 : ℝ) 1) :=
        monotoneOn_of_deriv_nonneg (convex_Icc (1 / 2) 1) hg_cont.continuousOn
          (fun x hx => by
            rw [interior_Icc] at hx
            exact (hg_deriv x ⟨by linarith [hx.1], hx.2⟩).differentiableAt.differentiableWithinAt)
          (fun x hx => by
            rw [interior_Icc] at hx
            rw [(hg_deriv x ⟨by linarith [hx.1], hx.2⟩).deriv]
            have := hg'_mono ⟨by norm_num, by norm_num⟩ ⟨by linarith [hx.1], hx.2⟩ hx.1.le
            linarith [hg'_half])
      have := hmono ⟨le_rfl, by norm_num⟩ ⟨hge, ht1⟩ hge
      linarith [hg_half]
  simp only [g] at hgoal
  linarith

/-- Product distribution identity over all subsets of `S`:
`∑ a ∈ S.powerset, ∏ j ∈ S, (if j ∈ a then p j else 1 - p j) = 1`. -/
private theorem sum_powerset_prod_ite {α : Type*} [DecidableEq α] (S : Finset α) (p : α → ℝ) :
    ∑ a ∈ S.powerset, ∏ j ∈ S, (if j ∈ a then p j else 1 - p j) = 1 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [powerset_insert, sum_union (disjoint_left.2 fun a ha1 ha2 => by
      obtain ⟨b, hb, rfl⟩ := mem_image.1 ha2
      exact hx ((mem_powerset.1 ha1) (mem_insert_self x b)))]
    have h1 : ∑ a ∈ s.powerset, ∏ j ∈ insert x s, (if j ∈ a then p j else 1 - p j) =
        (1 - p x) * ∑ a ∈ s.powerset, ∏ j ∈ s, (if j ∈ a then p j else 1 - p j) := by
      rw [mul_sum]
      refine sum_congr rfl fun a ha => ?_
      have hna : x ∉ a := fun h => hx ((mem_powerset.1 ha) h)
      rw [prod_insert hx]; simp only [hna, ↓reduceIte]
    have h2 : ∑ a ∈ s.powerset.image (insert x),
          ∏ j ∈ insert x s, (if j ∈ a then p j else 1 - p j) =
        p x * ∑ a ∈ s.powerset, ∏ j ∈ s, (if j ∈ a then p j else 1 - p j) := by
      rw [sum_image (fun a ha b hb hab => by
        have hax : x ∉ a := fun h => hx ((mem_powerset.1 ha) h)
        have hbx : x ∉ b := fun h => hx ((mem_powerset.1 hb) h)
        simpa [erase_insert hax, erase_insert hbx] using congrArg (Finset.erase · x) hab),
        mul_sum]
      refine sum_congr rfl fun a ha => ?_
      rw [prod_insert hx]; simp only [mem_insert_self, ↓reduceIte]
      congr 1
      refine prod_congr rfl fun j hj => ?_
      have hne : j ≠ x := fun h => hx (h ▸ hj)
      simp [hne]
    rw [h1, h2, ih]
    ring

/-- One-sided entropy bound for fixed `T₂`:
assuming `T₂.card = 2 * ℓ - 1`, `μ_f(T₂) > 2 ^ (-δ * ℓ - 1) * M_f(T₂)`, where
`δ = ε ^ 2 / (16 * log 2) - (1 + logb 2 (2 * ℓ + 1)) / ℓ`, we have
`∑ i ∈ T₂ᶜ, |Row₀(T(i)) - Row₁(T(i))| ≤ (ε / 2) * ∑ i ∈ T₂ᶜ, Row₀(T(i))`. -/
private theorem sum_abs_row0_sub_row1_le {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hn : n + 1 = 4 * ℓ)
    {f : Finset (Fin n) → ℝ} (hf : ∀ a, 0 ≤ f a)
    {ε : ℝ} (hε : 0 < ε) {T₂ : Finset (Fin n)} (hT₂ : T₂.card = 2 * ℓ - 1)
    (hbig :
      (2 : ℝ) ^ (-(ε ^ 2 / (16 * Real.log 2) - (1 + Real.logb 2 (2 * (ℓ : ℝ) + 1)) / ℓ) * ℓ - 1) *
          maxOn (powersetCard ℓ T₂ᶜ) f <
        (∑ a ∈ powersetCard ℓ T₂ᶜ, f a) / ((2 * ℓ).choose ℓ : ℝ)) :
    ∑ i ∈ T₂ᶜ,
        |row0 ℓ f ⟨(insert i T₂)ᶜ, T₂, i⟩ - row1 ℓ f ⟨(insert i T₂)ᶜ, T₂, i⟩| ≤
      (ε / 2) * ∑ i ∈ T₂ᶜ, row0 ℓ f ⟨(insert i T₂)ᶜ, T₂, i⟩ := by
  classical
  set S : Finset (Fin n) := T₂ᶜ
  have hS_card : S.card = 2 * ℓ := by rw [card_compl, Fintype.card_fin, hT₂]; omega
  set δ : ℝ := ε ^ 2 / (16 * Real.log 2) - (1 + Real.logb 2 (2 * (ℓ : ℝ) + 1)) / ℓ
  set Z : ℝ := ∑ a ∈ powersetCard ℓ S, f a
  set C : ℝ := ((2 * ℓ).choose ℓ : ℝ)
  set μf : ℝ := Z / C
  set Mf : ℝ := maxOn (powersetCard ℓ S) f
  have hC_pos : 0 < C := Nat.cast_pos.2 (Nat.choose_pos (by omega : ℓ ≤ 2 * ℓ))
  have hℓ_pos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hMf_nn : 0 ≤ Mf := maxOn_nonneg fun a _ => hf a
  have hμf_pos : 0 < μf := lt_of_le_of_lt (mul_nonneg (by positivity) hMf_nn) hbig
  have hZ_pos : 0 < Z := by
    have : Z = μf * C := (div_mul_cancel₀ Z hC_pos.ne').symm
    rw [this]; positivity
  -- Normalized weights `w a = f a / Z` on `powersetCard ℓ S` and marginals `lam j = P[j ∈ a]`.
  let w : Finset (Fin n) → ℝ := fun a => f a / Z
  have hw_nn : ∀ a, 0 ≤ w a := fun a => div_nonneg (hf a) hZ_pos.le
  have hw_sum : ∑ a ∈ powersetCard ℓ S, w a = 1 := by
    simp only [w, ← sum_div]
    exact div_self hZ_pos.ne'
  let lam : Fin n → ℝ := fun j => (∑ a ∈ (powersetCard ℓ S).filter (j ∈ ·), f a) / Z
  have hlam_eq : ∀ j, lam j = ∑ a ∈ (powersetCard ℓ S).filter (j ∈ ·), w a := fun j => by
    simp only [lam, w, ← sum_div]
  have hlam_compl : ∀ j, 1 - lam j = ∑ a ∈ (powersetCard ℓ S).filter (j ∉ ·), w a := fun j => by
    rw [hlam_eq, ← hw_sum, ← sum_filter_add_sum_filter_not (powersetCard ℓ S) (j ∈ ·) w]
    ring
  have hlam_bounds : ∀ j, 0 ≤ lam j ∧ lam j ≤ 1 := fun j =>
    ⟨by rw [hlam_eq]; exact sum_nonneg fun a _ => hw_nn a,
     by linarith [show 0 ≤ 1 - lam j by rw [hlam_compl]; exact sum_nonneg fun a _ => hw_nn a]⟩
  -- Flatness upper bound: `w a ≤ 2^(δ*ℓ + 1) / C` for all `a ∈ powersetCard ℓ S`.
  have hw_le : ∀ a ∈ powersetCard ℓ S, w a ≤ (2 : ℝ) ^ (δ * ℓ + 1) / C := by
    intro a ha
    have hfa_le : f a ≤ Mf := le_maxOn ha
    have hMf_lt : Mf < (2 : ℝ) ^ (δ * ℓ + 1) * μf := by
      have hmul := mul_lt_mul_of_pos_left hbig (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)
        (δ * ℓ + 1))
      rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at hmul
      have hexp : δ * ℓ + 1 + (-δ * ℓ - 1) = 0 := by ring
      simpa only [hexp, Real.rpow_zero, one_mul] using hmul
    have hfa_lt : f a ≤ (2 : ℝ) ^ (δ * ℓ + 1) * μf := hfa_le.trans hMf_lt.le
    simp only [w]
    rw [div_le_div_iff₀ hZ_pos hC_pos]
    have hZ_eq : Z = μf * C := (div_mul_cancel₀ Z hC_pos.ne').symm
    calc f a * C ≤ ((2 : ℝ) ^ (δ * ℓ + 1) * μf) * C := mul_le_mul_of_nonneg_right hfa_lt hC_pos.le
      _ = (2 : ℝ) ^ (δ * ℓ + 1) * Z := by rw [hZ_eq]; ring
  -- Entropy lower bound (in nats):
  -- `2 * ℓ * log 2 - (δ * ℓ + 1) * log 2 - log (2 * ℓ + 1) ≤ ∑ a, -w a * log (w a)`.
  have hent_lb :
      Real.log C - (δ * ℓ + 1) * Real.log 2 ≤ ∑ a ∈ powersetCard ℓ S, -(w a * Real.log (w a)) := by
    calc Real.log C - (δ * ℓ + 1) * Real.log 2
        = ∑ a ∈ powersetCard ℓ S, w a * (Real.log C - (δ * ℓ + 1) * Real.log 2) := by
          rw [← sum_mul, hw_sum, one_mul]
      _ ≤ ∑ a ∈ powersetCard ℓ S, -(w a * Real.log (w a)) := by
          refine sum_le_sum fun a ha => ?_
          rcases eq_or_lt_of_le (hw_nn a) with hw0 | hwpos
          · simp [← hw0]
          · have hlog := Real.log_le_log hwpos (hw_le a ha)
            rw [Real.log_div (by positivity) hC_pos.ne',
              Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
            have := mul_le_mul_of_nonneg_left hlog hwpos.le
            linarith
  -- Entropy subadditivity (in nats) via Gibbs's inequality against the product distribution `q`:
  -- `∑ a, -w a * log (w a) ≤ ∑ j ∈ S, -(lam j * log (lam j) + (1 - lam j) * log (1 - lam j))`.
  let q : Finset (Fin n) → ℝ := fun a => ∏ j ∈ S, (if j ∈ a then lam j else 1 - lam j)
  have hq_nn : ∀ a, 0 ≤ q a := fun a =>
    prod_nonneg fun j _ => by split_ifs <;> linarith [(hlam_bounds j).1, (hlam_bounds j).2]
  have hq_sum_le : ∑ a ∈ powersetCard ℓ S, q a ≤ 1 := by
    have hsub : powersetCard ℓ S ⊆ S.powerset := fun a ha =>
      mem_powerset.2 (mem_powersetCard.1 ha).1
    exact (sum_le_sum_of_subset_of_nonneg hsub fun a _ _ => hq_nn a).trans_eq
      (sum_powerset_prod_ite S lam)
  have hent_ub : ∑ a ∈ powersetCard ℓ S, -(w a * Real.log (w a)) ≤
      ∑ j ∈ S, -(lam j * Real.log (lam j) + (1 - lam j) * Real.log (1 - lam j)) := by
    have hgibbs : ∑ a ∈ powersetCard ℓ S, w a * (Real.log (q a) - Real.log (w a)) ≤ 0 := by
      calc ∑ a ∈ powersetCard ℓ S, w a * (Real.log (q a) - Real.log (w a))
          ≤ ∑ a ∈ powersetCard ℓ S, (q a - w a) := by
            refine sum_le_sum fun a ha => ?_
            rcases eq_or_lt_of_le (hw_nn a) with hw0 | hwpos
            · rw [← hw0, zero_mul, sub_zero]; exact hq_nn a
            · have hqpos : 0 < q a := by
                refine prod_pos fun j _ => ?_
                split_ifs with hj
                · rw [hlam_eq]
                  exact lt_of_lt_of_le hwpos (single_le_sum (fun b _ => hw_nn b)
                    (mem_filter.2 ⟨ha, hj⟩))
                · rw [hlam_compl]
                  exact lt_of_lt_of_le hwpos (single_le_sum (fun b _ => hw_nn b)
                    (mem_filter.2 ⟨ha, hj⟩))
              have hdiv := Real.log_le_sub_one_of_pos (div_pos hqpos hwpos)
              rw [Real.log_div hqpos.ne' hwpos.ne'] at hdiv
              calc w a * (Real.log (q a) - Real.log (w a))
                  ≤ w a * (q a / w a - 1) := mul_le_mul_of_nonneg_left hdiv hwpos.le
                _ = q a - w a := by field_simp
        _ = (∑ a ∈ powersetCard ℓ S, q a) - ∑ a ∈ powersetCard ℓ S, w a := sum_sub_distrib _ _
        _ ≤ 1 - 1 := by linarith [hq_sum_le, hw_sum]
        _ = 0 := sub_self 1
    have hq_log : ∑ a ∈ powersetCard ℓ S, w a * Real.log (q a) =
        ∑ j ∈ S, (lam j * Real.log (lam j) + (1 - lam j) * Real.log (1 - lam j)) := by
      have hterm : ∀ a ∈ powersetCard ℓ S, w a * Real.log (q a) =
          ∑ j ∈ S, w a * (if j ∈ a then Real.log (lam j) else Real.log (1 - lam j)) := by
        intro a ha
        rcases eq_or_lt_of_le (hw_nn a) with hw0 | hwpos
        · simp [← hw0]
        · rw [← mul_sum]
          congr 1
          have hne0 : ∀ j ∈ S, (if j ∈ a then lam j else 1 - lam j) ≠ 0 := by
            intro j _
            split_ifs with hj
            · rw [hlam_eq]
              exact (lt_of_lt_of_le hwpos (single_le_sum (fun b _ => hw_nn b)
                (mem_filter.2 ⟨ha, hj⟩))).ne'
            · rw [hlam_compl]
              exact (lt_of_lt_of_le hwpos (single_le_sum (fun b _ => hw_nn b)
                (mem_filter.2 ⟨ha, hj⟩))).ne'
          rw [Real.log_prod hne0]
          refine sum_congr rfl fun j _ => by split_ifs <;> rfl
      calc ∑ a ∈ powersetCard ℓ S, w a * Real.log (q a)
          = ∑ a ∈ powersetCard ℓ S,
              ∑ j ∈ S, w a * (if j ∈ a then Real.log (lam j) else Real.log (1 - lam j)) :=
            sum_congr rfl hterm
        _ = ∑ j ∈ S, ∑ a ∈ powersetCard ℓ S,
              w a * (if j ∈ a then Real.log (lam j) else Real.log (1 - lam j)) := sum_comm
        _ = ∑ j ∈ S, (lam j * Real.log (lam j) + (1 - lam j) * Real.log (1 - lam j)) := by
            refine sum_congr rfl fun j _ => ?_
            rw [← sum_filter_add_sum_filter_not (powersetCard ℓ S) (j ∈ ·)]
            have h1 : ∑ a ∈ (powersetCard ℓ S).filter (j ∈ ·),
                w a * (if j ∈ a then Real.log (lam j) else Real.log (1 - lam j)) =
                lam j * Real.log (lam j) := by
              rw [hlam_eq, sum_mul]
              exact sum_congr rfl fun a ha => by simp only [(mem_filter.1 ha).2, ↓reduceIte]
            have h2 : ∑ a ∈ (powersetCard ℓ S).filter (j ∉ ·),
                w a * (if j ∈ a then Real.log (lam j) else Real.log (1 - lam j)) =
                (1 - lam j) * Real.log (1 - lam j) := by
              rw [hlam_compl, sum_mul]
              exact sum_congr rfl fun a ha => by simp only [(mem_filter.1 ha).2, ↓reduceIte]
            rw [h1, h2]
    have hsplit : ∑ a ∈ powersetCard ℓ S, w a * (Real.log (q a) - Real.log (w a)) =
        (∑ a ∈ powersetCard ℓ S, w a * Real.log (q a)) +
          ∑ a ∈ powersetCard ℓ S, -(w a * Real.log (w a)) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun a _ => by ring
    rw [hsplit, hq_log] at hgibbs
    conv_rhs => rw [sum_neg_distrib]
    linarith
  -- Combine lower and upper entropy bounds with `four_pow_le_mul_choose` and quadratic KL bound.
  have hlogC : 2 * (ℓ : ℝ) * Real.log 2 - Real.log (2 * (ℓ : ℝ) + 1) ≤ Real.log C := by
    have h4 := four_pow_le_mul_choose ℓ
    have h2l_pos : (0 : ℝ) < 2 * (ℓ : ℝ) + 1 := by positivity
    have hdiv : (2 : ℝ) ^ (2 * ℓ) / (2 * (ℓ : ℝ) + 1) ≤ C := by
      rw [div_le_iff₀ h2l_pos]
      have : (2 : ℝ) ^ (2 * ℓ) = 4 ^ ℓ := by rw [pow_mul]; norm_num
      linarith
    have hlog := Real.log_le_log (by positivity) hdiv
    rw [Real.log_div (by positivity) h2l_pos.ne', Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
      at hlog
    exact hlog
  have hsum_sq : ∑ j ∈ S, (1 - 2 * lam j) ^ 2 ≤ 2 * (ℓ : ℝ) * (ε / 4) ^ 2 := by
    have h1 : ∑ j ∈ S, (1 - 2 * lam j) ^ 2 / 2 ≤
        ∑ j ∈ S, (Real.log 2 + lam j * Real.log (lam j) + (1 - lam j) * Real.log (1 - lam j)) :=
      sum_le_sum fun j _ => one_sub_two_mul_sq_div_two_le_kl_half (hlam_bounds j).1
        (hlam_bounds j).2
    have h2 : ∑ j ∈ S, (Real.log 2 + lam j * Real.log (lam j) +
          (1 - lam j) * Real.log (1 - lam j)) =
        2 * (ℓ : ℝ) * Real.log 2 -
          ∑ j ∈ S, -(lam j * Real.log (lam j) + (1 - lam j) * Real.log (1 - lam j)) := by
      rw [sum_neg_distrib, sub_neg_eq_add]
      have hconst : 2 * (ℓ : ℝ) * Real.log 2 = ∑ _j ∈ S, Real.log 2 := by
        rw [sum_const, hS_card, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
      rw [hconst, ← sum_add_distrib]
      exact sum_congr rfl fun j _ => by ring
    rw [← sum_div, h2] at h1
    have h3 : (∑ j ∈ S, (1 - 2 * lam j) ^ 2) / 2 ≤
        (δ * ℓ + 1) * Real.log 2 + Real.log (2 * (ℓ : ℝ) + 1) := by
      linarith [hent_lb, hent_ub, hlogC]
    have hδ_nat : 2 * ((δ * ℓ + 1) * Real.log 2 + Real.log (2 * (ℓ : ℝ) + 1)) =
        2 * (ℓ : ℝ) * (ε / 4) ^ 2 := by
      simp only [δ, Real.logb]
      field_simp
      ring
    linarith
  -- Apply Cauchy–Schwarz to bound `∑ j ∈ S, |1 - 2 * lam j| ≤ (2 * ℓ) * (ε / 4)`.
  have hsum_abs : ∑ j ∈ S, |1 - 2 * lam j| ≤ (2 * (ℓ : ℝ)) * (ε / 4) := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := fun j => |1 - 2 * lam j|)
    simp only [hS_card, Nat.cast_mul, Nat.cast_ofNat, sq_abs] at hcs
    have hsq : (∑ j ∈ S, |1 - 2 * lam j|) ^ 2 ≤ ((2 * (ℓ : ℝ)) * (ε / 4)) ^ 2 := by
      calc (∑ j ∈ S, |1 - 2 * lam j|) ^ 2
          ≤ (2 * (ℓ : ℝ)) * ∑ j ∈ S, (1 - 2 * lam j) ^ 2 := hcs
        _ ≤ (2 * (ℓ : ℝ)) * (2 * (ℓ : ℝ) * (ε / 4) ^ 2) :=
            mul_le_mul_of_nonneg_left hsum_sq (by positivity)
        _ = ((2 * (ℓ : ℝ)) * (ε / 4)) ^ 2 := by ring
    exact le_of_sq_le_sq hsq (by positivity)
  -- Express `Row₀`, `Row₁` in terms of `lam j` and `μf`.
  have hchoose_eq : ((2 * ℓ - 1).choose ℓ : ℝ) = C / 2 := by
    have h2 : 2 * ((2 * ℓ - 1).choose ℓ : ℝ) = C := by
      simpa only [C, Nat.cast_mul, Nat.cast_ofNat] using
        congrArg (Nat.cast (R := ℝ)) (two_mul_choose_two_mul_sub_one ℓ hℓ)
    linarith
  have hchoose_eq' : ((2 * ℓ - 1).choose (ℓ - 1) : ℝ) = C / 2 := by
    rw [← choose_two_mul_sub_one_eq ℓ hℓ, hchoose_eq]
  have hrow1_eq : ∀ j ∈ S, row1 ℓ f ⟨(insert j T₂)ᶜ, T₂, j⟩ = 2 * lam j * μf := by
    intro j _
    simp only [row1, lam, μf, hchoose_eq', S]
    field_simp
  have hrow0_eq : ∀ j ∈ S, row0 ℓ f ⟨(insert j T₂)ᶜ, T₂, j⟩ = 2 * (1 - lam j) * μf := by
    intro j _
    have hpart : powersetCard ℓ (insert j T₂)ᶜ = (powersetCard ℓ S).filter (j ∉ ·) := by
      ext a
      simp only [mem_powersetCard, mem_filter, S, subset_iff, mem_compl, mem_insert, not_or]
      exact ⟨fun ⟨hsub, hc⟩ => ⟨⟨fun x hx => (hsub hx).2, hc⟩, fun hj => (hsub hj).1 rfl⟩,
        fun ⟨⟨hsub, hc⟩, hnj⟩ => ⟨fun x hx => ⟨fun h => hnj (h ▸ hx), hsub hx⟩, hc⟩⟩
    have hsplit : ∑ a ∈ powersetCard ℓ (insert j T₂)ᶜ, f a +
        ∑ a ∈ (powersetCard ℓ S).filter (j ∈ ·), f a = Z := by
      rw [hpart, add_comm]
      exact sum_filter_add_sum_filter_not (powersetCard ℓ S) (j ∈ ·) f
    simp only [row0, lam, μf, hchoose_eq]
    have hsub : ∑ a ∈ powersetCard ℓ (insert j T₂)ᶜ, f a =
        Z - ∑ a ∈ (powersetCard ℓ S).filter (j ∈ ·), f a := by linarith
    rw [hsub]
    field_simp
  -- Compute `∑ j ∈ S, lam j = ℓ`.
  have hsum_lam : ∑ j ∈ S, lam j = ℓ := by
    simp only [lam, ← sum_div]
    have hdouble : ∑ j ∈ S, ∑ a ∈ (powersetCard ℓ S).filter (j ∈ ·), f a = (ℓ : ℝ) * Z := by
      calc ∑ j ∈ S, ∑ a ∈ (powersetCard ℓ S).filter (j ∈ ·), f a
          = ∑ j ∈ S, ∑ a ∈ powersetCard ℓ S, if j ∈ a then f a else 0 :=
            sum_congr rfl fun j _ => sum_filter _ _
        _ = ∑ a ∈ powersetCard ℓ S, ∑ j ∈ S, if j ∈ a then f a else 0 := sum_comm
        _ = ∑ a ∈ powersetCard ℓ S, (ℓ : ℝ) * f a := by
            refine sum_congr rfl fun a ha => ?_
            obtain ⟨haS, hac⟩ := mem_powersetCard.1 ha
            rw [← sum_filter, sum_const, nsmul_eq_mul,
              filter_mem_eq_inter, inter_eq_right.2 haS, hac]
        _ = (ℓ : ℝ) * Z := by rw [← mul_sum]
    rw [hdouble, mul_div_cancel_right₀ _ hZ_pos.ne']
  -- Finish by combining `hrow0_eq`, `hrow1_eq`, `hsum_abs`, and `hsum_lam`.
  have hlhs : ∑ i ∈ S, |row0 ℓ f ⟨(insert i T₂)ᶜ, T₂, i⟩ - row1 ℓ f ⟨(insert i T₂)ᶜ, T₂, i⟩| =
      2 * μf * ∑ j ∈ S, |1 - 2 * lam j| := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    rw [hrow0_eq j hj, hrow1_eq j hj]
    have : 2 * (1 - lam j) * μf - 2 * lam j * μf = (2 * μf) * (1 - 2 * lam j) := by ring
    rw [this, abs_mul, abs_of_pos (by positivity : 0 < 2 * μf)]
  have hrhs : ∑ i ∈ S, row0 ℓ f ⟨(insert i T₂)ᶜ, T₂, i⟩ = 2 * (ℓ : ℝ) * μf := by
    calc ∑ j ∈ S, row0 ℓ f ⟨(insert j T₂)ᶜ, T₂, j⟩
        = ∑ j ∈ S, (2 * μf - 2 * μf * lam j) :=
          sum_congr rfl fun j hj => by rw [hrow0_eq j hj]; ring
      _ = (2 * (ℓ : ℝ)) * (2 * μf) - 2 * μf * ∑ j ∈ S, lam j := by
          rw [sum_sub_distrib, sum_const, hS_card, nsmul_eq_mul,
            ← mul_sum, Nat.cast_mul, Nat.cast_ofNat]
      _ = 2 * (ℓ : ℝ) * μf := by rw [hsum_lam]; ring
  rw [hlhs, hrhs]
  calc 2 * μf * ∑ j ∈ S, |1 - 2 * lam j|
      ≤ 2 * μf * (2 * (ℓ : ℝ) * (ε / 4)) := mul_le_mul_of_nonneg_left hsum_abs (by positivity)
    _ = ε / 2 * (2 * (ℓ : ℝ) * μf) := by ring

end Step3

/-! ### Main rectangle corruption inequalities -/

section MainLemma

/-- **Rectangle corruption inequality (explicit finite form)**:
for `ℓ ≥ 1`, `n + 1 = 4 * ℓ`, nonnegative `f, g: Finset (Fin n) → ℝ`, and `0 < ε`,
```
  (1 - ε) * avgOn A (f · g) - avgOn B (f · g)
    ≤ maxOn (A ∪ B) (f · g) * (2 * (2 * ℓ + 1)) * 2 ^ (-(ε ^ 2 / (16 * log 2)) * ℓ).
``` -/
theorem razborov_corruption_explicit {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hn : n + 1 = 4 * ℓ)
    {f g : Finset (Fin n) → ℝ} (hf : ∀ a, 0 ≤ f a) (hg : ∀ b, 0 ≤ g b)
    {ε : ℝ} (hε : 0 < ε) :
    (1 - ε) * avgOn (disjointPairs n ℓ) (fun p => f p.1 * g p.2) -
        avgOn (uniqueInterPairs n ℓ) (fun p => f p.1 * g p.2) ≤
      maxOn (disjointPairs n ℓ ∪ uniqueInterPairs n ℓ) (fun p => f p.1 * g p.2) *
        (2 * (2 * (ℓ : ℝ) + 1)) * (2 : ℝ) ^ (-(ε ^ 2 / (16 * Real.log 2)) * ℓ) := by
  classical
  set δ : ℝ := ε ^ 2 / (16 * Real.log 2) - (1 + Real.logb 2 (2 * (ℓ : ℝ) + 1)) / ℓ
  set M_AB : ℝ := maxOn (disjointPairs n ℓ ∪ uniqueInterPairs n ℓ) (fun p => f p.1 * g p.2)
  have hℓ_pos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have h2_pow : (2 : ℝ) ^ (-δ * ℓ) =
      (2 * (2 * (ℓ : ℝ) + 1)) * (2 : ℝ) ^ (-(ε ^ 2 / (16 * Real.log 2)) * ℓ) := by
    have hexp : -δ * ℓ =
        -(ε ^ 2 / (16 * Real.log 2)) * ℓ + (1 + Real.logb 2 (2 * (ℓ : ℝ) + 1)) := by
      simp only [δ]; field_simp; ring
    rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
      Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) (by positivity)]
    ring
  -- Define `rowBig` and `colBig` predicates on partitions.
  let rowBig (T : RazPartition n) : Prop :=
    (2 : ℝ) ^ (-δ * ℓ - 1) * maxOn (powersetCard ℓ T.rightᶜ) f <
      (∑ a ∈ powersetCard ℓ T.rightᶜ, f a) / ((2 * ℓ).choose ℓ : ℝ)
  let colBig (T : RazPartition n) : Prop :=
    (2 : ℝ) ^ (-δ * ℓ - 1) * maxOn (powersetCard ℓ T.leftᶜ) g <
      (∑ b ∈ powersetCard ℓ T.leftᶜ, g b) / ((2 * ℓ).choose ℓ : ℝ)
  -- Step 3 (row & column sides): generic row-side bound, applied to `(f, g)` and swapped `(g, f)`.
  have hrow_gen : ∀ (F G : Finset (Fin n) → ℝ), (∀ a, 0 ≤ F a) → (∀ b, 0 ≤ G b) →
      ∑ T ∈ razParts n ℓ,
          (if (2 : ℝ) ^ (-δ * ℓ - 1) * maxOn (powersetCard ℓ T.rightᶜ) F <
              (∑ a ∈ powersetCard ℓ T.rightᶜ, F a) / ((2 * ℓ).choose ℓ : ℝ) then
            |row0 ℓ F T - row1 ℓ F T| * col0 ℓ G T else 0) ≤
        (ε / 2) * ∑ T ∈ razParts n ℓ, row0 ℓ F T * col0 ℓ G T := by
    intro F G hF hG
    rw [sum_razParts_by_right hn, sum_razParts_by_right hn, mul_sum]
    refine sum_le_sum fun T₂ hT₂ => ?_
    have hT₂c : T₂.card = 2 * ℓ - 1 := (mem_powersetCard.1 hT₂).2
    set c₀ : ℝ := (∑ b ∈ powersetCard ℓ T₂, G b) / ((2 * ℓ - 1).choose ℓ : ℝ)
    have hc₀_nn : 0 ≤ c₀ := div_nonneg (sum_nonneg fun b _ => hG b) (Nat.cast_nonneg _)
    by_cases hbig :
        (2 : ℝ) ^ (-δ * ℓ - 1) * maxOn (powersetCard ℓ T₂ᶜ) F <
          (∑ a ∈ powersetCard ℓ T₂ᶜ, F a) / ((2 * ℓ).choose ℓ : ℝ)
    · have h1 := sum_abs_row0_sub_row1_le hℓ hn hF hε hT₂c hbig
      calc ∑ i ∈ T₂ᶜ,
            (if (2 : ℝ) ^ (-δ * ℓ - 1) * maxOn (powersetCard ℓ T₂ᶜ) F <
                (∑ a ∈ powersetCard ℓ T₂ᶜ, F a) / ((2 * ℓ).choose ℓ : ℝ) then
              |row0 ℓ F ⟨(insert i T₂)ᶜ, T₂, i⟩ - row1 ℓ F ⟨(insert i T₂)ᶜ, T₂, i⟩| *
                col0 ℓ G ⟨(insert i T₂)ᶜ, T₂, i⟩
            else 0)
          = (∑ i ∈ T₂ᶜ,
              |row0 ℓ F ⟨(insert i T₂)ᶜ, T₂, i⟩ - row1 ℓ F ⟨(insert i T₂)ᶜ, T₂, i⟩|) * c₀ := by
            rw [sum_mul]
            exact sum_congr rfl fun i _ => by simp only [hbig, ↓reduceIte, col0, c₀]
        _ ≤ ((ε / 2) * ∑ i ∈ T₂ᶜ, row0 ℓ F ⟨(insert i T₂)ᶜ, T₂, i⟩) * c₀ :=
            mul_le_mul_of_nonneg_right h1 hc₀_nn
        _ = (ε / 2) * ∑ i ∈ T₂ᶜ,
              row0 ℓ F ⟨(insert i T₂)ᶜ, T₂, i⟩ * col0 ℓ G ⟨(insert i T₂)ᶜ, T₂, i⟩ := by
            rw [mul_assoc, sum_mul]; rfl
    · have hzero : ∑ i ∈ T₂ᶜ,
            (if (2 : ℝ) ^ (-δ * ℓ - 1) * maxOn (powersetCard ℓ T₂ᶜ) F <
                (∑ a ∈ powersetCard ℓ T₂ᶜ, F a) / ((2 * ℓ).choose ℓ : ℝ) then
              |row0 ℓ F ⟨(insert i T₂)ᶜ, T₂, i⟩ - row1 ℓ F ⟨(insert i T₂)ᶜ, T₂, i⟩| *
                col0 ℓ G ⟨(insert i T₂)ᶜ, T₂, i⟩
            else 0) = 0 :=
        sum_eq_zero fun i _ => by simp only [hbig, ↓reduceIte]
      rw [hzero]
      exact mul_nonneg (by positivity) (sum_nonneg fun i _ =>
        mul_nonneg (row0_nonneg hF _) (col0_nonneg hG _))
  have hrow_sum :
      ∑ T ∈ razParts n ℓ,
          (if rowBig T then |row0 ℓ f T - row1 ℓ f T| * col0 ℓ g T else 0) ≤
        (ε / 2) * ∑ T ∈ razParts n ℓ, row0 ℓ f T * col0 ℓ g T :=
    hrow_gen f g hf hg
  have hcol_sum :
      ∑ T ∈ razParts n ℓ,
          (if colBig T then row0 ℓ f T * |col0 ℓ g T - col1 ℓ g T| else 0) ≤
        (ε / 2) * ∑ T ∈ razParts n ℓ, row0 ℓ f T * col0 ℓ g T := by
    have hsw1 : ∑ T ∈ razParts n ℓ,
          (if colBig T then row0 ℓ f T * |col0 ℓ g T - col1 ℓ g T| else 0) =
        ∑ T ∈ razParts n ℓ,
          (if (2 : ℝ) ^ (-δ * ℓ - 1) * maxOn (powersetCard ℓ T.rightᶜ) g <
              (∑ b ∈ powersetCard ℓ T.rightᶜ, g b) / ((2 * ℓ).choose ℓ : ℝ) then
            |row0 ℓ g T - row1 ℓ g T| * col0 ℓ f T else 0) := by
      rw [sum_razParts_swap]
      exact sum_congr rfl fun T _ => by simp only [colBig, row0, row1, col0, col1, mul_comm]
    have hsw2 : ∑ T ∈ razParts n ℓ, row0 ℓ f T * col0 ℓ g T =
        ∑ T ∈ razParts n ℓ, row0 ℓ g T * col0 ℓ f T := by
      rw [sum_razParts_swap]
      exact sum_congr rfl fun T _ => by simp only [row0, col0, mul_comm]
    rw [hsw1, hsw2]
    exact hrow_gen g f hg hf
  -- Step 4 (small case): when `¬(rowBig T ∧ colBig T)`, `row0 * col0 ≤ 2^(-δ*ℓ) * M_AB`.
  have hsmall_pt : ∀ T ∈ razParts n ℓ, ¬(rowBig T ∧ colBig T) →
      row0 ℓ f T * col0 ℓ g T ≤ M_AB * (2 : ℝ) ^ (-δ * ℓ) := by
    intro T hT hnot
    obtain ⟨_, _, hdisj, h4, h5⟩ := mem_razParts.1 hT
    have hchoose_pos : (0 : ℝ) < ((2 * ℓ - 1).choose ℓ : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : ℓ ≤ 2 * ℓ - 1)
    have h2choose : 2 * ((2 * ℓ - 1).choose ℓ : ℝ) = ((2 * ℓ).choose ℓ : ℝ) := by
      exact_mod_cast two_mul_choose_two_mul_sub_one ℓ hℓ
    have hpow_mul : 2 * (2 : ℝ) ^ (-δ * ℓ - 1) = (2 : ℝ) ^ (-δ * ℓ) := by
      rw [show -δ * ℓ - 1 = (-δ * ℓ) + (-1) by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        Real.rpow_neg_one]
      ring
    have hnot' : ¬rowBig T ∨ ¬colBig T := not_and_or.1 hnot
    rcases hnot' with hnr | hnc
    · dsimp only [rowBig] at hnr; push Not at hnr
      have hrow_le : row0 ℓ f T ≤ (2 : ℝ) ^ (-δ * ℓ) * maxOn (powersetCard ℓ T.rightᶜ) f := by
        have hsub : powersetCard ℓ T.left ⊆ powersetCard ℓ T.rightᶜ :=
          powersetCard_mono (subset_compl_iff_disjoint_right.2 hdisj)
        have hsum_le : ∑ a ∈ powersetCard ℓ T.left, f a ≤ ∑ a ∈ powersetCard ℓ T.rightᶜ, f a :=
          sum_le_sum_of_subset_of_nonneg hsub fun a _ _ => hf a
        have hr0 : row0 ℓ f T ≤ 2 * ((∑ a ∈ powersetCard ℓ T.rightᶜ, f a) /
            ((2 * ℓ).choose ℓ : ℝ)) := by
          rw [row0, ← h2choose]
          have : (∑ a ∈ powersetCard ℓ T.left, f a) / ((2 * ℓ - 1).choose ℓ : ℝ) =
              2 * ((∑ a ∈ powersetCard ℓ T.left, f a) / (2 * ((2 * ℓ - 1).choose ℓ : ℝ))) := by
            field_simp
          rw [this]
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum_le (by positivity))
            (by norm_num)
        calc row0 ℓ f T
            ≤ 2 * ((2 : ℝ) ^ (-δ * ℓ - 1) * maxOn (powersetCard ℓ T.rightᶜ) f) :=
              hr0.trans (mul_le_mul_of_nonneg_left hnr (by norm_num))
          _ = (2 : ℝ) ^ (-δ * ℓ) * maxOn (powersetCard ℓ T.rightᶜ) f := by
              rw [← mul_assoc, hpow_mul]
      have hcol_le : col0 ℓ g T ≤ maxOn (powersetCard ℓ T.right) g := by
        rw [col0, div_le_iff₀ hchoose_pos]
        calc ∑ b ∈ powersetCard ℓ T.right, g b
            ≤ ∑ _b ∈ powersetCard ℓ T.right, maxOn (powersetCard ℓ T.right) g :=
              sum_le_sum fun b hb => le_maxOn hb
          _ = maxOn (powersetCard ℓ T.right) g * ((2 * ℓ - 1).choose ℓ : ℝ) := by
              rw [sum_const, nsmul_eq_mul, card_powersetCard, h5, mul_comm]
      have hprod_le :
          maxOn (powersetCard ℓ T.rightᶜ) f * maxOn (powersetCard ℓ T.right) g ≤ M_AB := by
        have hne1 : (powersetCard ℓ T.rightᶜ).Nonempty := by
          rw [← card_pos, card_powersetCard, card_compl, Fintype.card_fin, h5]
          exact Nat.choose_pos (by omega)
        have hne2 : (powersetCard ℓ T.right).Nonempty := by
          rw [← card_pos, card_powersetCard, h5]
          exact Nat.choose_pos (by omega)
        obtain ⟨a, ha, ha_eq⟩ := exists_mem_eq_sup' hne1 f
        obtain ⟨b, hb, hb_eq⟩ := exists_mem_eq_sup' hne2 g
        simp only [maxOn, hne1, hne2, ↓reduceDIte, ha_eq, hb_eq]
        obtain ⟨haS, hac⟩ := mem_powersetCard.1 ha
        obtain ⟨hbS, hbc⟩ := mem_powersetCard.1 hb
        have hab_disj : Disjoint a b :=
          disjoint_left.2 fun x hxa hxb => (mem_compl.1 (haS hxa)) (hbS hxb)
        exact le_maxOn (X := fun p => f p.1 * g p.2) (x := (a, b))
          (mem_union_left (uniqueInterPairs n ℓ) (mem_disjointPairs_iff.2 ⟨hac, hbc, hab_disj⟩))
      calc row0 ℓ f T * col0 ℓ g T
          ≤ ((2 : ℝ) ^ (-δ * ℓ) * maxOn (powersetCard ℓ T.rightᶜ) f) *
              maxOn (powersetCard ℓ T.right) g :=
            mul_le_mul hrow_le hcol_le (col0_nonneg hg T) (by
              exact mul_nonneg (by positivity) (maxOn_nonneg fun a _ => hf a))
        _ = (maxOn (powersetCard ℓ T.rightᶜ) f * maxOn (powersetCard ℓ T.right) g) *
              (2 : ℝ) ^ (-δ * ℓ) := by ring
        _ ≤ M_AB * (2 : ℝ) ^ (-δ * ℓ) := mul_le_mul_of_nonneg_right hprod_le (by positivity)
    · dsimp only [colBig] at hnc; push Not at hnc
      have hcol_le : col0 ℓ g T ≤ (2 : ℝ) ^ (-δ * ℓ) * maxOn (powersetCard ℓ T.leftᶜ) g := by
        have hsub : powersetCard ℓ T.right ⊆ powersetCard ℓ T.leftᶜ :=
          powersetCard_mono (subset_compl_iff_disjoint_right.2 hdisj.symm)
        have hsum_le : ∑ b ∈ powersetCard ℓ T.right, g b ≤ ∑ b ∈ powersetCard ℓ T.leftᶜ, g b :=
          sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => hg b
        have hc0 : col0 ℓ g T ≤ 2 * ((∑ b ∈ powersetCard ℓ T.leftᶜ, g b) /
            ((2 * ℓ).choose ℓ : ℝ)) := by
          rw [col0, ← h2choose]
          have : (∑ b ∈ powersetCard ℓ T.right, g b) / ((2 * ℓ - 1).choose ℓ : ℝ) =
              2 * ((∑ b ∈ powersetCard ℓ T.right, g b) / (2 * ((2 * ℓ - 1).choose ℓ : ℝ))) := by
            field_simp
          rw [this]
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum_le (by positivity))
            (by norm_num)
        calc col0 ℓ g T
            ≤ 2 * ((2 : ℝ) ^ (-δ * ℓ - 1) * maxOn (powersetCard ℓ T.leftᶜ) g) :=
              hc0.trans (mul_le_mul_of_nonneg_left hnc (by norm_num))
          _ = (2 : ℝ) ^ (-δ * ℓ) * maxOn (powersetCard ℓ T.leftᶜ) g := by
              rw [← mul_assoc, hpow_mul]
      have hrow_le : row0 ℓ f T ≤ maxOn (powersetCard ℓ T.left) f := by
        rw [row0, div_le_iff₀ hchoose_pos]
        calc ∑ a ∈ powersetCard ℓ T.left, f a
            ≤ ∑ _a ∈ powersetCard ℓ T.left, maxOn (powersetCard ℓ T.left) f :=
              sum_le_sum fun a ha => le_maxOn ha
          _ = maxOn (powersetCard ℓ T.left) f * ((2 * ℓ - 1).choose ℓ : ℝ) := by
              rw [sum_const, nsmul_eq_mul, card_powersetCard, h4, mul_comm]
      have hprod_le :
          maxOn (powersetCard ℓ T.left) f * maxOn (powersetCard ℓ T.leftᶜ) g ≤ M_AB := by
        have hne1 : (powersetCard ℓ T.left).Nonempty := by
          rw [← card_pos, card_powersetCard, h4]
          exact Nat.choose_pos (by omega)
        have hne2 : (powersetCard ℓ T.leftᶜ).Nonempty := by
          rw [← card_pos, card_powersetCard, card_compl, Fintype.card_fin, h4]
          exact Nat.choose_pos (by omega)
        obtain ⟨a, ha, ha_eq⟩ := exists_mem_eq_sup' hne1 f
        obtain ⟨b, hb, hb_eq⟩ := exists_mem_eq_sup' hne2 g
        simp only [maxOn, hne1, hne2, ↓reduceDIte, ha_eq, hb_eq]
        obtain ⟨haS, hac⟩ := mem_powersetCard.1 ha
        obtain ⟨hbS, hbc⟩ := mem_powersetCard.1 hb
        have hab_disj : Disjoint a b :=
          disjoint_left.2 fun x hxa hxb => (mem_compl.1 (hbS hxb)) (haS hxa)
        exact le_maxOn (X := fun p => f p.1 * g p.2) (x := (a, b))
          (mem_union_left (uniqueInterPairs n ℓ) (mem_disjointPairs_iff.2 ⟨hac, hbc, hab_disj⟩))
      calc row0 ℓ f T * col0 ℓ g T
          ≤ maxOn (powersetCard ℓ T.left) f *
              ((2 : ℝ) ^ (-δ * ℓ) * maxOn (powersetCard ℓ T.leftᶜ) g) :=
            mul_le_mul hrow_le hcol_le (col0_nonneg hg T) (maxOn_nonneg fun a _ => hf a)
        _ = (maxOn (powersetCard ℓ T.left) f * maxOn (powersetCard ℓ T.leftᶜ) g) *
              (2 : ℝ) ^ (-δ * ℓ) := by ring
        _ ≤ M_AB * (2 : ℝ) ^ (-δ * ℓ) := mul_le_mul_of_nonneg_right hprod_le (by positivity)
  -- Combine Steps 1–4 over all partitions `T ∈ razParts n ℓ`.
  have hsum_all :
      ∑ T ∈ razParts n ℓ, (row0 ℓ f T * col0 ℓ g T - row1 ℓ f T * col1 ℓ g T) ≤
        ε * ∑ T ∈ razParts n ℓ, row0 ℓ f T * col0 ℓ g T +
          ((razParts n ℓ).card : ℝ) * (M_AB * (2 : ℝ) ^ (-δ * ℓ)) := by
    have hpt : ∀ T ∈ razParts n ℓ,
        row0 ℓ f T * col0 ℓ g T - row1 ℓ f T * col1 ℓ g T ≤
          (if rowBig T then |row0 ℓ f T - row1 ℓ f T| * col0 ℓ g T else 0) +
          (if colBig T then row0 ℓ f T * |col0 ℓ g T - col1 ℓ g T| else 0) +
          M_AB * (2 : ℝ) ^ (-δ * ℓ) := by
      intro T hT
      have hMnn : 0 ≤ M_AB * (2 : ℝ) ^ (-δ * ℓ) :=
        mul_nonneg (maxOn_nonneg fun p _ => mul_nonneg (hf p.1) (hg p.2)) (by positivity)
      by_cases hboth : rowBig T ∧ colBig T
      · simp only [hboth.1, hboth.2, ↓reduceIte]
        have hrect := rectangle_diff_le (row0_nonneg (ℓ := ℓ) hf T) (row1_nonneg (ℓ := ℓ) hf T)
          (col0_nonneg (ℓ := ℓ) hg T) (col1_nonneg (ℓ := ℓ) hg T)
        linarith
      · have hs := hsmall_pt T hT hboth
        have h1 : 0 ≤ if rowBig T then |row0 ℓ f T - row1 ℓ f T| * col0 ℓ g T else 0 := by
          split_ifs
          · exact mul_nonneg (abs_nonneg _) (col0_nonneg hg T)
          · exact le_rfl
        have h2 : 0 ≤ if colBig T then row0 ℓ f T * |col0 ℓ g T - col1 ℓ g T| else 0 := by
          split_ifs
          · exact mul_nonneg (row0_nonneg hf T) (abs_nonneg _)
          · exact le_rfl
        have hr1c1 : 0 ≤ row1 ℓ f T * col1 ℓ g T :=
          mul_nonneg (row1_nonneg hf T) (col1_nonneg hg T)
        linarith
    calc ∑ T ∈ razParts n ℓ, (row0 ℓ f T * col0 ℓ g T - row1 ℓ f T * col1 ℓ g T)
        ≤ ∑ T ∈ razParts n ℓ,
            ((if rowBig T then |row0 ℓ f T - row1 ℓ f T| * col0 ℓ g T else 0) +
            (if colBig T then row0 ℓ f T * |col0 ℓ g T - col1 ℓ g T| else 0) +
            M_AB * (2 : ℝ) ^ (-δ * ℓ)) := sum_le_sum hpt
      _ = (∑ T ∈ razParts n ℓ,
            if rowBig T then |row0 ℓ f T - row1 ℓ f T| * col0 ℓ g T else 0) +
          (∑ T ∈ razParts n ℓ,
            if colBig T then row0 ℓ f T * |col0 ℓ g T - col1 ℓ g T| else 0) +
          ((razParts n ℓ).card : ℝ) * (M_AB * (2 : ℝ) ^ (-δ * ℓ)) := by
          simp only [sum_add_distrib, sum_const, nsmul_eq_mul]
      _ ≤ (ε / 2) * ∑ T ∈ razParts n ℓ, row0 ℓ f T * col0 ℓ g T +
          (ε / 2) * ∑ T ∈ razParts n ℓ, row0 ℓ f T * col0 ℓ g T +
          ((razParts n ℓ).card : ℝ) * (M_AB * (2 : ℝ) ^ (-δ * ℓ)) := by
          linarith [hrow_sum, hcol_sum]
      _ = ε * ∑ T ∈ razParts n ℓ, row0 ℓ f T * col0 ℓ g T +
          ((razParts n ℓ).card : ℝ) * (M_AB * (2 : ℝ) ^ (-δ * ℓ)) := by ring
  -- Divide by `|(razParts n ℓ)| > 0` and substitute Step 1 identities.
  have hPpos : (0 : ℝ) < ((razParts n ℓ).card : ℝ) := by
    exact_mod_cast (razParts_nonempty hℓ hn).card_pos
  have hdiv := div_le_div_of_nonneg_right hsum_all hPpos.le
  rw [sum_sub_distrib, sub_div, add_div, mul_div_assoc, mul_div_cancel_left₀ _ hPpos.ne'] at hdiv
  change avgOn (razParts n ℓ) (fun T => row0 ℓ f T * col0 ℓ g T) -
      avgOn (razParts n ℓ) (fun T => row1 ℓ f T * col1 ℓ g T) ≤
      ε * avgOn (razParts n ℓ) (fun T => row0 ℓ f T * col0 ℓ g T) +
        M_AB * (2 : ℝ) ^ (-δ * ℓ) at hdiv
  rw [avg_row0_mul_col0_eq_avg_A hℓ hn f g, avg_row1_mul_col1_eq_avg_B hℓ hn f g, h2_pow] at hdiv
  linarith

/-- **Rectangle corruption inequality (asymptotic form)**:
for every `n ≡ 3 (mod 4)` with `ℓ = (n + 1) / 4 ≥ 2`, every distribution `μ` supported on `A ∪ B`
that is uniform conditioned on `A` and on `B`, every nonnegative `f, g: Finset (Fin n) → ℝ`, and
every `0 < ε < 1`:
```
  (1 - ε) * E_μ[f(a) g(b) | A] - E_μ[f(a) g(b) | B]
    ≤ max_{(a, b) ∈ A ∪ B} (f(a) g(b)) * 2 ^ (-(ε ^ 2 / (16 * log 2)) * ℓ + C * log ℓ)
```
with an absolute constant `C` (`C = 4 / log 2` for natural `Real.log`, or `C = 4` for `log₂`). -/
theorem razborov_corruption_lemma :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), n % 4 = 3 → 2 ≤ (n + 1) / 4 →
      ∀ (μ : PMF (Finset (Fin n) × Finset (Fin n))), IsRazborovDist n ((n + 1) / 4) μ →
      ∀ (f g : Finset (Fin n) → ℝ), (∀ a, 0 ≤ f a) → (∀ b, 0 ≤ g b) →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        let ℓ := (n + 1) / 4
        let X : Finset (Fin n) × Finset (Fin n) → ℝ := fun p => f p.1 * g p.2
        (1 - ε) * condExpectPMF μ (disjointPairs n ℓ) X -
            condExpectPMF μ (uniqueInterPairs n ℓ) X ≤
          maxOn (disjointPairs n ℓ ∪ uniqueInterPairs n ℓ) X *
            (2 : ℝ) ^ (-(ε ^ 2 / (16 * Real.log 2)) * ℓ + C * Real.log ℓ) := by
  refine ⟨4 / Real.log 2, div_pos (by norm_num) (Real.log_pos (by norm_num)),
    fun n hn hℓ2 μ hμ f g hf hg ε hε _ => ?_⟩
  intro ℓ X
  have hℓ1 : 1 ≤ ℓ := by omega
  have hn4 : n + 1 = 4 * ℓ := by omega
  obtain ⟨_, hApos, hBpos, hAunif, hBunif⟩ := hμ
  rw [condExpectPMF_eq_avgOn X hApos hAunif, condExpectPMF_eq_avgOn X hBpos hBunif]
  have hexp := razborov_corruption_explicit hℓ1 hn4 hf hg hε
  have hℓr : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ2
  have hpoly : 2 * (2 * (ℓ : ℝ) + 1) ≤ (2 : ℝ) ^ (4 / Real.log 2 * Real.log ℓ) := by
    have hpow : (2 : ℝ) ^ (4 / Real.log 2 * Real.log ℓ) = (ℓ : ℝ) ^ (4 : ℕ) := by
      have heq : 4 / Real.log 2 * Real.log ℓ = Real.logb 2 ℓ * ((4 : ℕ) : ℝ) := by
        rw [Real.logb]; push_cast; ring
      rw [heq, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) (by positivity),
        Real.rpow_natCast]
    rw [hpow]
    nlinarith [sq_nonneg ((ℓ : ℝ) - 2)]
  have hMnn : 0 ≤ maxOn (disjointPairs n ℓ ∪ uniqueInterPairs n ℓ) X :=
    maxOn_nonneg fun p _ => mul_nonneg (hf p.1) (hg p.2)
  calc (1 - ε) * avgOn (disjointPairs n ℓ) X - avgOn (uniqueInterPairs n ℓ) X
      ≤ maxOn (disjointPairs n ℓ ∪ uniqueInterPairs n ℓ) X *
          (2 * (2 * (ℓ : ℝ) + 1)) * (2 : ℝ) ^ (-(ε ^ 2 / (16 * Real.log 2)) * ℓ) := hexp
    _ ≤ maxOn (disjointPairs n ℓ ∪ uniqueInterPairs n ℓ) X *
          (2 : ℝ) ^ (4 / Real.log 2 * Real.log ℓ) *
          (2 : ℝ) ^ (-(ε ^ 2 / (16 * Real.log 2)) * ℓ) := by
        gcongr
    _ = maxOn (disjointPairs n ℓ ∪ uniqueInterPairs n ℓ) X *
          (2 : ℝ) ^ (-(ε ^ 2 / (16 * Real.log 2)) * ℓ + 4 / Real.log 2 * Real.log ℓ) := by
        rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_comm]

end MainLemma

end CslibFrontier.Communication.Nondeterministic
