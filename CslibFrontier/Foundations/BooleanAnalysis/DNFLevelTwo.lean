module

public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.Data.BitString.PartialAssignment
public import CslibFrontier.Logics.Propositional.DNF
public import CslibFrontier.Probability.Product
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import CslibFrontier.Computability.DecisionTree.CanonicalTree
import CslibFrontier.Computability.DecisionTree.Switching
import CslibFrontier.Foundations.BooleanAnalysis.FourierRestriction
import CslibFrontier.Foundations.Data.BitString.PartialAssignment.Counting
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Level-2 Fourier Mass Bounds for Bounded-Width DNFs and Multilinear Derivatives

This module establishes level-`k` Fourier `L_1` bounds for decision trees, level-2 Fourier `L_1`
bounds for bounded-width DNFs via the switching lemma, and random-restriction bounds for multilinear
extension derivatives on `[-1/2, 1/2]^ι`:

1. Every function `f : (ι → Bool) → ℝ` with `|f x| ≤ 1` computed by a decision tree of depth `d`
   satisfies `∑_{|S| = k} |f̂(S)| ≤ C(d, k)`.
2. Every width-`w` DNF formula `F` (`w ≥ 1`) satisfies `∑_{|S| = 2} |(1_F)^(S)| ≤ 4608 * w^2`,
   independently of the number of terms and the number of variables.
3. Exact finite-difference Taylor expansion for the multilinear extension `multilinearExt`, product
   Bernoulli rounding identity `expect_prodBernPMF_eq_multilinearExt`, pointwise derivative bound
   `|∂_S f_multi(z)| ≤ 2 ^ #S`, and level-2 DNF derivative bound
   `∑_{|S| = 2} |∂_S (1_F)_multi(z)| ≤ 18432 * w^2` for all `z ∈ [-1/2, 1/2]^ι`.

## Main definitions

* `CslibFrontier.Foundations.BooleanAnalysis.fourierL1`: level-`k` Fourier `L_1` mass.
* `CslibFrontier.Foundations.BooleanAnalysis.dnfInd`: `{0, 1}`-valued real indicator of a DNF.
* `CslibFrontier.Foundations.BooleanAnalysis.multilinearExt`,
  `CslibFrontier.Foundations.BooleanAnalysis.multilinearDeriv`: multilinear extension and partial
  derivatives on `ℝ^ι`.
* `CslibFrontier.Foundations.BooleanAnalysis.signBernPMF`,
  `CslibFrontier.Foundations.BooleanAnalysis.prodBernPMF`: product Bernoulli rounding on
  `[-1, 1]^ι`.

## Main results

* `CslibFrontier.Foundations.BooleanAnalysis.fourierL1_le_choose_depth`,
  `CslibFrontier.Foundations.BooleanAnalysis.fourierL1_le_choose_complexity`
* `CslibFrontier.Foundations.BooleanAnalysis.fourierL1_dnf_two_le`
* `CslibFrontier.Foundations.BooleanAnalysis.expect_prodBernPMF_eq_multilinearExt`
* `CslibFrontier.Foundations.BooleanAnalysis.multilinearExt_add_sub_eq_sum_deriv`
* `CslibFrontier.Foundations.BooleanAnalysis.abs_multilinearDeriv_le`
* `CslibFrontier.Foundations.BooleanAnalysis.sum_abs_multilinearDeriv_dnf_two_le`
-/

public section

namespace CslibFrontier.Foundations.BooleanAnalysis

open Finset Cslib Cslib.BitString Cslib.DecisionTree Cslib.Logic.PL Cslib.Probability
open scoped BigOperators ENNReal NNReal

/-! ### : Decision-Tree Fourier `L_{1, k}` Bound -/

/-- Level-`k` Fourier `L₁` mass `∑_{|S| = k} |f̂(S)|` of a real function on the Boolean cube. -/
@[expose] noncomputable def fourierL1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => #S = k), |fourierCoeff f S|

/-- `{0, 1}`-valued real indicator of a DNF formula `F`. -/
@[expose] def dnfInd {ι : Type*} (F : DNF ι) (x : ι → Bool) : ℝ :=
  if DNF.eval x F then 1 else 0

/-- Hardwire coordinate `i` of a decision tree to Boolean value `b`. -/
def dtRestrict {ι β : Type*} [DecidableEq ι] (i : ι) (b : Bool) :
    DecisionTree ι β → DecisionTree ι β
  | .leaf v => .leaf v
  | .node j t₀ t₁ =>
    if j = i then if b then dtRestrict i b t₁ else dtRestrict i b t₀
    else .node j (dtRestrict i b t₀) (dtRestrict i b t₁)

private theorem dtRestrict_depth_le {ι β : Type*} [DecidableEq ι] (i : ι) (b : Bool)
    (t : DecisionTree ι β) : (dtRestrict i b t).depth ≤ t.depth := by
  induction t with
  | leaf v => simp [dtRestrict]
  | node j t₀ t₁ ih₀ ih₁ =>
    simp only [dtRestrict, DecisionTree.depth_node]
    by_cases hji : j = i
    · simp only [hji, ↓reduceIte]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    · simp only [hji, ↓reduceIte, DecisionTree.depth_node]; omega

private theorem dtRestrict_eval {ι β : Type*} [DecidableEq ι] (i : ι) (b : Bool)
    (t : DecisionTree ι β) (x : ι → Bool) :
    (dtRestrict i b t).eval x = t.eval (Function.update x i b) := by
  induction t with
  | leaf v => rfl
  | node j t₀ t₁ ih₀ ih₁ =>
    simp only [dtRestrict, DecisionTree.eval_node]
    by_cases hji : j = i
    · subst hji
      simp only [↓reduceIte, Function.update_self]
      cases b <;> simp [ih₀, ih₁]
    · simp only [hji, ↓reduceIte, DecisionTree.eval_node, Function.update_of_ne hji, ih₀, ih₁]

private theorem fourierCoeff_eq_zero_of_indep {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : (ι → Bool) → ℝ} {i : ι} (hg : ∀ x b, g (Function.update x i b) = g x)
    {S : Finset ι} (hi : i ∈ S) : fourierCoeff g S = 0 := by
  let flip : (ι → Bool) ≃ (ι → Bool) :=
    { toFun := fun x => Function.update x i (!x i)
      invFun := fun x => Function.update x i (!x i)
      left_inv := fun x => by
        funext j; by_cases h : j = i
        · subst h; simp
        · simp [Function.update_of_ne h]
      right_inv := fun x => by
        funext j; by_cases h : j = i
        · subst h; simp
        · simp [Function.update_of_ne h] }
  have hneg : fourierCoeff g S = -fourierCoeff g S := by
    unfold fourierCoeff
    rw [← Finset.expect_neg_distrib]
    refine Fintype.expect_equiv flip _ _ fun x => ?_
    change g x * chi ℝ S x =
      -(g (Function.update x i (!x i)) * chi ℝ S (Function.update x i (!x i)))
    rw [hg x (!x i), chi_update_of_mem hi x (!x i)]
    have hchi : chi ℝ S x = (-1 : ℝ) ^ (x i).toNat * chi ℝ (S.erase i) x := by
      have := chi_update_of_mem (R := ℝ) hi x (x i)
      rwa [Function.update_eq_self] at this
    rw [hchi]
    cases x i <;> simp
  linarith

/-- **Decision-tree Fourier `L_{1, k}` bound**: any real function `t.eval` computed by a decision
tree `t` of depth `d` with values in `[-1, 1]` satisfies `fourierL1 t.eval k ≤ C(d, k)`. -/
theorem fourierL1_le_choose_depth {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ (d : ℕ) (t : DecisionTree ι ℝ), t.depth ≤ d → (∀ x, |t.eval x| ≤ 1) →
      ∀ k : ℕ, fourierL1 t.eval k ≤ (d.choose k : ℝ)
  | d, .leaf c, _, hbd, k => by
    have hc : |c| ≤ 1 := hbd (fun _ => false)
    have hev : (DecisionTree.leaf c : DecisionTree ι ℝ).eval = fun _ => c := rfl
    cases k with
    | zero =>
      have hfilt : (Finset.univ : Finset (Finset ι)).filter (fun S => #S = 0) = {∅} := by
        ext S; simp [Finset.card_eq_zero]
      rw [fourierL1, hfilt, Finset.sum_singleton, hev, fourierCoeff_const, ite_eq_left rfl,
        Nat.choose_zero_right, Nat.cast_one]
      exact hc
    | succ k' =>
      have hzero : fourierL1 (DecisionTree.leaf c : DecisionTree ι ℝ).eval (k' + 1) = 0 := by
        refine Finset.sum_eq_zero fun S hS => ?_
        have hne : S ≠ ∅ := by
          intro h; subst h; simp at hS
        rw [hev, fourierCoeff_const, ite_eq_right hne, abs_zero]
      rw [hzero]; positivity
  | 0, .node _ _ _, hd, _, _ => by simp at hd
  | d + 1, .node i t₀ t₁, hd, hbd, k => by
    simp only [DecisionTree.depth_node] at hd
    let u₀ := dtRestrict i false t₀
    let u₁ := dtRestrict i true t₁
    have hu₀_d : u₀.depth ≤ d := (dtRestrict_depth_le i false t₀).trans (by omega)
    have hu₁_d : u₁.depth ≤ d := (dtRestrict_depth_le i true t₁).trans (by omega)
    have hu₀_ind : ∀ x b, u₀.eval (Function.update x i b) = u₀.eval x := fun x b => by
      simp [u₀, dtRestrict_eval]
    have hu₁_ind : ∀ x b, u₁.eval (Function.update x i b) = u₁.eval x := fun x b => by
      simp [u₁, dtRestrict_eval]
    have hu₀_bd : ∀ x, |u₀.eval x| ≤ 1 := fun x => by
      have h1 := hbd (Function.update x i false)
      simpa [u₀, dtRestrict_eval] using h1
    have hu₁_bd : ∀ x, |u₁.eval x| ≤ 1 := fun x => by
      have h1 := hbd (Function.update x i true)
      simpa [u₁, dtRestrict_eval] using h1
    have heval : ∀ x, (DecisionTree.node i t₀ t₁).eval x =
        ((1 / 2 : ℝ) * (u₀.eval x + u₁.eval x)) +
          chi ℝ {i} x * ((1 / 2 : ℝ) * (u₀.eval x - u₁.eval x)) := fun x => by
      simp only [DecisionTree.eval_node, chi_singleton]
      have h0 : u₀.eval x = t₀.eval (Function.update x i false) := dtRestrict_eval i false t₀ x
      have h1 : u₁.eval x = t₁.eval (Function.update x i true) := dtRestrict_eval i true t₁ x
      cases hx : x i
      · have hup : Function.update x i false = x := by rw [← hx, Function.update_eq_self]
        rw [h0, hup]; simp [signVal]; ring
      · have hup : Function.update x i true = x := by rw [← hx, Function.update_eq_self]
        rw [h1, hup]; simp [signVal]; ring
    have hcoeff : ∀ S : Finset ι, fourierCoeff (DecisionTree.node i t₀ t₁).eval S =
        if i ∈ S then (1 / 2 : ℝ) * (fourierCoeff u₀.eval (S.erase i) -
          fourierCoeff u₁.eval (S.erase i))
        else (1 / 2 : ℝ) * (fourierCoeff u₀.eval S + fourierCoeff u₁.eval S) := fun S => by
      have hfun : (DecisionTree.node i t₀ t₁).eval =
          fun x => (1 / 2 : ℝ) * (u₀.eval x + u₁.eval x) +
            chi ℝ {i} x * ((1 / 2 : ℝ) * (u₀.eval x - u₁.eval x)) := funext heval
      rw [hfun, fourierCoeff_add, fourierCoeff_const_mul, fourierCoeff_add,
        fourierCoeff_chi_mul, fourierCoeff_const_mul, fourierCoeff_sub]
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi, fourierCoeff_eq_zero_of_indep hu₀_ind hi,
          fourierCoeff_eq_zero_of_indep hu₁_ind hi]
        have hsd : symmDiff ({i} : Finset ι) S = S.erase i := by
          ext j; simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
          by_cases hji : j = i
          · subst hji; simp [hi]
          · simp [hji]
        rw [hsd]; ring
      · rw [ite_eq_right hi]
        have him : i ∈ symmDiff ({i} : Finset ι) S := by
          simp [Finset.mem_symmDiff, hi]
        rw [fourierCoeff_eq_zero_of_indep hu₀_ind him, fourierCoeff_eq_zero_of_indep hu₁_ind him]
        ring
    cases k with
    | zero =>
      have hfilt : (Finset.univ : Finset (Finset ι)).filter (fun S => #S = 0) = {∅} := by
        ext S; simp [Finset.card_eq_zero]
      simp only [fourierL1, hfilt, Finset.sum_singleton, Nat.choose_zero_right, Nat.cast_one]
      exact (abs_fourierCoeff_le_expect_abs _ _).trans
        ((expect_le_expect fun x _ => hbd x).trans_eq (expect_const Finset.univ_nonempty 1))
    | succ k' =>
      rw [fourierL1, ← Finset.sum_filter_add_sum_filter_not _ (fun S : Finset ι => i ∈ S)]
      have hpart1 :
          ∑ S ∈ ((Finset.univ : Finset (Finset ι)).filter (fun S => #S = k' + 1)).filter
              (fun S => i ∈ S),
            |fourierCoeff (DecisionTree.node i t₀ t₁).eval S| ≤ (d.choose k' : ℝ) := by
        have h1 :
            ∑ S ∈ ((Finset.univ : Finset (Finset ι)).filter (fun S => #S = k' + 1)).filter
                (fun S => i ∈ S),
              |fourierCoeff (DecisionTree.node i t₀ t₁).eval S| ≤
            ∑ S ∈ ((Finset.univ : Finset (Finset ι)).filter (fun S => #S = k' + 1)).filter
                (fun S => i ∈ S),
              (1 / 2 : ℝ) * (|fourierCoeff u₀.eval (S.erase i)| +
                |fourierCoeff u₁.eval (S.erase i)|) := by
          refine Finset.sum_le_sum fun S hS => ?_
          have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
          rw [hcoeff S, ite_eq_left hiS, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          gcongr
          exact abs_sub _ _
        have h2 :
            ∑ S ∈ ((Finset.univ : Finset (Finset ι)).filter (fun S => #S = k' + 1)).filter
                (fun S => i ∈ S),
              (1 / 2 : ℝ) * (|fourierCoeff u₀.eval (S.erase i)| +
                |fourierCoeff u₁.eval (S.erase i)|) ≤
            ∑ T ∈ (Finset.univ : Finset (Finset ι)).filter (fun T => #T = k'),
              (1 / 2 : ℝ) * (|fourierCoeff u₀.eval T| + |fourierCoeff u₁.eval T|) := by
          rw [← Finset.sum_image (g := fun S : Finset ι => S.erase i) (f := fun T =>
              (1 / 2 : ℝ) * (|fourierCoeff u₀.eval T| + |fourierCoeff u₁.eval T|))
            (fun S₁ h₁ S₂ h₂ hEq => by
              have hi₁ : i ∈ S₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp h₁)).2
              have hi₂ : i ∈ S₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp h₂)).2
              dsimp only at hEq
              rw [← Finset.insert_erase hi₁, ← Finset.insert_erase hi₂, hEq])]
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun T hT => ?_) (fun _ _ _ => by positivity)
          obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
          obtain ⟨hSc, hiS⟩ := Finset.mem_filter.mp hS
          have hcard := (Finset.mem_filter.mp hSc).2
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [Finset.card_erase_of_mem hiS, hcard]; omega
        have h3 :
            ∑ T ∈ (Finset.univ : Finset (Finset ι)).filter (fun T => #T = k'),
              (1 / 2 : ℝ) * (|fourierCoeff u₀.eval T| + |fourierCoeff u₁.eval T|) =
            (1 / 2 : ℝ) * (fourierL1 u₀.eval k' + fourierL1 u₁.eval k') := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]; rfl
        have ih0 := fourierL1_le_choose_depth d u₀ hu₀_d hu₀_bd k'
        have ih1 := fourierL1_le_choose_depth d u₁ hu₁_d hu₁_bd k'
        linarith
      have hpart2 :
          ∑ S ∈ ((Finset.univ : Finset (Finset ι)).filter (fun S => #S = k' + 1)).filter
              (fun S => i ∉ S),
            |fourierCoeff (DecisionTree.node i t₀ t₁).eval S| ≤ (d.choose (k' + 1) : ℝ) := by
        have h1 :
            ∑ S ∈ ((Finset.univ : Finset (Finset ι)).filter (fun S => #S = k' + 1)).filter
                (fun S => i ∉ S),
              |fourierCoeff (DecisionTree.node i t₀ t₁).eval S| ≤
            ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => #S = k' + 1),
              (1 / 2 : ℝ) * (|fourierCoeff u₀.eval S| + |fourierCoeff u₁.eval S|) := by
          calc _ ≤ ∑ S ∈ ((Finset.univ : Finset (Finset ι)).filter (fun S => #S = k' + 1)).filter
                  (fun S => i ∉ S),
                (1 / 2 : ℝ) * (|fourierCoeff u₀.eval S| + |fourierCoeff u₁.eval S|) := by
                refine Finset.sum_le_sum fun S hS => ?_
                have hniS : i ∉ S := (Finset.mem_filter.mp hS).2
                rw [hcoeff S, ite_eq_right hniS, abs_mul,
                  abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
                gcongr
                exact abs_add_le _ _
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun _ _ _ => by positivity)
        have h2 :
            ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => #S = k' + 1),
              (1 / 2 : ℝ) * (|fourierCoeff u₀.eval S| + |fourierCoeff u₁.eval S|) =
            (1 / 2 : ℝ) * (fourierL1 u₀.eval (k' + 1) + fourierL1 u₁.eval (k' + 1)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]; rfl
        have ih0 := fourierL1_le_choose_depth d u₀ hu₀_d hu₀_bd (k' + 1)
        have ih1 := fourierL1_le_choose_depth d u₁ hu₁_d hu₁_bd (k' + 1)
        linarith
      rw [Nat.choose_succ_succ, Nat.cast_add]
      linarith

/-- Decision-tree complexity Fourier `L_{1, k}` bound for Boolean functions mapped into
`[-1, 1]`. -/
theorem fourierL1_le_choose_complexity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → Bool) (v : Bool → ℝ) (hv : ∀ b, |v b| ≤ 1) (k : ℕ) :
    fourierL1 (fun x => v (f x)) k ≤ ((complexity f).choose k : ℝ) := by
  obtain ⟨t, ht, hd⟩ := complexity_le_iff.mp (le_refl (complexity f))
  have heq : (fun x => v (f x)) = (t.map v).eval := funext fun x => by
    rw [DecisionTree.eval_map, ht x]
  rw [heq]
  exact fourierL1_le_choose_depth (complexity f) (t.map v) (by simpa using hd)
    (fun x => by rw [DecisionTree.eval_map]; exact hv _) k

/-! ### : DNF Deduplication, Restriction, and Width-`w` Level-2 Fourier Bound -/

/-- Remove duplicate variable occurrences in a term, returning `none` if contradictory literals
appear. -/
def dedupTerm {ι : Type*} [DecidableEq ι] : Term ι → Option (Term ι)
  | [] => some []
  | (v, b) :: rest =>
    match dedupTerm rest with
    | none => none
    | some t' =>
      match t'.lookup v with
      | none => some ((v, b) :: t')
      | some c => if c = b then some t' else none

private theorem lookup_eq_some_mem {ι : Type*} [DecidableEq ι] {t : Term ι} {v : ι} {c : Bool}
    (h : t.lookup v = some c) : (v, c) ∈ t := by
  induction t with
  | nil => simp at h
  | cons a rest ih =>
    rcases a with ⟨w, d⟩
    simp only [List.lookup_cons] at h
    by_cases hvw : v == w
    · simp only [hvw, Option.some.injEq] at h
      subst h
      have heq : v = w := eq_of_beq hvw
      subst heq
      exact List.mem_cons_self
    · simp only [hvw] at h
      exact List.mem_cons_of_mem _ (ih h)

private theorem lookup_eq_none_not_mem_fst {ι : Type*} [DecidableEq ι] :
    ∀ {l : List (ι × Bool)} {v : ι}, l.lookup v = none → v ∉ l.map Prod.fst
  | [], _, _ => by simp
  | (v', b') :: rest, v, h => by
    simp only [List.lookup_cons] at h
    cases hv : (v == v')
    · rw [hv] at h
      have hne : v ≠ v' := by simpa [beq_eq_false_iff_ne] using hv
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨hne, lookup_eq_none_not_mem_fst h⟩
    · rw [hv] at h; cases h

private theorem dedupTerm_some_props {ι : Type*} [DecidableEq ι] {t t' : Term ι}
    (h : dedupTerm t = some t') :
    t'.length ≤ t.length ∧ (t'.map Prod.fst).Nodup ∧ ∀ x, Term.eval x t' = Term.eval x t := by
  induction t generalizing t' with
  | nil =>
    simp only [dedupTerm, Option.some.injEq] at h; subst h; exact ⟨le_rfl, by simp, fun _ => rfl⟩
  | cons l rest ih =>
    rcases l with ⟨v, b⟩
    simp only [dedupTerm] at h
    cases hr : dedupTerm rest with
    | none => rw [hr] at h; cases h
    | some t2 =>
      rw [hr] at h; dsimp only at h
      obtain ⟨hlen, hnd, hev⟩ := ih hr
      cases hl : t2.lookup v with
      | none =>
        rw [hl] at h; dsimp only at h; cases h
        have hnotmem : v ∉ t2.map Prod.fst := lookup_eq_none_not_mem_fst hl
        refine ⟨by simp; omega, List.nodup_cons.mpr ⟨hnotmem, hnd⟩, fun x => ?_⟩
        simp [Term.eval_cons, hev x]
      | some c =>
        rw [hl] at h; dsimp only at h
        by_cases hcb : c = b
        · rw [ite_eq_left hcb] at h; cases h; subst hcb
          refine ⟨by simp; omega, hnd, fun x => ?_⟩
          rw [Term.eval_cons, ← hev x]
          cases hte : Term.eval x t'
          · simp
          · have hxc := (Term.eval_eq_true_iff x t').mp hte (v, c) (lookup_eq_some_mem hl)
            simp [Literal.eval, hxc]
        · rw [ite_eq_right hcb] at h; cases h

private theorem dedupTerm_none_eval {ι : Type*} [DecidableEq ι] {t : Term ι}
    (h : dedupTerm t = none) (x : ι → Bool) : Term.eval x t = false := by
  induction t with
  | nil => simp [dedupTerm] at h
  | cons l rest ih =>
    rcases l with ⟨v, b⟩
    simp only [dedupTerm] at h
    cases hr : dedupTerm rest with
    | none => simp [Term.eval_cons, ih hr]
    | some t' =>
      rw [hr] at h; dsimp only at h
      cases hl : t'.lookup v with
      | none => rw [hl] at h; cases h
      | some c =>
        rw [hl] at h; dsimp only at h
        by_cases hcb : c = b
        · rw [ite_eq_left hcb] at h; cases h
        · have hmem : (v, c) ∈ t' := lookup_eq_some_mem hl
          have heval_rest := (dedupTerm_some_props hr).2.2 x
          rw [Term.eval_cons, ← heval_rest]
          cases hte : Term.eval x t'
          · simp
          · have hxc := (Term.eval_eq_true_iff x t').mp hte (v, c) hmem
            simp only [Literal.eval, Bool.and_true]
            rw [hxc]
            exact beq_eq_false_iff_ne.mpr hcb

/-- Clean a DNF so every term has pairwise distinct variables, preserving `DNF.eval` and width. -/
def dedupDNF {ι : Type*} [DecidableEq ι] (F : DNF ι) : DNF ι :=
  F.filterMap dedupTerm

private theorem dedupDNF_props {ι : Type*} [DecidableEq ι] {w : ℕ} (F : DNF ι)
    (hw : ∀ t ∈ F, t.length ≤ w) :
    (∀ t ∈ dedupDNF F, t.length ≤ w) ∧
    (∀ t ∈ dedupDNF F, (t.map Prod.fst).Nodup) ∧
    (∀ x, DNF.eval x (dedupDNF F) = DNF.eval x F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t' ht'
    obtain ⟨t, htF, hdt⟩ := List.mem_filterMap.mp ht'
    exact (dedupTerm_some_props hdt).1.trans (hw t htF)
  · intro t' ht'
    obtain ⟨t, _, hdt⟩ := List.mem_filterMap.mp ht'
    exact (dedupTerm_some_props hdt).2.1
  · intro x
    rw [Bool.eq_iff_iff, DNF.eval_eq_true_iff, DNF.eval_eq_true_iff]
    constructor
    · rintro ⟨t', ht', hev⟩
      obtain ⟨t, htF, hdt⟩ := List.mem_filterMap.mp ht'
      exact ⟨t, htF, (dedupTerm_some_props hdt).2.2 x ▸ hev⟩
    · rintro ⟨t, htF, hev⟩
      cases hdt : dedupTerm t with
      | none =>
        have hf := dedupTerm_none_eval hdt x
        rw [hev] at hf; cases hf
      | some t' =>
        exact ⟨t', List.mem_filterMap.mpr ⟨t, htF, hdt⟩, (dedupTerm_some_props hdt).2.2 x ▸ hev⟩

/-- Syntactically restrict a term by a partial assignment `ρ`, returning `none` if falsified. -/
def restrictTerm {ι : Type*} (ρ : PartialAssignment ι) : Term ι → Option (Term ι)
  | [] => some []
  | (v, b) :: rest =>
    match restrictTerm ρ rest with
    | none => none
    | some t' =>
      match ρ v with
      | none => some ((v, b) :: t')
      | some c => if c = b then some t' else none

private theorem restrictTerm_none_eval {ι : Type*} {ρ : PartialAssignment ι} {t : Term ι}
    (h : restrictTerm ρ t = none) (x : ι → Bool) : t.eval (ρ.fill x) = false := by
  induction t with
  | nil => simp [restrictTerm] at h
  | cons l rest ih =>
    rcases l with ⟨v, b⟩
    simp only [restrictTerm] at h
    cases hr : restrictTerm ρ rest with
    | none => rw [Term.eval_cons, ih hr, Bool.and_false]
    | some t' =>
      rw [hr] at h; dsimp only at h
      cases hρ : ρ v with
      | none => rw [hρ] at h; cases h
      | some c =>
        rw [hρ] at h; dsimp only at h
        by_cases hcb : c = b
        · rw [ite_eq_left hcb] at h; cases h
        · rw [Term.eval_cons]
          simp [Literal.eval, PartialAssignment.fill_of_eq_some hρ, beq_eq_false_iff_ne.mpr hcb]

private theorem restrictTerm_some_props {ι : Type*} {ρ : PartialAssignment ι} {t t' : Term ι}
    (h : restrictTerm ρ t = some t') :
    t'.length ≤ t.length ∧ ∀ x, Term.eval x t' = Term.eval (ρ.fill x) t := by
  induction t generalizing t' with
  | nil => simp only [restrictTerm, Option.some.injEq] at h; subst h; exact ⟨le_rfl, fun _ => rfl⟩
  | cons l rest ih =>
    rcases l with ⟨v, b⟩
    simp only [restrictTerm] at h
    cases hr : restrictTerm ρ rest with
    | none => rw [hr] at h; cases h
    | some t2 =>
      rw [hr] at h; dsimp only at h
      obtain ⟨hlen, hev⟩ := ih hr
      cases hρ : ρ v with
      | none =>
        rw [hρ] at h; dsimp only at h; cases h
        refine ⟨by simp; omega, fun x => ?_⟩
        simp [Term.eval_cons, Literal.eval, PartialAssignment.fill_of_eq_none hρ, hev x]
      | some c =>
        rw [hρ] at h; dsimp only at h
        by_cases hcb : c = b
        · rw [ite_eq_left hcb] at h; cases h; subst hcb
          refine ⟨by simp; omega, fun x => ?_⟩
          simp [Term.eval_cons, Literal.eval, PartialAssignment.fill_of_eq_some hρ, hev x]
        · rw [ite_eq_right hcb] at h; cases h

/-- Syntactically restrict a DNF by a partial assignment `ρ`, preserving width. -/
def restrictDNF {ι : Type*} (ρ : PartialAssignment ι) (F : DNF ι) : DNF ι :=
  F.filterMap (restrictTerm ρ)

/-- `restrictDNF ρ F` evaluates identically to `F` on `ρ.fill x` and never increases term width. -/
theorem restrictDNF_props {ι : Type*} {w : ℕ} (ρ : PartialAssignment ι) (F : DNF ι)
    (hw : ∀ t ∈ F, t.length ≤ w) :
    (∀ t ∈ restrictDNF ρ F, t.length ≤ w) ∧
    (∀ x, DNF.eval x (restrictDNF ρ F) = DNF.eval (ρ.fill x) F) := by
  refine ⟨?_, ?_⟩
  · intro t' ht'
    obtain ⟨t, htF, hrt⟩ := List.mem_filterMap.mp ht'
    exact (restrictTerm_some_props hrt).1.trans (hw t htF)
  · intro x
    rw [Bool.eq_iff_iff, DNF.eval_eq_true_iff, DNF.eval_eq_true_iff]
    constructor
    · rintro ⟨t', ht', hev⟩
      obtain ⟨t, htF, hrt⟩ := List.mem_filterMap.mp ht'
      exact ⟨t, htF, (restrictTerm_some_props hrt).2 x ▸ hev⟩
    · rintro ⟨t, htF, hev⟩
      cases hrt : restrictTerm ρ t with
      | none =>
        have hf := restrictTerm_none_eval hrt x
        rw [hev] at hf; cases hf
      | some t' =>
        exact ⟨t', List.mem_filterMap.mpr ⟨t, htF, hrt⟩, (restrictTerm_some_props hrt).2 x ▸ hev⟩

/-- Any function depending only on `ρ.free` has decision tree complexity at most `#ρ.free`. -/
private theorem complexity_comp_fill_le_card_free {ι β : Type*} [Fintype ι]
    (ρ : PartialAssignment ι) (f : (ι → Bool) → β) :
    complexity (fun x => f (ρ.fill x)) ≤ #ρ.free := by
  classical
  have hbuild : ∀ (S : Finset ι) (g : (ι → Bool) → β),
      (∀ x y, (∀ i ∈ S, x i = y i) → g x = g y) →
      ∃ t : DecisionTree ι β, t.Computes g ∧ t.depth ≤ #S := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro g hg
      refine ⟨.leaf (g fun _ => false), fun x => hg _ _ (by simp), by simp⟩
    | insert a S ha ih =>
      intro g hg
      obtain ⟨t₀, ht₀, hd₀⟩ := ih (fun x => g (Function.update x a false)) fun x y hxy =>
        hg _ _ fun i hi => by
          rcases Finset.mem_insert.mp hi with rfl | hiS
          · simp
          · simp [Function.update_of_ne (ne_of_mem_of_not_mem hiS ha), hxy i hiS]
      obtain ⟨t₁, ht₁, hd₁⟩ := ih (fun x => g (Function.update x a true)) fun x y hxy =>
        hg _ _ fun i hi => by
          rcases Finset.mem_insert.mp hi with rfl | hiS
          · simp
          · simp [Function.update_of_ne (ne_of_mem_of_not_mem hiS ha), hxy i hiS]
      refine ⟨.node a t₀ t₁, fun x => ?_, ?_⟩
      · simp only [DecisionTree.eval_node]
        cases hxa : x a
        · simp only [Bool.cond_false]
          rw [ht₀]
          dsimp only; congr 1; funext j; by_cases h : j = a
          · subst h; simp [hxa]
          · simp [Function.update_of_ne h]
        · simp only [Bool.cond_true]
          rw [ht₁]
          dsimp only; congr 1; funext j; by_cases h : j = a
          · subst h; simp [hxa]
          · simp [Function.update_of_ne h]
      · simp only [DecisionTree.depth_node, Finset.card_insert_of_notMem ha]; omega
  obtain ⟨t, ht, hd⟩ := hbuild ρ.free (fun x => f (ρ.fill x)) fun x y hxy => by
    congr 1; funext i
    cases hρ : ρ i with
    | none =>
      rw [PartialAssignment.fill_of_eq_none hρ, PartialAssignment.fill_of_eq_none hρ]
      exact hxy i (PartialAssignment.mem_free.mpr hρ)
    | some b =>
      rw [PartialAssignment.fill_of_eq_some hρ, PartialAssignment.fill_of_eq_some hρ]
  exact (complexity_le_depth ht).trans hd

/-- Exact finite sum identity: `∑_{s=0}^{ℓ-1} s * (1/2)^(s+1) = 1 - (ℓ + 1) / 2^ℓ`. -/
private theorem sum_range_mul_half_pow (ℓ : ℕ) :
    ∑ s ∈ Finset.range ℓ, (s : ℝ) * (1 / 2 : ℝ) ^ (s + 1) = 1 - ((ℓ + 1 : ℝ) / (2 : ℝ) ^ ℓ) := by
  induction ℓ with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hpow : (1 / 2 : ℝ) ^ (k + 1) = 1 / ((2 : ℝ) ^ k * 2) := by
      rw [one_div_pow, pow_succ]
    rw [hpow, pow_succ]
    have hpos : (2 : ℝ) ^ k ≠ 0 := by positivity
    push_cast
    field_simp [hpos]
    ring

/-- Sum of `(s - 1)` for `s = 1..c` equals `c.choose 2`. -/
private theorem choose_two_eq_sum_Icc (c : ℕ) :
    c.choose 2 = ∑ s ∈ Finset.Icc 1 c, (s - 1) := by
  induction c with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, ih]
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp), Nat.add_sub_cancel, add_comm]

/-- Ratio bound for `withFree`: when `32 * w * ℓ ≤ M` (`w ≥ 1`) and `s ≤ ℓ`,
`#(withFree ι (ℓ - s)) * (8 * w)^s ≤ #(withFree ι ℓ)`. -/
private theorem card_withFree_sub_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w ℓ s : ℕ} (hw : 1 ≤ w) (hℓM : 32 * w * ℓ ≤ Fintype.card ι) (hs : s ≤ ℓ) :
    #(PartialAssignment.withFree ι (ℓ - s)) * (8 * w) ^ s ≤
      #(PartialAssignment.withFree ι ℓ) := by
  induction s with
  | zero => simp
  | succ k ih =>
    have hkℓ : k ≤ ℓ := by omega
    have hstep := PartialAssignment.mul_card_extensions_sub_one
      (PartialAssignment.empty : PartialAssignment ι) (t := ℓ - k) (by omega)
    rw [PartialAssignment.free_empty, Finset.card_univ] at hstep
    have hsub : ℓ - (k + 1) = ℓ - k - 1 := by omega
    have hdom : 2 * (ℓ - k) * (8 * w) ≤ Fintype.card ι - (ℓ - k - 1) := by
      have h1 : ℓ - k ≤ ℓ := Nat.sub_le _ _
      have h2 : 16 * w * (ℓ - k) ≤ 16 * w * ℓ := Nat.mul_le_mul_left _ h1
      have h3 : ℓ ≤ 16 * w * ℓ := by nlinarith
      have h4 : ℓ - k - 1 ≤ ℓ := by omega
      have h5 : 16 * w * (ℓ - k) + (ℓ - k - 1) ≤ 32 * w * ℓ := by nlinarith
      have h6 : 2 * (ℓ - k) * (8 * w) = 16 * w * (ℓ - k) := by ring
      omega
    have h1 : #(PartialAssignment.withFree ι (ℓ - (k + 1))) * (8 * w) ≤
        #(PartialAssignment.withFree ι (ℓ - k)) := by
      rw [hsub]
      have hmul : #(PartialAssignment.withFree ι (ℓ - k - 1)) * (2 * (ℓ - k) * (8 * w)) ≤
          #(PartialAssignment.withFree ι (ℓ - k - 1)) * (Fintype.card ι - (ℓ - k - 1)) :=
        Nat.mul_le_mul_left _ hdom
      have hmul2 : 2 * (ℓ - k) * (#(PartialAssignment.withFree ι (ℓ - k - 1)) * (8 * w)) ≤
          2 * (ℓ - k) * #(PartialAssignment.withFree ι (ℓ - k)) := by
        calc 2 * (ℓ - k) * (#(PartialAssignment.withFree ι (ℓ - k - 1)) * (8 * w))
            = #(PartialAssignment.withFree ι (ℓ - k - 1)) * (2 * (ℓ - k) * (8 * w)) := by ring
          _ ≤ #(PartialAssignment.withFree ι (ℓ - k - 1)) * (Fintype.card ι - (ℓ - k - 1)) := hmul
          _ = (Fintype.card ι - (ℓ - k - 1)) * #(PartialAssignment.withFree ι (ℓ - k - 1)) :=
              mul_comm _ _
          _ = 2 * (ℓ - k) * #(PartialAssignment.withFree ι (ℓ - k)) := hstep
      exact Nat.le_of_mul_le_mul_left hmul2 (by omega)
    calc #(PartialAssignment.withFree ι (ℓ - (k + 1))) * (8 * w) ^ (k + 1)
        = (#(PartialAssignment.withFree ι (ℓ - (k + 1))) * (8 * w)) * (8 * w) ^ k := by
            rw [pow_succ']; ring
      _ ≤ #(PartialAssignment.withFree ι (ℓ - k)) * (8 * w) ^ k := Nat.mul_le_mul_right _ h1
      _ ≤ #(PartialAssignment.withFree ι ℓ) := ih hkℓ

/-- Average over `(J, z)` equals average over `withFree ι ℓ` for any real functional of a
partial assignment. -/
private theorem sum_powersetCard_sum_outside {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ℓ : ℕ) (g : PartialAssignment ι → ℝ) :
    ∑ J ∈ (Finset.univ : Finset ι).powersetCard ℓ,
      ∑ z : ι → Bool, g (PartialAssignment.outside J z) =
    (2 : ℝ) ^ ℓ * ∑ ρ ∈ PartialAssignment.withFree ι ℓ, g ρ := by
  have hfib :
      ∑ J ∈ (Finset.univ : Finset ι).powersetCard ℓ,
        ∑ z : ι → Bool, g (PartialAssignment.outside J z) =
      ∑ ρ ∈ PartialAssignment.withFree ι ℓ,
        ∑ p ∈ ((Finset.univ : Finset ι).powersetCard ℓ ×ˢ (Finset.univ : Finset (ι → Bool))).filter
            (fun p => PartialAssignment.outside p.1 p.2 = ρ), g ρ := by
    rw [← Finset.sum_product']
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : Finset ι × (ι → Bool) =>
      PartialAssignment.outside p.1 p.2) (t := PartialAssignment.withFree ι ℓ)]
    · refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun p hp => ?_
      rw [(Finset.mem_filter.mp hp).2]
    · intro p hp
      rw [PartialAssignment.mem_withFree, PartialAssignment.free_outside]
      exact (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2
  rw [hfib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hfree : #ρ.free = ℓ := PartialAssignment.mem_withFree.mp hρ
  have hcard :
      #(((Finset.univ : Finset ι).powersetCard ℓ ×ˢ (Finset.univ : Finset (ι → Bool))).filter
          (fun p => PartialAssignment.outside p.1 p.2 = ρ)) = 2 ^ ℓ := by
    rw [← hfree, ← PartialAssignment.card_filter_outside_eq ρ]
    refine Finset.card_nbij' (fun p => p.2) (fun z => (ρ.free, z)) (fun p hp => ?_)
      (fun z hz => ?_) (fun p hp => ?_) (fun z _ => rfl)
    · obtain ⟨_, hpρ⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      have hJ : p.1 = ρ.free := by rw [← hpρ, PartialAssignment.free_outside]
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hJ ▸ hpρ
    · obtain ⟨_, hzρ⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hz)
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard,
        Finset.subset_univ, Finset.mem_univ, true_and, hfree, hzρ]
    · obtain ⟨_, hpρ⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      exact Prod.ext (by rw [← hpρ, PartialAssignment.free_outside]) rfl
  exact_mod_cast hcard

/-- **Width-`w` DNF level-2 Fourier `L₁` bound**: for every DNF `F` of width at most `w`
(`w ≥ 1`) on any finite variable set `ι`, `fourierL1 (dnfInd F) 2 ≤ 4608 * w^2`. -/
theorem fourierL1_dnf_two_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w : ℕ} (hw : 1 ≤ w) (F : DNF ι) (hF : ∀ t ∈ F, t.length ≤ w) :
    fourierL1 (dnfInd F) 2 ≤ 4608 * (w : ℝ) ^ 2 := by
  -- First deduplicate `F` so every term has `Nodup` variables without changing `dnfInd F`.
  obtain ⟨hFw, hFnd, hFeval⟩ := dedupDNF_props F hF
  have hind_eq : dnfInd F = dnfInd (dedupDNF F) := funext fun x => by
    simp only [dnfInd, hFeval x]
  rw [hind_eq]
  generalize dedupDNF F = G at hFw hFnd
  set M := Fintype.card ι
  by_cases hsmall : M < 64 * w
  · -- Small `M < 64 * w`: trivial bound `C(M, 2) ≤ M^2 ≤ 4096 * w^2`.
    have hterm : ∀ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => #S = 2),
        |fourierCoeff (dnfInd G) S| ≤ 1 := fun S _ => by
      refine (abs_fourierCoeff_le_expect_abs _ _).trans
        ((expect_le_expect fun x _ => ?_).trans_eq (expect_const Finset.univ_nonempty 1))
      dsimp only [dnfInd]; split_ifs <;> norm_num
    have hcard : #((Finset.univ : Finset (Finset ι)).filter (fun S => #S = 2)) = M.choose 2 := by
      have : (Finset.univ : Finset (Finset ι)).filter (fun S => #S = 2) =
          (Finset.univ : Finset ι).powersetCard 2 := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
          Finset.subset_univ]
      rw [this, Finset.card_powersetCard, Finset.card_univ]
    have hsum : fourierL1 (dnfInd G) 2 ≤ (M.choose 2 : ℝ) := by
      calc fourierL1 (dnfInd G) 2
          ≤ ∑ _S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => #S = 2), (1 : ℝ) :=
            Finset.sum_le_sum hterm
        _ = (M.choose 2 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
    have hch : M.choose 2 ≤ M * M := by
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self _ 2).trans (Nat.mul_le_mul_left _ (by omega))
    have hM2 : (M.choose 2 : ℝ) ≤ (64 * w : ℝ) ^ 2 := by
      have h1 : (M.choose 2 : ℝ) ≤ (M : ℝ) * (M : ℝ) := by exact_mod_cast hch
      have h2 : (M : ℝ) ≤ 64 * (w : ℝ) := by exact_mod_cast hsmall.le
      nlinarith [Nat.cast_nonneg (α := ℝ) M]
    nlinarith
  · -- Main regime `64 * w ≤ M`: apply random restriction with `ℓ = M / (32 * w)` free vars.
    have hbig : 64 * w ≤ M := Nat.le_of_not_lt hsmall
    set ℓ := M / (32 * w)
    have hℓ_ge2 : 2 ≤ ℓ := by
      dsimp only [ℓ]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hℓM : 32 * w * ℓ ≤ M := Nat.mul_div_le M (32 * w)
    have hℓ_le_M : ℓ ≤ M := by nlinarith
    have hM_le_48 : M ≤ 48 * w * ℓ := by
      have hdiv : M < 32 * w * (ℓ + 1) := by
        dsimp only [ℓ]; exact Nat.lt_mul_div_succ M (show 0 < 32 * w by omega)
      have : 2 * (ℓ + 1) ≤ 3 * ℓ := by omega
      nlinarith
    -- Step 1: Lower bound average restricted `L_{1, 2}` by `(C(M-2, ℓ-2) / C(M, ℓ)) * L_{1, 2}`.
    have hchoose_pos : (0 : ℝ) < (M.choose ℓ : ℝ) := by
      exact_mod_cast Nat.choose_pos hℓ_le_M
    have hwithFree_pos : (0 : ℝ) < (#(PartialAssignment.withFree ι ℓ) : ℝ) := by
      rw [PartialAssignment.card_withFree]
      have := Nat.choose_pos hℓ_le_M
      positivity
    have hlower :
        ((M - 2).choose (ℓ - 2) : ℝ) * fourierL1 (dnfInd G) 2 ≤
          (1 / (2 : ℝ) ^ M) * ∑ J ∈ (Finset.univ : Finset ι).powersetCard ℓ,
            ∑ z : ι → Bool, fourierL1 (fun x => dnfInd G (J.piecewise x z)) 2 := by
      -- For each fixed `S` of size 2 and `J ⊇ S`, `|f̂(S)| ≤ 𝔼_z |(f|_{J,z})^(S)|`.
      have hpt : ∀ (J : Finset ι) (S : Finset ι), S ⊆ J →
          |fourierCoeff (dnfInd G) S| ≤
            (1 / (2 : ℝ) ^ M) * ∑ z : ι → Bool,
              |fourierCoeff (fun x => dnfInd G (J.piecewise x z)) S| := fun J S hSJ => by
        have hfe := fourierCoeff_expect_piecewise (dnfInd G) J S
        rw [ite_eq_left hSJ] at hfe
        have hexp : fourierCoeff (fun x => 𝔼 z, dnfInd G (J.piecewise x z)) S =
            𝔼 z, fourierCoeff (fun x => dnfInd G (J.piecewise x z)) S := by
          simp only [fourierCoeff, expect_mul]; exact expect_comm _ _ _
        rw [← hfe, hexp]
        refine (abs_expect_le _ _).trans_eq ?_
        rw [expect_eq_sum_div_card, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Nat.cast_pow, Nat.cast_ofNat, div_eq_inv_mul, one_div]
      -- Count `J ∈ powersetCard ℓ univ` containing a fixed 2-element set `S`.
      have hcount_J : ∀ S : Finset ι, #S = 2 →
          #(((Finset.univ : Finset ι).powersetCard ℓ).filter (fun J => S ⊆ J)) =
            (M - 2).choose (ℓ - 2) := fun S hS => by
        have hbi :
            (((Finset.univ : Finset ι).powersetCard ℓ).filter (fun J => S ⊆ J)) =
              ((Finset.univ \ S).powersetCard (ℓ - 2)).image (fun K => S ∪ K) := by
          ext J
          simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
            Finset.mem_image]
          constructor
          · rintro ⟨hJcard, hSJ⟩
            refine ⟨J \ S, ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ _) subset_rfl, ?_⟩,
              Finset.union_sdiff_of_subset hSJ⟩
            rw [Finset.card_sdiff_of_subset hSJ, hJcard, hS]
          · rintro ⟨K, ⟨hKsub, hKcard⟩, rfl⟩
            have hdisj : Disjoint S K :=
              Disjoint.mono_right hKsub Finset.disjoint_sdiff
            refine ⟨?_, Finset.subset_union_left⟩
            rw [Finset.card_union_of_disjoint hdisj, hS, hKcard]; omega
        rw [hbi, Finset.card_image_of_injOn]
        · rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ _),
            Finset.card_univ, hS]
        · intro K₁ hK₁ K₂ hK₂ hEq
          have h1 : Disjoint S K₁ :=
            Disjoint.mono_right (Finset.mem_powersetCard.mp hK₁).1 Finset.disjoint_sdiff
          have h2 : Disjoint S K₂ :=
            Disjoint.mono_right (Finset.mem_powersetCard.mp hK₂).1 Finset.disjoint_sdiff
          have := congrArg (fun A => A \ S) hEq
          simpa [Finset.union_sdiff_cancel_left h1, Finset.union_sdiff_cancel_left h2] using this
      calc ((M - 2).choose (ℓ - 2) : ℝ) * fourierL1 (dnfInd G) 2
          = ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => #S = 2),
              ∑ J ∈ ((Finset.univ : Finset ι).powersetCard ℓ).filter (fun J => S ⊆ J),
                |fourierCoeff (dnfInd G) S| := by
            rw [fourierL1, Finset.mul_sum]
            refine Finset.sum_congr rfl fun S hS => ?_
            rw [Finset.sum_const, nsmul_eq_mul, hcount_J S (Finset.mem_filter.mp hS).2]
        _ ≤ ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => #S = 2),
              ∑ J ∈ ((Finset.univ : Finset ι).powersetCard ℓ).filter (fun J => S ⊆ J),
                (1 / (2 : ℝ) ^ M) * ∑ z : ι → Bool,
                  |fourierCoeff (fun x => dnfInd G (J.piecewise x z)) S| := by
            refine Finset.sum_le_sum fun S _ => Finset.sum_le_sum fun J hJ =>
              hpt J S (Finset.mem_filter.mp hJ).2
        _ ≤ ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => #S = 2),
              ∑ J ∈ (Finset.univ : Finset ι).powersetCard ℓ,
                (1 / (2 : ℝ) ^ M) * ∑ z : ι → Bool,
                  |fourierCoeff (fun x => dnfInd G (J.piecewise x z)) S| := by
            refine Finset.sum_le_sum fun S _ =>
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun _ _ _ => by positivity)
        _ = (1 / (2 : ℝ) ^ M) * ∑ J ∈ (Finset.univ : Finset ι).powersetCard ℓ,
              ∑ z : ι → Bool, fourierL1 (fun x => dnfInd G (J.piecewise x z)) 2 := by
            rw [Finset.sum_comm, Finset.mul_sum]
            refine Finset.sum_congr rfl fun J _ => ?_
            rw [← Finset.mul_sum, Finset.sum_comm]
            rfl
    -- Step 2: Convert `(J, z)` average to `withFree ι ℓ` average and bound by switching lemma.
    have houtside_eq :
        ∑ J ∈ (Finset.univ : Finset ι).powersetCard ℓ,
          ∑ z : ι → Bool, fourierL1 (fun x => dnfInd G (J.piecewise x z)) 2 =
        (2 : ℝ) ^ ℓ * ∑ ρ ∈ PartialAssignment.withFree ι ℓ,
          fourierL1 (fun x => dnfInd G (ρ.fill x)) 2 := by
      have hpw : ∀ (J : Finset ι) (z x : ι → Bool),
          (PartialAssignment.outside J z).fill x = J.piecewise x z := fun J z x => by
        funext i
        by_cases hi : i ∈ J
        · simp [PartialAssignment.outside, PartialAssignment.fill, hi, Finset.piecewise]
        · simp [PartialAssignment.outside, PartialAssignment.fill, hi, Finset.piecewise]
      simpa only [hpw] using sum_powersetCard_sum_outside ℓ
        (fun ρ => fourierL1 (fun x => dnfInd G (ρ.fill x)) 2)
    have hupper_avg :
        ∑ ρ ∈ PartialAssignment.withFree ι ℓ, fourierL1 (fun x => dnfInd G (ρ.fill x)) 2 ≤
          (#(PartialAssignment.withFree ι ℓ) : ℝ) := by
      have hdt : ∀ ρ ∈ PartialAssignment.withFree ι ℓ,
          fourierL1 (fun x => dnfInd G (ρ.fill x)) 2 ≤
            ((complexity (fun x => DNF.eval (ρ.fill x) G)).choose 2 : ℝ) := fun ρ _ =>
        fourierL1_le_choose_complexity (fun x => DNF.eval (ρ.fill x) G)
          (fun b => if b then 1 else 0) (fun b => by cases b <;> norm_num) 2
      have hsum_dt :
          ∑ ρ ∈ PartialAssignment.withFree ι ℓ,
            ((complexity (fun x => DNF.eval (ρ.fill x) G)).choose 2 : ℝ) =
          ∑ s ∈ Finset.Icc 1 ℓ,
            ((s - 1 : ℕ) : ℝ) *
              (#((PartialAssignment.withFree ι ℓ).filter
                fun ρ => s ≤ complexity (fun x => DNF.eval (ρ.fill x) G)) : ℝ) := by
        have hstep1 :
            ∑ ρ ∈ PartialAssignment.withFree ι ℓ,
              ((complexity (fun x => DNF.eval (ρ.fill x) G)).choose 2 : ℝ) =
            ∑ ρ ∈ PartialAssignment.withFree ι ℓ,
              ∑ s ∈ Finset.Icc 1 ℓ,
                if s ≤ complexity (fun x => DNF.eval (ρ.fill x) G) then ((s - 1 : ℕ) : ℝ)
                else 0 := by
          refine Finset.sum_congr rfl fun ρ hρ => ?_
          rw [choose_two_eq_sum_Icc, Nat.cast_sum]
          have hle_ℓ : complexity (fun x => DNF.eval (ρ.fill x) G) ≤ ℓ := by
            have := complexity_comp_fill_le_card_free ρ (fun y => DNF.eval y G)
            rwa [PartialAssignment.mem_withFree.mp hρ] at this
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext s; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
        rw [hstep1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      have hsw_term : ∀ s ∈ Finset.Icc 1 ℓ,
          (#((PartialAssignment.withFree ι ℓ).filter
            fun ρ => s ≤ complexity (fun x => DNF.eval (ρ.fill x) G)) : ℝ) ≤
          (#(PartialAssignment.withFree ι ℓ) : ℝ) * (1 / 2 : ℝ) ^ s := fun s hs => by
        have hs_le : s ≤ ℓ := (Finset.mem_Icc.mp hs).2
        have hsw := DNF.card_switching_le hFw hFnd PartialAssignment.empty ℓ s
        have hrat := card_withFree_sub_mul_le (ι := ι) hw hℓM hs_le
        have hswR : (#((PartialAssignment.withFree ι ℓ).filter
            fun ρ => s ≤ complexity (fun x => DNF.eval (ρ.fill x) G)) : ℝ) ≤
            (#(PartialAssignment.withFree ι (ℓ - s)) : ℝ) * ((4 * w : ℕ) : ℝ) ^ s := by
          exact_mod_cast hsw
        have hratR : (#(PartialAssignment.withFree ι (ℓ - s)) : ℝ) * ((8 * w : ℕ) : ℝ) ^ s ≤
            (#(PartialAssignment.withFree ι ℓ) : ℝ) := by
          exact_mod_cast hrat
        have h8pos : (0 : ℝ) < ((8 * w : ℕ) : ℝ) ^ s := by positivity
        have h48 : ((4 * w : ℕ) : ℝ) ^ s = (1 / 2 : ℝ) ^ s * ((8 * w : ℕ) : ℝ) ^ s := by
          rw [← mul_pow]; congr 1; push_cast; ring
        rw [h48] at hswR
        nlinarith [show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ s by positivity]
      calc ∑ ρ ∈ PartialAssignment.withFree ι ℓ, fourierL1 (fun x => dnfInd G (ρ.fill x)) 2
          ≤ ∑ ρ ∈ PartialAssignment.withFree ι ℓ,
              ((complexity (fun x => DNF.eval (ρ.fill x) G)).choose 2 : ℝ) :=
            Finset.sum_le_sum hdt
        _ = ∑ s ∈ Finset.Icc 1 ℓ,
              ((s - 1 : ℕ) : ℝ) *
                (#((PartialAssignment.withFree ι ℓ).filter
                  fun ρ => s ≤ complexity (fun x => DNF.eval (ρ.fill x) G)) : ℝ) := hsum_dt
        _ ≤ ∑ s ∈ Finset.Icc 1 ℓ,
              ((s - 1 : ℕ) : ℝ) * ((#(PartialAssignment.withFree ι ℓ) : ℝ) * (1 / 2 : ℝ) ^ s) := by
            refine Finset.sum_le_sum fun s hs =>
              mul_le_mul_of_nonneg_left (hsw_term s hs) (Nat.cast_nonneg _)
        _ = (#(PartialAssignment.withFree ι ℓ) : ℝ) *
              ∑ s ∈ Finset.range ℓ, (s : ℝ) * (1 / 2 : ℝ) ^ (s + 1) := by
            rw [Finset.mul_sum]
            refine Finset.sum_nbij' (fun s => s - 1) (fun r => r + 1) (fun s hs => ?_)
              (fun r hr => ?_) (fun s hs => ?_) (fun r _ => ?_) (fun s hs => ?_)
            · simp only [Finset.mem_Icc, Finset.mem_range] at hs ⊢; omega
            · simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢; omega
            · simp only [Finset.mem_Icc] at hs; omega
            · omega
            · have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
              have hsub : s - 1 + 1 = s := by omega
              rw [hsub]; ring
        _ ≤ (#(PartialAssignment.withFree ι ℓ) : ℝ) * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            rw [sum_range_mul_half_pow]
            have : (0 : ℝ) ≤ ((ℓ + 1 : ℝ) / (2 : ℝ) ^ ℓ) := by positivity
            linarith
        _ = (#(PartialAssignment.withFree ι ℓ) : ℝ) := mul_one _
    -- Step 3: Combine Steps 1 & 2 and simplify the binomial ratio `C(M, ℓ) / C(M - 2, ℓ - 2)`.
    have hcomb :
        ((M - 2).choose (ℓ - 2) : ℝ) * fourierL1 (dnfInd G) 2 ≤ (M.choose ℓ : ℝ) := by
      have h1 : (1 / (2 : ℝ) ^ M) * ((2 : ℝ) ^ ℓ * (#(PartialAssignment.withFree ι ℓ) : ℝ)) =
          (M.choose ℓ : ℝ) := by
        rw [PartialAssignment.card_withFree, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        have hpow : (2 : ℝ) ^ ℓ * (2 : ℝ) ^ (M - ℓ) = (2 : ℝ) ^ M := by
          rw [← pow_add, Nat.add_sub_of_le hℓ_le_M]
        have hpos : (2 : ℝ) ^ M ≠ 0 := by positivity
        field_simp [hpos]
        linear_combination (M.choose ℓ : ℝ) * hpow
      calc ((M - 2).choose (ℓ - 2) : ℝ) * fourierL1 (dnfInd G) 2
          ≤ (1 / (2 : ℝ) ^ M) * ((2 : ℝ) ^ ℓ *
              ∑ ρ ∈ PartialAssignment.withFree ι ℓ,
                fourierL1 (fun x => dnfInd G (ρ.fill x)) 2) := by
            rw [← houtside_eq]; exact hlower
        _ ≤ (1 / (2 : ℝ) ^ M) * ((2 : ℝ) ^ ℓ * (#(PartialAssignment.withFree ι ℓ) : ℝ)) := by
            gcongr
        _ = (M.choose ℓ : ℝ) := h1
    -- Exact identity: `M * (M - 1) * C(M - 2, ℓ - 2) = ℓ * (ℓ - 1) * C(M, ℓ)`.
    have hchoose_step : ∀ a b : ℕ, (a + 1) * a.choose b = (a + 1).choose (b + 1) * (b + 1) := by
      intro a
      induction a with
      | zero =>
        intro b
        cases b with
        | zero => simp
        | succ b => simp [Nat.choose_succ_succ]
      | succ a ih =>
        intro b
        cases b with
        | zero => simp
        | succ b =>
          rw [Nat.choose_succ_succ (a + 1) (b + 1)]
          have h0 : (a + 1).choose (b + 1) = a.choose b + a.choose (b + 1) :=
            Nat.choose_succ_succ a b
          have h1 := ih b
          have h2 := ih (b + 1)
          nlinarith
    have hbin_id : ℓ * (ℓ - 1) * M.choose ℓ = M * (M - 1) * (M - 2).choose (ℓ - 2) := by
      have h1 := hchoose_step (M - 1) (ℓ - 1)
      have h2 := hchoose_step (M - 2) (ℓ - 2)
      have hM1 : M - 1 + 1 = M := by omega
      have hM2 : M - 2 + 1 = M - 1 := by omega
      have hℓ1 : ℓ - 1 + 1 = ℓ := by omega
      have hℓ2 : ℓ - 2 + 1 = ℓ - 1 := by omega
      rw [hM1, hℓ1] at h1
      rw [hM2, hℓ2] at h2
      calc ℓ * (ℓ - 1) * M.choose ℓ
          = (ℓ - 1) * (M.choose ℓ * ℓ) := by ring
        _ = (ℓ - 1) * (M * (M - 1).choose (ℓ - 1)) := by rw [← h1]
        _ = M * ((M - 1).choose (ℓ - 1) * (ℓ - 1)) := by ring
        _ = M * ((M - 1) * (M - 2).choose (ℓ - 2)) := by rw [← h2]
        _ = M * (M - 1) * (M - 2).choose (ℓ - 2) := by ring
    have hbin_pos : (0 : ℝ) < ((M - 2).choose (ℓ - 2) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : ℓ - 2 ≤ M - 2)
    have hratio : (M.choose ℓ : ℝ) ≤ 4608 * (w : ℝ) ^ 2 * ((M - 2).choose (ℓ - 2) : ℝ) := by
      have hbinR : (ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * (M.choose ℓ : ℝ) =
          (M : ℝ) * ((M - 1 : ℕ) : ℝ) * ((M - 2).choose (ℓ - 2) : ℝ) := by
        exact_mod_cast hbin_id
      have hℓ_sub : (ℓ : ℝ) ≤ 2 * ((ℓ - 1 : ℕ) : ℝ) := by
        have : ℓ ≤ 2 * (ℓ - 1) := by omega
        exact_mod_cast this
      have hM_le_R : (M : ℝ) ≤ 48 * (w : ℝ) * (ℓ : ℝ) := by exact_mod_cast hM_le_48
      have hM1_le_R : ((M - 1 : ℕ) : ℝ) ≤ 96 * (w : ℝ) * ((ℓ - 1 : ℕ) : ℝ) := by
        have : M - 1 ≤ M := Nat.sub_le _ _
        have hle : ((M - 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast this
        nlinarith [Nat.cast_nonneg (α := ℝ) w]
      have hprod_le : (M : ℝ) * ((M - 1 : ℕ) : ℝ) ≤
          4608 * (w : ℝ) ^ 2 * ((ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ)) := by
        have h1 : (M : ℝ) * ((M - 1 : ℕ) : ℝ) ≤
            (48 * (w : ℝ) * (ℓ : ℝ)) * (96 * (w : ℝ) * ((ℓ - 1 : ℕ) : ℝ)) :=
          mul_le_mul hM_le_R hM1_le_R (Nat.cast_nonneg _) (by positivity)
        linarith
      have hden_pos : (0 : ℝ) < (ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) := by
        have h1 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
        have h2 : (0 : ℝ) < ((ℓ - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < ℓ - 1)
        positivity
      nlinarith
    nlinarith

/-! ### : Multilinear Extension, Product Bernoulli Rounding, and Derivatives -/

/-- Multilinear extension of a real function `f : (ι → Bool) → ℝ` on `ℝ^ι`. -/
@[expose] noncomputable def multilinearExt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (z : ι → ℝ) : ℝ :=
  ∑ S : Finset ι, fourierCoeff f S * ∏ i ∈ S, z i

/-- Multilinear partial derivative `∂_S f_multi(z)` at `z : ι → ℝ`. -/
@[expose] noncomputable def multilinearDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (S : Finset ι) (z : ι → ℝ) : ℝ :=
  ∑ T : Finset ι, if S ⊆ T then fourierCoeff f T * ∏ i ∈ T \ S, z i else 0

/-- At `z = 0`, `multilinearExt f 0` equals the uniform expectation `𝔼_x f x`. -/
theorem multilinearExt_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ) :
    multilinearExt f 0 = 𝔼 x, f x := by
  rw [multilinearExt, Finset.sum_eq_single ∅]
  · simp [fourierCoeff_empty]
  · intro S _ hS
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    rw [Finset.prod_eq_zero hi rfl, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- On corners `z_i = signVal (x i) ∈ {-1, +1}`, `multilinearExt f` agrees with `f x`. -/
theorem multilinearExt_signVal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    multilinearExt f (fun i => signVal (x i)) = f x := by
  simp only [multilinearExt, ← chi_eq_prod_signVal, sum_fourierCoeff_mul_chi]

/-- Single-bit Bernoulli distribution with signed mean `z ∈ [-1, 1]`
(`Pr[false] = (1 + z)/2`, `Pr[true] = (1 - z)/2`). -/
@[expose] noncomputable def signBernPMF (z : ℝ) (hz : |z| ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => if b then ENNReal.ofReal ((1 - z) / 2) else ENNReal.ofReal ((1 + z) / 2))
    (by
      rw [Fintype.sum_bool]
      simp only [↓reduceIte, Bool.false_eq_true]
      have h1 : 0 ≤ (1 - z) / 2 := by linarith [(abs_le.mp hz).2]
      have h2 : 0 ≤ (1 + z) / 2 := by linarith [(abs_le.mp hz).1]
      rw [← ENNReal.ofReal_add h1 h2, show (1 - z) / 2 + (1 + z) / 2 = 1 by ring,
        ENNReal.ofReal_one])

/-- Product Bernoulli rounding distribution on `ι → Bool` with coordinate signed means `z i`. -/
@[expose] noncomputable def prodBernPMF {ι : Type*} [Fintype ι] (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1) :
    PMF (ι → Bool) :=
  Cslib.Probability.PMF.pi fun i => signBernPMF (z i) (hz i)

/-- **Exact expectation under product Bernoulli rounding**: `𝔼_{x ~ prodBernPMF z}[f x]` equals
`multilinearExt f z`. -/
theorem expect_prodBernPMF_eq_multilinearExt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1) :
    ∑ x : ι → Bool, (prodBernPMF z hz x).toReal * f x = multilinearExt f z := by
  have hchi : ∀ S : Finset ι,
      ∑ x : ι → Bool, (prodBernPMF z hz x).toReal * chi ℝ S x = ∏ i ∈ S, z i := fun S => by
    have hprod : ∀ x : ι → Bool,
        (prodBernPMF z hz x).toReal * chi ℝ S x =
          ∏ i : ι, (signBernPMF (z i) (hz i) (x i)).toReal *
            (if i ∈ S then signVal (x i) else 1) := fun x => by
      rw [prodBernPMF, Cslib.Probability.PMF.pi_apply, ENNReal.toReal_prod,
        chi_eq_prod_signVal, Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
    simp_rw [hprod]
    rw [← Fintype.prod_sum (fun (i : ι) (b : Bool) =>
      (signBernPMF (z i) (hz i) b).toReal * (if i ∈ S then signVal b else 1))]
    rw [← Finset.univ_inter S, ← Finset.prod_ite_mem Finset.univ S (fun i => z i)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
    have h1 : 0 ≤ (1 - z i) / 2 := by linarith [(abs_le.mp (hz i)).2]
    have h2 : 0 ≤ (1 + z i) / 2 := by linarith [(abs_le.mp (hz i)).1]
    simp only [signBernPMF, PMF.ofFintype_apply, ↓reduceIte, Bool.false_eq_true,
      ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2]
    by_cases hi : i ∈ S <;> simp [hi, signVal] <;> ring
  have hfx : ∀ x : ι → Bool, f x = ∑ S : Finset ι, fourierCoeff f S * chi ℝ S x :=
    fun x => (sum_fourierCoeff_mul_chi f x).symm
  simp_rw [hfx, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hpull : ∑ x : ι → Bool, (prodBernPMF z hz x).toReal * (fourierCoeff f S * chi ℝ S x) =
      fourierCoeff f S * ∑ x : ι → Bool, (prodBernPMF z hz x).toReal * chi ℝ S x := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  rw [hpull, hchi S]

/-- **Exact multilinear Taylor expansion (finite differences, zero calculus)**:
`f_multi(z + Δ) - f_multi(z) = ∑_{S ≠ ∅} ∂_S f_multi(z) * ∏_{i ∈ S} Δ_i`. -/
theorem multilinearExt_add_sub_eq_sum_deriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (z Δ : ι → ℝ) :
    multilinearExt f (fun i => z i + Δ i) - multilinearExt f z =
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (·.Nonempty),
        multilinearDeriv f S z * ∏ i ∈ S, Δ i := by
  have hexp : multilinearExt f (fun i => z i + Δ i) =
      ∑ S : Finset ι, multilinearDeriv f S z * ∏ i ∈ S, Δ i := by
    have hswap_add : ∀ T : Finset ι,
        ∏ i ∈ T, (z i + Δ i) = ∑ S ∈ T.powerset, (∏ i ∈ S, Δ i) * ∏ i ∈ T \ S, z i := fun T => by
      simp_rw [add_comm (z _) (Δ _)]
      exact Finset.prod_add Δ z T
    simp only [multilinearExt, hswap_add, Finset.mul_sum]
    calc ∑ T : Finset ι, ∑ S ∈ T.powerset,
          fourierCoeff f T * ((∏ i ∈ S, Δ i) * ∏ i ∈ T \ S, z i)
        = ∑ T : Finset ι, ∑ S : Finset ι,
            if S ⊆ T then fourierCoeff f T * ((∏ i ∈ S, Δ i) * ∏ i ∈ T \ S, z i) else 0 := by
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext S; simp [Finset.mem_powerset]
      _ = ∑ S : Finset ι, ∑ T : Finset ι,
            if S ⊆ T then fourierCoeff f T * ((∏ i ∈ S, Δ i) * ∏ i ∈ T \ S, z i) else 0 :=
          Finset.sum_comm
      _ = ∑ S : Finset ι, multilinearDeriv f S z * ∏ i ∈ S, Δ i := by
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [multilinearDeriv, Finset.sum_mul]
          refine Finset.sum_congr rfl fun T _ => by split_ifs <;> ring
  have h0 : multilinearDeriv f ∅ z = multilinearExt f z := by
    simp [multilinearDeriv, multilinearExt]
  rw [hexp]
  have hsplit : (Finset.univ : Finset (Finset ι)) =
      insert ∅ ((Finset.univ : Finset (Finset ι)).filter (·.Nonempty)) := by
    ext S
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and, true_iff,
      Finset.nonempty_iff_ne_empty]
    exact eq_or_ne S ∅
  conv_lhs => rw [hsplit, Finset.sum_insert (by simp)]
  rw [h0, Finset.prod_empty, mul_one]
  ring

/-- Single-coordinate half-random-restriction PMF for `|z| ≤ 1/2`: leaves the coordinate free
(`none`) with probability `1/2`, fixes it to `false` (+1) with probability `(1 + 2 z)/4`, and fixes
it to `true` (-1) with probability `(1 - 2 z)/4`. -/
noncomputable def halfRestrCoordPMF (z : ℝ) (hz : |z| ≤ 1 / 2) : PMF (Option Bool) :=
  PMF.ofFintype (fun o =>
    match o with
    | none => ENNReal.ofReal (1 / 2)
    | some false => ENNReal.ofReal ((1 + 2 * z) / 4)
    | some true => ENNReal.ofReal ((1 - 2 * z) / 4))
    (by
      rw [Fintype.sum_option, Fintype.sum_bool]
      have h1 : 0 ≤ (1 - 2 * z) / 4 := by linarith [(abs_le.mp hz).2]
      have h2 : 0 ≤ (1 + 2 * z) / 4 := by linarith [(abs_le.mp hz).1]
      rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (by norm_num) (by linarith),
        show (1 / 2 : ℝ) + ((1 - 2 * z) / 4 + (1 + 2 * z) / 4) = 1 by ring,
        ENNReal.ofReal_one])

/-- Product half-random-restriction PMF on `PartialAssignment ι` for `z ∈ [-1/2, 1/2]^ι`. -/
noncomputable def halfRestrPMF {ι : Type*} [Fintype ι] (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1 / 2) :
    PMF (PartialAssignment ι) :=
  Cslib.Probability.PMF.pi fun i => halfRestrCoordPMF (z i) (hz i)

/-- **Exact random-restriction representation of multilinear derivatives on `[-1/2, 1/2]^ι`**:
`𝔼_{ρ ~ halfRestrPMF z}[(f|_ρ)^(S)] = (1/2)^#S * ∂_S f_multi(z)`. -/
theorem expect_halfRestrPMF_fourierCoeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1 / 2) (S : Finset ι) :
    ∑ ρ : PartialAssignment ι,
      (halfRestrPMF z hz ρ).toReal * fourierCoeff (fun x => f (ρ.fill x)) S =
    (1 / 2 : ℝ) ^ #S * multilinearDeriv f S z := by
  -- First compute `𝔼_ρ[f (ρ.fill x)]` pointwise for each fixed `x : ι → Bool`.
  have hpoint : ∀ x : ι → Bool,
      ∑ ρ : PartialAssignment ι, (halfRestrPMF z hz ρ).toReal * f (ρ.fill x) =
        ∑ U : Finset ι, ((1 / 2 : ℝ) ^ #U * multilinearDeriv f U z) * chi ℝ U x := by
    intro x
    have hchi_ρ : ∀ T : Finset ι,
        ∑ ρ : PartialAssignment ι, (halfRestrPMF z hz ρ).toReal * chi ℝ T (ρ.fill x) =
          ∏ i ∈ T, (z i + (1 / 2 : ℝ) * signVal (x i)) := fun T => by
      have hprod : ∀ ρ : PartialAssignment ι,
          (halfRestrPMF z hz ρ).toReal * chi ℝ T (ρ.fill x) =
            ∏ i : ι, (halfRestrCoordPMF (z i) (hz i) (ρ i)).toReal *
              (if i ∈ T then signVal ((ρ i).getD (x i)) else 1) := fun ρ => by
        rw [halfRestrPMF, Cslib.Probability.PMF.pi_apply, ENNReal.toReal_prod,
          chi_eq_prod_signVal, Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
        rfl
      simp_rw [hprod]
      rw [← Fintype.prod_sum (fun (i : ι) (o : Option Bool) =>
        (halfRestrCoordPMF (z i) (hz i) o).toReal *
          (if i ∈ T then signVal (o.getD (x i)) else 1))]
      rw [← Finset.univ_inter T,
        ← Finset.prod_ite_mem Finset.univ T (fun i => z i + (1 / 2 : ℝ) * signVal (x i))]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Fintype.sum_option, Fintype.sum_bool]
      have h1 : 0 ≤ (1 - 2 * z i) / 4 := by linarith [(abs_le.mp (hz i)).2]
      have h2 : 0 ≤ (1 + 2 * z i) / 4 := by linarith [(abs_le.mp (hz i)).1]
      simp only [halfRestrCoordPMF, PMF.ofFintype_apply, Option.getD_none, Option.getD_some,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2]
      by_cases hi : i ∈ T <;> simp [hi, signVal] <;> ring
    have hfx : ∀ ρ : PartialAssignment ι,
        f (ρ.fill x) = ∑ T : Finset ι, fourierCoeff f T * chi ℝ T (ρ.fill x) :=
      fun ρ => (sum_fourierCoeff_mul_chi f (ρ.fill x)).symm
    simp_rw [hfx, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h1 :
        ∑ T : Finset ι, ∑ ρ : PartialAssignment ι,
          (halfRestrPMF z hz ρ).toReal * (fourierCoeff f T * chi ℝ T (ρ.fill x)) =
        multilinearExt f (fun i => z i + (1 / 2 : ℝ) * signVal (x i)) := by
      refine Finset.sum_congr rfl fun T _ => ?_
      have hpull : ∑ ρ : PartialAssignment ι,
            (halfRestrPMF z hz ρ).toReal * (fourierCoeff f T * chi ℝ T (ρ.fill x)) =
          fourierCoeff f T * ∑ ρ : PartialAssignment ι,
            (halfRestrPMF z hz ρ).toReal * chi ℝ T (ρ.fill x) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      rw [hpull, hchi_ρ T]
    rw [h1]
    have htay := multilinearExt_add_sub_eq_sum_deriv f z (fun i => (1 / 2 : ℝ) * signVal (x i))
    have h0 : multilinearDeriv f ∅ z = multilinearExt f z := by
      simp [multilinearDeriv, multilinearExt]
    have hsplit : (Finset.univ : Finset (Finset ι)) =
        insert ∅ ((Finset.univ : Finset (Finset ι)).filter (·.Nonempty)) := by
      ext U
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and, true_iff,
        Finset.nonempty_iff_ne_empty]
      exact eq_or_ne U ∅
    have hsum_all :
        multilinearExt f (fun i => z i + (1 / 2 : ℝ) * signVal (x i)) =
          ∑ U : Finset ι, multilinearDeriv f U z * ∏ i ∈ U, ((1 / 2 : ℝ) * signVal (x i)) := by
      conv_rhs => rw [hsplit, Finset.sum_insert (by simp)]
      rw [h0, Finset.prod_empty, mul_one]
      linarith
    rw [hsum_all]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← chi_eq_prod_signVal]
    ring
  -- Take the `S`-th Fourier coefficient of both sides.
  have hswap :
      ∑ ρ : PartialAssignment ι,
        (halfRestrPMF z hz ρ).toReal * fourierCoeff (fun x => f (ρ.fill x)) S =
      fourierCoeff
        (fun x => ∑ ρ : PartialAssignment ι, (halfRestrPMF z hz ρ).toReal * f (ρ.fill x)) S := by
    rw [fourierCoeff_sum_mul]
  rw [hswap, funext hpoint, fourierCoeff_sum_mul_chi]

/-- **Pointwise derivative bound on `[-1/2, 1/2]^ι`**: for any `f` with `|f x| ≤ 1` and
`z ∈ [-1/2, 1/2]^ι`, `|∂_S f_multi(z)| ≤ 2 ^ #S`. -/
theorem abs_multilinearDeriv_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ} (hf : ∀ x, |f x| ≤ 1)
    {z : ι → ℝ} (hz : ∀ i, |z i| ≤ 1 / 2) (S : Finset ι) :
    |multilinearDeriv f S z| ≤ (2 : ℝ) ^ #S := by
  have heq := expect_halfRestrPMF_fourierCoeff f z hz S
  have hle : |(1 / 2 : ℝ) ^ #S * multilinearDeriv f S z| ≤ 1 := by
    rw [← heq]
    calc |∑ ρ : PartialAssignment ι,
            (halfRestrPMF z hz ρ).toReal * fourierCoeff (fun x => f (ρ.fill x)) S|
        ≤ ∑ ρ : PartialAssignment ι,
            |(halfRestrPMF z hz ρ).toReal * fourierCoeff (fun x => f (ρ.fill x)) S| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ρ : PartialAssignment ι, (halfRestrPMF z hz ρ).toReal * 1 := by
          refine Finset.sum_le_sum fun ρ _ => ?_
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          exact (abs_fourierCoeff_le_expect_abs _ _).trans
            ((expect_le_expect fun x _ => hf (ρ.fill x)).trans_eq
              (expect_const Finset.univ_nonempty 1))
      _ = 1 := by simp only [mul_one, Cslib.Probability.PMF.sum_toReal]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ #S)] at hle
  have h2 : (2 : ℝ) ^ #S * (1 / 2 : ℝ) ^ #S = 1 := by rw [← mul_pow]; norm_num
  nlinarith [show (0 : ℝ) < (2 : ℝ) ^ #S by positivity]

/-- **Level-2 multilinear derivative `L₁` bound for width-`w` DNFs on `[-1/2, 1/2]^ι`**:
`∑_{|S| = 2} |∂_S (1_F)_multi(z)| ≤ 18432 * w^2`. -/
theorem sum_abs_multilinearDeriv_dnf_two_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w : ℕ} (hw : 1 ≤ w) (F : DNF ι) (hF : ∀ t ∈ F, t.length ≤ w)
    {z : ι → ℝ} (hz : ∀ i, |z i| ≤ 1 / 2) :
    ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => #S = 2),
      |multilinearDeriv (dnfInd F) S z| ≤ 18432 * (w : ℝ) ^ 2 := by
  have hstep :
      (1 / 4 : ℝ) * ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => #S = 2),
        |multilinearDeriv (dnfInd F) S z| ≤ 4608 * (w : ℝ) ^ 2 := by
    calc (1 / 4 : ℝ) * ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => #S = 2),
            |multilinearDeriv (dnfInd F) S z|
        = ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => #S = 2),
            |(1 / 2 : ℝ) ^ #S * multilinearDeriv (dnfInd F) S z| := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun S hS => ?_
          rw [(Finset.mem_filter.mp hS).2, abs_mul]
          norm_num
      _ = ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => #S = 2),
            |∑ ρ : PartialAssignment ι,
              (halfRestrPMF z hz ρ).toReal * fourierCoeff (fun x => dnfInd F (ρ.fill x)) S| := by
          refine Finset.sum_congr rfl fun S _ => by
            rw [expect_halfRestrPMF_fourierCoeff]
      _ ≤ ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => #S = 2),
            ∑ ρ : PartialAssignment ι,
              (halfRestrPMF z hz ρ).toReal * |fourierCoeff (fun x => dnfInd F (ρ.fill x)) S| := by
          refine Finset.sum_le_sum fun S _ => (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
          refine Finset.sum_congr rfl fun ρ _ => by
            rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      _ = ∑ ρ : PartialAssignment ι,
            (halfRestrPMF z hz ρ).toReal * fourierL1 (fun x => dnfInd F (ρ.fill x)) 2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ρ _ => (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ ρ : PartialAssignment ι, (halfRestrPMF z hz ρ).toReal * (4608 * (w : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun ρ _ =>
            mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          obtain ⟨hrw, hrev⟩ := restrictDNF_props ρ F hF
          have heq : (fun x => dnfInd F (ρ.fill x)) = dnfInd (restrictDNF ρ F) :=
            funext fun x => by simp only [dnfInd, hrev x]
          rw [heq]
          exact fourierL1_dnf_two_le hw (restrictDNF ρ F) hrw
      _ = 4608 * (w : ℝ) ^ 2 := by
          rw [← Finset.sum_mul, Cslib.Probability.PMF.sum_toReal, one_mul]
  linarith

end CslibFrontier.Foundations.BooleanAnalysis
