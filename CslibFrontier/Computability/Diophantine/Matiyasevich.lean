/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/
module

public import Mathlib.Computability.Halting
public import Mathlib.Logic.Godel.GodelBetaFunction
public import CslibFrontier.Computability.Diophantine.DegreeReduction

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Matiyasevich–Robinson–Davis–Putnam Theorem and Universal Quartic Equations

Completes the proof of the Matiyasevich–Robinson–Davis–Putnam (MRDP) theorem on top of Mathlib's
exponential Diophantine theorem (`Dioph.pow_dioph`) and combines it with Skolem degree reduction
(`CslibFrontier.Computability.Diophantine.DegreeReduction`) to construct single quartic (total
  degree at
most `4`) Diophantine representations over both `ℕ` and `ℤ` for every recursively enumerable
predicate, strictly under standard Lean axioms.

## Main definitions

* `CslibFrontier.Computability.Diophantine.mvPolyToPoly`: converts `MvPolynomial σ ℤ` into `Poly σ`.

## Main results

* `CslibFrontier.Computability.Diophantine.dioph_iff_exists_mvPoly`: finite-variable `MvPolynomial`
  characterization
  of `Dioph`.
* `CslibFrontier.Computability.Diophantine.choose_dioph`,
  `CslibFrontier.Computability.Diophantine.factorial_dioph`,
  `CslibFrontier.Computability.Diophantine.pair_dioph`,
  `CslibFrontier.Computability.Diophantine.unpair_left_dioph`,
  `CslibFrontier.Computability.Diophantine.unpair_right_dioph`,
  `CslibFrontier.Computability.Diophantine.beta_dioph`: binomial
  coefficients, factorials, Cantor pairing/unpairing, and Gödel's `β`-function are Diophantine.
* `CslibFrontier.Computability.Diophantine.bounded_forall_dioph`: Davis–Putnam–Robinson
  closure of Diophantine
  relations under bounded universal quantification `∀ i, 1 ≤ i → i ≤ n →...`.
* `CslibFrontier.Computability.Diophantine.diophFn_of_natPrimrec` and
  `CslibFrontier.Computability.Diophantine.diophPFun_of_natPartrec`:
  every primitive recursive (resp. partial recursive) function on `ℕ` is Diophantine.
* `CslibFrontier.Computability.Diophantine.universal_eval_graph_dioph` and
  `CslibFrontier.Computability.Diophantine.universal_dom_dioph`:
  the universal evaluation graph and halting domain of `Nat.Partrec.Code` are Diophantine.
* `CslibFrontier.Computability.Diophantine.rePred_iff_dioph`: a subset of `ℕ` is recursively
  enumerable if and only
  if it is Diophantine (MRDP theorem).
* `CslibFrontier.Computability.Diophantine.exists_universal_quartic_nat` and
  `CslibFrontier.Computability.Diophantine.rePred_exists_quartic_nat`: universal quartic Diophantine
  equation over `ℕ`
  and single degree-`≤ 4` Diophantine representations over `ℕ` for every recursively enumerable
  predicate.

## Tags

Hilbert's tenth problem, MRDP theorem, Diophantine sets, bounded quantification, quartic equations
-/

public section

namespace CslibFrontier.Computability.Diophantine

open MvPolynomial Dioph

/-! ### Bridge between `Dioph` and finite-variable `MvPolynomial _ ℤ` -/

/-- Converts `p : MvPolynomial σ ℤ` to a Mathlib `Poly σ` matching evaluation on `σ → ℕ`. -/
public noncomputable def mvPolyToPoly {σ : Type*} (p : MvPolynomial σ ℤ) : Poly σ :=
  eval₂ (Int.castRingHom (Poly σ)) Poly.proj p

@[simp]
public theorem mvPolyToPoly_apply {σ : Type*} (p : MvPolynomial σ ℤ) (x : σ → ℕ) :
    mvPolyToPoly p x = eval (fun i ↦ (x i : ℤ)) p := by
  unfold mvPolyToPoly
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [eval₂_C, eval_C]
    induction a using Int.induction_on with
    | zero => rfl
    | succ k ih =>
      rw [map_add, map_one]
      exact (congrArg (· + 1) ih)
    | pred k ih =>
      rw [map_sub, map_one]
      exact (congrArg (· - 1) ih)
  | add p q ihp ihq =>
    rw [eval₂_add, map_add]
    exact congrArg₂ (· + ·) ihp ihq
  | mul_X p i ihp =>
    rw [eval₂_mul, eval₂_X, map_mul, eval_X]
    exact congrArg (· * (x i : ℤ)) ihp

private theorem eval_eval₂_C {σ τ : Type*} (Q : MvPolynomial σ ℤ)
    (subst : σ → MvPolynomial τ ℤ) (z : τ → ℤ) :
    eval z (eval₂ C subst Q) = eval (fun u ↦ eval z (subst u)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C _ => rw [eval₂_C, eval_C, eval_C]
  | add _ _ hp hq => rw [eval₂_add, map_add, map_add, hp, hq]
  | mul_X _ _ hp => rw [eval₂_mul, eval₂_X, map_mul, map_mul, eval_X, hp]

/-- Every Diophantine set `S : Set (α → ℕ)` is cut out by a single multivariate polynomial
`P : MvPolynomial (α ⊕ Fin m) ℤ` with finitely many existential natural-number variables. -/
public theorem dioph_iff_exists_mvPoly {α : Type} {S : Set (α → ℕ)} :
    Dioph S ↔ ∃ (m : ℕ) (P : MvPolynomial (α ⊕ Fin m) ℤ),
      ∀ v : α → ℕ, v ∈ S ↔ ∃ y : Fin m → ℕ,
        eval (fun u ↦ ((Sum.elim v y u : ℕ) : ℤ)) P = 0 := by
  classical
  constructor
  · rintro ⟨β, f, hf⟩
    let Q : MvPolynomial (α ⊕ β) ℤ := polyToMvPoly f
    let B : Finset β := Q.support.biUnion fun s ↦ s.support.biUnion fun
      | Sum.inl _ => ∅
      | Sum.inr b => {b}
    let m := B.card
    let e : Fin m ≃ B := (Fintype.equivFinOfCardEq (Fintype.card_coe B)).symm
    let subst : α ⊕ β → MvPolynomial (α ⊕ Fin m) ℤ
      | Sum.inl a => X (Sum.inl a)
      | Sum.inr b => if hb : b ∈ B then X (Sum.inr (e.symm ⟨b, hb⟩)) else 0
    let P : MvPolynomial (α ⊕ Fin m) ℤ := eval₂ C subst Q
    refine ⟨m, P, fun v ↦ ?_⟩
    rw [hf v]
    constructor
    · rintro ⟨t, ht⟩
      let y : Fin m → ℕ := fun j ↦ t (e j).1
      refine ⟨y, ?_⟩
      have h1 : eval (fun u ↦ ((Sum.elim v y u : ℕ) : ℤ)) P =
          eval (fun u ↦ ((Sum.elim v t u : ℕ) : ℤ)) Q := by
        rw [show P = eval₂ C subst Q from rfl, eval_eval₂_C]
        rw [Q.as_sum, map_sum, map_sum]
        refine Finset.sum_congr rfl fun s hs ↦ ?_
        simp only [eval_monomial, Finsupp.prod]
        congr 1
        refine Finset.prod_congr rfl fun u hu ↦ ?_
        congr 1
        cases u with
        | inl a => simp [subst]
        | inr b =>
          have hb : b ∈ B := Finset.mem_biUnion.mpr
            ⟨s, hs, Finset.mem_biUnion.mpr ⟨Sum.inr b, hu, Finset.mem_singleton_self b⟩⟩
          simp [subst, dite_eq_left hb, y]
      rw [h1, eval_polyToMvPoly]
      exact ht
    · rintro ⟨y, hy⟩
      let t : β → ℕ := fun b ↦ if hb : b ∈ B then y (e.symm ⟨b, hb⟩) else 0
      refine ⟨t, ?_⟩
      rw [← eval_polyToMvPoly, ← hy, show P = eval₂ C subst Q from rfl, eval_eval₂_C]
      have hfn : (fun u : α ⊕ β ↦ ((Sum.elim v t u : ℕ) : ℤ)) =
          fun u ↦ eval (fun w ↦ ((Sum.elim v y w : ℕ) : ℤ)) (subst u) := by
        ext (a | b)
        · simp [subst]
        · by_cases hb : b ∈ B <;> simp [subst, t, hb]
      rw [hfn]
  · rintro ⟨m, P, hP⟩
    exact ⟨Fin m, mvPolyToPoly P, fun v ↦ by simp [hP v]⟩

/-- Finite existential quantification over `Fin m → ℕ` preserves `Dioph`. -/
private theorem ex_fin_dioph {α : Type} :
    ∀ {m : ℕ} {S : Set (α ⊕ Fin m → ℕ)}, Dioph S →
      Dioph {v : α → ℕ | ∃ y : Fin m → ℕ, Sum.elim v y ∈ S}
  | 0, S, hS => by
    let g : α ⊕ Fin 0 → α := Sum.elim id Fin.elim0
    refine (hS.reindex_dioph α g).ext fun v ↦ ?_
    constructor
    · intro hv
      have hvg : v ∘ g ∈ S := hv
      have heq : v ∘ g = Sum.elim v Fin.elim0 := by
        ext (a | j)
        · rfl
        · exact Fin.elim0 j
      rw [heq] at hvg
      exact ⟨Fin.elim0, hvg⟩
    · rintro ⟨y, hy⟩
      change v ∘ g ∈ S
      have heq : v ∘ g = Sum.elim v y := by
        ext (a | j)
        · rfl
        · exact Fin.elim0 j
      rwa [heq]
  | m + 1, S, hS => by
    let split : α ⊕ Fin (m + 1) → Option (α ⊕ Fin m)
      | Sum.inl a => some (Sum.inl a)
      | Sum.inr j => Fin.cases none (fun i ↦ some (Sum.inr i)) j
    have h1 : Dioph {w : Option (α ⊕ Fin m) → ℕ | w ∘ split ∈ S} :=
      hS.reindex_dioph _ split
    have h2 := h1.ex1_dioph
    refine (ex_fin_dioph h2).ext fun v ↦ ?_
    constructor
    · rintro ⟨y, y0, hy⟩
      refine ⟨Fin.cons y0 y, ?_⟩
      have hmem : Option.elim' y0 (Sum.elim v y) ∘ split ∈ S := hy
      have heq : Option.elim' y0 (Sum.elim v y) ∘ split = Sum.elim v (Fin.cons y0 y) := by
        ext (a | j)
        · rfl
        · exact Fin.cases rfl (fun _ ↦ rfl) j
      rwa [heq] at hmem
    · rintro ⟨y, hy⟩
      refine ⟨Fin.tail y, y 0, ?_⟩
      change Option.elim' (y 0) (Sum.elim v (Fin.tail y)) ∘ split ∈ S
      have heq : Option.elim' (y 0) (Sum.elim v (Fin.tail y)) ∘ split = Sum.elim v y := by
        ext (a | j)
        · rfl
        · exact Fin.cases rfl (fun _ ↦ rfl) j
      rwa [heq]

private theorem forall_fin_dioph {α : Type} :
    ∀ {m : ℕ} {S : Fin m → Set (α → ℕ)}, (∀ j, Dioph (S j)) →
      Dioph {v : α → ℕ | ∀ j : Fin m, v ∈ S j}
  | 0, _, _ => (eq_dioph (const_dioph 0) (const_dioph 0)).ext fun _ ↦
      ⟨fun _ (j : Fin 0) ↦ j.elim0, fun _ ↦ rfl⟩
  | m + 1, S, hS => by
    have h0 : Dioph (S 0) := hS 0
    have hrest : Dioph {v | ∀ i : Fin m, v ∈ S i.succ} := forall_fin_dioph fun i ↦ hS i.succ
    exact (inter h0 hrest).ext fun v ↦ (Fin.forall_fin_succ (P := fun j ↦ v ∈ S j)).symm

/-! ### Diophantine representations of `choose`, `factorial`, `pair`, `unpair`, and `beta` -/

private theorem choose_eq_pow_div_mod {n k B : ℕ} (hkn : k ≤ n) (hB : 2 ^ n < B) :
    ((B + 1) ^ n / B ^ k) % B = n.choose k := by
  have hBpos : 0 < B := lt_of_le_of_lt (Nat.zero_le _) hB
  have hBk_pos : 0 < B ^ k := pow_pos hBpos k
  have hexp : (B + 1) ^ n = ∑ j ∈ Finset.range (n + 1), n.choose j * B ^ j := by
    rw [add_pow]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [one_pow, mul_one, mul_comm]; rfl
  -- Split `range (n + 1)` into `j < k`, `j = k`, and `k < j`.
  have hlow : ∑ j ∈ Finset.range k, n.choose j * B ^ j < B ^ k := by
    cases k with
    | zero => simp
    | succ k' =>
      calc ∑ j ∈ Finset.range (k' + 1), n.choose j * B ^ j
          ≤ ∑ j ∈ Finset.range (k' + 1), n.choose j * B ^ k' := by
            refine Finset.sum_le_sum fun j hj ↦ Nat.mul_le_mul_left _ ?_
            exact Nat.pow_le_pow_right hBpos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
        _ = (∑ j ∈ Finset.range (k' + 1), n.choose j) * B ^ k' := (Finset.sum_mul _ _ _).symm
        _ ≤ (∑ j ∈ Finset.range (n + 1), n.choose j) * B ^ k' := by
            refine Nat.mul_le_mul_right _ (Finset.sum_le_sum_of_subset ?_)
            exact Finset.range_mono (by omega)
        _ = 2 ^ n * B ^ k' := by rw [Nat.sum_range_choose]
        _ < B * B ^ k' := Nat.mul_lt_mul_of_pos_right hB (pow_pos hBpos k')
        _ = B ^ (k' + 1) := by rw [pow_succ']
  have hhigh : ∃ Q : ℕ,
      ∑ j ∈ Finset.Ico (k + 1) (n + 1), n.choose j * B ^ j = Q * B * B ^ k := by
    refine ⟨∑ j ∈ Finset.Ico (k + 1) (n + 1), n.choose j * B ^ (j - (k + 1)), ?_⟩
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjk : k + 1 ≤ j := (Finset.mem_Ico.mp hj).1
    calc n.choose j * B ^ j
        = n.choose j * (B ^ (j - (k + 1)) * B ^ (k + 1)) := by
          rw [← pow_add, Nat.sub_add_cancel hjk]
      _ = n.choose j * B ^ (j - (k + 1)) * B * B ^ k := by
          rw [pow_succ']
          ring
  obtain ⟨Q, hQ⟩ := hhigh
  have hsplit : (B + 1) ^ n =
      (∑ j ∈ Finset.range k, n.choose j * B ^ j) + (n.choose k + Q * B) * B ^ k := by
    rw [hexp]
    have h1 : ∑ j ∈ Finset.range (n + 1), n.choose j * B ^ j =
        (∑ j ∈ Finset.range (k + 1), n.choose j * B ^ j) +
        ∑ j ∈ Finset.Ico (k + 1) (n + 1), n.choose j * B ^ j := by
      rw [← Finset.sum_range_add_sum_Ico _ (by omega : k + 1 ≤ n + 1)]
    rw [h1, Finset.sum_range_succ, hQ]
    ring
  have hdiv : (B + 1) ^ n / B ^ k = n.choose k + Q * B := by
    rw [hsplit, Nat.add_mul_div_right _ _ hBk_pos, Nat.div_eq_zero_iff.mpr (Or.inr hlow), zero_add]
  have hck_lt : n.choose k < B := by
    have hle : n.choose k ≤ 2 ^ n := by
      rw [← Nat.sum_range_choose n]
      exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    exact lt_of_le_of_lt hle hB
  rw [hdiv, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hck_lt]

/-- Binomial coefficients `Nat.choose (f v) (g v)` form a Diophantine function. -/
public theorem choose_dioph {α : Type} {f g : (α → ℕ) → ℕ}
    (hf : DiophFn f) (hg : DiophFn g) :
    DiophFn fun v ↦ (f v).choose (g v) := by
  have fn : DiophFn fun v : Option α → ℕ ↦ f (v ∘ some) := reindex_diophFn some hf
  have fg : DiophFn fun v : Option α → ℕ ↦ g (v ∘ some) := reindex_diophFn some hg
  have hB : DiophFn fun v : Option α → ℕ ↦ 2 ^ f (v ∘ some) + 1 :=
    add_dioph (pow_dioph (const_dioph 2) fn) (const_dioph 1)
  have hnum : DiophFn fun v : Option α → ℕ ↦
      ((2 ^ f (v ∘ some) + 1 + 1) ^ f (v ∘ some) /
        (2 ^ f (v ∘ some) + 1) ^ g (v ∘ some)) % (2 ^ f (v ∘ some) + 1) :=
    mod_dioph (div_dioph (pow_dioph (add_dioph hB (const_dioph 1)) fn) (pow_dioph hB fg)) hB
  have hcase1 : Dioph {v : Option α → ℕ | g (v ∘ some) ≤ f (v ∘ some) ∧
      v none = ((2 ^ f (v ∘ some) + 1 + 1) ^ f (v ∘ some) /
        (2 ^ f (v ∘ some) + 1) ^ g (v ∘ some)) % (2 ^ f (v ∘ some) + 1)} :=
    inter (le_dioph fg fn) (eq_dioph (proj_dioph none) hnum)
  have hcase2 : Dioph {v : Option α → ℕ | f (v ∘ some) < g (v ∘ some) ∧ v none = 0} :=
    inter (lt_dioph fn fg) (eq_dioph (proj_dioph none) (const_dioph 0))
  refine (union hcase1 hcase2).ext fun v ↦ Iff.symm ?_
  change (f (v ∘ some)).choose (g (v ∘ some)) = v none ↔ _
  by_cases hle : g (v ∘ some) ≤ f (v ∘ some)
  · have heq := choose_eq_pow_div_mod hle (Nat.lt_succ_self (2 ^ f (v ∘ some)))
    simp only [Set.mem_union, Set.mem_ofPred, hle, true_and, not_lt.mpr hle, false_and,
      or_false, heq, eq_comm]
  · have hlt : f (v ∘ some) < g (v ∘ some) := lt_of_not_ge hle
    simp only [Set.mem_union, Set.mem_ofPred, hle, false_and, hlt, true_and, false_or,
      Nat.choose_eq_zero_of_lt hlt, eq_comm]

private theorem descFactorial_eq_prod_range (r : ℕ) :
    ∀ n : ℕ, r.descFactorial n = ∏ j ∈ Finset.range n, (r - j)
  | 0 => rfl
  | n + 1 => by
    rw [Nat.descFactorial_succ, Finset.prod_range_succ, descFactorial_eq_prod_range r n, mul_comm]

private theorem pow_le_sub_pow_add {r a : ℕ} (har : a ≤ r) :
    ∀ k : ℕ, 1 ≤ k → r ^ k ≤ (r - a) ^ k + k * a * r ^ (k - 1)
  | 0, hk => absurd hk (by decide)
  | 1, _ => by simp [Nat.sub_add_cancel har]
  | k + 2, _ => by
    have ih := pow_le_sub_pow_add har (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at ih ⊢
    have hsub_le : (r - a) ^ (k + 1) ≤ r ^ (k + 1) :=
      Nat.pow_le_pow_left (Nat.sub_le r a) (k + 1)
    calc r ^ (k + 2)
        = r * r ^ (k + 1) := pow_succ' r (k + 1)
      _ ≤ r * ((r - a) ^ (k + 1) + (k + 1) * a * r ^ k) := Nat.mul_le_mul_left r ih
      _ = ((r - a) + a) * (r - a) ^ (k + 1) + (k + 1) * a * (r * r ^ k) := by
          rw [Nat.sub_add_cancel har, mul_add]
          ring
      _ = (r - a) ^ (k + 2) + a * (r - a) ^ (k + 1) + (k + 1) * a * r ^ (k + 1) := by
          rw [add_mul, pow_succ' (r - a) (k + 1), pow_succ' r k]
      _ ≤ (r - a) ^ (k + 2) + a * r ^ (k + 1) + (k + 1) * a * r ^ (k + 1) := by gcongr
      _ = (r - a) ^ (k + 2) + (k + 2) * a * r ^ (k + 1) := by ring

private theorem factorial_eq_pow_div_choose {n : ℕ} (hn : 1 ≤ n) :
    let r := (2 * n) ^ (n + 3)
    r ^ n / r.choose n = n.factorial := by
  intro r
  have h2n : 2 ≤ 2 * n := by omega
  have hnr : n ≤ r := by
    calc n ≤ 2 * n := by omega
      _ = (2 * n) ^ 1 := (pow_one _).symm
      _ ≤ (2 * n) ^ (n + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have hchoose_pos : 0 < r.choose n := Nat.choose_pos hnr
  have hdesc_eq : n.factorial * r.choose n = r.descFactorial n :=
    (Nat.descFactorial_eq_factorial_mul_choose r n).symm
  have hlow : n.factorial ≤ r ^ n / r.choose n := by
    rw [Nat.le_div_iff_mul_le hchoose_pos, hdesc_eq]
    exact Nat.descFactorial_le_pow r n
  have hdesc_ge : (r - n) ^ n ≤ r.descFactorial n := by
    rw [descFactorial_eq_prod_range]
    calc (r - n) ^ n
        = ∏ _j ∈ Finset.range n, (r - n) := by simp
      _ ≤ ∏ j ∈ Finset.range n, (r - j) := by
          refine Finset.prod_le_prod fun j hj ↦ ?_
          have hjn : j < n := Finset.mem_range.mp hj
          omega
  have hsmall : (n.factorial + 1) * n ^ 2 < r := by
    have hfac : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
    have h1 : 1 ≤ n ^ n := Nat.one_le_pow n n hn
    have h2 : 2 < 2 ^ (n + 3) := by
      calc 2 < 2 ^ 3 := by decide
        _ ≤ 2 ^ (n + 3) := Nat.pow_le_pow_right (by decide) (by omega)
    have h3 : n ^ (n + 2) ≤ n ^ (n + 3) := Nat.pow_le_pow_right hn (by omega)
    calc (n.factorial + 1) * n ^ 2
        ≤ (n ^ n + n ^ n) * n ^ 2 := by gcongr
      _ = 2 * n ^ (n + 2) := by rw [← two_mul, mul_assoc, ← pow_add]
      _ < 2 ^ (n + 3) * n ^ (n + 3) := by
          exact lt_of_lt_of_le
            (Nat.mul_lt_mul_of_pos_right h2 (pow_pos hn (n + 2)))
            (Nat.mul_le_mul_left _ h3)
      _ = r := by rw [← mul_pow]
  have hbern := pow_le_sub_pow_add hnr n hn
  have hrpow_pos : 0 < r ^ (n - 1) := pow_pos (by omega) (n - 1)
  have hrpow_eq : r * r ^ (n - 1) = r ^ n := by
    conv_rhs => rw [← Nat.sub_add_cancel hn, pow_succ']
  have hlt_fac : n.factorial * r ^ n < (n.factorial + 1) * (r - n) ^ n := by
    have hm := Nat.mul_le_mul_left (n.factorial + 1) hbern
    have hstep : (n.factorial + 1) * (n * n * r ^ (n - 1)) < r ^ n := by
      calc (n.factorial + 1) * (n * n * r ^ (n - 1))
          = ((n.factorial + 1) * n ^ 2) * r ^ (n - 1) := by ring
        _ < r * r ^ (n - 1) := Nat.mul_lt_mul_of_pos_right hsmall hrpow_pos
        _ = r ^ n := hrpow_eq
    have hsum : n.factorial * r ^ n + r ^ n ≤
        (n.factorial + 1) * (r - n) ^ n + (n.factorial + 1) * (n * n * r ^ (n - 1)) := by
      simpa [add_mul, one_mul, mul_add] using hm
    omega
  have hup : r ^ n / r.choose n < n.factorial + 1 := by
    refine Nat.div_lt_of_lt_mul ?_
    have hmul : n.factorial * r ^ n < n.factorial * ((n.factorial + 1) * r.choose n) := by
      calc n.factorial * r ^ n
          < (n.factorial + 1) * (r - n) ^ n := hlt_fac
        _ ≤ (n.factorial + 1) * r.descFactorial n := Nat.mul_le_mul_left _ hdesc_ge
        _ = (n.factorial + 1) * (n.factorial * r.choose n) := by rw [hdesc_eq]
        _ = n.factorial * ((n.factorial + 1) * r.choose n) := by ring
    exact Nat.lt_of_mul_lt_mul_left (by simpa [mul_comm (r.choose n)] using hmul)
  omega

/-- Factorials `(f v).factorial` form a Diophantine function. -/
public theorem factorial_dioph {α : Type} {f : (α → ℕ) → ℕ} (hf : DiophFn f) :
    DiophFn fun v ↦ (f v).factorial := by
  let rFn : (Option α → ℕ) → ℕ := fun v ↦ (2 * f (v ∘ some)) ^ (f (v ∘ some) + 3)
  let qFn : (Option α → ℕ) → ℕ := fun v ↦ rFn v ^ f (v ∘ some) / (rFn v).choose (f (v ∘ some))
  have fn : DiophFn fun v : Option α → ℕ ↦ f (v ∘ some) := reindex_diophFn some hf
  have fr : DiophFn rFn :=
    pow_dioph (mul_dioph (const_dioph 2) fn) (add_dioph fn (const_dioph 3))
  have fquot : DiophFn qFn :=
    div_dioph (pow_dioph fr fn) (choose_dioph fr fn)
  have hc0 : Dioph {v : Option α → ℕ | f (v ∘ some) = 0 ∧ v none = 1} :=
    inter (eq_dioph fn (const_dioph 0)) (eq_dioph (proj_dioph none) (const_dioph 1))
  have hc1 : Dioph {v : Option α → ℕ | 1 ≤ f (v ∘ some) ∧ v none = qFn v} :=
    inter (le_dioph (const_dioph 1) fn) (eq_dioph (proj_dioph none) fquot)
  refine (union hc0 hc1).ext fun v ↦ Iff.symm ?_
  change (f (v ∘ some)).factorial = v none ↔ _
  rcases Nat.eq_zero_or_pos (f (v ∘ some)) with h0 | hpos
  · simp [h0, eq_comm]
  · have h1 : 1 ≤ f (v ∘ some) := hpos
    have h0' : f (v ∘ some) ≠ 0 := by omega
    have hfac := factorial_eq_pow_div_choose h1
    simp only [Set.mem_union, Set.mem_ofPred, h0', false_and, h1, true_and, false_or, qFn, rFn]
    rw [hfac, eq_comm]

/-- Cantor pairing `Nat.pair (f v) (g v)` is a Diophantine function. -/
public theorem pair_dioph {α : Type} {f g : (α → ℕ) → ℕ}
    (hf : DiophFn f) (hg : DiophFn g) :
    DiophFn fun v ↦ Nat.pair (f v) (g v) := by
  have fa : DiophFn fun v : Option α → ℕ ↦ f (v ∘ some) := reindex_diophFn some hf
  have fb : DiophFn fun v : Option α → ℕ ↦ g (v ∘ some) := reindex_diophFn some hg
  have hc1 : Dioph {v : Option α → ℕ | f (v ∘ some) < g (v ∘ some) ∧
      v none = g (v ∘ some) * g (v ∘ some) + f (v ∘ some)} :=
    inter (lt_dioph fa fb) (eq_dioph (proj_dioph none) (add_dioph (mul_dioph fb fb) fa))
  have hc2 : Dioph {v : Option α → ℕ | g (v ∘ some) ≤ f (v ∘ some) ∧
      v none = f (v ∘ some) * f (v ∘ some) + f (v ∘ some) + g (v ∘ some)} :=
    inter (le_dioph fb fa)
      (eq_dioph (proj_dioph none) (add_dioph (add_dioph (mul_dioph fa fa) fa) fb))
  refine (union hc1 hc2).ext fun v ↦ Iff.symm ?_
  change Nat.pair (f (v ∘ some)) (g (v ∘ some)) = v none ↔ _
  simp only [Nat.pair, Set.mem_union, Set.mem_ofPred]
  split_ifs with h
  · simp [h, not_le.mpr h, eq_comm]
  · simp [h, le_of_not_gt h, eq_comm]

/-- Left Cantor unpairing `(Nat.unpair (f v)).1` is a Diophantine function. -/
public theorem unpair_left_dioph {α : Type} {f : (α → ℕ) → ℕ} (hf : DiophFn f) :
    DiophFn fun v ↦ (f v).unpair.1 := by
  have h : Dioph {w : Option (Option α) → ℕ |
      Nat.pair (w (some none)) (w none) = f (w ∘ some ∘ some)} :=
    eq_dioph (pair_dioph (proj_dioph (some none)) (proj_dioph none))
      (reindex_diophFn (some ∘ some) hf)
  refine h.ex1_dioph.ext fun v ↦ Iff.symm ?_
  change (f (v ∘ some)).unpair.1 = v none ↔ ∃ b : ℕ, Nat.pair (v none) b = f (v ∘ some)
  constructor
  · intro ha
    exact ⟨(f (v ∘ some)).unpair.2, by rw [← ha, Nat.pair_unpair]⟩
  · rintro ⟨b, hb⟩
    rw [← hb, Nat.unpair_pair]

/-- Right Cantor unpairing `(Nat.unpair (f v)).2` is a Diophantine function. -/
public theorem unpair_right_dioph {α : Type} {f : (α → ℕ) → ℕ} (hf : DiophFn f) :
    DiophFn fun v ↦ (f v).unpair.2 := by
  have h : Dioph {w : Option (Option α) → ℕ |
      Nat.pair (w none) (w (some none)) = f (w ∘ some ∘ some)} :=
    eq_dioph (pair_dioph (proj_dioph none) (proj_dioph (some none)))
      (reindex_diophFn (some ∘ some) hf)
  refine h.ex1_dioph.ext fun v ↦ Iff.symm ?_
  change (f (v ∘ some)).unpair.2 = v none ↔ ∃ a : ℕ, Nat.pair a (v none) = f (v ∘ some)
  constructor
  · intro hb
    exact ⟨(f (v ∘ some)).unpair.1, by rw [← hb, Nat.pair_unpair]⟩
  · rintro ⟨a, ha⟩
    rw [← ha, Nat.unpair_pair]

/-- Gödel's beta function `Nat.beta (f v) (g v)` is a Diophantine function. -/
public theorem beta_dioph {α : Type} {f g : (α → ℕ) → ℕ}
    (hf : DiophFn f) (hg : DiophFn g) :
    DiophFn fun v ↦ Nat.beta (f v) (g v) :=
  mod_dioph (unpair_left_dioph hf)
    (add_dioph (mul_dioph (add_dioph hg (const_dioph 1)) (unpair_right_dioph hf))
      (const_dioph 1))

/-! ### Davis–Putnam–Robinson bounded universal quantification -/

private def dprMod (M i : ℕ) : ℕ := M.factorial / i + 1

private theorem mul_dprMod {M i : ℕ} (hi1 : 1 ≤ i) (hiM : i ≤ M) :
    i * dprMod M i = M.factorial + i := by
  unfold dprMod
  rw [mul_add, mul_one, Nat.mul_div_cancel' (Nat.dvd_factorial hi1 hiM)]

private theorem two_le_dprMod {M i : ℕ} (hi1 : 1 ≤ i) (hiM : i ≤ M) :
    2 ≤ dprMod M i := by
  unfold dprMod
  have hle : i ≤ M.factorial := Nat.le_of_dvd (Nat.factorial_pos M) (Nat.dvd_factorial hi1 hiM)
  have hdiv : 1 ≤ M.factorial / i := (Nat.le_div_iff_mul_le hi1).mpr (by omega)
  omega

private theorem prod_Icc_one_succ {M : Type*} [CommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∏ i ∈ Finset.Icc 1 (k + 1), f i = (∏ i ∈ Finset.Icc 1 k, f i) * f (k + 1) := by
  have heq : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [heq, Finset.prod_insert (by simp), mul_comm]

private theorem prod_Icc_one_id (n : ℕ) : ∏ i ∈ Finset.Icc 1 n, i = n.factorial := by
  induction n with
  | zero => rfl
  | succ k ih => rw [prod_Icc_one_succ (fun i ↦ i) k, ih, Nat.factorial_succ, mul_comm]

private theorem prod_dprMod {M n : ℕ} (hnM : n ≤ M) :
    ∏ i ∈ Finset.Icc 1 n, dprMod M i = (M.factorial + n).choose n := by
  have hmul : n.factorial * ∏ i ∈ Finset.Icc 1 n, dprMod M i =
      n.factorial * (M.factorial + n).choose n := by
    rw [← prod_Icc_one_id n, ← Finset.prod_mul_distrib]
    have h1 : ∏ i ∈ Finset.Icc 1 n, (i * dprMod M i) =
        ∏ i ∈ Finset.Icc 1 n, (M.factorial + i) := by
      refine Finset.prod_congr rfl fun i hi ↦ ?_
      rcases Finset.mem_Icc.mp hi with ⟨h1, h2⟩
      exact mul_dprMod h1 (h2.trans hnM)
    rw [h1, prod_Icc_one_id n]
    have hasc : ∏ i ∈ Finset.Icc 1 n, (M.factorial + i) = (M.factorial + 1).ascFactorial n := by
      clear h1 hnM
      induction n with
      | zero => rfl
      | succ k ih =>
        rw [prod_Icc_one_succ (fun i ↦ M.factorial + i) k, ih, Nat.ascFactorial_succ]
        ring
    rw [hasc, Nat.ascFactorial_eq_factorial_mul_choose]
  exact Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos n) hmul

private theorem lt_prime_of_dvd_dprMod {M n i p : ℕ} (hMn : 2 * n ≤ M)
    (hi1 : 1 ≤ i) (hin : i ≤ n) (hp : p.Prime) (hdvd : p ∣ dprMod M i) :
    M < p := by
  by_contra hle
  push Not at hle
  have hpdvd_div : p ∣ M.factorial / i := by
    by_cases hpi : p ∣ i
    · have hfac_prod : ∏ k ∈ Finset.Icc 1 M, k = M.factorial := by
        clear hle hdvd hpi hin hi1 hMn
        induction M with
        | zero => simp
        | succ k ih =>
          rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1), ih, Nat.factorial_succ, mul_comm]
      have hsub : ({i, 2 * i} : Finset ℕ) ⊆ Finset.Icc 1 M := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hne : i ≠ 2 * i := by omega
      have hsub : ({i, 2 * i} : Finset ℕ) ⊆ Finset.Icc 1 M := fun x hx ↦ by
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_Icc.mpr ⟨hi1, by omega⟩
        · rw [Finset.mem_singleton.mp hx]; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hne : i ≠ 2 * i := by omega
      have hpair_dvd : i * (2 * i) ∣ M.factorial := by
        rw [← hfac_prod]
        have hp2 : ∏ k ∈ ({i, 2 * i} : Finset ℕ), k = i * (2 * i) :=
          Finset.prod_pair hne
        rw [← hp2]
        exact Finset.prod_dvd_prod_of_subset _ _ (fun k ↦ k) hsub
      have hip : i * p ∣ M.factorial :=
        dvd_trans (Nat.mul_dvd_mul_left i (dvd_trans hpi (dvd_mul_left i 2))) hpair_dvd
      rcases hip with ⟨q, hq⟩
      have hdiv : M.factorial / i = p * q := by
        rw [hq, mul_assoc, Nat.mul_div_cancel_left _ hi1]
      exact ⟨q, hdiv⟩
    · have hpM : p ∣ M.factorial := Nat.dvd_factorial hp.pos hle
      have heq : M.factorial = i * (M.factorial / i) :=
        (Nat.mul_div_cancel' (Nat.dvd_factorial hi1 (by omega))).symm
      rw [heq] at hpM
      exact (hp.coprime_iff_not_dvd.mpr hpi).dvd_of_dvd_mul_left hpM
  have hp1 : p ∣ 1 := by
    have := Nat.dvd_sub hdvd hpdvd_div
    simpa [dprMod] using this
  exact hp.not_dvd_one hp1

private theorem pairwise_coprime_dprMod {M n : ℕ} (hMn : 2 * n ≤ M) :
    (Finset.Icc 1 n : Set ℕ).Pairwise fun i j ↦ Nat.Coprime (dprMod M i) (dprMod M j) := by
  intro i hi j hj hij
  rcases Finset.mem_Icc.mp hi with ⟨hi1, hin⟩
  rcases Finset.mem_Icc.mp hj with ⟨hj1, hjn⟩
  refine Nat.coprime_of_dvd fun p hp hpi hpj ↦ ?_
  have hMp : M < p := lt_prime_of_dvd_dprMod hMn hi1 hin hp hpi
  have hbi : p ∣ M.factorial + i := by
    rw [← mul_dprMod hi1 (by omega)]
    exact dvd_mul_of_dvd_right hpi i
  have hbj : p ∣ M.factorial + j := by
    rw [← mul_dprMod hj1 (by omega)]
    exact dvd_mul_of_dvd_right hpj j
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hdiff : p ∣ j - i := by
      have := Nat.dvd_sub hbj hbi
      have hsub : M.factorial + j - (M.factorial + i) = j - i := by omega
      rwa [hsub] at this
    have := Nat.le_of_dvd (by omega) hdiff
    omega
  · have hdiff : p ∣ i - j := by
      have := Nat.dvd_sub hbi hbj
      have hsub : M.factorial + i - (M.factorial + j) = i - j := by omega
      rwa [hsub] at this
    have := Nat.le_of_dvd (by omega) hdiff
    omega

private theorem int_factorial_mul_choose_eq_prod (Y K : ℕ) :
    (((K + 1).factorial * Y.choose (K + 1) : ℕ) : ℤ) =
      ∏ k ∈ Finset.range (K + 1), ((Y : ℤ) - (k : ℤ)) := by
  by_cases hY : Y ≤ K
  · rw [Nat.choose_eq_zero_of_lt (by omega : Y < K + 1), mul_zero, Nat.cast_zero]
    symm
    exact Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : Y < K + 1)) (sub_self _)
  · rw [← Nat.descFactorial_eq_factorial_mul_choose, descFactorial_eq_prod_range, Nat.cast_prod]
    refine Finset.prod_congr rfl fun k hk ↦ ?_
    have hkY : k ≤ Y := by have := Finset.mem_range.mp hk; omega
    exact Nat.cast_sub hkY

private theorem eval_int_modEq {σ : Type*} (p : MvPolynomial σ ℤ) {m : ℤ} {u v : σ → ℤ}
    (huv : ∀ s, u s ≡ v s [ZMOD m]) :
    eval u p ≡ eval v p [ZMOD m] := by
  induction p using MvPolynomial.induction_on with
  | C _ => simp [Int.ModEq.refl]
  | add _ _ ihp ihq => simpa only [map_add] using ihp.add ihq
  | mul_X _ s ihp => simpa only [map_mul, eval_X] using ihp.mul (huv s)

private theorem natAbs_eval_lt_bound {σ : Type*} (P : MvPolynomial σ ℤ) (u : σ → ℤ) (A : ℕ)
    (hA : ∀ s, (u s).natAbs ≤ A) :
    (eval u P).natAbs <
      ((∑ s ∈ P.support, (P.coeff s).natAbs) + 1) * (A + 1) ^ P.totalDegree := by
  classical
  have hsum_abs : ∀ S : Finset (σ →₀ ℕ),
      (∑ s ∈ S, eval u (monomial s (P.coeff s))).natAbs ≤
        ∑ s ∈ S, (eval u (monomial s (P.coeff s))).natAbs := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)
  have hprod_abs : ∀ (s : σ →₀ ℕ) (T : Finset σ),
      (∏ i ∈ T, u i ^ s i).natAbs = ∏ i ∈ T, (u i ^ s i).natAbs := by
    intro s T
    induction T using Finset.induction_on with
    | empty => simp
    | insert a T ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Int.natAbs_mul, ih]
  have h1 : (eval u P).natAbs ≤
      ∑ s ∈ P.support, (P.coeff s).natAbs * (A + 1) ^ P.totalDegree := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    refine (hsum_abs P.support).trans (Finset.sum_le_sum fun s hs ↦ ?_)
    rw [eval_monomial, Finsupp.prod, Int.natAbs_mul, hprod_abs s s.support]
    refine Nat.mul_le_mul_left _ ?_
    calc ∏ i ∈ s.support, (u i ^ s i).natAbs
        ≤ ∏ i ∈ s.support, (A + 1) ^ s i := by
          refine Finset.prod_le_prod fun i _ ↦ ?_
          rw [Int.natAbs_pow]
          exact Nat.pow_le_pow_left ((hA i).trans (Nat.le_succ A)) (s i)
      _ = (A + 1) ^ (s.sum fun _ e ↦ e) := by
          rw [Finset.prod_pow_eq_pow_sum, Finsupp.sum]
      _ ≤ (A + 1) ^ P.totalDegree :=
          Nat.pow_le_pow_right (Nat.succ_pos A) (le_totalDegree hs)
  rw [← Finset.sum_mul] at h1
  have hpow : 0 < (A + 1) ^ P.totalDegree := pow_pos (Nat.succ_pos A) P.totalDegree
  calc (eval u P).natAbs
      ≤ (∑ s ∈ P.support, (P.coeff s).natAbs) * (A + 1) ^ P.totalDegree := h1
    _ < ((∑ s ∈ P.support, (P.coeff s).natAbs) + 1) * (A + 1) ^ P.totalDegree :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hpow

private theorem prime_dvd_prod_int {p : ℕ} (hp : p.Prime) {ι : Type*} (s : Finset ι)
    (f : ι → ℤ) (hdvd : (p : ℤ) ∣ ∏ i ∈ s, f i) :
    ∃ i ∈ s, (p : ℤ) ∣ f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty] at hdvd
    exact absurd (Int.natAbs_dvd_natAbs.mpr hdvd) hp.not_dvd_one
  | insert a s has ih =>
    rw [Finset.prod_insert has] at hdvd
    rcases hp.prime.dvd_or_dvd (Int.natAbs_dvd_natAbs.mpr hdvd |> fun h ↦ by
      rwa [Int.natAbs_natCast, Int.natAbs_mul] at h) with h1 | h2
    · exact ⟨a, Finset.mem_insert_self a s, Int.ofNat_dvd_left.mpr h1⟩
    · obtain ⟨i, his, hi⟩ := ih (Int.ofNat_dvd_left.mpr h2)
      exact ⟨i, Finset.mem_insert_of_mem his, hi⟩

private theorem prod_coprime_dvd_nat {ι : Type*} (s : Finset ι) (d : ι → ℕ) (z : ℕ)
    (hcop : (s : Set ι).Pairwise fun i j ↦ Nat.Coprime (d i) (d j))
    (hdvd : ∀ i ∈ s, d i ∣ z) :
    (∏ i ∈ s, d i) ∣ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has]
    have hcop_s : (s : Set ι).Pairwise fun i j ↦ Nat.Coprime (d i) (d j) :=
      hcop.mono (Finset.subset_insert a s)
    have hda : d a ∣ z := hdvd a (Finset.mem_insert_self a s)
    have hds : (∏ i ∈ s, d i) ∣ z :=
      ih hcop_s fun i hi ↦ hdvd i (Finset.mem_insert_of_mem hi)
    have hca : Nat.Coprime (d a) (∏ i ∈ s, d i) :=
      Nat.coprime_prod_right_iff.mpr fun i hi ↦
        hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
          (fun h ↦ has (h ▸ hi))
    exact hca.mul_dvd_of_dvd_of_dvd hda hds

/-- **Davis–Putnam–Robinson Bounded Universal Quantification Theorem**: if a relation
`S : Set (Option (Fin r) → ℕ)` is Diophantine, then for any Diophantine upper bound `bound`,
the relation `∀ i, 1 ≤ i → i ≤ bound v → (Option.elim' i v) ∈ S` is also Diophantine.
-/
public theorem bounded_forall_dioph {r : ℕ} {S : Set (Option (Fin r) → ℕ)}
    (hS : Dioph S) {bound : (Fin r → ℕ) → ℕ} (hbound : DiophFn bound) :
    Dioph {v : Fin r → ℕ | ∀ i : ℕ, 1 ≤ i → i ≤ bound v → (Option.elim' i v) ∈ S} := by
  classical
  obtain ⟨m, P, hP⟩ := dioph_iff_exists_mvPoly.mp hS
  let Ccoeff : ℕ := (∑ s ∈ P.support, (P.coeff s).natAbs) + 1
  let D : ℕ := P.totalDegree
  -- Existential block: `(K, M, B, W)` in `Fin 4` and `Y` in `Fin m`, so `Fin (4 + m)`.
  let vSum : (Fin r → ℕ) → ℕ := fun v ↦ ∑ a : Fin r, v a
  have hvSum_dioph : DiophFn vSum := by
    have : ∀ l : List (Fin r), DiophFn fun v : Fin r → ℕ ↦ (l.map v).sum := by
      intro l
      induction l with
      | nil => exact const_dioph 0
      | cons a as ih => exact add_dioph (proj_dioph a) ih
    convert this Finset.univ.toList using 1
    ext v
    exact (Finset.sum_map_toList Finset.univ v).symm
  -- Build polynomial `Pneg` over `(Fin r ⊕ Fin 4) ⊕ Fin m` substituting `none ↦ -B` (`B = idx 2`).
  let substNeg : Option (Fin r) ⊕ Fin m → MvPolynomial (Fin r ⊕ (Fin 4 ⊕ Fin m)) ℤ
    | Sum.inl none => -X (Sum.inr (Sum.inl 2))
    | Sum.inl (some a) => X (Sum.inl a)
    | Sum.inr j => X (Sum.inr (Sum.inr j))
  let Pneg : Poly (Fin r ⊕ (Fin 4 ⊕ Fin m)) := mvPolyToPoly (eval₂ C substNeg P)
  have hPneg_eval : ∀ (v : Fin r → ℕ) (w : Fin 4 → ℕ) (Y : Fin m → ℕ),
      Pneg (Sum.elim v (Sum.elim w Y)) =
        eval (Sum.elim
          (fun o : Option (Fin r) ↦ Option.casesOn o (-(w 2 : ℤ)) fun a ↦ (v a : ℤ))
          (fun j ↦ (Y j : ℤ))) P := by
    intro v w Y
    rw [show Pneg = mvPolyToPoly (eval₂ C substNeg P) from rfl, mvPolyToPoly_apply, eval_eval₂_C]
    refine congrArg (fun g ↦ eval g P) (funext fun u ↦ ?_)
    cases u with
    | inl o => cases o <;> simp [substNeg]
    | inr j => simp [substNeg]
  -- Core Diophantine predicate on `u : Fin r ⊕ (Fin 4 ⊕ Fin m) → ℕ`:
  let fn : (Fin r ⊕ (Fin 4 ⊕ Fin m) → ℕ) → ℕ := fun u ↦ bound (u ∘ Sum.inl)
  let fvSum : (Fin r ⊕ (Fin 4 ⊕ Fin m) → ℕ) → ℕ := fun u ↦ vSum (u ∘ Sum.inl)
  let fK : (Fin r ⊕ (Fin 4 ⊕ Fin m) → ℕ) → ℕ := fun u ↦ u (Sum.inr (Sum.inl 0))
  let fM : (Fin r ⊕ (Fin 4 ⊕ Fin m) → ℕ) → ℕ := fun u ↦ u (Sum.inr (Sum.inl 1))
  let fB : (Fin r ⊕ (Fin 4 ⊕ Fin m) → ℕ) → ℕ := fun u ↦ u (Sum.inr (Sum.inl 2))
  let fW : (Fin r ⊕ (Fin 4 ⊕ Fin m) → ℕ) → ℕ := fun u ↦ u (Sum.inr (Sum.inl 3))
  let fY : Fin m → (Fin r ⊕ (Fin 4 ⊕ Fin m) → ℕ) → ℕ := fun j u ↦ u (Sum.inr (Sum.inr j))
  have dfn : DiophFn fn := reindex_diophFn Sum.inl hbound
  have dfvSum : DiophFn fvSum := reindex_diophFn Sum.inl hvSum_dioph
  have dfK : DiophFn fK := proj_dioph _
  have dfM : DiophFn fM := proj_dioph _
  have dfB : DiophFn fB := proj_dioph _
  have dfW : DiophFn fW := proj_dioph _
  have dfY : ∀ j, DiophFn (fY j) := fun j ↦ proj_dioph _
  have dfBound : DiophFn fun u ↦ Ccoeff * (fn u + fvSum u + fK u + 1) ^ D :=
    mul_dioph (const_dioph Ccoeff)
      (pow_dioph (add_dioph (add_dioph (add_dioph dfn dfvSum) dfK) (const_dioph 1))
        (const_dioph D))
  have dCond : Dioph {u : Fin r ⊕ (Fin 4 ⊕ Fin m) → ℕ |
      2 * fn u ≤ fM u ∧
      fK u < fM u ∧
      Ccoeff * (fn u + fvSum u + fK u + 1) ^ D ≤ fM u ∧
      fB u = (fM u).factorial ∧
      fW u = (fB u + fn u).choose (fn u) ∧
      fW u ∣ (Pneg u).natAbs ∧
      ∀ j : Fin m, fW u ∣ (fK u + 1).factorial * (fY j u).choose (fK u + 1)} :=
    inter (le_dioph (mul_dioph (const_dioph 2) dfn) dfM) <|
    inter (lt_dioph dfK dfM) <|
    inter (le_dioph dfBound dfM) <|
    inter (eq_dioph dfB (factorial_dioph dfM)) <|
    inter (eq_dioph dfW (choose_dioph (add_dioph dfB dfn) dfn)) <|
    inter (dvd_dioph dfW (abs_poly_dioph Pneg)) <|
    forall_fin_dioph fun j ↦
      dvd_dioph dfW (mul_dioph (factorial_dioph (add_dioph dfK (const_dioph 1)))
        (choose_dioph (dfY j) (add_dioph dfK (const_dioph 1))))
  -- Existentially quantify `Fin 4` and `Fin m`.
  have dExM : Dioph {u : Fin r ⊕ Fin 4 → ℕ | ∃ Y : Fin m → ℕ,
      Sum.elim (u ∘ Sum.inl) (Sum.elim (u ∘ Sum.inr) Y) ∈
        {u | 2 * fn u ≤ fM u ∧ fK u < fM u ∧
          Ccoeff * (fn u + fvSum u + fK u + 1) ^ D ≤ fM u ∧
          fB u = (fM u).factorial ∧ fW u = (fB u + fn u).choose (fn u) ∧
          fW u ∣ (Pneg u).natAbs ∧
          ∀ j : Fin m, fW u ∣ (fK u + 1).factorial * (fY j u).choose (fK u + 1)}} := by
    let assoc : Fin r ⊕ (Fin 4 ⊕ Fin m) → (Fin r ⊕ Fin 4) ⊕ Fin m
      | Sum.inl a => Sum.inl (Sum.inl a)
      | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
      | Sum.inr (Sum.inr j) => Sum.inr j
    refine (ex_fin_dioph (dCond.reindex_dioph ((Fin r ⊕ Fin 4) ⊕ Fin m) assoc)).ext
      fun u ↦ exists_congr fun Y ↦ ?_
    have heq : Sum.elim u Y ∘ assoc = Sum.elim (u ∘ Sum.inl) (Sum.elim (u ∘ Sum.inr) Y) := by
      ext (a | (b | j)) <;> rfl
    simp [heq]
  refine (ex_fin_dioph dExM).ext fun v ↦ ?_
  simp only [Set.mem_ofPred, fn, fvSum, fK, fM, fB, fW, fY, Sum.elim_comp_inl,
    Sum.elim_comp_inr]
  set n := bound v
  constructor
  · -- Soundness: from DPR witnesses `(w, Y)`, extract a root `y` for each `1 ≤ i ≤ n`.
    rintro ⟨w, Y, h2n, hKM, hBM, hB, hW, hdvdP, hdvdY⟩ i hi1 hin
    dsimp only [Sum.elim_inr, Sum.elim_inl] at h2n hKM hBM hB hW hdvdP hdvdY
    rw [hP]
    set K := w 0
    set M := w 1
    let di := dprMod M i
    have hdi2 : 2 ≤ di := two_le_dprMod hi1 (by omega)
    let p := di.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpdi : p ∣ di := Nat.minFac_dvd di
    have hMp : M < p := lt_prime_of_dvd_dprMod h2n hi1 hin hp hpdi
    have hdiW : di ∣ w 3 := by
      rw [hW, hB, ← prod_dprMod (by omega : n ≤ M)]
      exact Finset.dvd_prod_of_mem (dprMod M) (Finset.mem_Icc.mpr ⟨hi1, hin⟩)
    have hpW : p ∣ w 3 := dvd_trans hpdi hdiW
    have hy_ex : ∀ j : Fin m, ∃ k : ℕ, k ≤ K ∧ (Y j : ℤ) ≡ (k : ℤ) [ZMOD (p : ℤ)] := by
      intro j
      have h1 : (p : ℤ) ∣ (((K + 1).factorial * (Y j).choose (K + 1) : ℕ) : ℤ) :=
        Int.ofNat_dvd.mpr (dvd_trans hpW (hdvdY j))
      rw [int_factorial_mul_choose_eq_prod] at h1
      obtain ⟨k, hk, hpk⟩ := prime_dvd_prod_int hp (Finset.range (K + 1)) _ h1
      exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk),
        Int.modEq_iff_dvd.mpr (by simpa only [neg_sub] using hpk.neg_right)⟩
    choose y hyK hymod using hy_ex
    refine ⟨y, ?_⟩
    have hBmod : -(w 2 : ℤ) ≡ (i : ℤ) [ZMOD (p : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      have h1 : p ∣ w 2 + i := by
        rw [hB, ← mul_dprMod hi1 (by omega)]
        exact dvd_mul_of_dvd_right hpdi i
      have h2 : (p : ℤ) ∣ ((w 2 + i : ℕ) : ℤ) := Int.ofNat_dvd.mpr h1
      convert h2 using 1
      push_cast
      ring
    have heval_mod := eval_int_modEq P (m := (p : ℤ))
      (u := Sum.elim (fun o : Option (Fin r) ↦ Option.casesOn o (-(w 2 : ℤ)) fun a ↦ (v a : ℤ))
        (fun j ↦ (Y j : ℤ)))
      (v := fun s ↦ ((Sum.elim (Option.elim' i v) y s : ℕ) : ℤ))
      (fun s ↦ by
        cases s with
        | inl o =>
          cases o with
          | none => exact hBmod
          | some a => exact Int.ModEq.refl _
        | inr j => exact hymod j)
    have hpPneg : (p : ℤ) ∣ Pneg (Sum.elim v (Sum.elim w Y)) :=
      Int.ofNat_dvd_left.mpr (dvd_trans hpW hdvdP)
    rw [hPneg_eval] at hpPneg
    have hpP : p ∣ (eval (fun s ↦ ((Sum.elim (Option.elim' i v) y s : ℕ) : ℤ)) P).natAbs := by
      refine Int.ofNat_dvd_left.mp ?_
      exact Int.modEq_zero_iff_dvd.mp (heval_mod.symm.trans (Int.modEq_zero_iff_dvd.mpr hpPneg))
    have hlt_p : (eval (fun s ↦ ((Sum.elim (Option.elim' i v) y s : ℕ) : ℤ)) P).natAbs < p := by
      refine lt_of_lt_of_le (natAbs_eval_lt_bound P _ (n + vSum v + K) fun s ↦ ?_)
        (le_trans hBM hMp.le)
      cases s with
      | inl o =>
        cases o with
        | none =>
          change i ≤ n + vSum v + K
          omega
        | some a =>
          have ha : v a ≤ vSum v :=
            Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
          change v a ≤ n + vSum v + K
          omega
      | inr j =>
        have hj := hyK j
        change y j ≤ n + vSum v + K
        omega
    have h0 : (eval (fun s ↦ ((Sum.elim (Option.elim' i v) y s : ℕ) : ℤ)) P).natAbs = 0 :=
      Nat.eq_zero_of_dvd_of_lt hpP hlt_p
    exact Int.natAbs_eq_zero.mp h0
  · -- Completeness: assemble per-`i` roots via the Chinese Remainder Theorem.
    intro hall
    have hy_all : ∀ i : ℕ, ∃ y : Fin m → ℕ,
        1 ≤ i → i ≤ n → eval (fun s ↦ ((Sum.elim (Option.elim' i v) y s : ℕ) : ℤ)) P = 0 := by
      intro i
      by_cases hi : 1 ≤ i ∧ i ≤ n
      · obtain ⟨y, hy⟩ := (hP (Option.elim' i v)).mp (hall i hi.1 hi.2)
        exact ⟨y, fun _ _ ↦ hy⟩
      · exact ⟨fun _ ↦ 0, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hi⟩
    choose y hy using hy_all
    let K : ℕ := (Finset.Icc 1 n).sup fun i ↦ Finset.univ.sup fun j : Fin m ↦ y i j
    have hyK : ∀ i ∈ Finset.Icc 1 n, ∀ j : Fin m, y i j ≤ K := fun i hi j ↦
      le_trans (Finset.le_sup (f := fun j : Fin m ↦ y i j) (Finset.mem_univ j))
        (Finset.le_sup (f := fun i ↦ Finset.univ.sup fun j : Fin m ↦ y i j) hi)
    let M : ℕ := max (2 * n) (max (K + 1) (Ccoeff * (n + vSum v + K + 1) ^ D))
    have h2n : 2 * n ≤ M := le_max_left _ _
    have hKM : K < M := lt_of_lt_of_le (Nat.lt_succ_self K)
      (le_trans (le_max_left _ _) (le_max_right _ _))
    have hBM : Ccoeff * (n + vSum v + K + 1) ^ D ≤ M :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    let B := M.factorial
    let W := (B + n).choose n
    have hcop := pairwise_coprime_dprMod h2n
    have hmod_ne : ∀ i ∈ Finset.Icc 1 n, dprMod M i ≠ 0 := fun i hi ↦ by
      rcases Finset.mem_Icc.mp hi with ⟨h1, h2⟩
      have hiM : i ≤ M := le_trans h2 (le_trans (by omega : n ≤ 2 * n) h2n)
      exact ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) (two_le_dprMod h1 hiM))
    let Y : Fin m → ℕ := fun j ↦
      (Nat.chineseRemainderOfFinset (fun i ↦ y i j) (dprMod M) (Finset.Icc 1 n)
        hmod_ne hcop).val
    have hYmod : ∀ j : Fin m, ∀ i ∈ Finset.Icc 1 n,
        (Y j : ℤ) ≡ (y i j : ℤ) [ZMOD (dprMod M i : ℤ)] := fun j i hi ↦
      Int.natCast_modEq_iff.mpr
        ((Nat.chineseRemainderOfFinset (fun i ↦ y i j) (dprMod M) (Finset.Icc 1 n)
          hmod_ne hcop).property i hi)
    let w : Fin 4 → ℕ := ![K, M, B, W]
    refine ⟨w, Y, h2n, hKM, hBM, rfl, rfl, ?_, ?_⟩
    · change W ∣ (Pneg (Sum.elim v (Sum.elim w Y))).natAbs
      rw [hPneg_eval, show W = ∏ i ∈ Finset.Icc 1 n, dprMod M i from (prod_dprMod (by omega)).symm]
      refine prod_coprime_dvd_nat (Finset.Icc 1 n) (dprMod M) _ hcop fun i hi ↦ ?_
      rcases Finset.mem_Icc.mp hi with ⟨hi1, hin⟩
      refine Int.ofNat_dvd_left.mp ?_
      have hBmod : -(B : ℤ) ≡ (i : ℤ) [ZMOD (dprMod M i : ℤ)] := by
        rw [Int.modEq_iff_dvd]
        have h1 : dprMod M i ∣ B + i :=
          ⟨i, by rw [mul_comm]; exact (mul_dprMod hi1 (by omega)).symm⟩
        convert Int.ofNat_dvd.mpr h1 using 1
        push_cast
        ring
      have hcong := eval_int_modEq P (m := (dprMod M i : ℤ))
        (u := Sum.elim (fun o : Option (Fin r) ↦ Option.casesOn o (-(B : ℤ)) fun a ↦ (v a : ℤ))
          (fun j ↦ (Y j : ℤ)))
        (v := fun s ↦ ((Sum.elim (Option.elim' i v) (y i) s : ℕ) : ℤ))
        (fun s ↦ by
          cases s with
          | inl o =>
            cases o with
            | none => exact hBmod
            | some a => exact Int.ModEq.refl _
          | inr j => exact hYmod j i hi)
      rw [hy i hi1 hin] at hcong
      exact Int.modEq_zero_iff_dvd.mp hcong
    · intro j
      change W ∣ (K + 1).factorial * (Y j).choose (K + 1)
      rw [show W = ∏ i ∈ Finset.Icc 1 n, dprMod M i from (prod_dprMod (by omega)).symm]
      refine prod_coprime_dvd_nat (Finset.Icc 1 n) (dprMod M) _ hcop fun i hi ↦ ?_
      refine Int.ofNat_dvd.mp ?_
      rw [int_factorial_mul_choose_eq_prod]
      have hdvd_factor : (dprMod M i : ℤ) ∣ (Y j : ℤ) - (y i j : ℤ) :=
        Int.modEq_iff_dvd.mp (hYmod j i hi).symm
      exact dvd_trans hdvd_factor
        (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_of_le (hyK i hi j))))

/-! ### The MRDP theorem: `Primrec`, `Partrec`, and `REPred` are Diophantine -/

/-- Every primitive recursive function `f : ℕ → ℕ` is a Diophantine function. -/
public theorem diophFn_of_natPrimrec {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∀ {α : Type} {g : (α → ℕ) → ℕ}, DiophFn g → DiophFn fun v ↦ f (g v) := by
  induction hf with
  | zero => intro α _ _; exact const_dioph 0
  | succ => intro α g dg; exact add_dioph dg (const_dioph 1)
  | left => intro α g dg; exact unpair_left_dioph dg
  | right => intro α g dg; exact unpair_right_dioph dg
  | pair _ _ ihf ihg => intro α h dh; exact pair_dioph (ihf dh) (ihg dh)
  | comp _ _ ihf ihg => intro α h dh; exact ihf (ihg dh)
  | @prec f₁ f₂ _ _ ih₁ ih₂ =>
    -- Prove `Dioph` on `Fin 3` (`v 0 = result`, `v 1 = input`, `v 2 = code c`), then reindex.
    have dStep : Dioph {w : Option (Fin 3) → ℕ |
        Nat.beta (w (some 2)) (w none) =
          f₂ (Nat.pair (w (some 1)).unpair.1
            (Nat.pair (w none - 1) (Nat.beta (w (some 2)) (w none - 1))))} :=
      eq_dioph
        (beta_dioph (proj_dioph (some 2)) (proj_dioph none))
        (ih₂ (pair_dioph
          (unpair_left_dioph (proj_dioph (some 1)))
          (pair_dioph
            (sub_dioph (proj_dioph none) (const_dioph 1))
            (beta_dioph (proj_dioph (some 2))
              (sub_dioph (proj_dioph none) (const_dioph 1))))))
    have dAll : Dioph {v : Fin 3 → ℕ | ∀ i, 1 ≤ i → i ≤ (v 1).unpair.2 →
        Nat.beta (v 2) i =
          f₂ (Nat.pair (v 1).unpair.1 (Nat.pair (i - 1) (Nat.beta (v 2) (i - 1))))} :=
      bounded_forall_dioph dStep (unpair_right_dioph (proj_dioph 1))
    have dBase : Dioph {v : Fin 3 → ℕ | Nat.beta (v 2) 0 = f₁ (v 1).unpair.1} :=
      eq_dioph (beta_dioph (proj_dioph 2) (const_dioph 0))
        (ih₁ (unpair_left_dioph (proj_dioph 1)))
    have dEnd : Dioph {v : Fin 3 → ℕ | Nat.beta (v 2) (v 1).unpair.2 = v 0} :=
      eq_dioph (beta_dioph (proj_dioph 2) (unpair_right_dioph (proj_dioph 1)))
        (proj_dioph 0)
    have dFull : Dioph {v : Fin 3 → ℕ |
        Nat.beta (v 2) 0 = f₁ (v 1).unpair.1 ∧
        Nat.beta (v 2) (v 1).unpair.2 = v 0 ∧
        ∀ i, 1 ≤ i → i ≤ (v 1).unpair.2 →
          Nat.beta (v 2) i =
            f₂ (Nat.pair (v 1).unpair.1 (Nat.pair (i - 1) (Nat.beta (v 2) (i - 1))))} :=
      inter dBase (inter dEnd dAll)
    intro α g dg
    -- Need `Dioph {u : Option α → ℕ | rec (u ∘ some) = u none}`.
    let mapC : Option (Option α) → Fin 3
      | none => 2
      | some none => 0
      | some (some _) => 1
    -- Substitute `g (u ∘ some)` for `v 1` using an extra variable.
    let mapCG : Fin 3 → Option (Option (Option α))
      | 0 => some (some none)
      | 1 => some none
      | 2 => none
    have dWithG : Dioph {w : Option (Option (Option α)) → ℕ |
        w (some none) = g (w ∘ some ∘ some ∘ some) ∧ w ∘ mapCG ∈
          {v : Fin 3 → ℕ |
            Nat.beta (v 2) 0 = f₁ (v 1).unpair.1 ∧
            Nat.beta (v 2) (v 1).unpair.2 = v 0 ∧
            ∀ i, 1 ≤ i → i ≤ (v 1).unpair.2 →
              Nat.beta (v 2) i =
                f₂ (Nat.pair (v 1).unpair.1 (Nat.pair (i - 1) (Nat.beta (v 2) (i - 1))))}} :=
      inter (eq_dioph (proj_dioph (some none)) (reindex_diophFn (some ∘ some ∘ some) dg))
        (dFull.reindex_dioph (Option (Option (Option α))) mapCG)
    refine dWithG.ex1_dioph.ex1_dioph.ext fun u ↦ Iff.symm ?_
    let x := g (u ∘ some)
    let a := x.unpair.1
    let n := x.unpair.2
    let seq : ℕ → ℕ := fun k ↦ Nat.rec (f₁ a) (fun y IH ↦ f₂ (Nat.pair a (Nat.pair y IH))) k
    change seq n = u none ↔
      ∃ x' c : ℕ, x' = x ∧
        Nat.beta c 0 = f₁ x'.unpair.1 ∧
        Nat.beta c x'.unpair.2 = u none ∧
        ∀ i, 1 ≤ i → i ≤ x'.unpair.2 →
          Nat.beta c i =
            f₂ (Nat.pair x'.unpair.1 (Nat.pair (i - 1) (Nat.beta c (i - 1))))
    constructor
    · intro hseq
      let l : List ℕ := List.ofFn fun k : Fin (n + 1) ↦ seq k.1
      let c := Nat.unbeta l
      have hbeta : ∀ k (hk : k ≤ n), Nat.beta c k = seq k := by
        intro k hk
        have hlen : k < l.length := by simp [l]; omega
        exact (Nat.beta_unbeta_coe l ⟨k, hlen⟩).trans (List.getElem_ofFn _)
      refine ⟨x, c, rfl, hbeta 0 (Nat.zero_le n), (hbeta n le_rfl).trans hseq, ?_⟩
      intro i hi1 hin
      rw [hbeta i hin, hbeta (i - 1) (by omega)]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rfl
    · rintro ⟨_, c, rfl, h0, hn, hstep⟩
      have hind : ∀ k, k ≤ n → Nat.beta c k = seq k := by
        intro k
        induction k with
        | zero => intro _; exact h0
        | succ j ih =>
          intro hj
          rw [hstep (j + 1) (by omega) hj, Nat.add_sub_cancel, ih (by omega)]
      rw [← hn, hind n le_rfl]

/-- Universal step-bounded evaluation `(e, k, n) ↦ encode (evaln k (ofNatCode e) n)` is
Diophantine: its value is `y + 1` iff `y ∈ evaln k (ofNatCode e) n`. -/
private def univEvalnNat (p : ℕ) : ℕ :=
  Encodable.encode
    (Nat.Partrec.Code.evaln p.unpair.1
      (Denumerable.ofNat Nat.Partrec.Code p.unpair.2.unpair.1)
      p.unpair.2.unpair.2)

private theorem natPrimrec_univEvalnNat : Nat.Primrec univEvalnNat := by
  refine Primrec.nat_iff.mp ?_
  unfold univEvalnNat
  refine Primrec.encode.comp ?_
  have harg : Primrec fun p : ℕ ↦
      ((p.unpair.1, Denumerable.ofNat Nat.Partrec.Code p.unpair.2.unpair.1),
        p.unpair.2.unpair.2) :=
    Primrec.pair
      (Primrec.pair (Primrec.fst.comp Primrec.unpair)
        ((Primrec.ofNat Nat.Partrec.Code).comp
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  exact Nat.Partrec.Code.primrec_evaln.comp harg

/-- The universal partial-recursive graph `{(e, n, y) | y ∈ (ofNatCode e).eval n}` is
Diophantine. -/
public theorem universal_eval_graph_dioph :
    Dioph {v : Fin 3 → ℕ |
      v 2 ∈ (Denumerable.ofNat Nat.Partrec.Code (v 0)).eval (v 1)} := by
  have dStep : Dioph {w : Option (Fin 3) → ℕ |
      univEvalnNat (Nat.pair (w none) (Nat.pair (w (some 0)) (w (some 1)))) =
        w (some 2) + 1} :=
    eq_dioph
      (diophFn_of_natPrimrec natPrimrec_univEvalnNat
        (pair_dioph (proj_dioph none)
          (pair_dioph (proj_dioph (some 0)) (proj_dioph (some 1)))))
      (add_dioph (proj_dioph (some 2)) (const_dioph 1))
  refine dStep.ex1_dioph.ext fun v ↦ Iff.symm ?_
  simp only [Set.mem_ofPred, Nat.Partrec.Code.evaln_complete]
  refine exists_congr fun k ↦ ?_
  simp only [univEvalnNat, Option.elim'_none, Option.elim'_some, Nat.unpair_pair, Option.mem_def]
  cases Nat.Partrec.Code.evaln k (Denumerable.ofNat Nat.Partrec.Code (v 0)) (v 1) with
  | none => simp [Encodable.encode]
  | some val => simp [Encodable.encode]

/-- The universal halting relation `{(e, n) | ((ofNatCode e).eval n).Dom}` is Diophantine. -/
public theorem universal_dom_dioph :
    Dioph {v : Fin 2 → ℕ |
      ((Denumerable.ofNat Nat.Partrec.Code (v 0)).eval (v 1)).Dom} := by
  let mapY : Fin 3 → Option (Fin 2)
    | 0 => some 0
    | 1 => some 1
    | 2 => none
  refine (universal_eval_graph_dioph.reindex_dioph (Option (Fin 2)) mapY).ex1_dioph.ext
    fun v ↦ ?_
  simp only [Set.mem_ofPred, Part.dom_iff_mem]
  exact Iff.rfl

/-- Every partial recursive function `f : ℕ →. ℕ` is a Diophantine partial function. -/
public theorem diophPFun_of_natPartrec {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    DiophPFun fun v : Fin 1 → ℕ ↦ f (v 0) := by
  obtain ⟨c, rfl⟩ := Nat.Partrec.Code.exists_code.mp hf
  let e := Encodable.encode c
  have h : Dioph {u : Option (Fin 1) → ℕ |
      u none ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval (u (some 0))} := by
    have d1 : Dioph {w : Option (Option (Fin 1)) → ℕ |
        w none = e ∧
        w (some none) ∈ (Denumerable.ofNat Nat.Partrec.Code (w none)).eval (w (some (some 0)))}
          := by
      let m3 : Fin 3 → Option (Option (Fin 1))
        | 0 => none
        | 1 => some (some 0)
        | 2 => some none
      exact inter (eq_dioph (proj_dioph none) (const_dioph e))
        ((universal_eval_graph_dioph.reindex_dioph (Option (Option (Fin 1))) m3).ext
          fun _ ↦ Iff.rfl)
    exact d1.ex1_dioph.ext fun u ↦
      ⟨fun ⟨_, h1, h2⟩ ↦ h1 ▸ h2, fun h ↦ ⟨e, rfl, h⟩⟩
  refine h.ext fun u ↦ ?_
  simp only [Set.mem_ofPred, e, Denumerable.ofNat_encode]
  exact Iff.rfl

private theorem int_ofNat_encode_eq (a : ℕ) : Encodable.encode (Int.ofNat a) = 2 * a := by
  change Nat.bit false a = 2 * a
  simp [Nat.bit]

private theorem int_negSucc_encode_eq (a : ℕ) : Encodable.encode (Int.negSucc a) = 2 * a + 1 := by
  simp [Encodable.encode, Equiv.intEquivNat, Equiv.intEquivNatSumNat,
    Equiv.natSumNatEquivNat, Function.uncurry, Nat.bit]

/-- Natural-number coercion `Int.ofNat : ℕ → ℤ` is primitive recursive. -/
public theorem primrec_int_ofNat : Primrec (Int.ofNat : ℕ → ℤ) :=
  ((Primrec.ofNat ℤ).comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)).of_eq fun a ↦ by
    change Denumerable.ofNat ℤ (2 * a) = Int.ofNat a
    rw [← int_ofNat_encode_eq, Denumerable.ofNat_encode]

private theorem primrec_int_negSucc : Primrec (Int.negSucc : ℕ → ℤ) :=
  ((Primrec.ofNat ℤ).comp
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))).of_eq fun a ↦ by
    change Denumerable.ofNat ℤ (2 * a + 1) = Int.negSucc a
    rw [← int_negSucc_encode_eq, Denumerable.ofNat_encode]

private theorem int_bodd_div2 (x : ℤ) :
    (if (Encodable.encode x).bodd then Int.negSucc (Encodable.encode x).div2
      else Int.ofNat (Encodable.encode x).div2) = x := by
  cases x with
  | ofNat a =>
    rw [int_ofNat_encode_eq, show 2 * a = Nat.bit false a by simp [Nat.bit],
      Nat.bodd_bit, Nat.div2_bit]; rfl
  | negSucc a =>
    rw [int_negSucc_encode_eq, show 2 * a + 1 = Nat.bit true a by simp [Nat.bit],
      Nat.bodd_bit, Nat.div2_bit]; rfl

/-- Integer addition is primitive recursive. -/
public theorem primrec_int_add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  have s1 : Primrec fun p : ℤ × ℤ ↦ (Encodable.encode p.1).bodd :=
    Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.fst)
  have s2 : Primrec fun p : ℤ × ℤ ↦ (Encodable.encode p.2).bodd :=
    Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.snd)
  have a : Primrec fun p : ℤ × ℤ ↦ (Encodable.encode p.1).div2 :=
    Primrec.nat_div2.comp (Primrec.encode.comp Primrec.fst)
  have b : Primrec fun p : ℤ × ℤ ↦ (Encodable.encode p.2).div2 :=
    Primrec.nat_div2.comp (Primrec.encode.comp Primrec.snd)
  have hpn := Primrec.ite (Primrec.nat_lt.comp b a)
    (primrec_int_ofNat.comp (Primrec.nat_sub.comp a (Primrec.succ.comp b)))
    (primrec_int_negSucc.comp (Primrec.nat_sub.comp b a))
  have hnp := Primrec.ite (Primrec.nat_lt.comp a b)
    (primrec_int_ofNat.comp (Primrec.nat_sub.comp b (Primrec.succ.comp a)))
    (primrec_int_negSucc.comp (Primrec.nat_sub.comp a b))
  have h := Primrec.ite (Primrec.eq.comp s1 (Primrec.const true))
    (Primrec.ite (Primrec.eq.comp s2 (Primrec.const true))
      (primrec_int_negSucc.comp (Primrec.succ.comp (Primrec.nat_add.comp a b))) hnp)
    (Primrec.ite (Primrec.eq.comp s2 (Primrec.const true)) hpn
      (primrec_int_ofNat.comp (Primrec.nat_add.comp a b)))
  refine h.of_eq fun ⟨x, y⟩ ↦ ?_
  have hx := int_bodd_div2 x; have hy := int_bodd_div2 y
  set ma := (Encodable.encode x).div2; set mb := (Encodable.encode y).div2
  dsimp only; cases hb1 : (Encodable.encode x).bodd <;> cases hb2 : (Encodable.encode y).bodd
  all_goals simp only [hb1, hb2, ↓reduceIte, Bool.false_eq_true] at hx hy ⊢; rw [← hx, ← hy]
  · rfl
  · split_ifs with hlt
    · change (((ma - (mb + 1)) : ℕ) : ℤ) = (ma : ℤ) + -(((mb + 1 : ℕ) : ℤ)); omega
    · change -((((mb - ma) + 1 : ℕ) : ℤ)) = (ma : ℤ) + -(((mb + 1 : ℕ) : ℤ)); omega
  · split_ifs with hlt
    · change (((mb - (ma + 1)) : ℕ) : ℤ) = -(((ma + 1 : ℕ) : ℤ)) + (mb : ℤ); omega
    · change -((((ma - mb) + 1 : ℕ) : ℤ)) = -(((ma + 1 : ℕ) : ℤ)) + (mb : ℤ); omega
  · change -((((ma + mb + 1) + 1 : ℕ) : ℤ)) = -(((ma + 1 : ℕ) : ℤ)) + -(((mb + 1 : ℕ) : ℤ))
    omega

/-- Integer multiplication is primitive recursive. -/
public theorem primrec_int_mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  have s1 : Primrec fun p : ℤ × ℤ ↦ (Encodable.encode p.1).bodd :=
    Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.fst)
  have s2 : Primrec fun p : ℤ × ℤ ↦ (Encodable.encode p.2).bodd :=
    Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.snd)
  have a : Primrec fun p : ℤ × ℤ ↦ (Encodable.encode p.1).div2 :=
    Primrec.nat_div2.comp (Primrec.encode.comp Primrec.fst)
  have b : Primrec fun p : ℤ × ℤ ↦ (Encodable.encode p.2).div2 :=
    Primrec.nat_div2.comp (Primrec.encode.comp Primrec.snd)
  have hpn := Primrec.ite (Primrec.eq.comp a (Primrec.const 0)) (Primrec.const (0 : ℤ))
    (primrec_int_negSucc.comp (Primrec.pred.comp (Primrec.nat_mul.comp a (Primrec.succ.comp b))))
  have hnp := Primrec.ite (Primrec.eq.comp b (Primrec.const 0)) (Primrec.const (0 : ℤ))
    (primrec_int_negSucc.comp (Primrec.pred.comp (Primrec.nat_mul.comp (Primrec.succ.comp a) b)))
  have h := Primrec.ite (Primrec.eq.comp s1 (Primrec.const true))
    (Primrec.ite (Primrec.eq.comp s2 (Primrec.const true))
      (primrec_int_ofNat.comp (Primrec.nat_mul.comp (Primrec.succ.comp a) (Primrec.succ.comp b)))
      hnp)
    (Primrec.ite (Primrec.eq.comp s2 (Primrec.const true)) hpn
      (primrec_int_ofNat.comp (Primrec.nat_mul.comp a b)))
  refine h.of_eq fun ⟨x, y⟩ ↦ ?_
  have hx := int_bodd_div2 x; have hy := int_bodd_div2 y
  set ma := (Encodable.encode x).div2; set mb := (Encodable.encode y).div2
  dsimp only; cases hb1 : (Encodable.encode x).bodd <;> cases hb2 : (Encodable.encode y).bodd
  all_goals simp only [hb1, hb2, ↓reduceIte, Bool.false_eq_true] at hx hy ⊢; rw [← hx, ← hy]
  · rfl
  · split_ifs with h0
    · simp [h0]
    · have hp : 1 ≤ ma * (mb + 1) := Nat.mul_pos (Nat.pos_of_ne_zero h0) (Nat.succ_pos mb)
      change -((((ma * (mb + 1) - 1) + 1 : ℕ) : ℤ)) = (ma : ℤ) * -(((mb + 1 : ℕ) : ℤ))
      rw [Nat.sub_add_cancel hp]; push_cast; ring
  · split_ifs with h0
    · simp [h0]
    · have hp : 1 ≤ (ma + 1) * mb := Nat.mul_pos (Nat.succ_pos ma) (Nat.pos_of_ne_zero h0)
      change -(((((ma + 1) * mb - 1) + 1 : ℕ) : ℤ)) = -(((ma + 1 : ℕ) : ℤ)) * (mb : ℤ)
      rw [Nat.sub_add_cancel hp]; push_cast; ring
  · change (((ma + 1) * (mb + 1) : ℕ) : ℤ) = -(((ma + 1 : ℕ) : ℤ)) * -(((mb + 1 : ℕ) : ℤ))
    push_cast; ring

private def evalListAssign {m : ℕ} (p : ℕ × List ℕ) : Fin 1 ⊕ Fin m → ℤ
  | Sum.inl _ => (p.1 : ℤ)
  | Sum.inr j => (p.2.getD j.1 0 : ℤ)

private theorem computable_evalListAssign {m : ℕ} (Q : MvPolynomial (Fin 1 ⊕ Fin m) ℤ) :
    Computable fun p : ℕ × List ℕ ↦ eval (evalListAssign p) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using Computable.const a
  | add _ _ ih₁ ih₂ =>
    simpa only [map_add] using (Primrec.to_comp primrec_int_add).comp (Computable.pair ih₁ ih₂)
  | mul_X _ u ih₁ =>
    have hu : Computable fun p : ℕ × List ℕ ↦ evalListAssign p u := by
      cases u with
      | inl _ => exact (primrec_int_ofNat.comp Primrec.fst).to_comp
      | inr j =>
        have h1 : Primrec fun p : ℕ × List ℕ ↦ p.2[j.1]? :=
          Primrec.list_getElem?.comp Primrec.snd (Primrec.const j.1)
        have h2 : Primrec fun p : ℕ × List ℕ ↦ p.2.getD j.1 0 :=
          (Primrec.option_casesOn h1 (Primrec.const 0)
            (Primrec.to₂ Primrec.snd)).of_eq fun p ↦ by
              rw [List.getD_eq_getElem?_getD]; cases p.2[j.1]? <;> rfl
        exact (primrec_int_ofNat.comp h2).to_comp
    simpa only [map_mul, eval_X] using
      (Primrec.to_comp primrec_int_mul).comp (Computable.pair ih₁ hu)

private theorem rePred_poly_zero {m : ℕ} (P : MvPolynomial (Fin 1 ⊕ Fin m) ℤ) :
    REPred fun n : ℕ ↦ ∃ y : Fin m → ℕ,
      eval (fun u ↦ ((Sum.elim (fun _ ↦ n) y u : ℕ) : ℤ)) P = 0 := by
  have htest : Computable fun q : ℕ × ℕ ↦
      decide (eval (evalListAssign (q.1, Denumerable.ofNat (List ℕ) q.2)) P = 0) :=
    ((Primrec.eq.comp Primrec.id (Primrec.const (0 : ℤ))).decide).to_comp.comp
      ((computable_evalListAssign P).comp
        (Computable.pair Computable.fst ((Primrec.ofNat (List ℕ)).to_comp.comp Computable.snd)))
  have hdom' : Partrec fun n : ℕ ↦
      Nat.rfind fun k ↦ Part.some
        (decide (eval (evalListAssign (n, Denumerable.ofNat (List ℕ) k)) P = 0)) :=
    Partrec.rfind (Partrec.some.comp htest.partrec)
  have hiff : ∀ n : ℕ,
      (∃ k : ℕ, eval (evalListAssign (n, Denumerable.ofNat (List ℕ) k)) P = 0) ↔
      (∃ y : Fin m → ℕ, eval (fun u ↦ ((Sum.elim (fun _ ↦ n) y u : ℕ) : ℤ)) P = 0) := fun n ↦ by
    constructor
    · rintro ⟨k, hk⟩
      let l := Denumerable.ofNat (List ℕ) k
      refine ⟨fun j ↦ l.getD j.1 0, ?_⟩
      have hfn : (fun u : Fin 1 ⊕ Fin m ↦
          ((Sum.elim (fun _ ↦ n) (fun j : Fin m ↦ l.getD j.1 0) u : ℕ) : ℤ)) =
          evalListAssign (n, l) := by ext (a | j) <;> rfl
      rwa [hfn]
    · rintro ⟨y, hy⟩
      refine ⟨Encodable.encode (List.ofFn y), ?_⟩
      rw [Denumerable.ofNat_encode]
      have hfn : evalListAssign (n, List.ofFn y) =
          fun u : Fin 1 ⊕ Fin m ↦ ((Sum.elim (fun _ ↦ n) y u : ℕ) : ℤ) := by
        ext (a | j)
        · rfl
        · simp [evalListAssign, List.getD_eq_getElem?_getD]
      rwa [hfn]
  have hfun : (fun n : ℕ ↦ (Nat.rfind fun k ↦ Part.some
      (decide (eval (evalListAssign (n, Denumerable.ofNat (List ℕ) k)) P = 0))).Dom) =
      fun n ↦ ∃ y : Fin m → ℕ, eval (fun u ↦ ((Sum.elim (fun _ ↦ n) y u : ℕ) : ℤ)) P = 0 :=
    funext fun n ↦ propext (Nat.rfind_dom.trans (by simpa using hiff n))
  exact hfun ▸ hdom'.dom_re

/-- **Matiyasevich–Robinson–Davis–Putnam (MRDP) Theorem**: a predicate `p : ℕ → Prop` is
recursively enumerable if and only if `{v : Fin 1 → ℕ | p (v 0)}` is Diophantine. -/
public theorem rePred_iff_dioph {p : ℕ → Prop} :
    REPred p ↔ Dioph {v : Fin 1 → ℕ | p (v 0)} := by
  constructor
  · intro hp
    have hpart : Nat.Partrec (fun n ↦ Part.assert (p n) fun _ ↦ Part.some 0) :=
      Partrec.nat_iff.mp hp
    refine (diophPFun_of_natPartrec hpart).ex1_dioph.ext fun v ↦ ?_
    change (∃ x : ℕ, x ∈ Part.assert (p (v 0)) fun _ ↦ Part.some 0) ↔ p (v 0)
    simp
  · intro hd
    obtain ⟨m, P, hP⟩ := dioph_iff_exists_mvPoly.mp hd
    have hfun : (fun n : ℕ ↦ ∃ y : Fin m → ℕ,
        eval (fun u ↦ ((Sum.elim (fun _ ↦ n) y u : ℕ) : ℤ)) P = 0) = p :=
      funext fun n ↦ propext (hP (fun _ ↦ n)).symm
    exact hfun ▸ rePred_poly_zero P

/-! ### Universal quartic Diophantine equations over `ℕ` and over `ℤ` -/

/-- **Universal Quartic Diophantine Equation over `ℕ` (Matiyasevich–Skolem–Jones)**: there exists
a single integer polynomial `U : MvPolynomial (Fin 2 ⊕ Fin m) ℤ` of total degree at most `4`
encoding the universal halting predicate `((ofNatCode e).eval n).Dom`. -/
public theorem exists_universal_quartic_nat :
    ∃ (m : ℕ) (U : MvPolynomial (Fin 2 ⊕ Fin m) ℤ),
      U.totalDegree ≤ 4 ∧
      ∀ e n : ℕ, ((Denumerable.ofNat Nat.Partrec.Code e).eval n).Dom ↔
        ∃ y : Fin m → ℕ, eval (fun v ↦ ((Sum.elim ![e, n] y v : ℕ) : ℤ)) U = 0 := by
  obtain ⟨m₀, P₀, hP₀⟩ := dioph_iff_exists_mvPoly.mp universal_dom_dioph
  let eqv0 : Fin 2 ⊕ Fin m₀ ≃ Fin (2 + m₀) := finSumFinEquiv
  let P₁ : MvPolynomial (Fin (2 + m₀)) ℤ := rename eqv0 P₀
  let Q := skolemQuarticNat P₁
  let k := (reduceToSystem 1 P₁).auxVars
  let eqv1 : QuarticNatVar P₁ ≃ Fin 2 ⊕ Fin (m₀ + k) :=
    (Equiv.sumCongr eqv0.symm (Equiv.refl (Fin k))).trans
      ((Equiv.sumAssoc (Fin 2) (Fin m₀) (Fin k)).trans
        (Equiv.sumCongr (Equiv.refl (Fin 2)) finSumFinEquiv))
  let U : MvPolynomial (Fin 2 ⊕ Fin (m₀ + k)) ℤ := rename eqv1 Q
  refine ⟨m₀ + k, U, (totalDegree_rename_le eqv1 Q).trans (totalDegree_skolemQuarticNat_le P₁), ?_⟩
  intro e n
  have h0 : ((Denumerable.ofNat Nat.Partrec.Code e).eval n).Dom ↔
      ∃ y₀ : Fin m₀ → ℕ, eval (fun u ↦ ((Sum.elim ![e, n] y₀ u : ℕ) : ℤ)) P₀ = 0 := hP₀ ![e, n]
  rw [h0]
  constructor
  · rintro ⟨y₀, hy₀⟩
    let x₁ : Fin (2 + m₀) → ℕ := Sum.elim ![e, n] y₀ ∘ eqv0.symm
    have hx₁ : eval (fun i ↦ (x₁ i : ℤ)) P₁ = 0 := by
      rw [show P₁ = rename eqv0 P₀ from rfl, eval_rename]
      exact (congrArg (fun g ↦ eval g P₀) (funext fun v ↦ by simp [x₁])).trans hy₀
    obtain ⟨y₁, hy₁⟩ := (exists_aux_eval_skolemQuarticNat_iff P₁ x₁).mpr hx₁
    let y : Fin (m₀ + k) → ℕ := Sum.elim y₀ y₁ ∘ finSumFinEquiv.symm
    refine ⟨y, ?_⟩
    rw [show U = rename eqv1 Q from rfl, eval_rename]
    refine (congrArg (fun g ↦ eval g Q) (funext fun w ↦ ?_)).trans hy₁
    rcases w with i | j
    · obtain ⟨u, rfl⟩ := eqv0.surjective i; cases u <;> simp [eqv1, x₁, y]
    · simp [eqv1, y]
  · rintro ⟨y, hy⟩
    rw [show U = rename eqv1 Q from rfl, eval_rename] at hy
    let y₀ : Fin m₀ → ℕ := fun i ↦ y (finSumFinEquiv (Sum.inl i))
    let y₁ : Fin k → ℕ := fun j ↦ y (finSumFinEquiv (Sum.inr j))
    let x₁ : Fin (2 + m₀) → ℕ := Sum.elim ![e, n] y₀ ∘ eqv0.symm
    have hy' : eval (fun v ↦ ((Sum.elim x₁ y₁ v : ℕ) : ℤ)) Q = 0 := by
      refine (congrArg (fun g ↦ eval g Q) (funext fun w ↦ ?_)).trans hy
      rcases w with i | j
      · obtain ⟨u, rfl⟩ := eqv0.surjective i; cases u <;> simp [eqv1, x₁, y₀]
      · simp [eqv1, y₁]
    have hx₁ := (exists_aux_eval_skolemQuarticNat_iff P₁ x₁).mp ⟨y₁, hy'⟩
    rw [show P₁ = rename eqv0 P₀ from rfl, eval_rename] at hx₁
    refine ⟨y₀, ?_⟩
    exact (congrArg (fun g ↦ eval g P₀) (funext fun v ↦ by simp [x₁])).trans hx₁

/-- Every recursively enumerable predicate `p : ℕ → Prop` is represented by a single polynomial
`Q : MvPolynomial (Fin 1 ⊕ Fin m) ℤ` of total degree at most `4` over `ℕ`, and also by a single
polynomial `Qℤ : MvPolynomial (Fin 1 ⊕ Fin mℤ) ℤ` of total degree at most `4` over `ℤ`. -/
public theorem rePred_exists_quartic_nat {p : ℕ → Prop} (hp : REPred p) :
    ∃ (m : ℕ) (Q : MvPolynomial (Fin 1 ⊕ Fin m) ℤ),
      Q.totalDegree ≤ 4 ∧
      ∀ n : ℕ, p n ↔ ∃ y : Fin m → ℕ, eval (fun v ↦ ((Sum.elim ![n] y v : ℕ) : ℤ)) Q = 0 := by
  have hpart : Nat.Partrec (fun n ↦ Part.assert (p n) fun _ ↦ Part.some 0) :=
    Partrec.nat_iff.mp hp
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hpart
  obtain ⟨m, U, hUdeg, hU⟩ := exists_universal_quartic_nat
  let e := Encodable.encode c
  let subst : Fin 2 ⊕ Fin m → MvPolynomial (Fin 1 ⊕ Fin m) ℤ
    | Sum.inl 0 => C (e : ℤ)
    | Sum.inl 1 => X (Sum.inl 0)
    | Sum.inr j => X (Sum.inr j)
  let Q : MvPolynomial (Fin 1 ⊕ Fin m) ℤ := eval₂ C subst U
  have hQeval : ∀ (y : Fin m → ℕ) (n : ℕ),
      eval (fun v ↦ ((Sum.elim ![n] y v : ℕ) : ℤ)) Q =
        eval (fun w ↦ eval (fun v ↦ ((Sum.elim ![n] y v : ℕ) : ℤ)) (subst w)) U :=
    fun y n ↦ eval_eval₂_C U subst _
  have hQdeg : Q.totalDegree ≤ 4 := by
    classical
    rw [show Q = eval₂ C subst U from rfl, eval₂_eq]
    refine totalDegree_finsetSum_le fun s hs ↦ ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    have hprod : ∀ u : Finset (Fin 2 ⊕ Fin m),
        (∏ v ∈ u, subst v ^ s v).totalDegree ≤ ∑ v ∈ u, (subst v ^ s v).totalDegree := by
      intro u
      induction u using Finset.induction_on with
      | empty => simp
      | insert a u ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha]
        exact (totalDegree_mul _ _).trans (Nat.add_le_add_left ih _)
    refine (hprod s.support).trans ?_
    calc ∑ v ∈ s.support, (subst v ^ s v).totalDegree
        ≤ ∑ v ∈ s.support, s v * 1 := by
          refine Finset.sum_le_sum fun v _ ↦ (totalDegree_pow _ _).trans
            (Nat.mul_le_mul_left _ ?_)
          rcases v with i | j
          · fin_cases i
            · change (C (e : ℤ) : MvPolynomial (Fin 1 ⊕ Fin m) ℤ).totalDegree ≤ 1
              rw [totalDegree_C]; exact Nat.zero_le 1
            · simp [subst, totalDegree_X]
          · simp [subst, totalDegree_X]
      _ = s.sum fun _ d ↦ d := by simp [Finsupp.sum]
      _ ≤ U.totalDegree := le_totalDegree hs
      _ ≤ 4 := hUdeg
  refine ⟨m, Q, hQdeg, fun n ↦ ?_⟩
  have hdom : p n ↔ ((Denumerable.ofNat Nat.Partrec.Code e).eval n).Dom := by
    simp [e, Denumerable.ofNat_encode, hc, Part.dom_iff_mem]
  rw [hdom, hU e n]
  refine exists_congr fun y ↦ ?_
  rw [hQeval y n]
  have hfn : (fun w ↦ eval (fun v ↦ ((Sum.elim ![n] y v : ℕ) : ℤ)) (subst w)) =
      fun w ↦ ((Sum.elim ![e, n] y w : ℕ) : ℤ) := by
    ext (i | j)
    · fin_cases i <;> simp [subst]
    · simp [subst]
  rw [hfn]

/-- Non-vacuity witness: the set of squares `{n : ℕ | ∃ k, n = k * k}` admits a single quartic
Diophantine representation over `ℕ` via `rePred_exists_quartic_nat`. -/
private example :
    ∃ (m : ℕ) (Q : MvPolynomial (Fin 1 ⊕ Fin m) ℤ),
      Q.totalDegree ≤ 4 ∧
      (∃ y : Fin m → ℕ, eval (fun v ↦ ((Sum.elim ![9] y v : ℕ) : ℤ)) Q = 0) ∧
      ¬ (∃ y : Fin m → ℕ, eval (fun v ↦ ((Sum.elim ![2] y v : ℕ) : ℤ)) Q = 0) := by
  have hd : Dioph {v : Fin 1 → ℕ | ∃ k : ℕ, v 0 = k * k} :=
    (eq_dioph (proj_dioph (some 0)) (mul_dioph (proj_dioph none) (proj_dioph none))).ex1_dioph
  obtain ⟨m, Q, hdeg, hiff⟩ :=
    rePred_exists_quartic_nat ((rePred_iff_dioph (p := fun n ↦ ∃ k, n = k * k)).mpr hd)
  refine ⟨m, Q, hdeg, (hiff 9).mp ⟨3, rfl⟩, ?_⟩
  intro h2
  rcases (hiff 2).mpr h2 with ⟨k, hk⟩
  rcases k with _ | _ | k
  · omega
  · omega
  · nlinarith

end CslibFrontier.Computability.Diophantine
