/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.BlumComplexity.Basic
import CslibFrontier.Computability.BlumComplexity.Cancellation
import CslibFrontier.Foundations.Computability.ComputablePred
import Mathlib.Algebra.Order.SuccPred.PartialSups
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.SuccPred.Nat

/-!
# The monotone and finite-family McCreight–Meyer union theorems

This module strengthens `Cslib.BlumComplexity.BlumMeasure.union_theorem` in two directions
following McCreight and Meyer
:

1. **Monotonicity (`exists_computable_monotone_tailMin`, `BlumMeasure.union_theorem_monotone`)**:
   when a uniformly computable, almost-everywhere increasing family `F : ℕ → ℕ → ℕ` consists of
   non-decreasing functions and contains at least one unbounded member, the diagonal union bound
   `t₀` can be replaced by its computable tail minimum `t(n) = min_{m ≥ n} t₀(m)`, which is total
   computable, **non-decreasing**, still dominates every `F i` almost everywhere, and satisfies
   `Φ.complexityClass t = ⋃ i, Φ.complexityClass (F i)`.
2. **Abstract & finite-family simultaneous union (`exists_computable_monotone_diagonal_union_bound`,
   `BlumMeasure.finite_union_theorem_monotone`)**: any countable family of computable requirements
   whose non-violation is monotone in the resource threshold admits a single computable
   non-decreasing McCreight–Meyer bound, and any finite family `Φ : Fin ℓ → BlumMeasure` admits a
   single computable non-decreasing `t` with `(Φ i).complexityClass t = ⋃ j, (Φ i).complexityClass
   (F j)` simultaneously for all `i : Fin ℓ`.

## Main results

* `Cslib.BlumComplexity.exists_computable_monotone_tailMin`: computable non-decreasing tail minimum
  `t(n) = min_{m ≥ n} t₀(m)` preserving almost-everywhere lower bounds by non-decreasing functions.
* `Cslib.BlumComplexity.exists_computable_fin_min`: computable non-decreasing pointwise minimum of
  a finite family of bounds dominating a common sequence.
* `Cslib.BlumComplexity.exists_computable_diagonal_union_bound`,
  `Cslib.BlumComplexity.exists_computable_monotone_diagonal_union_bound`: abstract computable and
  non-decreasing McCreight–Meyer diagonal union bounds for arbitrary computable violation
  predicates.
* `Cslib.BlumComplexity.BlumMeasure.union_theorem_monotone`: non-decreasing McCreight–Meyer Union
  Theorem for a single `BlumMeasure`.
* `Cslib.BlumComplexity.BlumMeasure.finite_union_theorem_monotone`: simultaneous non-decreasing
  McCreight–Meyer Union Theorem for a finite family `Fin ℓ → BlumMeasure`.
-/

public section

namespace Cslib.BlumComplexity

open Filter
open Cslib.BlumComplexity.Cancellation

private def rangeMin (f : ℕ → ℕ) (s : ℕ) : ℕ → ℕ
  | 0 => f s
  | k + 1 => min (rangeMin f s k) (f (s + k + 1))

private lemma rangeMin_le_init (f : ℕ → ℕ) (s : ℕ) : ∀ k : ℕ, rangeMin f s k ≤ f s
  | 0 => le_rfl
  | k + 1 => (min_le_left _ _).trans (rangeMin_le_init f s k)

private lemma rangeMin_le_of_le (f : ℕ → ℕ) (s : ℕ) :
    ∀ {k d : ℕ}, d ≤ k → rangeMin f s k ≤ f (s + d)
  | 0, d, hd => by obtain rfl : d = 0 := Nat.eq_zero_of_le_zero hd; exact le_rfl
  | k + 1, d, hd => by
    rcases Nat.of_le_succ hd with hdk | rfl
    · exact (min_le_left _ _).trans (rangeMin_le_of_le f s hdk)
    · exact min_le_right _ _

private lemma rangeMin_attains (f : ℕ → ℕ) (s : ℕ) :
    ∀ k : ℕ, ∃ m ≥ s, rangeMin f s k = f m
  | 0 => ⟨s, le_rfl, rfl⟩
  | k + 1 => by
    change ∃ m ≥ s, min (rangeMin f s k) (f (s + k + 1)) = f m
    rcases le_total (rangeMin f s k) (f (s + k + 1)) with hle | hle
    · obtain ⟨m, hm, heq⟩ := rangeMin_attains f s k
      exact ⟨m, hm, (min_eq_left hle).trans heq⟩
    · exact ⟨s + k + 1, by omega, min_eq_right hle⟩

private lemma computable₂_rangeMin {f : ℕ → ℕ} (hf : Computable f) :
    Computable₂ (rangeMin f) :=
  (Computable.nat_rec (f := fun p : ℕ × ℕ ↦ p.2) (g := fun p ↦ f p.1)
    (h := fun p q ↦ min q.2 (f (p.1 + q.1 + 1))) Computable.snd
    (hf.comp Computable.fst)
    (Primrec.nat_min.to_comp.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.succ.comp (Primrec.nat_add.to_comp.comp
        (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))))).to₂).of_eq
    fun ⟨s, k⟩ ↦ by
      induction k with
      | zero => rfl
      | succ k ih => dsimp only at ih ⊢; rw [rangeMin, ← ih]

/-- **Computable non-decreasing tail minimum.** If `t₀ : ℕ → ℕ` is total computable and pointwise
minorized by a total computable, non-decreasing, unbounded function `b : ℕ → ℕ`, then the tail
minimum `t(n) = min_{m ≥ n} t₀(m)` is total computable, non-decreasing, satisfies `t(n) ≤ t₀(n)`
for all `n`, attains `t₀(m)` for some `m ≥ n`, and preserves every almost-everywhere lower bound
`f ≤ᶠ[atTop] t₀` for non-decreasing functions `f : ℕ → ℕ`. -/
theorem exists_computable_monotone_tailMin {t₀ b : ℕ → ℕ}
    (ht₀ : Computable t₀) (hb : Computable b) (hb_mono : Monotone b)
    (hb_unbdd : ∀ B : ℕ, ∃ m : ℕ, B ≤ b m) (hbt : ∀ m : ℕ, b m ≤ t₀ m) :
    ∃ t : ℕ → ℕ,
      Computable t ∧
      Monotone t ∧
      (∀ n : ℕ, t n ≤ t₀ n) ∧
      (∀ n : ℕ, ∃ m ≥ n, t n = t₀ m) ∧
      ∀ f : ℕ → ℕ, Monotone f → f ≤ᶠ[atTop] t₀ → f ≤ᶠ[atTop] t := by
  have hdom : ∀ n : ℕ, (Nat.rfind fun m ↦ Part.some (decide (t₀ n ≤ b m))).Dom := fun n ↦ by
    obtain ⟨m, hm⟩ := hb_unbdd (t₀ n)
    obtain ⟨k, hk, -⟩ :=
      Nat.rfind_min' (p := fun m ↦ decide (t₀ n ≤ b m)) (m := m) (decide_eq_true hm)
    exact Part.dom_iff_mem.mpr ⟨k, hk⟩
  let cutoff : ℕ → ℕ := fun n ↦ (Nat.rfind fun m ↦ Part.some (decide (t₀ n ≤ b m))).get (hdom n)
  have hcutoff_spec : ∀ n : ℕ, t₀ n ≤ b (cutoff n) := fun n ↦
    of_decide_eq_true (Part.mem_some_iff.mp (Nat.mem_rfind.mp (Part.get_mem (hdom n))).1).symm
  have hcutoff_comp : Computable cutoff := by
    have hp : Partrec₂ fun n m : ℕ ↦ Part.some (decide (t₀ n ≤ b m)) :=
      Computable.partrec (Primrec.nat_le.decide.to_comp.comp
        (ht₀.comp Computable.fst) (hb.comp Computable.snd))
    exact (Partrec.rfind hp).of_eq_tot fun n ↦ Part.get_mem (hdom n)
  let t : ℕ → ℕ := fun n ↦ rangeMin t₀ n (cutoff n - n)
  have ht_comp : Computable t :=
    (computable₂_rangeMin ht₀).comp Computable.id
      (Primrec.nat_sub.to_comp.comp hcutoff_comp Computable.id)
  have ht_le_all : ∀ {n m : ℕ}, n ≤ m → t n ≤ t₀ m := fun {n m} hnm ↦ by
    rcases le_or_gt m (cutoff n) with hmc | hmc
    · have h1 := rangeMin_le_of_le t₀ n (k := cutoff n - n) (d := m - n) (by omega)
      rwa [Nat.add_sub_cancel' hnm] at h1
    · exact (rangeMin_le_init t₀ n _).trans
        ((hcutoff_spec n).trans ((hb_mono hmc.le).trans (hbt m)))
  have ht_attains : ∀ n : ℕ, ∃ m ≥ n, t n = t₀ m := fun n ↦ rangeMin_attains t₀ n (cutoff n - n)
  have ht_mono : Monotone t := fun n₁ n₂ h12 ↦ by
    obtain ⟨m, hm, hval⟩ := ht_attains n₂
    exact hval ▸ ht_le_all (h12.trans hm)
  refine ⟨t, ht_comp, ht_mono, fun _ ↦ ht_le_all le_rfl, ht_attains, fun f hf hft ↦ ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hft
  refine eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨m, hnm, hval⟩ := ht_attains n
  exact hval ▸ (hf hnm).trans (hN m (hn.trans hnm))

/-- **Pointwise minimum of a finite family of computable non-decreasing bounds.** -/
theorem exists_computable_fin_min {ι : Type*} {ℓ : ℕ} {F : ι → ℕ → ℕ}
    {tBase : ℕ → ℕ} (hBase_comp : Computable tBase) (hBase_mono : Monotone tBase)
    (hBase_dom : ∀ j : ι, F j ≤ᶠ[atTop] tBase)
    {ts : Fin ℓ → ℕ → ℕ} (hts_comp : ∀ i : Fin ℓ, Computable (ts i))
    (hts_mono : ∀ i : Fin ℓ, Monotone (ts i))
    (hts_dom : ∀ (i : Fin ℓ) (j : ι), F j ≤ᶠ[atTop] ts i) :
    ∃ t : ℕ → ℕ,
      Computable t ∧
      Monotone t ∧
      (∀ j : ι, F j ≤ᶠ[atTop] t) ∧
      (∀ i : Fin ℓ, ∀ n : ℕ, t n ≤ ts i n) := by
  induction ℓ with
  | zero => exact ⟨tBase, hBase_comp, hBase_mono, hBase_dom, fun i ↦ Fin.elim0 i⟩
  | succ m ih =>
    rcases m with _ | m'
    · exact ⟨ts 0, hts_comp 0, hts_mono 0, hts_dom 0, fun i n ↦ by rw [Fin.eq_zero i]⟩
    · obtain ⟨t', ht'_comp, ht'_mono, ht'_dom, ht'_le⟩ :=
        ih (fun i ↦ hts_comp i.succ) (fun i ↦ hts_mono i.succ) (fun i ↦ hts_dom i.succ)
      exact ⟨fun n ↦ min (ts 0 n) (t' n),
        Primrec.nat_min.to_comp.comp (hts_comp 0) ht'_comp,
        fun _ _ hab ↦ min_le_min (hts_mono 0 hab) (ht'_mono hab),
        fun j ↦ ((hts_dom 0 j).and (ht'_dom j)).mono fun _ ⟨h1, h2⟩ ↦ le_min h1 h2,
        fun i n ↦ Fin.cases (min_le_left _ _) (fun k ↦ (min_le_right _ _).trans (ht'_le k n)) i⟩

private lemma computable₂_partialSups {F : ℕ → ℕ → ℕ} (hF : Computable₂ F) :
    Computable₂ fun i n : ℕ ↦ partialSups (fun k ↦ F k n) i := by
  refine (Computable.nat_rec (f := fun p : ℕ × ℕ ↦ p.1) (g := fun p ↦ F 0 p.2)
    (h := fun p q ↦ max q.2 (F (q.1 + 1) p.2)) Computable.fst
    (hF.comp (Computable.const 0) Computable.snd)
    (Primrec.nat_max.to_comp.comp (Computable.snd.comp Computable.snd)
      (hF.comp (Computable.succ.comp (Computable.fst.comp Computable.snd))
        (Computable.snd.comp Computable.fst))).to₂).of_eq fun ⟨i, n⟩ ↦ ?_
  induction i with
  | zero => exact (partialSups_zero _).symm
  | succ i ih =>
    dsimp only at ih ⊢
    rw [partialSups_add_one (ι := ℕ), ← ih]

private lemma partialSups_eventuallyEq_of_eventually_le {F : ℕ → ℕ → ℕ}
    (hF : ∀ ⦃i j : ℕ⦄, i ≤ j → F i ≤ᶠ[atTop] F j) (i : ℕ) :
    (fun n ↦ partialSups (fun k ↦ F k n) i) =ᶠ[atTop] F i := by
  induction i with
  | zero => exact Eventually.of_forall fun n ↦ partialSups_zero (fun k ↦ F k n)
  | succ i ih =>
    filter_upwards [ih, hF (Nat.le_succ i)] with n hi hle
    rw [partialSups_add_one (ι := ℕ), hi]
    exact max_eq_right hle

private lemma monotone_partialSups_of_monotone {F : ℕ → ℕ → ℕ}
    (hmono : ∀ i : ℕ, Monotone (F i)) (i : ℕ) :
    Monotone fun n ↦ partialSups (fun k ↦ F k n) i := by
  induction i with
  | zero => exact fun _ _ hab ↦ by simpa only [partialSups_zero] using hmono 0 hab
  | succ i ih =>
    exact fun _ _ hab ↦ by
      simpa only [partialSups_add_one (ι := ℕ)] using max_le_max (ih hab) (hmono (i + 1) hab)

private lemma exists_pointwise_diagonal_union_bound {H : ℕ → ℕ → ℕ}
    (hH : Computable₂ H) (hH_idx : ∀ i n : ℕ, H i n ≤ H (i + 1) n)
    {viol : ℕ → ℕ → ℕ → Bool}
    (hviol : Computable fun p : ℕ × ℕ × ℕ ↦ viol p.1 p.2.1 p.2.2) :
    ∃ t₀ : ℕ → ℕ,
      Computable t₀ ∧
      (∀ n : ℕ, H 0 n ≤ t₀ n) ∧
      (∀ i : ℕ, H i ≤ᶠ[atTop] t₀) ∧
      ∀ r : ℕ, (∀ᶠ n in atTop, viol r n (t₀ n) = false) →
        ∃ i : ℕ, ∀ᶠ n in atTop, viol r n (H i n) = false := by
  let elig : ℕ → ℕ → Bool := fun p y ↦
    decide (p.unpair.1 ≤ p.unpair.2) && viol p.unpair.1 y (H p.unpair.2 y)
  have helig : Computable fun q : ℕ × ℕ × ℕ ↦ elig q.2.1 q.2.2 := by
    have hu : Computable fun q : ℕ × ℕ × ℕ ↦ q.2.1.unpair :=
      Primrec.unpair.to_comp.comp (Computable.fst.comp Computable.snd)
    have hy : Computable fun q : ℕ × ℕ × ℕ ↦ q.2.2 := Computable.snd.comp Computable.snd
    have hle : Computable fun q : ℕ × ℕ × ℕ ↦ decide ((q.2.1.unpair).1 ≤ (q.2.1.unpair).2) :=
      Primrec.nat_le.decide.to_comp.comp (Computable.fst.comp hu) (Computable.snd.comp hu)
    have harg : Computable fun q : ℕ × ℕ × ℕ ↦
        ((q.2.1.unpair).1, q.2.2, H (q.2.1.unpair).2 q.2.2) :=
      Computable.pair (Computable.fst.comp hu)
        (Computable.pair hy (hH.comp (Computable.snd.comp hu) hy))
    exact Primrec.and.to_comp.comp hle (Computable.of_eq (hviol.comp harg) fun _ ↦ rfl)
  let run : ℕ → Option ℕ := canc elig (fun _ ↦ false) 0
  let idx : ℕ → ℕ := fun y ↦ ((run y).map fun p ↦ p.unpair.2).getD y
  have hrun_comp : Computable run :=
    computable_canc (α := ℕ) (E := fun _ ↦ elig) (ov := fun _ _ ↦ false)
      helig (Computable.const false).to₂ (Computable.const 0) Computable.id
  have hidx_comp : Computable idx :=
    Computable.option_getD
      (Computable.option_map hrun_comp
        (Computable.snd.comp (Primrec.unpair.to_comp.comp Computable.snd)).to₂)
      Computable.id
  have hmono_idx : ∀ n : ℕ, Monotone (H · n) := fun n ↦ monotone_nat_of_le_succ (hH_idx · n)
  have hev_idx : ∀ I : ℕ, ∀ᶠ y in atTop, I ≤ idx y := fun I ↦ by
    filter_upwards [eventually_canc_ne elig (fun _ ↦ false) 0 (Nat.pair I I),
      eventually_ge_atTop I] with y hy hIy
    dsimp only [idx]
    cases h : run y with
    | none => exact hIy
    | some p =>
      rw [Option.map_some, Option.getD_some]
      by_contra! hlt
      have hE := (canc_eq_some.mp h).2.2.2.1
      have hji : p.unpair.1 ≤ p.unpair.2 := of_decide_eq_true (Bool.and_eq_true_iff.mp hE).1
      refine hy p ?_ h
      rw [← Nat.pair_unpair p]
      exact (Nat.pair_lt_pair_left _ (hji.trans_lt hlt)).trans (Nat.pair_lt_pair_right _ hlt)
  let t₀ : ℕ → ℕ := fun n ↦ H (idx n) n
  refine ⟨t₀, hH.comp hidx_comp Computable.id,
    fun n ↦ hmono_idx n (Nat.zero_le _),
    fun i ↦ (hev_idx i).mono fun n hn ↦ hmono_idx n hn,
    fun r hr ↦ ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hr
  by_contra hne
  let i := r + N
  let p := Nat.pair r i
  have hup : p.unpair = (r, i) := Nat.unpair_pair r i
  have hfreq : ∃ᶠ y in atTop, viol r y (H i y) = true :=
    (Filter.not_eventually.mp fun h ↦ hne ⟨i, h⟩).mono fun _ ↦ Bool.eq_true_of_not_eq_false
  obtain ⟨y, hy⟩ : ∃ y : ℕ, run y = some p := by
    by_contra! hnone
    obtain ⟨y, hy1, hy2⟩ := (hfreq.and_eventually (eventually_not_eligible hnone)).exists
    exact Bool.false_ne_true (hy2.symm.trans (by simp [elig, hup, hy1, i]))
  have hNy : N ≤ y :=
    (Nat.le_add_left N r).trans ((Nat.right_le_pair r i).trans (canc_le hy).2)
  have hidx_eq : idx y = i := by simp [idx, hy, hup]
  have hE := (Bool.and_eq_true_iff.mp (canc_eq_some.mp hy).2.2.2.1).2
  rw [hup] at hE
  have hfalse : viol r y (H i y) = false := by simpa only [t₀, hidx_eq] using hN y hNy
  exact Bool.false_ne_true (hfalse.symm.trans hE)

/-- **Abstract McCreight–Meyer diagonal union bound.** -/
theorem exists_computable_diagonal_union_bound {F : ℕ → ℕ → ℕ}
    (hF : Computable₂ F) (hF_le : ∀ ⦃i j : ℕ⦄, i ≤ j → F i ≤ᶠ[atTop] F j)
    {viol : ℕ → ℕ → ℕ → Bool}
    (hviol : Computable fun p : ℕ × ℕ × ℕ ↦ viol p.1 p.2.1 p.2.2) :
    ∃ t : ℕ → ℕ,
      Computable t ∧
      (∀ i : ℕ, F i ≤ᶠ[atTop] t) ∧
      ∀ r : ℕ, (∀ᶠ n in atTop, viol r n (t n) = false) →
        ∃ i : ℕ, ∀ᶠ n in atTop, viol r n (F i n) = false := by
  let G : ℕ → ℕ → ℕ := fun i n ↦ partialSups (fun k ↦ F k n) i
  obtain ⟨t, ht, -, hdom, hunion⟩ :=
    exists_pointwise_diagonal_union_bound (computable₂_partialSups hF)
      (fun i n ↦ partialSups_monotone (fun k ↦ F k n) (Nat.le_succ i)) hviol
  refine ⟨t, ht,
    fun i ↦ (hdom i).mono fun n hn ↦ (le_partialSups (fun k ↦ F k n) i).trans hn,
    fun r hr ↦ ?_⟩
  obtain ⟨i, hi⟩ := hunion r hr
  refine ⟨i, ?_⟩
  filter_upwards [hi, partialSups_eventuallyEq_of_eventually_le hF_le i] with n hvn heq
  exact heq ▸ hvn

/-- **Abstract non-decreasing McCreight–Meyer diagonal union bound**
.
-/
theorem exists_computable_monotone_diagonal_union_bound {F : ℕ → ℕ → ℕ}
    (hF : Computable₂ F) (hF_le : ∀ ⦃i j : ℕ⦄, i ≤ j → F i ≤ᶠ[atTop] F j)
    (hF_mono : ∀ i : ℕ, Monotone (F i))
    (hF_unbdd : ∃ i : ℕ, ∀ B : ℕ, ∃ n : ℕ, B ≤ F i n)
    {viol : ℕ → ℕ → ℕ → Bool}
    (hviol : Computable fun p : ℕ × ℕ × ℕ ↦ viol p.1 p.2.1 p.2.2)
    (hviol_mono : ∀ {r n B₁ B₂ : ℕ}, B₁ ≤ B₂ → viol r n B₁ = false → viol r n B₂ = false) :
    ∃ t : ℕ → ℕ,
      Computable t ∧
      Monotone t ∧
      (∀ i : ℕ, F i ≤ᶠ[atTop] t) ∧
      ∀ r : ℕ, (∀ᶠ n in atTop, viol r n (t n) = false) →
        ∃ i : ℕ, ∀ᶠ n in atTop, viol r n (F i n) = false := by
  obtain ⟨i₀, hi₀⟩ := hF_unbdd
  let G : ℕ → ℕ → ℕ := fun i n ↦ partialSups (fun k ↦ F k n) i
  let H : ℕ → ℕ → ℕ := fun i n ↦ G (i + i₀) n
  have hG_comp : Computable₂ G := computable₂_partialSups hF
  have hH_comp : Computable₂ H :=
    hG_comp.comp (Primrec.nat_add.to_comp.comp Computable.fst (Computable.const i₀)) Computable.snd
  have hH_idx : ∀ i n : ℕ, H i n ≤ H (i + 1) n := fun _ n ↦
    partialSups_monotone (fun k ↦ F k n) (by omega)
  have hH_mono : ∀ i : ℕ, Monotone (H i) := fun i ↦
    monotone_partialSups_of_monotone hF_mono (i + i₀)
  have hH0_unbdd : ∀ B : ℕ, ∃ n : ℕ, B ≤ H 0 n := fun B ↦ by
    obtain ⟨n, hn⟩ := hi₀ B
    exact ⟨n, hn.trans (by simpa [H, G] using le_partialSups (fun k ↦ F k n) i₀)⟩
  obtain ⟨t₀, ht₀_comp, hH0_le, hH_dom, hunion⟩ :=
    exists_pointwise_diagonal_union_bound hH_comp hH_idx hviol
  obtain ⟨t, ht_comp, ht_mono, ht_le_t₀, -, htail_dom⟩ :=
    exists_computable_monotone_tailMin ht₀_comp
      (hH_comp.comp (Computable.const 0) Computable.id) (hH_mono 0) hH0_unbdd hH0_le
  refine ⟨t, ht_comp, ht_mono, fun i ↦ ?_, fun r hr ↦ ?_⟩
  · have hFi : F i ≤ᶠ[atTop] H i := Eventually.of_forall fun n ↦
      (le_partialSups (fun k ↦ F k n) i).trans
        (partialSups_monotone (fun k ↦ F k n) (Nat.le_add_right i i₀))
    exact hFi.trans (htail_dom (H i) (hH_mono i) (hH_dom i))
  · obtain ⟨i, hi⟩ := hunion r (hr.mono fun n hvn ↦ hviol_mono (ht_le_t₀ n) hvn)
    refine ⟨i + i₀, ?_⟩
    filter_upwards [hi, partialSups_eventuallyEq_of_eventually_le hF_le (i + i₀)] with n hvn heq
    exact heq ▸ hvn

/-- **Non-decreasing McCreight–Meyer Union Theorem**
.
-/
theorem BlumMeasure.union_theorem_monotone (Φ : BlumMeasure) {F : ℕ → ℕ → ℕ}
    (hF : Computable₂ F) (hF_le : ∀ ⦃i j : ℕ⦄, i ≤ j → F i ≤ᶠ[atTop] F j)
    (hF_mono : ∀ i : ℕ, Monotone (F i))
    (hF_unbdd : ∃ i : ℕ, ∀ B : ℕ, ∃ n : ℕ, B ≤ F i n) :
    ∃ t : ℕ → ℕ,
      Computable t ∧
      Monotone t ∧
      (∀ i : ℕ, F i ≤ᶠ[atTop] t) ∧
      Φ.complexityClass t = ⋃ i : ℕ, Φ.complexityClass (F i) := by
  have hpred : ComputablePred fun p : ℕ × ℕ × ℕ ↦
      ¬ ∃ m ∈ Φ.cost (Denumerable.ofNat Nat.Partrec.Code p.1) p.2.1, m ≤ p.2.2 :=
    (Φ.computablePred_cost_le.comp (Computable.pair
      (Computable.pair
        ((Computable.ofNat Nat.Partrec.Code).comp Computable.fst)
        (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd))).not
  obtain ⟨b, hb_comp, hbeq⟩ := ComputablePred.computable_iff.mp hpred
  have hb_false : ∀ (r n B : ℕ),
      b (r, n, B) = false ↔
        ∃ m ∈ Φ.cost (Denumerable.ofNat Nat.Partrec.Code r) n, m ≤ B := fun r n B ↦ by
    have h1 : (¬ ∃ m ∈ Φ.cost (Denumerable.ofNat Nat.Partrec.Code r) n, m ≤ B) ↔
        b (r, n, B) = true := Iff.of_eq (congrFun hbeq (r, n, B))
    rw [Bool.eq_false_iff, ne_eq, ← h1, not_not]
  obtain ⟨t, ht_comp, ht_mono, ht_dom, hunion⟩ :=
    exists_computable_monotone_diagonal_union_bound hF hF_le hF_mono hF_unbdd
      (viol := fun r n B ↦ b (r, n, B)) hb_comp
      (fun {r n B₁ B₂} hB hv ↦ by
        obtain ⟨m, hm, hle⟩ := (hb_false r n B₁).mp hv
        exact (hb_false r n B₂).mpr ⟨m, hm, hle.trans hB⟩)
  refine ⟨t, ht_comp, ht_mono, ht_dom,
    Set.Subset.antisymm ?_ (Set.iUnion_subset fun i ↦ BlumMeasure.complexityClass_mono (ht_dom i))⟩
  intro g hg
  obtain ⟨c, hc, hev⟩ := BlumMeasure.mem_complexityClass.mp hg
  have hcost : ∀ᶠ n in atTop, b (Encodable.encode c, n, t n) = false :=
    hev.mono fun n hn ↦ (hb_false (Encodable.encode c) n (t n)).mpr (by
      rw [Denumerable.ofNat_encode]
      exact (Φ.forall_mem_cost_iff_exists_of_total hc n).mp hn)
  obtain ⟨i, hi⟩ := hunion (Encodable.encode c) hcost
  refine Set.mem_iUnion.mpr ⟨i, BlumMeasure.mem_complexityClass.mpr ⟨c, hc, hi.mono fun n hn ↦ ?_⟩⟩
  have hex := (hb_false (Encodable.encode c) n (F i n)).mp hn
  rw [Denumerable.ofNat_encode] at hex
  exact (Φ.forall_mem_cost_iff_exists_of_total hc n).mpr hex

/-- **Simultaneous non-decreasing McCreight–Meyer Union Theorem** for a finite family
`Φ : Fin ℓ → BlumMeasure`. -/
theorem BlumMeasure.finite_union_theorem_monotone {ℓ : ℕ} (Φ : Fin ℓ → BlumMeasure)
    {F : ℕ → ℕ → ℕ}
    (hF : Computable₂ F) (hF_le : ∀ ⦃i j : ℕ⦄, i ≤ j → F i ≤ᶠ[atTop] F j)
    (hF_mono : ∀ i : ℕ, Monotone (F i))
    (hF_unbdd : ∃ i : ℕ, ∀ B : ℕ, ∃ n : ℕ, B ≤ F i n) :
    ∃ t : ℕ → ℕ,
      Computable t ∧
      Monotone t ∧
      (∀ j : ℕ, F j ≤ᶠ[atTop] t) ∧
      ∀ i : Fin ℓ, (Φ i).complexityClass t = ⋃ j : ℕ, (Φ i).complexityClass (F j) := by
  obtain ⟨tBase, hBase_comp, hBase_mono, hBase_dom, -⟩ :=
    exists_computable_monotone_diagonal_union_bound hF hF_le hF_mono hF_unbdd
      (viol := fun _ _ _ ↦ false) (Computable.const false) (fun _ h ↦ h)
  choose ts hts_comp hts_mono hts_dom hts_eq using fun i : Fin ℓ ↦
    (Φ i).union_theorem_monotone hF hF_le hF_mono hF_unbdd
  obtain ⟨t, ht_comp, ht_mono, ht_dom, ht_le⟩ :=
    exists_computable_fin_min hBase_comp hBase_mono hBase_dom hts_comp hts_mono hts_dom
  refine ⟨t, ht_comp, ht_mono, ht_dom, fun i ↦ Set.Subset.antisymm ?_
    (Set.iUnion_subset fun j ↦ BlumMeasure.complexityClass_mono (ht_dom j))⟩
  rw [← hts_eq i]
  exact BlumMeasure.complexityClass_mono (Eventually.of_forall (ht_le i))

end Cslib.BlumComplexity
