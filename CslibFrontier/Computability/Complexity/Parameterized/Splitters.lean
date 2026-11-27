/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Mathlib.Data.Finset.Card

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Prime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Hypercube Partition Systems and Universal Binary Splitters

Explicit derandomization gadgets for parameterized complexity and hardness of approximation:

1. **$(\kappa, \rho)$-hypercube partition family** (`HypercubeUniverse`, `hypercubeSlice`): exact
   covering characterization showing that a collection of slices covers `Fin ρ → Fin κ` iff it
   contains a complete coordinate row.
2. **FKS and Bertrand–FKS universal binary splitters** (`IsUniversalBinarySplitter`,
   `fksPrimeFamily`, `nextPrimeGt`, `primeLinearHash`): explicit polynomial-time prime-finding and
   prime-linear disjoint-subset separation (`exists_primeLinear_disjoint_separator`).

## Main definitions

* `Cslib.Complexity.HypercubeUniverse`, `Cslib.Complexity.hypercubeSlice`.
* `Cslib.Complexity.IsUniversalBinarySplitter`, `Cslib.Complexity.modIndicator`,
  `Cslib.Complexity.fksPrimeFamily`, `Cslib.Complexity.nextPrimeGt`,
  `Cslib.Complexity.primeLinearHash`.

## Main results

* `Cslib.Complexity.biUnion_hypercubeSlice_eq_univ_iff`,
  `Cslib.Complexity.biUnion_hypercubeSlice_ne_univ_of_card_lt`: exact covering characterization of
  $(\kappa, \rho)$-hypercube partition slices.
* `Cslib.Complexity.exists_prime_mod_injOn_of_prod_gt`,
  `Cslib.Complexity.isUniversalBinarySplitter_fksPrimeFamily`: FKS prime-modulus splitter
  soundness.
* `Cslib.Complexity.prime_nextPrimeGt`, `Cslib.Complexity.lt_nextPrimeGt`,
  `Cslib.Complexity.nextPrimeGt_le`,
  `Cslib.Complexity.computableInPolyTime_nextPrimeGt`,
  `Cslib.Complexity.exists_primeLinearHash_injOn`,
  `Cslib.Complexity.exists_primeLinear_disjoint_separator`: constructive Bertrand prime finder and
  prime-linear disjoint-subset separator.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-! ### : $(\kappa, \rho)$-Hypercube Partition Family -/

/-- Ground universe `Fin ρ → Fin κ` of the `(κ, ρ)`-hypercube partition family. -/
abbrev HypercubeUniverse (κ ρ : ℕ) : Type := Fin ρ → Fin κ

/-- Cardinality of `HypercubeUniverse κ ρ` equals `κ ^ ρ`. -/
theorem card_hypercubeUniverse (κ ρ : ℕ) :
    Fintype.card (HypercubeUniverse κ ρ) = κ ^ ρ := by
  simp [HypercubeUniverse]

/-- Coordinate slice `P_{x, y} = {z : Fin ρ → Fin κ | z x = y}` of `HypercubeUniverse κ ρ`. -/
def hypercubeSlice {κ ρ : ℕ} (x : Fin ρ) (y : Fin κ) : Finset (HypercubeUniverse κ ρ) :=
  Finset.univ.filter fun z => z x = y

@[simp]
theorem mem_hypercubeSlice_iff {κ ρ : ℕ} {x : Fin ρ} {y : Fin κ}
    {z : HypercubeUniverse κ ρ} : z ∈ hypercubeSlice x y ↔ z x = y := by
  simp [hypercubeSlice]

/-- Distinct values `y₁ ≠ y₂` along the same coordinate `x` yield disjoint hypercube slices. -/
theorem disjoint_hypercubeSlice_of_ne {κ ρ : ℕ} (x : Fin ρ) {y₁ y₂ : Fin κ} (hne : y₁ ≠ y₂) :
    Disjoint (hypercubeSlice x y₁) (hypercubeSlice x y₂) :=
  Finset.disjoint_left.mpr fun _ hz₁ hz₂ =>
    hne ((mem_hypercubeSlice_iff.mp hz₁).symm.trans (mem_hypercubeSlice_iff.mp hz₂))

/-- For any fixed coordinate `x : Fin ρ`, the slices `hypercubeSlice x y` (`y : Fin κ`) are
pairwise disjoint. -/
theorem pairwiseDisjoint_hypercubeSlice_row {κ ρ : ℕ} (x : Fin ρ) :
    (Set.univ : Set (Fin κ)).PairwiseDisjoint (hypercubeSlice (κ := κ) x) :=
  fun _ _ _ _ hne => disjoint_hypercubeSlice_of_ne x hne

/-- For any fixed coordinate `x : Fin ρ`, the slices `hypercubeSlice x y` (`y : Fin κ`) cover the
entire hypercube `HypercubeUniverse κ ρ`. -/
@[simp]
theorem biUnion_hypercubeSlice_row_eq_univ {κ ρ : ℕ} (x : Fin ρ) :
    (Finset.univ : Finset (Fin κ)).biUnion (hypercubeSlice x) = Finset.univ := by
  ext; simp

/-- **Exact Covering Characterization of Hypercube Slices**: a union of coordinate slices indexed
by `I : Finset (Fin ρ × Fin κ)` covers `HypercubeUniverse κ ρ` if and only if `I` contains a full
coordinate row `{x} × Fin κ` for some `x : Fin ρ`. -/
theorem biUnion_hypercubeSlice_eq_univ_iff {κ ρ : ℕ} (I : Finset (Fin ρ × Fin κ)) :
    I.biUnion (fun p => hypercubeSlice p.1 p.2) = Finset.univ ↔
      ∃ x : Fin ρ, ∀ y : Fin κ, (x, y) ∈ I := by
  constructor
  · intro hcov; by_contra! hno
    let z : HypercubeUniverse κ ρ := fun x => (hno x).choose
    rcases Finset.mem_biUnion.mp (hcov ▸ Finset.mem_univ z) with ⟨⟨x, y⟩, hmem, hzx⟩
    rw [mem_hypercubeSlice_iff] at hzx; dsimp only [z] at hzx
    exact (hno x).choose_spec (hzx ▸ hmem)
  · rintro ⟨x, hx⟩
    ext z
    simp only [Finset.mem_biUnion, mem_hypercubeSlice_iff, Finset.mem_univ, iff_true]
    exact ⟨(x, z x), hx (z x), rfl⟩

/-- If `1 ≤ κ` and every coordinate row `x : Fin ρ` contributes strictly fewer than `κ` pairs to
`I`, the indexed slices cannot cover `HypercubeUniverse κ ρ`. -/
theorem biUnion_hypercubeSlice_ne_univ_of_card_lt {κ ρ : ℕ} {I : Finset (Fin ρ × Fin κ)}
    (hκ : 1 ≤ κ) (hrow : ∀ x : Fin ρ, (I.filter fun p => p.1 = x).card < κ) :
    I.biUnion (fun p => hypercubeSlice p.1 p.2) ≠ Finset.univ := by
  intro heq
  rcases (biUnion_hypercubeSlice_eq_univ_iff I).mp heq with ⟨x, hx⟩
  have _ : Nonempty (Fin κ) := ⟨⟨0, hκ⟩⟩
  have hsub : (Finset.univ : Finset (Fin κ)).map ⟨fun y => (x, y), fun _ _ h => (Prod.mk.inj h).2⟩ ⊆
      I.filter (fun p => p.1 = x) := fun p hp => by
    rcases Finset.mem_map.mp hp with ⟨y, -, rfl⟩
    exact Finset.mem_filter.mpr ⟨hx y, rfl⟩
  exact (hrow x).not_ge (by simpa using Finset.card_le_card hsub)

/-! ### : FKS Prime-Modulus Splitter and Bertrand–FKS Prime-Linear Separator -/

/-- A finite family `H` of Boolean functions `Fin N → Bool` is an `(N, L)`-universal binary
splitter if for every subset `S : Finset (Fin N)` with `S.card ≤ L` and every `u ∈ S`, some
`h ∈ H` evaluates to `true` at `u` and to `false` at all `v ∈ S` with `v ≠ u`. -/
@[expose]
def IsUniversalBinarySplitter (N L : ℕ) (H : Finset (Fin N → Bool)) : Prop :=
  ∀ S : Finset (Fin N), S.card ≤ L → ∀ u ∈ S,
    ∃ h ∈ H, h u = true ∧ ∀ v ∈ S, v ≠ u → h v = false

/-- Decidability of `IsUniversalBinarySplitter`. -/
instance instDecidableIsUniversalBinarySplitter (N L : ℕ) (H : Finset (Fin N → Bool)) :
    Decidable (IsUniversalBinarySplitter N L H) :=
  inferInstanceAs (Decidable (∀ S : Finset (Fin N), S.card ≤ L → ∀ u ∈ S,
    ∃ h ∈ H, h u = true ∧ ∀ v ∈ S, v ≠ u → h v = false))

/-- Modular residue indicator function `x ↦ decide (x.1 % p = r)` on `Fin N`. -/
@[expose]
def modIndicator (N p r : ℕ) : Fin N → Bool := fun x => decide (x.1 % p = r)

/-- The Fredman–Komlós–Szemerédi prime-modulus binary family on `Fin N` associated with a finite
set `P : Finset ℕ` of moduli. -/
def fksPrimeFamily (N : ℕ) (P : Finset ℕ) : Finset (Fin N → Bool) :=
  P.biUnion fun p => (Finset.range p).image (modIndicator N p)

theorem mem_fksPrimeFamily_iff {N : ℕ} {P : Finset ℕ} {h : Fin N → Bool} :
    h ∈ fksPrimeFamily N P ↔ ∃ p ∈ P, ∃ r < p, modIndicator N p r = h := by
  simp [fksPrimeFamily]

/-- The cardinality of `fksPrimeFamily N P` is at most `∑ p ∈ P, p`. -/
theorem card_fksPrimeFamily_le (N : ℕ) (P : Finset ℕ) :
    (fksPrimeFamily N P).card ≤ ∑ p ∈ P, p :=
  Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le.trans (by simp))

private lemma dvd_sub_of_mod_eq {x y m : ℕ} (hle : x ≤ y) (hmod : x % m = y % m) :
    m ∣ y - x := by
  refine ⟨y / m - x / m, ?_⟩
  have := Nat.div_add_mod x m
  have := Nat.div_add_mod y m
  rw [Nat.mul_sub]
  omega

private lemma prod_primes_dvd {P : Finset ℕ} {D : ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (hdvd : ∀ p ∈ P, p ∣ D) : (∏ p ∈ P, p) ∣ D := by
  induction P using Finset.cons_induction with
  | empty => simp
  | cons q Q hq ih =>
    rw [Finset.prod_cons]
    have hq_pr : Nat.Prime q := hP q (Finset.mem_cons_self q Q)
    have hQ_pr : ∀ p ∈ Q, Nat.Prime p := fun p hp => hP p (Finset.mem_cons_of_mem hp)
    have hcop : Nat.Coprime q (∏ p ∈ Q, p) := Nat.Coprime.prod_right fun p hp =>
      hq_pr.coprime_iff_not_dvd.mpr fun hqp =>
        hq (((hQ_pr p hp).dvd_iff_eq hq_pr.ne_one).mp hqp ▸ hp)
    exact hcop.mul_dvd_of_dvd_of_dvd (hdvd q (Finset.mem_cons_self q Q))
      (ih hQ_pr fun p hp => hdvd p (Finset.mem_cons_of_mem hp))

private lemma card_lt_pairs_eq_choose_two {N : ℕ} (S : Finset (Fin N)) :
    ((S ×ˢ S).filter (fun uv : Fin N × Fin N => uv.1 < uv.2)).card = S.card.choose 2 := by
  rw [← Finset.card_powersetCard 2 S]
  refine Finset.card_bij (fun uv _ => {uv.1, uv.2}) (fun uv huv => ?_) (fun a ha b hb heq => ?_)
    (fun T hT => ?_)
  · rcases Finset.mem_filter.mp huv with ⟨hmem, hlt⟩
    rcases Finset.mem_product.mp hmem with ⟨hu, hv⟩
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.insert_subset_iff.mpr ⟨hu, Finset.singleton_subset_iff.mpr hv⟩,
        Finset.card_pair hlt.ne⟩
  · have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have h1 : a.1 ∈ ({b.1, b.2} : Finset (Fin N)) := heq ▸ Finset.mem_insert_self a.1 {a.2}
    have h2 : a.2 ∈ ({b.1, b.2} : Finset (Fin N)) :=
      heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self a.2)
    have h3 : b.1 ∈ ({a.1, a.2} : Finset (Fin N)) := heq.symm ▸ Finset.mem_insert_self b.1 {b.2}
    have h4 : b.2 ∈ ({a.1, a.2} : Finset (Fin N)) :=
      heq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b.2)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3 h4
    ext <;> omega
  · rcases Finset.mem_powersetCard.mp hT with ⟨hsub, hcard⟩
    rcases Finset.card_eq_two.mp hcard with ⟨x, y, hne, rfl⟩
    have hxS : x ∈ S := hsub (Finset.mem_insert_self x {y})
    have hyS : y ∈ S := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxS, hyS⟩, hlt⟩, rfl⟩
    · exact ⟨(y, x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hyS, hxS⟩, hgt⟩,
        Finset.pair_comm y x⟩

/-- **FKS Prime-Modulus Injection**: if `1 ≤ N` and `P` is a finite set of primes whose product
strictly exceeds `N ^ L.choose 2`, then for every subset `S : Finset (Fin N)` of cardinality at
most `L`, some prime `p ∈ P` makes `x ↦ x.1 % p` injective on `S`. -/
theorem exists_prime_mod_injOn_of_prod_gt {N L : ℕ} (hN : 1 ≤ N) {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (hprod : N ^ L.choose 2 < ∏ p ∈ P, p)
    {S : Finset (Fin N)} (hS : S.card ≤ L) :
    ∃ p ∈ P, Set.InjOn (fun x : Fin N => x.1 % p) (S : Set (Fin N)) := by
  have hPne : P.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.prod_empty] at hprod
    exact (Nat.not_lt.mpr (Nat.one_le_pow _ _ hN)) hprod
  by_cases hcard1 : S.card ≤ 1
  · rcases hPne with ⟨p, hp⟩
    exact ⟨p, hp, fun x hx y hy _ => Finset.card_le_one_iff.mp hcard1 hx hy⟩
  · push Not at hcard1
    let pairs := (S ×ˢ S).filter (fun uv : Fin N × Fin N => uv.1 < uv.2)
    have hpairs_card : pairs.card ≤ L.choose 2 :=
      card_lt_pairs_eq_choose_two S ▸ Nat.choose_le_choose 2 hS
    have hpairs_pos : 0 < pairs.card :=
      card_lt_pairs_eq_choose_two S ▸ Nat.choose_pos (by omega)
    let D : ℕ := ∏ uv ∈ pairs, (uv.2.1 - uv.1.1)
    have hD_pos : 1 ≤ D := Finset.one_le_prod fun uv huv => by
      have hlt := (Finset.mem_filter.mp huv).2; omega
    have hD_lt : D < N ^ L.choose 2 := by
      have hle1 : D ≤ ∏ _uv ∈ pairs, (N - 1) := Finset.prod_le_prod fun uv huv => by
        have hlt := (Finset.mem_filter.mp huv).2; have hv := uv.2.2; omega
      rw [Finset.prod_const] at hle1
      exact (hle1.trans_lt (Nat.pow_lt_pow_left (by omega) hpairs_pos.ne')).trans_le
        (Nat.pow_le_pow_right hN hpairs_card)
    by_contra! hbad
    have hdvd_all : ∀ p ∈ P, p ∣ D := fun p hp => by
      have hnotinj := hbad p hp
      rw [Set.InjOn] at hnotinj
      push Not at hnotinj
      rcases hnotinj with ⟨x, hx, y, hy, hmod, hne⟩
      rcases lt_or_gt_of_ne hne with hxy | hyx
      · have hm : (x, y) ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩
        exact (dvd_sub_of_mod_eq (show x.1 ≤ y.1 from hxy.le) hmod).trans
          (Finset.dvd_prod_of_mem (fun uv : Fin N × Fin N => uv.2.1 - uv.1.1) hm)
      · have hm : (y, x) ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy, hx⟩, hyx⟩
        exact (dvd_sub_of_mod_eq (show y.1 ≤ x.1 from hyx.le) hmod.symm).trans
          (Finset.dvd_prod_of_mem (fun uv : Fin N × Fin N => uv.2.1 - uv.1.1) hm)
    have := Nat.le_of_dvd (by omega) (prod_primes_dvd hP hdvd_all)
    omega

/-- **FKS Universal Binary Splitter Soundness**: whenever `P` is a finite set of primes satisfying
`N ^ L.choose 2 < ∏ p ∈ P, p`, `fksPrimeFamily N P` is an `(N, L)`-universal binary splitter. -/
theorem isUniversalBinarySplitter_fksPrimeFamily {N L : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (hprod : N ^ L.choose 2 < ∏ p ∈ P, p) :
    IsUniversalBinarySplitter N L (fksPrimeFamily N P) := by
  intro S hS u hu
  rcases exists_prime_mod_injOn_of_prod_gt (by have := u.2; omega) hP hprod hS with
    ⟨p, hpP, hinj⟩
  refine ⟨modIndicator N p (u.1 % p),
    mem_fksPrimeFamily_iff.mpr ⟨p, hpP, u.1 % p, Nat.mod_lt _ (hP p hpP).pos, rfl⟩,
    by simp [modIndicator], fun v hv hne => ?_⟩
  simp only [modIndicator, decide_eq_false_iff_not]
  exact fun hmod => hne (hinj hv hu hmod)

/-- Constructive Bertrand prime finder: returns the least prime `p` strictly greater than
`max n 1` (guaranteed in `[max n 1 + 1, 2 * max n 1]` by Bertrand's postulate). -/
@[expose]
def nextPrimeGt (n : ℕ) : ℕ :=
  ((List.range (2 * max n 1 + 1)).find? fun p => decide (max n 1 < p) && decide p.Prime).getD 2

private lemma find_nextPrimeGt_spec (n : ℕ) :
    max n 1 < nextPrimeGt n ∧ Nat.Prime (nextPrimeGt n) ∧ nextPrimeGt n ≤ 2 * max n 1 := by
  let P : ℕ → Bool := fun p => decide (max n 1 < p) && decide p.Prime
  let B : ℕ := 2 * max n 1 + 1
  rcases Nat.exists_prime_lt_and_le_two_mul (max n 1) (by omega) with ⟨q, hq_prime, hq_gt, hq_le⟩
  have hex : ∃ p ∈ List.range B, P p = true :=
    ⟨q, List.mem_range.mpr (by omega), by simp [P, max_lt_iff.mp hq_gt, hq_prime]⟩
  rcases Option.isSome_iff_exists.mp (List.find?_isSome.mpr hex) with ⟨p₀, hp₀⟩
  have hnp : nextPrimeGt n = p₀ := by
    change ((List.range B).find? P).getD 2 = p₀
    simp [hp₀]
  rw [hnp]
  rcases List.find?_eq_some_iff_append.mp hp₀ with ⟨hPp₀, as, bs, hrange, -⟩
  have hp₀_lt : p₀ < B := List.mem_range.mp (by rw [hrange]; simp)
  simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hPp₀
  exact ⟨hPp₀.1, hPp₀.2, by omega⟩

/-- `nextPrimeGt n` is always prime. -/
theorem prime_nextPrimeGt (n : ℕ) : Nat.Prime (nextPrimeGt n) :=
  (find_nextPrimeGt_spec n).2.1

/-- `nextPrimeGt n` is strictly greater than `max n 1`. -/
theorem lt_nextPrimeGt (n : ℕ) : max n 1 < nextPrimeGt n :=
  (find_nextPrimeGt_spec n).1

/-- `nextPrimeGt n` is at most `2 * max n 1` (by Bertrand's postulate). -/
theorem nextPrimeGt_le (n : ℕ) : nextPrimeGt n ≤ 2 * max n 1 :=
  (find_nextPrimeGt_spec n).2.2

/-- Computing `nextPrimeGt` in unary is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_nextPrimeGt :
    ComputableInPolyTime nextPrimeGt encUnary encUnary := by
  have hmax : ComputableInPolyTime (fun n : ℕ => max n 1) encUnary encUnary :=
    ComputableInPolyTime.unary_max.comp
      (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const 1))
  have hB : ComputableInPolyTime (fun n : ℕ => 2 * max n 1 + 1) encUnary encUnary :=
    ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hmax)
      (ComputableInPolyTime.const 1)
  have hfind : ComputableInPolyTime
      (fun n : ℕ =>
        (List.range (2 * max n 1 + 1)).find? fun p => decide (max n 1 < p) && decide p.Prime)
      encUnary (encOption encUnary) := by
    refine ComputableInPolyTime.findWithInput (ComputableInPolyTime.range.comp hB) ?_
    exact ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.unary_lt.comp
        ((hmax.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _)))
      (ComputableInPolyTime.unary_decide_prime.comp (ComputableInPolyTime.snd _ _))
  have hget : ComputableInPolyTime (fun o : Option ℕ => o.getD 2) (encOption encUnary) encUnary :=
    by fun_prop
  exact hget.comp hfind

/-- Prime-linear two-stage modular hash `((a * x) % q) % m`. -/
@[expose]
def primeLinearHash (q m a x : ℕ) : ℕ := ((a * x) % q) % m

/-- Computing `primeLinearHash` in unary is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_primeLinearHash {γ : Type} {encIn : γ ↪ List Bool}
    {q m a v : γ → ℕ}
    (hq : ComputableInPolyTime q encIn encUnary)
    (hm : ComputableInPolyTime m encIn encUnary)
    (ha : ComputableInPolyTime a encIn encUnary)
    (hv : ComputableInPolyTime v encIn encUnary) :
    ComputableInPolyTime (fun x => primeLinearHash (q x) (m x) (a x) (v x)) encIn encUnary := by
  unfold primeLinearHash
  exact ComputableInPolyTime.unary_mod'
    (ComputableInPolyTime.unary_mod' (ComputableInPolyTime.unary_mul' ha hv) hq) hm

private lemma mul_mod_inj_of_prime {q d : ℕ} (hq : Nat.Prime q) (hd0 : 1 ≤ d) (hdq : d < q) :
    Set.InjOn (fun a : ℕ => (a * d) % q) (Finset.Icc 1 (q - 1) : Set ℕ) := by
  intro a₁ ha₁ a₂ ha₂ hmod
  rw [Finset.mem_coe, Finset.mem_Icc] at ha₁ ha₂
  have not_dvd_sub : ∀ {x y : ℕ}, x < y → y < q → (x * d) % q = (y * d) % q → False := by
    intro x y hxy _ hm
    have hdvd : q ∣ y * d - x * d := dvd_sub_of_mod_eq (Nat.mul_le_mul_right d hxy.le) hm
    rw [← Nat.sub_mul] at hdvd
    exact (hq.dvd_mul.mp hdvd).elim (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
      (Nat.not_dvd_of_pos_of_lt hd0 hdq)
  rcases lt_trichotomy a₁ a₂ with hlt | rfl | hgt
  · exact (not_dvd_sub hlt (by omega) hmod).elim
  · rfl
  · exact (not_dvd_sub hgt (by omega) hmod.symm).elim

private lemma bad_multipliers_card_le {q m u v : ℕ} (hq : Nat.Prime q) (hm : 1 ≤ m)
    (huv : u < v) (hvq : v < q) :
    ((Finset.Icc 1 (q - 1)).filter fun a =>
        primeLinearHash q m a u = primeLinearHash q m a v).card ≤ 2 * ((q - 1) / m) := by
  set I := Finset.Icc 1 (q - 1)
  set d := v - u
  have hd1 : 1 ≤ d := by omega
  have hdq : d < q := by omega
  let bad := I.filter fun a => primeLinearHash q m a u = primeLinearHash q m a v
  let K := Finset.Icc 1 ((q - 1) / m)
  let W := K.image (· * m) ∪ K.image (fun k => q - k * m)
  have hinj : Set.InjOn (fun a : ℕ => (a * d) % q) (bad : Set ℕ) :=
    (mul_mod_inj_of_prime hq hd1 hdq).mono (Finset.coe_subset.mpr (Finset.filter_subset _ I))
  have hsub : bad.image (fun a => (a * d) % q) ⊆ W := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨a, ha, rfl⟩
    rcases Finset.mem_filter.mp ha with ⟨haI, hhash⟩
    rcases Finset.mem_Icc.mp haI with ⟨ha1, haq⟩
    simp only [primeLinearHash] at hhash
    set ru := (a * u) % q
    set rv := (a * v) % q
    set rem := (a * d) % q
    have hru_lt : ru < q := Nat.mod_lt _ hq.pos
    have hrv_lt : rv < q := Nat.mod_lt _ hq.pos
    have hrem_lt : rem < q := Nat.mod_lt _ hq.pos
    have hrem_pos : 1 ≤ rem := by
      by_contra h0
      exact (hq.dvd_mul.mp (Nat.dvd_of_mod_eq_zero (by omega))).elim
        (Nat.not_dvd_of_pos_of_lt ha1 (by omega)) (Nat.not_dvd_of_pos_of_lt hd1 hdq)
    have hrv_eq : rv = (ru + rem) % q := by
      have hv_eq : a * v = a * u + a * d := by rw [← Nat.mul_add]; congr 1; omega
      rw [show rv = (a * v) % q from rfl, hv_eq, Nat.add_mod]
    by_cases hsum : ru + rem < q
    · rw [Nat.mod_eq_of_lt hsum] at hrv_eq
      rcases (show rv - ru = rem by omega) ▸
          dvd_sub_of_mod_eq (show ru ≤ rv by omega) hhash with ⟨k, hk⟩
      rw [mul_comm] at hk
      have hk1 : 1 ≤ k := by rcases k with _ | _ <;> [(simp at hk; omega); omega]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨k, Finset.mem_Icc.mpr ⟨hk1, (Nat.le_div_iff_mul_le hm).mpr (by omega)⟩, hk.symm⟩)
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hrv_eq
      rcases (show ru - rv = q - rem by omega) ▸
          dvd_sub_of_mod_eq (show rv ≤ ru by omega) hhash.symm with ⟨k, hk⟩
      rw [mul_comm] at hk
      have hk1 : 1 ≤ k := by rcases k with _ | _ <;> [(simp at hk; omega); omega]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨k, Finset.mem_Icc.mpr ⟨hk1, (Nat.le_div_iff_mul_le hm).mpr (by omega)⟩, by omega⟩)
  calc
    bad.card = (bad.image (fun a => (a * d) % q)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ W.card := Finset.card_le_card hsub
    _ ≤ (K.image (· * m)).card + (K.image (fun k => q - k * m)).card := Finset.card_union_le _ _
    _ ≤ K.card + K.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * ((q - 1) / m) := by simp [K]; omega

/-- **Bertrand–FKS Prime-Linear Injection**: for every prime `q > max N 2` and every subset
`S : Finset (Fin N)` of cardinality at most `L`, some multiplier `a ∈ Finset.Icc 1 (q - 1)` makes
`x ↦ primeLinearHash q (max (L * L) 1) a x.1` injective on `S`. -/
theorem exists_primeLinearHash_injOn {N L q : ℕ} (hq : Nat.Prime q) (hNq : max N 2 < q)
    {S : Finset (Fin N)} (hS : S.card ≤ L) :
    ∃ a ∈ Finset.Icc 1 (q - 1),
      Set.InjOn (fun x : Fin N => primeLinearHash q (max (L * L) 1) a x.1) (S : Set (Fin N)) := by
  set m := max (L * L) 1
  set I := Finset.Icc 1 (q - 1)
  have hq3 : 3 ≤ q := by have := le_max_right N 2; omega
  by_cases hcard1 : S.card ≤ 1
  · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩,
      fun x hx y hy _ => Finset.card_le_one_iff.mp hcard1 hx hy⟩
  · push Not at hcard1
    have hL2 : 2 ≤ L := by omega
    have hm_eq : m = L * L := max_eq_left (by nlinarith)
    have hm_pos : 1 ≤ m := le_max_right _ _
    let pairs := (S ×ˢ S).filter (fun uv : Fin N × Fin N => uv.1 < uv.2)
    let badUnion := pairs.biUnion fun uv =>
      I.filter fun a => primeLinearHash q m a uv.1.1 = primeLinearHash q m a uv.2.1
    have htwo_choose : 2 * pairs.card ≤ L * (L - 1) := by
      rw [card_lt_pairs_eq_choose_two]
      have hch : S.card.choose 2 ≤ L.choose 2 := Nat.choose_le_choose 2 hS
      have hmul : 2 * L.choose 2 = L * (L - 1) := by
        rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self L).two_dvd]
      omega
    have hbad_card : badUnion.card < I.card := by
      have hle1 : badUnion.card ≤ ∑ uv ∈ pairs, 2 * ((q - 1) / m) :=
        Finset.card_biUnion_le.trans (Finset.sum_le_sum fun uv huv =>
          bad_multipliers_card_le hq hm_pos (Finset.mem_filter.mp huv).2
            (lt_of_lt_of_le uv.2.2 ((le_max_left N 2).trans hNq.le)))
      rw [Finset.sum_const, smul_eq_mul] at hle1
      have hle2 : pairs.card * (2 * ((q - 1) / m)) ≤ L * (L - 1) * ((q - 1) / m) := by
        rw [show pairs.card * (2 * ((q - 1) / m)) = (2 * pairs.card) * ((q - 1) / m) by ring]
        exact Nat.mul_le_mul_right _ htwo_choose
      have hstrict : L * (L - 1) * ((q - 1) / m) < q - 1 := by
        by_cases hqm : (q - 1) / m = 0
        · rw [hqm]; omega
        · have hdiv_pos : 1 ≤ (q - 1) / m := Nat.pos_of_ne_zero hqm
          have hLL : L * (L - 1) < m := by
            rw [hm_eq]
            cases L with
            | zero => omega
            | succ L' => simp
          exact (Nat.mul_lt_mul_of_pos_right hLL hdiv_pos).trans_le (Nat.mul_div_le (q - 1) m)
      have hIcard : I.card = q - 1 := by simp [I]
      omega
    rcases Finset.exists_mem_notMem_of_card_lt_card hbad_card with ⟨a, haI, hanot⟩
    refine ⟨a, haI, fun x hx y hy hcoll => ?_⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hxy | hyx
    · exact hanot (Finset.mem_biUnion.mpr
        ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩,
          Finset.mem_filter.mpr ⟨haI, hcoll⟩⟩)
    · exact hanot (Finset.mem_biUnion.mpr
        ⟨(y, x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy, hx⟩, hyx⟩,
          Finset.mem_filter.mpr ⟨haI, hcoll.symm⟩⟩)

private def packBits : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | m + 1, f => 2 * packBits m (fun i => f (i + 1)) + if f 0 then 1 else 0

private lemma packBits_lt_two_pow : ∀ (m : ℕ) (f : ℕ → Bool), packBits m f < 2 ^ m
  | 0, _ => by simp [packBits]
  | m + 1, f => by
    have := packBits_lt_two_pow m (fun i => f (i + 1))
    rw [packBits, Nat.pow_succ]
    cases f 0 <;> simp <;> omega

private lemma testBit_packBits : ∀ {m : ℕ} (f : ℕ → Bool) {i : ℕ}, i < m →
    Nat.testBit (packBits m f) i = f i
  | 0, _, _, hi => by omega
  | m + 1, f, 0, _ => by rw [packBits]; cases f 0 <;> simp [Nat.testBit_zero]
  | m + 1, f, i + 1, hi => by
    rw [packBits, Nat.testBit_succ, show (2 * packBits m (fun j => f (j + 1)) +
        if f 0 then 1 else 0) / 2 = packBits m (fun j => f (j + 1)) by
        cases f 0 <;> [simp; simp [Nat.mul_add_div]]]
    exact testBit_packBits (fun j => f (j + 1)) (by omega)

/-- **Bertrand–FKS Prime-Linear Disjoint-Subset Separator**: for all disjoint subsets
`A, B : Finset (Fin N)` with `(A ∪ B).card ≤ L`, setting `q = nextPrimeGt (max N 2)` and
`m = max (L * L) 1`, there exist a multiplier `a ∈ Finset.Icc 1 (q - 1)` and a bitmask
`mask < 2 ^ m` whose bit lookup separates `A` (`true`) from `B` (`false`). -/
theorem exists_primeLinear_disjoint_separator {N L : ℕ} {A B : Finset (Fin N)}
    (hdisj : Disjoint A B) (hcard : (A ∪ B).card ≤ L) :
    ∃ a ∈ Finset.Icc 1 (nextPrimeGt (max N 2) - 1),
      ∃ mask < 2 ^ max (L * L) 1,
        (∀ u ∈ A,
          Nat.testBit mask (primeLinearHash (nextPrimeGt (max N 2)) (max (L * L) 1) a u.1) =
            true) ∧
        (∀ v ∈ B,
          Nat.testBit mask (primeLinearHash (nextPrimeGt (max N 2)) (max (L * L) 1) a v.1) =
            false) := by
  set q := nextPrimeGt (max N 2)
  set m := max (L * L) 1
  have hq : Nat.Prime q := prime_nextPrimeGt (max N 2)
  have hNq : max N 2 < q := by
    have h := lt_nextPrimeGt (max N 2)
    rwa [max_eq_left (show 1 ≤ max N 2 by have := le_max_right N 2; omega)] at h
  rcases exists_primeLinearHash_injOn hq hNq hcard with ⟨a, haI, hinj⟩
  let hfun : Fin N → ℕ := fun x => primeLinearHash q m a x.1
  let imgA : Finset ℕ := A.image hfun
  have hm_pos : 0 < m := by have := le_max_right (L * L) 1; omega
  refine ⟨a, haI, packBits m (fun t => decide (t ∈ imgA)), packBits_lt_two_pow m _,
    fun u hu => ?_, fun v hv => ?_⟩
  · have hlt : primeLinearHash q m a u.1 < m := Nat.mod_lt _ hm_pos
    rw [testBit_packBits _ hlt]
    exact decide_eq_true (Finset.mem_image_of_mem hfun hu)
  · have hlt : primeLinearHash q m a v.1 < m := Nat.mod_lt _ hm_pos
    rw [testBit_packBits _ hlt, decide_eq_false_iff_not]
    rintro hmem
    rcases Finset.mem_image.mp hmem with ⟨u, huA, huv⟩
    have heq : u = v := hinj (Finset.mem_coe.mpr (Finset.mem_union_left B huA))
      (Finset.mem_coe.mpr (Finset.mem_union_right A hv)) huv
    exact Finset.disjoint_left.mp hdisj huA (heq ▸ hv)

end Cslib.Complexity
