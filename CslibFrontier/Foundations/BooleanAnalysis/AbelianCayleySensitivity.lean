/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Hypercube
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Potechin–Tsang Induced Subgraph Bound for Finite Abelian Cayley Graphs

Every subset `U` of strictly more than half the elements of a finite additive commutative group `G`
contains an element `u ∈ U` with at least `√(|S| / 2)` Cayley neighbors `u + s ∈ U` for any
symmetric subset `S ⊆ G` with `0 ∉ S`. The proof partitions `S` into at
least `|S| / 2` unordered negation pairs `{g, -g}`, embeds affine Boolean cubes
`z ↦ x₀ + ∑ r : Fin D, (if z r then g r else 0)` over all shifts `x₀ : G`, finds by double
counting a shift whose pullback of `U` covers strictly more than half of `BitString D`, and applies
Huang's induced hypercube theorem (`Cslib.BitString.exists_mem_sqrt_card_le_card_update_mem`).

Specializing to `(Fin n → Fin m)` (`1 ≤ m`) with single-coordinate differences yields the induced
maximum-degree lower bound `√((m - 1) n / 2)` for subsets of the `m`-ary Hamming cube of density
strictly greater than `1 / 2`.

## Main results

* `CslibFrontier.BooleanAnalysis.exists_mem_sqrt_div_two_le_card_add_mem`: for a finite additive
  commutative group `G`, symmetric `S : Finset G`, and `U : Finset G` with
  `Fintype.card G < 2 * U.card`, some `u ∈ U` satisfies
  `√(S.card / 2) ≤ (S.filter fun s ↦ u + s ∈ U).card`.
* `CslibFrontier.BooleanAnalysis.sqrt_div_two_le_maxDegree_induce_addCayley`: induced
  `SimpleGraph.maxDegree` formulation on the symmetric additive Cayley graph of `(G, S)`.
* `CslibFrontier.BooleanAnalysis.exists_mem_sqrt_le_card_hamming_neighbors`: `m`-ary Hamming-cube
  specialization on `Fin n → Fin m` (`1 ≤ m`) giving a point `u ∈ U` with at least
  `√((m - 1) n / 2)` Hamming-distance-`1` neighbors in `U` whenever `m ^ n < 2 * U.card`.
-/

public section

namespace CslibFrontier.BooleanAnalysis

open Cslib Cslib.BitString

private lemma exists_neg_pair_reps {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) :
    ∃ (D : ℕ) (g : Fin D → G),
      S.card ≤ 2 * D ∧
      (∀ r : Fin D, g r ∈ S) ∧
      (∀ r₁ r₂ : Fin D, r₁ ≠ r₂ → g r₁ ≠ g r₂ ∧ g r₁ ≠ -g r₂) := by
  let pairFn (x : G) : Finset G := ({x, -x} : Finset G)
  let pairs : Finset (Finset G) := S.image pairFn
  have hcov : S ⊆ pairs.biUnion id := fun x hx ↦
    Finset.mem_biUnion.mpr ⟨pairFn x, Finset.mem_image_of_mem pairFn hx, by simp [pairFn]⟩
  have hcard : S.card ≤ 2 * pairs.card := by
    calc S.card ≤ (pairs.biUnion id).card := Finset.card_le_card hcov
      _ ≤ ∑ P ∈ pairs, P.card := Finset.card_biUnion_le
      _ ≤ ∑ _P ∈ pairs, 2 := Finset.sum_le_sum fun P hP ↦ by
          obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hP
          exact Finset.card_le_two
      _ = 2 * pairs.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  let e : Fin pairs.card ≃ {P : Finset G // P ∈ pairs} := pairs.equivFin.symm
  have hrep : ∀ r : Fin pairs.card, ∃ x ∈ S, pairFn x = (e r).1 := fun r ↦ by
    obtain ⟨x, hxS, hxP⟩ := Finset.mem_image.mp (e r).2
    exact ⟨x, hxS, hxP⟩
  choose g hgS hgP using hrep
  refine ⟨pairs.card, g, hcard, hgS, fun r₁ r₂ hne ↦ ?_⟩
  have hP_ne : pairFn (g r₁) ≠ pairFn (g r₂) := fun heq ↦
    hne (e.injective (Subtype.ext ((hgP r₁).symm.trans (heq.trans (hgP r₂)))))
  refine ⟨fun h ↦ hP_ne (congrArg pairFn h), fun h ↦ hP_ne ?_⟩
  ext y
  simp only [pairFn, Finset.mem_insert, Finset.mem_singleton, h, neg_neg, or_comm]

private lemma affineCube_update_not {G : Type*} [AddCommGroup G] {D : ℕ}
    (g : Fin D → G) (x₀ : G) (z : BitString D) (r : Fin D) :
    (x₀ + ∑ k : Fin D, if Function.update z r (!z r) k then g k else 0) =
      (x₀ + ∑ k : Fin D, if z k then g k else 0) + if z r then -g r else g r := by
  have hr : r ∈ (Finset.univ : Finset (Fin D)) := Finset.mem_univ r
  have h1 := (Finset.add_sum_erase Finset.univ
    (fun k ↦ if Function.update z r (!z r) k then g k else 0) hr).symm
  have h2 := (Finset.add_sum_erase Finset.univ (fun k ↦ if z k then g k else 0) hr).symm
  have hrest : (∑ k ∈ Finset.univ.erase r, if Function.update z r (!z r) k then g k else 0) =
      ∑ k ∈ Finset.univ.erase r, if z k then g k else 0 :=
    Finset.sum_congr rfl fun k hk ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [h1, h2, hrest, Function.update_self]
  cases z r <;> simp <;> abel

/-- **Potechin–Tsang abelian Cayley sensitivity bound**: in any finite additive commutative group
`G`, for any symmetric subset `S ⊆ G` and any `U ⊆ G` with `|G| < 2 |U|`, there exists `u ∈ U` with
at least `√(|S| / 2)` shifts `s ∈ S` such that `u + s ∈ U`. -/
theorem exists_mem_sqrt_div_two_le_card_add_mem {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] {S : Finset G} (hsym : ∀ g ∈ S, -g ∈ S)
    {U : Finset G} (hU : Fintype.card G < 2 * U.card) :
    ∃ u ∈ U, Real.sqrt ((S.card : ℝ) / 2) ≤ (S.filter fun s ↦ u + s ∈ U).card := by
  obtain ⟨D, g, hSD, hgS, hg_sep⟩ := exists_neg_pair_reps S
  let φ (x₀ : G) (z : BitString D) : G := x₀ + ∑ r : Fin D, if z r then g r else 0
  let W (x₀ : G) : Finset (BitString D) := Finset.univ.filter fun z ↦ φ x₀ z ∈ U
  have hsum_W : (∑ x₀ : G, (W x₀).card) = 2 ^ D * U.card := by
    simp_rw [W, Finset.card_filter]
    rw [Finset.sum_comm]
    have hinner : ∀ z : BitString D,
        (∑ x₀ : G, if φ x₀ z ∈ U then (1 : ℕ) else 0) = U.card := fun z ↦ by
      have heq := Equiv.sum_comp (Equiv.addRight (∑ r : Fin D, if z r then g r else 0))
        (fun y : G ↦ if y ∈ U then (1 : ℕ) else 0)
      exact heq.trans (by rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter])
    simp_rw [hinner]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      smul_eq_mul]
  have hex_shift : ∃ x₀ : G, 2 ^ D < 2 * (W x₀).card := by
    by_contra! hall
    have hle : ∑ x₀ : G, 2 * (W x₀).card ≤ ∑ _x₀ : G, 2 ^ D :=
      Finset.sum_le_sum fun x₀ _ ↦ hall x₀
    rw [← Finset.mul_sum, hsum_W, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    have hpos : 0 < 2 ^ D := pow_pos (by decide) D
    nlinarith
  obtain ⟨x₀, hx₀⟩ := hex_shift
  have hcard_D : 2 ^ Fintype.card (Fin D) < 2 * (W x₀).card := by
    simpa [Fintype.card_fin] using hx₀
  obtain ⟨z, hzW, hdeg⟩ := exists_mem_sqrt_card_le_card_update_mem (V := W x₀) hcard_D Finset.univ
  set u₀ : G := φ x₀ z
  have hu₀ : u₀ ∈ U := (Finset.mem_filter.mp hzW).2
  set Nz : Finset (Fin D) := Finset.univ.filter fun r ↦ Function.update z r (!z r) ∈ W x₀
  let step (r : Fin D) : G := if z r then -g r else g r
  have hstep_inj : Function.Injective step := fun r₁ r₂ h ↦ by
    by_contra hne
    obtain ⟨hne_eq, hne_neg⟩ := hg_sep r₁ r₂ hne
    dsimp only [step] at h
    cases hz₁ : z r₁ <;> cases hz₂ : z r₂ <;> simp only [hz₁, hz₂, Bool.false_eq_true,
      ↓reduceIte] at h
    · exact hne_eq h
    · exact hne_neg h
    · exact hne_neg (by simpa using congrArg Neg.neg h)
    · exact hne_eq (neg_inj.mp h)
  have himg_sub : Nz.image step ⊆ S.filter (fun s ↦ u₀ + s ∈ U) := by
    intro s hs
    obtain ⟨r, hrNz, rfl⟩ := Finset.mem_image.mp hs
    have hmemS : step r ∈ S := by
      dsimp only [step]; cases z r
      · exact hgS r
      · exact hsym (g r) (hgS r)
    have hmemW : Function.update z r (!z r) ∈ W x₀ := (Finset.mem_filter.mp hrNz).2
    have hmemU : u₀ + step r ∈ U := by
      have hupd := affineCube_update_not g x₀ z r
      simpa [u₀, φ, step, hupd] using (Finset.mem_filter.mp hmemW).2
    exact Finset.mem_filter.mpr ⟨hmemS, hmemU⟩
  have hD_le : (S.card : ℝ) / 2 ≤ (D : ℝ) := by
    have hcast : (S.card : ℝ) ≤ 2 * (D : ℝ) := by exact_mod_cast hSD
    linarith
  have hcard_le : Nz.card ≤ (S.filter fun s ↦ u₀ + s ∈ U).card := by
    rw [← Finset.card_image_of_injective Nz hstep_inj]
    exact Finset.card_le_card himg_sub
  refine ⟨u₀, hu₀, (Real.sqrt_le_sqrt hD_le).trans ?_⟩
  have hdeg' : Real.sqrt (D : ℝ) ≤ (Nz.card : ℝ) := by simpa [Nz] using hdeg
  exact hdeg'.trans (Nat.cast_le.mpr hcard_le)

/-- **Potechin–Tsang induced maximum-degree bound** on the symmetric additive Cayley graph
`G_S` (`Adj x y ↔ x ≠ y ∧ y - x ∈ S`): every `U ⊆ G` with `|G| < 2 |U|` satisfies
`√(|S| / 2) ≤ (G_S.induce U).maxDegree`. -/
theorem sqrt_div_two_le_maxDegree_induce_addCayley {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] {S : Finset G} (h0 : (0 : G) ∉ S) (hsym : ∀ g ∈ S, -g ∈ S)
    {U : Finset G} (hU : Fintype.card G < 2 * U.card) :
    let cay : SimpleGraph G :=
      { Adj := fun x y ↦ x ≠ y ∧ y - x ∈ S
        symm := ⟨fun _ _ ⟨hne, hmem⟩ ↦ ⟨hne.symm, by simpa [neg_sub] using hsym _ hmem⟩⟩
        loopless := ⟨fun _ h ↦ h.1 rfl⟩ }
    Real.sqrt ((S.card : ℝ) / 2) ≤ ((cay.induce (U : Set G)).maxDegree : ℝ) := by
  intro cay
  obtain ⟨u, huU, hle⟩ := exists_mem_sqrt_div_two_le_card_add_mem hsym hU
  refine hle.trans (Nat.cast_le.mpr ?_)
  let emb : {s : G // s ∈ S.filter fun s ↦ u + s ∈ U} →
      (cay.induce (U : Set G)).neighborFinset ⟨u, huU⟩ := fun s ↦
    ⟨⟨u + s.1, (Finset.mem_filter.mp s.2).2⟩, (SimpleGraph.mem_neighborFinset _ _ _).mpr
      ⟨fun h ↦ h0 (by
        have hs0 : s.1 = 0 := by simpa using h.symm
        exact hs0 ▸ (Finset.mem_filter.mp s.2).1),
        by simpa using (Finset.mem_filter.mp s.2).1⟩⟩
  have hemb_inj : Function.Injective emb := fun s₁ s₂ h ↦ Subtype.ext <|
    add_left_cancel (congrArg (fun v ↦ v.1.1) h)
  calc (S.filter fun s ↦ u + s ∈ U).card
      = Fintype.card {s : G // s ∈ S.filter fun s ↦ u + s ∈ U} := (Fintype.card_coe _).symm
    _ ≤ Fintype.card ((cay.induce (U : Set G)).neighborFinset ⟨u, huU⟩) :=
        Fintype.card_le_of_injective emb hemb_inj
    _ = (cay.induce (U : Set G)).degree ⟨u, huU⟩ := by
        rw [Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ (cay.induce (U : Set G)).maxDegree :=
        (cay.induce (U : Set G)).degree_le_maxDegree ⟨u, huU⟩

/-- **`m`-ary Hamming-cube specialization**: for `1 ≤ m` and any `U ⊆ Fin n → Fin m` covering
strictly more than half of the cube (`m ^ n < 2 * U.card`), some `u ∈ U` has at least
`√((m - 1) n / 2)` Hamming-distance-`1` neighbors in `U`. -/
theorem exists_mem_sqrt_le_card_hamming_neighbors {n m : ℕ} (hm : 1 ≤ m)
    {U : Finset (Fin n → Fin m)} (hU : m ^ n < 2 * U.card) :
    ∃ u ∈ U, Real.sqrt ((((m - 1) * n : ℕ) : ℝ) / 2) ≤
      (U.filter fun v ↦ (Finset.univ.filter fun i : Fin n ↦ u i ≠ v i).card = 1).card := by
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let fiber (i : Fin n) : Finset (Fin n → Fin m) :=
    ((Finset.univ : Finset (Fin m)).erase 0).image fun a ↦ Function.update (0 : Fin n → Fin m) i a
  let S : Finset (Fin n → Fin m) := Finset.univ.biUnion fiber
  have hsym : ∀ g ∈ S, -g ∈ S := fun g hg ↦ by
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_image.mpr
      ⟨-a, Finset.mem_erase.mpr ⟨neg_ne_zero.mpr (Finset.mem_erase.mp ha).1, Finset.mem_univ _⟩,
        funext fun j ↦ ?_⟩⟩
    by_cases hji : j = i <;> simp [hji]
  have hdisj : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint fiber :=
    fun i₁ _ i₂ _ hne ↦ Finset.disjoint_left.mpr fun g hg₁ hg₂ ↦ by
      obtain ⟨a₁, ha₁, rfl⟩ := Finset.mem_image.mp hg₁
      obtain ⟨a₂, -, heq⟩ := Finset.mem_image.mp hg₂
      have hv := congrFun heq i₁
      rw [Function.update_of_ne hne, Function.update_self] at hv
      exact (Finset.mem_erase.mp ha₁).1 hv.symm
  have hS_card : S.card = (m - 1) * n := by
    rw [Finset.card_biUnion hdisj]
    have hfib : ∀ i : Fin n, (fiber i).card = m - 1 := fun i ↦ by
      rw [Finset.card_image_of_injective _ (Function.update_injective _ i),
        Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fin]
    simp [hfib, mul_comm]
  have hcardG : Fintype.card (Fin n → Fin m) < 2 * U.card := by
    simpa [Fintype.card_pi, Fintype.card_fin] using hU
  obtain ⟨u, huU, hle⟩ := exists_mem_sqrt_div_two_le_card_add_mem hsym hcardG
  refine ⟨u, huU, (hS_card ▸ hle).trans (Nat.cast_le.mpr ?_)⟩
  have hmap : (S.filter fun s ↦ u + s ∈ U).image (u + ·) ⊆
      U.filter (fun v ↦ (Finset.univ.filter fun i : Fin n ↦ u i ≠ v i).card = 1) := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hsS, husU⟩ := Finset.mem_filter.mp hs
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hsS
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
    have hdiff : (Finset.univ.filter fun j : Fin n ↦
        u j ≠ (u + Function.update (0 : Fin n → Fin m) i a) j) = {i} := by
      ext j
      by_cases hji : j = i <;> simp [hji, ha0]
    exact Finset.mem_filter.mpr ⟨husU, by rw [hdiff, Finset.card_singleton]⟩
  rw [← Finset.card_image_of_injective _ (add_right_injective u)]
  exact Finset.card_le_card hmap

end CslibFrontier.BooleanAnalysis
