/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
public import Mathlib.Data.ZMod.Basic

/-!
# Minimum Hamming weight of low-degree functions over `𝔽₂` (Reed–Muller minimum distance)

Any nonzero function `F : BitString n → ZMod 2` of multilinear degree at most `d` (`d ≤ n`), i.e.,
`F ∈ Cslib.BitString.lowDegree (ZMod 2) (Fin n) d`, is nonzero on at least `2 ^ (n - d)` points of
the Boolean cube (`card_support_ge_of_mem_lowDegree`). This is the classical `2 ^ (n - d)` minimum
distance of the binary Reed–Muller code `RM(d, n)`.

## Main results

* `Cslib.BitString.card_support_ge_of_mem_lowDegree`: every nonzero
  `F ∈ lowDegree (ZMod 2) (Fin n) d` (`d ≤ n`) has `2 ^ (n - d) ≤ #{x : BitString n | F x ≠ 0}`.
-/

public section

namespace Cslib.BitString

open Finset

private abbrev snocBit {n : ℕ} (y : BitString n) (b : Bool) : BitString (n + 1) :=
  Fin.snoc (α := fun _ ↦ Bool) y b

private theorem snoc_mem_lowDegree {n D : ℕ} {F : BitString (n + 1) → ZMod 2}
    (hF : F ∈ lowDegree (ZMod 2) (Fin (n + 1)) D) (b : Bool) :
    (fun y : BitString n ↦ F (snocBit y b)) ∈ lowDegree (ZMod 2) (Fin n) D := by
  have hle : lowDegree (ZMod 2) (Fin (n + 1)) D ≤
      (lowDegree (ZMod 2) (Fin n) D).comap
        (LinearMap.funLeft (ZMod 2) (ZMod 2) fun y : BitString n ↦ snocBit y b) := by
    rw [lowDegree, Submodule.span_le]
    rintro _ ⟨S, hS, rfl⟩
    have hScard : #S ≤ D := hS
    change (fun y : BitString n ↦ monomial (ZMod 2) S (snocBit y b)) ∈
      lowDegree (ZMod 2) (Fin n) D
    let S' : Finset (Fin n) := univ.filter fun i ↦ i.castSucc ∈ S
    have hS'_le : #S' ≤ D := by
      have hmap : S'.image Fin.castSucc ⊆ S := by
        intro j hj
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
        exact (mem_filter.mp hi).2
      exact ((card_image_of_injective S' (Fin.castSucc_injective n)).symm.trans_le
        (card_le_card hmap)).trans hScard
    by_cases hlast : Fin.last n ∈ S
    · cases b
      · have hzero : (fun y : BitString n ↦ monomial (ZMod 2) S (snocBit y false)) = 0 := by
          funext y
          rw [monomial_apply]
          have hnot : ¬ ∀ j ∈ S, snocBit y false j = true := fun hall ↦ by
            have := hall (Fin.last n) hlast
            simp [snocBit] at this
          simp [hnot]
        rw [hzero]
        exact Submodule.zero_mem _
      · have heq : (fun y : BitString n ↦ monomial (ZMod 2) S (snocBit y true)) =
            monomial (ZMod 2) S' := by
          funext y
          rw [monomial_apply, monomial_apply]
          have hiff : (∀ j ∈ S, snocBit y true j = true) ↔ ∀ i ∈ S', y i = true :=
            ⟨fun hall i hi ↦ by simpa [snocBit] using hall i.castSucc (mem_filter.mp hi).2,
             fun hall j hj ↦ Fin.lastCases (by simp [snocBit])
               (fun i hi ↦ by simpa [snocBit] using hall i (mem_filter.mpr ⟨mem_univ i, hi⟩)) j hj⟩
          simp [hiff]
        rw [heq]
        exact monomial_mem_lowDegree hS'_le
    · have heq : (fun y : BitString n ↦ monomial (ZMod 2) S (snocBit y b)) =
          monomial (ZMod 2) S' := by
        funext y
        rw [monomial_apply, monomial_apply]
        have hiff : (∀ j ∈ S, snocBit y b j = true) ↔ ∀ i ∈ S', y i = true :=
          ⟨fun hall i hi ↦ by simpa [snocBit] using hall i.castSucc (mem_filter.mp hi).2,
           fun hall j hj ↦ Fin.lastCases (fun h ↦ absurd h hlast)
             (fun i hi ↦ by simpa [snocBit] using hall i (mem_filter.mpr ⟨mem_univ i, hi⟩)) j hj⟩
        simp [hiff]
      rw [heq]
      exact monomial_mem_lowDegree hS'_le
  exact hle hF

private theorem snoc_diff_mem_lowDegree {n e : ℕ} {F : BitString (n + 1) → ZMod 2}
    (hF : F ∈ lowDegree (ZMod 2) (Fin (n + 1)) (e + 1)) :
    (fun y : BitString n ↦ F (snocBit y true) - F (snocBit y false)) ∈
      lowDegree (ZMod 2) (Fin n) e := by
  let L : ((BitString (n + 1)) → ZMod 2) →ₗ[ZMod 2] ((BitString n) → ZMod 2) :=
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun y : BitString n ↦ snocBit y true) -
      LinearMap.funLeft (ZMod 2) (ZMod 2) (fun y : BitString n ↦ snocBit y false)
  have hle : lowDegree (ZMod 2) (Fin (n + 1)) (e + 1) ≤ (lowDegree (ZMod 2) (Fin n) e).comap L := by
    rw [lowDegree, Submodule.span_le]
    rintro _ ⟨S, hS, rfl⟩
    have hScard : #S ≤ e + 1 := hS
    change (fun y : BitString n ↦
      monomial (ZMod 2) S (snocBit y true) - monomial (ZMod 2) S (snocBit y false)) ∈
      lowDegree (ZMod 2) (Fin n) e
    let S' : Finset (Fin n) := univ.filter fun i ↦ i.castSucc ∈ S
    by_cases hlast : Fin.last n ∈ S
    · have hS'_le : #S' ≤ e := by
        have hmap : S'.image Fin.castSucc ⊆ S.erase (Fin.last n) := by
          intro j hj
          obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
          exact mem_erase.mpr ⟨Fin.castSucc_ne_last i, (mem_filter.mp hi).2⟩
        have h1 := (card_image_of_injective S' (Fin.castSucc_injective n)).symm.trans_le
          (card_le_card hmap)
        rw [card_erase_of_mem hlast] at h1
        have hpos : 0 < #S := card_pos.mpr ⟨Fin.last n, hlast⟩
        omega
      have heq : (fun y : BitString n ↦
            monomial (ZMod 2) S (snocBit y true) - monomial (ZMod 2) S (snocBit y false)) =
          monomial (ZMod 2) S' := by
        funext y
        rw [monomial_apply, monomial_apply, monomial_apply]
        have hnot : ¬ ∀ j ∈ S, snocBit y false j = true := fun hall ↦ by
          have := hall (Fin.last n) hlast
          simp [snocBit] at this
        have hiff : (∀ j ∈ S, snocBit y true j = true) ↔ ∀ i ∈ S', y i = true :=
          ⟨fun hall i hi ↦ by simpa [snocBit] using hall i.castSucc (mem_filter.mp hi).2,
           fun hall j hj ↦ Fin.lastCases (by simp [snocBit])
             (fun i hi ↦ by simpa [snocBit] using hall i (mem_filter.mpr ⟨mem_univ i, hi⟩)) j hj⟩
        simp [hnot, hiff]
      rw [heq]
      exact monomial_mem_lowDegree hS'_le
    · have hzero : (fun y : BitString n ↦
          monomial (ZMod 2) S (snocBit y true) - monomial (ZMod 2) S (snocBit y false)) = 0 := by
        funext y
        rw [monomial_apply, monomial_apply]
        have hiff : (∀ j ∈ S, snocBit y true j = true) ↔
            (∀ j ∈ S, snocBit y false j = true) :=
          forall₂_congr fun j hj ↦
            Fin.lastCases (fun h ↦ absurd h hlast) (fun i _ ↦ by simp [snocBit]) j hj
        split_ifs with h₁ h₂ h₂
        · exact sub_self 1
        · exact absurd (hiff.mp h₁) h₂
        · exact absurd (hiff.mpr h₂) h₁
        · exact sub_self 0
      rw [hzero]
      exact Submodule.zero_mem _
  exact hle hF

private theorem card_support_snoc_split {n : ℕ} (F : BitString (n + 1) → ZMod 2) :
    #{x : BitString (n + 1) | F x ≠ 0} =
      #{y : BitString n | F (snocBit y false) ≠ 0} +
      #{y : BitString n | F (snocBit y true) ≠ 0} := by
  let S₀ : Finset (BitString (n + 1)) :=
    (univ.filter fun y : BitString n ↦ F (snocBit y false) ≠ 0).image fun y ↦ snocBit y false
  let S₁ : Finset (BitString (n + 1)) :=
    (univ.filter fun y : BitString n ↦ F (snocBit y true) ≠ 0).image fun y ↦ snocBit y true
  have hdisj : Disjoint S₀ S₁ := by
    rw [disjoint_left]
    rintro x hx₀ hx₁
    obtain ⟨y₀, -, rfl⟩ := mem_image.mp hx₀
    obtain ⟨y₁, -, heq⟩ := mem_image.mp hx₁
    have := congrFun heq (Fin.last n)
    simp [snocBit] at this
  have hunion : univ.filter (fun x : BitString (n + 1) ↦ F x ≠ 0) = S₀ ∪ S₁ := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_union, S₀, S₁, mem_image]
    constructor
    · intro hFx
      let y : BitString n := Fin.init x
      have hx : snocBit y (x (Fin.last n)) = x := Fin.snoc_init_self x
      cases hlast : x (Fin.last n)
      · rw [hlast] at hx; exact Or.inl ⟨y, hx.symm ▸ hFx, hx⟩
      · rw [hlast] at hx; exact Or.inr ⟨y, hx.symm ▸ hFx, hx⟩
    · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩) <;> exact hy
  have hinj : ∀ b : Bool, Function.Injective (fun y : BitString n ↦ snocBit y b) :=
    fun b y₁ y₂ h ↦ funext fun i ↦ by simpa [snocBit] using congrFun h i.castSucc
  rw [hunion, card_union_of_disjoint hdisj, card_image_of_injective _ (hinj false),
    card_image_of_injective _ (hinj true)]

/-- **Reed–Muller minimum weight**: every nonzero polynomial `F ∈ lowDegree (ZMod 2) (Fin n) d` of
degree `d ≤ n` over `ZMod 2` is nonzero on at least `2 ^ (n - d)` points of `BitString n`. -/
theorem card_support_ge_of_mem_lowDegree {n d : ℕ} (hd : d ≤ n) {F : BitString n → ZMod 2}
    (hF : F ∈ lowDegree (ZMod 2) (Fin n) d) (hne : F ≠ 0) :
    2 ^ (n - d) ≤ #{x : BitString n | F x ≠ 0} := by
  induction n generalizing d with
  | zero =>
    have hd0 : d = 0 := Nat.eq_zero_of_le_zero hd
    subst hd0
    have hex : ∃ x : BitString 0, F x ≠ 0 := by
      by_contra hall; push Not at hall; exact hne (funext hall)
    obtain ⟨x, hx⟩ := hex
    exact Nat.succ_le_of_lt (card_pos.mpr ⟨x, mem_filter.mpr ⟨mem_univ x, hx⟩⟩)
  | succ n ih =>
    cases d with
    | zero =>
      have hconst : ∃ c : ZMod 2, F = fun _ ↦ c := by
        have hspan : lowDegree (ZMod 2) (Fin (n + 1)) 0 ≤
            Submodule.span (ZMod 2) {(1 : BitString (n + 1) → ZMod 2)} := by
          rw [lowDegree, Submodule.span_le]
          rintro _ ⟨S, hS, rfl⟩
          rw [card_eq_zero.mp (Nat.eq_zero_of_le_zero hS), monomial_empty]
          exact Submodule.subset_span rfl
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hspan hF)
        exact ⟨c, funext fun _ ↦ by simp⟩
      obtain ⟨c, rfl⟩ := hconst
      have hc0 : c ≠ 0 := fun hc ↦ hne (funext fun _ ↦ hc)
      have hall : ({x : BitString (n + 1) | c ≠ 0} : Finset _) = univ :=
        eq_univ_iff_forall.mpr fun x ↦ mem_filter.mpr ⟨mem_univ x, hc0⟩
      rw [hall, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      exact le_rfl
    | succ e =>
      rw [Nat.succ_sub_succ_eq_sub, card_support_snoc_split]
      let F₀ : BitString n → ZMod 2 := fun y ↦ F (snocBit y false)
      let F₁ : BitString n → ZMod 2 := fun y ↦ F (snocBit y true)
      by_cases heq : F₀ = F₁
      · have hF₀_ne : F₀ ≠ 0 := fun h0 ↦ hne <| funext fun x ↦ by
          have hx : snocBit (Fin.init x) (x (Fin.last n)) = x := Fin.snoc_init_self x
          cases hlast : x (Fin.last n)
          · rw [← hx, hlast]; exact congrFun h0 (Fin.init x)
          · rw [← hx, hlast]; exact congrFun (heq.symm.trans h0) (Fin.init x)
        have he_le : e ≤ n := by omega
        have hF₀_deg : F₀ ∈ lowDegree (ZMod 2) (Fin n) (e + 1) := snoc_mem_lowDegree hF false
        by_cases hen : e = n
        · subst hen
          obtain ⟨y₀, hy₀⟩ : ∃ y, F₀ y ≠ 0 := by
            by_contra hall; push Not at hall; exact hF₀_ne (funext hall)
          have hpos₀ : 1 ≤ #{y : BitString e | F₀ y ≠ 0} :=
            card_pos.mpr ⟨y₀, mem_filter.mpr ⟨mem_univ y₀, hy₀⟩⟩
          have hpos₁ : 1 ≤ #{y : BitString e | F₁ y ≠ 0} := by rwa [← heq]
          change 2 ^ (e - e) ≤ #{y : BitString e | F₀ y ≠ 0} + #{y : BitString e | F₁ y ≠ 0}
          rw [Nat.sub_self, pow_zero]
          omega
        · have he1_le : e + 1 ≤ n := by omega
          have h0 : 2 ^ (n - (e + 1)) ≤ #{y : BitString n | F₀ y ≠ 0} := ih he1_le hF₀_deg hF₀_ne
          have h1 : 2 ^ (n - (e + 1)) ≤ #{y : BitString n | F₁ y ≠ 0} := by rwa [← heq]
          have hpow : 2 ^ (n - e) = 2 ^ (n - (e + 1)) + 2 ^ (n - (e + 1)) := by
            rw [show n - e = (n - (e + 1)) + 1 by omega, pow_succ]
            omega
          change 2 ^ (n - e) ≤ #{y : BitString n | F₀ y ≠ 0} + #{y : BitString n | F₁ y ≠ 0}
          omega
      · have hdiff_ne : (fun y : BitString n ↦ F₁ y - F₀ y) ≠ 0 :=
          fun h0 ↦ heq (funext fun y ↦ (sub_eq_zero.mp (congrFun h0 y)).symm)
        have hdiff_deg : (fun y : BitString n ↦ F₁ y - F₀ y) ∈ lowDegree (ZMod 2) (Fin n) e :=
          snoc_diff_mem_lowDegree hF
        have hsub : univ.filter (fun y : BitString n ↦ F₁ y - F₀ y ≠ 0) ⊆
            univ.filter (fun y : BitString n ↦ F₀ y ≠ 0) ∪
              univ.filter (fun y : BitString n ↦ F₁ y ≠ 0) := by
          intro y hy
          have hne_y := (mem_filter.mp hy).2
          rw [mem_union, mem_filter, mem_filter]
          by_contra hboth
          push Not at hboth
          have h0 : F₀ y = 0 := hboth.1 (mem_univ y)
          have h1 : F₁ y = 0 := hboth.2 (mem_univ y)
          exact hne_y (by simp [h0, h1])
        calc 2 ^ (n - e)
            ≤ #{y : BitString n | F₁ y - F₀ y ≠ 0} := ih (by omega) hdiff_deg hdiff_ne
          _ ≤ #(univ.filter (fun y : BitString n ↦ F₀ y ≠ 0) ∪
              univ.filter (fun y : BitString n ↦ F₁ y ≠ 0)) := card_le_card hsub
          _ ≤ #{y : BitString n | F₀ y ≠ 0} + #{y : BitString n | F₁ y ≠ 0} := card_union_le _ _

end Cslib.BitString
