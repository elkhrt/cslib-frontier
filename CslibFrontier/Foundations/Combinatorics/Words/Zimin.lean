/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Card
public import CslibFrontier.Foundations.Combinatorics.Words.Avoidability

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Relation

/-!
# Zimin's Theorem and the Bean–Ehrenfeucht–McNulty Characterization

This module completes the three-way characterization of unavoidable word patterns proved by Bean,
Ehrenfeucht, and McNulty, Zimin, and Sapir: a finite pattern `w : List A` is
unavoidable if and only if some canonical Zimin word `ziminWord k` reflects `w`, if and only if
`w`
reduces to `` by iteratively deleting free sets (`CslibFrontier.Word.IsFreeSetReducible`), if
and only
if `w` reduces to `` by iteratively deleting free letters and identifying distinct occurring
letters (`CslibFrontier.Word.IsBEMReducible`).

To establish necessity (`IsUnavoidable w → ∃ k, Reflects (ziminWord k) w`) constructively under
standard Lean axioms, we iterate a `q`-uniform affine-line block morphism over `Fin q × Fin q` for
`q = w.length + 2`, project along a boundary-safe coordinate slot found by pigeonhole, and lift
reflection in `ziminWord k₀` across deleted non-occurring-slot letters via rainbow-padded Zimin
words. As corollaries we deduce that every nonempty unavoidable pattern admits a free letter and
that every unavoidable pattern over `r` letters has length at most `2 ^ r - 1`.

## Main results

* `CslibFrontier.Word.IsUnavoidable.exists_reflects_ziminWord`: every unavoidable pattern is
  reflected by
  some canonical Zimin word `ziminWord k`.
* `CslibFrontier.Word.isUnavoidable_iff_exists_reflects_ziminWord`: **Zimin's Theorem** — `w` is
  unavoidable iff some `ziminWord k` reflects `w`.
* `CslibFrontier.Word.isUnavoidable_iff_isFreeSetReducible`: **Zimin–Sapir Theorem** — `w` is
  unavoidable
  iff `w` reduces to `` by iteratively deleting free sets.
* `CslibFrontier.Word.IsFreeSet.isUnavoidable_of_deleteLetters` /
  `CslibFrontier.Word.IsFreeLetter.isUnavoidable_of_deleteLetter`: deleting a free set or free
  letter
  reflects unavoidability backwards.
* `CslibFrontier.Word.isUnavoidable_iff_isBEMReducible`: **Bean–Ehrenfeucht–McNulty Theorem** —
  `w` is
  unavoidable iff `w` reduces to `` by deleting free letters and identifying occurring letters.
* `CslibFrontier.Word.IsUnavoidable.exists_isFreeLetter`: every nonempty unavoidable pattern has
  at least
  one free letter.
* `CslibFrontier.Word.IsUnavoidable.length_le_two_pow_card_sub_one`: every unavoidable pattern
  whose
  letters lie in `s : Finset A` has length at most `2 ^ s.card - 1`.
-/

public section

namespace CslibFrontier.Word

section AffineDesubstitution

variable {A : Type*}

private theorem flatMap_singleton_eq {B : Type*} (w : List B) : w.flatMap (fun a ↦ [a]) = w := by
  induction w with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, ih]

private theorem flatMap_flatMap {B C : Type*} (u : List A) (φ : A → List B) (ψ : B → List C) :
    (u.flatMap φ).flatMap ψ = u.flatMap (fun a ↦ (φ a).flatMap ψ) := by
  induction u with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, List.flatMap_append, ih]

private theorem isInfix_flatMap {B C : Type*} {s v : List B} (h : s <:+: v) (ψ : B → List C) :
    s.flatMap ψ <:+: v.flatMap ψ := by
  rcases h with ⟨l₁, l₂, rfl⟩
  exact ⟨l₁.flatMap ψ, l₂.flatMap ψ, by simp [List.flatMap_append]⟩

private theorem infix_pair_getElem {B : Type*} {s t w : List B} {x y : B}
    (hst : s ++ [x, y] ++ t = w) :
    ∃ (h₀ : s.length < w.length) (h₁ : s.length + 1 < w.length),
      w[s.length]'h₀ = x ∧ w[s.length + 1]'h₁ = y := by
  subst hst
  have hlen : (s ++ [x, y] ++ t).length = s.length + 2 + t.length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · have hcat : s ++ [x, y] ++ t = s ++ (x :: y :: t) := by simp [List.append_assoc]
    simp only [hcat, List.getElem_append_right (Nat.le_refl s.length), Nat.sub_self,
      List.getElem_cons_zero]
  · have hcat : s ++ [x, y] ++ t = (s ++ [x]) ++ (y :: t) := by simp [List.append_assoc]
    have hle : (s ++ [x]).length ≤ s.length + 1 := by simp
    have hsub : s.length + 1 - (s ++ [x]).length = 0 := by simp
    simp only [hcat, List.getElem_append_right hle, hsub, List.getElem_cons_zero]

private def finList (q : ℕ) : List (Fin q) :=
  (List.range q).attach.map fun ⟨i, hi⟩ ↦ ⟨i, List.mem_range.mp hi⟩

private theorem length_finList (q : ℕ) : (finList q).length = q := by
  simp [finList]

private theorem getElem_finList {q i : ℕ} (hi : i < q) :
    (finList q)[i]'(by simp [length_finList, hi]) = ⟨i, hi⟩ := by
  simp [finList]

private def affineBlock {q : ℕ} (hq : 0 < q) (p : Fin q × Fin q) : List (Fin q × Fin q) :=
  (finList q).map fun j ↦ (j, ⟨(p.1.1 * j.1 + p.2.1) % q, Nat.mod_lt _ hq⟩)

private theorem length_affineBlock {q : ℕ} (hq : 0 < q) (p : Fin q × Fin q) :
    (affineBlock hq p).length = q := by
  simp [affineBlock, length_finList]

private theorem getElem_affineBlock {q : ℕ} (hq : 0 < q) (p : Fin q × Fin q) {r : ℕ} (hr : r < q) :
    (affineBlock hq p)[r]'(by simp [length_affineBlock, hr]) =
      (⟨r, hr⟩, ⟨(p.1.1 * r + p.2.1) % q, Nat.mod_lt _ hq⟩) := by
  simp only [affineBlock, List.getElem_map, getElem_finList hr]

private def recoverPair {q : ℕ} (hq : 0 < q) (j₀ : ℕ) (y₀ y₁ : Fin q) : Fin q × Fin q :=
  let aVal := (y₁.1 + q - y₀.1) % q
  let bVal := (y₀.1 + q - (aVal * j₀) % q) % q
  (⟨aVal, Nat.mod_lt _ hq⟩, ⟨bVal, Nat.mod_lt _ hq⟩)

private theorem recoverPair_spec {q : ℕ} (hq : 0 < q) {j₀ : ℕ} (p : Fin q × Fin q) :
    recoverPair hq j₀
      ⟨(p.1.1 * j₀ + p.2.1) % q, Nat.mod_lt _ hq⟩
      ⟨(p.1.1 * (j₀ + 1) + p.2.1) % q, Nat.mod_lt _ hq⟩ = p := by
  rcases p with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  set y₀ := (a * j₀ + b) % q
  set y₁ := (a * (j₀ + 1) + b) % q
  have hy₀ : y₀ < q := Nat.mod_lt _ hq
  have hy₁ : y₁ < q := Nat.mod_lt _ hq
  have hstep : y₁ = (y₀ + a) % q := by
    have hmul : a * (j₀ + 1) + b = (a * j₀ + b) + a := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_right_comm]
    dsimp [y₁, y₀]
    simp [hmul, Nat.add_mod]
  have ha_rec : (y₁ + q - y₀) % q = a := by
    by_cases hlt : y₀ + a < q
    · have hy₁_eq : y₁ = y₀ + a := by rw [hstep, Nat.mod_eq_of_lt hlt]
      have hsub : y₁ + q - y₀ = q + a := by omega
      rw [hsub, Nat.add_mod_left, Nat.mod_eq_of_lt ha]
    · have hlt2 : y₀ + a - q < q := by omega
      have heq : y₀ + a = q + (y₀ + a - q) := by omega
      have hmod : (y₀ + a) % q = y₀ + a - q := by
        conv_lhs => rw [heq]
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt hlt2]
      have hy₁_eq : y₁ = y₀ + a - q := hstep.trans hmod
      have hsub : y₁ + q - y₀ = a := by omega
      rw [hsub, Nat.mod_eq_of_lt ha]
  set d := (a * j₀) % q
  have hd : d < q := Nat.mod_lt _ hq
  have hy₀_d : y₀ = (d + b) % q := by
    dsimp [y₀, d]
    simp [Nat.add_mod]
  have hb_rec : (y₀ + q - d) % q = b := by
    by_cases hlt : d + b < q
    · have hy₀_eq : y₀ = d + b := by rw [hy₀_d, Nat.mod_eq_of_lt hlt]
      have hsub : y₀ + q - d = q + b := by omega
      rw [hsub, Nat.add_mod_left, Nat.mod_eq_of_lt hb]
    · have hlt2 : d + b - q < q := by omega
      have heq : d + b = q + (d + b - q) := by omega
      have hmod : (d + b) % q = d + b - q := by
        conv_lhs => rw [heq]
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt hlt2]
      have hy₀_eq : y₀ = d + b - q := hy₀_d.trans hmod
      have hsub : y₀ + q - d = b := by omega
      rw [hsub, Nat.mod_eq_of_lt hb]
  ext <;> simp [recoverPair, y₀, y₁, ha_rec, d, hb_rec]

private def extractBlocks {q : ℕ} (hq : 0 < q) (j₀ : ℕ) :
    List (Fin q × Fin q) → List (Fin q × Fin q)
  | [] => []
  | [_] => []
  | x :: y :: rest =>
    if x.1.1 = j₀ then recoverPair hq j₀ x.2 y.2 :: extractBlocks hq j₀ (y :: rest)
    else extractBlocks hq j₀ (y :: rest)

private theorem extractBlocks_append_of_getLast_ne {q : ℕ} (hq : 0 < q) (j₀ : ℕ) :
    ∀ (u v : List (Fin q × Fin q)),
      (∀ hu : u ≠ [], (u.getLast hu).1.1 ≠ j₀) →
      extractBlocks hq j₀ (u ++ v) = extractBlocks hq j₀ u ++ extractBlocks hq j₀ v
  | [], v, _ => by simp [extractBlocks]
  | [x], v, hne => by
    have hx : x.1.1 ≠ j₀ := hne (List.cons_ne_nil _ _)
    cases v with
    | nil => simp [extractBlocks]
    | cons y vs => simp [extractBlocks, hx]
  | x :: y :: us, v, hne => by
    have hne' : ∀ h : y :: us ≠ [], ((y :: us).getLast h).1.1 ≠ j₀ := by
      intro h
      have hlast : (x :: y :: us).getLast (List.cons_ne_nil _ _) = (y :: us).getLast h :=
        List.getLast_cons h
      rw [← hlast]
      exact hne (List.cons_ne_nil _ _)
    have ih := extractBlocks_append_of_getLast_ne hq j₀ (y :: us) v hne'
    simp only [List.cons_append] at ih ⊢
    simp only [extractBlocks]
    split_ifs <;> simp [ih]

private theorem extractBlocks_affineBlock {q : ℕ} (hq : 0 < q) {j₀ : ℕ} (hj₀ : j₀ + 1 < q)
    (p : Fin q × Fin q) : extractBlocks hq j₀ (affineBlock hq p) = [p] := by
  classical
  let f : Fin q → Fin q × Fin q := fun j ↦ (j, ⟨(p.1.1 * j.1 + p.2.1) % q, Nat.mod_lt _ hq⟩)
  have haux : ∀ (s : List (Fin q)),
      (∀ r : ℕ, (hr : r + 1 < s.length) → (s[r + 1]'hr).1 = (s[r]'(Nat.lt_of_succ_lt hr)).1 + 1) →
      extractBlocks hq j₀ (s.map f) =
        if ∃ r : ℕ, ∃ hr : r + 1 < s.length, (s[r]'(Nat.lt_of_succ_lt hr)).1 = j₀
        then [p] else [] := by
    intro s hs
    induction s with
    | nil => simp [extractBlocks]
    | cons a s' ih =>
      cases s' with
      | nil => simp [extractBlocks]
      | cons b s'' =>
        have hab : b.1 = a.1 + 1 := hs 0 (by simp)
        have hs' : ∀ r : ℕ, (hr : r + 1 < (b :: s'').length) →
            ((b :: s'')[r + 1]'hr).1 = ((b :: s'')[r]'(Nat.lt_of_succ_lt hr)).1 + 1 :=
          fun r hr ↦ hs (r + 1) (by simpa using Nat.succ_lt_succ hr)
        have hmono : ∀ r : ℕ, (hr : r < (b :: s'').length) →
            ((b :: s'')[r]'hr).1 = b.1 + r := by
          intro r
          induction r with
          | zero => intro _; simp
          | succ r ihr =>
            intro hr
            rw [hs' r hr, ihr (Nat.lt_of_succ_lt hr)]
            omega
        conv_lhs =>
          rw [List.map_cons, List.map_cons]
          dsimp [extractBlocks]
          rw [← List.map_cons]
        by_cases ha : (f a).1.1 = j₀
        · have ha' : a.1 = j₀ := ha
          subst ha'
          have hno_later : ¬ ∃ r : ℕ, ∃ hr : r + 1 < (b :: s'').length,
              ((b :: s'')[r]'(Nat.lt_of_succ_lt hr)).1 = a.1 := by
            rintro ⟨r, hr, heq⟩
            have := hmono r (Nat.lt_of_succ_lt hr)
            omega
          have hex : ∃ r : ℕ, ∃ hr : r + 1 < (a :: b :: s'').length,
              ((a :: b :: s'')[r]'(Nat.lt_of_succ_lt hr)).1 = a.1 :=
            ⟨0, by simp, rfl⟩
          have hfa : (f a).1.1 = a.1 := rfl
          rw [ih hs']
          simp only [hfa, ↓reduceIte, hno_later, hex]
          have hrec := recoverPair_spec hq (j₀ := a.1) p
          simpa [f, hab] using congrArg (· :: []) hrec
        · have ha' : a.1 ≠ j₀ := ha
          have hex_iff : (∃ r : ℕ, ∃ hr : r + 1 < (a :: b :: s'').length,
              ((a :: b :: s'')[r]'(Nat.lt_of_succ_lt hr)).1 = j₀) ↔
            (∃ r : ℕ, ∃ hr : r + 1 < (b :: s'').length,
              ((b :: s'')[r]'(Nat.lt_of_succ_lt hr)).1 = j₀) := by
            constructor
            · rintro ⟨r, hr, heq⟩
              cases r with
              | zero => exact absurd heq ha'
              | succ r' => exact ⟨r', by simpa using hr, heq⟩
            · rintro ⟨r', hr', heq⟩
              exact ⟨r' + 1, Nat.succ_lt_succ hr', heq⟩
          rw [ih hs']
          simp only [ha, hex_iff, ↓reduceIte]
  have hs_step : ∀ r : ℕ, (hr : r + 1 < (finList q).length) →
      ((finList q)[r + 1]'hr).1 = ((finList q)[r]'(Nat.lt_of_succ_lt hr)).1 + 1 := by
    intro r hr
    rw [length_finList] at hr
    rw [getElem_finList hr, getElem_finList (Nat.lt_of_succ_lt hr)]
  have hex : ∃ r : ℕ, ∃ hr : r + 1 < (finList q).length,
      ((finList q)[r]'(Nat.lt_of_succ_lt hr)).1 = j₀ := by
    refine ⟨j₀, by rw [length_finList]; exact hj₀, ?_⟩
    rw [getElem_finList (Nat.lt_of_succ_lt hj₀)]
  change extractBlocks hq j₀ ((finList q).map f) = [p]
  rw [haux (finList q) hs_step]
  simp only [hex, ↓reduceIte]

private theorem getLast_affineBlock_ne {q : ℕ} (hq : 0 < q) {j₀ : ℕ} (hj₀ : j₀ + 1 < q)
    (p : Fin q × Fin q) (hne : affineBlock hq p ≠ []) :
    ((affineBlock hq p).getLast hne).1.1 ≠ j₀ := by
  have hlen : (affineBlock hq p).length = q := length_affineBlock hq p
  rw [List.getLast_eq_getElem]
  have heq : (affineBlock hq p)[(affineBlock hq p).length - 1] =
      (affineBlock hq p)[q - 1]'(by rw [hlen]; omega) := by
    congr 1; omega
  rw [heq, getElem_affineBlock hq p (by omega)]
  dsimp
  omega

private theorem extractBlocks_flatMap_affineBlock {q : ℕ} (hq : 0 < q) {j₀ : ℕ} (hj₀ : j₀ + 1 < q)
    (W : List (Fin q × Fin q)) :
    extractBlocks hq j₀ (W.flatMap (affineBlock hq)) = W := by
  induction W with
  | nil => simp [extractBlocks]
  | cons p ps ih =>
    rw [List.flatMap_cons,
      extractBlocks_append_of_getLast_ne hq j₀ _ _ (getLast_affineBlock_ne hq hj₀ p),
      extractBlocks_affineBlock hq hj₀ p, ih]
    rfl

private theorem cyclic_pair_in_flatMap_affineBlock {q : ℕ} (hq : 0 < q) (W : List (Fin q × Fin q))
    {x y : Fin q × Fin q} (hxy : [x, y] <:+: W.flatMap (affineBlock hq)) :
    y.1.1 = (x.1.1 + 1) % q := by
  induction W with
  | nil =>
    rcases hxy with ⟨s, t, hst⟩
    have := congrArg List.length hst
    simp at this
    | cons p ps ih =>
    rw [List.flatMap_cons] at hxy
    rcases hxy with ⟨s, t, hst⟩
    have hlen_p : (affineBlock hq p).length = q := length_affineBlock hq p
    obtain ⟨hw₀, hw₁, hwx, hwy⟩ := infix_pair_getElem hst
    by_cases hs : s.length + 1 < q
    · have hx_eq : x = (affineBlock hq p)[s.length]'(by omega) := by
        have h2 : (affineBlock hq p ++ ps.flatMap (affineBlock hq))[s.length]'hw₀ =
            (affineBlock hq p)[s.length]'(by omega) :=
          List.getElem_append_left (by omega)
        exact hwx.symm.trans h2
      have hy_eq : y = (affineBlock hq p)[s.length + 1]'(by omega) := by
        have h2 : (affineBlock hq p ++ ps.flatMap (affineBlock hq))[s.length + 1]'hw₁ =
            (affineBlock hq p)[s.length + 1]'(by omega) :=
          List.getElem_append_left (by omega)
        exact hwy.symm.trans h2
      rw [hx_eq, hy_eq, getElem_affineBlock hq p (by omega), getElem_affineBlock hq p (by omega)]
      dsimp
      rw [Nat.mod_eq_of_lt (by omega)]
    · by_cases hboundary : s.length + 1 = q
      · have hx_eq : x = (affineBlock hq p)[q - 1]'(by omega) := by
          have h2 : (affineBlock hq p ++ ps.flatMap (affineBlock hq))[s.length]'hw₀ =
              (affineBlock hq p)[s.length]'(by omega) :=
            List.getElem_append_left (by omega)
          have hidx : (affineBlock hq p)[s.length]'(by omega) =
              (affineBlock hq p)[q - 1]'(by omega) := by congr 1; omega
          rw [← hwx, h2, hidx]
        cases ps with
        | nil =>
          simp only [List.flatMap_nil, List.append_nil, hlen_p] at hw₁
          omega
        | cons p₂ ps' =>
          have hy_eq : y = (affineBlock hq p₂)[0]'(by rw [length_affineBlock]; exact hq) := by
            rw [← hwy, List.getElem_append_right (by omega)]
            have hsub : s.length + 1 - (affineBlock hq p).length = 0 := by omega
            simp only [hsub, List.flatMap_cons]
            exact List.getElem_append_left (by rw [length_affineBlock]; exact hq)
          rw [hx_eq, hy_eq, getElem_affineBlock hq p (by omega), getElem_affineBlock hq p₂ hq]
          dsimp
          have hadd : q - 1 + 1 = q := by omega
          rw [hadd, Nat.mod_self]
      · have hge : q ≤ s.length := by omega
        have hs_split : affineBlock hq p <+: s := by
          have hp_pref : affineBlock hq p <+: s ++ ([x, y] ++ t) := by
            refine ⟨ps.flatMap (affineBlock hq), ?_⟩
            simpa [List.append_assoc] using hst.symm
          have htake : (s ++ ([x, y] ++ t)).take q = affineBlock hq p := by
            rcases hp_pref with ⟨r, hr⟩
            rw [← hr, List.take_left' hlen_p]
          rw [List.take_append_of_le_length hge] at htake
          exact ⟨s.drop q, by rw [← htake, List.take_append_drop]⟩
        rcases hs_split with ⟨s', rfl⟩
        apply ih
        refine ⟨s', t, ?_⟩
        have hst' : affineBlock hq p ++ (s' ++ [x, y] ++ t) =
            affineBlock hq p ++ ps.flatMap (affineBlock hq) := by
          simpa [List.append_assoc] using hst
        exact List.append_cancel_left hst'

private theorem exists_mem_range_not_mem :
    ∀ (m : ℕ) (bad : List ℕ), bad.length < m → ∃ j < m, j ∉ bad
  | 0, _, h => by omega
  | m + 1, bad, h => by
    by_cases hmem : m ∈ bad
    · have hlen_er : (bad.erase m).length < m := by
        have := List.length_erase_of_mem hmem
        have := List.length_pos_of_mem hmem
        omega
      obtain ⟨j, hjm, hj_er⟩ := exists_mem_range_not_mem m (bad.erase m) hlen_er
      refine ⟨j, by omega, fun hjb ↦ hj_er ?_⟩
      exact (List.mem_erase_of_ne (by omega)).mpr hjb
    · exact ⟨m, by omega, hmem⟩

private def rainbowPad (r : ℕ) (Z : List ℕ) : List ℕ :=
  List.range r ++ Z.flatMap (fun m ↦ [m + r] ++ List.range r)

private theorem pair_in_rainbowPad_succ {r : ℕ} (hr : 0 < r) (Z : List ℕ) {x y : ℕ}
    (hxy : [x, y] <:+: rainbowPad (r + 1) Z) :
    (x = 0 → y = 1) ∧ (y = 1 → x = 0) := by
  have hrange_pair : ∀ {s : ℕ} {a b : ℕ}, [a, b] <:+: List.range s → b = a + 1 := by
    intro s a b ⟨l₁, l₂, h⟩
    obtain ⟨h₀, h₁, ha, hb⟩ := infix_pair_getElem h
    simp only [List.getElem_range] at ha hb
    omega
  have haux : ∀ (L : List ℕ),
      [x, y] <:+: List.range (r + 1) ++ L.flatMap (fun m ↦ [m + (r + 1)] ++ List.range (r + 1)) →
      (x = 0 → y = 1) ∧ (y = 1 → x = 0) := by
    intro L
    induction L with
    | nil =>
      intro h
      simp only [List.flatMap_nil, List.append_nil] at h
      have hb := hrange_pair h
      omega
    | cons m ms ih =>
      intro h
      simp only [List.flatMap_cons] at h
      let U := List.range (r + 1)
      let V := ms.flatMap (fun m' ↦ [m' + (r + 1)] ++ List.range (r + 1))
      have hU_len : U.length = r + 1 := List.length_range
      have heq_cat : U ++ ([m + (r + 1)] ++ U ++ V) = (U ++ [m + (r + 1)]) ++ (U ++ V) := by
        simp [List.append_assoc]
      change [x, y] <:+: U ++ ([m + (r + 1)] ++ U ++ V) at h
      rw [heq_cat] at h
      rcases h with ⟨s, t, hst⟩
      obtain ⟨hw₀, hw₁, hwx, hwy⟩ := infix_pair_getElem hst
      by_cases hs_lt : s.length < r + 1
      · by_cases hs_lt2 : s.length + 1 < r + 1
        · have hx : x = s.length := by
            rw [← hwx, List.getElem_append_left (by simp [hU_len]; omega),
              List.getElem_append_left (by omega)]
            simp [U]
          have hy : y = s.length + 1 := by
            rw [← hwy, List.getElem_append_left (by simp [hU_len]; omega),
              List.getElem_append_left (by omega)]
            simp [U]
          omega
        · have hs_eq : s.length = r := by omega
          have hx : x = r := by
            rw [← hwx, List.getElem_append_left (by simp [hU_len]; omega),
              List.getElem_append_left (by omega)]
            simp [U, hs_eq]
          have hy : y = m + (r + 1) := by
            rw [← hwy, List.getElem_append_left (by simp [hU_len]; omega),
              List.getElem_append_right (by omega)]
            have hsub : s.length + 1 - U.length = 0 := by omega
            simp [hsub]
          omega
      · by_cases hs_eq : s.length = r + 1
        · have hx : x = m + (r + 1) := by
            rw [← hwx, List.getElem_append_left (by simp [hU_len]; omega),
              List.getElem_append_right (by omega)]
            have hsub : s.length - U.length = 0 := by omega
            simp [hsub]
          have hy : y = 0 := by
            rw [← hwy, List.getElem_append_right (by simp [hU_len]; omega)]
            have hsub : s.length + 1 - (U ++ [m + (r + 1)]).length = 0 := by
              simp [hU_len]; omega
            simp only [hsub]
            rw [List.getElem_append_left (by omega)]
            simp [U]
          omega
        · let k := (U ++ [m + (r + 1)]).length
          have hge : k ≤ s.length := by simp [k, hU_len]; omega
          have hpref : U ++ [m + (r + 1)] <+: s := by
            have htake : (s ++ ([x, y] ++ t)).take k = U ++ [m + (r + 1)] := by
              have hcat : s ++ ([x, y] ++ t) = (U ++ [m + (r + 1)]) ++ (U ++ V) := by
                simpa [List.append_assoc] using hst
              rw [hcat]
              exact List.take_left
            rw [List.take_append_of_le_length hge] at htake
            exact ⟨s.drop k, by rw [← htake, List.take_append_drop]⟩
          rcases hpref with ⟨s', rfl⟩
          apply ih
          refine ⟨s', t, ?_⟩
          have hst' : (U ++ [m + (r + 1)]) ++ (s' ++ [x, y] ++ t) =
              (U ++ [m + (r + 1)]) ++ (U ++ V) := by
            simpa [List.append_assoc] using hst
          exact List.append_cancel_left hst'
  exact haux Z hxy

private theorem reflects_ziminWord_rainbowPad (r k : ℕ) :
    Reflects (ziminWord (k + r)) (rainbowPad r (ziminWord k)) := by
  induction r with
  | zero =>
    have heq : rainbowPad 0 (ziminWord k) = ziminWord k := by
      simp [rainbowPad]
    rw [Nat.add_zero, heq]
    exact Reflects.refl _
  | succ r ih =>
    by_cases hr0 : r = 0
    · subst hr0
      have heq : rainbowPad 1 (ziminWord k) = ziminWord (k + 1) := by
        rw [ziminWord_succ_eq_flatMap]
        dsimp [rainbowPad]
        induction ziminWord k with
        | nil => rfl
        | cons m ms ihz =>
          simp only [List.flatMap_cons, List.cons_append, List.nil_append] at ihz ⊢
          rw [← ihz]
      rw [heq]
      exact Reflects.refl _
    · have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
      let W := rainbowPad (r + 1) (ziminWord k)
      have h0_free : IsFreeSet W ({0} : Set ℕ) := by
        rw [isFreeSet_iff]
        intro x hx y hy hchain
        simp only [Set.mem_singleton_iff] at hx hy
        subst hx hy
        rcases hasAlternatingChain_iff_reflTransGen.mp hchain with ⟨b, h0b, hb0⟩
        have hb_all : ∀ u : ℕ, Relation.ReflTransGen (SameRightNeighbor W) 0 u → u = 0 := by
          intro u hu
          induction hu with
          | refl => rfl
          | @tail u₁ u₂ _ hstep ihb =>
            subst ihb
            rcases sameRightNeighbor_iff.mp hstep with ⟨c, h0c, huc⟩
            have hc1 := (pair_in_rainbowPad_succ hr_pos (ziminWord k) h0c).1 rfl
            exact (pair_in_rainbowPad_succ hr_pos (ziminWord k) huc).2 hc1
        have hb_eq : b = 0 := hb_all b h0b
        subst hb_eq
        have h01 := (pair_in_rainbowPad_succ hr_pos (ziminWord k) hb0).1 rfl
        omega
      have hdel_eq : deleteLetters ({0} : Set ℕ) W = (rainbowPad r (ziminWord k)).map (· + 1) := by
        have hdel_range : deleteLetters ({0} : Set ℕ) (List.range (r + 1)) =
            (List.range r).map (· + 1) := by
          rw [List.range_succ_eq_map, deleteLetters_cons_of_mem (Set.mem_singleton 0)]
          have hno0 : ∀ a ∈ (List.range r).map Nat.succ, a ∉ ({0} : Set ℕ) := by
            intro a ha
            rcases List.mem_map.mp ha with ⟨_, _, rfl⟩
            simp
          exact deleteLetters_eq_self hno0
        dsimp [W, rainbowPad]
        rw [deleteLetters_append, hdel_range, List.map_append]
        congr 1
        induction ziminWord k with
        | nil => simp
        | cons m ms ihz =>
          simp only [List.flatMap_cons, List.cons_append]
          have hm_ne : m + (r + 1) ∉ ({0} : Set ℕ) := by simp
          rw [deleteLetters_cons_of_not_mem hm_ne, deleteLetters_append, hdel_range, ihz]
          simp [Nat.add_assoc]
      have href_map : Reflects (ziminWord (k + r)) ((rainbowPad r (ziminWord k)).map (· + 1)) :=
        (Reflects.of_injective_map (fun _ _ h ↦ Nat.succ.inj h) _).trans ih
      rw [← hdel_eq] at href_map
      have hsucc := h0_free.reflects_ziminWord_succ href_map
      simpa [Nat.add_assoc] using hsucc

private theorem range_split_slice {a b : ℕ} (hab : a ≤ b) :
    List.range a ++ (List.range (b - a)).map (a + ·) = List.range b := by
  have heq : b = a + (b - a) := by omega
  conv_rhs => rw [heq, List.range_add]

private theorem reflects_flatMap_affineBlock_imp {q : ℕ} (hq2 : 2 ≤ q)
    (W : List (Fin q × Fin q)) {β : List A} (hβ_len : β.length + 2 ≤ q)
    (href : Reflects (W.flatMap (affineBlock (by omega : 0 < q))) β)
    (hIH : ∀ γ : List A, γ.length ≤ β.length → Reflects W γ → ∃ k, Reflects (ziminWord k) γ) :
    ∃ k : ℕ, Reflects (ziminWord k) β := by
  classical
  have hq : 0 < q := by omega
  by_cases hβ0 : β = []
  · subst hβ0; exact ⟨0, reflects_nil _⟩
  rcases reflects_iff.mp href with ⟨φ, hφ, hinf⟩
  let badSlots : List ℕ := β.attach.map fun ⟨z, hz⟩ ↦ ((φ z).getLast (hφ z hz)).1.1
  have hbad_lt : badSlots.length < q - 1 := by simp [badSlots]; omega
  obtain ⟨j₀, hj₀_lt, hj₀_not_mem⟩ := exists_mem_range_not_mem (q - 1) badSlots hbad_lt
  have hj₀ : j₀ + 1 < q := by omega
  have hlast_ne : ∀ z ∈ β, ∀ hz : φ z ≠ [], ((φ z).getLast hz).1.1 ≠ j₀ := by
    intro z hz _ heq
    apply hj₀_not_mem
    simp only [badSlots, List.mem_map, List.mem_attach, true_and, Subtype.exists]
    exact ⟨z, hz, heq⟩
  let X : Set A := {z : A | extractBlocks hq j₀ (φ z) = []}
  have hext_flat : extractBlocks hq j₀ (β.flatMap φ) =
      (deleteLetters X β).flatMap (fun z ↦ extractBlocks hq j₀ (φ z)) := by
    have haux : ∀ l : List A, (∀ z ∈ l, z ∈ β) →
        extractBlocks hq j₀ (l.flatMap φ) =
          (deleteLetters X l).flatMap (fun z ↦ extractBlocks hq j₀ (φ z)) := by
      intro l hl
      induction l with
      | nil => simp [extractBlocks]
      | cons z zs ihl =>
        have hzw : z ∈ β := hl z (by simp)
        rw [List.flatMap_cons,
          extractBlocks_append_of_getLast_ne hq j₀ (φ z) (zs.flatMap φ)
            (fun h ↦ hlast_ne z hzw h),
          ihl (fun u hu ↦ hl u (by simp [hu]))]
        by_cases hzX : z ∈ X
        · rw [deleteLetters_cons_of_mem hzX]
          have hemp : extractBlocks hq j₀ (φ z) = [] := hzX
          simp [hemp]
        · rw [deleteLetters_cons_of_not_mem hzX]
          simp [List.flatMap_cons]
    exact haux β (fun _ hz ↦ hz)
  have hflat_last_ne : ∀ h : β.flatMap φ ≠ [], ((β.flatMap φ).getLast h).1.1 ≠ j₀ := by
    intro h
    have hlast_β : β.getLast hβ0 ∈ β := List.getLast_mem hβ0
    have hdrop : β.dropLast ++ [β.getLast hβ0] = β := List.dropLast_append_getLast hβ0
    have hflat_split : β.flatMap φ =
        β.dropLast.flatMap φ ++ φ (β.getLast hβ0) := by
      conv_lhs => rw [← hdrop, List.flatMap_append]
      simp
    have hne_last := hφ (β.getLast hβ0) hlast_β
    have hget : (β.flatMap φ).getLast h = (φ (β.getLast hβ0)).getLast hne_last := by
      have h1 : (β.dropLast.flatMap φ ++ φ (β.getLast hβ0)).getLast
          (by rw [← hflat_split]; exact h) =
          (φ (β.getLast hβ0)).getLast hne_last :=
        List.getLast_append_of_ne_nil _ hne_last
      simpa [hflat_split] using h1
    rw [hget]
    exact hlast_ne (β.getLast hβ0) hlast_β hne_last
  have hext_infix : extractBlocks hq j₀ (β.flatMap φ) <:+: W := by
    rw [← extractBlocks_flatMap_affineBlock hq hj₀ W]
    rcases hinf with ⟨pre, suf, hps⟩
    rw [← hps]
    by_cases hpre_empty : pre = []
    · subst hpre_empty
      simp only [List.nil_append]
      rw [extractBlocks_append_of_getLast_ne hq j₀ (β.flatMap φ) suf hflat_last_ne]
      exact ⟨[], extractBlocks hq j₀ suf, by simp⟩
    · by_cases hpre_last : (pre.getLast hpre_empty).1.1 = j₀
      · let pre' := pre.dropLast
        let c := pre.getLast hpre_empty
        have hpre_eq : pre' ++ [c] = pre := List.dropLast_append_getLast hpre_empty
        have hpre'_ne_j₀ : ∀ hp : pre' ≠ [], (pre'.getLast hp).1.1 ≠ j₀ := by
          intro hp heq
          let b := pre'.getLast hp
          have hbc : [b, c] <:+: W.flatMap (affineBlock hq) := by
            have hb_split : pre'.dropLast ++ [b] = pre' := List.dropLast_append_getLast hp
            refine ⟨pre'.dropLast, β.flatMap φ ++ suf, ?_⟩
            calc
              pre'.dropLast ++ [b, c] ++ (β.flatMap φ ++ suf)
                  = ((pre'.dropLast ++ [b]) ++ [c]) ++ β.flatMap φ ++ suf := by
                    simp [List.append_assoc]
              _ = pre ++ β.flatMap φ ++ suf := by rw [hb_split, hpre_eq]
              _ = W.flatMap (affineBlock hq) := hps
          have hcyc := cyclic_pair_in_flatMap_affineBlock hq W hbc
          rw [heq, hpre_last, Nat.mod_eq_of_lt hj₀] at hcyc
          omega
        have hcat : pre ++ β.flatMap φ ++ suf = pre' ++ (c :: (β.flatMap φ ++ suf)) := by
          rw [← hpre_eq]
          simp [List.append_assoc]
        rw [hcat, extractBlocks_append_of_getLast_ne hq j₀ pre' _ hpre'_ne_j₀]
        have hflat_ne : β.flatMap φ ≠ [] := by
          obtain ⟨z₀, hz₀⟩ := List.exists_mem_of_ne_nil β hβ0
          obtain ⟨w₀, hw₀⟩ := List.exists_mem_of_ne_nil (φ z₀) (hφ z₀ hz₀)
          exact List.ne_nil_of_mem (List.mem_flatMap.mpr ⟨z₀, hz₀, hw₀⟩)
        match h_eq : β.flatMap φ with
        | [] => exact absurd h_eq hflat_ne
        | d :: ds =>
          have hflat_last_ne' : ∀ h : (d :: ds) ≠ [], ((d :: ds).getLast h).1.1 ≠ j₀ := by
            simpa [h_eq] using hflat_last_ne
          have hc_j₀ : c.1.1 = j₀ := hpre_last
          simp only [List.cons_append, extractBlocks, hc_j₀, ↓reduceIte]
          rw [← List.cons_append,
            extractBlocks_append_of_getLast_ne hq j₀ (d :: ds) suf hflat_last_ne']
          refine ⟨extractBlocks hq j₀ pre' ++ [recoverPair hq j₀ c.2 d.2], extractBlocks hq j₀ suf,
            ?_⟩
          simp [List.append_assoc]
      · rw [List.append_assoc,
          extractBlocks_append_of_getLast_ne hq j₀ pre (β.flatMap φ ++ suf)
            (fun _ ↦ hpre_last),
          extractBlocks_append_of_getLast_ne hq j₀ (β.flatMap φ) suf hflat_last_ne]
        exact ⟨extractBlocks hq j₀ pre, extractBlocks hq j₀ suf, by simp [List.append_assoc]⟩
  have href_W : Reflects W (deleteLetters X β) := by
    refine reflects_iff.mpr ⟨fun z ↦ extractBlocks hq j₀ (φ z), ?_, ?_⟩
    · intro z hz
      exact (mem_deleteLetters.mp hz).2
    · rwa [← hext_flat]
  obtain ⟨k₀, hk₀⟩ := hIH (deleteLetters X β) (length_deleteLetters_le X β) href_W
  rcases reflects_iff.mp hk₀ with ⟨θ, hθ, hθ_inf⟩
  let pos : Fin q → ℕ := fun j ↦ (j.1 + q - (j₀ + 1)) % q
  have hpos_lt : ∀ j : Fin q, pos j < q := fun _ ↦ Nat.mod_lt _ hq
  have hpos_eq_top : ∀ j : Fin q, pos j = q - 1 ↔ j.1 = j₀ := by
    intro j
    have hj_lt : j.1 < q := j.2
    dsimp [pos]
    by_cases hle : j₀ + 1 ≤ j.1
    · have hsub : j.1 + q - (j₀ + 1) = q + (j.1 - (j₀ + 1)) := by omega
      rw [hsub, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hlt_mod : j.1 + q - (j₀ + 1) < q := by omega
      rw [Nat.mod_eq_of_lt hlt_mod]
      omega
  have hpos_step : ∀ x y : Fin q × Fin q, [x, y] <:+: W.flatMap (affineBlock hq) →
      (x.1.1 ≠ j₀ → pos y.1 = pos x.1 + 1) := by
    intro x y hxy hne
    have hcyc := cyclic_pair_in_flatMap_affineBlock hq W hxy
    have hx_lt : pos x.1 < q - 1 := by
      have := hpos_lt x.1
      have hne' := mt (hpos_eq_top x.1).mp hne
      omega
    dsimp [pos] at hx_lt ⊢
    by_cases hx_q1 : x.1.1 + 1 = q
    · have hy0 : y.1.1 = 0 := by rw [hcyc, hx_q1, Nat.mod_self]
      rw [hy0]
      have h1 : (x.1.1 + q - (j₀ + 1)) % q = x.1.1 - (j₀ + 1) := by
        have hsub : x.1.1 + q - (j₀ + 1) = q + (x.1.1 - (j₀ + 1)) := by omega
        rw [hsub, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      have h2 : (0 + q - (j₀ + 1)) % q = q - (j₀ + 1) := by
        simp only [Nat.zero_add]
        exact Nat.mod_eq_of_lt (by omega)
      rw [h1, h2]
      omega
    · have hy_succ : y.1.1 = x.1.1 + 1 := by rw [hcyc, Nat.mod_eq_of_lt (by omega)]
      rw [hy_succ]
      by_cases hle : j₀ + 1 ≤ x.1.1
      · have h1 : (x.1.1 + q - (j₀ + 1)) % q = x.1.1 - (j₀ + 1) := by
          have hsub : x.1.1 + q - (j₀ + 1) = q + (x.1.1 - (j₀ + 1)) := by omega
          rw [hsub, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        have h2 : (x.1.1 + 1 + q - (j₀ + 1)) % q = x.1.1 + 1 - (j₀ + 1) := by
          have hsub : x.1.1 + 1 + q - (j₀ + 1) = q + (x.1.1 + 1 - (j₀ + 1)) := by omega
          rw [hsub, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        rw [h1, h2]
        omega
      · have h1 : (x.1.1 + q - (j₀ + 1)) % q = x.1.1 + q - (j₀ + 1) := Nat.mod_eq_of_lt (by omega)
        by_cases heq_j : x.1.1 + 1 = j₀ + 1
        · omega
        · have h2 : (x.1.1 + 1 + q - (j₀ + 1)) % q = x.1.1 + 1 + q - (j₀ + 1) :=
            Nat.mod_eq_of_lt (by omega)
          rw [h1, h2]
          omega
  have hX_le : ∀ (z : A) (hzw : z ∈ β), z ∈ X →
      pos ((φ z).head (hφ z hzw)).1 ≤ pos ((φ z).getLast (hφ z hzw)).1 := by
    intro z hzw hzX
    have hφ_sub : φ z <:+: W.flatMap (affineBlock hq) := by
      rcases List.append_of_mem hzw with ⟨s₁, s₂, rfl⟩
      have h1 : φ z <:+: (s₁ ++ z :: s₂).flatMap φ :=
        ⟨s₁.flatMap φ, s₂.flatMap φ, by simp [List.append_assoc]⟩
      exact List.IsInfix.trans h1 hinf
    have haux : ∀ (u : List (Fin q × Fin q)) (hu : u ≠ []),
        u <:+: W.flatMap (affineBlock hq) →
        extractBlocks hq j₀ u = [] →
        pos (u.head hu).1 ≤ pos (u.getLast hu).1 := by
      intro u
      induction u with
      | nil => intro hu; exact absurd rfl hu
      | cons c cs ihu =>
        intro hu hsub hext
        cases cs with
        | nil => simp
        | cons d ds =>
          simp only [extractBlocks] at hext
          have hc_ne : c.1.1 ≠ j₀ := by
            intro hc_eq
            simp [hc_eq] at hext
          have hpair : [c, d] <:+: W.flatMap (affineBlock hq) := by
            have h1 : [c, d] <:+: c :: d :: ds := ⟨[], ds, rfl⟩
            exact List.IsInfix.trans h1 hsub
          have hstep := hpos_step c d hpair hc_ne
          have htail_sub : d :: ds <:+: W.flatMap (affineBlock hq) := by
            have h1 : d :: ds <:+: c :: d :: ds := ⟨[c], [], by simp⟩
            exact List.IsInfix.trans h1 hsub
          have hih := ihu (List.cons_ne_nil _ _) htail_sub (by simpa [hc_ne] using hext)
          simp only [List.head_cons] at hih ⊢
          have hgl : (c :: d :: ds).getLast hu = (d :: ds).getLast (List.cons_ne_nil _ _) :=
            List.getLast_cons _
          rw [hgl]
          omega
    exact haux (φ z) (hφ z hzw) hφ_sub hzX
  let R := List.range (q - 1)
  let aFn : A → ℕ := fun z ↦ if hz : z ∈ β then pos ((φ z).head (hφ z hz)).1 else 0
  let bFn : A → ℕ := fun z ↦ if hz : z ∈ β then pos ((φ z).getLast (hφ z hz)).1 else 0
  have ha_le : ∀ z ∈ β, aFn z ≤ q - 1 := by
    intro z hzw
    have := hpos_lt ((φ z).head (hφ z hzw)).1
    simp only [aFn, hzw, ↓reduceDIte]
    omega
  have hb_lt : ∀ z ∈ β, bFn z < q - 1 := by
    intro z hzw
    have hlt := hpos_lt ((φ z).getLast (hφ z hzw)).1
    have hne := mt (hpos_eq_top ((φ z).getLast (hφ z hzw)).1).mp
      (hlast_ne z hzw (hφ z hzw))
    simp only [bFn, hzw, ↓reduceDIte]
    omega
  let θExt : A → List ℕ := fun z ↦ if z ∈ X then [] else θ z
  let ψ : A → List ℕ := fun z ↦
    if _ : z ∈ β then
      if z ∈ X then
        (List.range (bFn z + 1 - aFn z)).map (aFn z + ·)
      else
        match θ z with
        | [] => [0]
        | m₀ :: ms =>
          (List.range (q - 1 - aFn z)).map (aFn z + ·) ++ [m₀ + (q - 1)] ++
            ms.flatMap (fun m ↦ R ++ [m + (q - 1)]) ++ List.range (bFn z + 1)
    else [0]
  have hψ_ne : ∀ z ∈ β, ψ z ≠ [] := by
    intro z hzw
    by_cases hzX : z ∈ X
    · have hab : aFn z ≤ bFn z := by
        simpa [aFn, bFn, hzw] using hX_le z hzw hzX
      have hpos_len : 0 < (ψ z).length := by
        simp only [ψ, hzw, hzX, ↓reduceDIte, ↓reduceIte, List.length_map, List.length_range]
        omega
      exact List.length_pos_iff.mp hpos_len
    · have hmem : z ∈ deleteLetters X β := mem_deleteLetters.mpr ⟨hzw, hzX⟩
      have hθz := hθ z hmem
      match h_eq : θ z with
      | [] => exact absurd h_eq hθz
      | m₀ :: ms =>
        simp only [ψ, hzw, hzX, ↓reduceDIte, ↓reduceIte, h_eq]
        intro hemp
        simp only [List.append_eq_nil_iff] at hemp
        exact List.cons_ne_nil _ _ hemp.1.1.2
  have hletter : ∀ z ∈ β,
      List.range (aFn z) ++ ψ z =
        (θExt z).flatMap (fun m ↦ R ++ [m + (q - 1)]) ++ List.range (bFn z + 1) := by
    intro z hzw
    by_cases hzX : z ∈ X
    · have hab : aFn z ≤ bFn z := by
        simpa [aFn, bFn, hzw] using hX_le z hzw hzX
      simp only [ψ, θExt, hzw, hzX, ↓reduceDIte, ↓reduceIte, List.flatMap_nil, List.nil_append]
      exact range_split_slice (by omega)
    · have hmem : z ∈ deleteLetters X β := mem_deleteLetters.mpr ⟨hzw, hzX⟩
      have hθz := hθ z hmem
      match h_eq : θ z with
      | [] => exact absurd h_eq hθz
      | m₀ :: ms =>
        simp only [ψ, θExt, hzw, hzX, ↓reduceDIte, ↓reduceIte, h_eq, List.flatMap_cons]
        have hR : List.range (aFn z) ++ (List.range (q - 1 - aFn z)).map (aFn z + ·) = R :=
          range_split_slice (ha_le z hzw)
        calc
          List.range (aFn z) ++ ((List.range (q - 1 - aFn z)).map (aFn z + ·) ++ [m₀ + (q - 1)] ++
              ms.flatMap (fun m ↦ R ++ [m + (q - 1)]) ++ List.range (bFn z + 1))
              = (List.range (aFn z) ++ (List.range (q - 1 - aFn z)).map (aFn z + ·)) ++
                  [m₀ + (q - 1)] ++ ms.flatMap (fun m ↦ R ++ [m + (q - 1)]) ++
                  List.range (bFn z + 1) := by simp [List.append_assoc]
          _ = (R ++ [m₀ + (q - 1)] ++ ms.flatMap (fun m ↦ R ++ [m + (q - 1)])) ++
                List.range (bFn z + 1) := by rw [hR]
  have hadj : ∀ y z : A, [y, z] <:+: β →
      List.range (bFn y + 1) = List.range (aFn z) := by
    intro y z hyz
    have hyw : y ∈ β := hyz.subset (by simp)
    have hzw : z ∈ β := hyz.subset (by simp)
    have hy_ne := hφ y hyw
    have hz_ne := hφ z hzw
    have hpair_W : [(φ y).getLast hy_ne, (φ z).head hz_ne] <:+: W.flatMap (affineBlock hq) := by
      have h1 : φ y ++ φ z <:+: β.flatMap φ := by
        simpa [List.flatMap_cons, List.flatMap_nil] using isInfix_flatMap hyz φ
      have h2 : [(φ y).getLast hy_ne, (φ z).head hz_ne] <:+: φ y ++ φ z := by
        have hy_sp : (φ y).dropLast ++ [(φ y).getLast hy_ne] = φ y :=
          List.dropLast_append_getLast hy_ne
        have hz_sp : (φ z).head hz_ne :: (φ z).tail = φ z := List.cons_head_tail hz_ne
        refine ⟨(φ y).dropLast, (φ z).tail, ?_⟩
        calc
          (φ y).dropLast ++ [(φ y).getLast hy_ne, (φ z).head hz_ne] ++ (φ z).tail
              = ((φ y).dropLast ++ [(φ y).getLast hy_ne]) ++ ((φ z).head hz_ne :: (φ z).tail) := by
                simp [List.append_assoc]
          _ = φ y ++ φ z := by rw [hy_sp, hz_sp]
      exact (h2.trans h1).trans hinf
    have hstep := hpos_step _ _ hpair_W (hlast_ne y hyw hy_ne)
    simp only [bFn, aFn, hyw, hzw, ↓reduceDIte]
    rw [hstep]
  have htel := flatMap_telescoping β hβ0
    (δR := fun z ↦ List.range (aFn z))
    (δL := fun z ↦ List.range (bFn z + 1))
    (ψ := ψ)
    (φ₀ := fun z ↦ (θExt z).flatMap (fun m ↦ R ++ [m + (q - 1)]))
    hletter hadj
  have hflat_θ : β.flatMap (fun z ↦ (θExt z).flatMap (fun m ↦ R ++ [m + (q - 1)])) =
      ((deleteLetters X β).flatMap θ).flatMap (fun m ↦ R ++ [m + (q - 1)]) := by
    rw [← flatMap_flatMap]
    have hinner : ∀ l : List A, l.flatMap θExt = (deleteLetters X l).flatMap θ := by
      intro l
      induction l with
      | nil => simp
      | cons z zs ihz =>
        by_cases hzX : z ∈ X
        · rw [deleteLetters_cons_of_mem hzX, List.flatMap_cons, ihz]
          simp [θExt, hzX]
        · rw [deleteLetters_cons_of_not_mem hzX, List.flatMap_cons, List.flatMap_cons, ihz]
          simp [θExt, hzX]
    rw [hinner β]
  rw [hflat_θ] at htel
  have href_rainbow : Reflects (rainbowPad (q - 1) (ziminWord k₀)) β := by
    refine reflects_iff.mpr ⟨ψ, hψ_ne, ?_⟩
    rcases hθ_inf with ⟨l₁, l₂, hlZ⟩
    have hrainbow_split : rainbowPad (q - 1) (ziminWord k₀) =
        l₁.flatMap (fun m ↦ R ++ [m + (q - 1)]) ++
          (((deleteLetters X β).flatMap θ).flatMap (fun m ↦ R ++ [m + (q - 1)]) ++ R) ++
          l₂.flatMap (fun m ↦ [m + (q - 1)] ++ R) := by
      dsimp [rainbowPad, R]
      rw [← hlZ]
      have hcomm : ∀ L : List ℕ,
          List.range (q - 1) ++ L.flatMap (fun m ↦ [m + (q - 1)] ++ List.range (q - 1)) =
            L.flatMap (fun m ↦ List.range (q - 1) ++ [m + (q - 1)]) ++ List.range (q - 1) := by
        intro L
        induction L with
        | nil => simp
        | cons m ms ihl =>
          simp only [List.flatMap_cons]
          calc
            List.range (q - 1) ++ ([m + (q - 1)] ++ List.range (q - 1) ++
                ms.flatMap (fun m' ↦ [m' + (q - 1)] ++ List.range (q - 1)))
                = (List.range (q - 1) ++ [m + (q - 1)]) ++
                    (List.range (q - 1) ++
                      ms.flatMap (fun m' ↦ [m' + (q - 1)] ++ List.range (q - 1))) := by
                  simp [List.append_assoc]
            _ = (List.range (q - 1) ++ [m + (q - 1)]) ++
                  (ms.flatMap (fun m' ↦ List.range (q - 1) ++ [m' + (q - 1)]) ++
                    List.range (q - 1)) := by rw [ihl]
            _ = (List.range (q - 1) ++ [m + (q - 1)] ++
                  ms.flatMap (fun m' ↦ List.range (q - 1) ++ [m' + (q - 1)])) ++
                  List.range (q - 1) := by simp [List.append_assoc]
      simp only [List.flatMap_append]
      calc
        List.range (q - 1) ++ (l₁.flatMap (fun m ↦ [m + (q - 1)] ++ List.range (q - 1)) ++
            ((deleteLetters X β).flatMap θ).flatMap
              (fun m ↦ [m + (q - 1)] ++ List.range (q - 1)) ++
            l₂.flatMap (fun m ↦ [m + (q - 1)] ++ List.range (q - 1)))
            = (List.range (q - 1) ++
                (l₁ ++ (deleteLetters X β).flatMap θ).flatMap
                  (fun m ↦ [m + (q - 1)] ++ List.range (q - 1))) ++
                l₂.flatMap (fun m ↦ [m + (q - 1)] ++ List.range (q - 1)) := by
              simp [List.flatMap_append, List.append_assoc]
        _ = ((l₁ ++ (deleteLetters X β).flatMap θ).flatMap
              (fun m ↦ List.range (q - 1) ++ [m + (q - 1)]) ++ List.range (q - 1)) ++
              l₂.flatMap (fun m ↦ [m + (q - 1)] ++ List.range (q - 1)) := by rw [hcomm]
        _ = _ := by simp [List.flatMap_append, List.append_assoc]
    have hb_last_le : bFn (β.getLast hβ0) + 1 ≤ q - 1 :=
      hb_lt (β.getLast hβ0) (List.getLast_mem hβ0)
    let sufR := (List.range (q - 1 - (bFn (β.getLast hβ0) + 1))).map
      (bFn (β.getLast hβ0) + 1 + ·)
    have hR_last : List.range (bFn (β.getLast hβ0) + 1) ++ sufR = R :=
      range_split_slice hb_last_le
    refine ⟨l₁.flatMap (fun m ↦ R ++ [m + (q - 1)]) ++ List.range (aFn (β.head hβ0)),
      sufR ++ l₂.flatMap (fun m ↦ [m + (q - 1)] ++ R), ?_⟩
    rw [hrainbow_split]
    calc
      (l₁.flatMap (fun m ↦ R ++ [m + (q - 1)]) ++ List.range (aFn (β.head hβ0))) ++ β.flatMap ψ ++
          (sufR ++ l₂.flatMap (fun m ↦ [m + (q - 1)] ++ R))
          = l₁.flatMap (fun m ↦ R ++ [m + (q - 1)]) ++
              (List.range (aFn (β.head hβ0)) ++ β.flatMap ψ) ++
              (sufR ++ l₂.flatMap (fun m ↦ [m + (q - 1)] ++ R)) := by simp [List.append_assoc]
      _ = l₁.flatMap (fun m ↦ R ++ [m + (q - 1)]) ++
            (((deleteLetters X β).flatMap θ).flatMap (fun m ↦ R ++ [m + (q - 1)]) ++
              (List.range (bFn (β.getLast hβ0) + 1) ++ sufR)) ++
            l₂.flatMap (fun m ↦ [m + (q - 1)] ++ R) := by
          rw [htel]; simp [List.append_assoc]
      _ = _ := by rw [hR_last]
  exact ⟨k₀ + (q - 1), href_rainbow.trans (reflects_ziminWord_rainbowPad (q - 1) k₀)⟩

private def affineWord {q : ℕ} (hq : 0 < q) : ℕ → List (Fin q × Fin q)
  | 0 => [(⟨0, hq⟩, ⟨0, hq⟩)]
  | m + 1 => (affineWord hq m).flatMap (affineBlock hq)

private theorem length_affineWord {q : ℕ} (hq : 0 < q) (m : ℕ) :
    (affineWord hq m).length = q ^ m := by
  induction m with
  | zero => simp [affineWord]
  | succ m ih =>
    have hflat : ∀ L : List (Fin q × Fin q),
        (L.flatMap (affineBlock hq)).length = q * L.length := by
      intro L
      induction L with
      | nil => simp
      | cons p ps ihL =>
        simp [List.flatMap_cons, length_affineBlock, ihL, Nat.mul_add, Nat.add_comm]
    rw [affineWord, hflat, ih, Nat.pow_succ, Nat.mul_comm]

/-- Every unavoidable pattern is reflected by some canonical Zimin word `ziminWord k`. -/
theorem IsUnavoidable.exists_reflects_ziminWord {w : List A} (hw : IsUnavoidable w) :
    ∃ k : ℕ, Reflects (ziminWord k) w := by
  let q := w.length + 2
  have hq2 : 2 ≤ q := by omega
  have hq : 0 < q := by omega
  obtain ⟨N, hN⟩ := hw.exists_length_forall_reflects (B := Fin q × Fin q)
  have hpow : N ≤ q ^ N := Nat.le_of_lt (Nat.lt_pow_self (by omega : 1 < q))
  have href_N : Reflects (affineWord hq N) w := hN _ (by rw [length_affineWord]; exact hpow)
  have hind : ∀ (m : ℕ) (β : List A), β.length ≤ w.length →
      Reflects (affineWord hq m) β → ∃ k : ℕ, Reflects (ziminWord k) β := by
    intro m
    induction m with
    | zero =>
      intro β _ href₀
      have hlen := href₀.length_le
      simp only [affineWord, List.length_singleton] at hlen
      match β with
      | [] => exact ⟨0, reflects_nil _⟩
      | [a] =>
        exact ⟨1, reflects_iff.mpr
          ⟨fun _ ↦ [0], fun _ _ ↦ List.cons_ne_nil _ _, ⟨[], [], by simp [ziminWord_succ]⟩⟩⟩
      | _ :: _ :: _ =>
        simp only [List.length_cons] at hlen
        omega
    | succ m ihm =>
      intro β hβ href_m
      exact reflects_flatMap_affineBlock_imp hq2 (affineWord hq m) (by omega) href_m
        (fun γ hγ ↦ ihm γ (Nat.le_trans hγ hβ))
  exact hind N w (Nat.le_refl _) href_N

/-- **Zimin's Theorem**: a pattern `w : List A` is unavoidable if and only if some
canonical
Zimin word `ziminWord k` reflects `w`.
-/
theorem isUnavoidable_iff_exists_reflects_ziminWord {w : List A} :
    IsUnavoidable w ↔ ∃ k : ℕ, Reflects (ziminWord k) w :=
  ⟨IsUnavoidable.exists_reflects_ziminWord,
    fun ⟨k, hk⟩ ↦ hk.isUnavoidable (isUnavoidable_ziminWord k)⟩

/-- **Zimin–Sapir Theorem**: a pattern `w : List A` is unavoidable if
and only if `w` can be reduced to `` by iteratively deleting free sets.
-/
theorem isUnavoidable_iff_isFreeSetReducible {w : List A} :
    IsUnavoidable w ↔ IsFreeSetReducible w :=
  isUnavoidable_iff_exists_reflects_ziminWord.trans
    isFreeSetReducible_iff_exists_reflects_ziminWord.symm

/-- Deleting a free set reflects unavoidability backwards: if `X` is a free set for `w` and
`deleteLetters X w` is unavoidable, then `w` is unavoidable. -/
theorem IsFreeSet.isUnavoidable_of_deleteLetters {w : List A} {X : Set A} (hX : IsFreeSet w X)
    (hdel : IsUnavoidable (deleteLetters X w)) : IsUnavoidable w :=
  isUnavoidable_iff_isFreeSetReducible.mpr
    (IsFreeSetReducible.delete_freeSet hX (isUnavoidable_iff_isFreeSetReducible.mp hdel))

/-- Deleting a free letter reflects unavoidability backwards: if
`x` is a free letter for `w` and `deleteLetter x w` is unavoidable, then `w` is unavoidable.
-/
theorem IsFreeLetter.isUnavoidable_of_deleteLetter {w : List A} {x : A} (hx : IsFreeLetter w x)
    (hdel : IsUnavoidable (deleteLetter x w)) : IsUnavoidable w := by
  rw [deleteLetter_eq_deleteLetters] at hdel
  exact ((isFreeLetter_iff_singleton_isFreeSet.mp hx).2).isUnavoidable_of_deleteLetters hdel

private theorem isFreeSet_identifyLetters_of_mem {w : List A} {X : Set A} (hX : IsFreeSet w X)
    {x y : A} (hx : x ∈ X) (hy : y ∈ X) :
    IsFreeSet (identifyLetters x y w) X := by
  classical
  let f : A → A := fun a ↦ if a = x then y else a
  have hf_eq : identifyLetters x y w = w.map f := identifyLetters_eq_map x y w
  have hfX : ∀ a : A, f a ∈ X ↔ a ∈ X := by
    intro a
    by_cases hax : a = x
    · subst hax; simp [f, hx, hy]
    · simp [f, hax]
  have hf_id : ∀ a c : A, c ∉ X → f a = c → a = c := by
    intro a c hcX hfac
    by_cases hax : a = x
    · subst hax
      simp only [f, ↓reduceIte] at hfac
      subst hfac
      exact absurd hy hcX
    · simpa [f, hax] using hfac
  have hpair_lift : ∀ u' v' : A, [u', v'] <:+: w.map f →
      ∃ u v : A, f u = u' ∧ f v = v' ∧ [u, v] <:+: w := by
    intro u' v' ⟨s', t', hst⟩
    obtain ⟨hw₀, hw₁, hfu, hfv⟩ := infix_pair_getElem hst
    have hs_le : s'.length + 2 ≤ w.length := by
      simp only [List.length_map] at hw₁
      omega
    let u := w[s'.length]'(by omega)
    let v := w[s'.length + 1]'(by omega)
    have hfu' : f u = u' := by simpa [u] using hfu
    have hfv' : f v = v' := by simpa [v] using hfv
    refine ⟨u, v, hfu', hfv', w.take s'.length, w.drop (s'.length + 2), ?_⟩
    have ht1 : w.take (s'.length + 1) = w.take s'.length ++ [u] :=
      List.take_succ_eq_append_getElem (by omega)
    have ht2 : w.take (s'.length + 2) = w.take (s'.length + 1) ++ [v] :=
      List.take_succ_eq_append_getElem (by omega)
    calc
      w.take s'.length ++ [u, v] ++ w.drop (s'.length + 2)
          = (w.take s'.length ++ [u] ++ [v]) ++ w.drop (s'.length + 2) := by
            simp [List.append_assoc]
      _ = w.take (s'.length + 2) ++ w.drop (s'.length + 2) := by rw [← ht1, ← ht2]
      _ = w := List.take_append_drop (s'.length + 2) w
  rw [hf_eq, isFreeSet_iff]
  intro x₀ hx₀ z_end hz_end hchain
  rcases hasAlternatingChain_iff_reflTransGen.mp hchain with ⟨b', hxb', hb'z⟩
  have hinv : ∀ u' : A, Relation.ReflTransGen (SameRightNeighbor (w.map f)) x₀ u' →
      u' ∈ X ∨ (u' ∉ X ∧ ∃ x₁ ∈ X, Relation.ReflTransGen (SameRightNeighbor w) x₁ u') := by
    intro u' hu'
    induction hu' with
    | refl => exact Or.inl hx₀
    | @tail u₁' u₂' _ hstep ihu =>
      by_cases hu₂X : u₂' ∈ X
      · exact Or.inl hu₂X
      · rcases sameRightNeighbor_iff.mp hstep with ⟨c', hu₁c', hu₂c'⟩
        obtain ⟨u₁, c₁, hfu₁, hfc₁, hu₁c_w⟩ := hpair_lift u₁' c' hu₁c'
        obtain ⟨u₂, c₂, hfu₂, hfc₂, hu₂c_w⟩ := hpair_lift u₂' c' hu₂c'
        by_cases hc'X : c' ∈ X
        · have hc₁X : c₁ ∈ X := (hfX c₁).mp (hfc₁.trans (Eq.refl c') ▸ hc'X)
          rcases ihu with hu₁'X | ⟨hu₁'nX, x₁, hx₁X, hpath⟩
          · have hu₁X : u₁ ∈ X := (hfX u₁).mp (hfu₁ ▸ hu₁'X)
            exact False.elim ((isFreeSet_iff.mp hX) u₁ hu₁X c₁ hc₁X
              (hasAlternatingChain_of_pair_infix hu₁c_w))
          · have hu₁_eq : u₁ = u₁' := hf_id u₁ u₁' hu₁'nX hfu₁
            subst hu₁_eq
            exact absurd (hasAlternatingChain_iff_reflTransGen.mpr ⟨u₁, hpath, hu₁c_w⟩)
              ((isFreeSet_iff.mp hX) x₁ hx₁X c₁ hc₁X)
        · have hc₁_eq : c₁ = c' := hf_id c₁ c' hc'X hfc₁
          have hc₂_eq : c₂ = c' := hf_id c₂ c' hc'X hfc₂
          have hu₂_eq : u₂ = u₂' := hf_id u₂ u₂' hu₂X hfu₂
          rw [hc₁_eq] at hu₁c_w
          rw [hc₂_eq, hu₂_eq] at hu₂c_w
          rcases ihu with hu₁'X | ⟨hu₁'nX, x₁, hx₁X, hpath⟩
          · have hu₁X : u₁ ∈ X := (hfX u₁).mp (hfu₁ ▸ hu₁'X)
            exact Or.inr ⟨hu₂X, u₁, hu₁X,
              Relation.ReflTransGen.single (sameRightNeighbor_iff.mpr ⟨c', hu₁c_w, hu₂c_w⟩)⟩
          · have hu₁_eq : u₁ = u₁' := hf_id u₁ u₁' hu₁'nX hfu₁
            rw [hu₁_eq] at hu₁c_w
            exact Or.inr ⟨hu₂X, x₁, hx₁X,
              hpath.tail (sameRightNeighbor_iff.mpr ⟨c', hu₁c_w, hu₂c_w⟩)⟩
  obtain ⟨b₀, z₀, hfb₀, hfz₀, hbz_w⟩ := hpair_lift b' z_end hb'z
  have hz₀X : z₀ ∈ X := (hfX z₀).mp (hfz₀ ▸ hz_end)
  rcases hinv b' hxb' with hb'X | ⟨hb'nX, x₁, hx₁X, hpath⟩
  · have hb₀X : b₀ ∈ X := (hfX b₀).mp (hfb₀ ▸ hb'X)
    exact (isFreeSet_iff.mp hX) b₀ hb₀X z₀ hz₀X (hasAlternatingChain_of_pair_infix hbz_w)
  · have hb₀_eq : b₀ = b' := hf_id b₀ b' hb'nX hfb₀
    subst hb₀_eq
    exact (isFreeSet_iff.mp hX) x₁ hx₁X z₀ hz₀X
      (hasAlternatingChain_iff_reflTransGen.mpr ⟨b₀, hpath, hbz_w⟩)

private theorem isBEMReducible_of_freeSet_cover :
    ∀ (L : List A) {w : List A} {X : Set A},
      IsFreeSet w X → (∀ a ∈ w, a ∈ X → a ∈ L) →
      IsBEMReducible (deleteLetters X w) → IsBEMReducible w
  | [], w, X, _, hcov, hred => by
    have heq : deleteLetters X w = w :=
      deleteLetters_eq_self (fun a haw haX ↦ (List.not_mem_nil (hcov a haw haX)).elim)
    rwa [heq] at hred
  | x :: ls, w, X, hX, hcov, hred => by
    classical
    by_cases hxw : x ∈ w ∧ x ∈ X
    · rcases hxw with ⟨hx_in_w, hx_in_X⟩
      by_cases hex : ∃ y ∈ w, y ∈ X ∧ y ≠ x
      · rcases hex with ⟨y, hy_in_w, hy_in_X, hyx⟩
        let w' := identifyLetters x y w
        have hdel_aux : ∀ u : List A, deleteLetters X (identifyLetters x y u) =
            deleteLetters X u := by
          intro u
          induction u with
          | nil => simp
          | cons a as iha =>
            by_cases hax : a = x
            · subst hax
              rw [identifyLetters_cons_eq, deleteLetters_cons_of_mem hy_in_X,
                deleteLetters_cons_of_mem hx_in_X, iha]
            · rw [identifyLetters_cons_ne hax]
              by_cases haX : a ∈ X
              · rw [deleteLetters_cons_of_mem haX, deleteLetters_cons_of_mem haX, iha]
              · rw [deleteLetters_cons_of_not_mem haX, deleteLetters_cons_of_not_mem haX, iha]
        have hdel_eq : deleteLetters X w' = deleteLetters X w := hdel_aux w
        have hcov' : ∀ a ∈ w', a ∈ X → a ∈ ls := by
          intro a haw' haX
          dsimp only [w'] at haw'
          rw [identifyLetters_eq_map] at haw'
          rcases List.mem_map.mp haw' with ⟨b, hbw, rfl⟩
          by_cases hbx : b = x
          · subst hbx
            simp only [↓reduceIte]
            have hyl := hcov y hy_in_w hy_in_X
            rcases List.mem_cons.mp hyl with rfl | hyls
            · exact absurd rfl hyx
            · exact hyls
          · simp only [hbx, ↓reduceIte] at haX ⊢
            have hbl := hcov b hbw haX
            rcases List.mem_cons.mp hbl with rfl | hbls
            · exact absurd rfl hbx
            · exact hbls
        have hX' : IsFreeSet w' X := isFreeSet_identifyLetters_of_mem hX hx_in_X hy_in_X
        rw [← hdel_eq] at hred
        exact IsBEMReducible.identify_letters hx_in_w hy_in_w hyx.symm
          (isBEMReducible_of_freeSet_cover ls hX' hcov' hred)
      · push Not at hex
        have hdel_single : deleteLetters X w = deleteLetter x w := by
          have haux : ∀ u : List A, (∀ a ∈ u, a ∈ w) →
              deleteLetters X u = deleteLetter x u := by
            intro u hu
            induction u with
            | nil => simp
            | cons a as iha =>
              by_cases haX : a ∈ X
              · have hax : a = x := hex a (hu a (by simp)) haX
                subst hax
                rw [deleteLetters_cons_of_mem hx_in_X, deleteLetter_cons_eq,
                  iha (fun b hb ↦ hu b (by simp [hb]))]
              · have hax : a ≠ x := fun h ↦ haX (h ▸ hx_in_X)
                rw [deleteLetters_cons_of_not_mem haX, deleteLetter_cons_ne hax,
                  iha (fun b hb ↦ hu b (by simp [hb]))]
          exact haux w (fun _ ha ↦ ha)
        rw [hdel_single] at hred
        exact IsBEMReducible.delete_freeLetter (hX.isFreeLetter hx_in_X hx_in_w) hred
    · have hcov_ls : ∀ a ∈ w, a ∈ X → a ∈ ls := by
        intro a haw haX
        rcases List.mem_cons.mp (hcov a haw haX) with rfl | hals
        · exact absurd ⟨haw, haX⟩ hxw
        · exact hals
      exact isBEMReducible_of_freeSet_cover ls hX hcov_ls hred

/-- **Bean–Ehrenfeucht–McNulty Theorem**: a pattern `w : List A` is unavoidable if and only
if `w` reduces to `` by iteratively deleting a free letter or identifying two distinct letters
occurring in `w`.
-/
theorem isUnavoidable_iff_isBEMReducible {w : List A} :
    IsUnavoidable w ↔ IsBEMReducible w := by
  constructor
  · intro hw
    have hfs := isUnavoidable_iff_isFreeSetReducible.mp hw
    clear hw
    induction hfs with
    | nil => exact IsBEMReducible.nil
    | @delete_freeSet u X hX _ ih =>
      exact isBEMReducible_of_freeSet_cover u hX (fun a hau _ ↦ hau) ih
  · intro hbem
    induction hbem with
    | nil => exact isUnavoidable_nil
    | delete_freeLetter hx _ ih => exact hx.isUnavoidable_of_deleteLetter ih
    | identify_letters _ _ _ _ ih => exact (reflects_identifyLetters _ _ _).isUnavoidable ih

/-- Every nonempty unavoidable pattern has at least one free letter. -/
theorem IsUnavoidable.exists_isFreeLetter {w : List A} (hw : IsUnavoidable w) (hne : w ≠ []) :
    ∃ x : A, IsFreeLetter w x := by
  have hfs := isUnavoidable_iff_isFreeSetReducible.mp hw
  clear hw
  induction hfs with
  | nil => exact absurd rfl hne
  | @delete_freeSet u X hX _ ih =>
    by_cases hex : ∃ x ∈ u, x ∈ X
    · rcases hex with ⟨x, hxu, hxX⟩
      exact ⟨x, hX.isFreeLetter hxX hxu⟩
    · push Not at hex
      have heq : deleteLetters X u = u := deleteLetters_eq_self hex
      rw [heq] at ih
      exact ih hne

private theorem length_le_two_mul_deleteLetters_succ :
    ∀ (w : List A) {X : Set A}, (∀ x ∈ X, ∀ y ∈ X, ¬ ([x, y] <:+: w)) →
      w.length ≤ 2 * (deleteLetters X w).length + 1
  | [], _, _ => by simp
  | a :: ws, X, hno => by
    by_cases haX : a ∈ X
    · cases ws with
      | nil => simp
      | cons b ws' =>
        have hbX : b ∉ X := fun hb ↦ hno a haX b hb ⟨[], ws', rfl⟩
        rw [deleteLetters_cons_of_mem haX, deleteLetters_cons_of_not_mem hbX]
        have hih := length_le_two_mul_deleteLetters_succ ws' (X := X)
          (fun x hx y hy hxy ↦ hno x hx y hy (hxy.trans ⟨[a, b], [], by simp⟩))
        simp only [List.length_cons]
        omega
    · rw [deleteLetters_cons_of_not_mem haX]
      have hih := length_le_two_mul_deleteLetters_succ ws (X := X)
        (fun x hx y hy hxy ↦ hno x hx y hy (hxy.trans ⟨[a], [], by simp⟩))
      simp only [List.length_cons]
      omega

/-- Every unavoidable pattern `w : List A` whose letters belong to a finite set `s : Finset A` has
length at most `2 ^ s.card - 1`.
-/
theorem IsUnavoidable.length_le_two_pow_card_sub_one {w : List A} (hw : IsUnavoidable w)
    (s : Finset A) (hs : ∀ a ∈ w, a ∈ s) : w.length ≤ 2 ^ s.card - 1 := by
  classical
  have hfs := isUnavoidable_iff_isFreeSetReducible.mp hw
  clear hw
  induction hfs generalizing s with
  | nil => simp
  | @delete_freeSet u X hX _ ih =>
    by_cases hex : ∃ x ∈ u, x ∈ X
    · rcases hex with ⟨x₀, hx₀u, hx₀X⟩
      let s' := s.filter (fun a ↦ ¬ decide (a ∈ X))
      have hs'_sub : ∀ a ∈ deleteLetters X u, a ∈ s' := by
        intro a ha
        rcases mem_deleteLetters.mp ha with ⟨hau, haX⟩
        simp [s', hs a hau, haX]
      have hcard_lt : s'.card < s.card := by
        refine Finset.card_lt_card ⟨Finset.filter_subset _ s, ?_⟩
        intro hsub
        have hx₀s : x₀ ∈ s := hs x₀ hx₀u
        have hx₀s' := hsub hx₀s
        simp [s', hx₀X] at hx₀s'
      have hpow_le : 2 * 2 ^ s'.card ≤ 2 ^ s.card := by
        have h1 : 2 ^ (s'.card + 1) ≤ 2 ^ s.card :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
        rwa [Nat.pow_succ, Nat.mul_comm] at h1
      have hih := ih s' hs'_sub
      have hlen_step := length_le_two_mul_deleteLetters_succ u
        (fun x hx y hy ↦ hX.not_pair_infix hx hy)
      have hpos' : 1 ≤ 2 ^ s'.card := Nat.one_le_pow _ 2 (by decide)
      have hpos : 1 ≤ 2 ^ s.card := Nat.one_le_pow _ 2 (by decide)
      omega
    · push Not at hex
      have heq : deleteLetters X u = u := deleteLetters_eq_self hex
      rw [heq] at ih
      exact ih s hs

/-- Over a `[Fintype A]` alphabet, every unavoidable pattern `w : List A` has length at most
`2 ^ Fintype.card A - 1`. -/
theorem IsUnavoidable.length_le_two_pow_fintypeCard_sub_one [Fintype A] {w : List A}
    (hw : IsUnavoidable w) : w.length ≤ 2 ^ Fintype.card A - 1 :=
  hw.length_le_two_pow_card_sub_one Finset.univ (fun a _ ↦ Finset.mem_univ a)

end AffineDesubstitution

end CslibFrontier.Word
