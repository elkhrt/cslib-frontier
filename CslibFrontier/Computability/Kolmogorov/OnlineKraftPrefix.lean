/-
Copyright (c) 2026 D. M. Stull, Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Kolmogorov.KraftChaitin
import CslibFrontier.Foundations.Data.List.Primrec
import Mathlib.Data.Rat.Cast.Order

/-!
# Primitive recursiveness, prefix monotonicity, and `ℝ≥0∞` bounds for `kcAllocList`

This file extends `CslibFrontier.Computability.Kolmogorov.KraftChaitin` with three structural
properties of the executable online binary Kraft–Chaitin allocator `Cslib.Kolmogorov.kcAllocList`
needed for stagewise and oracle-relativized Kraft–Chaitin and Levin coding constructions
:

1. **Primitive recursiveness** (`primrec_kcAllocList`): `kcAllocList` is primitive recursive,
   established by expressing `kcAllocListAux` as a left fold over `kcStep`.
2. **Online prefix monotonicity** (`prefix_of_kcAllocList_append`): appending further length
   requests to `r₁` extends the allocated codeword list `c₁` as a prefix `c₁ <+: c₁₂`, ensuring
   previously assigned codewords never change as new stagewise requests arrive.
3. **Extended-nonnegative-real Kraft interface** (`kcAllocList_spec_of_ennreal_sum_le_one`):
   allocation succeeds with exact lengths, `InformationTheory.IsPrefixFree`, and `List.Nodup`
   whenever `(reqs.map fun d ↦ (2 : ℝ≥0∞)⁻¹ ^ d).sum ≤ 1`.

## Main results

* `Cslib.Kolmogorov.primrec_kcAllocList`: `kcAllocList` is primitive recursive.
* `Cslib.Kolmogorov.prefix_of_kcAllocList_append`: online prefix stability of `kcAllocList` under
  list concatenation.
* `Cslib.Kolmogorov.kcAllocList_spec_of_ennreal_sum_le_one`: `ℝ≥0∞`-valued Kraft sum specification
  for `kcAllocList`.
-/

public section

open scoped ENNReal

namespace Cslib.Kolmogorov

private def kcFoldStep (st : Option (List (List Bool) × List (List Bool))) (ℓ : ℕ) :
    Option (List (List Bool) × List (List Bool)) :=
  st.bind fun af ↦
    match kcStep af.1 (some ℓ) with
    | (_, none) => none
    | (avail', some code) => some (avail', code :: af.2)

private lemma kcAllocListAux_eq_foldl (reqs : List ℕ) :
    ∀ avail acc : List (List Bool),
      kcAllocListAux avail acc reqs =
        (reqs.foldl kcFoldStep (some (avail, acc))).map fun af ↦ af.2.reverse := by
  induction reqs with
  | nil => intro avail acc; rfl
  | cons ℓ rs ih =>
    intro avail acc
    simp only [kcAllocListAux, List.foldl_cons, kcFoldStep, Option.bind_some]
    cases hstep : kcStep avail (some ℓ) with
    | mk avail' opt =>
      cases opt with
      | none =>
        have hnone : ∀ l : List ℕ, l.foldl kcFoldStep none = none := fun l ↦ by
          induction l with
          | nil => rfl
          | cons _ _ ihl => exact ihl
        simp only [hnone, Option.map_none]
      | some code => exact ih avail' (code :: acc)

/-- Primitive recursiveness of the finite online Kraft–Chaitin allocator `kcAllocList`. -/
theorem primrec_kcAllocList : Primrec kcAllocList := by
  have hfoldStep : Primrec₂ kcFoldStep := by
    have hinner : Primrec₂
        (fun (st_l : Option (List (List Bool) × List (List Bool)) × ℕ)
          (af : List (List Bool) × List (List Bool)) ↦
          match kcStep af.1 (some st_l.2) with
          | (_, none) => (none : Option (List (List Bool) × List (List Bool)))
          | (avail', some code) => some (avail', code :: af.2)) := by
      have hkc : Primrec (fun p : (Option (List (List Bool) × List (List Bool)) × ℕ) ×
          (List (List Bool) × List (List Bool)) ↦
          kcStep p.2.1 (some p.1.2)) :=
        primrec₂_kcStep.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.option_some.comp (Primrec.snd.comp Primrec.fst))
      have hsome : Primrec₂ (fun (p : (Option (List (List Bool) × List (List Bool)) × ℕ) ×
          (List (List Bool) × List (List Bool))) (code : List Bool) ↦
          some ((kcStep p.2.1 (some p.1.2)).1, code :: p.2.2)) :=
        Primrec₂.mk <| Primrec.option_some.comp <|
          (Primrec.fst.comp (hkc.comp Primrec.fst)).pair
            (Primrec.list_cons.comp Primrec.snd
              (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      refine Primrec₂.mk <| (Primrec.option_casesOn (Primrec.snd.comp hkc)
        (Primrec.const none) hsome).of_eq fun p ↦ ?_
      cases h : kcStep p.2.1 (some p.1.2) with
      | mk avail' opt => cases opt <;> rfl
    exact Primrec₂.mk <| Primrec.option_bind Primrec.fst hinner
  have hfoldl : Primrec (fun reqs : List ℕ ↦
      reqs.foldl kcFoldStep (some ([[]], []))) := by
    have hstep2 : Primrec₂ (fun (_ : List ℕ)
        (bs : ℕ × Option (List (List Bool) × List (List Bool))) ↦ kcFoldStep bs.2 bs.1) :=
      Primrec₂.mk <| hfoldStep.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd)
    have hrev : Primrec (fun reqs : List ℕ ↦
        reqs.reverse.foldr (fun ℓ st ↦ kcFoldStep st ℓ) (some ([[]], []))) :=
      (Primrec.list_foldr Primrec.list_reverse (Primrec.const (some ([[]], []))) hstep2).of_eq
        fun _ ↦ rfl
    exact hrev.of_eq fun reqs ↦ by rw [← List.foldl_reverse, List.reverse_reverse]
  exact (Primrec.option_map hfoldl
    (Primrec.list_reverse.comp (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun reqs ↦
    (kcAllocListAux_eq_foldl reqs [[]] []).symm

private lemma prefix_acc_of_kcAllocListAux {reqs : List ℕ} :
    ∀ {avail acc codes : List (List Bool)},
      kcAllocListAux avail acc reqs = some codes →
      acc.reverse <+: codes := by
  induction reqs with
  | nil =>
    intro avail acc codes h
    simp only [kcAllocListAux, Option.some.injEq] at h
    exact h ▸ List.prefix_rfl
  | cons ℓ rs ih =>
    intro avail acc codes h
    simp only [kcAllocListAux] at h
    cases hstep : kcStep avail (some ℓ) with
    | mk avail' opt =>
      rw [hstep] at h
      cases opt with
      | none => simp at h
      | some code =>
        have hpref := ih h
        rw [List.reverse_cons] at hpref
        exact (List.prefix_append acc.reverse [code]).trans hpref

private lemma prefix_of_kcAllocListAux_append {r₁ r₂ : List ℕ} :
    ∀ {avail acc c₁₂ c₁ : List (List Bool)},
      kcAllocListAux avail acc (r₁ ++ r₂) = some c₁₂ →
      kcAllocListAux avail acc r₁ = some c₁ →
      c₁ <+: c₁₂ := by
  induction r₁ with
  | nil =>
    intro avail acc c₁₂ c₁ h₁₂ h₁
    simp only [kcAllocListAux, Option.some.injEq, List.nil_append] at h₁ h₁₂
    subst h₁
    exact prefix_acc_of_kcAllocListAux h₁₂
  | cons ℓ rs ih =>
    intro avail acc c₁₂ c₁ h₁₂ h₁
    simp only [List.cons_append, kcAllocListAux] at h₁₂ h₁
    cases hstep : kcStep avail (some ℓ) with
    | mk avail' opt =>
      rw [hstep] at h₁₂ h₁
      cases opt with
      | none => simp at h₁
      | some code => exact ih h₁₂ h₁

/-- Online prefix monotonicity of `kcAllocList`: extending a valid request list `r₁` to `r₁ ++ r₂`
preserves all previously allocated codewords `c₁` as a prefix of `c₁₂`. -/
theorem prefix_of_kcAllocList_append {r₁ r₂ : List ℕ} {c₁₂ c₁ : List (List Bool)}
    (h₁₂ : kcAllocList (r₁ ++ r₂) = some c₁₂)
    (h₁ : kcAllocList r₁ = some c₁) : c₁ <+: c₁₂ :=
  prefix_of_kcAllocListAux_append h₁₂ h₁

private lemma ofReal_rat_dyadic_list_sum (l : List ℕ) :
    ENNReal.ofReal (((l.map fun ℓ ↦ (2 : ℚ)⁻¹ ^ ℓ).sum : ℚ) : ℝ) =
      (l.map fun d ↦ (2 : ℝ≥0∞)⁻¹ ^ d).sum := by
  induction l with
  | nil => simp
  | cons d rs ih =>
    have hnn : (0 : ℝ) ≤ (((rs.map fun ℓ ↦ (2 : ℚ)⁻¹ ^ ℓ).sum : ℚ) : ℝ) := by
      exact_mod_cast List.sum_nonneg fun q hq ↦ by
        obtain ⟨ℓ, _, rfl⟩ := List.mem_map.mp hq
        positivity
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_pow, Rat.cast_inv,
      Rat.cast_ofNat]
    rw [ENNReal.ofReal_add (by positivity) hnn, ih, ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat]

/-- Specification of `kcAllocList` from an `ℝ≥0∞`-valued Kraft sum bound: whenever
`(reqs.map fun d ↦ (2 : ℝ≥0∞)⁻¹ ^ d).sum ≤ 1`, `kcAllocList reqs` returns a duplicate-free,
prefix-free list of binary codewords matching the requested lengths elementwise. -/
theorem kcAllocList_spec_of_ennreal_sum_le_one {reqs : List ℕ}
    (hsum : (reqs.map fun d ↦ (2 : ℝ≥0∞)⁻¹ ^ d).sum ≤ 1) :
    ∃ codes : List (List Bool),
      kcAllocList reqs = some codes ∧
      codes.length = reqs.length ∧
      (∀ (i : ℕ) (hi : i < reqs.length) (hc : i < codes.length),
        (codes[i]'hc).length = reqs[i]) ∧
      InformationTheory.IsPrefixFree {p | p ∈ codes} ∧
      codes.Nodup := by
  have hrat_sum : (reqs.map fun ℓ ↦ (2 : ℚ)⁻¹ ^ ℓ).sum ≤ 1 := by
    have heq := ofReal_rat_dyadic_list_sum reqs
    by_contra hgt
    push Not at hgt
    have hgt_real : (1 : ℝ) < (((reqs.map fun ℓ ↦ (2 : ℚ)⁻¹ ^ ℓ).sum : ℚ) : ℝ) := by
      exact_mod_cast hgt
    have hgt_enn : (1 : ℝ≥0∞) < (reqs.map fun d ↦ (2 : ℝ≥0∞)⁻¹ ^ d).sum := by
      rw [← ENNReal.ofReal_one, ← heq]
      exact (ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans hgt_real)).mpr hgt_real
    exact hgt_enn.not_ge hsum
  obtain ⟨codes, hcodes, hmap, hpair⟩ := kcAllocList_eq_some_of_sum_le_one hrat_sum
  have hlen : codes.length = reqs.length := by
    simpa using congrArg List.length hmap
  refine ⟨codes, hcodes, hlen, fun i hi hc ↦ ?_,
    isPrefixFree_of_pairwise_prefixDisjoint hpair,
    nodup_of_pairwise_prefixDisjoint hpair⟩
  have hget := congrArg (fun l : List ℕ ↦ l[i]?) hmap
  simpa [List.getElem?_eq_getElem hc, List.getElem?_eq_getElem hi] using hget

end Cslib.Kolmogorov
