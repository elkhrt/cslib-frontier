module

public import CslibFrontier.Computability.Communication.Protocol
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Log
import CslibFrontier.Computability.Communication.Announce
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Monochromatic rectangle covers yield deterministic protocols

Any finite monochromatic rectangle cover of `f : X → Y → Z` of size `t` yields a deterministic
two-party communication protocol computing `f` with depth at most
`40 * (Nat.clog 2 (t + 1)) ^ 2` bits for arbitrary output alphabets `Z`.

## Main definitions

* `CslibFrontier.Communication.MonoCover`: a finite monochromatic rectangle cover of
  `f : X → Y → Z`.

## Main results

* `CslibFrontier.Communication.MonoCover.exists_protocol`: existence of a deterministic protocol of
  depth at most `40 * (Nat.clog 2 (C.size + 1)) ^ 2` computing `f`.
* `CslibFrontier.Communication.MonoCover.ecomplexityFun_le`: upper bound on
  `Protocol.ecomplexityFun f` in terms of `C.size`.
-/

public section

namespace CslibFrontier.Communication

open Finset Cslib.Communication

/-- A finite monochromatic rectangle cover of `f : X → Y → Z` of size `size`. -/
structure MonoCover {X Y Z : Type*} (f : X → Y → Z) where
  /-- Number of rectangles in the cover. -/
  size : ℕ
  /-- Alice's side of each rectangle. -/
  alice : Fin size → Set X
  /-- Bob's side of each rectangle. -/
  bob : Fin size → Set Y
  /-- Output color of each rectangle. -/
  color : Fin size → Z
  /-- Every rectangle is monochromatic for `f`. -/
  mono : ∀ i, ∀ x ∈ alice i, ∀ y ∈ bob i, f x y = color i
  /-- The rectangles cover all of `X × Y`. -/
  cover : ∀ x y, ∃ i, x ∈ alice i ∧ y ∈ bob i

namespace MonoCover

variable {X Y Z : Type*} {f : X → Y → Z} (C : MonoCover f)

/-- Candidates in `S` sharing an Alice-row with `i`. -/
private noncomputable def rowMeets (S : Finset (Fin C.size)) (i : Fin C.size) :
    Finset (Fin C.size) := by
  classical
  exact S.filter fun j => (C.alice i ∩ C.alice j).Nonempty

/-- Candidates in `S` sharing a Bob-column with `i`. -/
private noncomputable def colMeets (S : Finset (Fin C.size)) (i : Fin C.size) :
    Finset (Fin C.size) := by
  classical
  exact S.filter fun j => (C.bob i ∩ C.bob j).Nonempty

/-- Two rectangles of distinct colors cannot share both a row and a column. -/
private theorem not_mem_rowMeets_and_colMeets {S : Finset (Fin C.size)} {i j : Fin C.size}
    (hc : C.color i ≠ C.color j) (hr : j ∈ C.rowMeets S i) (hk : j ∈ C.colMeets S i) : False := by
  classical
  simp only [rowMeets, colMeets, mem_filter] at hr hk
  obtain ⟨x, hxi, hxj⟩ := hr.2
  obtain ⟨y, hyi, hyj⟩ := hk.2
  have h1 := C.mono i x hxi y hyi
  have h2 := C.mono j x hxj y hyj
  exact hc (h1.symm.trans h2)

/-- For any `i` and any subset `T` of candidates with color different from `C.color i`,
`i` meets at most `#T` members of `T` in rows and columns combined. -/
private theorem card_rowMeets_add_card_colMeets_le {T : Finset (Fin C.size)} {i : Fin C.size}
    (hdiff : ∀ j ∈ T, C.color i ≠ C.color j) :
    #(C.rowMeets T i) + #(C.colMeets T i) ≤ #T := by
  classical
  have hdisj : Disjoint (C.rowMeets T i) (C.colMeets T i) :=
    disjoint_left.mpr fun j hjr hjc =>
      C.not_mem_rowMeets_and_colMeets (hdiff j (mem_filter.mp hjr).1) hjr hjc
  have hunion : C.rowMeets T i ∪ C.colMeets T i ⊆ T :=
    union_subset (filter_subset _ _) (filter_subset _ _)
  rw [← card_union_of_disjoint hdisj]
  exact card_le_card hunion

/-- Size of the largest color class in `S`. -/
private noncomputable def maxColorCard (S : Finset (Fin C.size)) : ℕ := by
  classical
  exact S.sup fun i => #{j ∈ S | C.color j = C.color i}

private theorem card_colorClass_le_maxColorCard (S : Finset (Fin C.size)) (z : Z)
    [DecidableEq Z] : #{j ∈ S | C.color j = z} ≤ C.maxColorCard S := by
  classical
  by_cases hne : ({j ∈ S | C.color j = z} : Finset (Fin C.size)).Nonempty
  · obtain ⟨i, hi⟩ := hne
    obtain ⟨hiS, hiz⟩ := mem_filter.mp hi
    calc #{j ∈ S | C.color j = z}
        = #{j ∈ S | C.color j = C.color i} := by congr 1; ext j; simp [hiz]
      _ ≤ C.maxColorCard S := by
          unfold maxColorCard
          convert Finset.le_sup (f := fun i => #{j ∈ S | C.color j = C.color i}) hiS
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, card_empty]
    exact Nat.zero_le _

private theorem exists_color_eq_maxColorCard [DecidableEq Z] {S : Finset (Fin C.size)}
    (hS : S.Nonempty) :
    ∃ z : Z, #{j ∈ S | C.color j = z} = C.maxColorCard S := by
  classical
  obtain ⟨i, hiS, hmax⟩ := Finset.exists_mem_eq_sup S hS
    (fun i => #{j ∈ S | C.color j = C.color i})
  refine ⟨C.color i, ?_⟩
  unfold maxColorCard
  convert hmax.symm

private theorem maxColorCard_le_card (S : Finset (Fin C.size)) : C.maxColorCard S ≤ #S := by
  classical
  unfold maxColorCard
  exact Finset.sup_le fun i _ => card_filter_le S _

/-- Non-monochromaticity potential `Φ(S) = |S|^4 * (|S| - maxColorCard S)`. -/
private noncomputable def potential (S : Finset (Fin C.size)) : ℕ :=
  #S ^ 4 * (#S - C.maxColorCard S)

private theorem potential_eq_zero_iff {S : Finset (Fin C.size)} (hS : S.Nonempty) :
    C.potential S = 0 ↔ ∀ i ∈ S, ∀ j ∈ S, C.color i = C.color j := by
  classical
  have hpos : 0 < #S := card_pos.mpr hS
  have hle := C.maxColorCard_le_card S
  unfold potential
  rw [mul_eq_zero, pow_eq_zero_iff (by decide : 4 ≠ 0)]
  have hne0 : #S ≠ 0 := by omega
  simp only [hne0, false_or, Nat.sub_eq_zero_iff_le]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := C.exists_color_eq_maxColorCard hS
    have hcard : #{j ∈ S | C.color j = z} = #S :=
      le_antisymm (card_filter_le _ _) (h.trans_eq hz.symm)
    have hall : ∀ j ∈ S, C.color j = z := by
      have heq := Finset.eq_of_subset_of_card_le (filter_subset (fun j => C.color j = z) S) hcard.ge
      intro j hj
      rw [← heq] at hj
      exact (mem_filter.mp hj).2
    intro i hi j hj
    rw [hall i hi, hall j hj]
  · intro hall
    obtain ⟨i0, hi0⟩ := hS
    have hcard : #{j ∈ S | C.color j = C.color i0} = #S := by
      rw [Finset.filter_true_of_mem fun j hj => hall j hj i0 hi0]
    exact hcard ▸ C.card_colorClass_le_maxColorCard S (C.color i0)

/-- Existence of a color-respecting bipartition `S = S₁ ⊔ S₀` with either:
(a) `S₁` is a single color class of size `> #S / 2`, or
(b) both `S₁` and `S₀` have size in `[#S / 3, 2 * #S / 3]`. -/
private theorem exists_color_bipartition {S : Finset (Fin C.size)}
    (hnotmono : 0 < C.potential S) :
    ∃ S₁ S₀ : Finset (Fin C.size),
      Disjoint S₁ S₀ ∧ S₁ ∪ S₀ = S ∧
      (∀ i ∈ S₁, ∀ j ∈ S₀, C.color i ≠ C.color j) ∧
      ((2 * #S₁ > #S ∧ #S₀ = #S - C.maxColorCard S ∧ ∃ z, ∀ i ∈ S₁, C.color i = z) ∨
       (3 * #S₁ ≥ #S ∧ 3 * #S₀ ≥ #S ∧ 2 * C.maxColorCard S ≤ #S)) := by
  classical
  have hS : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    simp [hemp, potential] at hnotmono
  obtain ⟨zStar, hzStar⟩ := C.exists_color_eq_maxColorCard hS
  set m := C.maxColorCard S
  have hm_eq : #{j ∈ S | C.color j = zStar} = m := hzStar
  have hm_le : m ≤ #S := C.maxColorCard_le_card S
  by_cases hheavy : 2 * m > #S
  · refine ⟨{j ∈ S | C.color j = zStar}, {j ∈ S | C.color j ≠ zStar},
      disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1), filter_union_filter_not_eq _ S,
      fun i hi j hj => by
        rw [(mem_filter.mp hi).2]; exact (mem_filter.mp hj).2.symm, Or.inl ?_⟩
    have hsum : #{j ∈ S | C.color j = zStar} + #{j ∈ S | C.color j ≠ zStar} = #S :=
      card_filter_add_card_filter_not (s := S) (p := fun j => C.color j = zStar)
    refine ⟨by omega, by omega, zStar, fun i hi => (mem_filter.mp hi).2⟩
  · push Not at hheavy
    by_cases hmid : 3 * m ≥ #S
    · refine ⟨{j ∈ S | C.color j = zStar}, {j ∈ S | C.color j ≠ zStar},
        disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1), filter_union_filter_not_eq _ S,
        fun i hi j hj => by
          rw [(mem_filter.mp hi).2]; exact (mem_filter.mp hj).2.symm, Or.inr ?_⟩
      have hsum : #{j ∈ S | C.color j = zStar} + #{j ∈ S | C.color j ≠ zStar} = #S :=
        card_filter_add_card_filter_not (s := S) (p := fun j => C.color j = zStar)
      exact ⟨by omega, by omega, hheavy⟩
    · push Not at hmid
      -- Every color class has size `< #S / 3`; greedily collect colors until weight `≥ #S / 3`.
      let colors : Finset Z := S.image C.color
      let wt (K : Finset Z) : ℕ := #{j ∈ S | C.color j ∈ K}
      have hwt_full : 3 * wt colors ≥ #S := by
        have : wt colors = #S := by
          dsimp only [wt]
          rw [Finset.filter_true_of_mem fun j hj => mem_image_of_mem C.color hj]
        omega
      -- Take a subset `K ⊆ colors` of minimal cardinality with `3 * wt K ≥ #S`.
      obtain ⟨K, hKmem, hKmin⟩ := Finset.exists_min_image
        (colors.powerset.filter fun K => 3 * wt K ≥ #S) Finset.card
        ⟨colors, mem_filter.mpr ⟨mem_powerset_self colors, hwt_full⟩⟩
      obtain ⟨hKsub, hKge⟩ := mem_filter.mp hKmem
      rw [mem_powerset] at hKsub
      have hKne : K.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have hpos : 0 < #S := card_pos.mpr hS
        have hwt0 : wt K = 0 := by
          dsimp only [wt]
          simp [hemp]
        omega
      obtain ⟨z0, hz0⟩ := hKne
      have hKerase_lt : 3 * wt (K.erase z0) < #S := by
        by_contra hge
        push Not at hge
        have hmem : K.erase z0 ∈ colors.powerset.filter (fun K => 3 * wt K ≥ #S) :=
          mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset z0 K).trans hKsub), hge⟩
        have hcard_le := hKmin (K.erase z0) hmem
        have hlt := card_erase_lt_of_mem hz0
        omega
      have hwt_split : wt K = wt (K.erase z0) + #{j ∈ S | C.color j = z0} := by
        dsimp only [wt]
        rw [← card_union_of_disjoint]
        · congr 1; ext j; simp only [mem_filter, mem_union, mem_erase]
          constructor
          · rintro ⟨hjS, hjK⟩
            by_cases h : C.color j = z0
            · exact Or.inr ⟨hjS, h⟩
            · exact Or.inl ⟨hjS, h, hjK⟩
          · rintro (⟨hjS, _, hjK⟩ | ⟨hjS, rfl⟩)
            · exact ⟨hjS, hjK⟩
            · exact ⟨hjS, hz0⟩
        · exact disjoint_filter.mpr fun j _ h1 h2 => (mem_erase.mp h1).1 h2
      have hz0_lt : 3 * #{j ∈ S | C.color j = z0} < #S := by
        have := C.card_colorClass_le_maxColorCard S z0
        omega
      refine ⟨{j ∈ S | C.color j ∈ K}, {j ∈ S | C.color j ∉ K},
        disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1), filter_union_filter_not_eq _ S,
        fun i hi j hj heq => (mem_filter.mp hj).2 (heq ▸ (mem_filter.mp hi).2), Or.inr ?_⟩
      have hsum : #{j ∈ S | C.color j ∈ K} + #{j ∈ S | C.color j ∉ K} = #S :=
        card_filter_add_card_filter_not (s := S) (p := fun j => C.color j ∈ K)
      have hwtK : wt K = #{j ∈ S | C.color j ∈ K} := rfl
      exact ⟨hKge, by omega, hheavy⟩

/-- Key potential drop inequality: in both cases of the bipartition, halving the opposite side
shrinks `potential S` by at least a factor `5 / 6`. -/
private theorem potential_drop_heavy {S S' S₁ S₀ : Finset (Fin C.size)}
    (hsub : S' ⊆ S) (hdisj : Disjoint S₁ S₀) (hunion : S₁ ∪ S₀ = S)
    (hheavy : 2 * #S₁ > #S) (hS0 : #S₀ = #S - C.maxColorCard S)
    {z : Z} (hz : ∀ i ∈ S₁, C.color i = z)
    (hstep : 2 * #(S' ∩ S₀) ≤ #S₀ ∨ 2 * #(S' ∩ S₁) ≤ #S₁) :
    6 * C.potential S' ≤ 5 * C.potential S := by
  classical
  have hS_split : #S = #S₁ + #S₀ := by rw [← hunion, card_union_of_disjoint hdisj]
  have hS'_split : #S' = #(S' ∩ S₁) + #(S' ∩ S₀) := by
    rw [← card_union_of_disjoint (hdisj.mono inter_subset_right inter_subset_right),
      ← inter_union_distrib_left, hunion, inter_eq_left.mpr hsub]
  have hr'_le : #S' - C.maxColorCard S' ≤ #(S' ∩ S₀) := by
    have hsub1 : S' ∩ S₁ ⊆ {j ∈ S' | C.color j = z} := fun j hj =>
      mem_filter.mpr ⟨(mem_inter.mp hj).1, hz j (mem_inter.mp hj).2⟩
    have hm' : #(S' ∩ S₁) ≤ C.maxColorCard S' :=
      (card_le_card hsub1).trans (C.card_colorClass_le_maxColorCard S' z)
    omega
  have hcard_le : #S' ≤ #S := card_le_card hsub
  have hS'0_le : #(S' ∩ S₀) ≤ #S₀ := card_le_card inter_subset_right
  have hS'1_le : #(S' ∩ S₁) ≤ #S₁ := card_le_card inter_subset_right
  unfold potential
  rw [← hS0]
  rcases hstep with h0 | h1
  · have hpow : #S' ^ 4 ≤ #S ^ 4 := Nat.pow_le_pow_left hcard_le 4
    have hmul : 2 * (#S' ^ 4 * (#S' - C.maxColorCard S')) ≤ #S ^ 4 * #S₀ := by
      calc 2 * (#S' ^ 4 * (#S' - C.maxColorCard S'))
          = #S' ^ 4 * (2 * (#S' - C.maxColorCard S')) := by ring
        _ ≤ #S ^ 4 * #S₀ := Nat.mul_le_mul hpow (by omega)
    omega
  · have h4N' : 4 * #S' ≤ 3 * #S := by omega
    have hpow : 256 * #S' ^ 4 ≤ 81 * #S ^ 4 := by
      have h := Nat.pow_le_pow_left h4N' 4
      calc 256 * #S' ^ 4 = (4 * #S') ^ 4 := by ring
        _ ≤ (3 * #S) ^ 4 := h
        _ = 81 * #S ^ 4 := by ring
    have hmul : 256 * (#S' ^ 4 * (#S' - C.maxColorCard S')) ≤ 81 * (#S ^ 4 * #S₀) := by
      calc 256 * (#S' ^ 4 * (#S' - C.maxColorCard S'))
          = (256 * #S' ^ 4) * (#S' - C.maxColorCard S') := by ring
        _ ≤ (81 * #S ^ 4) * #S₀ := Nat.mul_le_mul hpow (hr'_le.trans hS'0_le)
        _ = 81 * (#S ^ 4 * #S₀) := by ring
    omega

private theorem potential_drop_balanced {S S' S₁ S₀ : Finset (Fin C.size)}
    (hsub : S' ⊆ S) (hdisj : Disjoint S₁ S₀) (hunion : S₁ ∪ S₀ = S)
    (h1 : 3 * #S₁ ≥ #S) (h0 : 3 * #S₀ ≥ #S) (hm : 2 * C.maxColorCard S ≤ #S)
    (hstep : 2 * #(S' ∩ S₀) ≤ #S₀ ∨ 2 * #(S' ∩ S₁) ≤ #S₁) :
    6 * C.potential S' ≤ 5 * C.potential S := by
  have hS_split : #S = #S₁ + #S₀ := by rw [← hunion, card_union_of_disjoint hdisj]
  have hS'_split : #S' = #(S' ∩ S₁) + #(S' ∩ S₀) := by
    rw [← card_union_of_disjoint (hdisj.mono inter_subset_right inter_subset_right),
      ← inter_union_distrib_left, hunion, inter_eq_left.mpr hsub]
  have hS'0_le : #(S' ∩ S₀) ≤ #S₀ := card_le_card inter_subset_right
  have hS'1_le : #(S' ∩ S₁) ≤ #S₁ := card_le_card inter_subset_right
  have h6N' : 6 * #S' ≤ 5 * #S := by
    rcases hstep with hs0 | hs1 <;> omega
  have hr : #S ≤ 2 * (#S - C.maxColorCard S) := by omega
  have hr' : #S' - C.maxColorCard S' ≤ #S' := Nat.sub_le _ _
  have hpow : 6 ^ 5 * #S' ^ 5 ≤ 5 ^ 5 * #S ^ 5 := by
    calc 6 ^ 5 * #S' ^ 5 = (6 * #S') ^ 5 := by ring
      _ ≤ (5 * #S) ^ 5 := Nat.pow_le_pow_left h6N' 5
      _ = 5 ^ 5 * #S ^ 5 := by ring
  unfold potential
  have h1' : #S' ^ 4 * (#S' - C.maxColorCard S') ≤ #S' ^ 5 := by
    calc #S' ^ 4 * (#S' - C.maxColorCard S') ≤ #S' ^ 4 * #S' := Nat.mul_le_mul_left _ hr'
      _ = #S' ^ 5 := by ring
  have h2' : 6 ^ 5 * (#S' ^ 4 * (#S' - C.maxColorCard S')) ≤
      2 * 5 ^ 5 * (#S ^ 4 * (#S - C.maxColorCard S)) := by
    calc 6 ^ 5 * (#S' ^ 4 * (#S' - C.maxColorCard S'))
        ≤ 6 ^ 5 * #S' ^ 5 := Nat.mul_le_mul_left _ h1'
      _ ≤ 5 ^ 5 * #S ^ 5 := hpow
      _ = 5 ^ 5 * (#S ^ 4 * #S) := by ring
      _ ≤ 5 ^ 5 * (#S ^ 4 * (2 * (#S - C.maxColorCard S))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hr)
      _ = 2 * 5 ^ 5 * (#S ^ 4 * (#S - C.maxColorCard S)) := by ring
  omega

/-- `r` phases of the generalized cover-halving protocol compute `f` whenever
`5 ^ r * potential S < 6 ^ r`. -/
private theorem exists_protocol_of_potential_lt [Nonempty Z] (r : ℕ)
    (S : Finset (Fin C.size)) :
    ∃ q : Protocol X Y Z, q.depth ≤ r * (2 * Nat.clog 2 (C.size + 1)) ∧
      (5 ^ r * C.potential S < 6 ^ r →
        ∀ x y, (∃ k ∈ S, x ∈ C.alice k ∧ y ∈ C.bob k) → q.run x y = f x y) := by
  classical
  induction r generalizing S with
  | zero =>
    by_cases hmono : C.potential S = 0
    · by_cases hne : S.Nonempty
      · refine ⟨.output (C.color hne.choose), by simp, fun _ x y ⟨k, hkS, hxk, hyk⟩ => ?_⟩
        rw [Protocol.run_output, C.mono k x hxk y hyk]
        exact (C.potential_eq_zero_iff hne).mp hmono hne.choose hne.choose_spec k hkS
      · refine ⟨.output (Classical.arbitrary Z), by simp, fun _ x y ⟨k, hkS, _, _⟩ => ?_⟩
        exact absurd ⟨k, hkS⟩ hne
    · refine ⟨.output (Classical.arbitrary Z), by simp, fun h => ?_⟩
      simp only [pow_zero, one_mul, Nat.lt_one_iff] at h
      exact absurd h hmono
  | succ r ih =>
    by_cases hmono : C.potential S = 0
    · by_cases hne : S.Nonempty
      · refine ⟨.output (C.color hne.choose), by simp, fun _ x y ⟨k, hkS, hxk, hyk⟩ => ?_⟩
        rw [Protocol.run_output, C.mono k x hxk y hyk]
        exact (C.potential_eq_zero_iff hne).mp hmono hne.choose hne.choose_spec k hkS
      · refine ⟨.output (Classical.arbitrary Z), by simp, fun _ x y ⟨k, hkS, _, _⟩ => ?_⟩
        exact absurd ⟨k, hkS⟩ hne
    · have hpos : 0 < C.potential S := Nat.pos_of_ne_zero hmono
      obtain ⟨S₁, S₀, hdisj, hunion, hdiff, hcases⟩ := C.exists_color_bipartition hpos
      choose! next hnext hnext_run using ih
      let goodA (x : X) (i : Fin C.size) : Prop :=
        i ∈ S ∧ x ∈ C.alice i ∧
          ((i ∈ S₁ ∧ 2 * #(C.rowMeets S i ∩ S₀) ≤ #S₀) ∨
           (i ∈ S₀ ∧ 2 * #(C.rowMeets S i ∩ S₁) ≤ #S₁))
      let goodB (y : Y) (j : Fin C.size) : Prop :=
        j ∈ S ∧ y ∈ C.bob j ∧
          ((j ∈ S₁ ∧ 2 * #(C.colMeets S j ∩ S₀) ≤ #S₀) ∨
           (j ∈ S₀ ∧ 2 * #(C.colMeets S j ∩ S₁) ≤ #S₁))
      let choiceA (x : X) : Option (Fin C.size) :=
        if h : ∃ i, goodA x i then some h.choose else none
      let choiceB (y : Y) : Option (Fin C.size) :=
        if h : ∃ j, goodB y j then some h.choose else none
      have hcard : Fintype.card (Option (Fin C.size)) = C.size + 1 := by simp
      obtain ⟨qa, hqa, hqa_run⟩ := Protocol.exists_run_eq_left (Y := Y) choiceA
      obtain ⟨qb, hqb, hqb_run⟩ := Protocol.exists_run_eq_right (X := X) choiceB
      rw [hcard] at hqa hqb
      let afterB : Option (Fin C.size) → Protocol X Y Z
        | some j => next (C.colMeets S j)
        | none => .output (Classical.arbitrary Z)
      let afterA : Option (Fin C.size) → Protocol X Y Z
        | some i => next (C.rowMeets S i)
        | none => qb.bind afterB
      have hdrop {S' : Finset (Fin C.size)} (hsub : S' ⊆ S)
          (hstep : 2 * #(S' ∩ S₀) ≤ #S₀ ∨ 2 * #(S' ∩ S₁) ≤ #S₁)
          (hpot : 5 ^ (r + 1) * C.potential S < 6 ^ (r + 1)) :
          5 ^ r * C.potential S' < 6 ^ r := by
        have h65 : 6 * C.potential S' ≤ 5 * C.potential S := by
          rcases hcases with ⟨hh, hS0, z, hz⟩ | ⟨h31, h30, hm⟩
          · exact C.potential_drop_heavy hsub hdisj hunion hh hS0 hz hstep
          · exact C.potential_drop_balanced hsub hdisj hunion h31 h30 hm hstep
        have hmul : 6 * (5 ^ r * C.potential S') < 6 * 6 ^ r := by
          calc 6 * (5 ^ r * C.potential S')
              = 5 ^ r * (6 * C.potential S') := by ring
            _ ≤ 5 ^ r * (5 * C.potential S) := Nat.mul_le_mul_left _ h65
            _ = 5 ^ (r + 1) * C.potential S := by ring
            _ < 6 ^ (r + 1) := hpot
            _ = 6 * 6 ^ r := by ring
        omega
      refine ⟨qa.bind afterA, ?_, fun hpot x y ⟨k, hkS, hxk, hyk⟩ => ?_⟩
      · set c := Nat.clog 2 (C.size + 1)
        have hB : ∀ o, (afterB o).depth ≤ r * (2 * c) := by
          rintro (_ | j)
          · simp [afterB]
          · exact hnext _
        have hA : ∀ o, (afterA o).depth ≤ c + r * (2 * c) := by
          rintro (_ | i)
          · exact (Protocol.depth_bind_le hB).trans (by omega)
          · exact (hnext _).trans (by omega)
        have hmul : (r + 1) * (2 * c) = r * (2 * c) + 2 * c := by ring
        refine (Protocol.depth_bind_le hA).trans ?_
        omega
      · rw [Protocol.run_bind, hqa_run]
        by_cases hA : ∃ i, goodA x i
        · have hi := hA.choose_spec
          simp only [choiceA, dite_eq_left hA, afterA]
          have hsub : C.rowMeets S hA.choose ⊆ S := filter_subset _ _
          have hstep : 2 * #(C.rowMeets S hA.choose ∩ S₀) ≤ #S₀ ∨
              2 * #(C.rowMeets S hA.choose ∩ S₁) ≤ #S₁ := by
            rcases hi.2.2 with ⟨_, h⟩ | ⟨_, h⟩
            · exact Or.inl h
            · exact Or.inr h
          refine hnext_run _ (hdrop hsub hstep hpot) x y ⟨k, ?_, hxk, hyk⟩
          simp only [rowMeets, mem_filter]
          exact ⟨hkS, x, hi.2.1, hxk⟩
        by_cases hB : ∃ j, goodB y j
        · have hj := hB.choose_spec
          simp only [choiceA, dite_eq_right hA, afterA, Protocol.run_bind, hqb_run, choiceB,
            dite_eq_left hB, afterB]
          have hsub : C.colMeets S hB.choose ⊆ S := filter_subset _ _
          have hstep : 2 * #(C.colMeets S hB.choose ∩ S₀) ≤ #S₀ ∨
              2 * #(C.colMeets S hB.choose ∩ S₁) ≤ #S₁ := by
            rcases hj.2.2 with ⟨_, h⟩ | ⟨_, h⟩
            · exact Or.inl h
            · exact Or.inr h
          refine hnext_run _ (hdrop hsub hstep hpot) x y ⟨k, ?_, hxk, hyk⟩
          simp only [colMeets, mem_filter]
          exact ⟨hkS, y, hj.2.1, hyk⟩
        · exfalso
          have hkU : k ∈ S₁ ∪ S₀ := hunion.symm ▸ hkS
          rcases mem_union.mp hkU with hk1 | hk0
          · have hrow_eq : C.rowMeets S k ∩ S₀ = C.rowMeets S₀ k := by
              ext j; simp only [rowMeets, mem_inter, mem_filter]
              exact ⟨fun ⟨⟨_, h⟩, hj0⟩ => ⟨hj0, h⟩,
                fun ⟨hj0, h⟩ => ⟨⟨hunion ▸ mem_union_right _ hj0, h⟩, hj0⟩⟩
            have hcol_eq : C.colMeets S k ∩ S₀ = C.colMeets S₀ k := by
              ext j; simp only [colMeets, mem_inter, mem_filter]
              exact ⟨fun ⟨⟨_, h⟩, hj0⟩ => ⟨hj0, h⟩,
                fun ⟨hj0, h⟩ => ⟨⟨hunion ▸ mem_union_right _ hj0, h⟩, hj0⟩⟩
            have hsum := C.card_rowMeets_add_card_colMeets_le (T := S₀) (i := k)
              (fun j hj => hdiff k hk1 j hj)
            have hA' : ¬ 2 * #(C.rowMeets S k ∩ S₀) ≤ #S₀ :=
              fun h => hA ⟨k, hkS, hxk, Or.inl ⟨hk1, h⟩⟩
            have hB' : ¬ 2 * #(C.colMeets S k ∩ S₀) ≤ #S₀ :=
              fun h => hB ⟨k, hkS, hyk, Or.inl ⟨hk1, h⟩⟩
            rw [hrow_eq] at hA'; rw [hcol_eq] at hB'
            omega
          · have hrow_eq : C.rowMeets S k ∩ S₁ = C.rowMeets S₁ k := by
              ext j; simp only [rowMeets, mem_inter, mem_filter]
              exact ⟨fun ⟨⟨_, h⟩, hj1⟩ => ⟨hj1, h⟩,
                fun ⟨hj1, h⟩ => ⟨⟨hunion ▸ mem_union_left _ hj1, h⟩, hj1⟩⟩
            have hcol_eq : C.colMeets S k ∩ S₁ = C.colMeets S₁ k := by
              ext j; simp only [colMeets, mem_inter, mem_filter]
              exact ⟨fun ⟨⟨_, h⟩, hj1⟩ => ⟨hj1, h⟩,
                fun ⟨hj1, h⟩ => ⟨⟨hunion ▸ mem_union_left _ hj1, h⟩, hj1⟩⟩
            have hsum := C.card_rowMeets_add_card_colMeets_le (T := S₁) (i := k)
              (fun j hj => (hdiff j hj k hk0).symm)
            have hA' : ¬ 2 * #(C.rowMeets S k ∩ S₁) ≤ #S₁ :=
              fun h => hA ⟨k, hkS, hxk, Or.inr ⟨hk0, h⟩⟩
            have hB' : ¬ 2 * #(C.colMeets S k ∩ S₁) ≤ #S₁ :=
              fun h => hB ⟨k, hkS, hyk, Or.inr ⟨hk0, h⟩⟩
            rw [hrow_eq] at hA'; rw [hcol_eq] at hB'
            omega

/-- **Generalized Kushilevitz–Nisan cover-to-protocol theorem**: a monochromatic rectangle cover
of `f : X → Y → Z` of size `t` yields a deterministic protocol of depth at most
`40 * (Nat.clog 2 (t + 1)) ^ 2` bits. -/
theorem exists_protocol [Nonempty Z] :
    ∃ q : Protocol X Y Z, q.run = f ∧ q.depth ≤ 40 * (Nat.clog 2 (C.size + 1)) ^ 2 := by
  set c := Nat.clog 2 (C.size + 1)
  set r := 20 * c
  obtain ⟨q, hqd, hqrun⟩ := C.exists_protocol_of_potential_lt r Finset.univ
  have hpot_le : C.potential Finset.univ ≤ C.size ^ 5 := by
    unfold potential
    have hcard : #(Finset.univ : Finset (Fin C.size)) = C.size := card_fin C.size
    rw [hcard]
    calc C.size ^ 4 * (C.size - C.maxColorCard Finset.univ)
        ≤ C.size ^ 4 * C.size := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = C.size ^ 5 := by ring
  have hlt_pow : C.size < 2 ^ c := by
    have hle : C.size + 1 ≤ 2 ^ c := Nat.le_pow_clog Nat.one_lt_two (C.size + 1)
    omega
  have h56 : 5 ^ r * C.potential Finset.univ < 6 ^ r := by
    have h1 : 2 ^ (5 * c) * 5 ^ (20 * c) ≤ 6 ^ (20 * c) := by
      have hbase : 2 * 5 ^ 4 ≤ 6 ^ 4 := by norm_num
      calc 2 ^ (5 * c) * 5 ^ (20 * c)
          = (2 * 5 ^ 4) ^ (5 * c) := by rw [mul_pow, ← pow_mul]; congr 2; ring
        _ ≤ (6 ^ 4) ^ (5 * c) := Nat.pow_le_pow_left hbase (5 * c)
        _ = 6 ^ (20 * c) := by rw [← pow_mul]; congr 1; ring
    have h2 : C.potential Finset.univ < 2 ^ (5 * c) := by
      calc C.potential Finset.univ ≤ C.size ^ 5 := hpot_le
        _ < (2 ^ c) ^ 5 := Nat.pow_lt_pow_left hlt_pow (by decide)
        _ = 2 ^ (5 * c) := by rw [← pow_mul, mul_comm]
    calc 5 ^ r * C.potential Finset.univ
        < 5 ^ (20 * c) * 2 ^ (5 * c) := Nat.mul_lt_mul_of_pos_left h2 (by positivity)
      _ = 2 ^ (5 * c) * 5 ^ (20 * c) := by ring
      _ ≤ 6 ^ (20 * c) := h1
  refine ⟨q, funext₂ fun x y => ?_, ?_⟩
  · obtain ⟨k, hxk, hyk⟩ := C.cover x y
    exact hqrun h56 x y ⟨k, mem_univ k, hxk, hyk⟩
  · calc q.depth ≤ r * (2 * c) := hqd
      _ = 40 * c ^ 2 := by ring

/-- Deterministic communication complexity upper bound from a monochromatic rectangle cover. -/
theorem ecomplexityFun_le [Nonempty Z] :
    Protocol.ecomplexityFun f ≤ ((40 * (Nat.clog 2 (C.size + 1)) ^ 2 : ℕ) : ℕ∞) := by
  obtain ⟨q, hrun, hdepth⟩ := C.exists_protocol
  exact Protocol.ecomplexityFun_le_iff.mpr ⟨q, hrun, hdepth⟩

end MonoCover

end CslibFrontier.Communication
