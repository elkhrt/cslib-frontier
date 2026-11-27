/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Problems.WordUnavoidability.ReductionForward

/-!
# Backward Direction and Bidirectional `ExactThreeSAT` Equivalence

This module proves `isUnavoidable_clauseGadgetPattern_imp_satisfiable`: if `clauseGadgetPattern φ`
is unavoidable, stripping separator letters from a Zimin–Sapir free-set reduction yields deletion
ranks whose earliest-deleted literal slots in each clause, variable, and tap gadget cannot
conflict
across the dedicated guard blocks, yielding a satisfying truth assignment for `φ`. Combining both
directions gives `isUnavoidable_threeCNFWord_iff_satisfiable` and
`isUnavoidable_threeCNFWord_iff_mem_ExactThreeSAT`.
-/

public section

namespace CslibFrontier.Complexity

open CslibFrontier.Word Cslib.Logic.PL Cslib.Complexity

section BackwardDirection

private def prefUnion (Xs : List (Set ClauseGadgetLetter)) (t : ℕ) : Set ClauseGadgetLetter :=
  {u | ∃ (i : ℕ) (hi : i < Xs.length), i < t ∧ u ∈ Xs[i]'hi}

private theorem prefUnion_zero (Xs : List (Set ClauseGadgetLetter)) : prefUnion Xs 0 = ∅ := by
  ext u; simp [prefUnion]

private theorem prefUnion_succ {Xs : List (Set ClauseGadgetLetter)} {t : ℕ} (ht : t < Xs.length) :
    prefUnion Xs (t + 1) = prefUnion Xs t ∪ Xs[t] := by
  ext u
  simp only [prefUnion, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨i, hi, hit, hu⟩
    by_cases h_eq : i = t
    · subst h_eq; exact Or.inr hu
    · exact Or.inl ⟨i, hi, by omega, hu⟩
  · rintro (⟨i, hi, hit, hu⟩ | hu)
    · exact ⟨i, hi, by omega, hu⟩
    · exact ⟨t, ht, Nat.lt_succ_self t, hu⟩

private theorem strip_separators_freeSet {φ : CNF ℕ} {B_all X : Set ClauseGadgetLetter}
    (hX : IsFreeSet (deleteLetters B_all (clauseGadgetPattern φ)) X) :
    IsFreeSet (deleteLetters {u ∈ B_all | u.isSep = false} (clauseGadgetPattern φ))
      {u ∈ X | u.isSep = false} := by
  let B_ns : Set ClauseGadgetLetter := {u ∈ B_all | u.isSep = false}
  let X_ns : Set ClauseGadgetLetter := {u ∈ X | u.isSep = false}
  have hB_sep : ∀ z, ClauseGadgetLetter.sep z ∉ B_ns := by
    intro z hz; simp [B_ns] at hz
  rw [isFreeSet_iff]
  intro x ⟨hxX, hx_ns⟩ y ⟨hyX, hy_ns⟩ hch
  rw [gadget_hasAlternatingChain_nonSep_iff hB_sep hx_ns hy_ns] at hch
  rcases hch with ⟨b, hpath, hby⟩
  have hbp_lift : ∀ u v, GadgetBlockPair φ B_ns u v →
      [u, v] <:+: deleteLetters B_all (clauseGadgetPattern φ) := by
    rintro u v ⟨_, _, blk, hblk, hinf⟩
    have heq_blk : deleteLetters B_ns blk = deleteLetters B_all blk := by
      have haux : ∀ l : List ClauseGadgetLetter, (∀ a ∈ l, a.isSep = false) →
          deleteLetters B_ns l = deleteLetters B_all l := by
        intro l hl
        induction l with
        | nil => simp
        | cons a as ihl =>
          have ha_ns := hl a (List.mem_cons_self ..)
          by_cases haB : a ∈ B_all
          · have ha_nsB : a ∈ B_ns := ⟨haB, ha_ns⟩
            simp only [deleteLetters_cons_of_mem ha_nsB,
              deleteLetters_cons_of_mem haB]
            exact ihl fun c hc ↦ hl c (List.mem_cons_of_mem _ hc)
          · have ha_nnsB : a ∉ B_ns := fun h ↦ haB h.1
            simp only [deleteLetters_cons_of_not_mem ha_nnsB,
              deleteLetters_cons_of_not_mem haB]
            congr 1
            exact ihl fun c hc ↦ hl c (List.mem_cons_of_mem _ hc)
      exact haux blk (no_sep_in_clauseGadgetBlocks φ blk hblk)
    rw [heq_blk] at hinf
    exact hinf.trans (IsInfix.deleteLetters (blk_infix_clauseGadgetPattern φ hblk) B_all)
  have hch_all : HasAlternatingChain (deleteLetters B_all (clauseGadgetPattern φ)) x y := by
    refine hasAlternatingChain_iff_reflTransGen.mpr ⟨b, ?_, hbp_lift b y hby⟩
    clear hby
    induction hpath with
    | refl => exact Relation.ReflTransGen.refl
    | @tail u₁ u₂ _ hsr ih =>
      rcases hsr with ⟨c, h₁, h₂⟩
      exact ih.tail (sameRightNeighbor_iff.mpr ⟨c, hbp_lift u₁ c h₁, hbp_lift u₂ c h₂⟩)
  exact (isFreeSet_iff.mp hX) x hxX y hyX hch_all

private theorem exists_nonSep_freeSet_seq {φ : CNF ℕ}
    (hunav : IsUnavoidable (clauseGadgetPattern φ)) :
    ∃ Xs : List (Set ClauseGadgetLetter),
      (∀ (t : ℕ) (ht : t < Xs.length) (z : ℕ), ClauseGadgetLetter.sep z ∉ Xs[t]'ht) ∧
      (∀ (t : ℕ) (ht : t < Xs.length),
        IsFreeSet (deleteLetters (prefUnion Xs t) (clauseGadgetPattern φ)) (Xs[t]'ht)) ∧
      (∀ t ≤ Xs.length, IsUnavoidable (deleteLetters (prefUnion Xs t) (clauseGadgetPattern φ))) ∧
      (∀ u ∈ clauseGadgetPattern φ, u.isSep = false → u ∈ prefUnion Xs Xs.length) := by
  have haux : ∀ (w : List ClauseGadgetLetter), IsFreeSetReducible w →
      ∀ B_all : Set ClauseGadgetLetter, w = deleteLetters B_all (clauseGadgetPattern φ) →
        ∃ Xs : List (Set ClauseGadgetLetter),
          (∀ (t : ℕ) (ht : t < Xs.length) (z : ℕ), ClauseGadgetLetter.sep z ∉ Xs[t]'ht) ∧
          (∀ (t : ℕ) (ht : t < Xs.length),
            IsFreeSet
              (deleteLetters ({u ∈ B_all | u.isSep =
                false} ∪ prefUnion Xs t) (clauseGadgetPattern φ))
              (Xs[t]'ht)) ∧
          (∀ u ∈ clauseGadgetPattern φ, u.isSep = false →
            u ∈ {u ∈ B_all | u.isSep = false} ∪ prefUnion Xs Xs.length) := by
    intro w hfs
    induction hfs with
    | nil =>
      intro B_all hnil
      refine ⟨[], by simp, by simp, ?_⟩
      intro u hup hns
      left
      refine ⟨?_, hns⟩
      by_contra huB
      have hmem : u ∈ deleteLetters B_all (clauseGadgetPattern φ) :=
        mem_deleteLetters.mpr ⟨hup, huB⟩
      rw [← hnil] at hmem
      exact List.not_mem_nil hmem
    | @delete_freeSet w₀ X hX _ ih =>
      intro B_all hw₀
      rw [hw₀] at hX
      have hw' : deleteLetters X w₀ = deleteLetters (B_all ∪ X) (clauseGadgetPattern φ) := by
        rw [hw₀]
        exact CslibFrontier.Word.deleteLetters_deleteLetters B_all X (clauseGadgetPattern φ)
      obtain ⟨Xs', hsep', hfree', hcov'⟩ := ih (B_all ∪ X) hw'
      let X_ns : Set ClauseGadgetLetter := {u ∈ X | u.isSep = false}
      have hX_ns_free := strip_separators_freeSet hX
      have hunion_eq : ∀ t : ℕ,
          {u ∈ B_all ∪ X | u.isSep = false} ∪ prefUnion Xs' t =
            {u ∈ B_all | u.isSep = false} ∪ prefUnion (X_ns :: Xs') (t + 1) := by
        intro t
        ext u
        simp only [Set.mem_union, Set.mem_ofPred_eq, prefUnion, List.length_cons]
        constructor
        · rintro ((⟨huB | huX, hns⟩) | ⟨i, hi, hit, hu⟩)
          · exact Or.inl ⟨huB, hns⟩
          · exact Or.inr ⟨0, Nat.succ_pos _, Nat.succ_pos _, huX, hns⟩
          · exact Or.inr ⟨i + 1, Nat.succ_lt_succ hi, Nat.succ_lt_succ hit, hu⟩
        · rintro (⟨huB, hns⟩ | ⟨i, hi, hit, hu⟩)
          · exact Or.inl ⟨Or.inl huB, hns⟩
          · cases i with
            | zero =>
              rcases hu with ⟨huX, hns⟩
              exact Or.inl ⟨Or.inr huX, hns⟩
            | succ j =>
              exact Or.inr ⟨j, Nat.lt_of_succ_lt_succ hi, Nat.lt_of_succ_lt_succ hit, hu⟩
      refine ⟨X_ns :: Xs', ?_, ?_, ?_⟩
      · intro t ht z
        cases t with
        | zero => intro hz; simp [X_ns] at hz
        | succ j => exact hsep' j (Nat.lt_of_succ_lt_succ ht) z
      · intro t ht
        cases t with
        | zero =>
          simpa [prefUnion_zero] using hX_ns_free
        | succ j =>
          have hj : j < Xs'.length := Nat.lt_of_succ_lt_succ ht
          have hf := hfree' j hj
          rwa [hunion_eq j] at hf
      · intro u hup hns
        have hc := hcov' u hup hns
        rwa [hunion_eq Xs'.length] at hc
  have h0 : clauseGadgetPattern φ =
    deleteLetters (∅ : Set ClauseGadgetLetter) (clauseGadgetPattern φ) :=
    (deleteLetters_eq_self (by simp)).symm
  obtain ⟨Xs, hsep, hfree0, hcov0⟩ :=
    haux (clauseGadgetPattern φ) (isUnavoidable_iff_isFreeSetReducible.mp hunav) ∅ h0
  have hempty_ns : {u ∈ (∅ : Set ClauseGadgetLetter) | u.isSep = false} = ∅ := by ext; simp
  have hfree : ∀ (t : ℕ) (ht : t < Xs.length),
      IsFreeSet (deleteLetters (prefUnion Xs t) (clauseGadgetPattern φ)) (Xs[t]'ht) := by
    intro t ht
    have hf := hfree0 t ht
    rwa [hempty_ns, Set.empty_union] at hf
  have hcov : ∀ u ∈ clauseGadgetPattern φ, u.isSep = false → u ∈ prefUnion Xs Xs.length := by
    intro u hup hns
    have hc := hcov0 u hup hns
    rwa [hempty_ns, Set.empty_union] at hc
  have hunav_at : ∀ t ≤ Xs.length,
      IsUnavoidable (deleteLetters (prefUnion Xs t) (clauseGadgetPattern φ)) := by
    intro t ht
    obtain ⟨d, hd⟩ : ∃ d, t + d = Xs.length := ⟨Xs.length - t, by omega⟩
    induction d generalizing t with
    | zero =>
      have ht_eq : t = Xs.length := by omega
      subst ht_eq
      exact isUnavoidable_deleteLetters_of_contains_nonSep hcov
    | succ d ihd =>
      have ht_lt : t < Xs.length := by omega
      have hnext := ihd (t + 1) (by omega) (by omega)
      exact (hfree t ht_lt).isUnavoidable_of_deleteLetters (by
        simpa only [CslibFrontier.Word.deleteLetters_deleteLetters,
          prefUnion_succ ht_lt] using hnext)
  exact ⟨Xs, hsep, hfree, hunav_at, hcov⟩

private noncomputable def stepOf (Xs : List (Set ClauseGadgetLetter)) (u : ClauseGadgetLetter)
    : ℕ := by
  classical exact Xs.findIdx (fun X ↦ decide (u ∈ X))

private theorem stepOf_spec :
    ∀ (Xs : List (Set ClauseGadgetLetter)) {u : ClauseGadgetLetter},
      u ∈ prefUnion Xs Xs.length →
      ∃ hlt : stepOf Xs u < Xs.length,
        u ∈ Xs[stepOf Xs u]'hlt ∧
        (∀ t ≤ stepOf Xs u, u ∉ prefUnion Xs t) ∧
        (∀ t, stepOf Xs u < t → u ∈ prefUnion Xs t)
  | [], _, hu => by simp [prefUnion] at hu
  | X :: Xs, u, hu => by
    classical
    by_cases huX : u ∈ X
    · have h0 : stepOf (X :: Xs) u = 0 := by simp [stepOf, List.findIdx_cons, huX]
      rw [h0]
      refine ⟨Nat.succ_pos _, huX, ?_, ?_⟩
      · intro t ht
        have ht0 : t = 0 := by omega
        subst ht0; simp [prefUnion]
      · intro t ht
        exact ⟨0, Nat.succ_pos _, ht, huX⟩
    · have hu_rest : u ∈ prefUnion Xs Xs.length := by
        rcases hu with ⟨i, hi, _, hui⟩
        cases i with
        | zero => exact absurd hui huX
        | succ j =>
          exact ⟨j, Nat.lt_of_succ_lt_succ hi, Nat.lt_of_succ_lt_succ hi, hui⟩
      obtain ⟨hlt', hmem', hbefore', _⟩ := stepOf_spec Xs hu_rest
      have hsucc : stepOf (X :: Xs) u = stepOf Xs u + 1 := by
        simp [stepOf, List.findIdx_cons, huX]
      rw [hsucc]
      refine ⟨Nat.succ_lt_succ hlt', hmem', ?_, ?_⟩
      · intro t ht
        rintro ⟨i, hi, hit, hui⟩
        cases i with
        | zero => exact huX hui
        | succ j =>
          have hj_lt : j < t - 1 := by omega
          exact hbefore' (t - 1) (by omega) ⟨j, Nat.lt_of_succ_lt_succ hi, hj_lt, hui⟩
      · intro t ht
        exact ⟨stepOf Xs u + 1, Nat.succ_lt_succ hlt', ht, hmem'⟩

private theorem mem_clauseGadgetPattern_of_blk {φ : CNF ℕ} {blk : List ClauseGadgetLetter}
    (hblk : blk ∈ clauseGadgetBlocks φ) {u : ClauseGadgetLetter} (hu : u ∈ blk) :
    u ∈ clauseGadgetPattern φ ∧ u.isSep = false :=
  ⟨(blk_infix_clauseGadgetPattern φ hblk).subset hu, no_sep_in_clauseGadgetBlocks φ blk hblk u hu⟩

private theorem pair2_infix_at {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {x y : ClauseGadgetLetter}
    (hblk : [x, y] ∈ clauseGadgetBlocks φ) (hx : x ∉ B) (hy : y ∉ B) :
    [x, y] <:+: deleteLetters B (clauseGadgetPattern φ) :=
  (infix_pair_two_gadget.mpr ⟨rfl, rfl, hx, hy⟩).trans
    (IsInfix.deleteLetters (blk_infix_clauseGadgetPattern φ hblk) B)

/-- If `clauseGadgetPattern φ` is unavoidable for a `3`-CNF formula `φ`, then `φ` is
satisfiable. -/
theorem isUnavoidable_clauseGadgetPattern_imp_satisfiable {φ : CNF ℕ}
    (h3 : ∀ c ∈ φ, c.length = 3) (hunav : IsUnavoidable (clauseGadgetPattern φ)) :
    φ.Satisfiable := by
  obtain ⟨Xs, _, hfree, hunav_at, hcov⟩ := exists_nonSep_freeSet_seq hunav
  have hnot_self_chain : ∀ (t : ℕ) (ht : t < Xs.length) (u : ClauseGadgetLetter),
      u ∈ Xs[t]'ht →
      ¬ HasAlternatingChain (deleteLetters (prefUnion Xs t) (clauseGadgetPattern φ)) u u :=
    fun t ht u hu ↦ (isFreeSet_iff.mp (hfree t ht)) u hu u hu
  have hnot_self_at : ∀ {t s : ℕ}, t = s → ∀ (hs : s < Xs.length) (u : ClauseGadgetLetter),
      u ∈ Xs[s]'hs →
      ¬ HasAlternatingChain (deleteLetters (prefUnion Xs t) (clauseGadgetPattern φ)) u u := by
    rintro t _ rfl hs u hu
    exact hnot_self_chain t hs u hu
  have hmem_step : ∀ {blk : List ClauseGadgetLetter}, blk ∈ clauseGadgetBlocks φ →
      ∀ {u : ClauseGadgetLetter}, u ∈ blk →
        ∃ hlt : stepOf Xs u < Xs.length,
          u ∈ Xs[stepOf Xs u]'hlt ∧
          (∀ t ≤ stepOf Xs u, u ∉ prefUnion Xs t) ∧
          (∀ t, stepOf Xs u < t → u ∈ prefUnion Xs t) := by
    intro blk hblk u hu
    obtain ⟨hup, hns⟩ := mem_clauseGadgetPattern_of_blk hblk hu
    exact stepOf_spec Xs (hcov u hup hns)
  have horig_blk : ∀ {j : ℕ}, j < φ.length → ∀ {blk : List ClauseGadgetLetter},
      blk ∈ origClauseBlocks j → blk ∈ clauseGadgetBlocks φ := by
    intro j hj blk hb
    exact mem_clauseGadgetBlocks_iff.mpr (Or.inl ⟨j, hj, hb⟩)
  have hvar_blk : ∀ {v : ℕ}, v ∈ φ.distinctVars → ∀ {blk : List ClauseGadgetLetter},
      blk ∈ varPosBlocks v → blk ∈ clauseGadgetBlocks φ := by
    intro v hv blk hb
    exact mem_clauseGadgetBlocks_iff.mpr (Or.inr (Or.inl ⟨v, hv, hb⟩))
  have htap_blk : ∀ {j : ℕ} (hj : j < φ.length) (k : Fin 3) {blk : List ClauseGadgetLetter},
      blk ∈ occTapBlocks j k (clauseLitAt (φ[j]'hj) k) → blk ∈ clauseGadgetBlocks φ := by
    intro j hj k blk hb
    exact mem_clauseGadgetBlocks_iff.mpr (Or.inr (Or.inr ⟨j, hj, k, hb⟩))
  have hsr_step : ∀ {w : List ClauseGadgetLetter} {x y c : ClauseGadgetLetter},
      [x, c] <:+: w → [y, c] <:+: w → SameRightNeighbor w x y :=
    fun h₁ h₂ ↦ sameRightNeighbor_iff.mpr ⟨_, h₁, h₂⟩
  -- Step 1: earliest literal of C_j precedes all helpers {ao, bo, co, do_}
  have horig_before : ∀ (j : ℕ) (hj : j < φ.length),
      let m_orig := min (stepOf Xs (.orig j 0))
        (min (stepOf Xs (.orig j 1)) (stepOf Xs (.orig j 2)))
      let m_help := min (min (stepOf Xs (.ao j)) (stepOf Xs (.bo j)))
        (min (stepOf Xs (.co j)) (stepOf Xs (.do_ j)))
      m_orig < m_help := by
    intro j hj m_orig m_help
    by_contra hnot_lt
    have hle : m_help ≤ m_orig := by omega
    obtain ⟨hao_lt, hao_X, hao_nb, _⟩ :=
      hmem_step (horig_blk hj (by simp [mem_origClauseBlocks_iff]))
        (by simp : ClauseGadgetLetter.ao j ∈ [.ao j, .orig j 0])
    obtain ⟨hbo_lt, hbo_X, hbo_nb, _⟩ :=
      hmem_step (horig_blk hj (by simp [mem_origClauseBlocks_iff]))
        (by simp : ClauseGadgetLetter.bo j ∈ [.bo j, .orig j 0])
    obtain ⟨hco_lt, hco_X, hco_nb, _⟩ :=
      hmem_step (horig_blk hj (by simp [mem_origClauseBlocks_iff]))
        (by simp : ClauseGadgetLetter.co j ∈ [.co j, .orig j 1])
    obtain ⟨hdo_lt, hdo_X, hdo_nb, _⟩ :=
      hmem_step (horig_blk hj (by simp [mem_origClauseBlocks_iff]))
        (by simp : ClauseGadgetLetter.do_ j ∈ [.do_ j, .orig j 2])
    obtain ⟨_, _, ho0_nb, _⟩ :=
      hmem_step (horig_blk hj (by simp [mem_origClauseBlocks_iff]))
        (by simp : ClauseGadgetLetter.orig j 0 ∈ [.ao j, .orig j 0])
    obtain ⟨_, _, ho1_nb, _⟩ :=
      hmem_step (horig_blk hj (by simp [mem_origClauseBlocks_iff]))
        (by simp : ClauseGadgetLetter.orig j 1 ∈ [.bo j, .orig j 1])
    obtain ⟨_, _, ho2_nb, _⟩ :=
      hmem_step (horig_blk hj (by simp [mem_origClauseBlocks_iff]))
        (by simp : ClauseGadgetLetter.orig j 2 ∈ [.co j, .orig j 2])
    let B := prefUnion Xs m_help
    let w := deleteLetters B (clauseGadgetPattern φ)
    have hp : ∀ {x y}, [x, y] ∈ origClauseBlocks j → x ∉ B → y ∉ B → [x, y] <:+: w :=
      fun hb hx hy ↦ pair2_infix_at (horig_blk hj hb) hx hy
    have na : ClauseGadgetLetter.ao j ∉ B := hao_nb m_help (by dsimp [m_help]; omega)
    have nb : ClauseGadgetLetter.bo j ∉ B := hbo_nb m_help (by dsimp [m_help]; omega)
    have nc : ClauseGadgetLetter.co j ∉ B := hco_nb m_help (by dsimp [m_help]; omega)
    have nd : ClauseGadgetLetter.do_ j ∉ B := hdo_nb m_help (by dsimp [m_help]; omega)
    have no0 : ClauseGadgetLetter.orig j 0 ∉ B := ho0_nb m_help (by dsimp [m_orig] at hle; omega)
    have no1 : ClauseGadgetLetter.orig j 1 ∉ B := ho1_nb m_help (by dsimp [m_orig] at hle; omega)
    have no2 : ClauseGadgetLetter.orig j 2 ∉ B := ho2_nb m_help (by dsimp [m_orig] at hle; omega)
    have p_ao0 := hp (by simp [mem_origClauseBlocks_iff]) na no0
    have p_bo0 := hp (by simp [mem_origClauseBlocks_iff]) nb no0
    have p_bo1 := hp (by simp [mem_origClauseBlocks_iff]) nb no1
    have p_co1 := hp (by simp [mem_origClauseBlocks_iff]) nc no1
    have p_co2 := hp (by simp [mem_origClauseBlocks_iff]) nc no2
    have p_do2 := hp (by simp [mem_origClauseBlocks_iff]) nd no2
    have p_da := hp (by simp [mem_origClauseBlocks_iff]) nd na
    have p_ab := hp (by simp [mem_origClauseBlocks_iff]) na nb
    have p_ac := hp (by simp [mem_origClauseBlocks_iff]) na nc
    have p_ad := hp (by simp [mem_origClauseBlocks_iff]) na nd
    have hmin_cases : m_help = stepOf Xs (.ao j) ∨ m_help = stepOf Xs (.bo j) ∨
        m_help = stepOf Xs (.co j) ∨ m_help = stepOf Xs (.do_ j) := by
      dsimp [m_help]; omega
    rcases hmin_cases with heq | heq | heq | heq
    · exact hnot_self_at heq hao_lt (.ao j) hao_X
        (hasAlternatingChain_iff_reflTransGen.mpr ⟨.do_ j,
          ((Relation.ReflTransGen.single (hsr_step p_ao0 p_bo0)).tail
            (hsr_step p_bo1 p_co1)).tail (hsr_step p_co2 p_do2), p_da⟩)
    · exact hnot_self_at heq hbo_lt (.bo j) hbo_X
        (hasAlternatingChain_iff_reflTransGen.mpr ⟨.ao j,
          Relation.ReflTransGen.single (hsr_step p_bo0 p_ao0), p_ab⟩)
    · exact hnot_self_at heq hco_lt (.co j) hco_X
        (hasAlternatingChain_iff_reflTransGen.mpr ⟨.ao j,
          (Relation.ReflTransGen.single (hsr_step p_co1 p_bo1)).tail (hsr_step p_bo0 p_ao0),
          p_ac⟩)
    · exact hnot_self_at heq hdo_lt (.do_ j) hdo_X
        (hasAlternatingChain_iff_reflTransGen.mpr ⟨.ao j,
          ((Relation.ReflTransGen.single (hsr_step p_do2 p_co2)).tail
            (hsr_step p_co1 p_bo1)).tail (hsr_step p_bo0 p_ao0), p_ad⟩)
  -- Step 2: earliest literal of P_v precedes all helpers {ap, bp, cp}
  have hvar_before : ∀ {v : ℕ}, v ∈ φ.distinctVars →
      min (stepOf Xs (.px v)) (stepOf Xs (.py v)) <
        min (stepOf Xs (.ap v)) (min (stepOf Xs (.bp v)) (stepOf Xs (.cp v))) := by
    intro v hv
    set m_var := min (stepOf Xs (.px v)) (stepOf Xs (.py v))
    set m_help := min (stepOf Xs (.ap v)) (min (stepOf Xs (.bp v)) (stepOf Xs (.cp v)))
    by_contra hnot_lt
    have hle : m_help ≤ m_var := by omega
    obtain ⟨hap_lt, hap_X, hap_nb, _⟩ :=
      hmem_step (hvar_blk hv (by simp [mem_varPosBlocks_iff]))
        (by simp : ClauseGadgetLetter.ap v ∈ [.ap v, .px v])
    obtain ⟨hbp_lt, hbp_X, hbp_nb, _⟩ :=
      hmem_step (hvar_blk hv (by simp [mem_varPosBlocks_iff]))
        (by simp : ClauseGadgetLetter.bp v ∈ [.bp v, .px v])
    obtain ⟨hcp_lt, hcp_X, hcp_nb, _⟩ :=
      hmem_step (hvar_blk hv (by simp [mem_varPosBlocks_iff]))
        (by simp : ClauseGadgetLetter.cp v ∈ [.cp v, .py v])
    obtain ⟨_, _, hpx_nb, _⟩ :=
      hmem_step (hvar_blk hv (by simp [mem_varPosBlocks_iff]))
        (by simp : ClauseGadgetLetter.px v ∈ [.ap v, .px v])
    obtain ⟨_, _, hpy_nb, _⟩ :=
      hmem_step (hvar_blk hv (by simp [mem_varPosBlocks_iff]))
        (by simp : ClauseGadgetLetter.py v ∈ [.bp v, .py v])
    let B := prefUnion Xs m_help
    let w := deleteLetters B (clauseGadgetPattern φ)
    have hp : ∀ {x y}, [x, y] ∈ varPosBlocks v → x ∉ B → y ∉ B → [x, y] <:+: w :=
      fun hb hx hy ↦ pair2_infix_at (hvar_blk hv hb) hx hy
    have na : ClauseGadgetLetter.ap v ∉ B := hap_nb m_help (by dsimp [m_help]; omega)
    have nb : ClauseGadgetLetter.bp v ∉ B := hbp_nb m_help (by dsimp [m_help]; omega)
    have nc : ClauseGadgetLetter.cp v ∉ B := hcp_nb m_help (by dsimp [m_help]; omega)
    have npx : ClauseGadgetLetter.px v ∉ B := hpx_nb m_help (by dsimp [m_var] at hle; omega)
    have npy : ClauseGadgetLetter.py v ∉ B := hpy_nb m_help (by dsimp [m_var] at hle; omega)
    have p_ax := hp (by simp [mem_varPosBlocks_iff]) na npx
    have p_bx := hp (by simp [mem_varPosBlocks_iff]) nb npx
    have p_by := hp (by simp [mem_varPosBlocks_iff]) nb npy
    have p_cy := hp (by simp [mem_varPosBlocks_iff]) nc npy
    have p_ca := hp (by simp [mem_varPosBlocks_iff]) nc na
    have p_ab := hp (by simp [mem_varPosBlocks_iff]) na nb
    have p_ac := hp (by simp [mem_varPosBlocks_iff]) na nc
    have hmin_cases : m_help = stepOf Xs (.ap v) ∨ m_help = stepOf Xs (.bp v) ∨
        m_help = stepOf Xs (.cp v) := by
      dsimp [m_help]; omega
    rcases hmin_cases with heq | heq | heq
    · exact hnot_self_at heq hap_lt (.ap v) hap_X
        (hasAlternatingChain_iff_reflTransGen.mpr ⟨.cp v,
          (Relation.ReflTransGen.single (hsr_step p_ax p_bx)).tail (hsr_step p_by p_cy), p_ca⟩)
    · exact hnot_self_at heq hbp_lt (.bp v) hbp_X
        (hasAlternatingChain_iff_reflTransGen.mpr ⟨.ap v,
          Relation.ReflTransGen.single (hsr_step p_bx p_ax), p_ab⟩)
    · exact hnot_self_at heq hcp_lt (.cp v) hcp_X
        (hasAlternatingChain_iff_reflTransGen.mpr ⟨.ap v,
          (Relation.ReflTransGen.single (hsr_step p_cy p_by)).tail (hsr_step p_bx p_ax), p_ac⟩)
  -- Step 3: earliest literal of D_{j, k} precedes all helpers {an, bn, cn}
  have htap_before : ∀ (j : ℕ) (hj : j < φ.length) (k : Fin 3),
      min (stepOf Xs (.qo j k)) (stepOf Xs (.qv j k)) <
        min (stepOf Xs (.an j k)) (min (stepOf Xs (.bn j k)) (stepOf Xs (.cn j k))) := by
    intro j hj k
    set m_tap := min (stepOf Xs (.qo j k)) (stepOf Xs (.qv j k))
    set m_help := min (stepOf Xs (.an j k)) (min (stepOf Xs (.bn j k)) (stepOf Xs (.cn j k)))
    by_contra hnot_lt
    have hle : m_help ≤ m_tap := by omega
    obtain ⟨han_lt, han_X, han_nb, _⟩ :=
      hmem_step (htap_blk hj k (by simp [mem_occTapBlocks_iff]))
        (by simp : ClauseGadgetLetter.an j k ∈ [.an j k, .bn j k])
    obtain ⟨hbn_lt, hbn_X, hbn_nb, _⟩ :=
      hmem_step (htap_blk hj k (by simp [mem_occTapBlocks_iff]))
        (by simp : ClauseGadgetLetter.bn j k ∈ [.bn j k, .an j k])
    obtain ⟨hcn_lt, hcn_X, hcn_nb, _⟩ :=
      hmem_step (htap_blk hj k (by simp [mem_occTapBlocks_iff]))
        (by simp : ClauseGadgetLetter.cn j k ∈ [.cn j k, .an j k])
    obtain ⟨_, _, hqo_nb, _⟩ :=
      hmem_step (htap_blk hj k (by simp [mem_occTapBlocks_iff]))
        (by simp : ClauseGadgetLetter.qo j k ∈ [.qo j k, .bn j k])
    obtain ⟨_, _, hqv_nb, _⟩ :=
      hmem_step (htap_blk hj k (by simp [mem_occTapBlocks_iff]))
        (by simp : ClauseGadgetLetter.qv j k ∈ [.qv j k, .cn j k])
    let B := prefUnion Xs m_help
    let w := deleteLetters B (clauseGadgetPattern φ)
    have hp : ∀ {x y}, [x, y] ∈ occTapBlocks j k (clauseLitAt φ[j] k) →
        x ∉ B → y ∉ B → [x, y] <:+: w :=
      fun hb hx hy ↦ pair2_infix_at (htap_blk hj k hb) hx hy
    have na : ClauseGadgetLetter.an j k ∉ B := han_nb m_help (by dsimp [m_help]; omega)
    have nb : ClauseGadgetLetter.bn j k ∉ B := hbn_nb m_help (by dsimp [m_help]; omega)
    have nc : ClauseGadgetLetter.cn j k ∉ B := hcn_nb m_help (by dsimp [m_help]; omega)
    have nqo : ClauseGadgetLetter.qo j k ∉ B := hqo_nb m_help (by dsimp [m_tap] at hle; omega)
    have nqv : ClauseGadgetLetter.qv j k ∉ B := hqv_nb m_help (by dsimp [m_tap] at hle; omega)
    have p_ab := hp (by simp [mem_occTapBlocks_iff]) na nb
    have p_ob := hp (by simp [mem_occTapBlocks_iff]) nqo nb
    have p_oc := hp (by simp [mem_occTapBlocks_iff]) nqo nc
    have p_vc := hp (by simp [mem_occTapBlocks_iff]) nqv nc
    have p_va := hp (by simp [mem_occTapBlocks_iff]) nqv na
    have p_ba := hp (by simp [mem_occTapBlocks_iff]) nb na
    have p_ca := hp (by simp [mem_occTapBlocks_iff]) nc na
    have hmin_cases : m_help = stepOf Xs (.an j k) ∨ m_help = stepOf Xs (.bn j k) ∨
        m_help = stepOf Xs (.cn j k) := by
      dsimp [m_help]; omega
    rcases hmin_cases with heq | heq | heq
    · exact hnot_self_at heq han_lt (.an j k) han_X
        (hasAlternatingChain_iff_reflTransGen.mpr ⟨.qv j k,
          (Relation.ReflTransGen.single (hsr_step p_ab p_ob)).tail (hsr_step p_oc p_vc), p_va⟩)
    · exact hnot_self_at heq hbn_lt (.bn j k) hbn_X
        (hasAlternatingChain_iff_reflTransGen.mpr ⟨.qo j k,
          (Relation.ReflTransGen.single (hsr_step p_ba p_va)).tail (hsr_step p_vc p_oc), p_ob⟩)
    · exact hnot_self_at heq hcn_lt (.cn j k) hcn_X
        (hasAlternatingChain_iff_reflTransGen.mpr ⟨.qv j k,
          Relation.ReflTransGen.single (hsr_step p_ca p_va), p_vc⟩)
  -- Step 4a: guard go_{j, k} prevents orig_{j, k} and qo_{j, k} both being earliest
  have hgo_conflict : ∀ (j : ℕ) (hj : j < φ.length) (k : Fin 3),
      stepOf Xs (.orig j k) ≤ min (stepOf Xs (.orig j 0))
        (min (stepOf Xs (.orig j 1)) (stepOf Xs (.orig j 2))) →
      ¬ (stepOf Xs (.qo j k) ≤ stepOf Xs (.qv j k)) := by
    intro j hj k horig_min hqo_le
    have hmo := horig_before j hj
    have hmt := htap_before j hj k
    obtain ⟨hgo_lt, hgo_X, hgo_nb, _⟩ :=
      hmem_step (htap_blk hj k (by simp [mem_occTapBlocks_iff]))
        (by simp : ClauseGadgetLetter.go j k ∈ [.go j k, .an j k])
    obtain ⟨_, _, ho_k_nb, ho_k_af⟩ :=
      hmem_step (htap_blk hj k (by simp [mem_occTapBlocks_iff]))
        (by simp : ClauseGadgetLetter.orig j k ∈ [.go j k, .orig j k, .qo j k, .go j k])
    obtain ⟨_, _, hqo_nb, hqo_af⟩ :=
      hmem_step (htap_blk hj k (by simp [mem_occTapBlocks_iff]))
        (by simp : ClauseGadgetLetter.qo j k ∈ [.qo j k, .bn j k])
    set τ := stepOf Xs (.go j k)
    have hgo_blk : [.go j k, .orig j k, .qo j k, .go j k] ∈ clauseGadgetBlocks φ :=
      htap_blk hj k (by simp [mem_occTapBlocks_iff])
    by_cases hτ_p : τ ≤ stepOf Xs (.orig j k)
    · obtain ⟨_, _, hao_nb, _⟩ :=
        hmem_step (horig_blk hj (by simp [mem_origClauseBlocks_iff]))
          (by simp : ClauseGadgetLetter.ao j ∈ [.ao j, .orig j 0])
      obtain ⟨_, _, hbo_nb, _⟩ :=
        hmem_step (horig_blk hj (by simp [mem_origClauseBlocks_iff]))
          (by simp : ClauseGadgetLetter.bo j ∈ [.bo j, .orig j 0])
      obtain ⟨_, _, hco_nb, _⟩ :=
        hmem_step (horig_blk hj (by simp [mem_origClauseBlocks_iff]))
          (by simp : ClauseGadgetLetter.co j ∈ [.co j, .orig j 1])
      obtain ⟨_, _, ho0_nb, _⟩ :=
        hmem_step (horig_blk hj (by simp [mem_origClauseBlocks_iff]))
          (by simp : ClauseGadgetLetter.orig j 0 ∈ [.ao j, .orig j 0])
      obtain ⟨_, _, ho1_nb, _⟩ :=
        hmem_step (horig_blk hj (by simp [mem_origClauseBlocks_iff]))
          (by simp : ClauseGadgetLetter.orig j 1 ∈ [.bo j, .orig j 1])
      obtain ⟨_, _, ho2_nb, _⟩ :=
        hmem_step (horig_blk hj (by simp [mem_origClauseBlocks_iff]))
          (by simp : ClauseGadgetLetter.orig j 2 ∈ [.co j, .orig j 2])
      let B := prefUnion Xs τ
      let w := deleteLetters B (clauseGadgetPattern φ)
      have hmo' : min (stepOf Xs (.orig j 0))
          (min (stepOf Xs (.orig j 1)) (stepOf Xs (.orig j 2))) <
          min (min (stepOf Xs (.ao j)) (stepOf Xs (.bo j)))
            (min (stepOf Xs (.co j)) (stepOf Xs (.do_ j))) := hmo
      have hk_range : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
      have hτ_min : τ ≤ min (stepOf Xs (.orig j 0))
          (min (stepOf Xs (.orig j 1)) (stepOf Xs (.orig j 2))) := by omega
      have ng : ClauseGadgetLetter.go j k ∉ B := hgo_nb τ (Nat.le_refl _)
      have np : ClauseGadgetLetter.orig j k ∉ B := ho_k_nb τ hτ_p
      have na : ClauseGadgetLetter.ao j ∉ B := hao_nb τ (by omega)
      have nb : ClauseGadgetLetter.bo j ∉ B := hbo_nb τ (by omega)
      have nc : ClauseGadgetLetter.co j ∉ B := hco_nb τ (by omega)
      have no0 : ClauseGadgetLetter.orig j 0 ∉ B := ho0_nb τ (by omega)
      have no1 : ClauseGadgetLetter.orig j 1 ∉ B := ho1_nb τ (by omega)
      have no2 : ClauseGadgetLetter.orig j 2 ∉ B := ho2_nb τ (by omega)
      have p_gp : [.go j k, .orig j k] <:+: w :=
        (infix_pair_guard4.mpr (Or.inr ⟨ng, Or.inl ⟨rfl, rfl, np⟩⟩)).trans
          (IsInfix.deleteLetters (blk_infix_clauseGadgetPattern φ hgo_blk) B)
      have p_ag : [.ao j, .go j k] <:+: w :=
        pair2_infix_at (htap_blk hj k (by simp [mem_occTapBlocks_iff])) na ng
      have p_ao0 := pair2_infix_at (horig_blk hj (by simp [mem_origClauseBlocks_iff])) na no0
      have p_bo0 := pair2_infix_at (horig_blk hj (by simp [mem_origClauseBlocks_iff])) nb no0
      have p_bo1 := pair2_infix_at (horig_blk hj (by simp [mem_origClauseBlocks_iff])) nb no1
      have p_co1 := pair2_infix_at (horig_blk hj (by simp [mem_origClauseBlocks_iff])) nc no1
      have p_co2 := pair2_infix_at (horig_blk hj (by simp [mem_origClauseBlocks_iff])) nc no2
      fin_cases k
      · exact hnot_self_chain τ hgo_lt (.go j 0) hgo_X
          (hasAlternatingChain_iff_reflTransGen.mpr ⟨.ao j,
            Relation.ReflTransGen.single (hsr_step p_gp p_ao0), p_ag⟩)
      · exact hnot_self_chain τ hgo_lt (.go j 1) hgo_X
          (hasAlternatingChain_iff_reflTransGen.mpr ⟨.ao j,
            (Relation.ReflTransGen.single (hsr_step p_gp p_bo1)).tail (hsr_step p_bo0 p_ao0),
            p_ag⟩)
      · exact hnot_self_chain τ hgo_lt (.go j 2) hgo_X
          (hasAlternatingChain_iff_reflTransGen.mpr ⟨.ao j,
            ((Relation.ReflTransGen.single (hsr_step p_gp p_co2)).tail
              (hsr_step p_co1 p_bo1)).tail (hsr_step p_bo0 p_ao0), p_ag⟩)
    · by_cases hτ_q : τ ≤ stepOf Xs (.qo j k)
      · obtain ⟨_, _, han_nb, _⟩ :=
          hmem_step (htap_blk hj k (by simp [mem_occTapBlocks_iff]))
            (by simp : ClauseGadgetLetter.an j k ∈ [.an j k, .bn j k])
        obtain ⟨_, _, hcn_nb, _⟩ :=
          hmem_step (htap_blk hj k (by simp [mem_occTapBlocks_iff]))
            (by simp : ClauseGadgetLetter.cn j k ∈ [.qo j k, .cn j k])
        obtain ⟨_, _, hqv_nb, _⟩ :=
          hmem_step (htap_blk hj k (by simp [mem_occTapBlocks_iff]))
            (by simp : ClauseGadgetLetter.qv j k ∈ [.qv j k, .cn j k])
        let B := prefUnion Xs τ
        let w := deleteLetters B (clauseGadgetPattern φ)
        have ng : ClauseGadgetLetter.go j k ∉ B := hgo_nb τ (Nat.le_refl _)
        have nq : ClauseGadgetLetter.qo j k ∉ B := hqo_nb τ hτ_q
        have nqv : ClauseGadgetLetter.qv j k ∉ B := hqv_nb τ (by omega)
        have na : ClauseGadgetLetter.an j k ∉ B := han_nb τ (by omega)
        have nc : ClauseGadgetLetter.cn j k ∉ B := hcn_nb τ (by omega)
        have p_ga := pair2_infix_at (htap_blk hj k (by simp [mem_occTapBlocks_iff])) ng na
        have p_va := pair2_infix_at (htap_blk hj k (by simp [mem_occTapBlocks_iff])) nqv na
        have p_vc := pair2_infix_at (htap_blk hj k (by simp [mem_occTapBlocks_iff])) nqv nc
        have p_oc := pair2_infix_at (htap_blk hj k (by simp [mem_occTapBlocks_iff])) nq nc
        have p_qg : [.qo j k, .go j k] <:+: w :=
          (infix_pair_guard4.mpr (Or.inr ⟨ng, Or.inr (Or.inl ⟨rfl, rfl, nq⟩)⟩)).trans
            (IsInfix.deleteLetters (blk_infix_clauseGadgetPattern φ hgo_blk) B)
        exact hnot_self_chain τ hgo_lt (.go j k) hgo_X
          (hasAlternatingChain_iff_reflTransGen.mpr ⟨.qo j k,
            (Relation.ReflTransGen.single (hsr_step p_ga p_va)).tail (hsr_step p_vc p_oc), p_qg⟩)
      · let T := max (stepOf Xs (.orig j k)) (stepOf Xs (.qo j k)) + 1
        have hT_le : T ≤ τ := by dsimp [T]; omega
        have hp_in : ClauseGadgetLetter.orig j k ∈ prefUnion Xs T := ho_k_af T (by dsimp [T]; omega)
        have hq_in : ClauseGadgetLetter.qo j k ∈ prefUnion Xs T := hqo_af T (by dsimp [T]; omega)
        have hg_out : ClauseGadgetLetter.go j k ∉ prefUnion Xs T := hgo_nb T hT_le
        have hgg : [.go j k, .go j k] <:+: deleteLetters (prefUnion Xs T) (clauseGadgetPattern φ) :=
          (infix_pair_guard4.mpr
            (Or.inr ⟨hg_out, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hp_in, hq_in⟩)))⟩)).trans
            (IsInfix.deleteLetters (blk_infix_clauseGadgetPattern φ hgo_blk) (prefUnion Xs T))
        exact isAvoidable_iff.mp (isAvoidable_of_pair_infix hgg) (hunav_at T (by omega))
  -- Step 4b: guard gv_{j, k} prevents conflictVarSlot and qv_{j, k} both being earliest
  have hgv_conflict : ∀ (j : ℕ) (hj : j < φ.length) (k : Fin 3),
      stepOf Xs (.qv j k) ≤ stepOf Xs (.qo j k) →
      ¬ (stepOf Xs (conflictVarSlot (clauseLitAt φ[j] k)) ≤
          min (stepOf Xs (.px (clauseLitAt φ[j] k).1))
            (stepOf Xs (.py (clauseLitAt φ[j] k).1))) := by
    intro j hj k hqv_le hpvar_min
    have hv := lit_var_mem_distinctVars h3 hj k
    have hmv := hvar_before hv
    have hmt := htap_before j hj k
    set v₀ := (clauseLitAt φ[j] k).1
    set pvar := conflictVarSlot (clauseLitAt φ[j] k)
    obtain ⟨hgv_lt, hgv_X, hgv_nb, _⟩ :=
      hmem_step (htap_blk hj k (by simp [mem_occTapBlocks_iff]))
        (by simp : ClauseGadgetLetter.gv j k ∈ [.gv j k, .an j k])
    obtain ⟨_, _, hpvar_nb, hpvar_af⟩ :=
      hmem_step (htap_blk hj k (by simp [mem_occTapBlocks_iff, pvar]))
        (by simp : pvar ∈ [.gv j k, pvar, .qv j k, .gv j k])
    obtain ⟨_, _, hqv_nb, hqv_af⟩ :=
      hmem_step (htap_blk hj k (by simp [mem_occTapBlocks_iff]))
        (by simp : ClauseGadgetLetter.qv j k ∈ [.qv j k, .cn j k])
    set τ := stepOf Xs (.gv j k)
    have hgv_blk : [.gv j k, pvar, .qv j k, .gv j k] ∈ clauseGadgetBlocks φ :=
      htap_blk hj k (by simp [mem_occTapBlocks_iff, pvar])
    by_cases hτ_p : τ ≤ stepOf Xs pvar
    · obtain ⟨_, _, hap_nb, _⟩ :=
        hmem_step (hvar_blk hv (by simp [mem_varPosBlocks_iff]))
          (by simp : ClauseGadgetLetter.ap v₀ ∈ [.ap v₀, .px v₀])
      obtain ⟨_, _, hbp_nb, _⟩ :=
        hmem_step (hvar_blk hv (by simp [mem_varPosBlocks_iff]))
          (by simp : ClauseGadgetLetter.bp v₀ ∈ [.bp v₀, .px v₀])
      obtain ⟨_, _, hpx_nb, _⟩ :=
        hmem_step (hvar_blk hv (by simp [mem_varPosBlocks_iff]))
          (by simp : ClauseGadgetLetter.px v₀ ∈ [.ap v₀, .px v₀])
      obtain ⟨_, _, hpy_nb, _⟩ :=
        hmem_step (hvar_blk hv (by simp [mem_varPosBlocks_iff]))
          (by simp : ClauseGadgetLetter.py v₀ ∈ [.bp v₀, .py v₀])
      let B := prefUnion Xs τ
      let w := deleteLetters B (clauseGadgetPattern φ)
      have ng : ClauseGadgetLetter.gv j k ∉ B := hgv_nb τ (Nat.le_refl _)
      have np : pvar ∉ B := hpvar_nb τ hτ_p
      have na : ClauseGadgetLetter.ap v₀ ∉ B := hap_nb τ (by omega)
      have nb : ClauseGadgetLetter.bp v₀ ∉ B := hbp_nb τ (by omega)
      have npx : ClauseGadgetLetter.px v₀ ∉ B := hpx_nb τ (by omega)
      have npy : ClauseGadgetLetter.py v₀ ∉ B := hpy_nb τ (by omega)
      have p_gp : [.gv j k, pvar] <:+: w :=
        (infix_pair_guard4.mpr (Or.inr ⟨ng, Or.inl ⟨rfl, rfl, np⟩⟩)).trans
          (IsInfix.deleteLetters (blk_infix_clauseGadgetPattern φ hgv_blk) B)
      have p_ag : [.ap v₀, .gv j k] <:+: w :=
        pair2_infix_at (htap_blk hj k (by simp [mem_occTapBlocks_iff, v₀])) na ng
      have p_ax := pair2_infix_at (hvar_blk hv (by simp [mem_varPosBlocks_iff])) na npx
      have p_bx := pair2_infix_at (hvar_blk hv (by simp [mem_varPosBlocks_iff])) nb npx
      have p_by := pair2_infix_at (hvar_blk hv (by simp [mem_varPosBlocks_iff])) nb npy
      rcases conflictVarSlot_cases (clauseLitAt φ[j] k) with ⟨_, hpv⟩ | ⟨_, hpv⟩
      · rw [show pvar = .py v₀ from hpv] at p_gp
        exact hnot_self_chain τ hgv_lt (.gv j k) hgv_X
          (hasAlternatingChain_iff_reflTransGen.mpr ⟨.ap v₀,
            (Relation.ReflTransGen.single (hsr_step p_gp p_by)).tail (hsr_step p_bx p_ax), p_ag⟩)
      · rw [show pvar = .px v₀ from hpv] at p_gp
        exact hnot_self_chain τ hgv_lt (.gv j k) hgv_X
          (hasAlternatingChain_iff_reflTransGen.mpr ⟨.ap v₀,
            Relation.ReflTransGen.single (hsr_step p_gp p_ax), p_ag⟩)
    · by_cases hτ_q : τ ≤ stepOf Xs (.qv j k)
      · obtain ⟨_, _, han_nb, _⟩ :=
          hmem_step (htap_blk hj k (by simp [mem_occTapBlocks_iff]))
            (by simp : ClauseGadgetLetter.an j k ∈ [.an j k, .bn j k])
        let B := prefUnion Xs τ
        let w := deleteLetters B (clauseGadgetPattern φ)
        have ng : ClauseGadgetLetter.gv j k ∉ B := hgv_nb τ (Nat.le_refl _)
        have nq : ClauseGadgetLetter.qv j k ∉ B := hqv_nb τ hτ_q
        have na : ClauseGadgetLetter.an j k ∉ B := han_nb τ (by omega)
        have p_ga := pair2_infix_at (htap_blk hj k (by simp [mem_occTapBlocks_iff])) ng na
        have p_va := pair2_infix_at (htap_blk hj k (by simp [mem_occTapBlocks_iff])) nq na
        have p_qg : [.qv j k, .gv j k] <:+: w :=
          (infix_pair_guard4.mpr (Or.inr ⟨ng, Or.inr (Or.inl ⟨rfl, rfl, nq⟩)⟩)).trans
            (IsInfix.deleteLetters (blk_infix_clauseGadgetPattern φ hgv_blk) B)
        exact hnot_self_chain τ hgv_lt (.gv j k) hgv_X
          (hasAlternatingChain_iff_reflTransGen.mpr ⟨.qv j k,
            Relation.ReflTransGen.single (hsr_step p_ga p_va), p_qg⟩)
      · let T := max (stepOf Xs pvar) (stepOf Xs (.qv j k)) + 1
        have hT_le : T ≤ τ := by dsimp [T]; omega
        have hp_in : pvar ∈ prefUnion Xs T := hpvar_af T (by dsimp [T]; omega)
        have hq_in : ClauseGadgetLetter.qv j k ∈ prefUnion Xs T := hqv_af T (by dsimp [T]; omega)
        have hg_out : ClauseGadgetLetter.gv j k ∉ prefUnion Xs T := hgv_nb T hT_le
        have hgg : [.gv j k, .gv j k] <:+: deleteLetters (prefUnion Xs T) (clauseGadgetPattern φ) :=
          (infix_pair_guard4.mpr
            (Or.inr ⟨hg_out, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hp_in, hq_in⟩)))⟩)).trans
            (IsInfix.deleteLetters (blk_infix_clauseGadgetPattern φ hgv_blk) (prefUnion Xs T))
        exact isAvoidable_iff.mp (isAvoidable_of_pair_infix hgg) (hunav_at T (by omega))
  -- Read off the satisfying Boolean assignment from stepOf
  refine ⟨fun v ↦ decide (stepOf Xs (.px v) ≤ stepOf Xs (.py v)), ?_⟩
  rw [CNF.eval_eq_true_iff]
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  have hlen : φ[j].length = 3 := h3 φ[j] hc
  let m_orig := min (stepOf Xs (.orig j 0)) (min (stepOf Xs (.orig j 1)) (stepOf Xs (.orig j 2)))
  have hex_k : ∃ k : Fin 3, stepOf Xs (.orig j k) ≤ m_orig := by
    by_cases h01 : stepOf Xs (.orig j 0) ≤ min (stepOf Xs (.orig j 1)) (stepOf Xs (.orig j 2))
    · exact ⟨0, by dsimp [m_orig]; omega⟩
    · by_cases h12 : stepOf Xs (.orig j 1) ≤ stepOf Xs (.orig j 2)
      · exact ⟨1, by dsimp [m_orig]; omega⟩
      · exact ⟨2, by dsimp [m_orig]; omega⟩
  obtain ⟨k, hk_min⟩ := hex_k
  have hnot_qo : ¬ (stepOf Xs (.qo j k) ≤ stepOf Xs (.qv j k)) := hgo_conflict j hj k hk_min
  have hqv_le : stepOf Xs (.qv j k) ≤ stepOf Xs (.qo j k) := by omega
  have hnot_pvar := hgv_conflict j hj k hqv_le
  let lit := clauseLitAt φ[j] k
  have hlit_mem : lit ∈ φ[j] := by
    rw [show lit = clauseLitAt φ[j] k from rfl, clauseLitAt_eq_getElem hlen k]
    exact List.getElem_mem (by omega)
  rw [Clause.eval_eq_true_iff]
  refine ⟨lit, hlit_mem, ?_⟩
  rcases hlp : lit with ⟨v, pol⟩
  have hnot_pvar' : ¬ (stepOf Xs (conflictVarSlot (v, pol)) ≤
      min (stepOf Xs (.px v)) (stepOf Xs (.py v))) := by
    simpa [lit, hlp] using hnot_pvar
  cases pol
  · simp only [conflictVarSlot_mk_false] at hnot_pvar'
    have hnot : ¬ (stepOf Xs (.px v) ≤ stepOf Xs (.py v)) := by omega
    simp [hnot]
  · simp only [conflictVarSlot_mk_true] at hnot_pvar'
    have hle : stepOf Xs (.px v) ≤ stepOf Xs (.py v) := by omega
    simp [hle]

end BackwardDirection

/-- For any `3`-CNF formula `φ`, `threeCNFWord φ` is unavoidable if and only if `φ` is
satisfiable. -/
theorem isUnavoidable_threeCNFWord_iff_satisfiable {φ : CNF ℕ}
    (h3 : ∀ c ∈ φ, c.length = 3) :
    IsUnavoidable (threeCNFWord φ) ↔ φ.Satisfiable := by
  have hb3 : isExactThreeCNF φ = true := isExactThreeCNF_eq_true_iff.mpr h3
  rw [threeCNFWord_eq_map_toNat hb3]
  have hmap : IsUnavoidable ((clauseGadgetPattern φ).map ClauseGadgetLetter.toNat) ↔
      IsUnavoidable (clauseGadgetPattern φ) :=
    isUnavoidable_map_iff ClauseGadgetLetter.toNat_injective
  rw [hmap]
  exact ⟨isUnavoidable_clauseGadgetPattern_imp_satisfiable h3,
    satisfiable_imp_isUnavoidable_clauseGadgetPattern h3⟩

/-- **Exact `ExactThreeSAT` Reduction Equivalence**: for every CNF formula `φ : CNF ℕ`,
`threeCNFWord φ` is unavoidable if and only if `φ ∈ ExactThreeSAT`. -/
theorem isUnavoidable_threeCNFWord_iff_mem_ExactThreeSAT (φ : CNF ℕ) :
    IsUnavoidable (threeCNFWord φ) ↔ φ ∈ ExactThreeSAT := by
  cases hb3 : isExactThreeCNF φ
  · have hnot3 : ¬ ∀ c ∈ φ, c.length = 3 := by
      intro h3
      have ht : isExactThreeCNF φ = true := isExactThreeCNF_eq_true_iff.mpr h3
      rw [hb3] at ht; cases ht
    rw [threeCNFWord_eq_of_false hb3]
    have hav : ¬ IsUnavoidable ([0, 0] : List ℕ) :=
      isAvoidable_iff.mp (isAvoidable_of_pair_infix (x := 0) (List.infix_refl [0, 0]))
    exact ⟨fun h ↦ absurd h hav, fun h ↦ absurd h.1 hnot3⟩
  · have h3 : ∀ c ∈ φ, c.length = 3 := isExactThreeCNF_eq_true_iff.mp hb3
    exact ⟨fun h ↦ ⟨h3, (isUnavoidable_threeCNFWord_iff_satisfiable h3).mp h⟩,
      fun h ↦ (isUnavoidable_threeCNFWord_iff_satisfiable h3).mpr h.2⟩

end CslibFrontier.Complexity

end
