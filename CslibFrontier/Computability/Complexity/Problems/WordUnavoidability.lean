/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Complexity.Problems.ExactThreeSAT
public import CslibFrontier.Computability.Complexity.Problems.WordUnavoidability.GraphFree
public import CslibFrontier.Computability.Complexity.Problems.WordUnavoidability.ReductionBackward

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size

/-!
# `NP`-Completeness of Word Pattern Unavoidability

`WordUnavoidability` is the set of finite word patterns `α : List ℕ` (encoded by
`encWord := encList encNat`) that are unavoidable over every finite alphabet.

* **Membership in `NP`** (`wordUnavoidability_mem_NP`): by the Zimin–Sapir theorem, a pattern `α`
  of
  length `n` is unavoidable if and only if it reduces to `` in at most `n` free-set deletions
  `Xs : List (List ℕ)` with each `X ∈ Xs` a sublist of `α`, checked in polynomial time by
  `checkFreeSetSeq`.
* **`NP`-hardness and `NP`-completeness** (`wordUnavoidability_npHard`,
  `wordUnavoidability_npComplete`): `ExactThreeSAT` (and hence `ThreeSAT`) reduces to
  `WordUnavoidability` in polynomial time via `threeCNFWord`.

## Main definitions

* `WordUnavoidability`: decision problem `{α : List ℕ | IsUnavoidable α}`.
* `checkFreeSetSeq`: polynomial-time verifier for free-set deletion sequences.

## Main results

* `wordUnavoidability_mem_NP`: `WordUnavoidability ∈ NP encWord`.
* `polyTimeReducible_ExactThreeSAT_WordUnavoidability`: `ExactThreeSAT` reduces to
  `WordUnavoidability` in polynomial time.
* `polyTimeReducible_ThreeSAT_WordUnavoidability`: `ThreeSAT` reduces to `WordUnavoidability` in
  polynomial time.
* `wordUnavoidability_npHard`: `NPHard encWord WordUnavoidability`.
* `wordUnavoidability_npComplete`: `NPComplete encWord WordUnavoidability`.
-/

public section

namespace CslibFrontier.Complexity

open CslibFrontier.Word Cslib Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-- Decision problem of pattern unavoidability over natural-number letter indices (`List ℕ`). -/
def WordUnavoidability : Set (List ℕ) :=
  {α | IsUnavoidable α}

/-- Binary list encoding of a list of words `List (List ℕ)` (`encList encWord`). -/
abbrev encBlockList : List (List ℕ) ↪ List Bool :=
  encList encWord

private def notMemWordBool (p : List ℕ × ℕ) : Bool :=
  !(p.1.any (· == p.2))

private def stepFreeSetCheck (st : List ℕ × Bool) (X : List ℕ) : List ℕ × Bool :=
  (st.1.filter (fun a ↦ notMemWordBool (X, a)), st.2 && isFreeSetBool (st.1, X))

/-- Polynomial-time certificate checker for a candidate free-set deletion sequence
`Xs : List (List ℕ)` on pattern `α : List ℕ`. -/
def checkFreeSetSeq (inp : List ℕ × List (List ℕ)) : Bool :=
  let res := inp.2.foldl stepFreeSetCheck (inp.1, true)
  res.1.isEmpty && res.2

private theorem sublist_foldl_stepFreeSetCheck :
    ∀ (Xs : List (List ℕ)) (w : List ℕ) (ok : Bool),
      List.Sublist (Xs.foldl stepFreeSetCheck (w, ok)).1 w
  | [], _, _ => List.Sublist.refl _
  | _ :: Xs, _, _ =>
    (sublist_foldl_stepFreeSetCheck Xs _ _).trans (List.filter_sublist)

private theorem computableInPolyTime_stepFreeSetCheck :
    ComputableInPolyTime (fun p : (List ℕ × Bool) × List ℕ ↦ stepFreeSetCheck p.1 p.2)
      (encPair (encPair encWord encBool) encWord) (encPair encWord encBool) := by
  let encSt := encPair encWord encBool
  let encIn := encPair encSt encWord
  have hst : ComputableInPolyTime (fun p : (List ℕ × Bool) × List ℕ ↦ p.1) encIn encSt :=
    fst _ _
  have hw : ComputableInPolyTime (fun p : (List ℕ × Bool) × List ℕ ↦ p.1.1) encIn encWord :=
    (fst encWord encBool).comp hst
  have hok : ComputableInPolyTime (fun p : (List ℕ × Bool) × List ℕ ↦ p.1.2) encIn encBool :=
    (snd encWord encBool).comp hst
  have hX : ComputableInPolyTime (fun p : (List ℕ × Bool) × List ℕ ↦ p.2) encIn encWord :=
    snd _ _
  have hnotMem : ComputableInPolyTime notMemWordBool (encPair encWord encNat) encBool := by
    unfold notMemWordBool
    fun_prop
  have hw' : ComputableInPolyTime
      (fun p : (List ℕ × Bool) × List ℕ ↦ p.1.1.filter (fun a ↦ notMemWordBool (p.2, a)))
      encIn encWord :=
    filterWith hnotMem hX hw
  have hok' : ComputableInPolyTime
      (fun p : (List ℕ × Bool) × List ℕ ↦ p.1.2 && isFreeSetBool (p.1.1, p.2))
      encIn encBool :=
    bool_and' hok (computableInPolyTime_isFreeSetBool.comp (hw.prod hX))
  exact hw'.prod hok'

/-- `checkFreeSetSeq` runs in polynomial time on multi-tape Turing machines. -/
@[fun_prop]
theorem computableInPolyTime_checkFreeSetSeq :
    ComputableInPolyTime checkFreeSetSeq (encPair encWord encBlockList) encBool := by
  let encSt := encPair encWord encBool
  let encIn := encPair encWord encBlockList
  have hlist : ComputableInPolyTime (fun inp : List ℕ × List (List ℕ) ↦ inp.2)
      encIn encBlockList := snd _ _
  have hinit : ComputableInPolyTime (fun inp : List ℕ × List (List ℕ) ↦ (inp.1, true))
      encIn encSt := (fst encWord encBlockList).prod (const true)
  have hB : PolyBounded (fun inp : List ℕ × List (List ℕ) ↦ (encIn inp).length)
      (fun inp ↦ 2 * (encIn inp).length + 2) :=
    PolyBounded.of_forall_le 2 1 (fun _ ↦ by simp only [pow_one]; omega)
  have hfold : ComputableInPolyTime
      (fun inp : List ℕ × List (List ℕ) ↦ inp.2.foldl stepFreeSetCheck (inp.1, true))
      encIn encSt := by
    refine foldl' hlist hinit computableInPolyTime_stepFreeSetCheck hB ?_
    intro inp i _
    have hsub := sublist_foldl_stepFreeSetCheck (inp.2.take i) inp.1 true
    have hlen_w : (encWord ((inp.2.take i).foldl stepFreeSetCheck (inp.1, true)).1).length ≤
        (encWord inp.1).length :=
      length_encList_sublist encNat hsub
    have hpair_inp : (encWord inp.1).length ≤ (encIn inp).length := by
      simp only [encIn, length_encPair]
      omega
    simp only [encSt, length_encPair, encBool_apply, List.length_singleton]
    omega
  exact bool_and' ((listIsEmpty' encNat).comp ((fst encWord encBool).comp hfold))
    ((snd encWord encBool).comp hfold)

private theorem foldl_stepFreeSetCheck_false :
    ∀ (Xs : List (List ℕ)) (w : List ℕ),
      (Xs.foldl stepFreeSetCheck (w, false)).2 = false
  | [], _ => rfl
  | X :: Xs, w => by
    simp only [List.foldl_cons, stepFreeSetCheck, Bool.false_and]
    exact foldl_stepFreeSetCheck_false Xs _

private theorem filter_notMemWordBool_eq_deleteLetters (X w : List ℕ) :
    w.filter (fun a ↦ notMemWordBool (X, a)) =
      CslibFrontier.Word.deleteLetters {x : ℕ | x ∈ X} w := by
  classical
  rw [CslibFrontier.Word.deleteLetters_eq_filter]
  apply List.filter_congr
  intro a _
  rw [Bool.eq_iff_iff]
  simp only [notMemWordBool, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    List.any_eq_true, beq_iff_eq, decide_eq_true_eq, Set.mem_ofPred_eq]
  exact ⟨fun h ha ↦ h ⟨a, ha, rfl⟩, fun h ⟨x, hx, hxa⟩ ↦ h (hxa ▸ hx)⟩

private theorem checkFreeSetSeq_sound :
    ∀ (Xs : List (List ℕ)) (w : List ℕ),
      checkFreeSetSeq (w, Xs) = true → IsUnavoidable w
  | [], w, h => by
    simp only [checkFreeSetSeq, List.foldl_nil, Bool.and_true, List.isEmpty_iff] at h
    subst h
    exact isUnavoidable_nil
  | X :: Xs, w, h => by
    simp only [checkFreeSetSeq, List.foldl_cons, stepFreeSetCheck, Bool.true_and] at h
    cases hfs : isFreeSetBool (w, X)
    · rw [hfs, foldl_stepFreeSetCheck_false, Bool.and_false] at h
      cases h
    · rw [hfs] at h
      have hrec : IsUnavoidable (w.filter (fun a ↦ notMemWordBool (X, a))) :=
        checkFreeSetSeq_sound Xs _ h
      rw [filter_notMemWordBool_eq_deleteLetters] at hrec
      have hfree : IsFreeSet w {x : ℕ | x ∈ X} := (isFreeSetBool_eq_true_iff w X).mp hfs
      exact hfree.isUnavoidable_of_deleteLetters hrec

private theorem length_deleteLetters_lt_of_mem {S : Set ℕ} {w : List ℕ} {a₀ : ℕ}
    (ha₀w : a₀ ∈ w) (ha₀S : a₀ ∈ S) :
    (CslibFrontier.Word.deleteLetters S w).length < w.length := by
  rcases List.append_of_mem ha₀w with ⟨s₁, s₂, rfl⟩
  rw [CslibFrontier.Word.deleteLetters_append, CslibFrontier.Word.deleteLetters_cons_of_mem ha₀S]
  have h₁ := CslibFrontier.Word.length_deleteLetters_le S s₁
  have h₂ := CslibFrontier.Word.length_deleteLetters_le S s₂
  simp only [List.length_append, List.length_cons]
  omega

private theorem sublist_deleteLetters (S : Set ℕ) (w : List ℕ) :
    List.Sublist (CslibFrontier.Word.deleteLetters S w) w := by
  classical
  rw [CslibFrontier.Word.deleteLetters_eq_filter]
  exact List.filter_sublist

private theorem exists_short_checkFreeSetSeq {w : List ℕ} (hw : IsUnavoidable w) :
    ∃ Xs : List (List ℕ),
      checkFreeSetSeq (w, Xs) = true ∧
      Xs.length ≤ w.length ∧
      ∀ X ∈ Xs, List.Sublist X w := by
  have hfs := isUnavoidable_iff_isFreeSetReducible.mp hw
  clear hw
  induction hfs with
  | nil =>
    exact ⟨[], rfl, Nat.le_refl _, fun _ h ↦ False.elim (List.not_mem_nil h)⟩
  | @delete_freeSet u S hS _ ih =>
    classical
    by_cases hex : ∃ a₀ ∈ u, a₀ ∈ S
    · rcases hex with ⟨a₀, ha₀u, ha₀S⟩
      obtain ⟨Xs', hchk', hlen', hsub'⟩ := ih
      let X : List ℕ := u.filter (fun a ↦ decide (a ∈ S))
      have hX_sub_u : List.Sublist X u := List.filter_sublist
      have hX_set_sub : {x : ℕ | x ∈ X} ⊆ S := by
        intro x hx
        simp only [Set.mem_ofPred_eq, X, List.mem_filter, decide_eq_true_eq] at hx
        exact hx.2
      have hX_free : isFreeSetBool (u, X) = true :=
        (isFreeSetBool_eq_true_iff u X).mpr (hS.mono hX_set_sub)
      have hdel_eq : u.filter (fun a ↦ notMemWordBool (X, a)) =
          CslibFrontier.Word.deleteLetters S u := by
        rw [CslibFrontier.Word.deleteLetters_eq_filter]
        have haux : ∀ l : List ℕ, (∀ a ∈ l, a ∈ u) →
            l.filter (fun a ↦ notMemWordBool (X, a)) =
              l.filter (fun a ↦ !decide (a ∈ S)) := by
          intro l hl
          induction l with
          | nil => rfl
          | cons a as ihl =>
            have hau : a ∈ u := hl a (List.mem_cons_self)
            have heq_b : notMemWordBool (X, a) = !decide (a ∈ S) := by
              rw [Bool.eq_iff_iff]
              simp only [notMemWordBool, X, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
                List.any_eq_true, List.mem_filter, decide_eq_true_eq, beq_iff_eq]
              exact ⟨fun h haS ↦ h ⟨a, ⟨hau, haS⟩, rfl⟩,
                fun h ⟨x, ⟨_, hxS⟩, hxa⟩ ↦ h (hxa ▸ hxS)⟩
            simp only [List.filter_cons, heq_b, ihl (fun b hb ↦ hl b (List.mem_cons_of_mem _ hb))]
        exact haux u (fun _ ha ↦ ha)
      have hlt : (CslibFrontier.Word.deleteLetters S u).length < u.length :=
        length_deleteLetters_lt_of_mem ha₀u ha₀S
      refine ⟨X :: Xs', ?_, ?_, ?_⟩
      · simp only [checkFreeSetSeq, List.foldl_cons, stepFreeSetCheck, Bool.true_and, hX_free,
          hdel_eq]
        exact hchk'
      · simp only [List.length_cons]
        omega
      · intro Y hY
        rcases List.mem_cons.mp hY with rfl | hYs
        · exact hX_sub_u
        · exact (hsub' Y hYs).trans (sublist_deleteLetters S u)
    · push Not at hex
      have heq : CslibFrontier.Word.deleteLetters S u = u :=
        CslibFrontier.Word.deleteLetters_eq_self hex
      rwa [heq] at ih

/-- `WordUnavoidability` belongs to `NP` (`NP encWord`). -/
theorem wordUnavoidability_mem_NP : WordUnavoidability ∈ NP encWord := by
  refine mem_NP_of_check (Decoder.list (Decoder.list Decoder.nat))
    (p := 2 * Polynomial.X ^ 2 + Polynomial.X)
    computableInPolyTime_checkFreeSetSeq
    (fun α Xs h ↦ checkFreeSetSeq_sound Xs α h) ?_
  intro α hα
  obtain ⟨Xs, hchk, hlen_Xs, hsub⟩ := exists_short_checkFreeSetSeq hα
  refine ⟨Xs, hchk, ?_⟩
  let n := (encWord α).length
  have hb : ∀ X ∈ Xs, (encWord X).length ≤ n := fun X hX ↦
    length_encList_sublist encNat (hsub X hX)
  have h1 : (encBlockList Xs).length ≤ Xs.length * (2 * n + 1) :=
    length_encList_le encWord Xs hb
  have h2 : Xs.length ≤ n := hlen_Xs.trans (SizedListEncoding.length_le (encA := encNat) α)
  have h3 : Xs.length * (2 * n + 1) ≤ n * (2 * n + 1) :=
    Nat.mul_le_mul_right (2 * n + 1) h2
  have heval : (2 * Polynomial.X ^ 2 + Polynomial.X : Polynomial ℕ).eval n = n * (2 * n + 1) := by
    simp [pow_two]
    ring
  rw [heval]
  exact h1.trans h3

/-- `ExactThreeSAT` reduces to `WordUnavoidability` in polynomial time via `threeCNFWord`. -/
theorem polyTimeReducible_ExactThreeSAT_WordUnavoidability :
    PolyTimeReducible encCNF encWord ExactThreeSAT WordUnavoidability :=
  ⟨threeCNFWord, computableInPolyTime_threeCNFWord,
    fun φ ↦ (isUnavoidable_threeCNFWord_iff_mem_ExactThreeSAT φ).symm⟩

/-- `ThreeSAT` reduces to `WordUnavoidability` in polynomial time. -/
theorem polyTimeReducible_ThreeSAT_WordUnavoidability :
    PolyTimeReducible encCNF encWord ThreeSAT WordUnavoidability :=
  polyTimeReducible_ThreeSAT_ExactThreeSAT.trans polyTimeReducible_ExactThreeSAT_WordUnavoidability

/-- `WordUnavoidability` is `NP`-hard (`NPHard encWord WordUnavoidability`). -/
theorem wordUnavoidability_npHard : NPHard encWord WordUnavoidability :=
  ExactThreeSAT_npHard.trans polyTimeReducible_ExactThreeSAT_WordUnavoidability

/-- Deciding whether a finite word pattern is unavoidable is `NP`-complete
(`NPComplete encWord WordUnavoidability`). -/
theorem wordUnavoidability_npComplete : NPComplete encWord WordUnavoidability :=
  ⟨wordUnavoidability_mem_NP, wordUnavoidability_npHard⟩

/-- Non-vacuity positive instance: the Zimin word `Z_2 = [0, 1, 0]` lies in
`WordUnavoidability`. -/
theorem mem_wordUnavoidability_witness : ([0, 1, 0] : List ℕ) ∈ WordUnavoidability := by
  have hz : CslibFrontier.Word.ziminWord 2 = [0, 1, 0] := by
    have h2 : (2 : ℕ) = 0 + 1 + 1 := rfl
    rw [h2, CslibFrontier.Word.ziminWord_succ, CslibFrontier.Word.ziminWord_succ,
      CslibFrontier.Word.ziminWord_zero]
    rfl
  rw [WordUnavoidability, Set.mem_ofPred_eq, ← hz]
  exact CslibFrontier.Word.isUnavoidable_ziminWord 2

/-- Non-vacuity negative instance: the square pattern `[0, 0]` is avoidable
(`[0, 0] ∉ WordUnavoidability`). -/
theorem not_mem_wordUnavoidability_witness : ([0, 0] : List ℕ) ∉ WordUnavoidability :=
  isAvoidable_iff.mp (isAvoidable_of_pair_infix (x := 0) (List.infix_refl [0, 0]))

end CslibFrontier.Complexity

end
