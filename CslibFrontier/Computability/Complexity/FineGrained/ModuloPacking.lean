/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.ModulusSelection
public import CslibFrontier.Computability.Complexity.FineGrained.ResidueHeavy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Linarith

/-!
# Single-Array Modulo Packing on Multi-Tape Turing Machines

This module constructs a deterministic multi-tape Turing machine algorithm with explicit
`ComputableInO` bounds for the single-array modulo packing `oneArrayList U N M L₁ L₂ L₃` of Chan and
He's 3SUM-to-Convolution-3SUM reduction, materializing the four-way interleaved
convolution array `Node.oneArray` of length `4 * N` in positive natural numbers via LSD binary radix
sort and single-pass run grouping.

## Main definitions

* `CslibFrontier.Complexity.packCellInt`,
  `CslibFrontier.Complexity.packCellNat`: signed and natural-number
  cell values of `Node.oneArray` at index `u` from bucket count `cnt` and representative `val`.
* `CslibFrontier.Complexity.oneArrayList`: materializes the single-array convolution instance of
  length
  `4 * N` in `List ℕ`.
* `CslibFrontier.Complexity.PackInput`, `CslibFrontier.Complexity.encPackInput`,
  `CslibFrontier.Complexity.packLen`,
  `CslibFrontier.Complexity.packScale`: input tuple, encoding, work
  length, and bit-scale parameter for `oneArrayList`.

## Main results

* `CslibFrontier.Complexity.oneArrayList_zero_len`, `CslibFrontier.Complexity.length_oneArrayList`,
  `CslibFrontier.Complexity.oneArrayList_eq_ofFn`: `@[simp]` zero-length identity, exact length `4
  * N`,
  and exact agreement with `Node.oneArray`.
* `CslibFrontier.Complexity.oneArrayList_pos_and_le`,
  `CslibFrontier.Complexity.oneArrayList_conv_iff`:
  strict positivity, upper bound `60 * U + 40`, and equivalence of additive solutions with
  `Convolution (4 * N)` under `Bdd U`.
* `CslibFrontier.Complexity.packLen_le`,
  `CslibFrontier.Complexity.packScale_le`: componentwise upper bounds.
* `CslibFrontier.Complexity.computableInO_oneArrayList`: quasi-linear Turing machine time and
  space bound
  `O(packLen x * packScale x ^ d)`.
-/

public section

namespace CslibFrontier.Complexity

open Turing Turing.MultiTapeTM
open Cslib.Algorithms.ThreeSum
open Cslib.Algorithms.ThreeSum.ChanHe

private theorem length_encNat (n : ℕ) : (encNat n).length = n.size := by
  rw [encNat_apply, Nat.size_eq_bits_len]

private theorem size_le_self (k : ℕ) : k.size ≤ k :=
  Nat.size_le.mpr k.lt_two_pow_self

private theorem head?_dropWhile_not {α : Type*} (p : α → Bool) :
    ∀ (l : List α) {b : α}, (l.dropWhile p).head? = some b → ¬ p b = true
  | [], _, h => by simp at h
  | a :: as, b, h => by
    rw [List.dropWhile_cons] at h
    split_ifs at h with hp
    · exact head?_dropWhile_not p as h
    · simp only [List.head?_cons, Option.some.injEq] at h
      rwa [← h]

private theorem size_four_mul_le (n : ℕ) : (4 * n).size ≤ n.size + 2 :=
  Nat.size_le.mpr (by have := Nat.lt_size_self n; rw [Nat.pow_add]; omega)

private theorem size_four_mul_succ_le (n : ℕ) : (4 * n + 1).size ≤ n.size + 3 :=
  Nat.size_le.mpr (by have := Nat.lt_size_self n; rw [Nat.pow_add]; omega)

private theorem foldl_const {α σ : Type*} (s : σ) : ∀ l : List α, l.foldl (fun a _ => a) s = s
  | [] => rfl
  | _ :: as => foldl_const s as

private theorem length_flatMap_le_mul {α β : Type*} (f : α → List β) (k : ℕ)
    (hf : ∀ a, (f a).length ≤ k) : ∀ l : List α, (l.flatMap f).length ≤ k * l.length
  | [] => by simp
  | a :: as => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
    have := hf a; have := length_flatMap_le_mul f k hf as; omega

attribute [local irreducible] encNat encIntBin encUnary

/-- Signed cell value of `Node.oneArray` at index `u` from bucket count `cnt` and representative
`val`. -/
def packCellInt (U u cnt : ℕ) (val : ℤ) : ℤ :=
  let W : ℤ := 2 * (U : ℤ) + 1
  let G : ℤ := 3 * W + 1
  if u % 4 = 1 then (if cnt = 1 then val else W) + G
  else if u % 4 = 2 then (if cnt = 1 then val else W) + 3 * G
  else if u % 4 = 3 then (if cnt = 1 then val else -W) + 4 * G
  else 10 * G

/-- Truncated natural-number cell value `(packCellInt U u cnt val).toNat`. -/
def packCellNat (U u cnt : ℕ) (val : ℤ) : ℕ :=
  (packCellInt U u cnt val).toNat

private def accStep (cv : ℕ × ℤ) (o : Option ℤ) : ℕ × ℤ :=
  if o.isSome then (if decide (cv.1 + 1 ≤ 2) then cv.1 + 1 else 2, o.getD 0) else cv

private abbrev PackState := (ℕ × ℕ) × (ℕ × ℤ)

private def encPackState : PackState ↪ List Bool :=
  encPair (encPair encNat encNat) (encPair encNat encIntBin)

private abbrev TagItem := ℕ × Option ℤ

private def encTagItem : TagItem ↪ List Bool :=
  encPair encNat (encOption encIntBin)

private def packNext (p : PackState × TagItem) : PackState :=
  if decide (p.2.1 = p.1.1.2) then ((p.1.1.1, p.1.1.2), accStep p.1.2 p.2.2)
  else ((p.1.1.1, p.2.1), accStep (0, 0) p.2.2)

private def packEmit (p : PackState × TagItem) : List ℕ :=
  if decide (p.2.1 = p.1.1.2) then []
  else [packCellNat p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2]

private def emitTag₁ (q : (ℕ × ℕ) × ℤ) : List TagItem :=
  if decide (4 * intRemNat q.1.2 q.2 + 1 < 4 * q.1.1) then
    [(4 * intRemNat q.1.2 q.2 + 1, some q.2)]
  else []

private def emitTag₂ (q : (ℕ × ℕ) × ℤ) : List TagItem :=
  if decide (4 * intRemNat q.1.2 q.2 + 2 < 4 * q.1.1) then
    [(4 * intRemNat q.1.2 q.2 + 2, some q.2)]
  else []

private def emitTag₃ (q : (ℕ × ℕ) × ℤ) : List TagItem :=
  (if decide (4 * intRemNat q.1.2 (-q.2) + 3 < 4 * q.1.1) then
      [(4 * intRemNat q.1.2 (-q.2) + 3, some (-q.2))] else []) ++
    (if decide (4 * (intRemNat q.1.2 (-q.2) + q.1.2) + 3 < 4 * q.1.1) then
      [(4 * (intRemNat q.1.2 (-q.2) + q.1.2) + 3, some (-q.2))] else [])

private def rawTagItems (N M : ℕ) (L₁ L₂ L₃ : List ℤ) : List TagItem :=
  (fastRange (4 * N + 1)).map (fun u => (u, (none : Option ℤ))) ++
    (streamList Prod.fst emitTag₁ (N, M) L₁ ++
      (streamList Prod.fst emitTag₂ (N, M) L₂ ++
        streamList Prod.fst emitTag₃ (N, M) L₃))

/-- Materializes the packed single-array convolution instance of length `4 * N` in `List ℕ`. -/
def oneArrayList (U N M : ℕ) (L₁ L₂ L₃ : List ℤ) : List ℕ :=
  let sorted := radixSortBy Prod.fst (4 * N).size (rawTagItems N M L₁ L₂ L₃)
  streamList packNext packEmit ((U, 0), (0, 0)) sorted

private theorem streamList_emitTag_eq_flatMap (emit : (ℕ × ℕ) × ℤ → List TagItem) (s : ℕ × ℕ)
    (L : List ℤ) :
    streamList Prod.fst emit s L = L.flatMap (fun x => emit (s, x)) := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp [streamList_cons, ih]

private theorem rawTagItems_keys_le (N M : ℕ) (L₁ L₂ L₃ : List ℤ) :
    ∀ a ∈ rawTagItems N M L₁ L₂ L₃, a.1 ≤ 4 * N := by
  intro a ha
  unfold rawTagItems at ha
  rw [fastRange_eq_range, streamList_emitTag_eq_flatMap, streamList_emitTag_eq_flatMap,
    streamList_emitTag_eq_flatMap] at ha
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap] at ha
  rcases ha with ⟨u, hu, rfl⟩ | ⟨x, _, hx⟩ | ⟨y, _, hy⟩ | ⟨z, _, hz⟩
  · omega
  · unfold emitTag₁ at hx; dsimp only at hx; split_ifs at hx with h
    · rw [List.mem_singleton.mp hx]; have := of_decide_eq_true h; omega
    · cases hx
  · unfold emitTag₂ at hy; dsimp only at hy; split_ifs at hy with h
    · rw [List.mem_singleton.mp hy]; have := of_decide_eq_true h; omega
    · cases hy
  · unfold emitTag₃ at hz; dsimp only at hz
    rcases List.mem_append.mp hz with h1 | h2
    · split_ifs at h1 with h
      · rw [List.mem_singleton.mp h1]; have := of_decide_eq_true h; omega
      · cases h1
    · split_ifs at h2 with h
      · rw [List.mem_singleton.mp h2]; have := of_decide_eq_true h; omega
      · cases h2

private theorem mem_none_rawTagItems {N M : ℕ} {L₁ L₂ L₃ : List ℤ} {u : ℕ} (hu : u ≤ 4 * N) :
    (u, (none : Option ℤ)) ∈ rawTagItems N M L₁ L₂ L₃ := by
  unfold rawTagItems
  rw [fastRange_eq_range]
  exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_range.mpr (by omega)))

private theorem streamList_pack_same {same rest : List TagItem} {U cur : ℕ} (cv : ℕ × ℤ)
    (hsame : ∀ a ∈ same, a.1 = cur) :
    streamList packNext packEmit ((U, cur), cv) (same ++ rest) =
      streamList packNext packEmit ((U, cur), same.foldl (fun s a => accStep s a.2) cv) rest := by
  induction same generalizing cv with
  | nil => rfl
  | cons a as ih =>
    have ha : a.1 = cur := hsame a (List.mem_cons_self ..)
    have has : ∀ x ∈ as, x.1 = cur := fun x hx => hsame x (List.mem_cons_of_mem _ hx)
    simp only [List.cons_append, streamList_cons, packEmit, ha, decide_true, ↓reduceIte,
      List.nil_append, packNext, List.foldl_cons]
    exact ih _ has

private theorem streamList_pack_groups {K : ℕ} :
    ∀ d cur (S : List TagItem) (U : ℕ), cur ≤ K → K - cur = d →
      S.Pairwise (fun a b => a.1 ≤ b.1) →
      (∀ a ∈ S, cur ≤ a.1 ∧ a.1 ≤ K) →
      (∀ u, cur < u → u ≤ K → ∃ a ∈ S, a.1 = u) →
      streamList packNext packEmit ((U, cur), (0, 0)) S =
        ((List.range (K - cur)).map fun i =>
          let u := cur + i
          let grp := S.filter (fun a => decide (a.1 = u))
          let cv := grp.foldl (fun s a => accStep s a.2) (0, 0)
          packCellNat U u cv.1 cv.2) := by
  intro d
  induction d with
  | zero =>
    intro cur S U hle hd _ hbounds _
    have hK : cur = K := by omega
    subst hK
    have hsame : ∀ a ∈ S, a.1 = cur := fun a ha => by have := hbounds a ha; omega
    have h := streamList_pack_same (same := S) (rest := []) (U := U) (0, 0) hsame
    rw [List.append_nil] at h
    rw [h, streamList_nil, Nat.sub_self, List.range_zero, List.map_nil]
  | succ d ih =>
    intro cur S U hle hd hsort hbounds hexists
    have hlt : cur < K := by omega
    let pred : TagItem → Bool := fun a => decide (a.1 = cur)
    let same := S.takeWhile pred
    let rest := S.dropWhile pred
    have hS_eq : same ++ rest = S := List.takeWhile_append_dropWhile
    have hsame_key : ∀ a ∈ same, a.1 = cur := fun a ha =>
      of_decide_eq_true (List.mem_takeWhile_imp (p := pred) ha)
    have hrest_bounds : ∀ a ∈ rest, cur + 1 ≤ a.1 ∧ a.1 ≤ K := by
      cases hdw : rest with
      | nil => simp
      | cons b bs =>
        have hb_not : ¬ pred b = true := by
          have hhead : (S.dropWhile pred).head? = some b := by change rest.head? = _; rw [hdw]; rfl
          exact head?_dropWhile_not pred S hhead
        have hb_ne : b.1 ≠ cur := by simpa [pred] using hb_not
        have hb_S : b ∈ S := by
          rw [← hS_eq, hdw]; exact List.mem_append_right _ (List.mem_cons_self ..)
        have hb_gt : cur + 1 ≤ b.1 := by have := (hbounds b hb_S).1; omega
        have hsort_rest : rest.Pairwise (fun u v => u.1 ≤ v.1) := by
          rw [← hS_eq] at hsort
          exact (List.pairwise_append.mp hsort).2.1
        rw [hdw] at hsort_rest
        have hbs_ge := (List.pairwise_cons.mp hsort_rest).1
        intro a ha
        have ha_S : a ∈ S := by
          rw [← hS_eq, hdw]; exact List.mem_append_right _ ha
        rcases List.mem_cons.mp ha with rfl | habs
        · exact ⟨hb_gt, (hbounds a hb_S).2⟩
        · exact ⟨hb_gt.trans (hbs_ge a habs), (hbounds a ha_S).2⟩
    obtain ⟨b0, hb0_S, hb0_key⟩ := hexists (cur + 1) (by omega) hlt
    have hb0_rest : b0 ∈ rest := by
      rw [← hS_eq] at hb0_S
      rcases List.mem_append.mp hb0_S with hb0_same | hb0_r
      · exfalso; have := hsame_key b0 hb0_same; omega
      · exact hb0_r
    obtain ⟨b, bs, hrest_cons⟩ : ∃ b bs, rest = b :: bs := by
      cases hdw : rest with
      | nil => rw [hdw] at hb0_rest; simp at hb0_rest
      | cons b bs => exact ⟨b, bs, rfl⟩
    have hsort_rest : rest.Pairwise (fun u v => u.1 ≤ v.1) := by
      rw [← hS_eq] at hsort
      exact (List.pairwise_append.mp hsort).2.1
    have hb_key : b.1 = cur + 1 := by
      have hb_ge := (hrest_bounds b (by rw [hrest_cons]; exact List.mem_cons_self ..)).1
      rw [hrest_cons] at hsort_rest hb0_rest
      rcases List.mem_cons.mp hb0_rest with rfl | hb0_bs
      · exact hb0_key
      · have hle_b0 := (List.pairwise_cons.mp hsort_rest).1 b0 hb0_bs
        omega
    have hfilter_cur : S.filter (fun a => decide (a.1 = cur)) = same := by
      rw [← hS_eq, List.filter_append]
      have h1 : same.filter (fun a => decide (a.1 = cur)) = same :=
        List.filter_eq_self.mpr fun a ha => decide_eq_true (hsame_key a ha)
      have h2 : rest.filter (fun a => decide (a.1 = cur)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        have := (hrest_bounds a ha).1
        simp; omega
      rw [h1, h2, List.append_nil]
    have hfilter_gt : ∀ u, cur + 1 ≤ u →
        S.filter (fun a => decide (a.1 = u)) = rest.filter (fun a => decide (a.1 = u)) := by
      intro u hu
      rw [← hS_eq, List.filter_append]
      have h1 : same.filter (fun a => decide (a.1 = u)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        have := hsame_key a ha
        simp; omega
      rw [h1, List.nil_append]
    rw [← hS_eq, streamList_pack_same (0, 0) hsame_key, hS_eq]
    have hstep_head :
        streamList packNext packEmit
          ((U, cur), same.foldl (fun s a => accStep s a.2) (0, 0)) rest =
        packCellNat U cur (same.foldl (fun s a => accStep s a.2) (0, 0)).1
            (same.foldl (fun s a => accStep s a.2) (0, 0)).2 ::
          streamList packNext packEmit ((U, cur + 1), (0, 0)) rest := by
      rw [hrest_cons, streamList_cons]
      conv_rhs => rw [streamList_cons]
      have hcne : decide (cur + 1 = cur) = false := decide_eq_false (by omega)
      simp only [packEmit, packNext, hb_key, hcne, decide_true, Bool.false_eq_true, ↓reduceIte,
        List.cons_append, List.nil_append]
    rw [hstep_head]
    have hrest_ex : ∀ u, cur + 1 < u → u ≤ K → ∃ a ∈ rest, a.1 = u := by
      intro u hu1 huK
      obtain ⟨a, haS, hak⟩ := hexists u (by omega) huK
      rw [← hS_eq] at haS
      rcases List.mem_append.mp haS with has | har
      · exfalso; have := hsame_key a has; omega
      · exact ⟨a, har, hak⟩
    rw [ih (cur + 1) rest U (by omega) (by omega) hsort_rest hrest_bounds hrest_ex]
    have hrng : K - cur = (K - (cur + 1)) + 1 := by omega
    rw [hrng, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.add_zero, hfilter_cur]
    congr 1
    apply List.map_congr_left
    intro i _
    dsimp only [Function.comp_apply]
    have heq_u : cur + (i + 1) = cur + 1 + i := by omega
    rw [heq_u, hfilter_gt (cur + 1 + i) (by omega)]

@[simp]
theorem oneArrayList_zero_len (U M : ℕ) (L₁ L₂ L₃ : List ℤ) :
    oneArrayList U 0 M L₁ L₂ L₃ = [] := by
  unfold oneArrayList
  let S := radixSortBy Prod.fst (4 * 0).size (rawTagItems 0 M L₁ L₂ L₃)
  have hperm := radixSortBy_perm Prod.fst (4 * 0).size (rawTagItems 0 M L₁ L₂ L₃)
  have hsort : S.Pairwise (fun a b => a.1 ≤ b.1) := by
    refine pairwise_radixSortBy Prod.fst (4 * 0).size fun a ha => ?_
    have hk := rawTagItems_keys_le 0 M L₁ L₂ L₃ a ha
    have hlt := Nat.lt_size_self (4 * 0)
    omega
  have hbnd : ∀ a ∈ S, 0 ≤ a.1 ∧ a.1 ≤ 0 := fun a ha =>
    ⟨Nat.zero_le _, rawTagItems_keys_le 0 M L₁ L₂ L₃ a (hperm.mem_iff.mp ha)⟩
  change streamList packNext packEmit ((U, 0), (0, 0)) S = []
  rw [streamList_pack_groups (K := 0) 0 0 S U le_rfl rfl hsort hbnd
    (fun _ h1 _ => absurd h1 (by omega))]
  simp

theorem length_oneArrayList (U N M : ℕ) (L₁ L₂ L₃ : List ℤ) :
    (oneArrayList U N M L₁ L₂ L₃).length = 4 * N := by
  unfold oneArrayList
  let S := radixSortBy Prod.fst (4 * N).size (rawTagItems N M L₁ L₂ L₃)
  have hperm := radixSortBy_perm Prod.fst (4 * N).size (rawTagItems N M L₁ L₂ L₃)
  have hsort : S.Pairwise (fun a b => a.1 ≤ b.1) := by
    refine pairwise_radixSortBy Prod.fst (4 * N).size fun a ha => ?_
    exact (rawTagItems_keys_le N M L₁ L₂ L₃ a ha).trans_lt (Nat.lt_size_self (4 * N))
  have hbnd : ∀ a ∈ S, 0 ≤ a.1 ∧ a.1 ≤ 4 * N := fun a ha =>
    ⟨Nat.zero_le _, rawTagItems_keys_le N M L₁ L₂ L₃ a (hperm.mem_iff.mp ha)⟩
  have hex : ∀ u, 0 < u → u ≤ 4 * N → ∃ a ∈ S, a.1 = u := fun u _ hu =>
    ⟨(u, none), hperm.mem_iff.mpr (mem_none_rawTagItems hu), rfl⟩
  change (streamList packNext packEmit ((U, 0), (0, 0)) S).length = 4 * N
  rw [streamList_pack_groups (K := 4 * N) (4 * N) 0 S U (Nat.zero_le _) (Nat.sub_zero _)
    hsort hbnd hex, List.length_map, List.length_range, Nat.sub_zero]

private theorem foldl_accStep_count_and_unique (grp : List TagItem) :
    let someVals := grp.filterMap Prod.snd
    let cv := grp.foldl (fun s a => accStep s a.2) (0, 0)
    cv.1 = min someVals.length 2 ∧ (someVals.length = 1 → someVals = [cv.2]) := by
  suffices ∀ (g : List TagItem) (c : ℕ) (v : ℤ),
      c ≤ 2 →
      let sv := g.filterMap Prod.snd
      let cv := g.foldl (fun s a => accStep s a.2) (c, v)
      cv.1 = min (c + sv.length) 2 ∧
        (c = 0 → sv.length = 1 → sv = [cv.2]) ∧
        (c = 1 → sv = [] → cv.2 = v) from by
    obtain ⟨h1, h2, _⟩ := this grp 0 0 (by omega)
    exact ⟨by simpa using h1, h2 rfl⟩
  intro g
  induction g with
  | nil =>
    intro c v hc; dsimp only
    simp only [List.filterMap_nil, List.length_nil, Nat.add_zero, List.foldl_nil]
    exact ⟨by omega, by simp, by simp⟩
  | cons a gs ih =>
    intro c v hc; dsimp only
    rcases a with ⟨u, _ | w⟩
    · rw [List.filterMap_cons_none rfl, List.foldl_cons]
      exact ih c v hc
    · rw [show ((u, some w) :: gs).filterMap Prod.snd = w :: gs.filterMap Prod.snd from rfl,
        List.length_cons, List.foldl_cons]
      set c' := if decide (c + 1 ≤ 2) then c + 1 else 2
      have hacc : accStep (c, v) (some w) = (c', w) := rfl
      rw [hacc]
      have hc' : c' = min (c + 1) 2 := by
        dsimp only [c']; split_ifs with h <;> simp only [decide_eq_true_eq] at h <;> omega
      obtain ⟨h1, _, h3⟩ := ih c' w (by omega)
      refine ⟨by omega, ?_, fun _ hnil => by cases hnil⟩
      intro hc0 hlen; subst hc0
      have hgs_nil : gs.filterMap Prod.snd = [] := List.length_eq_zero_iff.mp (by omega)
      rw [hgs_nil, h3 (by omega) hgs_nil]

private theorem filterMap_snd_perm {A B : List TagItem} (hp : A.Perm B) (u : ℕ) :
    ((A.filter fun a => decide (a.1 = u)).filterMap Prod.snd).Perm
      ((B.filter fun a => decide (a.1 = u)).filterMap Prod.snd) :=
  (hp.filter _).filterMap _

private theorem rawTagItems_filterMap_u {N M u : ℕ} (hu : u < 4 * N) (hM : 0 < M)
    {L₁ L₂ L₃ : List ℤ} (h₁ : L₁.Nodup) (h₂ : L₂.Nodup) (h₃ : L₃.Nodup) :
    let vals := ((rawTagItems N M L₁ L₂ L₃).filter fun a => decide (a.1 = u)).filterMap Prod.snd
    vals.Nodup ∧
      (u % 4 = 0 → vals = []) ∧
      (u % 4 = 1 → vals.toFinset = bucket L₁.toFinset M (u / 4 : ℕ)) ∧
      (u % 4 = 2 → vals.toFinset = bucket L₂.toFinset M (u / 4 : ℕ)) ∧
      (u % 4 = 3 → vals.toFinset =
        if u / 4 < 2 * M then bucket (L₃.toFinset.image fun c => -c) M ((u / 4) % M : ℕ)
        else ∅) := by
  have hnone_empty : (((fastRange (4 * N + 1)).map (fun k => (k, (none : Option ℤ)))).filter
      fun a => decide (a.1 = u)).filterMap Prod.snd = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro a ha
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_filter ha)
    rfl
  have htag1_mod : ∀ a ∈ streamList Prod.fst emitTag₁ (N, M) L₁, a.1 % 4 = 1 := by
    rw [streamList_emitTag_eq_flatMap]
    intro a ha
    obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp ha
    unfold emitTag₁ at hx; split_ifs at hx
    · rw [List.mem_singleton.mp hx]; omega
    · cases hx
  have htag2_mod : ∀ a ∈ streamList Prod.fst emitTag₂ (N, M) L₂, a.1 % 4 = 2 := by
    rw [streamList_emitTag_eq_flatMap]; intro a ha
    obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp ha
    unfold emitTag₂ at hx; split_ifs at hx
    · rw [List.mem_singleton.mp hx]; omega
    · cases hx
  have htag3_mod : ∀ a ∈ streamList Prod.fst emitTag₃ (N, M) L₃, a.1 % 4 = 3 := by
    rw [streamList_emitTag_eq_flatMap]; intro a ha
    obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp ha
    unfold emitTag₃ at hx
    rcases List.mem_append.mp hx with h1 | h2
    · split_ifs at h1; · rw [List.mem_singleton.mp h1]; omega
      · cases h1
    · split_ifs at h2; · rw [List.mem_singleton.mp h2]; omega
      · cases h2
  have filter_nil_of_mod : ∀ {T : List TagItem} {r : ℕ},
      (∀ a ∈ T, a.1 % 4 = r) → u % 4 ≠ r → (T.filter fun a => decide (a.1 = u)) = [] := by
    intro T r hmod hne
    rw [List.filter_eq_nil_iff]
    intro a ha
    simp only [decide_eq_true_eq]
    intro heq
    exact hne (heq ▸ hmod a ha)
  have hdecomp :
      (((rawTagItems N M L₁ L₂ L₃).filter fun a => decide (a.1 = u)).filterMap Prod.snd) =
        (((streamList Prod.fst emitTag₁ (N, M) L₁).filter fun a => decide (a.1 = u)).filterMap
          Prod.snd) ++
        (((streamList Prod.fst emitTag₂ (N, M) L₂).filter fun a => decide (a.1 = u)).filterMap
          Prod.snd) ++
        (((streamList Prod.fst emitTag₃ (N, M) L₃).filter fun a => decide (a.1 = u)).filterMap
          Prod.snd) := by
    unfold rawTagItems
    simp only [List.filter_append, List.filterMap_append, hnone_empty, List.nil_append,
      List.append_assoc]
  have hcase (c : ℕ) (emit : (ℕ × ℕ) × ℤ → List TagItem)
      (he : ∀ z, emit ((N, M), z) = if decide (4 * intRemNat M z + c < 4 * N) then
        [(4 * intRemNat M z + c, some z)] else []) :
      ∀ L : List ℤ,
        ((streamList Prod.fst emit (N, M) L).filter fun a => decide (a.1 = u)).filterMap Prod.snd =
          L.filter (fun x => decide (4 * intRemNat M x + c = u)) := by
    intro L; rw [streamList_emitTag_eq_flatMap]
    induction L with
    | nil => rfl
    | cons x xs ih =>
      rw [List.flatMap_cons, List.filter_append, List.filterMap_append, ih, he, List.filter_cons]
      by_cases h : 4 * intRemNat M x + c = u
      · simp [h, hu]
      · by_cases hlt : 4 * intRemNat M x + c < 4 * N <;> simp [h, hlt]
  have hcase3 : ∀ L : List ℤ,
      ((streamList Prod.fst emitTag₃ (N, M) L).filter fun a => decide (a.1 = u)).filterMap
          Prod.snd =
        (L.filter fun z =>
          decide (4 * intRemNat M (-z) + 3 = u ∨ 4 * (intRemNat M (-z) + M) + 3 = u)).map
          (fun z => -z) := by
    intro L; rw [streamList_emitTag_eq_flatMap]
    induction L with
    | nil => rfl
    | cons z zs ih =>
      simp only [List.flatMap_cons, List.filter_append, List.filterMap_append, ih, List.filter_cons]
      unfold emitTag₃; dsimp only
      have hr_lt : intRemNat M (-z) < M := intRemNat_lt hM (-z)
      set a1 := 4 * intRemNat M (-z) + 3
      set a2 := 4 * (intRemNat M (-z) + M) + 3
      by_cases hA : a1 = u
      · have hB : a2 ≠ u := by omega
        by_cases hltB : a2 < 4 * N <;> simp [hA, hB, hu, hltB]
      · by_cases hB : a2 = u
        · by_cases hltA : a1 < 4 * N <;> simp [hA, hB, hu, hltA]
        · by_cases hltA : a1 < 4 * N <;> by_cases hltB : a2 < 4 * N <;>
            simp [hA, hB, hltA, hltB]
  have hmod4 : u % 4 = 0 ∨ u % 4 = 1 ∨ u % 4 = 2 ∨ u % 4 = 3 := by omega
  rcases hmod4 with hm0 | hm1 | hm2 | hm3
  · have e1 := filter_nil_of_mod htag1_mod (by omega)
    have e2 := filter_nil_of_mod htag2_mod (by omega)
    have e3 := filter_nil_of_mod htag3_mod (by omega)
    have hall : ((rawTagItems N M L₁ L₂ L₃).filter fun a => decide (a.1 = u)).filterMap Prod.snd =
        [] := by rw [hdecomp, e1, e2, e3]; rfl
    refine ⟨by rw [hall]; exact List.nodup_nil, fun _ => hall, by omega, by omega, by omega⟩
  · have hall : ((rawTagItems N M L₁ L₂ L₃).filter fun a => decide (a.1 = u)).filterMap Prod.snd =
        L₁.filter (fun x => decide (4 * intRemNat M x + 1 = u)) := by
      rw [hdecomp, hcase 1 emitTag₁ (fun _ => rfl) L₁, filter_nil_of_mod htag2_mod (by omega),
        filter_nil_of_mod htag3_mod (by omega)]; simp
    refine ⟨by rw [hall]; exact h₁.filter _, by omega, fun _ => ?_, by omega, by omega⟩
    rw [hall]; ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, bucket, Finset.mem_filter]
    refine and_congr_right fun _ => ⟨fun heq => by rw [← intRemNat_cast hM x]; omega,
      fun hmod => by have := Int.ofNat.inj ((intRemNat_cast hM x).trans hmod); omega⟩
  · have hall : ((rawTagItems N M L₁ L₂ L₃).filter fun a => decide (a.1 = u)).filterMap Prod.snd =
        L₂.filter (fun x => decide (4 * intRemNat M x + 2 = u)) := by
      rw [hdecomp, filter_nil_of_mod htag1_mod (by omega), hcase 2 emitTag₂ (fun _ => rfl) L₂,
        filter_nil_of_mod htag3_mod (by omega)]; simp
    refine ⟨by rw [hall]; exact h₂.filter _, by omega, by omega, fun _ => ?_, by omega⟩
    rw [hall]; ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, bucket, Finset.mem_filter]
    refine and_congr_right fun _ => ⟨fun heq => by rw [← intRemNat_cast hM x]; omega,
      fun hmod => by have := Int.ofNat.inj ((intRemNat_cast hM x).trans hmod); omega⟩
  · have e1 := filter_nil_of_mod htag1_mod (by omega)
    have e2 := filter_nil_of_mod htag2_mod (by omega)
    have hall : ((rawTagItems N M L₁ L₂ L₃).filter fun a => decide (a.1 = u)).filterMap Prod.snd =
        (L₃.filter fun z =>
          decide (4 * intRemNat M (-z) + 3 = u ∨ 4 * (intRemNat M (-z) + M) + 3 = u)).map
          (fun z => -z) := by
      rw [hdecomp, e1, e2, hcase3 L₃]; simp
    have hnd3 : (((rawTagItems N M L₁ L₂ L₃).filter fun a => decide (a.1 = u)).filterMap
        Prod.snd).Nodup := by
      rw [hall]
      exact (h₃.filter _).map neg_injective
    refine ⟨hnd3, by omega, by omega, by omega, fun _ => ?_⟩
    rw [hall]
    ext y
    by_cases hk : u / 4 < 2 * M
    · simp only [hk, ↓reduceIte, List.mem_toFinset, List.mem_map, List.mem_filter,
        decide_eq_true_eq, bucket, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨z, ⟨hzL, hcond⟩, rfl⟩
        refine ⟨⟨z, hzL, rfl⟩, ?_⟩
        have hr_lt : intRemNat M (-z) < M := intRemNat_lt hM (-z)
        have hcast := intRemNat_cast hM (-z)
        rcases hcond with hA | hB
        · have hdiv : u / 4 = intRemNat M (-z) := by omega
          rw [hdiv, Nat.mod_eq_of_lt hr_lt, hcast]
        · have hdiv : u / 4 = intRemNat M (-z) + M := by omega
          rw [hdiv, Nat.add_mod_right, Nat.mod_eq_of_lt hr_lt, hcast]
      · rintro ⟨⟨z, hzL, rfl⟩, hmod⟩
        refine ⟨z, ⟨hzL, ?_⟩, rfl⟩
        have hcast := intRemNat_cast hM (-z)
        rw [← hcast] at hmod
        have hr_eq : intRemNat M (-z) = (u / 4) % M := Int.ofNat.inj hmod
        by_cases hkM : u / 4 < M
        · left
          rw [Nat.mod_eq_of_lt hkM] at hr_eq
          omega
        · right
          have hsub : (u / 4) % M = u / 4 - M := by
            have hlt2 : u / 4 - M < M := by omega
            conv_lhs => rw [show u / 4 = (u / 4 - M) + M by omega]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
          rw [hsub] at hr_eq
          omega
    · simp only [hk, ↓reduceIte, Finset.notMem_empty, iff_false, List.mem_toFinset,
        List.mem_map, List.mem_filter, decide_eq_true_eq]
      rintro ⟨z, ⟨_, hcond⟩, _⟩
      have hr_lt : intRemNat M (-z) < M := intRemNat_lt hM (-z)
      omega

private theorem arr_eq_of_nodup_finset (B : Finset ℤ) (padVal : ℤ) (vals : List ℤ)
    (hnd : vals.Nodup) (heq : vals.toFinset = B)
    (cnt : ℕ) (v : ℤ) (hcnt : cnt = min vals.length 2) (hv : vals.length = 1 → vals = [v]) :
    (if cnt = 1 then v else padVal) =
      (if B.card = 1 then ∑ x ∈ B, x else padVal) := by
  have hcard : B.card = vals.length := by
    rw [← heq, List.toFinset_card_of_nodup hnd]
  by_cases h1 : vals.length = 1
  · have hcnt1 : cnt = 1 := by omega
    have hB1 : B.card = 1 := by omega
    have hvs : vals = [v] := hv h1
    have hB_eq : B = {v} := by rw [← heq, hvs]; simp
    simp only [hcnt1, hB_eq, Finset.card_singleton, ↓reduceIte, Finset.sum_singleton]
  · have hcnt_ne : cnt ≠ 1 := by omega
    have hB_ne : B.card ≠ 1 := by omega
    simp only [hcnt_ne, hB_ne, ↓reduceIte]

/-- For `0 < M` and duplicate-free `L₁, L₂, L₃`, `oneArrayList` materializes
`List.ofFn (fun u : Fin (4 * N) => ((Node.mk ...).oneArray U u).toNat)`. -/
theorem oneArrayList_eq_ofFn {U N M : ℕ} (hM : 0 < M) {L₁ L₂ L₃ : List ℤ}
    (h₁ : L₁.Nodup) (h₂ : L₂.Nodup) (h₃ : L₃.Nodup) :
    oneArrayList U N M L₁ L₂ L₃ =
      List.ofFn (fun u : Fin (4 * N) =>
        ((Node.mk L₁.toFinset L₂.toFinset L₃.toFinset M).oneArray U u).toNat) := by
  unfold oneArrayList
  let T := rawTagItems N M L₁ L₂ L₃
  let S := radixSortBy Prod.fst (4 * N).size T
  have hperm := radixSortBy_perm Prod.fst (4 * N).size T
  have hsort : S.Pairwise (fun a b => a.1 ≤ b.1) := by
    refine pairwise_radixSortBy Prod.fst (4 * N).size fun a ha => ?_
    exact (rawTagItems_keys_le N M L₁ L₂ L₃ a ha).trans_lt (Nat.lt_size_self (4 * N))
  have hbnd : ∀ a ∈ S, 0 ≤ a.1 ∧ a.1 ≤ 4 * N := fun a ha =>
    ⟨Nat.zero_le _, rawTagItems_keys_le N M L₁ L₂ L₃ a (hperm.mem_iff.mp ha)⟩
  have hex : ∀ u, 0 < u → u ≤ 4 * N → ∃ a ∈ S, a.1 = u := fun u _ hu =>
    ⟨(u, none), hperm.mem_iff.mpr (mem_none_rawTagItems hu), rfl⟩
  change streamList packNext packEmit ((U, 0), (0, 0)) S = _
  rw [streamList_pack_groups (K := 4 * N) (4 * N) 0 S U (Nat.zero_le _) (Nat.sub_zero _)
    hsort hbnd hex, Nat.sub_zero]
  refine List.ext_getElem (by simp) fun u hu1 hu2 => ?_
  have hu_lt : u < 4 * N := by simpa using hu1
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, zero_add]
  let grpS := S.filter (fun a => decide (a.1 = u))
  let cv := grpS.foldl (fun s a => accStep s a.2) (0, 0)
  change packCellNat U u cv.1 cv.2 = _
  unfold packCellNat
  congr 1
  obtain ⟨hcntS, hvS⟩ := foldl_accStep_count_and_unique grpS
  have hp_vals := filterMap_snd_perm hperm u
  let valsT := (T.filter fun a => decide (a.1 = u)).filterMap Prod.snd
  have hndS : (grpS.filterMap Prod.snd).Nodup :=
    hp_vals.nodup_iff.mpr (rawTagItems_filterMap_u hu_lt hM h₁ h₂ h₃).1
  have hfs_eq : (grpS.filterMap Prod.snd).toFinset = valsT.toFinset := by
    ext x; rw [List.mem_toFinset, List.mem_toFinset]; exact hp_vals.mem_iff
  obtain ⟨_, _, hm1, hm2, hm3⟩ := rawTagItems_filterMap_u hu_lt hM h₁ h₂ h₃
  unfold packCellInt Node.oneArray oneArray arrXY arrZ arr pad
  dsimp only
  have hpad : (2 * (U : ℤ) + 1 : ℤ) = ↑(2 * U + 1) := by push_cast; ring
  rcases (by omega : u % 4 = 0 ∨ u % 4 = 1 ∨ u % 4 = 2 ∨ u % 4 = 3) with h0 | h1 | h2 | h3
  · simp only [h0, Nat.reduceEqDiff, ↓reduceIte, hpad]
  · simp only [h1, ↓reduceIte, hpad]
    rw [arr_eq_of_nodup_finset _ _ (grpS.filterMap Prod.snd) hndS (hfs_eq.trans (hm1 h1))
      cv.1 cv.2 hcntS hvS]
  · simp only [h2, Nat.reduceEqDiff, ↓reduceIte, hpad]
    rw [arr_eq_of_nodup_finset _ _ (grpS.filterMap Prod.snd) hndS (hfs_eq.trans (hm2 h2))
      cv.1 cv.2 hcntS hvS]
  · simp only [h3, Nat.reduceEqDiff, ↓reduceIte, hpad]
    by_cases hk : u / 4 < 2 * M
    · have hB := hfs_eq.trans (hm3 h3); simp only [hk, ↓reduceIte] at hB ⊢
      rw [arr_eq_of_nodup_finset _ _ (grpS.filterMap Prod.snd) hndS hB cv.1 cv.2 hcntS hvS]
    · have hB := hfs_eq.trans (hm3 h3); simp only [hk, ↓reduceIte] at hB ⊢
      have hne1 : cv.1 ≠ 1 := by
        cases hfm : grpS.filterMap Prod.snd with
        | nil =>
          have hc0 : cv.1 = min ([] : List ℤ).length 2 := hfm ▸ hcntS
          simp only [List.length_nil] at hc0; omega
        | cons x xs =>
          have : x ∈ (∅ : Finset ℤ) := hB ▸ List.mem_toFinset.mpr (hfm ▸ List.mem_cons_self ..)
          cases Finset.notMem_empty x this
      simp only [hne1, ↓reduceIte]

private theorem node_oneArray_bounds {U : ℕ} {ν : Node}
    (b₁ : Bdd U ν.S₁) (b₂ : Bdd U ν.S₂) (b₃ : Bdd U ν.S₃) (u : ℕ) :
    3 ≤ ν.oneArray U u ∧ ν.oneArray U u ≤ 60 * (U : ℤ) + 40 := by
  have hub := (abs_le.mp (Node.abs_oneArray_le b₁ b₂ b₃ u)).2
  refine ⟨?_, hub⟩
  have h1 := (abs_le.mp (abs_arrXY_le ν.M b₁ (u / 4))).1
  have h2 := (abs_le.mp (abs_arrXY_le ν.M b₂ (u / 4))).1
  have h3 := (abs_le.mp (abs_arrZ_le ν.M b₃ (u / 4))).1
  unfold Node.oneArray oneArray
  dsimp only
  push_cast at h1 h2 h3 ⊢
  split_ifs <;> omega

/-- Under `Bdd U`, every entry of `oneArrayList` lies in `[1, 60 * U + 40]`. -/
theorem oneArrayList_pos_and_le {U N M : ℕ} (hM : 0 < M) {L₁ L₂ L₃ : List ℤ}
    (h₁ : L₁.Nodup) (h₂ : L₂.Nodup) (h₃ : L₃.Nodup)
    (b₁ : Bdd U L₁.toFinset) (b₂ : Bdd U L₂.toFinset) (b₃ : Bdd U L₃.toFinset)
    {a : ℕ} (ha : a ∈ oneArrayList U N M L₁ L₂ L₃) :
    0 < a ∧ a ≤ 60 * U + 40 := by
  rw [oneArrayList_eq_ofFn hM h₁ h₂ h₃, List.mem_ofFn] at ha
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨hlo, hhi⟩ :=
    node_oneArray_bounds (ν := Node.mk L₁.toFinset L₂.toFinset L₃.toFinset M) b₁ b₂ b₃ u
  omega

/-- Under `Bdd U`, additive solutions in `oneArrayList` coincide with `Convolution (4 * N)`. -/
theorem oneArrayList_conv_iff {U N M : ℕ} (hM : 0 < M) {L₁ L₂ L₃ : List ℤ}
    (h₁ : L₁.Nodup) (h₂ : L₂.Nodup) (h₃ : L₃.Nodup)
    (b₁ : Bdd U L₁.toFinset) (b₂ : Bdd U L₂.toFinset) (b₃ : Bdd U L₃.toFinset) :
    (∃ (i j : ℕ) (h : i + j < (oneArrayList U N M L₁ L₂ L₃).length),
      (oneArrayList U N M L₁ L₂ L₃)[i]'(by omega) +
        (oneArrayList U N M L₁ L₂ L₃)[j]'(by omega) =
        (oneArrayList U N M L₁ L₂ L₃)[i + j]'h) ↔
      Convolution (4 * N) ((Node.mk L₁.toFinset L₂.toFinset L₃.toFinset M).oneArray U) := by
  let ν : Node := Node.mk L₁.toFinset L₂.toFinset L₃.toFinset M
  have heq := oneArrayList_eq_ofFn (U := U) (N := N) hM h₁ h₂ h₃
  have hcast : ∀ k, ((ν.oneArray U k).toNat : ℤ) = ν.oneArray U k := fun k =>
    Int.toNat_of_nonneg (by have := (node_oneArray_bounds (ν := ν) b₁ b₂ b₃ k).1; omega)
  have hget : ∀ (k : ℕ) (hk : k < (oneArrayList U N M L₁ L₂ L₃).length),
      ((oneArrayList U N M L₁ L₂ L₃)[k]'hk : ℤ) = ν.oneArray U k := fun k hk => by
    have hk' : k < 4 * N := by rwa [length_oneArrayList] at hk
    have : (oneArrayList U N M L₁ L₂ L₃)[k]'hk = (ν.oneArray U k).toNat := by
      simp only [heq, List.getElem_ofFn]; rfl
    rw [this, hcast]
  constructor
  · rintro ⟨i, j, hij, hsum⟩
    refine ⟨i, j, by rwa [length_oneArrayList] at hij, ?_⟩
    have hsumZ := congrArg (Nat.cast : ℕ → ℤ) hsum
    rwa [Nat.cast_add, hget i (by omega), hget j (by omega), hget (i + j) hij] at hsumZ
  · rintro ⟨i, j, hij, hsum⟩
    have hij_len : i + j < (oneArrayList U N M L₁ L₂ L₃).length := by rwa [length_oneArrayList]
    refine ⟨i, j, hij_len, Nat.cast_injective (R := ℤ) ?_⟩
    rw [Nat.cast_add, hget i (by omega), hget j (by omega), hget (i + j) hij_len]
    exact hsum

/-- Input tuple `((U, (N, M)), (L₁, (L₂, L₃)))` for `oneArrayList`. -/
abbrev PackInput := (ℕ × (ℕ × ℕ)) × IntTriple

/-- Encoding of `PackInput`. -/
@[expose] def encPackInput : PackInput ↪ List Bool :=
  encPair (encPair encNat (encPair encNat encNat)) encIntTriple

/-- Total work length `N + |L₁| + |L₂| + |L₃| + 1` of `x : PackInput`. -/
def packLen (x : PackInput) : ℕ :=
  x.1.2.1 + x.2.1.length + x.2.2.1.length + x.2.2.2.length + 1

/-- Bit-scale parameter for `oneArrayList` on `x : PackInput`. -/
def packScale (x : PackInput) : ℕ :=
  x.1.1.size + x.1.2.1.size + x.1.2.2.size +
    listMax (fun z => (encIntBin z).length) x.2.1 +
    listMax (fun z => (encIntBin z).length) x.2.2.1 +
    listMax (fun z => (encIntBin z).length) x.2.2.2 + (packLen x).size + 8

theorem packLen_le {x : PackInput} {b : ℕ}
    (h : x.1.2.1 + x.2.1.length + x.2.2.1.length + x.2.2.2.length + 1 ≤ b) :
    packLen x ≤ b := by unfold packLen; exact h

theorem packScale_le {x : PackInput} {bU bN bM b1 b2 b3 bP : ℕ}
    (hU : x.1.1.size ≤ bU) (hN : x.1.2.1.size ≤ bN) (hM : x.1.2.2.size ≤ bM)
    (h1 : listMax (fun z => (encIntBin z).length) x.2.1 ≤ b1)
    (h2 : listMax (fun z => (encIntBin z).length) x.2.2.1 ≤ b2)
    (h3 : listMax (fun z => (encIntBin z).length) x.2.2.2 ≤ b3)
    (hP : (packLen x).size ≤ bP) :
    packScale x ≤ bU + bN + bM + b1 + b2 + b3 + bP + 8 := by
  dsimp only [packScale]; omega

private theorem computableInPolyTime_accStep :
    ComputableInPolyTime (fun q : (ℕ × ℤ) × Option ℤ => accStep q.1 q.2)
      (encPair (encPair encNat encIntBin) (encOption encIntBin)) (encPair encNat encIntBin) := by
  unfold accStep; fun_prop

private theorem computableInPolyTime_singletonIf {α : Type} {encA : α ↪ List Bool} :
    ComputableInPolyTime (fun q : Bool × α => if q.1 then [q.2] else [])
      (encPair encBool encA) (encList encA) := by fun_prop

private theorem computableInPolyTime_packNext :
    ComputableInPolyTime packNext (encPair encPackState encTagItem) encPackState := by
  let eS := encPair (encPair encNat encNat) (encPair encNat encIntBin)
  let eT := encPair encNat (encOption encIntBin)
  have h1 := (ComputableInPolyTime.fst (encPair encNat encNat) (encPair encNat encIntBin)).comp
    (ComputableInPolyTime.fst eS eT)
  have h2 := (ComputableInPolyTime.snd (encPair encNat encNat) (encPair encNat encIntBin)).comp
    (ComputableInPolyTime.fst eS eT)
  have hU := (ComputableInPolyTime.fst encNat encNat).comp h1
  have hcur := (ComputableInPolyTime.snd encNat encNat).comp h1
  have hu := (ComputableInPolyTime.fst encNat (encOption encIntBin)).comp
    (ComputableInPolyTime.snd eS eT)
  have ho := (ComputableInPolyTime.snd encNat (encOption encIntBin)).comp
    (ComputableInPolyTime.snd eS eT)
  have heq : ComputableInPolyTime (fun q : ℕ × ℕ => decide (q.1 = q.2))
      (encPair encNat encNat) encBool := by fun_prop
  have hc0 : ComputableInPolyTime (fun _ : PackState × TagItem => ((0 : ℕ), (0 : ℤ)))
      (encPair eS eT) (encPair encNat encIntBin) := ComputableInPolyTime.const (0, 0)
  exact ComputableInPolyTime.ite (heq.comp (hu.prod hcur))
    (h1.prod (computableInPolyTime_accStep.comp (h2.prod ho)))
    ((hU.prod hu).prod (computableInPolyTime_accStep.comp (hc0.prod ho)))

private theorem computableInPolyTime_packCellNat :
    ComputableInPolyTime (fun q : (ℕ × ℕ) × (ℕ × ℤ) => packCellNat q.1.1 q.1.2 q.2.1 q.2.2)
      (encPair (encPair encNat encNat) (encPair encNat encIntBin)) encNat := by
  have hg : ComputableInPolyTime (fun u : ℕ => (3 * (2 * (u : ℤ) + 1) + 1 : ℤ))
      encNat encIntBin := by fun_prop
  have hw : ComputableInPolyTime (fun u : ℕ => (2 * (u : ℤ) + 1 : ℤ))
      encNat encIntBin := by fun_prop
  have hmod : ComputableInPolyTime (fun u : ℕ => u % 4) encNat encNat :=
    (by fun_prop : ComputableInPolyTime
      (fun u : ℕ => (if u.testBit 0 then 1 else 0) + (if u.testBit 1 then 2 else 0))
      encNat encNat).of_enc_eq fun u => congrArg encNat (by
      rw [Nat.testBit_zero, show (1 : ℕ) = 0 + 1 from rfl, Nat.testBit_add_one, Nat.testBit_zero]
      simp only [decide_eq_true_eq]; split_ifs <;> omega)
  have hselP : ComputableInPolyTime
      (fun r : ℤ × (ℕ × ℤ) => if decide (r.2.1 = 1) then r.2.2 else r.1)
      (encPair encIntBin (encPair encNat encIntBin)) encIntBin := by fun_prop
  have hselN : ComputableInPolyTime
      (fun r : ℤ × (ℕ × ℤ) => if decide (r.2.1 = 1) then r.2.2 else -r.1)
      (encPair encIntBin (encPair encNat encIntBin)) encIntBin := by fun_prop
  have hbr : ComputableInPolyTime
      (fun t : (ℕ × ℤ) × (ℤ × ℤ) =>
        (if decide (t.1.1 = 1) then t.2.1 + t.1.2 else if decide (t.1.1 = 2) then
          t.2.1 + 3 * t.1.2 else if decide (t.1.1 = 3) then t.2.2 + 4 * t.1.2
          else 10 * t.1.2).toNat)
      (encPair (encPair encNat encIntBin) (encPair encIntBin encIntBin)) encNat := by fun_prop
  have h1 := ComputableInPolyTime.fst (encPair encNat encNat) (encPair encNat encIntBin)
  have h2 := ComputableInPolyTime.snd (encPair encNat encNat) (encPair encNat encIntBin)
  have hU := (ComputableInPolyTime.fst encNat encNat).comp h1
  have hu := (ComputableInPolyTime.snd encNat encNat).comp h1
  have hwq := (hw.comp hU).prod h2
  exact (hbr.comp (((hmod.comp hu).prod (hg.comp hU)).prod
    ((hselP.comp hwq).prod (hselN.comp hwq)))).of_enc_eq fun q => congrArg encNat (by
    unfold packCellNat packCellInt; dsimp only [Function.comp_apply]
    simp only [decide_eq_true_eq])

private theorem computableInPolyTime_packEmit :
    ComputableInPolyTime packEmit (encPair encPackState encTagItem) (encList encNat) := by
  have hc := computableInPolyTime_packCellNat.comp
    (ComputableInPolyTime.fst encPackState encTagItem)
  have hcur := (ComputableInPolyTime.snd encNat encNat).comp
    ((ComputableInPolyTime.fst (encPair encNat encNat) (encPair encNat encIntBin)).comp
      (ComputableInPolyTime.fst encPackState encTagItem))
  have hu := (ComputableInPolyTime.fst encNat (encOption encIntBin)).comp
    (ComputableInPolyTime.snd encPackState encTagItem)
  have hneq : ComputableInPolyTime (fun q : ℕ × ℕ => !decide (q.1 = q.2))
      (encPair encNat encNat) encBool := by fun_prop
  exact (computableInPolyTime_singletonIf.comp ((hneq.comp (hu.prod hcur)).prod hc)).of_enc_eq
    fun p => by
      unfold packEmit; dsimp only [Function.comp_apply]; cases decide (p.2.1 = p.1.1.2) <;> rfl

private theorem computableInPolyTime_initPackState :
    ComputableInPolyTime (fun u : ℕ => (((u, 0), (0, 0)) : PackState)) encNat encPackState := by
  unfold encPackState; fun_prop

private theorem computableInPolyTime_tagSingle (c : ℕ) :
    ComputableInPolyTime
      (fun r : (ℕ × ℕ) × ℤ =>
        if decide (4 * r.1.2 + c < 4 * r.1.1) then [((4 * r.1.2 + c, some r.2) : TagItem)] else [])
      (encPair (encPair encNat encNat) encIntBin) (encList encTagItem) := by
  let p1 := (ComputableInPolyTime.fst encNat encNat).comp
    (ComputableInPolyTime.fst (encPair encNat encNat) encIntBin)
  let p2 := (ComputableInPolyTime.snd encNat encNat).comp
    (ComputableInPolyTime.fst (encPair encNat encNat) encIntBin)
  have hu := (by fun_prop : ComputableInPolyTime (fun n : ℕ => 4 * n + c) encNat encNat).comp p2
  have hu1 := (by fun_prop : ComputableInPolyTime (fun n : ℕ => n + 1) encNat encNat).comp hu
  have hu2 := (by fun_prop : ComputableInPolyTime (fun n : ℕ => 4 * n) encNat encNat).comp p1
  have hle : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
      (encPair encNat encNat) encBool := by fun_prop
  have hs := (by fun_prop : ComputableInPolyTime (Option.some : ℤ → Option ℤ)
    encIntBin (encOption encIntBin)).comp
    (ComputableInPolyTime.snd (encPair encNat encNat) encIntBin)
  exact (computableInPolyTime_singletonIf.comp
    ((hle.comp (hu1.prod hu2)).prod (hu.prod hs))).of_enc_eq fun r => by
      dsimp only [Function.comp_apply]
      rw [show decide (4 * r.1.2 + c + 1 ≤ 4 * r.1.1) = decide (4 * r.1.2 + c < 4 * r.1.1) from
        decide_eq_decide.mpr Nat.succ_le_iff]; rfl

private theorem computableInPolyTime_emitTag₁ :
    ComputableInPolyTime emitTag₁
      (encPair (encPair encNat encNat) encIntBin) (encList encTagItem) :=
  (computableInPolyTime_tagSingle 1).comp (by fun_prop :
    ComputableInPolyTime (fun q : (ℕ × ℕ) × ℤ => ((q.1.1, intRemNat q.1.2 q.2), q.2))
      (encPair (encPair encNat encNat) encIntBin) (encPair (encPair encNat encNat) encIntBin))

private theorem computableInPolyTime_emitTag₂ :
    ComputableInPolyTime emitTag₂
      (encPair (encPair encNat encNat) encIntBin) (encList encTagItem) :=
  (computableInPolyTime_tagSingle 2).comp (by fun_prop :
    ComputableInPolyTime (fun q : (ℕ × ℕ) × ℤ => ((q.1.1, intRemNat q.1.2 q.2), q.2))
      (encPair (encPair encNat encNat) encIntBin) (encPair (encPair encNat encNat) encIntBin))

private theorem computableInPolyTime_emitTag₃ :
    ComputableInPolyTime emitTag₃
      (encPair (encPair encNat encNat) encIntBin) (encList encTagItem) := by
  have happ : ComputableInPolyTime (fun p : List TagItem × List TagItem => p.1 ++ p.2)
      (encPair (encList encTagItem) (encList encTagItem)) (encList encTagItem) := by fun_prop
  have h1 := (computableInPolyTime_tagSingle 3).comp (by fun_prop :
    ComputableInPolyTime (fun q : (ℕ × ℕ) × ℤ => ((q.1.1, intRemNat q.1.2 (-q.2)), -q.2))
      (encPair (encPair encNat encNat) encIntBin) (encPair (encPair encNat encNat) encIntBin))
  have h2 := (computableInPolyTime_tagSingle 3).comp (by fun_prop :
    ComputableInPolyTime (fun q : (ℕ × ℕ) × ℤ => ((q.1.1, intRemNat q.1.2 (-q.2) + q.1.2), -q.2))
      (encPair (encPair encNat encNat) encIntBin) (encPair (encPair encNat encNat) encIntBin))
  exact happ.comp (h1.prod h2)

private theorem computableInPolyTime_tagNone :
    ComputableInPolyTime (fun q : Unit × ℕ => (q.2, (none : Option ℤ)))
      (encPair encUnit encNat) encTagItem := by
  unfold encTagItem
  fun_prop

private theorem computableInPolyTime_fourNSucc :
    ComputableInPolyTime (fun n : ℕ => 4 * n + 1) encNat encNat := by fun_prop

private theorem computableInPolyTime_fourNSize :
    ComputableInPolyTime (fun n : ℕ => (4 * n).size) encNat encNat := by
  have h1 : ComputableInPolyTime (fun n : ℕ => 4 * n) encNat encNat := by fun_prop
  have h2 : ComputableInPolyTime Nat.size encNat encNat :=
    ComputableInPolyTime.unary_to_binary.comp ComputableInPolyTime.binary_size
  exact h2.comp h1

private theorem computableInO_packStream :
    ∃ d, ComputableInO
      (fun p : ℕ × List TagItem => streamList packNext packEmit ((p.1, 0), (0, 0)) p.2)
      (encPair encNat (encList encTagItem)) (encList encNat)
      (fun p => (p.2.length + 1) *
        (p.1.size + listMax (fun a => (encTagItem a).length) p.2 + 8) ^ d)
      (fun p => (p.2.length + 1) *
        (p.1.size + listMax (fun a => (encTagItem a).length) p.2 + 8) ^ d) := by
  let lMax : PackState × List TagItem → ℕ :=
    fun p => 4 * p.1.1.1.size + 2 * p.1.1.2.size + 2 * p.1.2.1.size +
      (encIntBin p.1.2.2).length + 4 * listMax (fun a => (encTagItem a).length) p.2 + 12
  have hinv : ∀ (t : List TagItem) (U cur cnt : ℕ) (val : ℤ),
      let r := t.foldl (fun s a => packNext (s, a)) ((U, cur), (cnt, val))
      r.1.1 = U ∧ r.2.1 ≤ max cnt 2 ∧
        (r.1.2 = cur ∨ ∃ a ∈ t, r.1.2 = a.1) ∧
        (r.2.2 = val ∨ r.2.2 = 0 ∨ ∃ a ∈ t, a.2 = some r.2.2) := by
    intro t
    induction t with
    | nil =>
      intro U cur cnt val
      exact ⟨rfl, le_max_left _ _, Or.inl rfl, Or.inl rfl⟩
    | cons a ts ih =>
      intro U cur cnt val
      dsimp only
      rw [List.foldl_cons]
      let st' := packNext (((U, cur), (cnt, val)), a)
      have hst' : st'.1.1 = U ∧ st'.2.1 ≤ max cnt 2 ∧
          (st'.1.2 = cur ∨ st'.1.2 = a.1) ∧
          (st'.2.2 = val ∨ st'.2.2 = 0 ∨ a.2 = some st'.2.2) := by
        dsimp only [st']
        unfold packNext accStep
        rcases a with ⟨u, _ | w⟩ <;> simp only [Option.isSome_none, Option.isSome_some,
          Option.getD_some, Bool.false_eq_true, ↓reduceIte] <;>
          split_ifs <;> simp_all
      obtain ⟨hU', hcnt', hcur', hval'⟩ := ih st'.1.1 st'.1.2 st'.2.1 st'.2.2
      refine ⟨hU'.trans hst'.1, hcnt'.trans (max_le hst'.2.1 (le_max_right _ _)), ?_, ?_⟩
      · rcases hcur' with h1 | ⟨b, hb, h2⟩
        · rcases hst'.2.2.1 with hc1 | hc2
          · exact Or.inl (h1.trans hc1)
          · exact Or.inr ⟨a, List.mem_cons_self .., h1.trans hc2⟩
        · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, h2⟩
      · rcases hval' with hv1 | hv0 | ⟨b, hb, hvb⟩
        · rcases hst'.2.2.2 with hs1 | hs0 | hsa
          · exact Or.inl (hv1.trans hs1)
          · exact Or.inr (Or.inl (hv1.trans hs0))
          · exact Or.inr (Or.inr ⟨a, List.mem_cons_self .., hsa.trans (congrArg some hv1.symm)⟩)
        · exact Or.inr (Or.inl hv0)
        · exact Or.inr (Or.inr ⟨b, List.mem_cons_of_mem _ hb, hvb⟩)
  have h2sz : ∀ c : ℕ, c ≤ 2 → c.size ≤ 2 := by
    intro c hc; interval_cases c <;> decide
  have h0int : (encIntBin 0).length = 1 := by rw [length_encIntBin]; simp
  obtain ⟨dp, hstr⟩ := computableInO_streamList (lMax := lMax)
    Prod.fst Prod.snd (fun _ => rfl) computableInPolyTime_packNext computableInPolyTime_packEmit
    (fun _ => rfl)
    (fun p j _ => by
      simp only [streamState]
      obtain ⟨hU', hcnt', hcur', hval'⟩ :=
        hinv (p.2.take j) p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2
      set r := (p.2.take j).foldl (fun s a => packNext (s, a)) p.1
      change r.1.1 = p.1.1.1 at hU'
      change r.2.1 ≤ max p.1.2.1 2 at hcnt'
      change r.1.2 = p.1.1.2 ∨ ∃ a ∈ p.2.take j, r.1.2 = a.1 at hcur'
      change r.2.2 = p.1.2.2 ∨ r.2.2 = 0 ∨ ∃ a ∈ p.2.take j, a.2 = some r.2.2 at hval'
      have hcs : r.2.1.size ≤ p.1.2.1.size + 2 := by
        by_cases hc2 : p.1.2.1 ≤ 2
        · have hr2 : r.2.1 ≤ 2 := hcnt'.trans (max_le hc2 le_rfl)
          exact (h2sz r.2.1 hr2).trans (by omega)
        · have hrp : r.2.1 ≤ p.1.2.1 := hcnt'.trans (max_le le_rfl (by omega))
          exact (Nat.size_le_size hrp).trans (by omega)
      have hcur_sz :
          r.1.2.size ≤ p.1.1.2.size + listMax (fun a => (encTagItem a).length) p.2 := by
        rcases hcur' with h1 | ⟨a, ha, h2⟩
        · rw [h1]; omega
        · have ha_le := le_listMax (f := fun x => (encTagItem x).length) (List.mem_of_mem_take ha)
          have hpair_a := length_encPair (enc₁ := encNat) (enc₂ := encOption encIntBin) a
          change (encTagItem a).length = _ at hpair_a
          rw [length_encNat] at hpair_a; rw [h2]; omega
      have hval_len : (encIntBin r.2.2).length ≤
          (encIntBin p.1.2.2).length + listMax (fun a => (encTagItem a).length) p.2 + 1 := by
        rcases hval' with hv1 | hv0 | ⟨a, ha, h2⟩
        · rw [hv1]; omega
        · rw [hv0, h0int]; omega
        · have ha_le := le_listMax (f := fun x => (encTagItem x).length) (List.mem_of_mem_take ha)
          have hpair_a := length_encPair (enc₁ := encNat) (enc₂ := encOption encIntBin) a
          change (encTagItem a).length = _ at hpair_a
          rw [h2, encOption_some, List.length_cons] at hpair_a; omega
      simp only [encPackState, length_encPair, length_encNat, hU']
      dsimp only [lMax]; omega)
    (fun p j hj => by
      have := le_listMax (f := fun x => (encTagItem x).length) (List.getElem_mem hj)
      dsimp only [lMax]; omega)
  obtain ⟨di, _, hdi⟩ := computableInPolyTime_initPackState.exists_degree
  let encIn := encPair encNat (encList encTagItem)
  have hinit1 : ComputableInO (fun p : ℕ × List TagItem => (((p.1, 0), (0, 0)) : PackState))
      encIn encPackState
      (fun p => (encIn p).length + ((encNat p.1).length + 1) ^ di)
      (fun p => (encIn p).length + ((encNat p.1).length + 1) ^ di) :=
    hdi.inO.comp (ComputableInO.fst encNat (encList encTagItem))
  have hinit := (hinit1.prod (ComputableInO.snd encNat (encList encTagItem))).mono_le
    (T' := fun p => 2 * (encIn p).length + ((encNat p.1).length + 1) ^ di)
    (S' := fun p => 2 * (encIn p).length + ((encNat p.1).length + 1) ^ di)
    (fun _ => by dsimp only [encIn]; omega) (fun _ => by dsimp only [encIn]; omega)
  have hcomp := hstr.comp hinit
  let D := di + dp + 2
  refine ⟨D, hcomp.weaken ?_ ?_⟩
  all_goals
    refine BigOLe.of_le_linear (32 + 2 ^ di + 8 ^ dp) 0 fun p => ?_
    let S := p.1.size + listMax (fun a => (encTagItem a).length) p.2 + 8
    have hS1 : 1 ≤ S := by dsimp only [S]; omega
    have hSD : S ≤ S ^ D := Nat.le_self_pow (by dsimp only [D]; omega) S
    have hlenR : (encList encTagItem p.2).length ≤ 3 * ((p.2.length + 1) * S ^ D) := by
      have h1 := (length_encList_le_mul encTagItem p.2
        (b := listMax (fun a => (encTagItem a).length) p.2)
        fun a ha => le_listMax (f := fun x => (encTagItem x).length) ha).trans
        (Nat.mul_le_mul_left _ (by dsimp only [S]; omega : _ ≤ 3 * S))
      nlinarith [Nat.mul_le_mul (Nat.le_succ p.2.length) hSD]
    have hlenIn : (encIn p).length ≤ 6 * ((p.2.length + 1) * S ^ D) := by
      rw [length_encPair, length_encNat]
      nlinarith [(by dsimp only [S]; omega : p.1.size ≤ S).trans hSD]
    have h0s : (0 : ℕ).size = 0 := by decide
    have hst0 : (encPackState ((p.1, 0), (0, 0))).length = 4 * p.1.size + 5 := by
      simp only [encPackState, length_encPair, length_encNat, h0int, h0s]; omega
    have hpair : (encPair encPackState (encList encTagItem) (((p.1, 0), (0, 0)), p.2)).length ≤
        16 * ((p.2.length + 1) * S ^ D) := by
      rw [length_encPair, hst0]; dsimp only
      nlinarith [(by dsimp only [S]; omega : p.1.size + 1 ≤ S).trans hSD]
    have hpow_di : ((encNat p.1).length + 1) ^ di ≤ 2 ^ di * ((p.2.length + 1) * S ^ D) := by
      rw [length_encNat]
      exact (Nat.pow_le_pow_left (by dsimp only [S]; omega : _ ≤ 2 * S) di).trans
        ((Nat.mul_pow 2 S di).le.trans (Nat.mul_le_mul_left _
          ((Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega)).trans
            (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))))
    have hlmax : lMax (((p.1, 0), (0, 0)), p.2) + 1 ≤ 8 * S := by
      dsimp only [lMax, S]; rw [h0int, h0s]; omega
    have hpow_dp : (p.2.length + 1) * (lMax (((p.1, 0), (0, 0)), p.2) + 1) ^ dp ≤
        8 ^ dp * ((p.2.length + 1) * S ^ D) :=
      (Nat.mul_le_mul_left (p.2.length + 1)
        ((Nat.pow_le_pow_left hlmax dp).trans ((Nat.mul_pow 8 S dp).le.trans
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega)))))).trans_eq
        (Nat.mul_left_comm _ _ _)
    change 2 * (encIn p).length + ((encNat p.1).length + 1) ^ di +
        ((encPair encPackState (encList encTagItem) (((p.1, 0), (0, 0)), p.2)).length +
          (p.2.length + 1) * (lMax (((p.1, 0), (0, 0)), p.2) + 1) ^ dp) ≤
      (32 + 2 ^ di + 8 ^ dp) * ((p.2.length + 1) * S ^ D) + 0
    rw [Nat.add_mul (32 + 2 ^ di) (8 ^ dp), Nat.add_mul 32 (2 ^ di)]; omega

private theorem length_encPackInput_le (x : PackInput) :
    (encPackInput x).length ≤ 16 * (packLen x * packScale x) := by
  change (encPair (encPair encNat (encPair encNat encNat))
    (encPair (encList encIntBin) (encPair (encList encIntBin) (encList encIntBin))) x).length ≤ _
  simp only [length_encPair, length_encNat]
  have bnd (L : List ℤ) (hb : listMax (fun z => (encIntBin z).length) L + 1 ≤ packScale x) :
      (encList encIntBin L).length ≤ 2 * (L.length * packScale x) :=
    ((length_encList_le_mul encIntBin L (b := listMax (fun z => (encIntBin z).length) L)
      fun z hz => le_listMax (f := fun w => (encIntBin w).length) hz).trans
      (Nat.mul_le_mul_left _ (by omega : 2 * _ + 1 ≤ 2 * packScale x))).trans_eq
      (Nat.mul_left_comm _ _ _)
  have hl1 := bnd x.2.1 (by dsimp only [packScale]; omega)
  have hl2 := bnd x.2.2.1 (by dsimp only [packScale]; omega)
  have hl3 := bnd x.2.2.2 (by dsimp only [packScale]; omega)
  have hhead : 2 * x.1.1.size + 1 + (2 * x.1.2.1.size + 1 + x.1.2.2.size) ≤ 2 * packScale x := by
    dsimp only [packScale]; omega
  have hpL : x.2.1.length + x.2.2.1.length + x.2.2.2.length + 1 ≤ packLen x := by
    dsimp only [packLen]; omega
  nlinarith [show 1 ≤ packScale x by dsimp only [packScale]; omega]

private theorem computableInO_fnOnPackN {f : ℕ → ℕ} (hf : ComputableInPolyTime f encNat encNat) :
    ∃ d, ComputableInO (fun x : PackInput => f x.1.2.1) encPackInput encNat
      (fun x => packLen x * packScale x ^ d) (fun x => packLen x * packScale x ^ d) := by
  have hN : ComputableInO (fun x : PackInput => x.1.2.1) encPackInput encNat
      (fun x => (encPackInput x).length) (fun x => (encPackInput x).length) :=
    (ComputableInO.fst encNat encNat).comp_linear
      ((ComputableInO.snd encNat (encPair encNat encNat)).comp_linear
        (ComputableInO.fst _ encIntTriple))
  obtain ⟨df, _, hdf⟩ := hf.exists_degree
  refine ⟨df + 1, (hdf.inO.comp hN).weaken ?_ ?_⟩
  all_goals
    refine BigOLe.of_le_linear (16 + 2 ^ df) 0 fun x => ?_
    have hS1 : 1 ≤ packScale x := by dsimp only [packScale]; omega
    have hSD : packScale x ≤ packScale x ^ (df + 1) := Nat.le_self_pow (by omega) _
    have hin : (encPackInput x).length ≤ 16 * (packLen x * packScale x ^ (df + 1)) :=
      (length_encPackInput_le x).trans (by nlinarith [Nat.mul_le_mul_left (packLen x) hSD])
    have hpow : (x.1.2.1.size + 1) ^ df ≤ 2 ^ df * (packLen x * packScale x ^ (df + 1)) :=
      calc _ ≤ (2 * packScale x) ^ df :=
            Nat.pow_le_pow_left (by dsimp only [packScale]; omega) df
        _ = 2 ^ df * packScale x ^ df := Nat.mul_pow 2 _ df
        _ ≤ 2 ^ df * packScale x ^ (df + 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (Nat.le_succ df))
        _ ≤ 2 ^ df * (packLen x * packScale x ^ (df + 1)) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by dsimp only [packLen]; omega))
    change (encPackInput x).length + ((encNat x.1.2.1).length + 1) ^ df ≤ _
    rw [length_encNat, Nat.add_mul 16 (2 ^ df)]; omega

private theorem computableInO_emitOnPack (emit : (ℕ × ℕ) × ℤ → List TagItem)
    (hemit : ComputableInPolyTime emit
      (encPair (encPair encNat encNat) encIntBin) (encList encTagItem))
    (sel : PackInput → List ℤ)
    (hsel : ComputableInO sel encPackInput (encList encIntBin)
      (fun x => (encPackInput x).length) (fun x => (encPackInput x).length))
    (hlenSel : ∀ x, (sel x).length ≤ packLen x)
    (hmaxSel : ∀ x, listMax (fun z => (encIntBin z).length) (sel x) ≤ packScale x) :
    ∃ d, ComputableInO (fun x : PackInput => streamList Prod.fst emit x.1.2 (sel x))
      encPackInput (encList encTagItem)
      (fun x => packLen x * packScale x ^ d) (fun x => packLen x * packScale x ^ d) := by
  let encNM := encPair encNat encNat
  let lMax : (ℕ × ℕ) × List ℤ → ℕ :=
    fun p => (encNM p.1).length + listMax (fun z => (encIntBin z).length) p.2 + 2
  have hnext : ComputableInPolyTime (Prod.fst : (ℕ × ℕ) × ℤ → ℕ × ℕ)
      (encPair encNM encIntBin) encNM := by fun_prop
  obtain ⟨de, hstr⟩ := computableInO_streamList (lMax := lMax)
    Prod.fst Prod.snd (fun _ => rfl) hnext hemit (fun _ => rfl)
    (fun p j _ => by simp only [streamState, foldl_const]; dsimp only [lMax]; omega)
    (fun p j hj => by
      have := le_listMax (f := fun z => (encIntBin z).length) (List.getElem_mem hj)
      dsimp only [lMax]; omega)
  have hnm : ComputableInO (fun x : PackInput => x.1.2) encPackInput encNM
      (fun x => (encPackInput x).length) (fun x => (encPackInput x).length) :=
    (ComputableInO.snd encNat encNM).comp_linear (ComputableInO.fst _ encIntTriple)
  have hpair := (hnm.prod hsel).mono_le
    (T' := fun x => 2 * (encPackInput x).length) (S' := fun x => 2 * (encPackInput x).length)
    (fun _ => by omega) (fun _ => by omega)
  let D := de + 2
  refine ⟨D, (hstr.comp hpair).weaken ?_ ?_⟩
  all_goals
    refine BigOLe.of_le_linear (64 + 2 * 4 ^ de) 0 fun x => ?_
    let S := packScale x
    have hS1 : 1 ≤ S := by dsimp only [S, packScale]; omega
    have hSD : S ≤ S ^ D := Nat.le_self_pow (by dsimp only [D]; omega) S
    have hin : (encPackInput x).length ≤ 16 * (packLen x * S ^ D) :=
      (length_encPackInput_le x).trans (by nlinarith [Nat.mul_le_mul_left (packLen x) hSD])
    have hpL : (encPair encNM (encList encIntBin) (x.1.2, sel x)).length ≤
        8 * (packLen x * S ^ D) := by
      simp only [encNM, length_encPair, length_encNat]
      have hselL := length_encList_le_mul encIntBin (sel x) (b := S) fun z hz =>
        (le_listMax (f := fun w => (encIntBin w).length) hz).trans (hmaxSel x)
      have hselL' : (encList encIntBin (sel x)).length ≤ 3 * (packLen x * S) :=
        ((hselL.trans (Nat.mul_le_mul_left _ (by omega : 2 * S + 1 ≤ 3 * S))).trans
          (Nat.mul_le_mul_right _ (hlenSel x))).trans_eq (Nat.mul_left_comm _ _ _)
      have hnmL : 2 * x.1.2.1.size + 1 + x.1.2.2.size ≤ 2 * S := by dsimp only [S, packScale]; omega
      have hPL1 : 1 ≤ packLen x := by dsimp only [packLen]; omega
      nlinarith [Nat.mul_le_mul_left (packLen x) hSD]
    have hlmax : lMax (x.1.2, sel x) + 1 ≤ 4 * S := by
      dsimp only [lMax, encNM]; rw [length_encPair, length_encNat, length_encNat]
      have := hmaxSel x; dsimp only [S, packScale] at *; omega
    have hp : (lMax (x.1.2, sel x) + 1) ^ de ≤ 4 ^ de * S ^ D :=
      (Nat.pow_le_pow_left hlmax de).trans ((Nat.mul_pow 4 S de).le.trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega))))
    have hlen2 : (sel x).length + 1 ≤ 2 * packLen x := by
      have := hlenSel x; have : 1 ≤ packLen x := by dsimp only [packLen]; omega
      omega
    have hpow : ((sel x).length + 1) * (lMax (x.1.2, sel x) + 1) ^ de ≤
        2 * 4 ^ de * (packLen x * S ^ D) :=
      (Nat.mul_le_mul hlen2 hp).trans_eq
        (by rw [Nat.mul_assoc 2, Nat.mul_left_comm (packLen x), ← Nat.mul_assoc 2])
    change 2 * (encPackInput x).length +
        ((encPair encNM (encList encIntBin) (x.1.2, sel x)).length +
          ((sel x).length + 1) * (lMax (x.1.2, sel x) + 1) ^ de) ≤
      (64 + 2 * 4 ^ de) * (packLen x * S ^ D) + 0
    rw [Nat.add_mul 64 (2 * 4 ^ de)]; omega

/-- `oneArrayList U N M L₁ L₂ L₃` runs in quasi-linear time `O(packLen x * packScale x ^ d)`. -/
theorem computableInO_oneArrayList :
    ∃ d, ComputableInO
      (fun x : PackInput => oneArrayList x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2)
      encPackInput (encList encNat)
      (fun x => packLen x * packScale x ^ d) (fun x => packLen x * packScale x ^ d) := by
  obtain ⟨df4, h4N⟩ := computableInO_fnOnPackN computableInPolyTime_fourNSucc
  obtain ⟨dfr, hfr⟩ := computableInO_fastRange
  obtain ⟨dtn, htn⟩ := computableInO_streamMapWith
    (f := fun q : Unit × ℕ => (q.2, (none : Option ℤ))) computableInPolyTime_tagNone
    (lMax := fun p : Unit × List ℕ => listMax Nat.size p.2 + 2) (fun _ => Nat.zero_le _)
    (fun p j hj => by
      rw [length_encNat]; have := le_listMax (f := Nat.size) (List.getElem_mem hj); omega)
  let d0 := df4 + dfr + dtn + 2
  have htag0 : ComputableInO
      (fun x : PackInput => (fastRange (4 * x.1.2.1 + 1)).map fun u => (u, (none : Option ℤ)))
      encPackInput (encList encTagItem)
      (fun x => packLen x * packScale x ^ d0) (fun x => packLen x * packScale x ^ d0) := by
    have hrng : ComputableInO (fun x : PackInput => fastRange (4 * x.1.2.1 + 1))
        encPackInput (encList encNat)
        (fun x => packLen x * packScale x ^ (df4 + dfr + 1))
        (fun x => packLen x * packScale x ^ (df4 + dfr + 1)) := by
      refine (hfr.comp h4N).weaken ?_ ?_
      all_goals
        refine BigOLe.add (BigOLe.of_le fun x => Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by dsimp only [packScale]; omega) (by omega)))
          (BigOLe.of_le_linear (6 * 2 ^ dfr) 0 fun x => ?_)
        have hsz := size_four_mul_succ_le x.1.2.1
        have hp : ((4 * x.1.2.1 + 1).size + 1) ^ dfr ≤
            2 ^ dfr * packScale x ^ (df4 + dfr + 1) :=
          (Nat.pow_le_pow_left (by dsimp only [packScale]; omega : _ ≤ 2 * packScale x) dfr).trans
            ((Nat.mul_pow 2 _ dfr).le.trans (Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right (by dsimp only [packScale]; omega) (by omega))))
        exact (Nat.mul_le_mul (by dsimp only [packLen]; omega : _ ≤ 6 * packLen x) hp).trans_eq
          (by rw [Nat.mul_assoc 6, Nat.mul_left_comm (packLen x), ← Nat.mul_assoc 6, add_zero])
    have hunitRng : ComputableInO (fun x : PackInput => ((), fastRange (4 * x.1.2.1 + 1)))
        encPackInput (encPair encUnit (encList encNat))
        (fun x => packLen x * packScale x ^ (df4 + dfr + 1))
        (fun x => packLen x * packScale x ^ (df4 + dfr + 1)) := by
      refine ((ComputableInO.constZero ()).prod hrng).weaken ?_ ?_
      all_goals
        refine BigOLe.of_le_linear 18 0 fun x => ?_
        have hSD : packScale x ≤ packScale x ^ (df4 + dfr + 1) := Nat.le_self_pow (by omega) _
        have hin : (encPackInput x).length ≤ 16 * (packLen x * packScale x ^ (df4 + dfr + 1)) :=
          (length_encPackInput_le x).trans (by nlinarith [Nat.mul_le_mul_left (packLen x) hSD])
        omega
    refine (htn.comp hunitRng).weaken ?_ ?_
    all_goals
      refine BigOLe.add (BigOLe.of_le fun x => Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by dsimp only [packScale]; omega) (by dsimp only [d0]; omega)))
        (BigOLe.of_le_linear (32 + 6 * 2 ^ dtn) 0 fun x => ?_)
      let R := fastRange (4 * x.1.2.1 + 1)
      have hR_eq : R = List.range (4 * x.1.2.1 + 1) := fastRange_eq_range _
      have hlmR : listMax Nat.size R ≤ x.1.2.1.size + 3 := listMax_le fun u hu => by
        rw [hR_eq, List.mem_range] at hu
        exact (Nat.size_le_size (Nat.le_of_lt hu)).trans (size_four_mul_succ_le _)
      have hSD : packScale x ≤ packScale x ^ d0 := Nat.le_self_pow (by dsimp only [d0]; omega) _
      have hlenR : (encPair encUnit (encList encNat) ((), R)).length ≤
          32 * (packLen x * packScale x ^ d0) := by
        rw [length_encPair]; dsimp only
        have hu0 : (encUnit ()).length = 0 := rfl
        have h1 := length_encList_le_mul encNat R (b := x.1.2.1.size + 3) fun u hu => by
          rw [length_encNat]; exact (le_listMax (f := Nat.size) hu).trans hlmR
        have hRlen_le : R.length ≤ 5 * packLen x := by
          rw [hR_eq, List.length_range]; dsimp only [packLen]; omega
        have h3 : (encList encNat R).length ≤ 15 * (packLen x * packScale x) :=
          ((h1.trans (Nat.mul_le_mul_left _ (by dsimp only [packScale]; omega :
            _ ≤ 3 * packScale x))).trans (Nat.mul_le_mul_right _ hRlen_le)).trans_eq
            (by rw [Nat.mul_assoc 5, Nat.mul_left_comm (packLen x), ← Nat.mul_assoc 5])
        have hPL1 : 1 ≤ packLen x * packScale x ^ d0 :=
          Nat.mul_pos (by dsimp only [packLen]; omega)
            (Nat.one_le_pow _ _ (by dsimp only [packScale]; omega))
        rw [hu0]; nlinarith [Nat.mul_le_mul_left (packLen x) hSD]
      have hp : (listMax Nat.size R + 2 + 1) ^ dtn ≤ 2 ^ dtn * packScale x ^ d0 :=
        (Nat.pow_le_pow_left (by dsimp only [packScale]; omega : _ ≤ 2 * packScale x) dtn).trans
          ((Nat.mul_pow 2 _ dtn).le.trans (Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (by dsimp only [packScale]; omega) (by dsimp only [d0]; omega))))
      have hRlen6 : R.length + 1 ≤ 6 * packLen x := by
        rw [hR_eq, List.length_range]; dsimp only [packLen]; omega
      have hpow : (R.length + 1) * (listMax Nat.size R + 2 + 1) ^ dtn ≤
          6 * 2 ^ dtn * (packLen x * packScale x ^ d0) :=
        (Nat.mul_le_mul hRlen6 hp).trans_eq
          (by rw [Nat.mul_assoc 6, Nat.mul_left_comm (packLen x), ← Nat.mul_assoc 6])
      change (encPair encUnit (encList encNat) ((), R)).length +
          (R.length + 1) * (listMax Nat.size R + 2 + 1) ^ dtn ≤
        (32 + 6 * 2 ^ dtn) * (packLen x * packScale x ^ d0) + 0
      rw [Nat.add_mul 32 (6 * 2 ^ dtn)]; omega
  have hL1 : ComputableInO (fun x : PackInput => x.2.1) encPackInput (encList encIntBin)
      (fun x => (encPackInput x).length) (fun x => (encPackInput x).length) :=
    (ComputableInO.fst _ _).comp_linear (ComputableInO.snd _ encIntTriple)
  have hL2 : ComputableInO (fun x : PackInput => x.2.2.1) encPackInput (encList encIntBin)
      (fun x => (encPackInput x).length) (fun x => (encPackInput x).length) :=
    (ComputableInO.fst _ _).comp_linear
      ((ComputableInO.snd _ _).comp_linear (ComputableInO.snd _ encIntTriple))
  have hL3 : ComputableInO (fun x : PackInput => x.2.2.2) encPackInput (encList encIntBin)
      (fun x => (encPackInput x).length) (fun x => (encPackInput x).length) :=
    (ComputableInO.snd _ _).comp_linear
      ((ComputableInO.snd _ _).comp_linear (ComputableInO.snd _ encIntTriple))
  obtain ⟨d1, htag1⟩ := computableInO_emitOnPack emitTag₁ computableInPolyTime_emitTag₁
    (fun x => x.2.1) hL1 (fun x => by dsimp only [packLen]; omega)
    (fun x => by dsimp only [packScale]; omega)
  obtain ⟨d2, htag2⟩ := computableInO_emitOnPack emitTag₂ computableInPolyTime_emitTag₂
    (fun x => x.2.2.1) hL2 (fun x => by dsimp only [packLen]; omega)
    (fun x => by dsimp only [packScale]; omega)
  obtain ⟨d3, htag3⟩ := computableInO_emitOnPack emitTag₃ computableInPolyTime_emitTag₃
    (fun x => x.2.2.2) hL3 (fun x => by dsimp only [packLen]; omega)
    (fun x => by dsimp only [packScale]; omega)
  let draw := d0 + d1 + d2 + d3 + 1
  have hraw : ComputableInO
      (fun x : PackInput => rawTagItems x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2)
      encPackInput (encList encTagItem)
      (fun x => packLen x * packScale x ^ draw)
      (fun x => packLen x * packScale x ^ draw) := by
    have h23 := htag2.append htag3 (fun x => encList_append encTagItem _ _)
    have h123 := htag1.append h23 (fun x => encList_append encTagItem _ _)
    have h0123 := htag0.append h123 (fun x => encList_append encTagItem _ _)
    refine h0123.weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear 4 0 fun x => ?_
      have hS1 : 1 ≤ packScale x := by dsimp only [packScale]; omega
      have hp0 := Nat.mul_le_mul_left (packLen x)
        (Nat.pow_le_pow_right hS1 (by dsimp only [draw]; omega : d0 ≤ draw))
      have hp1 := Nat.mul_le_mul_left (packLen x)
        (Nat.pow_le_pow_right hS1 (by dsimp only [draw]; omega : d1 ≤ draw))
      have hp2 := Nat.mul_le_mul_left (packLen x)
        (Nat.pow_le_pow_right hS1 (by dsimp only [draw]; omega : d2 ≤ draw))
      have hp3 := Nat.mul_le_mul_left (packLen x)
        (Nat.pow_le_pow_right hS1 (by dsimp only [draw]; omega : d3 ≤ draw))
      change packLen x * packScale x ^ d0 +
          (packLen x * packScale x ^ d1 +
            (packLen x * packScale x ^ d2 + packLen x * packScale x ^ d3)) ≤
        4 * (packLen x * packScale x ^ draw) + 0
      omega
  have hraw_len (x : PackInput) :
      (rawTagItems x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2).length ≤ 6 * packLen x := by
    unfold rawTagItems
    simp only [List.length_append, List.length_map, fastRange_eq_range, List.length_range,
      streamList_emitTag_eq_flatMap]
    have hl1 := length_flatMap_le_mul (fun z => emitTag₁ (x.1.2, z)) 1
      (fun z => by unfold emitTag₁; split_ifs <;> simp) x.2.1
    have hl2 := length_flatMap_le_mul (fun z => emitTag₂ (x.1.2, z)) 1
      (fun z => by unfold emitTag₂; split_ifs <;> simp) x.2.2.1
    have hl3 := length_flatMap_le_mul (fun z => emitTag₃ (x.1.2, z)) 2
      (fun z => by unfold emitTag₃; split_ifs <;> simp) x.2.2.2
    simp only [Nat.one_mul, show (x.1.2.1, x.1.2.2) = x.1.2 from rfl] at hl1 hl2 hl3 ⊢
    dsimp only [packLen]; omega
  have hraw_elem (x : PackInput) (a : TagItem)
      (ha : a ∈ rawTagItems x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2) :
      (encTagItem a).length ≤ 4 * packScale x := by
    have hk := rawTagItems_keys_le x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2 a ha
    have hksz : a.1.size ≤ x.1.2.1.size + 2 :=
      (Nat.size_le_size hk).trans (size_four_mul_le _)
    unfold rawTagItems at ha
    rw [fastRange_eq_range, streamList_emitTag_eq_flatMap, streamList_emitTag_eq_flatMap,
      streamList_emitTag_eq_flatMap] at ha
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap] at ha
    have bndSome (w : ℤ) (hw : (encIntBin w).length ≤ packScale x) (hak : a.2 = some w) :
        (encTagItem a).length ≤ 4 * packScale x := by
      simp only [encTagItem, length_encPair, length_encNat, hak, encOption_some, List.length_cons]
      dsimp only [packScale] at *; omega
    rcases ha with ⟨u, _, rfl⟩ | ⟨z, hz, hmem⟩ | ⟨z, hz, hmem⟩ | ⟨z, hz, hmem⟩
    · simp only [encTagItem, length_encPair, length_encNat, encOption_none, List.length_nil]
      dsimp only [packScale] at *; omega
    · unfold emitTag₁ at hmem; dsimp only at hmem; split_ifs at hmem
      · exact bndSome z ((le_listMax (f := fun w => (encIntBin w).length) hz).trans
          (by dsimp only [packScale]; omega)) (congrArg Prod.snd (List.mem_singleton.mp hmem))
      · cases hmem
    · unfold emitTag₂ at hmem; dsimp only at hmem; split_ifs at hmem
      · exact bndSome z ((le_listMax (f := fun w => (encIntBin w).length) hz).trans
          (by dsimp only [packScale]; omega)) (congrArg Prod.snd (List.mem_singleton.mp hmem))
      · cases hmem
    · unfold emitTag₃ at hmem; dsimp only at hmem
      have hw : (encIntBin (-z)).length ≤ packScale x := by
        rw [length_encIntBin, Int.natAbs_neg, ← length_encIntBin]
        exact (le_listMax (f := fun w => (encIntBin w).length) hz).trans
          (by dsimp only [packScale]; omega)
      rcases List.mem_append.mp hmem with h1 | h2
      · split_ifs at h1
        · exact bndSome (-z) hw (congrArg Prod.snd (List.mem_singleton.mp h1))
        · cases h1
      · split_ifs at h2
        · exact bndSome (-z) hw (congrArg Prod.snd (List.mem_singleton.mp h2))
        · cases h2
  obtain ⟨db4, hb4⟩ := computableInO_fnOnPackN computableInPolyTime_fourNSize
  have hkeyPt : ComputableInPolyTime (Prod.fst : TagItem → ℕ) encTagItem encNat := by
    unfold encTagItem; fun_prop
  obtain ⟨dr, hsort⟩ := computableInO_radixSortBy (key := Prod.fst) hkeyPt
    (lMax := fun x => 4 * packScale x) hb4 hraw
    (fun x => by
      rw [length_encNat]
      have h1 := size_le_self (4 * x.1.2.1).size
      have h2 := size_four_mul_le x.1.2.1
      dsimp only [packScale]; omega)
    hraw_elem
  have hraw_enc (x : PackInput) :
      (encList encTagItem (rawTagItems x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2)).length ≤
        54 * (packLen x * packScale x) :=
    (((length_encList_le_mul encTagItem _ (b := 4 * packScale x) (hraw_elem x)).trans
      (Nat.mul_le_mul_left _ (by dsimp only [packScale]; omega : _ ≤ 9 * packScale x))).trans
      (Nat.mul_le_mul_right _ (hraw_len x))).trans_eq
      (by rw [Nat.mul_assoc 6, Nat.mul_left_comm (packLen x), ← Nat.mul_assoc 6])
  let dsort := db4 + draw + dr + 4
  have hsort' : ComputableInO
      (fun x : PackInput =>
        radixSortBy Prod.fst (4 * x.1.2.1).size
          (rawTagItems x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2))
      encPackInput (encList encTagItem)
      (fun x => packLen x * packScale x ^ dsort) (fun x => packLen x * packScale x ^ dsort) := by
    refine hsort.weaken ?_ ?_
    · refine BigOLe.add (BigOLe.add ?_ ?_) ?_
      · exact BigOLe.of_le fun x => Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by dsimp only [packScale]; omega) (by dsimp only [dsort]; omega))
      · exact BigOLe.of_le fun x => Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by dsimp only [packScale]; omega) (by dsimp only [dsort]; omega))
      · refine BigOLe.of_le_linear (64 + 7 * 5 ^ dr) 0 fun x => ?_
        let S := packScale x
        have hS1 : 1 ≤ S := by dsimp only [S, packScale]; omega
        have hSD : S * S ^ (dsort - 1) = S ^ dsort := (pow_succ' S (dsort - 1)).symm
        have hSpow : S ≤ S ^ (dsort - 1) := Nat.le_self_pow (by dsimp only [dsort]; omega) S
        have ha : (encList encTagItem
            (rawTagItems x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2)).length ≤
            54 * (packLen x * S ^ (dsort - 1)) :=
          (hraw_enc x).trans (by nlinarith [Nat.mul_le_mul_left (packLen x) hSpow])
        have hp : (4 * S + 1) ^ dr ≤ 5 ^ dr * S ^ (dsort - 1) :=
          (Nat.pow_le_pow_left (by omega) dr).trans ((Nat.mul_pow 5 S dr).le.trans
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by dsimp only [dsort]; omega))))
        have hl7 : (rawTagItems x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2).length + 1 ≤
            7 * packLen x := by
          have := hraw_len x; have : 1 ≤ packLen x := by dsimp only [packLen]; omega
          omega
        have hb : ((rawTagItems x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2).length + 1) *
            (4 * S + 1) ^ dr ≤ 7 * 5 ^ dr * (packLen x * S ^ (dsort - 1)) :=
          (Nat.mul_le_mul hl7 hp).trans_eq
            (by rw [Nat.mul_assoc 7, Nat.mul_left_comm (packLen x), ← Nat.mul_assoc 7])
        have hc : ((encNat (4 * x.1.2.1).size).length + 1) ^ 2 ≤
            4 * (packLen x * S ^ (dsort - 1)) := by
          rw [length_encNat]
          have h1 : (4 * x.1.2.1).size.size + 1 ≤ 2 * S := by
            have := size_le_self (4 * x.1.2.1).size; have := size_four_mul_le x.1.2.1
            dsimp only [S, packScale]; omega
          have hsq : ((4 * x.1.2.1).size.size + 1) ^ 2 ≤ 4 * S ^ (dsort - 1) :=
            (Nat.pow_le_pow_left h1 2).trans ((Nat.mul_pow 2 S 2).le.trans
              (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hS1 (by dsimp only [dsort]; omega))))
          have hPL1 : 1 ≤ packLen x := by dsimp only [packLen]; omega
          exact hsq.trans (by nlinarith [Nat.one_le_pow (dsort - 1) S hS1])
        have hsum :
            (encList encTagItem (rawTagItems x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2)).length +
              ((rawTagItems x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2).length + 1) * (4 * S + 1) ^ dr +
              ((encNat (4 * x.1.2.1).size).length + 1) ^ 2 ≤
            (64 + 7 * 5 ^ dr) * (packLen x * S ^ (dsort - 1)) := by
          rw [Nat.add_mul 64 (7 * 5 ^ dr)]; omega
        have hbp1 : (4 * x.1.2.1).size + 1 ≤ S := by
          have := size_four_mul_le x.1.2.1; dsimp only [S, packScale]; omega
        calc ((4 * x.1.2.1).size + 1) * _
            ≤ S * ((64 + 7 * 5 ^ dr) * (packLen x * S ^ (dsort - 1))) := Nat.mul_le_mul hbp1 hsum
          _ = (64 + 7 * 5 ^ dr) * (packLen x * (S * S ^ (dsort - 1))) := by
              rw [Nat.mul_left_comm, ← Nat.mul_assoc (packLen x),
                Nat.mul_left_comm S (packLen x), Nat.mul_assoc]
          _ = (64 + 7 * 5 ^ dr) * (packLen x * S ^ dsort) + 0 := by rw [hSD, add_zero]
    · refine BigOLe.add (BigOLe.add (BigOLe.add (BigOLe.add ?_ ?_) ?_) ?_) ?_
      · exact BigOLe.of_le fun x => Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by dsimp only [packScale]; omega) (by dsimp only [dsort]; omega))
      · exact BigOLe.of_le fun x => Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by dsimp only [packScale]; omega) (by dsimp only [dsort]; omega))
      · refine BigOLe.of_le_linear 54 0 fun x => ?_
        have hS : packScale x ≤ packScale x ^ dsort :=
          Nat.le_self_pow (by dsimp only [dsort]; omega) _
        exact (hraw_enc x).trans (by nlinarith [Nat.mul_le_mul_left (packLen x) hS])
      · refine BigOLe.of_le_linear (7 * 5 ^ dr) 0 fun x => ?_
        have hS1 : 1 ≤ packScale x := by dsimp only [packScale]; omega
        have hp : (4 * packScale x + 1) ^ dr ≤ 5 ^ dr * packScale x ^ dsort :=
          (Nat.pow_le_pow_left (by omega) dr).trans ((Nat.mul_pow 5 _ dr).le.trans
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by dsimp only [dsort]; omega))))
        have hl7 : (rawTagItems x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2).length + 1 ≤
            7 * packLen x := by
          have := hraw_len x; have : 1 ≤ packLen x := by dsimp only [packLen]; omega
          omega
        exact (Nat.mul_le_mul hl7 hp).trans_eq
          (by rw [Nat.mul_assoc 7, Nat.mul_left_comm (packLen x), ← Nat.mul_assoc 7, add_zero])
      · refine BigOLe.of_le fun x => ?_
        rw [length_encNat]
        have h1 : (4 * x.1.2.1).size.size ≤ packScale x := by
          have := size_le_self (4 * x.1.2.1).size; have := size_four_mul_le x.1.2.1
          dsimp only [packScale]; omega
        exact (h1.trans (Nat.le_self_pow (by dsimp only [dsort]; omega) _)).trans
          (Nat.le_mul_of_pos_left _ (by dsimp only [packLen]; omega))
  have hU : ComputableInO (fun x : PackInput => x.1.1) encPackInput encNat
      (fun x => (encPackInput x).length) (fun x => (encPackInput x).length) :=
    (ComputableInO.fst encNat (encPair encNat encNat)).comp_linear
      (ComputableInO.fst _ encIntTriple)
  have hpairSort : ComputableInO
      (fun x : PackInput =>
        (x.1.1, radixSortBy Prod.fst (4 * x.1.2.1).size
          (rawTagItems x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2)))
      encPackInput (encPair encNat (encList encTagItem))
      (fun x => packLen x * packScale x ^ (dsort + 1))
      (fun x => packLen x * packScale x ^ (dsort + 1)) := by
    refine (hU.prod hsort').weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear 17 0 fun x => ?_
      have hS1 : 1 ≤ packScale x := by dsimp only [packScale]; omega
      have hSD1 : packScale x ≤ packScale x ^ (dsort + 1) := Nat.le_self_pow (by omega) _
      have hin : (encPackInput x).length ≤ 16 * (packLen x * packScale x ^ (dsort + 1)) :=
        (length_encPackInput_le x).trans (by nlinarith [Nat.mul_le_mul_left (packLen x) hSD1])
      have hs := Nat.mul_le_mul_left (packLen x)
        (Nat.pow_le_pow_right hS1 (by omega : dsort ≤ dsort + 1))
      omega
  obtain ⟨dps, hps⟩ := computableInO_packStream
  let D := dsort + dps + 2
  have hcomp := (hps.comp hpairSort).of_enc_eq
    (g := fun x : PackInput => oneArrayList x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2)
    fun _ => rfl
  refine ⟨D, hcomp.weaken ?_ ?_⟩
  all_goals
    refine BigOLe.add ?_ ?_
    · exact BigOLe.of_le fun x => Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by dsimp only [packScale]; omega) (by dsimp only [D]; omega))
    · refine BigOLe.of_le_linear (7 * 6 ^ dps) 0 fun x => ?_
      let Srt := radixSortBy Prod.fst (4 * x.1.2.1).size
        (rawTagItems x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2)
      have hlm : listMax (fun a => (encTagItem a).length) Srt ≤ 4 * packScale x :=
        listMax_le fun a ha => hraw_elem x a ((mem_radixSortBy ..).mp ha)
      have hbase : x.1.1.size + listMax (fun a => (encTagItem a).length) Srt + 8 ≤
          6 * packScale x := by dsimp only [packScale] at *; omega
      have hp : (x.1.1.size + listMax (fun a => (encTagItem a).length) Srt + 8) ^ dps ≤
          6 ^ dps * packScale x ^ D :=
        (Nat.pow_le_pow_left hbase dps).trans ((Nat.mul_pow 6 _ dps).le.trans
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by dsimp only [packScale]; omega)
            (by dsimp only [D]; omega))))
      have hlenSrt : Srt.length + 1 ≤ 7 * packLen x := by
        dsimp only [Srt]; rw [length_radixSortBy]
        have := hraw_len x; dsimp only [packLen] at *; omega
      change (Srt.length + 1) *
          (x.1.1.size + listMax (fun a => (encTagItem a).length) Srt + 8) ^ dps ≤
        7 * 6 ^ dps * (packLen x * packScale x ^ D) + 0
      calc _ ≤ (7 * packLen x) * (6 ^ dps * packScale x ^ D) := Nat.mul_le_mul hlenSrt hp
        _ = 7 * 6 ^ dps * (packLen x * packScale x ^ D) + 0 := by
          rw [Nat.mul_assoc 7, Nat.mul_left_comm (packLen x), ← Nat.mul_assoc 7, add_zero]

end CslibFrontier.Complexity
