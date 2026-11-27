module

public import Cslib.Probability.PMF
public import CslibFrontier.Computability.Probabilistic.UniformNat
public import Mathlib.Data.Finset.Card

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Choose
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Combinatorial Subset Unranking and Approximate Uniform PPT Sampling

This module formalizes lexicographic combinatorial unranking of `n`-element subsets of `Fin m`
and an `IsPPTOn` approximate uniform `n`-subset sampler:

* `CslibFrontier.Computability.Probabilistic.Sampling.unrankSubset`: lexicographic unranking from
  `Fin (m.choose n)` to sorted lists of `n` elements in `Fin m`.
* `CslibFrontier.Computability.Probabilistic.Sampling.unrankSubsetEquiv`:
  bijection between `Fin (m.choose n)` and
  `{S : Finset (Fin m) // S.card = n}`.
* `CslibFrontier.Computability.Probabilistic.Sampling.computableInPolyTime_unrankSubset`:
  uniform polynomial-time
  certificate on unary `(m, n)` and binary `r`.
* `CslibFrontier.Computability.Probabilistic.Sampling.sampleSubsetProgram`,
  `CslibFrontier.Computability.Probabilistic.Sampling.isPPTOn_sampleSubsetProgram`,
  `CslibFrontier.Computability.Probabilistic.Sampling.dist_eval_sampleSubsetProgram_le`:
  strict PPT approximate uniform `n`-subset sampler with statistical distance at most
  `(m.choose n) / 2 ^ width`.

All results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Main definitions

* `CslibFrontier.Computability.Probabilistic.Sampling.unrankSubsetStep`,
  `CslibFrontier.Computability.Probabilistic.Sampling.unrankSubset`,
  `CslibFrontier.Computability.Probabilistic.Sampling.listToFinsetFin`,
  `CslibFrontier.Computability.Probabilistic.Sampling.unrankSubsetEquiv`,
  `CslibFrontier.Computability.Probabilistic.Sampling.sampleSubsetProgram`.

## Main results

* `CslibFrontier.Computability.Probabilistic.Sampling.computableInPolyTime_unrankSubset`
* `CslibFrontier.Computability.Probabilistic.Sampling.isPPTOn_sampleSubsetProgram`
* `CslibFrontier.Computability.Probabilistic.Sampling.dist_eval_sampleSubsetProgram_le`

## Tags

combinatorial unranking, subset sampling, PPT, statistical distance, derandomization
-/

public section

namespace CslibFrontier.Computability.Probabilistic.Sampling

open Finset Cslib.Probability

section SubsetUnranking

/-- One step of combinatorial subset unranking over `Fin m`. -/
def unrankSubsetStep (m : ℕ) (state : ℕ × ℕ × List ℕ) (i : ℕ) : ℕ × ℕ × List ℕ :=
  let rem := state.1
  let r := state.2.1
  let acc := state.2.2
  if rem = 0 then (0, r, acc)
  else
    let c := (m - 1 - i).choose (rem - 1)
    if r < c then (rem - 1, r, acc ++ [i]) else (rem, r - c, acc)

/-- Combinatorial unranking of the `r`-th `n`-subset of `Fin m` as a sorted list of `ℕ`. -/
def unrankSubset (m n r : ℕ) : List ℕ :=
  ((List.range m).foldl (unrankSubsetStep m) (n, r, [])).2.2

@[simp]
theorem unrankSubset_zero (m r : ℕ) : unrankSubset m 0 r = [] := by
  unfold unrankSubset
  have hconst : ∀ (l : List ℕ) (r' : ℕ) (acc : List ℕ),
      (l.foldl (unrankSubsetStep m) (0, r', acc)).2.2 = acc := by
    intro l
    induction l with
    | nil => intros; rfl
    | cons x xs ih => intro r' acc; simp [unrankSubsetStep, ih]
  exact hconst _ _ _

/-- Recursive specification of `unrankSubset` starting at offset `lo` over `len` elements. -/
def unrankSubsetAux (lo : ℕ) : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | len + 1, rem, r =>
    if rem = 0 then []
    else
      let c := len.choose (rem - 1)
      if r < c then lo :: unrankSubsetAux (lo + 1) len (rem - 1) r
      else unrankSubsetAux (lo + 1) len rem (r - c)

private lemma foldl_unrankSubsetStep_eq (len lo rem r : ℕ) (acc : List ℕ)
    (hrem : rem ≤ len) (hr : r < len.choose rem) :
    (((List.range len).map (· + lo)).foldl (unrankSubsetStep (lo + len)) (rem, r, acc)).2.2 =
      acc ++ unrankSubsetAux lo len rem r := by
  induction len generalizing lo rem r acc with
  | zero =>
    have h0 : rem = 0 := by omega
    subst h0; simp [unrankSubsetAux]
  | succ len ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.foldl_cons]
    simp only [zero_add, unrankSubsetStep, unrankSubsetAux]
    by_cases hrem0 : rem = 0
    · simp only [hrem0, ↓reduceIte, List.append_nil]
      have hconst : ∀ (l : List ℕ) (r' : ℕ) (a' : List ℕ),
          (l.foldl (unrankSubsetStep (lo + (len + 1))) (0, r', a')).2.2 = a' := by
        intro l
        induction l with
        | nil => intros; rfl
        | cons x xs ihxs => intro r' a'; simp [unrankSubsetStep, ihxs]
      exact hconst _ _ _
    · have hsub : lo + (len + 1) - 1 - lo = len := by omega
      simp only [hrem0, ↓reduceIte, hsub]
      have hmap : List.map (· + lo) (List.map (· + 1) (List.range len)) =
          List.map (· + (lo + 1)) (List.range len) := by
        rw [List.map_map]
        refine List.map_congr_left fun x _ ↦ by dsimp; omega
      have hlen_eq : lo + (len + 1) = (lo + 1) + len := by omega
      rw [hmap, hlen_eq]
      split_ifs with hlt
      · have hrem1 : rem - 1 ≤ len := by
          by_contra hgt
          have : len.choose (rem - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          omega
        rw [ih (lo + 1) (rem - 1) r (acc ++ [lo]) hrem1 hlt, List.append_assoc,
          List.singleton_append]
      · have hpascal : (len + 1).choose rem = len.choose (rem - 1) + len.choose rem := by
          obtain ⟨rem', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hrem0
          simpa [Nat.add_comm] using Nat.choose_succ_succ len rem'
        have hr' : r - len.choose (rem - 1) < len.choose rem := by omega
        have hrem' : rem ≤ len := by
          by_contra hgt
          have : len.choose rem = 0 := Nat.choose_eq_zero_of_lt (by omega)
          omega
        exact ih (lo + 1) rem (r - len.choose (rem - 1)) acc hrem' hr'

private lemma unrankSubset_eq_aux {m n r : ℕ} (hn : n ≤ m) (hr : r < m.choose n) :
    unrankSubset m n r = unrankSubsetAux 0 m n r := by
  have h := foldl_unrankSubsetStep_eq m 0 n r [] hn hr
  simpa [unrankSubset] using h

private lemma unrankSubsetAux_spec (lo len rem r : ℕ) (hrem : rem ≤ len)
    (hr : r < len.choose rem) :
    (unrankSubsetAux lo len rem r).length = rem ∧
    (unrankSubsetAux lo len rem r).Pairwise (· < ·) ∧
    (∀ x ∈ unrankSubsetAux lo len rem r, lo ≤ x ∧ x < lo + len) := by
  induction len generalizing lo rem r with
  | zero =>
    have h0 : rem = 0 := by omega
    subst h0; simp [unrankSubsetAux]
  | succ len ih =>
    unfold unrankSubsetAux
    by_cases hrem0 : rem = 0
    · simp [hrem0]
    · simp only [hrem0, ↓reduceIte]
      split_ifs with hlt
      · have hrem1 : rem - 1 ≤ len := by
          by_contra hgt
          have : len.choose (rem - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          omega
        obtain ⟨hlen, hpw, hmem⟩ := ih (lo + 1) (rem - 1) r hrem1 hlt
        refine ⟨by simp [hlen]; omega, ?_, ?_⟩
        · rw [List.pairwise_cons]
          exact ⟨fun x hx ↦ by have := (hmem x hx).1; omega, hpw⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · omega
          · have := hmem x hx; omega
      · have hpascal : (len + 1).choose rem = len.choose (rem - 1) + len.choose rem := by
          obtain ⟨rem', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hrem0
          simpa [Nat.add_comm] using Nat.choose_succ_succ len rem'
        have hr' : r - len.choose (rem - 1) < len.choose rem := by omega
        have hrem' : rem ≤ len := by
          by_contra hgt
          have : len.choose rem = 0 := Nat.choose_eq_zero_of_lt (by omega)
          omega
        obtain ⟨hlen, hpw, hmem⟩ := ih (lo + 1) rem (r - len.choose (rem - 1)) hrem' hr'
        refine ⟨hlen, hpw, fun x hx ↦ ?_⟩
        have := hmem x hx; omega

private lemma unrankSubsetAux_injective (lo len rem : ℕ) {r₁ r₂ : ℕ}
    (hr₁ : r₁ < len.choose rem) (hr₂ : r₂ < len.choose rem)
    (heq : unrankSubsetAux lo len rem r₁ = unrankSubsetAux lo len rem r₂) : r₁ = r₂ := by
  induction len generalizing lo rem r₁ r₂ with
  | zero =>
    rcases Nat.eq_zero_or_pos rem with rfl | hpos
    · simp at hr₁ hr₂; omega
    · simp [Nat.choose_eq_zero_of_lt hpos] at hr₁
  | succ len ih =>
    by_cases hrem0 : rem = 0
    · subst hrem0; simp at hr₁ hr₂; omega
    · have hpascal : (len + 1).choose rem = len.choose (rem - 1) + len.choose rem := by
        obtain ⟨rem', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hrem0
        simpa [Nat.add_comm] using Nat.choose_succ_succ len rem'
      simp only [unrankSubsetAux, hrem0, ↓reduceIte] at heq
      split_ifs at heq with h1 h2
      · exact ih (lo + 1) (rem - 1) h1 h2 (List.cons.inj heq).2
      · exfalso
        have hrem' : rem ≤ len := by
          by_contra hgt; have := Nat.choose_eq_zero_of_lt (by omega : len < rem); omega
        have hmem := (unrankSubsetAux_spec (lo + 1) len rem (r₂ - len.choose (rem - 1))
          hrem' (by omega)).2.2 lo (heq ▸ List.mem_cons_self)
        omega
      · exfalso
        have hrem' : rem ≤ len := by
          by_contra hgt; have := Nat.choose_eq_zero_of_lt (by omega : len < rem); omega
        have hmem := (unrankSubsetAux_spec (lo + 1) len rem (r₁ - len.choose (rem - 1))
          hrem' (by omega)).2.2 lo (heq.symm ▸ List.mem_cons_self)
        omega
      · have hsub := ih (lo + 1) rem (by omega : r₁ - len.choose (rem - 1) < len.choose rem)
          (by omega) heq
        omega

theorem unrankSubset_length {m n r : ℕ} (hn : n ≤ m) (hr : r < m.choose n) :
    (unrankSubset m n r).length = n := by
  rw [unrankSubset_eq_aux hn hr]
  exact (unrankSubsetAux_spec 0 m n r hn hr).1

theorem unrankSubset_pairwise_lt {m n r : ℕ} (hn : n ≤ m) (hr : r < m.choose n) :
    (unrankSubset m n r).Pairwise (· < ·) := by
  rw [unrankSubset_eq_aux hn hr]
  exact (unrankSubsetAux_spec 0 m n r hn hr).2.1

theorem unrankSubset_lt {m n r : ℕ} (hn : n ≤ m) (hr : r < m.choose n) :
    ∀ x ∈ unrankSubset m n r, x < m := by
  rw [unrankSubset_eq_aux hn hr]
  intro x hx
  have := (unrankSubsetAux_spec 0 m n r hn hr).2.2 x hx
  omega

/-- Convert a list of naturals `< m` to a `Finset (Fin m)` via `pmap`. -/
def listToFinsetFin (m : ℕ) (l : List ℕ) : Finset (Fin m) :=
  (l.filter (· < m)).pmap (fun x hx ↦ ⟨x, by simpa using hx⟩)
    (fun x hx ↦ (List.mem_filter.mp hx).2 |> of_decide_eq_true) |>.toFinset

@[simp]
theorem listToFinsetFin_nil (m : ℕ) : listToFinsetFin m [] = ∅ := by
  simp [listToFinsetFin]

theorem mem_listToFinsetFin_iff (m : ℕ) (l : List ℕ) (x : Fin m) :
    x ∈ listToFinsetFin m l ↔ x.val ∈ l := by
  simp only [listToFinsetFin, List.mem_toFinset, List.mem_pmap, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨y, ⟨hy, _⟩, rfl⟩
    exact hy
  · intro hx
    exact ⟨x.val, ⟨hx, x.isLt⟩, rfl⟩

theorem card_listToFinsetFin_unrankSubset {m n r : ℕ} (hn : n ≤ m) (hr : r < m.choose n) :
    (listToFinsetFin m (unrankSubset m n r)).card = n := by
  have hlt := unrankSubset_lt hn hr
  have hfilt : (unrankSubset m n r).filter (· < m) = unrankSubset m n r :=
    List.filter_eq_self.mpr fun x hx ↦ decide_eq_true (hlt x hx)
  have hpw := unrankSubset_pairwise_lt hn hr
  have hnd : (unrankSubset m n r).Nodup := hpw.imp (fun h ↦ Nat.ne_of_lt h)
  unfold listToFinsetFin
  simp only [hfilt]
  rw [List.toFinset_card_of_nodup]
  · rw [List.length_pmap, unrankSubset_length hn hr]
  · exact hnd.pmap fun a _ b _ h ↦ congrArg Fin.val h

theorem listToFinsetFin_unrankSubset_inj {m n : ℕ} (hn : n ≤ m) {r₁ r₂ : ℕ}
    (hr₁ : r₁ < m.choose n) (hr₂ : r₂ < m.choose n)
    (h : listToFinsetFin m (unrankSubset m n r₁) = listToFinsetFin m (unrankSubset m n r₂)) :
    r₁ = r₂ := by
  have h1 := unrankSubset_eq_aux hn hr₁
  have h2 := unrankSubset_eq_aux hn hr₂
  have hpw1 := unrankSubset_pairwise_lt hn hr₁
  have hpw2 := unrankSubset_pairwise_lt hn hr₂
  have hlt1 := unrankSubset_lt hn hr₁
  have hlt2 := unrankSubset_lt hn hr₂
  have hmem_eq : ∀ x : ℕ, x ∈ unrankSubset m n r₁ ↔ x ∈ unrankSubset m n r₂ := by
    intro x
    by_cases hx : x < m
    · have := Finset.ext_iff.mp h ⟨x, hx⟩
      simpa only [mem_listToFinsetFin_iff] using this
    · exact ⟨fun hm ↦ (hx (hlt1 x hm)).elim, fun hm ↦ (hx (hlt2 x hm)).elim⟩
  have hlist_eq : unrankSubset m n r₁ = unrankSubset m n r₂ :=
    ((List.perm_ext_iff_of_nodup (hpw1.imp fun h ↦ Nat.ne_of_lt h)
      (hpw2.imp fun h ↦ Nat.ne_of_lt h)).mpr hmem_eq).eq_of_pairwise
      (fun _ _ _ _ ↦ le_antisymm)
      (hpw1.imp fun h ↦ Nat.le_of_lt h)
      (hpw2.imp fun h ↦ Nat.le_of_lt h)
  rw [h1, h2] at hlist_eq
  exact unrankSubsetAux_injective 0 m n hr₁ hr₂ hlist_eq

/-- Bijection between `Fin (m.choose n)` and the `n`-element subsets of `Fin m`. -/
noncomputable def unrankSubsetEquiv (m n : ℕ) (hn : n ≤ m) :
    Fin (m.choose n) ≃ {S : Finset (Fin m) // S.card = n} := by
  have hcard : Fintype.card (Fin (m.choose n)) =
      Fintype.card {S : Finset (Fin m) // S.card = n} := by
    rw [Fintype.card_fin]
    have h1 : Fintype.card {S : Finset (Fin m) // S.card = n} =
        (Finset.powersetCard n (Finset.univ : Finset (Fin m))).card := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr
        (Equiv.subtypeEquivRight fun S ↦ by simp [Finset.mem_powersetCard])
    rw [h1, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  refine Equiv.ofBijective
    (fun r : Fin (m.choose n) ↦
      ⟨listToFinsetFin m (unrankSubset m n r.val),
        card_listToFinsetFin_unrankSubset hn r.isLt⟩) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨fun r₁ r₂ heq ↦ Fin.ext (listToFinsetFin_unrankSubset_inj hn r₁.isLt r₂.isLt
    (congrArg Subtype.val heq)), hcard⟩

@[simp]
theorem unrankSubsetEquiv_apply_val (m n : ℕ) (hn : n ≤ m) (r : Fin (m.choose n)) :
    (unrankSubsetEquiv m n hn r).1 = listToFinsetFin m (unrankSubset m n r.val) := by
  rfl

/-- `unrankSubset` is uniformly polynomial-time on unary `(m, n)` and binary `r`. -/
theorem computableInPolyTime_unrankSubset :
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ ↦ unrankSubset p.1.1 p.1.2 p.2)
      (Turing.MultiTapeTM.encPair
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary)
        Turing.MultiTapeTM.encNat)
      (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encUnary) := by
  open Turing.MultiTapeTM ComputableInPolyTime in
  let encP := encPair (encPair encUnary encUnary) encNat
  let encS := encPair encUnary (encPair encNat (encList encUnary))
  let encQ := encPair (encPair encUnary encS) encUnary
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × (ℕ × (ℕ × List ℕ))) × ℕ ↦ unrankSubsetStep q.1.1 q.1.2 q.2)
      encQ encS := by
    have hm : ComputableInPolyTime (fun q : (ℕ × (ℕ × (ℕ × List ℕ))) × ℕ ↦ q.1.1)
        encQ encUnary := (fst encUnary encS).comp (fst _ _)
    have hs : ComputableInPolyTime (fun q : (ℕ × (ℕ × (ℕ × List ℕ))) × ℕ ↦ q.1.2)
        encQ encS := (snd encUnary encS).comp (fst _ _)
    have hi : ComputableInPolyTime (fun q : (ℕ × (ℕ × (ℕ × List ℕ))) × ℕ ↦ q.2)
        encQ encUnary := snd _ _
    have hrem : ComputableInPolyTime (fun q : (ℕ × (ℕ × (ℕ × List ℕ))) × ℕ ↦ q.1.2.1)
        encQ encUnary := (fst encUnary _).comp hs
    have hr : ComputableInPolyTime (fun q : (ℕ × (ℕ × (ℕ × List ℕ))) × ℕ ↦ q.1.2.2.1)
        encQ encNat := (fst encNat _).comp ((snd encUnary _).comp hs)
    have hacc : ComputableInPolyTime (fun q : (ℕ × (ℕ × (ℕ × List ℕ))) × ℕ ↦ q.1.2.2.2)
        encQ (encList encUnary) := (snd encNat _).comp ((snd encUnary _).comp hs)
    have hm1 : ComputableInPolyTime (fun q : (ℕ × (ℕ × (ℕ × List ℕ))) × ℕ ↦ q.1.1 - 1 - q.2)
        encQ encUnary := unary_sub.comp ((unary_sub.comp (hm.prod (const 1))).prod hi)
    have hrem1 : ComputableInPolyTime (fun q : (ℕ × (ℕ × (ℕ × List ℕ))) × ℕ ↦ q.1.2.1 - 1)
        encQ encUnary := unary_sub.comp (hrem.prod (const 1))
    have hc : ComputableInPolyTime
        (fun q : (ℕ × (ℕ × (ℕ × List ℕ))) × ℕ ↦ (q.1.1 - 1 - q.2).choose (q.1.2.1 - 1))
        encQ encNat := binary_choose' hm1 hrem1
    have hcond0 : ComputableInPolyTime
        (fun q : (ℕ × (ℕ × (ℕ × List ℕ))) × ℕ ↦ q.1.2.1 == 0)
        encQ encBool := unary_beq hrem (const 0)
    have hcond_lt : ComputableInPolyTime
        (fun q : (ℕ × (ℕ × (ℕ × List ℕ))) × ℕ ↦ decide (q.1.2.2.1 <
          (q.1.1 - 1 - q.2).choose (q.1.2.1 - 1)))
        encQ encBool := binary_lt' hr hc
    have hbranch0 : ComputableInPolyTime
        (fun q : (ℕ × (ℕ × (ℕ × List ℕ))) × ℕ ↦ (0, q.1.2.2.1, q.1.2.2.2))
        encQ encS := (const 0).prod (hr.prod hacc)
    have hbranch_lt : ComputableInPolyTime
        (fun q : (ℕ × (ℕ × (ℕ × List ℕ))) × ℕ ↦ (q.1.2.1 - 1, q.1.2.2.1, q.1.2.2.2 ++ [q.2]))
        encQ encS := hrem1.prod (hr.prod (listAppend' hacc (cons' hi (const []))))
    have hbranch_ge : ComputableInPolyTime
        (fun q : (ℕ × (ℕ × (ℕ × List ℕ))) × ℕ ↦
          (q.1.2.1, q.1.2.2.1 - (q.1.1 - 1 - q.2).choose (q.1.2.1 - 1), q.1.2.2.2))
        encQ encS := hrem.prod ((binary_sub' hr hc).prod hacc)
    have houter := ite hcond0 hbranch0 (ite hcond_lt hbranch_lt hbranch_ge)
    refine houter.of_enc_eq fun q ↦ congrArg encS ?_
    unfold unrankSubsetStep
    simp only [beq_iff_eq, decide_eq_true_eq]
  have hinit : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ ↦ (p.1.2, p.2, ([] : List ℕ))) encP encS :=
    ((snd encUnary encUnary).comp (fst _ _)).prod ((snd _ _).prod (const []))
  have hpar : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ ↦ p.1.1) encP encUnary :=
    (fst encUnary encUnary).comp (fst _ _)
  have hfold := foldlWith_of_bounded_growth (encA := encUnary) (encL := encList encUnary)
    (encB := encS) (encP := encUnary) (encIn := encP)
    (par := fun p ↦ p.1.1) (list := fun p ↦ List.range p.1.1)
    (step := unrankSubsetStep)
    hpar (range.comp hpar) hinit hstep
    (growth := fun p ↦ (encP p).length + 2 * p.1.1 + 4)
    (by
      refine PolyBounded.add (PolyBounded.add .self ?_) (.const 4)
      have h1 : PolyBounded (fun p : (ℕ × ℕ) × ℕ ↦ (encP p).length) (fun p ↦ p.1.1) := by
        simpa only [encUnary_apply, List.length_replicate] using hpar.polyBounded_length
      exact PolyBounded.mul (.const 2) h1)
    (fun p s i hi ↦ by
      have hi_lt : i < p.1.1 := List.mem_range.mp hi
      unfold unrankSubsetStep
      dsimp only
      split_ifs with h0 hlt
      · simp only [encS, length_encPair, encUnary_apply, List.length_replicate]
        omega
      · simp only [encS, length_encPair, encUnary_apply, List.length_replicate,
          length_encList, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
        omega
      · simp only [encS, length_encPair, encUnary_apply, List.length_replicate,
          encNat_apply]
        have hsub : (s.2.1 - (p.1.1 - 1 - i).choose (s.1 - 1)).bits.length ≤ s.2.1.bits.length := by
          rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
          exact Nat.size_le_size (Nat.sub_le _ _)
        omega)
  exact (snd encNat (encList encUnary)).comp ((snd encUnary _).comp hfold)

/-- PPT sampler for an approximately uniform `n`-subset of `Fin m` using `width` fair bits. -/
noncomputable def sampleSubsetProgram (m n width : ℕ) : Cslib.ProbComp (List ℕ) :=
  unrankSubset m n <$> Cslib.ProbComp.sampleModNat width (m.choose n)

theorem eval_sampleSubsetProgram (m n width : ℕ) :
    Cslib.ProbComp.eval (sampleSubsetProgram m n width) =
      (Cslib.ProbComp.eval (Cslib.ProbComp.sampleModNat width (m.choose n))).map
        (unrankSubset m n) := by
  simp [sampleSubsetProgram, Cslib.ProbComp.eval_map]

/-- `sampleSubsetProgram` is uniformly `IsPPTOn` for polynomial-time unary `(m, n, width)`. -/
theorem isPPTOn_sampleSubsetProgram {α : Type} {input : α ↪ List Bool}
    {m n width : α → ℕ}
    (hm : Turing.MultiTapeTM.ComputableInPolyTime m input Turing.MultiTapeTM.encUnary)
    (hn : Turing.MultiTapeTM.ComputableInPolyTime n input Turing.MultiTapeTM.encUnary)
    (hwidth : Turing.MultiTapeTM.ComputableInPolyTime width input Turing.MultiTapeTM.encUnary) :
    IsPPTOn input (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encUnary)
      (fun a ↦ sampleSubsetProgram (m a) (n a) (width a)) := by
  have hmod : Turing.MultiTapeTM.ComputableInPolyTime (fun a ↦ (m a).choose (n a))
      input Turing.MultiTapeTM.encNat :=
    Turing.MultiTapeTM.ComputableInPolyTime.binary_choose' hm hn
  have hsample := isPPTOn_sampleModNat hwidth hmod
  have hpair : Turing.MultiTapeTM.ComputableInPolyTime
      (fun p : α × ℕ ↦ ((m p.1, n p.1), p.2))
      (Turing.MultiTapeTM.encPair input Turing.MultiTapeTM.encNat)
      (Turing.MultiTapeTM.encPair
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary)
        Turing.MultiTapeTM.encNat) :=
    ((hm.comp' (Turing.MultiTapeTM.ComputableInPolyTime.fst input
        Turing.MultiTapeTM.encNat)).prod
      (hn.comp' (Turing.MultiTapeTM.ComputableInPolyTime.fst input
        Turing.MultiTapeTM.encNat))).prod
      (Turing.MultiTapeTM.ComputableInPolyTime.snd input Turing.MultiTapeTM.encNat)
  have hcb_raw := computableInPolyTime_unrankSubset.comp' hpair
  have hcb : Turing.MultiTapeTM.ComputableInPolyTime
      (fun p : α × ℕ ↦ unrankSubset (m p.1) (n p.1) p.2)
      (Turing.MultiTapeTM.encPair input Turing.MultiTapeTM.encNat)
      (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encUnary) := hcb_raw
  have hres := hsample.map_with (f := fun a r ↦ unrankSubset (m a) (n a) r) hcb
  unfold sampleSubsetProgram
  exact hres

open scoped Cslib.Probability.PMF in
/-- Statistical-distance bound for `sampleSubsetProgram` relative to the exact uniform
distribution on `n`-element subsets of `Fin m`. -/
theorem dist_eval_sampleSubsetProgram_le {m n width : ℕ} (hn : n ≤ m) :
    let μ := (Cslib.ProbComp.eval (sampleSubsetProgram m n width)).map (listToFinsetFin m)
    let U := (@PMF.uniformOfFintype {S : Finset (Fin m) // S.card = n} _
      ⟨unrankSubsetEquiv m n hn ⟨0, Nat.choose_pos hn⟩⟩).map Subtype.val
    (1 / 2 : ℝ) * ∑ S : Finset (Fin m), |(μ S).toReal - (U S).toReal| ≤
      (m.choose n : ℝ) / (2 : ℝ) ^ width := by
  intro μ U
  have : NeZero (m.choose n) := ⟨(Nat.choose_pos hn).ne'⟩
  have : Nonempty {S : Finset (Fin m) // S.card = n} :=
    ⟨unrankSubsetEquiv m n hn ⟨0, Nat.choose_pos hn⟩⟩
  have hmod := Cslib.ProbComp.dist_map_natCast_eval_sampleModNat_le width (m.choose n)
  let f : ZMod (m.choose n) → Finset (Fin m) :=
    fun r ↦ listToFinsetFin m (unrankSubset m n r.val)
  have hμ : μ = ((Cslib.ProbComp.eval (Cslib.ProbComp.sampleModNat width (m.choose n))).map
      (Nat.cast : ℕ → ZMod (m.choose n))).map f := by
    dsimp only [μ]
    rw [eval_sampleSubsetProgram, Cslib.ProbComp.eval_sampleModNat,
      PMF.map_comp, PMF.map_comp, PMF.map_comp, PMF.map_comp]
    refine congrArg (PMF.map · _) (funext fun x ↦ ?_)
    dsimp [f, Function.comp_def]
    rw [ZMod.val_natCast_of_lt (Nat.mod_lt x.val (Nat.choose_pos hn))]
  have hU : U = (PMF.uniformOfFintype (ZMod (m.choose n))).map f := by
    let eZ : ZMod (m.choose n) ≃ Fin (m.choose n) :=
      { toFun := fun r ↦ ⟨r.val, r.val_lt⟩
        invFun := fun i ↦ (i.val : ZMod (m.choose n))
        left_inv := fun r ↦ ZMod.natCast_zmod_val r
        right_inv := fun i ↦ Fin.ext (ZMod.val_natCast_of_lt i.isLt) }
    let e : ZMod (m.choose n) ≃ {S : Finset (Fin m) // S.card = n} :=
      eZ.trans (unrankSubsetEquiv m n hn)
    have h1 : PMF.uniformOfFintype {S : Finset (Fin m) // S.card = n} =
        (PMF.uniformOfFintype (ZMod (m.choose n))).map e :=
      (PMF.uniformOfFintype_map_equiv e).symm
    dsimp only [U]
    rw [h1, PMF.map_comp]
    rfl
  rw [hμ, hU]
  have hdpi := Cslib.Probability.PMF.dist_map_le
    ((Cslib.ProbComp.eval (Cslib.ProbComp.sampleModNat width (m.choose n))).map
      (Nat.cast : ℕ → ZMod (m.choose n)))
    (PMF.uniformOfFintype (ZMod (m.choose n))) f
  have hdist_eq :
      (1 / 2 : ℝ) * ∑ S : Finset (Fin m),
        |((((Cslib.ProbComp.eval (Cslib.ProbComp.sampleModNat width (m.choose n))).map
            (Nat.cast : ℕ → ZMod (m.choose n))).map f) S).toReal -
          (((PMF.uniformOfFintype (ZMod (m.choose n))).map f) S).toReal| =
        dist (((Cslib.ProbComp.eval (Cslib.ProbComp.sampleModNat width (m.choose n))).map
            (Nat.cast : ℕ → ZMod (m.choose n))).map f)
          ((PMF.uniformOfFintype (ZMod (m.choose n))).map f) := by
    rw [Cslib.Probability.PMF.dist_eq]; ring
  rw [hdist_eq]
  exact hdpi.trans hmod

end SubsetUnranking

end CslibFrontier.Computability.Probabilistic.Sampling
