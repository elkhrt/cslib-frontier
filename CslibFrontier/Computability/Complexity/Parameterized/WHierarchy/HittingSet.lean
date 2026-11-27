/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google LLC
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.HittingSet
public import CslibFrontier.Computability.Circuit.Boolean.Unbounded.WeftTwoCertificates
import CslibFrontier.Computability.Circuit.Encoding.Layer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.ListsUpTo
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# `W[2]`-Hardness and `W[2]`-Completeness of Hitting Set and Set Cover

Under standard Lean axioms, this module proves that **Hitting Set** and **Set Cover** are
`W[2]`-hard (and hence **`W[2]`-complete** when combined with `hittingSet_mem_W` and
`setCover_mem_W` from `CslibFrontier.Computability.Complexity.Problems.HittingSet`):

1. **FPT reduction from `WCS 2 d` to `HittingSet` (`wcsTwoToHittingSet`)**: for each fixed circuit
   depth `d`, constructs in polynomial time a set system over top-level weft-2 claim certificates
   (`weftTwoCerts`) and index brackets (`WCS.ToClique.brackets (d + 1)`) with hitting budget
   `WCS.ToClique.size (d + 1) n k ≤ (k + 1) ^ 2 ^ (d + 2) + 1`, enforcing:
   - selection of at least one valid weft-2 top-level certificate and one bracket per index list;
   - pairwise consistency across all chosen brackets, uniquely determining a weight-`k` input `x`;
   - refutation of every weft-1 sub-certificate for the negation (`negWire`) of each weft-1 check
     wire of the chosen top-level certificate.
2. **`W[2]`-hardness and collapse equivalence (`hittingSet_wHard`, `setCover_wHard`,
   `W_two_eq_FPT_iff_hittingSet`)**: `HittingSet` and `SetCover` are `W[2]`-hard with parameter `k`,
   and `W[2] = FPT` holds if and only if `HittingSet ∈ FPT`.

## Main definitions

* `Cslib.Complexity.wcsTwoToHittingSet`: parameterized polynomial-time reduction
  from `WCS 2 d` to `HittingSet`.

## Main results

* `Cslib.Complexity.wcsTwoToHittingSet_mem_iff`,
  `Cslib.Complexity.computableInPolyTime_wcsTwoToHittingSet`,
  `Cslib.Complexity.fptReducible_wcsTwo_hittingSet`: correctness, polynomial-time
  computability, and FPT reducibility of `wcsTwoToHittingSet`.
* `Cslib.Complexity.hittingSet_wHard`,
  `Cslib.Complexity.setCover_wHard`: `W[2]`-hardness of `HittingSet` and
  `SetCover`.
* `Cslib.Complexity.W_two_eq_FPT_iff_hittingSet`: `W[2] = FPT` iff `HittingSet` is
  in `FPT`.

## Tags

hitting set, set cover, W[2]-hardness, W[2]-completeness, parameterized complexity
-/

public section

open Cslib Cslib.Complexity Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded
open Turing.MultiTapeTM ComputableInPolyTime

namespace Cslib.Complexity

/-! ### 1. Hitting Set Instance for `WCS 2 d` -/

private structure W2Spec where
  kind : ℕ
  idxList : List ℕ
  pairP : List (ℕ × ℕ)
  pairQ : List (ℕ × ℕ)
  topCl : List (ℕ × Bool)
  subCl : List (ℕ × Bool)
  deriving DecidableEq

private abbrev encIdxList : List ℕ ↪ List Bool := encList encUnary

private abbrev W2SpecTuple : Type :=
  ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × Bool) × List (ℕ × Bool)

private abbrev encW2SpecTuple : W2SpecTuple ↪ List Bool :=
  encPair encUnary (encPair encIdxList (encPair WCS.ToClique.encBracket
    (encPair WCS.ToClique.encBracket
      (encPair WCS.ToClique.encClaimList WCS.ToClique.encClaimList))))

private def w2SpecToTuple (s : W2Spec) : W2SpecTuple :=
  (s.kind, s.idxList, s.pairP, s.pairQ, s.topCl, s.subCl)

private def encW2Spec : W2Spec ↪ List Bool where
  toFun s := encW2SpecTuple (w2SpecToTuple s)
  inj' a b h := by
    have h' := encW2SpecTuple.injective h
    cases a
    cases b
    simp only [w2SpecToTuple, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h'
    rfl

private lemma computableInPolyTime_w2SpecToTuple {γ : Type} {encIn : γ ↪ List Bool}
    {f : γ → W2Spec} (hf : ComputableInPolyTime f encIn encW2Spec) :
    ComputableInPolyTime (fun x => w2SpecToTuple (f x)) encIn encW2SpecTuple :=
  hf.of_enc_eq fun _ => rfl

@[local fun_prop]
private lemma encW2Spec_kind_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {f : γ → W2Spec} (hf : ComputableInPolyTime f encIn encW2Spec) :
    ComputableInPolyTime (fun x => (f x).kind) encIn encUnary :=
  (fst _ _).comp (computableInPolyTime_w2SpecToTuple hf)

@[local fun_prop]
private lemma encW2Spec_idxList_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {f : γ → W2Spec} (hf : ComputableInPolyTime f encIn encW2Spec) :
    ComputableInPolyTime (fun x => (f x).idxList) encIn encIdxList :=
  (fst _ _).comp ((snd _ _).comp (computableInPolyTime_w2SpecToTuple hf))

@[local fun_prop]
private lemma encW2Spec_pairP_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {f : γ → W2Spec} (hf : ComputableInPolyTime f encIn encW2Spec) :
    ComputableInPolyTime (fun x => (f x).pairP) encIn WCS.ToClique.encBracket :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (computableInPolyTime_w2SpecToTuple hf)))

@[local fun_prop]
private lemma encW2Spec_pairQ_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {f : γ → W2Spec} (hf : ComputableInPolyTime f encIn encW2Spec) :
    ComputableInPolyTime (fun x => (f x).pairQ) encIn WCS.ToClique.encBracket :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp
    (computableInPolyTime_w2SpecToTuple hf))))

@[local fun_prop]
private lemma encW2Spec_topCl_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {f : γ → W2Spec} (hf : ComputableInPolyTime f encIn encW2Spec) :
    ComputableInPolyTime (fun x => (f x).topCl) encIn WCS.ToClique.encClaimList :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp
    (computableInPolyTime_w2SpecToTuple hf)))))

@[local fun_prop]
private lemma encW2Spec_subCl_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {f : γ → W2Spec} (hf : ComputableInPolyTime f encIn encW2Spec) :
    ComputableInPolyTime (fun x => (f x).subCl) encIn WCS.ToClique.encClaimList :=
  (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp
    (computableInPolyTime_w2SpecToTuple hf)))))

@[local fun_prop]
private lemma encW2Spec_mk_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {k : γ → ℕ} {il : γ → List ℕ} {pP pQ : γ → List (ℕ × ℕ)}
    {tC sC : γ → List (ℕ × Bool)}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hil : ComputableInPolyTime il encIn encIdxList)
    (hpP : ComputableInPolyTime pP encIn WCS.ToClique.encBracket)
    (hpQ : ComputableInPolyTime pQ encIn WCS.ToClique.encBracket)
    (htC : ComputableInPolyTime tC encIn WCS.ToClique.encClaimList)
    (hsC : ComputableInPolyTime sC encIn WCS.ToClique.encClaimList) :
    ComputableInPolyTime (fun x => W2Spec.mk (k x) (il x) (pP x) (pQ x) (tC x) (sC x))
      encIn encW2Spec :=
  (hk.prod (hil.prod (hpP.prod (hpQ.prod (htC.prod hsC))))).of_enc_eq fun _ => rfl

private def w2Vertices (d n kk : ℕ) (gates : List (Unbounded.Op × List ℕ)) (o : ℕ) :
    List WCS.ToClique.Vertex :=
  (weftTwoCerts d n gates o).map (fun cl => ⟨true, cl, []⟩) ++
    (WCS.ToClique.brackets (d + 1) n kk).map (fun P => ⟨false, [], P⟩)

private def w2Specs (d n kk : ℕ) (gates : List (Unbounded.Op × List ℕ)) (o : ℕ) :
    List W2Spec :=
  let topCerts := weftTwoCerts d n gates o
  let brs := WCS.ToClique.brackets (d + 1) n kk
  let idxLs := WCS.ToClique.indexLists (d + 1) kk
  let gExt := gatesWithNeg n gates
  let s0 : List W2Spec := [⟨0, [], [], [], [], []⟩]
  let s1 : List W2Spec := idxLs.map fun C => ⟨1, C, [], [], [], []⟩
  let s2 : List W2Spec := brs.flatMap fun P =>
    (brs.filter fun Q =>
      decide (P.map Prod.fst ≠ Q.map Prod.fst) && !WCS.ToClique.consistent P Q).map
      fun Q => ⟨2, [], P, Q, [], []⟩
  let s3 : List W2Spec := topCerts.flatMap fun topCl =>
    (topCl.flatMap (WeftOne.claimChecks n gates)).flatMap fun e =>
      (WCS.ToClique.certs (d + 1) n gExt (negWire n gates.length e)).map fun subCl =>
        ⟨3, [], [], [], topCl, subCl⟩
  s0 ++ s1 ++ s2 ++ s3

private def w2Mem (n kk : ℕ) (gates : List (Unbounded.Op × List ℕ))
    (sp : W2Spec) (v : WCS.ToClique.Vertex) : Bool :=
  if sp.kind == 0 then
    v.isCert
  else if sp.kind == 1 then
    !v.isCert && decide (v.bracket.map Prod.fst = sp.idxList)
  else if sp.kind == 2 then
    !v.isCert &&
      ((decide (v.bracket.map Prod.fst = sp.pairP.map Prod.fst) && decide (v.bracket ≠ sp.pairP)) ||
       (decide (v.bracket.map Prod.fst = sp.pairQ.map Prod.fst) && decide (v.bracket ≠ sp.pairQ)))
  else
    (v.isCert && decide (v.claims ≠ sp.topCl)) ||
      (!v.isCert && WCS.ToClique.refutes n kk (gatesWithNeg n gates) sp.subCl v.bracket)

private def w2System (d n : ℕ) (gates : List (Unbounded.Op × List ℕ)) (o k : ℕ) :
    SetSystem × ℕ :=
  let kk := min (n + 1) k
  (ofSpecSetSystem (w2Vertices d n kk gates o) (w2Specs d n kk gates o) (w2Mem n kk gates),
    WCS.ToClique.size (d + 1) n k)

/-- FPT reduction from `WCS 2 d` to `HittingSet`. -/
def wcsTwoToHittingSet {d : ℕ} (x : WCSInstance 2 d) : SetSystem × ℕ :=
  w2System d x.circuit.toCircuit.1 x.circuit.toCircuit.2.code.1
    (x.circuit.toCircuit.2.outputs 0).toNat x.weight

private lemma mem_w2Vertices {d n kk : ℕ} {gates : List (Unbounded.Op × List ℕ)} {o : ℕ}
    {v : WCS.ToClique.Vertex} :
    v ∈ w2Vertices d n kk gates o ↔
      (v.isCert = true ∧ v.bracket = [] ∧ v.claims ∈ weftTwoCerts d n gates o) ∨
      (v.isCert = false ∧ v.claims = [] ∧ v.bracket ∈ WCS.ToClique.brackets (d + 1) n kk) := by
  obtain ⟨b, cl, P⟩ := v
  simp only [w2Vertices, List.mem_append, List.mem_map, WCS.ToClique.Vertex.mk.injEq]
  constructor
  · rintro (⟨cl', h, rfl, rfl, rfl⟩ | ⟨P', h, rfl, rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl, h⟩
    · exact Or.inr ⟨rfl, rfl, h⟩
  · rintro (⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩)
    · exact Or.inl ⟨cl, h, rfl, rfl, rfl⟩
    · exact Or.inr ⟨P, h, rfl, rfl, rfl⟩

private lemma exists_strictMonoOn_enum_nat (T : Finset ℕ) :
    ∃ u : ℕ → ℕ, StrictMonoOn u (Set.Iio T.card) ∧
      ∀ s, s ∈ T ↔ ∃ i < T.card, u i = s := by
  classical
  let e := T.orderEmbOfFin rfl
  refine ⟨fun j => if h : j < T.card then e ⟨j, h⟩ else 0, ?_, fun s => ?_⟩
  · intro i hi j hj hij
    simp only [Set.mem_Iio] at hi hj
    simp only [hi, hj, dite_true]
    exact e.strictMono (Fin.mk_lt_mk.2 hij)
  · constructor
    · intro hs
      obtain ⟨i, hi⟩ := (Finset.range_orderEmbOfFin T rfl ▸ hs : s ∈ Set.range e)
      exact ⟨i.1, i.2, by simp only [i.2, dite_true, Fin.eta]; exact hi⟩
    · rintro ⟨i, hi, rfl⟩
      simp only [hi, dite_true]
      exact Finset.orderEmbOfFin_mem T rfl _

private def w2Selected (n kk : ℕ) (u : ℕ → ℕ) : BitString n :=
  fun i => decide (∃ j < kk, u j = i.1)

private lemma weight_w2Selected {n kk : ℕ} {u : ℕ → ℕ} (hu : StrictMonoOn u (Set.Iio kk))
    (hun : ∀ j < kk, u j < n) : BitString.weight (w2Selected n kk u) = kk := by
  classical
  have himg : (Finset.univ.filter fun i : Fin n => w2Selected n kk u i = true).map
      Fin.valEmbedding = (Finset.range kk).image u := by
    ext s
    simp only [w2Selected, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_image, Finset.mem_range, decide_eq_true_eq]
    exact ⟨fun ⟨i, ⟨j, hj, hji⟩, his⟩ => ⟨j, hj, hji.trans his⟩,
      fun ⟨j, hj, hjs⟩ => ⟨⟨u j, hun j hj⟩, ⟨j, hj, rfl⟩, hjs⟩⟩
  have hinj : Set.InjOn u ↑(Finset.range kk) := Finset.coe_range kk ▸ hu.injOn
  rw [BitString.weight, ← Finset.card_map Fin.valEmbedding, himg,
    Finset.card_image_of_injOn hinj, Finset.card_range]

private lemma getD_ofFn_w2Selected {n kk : ℕ} (u : ℕ → ℕ) {s : ℕ} (hs : s < n) :
    (List.ofFn (w2Selected n kk u)).getD s false = decide (∃ j < kk, u j = s) := by
  rw [List.getD_eq_getElem _ _ (by rwa [List.length_ofFn]), List.getElem_ofFn]
  rfl

/-! ### 2. Correctness of `wcsTwoToHittingSet` -/

/-- Correctness of `wcsTwoToHittingSet`: `wcsTwoToHittingSet x ∈ HittingSet ↔ x ∈ WCS 2 d`. -/
theorem wcsTwoToHittingSet_mem_iff {d : ℕ} (x : WCSInstance 2 d) :
    wcsTwoToHittingSet x ∈ HittingSet ↔ x ∈ WCS 2 d := by
  classical
  obtain ⟨⟨⟨n, c⟩, hw_le, hd_le⟩, k⟩ := x
  rw [mem_WCS]
  unfold wcsTwoToHittingSet w2System
  dsimp only
  set gates := c.code.1
  set o := (c.outputs 0).toNat
  set kk := min (n + 1) k with hkk_def
  rw [mem_hittingSet_ofSpecSetSystem_iff]
  constructor
  · -- Soundness: a hitting set `H` of size `≤ size (d + 1) n k` yields a weight-`k` input.
    rintro ⟨H, hHcard, hHvs, hHhit⟩
    let label (v : WCS.ToClique.Vertex) : Option (List ℕ) :=
      if v.isCert then none else some (v.bracket.map Prod.fst)
    let targetLabels : Finset (Option (List ℕ)) :=
      insert none ((WCS.ToClique.indexLists (d + 1) kk).toFinset.image some)
    have htarget_card : targetLabels.card = WCS.ToClique.size (d + 1) n k := by
      rw [WCS.ToClique.size, ← hkk_def]
      simp only [targetLabels]
      rw [Finset.card_insert_of_notMem (by simp),
        Finset.card_image_of_injective _ (Option.some_injective _),
        List.toFinset_card_of_nodup (WCS.ToClique.nodup_indexLists (d + 1) kk)]
    have hlabel_mem : ∀ v ∈ H, label v ∈ targetLabels := by
      intro v hv
      rcases mem_w2Vertices.1 (hHvs v hv) with ⟨h1, _, _⟩ | ⟨h1, _, hP⟩
      · simp [label, h1, targetLabels]
      · obtain ⟨hlen, hlt⟩ := WCS.ToClique.mem_brackets.1 hP
        simp only [label, h1, Bool.false_eq_true, ↓reduceIte, targetLabels, Finset.mem_insert,
          reduceCtorEq, Finset.mem_image, List.mem_toFinset, Option.some.injEq, exists_eq_right,
          false_or]
        exact WCS.ToClique.mem_indexLists.2 ⟨by simpa using hlen, fun j hj =>
          let ⟨p, hp, h⟩ := List.mem_map.1 hj; h ▸ (hlt p hp).1⟩
    have hsurj : targetLabels ⊆ H.image label := by
      intro l hl
      simp only [targetLabels, Finset.mem_insert, Finset.mem_image, List.mem_toFinset] at hl
      rcases hl with rfl | ⟨C, hC, rfl⟩
      · have hs0 : (⟨0, [], [], [], [], []⟩ : W2Spec) ∈ w2Specs d n kk gates o := by
          simp [w2Specs]
        obtain ⟨v, hvH, hmv⟩ := hHhit _ hs0
        simp only [w2Mem, beq_self_eq_true, ↓reduceIte] at hmv
        exact Finset.mem_image.2 ⟨v, hvH, by simp [label, hmv]⟩
      · have hs1 : (⟨1, C, [], [], [], []⟩ : W2Spec) ∈ w2Specs d n kk gates o := by
          simp only [w2Specs, List.mem_append]
          exact Or.inl (Or.inl (Or.inr (List.mem_map_of_mem hC)))
        obtain ⟨v, hvH, hmv⟩ := hHhit _ hs1
        simp only [w2Mem, Nat.reduceBeqDiff, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
          Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hmv
        exact Finset.mem_image.2 ⟨v, hvH, by simp [label, hmv.1, hmv.2]⟩
    have hcard_eq : H.card = WCS.ToClique.size (d + 1) n k := by
      have h1 := (htarget_card ▸ Finset.card_le_card hsurj).trans Finset.card_image_le
      omega
    have hinj : Set.InjOn label ↑H := by
      apply Finset.injOn_of_card_image_eq
      have hsub : H.image label ⊆ targetLabels := by
        intro l hl
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hl
        exact hlabel_mem v hv
      exact le_antisymm ((Finset.card_le_card hsub).trans_eq htarget_card)
        (htarget_card ▸ Finset.card_le_card hsurj) |>.trans hcard_eq.symm
    obtain ⟨vTop, hvTopH, hvTopC⟩ := hHhit ⟨0, [], [], [], [], []⟩ (by simp [w2Specs])
    simp only [w2Mem, beq_self_eq_true, ↓reduceIte] at hvTopC
    obtain ⟨_, _, htopMem⟩ :
        vTop.isCert = true ∧ vTop.bracket = [] ∧ vTop.claims ∈ weftTwoCerts d n gates o := by
      rcases mem_w2Vertices.1 (hHvs vTop hvTopH) with h | h
      · exact h
      · simp [hvTopC] at h
    let topCl := vTop.claims
    have hunique_cert : ∀ v ∈ H, v.isCert = true → v = vTop := by
      intro v hv hvc
      apply hinj hv hvTopH
      simp [label, hvc, hvTopC]
    have hex_br : ∀ C ∈ WCS.ToClique.indexLists (d + 1) kk,
        ∃ P ∈ WCS.ToClique.brackets (d + 1) n kk,
          (⟨false, [], P⟩ : WCS.ToClique.Vertex) ∈ H ∧ P.map Prod.fst = C := by
      intro C hC
      have hs1 : (⟨1, C, [], [], [], []⟩ : W2Spec) ∈ w2Specs d n kk gates o := by
        simp only [w2Specs, List.mem_append]
        exact Or.inl (Or.inl (Or.inr (List.mem_map_of_mem hC)))
      obtain ⟨v, hvH, hmv⟩ := hHhit _ hs1
      simp only [w2Mem, Nat.reduceBeqDiff, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
        Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hmv
      rcases mem_w2Vertices.1 (hHvs v hvH) with ⟨h1, _, _⟩ | ⟨h1, h2, h3⟩
      · simp [hmv.1] at h1
      · obtain ⟨b, cl, P⟩ := v
        dsimp only at h1 h2 h3 hmv
        subst h1 h2
        exact ⟨P, h3, hvH, hmv.2⟩
    have hunique_br : ∀ v ∈ H, v.isCert = false → ∀ P,
        (⟨false, [], P⟩ : WCS.ToClique.Vertex) ∈ H →
        v.bracket.map Prod.fst = P.map Prod.fst → v.bracket = P := by
      intro v hv hvf P hPH hfst_eq
      have heq := hinj hv hPH (by simp [label, hvf, hfst_eq])
      simpa using congrArg WCS.ToClique.Vertex.bracket heq
    have hcons : ∀ P Q,
        (⟨false, [], P⟩ : WCS.ToClique.Vertex) ∈ H →
        (⟨false, [], Q⟩ : WCS.ToClique.Vertex) ∈ H →
        P.map Prod.fst ≠ Q.map Prod.fst →
        WCS.ToClique.consistent P Q = true := by
      intro P Q hPH hQH hne
      by_contra hnot
      have hnot' : WCS.ToClique.consistent P Q = false := Bool.eq_false_iff.2 hnot
      have hPbr : P ∈ WCS.ToClique.brackets (d + 1) n kk := by
        rcases mem_w2Vertices.1 (hHvs _ hPH) with ⟨h1, _, _⟩ | ⟨_, _, h3⟩
        · simp at h1
        · exact h3
      have hQbr : Q ∈ WCS.ToClique.brackets (d + 1) n kk := by
        rcases mem_w2Vertices.1 (hHvs _ hQH) with ⟨h1, _, _⟩ | ⟨_, _, h3⟩
        · simp at h1
        · exact h3
      have hs2 : (⟨2, [], P, Q, [], []⟩ : W2Spec) ∈ w2Specs d n kk gates o := by
        simp only [w2Specs, List.mem_append]
        refine Or.inl (Or.inr (List.mem_flatMap.2 ⟨P, hPbr, List.mem_map.2 ⟨Q, ?_, rfl⟩⟩))
        exact List.mem_filter.2 ⟨hQbr, by simp [hne, hnot']⟩
      obtain ⟨v, hvH, hmv⟩ := hHhit _ hs2
      simp only [w2Mem, Nat.reduceBeqDiff, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
        Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hmv
      rcases hmv with ⟨hvf, ⟨hfstP, hneP⟩ | ⟨hfstQ, hneQ⟩⟩
      · exact hneP (hunique_br v hvH hvf P hPH hfstP)
      · exact hneQ (hunique_br v hvH hvf Q hQH hfstQ)
    have hsing : ∀ j < kk, ∃ s,
        (⟨false, [], [(j, s)]⟩ : WCS.ToClique.Vertex) ∈ H ∧ s < n := by
      intro j hj
      obtain ⟨P, hPbr, hPH, hPC⟩ := hex_br [j]
        (WCS.ToClique.mem_indexLists.2 ⟨by simp [Nat.one_le_two_pow], by simpa using hj⟩)
      obtain ⟨⟨j', s⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.1 hPC
      exact ⟨s, hPH, ((WCS.ToClique.mem_brackets.1 hPbr).2 _ (List.mem_singleton_self _)).2⟩
    choose! u huH hun using hsing
    have hpairs : ∀ P, (⟨false, [], P⟩ : WCS.ToClique.Vertex) ∈ H →
        ∀ p ∈ P, p.1 < kk ∧ p.2 = u p.1 := by
      intro P hPH p hp
      have hPbr : P ∈ WCS.ToClique.brackets (d + 1) n kk := by
        rcases mem_w2Vertices.1 (hHvs _ hPH) with ⟨h1, _, _⟩ | ⟨_, _, h3⟩
        · simp at h1
        · exact h3
      have hp1 : p.1 < kk := ((WCS.ToClique.mem_brackets.1 hPbr).2 p hp).1
      refine ⟨hp1, ?_⟩
      by_cases hfst_eq : P.map Prod.fst = [p.1]
      · have hPeq : P = [(p.1, u p.1)] :=
          hunique_br ⟨false, [], P⟩ hPH rfl [(p.1, u p.1)] (huH p.1 hp1) (by simpa using hfst_eq)
        rw [hPeq, List.mem_singleton] at hp
        exact congrArg Prod.snd hp
      · have hok := WCS.ToClique.consistent_iff.1 (hcons P [(p.1, u p.1)] hPH (huH p.1 hp1)
          (by simpa using hfst_eq)) p hp (p.1, u p.1) (List.mem_singleton_self _)
        exact ((WCS.ToClique.pairOk_iff _ _).1 hok).1.1 rfl
    have hmono : StrictMonoOn u (Set.Iio kk) := by
      intro i hi j hj hij
      have hok := WCS.ToClique.consistent_iff.1 (hcons [(i, u i)] [(j, u j)] (huH i hi) (huH j hj)
        (by simp; omega)) (i, u i) (List.mem_singleton_self _) (j, u j) (List.mem_singleton_self _)
      exact ((WCS.ToClique.pairOk_iff _ _).1 hok).2.1 hij
    have hkk_eq : kk = k := by
      have := (weight_w2Selected hmono hun).symm.trans_le (BitString.weight_le_length _)
      omega
    refine ⟨w2Selected n kk u, hkk_eq ▸ weight_w2Selected hmono hun, ?_⟩
    rw [Circuit.eval_eq_getD _ _ false]
    refine eval_of_weftTwoClaimsValid c.isCodeFrom_code (mem_weftTwoCerts.1 htopMem).2.2
      List.length_ofFn fun e he => ?_
    by_contra hfail
    have hvalid_top := (mem_weftTwoCerts.1 htopMem).2.2
    rw [weftTwoClaimsValid_eq_true_iff] at hvalid_top
    obtain ⟨hcap_w, hcap_d⟩ := hvalid_top.2 e he
    have he_lt : e.1 < n + gates.length := by
      by_contra hge
      have hlen_cd : (capDepths d n gates).length = n + gates.length :=
        length_capDepths d n gates
      rw [List.getD_eq_default _ _ (by omega)] at hcap_d
      omega
    have he_weft : (evalCode (depthInterpretation (largeGateCost Unbounded.signature)) 0
        (List.replicate n 0) gates).getD e.1 0 ≤ 1 := by
      have hcw_eq : (capWefts n c.code.1).getD e.1 3 =
          min 3 ((evalCode (depthInterpretation (largeGateCost Unbounded.signature)) 0
            (List.replicate n 0) gates).getD e.1 0) :=
        getD_capWefts_eq_min c.isCodeFrom_code he_lt
      rw [hcw_eq] at hcap_w
      omega
    have he_depth : (evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
        (List.replicate n 0) gates).getD e.1 0 ≤ d := by
      have hcd_eq : (capDepths d n c.code.1).getD e.1 (d + 1) =
          min (d + 1) ((evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
            (List.replicate n 0) gates).getD e.1 0) :=
        getD_capDepths_eq_min d c.isCodeFrom_code he_lt
      rw [hcd_eq] at hcap_d
      omega
    have hneg_eval : (evalCode Unbounded.interpretation false (List.ofFn (w2Selected n kk u))
        (gatesWithNeg n gates)).getD (negWire n gates.length e) false = true := by
      rw [getD_evalCode_negWire List.length_ofFn he_lt]
      cases hv : (evalCode Unbounded.interpretation false (List.ofFn (w2Selected n kk u))
        gates).getD e.1 false <;> cases hb : e.2
      · exact absurd (hv.trans hb.symm) hfail
      · rfl
      · rfl
      · exact absurd (hv.trans hb.symm) hfail
    obtain ⟨hneg_lt, hneg_w, hneg_d⟩ :=
      weft_depth_negWire c.isCodeFrom_code he_lt he_weft he_depth
    obtain ⟨subCl, hsub_len, hsub_corr, hsub_val⟩ :=
      WeftOne.exists_claimsValid (isCodeFrom_gatesWithNeg c.isCodeFrom_code)
        List.length_ofFn hneg_lt hneg_w hneg_d hneg_eval
    have hsub_mem : subCl ∈ WCS.ToClique.certs (d + 1) n (gatesWithNeg n gates)
        (negWire n gates.length e) :=
      WCS.ToClique.mem_certs.2 ⟨hsub_len, fun q hq => (hsub_corr q hq).1, hsub_val⟩
    have hs3 : (⟨3, [], [], [], topCl, subCl⟩ : W2Spec) ∈ w2Specs d n kk gates o := by
      simp only [w2Specs, List.mem_append]
      exact Or.inr (List.mem_flatMap.2 ⟨topCl, htopMem,
        List.mem_flatMap.2 ⟨e, he, List.mem_map.2 ⟨subCl, hsub_mem, rfl⟩⟩⟩)
    obtain ⟨v, hvH, hmv⟩ := hHhit _ hs3
    simp only [w2Mem, Nat.reduceBeqDiff, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true,
      Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hmv
    rcases hmv with ⟨hvc, hne_top⟩ | ⟨hvf, href⟩
    · have hv_eq := hunique_cert v hvH hvc
      exact hne_top (hv_eq ▸ rfl)
    · have hvH' : (⟨false, [], v.bracket⟩ : WCS.ToClique.Vertex) ∈ H := by
        rcases mem_w2Vertices.1 (hHvs v hvH) with ⟨h1, _, _⟩ | ⟨h1, h2, _⟩
        · simp [hvf] at h1
        · obtain ⟨b, cl, P⟩ := v
          dsimp only at h1 h2
          subst h1 h2
          exact hvH
      have hnoref := WCS.ToClique.refutes_eq_false (isCodeFrom_gatesWithNeg c.isCodeFrom_code)
        (WCS.ToClique.forall₂_knowList List.length_ofFn fun s hs b hb => by
          rw [WCS.ToClique.know_sound hmono (hpairs v.bracket hvH') hb,
            getD_ofFn_w2Selected u hs])
        (WeftOne.checks_correct (isCodeFrom_gatesWithNeg c.isCodeFrom_code) List.length_ofFn
          fun q hq => (hsub_corr q hq).2)
      rw [hnoref] at href
      cases href
  · -- Completeness: a weight-`k` satisfying input yields a hitting set of size `size (d + 1) n k`.
    rintro ⟨x, hxk, hx_eval⟩
    have hkn : k ≤ n := hxk ▸ BitString.weight_le_length x
    have hkk_eq : kk = k := min_eq_right (by omega)
    rw [hkk_eq]
    set T_ones : Finset ℕ := (Finset.univ.filter fun i : Fin n => x i = true).map Fin.valEmbedding
    have hTcard : T_ones.card = k := by
      rw [Finset.card_map]
      exact hxk
    obtain ⟨u, hu_mono, hu_iff⟩ := exists_strictMonoOn_enum_nat T_ones
    rw [hTcard] at hu_mono hu_iff
    have hun : ∀ j < k, u j < n := by
      intro j hj
      have hm := (hu_iff (u j)).2 ⟨j, hj, rfl⟩
      obtain ⟨i, _, hi_eq⟩ := Finset.mem_map.1 hm
      rw [Fin.valEmbedding_apply] at hi_eq
      exact hi_eq ▸ i.isLt
    have hx_eq : x = w2Selected n k u := by
      funext i
      simp only [w2Selected, ← hu_iff, T_ones, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
        true_and, Fin.valEmbedding_apply]
      by_cases hxi : x i = true
      · rw [hxi, eq_comm, decide_eq_true_eq]
        exact ⟨i, hxi, rfl⟩
      · have hxf : x i = false := Bool.eq_false_iff.2 hxi
        rw [hxf, eq_comm, decide_eq_false_iff_not]
        rintro ⟨j, hj, hji⟩
        have hij : j = i := Fin.ext hji
        subst hij
        exact hxi hj
    subst hx_eq
    have ho_lt : o < n + gates.length := c.toNat_outputs_lt 0
    have ho_weft : (evalCode (depthInterpretation (largeGateCost Unbounded.signature)) 0
        (List.replicate n 0) gates).getD o 0 ≤ 2 := by
      change (evalCode (depthInterpretation (largeGateCost Unbounded.signature)) 0
        (List.replicate n 0) c.code.1).getD (c.outputs 0).toNat 0 ≤ 2
      rw [c.getD_evalCode_depthInterpretation _ 0]
      exact (Circuit.weft_le_iff c).1 hw_le 0
    have ho_depth : (evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
        (List.replicate n 0) gates).getD o 0 ≤ d := by
      change (evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
        (List.replicate n 0) c.code.1).getD (c.outputs 0).toNat 0 ≤ d
      rw [c.getD_evalCode_depthInterpretation _ 0]
      have hd_one : c.depthWith 1 ≤ d := by rwa [Circuit.depthWith_one]
      exact (Circuit.depthWith_le_iff (cost := 1) (c := c)).1 hd_one 0
    rw [Circuit.eval_eq_getD _ _ false] at hx_eval
    obtain ⟨topCl, htop_len, htop_corr, htop_chk, htop_fin⟩ :=
      exists_weftTwoClaims c.isCodeFrom_code List.length_ofFn ho_lt ho_weft ho_depth
    have htop_val : weftTwoClaimsValid d n gates o topCl = true := by
      refine Bool.and_eq_true_iff.2 ⟨decide_eq_true ?_, List.all_eq_true.2 fun e he => ?_⟩
      · exact (WeftOne.getD_kleeneEval_overrideGates_eq c.isCodeFrom_code List.length_ofFn
          (fun q hq => (htop_corr q hq).2)
          (htop_fin topCl (.refl _) fun q hq => (htop_corr q hq).2)).trans (congrArg some hx_eval)
      · exact Bool.and_eq_true_iff.2
          ⟨decide_eq_true (htop_chk e he).1, decide_eq_true (htop_chk e he).2⟩
    have htop_mem : topCl ∈ weftTwoCerts d n gates o :=
      mem_weftTwoCerts.2 ⟨htop_len.trans (Nat.pow_le_pow_right (by decide) ho_depth),
        fun q hq => (htop_corr q hq).1, htop_val⟩
    let B (C : List ℕ) : List (ℕ × ℕ) := C.map fun j => (j, u j)
    have hB_mem : ∀ C ∈ WCS.ToClique.indexLists (d + 1) k,
        B C ∈ WCS.ToClique.brackets (d + 1) n k := by
      intro C hC
      obtain ⟨hlen, hlt⟩ := WCS.ToClique.mem_indexLists.1 hC
      refine WCS.ToClique.mem_brackets.2 ⟨by simpa [B] using hlen, fun p hp => ?_⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
      exact ⟨hlt j hj, hun j (hlt j hj)⟩
    let H : Finset WCS.ToClique.Vertex :=
      insert ⟨true, topCl, []⟩
        ((WCS.ToClique.indexLists (d + 1) k).toFinset.image fun C => ⟨false, [], B C⟩)
    refine ⟨H, ?_, ?_, ?_⟩
    · rw [WCS.ToClique.size, min_eq_right (by omega : k ≤ n + 1)]
      refine (Finset.card_insert_le _ _).trans ?_
      have := Finset.card_image_le (s := (WCS.ToClique.indexLists (d + 1) k).toFinset)
        (f := fun C => (⟨false, [], B C⟩ : WCS.ToClique.Vertex))
      have hnd := List.toFinset_card_of_nodup (WCS.ToClique.nodup_indexLists (d + 1) k)
      omega
    · intro v hv
      simp only [H, Finset.mem_insert, Finset.mem_image, List.mem_toFinset] at hv
      rcases hv with rfl | ⟨C, hC, rfl⟩
      · exact mem_w2Vertices.2 (Or.inl ⟨rfl, rfl, htop_mem⟩)
      · exact mem_w2Vertices.2 (Or.inr ⟨rfl, rfl, hB_mem C hC⟩)
    · intro sp hsp
      simp only [w2Specs, List.mem_append] at hsp
      rcases hsp with ((h0 | h1) | h2) | h3
      · rw [List.mem_singleton] at h0
        subst h0
        exact ⟨⟨true, topCl, []⟩, Finset.mem_insert_self _ _, by simp [w2Mem]⟩
      · obtain ⟨C, hC, rfl⟩ := List.mem_map.1 h1
        refine ⟨⟨false, [], B C⟩,
          Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (List.mem_toFinset.2 hC)), ?_⟩
        have hfst_B : (B C).map Prod.fst = C := List.map_map.trans (List.map_id C)
        simp [w2Mem, hfst_B]
      · obtain ⟨P, hP, hQ'⟩ := List.mem_flatMap.1 h2
        obtain ⟨Q, hQf, rfl⟩ := List.mem_map.1 hQ'
        obtain ⟨hQ, hfilt⟩ := List.mem_filter.1 hQf
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hfilt
        have hCP : P.map Prod.fst ∈ WCS.ToClique.indexLists (d + 1) k := by
          obtain ⟨hlen, hlt⟩ := WCS.ToClique.mem_brackets.1 hP
          exact WCS.ToClique.mem_indexLists.2 ⟨by simpa using hlen,
            fun j hj => let ⟨p, hp, h⟩ := List.mem_map.1 hj; h ▸ (hlt p hp).1⟩
        have hCQ : Q.map Prod.fst ∈ WCS.ToClique.indexLists (d + 1) k := by
          obtain ⟨hlen, hlt⟩ := WCS.ToClique.mem_brackets.1 hQ
          exact WCS.ToClique.mem_indexLists.2 ⟨by simpa using hlen,
            fun j hj => let ⟨p, hp, h⟩ := List.mem_map.1 hj; h ▸ (hlt p hp).1⟩
        have hBC_cons :
            WCS.ToClique.consistent (B (P.map Prod.fst)) (B (Q.map Prod.fst)) = true := by
          refine WCS.ToClique.consistent_iff.2 fun p hp q hq => ?_
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
          obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hq
          have hi_lt := (WCS.ToClique.mem_indexLists.1 hCP).2 i hi
          have hj_lt := (WCS.ToClique.mem_indexLists.1 hCQ).2 j hj
          rw [WCS.ToClique.pairOk_iff]
          exact ⟨(hu_mono.injOn.eq_iff hi_lt hj_lt).symm,
            (hu_mono.lt_iff_lt (Set.mem_Iio.2 hi_lt) (Set.mem_Iio.2 hj_lt)).symm⟩
        by_cases hBP : B (P.map Prod.fst) = P
        · have hBQ : B (Q.map Prod.fst) ≠ Q := by
            intro hBQ_eq
            rw [hBP, hBQ_eq] at hBC_cons
            rw [hBC_cons] at hfilt
            cases hfilt.2
          refine ⟨⟨false, [], B (Q.map Prod.fst)⟩,
            Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (List.mem_toFinset.2 hCQ)), ?_⟩
          have hfst_Q : (B (Q.map Prod.fst)).map Prod.fst = Q.map Prod.fst :=
            List.map_map.trans (List.map_id _)
          simp [w2Mem, hfst_Q, hBQ]
        · refine ⟨⟨false, [], B (P.map Prod.fst)⟩,
            Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (List.mem_toFinset.2 hCP)), ?_⟩
          have hfst_P : (B (P.map Prod.fst)).map Prod.fst = P.map Prod.fst :=
            List.map_map.trans (List.map_id _)
          simp [w2Mem, hfst_P, hBP]
      · obtain ⟨topCl', htop', he'⟩ := List.mem_flatMap.1 h3
        obtain ⟨e, he, hsub'⟩ := List.mem_flatMap.1 he'
        obtain ⟨subCl, hsub_mem, rfl⟩ := List.mem_map.1 hsub'
        by_cases hsame : topCl = topCl'
        · subst hsame
          have he_true : (evalCode Unbounded.interpretation false (List.ofFn (w2Selected n k u))
              gates).getD e.1 false = e.2 :=
            WeftOne.checks_correct c.isCodeFrom_code List.length_ofFn
              (fun q hq => (htop_corr q hq).2) e he
          have he_lt : e.1 < n + gates.length := by
            by_contra hge
            have hc2 := (htop_chk e he).2
            have hlen_cd : (capDepths d n c.code.1).length = n + gates.length :=
              length_capDepths d n c.code.1
            rw [List.getD_eq_default _ _ (by omega)] at hc2
            omega
          have hneg_false : (evalCode Unbounded.interpretation false (List.ofFn (w2Selected n k u))
              (gatesWithNeg n gates)).getD (negWire n gates.length e) false = false := by
            rw [getD_evalCode_negWire List.length_ofFn he_lt, he_true]
            cases e.2 <;> rfl
          have hex_ref : ∃ C ∈ WCS.ToClique.indexLists (d + 1) k,
              WCS.ToClique.refutes n k (gatesWithNeg n gates) subCl (B C) = true := by
            by_contra! hall_noref
            have hsub_val := (WCS.ToClique.mem_certs.1 hsub_mem).2.2
            have hsub_chks : ∀ q ∈ subCl.flatMap (WeftOne.claimChecks n (gatesWithNeg n gates)),
                (evalCode Unbounded.interpretation false (List.ofFn (w2Selected n k u))
                  (gatesWithNeg n gates)).getD q.1 false = q.2 := by
              intro q hq
              simp only [WeftOne.claimsValid, Bool.and_eq_true, List.all_eq_true,
                decide_eq_true_eq] at hsub_val
              obtain ⟨S_det, hScard, hSlt, hSdet⟩ :=
                WeftOne.exists_determining (isCodeFrom_gatesWithNeg c.isCodeFrom_code)
                  (hsub_val.2 q hq) le_rfl
              obtain ⟨J, hJcard, hJlt, hJknow⟩ := WCS.ToClique.exists_cover hu_mono S_det
              have hJlen : J.toList.length ≤ 2 ^ (d + 2) := by
                rw [Finset.length_toList, show d + 2 = (d + 1) + 1 by omega, pow_succ, mul_comm]
                exact hJcard.trans (Nat.mul_le_mul_left 2 hScard)
              have hJC : J.toList ∈ WCS.ToClique.indexLists (d + 1) k :=
                WCS.ToClique.mem_indexLists.2 ⟨hJlen,
                  fun j hj => hJlt j (Finset.mem_toList.1 hj)⟩
              have hnr : WCS.ToClique.refutes n k (gatesWithNeg n gates) subCl (B J.toList) =
                  false := Bool.eq_false_iff.2 (hall_noref J.toList hJC)
              have hJP : ∀ j ∈ J, (j, u j) ∈ B J.toList := fun j hj =>
                List.mem_map_of_mem (Finset.mem_toList.2 hj)
              have hPu : ∀ p ∈ B J.toList, p.1 < k ∧ p.2 = u p.1 := by
                intro p hp
                obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
                exact ⟨hJlt j (Finset.mem_toList.1 hj), rfl⟩
              have hdet := hSdet (List.ofFn (w2Selected n k u))
                (WCS.ToClique.knowList n k (B J.toList)) List.length_ofFn
                (WCS.ToClique.length_knowList n k _) fun s hs => by
                  rw [WCS.ToClique.getD_knowList _ (hSlt s hs), getD_ofFn_w2Selected u (hSlt s hs)]
                  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 (hJknow _ hJP s hs)
                  rw [hb, WCS.ToClique.know_sound hu_mono hPu hb]
              rw [WCS.ToClique.refutes, List.any_eq_false] at hnr
              have hbad := hnr q hq
              rw [hdet] at hbad
              obtain ⟨qw, qb⟩ := q
              simp only at hbad ⊢
              generalize (evalCode Unbounded.interpretation false (List.ofFn (w2Selected n k u))
                (gatesWithNeg n gates)).getD qw false = qv at hbad ⊢
              cases qv <;> cases qb <;> simp at hbad ⊢
            have hneg_true := WeftOne.eval_of_claimsValid
              (isCodeFrom_gatesWithNeg c.isCodeFrom_code) hsub_val List.length_ofFn hsub_chks
            rw [hneg_false] at hneg_true
            cases hneg_true
          obtain ⟨C, hC, href⟩ := hex_ref
          exact ⟨⟨false, [], B C⟩,
            Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (List.mem_toFinset.2 hC)),
            by simp [w2Mem, href]⟩
        · exact ⟨⟨true, topCl, []⟩, Finset.mem_insert_self _ _, by simp [w2Mem, hsame]⟩

/-! ### 3. Polynomial-Time Certificate and `W[2]`-Hardness -/

private lemma beq_some_not_eq_w2 (v : Option Bool) (b : Bool) :
    (v == some (!b)) = decide (v = if b then some false else some true) := by
  cases b <;> exact Bool.beq_eq_decide_eq _ _

private lemma computableInPolyTime_refutes_w2 {γ : Type} {encIn : γ ↪ List Bool}
    {n kk : γ → ℕ} {gates : γ → List (Unbounded.Op × List ℕ)}
    {cl : γ → List (ℕ × Bool)} {P : γ → List (ℕ × ℕ)}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hkk : ComputableInPolyTime kk encIn encUnary)
    (hg : ComputableInPolyTime gates encIn (encList (Circuit.encGate Unbounded.encOp)))
    (hcl : ComputableInPolyTime cl encIn WCS.ToClique.encClaimList)
    (hP : ComputableInPolyTime P encIn WCS.ToClique.encBracket) :
    ComputableInPolyTime (fun a => WCS.ToClique.refutes (n a) (kk a) (gates a) (cl a) (P a))
      encIn encBool := by
  have hknowL : ComputableInPolyTime
      (fun a => WCS.ToClique.knowList (n a) (kk a) (P a))
      encIn (encList (encOption encBool)) := by
    unfold WCS.ToClique.knowList
    refine mapWithInput (range.comp hn) ?_
    exact WCS.ToClique.computableInPolyTime_know (hkk.comp (fst _ _)) (hP.comp (fst _ _)) (snd _ _)
  unfold WCS.ToClique.refutes
  simp only [beq_some_not_eq_w2]
  refine anyWithInput (WeftOne.computableInPolyTime_checks hn hg hcl) ?_
  have hval := listGetD_binary (encIn := encPair encIn (encPair encNat encBool))
    (encA := encOption encBool) (encL := encList (encOption encBool))
    (i := fun p => p.2.1) none
    ((computableInPolyTime_kleeneEval hknowL hg).comp (fst _ _)) (by fun_prop)
  have hb : ComputableInPolyTime
      (fun p : γ × (ℕ × Bool) => if p.2.2 then (some false : Option Bool) else some true)
      (encPair encIn (encPair encNat encBool)) (encOption encBool) :=
    ((snd encNat encBool).comp (snd _ _)).ite (const (some false)) (const (some true))
  have heq : ComputableInPolyTime
      (fun r : Option Bool × Option Bool => decide (r.1 = r.2))
      (encPair (encOption encBool) (encOption encBool)) encBool := by fun_prop
  exact heq.comp (hval.prod hb)

/-- Polynomial-time certificate for `wcsTwoToHittingSet` at fixed depth `d`. -/
theorem computableInPolyTime_wcsTwoToHittingSet (d : ℕ) :
    ComputableInPolyTime (wcsTwoToHittingSet (d := d)) (encWCS 2 d) encHittingSet := by
  have hwc := encWCS_circuit_polyTime (t := 2) (d := d) ComputableInPolyTime.id'
  have hn := WeftCircuit.computableInPolyTime_numInputs hwc
  have hg := WeftCircuit.computableInPolyTime_gates hwc
  have houts := WeftCircuit.computableInPolyTime_outputs hwc
  have hk := encWCS_weight_polyTime (t := 2) (d := d) ComputableInPolyTime.id'
  have ho : ComputableInPolyTime
      (fun x : WCSInstance 2 d => x.circuit.toCircuit.2.code.2.getD 0 0)
      (encWCS 2 d) encNat := by fun_prop
  have hkk : ComputableInPolyTime
      (fun x : WCSInstance 2 d => min (x.circuit.toCircuit.1 + 1) x.weight)
      (encWCS 2 d) encUnary := by fun_prop
  have hgl := (length_list (Circuit.encGate Unbounded.encOp)).comp hg
  have hclU : ComputableInPolyTime
      (fun x : WCSInstance 2 d =>
        WCS.ToClique.claimUniverse x.circuit.toCircuit.1 x.circuit.toCircuit.2.code.1.length)
      (encWCS 2 d) WCS.ToClique.encClaimList := by
    unfold WCS.ToClique.claimUniverse
    fun_prop
  have htopCerts : ComputableInPolyTime
      (fun x : WCSInstance 2 d =>
        weftTwoCerts d x.circuit.toCircuit.1 x.circuit.toCircuit.2.code.1
          (x.circuit.toCircuit.2.code.2.getD 0 0))
      (encWCS 2 d) (encList WCS.ToClique.encClaimList) :=
    computableInPolyTime_weftTwoCerts d hn hg ho
  have hpairs : ComputableInPolyTime
      (fun x : WCSInstance 2 d =>
        WCS.ToClique.pairs x.circuit.toCircuit.1 (min (x.circuit.toCircuit.1 + 1) x.weight))
      (encWCS 2 d) WCS.ToClique.encBracket := by
    unfold WCS.ToClique.pairs
    refine flatMapWithInput (range.comp hkk) ?_
    refine mapWithInput (range.comp (hn.comp (fst (encWCS 2 d) encUnary))) ?_
    exact ((snd (encWCS 2 d) encUnary).comp (fst _ _)).prod (snd _ _)
  have hbrs : ComputableInPolyTime
      (fun x : WCSInstance 2 d =>
        WCS.ToClique.brackets (d + 1) x.circuit.toCircuit.1
          (min (x.circuit.toCircuit.1 + 1) x.weight))
      (encWCS 2 d) (encList WCS.ToClique.encBracket) :=
    listsUpTo hpairs (2 ^ (d + 2))
  have hidxLs : ComputableInPolyTime
      (fun x : WCSInstance 2 d =>
        WCS.ToClique.indexLists (d + 1) (min (x.circuit.toCircuit.1 + 1) x.weight))
      (encWCS 2 d) (encList encIdxList) :=
    listsUpTo (range.comp hkk) (2 ^ (d + 2))
  have hvs : ComputableInPolyTime
      (fun x : WCSInstance 2 d =>
        w2Vertices d x.circuit.toCircuit.1 (min (x.circuit.toCircuit.1 + 1) x.weight)
          x.circuit.toCircuit.2.code.1 (x.circuit.toCircuit.2.code.2.getD 0 0))
      (encWCS 2 d) (encList WCS.ToClique.encVertex) := by
    unfold w2Vertices
    have hv1 : ComputableInPolyTime
        (fun x : WCSInstance 2 d =>
          (weftTwoCerts d x.circuit.toCircuit.1 x.circuit.toCircuit.2.code.1
            (x.circuit.toCircuit.2.code.2.getD 0 0)).map
            fun cl => (⟨true, cl, []⟩ : WCS.ToClique.Vertex))
        (encWCS 2 d) (encList WCS.ToClique.encVertex) :=
      mapWithInput htopCerts (WCS.ToClique.encVertex_mk_polyTime (const true) (snd _ _) (const []))
    have hv2 : ComputableInPolyTime
        (fun x : WCSInstance 2 d =>
          (WCS.ToClique.brackets (d + 1) x.circuit.toCircuit.1
            (min (x.circuit.toCircuit.1 + 1) x.weight)).map
            fun P => (⟨false, [], P⟩ : WCS.ToClique.Vertex))
        (encWCS 2 d) (encList WCS.ToClique.encVertex) :=
      mapWithInput hbrs (WCS.ToClique.encVertex_mk_polyTime (const false) (const []) (snd _ _))
    exact listAppend' hv1 hv2
  have hgExt := computableInPolyTime_gatesWithNeg hn hg
  have hclUExt : ComputableInPolyTime
      (fun x : WCSInstance 2 d =>
        WCS.ToClique.claimUniverse x.circuit.toCircuit.1
          (gatesWithNeg x.circuit.toCircuit.1 x.circuit.toCircuit.2.code.1).length)
      (encWCS 2 d) WCS.ToClique.encClaimList := by
    have hgExtL := (length_list (Circuit.encGate Unbounded.encOp)).comp hgExt
    unfold WCS.ToClique.claimUniverse
    fun_prop
  have hcandSub := listsUpTo hclUExt (2 ^ (d + 1))
  have hspecs : ComputableInPolyTime
      (fun x : WCSInstance 2 d =>
        w2Specs d x.circuit.toCircuit.1 (min (x.circuit.toCircuit.1 + 1) x.weight)
          x.circuit.toCircuit.2.code.1 (x.circuit.toCircuit.2.code.2.getD 0 0))
      (encWCS 2 d) (encList encW2Spec) := by
    have hs0 : ComputableInPolyTime
        (fun _ : WCSInstance 2 d => ([⟨0, [], [], [], [], []⟩] : List W2Spec))
        (encWCS 2 d) (encList encW2Spec) := const _
    have hs1 : ComputableInPolyTime
        (fun x : WCSInstance 2 d =>
          (WCS.ToClique.indexLists (d + 1) (min (x.circuit.toCircuit.1 + 1) x.weight)).map
            fun C => (⟨1, C, [], [], [], []⟩ : W2Spec))
        (encWCS 2 d) (encList encW2Spec) :=
      mapWithInput hidxLs
        (encW2Spec_mk_polyTime (const 1) (snd _ _) (const []) (const []) (const []) (const []))
    have hs2 : ComputableInPolyTime
        (fun x : WCSInstance 2 d =>
          (WCS.ToClique.brackets (d + 1) x.circuit.toCircuit.1
            (min (x.circuit.toCircuit.1 + 1) x.weight)).flatMap fun P =>
            ((WCS.ToClique.brackets (d + 1) x.circuit.toCircuit.1
              (min (x.circuit.toCircuit.1 + 1) x.weight)).filter fun Q =>
                decide (P.map Prod.fst ≠ Q.map Prod.fst) && !WCS.ToClique.consistent P Q).map
              fun Q => (⟨2, [], P, Q, [], []⟩ : W2Spec))
        (encWCS 2 d) (encList encW2Spec) := by
      refine flatMapWithInput hbrs ?_
      have hfiltQ : ComputableInPolyTime
          (fun p : WCSInstance 2 d × List (ℕ × ℕ) =>
            (WCS.ToClique.brackets (d + 1) p.1.circuit.toCircuit.1
              (min (p.1.circuit.toCircuit.1 + 1) p.1.weight)).filter fun Q =>
                decide (p.2.map Prod.fst ≠ Q.map Prod.fst) && !WCS.ToClique.consistent p.2 Q)
          (encPair (encWCS 2 d) WCS.ToClique.encBracket)
          (encList WCS.ToClique.encBracket) := by
        refine filterWithInput (hbrs.comp (fst _ _)) ?_
        have hP : ComputableInPolyTime
            (fun q : (WCSInstance 2 d × List (ℕ × ℕ)) × List (ℕ × ℕ) => q.1.2)
            (encPair (encPair (encWCS 2 d) WCS.ToClique.encBracket) WCS.ToClique.encBracket)
            WCS.ToClique.encBracket := (snd _ _).comp (fst _ _)
        have hQ : ComputableInPolyTime
            (fun q : (WCSInstance 2 d × List (ℕ × ℕ)) × List (ℕ × ℕ) => q.2)
            (encPair (encPair (encWCS 2 d) WCS.ToClique.encBracket) WCS.ToClique.encBracket)
            WCS.ToClique.encBracket := snd _ _
        have hcons := WCS.ToClique.computableInPolyTime_consistent hP hQ
        have hne_fst : ComputableInPolyTime
            (fun q : (WCSInstance 2 d × List (ℕ × ℕ)) × List (ℕ × ℕ) =>
              decide (q.1.2.map Prod.fst ≠ q.2.map Prod.fst))
            (encPair (encPair (encWCS 2 d) WCS.ToClique.encBracket) WCS.ToClique.encBracket)
            encBool := by fun_prop
        exact (bool_and' (hne_fst) ((bool_not.comp hcons)))
      exact mapWithInput hfiltQ
        (encW2Spec_mk_polyTime (const 2) (const []) ((snd _ _).comp (fst _ _)) (snd _ _)
          (const []) (const []))
    have hs3 : ComputableInPolyTime
        (fun x : WCSInstance 2 d =>
          (weftTwoCerts d x.circuit.toCircuit.1 x.circuit.toCircuit.2.code.1
            (x.circuit.toCircuit.2.code.2.getD 0 0)).flatMap fun topCl =>
            (topCl.flatMap (WeftOne.claimChecks x.circuit.toCircuit.1
              x.circuit.toCircuit.2.code.1)).flatMap fun e =>
              (WCS.ToClique.certs (d + 1) x.circuit.toCircuit.1
                (gatesWithNeg x.circuit.toCircuit.1 x.circuit.toCircuit.2.code.1)
                (negWire x.circuit.toCircuit.1 x.circuit.toCircuit.2.code.1.length e)).map
                fun subCl => (⟨3, [], [], [], topCl, subCl⟩ : W2Spec))
        (encWCS 2 d) (encList encW2Spec) := by
      refine flatMapWithInput htopCerts ?_
      have hchks1 := WeftOne.computableInPolyTime_checks
        (hn.comp (fst _ _)) (hg.comp (fst _ _)) (snd _ _)
      refine flatMapWithInput hchks1 ?_
      let E2 := encPair (encPair (encWCS 2 d) WCS.ToClique.encClaimList) (encPair encNat encBool)
      have hx2 : ComputableInPolyTime (fun q => q.1.1) E2 (encWCS 2 d) :=
        (fst _ _).comp (fst _ _)
      have hnegW : ComputableInPolyTime
          (fun q : (WCSInstance 2 d × List (ℕ × Bool)) × (ℕ × Bool) =>
            negWire q.1.1.circuit.toCircuit.1 q.1.1.circuit.toCircuit.2.code.1.length q.2)
          E2 encNat :=
        computableInPolyTime_negWire (unary_to_binary.comp (hn.comp hx2))
          (unary_to_binary.comp (hgl.comp hx2)) (snd _ _)
      have hsubCerts : ComputableInPolyTime
          (fun q : (WCSInstance 2 d × List (ℕ × Bool)) × (ℕ × Bool) =>
            WCS.ToClique.certs (d + 1) q.1.1.circuit.toCircuit.1
              (gatesWithNeg q.1.1.circuit.toCircuit.1 q.1.1.circuit.toCircuit.2.code.1)
              (negWire q.1.1.circuit.toCircuit.1 q.1.1.circuit.toCircuit.2.code.1.length q.2))
          E2 (encList WCS.ToClique.encClaimList) := by
        unfold WCS.ToClique.certs
        refine filterWithInput (hcandSub.comp hx2) ?_
        exact WeftOne.computableInPolyTime_claimsValid (d + 1)
          (hn.comp (hx2.comp (fst _ _)))
          (hgExt.comp (hx2.comp (fst _ _)))
          (hnegW.comp (fst _ _))
          (snd _ _)
      exact mapWithInput hsubCerts
        (encW2Spec_mk_polyTime (const 3) (const []) (const []) (const [])
          (((snd _ _).comp (fst _ _)).comp (fst _ _)) (snd _ _))
    unfold w2Specs
    exact listAppend' (listAppend' (listAppend' hs0 hs1) hs2) hs3
  have hmem : ComputableInPolyTime
      (fun p : WCSInstance 2 d × (W2Spec × WCS.ToClique.Vertex) =>
        w2Mem p.1.circuit.toCircuit.1 (min (p.1.circuit.toCircuit.1 + 1) p.1.weight)
          p.1.circuit.toCircuit.2.code.1 p.2.1 p.2.2)
      (encPair (encWCS 2 d) (encPair encW2Spec WCS.ToClique.encVertex)) encBool := by
    let EM := encPair (encWCS 2 d) (encPair encW2Spec WCS.ToClique.encVertex)
    have hsp : ComputableInPolyTime (fun p => p.2.1) EM encW2Spec := (fst _ _).comp (snd _ _)
    have hv : ComputableInPolyTime (fun p => p.2.2) EM WCS.ToClique.encVertex :=
      (snd _ _).comp (snd _ _)
    have hkind : ComputableInPolyTime (fun p => p.2.1.kind) EM encUnary :=
      encW2Spec_kind_polyTime hsp
    have hk0 : ComputableInPolyTime (fun p => p.2.1.kind == 0) EM encBool := by
      have : (fun p : WCSInstance 2 d × (W2Spec × WCS.ToClique.Vertex) => p.2.1.kind == 0) =
          fun p => decide (p.2.1.kind = 0) := funext fun _ => Bool.beq_eq_decide_eq _ _
      rw [this]; exact decide_eq' hkind (const 0)
    have hk1 : ComputableInPolyTime (fun p => p.2.1.kind == 1) EM encBool := by
      have : (fun p : WCSInstance 2 d × (W2Spec × WCS.ToClique.Vertex) => p.2.1.kind == 1) =
          fun p => decide (p.2.1.kind = 1) := funext fun _ => Bool.beq_eq_decide_eq _ _
      rw [this]; exact decide_eq' hkind (const 1)
    have hk2 : ComputableInPolyTime (fun p => p.2.1.kind == 2) EM encBool := by
      have : (fun p : WCSInstance 2 d × (W2Spec × WCS.ToClique.Vertex) => p.2.1.kind == 2) =
          fun p => decide (p.2.1.kind = 2) := funext fun _ => Bool.beq_eq_decide_eq _ _
      rw [this]; exact decide_eq' hkind (const 2)
    have hisCert := WCS.ToClique.encVertex_isCert_polyTime hv
    have hvCl := WCS.ToClique.encVertex_claims_polyTime hv
    have hvBr := WCS.ToClique.encVertex_bracket_polyTime hv
    have hidxL := encW2Spec_idxList_polyTime hsp
    have hpP := encW2Spec_pairP_polyTime hsp
    have hpQ := encW2Spec_pairQ_polyTime hsp
    have htopC := encW2Spec_topCl_polyTime hsp
    have hsubC := encW2Spec_subCl_polyTime hsp
    have hb1 : ComputableInPolyTime
        (fun p : WCSInstance 2 d × (W2Spec × WCS.ToClique.Vertex) =>
          !p.2.2.isCert && decide (p.2.2.bracket.map Prod.fst = p.2.1.idxList)) EM encBool := by
      fun_prop
    have hb2 : ComputableInPolyTime
        (fun p : WCSInstance 2 d × (W2Spec × WCS.ToClique.Vertex) =>
          !p.2.2.isCert &&
            ((decide (p.2.2.bracket.map Prod.fst = p.2.1.pairP.map Prod.fst) &&
                decide (p.2.2.bracket ≠ p.2.1.pairP)) ||
             (decide (p.2.2.bracket.map Prod.fst = p.2.1.pairQ.map Prod.fst) &&
                decide (p.2.2.bracket ≠ p.2.1.pairQ)))) EM encBool := by
      fun_prop
    have href := computableInPolyTime_refutes_w2
      (hn.comp (fst _ _)) (hkk.comp (fst _ _)) (hgExt.comp (fst _ _)) hsubC hvBr
    have hb3 : ComputableInPolyTime
        (fun p : WCSInstance 2 d × (W2Spec × WCS.ToClique.Vertex) =>
          (p.2.2.isCert && decide (p.2.2.claims ≠ p.2.1.topCl)) ||
            (!p.2.2.isCert && WCS.ToClique.refutes p.1.circuit.toCircuit.1
              (min (p.1.circuit.toCircuit.1 + 1) p.1.weight)
              (gatesWithNeg p.1.circuit.toCircuit.1 p.1.circuit.toCircuit.2.code.1)
              p.2.1.subCl p.2.2.bracket)) EM encBool := by
      have hleft : ComputableInPolyTime
          (fun p : WCSInstance 2 d × (W2Spec × WCS.ToClique.Vertex) =>
            p.2.2.isCert && decide (p.2.2.claims ≠ p.2.1.topCl)) EM encBool := by
        fun_prop
      exact (bool_or' (hleft) (((bool_and' (bool_not.comp hisCert) (href)))))
    unfold w2Mem
    exact hk0.ite hisCert (hk1.ite hb1 (hk2.ite hb2 hb3))
  have hsize : ComputableInPolyTime
      (fun x : WCSInstance 2 d => WCS.ToClique.size (d + 1) x.circuit.toCircuit.1 x.weight)
      (encWCS 2 d) encNat := by
    unfold WCS.ToClique.size
    have hlen_idx := (length_list encIdxList).comp hidxLs
    fun_prop
  have heq : (wcsTwoToHittingSet (d := d)) = fun x : WCSInstance 2 d =>
      (ofSpecSetSystem
        (w2Vertices d x.circuit.toCircuit.1 (min (x.circuit.toCircuit.1 + 1) x.weight)
          x.circuit.toCircuit.2.code.1 (x.circuit.toCircuit.2.code.2.getD 0 0))
        (w2Specs d x.circuit.toCircuit.1 (min (x.circuit.toCircuit.1 + 1) x.weight)
          x.circuit.toCircuit.2.code.1 (x.circuit.toCircuit.2.code.2.getD 0 0))
        (w2Mem x.circuit.toCircuit.1 (min (x.circuit.toCircuit.1 + 1) x.weight)
          x.circuit.toCircuit.2.code.1),
       WCS.ToClique.size (d + 1) x.circuit.toCircuit.1 x.weight) := by
    funext x
    simp [wcsTwoToHittingSet, w2System, Circuit.code]
  rw [heq]
  exact (computableInPolyTime_ofSpecSetSystem hvs hspecs hmem).prod hsize

/-- `WCS 2 d` FPT-reduces to `HittingSet` for every fixed depth `d`. -/
theorem fptReducible_wcsTwo_hittingSet (d : ℕ) :
    FPTReducible (encWCS 2 d) encHittingSet WCSInstance.weight Prod.snd (WCS 2 d) HittingSet :=
  FPTReducible.of_computableInPolyTime (computableInPolyTime_wcsTwoToHittingSet d)
    (h := fun k => (k + 1) ^ 2 ^ (d + 2) + 1)
    (fun x => WCS.ToClique.size_le (d + 1) x.circuit.toCircuit.1 x.weight)
    fun x => (wcsTwoToHittingSet_mem_iff x).symm

/-- **`HittingSet` is `W[2]`-hard** with parameter `k`. -/
theorem hittingSet_wHard : WHard 2 encHittingSet Prod.snd HittingSet :=
  wHard_iff.2 fptReducible_wcsTwo_hittingSet

/-- **`SetCover` is `W[2]`-hard** with parameter `k`. -/
theorem setCover_wHard : WHard 2 encSetCover Prod.snd SetCover :=
  hittingSet_wHard.trans fptReducible_hittingSet_setCover

/-- **`W[2] = FPT` if and only if `HittingSet` is in `FPT`**. -/
theorem W_two_eq_FPT_iff_hittingSet :
    (∀ ⦃α : Type⦄ (enc : α ↪ List Bool) (κ : α → ℕ), W 2 enc κ = FPT enc κ) ↔
      HittingSet ∈ FPT encHittingSet Prod.snd :=
  ⟨fun h => h _ _ ▸ hittingSet_mem_W,
    fun h _ _ _ => Set.Subset.antisymm (hittingSet_wHard.subset_FPT h) (FPT_subset_W 2)⟩

end Cslib.Complexity
