/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle.BoundedQuery
public import CslibFrontier.Computability.Complexity.Problems.IndependentSet
public import CslibFrontier.Computability.Complexity.Reduction
import Cslib.Foundations.Data.Polynomial.Monotone
import CslibFrontier.Computability.Complexity.Classes.NP.Image
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Classes.Oracle.Deterministic
import CslibFrontier.Computability.Complexity.Classes.Oracle.FewQueries
import CslibFrontier.Computability.Complexity.Classes.Oracle.ThresholdSearch
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Logics.Propositional.CNF.Eval
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.Finset.Sigma

/-!
# $\Theta_2^p$-Completeness of Equal-Independence-Number

`Cslib.Complexity.EqualIndepNum` is the set of graph pairs `(G₁, G₂)` satisfying
`G₁.indepNum = G₂.indepNum`.

## Main definitions

* `Cslib.Complexity.EqualIndepNum`: pairs `(G₁, G₂)` of graphs with equal independence numbers.

## Main results

* `Cslib.Complexity.computableInPolyTimeWithOracleQueries_indepNum`: binary search computes
  `G.indepNum` in polynomial time using `O(log n)` queries to `SAT`.
* `Cslib.Complexity.EqualIndepNum_mem_PNPLog`: `EqualIndepNum ∈ PNPLog (encPair encGraph encGraph)`.
* `Cslib.Complexity.EqualIndepNum_pnpLogHard`, `Cslib.Complexity.EqualIndepNum_pnpLogComplete`:
  Wagner–Kadin query-census reduction establishing $\Theta_2^p$-completeness of `EqualIndepNum`.
-/

public section

open Cslib Cslib.Logic.PL Cslib.Probability
open Turing Turing.MultiTapeMachine Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

namespace Cslib.Complexity

/-- **`EqualIndepNum`**: pairs of graphs `(G₁, G₂)` with `G₁.indepNum = G₂.indepNum`. -/
@[expose]
def EqualIndepNum : Set (Graph × Graph) :=
  {p | p.1.indepNum = p.2.indepNum}

private def unaryToNat (n : ℕ) : ℕ := n

@[fun_prop]
private theorem computableInPolyTime_unaryToNat :
    ComputableInPolyTime unaryToNat encUnary encNat :=
  unary_to_binary

@[fun_prop]
private theorem computableInPolyTime_unaryToNat_comp {γ : Type} {enc : γ ↪ List Bool}
    {f : γ → ℕ} (hf : ComputableInPolyTime f enc encUnary) :
    ComputableInPolyTime (fun x => unaryToNat (f x)) enc encNat :=
  computableInPolyTime_unaryToNat.comp hf

private def pairCode (a b : ℕ) : ℕ := Nat.pair a b

@[fun_prop]
private theorem computableInPolyTime_pairCode_comp {γ : Type} {enc : γ ↪ List Bool}
    {a b : γ → ℕ} (ha : ComputableInPolyTime a enc encUnary)
    (hb : ComputableInPolyTime b enc encUnary) :
    ComputableInPolyTime (fun x => pairCode (a x) (b x)) enc encNat :=
  unary_to_binary.comp (unary_pair.comp (ha.prod hb))

private theorem pairCode_inj {a₁ b₁ a₂ b₂ : ℕ} :
    pairCode a₁ b₁ = pairCode a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := Nat.pair_eq_pair

private def disjointUnionList (gs : List Graph) : Graph where
  vertices := gs.zipIdx.flatMap fun Gt =>
    (List.range Gt.1.distinctVertices.length).map fun i => pairCode Gt.2 i
  edges := gs.zipIdx.flatMap fun Gt =>
    (List.range Gt.1.distinctVertices.length).flatMap fun i =>
      ((List.range Gt.1.distinctVertices.length).filter fun j =>
        Gt.1.adjBool (Gt.1.distinctVertices.getD i 0) (Gt.1.distinctVertices.getD j 0)).map
        fun j => (pairCode Gt.2 i, pairCode Gt.2 j)

@[fun_prop]
private theorem computableInPolyTime_disjointUnionList :
    ComputableInPolyTime disjointUnionList (encList encGraph) encGraph := by
  unfold disjointUnionList; fun_prop

private theorem mem_zipIdx_iff_getElem {α : Type*} {l : List α} {x : α} {t : ℕ} :
    (x, t) ∈ l.zipIdx ↔ ∃ h : t < l.length, l[t] = x := by
  rw [List.mem_iff_getElem]
  simp only [List.length_zipIdx, List.getElem_zipIdx, Nat.zero_add, Prod.mk.injEq]
  exact ⟨fun ⟨i, hi, hx, hit⟩ => ⟨hit ▸ hi, hit ▸ hx⟩, fun ⟨ht, hx⟩ => ⟨t, ht, hx, rfl⟩⟩

private theorem mem_vertices_disjointUnionList {gs : List Graph} {w : ℕ} :
    w ∈ (disjointUnionList gs).vertices ↔
      ∃ (t : Fin gs.length) (i : Fin gs[t].distinctVertices.length),
        w = pairCode t.1 i.1 := by
  simp only [disjointUnionList, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨⟨G, t⟩, hGt, i, hi, rfl⟩
    obtain ⟨ht_lt, rfl⟩ := mem_zipIdx_iff_getElem.mp hGt
    exact ⟨⟨t, ht_lt⟩, ⟨i, hi⟩, rfl⟩
  · rintro ⟨⟨t, ht⟩, ⟨i, hi⟩, rfl⟩
    exact ⟨(gs[t], t), mem_zipIdx_iff_getElem.mpr ⟨ht, rfl⟩, i, hi, rfl⟩

private theorem mem_edges_disjointUnionList {gs : List Graph} {x y : ℕ} :
    (x, y) ∈ (disjointUnionList gs).edges ↔
      ∃ (t : Fin gs.length) (i j : Fin gs[t].distinctVertices.length),
        gs[t].toSimpleGraph.Adj (gs[t].vertexEquiv i).1 (gs[t].vertexEquiv j).1 ∧
          x = pairCode t.1 i.1 ∧ y = pairCode t.1 j.1 := by
  simp only [disjointUnionList, List.mem_flatMap, List.mem_map,
    List.mem_filter, List.mem_range, Prod.mk.injEq, Graph.adjBool_eq_true_iff]
  constructor
  · rintro ⟨⟨G, t⟩, hGt, i, hi, j, ⟨hj, hadj⟩, rfl, rfl⟩
    obtain ⟨ht_lt, rfl⟩ := mem_zipIdx_iff_getElem.mp hGt
    exact ⟨⟨t, ht_lt⟩, ⟨i, hi⟩, ⟨j, hj⟩,
      by rwa [Graph.vertexEquiv_apply, Graph.vertexEquiv_apply], rfl, rfl⟩
  · rintro ⟨⟨t, ht⟩, ⟨i, hi⟩, ⟨j, hj⟩, hadj, rfl, rfl⟩
    rw [Graph.vertexEquiv_apply, Graph.vertexEquiv_apply] at hadj
    exact ⟨(gs[t], t), mem_zipIdx_iff_getElem.mpr ⟨ht, rfl⟩, i, hi, j, ⟨hj, hadj⟩, rfl, rfl⟩

private theorem adj_disjointUnionList_pairCode {gs : List Graph}
    (t₁ t₂ : Fin gs.length) (i₁ : Fin gs[t₁].distinctVertices.length)
    (i₂ : Fin gs[t₂].distinctVertices.length) :
    (disjointUnionList gs).toSimpleGraph.Adj (pairCode t₁.1 i₁.1) (pairCode t₂.1 i₂.1) ↔
      t₁ = t₂ ∧ gs[t₁].toSimpleGraph.Adj (gs[t₁].vertexEquiv i₁).1 (gs[t₂].vertexEquiv i₂).1 := by
  rw [Graph.toSimpleGraph_adj]
  constructor
  · rintro ⟨_, hmem | hmem⟩
    · obtain ⟨t, i, j, hadj, e1, e2⟩ := mem_edges_disjointUnionList.mp hmem
      have ht1 : t₁ = t := Fin.ext (pairCode_inj.mp e1).1
      have ht2 : t₂ = t := Fin.ext (pairCode_inj.mp e2).1
      subst ht1 ht2
      have hi1 : i₁ = i := Fin.ext (pairCode_inj.mp e1).2
      have hj2 : i₂ = j := Fin.ext (pairCode_inj.mp e2).2
      subst hi1 hj2; exact ⟨rfl, hadj⟩
    · obtain ⟨t, i, j, hadj, e1, e2⟩ := mem_edges_disjointUnionList.mp hmem
      have ht2 : t₂ = t := Fin.ext (pairCode_inj.mp e1).1
      have ht1 : t₁ = t := Fin.ext (pairCode_inj.mp e2).1
      subst ht1 ht2
      have hi2 : i₂ = i := Fin.ext (pairCode_inj.mp e1).2
      have hj1 : i₁ = j := Fin.ext (pairCode_inj.mp e2).2
      subst hi2 hj1; exact ⟨rfl, hadj.symm⟩
  · rintro ⟨rfl, hadj⟩
    exact ⟨fun h => hadj.ne (congrArg (fun k => (gs[t₁].vertexEquiv k).1)
        (Fin.ext (pairCode_inj.mp h).2)),
      Or.inl (mem_edges_disjointUnionList.mpr ⟨t₁, i₁, i₂, hadj, rfl, rfl⟩)⟩

private theorem indepNum_disjointUnionList (gs : List Graph) :
    (disjointUnionList gs).indepNum = (gs.map Graph.indepNum).sum := by
  classical
  have hsum_fin : (gs.map Graph.indepNum).sum = ∑ t : Fin gs.length, gs[t].indepNum := by
    conv_lhs => rw [← List.ofFn_getElem (xs := gs)]
    simp
  rw [hsum_fin]
  let emb : (Σ t : Fin gs.length, Fin gs[t].distinctVertices.length) ↪ ℕ :=
    ⟨fun p => pairCode p.1.1 p.2.1, fun ⟨t₁, i₁⟩ ⟨t₂, i₂⟩ h => by
      obtain ⟨ht, hi⟩ := pairCode_inj.mp h
      have hteq : t₁ = t₂ := Fin.ext ht
      subst hteq; exact Sigma.ext rfl (heq_of_eq (Fin.ext hi))⟩
  refine le_antisymm ?_ ?_
  · obtain ⟨S, hSV, hS⟩ :=
      mem_IndependentSet_iff.mp (Graph.indepNum_mem_IndependentSet (disjointUnionList gs))
    change (disjointUnionList gs).toSimpleGraph.IsNIndepSet (disjointUnionList gs).indepNum S at hS
    let slice : ∀ t : Fin gs.length, Finset (Fin gs[t].distinctVertices.length) :=
      fun t => Finset.univ.filter fun i => pairCode t.1 i.1 ∈ S
    have hS_eq : S = (Finset.univ.sigma slice).map emb := by
      ext w
      simp only [Finset.mem_map, Finset.mem_sigma, Finset.mem_univ, true_and, slice,
        Finset.mem_filter, emb]
      refine ⟨fun hw => ?_, fun ⟨⟨t, i⟩, hw, heq⟩ => heq ▸ hw⟩
      obtain ⟨t, i, rfl⟩ := mem_vertices_disjointUnionList.mp (hSV w hw)
      exact ⟨⟨t, i⟩, hw, rfl⟩
    rw [← hS.card_eq, hS_eq, Finset.card_map, Finset.card_sigma]
    refine Finset.sum_le_sum fun t _ => ?_
    have hind_t : gs[t].induced.IsIndepSet
        (((slice t).map gs[t].vertexEquiv.toEmbedding : Finset _) : Set _) := by
      intro u hu v hv huv hadj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hu)
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hv)
      exact hS.isIndepSet (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
        (fun h => huv (congrArg gs[t].vertexEquiv (Fin.ext (pairCode_inj.mp h).2)))
        ((adj_disjointUnionList_pairCode t t i j).mpr ⟨rfl, hadj⟩)
    simpa [Graph.indepNum] using hind_t.card_le_indepNum
  · rw [Graph.le_indepNum_iff, mem_IndependentSet_iff_mk]
    choose J hJ using fun t : Fin gs.length => gs[t].induced.exists_isNIndepSet_indepNum
    let slice : ∀ t : Fin gs.length, Finset (Fin gs[t].distinctVertices.length) :=
      fun t => (J t).map gs[t].vertexEquiv.symm.toEmbedding
    refine ⟨(Finset.univ.sigma slice).map emb, ?_, ?_, ?_⟩
    · intro w hw; obtain ⟨⟨t, i⟩, -, rfl⟩ := Finset.mem_map.mp hw
      exact mem_vertices_disjointUnionList.mpr ⟨t, i, rfl⟩
    · intro x hx y hy hxy hadj
      obtain ⟨⟨t₁, i₁⟩, hi₁, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
      obtain ⟨⟨t₂, i₂⟩, hi₂, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
      obtain ⟨rfl, hadj'⟩ := (adj_disjointUnionList_pairCode t₁ t₂ i₁ i₂).mp hadj
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, slice, Finset.mem_map] at hi₁ hi₂
      obtain ⟨u₁, hu₁, e1⟩ := hi₁; obtain ⟨u₂, hu₂, e2⟩ := hi₂
      have hv₁ : gs[t₁].vertexEquiv i₁ = u₁ := by
        rw [← e1]; exact gs[t₁].vertexEquiv.apply_symm_apply _
      have hv₂ : gs[t₁].vertexEquiv i₂ = u₂ := by
        rw [← e2]; exact gs[t₁].vertexEquiv.apply_symm_apply _
      have hadj_ind : gs[t₁].induced.Adj u₁ u₂ := by
        change gs[t₁].toSimpleGraph.Adj u₁.1 u₂.1
        rwa [← hv₁, ← hv₂]
      exact (hJ t₁).isIndepSet hu₁ hu₂
        (fun h => hxy (congrArg (fun k => emb ⟨t₁, k⟩) (by rw [← e1, ← e2, h]))) hadj_ind
    · rw [Finset.card_map, Finset.card_sigma]
      exact Finset.sum_congr rfl fun t _ => by simp [slice, Graph.indepNum, (hJ t).card_eq]

/-- Binary search on `[1, G.vertices.length + 1)` computes `G.indepNum` in polynomial time with
at most `1 * Nat.log 2 |encGraph G| + 1` queries to `encCNF '' SAT`. -/
theorem computableInPolyTimeWithOracleQueries_indepNum :
    ComputableInPolyTimeWithOracleQueries (encCNF '' SAT)
      (fun n => 1 * Nat.log 2 n + 1) Graph.indepNum encGraph encNat := by
  classical
  obtain ⟨toSAT, htoSAT, hSAT⟩ :=
    CookLevin.SAT_npHard encIndependentSetInstance IndependentSet IndependentSet.mem_NP
  let req : Graph → ℕ → List Bool := fun G m => encCNF (toSAT ⟨G, m⟩)
  have hreq : ComputableInPolyTime (fun q : OracleThresholdQuery Graph => req q.inst q.target)
      (encOracleThresholdQuery encGraph) encBits :=
    (ComputableInPolyTime.of_eq (f := fun φ : CNF ℕ => encCNF φ) fun _ => rfl).comp
      (htoSAT.comp (encIndependentSetInstance_mk_polyTime
        (encOracleThresholdQuery_inst_polyTime .id')
        (encOracleThresholdQuery_target_polyTime .id')))
  have hreq_iff : ∀ G m, req G m ∈ encCNF '' SAT ↔ m ≤ G.indepNum := fun G m => by
    simp only [req, Graph.le_indepNum_iff, hSAT ⟨G, m⟩]
    exact ⟨fun ⟨φ, hφ, heq⟩ => encCNF.injective heq ▸ hφ, fun h => ⟨_, h, rfl⟩⟩
  have hhi : ComputableInPolyTime (fun G : Graph => G.vertices.length + 1) encGraph encNat :=
    binary_add' (unary_to_binary.comp ((length_list encNat).comp (encGraph_vertices_polyTime .id')))
      (const 1)
  have hsize : ∀ G : Graph,
      (G.vertices.length + 1 - 1).size ≤ 1 * Nat.log 2 (encGraph G).length + 1 := fun G => by
    rw [Nat.add_sub_cancel, one_mul]
    have hsz : G.vertices.length.size ≤ Nat.log 2 G.vertices.length + 1 :=
      Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide : 1 < 2) G.vertices.length)
    exact hsz.trans (Nat.succ_le_succ (Nat.log_mono_right G.length_vertices_le_encGraph))
  have hpost := (computableInPolyTimeWithOracleQueries_bisect (encCNF '' SAT)
    (r := fun n => 1 * Nat.log 2 n + 1) hreq (const 1) hhi hsize).map (binary_sub' .id' (const 1))
  refine ⟨_, hpost.choose_spec.1, fun G => ⟨?_, (hpost.choose_spec.2 G).2⟩⟩
  rw [(hpost.choose_spec.2 G).1]
  let test : ℕ → Bool := fun m => decide (req G m ∈ encCNF '' SAT)
  obtain ⟨hlo, _, htrue, hfalse⟩ :=
    iterate_bisectStep_spec (lo := 1) (hi := G.vertices.length + 1) (test := test)
      fun m m' _ hmm' _ ht => by
        simp only [test, decide_eq_true_eq, hreq_iff] at ht ⊢; exact hmm'.trans ht
  let k := ((bisectStep test)^[(G.vertices.length + 1 - 1).size] ⟨1, G.vertices.length + 1⟩).lo
  change k - 1 = G.indepNum
  have hind_le : G.indepNum ≤ G.vertices.length :=
    G.indepNum_le_card.trans G.vertices.toFinset_card_le
  have hk_le : k - 1 ≤ G.indepNum := by
    rcases Nat.eq_or_lt_of_le hlo with hk1 | hgt1
    · omega
    · simpa only [test, decide_eq_true_eq, hreq_iff] using htrue (k - 1) (by omega) (by omega)
  have hind_lt_k : G.indepNum < k := by
    by_contra! hge
    have hf := hfalse G.indepNum hge (by omega)
    simp only [test, decide_eq_false_iff_not, hreq_iff] at hf; exact hf le_rfl
  exact le_antisymm hk_le (Nat.le_sub_one_of_lt hind_lt_k)

/-- **`EqualIndepNum ∈ PNPLog (encPair encGraph encGraph)`**. -/
theorem EqualIndepNum_mem_PNPLog : EqualIndepNum ∈ PNPLog (encPair encGraph encGraph) := by
  have hmono : Monotone (fun n => 1 * Nat.log 2 n + 1) := fun _ _ h => by
    simpa using Nat.log_mono_right h
  have h₁ := computableInPolyTimeWithOracleQueries_indepNum.preprocess
    (stretch := fun n => n) (fst encGraph encGraph) hmono
    fun p => length_le_encPair_left encGraph encGraph p
  have hcomp := computableInPolyTimeWithOracleQueries_indepNum.preprocess
    (stretch := fun n => n)
    ((snd encGraph encGraph).comp (fst (encPair encGraph encGraph) encNat)) hmono
    fun q => (length_le_encPair_right encGraph encGraph q.1).trans
      (length_le_encPair_left (encPair encGraph encGraph) encNat q)
  have h₂_eq : ComputableInPolyTimeWithOracleQueries (encCNF '' SAT)
      (fun n => 1 * Nat.log 2 n + 1)
      (fun q : (Graph × Graph) × ℕ => decide (q.2 = q.1.2.indepNum))
      (encPair (encPair encGraph encGraph) encNat) encBool := by
    refine (hcomp.bind_with (g := fun q m => decide (q.2 = m))
      (((decide_eq' ((snd (encPair encGraph encGraph) encNat).comp (fst _ _))
        (snd _ _)).of_enc_eq fun _ => rfl).computableInPolyTimeWithOracleQueries
        (encCNF '' SAT) (fun _ => 0))
      (fun _ _ _ => le_rfl) (midLen := fun n => 3 * n + 2) fun q => ?_).mono fun _ => le_rfl
    have hind_le : q.1.2.indepNum ≤ (encPair (encPair encGraph encGraph) encNat q).length :=
      (q.1.2.indepNum_le_card.trans
        (q.1.2.vertices.toFinset_card_le.trans q.1.2.length_vertices_le_encGraph)).trans
        ((length_le_encPair_right encGraph encGraph q.1).trans
          (length_le_encPair_left (encPair encGraph encGraph) encNat q))
    have hnat : (encNat q.1.2.indepNum).length ≤
        (encPair (encPair encGraph encGraph) encNat q).length := by
      rw [encNat_apply, Nat.size_eq_bits_len]
      exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans hind_le
    rw [length_encPair]; dsimp only [Function.comp_apply]; omega
  have hfull := h₁.bind_with (g := fun p m => decide (m = p.2.indepNum)) h₂_eq hmono
    (midLen := fun n => 3 * n + 3) fun p => by
      have hind_le : p.1.indepNum ≤ (encPair encGraph encGraph p).length :=
        (p.1.indepNum_le_card.trans
          (p.1.vertices.toFinset_card_le.trans p.1.length_vertices_le_encGraph)).trans
          (length_le_encPair_left encGraph encGraph p)
      have hnat : (encNat p.1.indepNum).length ≤ (encPair encGraph encGraph p).length := by
        rw [encNat_apply, Nat.size_eq_bits_len]
        exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans hind_le
      rw [length_encPair]; dsimp only [Function.comp_apply]; omega
  refine mem_PNPLog_of_mem_PWithOracleQueries (c := 6) image_SAT_mem_NP
    ⟨_, hfull.mono (fun n => ?_), fun p => by simp [EqualIndepNum]⟩
  have hlog : Nat.log 2 (3 * n + 3) ≤ Nat.log 2 n + 3 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · decide
    · calc Nat.log 2 (3 * n + 3) ≤ Nat.log 2 (n * 2 * 2 * 2) := Nat.log_mono_right (by omega)
        _ = Nat.log 2 n + 3 := by
          rw [Nat.log_mul_base (by omega) (by omega), Nat.log_mul_base (by omega) (by omega),
            Nat.log_mul_base (by omega) (by omega)]
  omega

/-! ### Clamped CNFs and Wagner–Kadin hardness of `EqualIndepNum` -/

private def clampCNF (φ : CNF ℕ) : CNF ℕ :=
  [(0, false)] :: φ.map fun c => (0, true) :: c.map fun l => (l.1 + 1, l.2)

private theorem computableInPolyTime_clampCNF :
    ComputableInPolyTime clampCNF encCNF encCNF := by
  let encLit := encPair encNat encBool
  let encCl := encList encLit
  have hlit : ComputableInPolyTime (fun l : Literal ℕ => ((l.1 + 1, l.2) : Literal ℕ))
      encLit encLit :=
    (binary_add' (fst encNat encBool) (const 1)).prod (snd encNat encBool)
  have hcl : ComputableInPolyTime
      (fun c : Clause ℕ => ((0, true) :: c.map fun l => (l.1 + 1, l.2) : Clause ℕ))
      encCl encCl :=
    ((cons encLit).comp ((const (0, true)).prod
      (mapWithInput (f := fun _ l => (l.1 + 1, l.2)) (id' (encIn := encCl))
        ((hlit.comp (snd encCl encLit)).of_enc_eq fun _ =>
          congrArg encLit (by dsimp only [Function.comp_apply]))))).of_enc_eq fun _ =>
      congrArg encCl (by dsimp only [Function.comp_apply])
  exact (((cons encCl).comp ((const [(0, false)]).prod
    (mapWithInput (f := fun _ c => (0, true) :: c.map fun l => (l.1 + 1, l.2))
      (id' (encIn := encList encCl))
      ((hcl.comp (snd (encList encCl) encCl)).of_enc_eq fun _ =>
        congrArg encCl (by dsimp only [Function.comp_apply]))))).of_enc_eq fun _ =>
      congrArg encCNF (by dsimp only [clampCNF, Function.comp_apply]))

private theorem eval_map_shift (c : Clause ℕ) (τ : ℕ → Bool) :
    Clause.eval τ (c.map fun l => (l.1 + 1, l.2)) = Clause.eval (fun x => τ (x + 1)) c := by
  induction c with
  | nil => rfl
  | cons l tl ih =>
    rcases l with ⟨_, _⟩
    simp only [List.map_cons, Clause.eval_cons, Literal.eval_mk, ih]

open Classical in
private theorem indepNum_toIndependentSet_clampCNF (φ : CNF ℕ) :
    (SAT.toIndependentSet (clampCNF φ)).graph.indepNum =
      φ.length + (if φ ∈ SAT then 1 else 0) := by
  have hlen : (clampCNF φ).length = φ.length + 1 := by simp [clampCNF]
  have hmax : (SAT.toIndependentSet (clampCNF φ)).graph.indepNum ≤ φ.length + 1 := by
    obtain ⟨σ, hσ⟩ := (SAT.le_indepNum_toIndependentSet_iff (clampCNF φ) _).mp le_rfl; omega
  by_cases hsat : φ ∈ SAT
  · simp only [hsat, ↓reduceIte]
    refine le_antisymm hmax ((SAT.le_indepNum_toIndependentSet_iff _ _).mpr ?_)
    obtain ⟨σ, hσ⟩ := mem_SAT.mp hsat
    let τ : ℕ → Bool := fun | 0 => false | x + 1 => σ x
    have heval : (clampCNF φ).eval τ = true := by
      rw [CNF.eval_eq_true_iff]; intro cl hcl
      simp only [clampCNF, List.mem_cons, List.mem_map] at hcl
      rcases hcl with rfl | ⟨c, hc, rfl⟩
      · rfl
      · rw [Clause.eval_cons, eval_map_shift]
        simpa [τ] using (CNF.eval_eq_true_iff σ φ).mp hσ c hc
    exact ⟨τ, by rw [CNF.countUnsat_eq_zero_iff.mpr heval, hlen, add_zero]⟩
  · simp only [hsat, ↓reduceIte, add_zero]
    refine le_antisymm ?_ ((SAT.le_indepNum_toIndependentSet_iff _ _).mpr ?_)
    · by_contra! hgt
      obtain ⟨τ, hτ⟩ := (SAT.le_indepNum_toIndependentSet_iff (clampCNF φ) (φ.length + 1)).mp hgt
      have heval := (CNF.eval_eq_true_iff _ _).mp
        (CNF.countUnsat_eq_zero_iff.mp (by omega : (clampCNF φ).countUnsat τ = 0))
      have hτ0 : τ 0 = false := by
        simpa [Clause.eval, Literal.eval] using heval [(0, false)] (by simp [clampCNF])
      refine hsat (mem_SAT.mpr ⟨fun x => τ (x + 1),
        (CNF.eval_eq_true_iff _ _).mpr fun c hc => ?_⟩)
      have hcl := heval ((0, true) :: c.map fun l => (l.1 + 1, l.2))
        (List.mem_cons_of_mem _ (List.mem_map_of_mem hc))
      rw [Clause.eval_cons, eval_map_shift] at hcl; simpa [hτ0] using hcl
    · let τ : ℕ → Bool := fun _ => true
      have h0 : (φ.map fun c => (0, true) :: c.map fun l => (l.1 + 1, l.2)).countP
          (fun cl => decide ¬ (Clause.eval τ cl = true)) = 0 :=
        List.countP_eq_zero.mpr fun cl hcl => by
          obtain ⟨c, -, rfl⟩ := List.mem_map.mp hcl; simp [τ]
      have heq_cnt : (clampCNF φ).countUnsat τ =
          (clampCNF φ).countP (fun cl => decide ¬ (Clause.eval τ cl = true)) := rfl
      have hcnt : (clampCNF φ).countP (fun cl => decide ¬ (Clause.eval τ cl = true)) ≤ 1 := by
        rw [clampCNF, List.countP_cons, h0]; split_ifs <;> omega
      exact ⟨τ, by omega⟩

private def edgelessGraph (m : ℕ) : Graph := ⟨(List.range m).map unaryToNat, []⟩

@[fun_prop]
private theorem computableInPolyTime_edgelessGraph :
    ComputableInPolyTime edgelessGraph encUnary encGraph := by unfold edgelessGraph; fun_prop

private theorem vertices_edgelessGraph (m : ℕ) : (edgelessGraph m).vertices = List.range m :=
  List.map_id (List.range m)

private theorem indepNum_edgelessGraph (m : ℕ) : (edgelessGraph m).indepNum = m := by
  refine le_antisymm ?_ ?_
  · calc (edgelessGraph m).indepNum ≤ (edgelessGraph m).vertices.toFinset.card :=
          (edgelessGraph m).indepNum_le_card
      _ = m := by rw [vertices_edgelessGraph, List.toFinset_card_of_nodup List.nodup_range,
          List.length_range]
  · rw [Graph.le_indepNum_iff, mem_IndependentSet_iff_mk]
    refine ⟨(List.range m).toFinset, fun v hv => by
      rw [vertices_edgelessGraph]; exact List.mem_toFinset.mp hv, ⟨?_, ?_⟩⟩
    · intro _ _ _ _ _ hadj; rw [Graph.toSimpleGraph_adj] at hadj; simp [edgelessGraph] at hadj
    · rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range]

private theorem interpret_congr_queriesWith {Operation β : Type}
    {ans₁ ans₂ : Operation × List Bool → List Bool} (prog : WordQueryComp Operation β)
    (h : ∀ q ∈ OracleComp.queriesWith ans₁ prog, ans₁ q = ans₂ q) :
    OracleComp.interpret (m := Id) ans₁ prog = OracleComp.interpret (m := Id) ans₂ prog := by
  induction prog using PFunctor.FreeM.induction with
  | pure _ => rfl
  | lift_bind q cont ih =>
    have hq : ans₁ q = ans₂ q :=
      h q (by erw [OracleComp.queriesWith_query_bind]; exact List.mem_cons_self)
    erw [OracleComp.interpret_id_query_bind, OracleComp.interpret_id_query_bind]
    rw [hq]; exact ih _ fun q' hq' => h q' (by
      erw [OracleComp.queriesWith_query_bind]; rw [hq]; exact List.mem_cons_of_mem _ hq')

private def logPop {Operation : Type} (q : Operation × List Bool)
    (st : List Bool × List (List Bool)) : List Bool × (List Bool × List (List Bool)) :=
  ([st.1.headD false], (st.1.tail, st.2 ++ [q.2]))

open Classical in
private theorem run_interpret_logPop_program {Operation β : Type} (O : Set (List Bool))
    (prog : WordQueryComp Operation β) (s : List Bool) (acc : List (List Bool))
    (hs : ∀ idx, s.getD idx false =
      ((OracleComp.queriesWith (languageOracle O) prog).map
        fun q => decide (q.2 ∈ O)).getD idx false) :
    (OracleComp.interpret (m := StateM (List Bool × List (List Bool)))
        (fun q => (logPop q : StateM _ _)) prog).run (s, acc) =
      (OracleComp.interpret (m := Id) (languageOracle O) prog,
        (s.drop (OracleComp.queriesWith (languageOracle O) prog).length,
          acc ++ (OracleComp.queriesWith (languageOracle O) prog).map Prod.snd)) := by
  induction prog using PFunctor.FreeM.induction generalizing s acc with
  | pure b =>
    change (b, (s, acc)) = (b, (s.drop 0, acc ++ []))
    rw [List.drop_zero, List.append_nil]
  | lift_bind q cont ih =>
    have h0 : s.headD false = decide (q.2 ∈ O) := by
      have hidx := hs 0
      erw [OracleComp.queriesWith_query_bind] at hidx; cases s <;> simpa using hidx
    have htail : ∀ idx, s.tail.getD idx false =
        ((OracleComp.queriesWith (languageOracle O) (cont [decide (q.2 ∈ O)])).map
          fun q' => decide (q'.2 ∈ O)).getD idx false := fun idx => by
      have hidx := hs (idx + 1)
      erw [OracleComp.queriesWith_query_bind] at hidx
      cases s <;> simpa [languageOracle] using hidx
    erw [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      OracleComp.queriesWith_query_bind, OracleComp.interpret_id_query_bind]
    change (OracleComp.interpret (m := StateM (List Bool × List (List Bool)))
        (fun q => (logPop q : StateM _ _))
        (cont [s.headD false])).run (s.tail, acc ++ [q.2]) = _
    rw [h0, ih [decide (q.2 ∈ O)] s.tail (acc ++ [q.2]) htail]
    simp only [languageOracle, List.length_cons, List.map_cons, List.append_assoc,
      List.singleton_append]
    cases s <;> simp

private theorem run_interpret_logPop_finiteStep {k : ℕ} {Control Operation : Type}
    [DecidableEq Operation] (machine : MultiTapePTM k Bool Control Operation)
    (cfg : FiniteConfig k Bool Control Operation) (s : List Bool) (log : List (List Bool)) :
    let cur := (OracleComp.interpret (m := StateM (List Bool × List (List Bool)))
      (fun q => (logPop q : StateM _ _))
      (MultiTapeMachine.finiteStep machine
        (fun choices => choices <$> (pure false : OracleComp _ Bool))
        (fun op word => OracleComp.query (op, word)) cfg)).run (s, log)
    (cur.1, cur.2.1) = machine.popStep (cfg, s) ∧
      (∀ w ∈ cur.2.2, w ∈ log ∨
        ((machine.pendingQuery cfg).isSome = true ∧ w = machine.pendingRequest cfg)) := by
  cases hst : cfg.tapes.state with
  | none =>
    have hpq : machine.pendingQuery cfg = none := by simp [MultiTapePTM.pendingQuery, hst]
    have hloc : machine.localStep cfg = cfg := by simp [MultiTapePTM.localStep, hst]
    have hfin : MultiTapeMachine.finiteStep machine
        (fun choices => choices <$> (pure false : WordQueryComp Operation Bool))
        (fun op word =>
          OracleComp.query (spec := fun _ : Operation × List Bool => List Bool) (op, word)) cfg =
        pure cfg := by
      simp [MultiTapeMachine.finiteStep, hst]
    have hrun_n : (OracleComp.interpret (m := StateM (List Bool × List (List Bool)))
        (fun q => (logPop q : StateM _ _))
        (MultiTapeMachine.finiteStep machine
          (fun choices => choices <$> (pure false : WordQueryComp Operation Bool))
          (fun op word =>
            OracleComp.query (spec := fun _ : Operation × List Bool => List Bool) (op, word))
          cfg)).run (s, log) = (cfg, (s, log)) := by
      rw [hfin, OracleComp.interpret_pure, StateT.run_pure]; rfl
    rw [hrun_n]
    exact ⟨by simp [MultiTapePTM.popStep, hpq, hloc], fun _ h => Or.inl h⟩
  | some control =>
    cases htr : machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols false with
    | step action symbol move =>
      have hpq : machine.pendingQuery cfg = none := by
        simp [MultiTapePTM.pendingQuery, hst, htr]
      have hloc : machine.localStep cfg = cfg.step action symbol move := by
        simp [MultiTapePTM.localStep, hst, htr]
      have hfin : MultiTapeMachine.finiteStep machine
          (fun choices => choices <$> (pure false : WordQueryComp Operation Bool))
          (fun op word =>
            OracleComp.query (spec := fun _ : Operation × List Bool => List Bool) (op, word)) cfg =
          pure (cfg.step action symbol move) := by
        simp [MultiTapeMachine.finiteStep, hst, htr]
      have hrun_s : (OracleComp.interpret (m := StateM (List Bool × List (List Bool)))
          (fun q => (logPop q : StateM _ _))
          (MultiTapeMachine.finiteStep machine
            (fun choices => choices <$> (pure false : WordQueryComp Operation Bool))
            (fun op word =>
              OracleComp.query (spec := fun _ : Operation × List Bool => List Bool) (op, word))
            cfg)).run (s, log) = (cfg.step action symbol move, (s, log)) := by
        rw [hfin, OracleComp.interpret_pure, StateT.run_pure]; rfl
      rw [hrun_s]
      exact ⟨by simp [MultiTapePTM.popStep, hpq, hloc], fun _ h => Or.inl h⟩
    | query op next =>
      have hpq : machine.pendingQuery cfg = some (op, next) := by
        simp [MultiTapePTM.pendingQuery, hst, htr]
      have hreq : machine.pendingRequest cfg = (cfg.channels op).1 := by
        simp [MultiTapePTM.pendingRequest, hpq]
      have hrec : ∀ b, machine.receiveBit (cfg, b) = cfg.receive op next [b] := fun b => by
        simp [MultiTapePTM.receiveBit, hpq]
      have hrun_q : (OracleComp.interpret (m := StateM (List Bool × List (List Bool)))
          (fun q => (logPop q : StateM _ _))
          (MultiTapeMachine.finiteStep machine
            (fun choices => choices <$> (pure false : WordQueryComp Operation Bool))
            (fun op word =>
              OracleComp.query (spec := fun _ : Operation × List Bool => List Bool) (op, word))
            cfg)).run (s, log) =
          (cfg.receive op next [s.headD false], (s.tail, log ++ [(cfg.channels op).1])) := by
        simp only [MultiTapeMachine.finiteStep, hst, htr, map_pure, pure_bind,
          OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind]
        rfl
      rw [hrun_q]
      refine ⟨by simp [MultiTapePTM.popStep, hpq, hrec], fun w hw => ?_⟩
      rcases List.mem_append.mp hw with hlog | hsing
      · exact Or.inl hlog
      · exact Or.inr ⟨by simp [hpq], by rw [hreq, List.mem_singleton.mp hsing]⟩

private theorem run_interpret_logPop_machine {k : ℕ} {Control Operation : Type}
    [DecidableEq Operation] (machine : MultiTapePTM k Bool Control Operation)
    (fuel : ℕ) (input s₀ : List Bool) :
    ∀ w ∈ ((OracleComp.interpret (m := StateM (List Bool × List (List Bool)))
        (fun q => (logPop q : StateM _ _))
        (machine.run (pure false) (fun op word => OracleComp.query (op, word))
          fuel input)).run (s₀, [])).2.2,
      ∃ i < fuel,
        (machine.pendingQuery
          ((machine.popStep^[i] (FiniteConfig.init machine.initial input, s₀)).1)).isSome = true ∧
        w = machine.pendingRequest
          ((machine.popStep^[i] (FiniteConfig.init machine.initial input, s₀)).1) := by
  change ∀ w ∈ ((OracleComp.interpret (m := StateM (List Bool × List (List Bool)))
      (fun q => (logPop q : StateM _ _))
      (MultiTapeMachine.run machine (fun choices => choices <$> (pure false : OracleComp _ Bool))
        (fun op word => OracleComp.query (op, word)) fuel input)).run (s₀, [])).2.2, _
  rw [← finiteRunFrom_init, finiteRunFrom, OracleComp.interpret_map, StateT.run_map]
  suffices h : ∀ (n : ℕ) (acc : List (List Bool)),
      let res := (OracleComp.interpret (m := StateM (List Bool × List (List Bool)))
        (fun q => (logPop q : StateM _ _))
        (OracleComp.iterate n (MultiTapeMachine.finiteStep machine
          (fun choices => choices <$> (pure false : OracleComp _ Bool))
          (fun op word => OracleComp.query (op, word)))
          (FiniteConfig.init machine.initial input))).run (s₀, acc)
      (res.1, res.2.1) = machine.popStep^[n] (FiniteConfig.init machine.initial input, s₀) ∧
        ∀ w ∈ res.2.2, w ∈ acc ∨ ∃ i < n,
          (machine.pendingQuery
            ((machine.popStep^[i]
              (FiniteConfig.init machine.initial input, s₀)).1)).isSome = true ∧
          w = machine.pendingRequest
            ((machine.popStep^[i] (FiniteConfig.init machine.initial input, s₀)).1) by
    intro w hw; simpa using (h fuel []).2 w hw
  intro n; induction n with
  | zero => intro acc; exact ⟨rfl, fun _ hw => Or.inl hw⟩
  | succ n ih =>
    intro acc; obtain ⟨heq, hmem⟩ := ih acc
    set prev := (OracleComp.interpret (m := StateM (List Bool × List (List Bool)))
      (fun q => (logPop q : StateM _ _))
      (OracleComp.iterate n (MultiTapeMachine.finiteStep machine
        (fun choices => choices <$> (pure false : OracleComp _ Bool))
        (fun op word => OracleComp.query (op, word)))
        (FiniteConfig.init machine.initial input))).run (s₀, acc)
    have hcfg : prev.1 = (machine.popStep^[n]
        (FiniteConfig.init machine.initial input, s₀)).1 := congrArg Prod.fst heq
    have hstep := run_interpret_logPop_finiteStep machine prev.1 prev.2.1 prev.2.2
    rw [OracleComp.iterate_succ, OracleComp.interpret_bind, StateT.run_bind]
    refine ⟨by rw [Function.iterate_succ_apply', ← heq]; exact hstep.1, fun w hw => ?_⟩
    rcases hstep.2 w hw with hprev | ⟨hpq, hw_eq⟩
    · exact (hmem w hprev).imp id fun ⟨i, hi, hpqi, hwi⟩ =>
        ⟨i, Nat.lt_succ_of_lt hi, hpqi, hwi⟩
    · rw [hcfg] at hpq hw_eq; exact Or.inr ⟨n, Nat.lt_succ_self n, hpq, hw_eq⟩

private theorem computableInPolyTime_popStep_aux {k : ℕ} {Control Operation : Type}
    [Finite Control] [Fintype Operation] [DecidableEq Operation]
    (machine : MultiTapePTM k Bool Control Operation) :
    ComputableInPolyTime machine.popStep
      (encPair encFiniteConfig encBits) (encPair encFiniteConfig encBits) := by
  unfold MultiTapePTM.popStep
  exact ComputableInPolyTime.ite
    ((ComputableInPolyTime.of_finite (encOut := encBool) Option.isSome).comp
      (machine.pendingQuery_pt.comp (fst _ _)))
    ((machine.receiveBit_pt.comp ((fst _ _).prod
      ((headD (encA := encBool) (encL := encBits) false).comp (snd _ _)))).prod
      (bitsTail.comp (snd _ _)))
    ((machine.localStep_pt.comp (fst _ _)).prod (snd _ _))

private theorem getD_bits_foldr_bit_aux (l : List Bool) (i : ℕ) :
    (l.foldr Nat.bit 0).bits.getD i false = l.getD i false := by
  change (l.foldr Nat.bit 0).bits.getD i default = l.getD i default
  rw [List.getD_default_eq_getI, ← Nat.testBit_eq_inth]
  induction l generalizing i with
  | nil => simp
  | cons _ _ ih =>
    rw [List.foldr_cons]; cases i <;> [simp; simpa [Nat.testBit_bit_succ] using ih _]

private def cfgAtStepAux {α : Type} (enc : α ↪ List Bool) {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit) (x : (α × List Bool) × ℕ) :
    FiniteConfig k Bool Control Unit :=
  (machine.popStep^[x.2] (FiniteConfig.init machine.initial (enc x.1.1), x.1.2)).1

private def stepYAux {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit) (Y : List (List Bool))
    (cfg : FiniteConfig k Bool Control Unit) : FiniteConfig k Bool Control Unit :=
  if (machine.pendingQuery cfg).isSome then
    machine.receiveBit (cfg, Y.any fun w => decide (w = machine.pendingRequest cfg))
  else machine.localStep cfg

private theorem popStep_space_and_cfgAtStep_pt {α : Type} {enc : α ↪ List Bool}
    {k : ℕ} {Control : Type} [Finite Control] (machine : MultiTapePTM k Bool Control Unit) :
    (∀ (a : α) (s : List Bool) (i : ℕ),
      FiniteConfig.SpaceBound (enc a).length i 1 (cfgAtStepAux enc machine ((a, s), i)) ∧
      (machine.popStep^[i] (FiniteConfig.init machine.initial (enc a), s)).2.length ≤
        s.length) ∧
    ComputableInPolyTime (cfgAtStepAux enc machine)
      (encPair (encPair enc encBits) encUnary) encFiniteConfig := by
  have hspace_pop (a : α) (s : List Bool) (i : ℕ) :
      FiniteConfig.SpaceBound (enc a).length i 1 (cfgAtStepAux enc machine ((a, s), i)) ∧
      (machine.popStep^[i] (FiniteConfig.init machine.initial (enc a), s)).2.length ≤
        s.length := by
    unfold cfgAtStepAux
    induction i with
    | zero => exact ⟨FiniteConfig.spaceBound_init _ _ _, le_rfl⟩
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      have hfst : (machine.popStep
          (machine.popStep^[i] (FiniteConfig.init machine.initial (enc a), s))).1 =
          machine.answerStep
            (fun _ => [(machine.popStep^[i]
              (FiniteConfig.init machine.initial (enc a), s)).2.headD false])
            (machine.popStep^[i] (FiniteConfig.init machine.initial (enc a), s)).1 := by
        rw [machine.answerStep_bit (fun _ => _), MultiTapePTM.popStep]; split_ifs <;> rfl
      have hsnd : (machine.popStep
          (machine.popStep^[i] (FiniteConfig.init machine.initial (enc a), s))).2.length ≤
          (machine.popStep^[i] (FiniteConfig.init machine.initial (enc a), s)).2.length := by
        unfold MultiTapePTM.popStep; split_ifs <;> simp
      exact ⟨hfst ▸ machine.spaceBound_answerStep (fun _ => _) ih.1, hsnd.trans ih.2⟩
  refine ⟨hspace_pop, ?_⟩
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Unit)
  have hinit := (finiteConfig_init (k := k) (Oracle := Unit)
    ((fst enc encBits).comp (fst _ encUnary)) machine.initial).prod
    ((snd enc encBits).comp (fst _ _))
  have hbound : PolyBounded (fun x => (encPair (encPair enc encBits) encUnary x).length)
      (fun x => 2 * (cf * ((encPair (encPair enc encBits) encUnary x).length + 2)) + 1 +
        (encPair (encPair enc encBits) encUnary x).length) := by growth_poly
  have hit := ComputableInPolyTime.iterate (snd _ _) hinit
    (computableInPolyTime_popStep_aux machine) hbound fun x i _ => by
      dsimp only [Function.comp_apply]
      obtain ⟨h₁, h₂⟩ := hspace_pop x.1.1 x.1.2 i
      have hlen₁ : (encPair (encPair enc encBits) encUnary x).length =
          2 * (2 * (enc x.1.1).length + 1 + x.1.2.length) + 1 + x.2 := by
        rw [length_encPair x, length_encPair x.1, encBits_apply, encUnary_apply,
          List.length_replicate]
      have hc := (hcf _ _ _ _ h₁).trans (Nat.mul_le_mul_left cf (show
        (enc x.1.1).length + i + 1 + 1 ≤
          (encPair (encPair enc encBits) encUnary x).length + 2 by omega))
      change (encPair encFiniteConfig encBits
          (machine.popStep^[i] (FiniteConfig.init machine.initial (enc x.1.1), x.1.2))).length ≤ _
      rw [length_encPair, encBits_apply]
      exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hc) 1)
        (h₂.trans (by omega))
  exact ((fst encFiniteConfig encBits).comp hit).of_enc_eq fun _ =>
    congrArg encFiniteConfig (by dsimp only [cfgAtStepAux, Function.comp_apply]; rfl)

private theorem computableInPolyTime_runAgainstList_aux {α : Type} {enc : α ↪ List Bool}
    {k : ℕ} {Control : Type} [Finite Control] (machine : MultiTapePTM k Bool Control Unit)
    (cm dm : ℕ) :
    ComputableInPolyTime
      (fun p : α × List (List Bool) =>
        ((stepYAux machine p.2)^[cm * ((enc p.1).length + 1) ^ dm]
          (FiniteConfig.init machine.initial (enc p.1))).tapes.output)
      (encPair enc (encList encBits)) encBits := by
  let _ : Fintype Control := Fintype.ofFinite Control
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Unit)
  let T : α → ℕ := fun a => cm * ((enc a).length + 1) ^ dm
  have hT_pt : ComputableInPolyTime T enc encUnary :=
    ((unary_eval (Polynomial.C cm * (Polynomial.X + 1) ^ dm)).comp
      (encoding_length enc)).of_enc_eq fun a => by simp [T]
  have hstepY_eq : ∀ Y cfg,
      stepYAux machine Y cfg = machine.answerStep (fun q => [Y.any fun w => decide (w =
        q.2)]) cfg :=
    fun Y cfg => (machine.answerStep_bit (fun w => Y.any fun u => decide (u = w)) cfg).symm
  have hstepY_pt : ComputableInPolyTime
      (fun p : List (List Bool) × FiniteConfig k Bool Control Unit => stepYAux machine p.1 p.2)
      (encPair (encList encBits) encFiniteConfig) encFiniteConfig :=
    (ComputableInPolyTime.ite (encC := encBool)
      (((of_finite (encOut := encBool) Option.isSome).comp machine.pendingQuery_pt).comp (snd _ _))
      (machine.receiveBit_pt.comp ((snd _ _).prod
        (anyWithInput (test := fun p w => decide (w = machine.pendingRequest p.2)) (fst _ _)
          ((decide_eq' (snd _ _) ((machine.pendingRequest_pt.comp (snd _ _)).comp
            (fst _ _))).of_enc_eq fun _ =>
              congrArg encBool (by dsimp only [Function.comp_apply])))))
      (machine.localStep_pt.comp (snd _ _))).of_enc_eq fun _ =>
        congrArg encFiniteConfig (by dsimp only [stepYAux, Function.comp_apply])
  have hsize : PolyBounded (fun p : α × List (List Bool) =>
      (encPair enc (encList encBits) p).length)
      (fun p => cf * ((encPair enc (encList encBits) p).length +
        cm * ((encPair enc (encList encBits) p).length + 1) ^ dm + 2)) := by growth_poly
  have henc_fst : ComputableInPolyTime (fun p : α × List (List Bool) => enc p.1)
      (encPair enc (encList encBits)) encBits :=
    (ComputableInPolyTime.of_eq (f := fun a : α => enc a) fun _ => rfl).comp
      (fst enc (encList encBits))
  have hit := iterateWith_spec (snd enc (encList encBits)) (hT_pt.comp (fst _ _))
    (finiteConfig_init henc_fst machine.initial) hstepY_pt
    (fun p i cfg => FiniteConfig.SpaceBound (enc p.1).length i 1 cfg)
    (fun _ => FiniteConfig.spaceBound_init _ _ _)
    (fun p _ _ _ hsp => by
      rw [hstepY_eq]
      exact machine.spaceBound_answerStep (fun u => p.2.any fun w => decide (w = u)) hsp)
    hsize fun p i cfg hi hsp => by
      dsimp only [Function.comp_apply] at hi
      have hlen_le := length_le_encPair_left enc (encList encBits) p
      have hT_le : T p.1 ≤ cm * ((encPair enc (encList encBits) p).length + 1) ^ dm :=
        Nat.mul_le_mul_left cm (Nat.pow_le_pow_left (by omega) dm)
      exact (hcf _ _ _ _ hsp).trans (Nat.mul_le_mul_left cf (by omega))
  exact ((by fun_prop : ComputableInPolyTime
    (fun cfg : FiniteConfig k Bool Control Unit => cfg.tapes.output)
    encFiniteConfig encBits).comp hit.1).of_enc_eq fun _ =>
      congrArg encBits (by dsimp only [T, Function.comp_apply])

open Classical in
private theorem exists_query_tree_simulator {α : Type} {enc : α ↪ List Bool}
    {A : Set (List Bool)} {c_q : ℕ} {f : α → Bool}
    (hf : ComputableInPolyTimeWithOracleQueries A (fun n => c_q * Nat.log 2 n + c_q)
      f enc encBool) :
    ∃ (cm dm : ℕ) (allDistinctQueries : α → List (List Bool))
      (runAgainstList : α × List (List Bool) → List Bool),
      ComputableInPolyTime allDistinctQueries enc (encList encBits) ∧
      ComputableInPolyTime runAgainstList (encPair enc (encList encBits)) encBits ∧
      (∀ a w, w ∈ allDistinctQueries a → w.length ≤ cm * ((enc a).length + 1) ^ dm) ∧
      (∀ a, (runAgainstList (a, (allDistinctQueries a).filter fun w => decide (w ∈ A))).headD
          false = f a) := by
  obtain ⟨program, hcert, hprog⟩ := hf
  obtain ⟨k, Control, _, machine, cm, dm, hrun⟩ :=
    IsOraclePPTOn.exists_run_pure_false_stateM hcert
  let _ : Fintype Control := Fintype.ofFinite Control
  have hrun_stateless : ∀ (a : α) (ans : Unit × List Bool → List Bool),
      OracleComp.interpret (m := Id) ans
        (machine.run (pure false) (fun op word => OracleComp.query (op, word))
          (cm * ((enc a).length + 1) ^ dm) (enc a)) =
        encBool (OracleComp.interpret (m := Id) ans (program a)) := fun a ans => by
    have h := congrArg Prod.fst (hrun a Unit (fun q s => (ans q, s)) ())
    have e {γ} (p : WordQueryComp Unit γ) :
        (OracleComp.interpret (m := StateM Unit)
          (fun q => ((fun s => (ans q, s)) : StateM Unit _)) p).run () =
          (OracleComp.interpret (m := Id) ans p, ()) :=
      OracleComp.run_interpret_stateless (m := Id) ans p ()
    rwa [e, e] at h
  let T : α → ℕ := fun a => cm * ((enc a).length + 1) ^ dm
  let R : α → ℕ := fun a => 2 ^ c_q * ((enc a).length + 1) ^ c_q
  have hT_pt : ComputableInPolyTime T enc encUnary :=
    ((unary_eval (Polynomial.C cm * (Polynomial.X + 1) ^ dm)).comp
      (encoding_length enc)).of_enc_eq fun a => by simp [T]
  have hR_pt : ComputableInPolyTime R enc encUnary :=
    ((unary_eval (Polynomial.C (2 ^ c_q) * (Polynomial.X + 1) ^ c_q)).comp
      (encoding_length enc)).of_enc_eq fun a => by simp [R]
  obtain ⟨hspace_pop, hcfgAtStep_pt⟩ :=
    popStep_space_and_cfgAtStep_pt (enc := enc) machine
  let rawQueries : α → List (List Bool) := fun a =>
    (List.range (R a)).flatMap fun j =>
      ((List.range (T a)).filter fun i =>
        (machine.pendingQuery (cfgAtStepAux enc machine ((a, Nat.bits j), i))).isSome).map
          fun i => machine.pendingRequest (cfgAtStepAux enc machine ((a, Nat.bits j), i))
  have hbits : ComputableInPolyTime (fun j : ℕ => Nat.bits j) encUnary encBits :=
    ((ComputableInPolyTime.of_eq (encIn := encNat) (encOut := encBits)
      (f := fun j : ℕ => encNat j) fun _ => rfl).comp unary_to_binary).of_enc_eq
      fun j => by rw [encBits_apply, Function.comp_apply, encNat_apply]; rfl
  have hraw_pt : ComputableInPolyTime rawQueries enc (encList encBits) := by
    have hcfg_p := hcfgAtStep_pt.comp
      (((fst enc encUnary).comp (fst (encPair enc encUnary) encUnary) |>.prod
        (hbits.comp ((snd enc encUnary).comp (fst (encPair enc encUnary) encUnary)))).prod
          (snd (encPair enc encUnary) encUnary))
    exact (flatMapWithInput
      (f := fun a j => ((List.range (T a)).filter fun i =>
        (machine.pendingQuery (cfgAtStepAux enc machine ((a, Nat.bits j), i))).isSome).map
          fun i => machine.pendingRequest (cfgAtStepAux enc machine ((a, Nat.bits j), i)))
      (range.comp hR_pt)
      ((mapWithInput (f :=
          fun aj i => machine.pendingRequest (cfgAtStepAux enc machine ((aj.1, Nat.bits aj.2), i)))
        (filterWithInput (test := fun aj i =>
            (machine.pendingQuery (cfgAtStepAux enc machine ((aj.1, Nat.bits aj.2), i))).isSome)
          (range.comp (hT_pt.comp (fst _ _)))
          ((((of_finite (encOut := encBool) Option.isSome).comp machine.pendingQuery_pt).comp
            hcfg_p).of_enc_eq fun _ => congrArg encBool (by dsimp only [Function.comp_apply])))
        ((machine.pendingRequest_pt.comp hcfg_p).of_enc_eq fun _ =>
          congrArg encBits (by dsimp only [Function.comp_apply]))).of_enc_eq fun _ =>
        congrArg (encList encBits) (by dsimp only [Function.comp_apply]))).of_enc_eq fun _ =>
      congrArg (encList encBits) (by dsimp only [rawQueries, Function.comp_apply])
  let allDistinctQueries : α → List (List Bool) := fun a =>
    selectDistinct (rawQueries a) (List.replicate (rawQueries a).length true)
  have hrep : ComputableInPolyTime (fun n : ℕ => List.replicate n true) encUnary encBits :=
    ComputableInPolyTime.of_eq (encIn := encUnary) (encOut := encBits)
      (f := fun n : ℕ => List.replicate n true) fun n => by simp only [encBits_apply,
        encUnary_apply]
  have hall_pt : ComputableInPolyTime allDistinctQueries enc (encList encBits) :=
    ((computableInPolyTime_selectDistinct encBits).comp
      (hraw_pt.prod (hrep.comp ((length_list encBits).comp hraw_pt)))).of_enc_eq
      fun _ => congrArg (encList encBits) (by dsimp only [allDistinctQueries, Function.comp_apply])
  have hall_length_le : ∀ a (w : List Bool), w ∈ allDistinctQueries a → w.length ≤ T a := by
    intro a w hw
    have hw_raw := (mem_selectDistinct_replicate (l := rawQueries a)).mp hw
    simp only [rawQueries, List.mem_flatMap, List.mem_range, List.mem_map,
      List.mem_filter] at hw_raw
    obtain ⟨j, _, i, ⟨hi, _⟩, rfl⟩ := hw_raw
    exact (machine.length_pendingRequest_le (hspace_pop a (Nat.bits j) i).1).trans hi.le
  have hall_covers : ∀ a (q : Unit × List Bool),
      q ∈ OracleComp.queriesWith (languageOracle A) (program a) →
        q.2 ∈ allDistinctQueries a := by
    intro a q hq
    dsimp only [allDistinctQueries]; rw [mem_selectDistinct_replicate]
    let answers := (OracleComp.queriesWith (languageOracle A) (program a)).map
      fun q' => decide (q'.2 ∈ A)
    let jStar := answers.foldr Nat.bit 0
    have hlog_bound : 2 ^ (c_q * Nat.log 2 (enc a).length + c_q) ≤ R a := by
      have hlog : 2 ^ Nat.log 2 (enc a).length ≤ (enc a).length + 1 := by
        rcases Nat.eq_zero_or_pos (enc a).length with h0 | hn
        · simp [h0]
        · exact (Nat.pow_log_le_self 2 hn.ne').trans (Nat.le_succ _)
      dsimp only [R]; rw [pow_add, mul_comm (2 ^ c_q), mul_comm c_q, pow_mul]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hlog c_q)
    have hjStar_lt : jStar < R a :=
      (Nat.foldr_bit_lt answers).trans_le
        ((Nat.pow_le_pow_right (by omega) (by simpa [answers] using (hprog a).2)).trans hlog_bound)
    have hprog_log := run_interpret_logPop_program A (program a) (Nat.bits jStar) []
      fun idx => getD_bits_foldr_bit_aux answers idx
    have hm_eq := congrArg (fun p => p.2.2) (hrun a _ logPop (Nat.bits jStar, []))
    rw [hprog_log] at hm_eq
    dsimp only [Prod.map, id_eq] at hm_eq
    rw [List.nil_append] at hm_eq
    have hmem_log : q.2 ∈ (OracleComp.queriesWith (languageOracle A) (program a)).map Prod.snd :=
      List.mem_map_of_mem hq
    rw [← hm_eq] at hmem_log
    obtain ⟨i, hi, hpq, hw⟩ := run_interpret_logPop_machine machine (T a) (enc a)
      (Nat.bits jStar) q.2 hmem_log
    simp only [rawQueries, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
      cfgAtStepAux]
    exact ⟨jStar, hjStar_lt, i, ⟨hi, hpq⟩, hw.symm⟩
  have hstepY_eq : ∀ Y cfg,
      stepYAux machine Y cfg =
        machine.answerStep (fun q => [Y.any fun w => decide (w = q.2)]) cfg :=
    fun Y cfg => (machine.answerStep_bit (fun w => Y.any fun u => decide (u = w)) cfg).symm
  let runAgainstList : α × List (List Bool) → List Bool := fun p =>
    ((stepYAux machine p.2)^[T p.1] (FiniteConfig.init machine.initial (enc p.1))).tapes.output
  have hrunAgainstList_pt : ComputableInPolyTime runAgainstList
      (encPair enc (encList encBits)) encBits :=
    computableInPolyTime_runAgainstList_aux machine cm dm
  have hrun_YStar : ∀ a,
      (runAgainstList (a, (allDistinctQueries a).filter fun w => decide (w ∈ A))).headD false =
        f a := by
    intro a
    have hfun : ∀ Y, stepYAux machine Y =
        machine.answerStep (fun q => [Y.any fun w => decide (w = q.2)]) :=
      fun Y => funext (hstepY_eq Y)
    have hrunAgainstList_eq : ∀ Y, runAgainstList (a, Y) =
        encBool (OracleComp.interpret (m := Id)
          (fun q => [Y.any fun w => decide (w = q.2)]) (program a)) := fun Y => by
      dsimp only [runAgainstList, T]; rw [hfun, ← machine.interpret_run_pure_false, hrun_stateless]
    rw [hrunAgainstList_eq, encBool_apply, List.headD_cons, ← (hprog a).1]; symm
    refine interpret_congr_queriesWith (program a) fun q hq => ?_
    have hmemU := hall_covers a q hq
    simp only [languageOracle]; congr 1
    by_cases hqA : q.2 ∈ A
    · simp only [hqA, decide_true]
      exact (List.any_eq_true.mpr
        ⟨q.2, List.mem_filter.mpr ⟨hmemU, decide_eq_true hqA⟩, decide_eq_true rfl⟩).symm
    · simp only [hqA, decide_false]
      refine (Bool.eq_false_iff.mpr fun h => ?_).symm
      obtain ⟨w, hw, hwq⟩ := List.any_eq_true.mp h
      rw [of_decide_eq_true hwq] at hw
      exact hqA (of_decide_eq_true (List.mem_filter.mp hw).2)
  exact ⟨cm, dm, allDistinctQueries, runAgainstList, hall_pt, hrunAgainstList_pt,
    hall_length_le, hrun_YStar⟩

open Classical in
private theorem exists_scoreGeLang_mem_NP {α : Type} {enc : α ↪ List Bool}
    {A : Set (List Bool)} (hA_NP : A ∈ NP encBits) {f : α → Bool}
    {cm dm : ℕ} {allDistinctQueries : α → List (List Bool)}
    {runAgainstList : α × List (List Bool) → List Bool}
    (hall_pt : ComputableInPolyTime allDistinctQueries enc (encList encBits))
    (hrunAgainstList_pt : ComputableInPolyTime runAgainstList
      (encPair enc (encList encBits)) encBits)
    (hall_length_le : ∀ a w, w ∈ allDistinctQueries a →
      w.length ≤ cm * ((enc a).length + 1) ^ dm)
    (hrun_YStar : ∀ a,
      (runAgainstList (a, (allDistinctQueries a).filter fun w => decide (w ∈ A))).headD false =
        f a) :
    ∃ ScoreGeLang : Set (α × ℕ),
      ScoreGeLang ∈ NP (encPair enc encUnary) ∧
      ∀ a m, (a, m) ∈ ScoreGeLang ↔
        m ≤ 2 * ((allDistinctQueries a).filter fun w => decide (w ∈ A)).length + (f a).toNat := by
  obtain ⟨p_A, V_A, hVA_pt, hVA_spec⟩ := mem_NP.mp hA_NP
  let validSublist : α → List (List Bool) → List (List Bool) := fun a certs =>
    (((allDistinctQueries a).zip certs).filter fun wc =>
      (wc.2.length == p_A.eval wc.1.length) && V_A wc).map Prod.fst
  let checkScore : (α × ℕ) × (List (List Bool) × Bool) → Bool := fun x =>
    let Y := validSublist x.1.1 x.2.1
    decide (x.1.2 ≤ 2 * Y.length + x.2.2.toNat) &&
      (!x.2.2 || (runAgainstList (x.1.1, Y)).headD false)
  have hvalidSublist_pt : ComputableInPolyTime
      (fun x : (α × ℕ) × (List (List Bool) × Bool) => validSublist x.1.1 x.2.1)
      (encPair (encPair enc encUnary) (encPair (encList encBits) encBool))
      (encList encBits) := by
    have hzip := (zip encBits encBits).comp
      ((hall_pt.comp ((fst enc encUnary).comp (fst _ _))).prod
        ((fst (encList encBits) encBool).comp (snd _ _)))
    have hpred : ComputableInPolyTime
        (fun wc : List Bool × List Bool => (wc.2.length == p_A.eval wc.1.length) && V_A wc)
        (encPair encBits encBits) encBool :=
      bool_and' (unary_beq (length_bits.comp (snd _ _))
        ((unary_eval p_A).comp (length_bits.comp (fst _ _)))) hVA_pt
    exact mapWithInput (f := fun _ wc => wc.1) ((ComputableInPolyTime.filter hpred).comp hzip)
      (((fst encBits encBits).comp (snd _ _)).of_enc_eq fun _ => rfl)
  have hcheckScore_pt : ComputableInPolyTime checkScore
      (encPair (encPair enc encUnary) (encPair (encList encBits) encBool)) encBool := by
    have hx_a := (fst enc encUnary).comp (fst _ (encPair (encList encBits) encBool))
    have hx_m := (snd enc encUnary).comp (fst _ (encPair (encList encBits) encBool))
    have hx_bit := (snd (encList encBits) encBool).comp (snd (encPair enc encUnary) _)
    exact bool_and'
      (unary_le' hx_m (unary_add' (unary_mul' (const 2)
        ((length_list encBits).comp hvalidSublist_pt)) (bool_toUnary.comp hx_bit)))
      (bool_or.comp ((bool_not.comp hx_bit).prod
        ((headD (encA := encBool) (encL := encBits) false).comp
          (hrunAgainstList_pt.comp (hx_a.prod hvalidSublist_pt)))))
  have hmap_fst_zip_sub : ∀ (l₁ l₂ : List (List Bool)),
      ((l₁.zip l₂).map Prod.fst).Sublist l₁ := by
    intro l₁
    induction l₁ with
    | nil => intro _; simp
    | cons _ tl ih => intro l₂; cases l₂ <;> [simp; simp [ih _]]
  let ScoreGeLang : Set (α × ℕ) :=
    {p | ∃ w : List (List Bool) × Bool, checkScore (p, w) = true}
  have hScore_NP : ScoreGeLang ∈ NP (encPair enc encUnary) := by
    obtain ⟨cU, dU, hlenU⟩ := hall_pt.polyBounded_length.exists_le
    let certCap : ℕ → ℕ := fun n =>
      2 * ((cU * (n + 1) ^ dU) * (2 * (p_A.eval (cm * (n + 1) ^ dm) + 1) + 2)) + 5
    have hpoly_cap : PolynomiallyBounded certCap := by dsimp [certCap]; fun_prop
    obtain ⟨p_wit, hp_wit⟩ :=
      (PolyBounded.of_polynomiallyBounded
        (fun p : α × ℕ => (encPair enc encUnary p).length) hpoly_cap).exists_polynomial
    refine mem_NP_of_check (p := p_wit) (Decoder.pair (.list .bits) .bool) hcheckScore_pt
      (fun _ w hw => ⟨w, hw⟩) fun p ⟨⟨certs, bit⟩, hw⟩ => ?_
    let certs' : List (List Bool) :=
      ((allDistinctQueries p.1).zip certs).map fun wc =>
        if (wc.2.length == p_A.eval wc.1.length) && V_A wc then wc.2
        else List.replicate (p_A.eval wc.1.length + 1) false
    have hzip_eq : (allDistinctQueries p.1).zip certs' =
        ((allDistinctQueries p.1).zip certs).map fun wc =>
          (wc.1, if (wc.2.length == p_A.eval wc.1.length) && V_A wc then wc.2
            else List.replicate (p_A.eval wc.1.length + 1) false) := by
      apply List.ext_getElem (by simp [certs']); intro _ _ _; simp [certs']
    have hY_eq : validSublist p.1 certs' = validSublist p.1 certs := by
      dsimp only [validSublist]; rw [hzip_eq, List.filter_map, List.map_map]; congr 1
      refine List.filter_congr fun wc _ => ?_
      dsimp only [Function.comp_apply]
      by_cases hcond : ((wc.2.length == p_A.eval wc.1.length) && V_A wc) = true <;> simp [hcond]
    refine ⟨(certs', bit), by dsimp only [checkScore] at hw ⊢; rwa [hY_eq],
      (?_ : _ ≤ certCap (encPair enc encUnary p).length).trans (hp_wit p)⟩
    have hn_le := length_le_encPair_left enc encUnary p
    have hT_le : cm * ((enc p.1).length + 1) ^ dm ≤
        cm * ((encPair enc encUnary p).length + 1) ^ dm :=
      Nat.mul_le_mul_left cm (Nat.pow_le_pow_left (Nat.succ_le_succ hn_le) dm)
    have hU_cnt : certs'.length ≤ cU * ((encPair enc encUnary p).length + 1) ^ dU :=
      (by simp [certs'] : certs'.length ≤ (allDistinctQueries p.1).length).trans
        ((length_le_length_encList encBits _).trans ((hlenU p.1).trans
          (Nat.mul_le_mul_left cU (Nat.pow_le_pow_left (Nat.succ_le_succ hn_le) dU))))
    have helem : ∀ c ∈ certs', (encBits c).length ≤
        p_A.eval (cm * ((enc p.1).length + 1) ^ dm) + 1 := by
      intro c hc
      obtain ⟨wc, hwc, rfl⟩ := List.mem_map.mp hc
      have hwc_mem : wc.1 ∈ allDistinctQueries p.1 :=
        (hmap_fst_zip_sub (allDistinctQueries p.1) certs).subset
          (List.mem_map_of_mem (f := Prod.fst) hwc)
      have hpmono := Polynomial.eval_mono p_A (hall_length_le p.1 wc.1 hwc_mem)
      split_ifs with hok
      · simp only [Bool.and_eq_true, beq_iff_eq] at hok; rw [encBits_apply, hok.1]; omega
      · rw [encBits_apply, List.length_replicate]; omega
    have hlist_len := (length_encList_le encBits certs' helem).trans
      (Nat.mul_le_mul_left certs'.length (show
        2 * (p_A.eval (cm * ((enc p.1).length + 1) ^ dm) + 1) + 1 ≤
          2 * (p_A.eval (cm * ((enc p.1).length + 1) ^ dm) + 1) + 2 by omega))
    have hp_le := Polynomial.eval_mono p_A hT_le
    have hprod_le := Nat.mul_le_mul hU_cnt
      (show 2 * (p_A.eval (cm * ((enc p.1).length + 1) ^ dm) + 1) + 2 ≤
        2 * (p_A.eval (cm * ((encPair enc encUnary p).length + 1) ^ dm) + 1) + 2 by omega)
    rw [length_encPair, encBool_apply, List.length_singleton]; dsimp only [certCap]; omega
  let YStar : α → List (List Bool) := fun a =>
    (allDistinctQueries a).filter fun w => decide (w ∈ A)
  have hsublist_filter : ∀ {l₁ l₂ : List (List Bool)} {p : List Bool → Bool},
      l₁.Sublist l₂ → (∀ x ∈ l₁, p x = true) → l₁.Sublist (l₂.filter p) := by
    intro l₁ l₂ p hsub hp
    induction hsub with
    | slnil => exact .slnil
    | cons _ _ ih => rw [List.filter_cons]; split_ifs <;> [exact .cons _ (ih hp); exact ih hp]
    | cons_cons a _ ih =>
      rw [List.filter_cons, ite_eq_left (hp a List.mem_cons_self)]
      exact .cons_cons _ (ih fun x hx => hp x (List.mem_cons_of_mem a hx))
  have hvalidSublist_sub : ∀ a certs, (validSublist a certs).Sublist (YStar a) := by
    intro a certs
    have h1 : (validSublist a certs).Sublist (((allDistinctQueries a).zip certs).map Prod.fst) :=
      List.filter_sublist.map Prod.fst
    refine hsublist_filter (h1.trans (hmap_fst_zip_sub (allDistinctQueries a) certs)) fun w hw => ?_
    simp only [validSublist, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨⟨w', cert⟩, ⟨_, hlen_c, hv_c⟩, rfl⟩ := hw
    exact decide_eq_true ((hVA_spec w').mpr ⟨cert, hlen_c, hv_c⟩)
  have hexists_certsStar : ∀ a, ∃ certs : List (List Bool), validSublist a certs = YStar a := by
    intro a
    have hch : ∀ w : List Bool, ∃ c : List Bool,
        ((c.length == p_A.eval w.length) && V_A (w, c)) = decide (w ∈ A) := fun w => by
      by_cases hw : w ∈ A
      · obtain ⟨c, hc_len, hc_v⟩ := (hVA_spec w).mp hw; exact ⟨c, by simp [hw, hc_len, hc_v]⟩
      · exact ⟨List.replicate (p_A.eval w.length + 1) false, by simp [hw]⟩
    choose certOf hcertOf using hch
    refine ⟨(allDistinctQueries a).map certOf, ?_⟩
    have hzip_map : (allDistinctQueries a).zip ((allDistinctQueries a).map certOf) =
        (allDistinctQueries a).map fun w => (w, certOf w) := by
      apply List.ext_getElem (by simp); intro _ _ _; simp
    simp only [validSublist, YStar, hzip_map, List.filter_map, List.map_map]
    dsimp only [Function.comp_def]
    rw [List.filter_congr fun w _ => hcertOf w]; exact List.map_id _
  refine ⟨ScoreGeLang, hScore_NP, fun a m => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨certs, bit⟩, hc⟩
    simp only [checkScore, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      Bool.not_eq_true'] at hc
    have hsub := hvalidSublist_sub a certs
    have hsub_len : (validSublist a certs).length ≤
        ((allDistinctQueries a).filter fun w => decide (w ∈ A)).length := hsub.length_le
    rcases Nat.lt_or_eq_of_le hsub_len with hlt | heq_len
    · have := Bool.toNat_le bit; omega
    · have hY_eq : validSublist a certs = YStar a := hsub.eq_of_length heq_len
      cases bit with
      | false => simp at hc; omega
      | true =>
        have hf_t : f a = true := by
          rcases hc.2 with hf | hr; · cases hf
          · rwa [hY_eq, hrun_YStar] at hr
        rw [hf_t]; simpa [heq_len] using hc.1
  · intro hm_le
    obtain ⟨certsStar, hcertsStar⟩ := hexists_certsStar a
    refine ⟨(certsStar, f a), ?_⟩
    simp only [checkScore, hcertsStar, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      Bool.not_eq_true']
    exact ⟨hm_le, by cases hfa : f a <;> [exact Or.inl rfl; exact Or.inr (by
      simpa [YStar, hfa] using hrun_YStar a)]⟩

/-- **Wagner–Kadin hardness of `EqualIndepNum` for $\Theta_2^p$**. -/
theorem EqualIndepNum_pnpLogHard :
    PolyTimeHard @PNPLog (encPair encGraph encGraph) EqualIndepNum := by
  classical
  intro α enc L hL
  obtain ⟨A, hA_NP, c_q, f, hf_oracle, hL_iff⟩ := mem_PNPLog.mp hL
  obtain ⟨cm, dm, allDistinctQueries, runAgainstList, hall_pt, hrunAgainstList_pt,
    hall_length_le, hrun_YStar⟩ := exists_query_tree_simulator hf_oracle
  obtain ⟨ScoreGeLang, hScore_NP, hScore_iff⟩ := exists_scoreGeLang_mem_NP hA_NP
    hall_pt hrunAgainstList_pt hall_length_le hrun_YStar
  let KStar : α → ℕ := fun a => ((allDistinctQueries a).filter fun w => decide (w ∈ A)).length
  obtain ⟨toCNF, htoCNF_pt, htoCNF_iff⟩ :=
    CookLevin.SAT_npHard (encPair enc encUnary) ScoreGeLang hScore_NP
  let Q : α → ℕ := fun a => (allDistinctQueries a).length
  have hQ_pt : ComputableInPolyTime Q enc encUnary := (length_list encBits).comp hall_pt
  let phiOdd : α × ℕ → CNF ℕ := fun p => toCNF (p.1, 2 * p.2 + 1)
  let phiEven : α × ℕ → CNF ℕ := fun p => toCNF (p.1, 2 * (p.2 + 1))
  have hphiOdd_pt : ComputableInPolyTime phiOdd (encPair enc encUnary) encCNF :=
    htoCNF_pt.comp ((fst _ _).prod (unary_add' (unary_mul' (const 2) (snd _ _)) (const 1)))
  have hphiEven_pt : ComputableInPolyTime phiEven (encPair enc encUnary) encCNF :=
    htoCNF_pt.comp ((fst _ _).prod (unary_mul' (const 2) (unary_add' (snd _ _) (const 1))))
  let unarySum : List ℕ → ℕ := fun l => l.foldl (· + ·) 0
  have hfold_add : ∀ (l : List ℕ) (acc : ℕ), l.foldl (· + ·) acc = acc + l.sum := by
    intro l; induction l with
    | nil => intro _; simp
    | cons _ _ ih => intro _; simp [ih, Nat.add_assoc]
  have hunarySum_eq : ∀ l, unarySum l = l.sum := fun l => by
    simpa [unarySum] using hfold_add l 0
  have hunarySum_pt : ComputableInPolyTime unarySum (encList encUnary) encUnary := by
    refine foldl' .id' (const 0) unary_add .self fun l i _ => ?_
    simp only [encUnary_apply, List.length_replicate, hfold_add, zero_add]
    have hsum_take : ∀ m : List ℕ, m.sum ≤ (encList encUnary m).length := fun m => by
      induction m with
      | nil => simp
      | cons _ _ ih =>
        simp only [List.sum_cons, encList_cons, List.length_append, length_frame,
          encUnary_apply, List.length_replicate]; omega
    exact (hsum_take (l.take i)).trans (length_encList_take_le encUnary l i)
  let bOdd : α → ℕ := fun a =>
    unarySum ((List.range (Q a + 1)).map fun t => (phiOdd (a, t)).length)
  let bEven : α → ℕ := fun a =>
    unarySum ((List.range (Q a)).map fun t => (phiEven (a, t)).length)
  have hbOdd_pt := hunarySum_pt.comp
    (mapWithInput (f := fun a t => (phiOdd (a, t)).length)
      (range.comp (unary_add' hQ_pt (const 1)))
      ((SAT.computableInPolyTime_length hphiOdd_pt).of_enc_eq fun _ => rfl))
  have hbEven_pt := hunarySum_pt.comp
    (mapWithInput (f := fun a t => (phiEven (a, t)).length) (range.comp hQ_pt)
      ((SAT.computableInPolyTime_length hphiEven_pt).of_enc_eq fun _ => rfl))
  let buildX₁ : α → Graph := fun a =>
    disjointUnionList
      (((List.range (Q a + 1)).map fun t =>
          (SAT.toIndependentSet (clampCNF (phiOdd (a, t)))).graph) ++
        [edgelessGraph (bEven a + 1)])
  let buildX₂ : α → Graph := fun a =>
    disjointUnionList
      (((List.range (Q a)).map fun t =>
          (SAT.toIndependentSet (clampCNF (phiEven (a, t)))).graph) ++
        [edgelessGraph (bOdd a + 2)])
  have hX₁_pt : ComputableInPolyTime buildX₁ enc encGraph :=
    computableInPolyTime_disjointUnionList.comp ((listAppend encGraph).comp
      ((mapWithInput (f := fun a t => (SAT.toIndependentSet (clampCNF (phiOdd (a, t)))).graph)
        (range.comp (unary_add' hQ_pt (const 1)))
        ((encIndependentSetInstance_graph_polyTime
          (SAT.computableInPolyTime_toIndependentSet.comp
            (computableInPolyTime_clampCNF.comp hphiOdd_pt))).of_enc_eq fun _ => rfl)).prod
        ((cons encGraph).comp ((computableInPolyTime_edgelessGraph.comp
          (unary_add' hbEven_pt (const 1))).prod (const [])))))
  have hX₂_pt : ComputableInPolyTime buildX₂ enc encGraph :=
    computableInPolyTime_disjointUnionList.comp ((listAppend encGraph).comp
      ((mapWithInput (f := fun a t => (SAT.toIndependentSet (clampCNF (phiEven (a, t)))).graph)
        (range.comp hQ_pt)
        ((encIndependentSetInstance_graph_polyTime
          (SAT.computableInPolyTime_toIndependentSet.comp
            (computableInPolyTime_clampCNF.comp hphiEven_pt))).of_enc_eq fun _ => rfl)).prod
        ((cons encGraph).comp ((computableInPolyTime_edgelessGraph.comp
          (unary_add' hbOdd_pt (const 2))).prod (const [])))))
  have hsum_range_ite : ∀ M K : ℕ, K ≤ M →
      ((List.range M).map fun t => if t < K then 1 else 0).sum = K := by
    intro M; induction M with
    | zero =>
      intro K hK
      obtain rfl : K = 0 := by omega
      rfl
    | succ m ih =>
      intro K hK
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
      rcases Nat.eq_or_lt_of_le hK with rfl | hlt
      · have h1 : ((List.range m).map fun t => if t < m + 1 then 1 else 0) =
            (List.range m).map fun _ => 1 :=
          List.map_congr_left fun t ht => by
            have := List.mem_range.mp ht; simp [Nat.lt_succ_of_lt this]
        rw [h1]; simp
      · rw [ih K (by omega), ite_eq_right (by omega), add_zero]
  have hsum_map_add : ∀ (l : List ℕ) (g₁ g₂ : ℕ → ℕ),
      (l.map fun x => g₁ x + g₂ x).sum = (l.map g₁).sum + (l.map g₂).sum := by
    intro l g₁ g₂; induction l with
    | nil => simp
    | cons _ _ ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]
  refine ⟨fun a => (buildX₁ a, buildX₂ a), hX₁_pt.prod hX₂_pt, fun a => ?_⟩
  have hK_le_Q : KStar a ≤ Q a := List.length_filter_le _ _
  have hfa_le : (f a).toNat ≤ 1 := Bool.toNat_le (f a)
  have hX₁_ind : (buildX₁ a).indepNum = bOdd a + (KStar a + (f a).toNat) + (bEven a + 1) := by
    simp only [buildX₁, indepNum_disjointUnionList, List.map_append, List.sum_append,
      List.map_map, List.map_singleton, List.sum_singleton, indepNum_edgelessGraph]
    congr 1
    have hmap1 : List.map ((fun g : Graph => g.indepNum) ∘ fun t =>
        (SAT.toIndependentSet (clampCNF (phiOdd (a, t)))).graph) (List.range (Q a + 1)) =
        (List.range (Q a + 1)).map fun t =>
          (phiOdd (a, t)).length + (if t < KStar a + (f a).toNat then 1 else 0) :=
      List.map_congr_left fun t _ => by
        dsimp only [Function.comp_apply]
        rw [indepNum_toIndependentSet_clampCNF, ← htoCNF_iff (a, 2 * t + 1), hScore_iff]
        congr 1
        have hiff : (2 * t + 1 ≤ 2 * KStar a + (f a).toNat) ↔ t < KStar a + (f a).toNat := by
          cases f a <;> simp
        exact ite_congr (propext hiff) (fun _ => rfl) (fun _ => rfl)
    rw [hmap1, hsum_map_add (List.range (Q a + 1)) (fun t => (phiOdd (a, t)).length)
      (fun t => if t < KStar a + (f a).toNat then 1 else 0), ← hunarySum_eq,
      hsum_range_ite (Q a + 1) (KStar a + (f a).toNat) (by omega)]
  have hX₂_ind : (buildX₂ a).indepNum = bEven a + KStar a + (bOdd a + 2) := by
    simp only [buildX₂, indepNum_disjointUnionList, List.map_append, List.sum_append,
      List.map_map, List.map_singleton, List.sum_singleton, indepNum_edgelessGraph]
    congr 1
    have hmap2 : List.map ((fun g : Graph => g.indepNum) ∘ fun t =>
        (SAT.toIndependentSet (clampCNF (phiEven (a, t)))).graph) (List.range (Q a)) =
        (List.range (Q a)).map fun t =>
          (phiEven (a, t)).length + (if t < KStar a then 1 else 0) :=
      List.map_congr_left fun t _ => by
        dsimp only [Function.comp_apply]
        rw [indepNum_toIndependentSet_clampCNF, ← htoCNF_iff (a, 2 * (t + 1)), hScore_iff]
        congr 1
        have hiff : (2 * (t + 1) ≤ 2 * KStar a + (f a).toNat) ↔ t < KStar a := by
          (cases f a <;> simp); omega
        exact ite_congr (propext hiff) (fun _ => rfl) (fun _ => rfl)
    rw [hmap2, hsum_map_add (List.range (Q a)) (fun t => (phiEven (a, t)).length)
      (fun t => if t < KStar a then 1 else 0), ← hunarySum_eq,
      hsum_range_ite (Q a) (KStar a) hK_le_Q]
  change a ∈ L ↔ (buildX₁ a).indepNum = (buildX₂ a).indepNum
  rw [hX₁_ind, hX₂_ind, hL_iff a]
  cases f a <;> simp <;> omega

/-- **`EqualIndepNum` is $\Theta_2^p$-complete.** -/
theorem EqualIndepNum_pnpLogComplete :
    PolyTimeComplete @PNPLog (encPair encGraph encGraph) EqualIndepNum :=
  ⟨EqualIndepNum_mem_PNPLog, EqualIndepNum_pnpLogHard⟩

end Cslib.Complexity
