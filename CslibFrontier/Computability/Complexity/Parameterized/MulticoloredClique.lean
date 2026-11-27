/-
Copyright (c) 2026 The FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# $\mathrm{W}[1]$-Completeness of Multicolored Clique and Power-of-Two Multicolored Clique

This module formalizes the parameterized **Multicolored Clique** ($k$-Multicolored Clique) problem
both on general vertex-partitioned graphs and in its canonical **Power-of-Two Equipartite** normal
form (`PowTwoMC`, where $k \ge 1$ color classes each have exact cardinality $n = 2^b$ with $b \ge 1$
and edges go strictly between distinct color classes), proving $\mathrm{W}[1]$-membership and
$\mathrm{W}[1]$-hardness under standard Lean axioms from `Cslib.Complexity.Clique_mem_W` and
`Cslib.Complexity.Clique_wHard`:

1. **Power-of-Two Equipartite Multicolored Clique (`PowTwoMCInstance`, `PowTwoMC`)**:
   - `PowTwoMCInstance` stores `k` (number of color classes, in unary), `b` (logarithmic bit-width
     per class, in unary), `n` (color-class size, in unary), and inter-color edge records
     `((i, u), (j, v))` (`i < j < k`, `u, v < n`).
   - `PowTwoMC` requires `1 ≤ k`, `1 ≤ b`, `n = 2 ^ b`, and a selector `sel : Fin k → Fin n` whose
     selected vertices are pairwise joined across all `i < j`.
2. **Unconditional $\mathrm{W}[1]$-completeness under standard Lean axioms**:
   - `fptReducible_clique_powTwoMC` and `powTwoMC_wHard`: polynomial-time FPT reduction from
     `Cslib.Complexity.Clique` by replicating `G.distinctVertices` across `k` color classes and
     padding each class with isolated dummy vertices up to `2 ^ (Nat.size |V| + 1) ≤ 4 |V| + 2`.
   - `fptReducible_powTwoMC_clique` and `powTwoMC_mem_W`: polynomial-time FPT reduction from
     `PowTwoMC` back to `Cslib.Complexity.Clique`.
   - `w_one_eq_fpt_iff_powTwoMC`: `W[1] = FPT` if and only if `PowTwoMC ∈ FPT`.

## Main definitions

* `Cslib.Complexity.PowTwoMCInstance`: power-of-two equipartite multicolored clique instance.
* `Cslib.Complexity.encPowTwoMCInstance`: binary encoding of `PowTwoMCInstance`.
* `Cslib.Complexity.PowTwoMC`: the parameterized decision problem $k$-Multicolored Clique on
  $k$ color classes of size $n = 2^b$.

## Main results

* `Cslib.Complexity.fptReducible_clique_powTwoMC`
* `Cslib.Complexity.powTwoMC_wHard`
* `Cslib.Complexity.fptReducible_powTwoMC_clique`
* `Cslib.Complexity.powTwoMC_mem_W`
* `Cslib.Complexity.w_one_eq_fpt_iff_powTwoMC`
-/

public section

open Cslib Cslib.Complexity Turing.MultiTapeTM

namespace Cslib.Complexity

/-! ### 1. Power-of-Two Equipartite Multicolored Clique -/

/-- An instance of **Power-of-Two Equipartite Multicolored Clique** (`PowTwoMC`): `k` color classes
(`0, …, k - 1`) each of declared size `n` (intended to equal `2 ^ b` with `b ≥ 1`), together with a
list of inter-color edges `((i, u), (j, v))` connecting vertex `u` of color `i` to vertex `v` of
color `j`. -/
@[ext]
structure PowTwoMCInstance where
  /-- Number of color classes (`k`), encoded in unary. -/
  k : ℕ
  /-- Logarithmic bit-length per color class (`b`), encoded in unary. -/
  b : ℕ
  /-- Size of each color class (`n`), encoded in unary (`n = 2 ^ b` on valid instances). -/
  n : ℕ
  /-- Directed inter-color edge list `((i, u), (j, v))` for `i < j`. -/
  edges : List ((ℕ × ℕ) × (ℕ × ℕ))
  deriving DecidableEq, Repr, Inhabited

/-- Binary encoding of `PowTwoMCInstance`: `k`, `b`, and `n` in unary, followed by framed edge
quadruples in binary. -/
@[expose]
def encPowTwoMCInstance : PowTwoMCInstance ↪ List Bool :=
  ⟨fun x ↦
      encPair encUnary
        (encPair encUnary
          (encPair encUnary
            (encList (encPair (encPair encNat encNat) (encPair encNat encNat)))))
        (x.k, (x.b, (x.n, x.edges))),
    fun x y h ↦ by
      have h' := (encPair encUnary
        (encPair encUnary
          (encPair encUnary
            (encList (encPair (encPair encNat encNat) (encPair encNat encNat)))))).injective h
      cases x; cases y; simp_all⟩

@[simp]
theorem encPowTwoMCInstance_apply (x : PowTwoMCInstance) :
    encPowTwoMCInstance x =
      encPair encUnary
        (encPair encUnary
          (encPair encUnary
            (encList (encPair (encPair encNat encNat) (encPair encNat encNat)))))
        (x.k, (x.b, (x.n, x.edges))) := rfl

private theorem computableInPolyTime_powTwoMCFields :
    ComputableInPolyTime
      (fun x : PowTwoMCInstance ↦ (x.k, (x.b, (x.n, x.edges))))
      encPowTwoMCInstance
      (encPair encUnary
        (encPair encUnary
          (encPair encUnary
            (encList (encPair (encPair encNat encNat) (encPair encNat encNat)))))) :=
  ComputableInPolyTime.id'.of_enc_eq fun _ ↦ rfl

/-- Projecting `PowTwoMCInstance.k` in unary is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_powTwoMC_k {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → PowTwoMCInstance} (hg : ComputableInPolyTime g encIn encPowTwoMCInstance) :
    ComputableInPolyTime (fun a ↦ (g a).k) encIn encUnary :=
  ((ComputableInPolyTime.fst _ _).comp computableInPolyTime_powTwoMCFields).comp hg

/-- Projecting `PowTwoMCInstance.b` in unary is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_powTwoMC_b {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → PowTwoMCInstance} (hg : ComputableInPolyTime g encIn encPowTwoMCInstance) :
    ComputableInPolyTime (fun a ↦ (g a).b) encIn encUnary :=
  ((ComputableInPolyTime.fst _ _).comp
    ((ComputableInPolyTime.snd _ _).comp computableInPolyTime_powTwoMCFields)).comp hg

/-- Projecting `PowTwoMCInstance.n` in unary is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_powTwoMC_n {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → PowTwoMCInstance} (hg : ComputableInPolyTime g encIn encPowTwoMCInstance) :
    ComputableInPolyTime (fun a ↦ (g a).n) encIn encUnary :=
  ((ComputableInPolyTime.fst _ _).comp
    ((ComputableInPolyTime.snd _ _).comp
      ((ComputableInPolyTime.snd _ _).comp computableInPolyTime_powTwoMCFields))).comp hg

/-- Projecting `PowTwoMCInstance.edges` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_powTwoMC_edges {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → PowTwoMCInstance} (hg : ComputableInPolyTime g encIn encPowTwoMCInstance) :
    ComputableInPolyTime (fun a ↦ (g a).edges) encIn
      (encList (encPair (encPair encNat encNat) (encPair encNat encNat))) :=
  ((ComputableInPolyTime.snd _ _).comp
    ((ComputableInPolyTime.snd _ _).comp
      ((ComputableInPolyTime.snd _ _).comp computableInPolyTime_powTwoMCFields))).comp hg

/-- Constructing a `PowTwoMCInstance` from polynomial-time fields is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_powTwoMC_mk {γ : Type} {encIn : γ ↪ List Bool}
    {fk fb fn : γ → ℕ} {fedges : γ → List ((ℕ × ℕ) × (ℕ × ℕ))}
    (hk : ComputableInPolyTime fk encIn encUnary)
    (hb : ComputableInPolyTime fb encIn encUnary)
    (hn : ComputableInPolyTime fn encIn encUnary)
    (he : ComputableInPolyTime fedges encIn
      (encList (encPair (encPair encNat encNat) (encPair encNat encNat)))) :
    ComputableInPolyTime (fun a ↦ PowTwoMCInstance.mk (fk a) (fb a) (fn a) (fedges a))
      encIn encPowTwoMCInstance :=
  (hk.prod (hb.prod (hn.prod he))).of_enc_eq fun _ ↦ rfl

/-- **Power-of-Two Equipartite Multicolored Clique** (`PowTwoMC`): valid instances have `1 ≤ k`,
`1 ≤ b`, `n = 2 ^ b`, and have one chosen vertex `sel i : Fin n` in each color class `i < k` such
that `((i, sel i), (j, sel j)) ∈ x.edges` for all `i < j`. -/
@[expose]
def PowTwoMC : Set PowTwoMCInstance :=
  {x | 1 ≤ x.k ∧ 1 ≤ x.b ∧ x.n = 2 ^ x.b ∧
    ∃ sel : Fin x.k → Fin x.n,
      ∀ i j : Fin x.k, i < j → ((i.1, (sel i).1), (j.1, (sel j).1)) ∈ x.edges}

/-! ### 2. Polynomial-Time FPT Reduction from `Clique` to `PowTwoMC` -/

private def powTwoExp (V : List ℕ) : ℕ :=
  V.length.size + 1

private theorem one_le_powTwoExp (V : List ℕ) : 1 ≤ powTwoExp V :=
  Nat.le_add_left 1 _

private theorem lt_two_pow_powTwoExp (V : List ℕ) : V.length < 2 ^ powTwoExp V :=
  (Nat.lt_size_self V.length).trans (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _))

private theorem two_pow_powTwoExp_le (V : List ℕ) : 2 ^ powTwoExp V ≤ 4 * V.length + 2 := by
  unfold powTwoExp
  rcases eq_or_ne V.length 0 with h0 | hne
  · simp [h0]
  · have hpos : 0 < V.length.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hne)
    have hle : 2 ^ (V.length.size - 1) ≤ V.length := by
      by_contra hlt
      push Not at hlt
      have := Nat.size_le.mpr hlt
      omega
    have hexp : V.length.size + 1 = (V.length.size - 1) + 2 := by omega
    rw [hexp, Nat.pow_add]
    linarith

/-- Maps a `CliqueInstance` `(G, m)` to `PowTwoMCInstance` by replicating `G.distinctVertices`
into `m` color classes of power-of-two size `2 ^ (|V|.size + 1) ≤ 4 |V| + 2`. -/
def cliqueToPowTwoMC (x : CliqueInstance) : PowTwoMCInstance :=
  let V := x.graph.distinctVertices
  let cap := min V.length x.m
  if cap = 0 then
    if x.m = 0 then ⟨1, 1, 2, []⟩ else ⟨0, 1, 2, []⟩
  else if cap < x.m then
    ⟨0, 1, 2, []⟩
  else
    let b := powTwoExp V
    let n := min (4 * V.length + 2) (2 ^ b)
    let edges :=
      (List.range cap).flatMap fun i ↦
        (List.range cap).flatMap fun j ↦
          if i < j then
            (List.range V.length).flatMap fun u ↦
              (List.range V.length).filterMap fun v ↦
                if x.graph.adjBool (V.getD u 0) (V.getD v 0) then
                  some ((i, u), (j, v))
                else none
          else []
    ⟨cap, b, n, edges⟩

private theorem cliqueToPowTwoMC_k_le (x : CliqueInstance) :
    (cliqueToPowTwoMC x).k ≤ x.m + 1 := by
  unfold cliqueToPowTwoMC
  dsimp only
  split_ifs with h0 hm0 hlt
  · dsimp only; omega
  · dsimp only; omega
  · dsimp only; omega
  · dsimp only
    have : min x.graph.distinctVertices.length x.m ≤ x.m := Nat.min_le_right _ _
    omega

private theorem cliqueToPowTwoMC_mem_iff (x : CliqueInstance) :
    cliqueToPowTwoMC x ∈ PowTwoMC ↔ x ∈ Clique := by
  rcases x with ⟨G, m⟩
  set V := G.distinctVertices
  set cap := min V.length m
  by_cases h0 : cap = 0
  · by_cases hm0 : m = 0
    · subst hm0
      have hyes : cliqueToPowTwoMC ⟨G, 0⟩ = ⟨1, 1, 2, []⟩ := by
        unfold cliqueToPowTwoMC; simp
      rw [hyes]
      refine ⟨fun _ ↦ ?_, fun _ ↦ ⟨le_rfl, le_rfl, rfl, fun _ ↦ ⟨0, by decide⟩, fun i j hij ↦ ?_⟩⟩
      · rw [mem_Clique_iff_mk]
        exact ⟨∅, fun _ h ↦ (Finset.notMem_empty _ h).elim, by simp⟩
      · rcases i with ⟨iv, hi⟩
        rcases j with ⟨jv, hj⟩
        dsimp only at hi hj
        simp only [Fin.mk_lt_mk] at hij
        omega
    · have hV0 : G.distinctVertices.length = 0 := by
        have : min G.distinctVertices.length m = 0 := h0
        omega
      have hno : cliqueToPowTwoMC ⟨G, m⟩ = ⟨0, 1, 2, []⟩ := by
        unfold cliqueToPowTwoMC; dsimp only
        rw [ite_eq_left h0, ite_eq_right hm0]
      rw [hno]
      refine ⟨fun h ↦ by simp [PowTwoMC] at h, fun hcl ↦ ?_⟩
      have hle := Graph.le_card_of_mem_Clique hcl
      rw [← Graph.length_distinctVertices] at hle
      omega
  · by_cases hlt : cap < m
    · have hno : cliqueToPowTwoMC ⟨G, m⟩ = ⟨0, 1, 2, []⟩ := by
        unfold cliqueToPowTwoMC; dsimp only
        rw [ite_eq_right h0, ite_eq_left hlt]
      rw [hno]
      refine ⟨fun h ↦ by simp [PowTwoMC] at h, fun hcl ↦ ?_⟩
      have hle := Graph.le_card_of_mem_Clique hcl
      rw [← Graph.length_distinctVertices] at hle
      have : cap = m := Nat.min_eq_right hle
      omega
    · have hcap_eq : cap = m := by omega
      have hm_pos : 1 ≤ m := by omega
      have hm_le : m ≤ V.length := by omega
      have hdef : cliqueToPowTwoMC ⟨G, m⟩ =
          ⟨m, powTwoExp V, min (4 * V.length + 2) (2 ^ powTwoExp V),
            (List.range m).flatMap fun i ↦
              (List.range m).flatMap fun j ↦
                if i < j then
                  (List.range V.length).flatMap fun u ↦
                    (List.range V.length).filterMap fun v ↦
                      if G.adjBool (V.getD u 0) (V.getD v 0) then
                        some ((i, u), (j, v))
                      else none
                else []⟩ := by
        unfold cliqueToPowTwoMC; dsimp only
        rw [ite_eq_right h0, ite_eq_right hlt]
        simp only [V, cap, hcap_eq]
      rw [hdef]
      have hn_eq : min (4 * V.length + 2) (2 ^ powTwoExp V) = 2 ^ powTwoExp V :=
        Nat.min_eq_right (two_pow_powTwoExp_le V)
      simp only [PowTwoMC, Set.mem_ofPred_eq, hn_eq, hm_pos, one_le_powTwoExp V, true_and]
      have hedge_iff {i j u v : ℕ} (hi : i < m) (hj : j < m) (hij : i < j) :
          ((i, u), (j, v)) ∈
            ((List.range m).flatMap fun i' ↦
              (List.range m).flatMap fun j' ↦
                if i' < j' then
                  (List.range V.length).flatMap fun u' ↦
                    (List.range V.length).filterMap fun v' ↦
                      if G.adjBool (V.getD u' 0) (V.getD v' 0) then
                        some ((i', u'), (j', v'))
                      else none
                else []) ↔
            u < V.length ∧ v < V.length ∧ G.toSimpleGraph.Adj (V.getD u 0) (V.getD v 0) := by
        simp only [List.mem_flatMap, List.mem_range]
        constructor
        · rintro ⟨i', _, j', _, hrest⟩
          by_cases hij' : i' < j'
          · simp only [hij', ↓reduceIte, List.mem_flatMap, List.mem_range,
              List.mem_filterMap] at hrest
            obtain ⟨u', hu', v', hv', hopt⟩ := hrest
            split_ifs at hopt with hadj
            simp only [Option.some.injEq, Prod.mk.injEq] at hopt
            rcases hopt with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
            exact ⟨hu', hv', (G.adjBool_eq_true_iff _ _).mp hadj⟩
          · simp [hij'] at hrest
        · rintro ⟨hu, hv, hadj⟩
          have hadjB : G.adjBool (V.getD u 0) (V.getD v 0) = true :=
            (G.adjBool_eq_true_iff _ _).mpr hadj
          refine ⟨i, hi, j, hj, ?_⟩
          simp only [hij, ↓reduceIte, List.mem_flatMap, List.mem_range, List.mem_filterMap]
          exact ⟨u, hu, v, hv, by rw [ite_eq_left hadjB]⟩
      by_cases hm1 : m = 1
      · subst hm1
        refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
        · rw [mem_Clique_iff_mk]
          have hVne : 0 < V.length := hm_le
          refine ⟨{V[0]}, fun w hw ↦ ?_, ?_⟩
          · rw [Finset.mem_singleton.mp hw]
            exact Graph.mem_distinctVertices.mp (List.getElem_mem hVne)
          · simp [SimpleGraph.isNClique_iff]
        · exact ⟨fun _ ↦ ⟨0, (by omega : 0 < V.length).trans (lt_two_pow_powTwoExp V)⟩,
            fun i j hij ↦ absurd (Fin.lt_def.mp hij) (by have := i.2; have := j.2; omega)⟩
      · have hm2 : 2 ≤ m := by omega
        constructor
        · rintro ⟨sel, hsel⟩
          have hu_lt : ∀ i : Fin m, (sel i).1 < V.length := by
            intro i
            by_cases hi0 : i.1 = 0
            · have h01 : (⟨0, by omega⟩ : Fin m) < ⟨1, by omega⟩ := by simp [Fin.lt_def]
              have he := (hedge_iff (by omega) (by omega) h01).mp (hsel ⟨0, by omega⟩ ⟨1,
                by omega⟩ h01)
              have hi_eq : i = ⟨0, by omega⟩ := Fin.ext hi0
              simpa [hi_eq] using he.1
            · have h0i : (⟨0, by omega⟩ : Fin m) < i := by
                simp [Fin.lt_def]; omega
              have he := (hedge_iff (by omega) i.2 h0i).mp (hsel ⟨0, by omega⟩ i h0i)
              exact he.2.1
          let f : Fin m → ℕ := fun i ↦ V.getD (sel i).1 0
          have hfinj : Function.Injective f := by
            intro i j hfj
            rcases lt_trichotomy i j with hij | rfl | hji
            · have he := (hedge_iff i.2 j.2 hij).mp (hsel i j hij)
              exact (he.2.2.ne hfj).elim
            · rfl
            · have he := (hedge_iff j.2 i.2 hji).mp (hsel j i hji)
              exact (he.2.2.ne hfj.symm).elim
          rw [mem_Clique_iff_mk]
          refine ⟨Finset.univ.image f, ?_, ?_⟩
          · intro w hw
            obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
            have hlt_i := hu_lt i
            dsimp only [f]
            rw [List.getD_eq_getElem V 0 hlt_i]
            exact Graph.mem_distinctVertices.mp (List.getElem_mem hlt_i)
          · rw [SimpleGraph.isNClique_iff, Finset.card_image_of_injective _ hfinj, Finset.card_fin]
            refine ⟨?_, rfl⟩
            intro a ha b hb hab
            rw [Finset.mem_coe, Finset.mem_image] at ha hb
            obtain ⟨i, _, rfl⟩ := ha
            obtain ⟨j, _, rfl⟩ := hb
            have hij_ne : i ≠ j := fun h ↦ hab (congrArg f h)
            rcases lt_or_gt_of_ne hij_ne with hij | hji
            · exact ((hedge_iff i.2 j.2 hij).mp (hsel i j hij)).2.2
            · exact (((hedge_iff j.2 i.2 hji).mp (hsel j i hji)).2.2).symm
        · intro hcl
          rw [mem_Clique_iff_mk] at hcl
          obtain ⟨S, hSV, hScl, hScard⟩ := hcl
          -- Map `S` injectively to indices in `V = G.distinctVertices` and enumerate them via
          -- `orderEmbOfFin`.
          let idxSet : Finset ℕ := S.image (fun w ↦ V.idxOf w)
          have hidx_inj : Set.InjOn (fun w ↦ V.idxOf w) S := by
            intro a ha b hb heq
            have haV : a ∈ V := Graph.mem_distinctVertices.mpr (hSV a ha)
            have hbV : b ∈ V := Graph.mem_distinctVertices.mpr (hSV b hb)
            have hlt_a := List.idxOf_lt_length_iff.mpr haV
            have hlt_b := List.idxOf_lt_length_iff.mpr hbV
            have hget := congrArg (fun k ↦ V.getD k 0) heq
            rw [List.getD_eq_getElem V 0 hlt_a, List.getD_eq_getElem V 0 hlt_b,
              List.getElem_idxOf hlt_a, List.getElem_idxOf hlt_b] at hget
            exact hget
          have hidx_card : idxSet.card = m :=
            (Finset.card_image_of_injOn hidx_inj).trans hScard
          let emb := idxSet.orderEmbOfFin hidx_card
          have hemb_lt : ∀ i : Fin m, emb i < V.length := by
            intro i
            have hmem := idxSet.orderEmbOfFin_mem hidx_card i
            obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp hmem
            rw [← hweq]
            exact List.idxOf_lt_length_iff.mpr (Graph.mem_distinctVertices.mpr (hSV w hw))
          refine ⟨fun i ↦ ⟨emb i, (hemb_lt i).trans (lt_two_pow_powTwoExp V)⟩, fun i j hij ↦ ?_⟩
          rw [hedge_iff i.2 j.2 hij]
          refine ⟨hemb_lt i, hemb_lt j, ?_⟩
          have hmem_i := idxSet.orderEmbOfFin_mem hidx_card i
          have hmem_j := idxSet.orderEmbOfFin_mem hidx_card j
          obtain ⟨wi, hwi, hwi_eq⟩ := Finset.mem_image.mp hmem_i
          obtain ⟨wj, hwj, hwj_eq⟩ := Finset.mem_image.mp hmem_j
          have hget_i : V.getD (emb i) 0 = wi := by
            rw [← hwi_eq, List.getD_eq_getElem V 0
              (List.idxOf_lt_length_iff.mpr (Graph.mem_distinctVertices.mpr (hSV wi hwi))),
              List.getElem_idxOf]
          have hget_j : V.getD (emb j) 0 = wj := by
            rw [← hwj_eq, List.getD_eq_getElem V 0
              (List.idxOf_lt_length_iff.mpr (Graph.mem_distinctVertices.mpr (hSV wj hwj))),
              List.getElem_idxOf]
          rw [hget_i, hget_j]
          have hne_w : wi ≠ wj := fun h ↦ by
            have : emb i = emb j := hwi_eq.symm.trans ((congrArg V.idxOf h).trans hwj_eq)
            exact hij.ne (emb.injective this)
          exact hScl hwi hwj hne_w

open ComputableInPolyTime in
/-- `cliqueToPowTwoMC` is computable in polynomial time. -/
theorem computableInPolyTime_cliqueToPowTwoMC :
    ComputableInPolyTime cliqueToPowTwoMC encCliqueInstance encPowTwoMCInstance := by
  have hV : ComputableInPolyTime (fun x : CliqueInstance ↦ x.graph.distinctVertices)
      encCliqueInstance (encList encNat) := by fun_prop
  have hVlen : ComputableInPolyTime (fun x : CliqueInstance ↦ x.graph.distinctVertices.length)
      encCliqueInstance encUnary := (length_list encNat).comp hV
  have hcap : ComputableInPolyTime
      (fun x : CliqueInstance ↦ min x.graph.distinctVertices.length x.m)
      encCliqueInstance encUnary := binary_min_unary' hVlen (by fun_prop)
  have hb : ComputableInPolyTime (fun x : CliqueInstance ↦ powTwoExp x.graph.distinctVertices)
      encCliqueInstance encUnary := by
    unfold powTwoExp
    exact unary_add' (binary_size.comp (unary_to_binary.comp hVlen)) (const 1)
  have hn : ComputableInPolyTime
      (fun x : CliqueInstance ↦
        min (4 * x.graph.distinctVertices.length + 2)
          (2 ^ powTwoExp x.graph.distinctVertices))
      encCliqueInstance encUnary :=
    binary_min_unary' (unary_add' (unary_mul' (const 4) hVlen) (const 2))
      (binary_two_pow.comp hb)
  -- Express `filterMap` via `filter` + `map` so standard list `fun_prop` rules apply directly.
  have hedges : ComputableInPolyTime
      (fun x : CliqueInstance ↦
        let V := x.graph.distinctVertices
        let cap := min V.length x.m
        (List.range cap).flatMap fun i ↦
          (List.range cap).flatMap fun j ↦
            if decide (i < j) then
              (List.range V.length).flatMap fun u ↦
                ((List.range V.length).filter fun v ↦
                  x.graph.adjBool (V.getD u 0) (V.getD v 0)).map fun v ↦
                    ((i, u), (j, v))
            else [])
      encCliqueInstance
      (encList (encPair (encPair encNat encNat) (encPair encNat encNat))) := by
    apply flatMapWithInput (range.comp hcap)
    apply flatMapWithInput (range.comp (hcap.comp (fst _ _)))
    apply ComputableInPolyTime.ite (by fun_prop)
    · apply flatMapWithInput (range.comp (hVlen.comp ((fst _ _).comp (fst _ _))))
      have hinner_filter : ComputableInPolyTime
          (fun p : ((CliqueInstance × ℕ) × ℕ) × ℕ ↦
            (List.range p.1.1.1.graph.distinctVertices.length).filter fun v ↦
              p.1.1.1.graph.adjBool (p.1.1.1.graph.distinctVertices.getD p.2 0)
                (p.1.1.1.graph.distinctVertices.getD v 0))
          (encPair (encPair (encPair encCliqueInstance encUnary) encUnary) encUnary)
          (encList encUnary) := by
        apply filterWithInput (range.comp (hVlen.comp ((fst _ _).comp ((fst _ _).comp (fst _ _)))))
        apply Graph.computableInPolyTime_adjBool_comp
        · fun_prop
        · exact listGetDWithInput (by fun_prop) (by fun_prop) 0
        · exact listGetDWithInput (by fun_prop) (by fun_prop) 0
      apply mapWithInput hinner_filter
      have hi_bin : ComputableInPolyTime
          (fun q : (((CliqueInstance × ℕ) × ℕ) × ℕ) × ℕ ↦ q.1.1.1.2)
          (encPair (encPair (encPair (encPair encCliqueInstance encUnary) encUnary)
            encUnary) encUnary) encNat :=
        unary_to_binary.comp (by fun_prop)
      have hj_bin : ComputableInPolyTime
          (fun q : (((CliqueInstance × ℕ) × ℕ) × ℕ) × ℕ ↦ q.1.1.2)
          (encPair (encPair (encPair (encPair encCliqueInstance encUnary) encUnary)
            encUnary) encUnary) encNat :=
        unary_to_binary.comp (by fun_prop)
      have hu_bin : ComputableInPolyTime
          (fun q : (((CliqueInstance × ℕ) × ℕ) × ℕ) × ℕ ↦ q.1.2)
          (encPair (encPair (encPair (encPair encCliqueInstance encUnary) encUnary)
            encUnary) encUnary) encNat :=
        unary_to_binary.comp (by fun_prop)
      have hv_bin : ComputableInPolyTime
          (fun q : (((CliqueInstance × ℕ) × ℕ) × ℕ) × ℕ ↦ q.2)
          (encPair (encPair (encPair (encPair encCliqueInstance encUnary) encUnary)
            encUnary) encUnary) encNat :=
        unary_to_binary.comp (by fun_prop)
      exact (hi_bin.prod hu_bin).prod (hj_bin.prod hv_bin)
    · exact const []
  have hmain : ComputableInPolyTime
      (fun x : CliqueInstance ↦
        let V := x.graph.distinctVertices
        let cap := min V.length x.m
        if decide (cap = 0) then
          if decide (x.m = 0) then PowTwoMCInstance.mk 1 1 2 []
          else PowTwoMCInstance.mk 0 1 2 []
        else if decide (cap < x.m) then
          PowTwoMCInstance.mk 0 1 2 []
        else
          PowTwoMCInstance.mk cap (powTwoExp V)
            (min (4 * V.length + 2) (2 ^ powTwoExp V))
            ((List.range cap).flatMap fun i ↦
              (List.range cap).flatMap fun j ↦
                if decide (i < j) then
                  (List.range V.length).flatMap fun u ↦
                    ((List.range V.length).filter fun v ↦
                      x.graph.adjBool (V.getD u 0) (V.getD v 0)).map fun v ↦
                        ((i, u), (j, v))
                else []))
      encCliqueInstance encPowTwoMCInstance := by
    have hcond0 : ComputableInPolyTime
        (fun x : CliqueInstance ↦ decide (min x.graph.distinctVertices.length x.m = 0))
        encCliqueInstance encBool :=
      (unary_beq hcap (const 0)).of_enc_eq fun _ ↦ by simp [beq_eq_decide]
    have hcondm0 : ComputableInPolyTime
        (fun x : CliqueInstance ↦ decide (x.m = 0))
        encCliqueInstance encBool := by fun_prop
    have hcondlt : ComputableInPolyTime
        (fun x : CliqueInstance ↦ decide (min x.graph.distinctVertices.length x.m < x.m))
        encCliqueInstance encBool :=
      binary_lt' (unary_to_binary.comp hcap) (by fun_prop)
    exact hcond0.ite
      (hcondm0.ite
        (computableInPolyTime_powTwoMC_mk (const 1) (const 1) (const 2) (const []))
        (computableInPolyTime_powTwoMC_mk (const 0) (const 1) (const 2) (const [])))
      (hcondlt.ite
        (computableInPolyTime_powTwoMC_mk (const 0) (const 1) (const 2) (const []))
        (computableInPolyTime_powTwoMC_mk hcap hb hn hedges))
  refine hmain.of_enc_eq fun x ↦ congrArg encPowTwoMCInstance ?_
  have hfm : ∀ (l : List ℕ) (p : ℕ → Bool) (g : ℕ → (ℕ × ℕ) × (ℕ × ℕ)),
      (l.filter p).map g = l.filterMap (fun v ↦ if p v then some (g v) else none) := by
    intro l p g
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.filter_cons, List.filterMap_cons]
      cases p a <;> simp [ih]
  simp only [cliqueToPowTwoMC, decide_eq_true_eq, hfm]

/-- `Cslib.Complexity.Clique` fpt-reduces to `PowTwoMC` in polynomial time. -/
theorem fptReducible_clique_powTwoMC :
    FPTReducible encCliqueInstance encPowTwoMCInstance (·.m) (·.k) Clique PowTwoMC :=
  FPTReducible.of_computableInPolyTime computableInPolyTime_cliqueToPowTwoMC
    (h := fun m ↦ m + 1) cliqueToPowTwoMC_k_le (fun x ↦ (cliqueToPowTwoMC_mem_iff x).symm)

/-- **`PowTwoMC` is `W[1]`-hard** under standard Lean axioms. -/
theorem powTwoMC_wHard : WHard 1 encPowTwoMCInstance (·.k) PowTwoMC :=
  Clique_wHard.trans fptReducible_cliqueToPowTwoMC_aux
where
  fptReducible_cliqueToPowTwoMC_aux := fptReducible_clique_powTwoMC

/-! ### 3. Polynomial-Time FPT Reduction from `PowTwoMC` to `Clique` -/

/-- Maps a `PowTwoMCInstance` back to `CliqueInstance` on vertex codes `Nat.pair i u`
(`i < x.k`, `u < x.n`). -/
def powTwoMCToClique (x : PowTwoMCInstance) : CliqueInstance :=
  if 1 ≤ x.k ∧ 1 ≤ x.b ∧ x.n = 2 ^ x.b then
    let verts := (List.range x.k).flatMap fun i ↦ (List.range x.n).map fun u ↦ Nat.pair i u
    let edges :=
      (List.range x.k).flatMap fun i ↦
        (List.range x.k).flatMap fun j ↦
          if i < j then
            (List.range x.n).flatMap fun u ↦
              ((List.range x.n).filter fun v ↦
                x.edges.any fun e ↦ decide (e = ((i, u), (j, v)))).map fun v ↦
                  (Nat.pair i u, Nat.pair j v)
          else []
    ⟨⟨verts, edges⟩, x.k⟩
  else
    ⟨⟨[], []⟩, 1⟩

private theorem powTwoMCToClique_mem_iff (x : PowTwoMCInstance) :
    powTwoMCToClique x ∈ Clique ↔ x ∈ PowTwoMC := by
  by_cases hvalid : 1 ≤ x.k ∧ 1 ≤ x.b ∧ x.n = 2 ^ x.b
  · obtain ⟨hk1, hb1, hn_eq⟩ := hvalid
    have hdef : powTwoMCToClique x =
        ⟨⟨(List.range x.k).flatMap fun i ↦ (List.range x.n).map fun u ↦ Nat.pair i u,
          (List.range x.k).flatMap fun i ↦
            (List.range x.k).flatMap fun j ↦
              if i < j then
                (List.range x.n).flatMap fun u ↦
                  ((List.range x.n).filter fun v ↦
                    x.edges.any fun e ↦ decide (e = ((i, u), (j, v)))).map fun v ↦
                      (Nat.pair i u, Nat.pair j v)
              else []⟩, x.k⟩ := by
      unfold powTwoMCToClique
      rw [ite_eq_left ⟨hk1, hb1, hn_eq⟩]
    rw [hdef, mem_Clique_iff_mk]
    simp only [PowTwoMC, Set.mem_ofPred_eq, hk1, hb1, true_and]
    set G : Graph :=
      ⟨(List.range x.k).flatMap fun i ↦ (List.range x.n).map fun u ↦ Nat.pair i u,
        (List.range x.k).flatMap fun i ↦
          (List.range x.k).flatMap fun j ↦
            if i < j then
              (List.range x.n).flatMap fun u ↦
                ((List.range x.n).filter fun v ↦
                  x.edges.any fun e ↦ decide (e = ((i, u), (j, v)))).map fun v ↦
                    (Nat.pair i u, Nat.pair j v)
            else []⟩
    have hmem_verts {w : ℕ} :
        w ∈ G.vertices ↔ (Nat.unpair w).1 < x.k ∧ (Nat.unpair w).2 < x.n := by
      simp only [G, List.mem_flatMap, List.mem_range, List.mem_map]
      refine ⟨fun ⟨i, hi, u, hu, hiu⟩ ↦ by rw [← hiu, Nat.unpair_pair]; exact ⟨hi, hu⟩,
        fun ⟨hi, hu⟩ ↦ ⟨(Nat.unpair w).1, hi, (Nat.unpair w).2, hu, Nat.pair_unpair w⟩⟩
    have hedge_G {p q : ℕ} :
        (p, q) ∈ G.edges ↔
          (Nat.unpair p).1 < (Nat.unpair q).1 ∧ (Nat.unpair q).1 < x.k ∧
          (Nat.unpair p).2 < x.n ∧ (Nat.unpair q).2 < x.n ∧
          (Nat.unpair p, Nat.unpair q) ∈ x.edges := by
      simp only [G, List.mem_flatMap, List.mem_range]
      constructor
      · rintro ⟨i, _, j, hj, hrest⟩
        by_cases hij : i < j
        · simp only [hij, ↓reduceIte, List.mem_flatMap, List.mem_range, List.mem_map,
            List.mem_filter, List.any_eq_true, decide_eq_true_eq] at hrest
          obtain ⟨u, hu, v, ⟨hv, e, he, rfl⟩, hpq⟩ := hrest
          simp only [Prod.mk.injEq] at hpq
          rcases hpq with ⟨rfl, rfl⟩
          simp only [Nat.unpair_pair]
          exact ⟨hij, hj, hu, hv, he⟩
        · simp [hij] at hrest
      · rintro ⟨hij, hj, hu, hv, he⟩
        refine ⟨(Nat.unpair p).1, hij.trans hj, (Nat.unpair q).1, hj, ?_⟩
        simp only [hij, ↓reduceIte, List.mem_flatMap, List.mem_range, List.mem_map,
          List.mem_filter, List.any_eq_true, decide_eq_true_eq]
        exact ⟨(Nat.unpair p).2, hu, (Nat.unpair q).2,
          ⟨hv, _, he, rfl⟩, Prod.ext (Nat.pair_unpair p) (Nat.pair_unpair q)⟩
    constructor
    · rintro ⟨S, hSV, hScl, hScard⟩
      refine ⟨hn_eq, ?_⟩
      -- Colors of distinct vertices in `S` are pairwise distinct, hence cover `Fin x.k`.
      have hcol_inj : Set.InjOn (fun w ↦ (Nat.unpair w).1) S := by
        intro a ha b hb heq
        by_contra hab
        have hadj := hScl ha hb hab
        rw [Graph.toSimpleGraph_adj] at hadj
        dsimp only at heq
        rcases hadj.2 with h1 | h2
        · have hlt := (hedge_G.mp h1).1; rw [heq] at hlt; exact lt_irrefl _ hlt
        · have hlt := (hedge_G.mp h2).1; rw [heq] at hlt; exact lt_irrefl _ hlt
      have hcol_sub : S.image (fun w ↦ (Nat.unpair w).1) ⊆ Finset.range x.k := by
        intro c hc
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
        exact Finset.mem_range.mpr (hmem_verts.mp (hSV w hw)).1
      have hcol_eq : S.image (fun w ↦ (Nat.unpair w).1) = Finset.range x.k :=
        Finset.eq_of_subset_of_card_le hcol_sub
          (by rw [Finset.card_range, Finset.card_image_of_injOn hcol_inj, hScard])
      have hex_col : ∀ i : Fin x.k, ∃ w ∈ S, (Nat.unpair w).1 = i.1 := by
        intro i
        have hi : i.1 ∈ S.image (fun w ↦ (Nat.unpair w).1) := by
          rw [hcol_eq]; exact Finset.mem_range.mpr i.2
        exact Finset.mem_image.mp hi
      choose w hwS hwcol using hex_col
      refine ⟨fun i ↦ ⟨(Nat.unpair (w i)).2, (hmem_verts.mp (hSV (w i) (hwS i))).2⟩,
        fun i j hij ↦ ?_⟩
      have hne_w : w i ≠ w j := fun h ↦ hij.ne (Fin.ext ((hwcol i).symm.trans (h ▸ hwcol j)))
      have hadj := hScl (hwS i) (hwS j) hne_w
      rw [Graph.toSimpleGraph_adj] at hadj
      rcases hadj.2 with h1 | h2
      · have he := (hedge_G.mp h1).2.2.2.2
        rwa [← Prod.eta (Nat.unpair (w i)), ← Prod.eta (Nat.unpair (w j)),
          hwcol i, hwcol j] at he
      · have hlt_ji := (hedge_G.mp h2).1
        rw [hwcol j, hwcol i] at hlt_ji
        exact (lt_asymm hij hlt_ji).elim
    · rintro ⟨_, sel, hsel⟩
      let f : Fin x.k → ℕ := fun i ↦ Nat.pair i.1 (sel i).1
      have hfinj : Function.Injective f := fun i j h ↦
        Fin.ext (Nat.pair_eq_pair.mp h).1
      refine ⟨Finset.univ.image f, ?_, ?_⟩
      · intro w hw
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
        rw [hmem_verts]
        simp [f, i.2, (sel i).2]
      · rw [SimpleGraph.isNClique_iff, Finset.card_image_of_injective _ hfinj, Finset.card_fin]
        refine ⟨?_, rfl⟩
        intro a ha b hb hab
        rw [Finset.mem_coe, Finset.mem_image] at ha hb
        obtain ⟨i, _, rfl⟩ := ha
        obtain ⟨j, _, rfl⟩ := hb
        have hij_ne : i ≠ j := fun h ↦ hab (congrArg f h)
        rw [Graph.toSimpleGraph_adj]
        refine ⟨hab, ?_⟩
        rcases lt_or_gt_of_ne hij_ne with hij | hji
        · left
          rw [hedge_G]
          simp only [f, Nat.unpair_pair]
          exact ⟨hij, j.2, (sel i).2, (sel j).2, hsel i j hij⟩
        · right
          rw [hedge_G]
          simp only [f, Nat.unpair_pair]
          exact ⟨hji, i.2, (sel j).2, (sel i).2, hsel j i hji⟩
  · have hdef : powTwoMCToClique x = ⟨⟨[], []⟩, 1⟩ := by
      unfold powTwoMCToClique
      rw [ite_eq_right hvalid]
    rw [hdef, mem_Clique_iff_mk]
    refine ⟨fun ⟨S, hSV, _, hcard⟩ ↦ ?_, fun h ↦ (hvalid ⟨h.1, h.2.1, h.2.2.1⟩).elim⟩
    have hempty : S = ∅ := Finset.eq_empty_of_forall_notMem fun v hv ↦ by simpa using hSV v hv
    simp [hempty] at hcard

open ComputableInPolyTime in
/-- `powTwoMCToClique` is computable in polynomial time. -/
theorem computableInPolyTime_powTwoMCToClique :
    ComputableInPolyTime powTwoMCToClique encPowTwoMCInstance encCliqueInstance := by
  have hk : ComputableInPolyTime (fun x : PowTwoMCInstance ↦ x.k)
      encPowTwoMCInstance encUnary := computableInPolyTime_powTwoMC_k id'
  have hb : ComputableInPolyTime (fun x : PowTwoMCInstance ↦ x.b)
      encPowTwoMCInstance encUnary := computableInPolyTime_powTwoMC_b id'
  have hn : ComputableInPolyTime (fun x : PowTwoMCInstance ↦ x.n)
      encPowTwoMCInstance encUnary := computableInPolyTime_powTwoMC_n id'
  have he : ComputableInPolyTime (fun x : PowTwoMCInstance ↦ x.edges)
      encPowTwoMCInstance
      (encList (encPair (encPair encNat encNat) (encPair encNat encNat))) :=
    computableInPolyTime_powTwoMC_edges id'
  have hcond : ComputableInPolyTime
      (fun x : PowTwoMCInstance ↦ decide (1 ≤ x.k) && decide (1 ≤ x.b) && decide (x.n = 2 ^ x.b))
      encPowTwoMCInstance encBool :=
    bool_and' (bool_and' (by fun_prop) (by fun_prop))
      (((unary_to_binary.comp hn).beq (binary_two_pow.comp hb)).of_enc_eq
        fun _ ↦ by simp [beq_eq_decide])
  have hverts : ComputableInPolyTime
      (fun x : PowTwoMCInstance ↦
        (List.range x.k).flatMap fun i ↦ (List.range x.n).map fun u ↦ Nat.pair i u)
      encPowTwoMCInstance (encList encNat) := by
    apply flatMapWithInput (range.comp hk)
    apply mapWithInput (range.comp (hn.comp (fst _ _)))
    exact unary_to_binary.comp (unary_pair.comp ((snd _ _).comp (fst _ _) |>.prod (snd _ _)))
  have hedges : ComputableInPolyTime
      (fun x : PowTwoMCInstance ↦
        (List.range x.k).flatMap fun i ↦
          (List.range x.k).flatMap fun j ↦
            if decide (i < j) then
              (List.range x.n).flatMap fun u ↦
                ((List.range x.n).filter fun v ↦
                  x.edges.any fun e ↦ decide (e = ((i, u), (j, v)))).map fun v ↦
                    (Nat.pair i u, Nat.pair j v)
            else [])
      encPowTwoMCInstance (encList (encPair encNat encNat)) := by
    apply flatMapWithInput (range.comp hk)
    apply flatMapWithInput (range.comp (hk.comp (fst _ _)))
    apply ComputableInPolyTime.ite (by fun_prop)
    · apply flatMapWithInput (range.comp (hn.comp ((fst _ _).comp (fst _ _))))
      have hflt : ComputableInPolyTime
          (fun p : ((PowTwoMCInstance × ℕ) × ℕ) × ℕ ↦
            (List.range p.1.1.1.n).filter fun v ↦
              p.1.1.1.edges.any fun e ↦ decide (e = ((p.1.1.2, p.2), (p.1.2, v))))
          (encPair (encPair (encPair encPowTwoMCInstance encUnary) encUnary) encUnary)
          (encList encUnary) := by
        apply filterWithInput (range.comp (hn.comp ((fst _ _).comp ((fst _ _).comp (fst _ _)))))
        apply anyWithInput (he.comp ((fst _ _).comp ((fst _ _).comp ((fst _ _).comp (fst _ _)))))
        have hi_b : ComputableInPolyTime
            (fun q : ((((PowTwoMCInstance × ℕ) × ℕ) × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) ↦
              q.1.1.1.1.2)
            (encPair
              (encPair (encPair (encPair (encPair encPowTwoMCInstance encUnary) encUnary)
                encUnary) encUnary)
              (encPair (encPair encNat encNat) (encPair encNat encNat))) encNat :=
          unary_to_binary.comp (by fun_prop)
        have hj_b : ComputableInPolyTime
            (fun q : ((((PowTwoMCInstance × ℕ) × ℕ) × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) ↦
              q.1.1.1.2)
            (encPair
              (encPair (encPair (encPair (encPair encPowTwoMCInstance encUnary) encUnary)
                encUnary) encUnary)
              (encPair (encPair encNat encNat) (encPair encNat encNat))) encNat :=
          unary_to_binary.comp (by fun_prop)
        have hu_b : ComputableInPolyTime
            (fun q : ((((PowTwoMCInstance × ℕ) × ℕ) × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) ↦
              q.1.1.2)
            (encPair
              (encPair (encPair (encPair (encPair encPowTwoMCInstance encUnary) encUnary)
                encUnary) encUnary)
              (encPair (encPair encNat encNat) (encPair encNat encNat))) encNat :=
          unary_to_binary.comp (by fun_prop)
        have hv_b : ComputableInPolyTime
            (fun q : ((((PowTwoMCInstance × ℕ) × ℕ) × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) ↦
              q.1.2)
            (encPair
              (encPair (encPair (encPair (encPair encPowTwoMCInstance encUnary) encUnary)
                encUnary) encUnary)
              (encPair (encPair encNat encNat) (encPair encNat encNat))) encNat :=
          unary_to_binary.comp (by fun_prop)
        exact decide_eq' (snd _ _) ((hi_b.prod hu_b).prod (hj_b.prod hv_b))
      apply mapWithInput hflt
      have hp1 : ComputableInPolyTime
          (fun q : (((PowTwoMCInstance × ℕ) × ℕ) × ℕ) × ℕ ↦ Nat.pair q.1.1.1.2 q.1.2)
          (encPair (encPair (encPair (encPair encPowTwoMCInstance encUnary) encUnary)
            encUnary) encUnary) encNat :=
        unary_to_binary.comp (unary_pair.comp
          ((by fun_prop : ComputableInPolyTime _ _ encUnary).prod
          (by fun_prop : ComputableInPolyTime _ _ encUnary)))
      have hp2 : ComputableInPolyTime
          (fun q : (((PowTwoMCInstance × ℕ) × ℕ) × ℕ) × ℕ ↦ Nat.pair q.1.1.2 q.2)
          (encPair (encPair (encPair (encPair encPowTwoMCInstance encUnary) encUnary)
            encUnary) encUnary) encNat :=
        unary_to_binary.comp (unary_pair.comp
          ((by fun_prop : ComputableInPolyTime _ _ encUnary).prod
          (by fun_prop : ComputableInPolyTime _ _ encUnary)))
      exact hp1.prod hp2
    · exact const []
  have hmain : ComputableInPolyTime
      (fun x : PowTwoMCInstance ↦
        if decide (1 ≤ x.k) && decide (1 ≤ x.b) && decide (x.n = 2 ^ x.b) then
          CliqueInstance.mk
            (Graph.mk
              ((List.range x.k).flatMap fun i ↦ (List.range x.n).map fun u ↦ Nat.pair i u)
              ((List.range x.k).flatMap fun i ↦
                (List.range x.k).flatMap fun j ↦
                  if decide (i < j) then
                    (List.range x.n).flatMap fun u ↦
                      ((List.range x.n).filter fun v ↦
                        x.edges.any fun e ↦ decide (e = ((i, u), (j, v)))).map fun v ↦
                          (Nat.pair i u, Nat.pair j v)
                  else []))
            x.k
        else
          CliqueInstance.mk (Graph.mk [] []) 1)
      encPowTwoMCInstance encCliqueInstance :=
    hcond.ite
      (encCliqueInstance_mk_polyTime (encGraph_mk_polyTime hverts hedges)
        (unary_to_binary.comp hk))
      (const (⟨⟨[], []⟩, 1⟩ : CliqueInstance))
  refine hmain.of_enc_eq fun x ↦ congrArg encCliqueInstance ?_
  by_cases hvalid : 1 ≤ x.k ∧ 1 ≤ x.b ∧ x.n = 2 ^ x.b
  · obtain ⟨h1, h2, h3⟩ := hvalid
    simp [powTwoMCToClique, h1, h2, h3]
  · have hfalse : (decide (1 ≤ x.k) && decide (1 ≤ x.b) && decide (x.n = 2 ^ x.b)) = false := by
      rw [Bool.eq_false_iff]
      intro ht
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
      exact hvalid ⟨ht.1.1, ht.1.2, ht.2⟩
    simp [powTwoMCToClique, hvalid, hfalse]

/-- `PowTwoMC` fpt-reduces to `Cslib.Complexity.Clique` in polynomial time. -/
theorem fptReducible_powTwoMC_clique :
    FPTReducible encPowTwoMCInstance encCliqueInstance (·.k) (·.m) PowTwoMC Clique :=
  FPTReducible.of_computableInPolyTime computableInPolyTime_powTwoMCToClique
    (h := fun k ↦ k + 1)
    (fun x ↦ by
      unfold powTwoMCToClique
      split_ifs <;> dsimp only <;> omega)
    (fun x ↦ (powTwoMCToClique_mem_iff x).symm)

/-- **`PowTwoMC` belongs to `W[1]`** under standard Lean axioms. -/
theorem powTwoMC_mem_W : PowTwoMC ∈ W 1 encPowTwoMCInstance (·.k) :=
  fptReducible_powTwoMC_clique.mem_W Clique_mem_W

/-- **`W[1] = FPT` if and only if `PowTwoMC ∈ FPT`** under standard Lean axioms. -/
theorem w_one_eq_fpt_iff_powTwoMC :
    (∀ ⦃α : Type⦄ (enc : α ↪ List Bool) (κ : α → ℕ), W 1 enc κ = FPT enc κ) ↔
      PowTwoMC ∈ FPT encPowTwoMCInstance (·.k) :=
  ⟨fun h ↦ h _ _ ▸ powTwoMC_mem_W,
    fun h _ _ _ ↦ Set.Subset.antisymm (powTwoMC_wHard.subset_FPT h) (FPT_subset_W 1)⟩

end Cslib.Complexity
