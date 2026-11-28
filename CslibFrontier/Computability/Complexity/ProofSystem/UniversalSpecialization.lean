module

public import CslibFrontier.Computability.Complexity.ProofSystem.FregeReduction
public import CslibFrontier.Computability.Complexity.ProofSystem.UniversalEval

import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Frege Specialization of Universal Circuit Evaluators

This module proves that specializing the `univDescLen k m S` description variables of the range-
avoidance formula `tauFormula 0 (univEvalCircuit k m S hk) b` to the canonical Boolean encoding
`encodeCircuit c S hS` of any size-`≤ S` De Morgan circuit `c : Circuit signature k m` admits a
uniform polynomial-size verified Frege reduction to `tauFormula 0 c b` (using pure Frege rules with
zero extension or extra axioms).

## Main definitions

* `CslibFrontier.ProofComplexity.initConstSubst`, `CslibFrontier.ProofComplexity.initConstPairs`:
  propositional substitution fixing atoms `0 .. ℓ - 1` to Boolean constants `v : BitString ℓ` and
  its finite association-list representation.

## Main results

* `CslibFrontier.ProofComplexity.listSubst_initConstPairs`,
  `CslibFrontier.ProofComplexity.length_initConstPairs_le`: exactness and quadratic size bound of
  `initConstPairs`.
* `CslibFrontier.ProofComplexity.exists_frege_reduce_univEvalCircuit`: uniform polynomial-size
  verified Frege reduction from `(tauFormula 0 U b).subst (initConstSubst (encodeCircuit c S hS))`
  (after a polynomial-size wire-renaming substitution) to `tauFormula 0 c b`.


-/

public section

namespace CslibFrontier.ProofComplexity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Logic.PL
open Turing.MultiTapeTM
open Finset

/-! ### Polynomial-size verified Frege specialization of `univEvalCircuit` -/

/-- Propositional substitution replacing the first `ℓ` atoms `a < ℓ` by Boolean constants
`boolConst (v ⟨a, h⟩)` and leaving every atom `a ≥ ℓ` unchanged. -/
@[expose]
def initConstSubst {ℓ : ℕ} (v : BitString ℓ) : ℕ → Formula := fun a =>
  if h : a < ℓ then boolConst (v ⟨a, h⟩) else .atom a

/-- `initConstSubst v` on an atom `a < ℓ` evaluates to `boolConst (v ⟨a, h⟩)`. -/
theorem initConstSubst_of_lt {ℓ a : ℕ} (v : BitString ℓ) (h : a < ℓ) :
    initConstSubst v a = boolConst (v ⟨a, h⟩) := dite_eq_left h

/-- `initConstSubst v` on an atom `a ≥ ℓ` leaves `.atom a` unchanged. -/
theorem initConstSubst_of_ge {ℓ a : ℕ} (v : BitString ℓ) (h : ¬a < ℓ) :
    initConstSubst v a = .atom a := dite_eq_right h

/-- Explicit finite association list realizing `initConstSubst v` as
`listSubst (initConstPairs v)`. -/
def initConstPairs {ℓ : ℕ} (v : BitString ℓ) : List (ℕ × Formula) :=
  (List.finRange ℓ).map fun i => (i.val, boolConst (v i))

/-- `listSubst (initConstPairs v)` equals `initConstSubst v` pointwise on every atom. -/
theorem listSubst_initConstPairs {ℓ : ℕ} (v : BitString ℓ) :
    listSubst (initConstPairs v) = initConstSubst v := by
  funext a
  have hfind : ∀ (l : List (Fin ℓ)), (∀ x ∈ l, ∀ y ∈ l, x.val = y.val → x = y) →
      (l.map fun i => (i.val, boolConst (v i))).find? (fun kv => kv.1 == a) =
        if h : a < ℓ then if ⟨a, h⟩ ∈ l then some (a, boolConst (v ⟨a,
          h⟩)) else none else none := by
    intro l; induction l with
    | nil => intro _; simp
    | cons x xs ih =>
      intro hinj
      simp only [List.map_cons, List.find?_cons]
      by_cases hxa : x.val = a
      · subst hxa; simp [x.isLt]
      · have hne : (x.val == a) = false := beq_false_of_ne hxa
        rw [hne, ih fun u hu w hw =>
          hinj u (List.mem_cons_of_mem _ hu) w (List.mem_cons_of_mem _ hw)]
        by_cases ha : a < ℓ
        · have hxne : (⟨a, ha⟩ : Fin ℓ) ≠ x := fun h => hxa (congrArg Fin.val h).symm
          simp [ha, hxne]
        · simp [ha]
  have hf := hfind (List.finRange ℓ) fun _ _ _ _ h => Fin.ext h
  by_cases ha : a < ℓ
  · simp only [ha, List.mem_finRange, ↓reduceDIte, ↓reduceIte] at hf
    exact (listSubst_of_find?_eq_some hf).trans (initConstSubst_of_lt v ha).symm
  · simp only [ha, ↓reduceDIte] at hf
    exact (listSubst_of_find?_eq_none hf).trans (initConstSubst_of_ge v ha).symm

/-- Quadratic encoded-length bound on `initConstPairs v`. -/
theorem length_initConstPairs_le {ℓ : ℕ} (v : BitString ℓ) :
    (encList (encPair encNat encFormula) (initConstPairs v)).length ≤ 64 * (ℓ + 1) ^ 2 := by
  have hbc (b : Bool) : (encFormula (boolConst b)).length ≤ 20 := by cases b <;> decide
  have hlist : ∀ l : List (Fin ℓ),
      (encList (encPair encNat encFormula) (l.map fun i => (i.val, boolConst (v i)))).length ≤
        l.length * (4 * ℓ + 50) + 1 := by
    intro l; induction l with
    | nil => simp
    | cons i rest ih =>
      have hi : (encNat i.val).length ≤ ℓ :=
        (length_encNat_mono i.isLt.le).trans (length_encNat_le_self ℓ)
      have hb := hbc (v i)
      simp only [List.map_cons, encList_cons, List.length_append, length_frame, length_encPair,
        List.length_cons]
      nlinarith
  have h := hlist (List.finRange ℓ)
  rw [List.length_finRange] at h
  have : ℓ * (4 * ℓ + 50) + 1 ≤ 64 * (ℓ + 1) ^ 2 := by nlinarith
  exact h.trans this

/-- Converting a `WireSim n g` to its anchor target wire (falling back to `.input ⟨0, hn⟩`) and
`OneVarSim`. -/
private def wireSimToOneVar {n g : ℕ} (hn : 1 ≤ n) : WireSim n g → Wire n g × OneVarSim
  | .inl b => (.input ⟨0, hn⟩, .inl b)
  | .inr (neg, w) => (w, .inr neg)

private theorem liftOneVar_wireSimToOneVar {n g : ℕ} (hn : 1 ≤ n) (s : WireSim n g) :
    liftOneVar (wireSimToOneVar hn s).1 (wireSimToOneVar hn s).2 = s := by
  rcases s with b | ⟨neg, w⟩ <;> rfl

/-- Universal one-variable `IsGateSim` lemma for binary gates where one operand is a constant
`.inl bConst` and the other is an arbitrary `s : WireSim n c.size`! -/
private theorem isGateSim_and_const_left {n' m' n m : ℕ} (hn : 1 ≤ n)
    {c' : Circuit signature n' m'} {c : Circuit signature n m}
    {sim : Wire n' c'.size → WireSim n c.size} {k' : Fin c'.size}
    {i₁ i₂ : ℕ} (h1 : i₁ < n' + k'.val) (h2 : i₂ < n' + k'.val)
    (hlk : c'.program.lines k' =
      (rawGateToLine n' k'.val (.and i₁ i₂)).mapWires (wireCastLE k'.isLt.le))
    (bc : Bool) (s : WireSim n c.size)
    (hs1 : ∀ u, natToWire n' k'.val i₁ = some u → sim (wireCastLE k'.isLt.le u) = .inl bc)
    (hs2 : ∀ u, natToWire n' k'.val i₂ = some u → sim (wireCastLE k'.isLt.le u) = s)
    (hout : sim (.gate k') = if bc then s else .inl false) :
    IsGateSim c' c sim k' := by
  obtain ⟨u₁, hu₁, -⟩ := isSome_natToWire_of_lt h1
  obtain ⟨u₂, hu₂, -⟩ := isSome_natToWire_of_lt h2
  have hl : c'.program.lines k' =
      ⟨.and, ![wireCastLE k'.isLt.le u₁, wireCastLE k'.isLt.le u₂]⟩ := by
    rw [hlk, rawGateToLine_and_of_eq hu₁ hu₂, Line.mapWires]
    congr 1; funext x; fin_cases x <;> rfl
  let p := wireSimToOneVar hn s
  let eOut : OneVarSim := if bc then p.2 else .inl false
  refine isGateSim_of_oneVar p.1 eOut (.inl bc) p.2
    (by rw [hout]; dsimp [eOut]; cases bc
        · rfl
        · exact (liftOneVar_wireSimToOneVar hn s).symm)
    (fun x => by
      generalize c'.program.lines k' = lk at hl x ⊢; subst hl
      fin_cases x
      · exact hs1 u₁ hu₁
      · exact (hs2 u₂ hu₂).trans (liftOneVar_wireSimToOneVar hn s).symm)
    (by
      rw [hl]
      exact oneVarGateTemplate_mem_taut_of_eq _ _ _ _ fun v => by
        dsimp only [eOut]; cases bc <;> rcases p.2 with (_ | _) | (_ | _) <;> cases v <;> rfl)

private theorem isGateSim_or_const {n' m' n m : ℕ} (hn : 1 ≤ n)
    {c' : Circuit signature n' m'} {c : Circuit signature n m}
    {sim : Wire n' c'.size → WireSim n c.size} {k' : Fin c'.size}
    {i₁ i₂ : ℕ} (h1 : i₁ < n' + k'.val) (h2 : i₂ < n' + k'.val)
    (hlk : c'.program.lines k' =
      (rawGateToLine n' k'.val (.or i₁ i₂)).mapWires (wireCastLE k'.isLt.le))
    (s₁ s₂ : WireSim n c.size)
    (hs1 : ∀ u, natToWire n' k'.val i₁ = some u → sim (wireCastLE k'.isLt.le u) = s₁)
    (hs2 : ∀ u, natToWire n' k'.val i₂ = some u → sim (wireCastLE k'.isLt.le u) = s₂)
    (hcase : (s₁ = .inl false ∧ sim (.gate k') = s₂) ∨ (s₂ = .inl false ∧ sim (.gate k') = s₁)) :
    IsGateSim c' c sim k' := by
  obtain ⟨u₁, hu₁, -⟩ := isSome_natToWire_of_lt h1
  obtain ⟨u₂, hu₂, -⟩ := isSome_natToWire_of_lt h2
  have hl : c'.program.lines k' =
      ⟨.or, ![wireCastLE k'.isLt.le u₁, wireCastLE k'.isLt.le u₂]⟩ := by
    rw [hlk, rawGateToLine_or_of_eq hu₁ hu₂, Line.mapWires]
    congr 1; funext x; fin_cases x <;> rfl
  rcases hcase with ⟨rfl, hout⟩ | ⟨rfl, hout⟩
  · let p := wireSimToOneVar hn s₂
    exact isGateSim_of_oneVar p.1 p.2 (.inl false) p.2
      (hout.trans (liftOneVar_wireSimToOneVar hn s₂).symm)
      (fun x => by
        generalize c'.program.lines k' = lk at hl x ⊢; subst hl
        fin_cases x; · exact hs1 u₁ hu₁
        · exact (hs2 u₂ hu₂).trans (liftOneVar_wireSimToOneVar hn s₂).symm)
      (by
        rw [hl]
        exact oneVarGateTemplate_mem_taut_of_eq _ _ _ _ fun v => by
          rcases p.2 with (_ | _) | (_ | _) <;> cases v <;> rfl)
  · let p := wireSimToOneVar hn s₁
    exact isGateSim_of_oneVar p.1 p.2 p.2 (.inl false)
      (hout.trans (liftOneVar_wireSimToOneVar hn s₁).symm)
      (fun x => by
        generalize c'.program.lines k' = lk at hl x ⊢; subst hl
        fin_cases x
        · exact (hs1 u₁ hu₁).trans (liftOneVar_wireSimToOneVar hn s₁).symm
        · exact hs2 u₂ hu₂)
      (by
        rw [hl]
        exact oneVarGateTemplate_mem_taut_of_eq _ _ _ _ fun v => by
          rcases p.2 with (_ | _) | (_ | _) <;> cases v <;> rfl)

/-- Symbolic `WireSim` assigned to gate offset `p < 2 * ws.length` of a one-hot `muxGates`
selecting index `i₀` with target symbolic value `sTarget`. -/
private def muxGateSim {k g : ℕ} (i₀ : ℕ) (sTarget : WireSim k g) (p : ℕ) : WireSim k g :=
  let i := p / 2
  if p % 2 = 0 then
    if i = i₀ then sTarget else .inl false
  else
    if i₀ ≤ i then sTarget else .inl false

/-- Every gate inside a one-hot `muxGates` block satisfies `IsGateSim`! -/
private theorem isGateSim_muxBlock {n' m' k m : ℕ} (hk : 1 ≤ k)
    {c' : Circuit signature n' m'} {c : Circuit signature k m}
    {sim : Wire n' c'.size → WireSim k c.size}
    (selBase gStart acc i₀ : ℕ) (ws : List ℕ) (sTarget : WireSim k c.size)
    (hi₀ : i₀ < ws.length) (p : ℕ) (hp : p < 2 * ws.length)
    (hg_lt : gStart + p < c'.size)
    (hlk : c'.program.lines ⟨gStart + p, hg_lt⟩ =
      (rawGateToLine n' (gStart + p)
        ((muxGates selBase (n' + gStart) acc ws)[p]'(by simp [hp]))).mapWires
        (wireCastLE hg_lt.le))
    (hsim_mux : ∀ q < 2 * ws.length, ∀ hq : gStart + q < c'.size,
      sim (.gate ⟨gStart + q, hq⟩) = muxGateSim i₀ sTarget q)
    (hacc_lt : acc < n' + gStart)
    (hacc_sim : ∀ u, natToWire n' (gStart + p) acc = some u →
      sim (wireCastLE hg_lt.le u) = .inl false)
    (hsel : ∀ i < ws.length, selBase + i < n' + gStart ∧
      ∀ u, natToWire n' (gStart + p) (selBase + i) = some u →
        sim (wireCastLE hg_lt.le u) = .inl (decide (i = i₀)))
    (hws_lt : ∀ i (hi : i < ws.length), ws[i] < n' + gStart)
    (hws_i0 : ∀ u, natToWire n' (gStart + p) ws[i₀] = some u →
      sim (wireCastLE hg_lt.le u) = sTarget) :
    IsGateSim c' c sim ⟨gStart + p, hg_lt⟩ := by
  rw [getElem_muxGates selBase (n' + gStart) acc ws p hp] at hlk
  let i := p / 2
  have hi : i < ws.length := by dsimp [i]; omega
  have hnw_gate (q : ℕ) (hq : q < p) :
      ∀ u, natToWire n' (gStart + p) (n' + gStart + q) = some u →
        sim (wireCastLE hg_lt.le u) = muxGateSim i₀ sTarget q := by
    intro u hu
    have h1 : ¬(n' + gStart + q < n') := by omega
    have h2 : n' + gStart + q - n' < gStart + p := by omega
    rw [natToWire_of_ge_of_lt h1 h2, Option.some.injEq] at hu; subst hu
    have hfin : (⟨n' + gStart + q - n', by omega⟩ : Fin c'.size) =
        ⟨gStart + q, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [wireCastLE_gate]; dsimp only [Fin.castLE]; rw [hfin]
    exact hsim_mux q (by omega) (by omega)
  by_cases hmod : p % 2 = 0
  · simp only [hmod, ↓reduceIte] at hlk
    obtain ⟨u₂, hu₂, -⟩ := isSome_natToWire_of_lt (n := n') (g := gStart + p) (idx := ws[i])
      (by have := hws_lt i hi; dsimp [i] at *; omega)
    let s₂ := if i = i₀ then sTarget else sim (wireCastLE hg_lt.le u₂)
    refine isGateSim_and_const_left hk (by have := (hsel i hi).1; dsimp [i] at *; omega)
      (by have := hws_lt i hi; dsimp [i] at *; omega) hlk (decide (i = i₀)) s₂ (hsel i hi).2
      (fun u hu => by
        dsimp only [s₂]; split_ifs with hie
        · subst hie; exact hws_i0 u hu
        · cases hu.symm.trans hu₂; rfl)
      (by rw [hsim_mux p hp hg_lt]; dsimp only [muxGateSim, s₂]; rw [ite_eq_left hmod]
          change (if i = i₀ then sTarget else .inl false) = _
          by_cases hie : i = i₀ <;> simp [hie])
  · simp only [hmod, ↓reduceIte] at hlk
    have hp_eq : p = 2 * i + 1 := by dsimp [i]; omega
    let ac := if i = 0 then acc else n' + gStart + 2 * i - 1
    have hac_lt : ac < n' + (gStart + p) := by dsimp [ac, i]; split_ifs <;> omega
    let s₁ : WireSim k c.size :=
      if i = 0 then .inl false else if i₀ ≤ i - 1 then sTarget else .inl false
    let s₂ : WireSim k c.size := if i = i₀ then sTarget else .inl false
    refine isGateSim_or_const hk hac_lt (by dsimp [i] at *; omega) hlk s₁ s₂
      (fun u hu => by
        by_cases hi0 : i = 0
        · simp only [s₁, ac, hi0, ↓reduceIte] at hu ⊢; exact hacc_sim u hu
        · have hac_e : ac = n' + gStart + (2 * (i - 1) + 1) := by
            dsimp [ac]; rw [ite_eq_right hi0]; omega
          have h0 := hnw_gate (2 * (i - 1) + 1) (by omega) u (hac_e ▸ hu)
          have hd : (2 * (i - 1) + 1) / 2 = i - 1 := by omega
          have hm : (2 * (i - 1) + 1) % 2 = 1 := by omega
          simpa [muxGateSim, hd, hm, s₁, hi0] using h0)
      (fun u hu => by
        have h0 := hnw_gate (2 * i) (by omega) u (by simpa [add_assoc] using hu)
        simpa [muxGateSim, s₂] using h0)
      (by
        rw [hsim_mux p hp hg_lt]; dsimp only [muxGateSim]
        rw [ite_eq_right hmod]
        change (s₁ = .inl false ∧ (if i₀ ≤ i then sTarget else .inl false) = s₂) ∨
          (s₂ = .inl false ∧ (if i₀ ≤ i then sTarget else .inl false) = s₁)
        by_cases hlt : i < i₀
        · left
          refine ⟨?_, by simp [s₂, show ¬(i₀ ≤ i) by omega, show i ≠ i₀ by omega]⟩
          dsimp only [s₁]; split_ifs with h0 h1 <;> [rfl; omega; rfl]
        · by_cases hie : i = i₀
          · left
            refine ⟨?_, by simp [s₂, hie]⟩
            dsimp only [s₁]; split_ifs with h0 h1 <;> [rfl; omega; rfl]
          · right
            refine ⟨by simp [s₂, hie], ?_⟩
            simp only [s₁, show i ≠ 0 by omega, show i₀ ≤ i - 1 by omega,
              show i₀ ≤ i by omega, ↓reduceIte])

/-- Flatten indexing into `((List.range n).map f).flatten` when every `f r` has length `L`. -/
private theorem getElem_flatten_range {α : Type*} (f : ℕ → List α) (L : ℕ) (hL : 1 ≤ L)
    (hlen : ∀ r, (f r).length = L) :
    ∀ (n p : ℕ) (hp : p < n * L),
      (((List.range n).map f).flatten)[p]'(by
        have aux : ∀ t, (((List.range t).map f).flatten).length = t * L := by
          intro t; induction t with
          | zero => simp
          | succ t ih => rw [List.range_succ, List.map_append, List.flatten_append,
              List.length_append, ih]; simp [hlen, Nat.succ_mul]
        rw [aux]; exact hp) =
      (f (p / L))[p % L]'(by rw [hlen]; exact Nat.mod_lt p hL) := by
  have aux : ∀ t, (((List.range t).map f).flatten).length = t * L := by
    intro t; induction t with
    | zero => simp
    | succ t ih => rw [List.range_succ, List.map_append, List.flatten_append,
        List.length_append, ih]; simp [hlen, Nat.succ_mul]
  intro n; induction n with
  | zero => intro _ h; simp at h
  | succ n ih =>
    intro p hp
    simp only [List.range_succ, List.map_append, List.flatten_append]
    by_cases hpn : p < n * L
    · rw [List.getElem_append_left (by rw [aux]; exact hpn)]; exact ih p hpn
    · rw [List.getElem_append_right (by rw [aux]; omega)]
      simp only [aux, List.map_singleton, List.flatten_cons, List.flatten_nil, List.append_nil]
      have hsub : p - n * L < L := by rw [Nat.succ_mul] at hp; omega
      have hd : p / L = n := by
        rw [show p = L * n + (p - n * L) by rw [mul_comm]; omega,
          Nat.mul_add_div hL, Nat.div_eq_of_lt hsub, add_zero]
      have hm : p % L = p - n * L := by
        conv_lhs => rw [show p = L * n + (p - n * L) by rw [mul_comm]; omega]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hsub]
      simp [hd, hm]

private theorem univSpec_poly_bound (C₀ k m S csz : ℕ) (hS : csz ≤ S) :
    let ℓ := univDescLen k m S
    let n' := ℓ + k
    let Usz := 1 + S * univStepGateCount k S + m * (2 * (k + S))
    40 * (n' + Usz + 1) * (k + csz + n' + Usz + 20) +
      C₀ * (n' + Usz + k + csz + m + 2) ^ 6 ≤
      (C₀ + 40) * 32 ^ 6 * (k + m + S + 4) ^ 12 := by
  intro ℓ n' Usz
  set P := k + m + S + 4
  have hℓ_le : ℓ ≤ 8 * P ^ 2 := univDescLen_le_eight_mul_sq k m S
  have hUsz_le : Usz ≤ 10 * P ^ 2 := univRawGates_len_le_ten_mul_sq k m S
  have hP2 : P ≤ P ^ 2 := Nat.le_self_pow (by decide) P
  have hkP : k ≤ P ^ 2 := (show k ≤ P by dsimp [P]; omega).trans hP2
  have hcszP : csz ≤ P ^ 2 := (show csz ≤ P by dsimp [P]; omega).trans hP2
  have hmP : m ≤ P ^ 2 := (show m ≤ P by dsimp [P]; omega).trans hP2
  have h16 : 16 ≤ P ^ 2 :=
    (show 16 = 4 ^ 2 by decide) ▸ Nat.pow_le_pow_left (show 4 ≤ P by dsimp [P]; omega) 2
  have h1 : n' + Usz + 1 ≤ 32 * P ^ 2 := by dsimp [n']; omega
  have h2 : k + csz + n' + Usz + 20 ≤ 32 * P ^ 2 := by dsimp [n']; omega
  have h3 : n' + Usz + k + csz + m + 2 ≤ 32 * P ^ 2 := by dsimp [n']; omega
  set Q := 32 * P ^ 2
  have hQ2 : Q * Q ≤ Q ^ 6 := by
    rw [← sq]
    exact Nat.pow_le_pow_right (by dsimp [Q]; omega) (by decide)
  have hp_le : 40 * (n' + Usz + 1) * (k + csz + n' + Usz + 20) ≤ 40 * Q ^ 6 :=
    calc 40 * (n' + Usz + 1) * (k + csz + n' + Usz + 20)
        ≤ 40 * Q * Q := Nat.mul_le_mul (Nat.mul_le_mul_left 40 h1) h2
      _ = 40 * (Q * Q) := Nat.mul_assoc 40 Q Q
      _ ≤ 40 * Q ^ 6 := Nat.mul_le_mul_left 40 hQ2
  have hs_le : C₀ * (n' + Usz + k + csz + m + 2) ^ 6 ≤ C₀ * Q ^ 6 :=
    Nat.mul_le_mul_left C₀ (Nat.pow_le_pow_left h3 6)
  calc _ ≤ 40 * Q ^ 6 + C₀ * Q ^ 6 := Nat.add_le_add hp_le hs_le
    _ = (C₀ + 40) * Q ^ 6 := by rw [← Nat.add_mul, add_comm 40 C₀]
    _ = (C₀ + 40) * 32 ^ 6 * P ^ 12 := by
      dsimp only [Q]; rw [Nat.mul_pow, ← pow_mul, ← mul_assoc]

/-- **Polynomial-size verified Frege specialization of `univEvalCircuit`.** There is an absolute
constant `C ≥ 1` such that for every `k ≥ 1`, `m, S : ℕ`, every circuit `c : Circuit signature k m`
with `c.size ≤ S`, and every target `b : BitString m`, substituting `encodeCircuit c S hS` for the
`univDescLen k m S` description atoms of `tauFormula 0 (univEvalCircuit k m S hk) b` and applying a
polynomial-size wire-renaming substitution `listSubst restPairs` admits a verified Extended Frege
proof (using pure Frege rules with zero extension or extra axioms) reducing it to
`tauFormula 0 c b` in encoded bit length at most `C * (k + m + S + 4) ^ 12`. -/
theorem exists_frege_reduce_univEvalCircuit :
    ∃ C : ℕ, 1 ≤ C ∧
      ∀ {k m : ℕ} (hk : 1 ≤ k) (c : Circuit signature k m) (S : ℕ) (hS : c.size ≤ S)
        (b : BitString m),
        let U := univEvalCircuit k m S hk
        let v := encodeCircuit c S hS
        ∃ (restPairs : List (ℕ × Formula)) (steps : List EFStep),
          runEFProof (fun _ => false) steps =
            .imp (((tauFormula 0 U b).subst (initConstSubst v)).subst (listSubst restPairs))
              (tauFormula 0 c b) ∧
          (encList (encPair encNat encFormula) restPairs).length +
            (encList encEFStep steps).length ≤
            C * (k + m + S + 4) ^ 12 := by
  obtain ⟨C₀, hC₀, hred⟩ := exists_frege_reduce_tauFormula
  refine ⟨(C₀ + 40) * 32 ^ 6, Nat.mul_pos (by omega) (Nat.pow_pos (by decide)),
    fun {k m} hk c S hS b => ?_⟩
  let ℓ := univDescLen k m S
  let n' := ℓ + k
  let U := univEvalCircuit k m S hk
  let v := encodeCircuit c S hS
  let Lstep := univStepGateCount k S
  have hLstep_gt : 4 * (k + S) + 10 < Lstep := four_mul_add_ten_lt_univStepGateCount k S
  have hLstep_sub : Lstep - (4 * (k + S) + 10) = 10 := univStepGateCount_sub_four_mul_add_ten k S
  have hLstep_pos : 1 ≤ Lstep := by omega
  have hstride_ge : 5 + (k + S) + (k + S) ≤ univGateDescStride k S := univGateDescStride_ge k S
  let simTargetWire (idx : ℕ) : WireSim k c.size :=
    if h1 : idx < k then .inr (false, .input ⟨idx, h1⟩)
    else if h2 : idx - k < c.size then .inr (false, .gate ⟨idx - k, h2⟩)
    else .inl false
  have hsimTarget_wireToNat (w : Wire k c.size) : simTargetWire (wireToNat w) =
    .inr (false, w) := by
    cases w with
    | input i => simp [simTargetWire, i.isLt]
    | gate g =>
      simp only [wireToNat_gate, simTargetWire, show ¬(k + g.val < k) by omega,
        Nat.add_sub_cancel_left, g.isLt, ↓reduceDIte]
  let i0At (r : ℕ) : ℕ := if hrc : r < c.size then lineArg0 (c.program.lines ⟨r, hrc⟩) else 0
  let i1At (r : ℕ) : ℕ := if hrc : r < c.size then lineArg1 (c.program.lines ⟨r, hrc⟩) else 0
  let opcAt (r : ℕ) : ℕ :=
    if hrc : r < c.size then (opToCode (c.program.lines ⟨r, hrc⟩).op).val else 0
  let opSim (r d0 : ℕ) : WireSim k c.size :=
    if d0 = 0 then
      if hrc : r < c.size then
        if opcAt r = 0 then .inr (false, .gate ⟨r, hrc⟩) else .inl false
      else .inl false
    else if d0 = 1 then
      if hrc : r < c.size then
        if opcAt r = 1 then .inr (false, .gate ⟨r, hrc⟩) else .inl true
      else .inl true
    else if d0 = 2 then
      if opcAt r = 2 then simTargetWire (i0At r) else .inl false
    else if d0 = 3 then
      if hrc : r < c.size then
        if opcAt r = 2 then .inr (false, .gate ⟨r, hrc⟩) else .inl true
      else .inl true
    else if d0 = 4 then
      if opcAt r = 3 then simTargetWire (i0At r) else .inl false
    else if d0 = 5 then
      if opcAt r = 3 then simTargetWire (i1At r) else .inl false
    else if d0 = 6 then
      if hrc : r < c.size then
        if opcAt r = 3 then .inr (false, .gate ⟨r, hrc⟩) else .inl false
      else .inl false
    else if d0 = 7 then
      if opcAt r = 4 then simTargetWire (i0At r) else .inl false
    else if d0 = 8 then
      if opcAt r = 4 then simTargetWire (i1At r) else .inl false
    else
      if hrc : r < c.size then
        if opcAt r = 4 then .inr (false, .gate ⟨r, hrc⟩) else .inl false
      else .inl false
  let stepSim (r off : ℕ) : WireSim k c.size :=
    let sOut : WireSim k c.size :=
      if hrc : r < c.size then .inr (false, .gate ⟨r, hrc⟩) else .inl false
    if off < 2 * (k + S) then muxGateSim (i0At r) (simTargetWire (i0At r)) off
    else if off < 4 * (k + S) then muxGateSim (i1At r) (simTargetWire (i1At r)) (off - 2 * (k + S))
    else if off < 4 * (k + S) + 10 then opSim r (off - 4 * (k + S))
    else muxGateSim (opcAt r) sOut (off - (4 * (k + S) + 10))
  let sim : Wire n' U.size → WireSim k c.size
    | .input idx =>
      if h : idx.val < ℓ then .inl (v ⟨idx.val, h⟩)
      else .inr (false, .input ⟨idx.val - ℓ, by dsimp [n'] at idx; omega⟩)
    | .gate g' =>
      if g'.val = 0 then .inl false
      else if g'.val < 1 + S * Lstep then
        let p := g'.val - 1
        stepSim (p / Lstep) (p % Lstep)
      else
        let p := g'.val - (1 + S * Lstep)
        let j := p / (2 * (k + S))
        let off := p % (2 * (k + S))
        if hj : j < m then
          muxGateSim (wireToNat (c.outputs ⟨j, hj⟩)) (.inr (false, c.outputs ⟨j, hj⟩)) off
        else .inl false
  have hline_U (g' : Fin U.size) :
      U.program.lines g' =
        (rawGateToLine n' g'.val ((univRawGates k m S)[g'.val]'g'.isLt)).mapWires
          (wireCastLE g'.isLt.le) :=
    lines_buildRawCircuit n' (by dsimp [n']; omega) (univRawGates k m S) (univRawOuts k m S) g'
  have hnw_sim {g0 : ℕ} (hg0_lt : g0 < U.size) {idx : ℕ} (h : idx < n' + g0)
      (u : Wire n' g0) (hu : natToWire n' g0 idx = some u) :
      sim (wireCastLE hg0_lt.le u) =
        if hi : idx < n' then sim (.input ⟨idx, hi⟩)
        else sim (.gate ⟨idx - n', by omega⟩) := by
    by_cases hi : idx < n'
    · rw [natToWire_of_lt _ hi, Option.some.injEq] at hu; subst hu
      simp [hi]
    · have h2 : idx - n' < g0 := by omega
      rw [natToWire_of_ge_of_lt hi h2, Option.some.injEq] at hu; subst hu
      simp [hi]
  have hfw_sim {g0 : ℕ} (hg0_lt : g0 < U.size) (hpos : 0 < g0) :
      ∀ u, natToWire n' g0 n' = some u → sim (wireCastLE hg0_lt.le u) = .inl false := by
    intro u hu; rw [hnw_sim hg0_lt (by omega) u hu]; simp [sim]
  have hdesc_sim {g0 : ℕ} (hg0_lt : g0 < U.size) {pos : ℕ} (hp : pos < ℓ) :
      ∀ u, natToWire n' g0 pos = some u →
        sim (wireCastLE hg0_lt.le u) = .inl (v ⟨pos, hp⟩) := by
    intro u hu; rw [hnw_sim hg0_lt (by dsimp [n']; omega) u hu]
    rw [dite_eq_left (show pos < n' by dsimp [n']; omega)]; simp [sim, hp]
  have havail_sim {g0 : ℕ} (hg0_lt : g0 < U.size) (r idx : ℕ) (hrS : r ≤ S) (hidx : idx < k + S)
      (hg_ge : 1 + r * Lstep ≤ g0) (hbound : idx < k + min r c.size) :
      ∀ u, natToWire n' g0 ((univAvailWires k m S r)[idx]'(by simp [hidx])) = some u →
        sim (wireCastLE hg0_lt.le u) = simTargetWire idx := by
    intro u hu
    have hlt := (univAvailWires_lt k m S r idx hidx).trans_le
      (show n' + 1 + r * Lstep ≤ n' + g0 by omega)
    rw [hnw_sim hg0_lt hlt u hu]
    have hge := getElem_univAvailWires k m S r idx hidx
    by_cases hik : idx < k
    · have hw : (univAvailWires k m S r)[idx]'(by simp [hidx]) = ℓ + idx := by simp [hge, hik, ℓ]
      simp only [hw, show ℓ + idx < n' by dsimp [n']; omega, ↓reduceDIte, sim,
        show ¬(ℓ + idx < ℓ) by omega, Nat.add_sub_cancel_left, simTargetWire, hik]
    · set t := idx - k
      have htr : t < r := by omega
      have htc : t < c.size := by omega
      have hw : (univAvailWires k m S r)[idx]'(by simp [hidx]) =
          n' + (1 + t * Lstep + (Lstep - 1)) := by
        rw [hge, ite_eq_right hik, ite_eq_left htr, univSimGateWire_eq_step_last]
      have hd : (t * Lstep + (Lstep - 1)) / Lstep = t := by
        rw [mul_comm t, Nat.mul_add_div hLstep_pos, Nat.div_eq_of_lt (by omega), add_zero]
      have hm : (t * Lstep + (Lstep - 1)) % Lstep = Lstep - 1 := by
        rw [mul_comm t, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      have hts : t * Lstep + (Lstep - 1) < S * Lstep := by
        have := Nat.mul_le_mul_right Lstep (show t < S by omega); rw [Nat.succ_mul] at this; omega
      simp only [hw, show ¬(n' + (1 + t * Lstep + (Lstep - 1)) < n') by omega, ↓reduceDIte,
        Nat.add_sub_cancel_left, sim, show 1 + t * Lstep + (Lstep - 1) ≠ 0 by omega,
        show 1 + t * Lstep + (Lstep - 1) < 1 + S * Lstep by omega,
        show 1 + t * Lstep + (Lstep - 1) - 1 = t * Lstep + (Lstep - 1) by omega,
        hd, hm, simTargetWire, hik, show idx - k = t from rfl, htc, ↓reduceIte]
      dsimp only [stepSim, opcAt]
      have hopc5 : (opToCode (c.program.lines ⟨t, htc⟩).op).val < 5 := (opToCode _).isLt
      simp only [show ¬(Lstep - 1 < 2 * (k + S)) by omega,
        show ¬(Lstep - 1 < 4 * (k + S)) by omega,
        show ¬(Lstep - 1 < 4 * (k + S) + 10) by omega,
        show Lstep - 1 - (4 * (k + S) + 10) = 9 by omega,
        muxGateSim, show (9 : ℕ) % 2 ≠ 0 by decide, show (9 : ℕ) / 2 = 4 by decide,
        htc, ↓reduceDIte, show (opToCode (c.program.lines ⟨t, htc⟩).op).val ≤ 4 by omega,
        ↓reduceIte]
  have harg0_acyc {r : ℕ} (hrc : r < c.size) :
      lineArg0 (c.program.lines ⟨r, hrc⟩) < k + r := by
    have ha := program_lines_wireToNat_lt c.program ⟨r, hrc⟩
    generalize c.program.lines ⟨r, hrc⟩ = lk at ha ⊢
    rcases lk with ⟨op, lws⟩
    cases op with
    | const _ => simp; omega
    | not => exact ha 0
    | and => exact ha 0
    | or => exact ha 0
  have harg1_acyc {r : ℕ} (hrc : r < c.size) :
      lineArg1 (c.program.lines ⟨r, hrc⟩) < k + r := by
    have ha := program_lines_wireToNat_lt c.program ⟨r, hrc⟩
    generalize c.program.lines ⟨r, hrc⟩ = lk at ha ⊢
    rcases lk with ⟨op, lws⟩
    cases op with
    | const _ => simp; omega
    | not => simp; omega
    | and => exact ha 1
    | or => exact ha 1
  have hget_cons : ∀ (x : RawGate) (xs : List RawGate) (idx p0 : ℕ)
      (h1 : idx < (x :: xs).length) (hp0 : idx = p0 + 1),
      (x :: xs)[idx]'h1 = xs[p0]'(by simp at h1; omega) := by
    rintro x xs _ p0 h1 rfl; rfl
  have hmap_cast : ∀ {a₁ a₂ : ℕ} (ha : a₁ = a₂) (h1 : a₁ ≤ U.size) (h2 : a₂ ≤ U.size)
      {g₁ g₂ : RawGate} (hg : g₁ = g₂),
      (rawGateToLine n' a₁ g₁).mapWires (wireCastLE h1) =
        (rawGateToLine n' a₂ g₂).mapWires (wireCastLE h2) := by
    rintro a _ rfl _ _ g _ rfl; rfl
  have hgates (g' : Fin U.size) : IsGateSim U c sim g' := by
    have hlk := hline_U g'
    by_cases hg0 : g'.val = 0
    · have hrg : (univRawGates k m S)[g'.val]'g'.isLt = .const false := by simp [hg0]
      have hl : U.program.lines g' = ⟨.const false, Fin.elim0⟩ := by
        rw [hlk, hrg, rawGateToLine_const]; dsimp [Line.mapWires]; congr 1; funext x; exact x.elim0
      exact isGateSim_of_oneVar (.input ⟨0, hk⟩) (.inl false) (.inl false) (.inl false)
        (by simp [sim, hg0]) (fun x => by rw [hl] at x; exact x.elim0) (by rw [hl]; intro _; rfl)
    · by_cases hgS : g'.val < 1 + S * Lstep
      · set p := g'.val - 1
        have hpS : p < S * Lstep := by omega
        set r := p / Lstep; set off := p % Lstep
        have hrS : r < S := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
        have hoff : off < Lstep := Nat.mod_lt p hLstep_pos
        have hg_eq : g'.val = 1 + r * Lstep + off := by
          have : r * Lstep + off = p := by rw [mul_comm]; exact Nat.div_add_mod p Lstep
          omega
        have hrg : (univRawGates k m S)[g'.val]'g'.isLt =
            (univGateBlock k m S r)[off]'(by rw [length_univGateBlock]; exact hoff) := by
          have hfl_len : (((List.range S).map (univGateBlock k m S)).flatten).length =
              S * Lstep := by
            have aux : ∀ t, (((List.range t).map (univGateBlock k m S)).flatten).length =
                t * Lstep := by
              intro t; induction t with
              | zero => simp
              | succ t ih => rw [List.range_succ, List.map_append, List.flatten_append,
                  List.length_append, ih]; simp [Lstep, Nat.succ_mul]
            exact aux S
          refine (hget_cons _ _ g'.val p g'.isLt (by omega)).trans ?_
          rw [List.getElem_append_left (by rw [hfl_len]; exact hpS)]
          exact getElem_flatten_range (univGateBlock k m S) Lstep hLstep_pos
            (length_univGateBlock k m S) S p hpS
        have hsim_step (q : ℕ) (hq : q < Lstep)
            (hgq : 1 + r * Lstep + q < U.size) :
            sim (.gate ⟨1 + r * Lstep + q, hgq⟩) = stepSim r q := by
          have hpq : r * Lstep + q < S * Lstep := by
            have := Nat.mul_le_mul_right Lstep hrS; rw [Nat.succ_mul] at this; omega
          have hd : (r * Lstep + q) / Lstep = r := by
            rw [mul_comm r, Nat.mul_add_div hLstep_pos, Nat.div_eq_of_lt hq, add_zero]
          have hm : (r * Lstep + q) % Lstep = q := by
            rw [mul_comm r, Nat.mul_add_mod, Nat.mod_eq_of_lt hq]
          dsimp only [sim]
          rw [ite_eq_right (by omega), ite_eq_left (by omega)]
          simp only [show 1 + r * Lstep + q - 1 = r * Lstep + q by omega, hd, hm]
        have hg1_lt : 1 + r * Lstep + off < U.size := hg_eq ▸ g'.isLt
        have hg_fin : g' = ⟨1 + r * Lstep + off, hg1_lt⟩ := Fin.ext hg_eq
        let i0 := i0At r
        let i1 := i1At r
        let opc := opcAt r
        let s0 := simTargetWire i0
        let s1 := simTargetWire i1
        let sOut : WireSim k c.size :=
          if hrc : r < c.size then .inr (false, .gate ⟨r, hrc⟩) else .inl false
        have hi0_lt : i0 < k + S := by
          dsimp [i0, i0At]; split_ifs with hrc
          · exact (harg0_acyc hrc).trans_le (by omega)
          · omega
        have hi1_lt : i1 < k + S := by
          dsimp [i1, i1At]; split_ifs with hrc
          · exact (harg1_acyc hrc).trans_le (by omega)
          · omega
        have hopc_lt : opc < 5 := by
          dsimp [opc, opcAt]; split_ifs
          · exact (opToCode _).isLt
          · omega
        let ws := univAvailWires k m S r
        let opBase := r * univGateDescStride k S
        have hst_ℓ : opBase + univGateDescStride k S ≤ ℓ := by
          have h1 := Nat.mul_le_mul_right (univGateDescStride k S) hrS
          have h2 := mul_univGateDescStride_le_univDescLen k m S
          rw [Nat.succ_mul] at h1; dsimp only [opBase, ℓ]; omega
        by_cases h1 : off < 2 * (k + S)
        · have hbg := getElem_univGateBlock_mux1 k m S r off h1
          rw [hg_fin]
          refine isGateSim_muxBlock (c' := U) (c := c) (sim := sim)
            hk (opBase + 5) (1 + r * Lstep) n' i0 ws s0
            (by simp [ws, hi0_lt]) off (by simp [ws, h1]) hg1_lt
            (by rw [← hg_fin]; exact hlk.trans (hmap_cast hg_eq _ _ (hrg.trans hbg)))
            (fun q hq hgq => by
              rw [hsim_step q (by simp [ws] at hq; omega) hgq]
              dsimp [stepSim]; rw [ite_eq_left (by simpa [ws] using hq)])
            (by omega) (hfw_sim hg1_lt (by omega))
            (fun idx hidx => by
              have hi' : idx < k + S := by simpa [ws] using hidx
              have hp' : opBase + 5 + idx < ℓ := by omega
              exact ⟨by have : ℓ ≤ n' := Nat.le_add_right ℓ k; omega, fun u hu =>
                (hdesc_sim hg1_lt hp' u hu).trans (by
                  dsimp only [v, opBase, i0, i0At]; rw [encodeCircuit_arg0 c S hS hrS hi'])⟩)
            (fun idx hidx => by
              simpa [n', ℓ, Lstep, add_assoc] using
                univAvailWires_lt k m S r idx (by simpa [ws] using hidx))
            (fun u hu => havail_sim hg1_lt r i0 hrS.le hi0_lt (by omega)
              (by by_cases hrc : r < c.size
                  · rw [min_eq_left hrc.le]; simpa [i0, i0At, hrc] using harg0_acyc hrc
                  · have : i0 = 0 := dite_eq_right hrc; omega) u hu)
        · by_cases h2 : off < 4 * (k + S)
          · set off2 := off - 2 * (k + S)
            have hoff2 : off2 < 2 * (k + S) := by omega
            let gs2 := 1 + r * Lstep + 2 * (k + S)
            have hg2_lt : gs2 + off2 < U.size := by have := g'.isLt; dsimp [gs2]; omega
            have hg_fin2 : g' = ⟨gs2 + off2, hg2_lt⟩ := Fin.ext (by dsimp [gs2]; omega)
            have hbg : (univGateBlock k m S r)[off]'(by simp [Lstep, hoff]) =
                (muxGates (opBase + 5 + (k + S)) (n' + gs2) n' ws)[off2]'(by simp [ws, hoff2]) :=
              getElem_univGateBlock_mux2 k m S r off h1 h2
            rw [hg_fin2]
            refine isGateSim_muxBlock (c' := U) (c := c) (sim := sim)
              hk (opBase + 5 + (k + S)) gs2 n' i1 ws s1
              (by simp [ws, hi1_lt]) off2 (by simp [ws, hoff2]) hg2_lt
              (by rw [← hg_fin2]
                  exact hlk.trans (hmap_cast (congrArg Fin.val hg_fin2) _ _ (hrg.trans hbg)))
              (fun q hq hgq => by
                have hq' : q < 2 * (k + S) := by simpa [ws] using hq
                have heq' : gs2 + q = 1 + r * Lstep + (2 * (k + S) + q) := by dsimp [gs2]; omega
                have hfin' : (⟨gs2 + q, hgq⟩ : Fin U.size) = ⟨_, heq' ▸ hgq⟩ := Fin.ext heq'
                rw [hfin', hsim_step (2 * (k + S) + q) (by omega)]
                dsimp [stepSim]
                rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left])
              (by dsimp [gs2]; omega) (hfw_sim hg2_lt (by dsimp [gs2]; omega))
              (fun idx hidx => by
                have hi' : idx < k + S := by simpa [ws] using hidx
                have hp' : opBase + 5 + (k + S) + idx < ℓ := by omega
                exact ⟨by dsimp [n', gs2]; omega, fun u hu =>
                  (hdesc_sim hg2_lt hp' u hu).trans (by
                    dsimp only [v, opBase, i1, i1At]; rw [encodeCircuit_arg1 c S hS hrS hi'])⟩)
              (fun idx hidx => (univAvailWires_lt k m S r idx (by simpa [ws] using hidx)).trans
                (by dsimp [n', ℓ, gs2, Lstep]; omega))
              (fun u hu => havail_sim hg2_lt r i1 hrS.le hi1_lt (by dsimp [gs2]; omega)
                (by by_cases hrc : r < c.size
                    · rw [min_eq_left hrc.le]; simpa [i1, i1At, hrc] using harg1_acyc hrc
                    · have : i1 = 0 := dite_eq_right hrc; omega) u hu)
          · let gs3 := 1 + r * Lstep + 4 * (k + S)
            let a1w := n' + (1 + r * Lstep + (2 * (k + S) - 1))
            let a2w := n' + (1 + r * Lstep + (4 * (k + S) - 1))
            have ha1_sim : a1w < n' + g'.val ∧
                ∀ u, natToWire n' g'.val a1w = some u → sim (wireCastLE g'.isLt.le u) = s0 := by
              refine ⟨by dsimp [a1w]; omega, fun u hu => ?_⟩
              rw [hnw_sim g'.isLt (by dsimp [a1w]; omega) u hu,
                dite_eq_right (by dsimp [a1w]; omega)]
              have hf : (⟨a1w - n', by dsimp [a1w]; omega⟩ : Fin U.size) =
                  ⟨1 + r * Lstep + (2 * (k + S) - 1), by omega⟩ := Fin.ext (by dsimp [a1w]; omega)
              rw [hf, hsim_step (2 * (k + S) - 1) (by omega)]
              dsimp only [stepSim]; rw [ite_eq_left (by omega)]
              dsimp only [muxGateSim]
              have hmod : (2 * (k + S) - 1) % 2 ≠ 0 := by omega
              have hdiv : (2 * (k + S) - 1) / 2 = k + S - 1 := by omega
              rw [ite_eq_right hmod, hdiv, ite_eq_left (show i0 ≤ k + S - 1 by omega)]
            have ha2_sim : a2w < n' + g'.val ∧
                ∀ u, natToWire n' g'.val a2w = some u → sim (wireCastLE g'.isLt.le u) = s1 := by
              refine ⟨by dsimp [a2w]; omega, fun u hu => ?_⟩
              rw [hnw_sim g'.isLt (by dsimp [a2w]; omega) u hu,
                dite_eq_right (by dsimp [a2w]; omega)]
              have hf : (⟨a2w - n', by dsimp [a2w]; omega⟩ : Fin U.size) =
                  ⟨1 + r * Lstep + (4 * (k + S) - 1), by omega⟩ := Fin.ext (by dsimp [a2w]; omega)
              rw [hf, hsim_step (4 * (k + S) - 1) (by omega)]
              dsimp only [stepSim]; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
              have hsub : 4 * (k + S) - 1 - 2 * (k + S) = 2 * (k + S) - 1 := by omega
              rw [hsub]; dsimp only [muxGateSim]
              rw [ite_eq_right (by omega), show (2 * (k + S) - 1) / 2 = k + S - 1 by omega,
                ite_eq_left (show i1 ≤ k + S - 1 by omega)]
            have hop_wire (d : ℕ) (hd : d < 10) (hlt : gs3 + d < g'.val) :
                ∀ u, natToWire n' g'.val (n' + gs3 + d) = some u →
                  sim (wireCastLE g'.isLt.le u) = stepSim r (4 * (k + S) + d) := by
              intro u hu
              rw [hnw_sim g'.isLt (by omega) u hu, dite_eq_right (by omega)]
              have hf : (⟨n' + gs3 + d - n', by omega⟩ : Fin U.size) =
                  ⟨1 + r * Lstep + (4 * (k + S) + d), by dsimp [gs3] at hlt; omega⟩ :=
                Fin.ext (by dsimp [gs3]; omega)
              rw [hf]; exact hsim_step (4 * (k + S) + d) (by omega) _
            have hstep_d (d0 : ℕ) (hd0 : d0 < 10) :
                stepSim r (4 * (k + S) + d0) = opSim r d0 := by
              dsimp only [stepSim]
              rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
                Nat.add_sub_cancel_left]
            have hstep0 : stepSim r (4 * (k + S) + 0) =
                if hrc : r < c.size then if opc =
                  0 then .inr (false, .gate ⟨r, hrc⟩) else .inl false
                else .inl false := hstep_d 0 (by omega)
            have hstep1 : stepSim r (4 * (k + S) + 1) =
                if hrc : r < c.size then if opc = 1 then .inr (false, .gate ⟨r, hrc⟩) else .inl true
                else .inl true := hstep_d 1 (by omega)
            have hstep2 : stepSim r (4 * (k + S) + 2) =
                if opc = 2 then s0 else .inl false := hstep_d 2 (by omega)
            have hstep3 : stepSim r (4 * (k + S) + 3) =
                if hrc : r < c.size then if opc = 2 then .inr (false, .gate ⟨r, hrc⟩) else .inl true
                else .inl true := hstep_d 3 (by omega)
            have hstep4 : stepSim r (4 * (k + S) + 4) =
                if opc = 3 then s0 else .inl false := hstep_d 4 (by omega)
            have hstep5 : stepSim r (4 * (k + S) + 5) =
                if opc = 3 then s1 else .inl false := hstep_d 5 (by omega)
            have hstep6 : stepSim r (4 * (k + S) + 6) =
                if hrc : r < c.size then if opc =
                  3 then .inr (false, .gate ⟨r, hrc⟩) else .inl false
                else .inl false := hstep_d 6 (by omega)
            have hstep7 : stepSim r (4 * (k + S) + 7) =
                if opc = 4 then s0 else .inl false := hstep_d 7 (by omega)
            have hstep8 : stepSim r (4 * (k + S) + 8) =
                if opc = 4 then s1 else .inl false := hstep_d 8 (by omega)
            have hstep9 : stepSim r (4 * (k + S) + 9) =
                if hrc : r < c.size then if opc =
                  4 then .inr (false, .gate ⟨r, hrc⟩) else .inl false
                else .inl false := hstep_d 9 (by omega)
            by_cases h3 : off < 4 * (k + S) + 10
            · set d := off - 4 * (k + S)
              have hd10 : d < 10 := by omega
              have hsim_g : sim (.gate g') = stepSim r (4 * (k + S) + d) := by
                rw [hg_fin, hsim_step off hoff]; congr 1; omega
              have hbg : (univGateBlock k m S r)[off]'(by simp [Lstep, hoff]) =
                  ([ .const false, .const true,
                     .and (opBase + 2) a1w, .not (n' + gs3 + 2),
                     .and (opBase + 3) a1w, .and (opBase + 3) a2w,
                     .and (n' + gs3 + 4) (n' + gs3 + 5),
                     .and (opBase + 4) a1w, .and (opBase + 4) a2w,
                     .or (n' + gs3 + 7) (n' + gs3 + 8) ] : List RawGate)[d]'hd10 :=
                getElem_univGateBlock_ops (by omega) m S r off h2 h3
              have hop_sel (t : ℕ) (ht : t < 5) :
                  opBase + t < n' + g'.val ∧
                  ∀ u, natToWire n' g'.val (opBase + t) = some u →
                    sim (wireCastLE g'.isLt.le u) = .inl (decide (t = opc)) := by
                have hp' : opBase + t < ℓ := by omega
                exact ⟨by have : ℓ ≤ n' := Nat.le_add_right ℓ k; omega, fun u hu =>
                  (hdesc_sim g'.isLt hp' u hu).trans (by
                    dsimp only [v, opBase, opc, opcAt]; rw [encodeCircuit_op c S hS hrS ht])⟩
              rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨
                  d = 7 ∨ d = 8 ∨ d = 9 by omega) with
                hd | hd | hd | hd | hd | hd | hd | hd | hd | hd
              · have hgr : (univRawGates k m S)[g'.val]'g'.isLt = .const false := by
                  rw [hrg, hbg]; simp only [hd, List.getElem_cons_zero]
                have hl : U.program.lines g' = ⟨.const false, Fin.elim0⟩ := by
                  rw [hlk, hgr, rawGateToLine_const]; dsimp [Line.mapWires]; congr 1; funext x
                  exact x.elim0
                by_cases hc0 : ∃ hrc : r < c.size, opc = 0
                · obtain ⟨hrc, hop0⟩ := hc0
                  have hop_eq : (U.program.lines g').op = (c.program.lines ⟨r, hrc⟩).op := by
                    rw [hl]; dsimp [opc, opcAt] at hop0; rw [dite_eq_left hrc] at hop0
                    cases hco : (c.program.lines ⟨r, hrc⟩).op with
                    | const bv => cases bv <;> [rfl; (rw [hco] at hop0; cases hop0)]
                    | _ => rw [hco] at hop0; cases hop0
                  exact isGateSim_of_preserve ⟨r, hrc⟩ hop_eq
                    (by rw [hsim_g, hd, hstep0, dite_eq_left hrc, ite_eq_left hop0])
                    (fun x => by rw [hl] at x; exact x.elim0)
                · have hs : sim (.gate g') = .inl false := by
                    rw [hsim_g, hd, hstep0]
                    by_cases hrc : r < c.size
                    · rw [dite_eq_left hrc, ite_eq_right (fun h0 => hc0 ⟨hrc, h0⟩)]
                    · rw [dite_eq_right hrc]
                  exact isGateSim_of_oneVar (.input ⟨0, hk⟩) (.inl false) (.inl false) (.inl false)
                    hs (fun x => by rw [hl] at x; exact x.elim0) (by rw [hl]; intro _; rfl)
              · have hgr : (univRawGates k m S)[g'.val]'g'.isLt = .const true := by
                  rw [hrg, hbg]; simp only [hd, List.getElem_cons_succ, List.getElem_cons_zero]
                have hl : U.program.lines g' = ⟨.const true, Fin.elim0⟩ := by
                  rw [hlk, hgr, rawGateToLine_const]; dsimp [Line.mapWires]; congr 1; funext x
                  exact x.elim0
                by_cases hc1 : ∃ hrc : r < c.size, opc = 1
                · obtain ⟨hrc, hop1⟩ := hc1
                  have hop_eq : (U.program.lines g').op = (c.program.lines ⟨r, hrc⟩).op := by
                    rw [hl]; dsimp [opc, opcAt] at hop1; rw [dite_eq_left hrc] at hop1
                    cases hco : (c.program.lines ⟨r, hrc⟩).op with
                    | const bv => cases bv <;> [(rw [hco] at hop1; cases hop1); rfl]
                    | _ => rw [hco] at hop1; cases hop1
                  exact isGateSim_of_preserve ⟨r, hrc⟩ hop_eq
                    (by rw [hsim_g, hd, hstep1, dite_eq_left hrc, ite_eq_left hop1])
                    (fun x => by rw [hl] at x; exact x.elim0)
                · have hs : sim (.gate g') = .inl true := by
                    rw [hsim_g, hd, hstep1]
                    by_cases hrc : r < c.size
                    · rw [dite_eq_left hrc, ite_eq_right (fun h1' => hc1 ⟨hrc, h1'⟩)]
                    · rw [dite_eq_right hrc]
                  exact isGateSim_of_oneVar (.input ⟨0, hk⟩) (.inl true) (.inl false) (.inl false)
                    hs (fun x => by rw [hl] at x; exact x.elim0) (by rw [hl]; intro _; rfl)
              · have hgr : (univRawGates k m S)[g'.val]'g'.isLt = .and (opBase + 2) a1w := by
                  rw [hrg, hbg]; simp only [hd, List.getElem_cons_succ, List.getElem_cons_zero]
                refine isGateSim_and_const_left hk (hop_sel 2 (by omega)).1 ha1_sim.1
                  (by rw [hlk, hgr]) (decide (2 = opc)) s0
                  (hop_sel 2 (by omega)).2 ha1_sim.2 ?_
                rw [hsim_g, hd, hstep2]
                by_cases he : opc = 2
                · rw [ite_eq_left he, ite_eq_left (decide_eq_true he.symm)]
                · rw [ite_eq_right he, ite_eq_right (mt of_decide_eq_true (Ne.symm he))]
              · have hgr : (univRawGates k m S)[g'.val]'g'.isLt = .not (n' + gs3 + 2) := by
                  rw [hrg, hbg]; simp only [hd, List.getElem_cons_succ, List.getElem_cons_zero]
                have hw2_lt : n' + gs3 + 2 < n' + g'.val := by dsimp [gs3]; omega
                obtain ⟨u₀, hu₀, -⟩ := isSome_natToWire_of_lt hw2_lt
                have hl : U.program.lines g' = ⟨.not, fun _ => wireCastLE g'.isLt.le u₀⟩ := by
                  rw [hlk, hgr, rawGateToLine_not_of_eq hu₀]; rfl
                have hu₀_s : sim (wireCastLE g'.isLt.le u₀) =
                    if opc = 2 then s0 else .inl false :=
                  (hop_wire 2 (by omega) (by dsimp [gs3]; omega) u₀ hu₀).trans hstep2
                by_cases hc2 : ∃ hrc : r < c.size, opc = 2
                · obtain ⟨hrc, hop2⟩ := hc2
                  have hco : (c.program.lines ⟨r, hrc⟩).op = .not := by
                    dsimp [opc, opcAt] at hop2; rw [dite_eq_left hrc] at hop2
                    cases ho : (c.program.lines ⟨r, hrc⟩).op with
                    | const bv => cases bv <;> (rw [ho] at hop2; cases hop2)
                    | not => rfl
                    | _ => rw [ho] at hop2; cases hop2
                  have hop_eq : (U.program.lines g').op = (c.program.lines ⟨r, hrc⟩).op := by
                    rw [hl, hco]
                  refine isGateSim_of_preserve ⟨r, hrc⟩ hop_eq
                    (by rw [hsim_g, hd, hstep3, dite_eq_left hrc, ite_eq_left hop2]) fun x => ?_
                  have hs0_eq : s0 = .inr (false, (c.program.lines ⟨r, hrc⟩).wires
                      (⟨0, by rw [hco]; decide⟩)) := by
                    dsimp [s0, i0, i0At]; rw [dite_eq_left hrc]
                    generalize c.program.lines ⟨r, hrc⟩ = lk at hco ⊢
                    rcases lk with ⟨op, lws⟩; dsimp at hco; subst hco
                    exact hsimTarget_wireToNat (lws 0)
                  have hx : (U.program.lines g').wires x = wireCastLE g'.isLt.le u₀ := by
                    generalize U.program.lines g' = lk at hl x ⊢; subst hl; rfl
                  have hxl : x.val < 1 := x.isLt.trans_eq (by rw [hl])
                  have hx0 : (⟨0, by rw [hco]; decide⟩ :
                      Fin (signature.Arity (c.program.lines ⟨r, hrc⟩).op)) =
                      x.cast (congrArg signature.Arity hop_eq) :=
                    Fin.ext (by change 0 = x.val; omega)
                  rw [hx, hu₀_s, ite_eq_left hop2, hs0_eq, hx0]
                · have hop2 : opc ≠ 2 := fun h => by
                    by_cases hrc : r < c.size
                    · exact hc2 ⟨hrc, h⟩
                    · dsimp [opc, opcAt] at h; rw [dite_eq_right hrc] at h; omega
                  exact isGateSim_of_oneVar (.input ⟨0, hk⟩) (.inl true) (.inl false) (.inl false)
                    (by rw [hsim_g, hd, hstep3]
                        by_cases hrc : r < c.size
                        · rw [dite_eq_left hrc, ite_eq_right hop2]; rfl
                        · rw [dite_eq_right hrc]; rfl)
                    (fun x => by
                      generalize U.program.lines g' = lk at hl x ⊢; subst hl
                      fin_cases x; exact hu₀_s.trans (ite_eq_right hop2))
                    (by rw [hl]; intro _; rfl)
              · have hgr : (univRawGates k m S)[g'.val]'g'.isLt = .and (opBase + 3) a1w := by
                  rw [hrg, hbg]; simp only [hd, List.getElem_cons_succ, List.getElem_cons_zero]
                refine isGateSim_and_const_left hk (hop_sel 3 (by omega)).1 ha1_sim.1
                  (by rw [hlk, hgr]) (decide (3 = opc)) s0
                  (hop_sel 3 (by omega)).2 ha1_sim.2 ?_
                rw [hsim_g, hd, hstep4]
                by_cases he : opc = 3
                · rw [ite_eq_left he, ite_eq_left (decide_eq_true he.symm)]
                · rw [ite_eq_right he, ite_eq_right (mt of_decide_eq_true (Ne.symm he))]
              · have hgr : (univRawGates k m S)[g'.val]'g'.isLt = .and (opBase + 3) a2w := by
                  rw [hrg, hbg]; simp only [hd, List.getElem_cons_succ, List.getElem_cons_zero]
                refine isGateSim_and_const_left hk (hop_sel 3 (by omega)).1 ha2_sim.1
                  (by rw [hlk, hgr]) (decide (3 = opc)) s1
                  (hop_sel 3 (by omega)).2 ha2_sim.2 ?_
                rw [hsim_g, hd, hstep5]
                by_cases he : opc = 3
                · rw [ite_eq_left he, ite_eq_left (decide_eq_true he.symm)]
                · rw [ite_eq_right he, ite_eq_right (mt of_decide_eq_true (Ne.symm he))]
              · have hgr : (univRawGates k m S)[g'.val]'g'.isLt =
                    .and (n' + gs3 + 4) (n' + gs3 + 5) := by
                  rw [hrg, hbg]; simp only [hd, List.getElem_cons_succ, List.getElem_cons_zero]
                obtain ⟨u₁, hu₁, -⟩ := isSome_natToWire_of_lt (n := n') (g := g'.val)
                  (idx := n' + gs3 + 4) (by dsimp [gs3]; omega)
                obtain ⟨u₂, hu₂, -⟩ := isSome_natToWire_of_lt (n := n') (g := g'.val)
                  (idx := n' + gs3 + 5) (by dsimp [gs3]; omega)
                have hl : U.program.lines g' =
                    ⟨.and, ![wireCastLE g'.isLt.le u₁, wireCastLE g'.isLt.le u₂]⟩ := by
                  rw [hlk, hgr, rawGateToLine_and_of_eq hu₁ hu₂]
                  dsimp only [Line.mapWires]; congr 1; funext x; fin_cases x <;> rfl
                have hu₁_s : sim (wireCastLE g'.isLt.le u₁) =
                    if opc = 3 then s0 else .inl false :=
                  (hop_wire 4 (by omega) (by dsimp [gs3]; omega) u₁ hu₁).trans hstep4
                have hu₂_s : sim (wireCastLE g'.isLt.le u₂) =
                    if opc = 3 then s1 else .inl false :=
                  (hop_wire 5 (by omega) (by dsimp [gs3]; omega) u₂ hu₂).trans hstep5
                by_cases hc3 : ∃ hrc : r < c.size, opc = 3
                · obtain ⟨hrc, hop3⟩ := hc3
                  have hco : (c.program.lines ⟨r, hrc⟩).op = .and := by
                    dsimp [opc, opcAt] at hop3; rw [dite_eq_left hrc] at hop3
                    cases ho : (c.program.lines ⟨r, hrc⟩).op with
                    | const bv => cases bv <;> (rw [ho] at hop3; cases hop3)
                    | and => rfl
                    | _ => rw [ho] at hop3; cases hop3
                  have hop_eq : (U.program.lines g').op = (c.program.lines ⟨r, hrc⟩).op := by
                    rw [hl, hco]
                  refine isGateSim_of_preserve ⟨r, hrc⟩ hop_eq
                    (by rw [hsim_g, hd, hstep6, dite_eq_left hrc, ite_eq_left hop3]) fun x => ?_
                  have hargs_eq : s0 =
                    .inr (false, (c.program.lines ⟨r, hrc⟩).wires ⟨0, by rw [hco]; decide⟩) ∧
                      s1 = .inr (false, (c.program.lines ⟨r, hrc⟩).wires ⟨1,
                        by rw [hco]; decide⟩) := by
                    dsimp [s0, s1, i0, i1, i0At, i1At]; simp only [hrc, ↓reduceDIte]
                    generalize c.program.lines ⟨r, hrc⟩ = lk at hco ⊢
                    rcases lk with ⟨op, lws⟩; dsimp at hco; subst hco
                    exact ⟨hsimTarget_wireToNat (lws 0), hsimTarget_wireToNat (lws 1)⟩
                  have hxl : x.val < 2 := x.isLt.trans_eq (by rw [hl])
                  rcases (show x.val = 0 ∨ x.val = 1 by omega) with hx0 | hx1
                  · have hw : (U.program.lines g').wires x = wireCastLE g'.isLt.le u₁ := by
                      generalize U.program.lines g' = lk at hl x hx0 ⊢; subst hl
                      have : x = 0 := Fin.ext hx0; subst this; rfl
                    have hxc : (⟨0, by rw [hco]; decide⟩ :
                        Fin (signature.Arity (c.program.lines ⟨r, hrc⟩).op)) =
                        x.cast (congrArg signature.Arity hop_eq) :=
                      Fin.ext (by change 0 = x.val; omega)
                    rw [hw, hu₁_s, ite_eq_left hop3, hargs_eq.1, hxc]
                  · have hw : (U.program.lines g').wires x = wireCastLE g'.isLt.le u₂ := by
                      generalize U.program.lines g' = lk at hl x hx1 ⊢; subst hl
                      have : x = 1 := Fin.ext hx1; subst this; rfl
                    have hxc : (⟨1, by rw [hco]; decide⟩ :
                        Fin (signature.Arity (c.program.lines ⟨r, hrc⟩).op)) =
                        x.cast (congrArg signature.Arity hop_eq) :=
                      Fin.ext (by change 1 = x.val; omega)
                    rw [hw, hu₂_s, ite_eq_left hop3, hargs_eq.2, hxc]
                · have hop3 : opc ≠ 3 := fun h => by
                    by_cases hrc : r < c.size
                    · exact hc3 ⟨hrc, h⟩
                    · dsimp [opc, opcAt] at h; rw [dite_eq_right hrc] at h; omega
                  exact isGateSim_of_oneVar (.input ⟨0, hk⟩) (.inl false) (.inl false) (.inl false)
                    (by rw [hsim_g, hd, hstep6]
                        by_cases hrc : r < c.size
                        · rw [dite_eq_left hrc, ite_eq_right hop3]; rfl
                        · rw [dite_eq_right hrc]; rfl)
                    (fun x => by
                      generalize U.program.lines g' = lk at hl x ⊢; subst hl
                      fin_cases x
                      · exact hu₁_s.trans (ite_eq_right hop3)
                      · exact hu₂_s.trans (ite_eq_right hop3))
                    (by rw [hl]; intro _; rfl)
              · have hgr : (univRawGates k m S)[g'.val]'g'.isLt = .and (opBase + 4) a1w := by
                  rw [hrg, hbg]; simp only [hd, List.getElem_cons_succ, List.getElem_cons_zero]
                refine isGateSim_and_const_left hk (hop_sel 4 (by omega)).1 ha1_sim.1
                  (by rw [hlk, hgr]) (decide (4 = opc)) s0
                  (hop_sel 4 (by omega)).2 ha1_sim.2 ?_
                rw [hsim_g, hd, hstep7]
                by_cases he : opc = 4
                · rw [ite_eq_left he, ite_eq_left (decide_eq_true he.symm)]
                · rw [ite_eq_right he, ite_eq_right (mt of_decide_eq_true (Ne.symm he))]
              · have hgr : (univRawGates k m S)[g'.val]'g'.isLt = .and (opBase + 4) a2w := by
                  rw [hrg, hbg]; simp only [hd, List.getElem_cons_succ, List.getElem_cons_zero]
                refine isGateSim_and_const_left hk (hop_sel 4 (by omega)).1 ha2_sim.1
                  (by rw [hlk, hgr]) (decide (4 = opc)) s1
                  (hop_sel 4 (by omega)).2 ha2_sim.2 ?_
                rw [hsim_g, hd, hstep8]
                by_cases he : opc = 4
                · rw [ite_eq_left he, ite_eq_left (decide_eq_true he.symm)]
                · rw [ite_eq_right he, ite_eq_right (mt of_decide_eq_true (Ne.symm he))]
              · have hgr : (univRawGates k m S)[g'.val]'g'.isLt =
                    .or (n' + gs3 + 7) (n' + gs3 + 8) := by
                  rw [hrg, hbg]; simp only [hd, List.getElem_cons_succ, List.getElem_cons_zero]
                obtain ⟨u₁, hu₁, -⟩ := isSome_natToWire_of_lt (n := n') (g := g'.val)
                  (idx := n' + gs3 + 7) (by dsimp [gs3]; omega)
                obtain ⟨u₂, hu₂, -⟩ := isSome_natToWire_of_lt (n := n') (g := g'.val)
                  (idx := n' + gs3 + 8) (by dsimp [gs3]; omega)
                have hl : U.program.lines g' =
                    ⟨.or, ![wireCastLE g'.isLt.le u₁, wireCastLE g'.isLt.le u₂]⟩ := by
                  rw [hlk, hgr, rawGateToLine_or_of_eq hu₁ hu₂]
                  dsimp only [Line.mapWires]; congr 1; funext x; fin_cases x <;> rfl
                have hu₁_s : sim (wireCastLE g'.isLt.le u₁) =
                    if opc = 4 then s0 else .inl false :=
                  (hop_wire 7 (by omega) (by dsimp [gs3]; omega) u₁ hu₁).trans hstep7
                have hu₂_s : sim (wireCastLE g'.isLt.le u₂) =
                    if opc = 4 then s1 else .inl false :=
                  (hop_wire 8 (by omega) (by dsimp [gs3]; omega) u₂ hu₂).trans hstep8
                by_cases hc4 : ∃ hrc : r < c.size, opc = 4
                · obtain ⟨hrc, hop4⟩ := hc4
                  have hco : (c.program.lines ⟨r, hrc⟩).op = .or := by
                    dsimp [opc, opcAt] at hop4; rw [dite_eq_left hrc] at hop4
                    cases ho : (c.program.lines ⟨r, hrc⟩).op with
                    | const bv => cases bv <;> (rw [ho] at hop4; cases hop4)
                    | or => rfl
                    | _ => rw [ho] at hop4; cases hop4
                  have hop_eq : (U.program.lines g').op = (c.program.lines ⟨r, hrc⟩).op := by
                    rw [hl, hco]
                  refine isGateSim_of_preserve ⟨r, hrc⟩ hop_eq
                    (by rw [hsim_g, hd, hstep9, dite_eq_left hrc, ite_eq_left hop4]) fun x => ?_
                  have hargs_eq : s0 =
                    .inr (false, (c.program.lines ⟨r, hrc⟩).wires ⟨0, by rw [hco]; decide⟩) ∧
                      s1 = .inr (false, (c.program.lines ⟨r, hrc⟩).wires ⟨1,
                        by rw [hco]; decide⟩) := by
                    dsimp [s0, s1, i0, i1, i0At, i1At]; simp only [hrc, ↓reduceDIte]
                    generalize c.program.lines ⟨r, hrc⟩ = lk at hco ⊢
                    rcases lk with ⟨op, lws⟩; dsimp at hco; subst hco
                    exact ⟨hsimTarget_wireToNat (lws 0), hsimTarget_wireToNat (lws 1)⟩
                  have hxl : x.val < 2 := x.isLt.trans_eq (by rw [hl])
                  rcases (show x.val = 0 ∨ x.val = 1 by omega) with hx0 | hx1
                  · have hw : (U.program.lines g').wires x = wireCastLE g'.isLt.le u₁ := by
                      generalize U.program.lines g' = lk at hl x hx0 ⊢; subst hl
                      have : x = 0 := Fin.ext hx0; subst this; rfl
                    have hxc : (⟨0, by rw [hco]; decide⟩ :
                        Fin (signature.Arity (c.program.lines ⟨r, hrc⟩).op)) =
                        x.cast (congrArg signature.Arity hop_eq) :=
                      Fin.ext (by change 0 = x.val; omega)
                    rw [hw, hu₁_s, ite_eq_left hop4, hargs_eq.1, hxc]
                  · have hw : (U.program.lines g').wires x = wireCastLE g'.isLt.le u₂ := by
                      generalize U.program.lines g' = lk at hl x hx1 ⊢; subst hl
                      have : x = 1 := Fin.ext hx1; subst this; rfl
                    have hxc : (⟨1, by rw [hco]; decide⟩ :
                        Fin (signature.Arity (c.program.lines ⟨r, hrc⟩).op)) =
                        x.cast (congrArg signature.Arity hop_eq) :=
                      Fin.ext (by change 1 = x.val; omega)
                    rw [hw, hu₂_s, ite_eq_left hop4, hargs_eq.2, hxc]
                · have hop4 : opc ≠ 4 := fun h => by
                    by_cases hrc : r < c.size
                    · exact hc4 ⟨hrc, h⟩
                    · dsimp [opc, opcAt] at h; rw [dite_eq_right hrc] at h; omega
                  exact isGateSim_of_oneVar (.input ⟨0, hk⟩) (.inl false) (.inl false) (.inl false)
                    (by rw [hsim_g, hd, hstep9]
                        by_cases hrc : r < c.size
                        · rw [dite_eq_left hrc, ite_eq_right hop4]; rfl
                        · rw [dite_eq_right hrc]; rfl)
                    (fun x => by
                      generalize U.program.lines g' = lk at hl x ⊢; subst hl
                      fin_cases x
                      · exact hu₁_s.trans (ite_eq_right hop4)
                      · exact hu₂_s.trans (ite_eq_right hop4))
                    (by rw [hl]; intro _; rfl)
            · set off4 := off - (4 * (k + S) + 10)
              have hoff4 : off4 < 10 := by omega
              let gs4 := gs3 + 10
              let bws : List ℕ :=
                [n' + gs3, n' + gs3 + 1, n' + gs3 + 3, n' + gs3 + 6, n' + gs3 + 9]
              have hgs4_lt : gs4 + off4 < U.size := by
                have := g'.isLt; dsimp [gs4, gs3] at *; omega
              have hg_fin4 : g' = ⟨gs4 + off4, hgs4_lt⟩ :=
                Fin.ext (by dsimp [gs4, gs3]; omega)
              have hbg : (univGateBlock k m S r)[off]'(by simp [Lstep, hoff]) =
                  (muxGates opBase (n' + gs4) n' bws)[off4]'(by simp [bws, hoff4]) :=
                getElem_univGateBlock_muxOp k m S r off h3 hoff
              rw [hg_fin4]
              refine isGateSim_muxBlock (c' := U) (c := c) (sim := sim)
                hk opBase gs4 n' opc bws sOut
                (by simp [bws, hopc_lt]) off4 (by simp [bws, hoff4]) hgs4_lt
                (by rw [← hg_fin4]
                    exact hlk.trans (hmap_cast (congrArg Fin.val hg_fin4) _ _ (hrg.trans hbg)))
                (fun q hq hgq => by
                  have hq' : q < 10 := by simpa [bws] using hq
                  have heq' : gs4 + q = 1 + r * Lstep + (4 * (k + S) + 10 + q) := by
                    dsimp [gs4, gs3]; omega
                  have hf : (⟨gs4 + q, hgq⟩ : Fin U.size) = ⟨_, heq' ▸ hgq⟩ := Fin.ext heq'
                  rw [hf, hsim_step _ (by omega)]
                  dsimp [stepSim]
                  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
                    Nat.add_sub_cancel_left])
                (by dsimp [gs4, gs3]; omega) (hfw_sim hgs4_lt (by dsimp [gs4, gs3]; omega))
                (fun idx hidx => by
                  have hi5 : idx < 5 := by simpa [bws] using hidx
                  have hp' : opBase + idx < ℓ := by omega
                  exact ⟨by dsimp [n', gs4, gs3]; omega, fun u hu =>
                    (hdesc_sim hgs4_lt hp' u hu).trans (by
                      dsimp only [v, opBase, opc, opcAt]; rw [encodeCircuit_op c S hS hrS hi5])⟩)
                (fun idx hidx => by
                  have hi5 : idx < 5 := by simpa [bws] using hidx
                  rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 by omega)
                    with rfl | rfl | rfl | rfl | rfl <;>
                    (simp only [bws, List.getElem_cons_succ, List.getElem_cons_zero]
                     dsimp [gs4]; omega))
                (fun u hu => by
                  have hget_br (d : ℕ) (hd : d < 10)
                      (hu' : natToWire n' (gs4 + off4) (n' + gs3 + d) = some u) :
                      sim (wireCastLE hgs4_lt.le u) = stepSim r (4 * (k + S) + d) := by
                    have h1' : ¬(n' + gs3 + d < n') := by omega
                    have h2' : n' + gs3 + d - n' < gs4 + off4 := by dsimp [gs4]; omega
                    rw [natToWire_of_ge_of_lt h1' h2', Option.some.injEq] at hu'; subst hu'
                    have hf : (⟨n' + gs3 + d - n', by omega⟩ : Fin U.size) =
                        ⟨1 + r * Lstep + (4 * (k + S) +
                          d), by dsimp [gs4, gs3] at hgs4_lt; omega⟩ :=
                      Fin.ext (by dsimp [gs3]; omega)
                    rw [wireCastLE_gate]; dsimp only [Fin.castLE]; rw [hf]
                    exact hsim_step (4 * (k + S) + d) (by omega) _
                  rcases (show opc = 0 ∨ opc = 1 ∨ opc = 2 ∨ opc = 3 ∨ opc = 4 by omega)
                    with ho | ho | ho | ho | ho
                  · simp only [bws, ho, List.getElem_cons_zero] at hu
                    rw [hget_br 0 (by omega) hu, hstep0]; dsimp only [sOut]
                    by_cases hrc : r < c.size
                    · rw [dite_eq_left hrc, dite_eq_left hrc, ite_eq_left ho]
                    · rw [dite_eq_right hrc, dite_eq_right hrc]
                  · simp only [bws, ho, List.getElem_cons_succ, List.getElem_cons_zero] at hu
                    rw [hget_br 1 (by omega) hu, hstep1]; dsimp only [sOut]
                    by_cases hrc : r < c.size
                    · rw [dite_eq_left hrc, dite_eq_left hrc, ite_eq_left ho]
                    · have : opc = 0 := dite_eq_right hrc; omega
                  · simp only [bws, ho, List.getElem_cons_succ, List.getElem_cons_zero] at hu
                    rw [hget_br 3 (by omega) hu, hstep3]; dsimp only [sOut]
                    by_cases hrc : r < c.size
                    · rw [dite_eq_left hrc, dite_eq_left hrc, ite_eq_left ho]
                    · have : opc = 0 := dite_eq_right hrc; omega
                  · simp only [bws, ho, List.getElem_cons_succ, List.getElem_cons_zero] at hu
                    rw [hget_br 6 (by omega) hu, hstep6]; dsimp only [sOut]
                    by_cases hrc : r < c.size
                    · rw [dite_eq_left hrc, dite_eq_left hrc, ite_eq_left ho]
                    · have : opc = 0 := dite_eq_right hrc; omega
                  · simp only [bws, ho, List.getElem_cons_succ, List.getElem_cons_zero] at hu
                    rw [hget_br 9 (by omega) hu, hstep9]; dsimp only [sOut]
                    by_cases hrc : r < c.size
                    · rw [dite_eq_left hrc, dite_eq_left hrc, ite_eq_left ho]
                    · have : opc = 0 := dite_eq_right hrc; omega)
      · set p := g'.val - (1 + S * Lstep)
        have hpm : p < m * (2 * (k + S)) := by
          have hu := g'.isLt.trans_eq (size_univEvalCircuit k m S hk)
          change g'.val < 1 + S * Lstep + m * (2 * (k + S)) at hu
          omega
        set j := p / (2 * (k + S)); set off := p % (2 * (k + S))
        have hjm : j < m := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
        have hoff : off < 2 * (k + S) := Nat.mod_lt p (by omega)
        let gso := 1 + S * Lstep + j * (2 * (k + S))
        have hgso_lt : gso + off < U.size := by
          have : j * (2 * (k + S)) + off = p := by rw [mul_comm]; exact Nat.div_add_mod p _
          have := g'.isLt; dsimp [gso]; omega
        have hg_fino : g' = ⟨gso + off, hgso_lt⟩ := Fin.ext (by
          have : j * (2 * (k + S)) + off = p := by rw [mul_comm]; exact Nat.div_add_mod p _
          dsimp [gso]; omega)
        have hrg : (univRawGates k m S)[g'.val]'g'.isLt =
            (univOutBlock k m S j)[off]'(by simp [hoff]) := by
          have h1l : (((List.range S).map (univGateBlock k m S)).flatten).length = S * Lstep := by
            have aux : ∀ t, (((List.range t).map (univGateBlock k m S)).flatten).length =
                t * Lstep := by
              intro t; induction t with
              | zero => simp
              | succ t ih => rw [List.range_succ, List.map_append, List.flatten_append,
                  List.length_append, ih]; simp [Lstep, Nat.succ_mul]
            exact aux S
          refine (hget_cons _ _ g'.val (g'.val - 1) g'.isLt (by omega)).trans ?_
          rw [List.getElem_append_right (by rw [h1l]; omega)]
          simp only [h1l, show g'.val - 1 - S * Lstep = p by omega]
          exact getElem_flatten_range (univOutBlock k m S) (2 * (k + S)) (by omega)
            (length_univOutBlock k m S) m p hpm
        let jf : Fin m := ⟨j, hjm⟩
        let i0 := wireToNat (c.outputs jf)
        have hi0 : i0 < k + S := (wireToNat_lt (c.outputs jf)).trans_le (by omega)
        let selBase := S * univGateDescStride k S + j * (k + S)
        let ws := univAvailWires k m S S
        have hbgo : (univOutBlock k m S j)[off]'(by simp [hoff]) =
            (muxGates selBase (n' + gso) n' ws)[off]'(by simp [ws, hoff]) :=
          getElem_univOutBlock k m S j off hoff
        rw [hg_fino]
        refine isGateSim_muxBlock (c' := U) (c := c) (sim := sim)
          hk selBase gso n' i0 ws (.inr (false, c.outputs jf))
          (by simp [ws, hi0]) off (by simp [ws, hoff]) hgso_lt
          (by rw [← hg_fino]
              exact hlk.trans (hmap_cast (congrArg Fin.val hg_fino) _ _ (hrg.trans hbgo)))
          (fun q hq hgq => by
            have hq' : q < 2 * (k + S) := by simpa [ws] using hq
            have hd : (j * (2 * (k + S)) + q) / (2 * (k + S)) = j := by
              rw [mul_comm j, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hq', add_zero]
            have hm : (j * (2 * (k + S)) + q) % (2 * (k + S)) = q := by
              rw [mul_comm j, Nat.mul_add_mod, Nat.mod_eq_of_lt hq']
            simp only [sim, show gso + q ≠ 0 by dsimp [gso]; omega, ↓reduceIte,
              show ¬(gso + q < 1 + S * Lstep) by dsimp [gso]; omega,
              show gso + q - (1 + S * Lstep) = j * (2 * (k + S)) + q by dsimp [gso]; omega,
              hd, hm, hjm, ↓reduceDIte, jf, i0])
          (by dsimp [gso]; omega) (hfw_sim hgso_lt (by dsimp [gso]; omega))
          (fun idx hidx => by
            have hi' : idx < k + S := by simpa [ws] using hidx
            have hp' : selBase + idx < ℓ := add_mul_lt_univDescLen hjm hi'
            exact ⟨by dsimp [n', gso]; omega, fun u hu =>
              (hdesc_sim hgso_lt hp' u hu).trans (by
                dsimp only [v, selBase]; rw [encodeCircuit_out c S hS jf hi'])⟩)
          (fun idx hidx => (univAvailWires_lt k m S S idx (by simpa [ws] using hidx)).trans_le
            (by dsimp [n', ℓ, gso, Lstep]; omega))
          (fun u hu => (havail_sim hgso_lt S i0 le_rfl hi0 (by dsimp [gso]; omega)
            (by rw [min_eq_right hS]; exact wireToNat_lt (c.outputs jf)) u hu).trans
            (hsimTarget_wireToNat (c.outputs jf)))
  have houts : IsOutputSim U c sim b b := by
    intro j
    refine Or.inr (Or.inl ⟨?_, rfl⟩)
    have hjo : j.val < (univRawOuts k m S).length := by simp
    have hout_idx : (univRawOuts k m S)[j.val] =
        n' + (1 + S * Lstep + j.val * (2 * (k + S)) + (2 * (k + S) - 1)) := by
      have h0 := getElem_univRawOuts_of_pos (m := m) (k := k) (S := S) (j := j.val)
        (by omega) j.isLt
      have h2pos : 1 ≤ 2 * (k + S) := by omega
      rw [h0, Nat.succ_mul]
      change (n' + 1 + S * Lstep) + (j.val * (2 * (k + S)) + 2 * (k + S)) - 1 = _; omega
    have hg_lt : 1 + S * Lstep + j.val * (2 * (k + S)) + (2 * (k + S) - 1) < U.size := by
      rw [size_univEvalCircuit]
      have := Nat.mul_le_mul_right (2 * (k + S)) j.isLt; rw [Nat.succ_mul] at this
      dsimp [Lstep]; omega
    have hnw : natToWire n' U.size (univRawOuts k m S)[j.val] =
        some (.gate ⟨1 + S * Lstep + j.val * (2 * (k + S)) + (2 * (k + S) - 1), hg_lt⟩) := by
      rw [hout_idx, natToWire_of_ge_of_lt (by omega) (by omega)]
      congr 2; exact Fin.ext (by dsimp; omega)
    have huo : U.outputs j =
        .gate ⟨1 + S * Lstep + j.val * (2 * (k + S)) + (2 * (k + S) - 1), hg_lt⟩ := by
      change (natToWire n' (univRawGates k m S).length (univRawOuts k m S)[j.val]).getD _ = _
      change (natToWire n' U.size (univRawOuts k m S)[j.val]).getD _ = _
      rw [hnw]; rfl
    rw [huo]
    have hd : (j.val * (2 * (k + S)) + (2 * (k + S) - 1)) / (2 * (k + S)) = j.val := by
      rw [mul_comm j.val, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), add_zero]
    have hm : (j.val * (2 * (k + S)) + (2 * (k + S) - 1)) % (2 * (k + S)) = 2 * (k + S) - 1 := by
      rw [mul_comm j.val, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have hi0 : wireToNat (c.outputs j) ≤ k + S - 1 := by
      have := (wireToNat_lt (c.outputs j)).trans_le (show k + c.size ≤ k + S by omega); omega
    simp only [sim, show 1 + S * Lstep + j.val * (2 * (k + S)) + (2 * (k + S) - 1) ≠ 0 by omega,
      show ¬(1 + S * Lstep + j.val * (2 * (k + S)) + (2 * (k + S) - 1) < 1 + S * Lstep) by omega,
      show 1 + S * Lstep + j.val * (2 * (k + S)) + (2 * (k + S) - 1) - (1 + S * Lstep) =
        j.val * (2 * (k + S)) + (2 * (k + S) - 1) by omega,
      hd, hm, j.isLt, ↓reduceDIte, muxGateSim, show (2 * (k + S) - 1) % 2 ≠ 0 by omega,
      show (2 * (k + S) - 1) / 2 = k + S - 1 by omega, hi0, ↓reduceIte]
  obtain ⟨steps, hrun, hst_len⟩ := hred U c sim b b hgates houts
  let restPairs := (wireSimPairs sim).drop ℓ
  have hsubst_eq : ((tauFormula 0 U b).subst (initConstSubst v)).subst (listSubst restPairs) =
      (tauFormula 0 U b).subst (listSubst (wireSimPairs sim)) := by
    rw [subst_subst]
    refine subst_congr_atoms fun a ha => ?_
    have ha_lt : a < n' + U.size := by
      have := (mem_Ico.1 (formulaAtoms_tauFormula_subset 0 U b ha)).2; omega
    by_cases haℓ : a < ℓ
    · rw [initConstSubst_of_lt v haℓ]
      have hbc : (boolConst (v ⟨a, haℓ⟩)).subst (listSubst restPairs) =
          wireSimFormula (n := k) (g := c.size) (.inl (v ⟨a, haℓ⟩)) := by cases v ⟨a, haℓ⟩ <;> rfl
      have hwp := listSubst_wireSimPairs sim (.input ⟨a, by dsimp [n']; omega⟩)
      simp only [stdWireAtom_input, zero_add, sim, haℓ, ↓reduceDIte] at hwp
      exact hbc.trans hwp.symm
    · rw [initConstSubst_of_ge v haℓ, subst_var]
      have hsplit : wireSimPairs sim =
          ((List.finRange n').take ℓ).map (fun i => (i.val, wireSimFormula (sim (.input i)))) ++
            restPairs :=
        wireSimPairs_drop_of_le (by dsimp [n']; omega) sim
      have hnone : (((List.finRange n').take ℓ).map
          (fun i => (i.val, wireSimFormula (sim (.input i))))).find? (fun kv => kv.1 == a) =
          none := by
        rw [List.find?_eq_none]; rintro _ hmem
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hmem
        obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.1 hi
        simp only [List.length_take, List.length_finRange, List.getElem_take,
          List.getElem_finRange] at hidx hget
        have : i.val < ℓ := by rw [← hget]; dsimp; omega
        simp [show i.val ≠ a by omega]
      rw [hsplit, listSubst_append_of_find?_eq_none hnone]
  have hrest_le : (encList (encPair encNat encFormula) restPairs).length ≤
      (encList (encPair encNat encFormula) (wireSimPairs sim)).length := by
    have hdrop : ∀ (k0 : ℕ) (l : List (ℕ × Formula)),
        (encList (encPair encNat encFormula) (l.drop k0)).length ≤
          (encList (encPair encNat encFormula) l).length := by
      intro k0; induction k0 with
      | zero => intro _; exact le_rfl
      | succ k0 ih =>
        intro l; cases l with
        | nil => simp
        | cons x xs =>
          refine (ih xs).trans ?_
          simp only [encList_cons, List.length_append, length_frame]; omega
    exact hdrop ℓ (wireSimPairs sim)
  refine ⟨restPairs, steps, by rwa [hsubst_eq], ?_⟩
  have hp0 := hrest_le.trans (length_wireSimPairs_le sim)
  have hUsz : U.size = 1 + S * univStepGateCount k S + m * (2 * (k + S)) :=
    size_univEvalCircuit k m S hk
  rw [hUsz] at hp0 hst_len
  exact (Nat.add_le_add hp0 hst_len).trans (univSpec_poly_bound C₀ k m S c.size hS)

end CslibFrontier.ProofComplexity
