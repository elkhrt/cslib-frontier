module

public import CslibFrontier.Computability.Circuit.Boolean.DepthClasses
public import CslibFrontier.Computability.Circuit.Boolean.Unbounded.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Partial
public import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Computability.Circuit.Encoding.Check
import CslibFrontier.Computability.Circuit.Encoding.Layer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# `ACC^k` circuits: fan-in compression, strict decoding, and polynomial-time evaluation

Defines the nonuniform circuit hierarchy `ACC k = ⋃ q ≥ 2, ACMod q k` (matching
`ACC⁰ = ⋃ q ≥ 2, AC0Mod q` at `k = 0`), proves fan-in compression for `MOD_q` circuits
(showing every gate-count-bounded `AC^k[q]` circuit has an equivalent circuit of the same
gate count, no larger depth, and polynomially bounded `Unbounded.encExtCircuit 1` encoding),
and establishes polynomial-time strict decoding (`PartialDecoder`), evaluation, and depth
checking for `Unbounded.extSignature` circuits.

## Main definitions

* `CslibFrontier.Circuits.Boolean.ACC`: the nonuniform circuit class `ACC^k = ⋃ q ≥ 2, AC^k[q]`.
* `CslibFrontier.Circuits.Boolean.decExtCircuit`: strict polynomial-time `PartialDecoder` for
  `Unbounded.encExtCircuit 1`.
* `CslibFrontier.Circuits.Boolean.evalRawExtCircuit`: polynomial-time evaluator for encoded
  `Unbounded.extSignature` circuits under `MOD_q` gates.
* `CslibFrontier.Circuits.Boolean.checkACMod`: polynomial-time checker verifying that a bit string
  encodes a valid `n`-input `Unbounded.extSignature` circuit of depth at most
  `c * (⌊log₂ n⌋ + 1)^k`.

## Main results

* `CslibFrontier.Circuits.Boolean.ACC_zero`: `ACC 0 = ⋃ q ≥ 2, AC0Mod q`.
* `CslibFrontier.Circuits.Boolean.exists_bounded_encExtCircuit_of_ACMod`: fan-in compression yields
  polynomially bounded `Unbounded.encExtCircuit 1` encodings for every `L ∈ ACMod q k` (`q ≥ 2`).
* `CslibFrontier.Circuits.Boolean.computableInPolyTime_evalRawExtCircuit`,
  `CslibFrontier.Circuits.Boolean.evalRawExtCircuit_encExtCircuit`: polynomial-time evaluation and
  semantic soundness on encoded circuits.
* `CslibFrontier.Circuits.Boolean.computableInPolyTime_checkACMod`,
  `CslibFrontier.Circuits.Boolean.checkACMod_eq_true_iff`: polynomial-time validity and depth
  checking.
-/

public section

namespace CslibFrontier.Circuits.Boolean

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded
open Turing.MultiTapeTM

/-! ### Nonuniform `ACC^k` hierarchy -/

/-- **Nonuniform `ACC^k`**: languages decided by polynomial-size circuits of depth
`O((⌊log₂ n⌋ + 1)^k)` over negation, unbounded fan-in conjunction and disjunction, and
unbounded fan-in `MOD_q` gates for some fixed modulus `q ≥ 2`. -/
def ACC (k : ℕ) : Set (Language Bool) :=
  ⋃ q ≥ 2, ACMod q k

/-- Membership characterization for `ACC k`. -/
theorem mem_ACC_iff {k : ℕ} {L : Language Bool} :
    L ∈ ACC k ↔ ∃ q ≥ 2, L ∈ ACMod q k := by
  simp only [ACC, Set.mem_iUnion, exists_prop]

/-- At `k = 0`, `ACC 0` coincides with `ACC⁰ = ⋃ q ≥ 2, AC0Mod q`. -/
theorem ACC_zero : ACC 0 = ⋃ q ≥ 2, AC0Mod q := by
  ext L
  simp only [ACC, Set.mem_iUnion, exists_prop, ACMod_zero]

/-- `ACC` is monotone in the polylogarithmic depth exponent `k`. -/
theorem ACC_mono {i j : ℕ} (hij : i ≤ j) : ACC i ⊆ ACC j := by
  intro L hL
  obtain ⟨q, hq, hLq⟩ := mem_ACC_iff.mp hL
  exact mem_ACC_iff.mpr ⟨q, hq, ACMod_mono q hij hLq⟩

/-- `AC^k ⊆ ACC^k` for every `k : ℕ`. -/
theorem AC_subset_ACC (k : ℕ) : AC k ⊆ ACC k := fun _ hL ↦
  mem_ACC_iff.mpr ⟨2, le_rfl, AC_subset_ACMod 2 k hL⟩

private theorem weight_comp_finProdFinEquiv_fst {m k : ℕ} (x : Fin m → Bool) :
    (Finset.univ.filter fun j : Fin (m * k) ↦ x (finProdFinEquiv.symm j).1 = true).card =
      (Finset.univ.filter fun i : Fin m ↦ x i = true).card * k := by
  have h1 : ∀ {n : ℕ} (f : Fin n → Bool),
      (Finset.univ.filter fun i : Fin n ↦ f i = true).card = ∑ i : Fin n, (f i).toNat := by
    intro n f
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    cases f i <;> rfl
  rw [h1, h1, Equiv.sum_comp finProdFinEquiv.symm (fun p : Fin m × Fin k ↦ (x p.1).toNat),
    Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ ↦ Nat.mul_comm _ _

private def modMulSimCircuit (m : ℕ) :
    (op : ExtOp) → Circuit extSignature (extSignature.Arity op) 1
  | .ac op => Circuit.oneGate (σ := extSignature) (.ac op) id
  | .gate r => Circuit.oneGate (σ := extSignature) (.gate (r * m))
      fun j ↦ (finProdFinEquiv.symm j).1

/-- Divisibility monotonicity for `AC^k[q]`: if `q ∣ q'` and `0 < q'`, then
`ACMod q k ⊆ ACMod q' k`. -/
theorem ACMod_subset_ACMod_of_dvd {q q' : ℕ} (hq' : 0 < q') (hdvd : q ∣ q') (k : ℕ) :
    ACMod q k ⊆ ACMod q' k := by
  obtain ⟨m, rfl⟩ := hdvd
  have hm : 0 < m := Nat.pos_of_mul_pos_left hq'
  refine DepthClass.subset_of_simulation (b := 1) (c := 1) fun op ↦
    ⟨modMulSimCircuit m op, ?_, ?_, ?_⟩
  · intro x
    funext o
    rw [Subsingleton.elim o 0]
    cases op with
    | ac op => rfl
    | gate r =>
      simp only [modMulSimCircuit, Circuit.eval_oneGate, single, extInterpretation_gate, modGate,
        weight_comp_finProdFinEquiv_fst, Nat.mul_mod_mul_right, ne_eq, mul_eq_zero, hm.ne',
        or_false]
  · cases op <;> simp [modMulSimCircuit]
  · cases op <;> simp [modMulSimCircuit]

/-! ### Fan-in compression for `MOD_q` circuits -/

/-- Reduce multiplicities in a wire list modulo `q`, keeping every distinct wire `w` repeated
`args.count w % q` times. -/
private def compressArgs (q : ℕ) (args : List ℕ) : List ℕ :=
  args.dedup.flatMap fun w ↦ List.replicate (args.count w % q) w

private theorem mem_compressArgs_subset {q : ℕ} {args : List ℕ} {w : ℕ}
    (hw : w ∈ compressArgs q args) : w ∈ args := by
  simp only [compressArgs, List.mem_flatMap, List.mem_replicate] at hw
  obtain ⟨u, hu, -, rfl⟩ := hw
  exact List.mem_dedup.mp hu

private theorem length_compressArgs_le {q n : ℕ} {args : List ℕ} (hq : 0 < q)
    (hargs : ∀ w ∈ args, w < n) : (compressArgs q args).length ≤ q * n := by
  have hdedup_le : args.dedup.length ≤ n := by
    have hsub : args.dedup.toFinset ⊆ Finset.range n := fun w hw ↦
      Finset.mem_range.mpr (hargs w (List.mem_dedup.mp (List.mem_toFinset.mp hw)))
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup (List.nodup_dedup args), Finset.card_range] at hcard
    exact hcard
  rw [compressArgs, List.length_flatMap]
  have hsum : (args.dedup.map fun w ↦ (List.replicate (args.count w % q) w).length).sum ≤
      args.dedup.length * q := by
    have hbound : ∀ x ∈ args.dedup.map fun w ↦ (List.replicate (args.count w % q) w).length,
        x ≤ q := by
      intro x hx
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx
      rw [List.length_replicate]
      exact (Nat.mod_lt _ hq).le
    simpa [smul_eq_mul] using List.sum_le_length_nsmul _ q hbound
  exact hsum.trans (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left q hdedup_le)

private theorem length_filter_list_eq_sum_count {α : Type*} [DecidableEq α]
    (l : List α) (p : α → Bool) :
    (l.filter p).length = (l.dedup.map fun w ↦ if p w then l.count w else 0).sum := by
  have hnodup : l.dedup.Nodup := List.nodup_dedup l
  have hsub : ∀ x ∈ l, x ∈ l.dedup := fun x hx ↦ List.mem_dedup.mpr hx
  revert hnodup hsub
  generalize l.dedup = u
  intro hnodup hsub
  induction l with
  | nil =>
    simp only [List.filter_nil, List.length_nil, List.count_nil, ite_self]
    induction u with
    | nil => rfl
    | cons _ _ _ => simp
  | cons a l ih =>
    have hsub_l : ∀ x ∈ l, x ∈ u := fun x hx ↦ hsub x (List.mem_cons_of_mem a hx)
    have ha_u : a ∈ u := hsub a (List.mem_cons_self ..)
    have hcount (w : α) : (a :: l).count w = (if w = a then 1 else 0) + l.count w := by
      rw [List.count_cons, Nat.add_comm]
      by_cases hwa : w = a
      · simp [hwa]
      · simp [hwa, Ne.symm hwa]
    have hmap_eq : (u.map fun w ↦ if p w then (a :: l).count w else 0).sum =
        (if p a then 1 else 0) + (u.map fun w ↦ if p w then l.count w else 0).sum := by
      clear ih hsub hsub_l
      induction u with
      | nil => simp at ha_u
      | cons b u ihu =>
        rw [List.nodup_cons] at hnodup
        rcases List.mem_cons.mp ha_u with rfl | hau
        · simp only [List.map_cons, List.sum_cons, hcount]
          have hrest :
              (u.map fun w ↦ if p w then (if w = a then 1 else 0) + l.count w else 0) =
              u.map fun w ↦ if p w then l.count w else 0 := by
            apply List.map_congr_left
            intro w hw
            have hwa : w ≠ a := fun h ↦ hnodup.1 (h ▸ hw)
            simp [hwa]
          rw [hrest]
          cases p a
          · simp
          · simp
            omega
        · have hba : b ≠ a := fun h ↦ hnodup.1 (h ▸ hau)
          simp only [List.map_cons, List.sum_cons, hcount b, hba, ↓reduceIte, zero_add]
          rw [ihu hnodup.2 hau]
          omega
    rw [hmap_eq, ← ih hsub_l, List.filter_cons]
    cases p a
    · simp
    · simp
      omega

private theorem sum_map_mod_eq {α : Type*} (l : List α) (f : α → ℕ) (q : ℕ) :
    (l.map fun x ↦ f x % q).sum % q = (l.map f).sum % q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.add_mod, ih, Nat.mod_mod, ← Nat.add_mod]

private theorem length_filter_compressArgs_mod (q : ℕ) (args : List ℕ) (p : ℕ → Bool) :
    ((compressArgs q args).filter p).length % q = (args.filter p).length % q := by
  rw [length_filter_list_eq_sum_count args p, compressArgs, List.filter_flatMap,
    List.length_flatMap]
  have hmap :
      (args.dedup.map fun w ↦ ((List.replicate (args.count w % q) w).filter p).length) =
      args.dedup.map fun w ↦ (if p w then args.count w else 0) % q := by
    apply List.map_congr_left
    intro w _
    simp only [List.filter_replicate]
    cases p w <;> simp
  rw [hmap, sum_map_mod_eq]

private theorem card_fin_filter_eq_length_filter (l : List ℕ) (p : ℕ → Bool) :
    (Finset.univ.filter fun i : Fin l.length ↦ p l[i.val] = true).card = (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    change (Finset.univ.filter fun i : Fin (l.length + 1) ↦ p (a :: l)[i.val] = true).card = _
    rw [List.filter_cons, Finset.card_filter, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
      ← Finset.card_filter, ih]
    by_cases h : p a = true <;> simp [h, Nat.add_comm]

/-- Compress one gate of an `Unbounded.extSignature` circuit modulo `q`. -/
private def compressGate (q : ℕ) (g : ExtOp × List ℕ) : ExtOp × List ℕ :=
  match g.1 with
  | .ac .not => g
  | .ac (.and _) => (.ac (.and g.2.dedup.length), g.2.dedup)
  | .ac (.or _) => (.ac (.or g.2.dedup.length), g.2.dedup)
  | .gate _ => (.gate (compressArgs q g.2).length, compressArgs q g.2)

private theorem mem_compressGate_subset {q : ℕ} {g : ExtOp × List ℕ} {w : ℕ}
    (hw : w ∈ (compressGate q g).2) : w ∈ g.2 := by
  rcases g with ⟨op, args⟩
  cases op with
  | ac op' =>
    cases op' with
    | not => exact hw
    | and _ => exact List.mem_dedup.mp hw
    | or _ => exact List.mem_dedup.mp hw
  | gate _ => exact mem_compressArgs_subset hw

private theorem compressGate_arity (q : ℕ) {g : ExtOp × List ℕ}
    (harity : g.2.length = extSignature.Arity g.1) :
    (compressGate q g).2.length = extSignature.Arity (compressGate q g).1 := by
  rcases g with ⟨op, args⟩
  cases op with
  | ac op' =>
    cases op' with
    | not => simpa [compressGate] using harity
    | and _ => simp [compressGate]
    | or _ => simp [compressGate]
  | gate _ => rfl

private theorem compressGate_isCodeFrom {q n : ℕ} {gates : List (ExtOp × List ℕ)}
    (h : Program.IsCodeFrom extSignature n 0 gates) :
    Program.IsCodeFrom extSignature n 0 (gates.map (compressGate q)) := by
  refine Program.isCodeFrom_of_getElem fun j hj ↦ ?_
  have hj' : j < gates.length := by simpa using hj
  obtain ⟨harity, hlt⟩ := h.getElem j hj'
  simp only [List.getElem_map]
  exact ⟨compressGate_arity q harity, fun i hi ↦ hlt i (mem_compressGate_subset hi)⟩

private theorem evalCode_compressGates (q : ℕ) (x : List Bool) {gates : List (ExtOp × List ℕ)}
    (h : Program.IsCodeFrom extSignature x.length 0 gates) :
    evalCode (extInterpretation (modGate q)) false x (gates.map (compressGate q)) =
      evalCode (extInterpretation (modGate q)) false x gates := by
  induction gates using List.reverseRecOn with
  | nil => rfl
  | append_singleton gates g ih =>
    rw [Program.isCodeFrom_append] at h
    have ih' := ih h.1
    obtain ⟨harity, -⟩ := h.2.1
    rw [List.map_append, List.map_singleton, evalCode_append_singleton, evalCode_append_singleton,
      ih']
    congr 2
    set vals := evalCode (extInterpretation (modGate q)) false x gates
    rcases g with ⟨op, args⟩
    cases op with
    | ac op' =>
      cases op' with
      | not => rfl
      | and m =>
        have hlen : args.length = m := by simpa [ExtOp.arity, Op.arity] using harity
        simp only [compressGate, extInterpretation_ac, interpretation_and, decide_eq_decide]
        constructor
        · intro hall j
          have hlt : j.val < args.length := j.isLt.trans_eq hlen.symm
          have hmem : args[j.val] ∈ args.dedup := List.mem_dedup.mpr (List.getElem_mem hlt)
          obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hmem
          have h1 := hall ⟨i, hi⟩
          simp only [List.getElem?_eq_getElem hi, Option.elim_some, heq] at h1
          simpa only [List.getElem?_eq_getElem hlt, Option.elim_some] using h1
        · intro hall i
          have hmem : args.dedup[i.val] ∈ args := List.mem_dedup.mp (List.getElem_mem i.isLt)
          obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hmem
          have h1 := hall ⟨j, hlen ▸ hj⟩
          simp only [List.getElem?_eq_getElem hj, Option.elim_some, heq] at h1
          simpa only [List.getElem?_eq_getElem i.isLt, Option.elim_some] using h1
      | or m =>
        have hlen : args.length = m := by simpa [ExtOp.arity, Op.arity] using harity
        simp only [compressGate, extInterpretation_ac, interpretation_or, decide_eq_decide]
        constructor
        · rintro ⟨i, hi⟩
          have hmem : args.dedup[i.val] ∈ args := List.mem_dedup.mp (List.getElem_mem i.isLt)
          obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hmem
          refine ⟨⟨j, hlen ▸ hj⟩, ?_⟩
          simp only [List.getElem?_eq_getElem i.isLt, Option.elim_some, ← heq] at hi
          simpa only [List.getElem?_eq_getElem hj, Option.elim_some] using hi
        · rintro ⟨j, hj⟩
          have hlt : j.val < args.length := j.isLt.trans_eq hlen.symm
          have hmem : args[j.val] ∈ args.dedup := List.mem_dedup.mpr (List.getElem_mem hlt)
          obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hmem
          refine ⟨⟨i, hi⟩, ?_⟩
          simp only [List.getElem?_eq_getElem hlt, Option.elim_some, ← heq] at hj
          simpa only [List.getElem?_eq_getElem hi, Option.elim_some] using hj
    | gate m =>
      have hlen : m = args.length := by simpa [ExtOp.arity] using harity.symm
      simp only [compressGate, extInterpretation_gate, modGate, decide_eq_decide]
      have hcard_lhs :
          (Finset.univ.filter fun i : Fin (compressArgs q args).length ↦
            (compressArgs q args)[i.val]?.elim false (vals.getD · false) = true).card =
            ((compressArgs q args).filter fun w ↦ vals.getD w false).length := by
        rw [← card_fin_filter_eq_length_filter]
        congr 1
        ext i
        simp
      have hcard_rhs :
          (Finset.univ.filter fun i : Fin m ↦
            args[i.val]?.elim false (vals.getD · false) = true).card =
            (args.filter fun w ↦ vals.getD w false).length := by
        subst hlen
        rw [← card_fin_filter_eq_length_filter]
        congr 1
        ext i
        simp
      rw [hcard_lhs, hcard_rhs, length_filter_compressArgs_mod]

private theorem evalCode_depth_compressGates_le (q n : ℕ) {gates : List (ExtOp × List ℕ)}
    (h : Program.IsCodeFrom extSignature n 0 gates) :
    ∀ w,
      (evalCode (depthInterpretation (σ := extSignature) 1) 0 (List.replicate n 0)
        (gates.map (compressGate q))).getD w 0 ≤
      (evalCode (depthInterpretation (σ := extSignature) 1) 0
        (List.replicate n 0) gates).getD w 0 := by
  induction gates using List.reverseRecOn with
  | nil => intro w; exact le_rfl
  | append_singleton gates g ih =>
    rw [Program.isCodeFrom_append] at h
    have ih' := ih h.1
    obtain ⟨harity, -⟩ := h.2.1
    set dL := evalCode (depthInterpretation (σ := extSignature) 1) 0 (List.replicate n 0)
      (gates.map (compressGate q))
    set dR := evalCode (depthInterpretation (σ := extSignature) 1) 0 (List.replicate n 0) gates
    have hlenL : dL.length = n + gates.length := by simp [dL, length_evalCode]
    have hlenR : dR.length = n + gates.length := by simp [dR, length_evalCode]
    intro w
    rw [List.map_append, List.map_singleton, evalCode_append_singleton, evalCode_append_singleton]
    rcases lt_trichotomy w (n + gates.length) with hlt | rfl | hgt
    · rw [List.getD_append _ _ _ _ (by rw [hlenL]; exact hlt),
        List.getD_append _ _ _ _ (by rw [hlenR]; exact hlt)]
      exact ih' w
    · rw [List.getD_append_right _ _ _ _ (by rw [hlenL]),
        List.getD_append_right _ _ _ _ (by rw [hlenR]), hlenL, hlenR, Nat.sub_self]
      simp only [List.getD_cons_zero, depthInterpretation, Fin.foldl_max_eq_max_sup, Nat.zero_max,
        Pi.one_apply]
      apply Nat.add_le_add_right
      apply Finset.sup_le
      intro a _
      have hga := compressGate_arity q harity
      have ha_lt : a.val < (compressGate q g).2.length := a.isLt.trans_eq hga.symm
      rw [List.getElem?_eq_getElem ha_lt, Option.elim_some]
      have hmem : (compressGate q g).2[a.val] ∈ g.2 :=
        mem_compressGate_subset (List.getElem_mem ha_lt)
      obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hmem
      have hle_sup := Finset.le_sup (f := fun k : Fin (extSignature.Arity g.1) ↦
        g.2[k.val]?.elim 0 (dR.getD · 0)) (Finset.mem_univ ⟨j, harity ▸ hj⟩)
      simp only [List.getElem?_eq_getElem hj, Option.elim_some, heq] at hle_sup
      exact (ih' _).trans hle_sup
    · rw [List.getD_eq_default _ _
          (by rw [List.length_append, List.length_singleton, hlenL]; omega),
        List.getD_eq_default _ _
          (by rw [List.length_append, List.length_singleton, hlenR]; omega)]

private theorem length_encExtCircuit_compress_le {q n : ℕ} (hq : 0 < q)
    (c : Circuit extSignature n 1) {C' : Circuit extSignature n 1}
    (hC' : C'.code = (c.code.1.map (compressGate q), c.code.2)) :
    (Unbounded.encExtCircuit 1 ⟨n, C'⟩).length ≤
      40 * (q + 2) ^ 2 * (n + c.size + 2) ^ 3 := by
  set M := n + c.size
  have hcode := c.isCodeFrom_code
  have hout := c.toNat_outputs_lt 0
  rw [Circuit.length_code_fst] at hout
  have hgate_bound : ∀ g' ∈ c.code.1.map (compressGate q),
      (Circuit.encGate Unbounded.encExtOp g').length ≤ 8 * (q + 1) * (M + 1) ^ 2 := by
    intro g' hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨harity, hlt⟩ := hcode.getElem j hj
    have hj_sz : j < c.size := by rwa [Circuit.length_code_fst] at hj
    have hwires_lt : ∀ w ∈ c.code.1[j].2, w < M := fun w hw ↦
      (hlt w hw).trans_le (by omega)
    have hcomp_lt : ∀ w ∈ (compressGate q c.code.1[j]).2, w < M := fun w hw ↦
      hwires_lt w (mem_compressGate_subset hw)
    have hcomp_len : (compressGate q c.code.1[j]).2.length ≤ q * M + 1 := by
      rcases hg0 : c.code.1[j] with ⟨op, args⟩
      rw [hg0] at harity hwires_lt
      cases op with
      | ac op' =>
        cases op' with
        | not => simp [compressGate, harity]
        | and _ | or _ =>
          have hsub : args.dedup.toFinset ⊆ Finset.range M := fun w hw ↦
            Finset.mem_range.mpr (hwires_lt w (List.mem_dedup.mp (List.mem_toFinset.mp hw)))
          have hcard := Finset.card_le_card hsub
          rw [List.toFinset_card_of_nodup (List.nodup_dedup args), Finset.card_range] at hcard
          simp only [compressGate]
          have : M ≤ q * M := Nat.le_mul_of_pos_left M hq
          omega
      | gate _ =>
        simp only [compressGate]
        exact (length_compressArgs_le hq hwires_lt).trans (Nat.le_succ _)
    have hop_len :
        (Unbounded.encExtOp (compressGate q c.code.1[j]).1).length ≤ 3 * (q * M + 1) + 3 := by
      simp only [Unbounded.encExtOp, Function.Embedding.coeFn_mk, encUnary_apply,
        List.length_replicate]
      have harity' := compressGate_arity q harity
      cases hop : (compressGate q c.code.1[j]).1 with
      | ac op' =>
        cases op' with
        | not => simp [ExtOp.toNat]
        | and m | or m =>
          rw [hop] at harity'
          simp only [ExtOp.toNat, extSignature, ExtOp.arity, Op.arity] at harity' ⊢
          omega
      | gate m =>
        rw [hop] at harity'
        simp only [ExtOp.toNat, extSignature, ExtOp.arity] at harity' ⊢
        omega
    have hargs_enc : (encList encNat (compressGate q c.code.1[j]).2).length ≤
        (q * M + 1) * (2 * M + 1) := by
      have hElem : ∀ w ∈ (compressGate q c.code.1[j]).2, (encNat w).length ≤ M := fun w hw ↦ by
        rw [encNat_apply, Nat.size_eq_bits_len]
        have hltM := hcomp_lt w hw
        have : w.size ≤ w := Nat.size_le_self w
        omega
      have hlist := length_encList_le encNat (compressGate q c.code.1[j]).2 hElem
      exact hlist.trans (Nat.mul_le_mul_right _ hcomp_len)
    rw [Circuit.encGate, length_encPair]
    dsimp only
    nlinarith
  have hgates_enc :
      (encList (Circuit.encGate Unbounded.encExtOp) (c.code.1.map (compressGate q))).length ≤
      c.size * (2 * (8 * (q + 1) * (M + 1) ^ 2) + 1) := by
    have hlist := length_encList_le (Circuit.encGate Unbounded.encExtOp)
      (c.code.1.map (compressGate q)) hgate_bound
    rw [List.length_map, Circuit.length_code_fst] at hlist
    exact hlist
  have houts_enc : (encList encNat c.code.2).length ≤ 2 * M + 1 := by
    have h1 : c.code.2 = [(c.outputs 0).toNat] := by
      simp [Circuit.code, List.ofFn_succ]
    rw [h1, encList_cons, encList_nil, List.append_nil, length_frame, encNat_apply,
      Nat.size_eq_bits_len]
    have : (c.outputs 0).toNat.size ≤ (c.outputs 0).toNat := Nat.size_le_self _
    omega
  rw [Unbounded.encExtCircuit, Circuit.encCircuit_apply, hC', length_encPair, Circuit.encCode,
    length_encPair]
  simp only [encUnary_apply, List.length_replicate]
  have hcs : c.size ≤ M := Nat.le_add_left _ _
  have hnM : n ≤ M := Nat.le_add_right _ _
  have hq2 : q + 1 ≤ (q + 2) ^ 2 := by nlinarith
  have hM3 : M * (M + 1) ^ 2 ≤ (M + 2) ^ 3 := by nlinarith
  have hM_lin : 6 * M + 3 ≤ 8 * (M + 2) ^ 3 := by nlinarith
  have h1 : c.size * (2 * (8 * (q + 1) * (M + 1) ^ 2) + 1) ≤
      16 * (q + 1) * (M * (M + 1) ^ 2) + M := by
    calc c.size * (2 * (8 * (q + 1) * (M + 1) ^ 2) + 1)
        ≤ M * (2 * (8 * (q + 1) * (M + 1) ^ 2) + 1) := Nat.mul_le_mul_right _ hcs
      _ = 16 * (q + 1) * (M * (M + 1) ^ 2) + M := by ring
  have h2 : 32 * (q + 1) * (M * (M + 1) ^ 2) ≤ 32 * (q + 2) ^ 2 * (M + 2) ^ 3 := by
    calc 32 * (q + 1) * (M * (M + 1) ^ 2)
        ≤ 32 * (q + 2) ^ 2 * (M * (M + 1) ^ 2) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 32 hq2)
      _ ≤ 32 * (q + 2) ^ 2 * (M + 2) ^ 3 := Nat.mul_le_mul_left _ hM3
  have h3 : 8 * (M + 2) ^ 3 ≤ 8 * (q + 2) ^ 2 * (M + 2) ^ 3 := by
    have : 1 ≤ (q + 2) ^ 2 := by nlinarith
    calc 8 * (M + 2) ^ 3 = 8 * 1 * (M + 2) ^ 3 := by ring
      _ ≤ 8 * (q + 2) ^ 2 * (M + 2) ^ 3 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 this)
  have h21 : 2 * (16 * (q + 1) * (M * (M + 1) ^ 2)) = 32 * (q + 1) * (M * (M + 1) ^ 2) := by ring
  have h40 :
      32 * (q + 2) ^ 2 * (M + 2) ^ 3 + 8 * (q + 2) ^ 2 * (M + 2) ^ 3 =
        40 * (q + 2) ^ 2 * (M + 2) ^ 3 := by ring
  omega

/-- **Fan-in compression for `AC^k[q]`**: for every `q ≥ 2` and `L ∈ ACMod q k`, there exist a
depth factor `c` and a polynomial `P` such that every slice `L.slice n` is computed by a circuit
`C : Circuit extSignature n 1` of depth at most `c * (⌊log₂ n⌋ + 1)^k` and encoding length
`(Unbounded.encExtCircuit 1 ⟨n, C⟩).length ≤ P.eval n`. -/
theorem exists_bounded_encExtCircuit_of_ACMod {q k : ℕ} (hq : 2 ≤ q) {L : Language Bool}
    (hL : L ∈ ACMod q k) :
    ∃ (c : ℕ) (P : Polynomial ℕ), ∀ n,
      ∃ C : Circuit extSignature n 1,
        C.Computes (extInterpretation (modGate q)) (single (L.slice n)) ∧
        C.depth ≤ c * (Nat.log 2 n + 1) ^ k ∧
        (Unbounded.encExtCircuit 1 ⟨n, C⟩).length ≤ P.eval n := by
  obtain ⟨c, s, hs, hC⟩ := hL
  obtain ⟨cs, ds, hs_le⟩ := polynomiallyBounded_iff_le.mp hs
  let P : Polynomial ℕ :=
    Polynomial.C (40 * (q + 2) ^ 2) *
      (Polynomial.X + Polynomial.C cs * (Polynomial.X + 1) ^ ds + 2) ^ 3
  refine ⟨c, P, fun n ↦ ?_⟩
  obtain ⟨C, hComp, hDepth, hSize⟩ := hC n
  have hvalid :
      (Circuit.ofCode (σ := extSignature) n 1
        (C.code.1.map (compressGate q), C.code.2)).isSome := by
    rw [Circuit.isSome_ofCode_iff]
    refine ⟨compressGate_isCodeFrom C.isCodeFrom_code, by simp [Circuit.code], fun i hi ↦ ?_⟩
    simp only [List.length_map]
    exact (Circuit.isSome_ofCode_iff.mp (by rw [Circuit.ofCode_code]; rfl)).2.2 i hi
  obtain ⟨C', hC'_eq⟩ := Option.isSome_iff_exists.mp hvalid
  have hcode : C'.code = (C.code.1.map (compressGate q), C.code.2) :=
    Circuit.code_of_ofCode_eq_some hC'_eq
  have hout0 : (C'.outputs 0).toNat = (C.outputs 0).toNat := by
    have h2 : C'.code.2 = C.code.2 := by rw [hcode]
    simpa [Circuit.code] using congrArg (fun l : List ℕ ↦ l.getD 0 0) h2
  refine ⟨C', ?_, ?_, ?_⟩
  · intro x
    funext j
    rw [Subsingleton.elim j 0, Circuit.eval_eq_getD _ _ false, hcode, hout0]
    have hfrom : Program.IsCodeFrom extSignature (List.ofFn x).length 0 C.code.1 := by
      simpa using C.isCodeFrom_code
    rw [evalCode_compressGates q (List.ofFn x) hfrom, ← Circuit.eval_eq_getD _ _ false, hComp x]
  · rw [← Circuit.depthWith_one, Circuit.depthWith_le_iff]
    intro j
    rw [Subsingleton.elim j 0, ← Circuit.getD_evalCode_depthInterpretation, hcode, hout0]
    exact (evalCode_depth_compressGates_le q n C.isCodeFrom_code _).trans
      (by
        rw [Circuit.getD_evalCode_depthInterpretation, Program.wireDepthsWith_one]
        exact (C.outputDepths_le_depth 0).trans hDepth)
  · have hlen := length_encExtCircuit_compress_le (by omega : 0 < q) C hcode
    have hsz : C.size ≤ cs * (n + 1) ^ ds := hSize.trans (hs_le n)
    refine hlen.trans ?_
    simp only [P, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)

/-! ### Strict partial decoder for `Unbounded.encExtCircuit 1` -/

/-- Inverse of `ExtOp.toNat`: decodes a natural number back to an `ExtOp`. -/
private def extOpOfNat : ℕ → ExtOp
  | 0 => .ac .not
  | k + 1 =>
    match k % 3 with
    | 0 => .ac (.and (k / 3))
    | 1 => .ac (.or (k / 3))
    | _ => .gate (k / 3)

private theorem extOpOfNat_toNat (op : ExtOp) : extOpOfNat op.toNat = op := by
  cases op with
  | ac op' =>
    cases op' with
    | not => rfl
    | and m =>
      change extOpOfNat (3 * m + 1) = .ac (.and m)
      simp [extOpOfNat, Nat.mul_mod_right, Nat.mul_div_right m (by omega : 0 < 3)]
    | or m =>
      change extOpOfNat ((3 * m + 1) + 1) = .ac (.or m)
      simp [extOpOfNat, Nat.add_mod, Nat.mul_mod_right]
      omega
  | gate m =>
    change extOpOfNat ((3 * m + 2) + 1) = .gate m
    simp [extOpOfNat, Nat.add_mod, Nat.mul_mod_right]
    omega

private theorem toNat_extOpOfNat (k : ℕ) : (extOpOfNat k).toNat = k := by
  cases k with
  | zero => rfl
  | succ k =>
    unfold extOpOfNat
    have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hmod with h | h | h <;> simp [h, ExtOp.toNat] <;> omega

/-- Total polynomial-time decoder for `Unbounded.encExtOp`. -/
private def decExtOp : Decoder Unbounded.encExtOp :=
  Decoder.unary.map extOpOfNat ExtOp.toNat extOpOfNat_toNat fun k ↦ by
    simp [Unbounded.encExtOp, toNat_extOpOfNat]

/-- Strict polynomial-time partial decoder for raw `(n, (gates, outputs))` circuit tuples. -/
private def decRawExtCircuit :
    PartialDecoder (encPair encUnary (Circuit.encCode Unbounded.encExtOp)) :=
  PartialDecoder.pair (PartialDecoder.ofDecoder Decoder.unary)
    (PartialDecoder.pair
      (PartialDecoder.list
        (PartialDecoder.pair (PartialDecoder.ofDecoder decExtOp)
          (PartialDecoder.list (PartialDecoder.ofDecoder Decoder.nat))))
      (PartialDecoder.list (PartialDecoder.ofDecoder Decoder.nat)))

/-- Computing the binary arity of an `ExtOp` is polynomial-time. -/
private theorem computableInPolyTime_extOp_arity :
    ComputableInPolyTime extSignature.Arity Unbounded.encExtOp encNat := by
  have heq (op : ExtOp) : extSignature.Arity op =
      if op.toNat == 0 then 1 else (op.toNat - 1) / 3 := by
    cases op with
    | ac op' =>
      cases op' with
      | not => rfl
      | and m => simp [ExtOp.arity, Op.arity, ExtOp.toNat]
      | or m => simp [ExtOp.arity, Op.arity, ExtOp.toNat]; omega
    | gate m => simp [ExtOp.arity, ExtOp.toNat]; omega
  have h_pt :
      ComputableInPolyTime (fun op : ExtOp ↦ if op.toNat == 0 then 1 else (op.toNat - 1) / 3)
        Unbounded.encExtOp encUnary := by
    have hnat := computableInPolyTime_extOp_toNat
    have hcond : ComputableInPolyTime (fun op : ExtOp ↦ op.toNat == 0)
        Unbounded.encExtOp encBool := by fun_prop
    have hdiv : ComputableInPolyTime (fun op : ExtOp ↦ (op.toNat - 1) / 3)
        Unbounded.encExtOp encUnary := by fun_prop
    exact ComputableInPolyTime.ite' hcond (ComputableInPolyTime.const 1) hdiv
  exact (ComputableInPolyTime.unary_to_binary.comp h_pt).of_enc_eq fun op ↦ by
    exact congrArg encNat (heq op)

/-- Boolean well-formedness check for a raw 1-output `Unbounded.extSignature` circuit tuple. -/
private def rawExtCircuitWellFormed (t : ℕ × (List (ExtOp × List ℕ) × List ℕ)) : Bool :=
  codeCheck extSignature t.1 t.2.1 &&
    decide (t.2.2.length = 1) &&
    t.2.2.all fun o ↦ decide (o < t.1 + t.2.1.length)

private theorem rawExtCircuitWellFormed_eq_true_iff
    {t : ℕ × (List (ExtOp × List ℕ) × List ℕ)} :
    rawExtCircuitWellFormed t = true ↔ (Circuit.ofCode (σ := extSignature) t.1 1 t.2).isSome := by
  rw [Circuit.isSome_ofCode_iff, rawExtCircuitWellFormed, Bool.and_eq_true, Bool.and_eq_true,
    codeCheck_eq_true_iff, decide_eq_true_eq, List.all_eq_true]
  simp only [decide_eq_true_eq, and_assoc]

private theorem computableInPolyTime_rawExtCircuitWellFormed :
    ComputableInPolyTime rawExtCircuitWellFormed
      (encPair encUnary (Circuit.encCode Unbounded.encExtOp)) encBool := by
  unfold rawExtCircuitWellFormed
  let encR := encPair encUnary (Circuit.encCode Unbounded.encExtOp)
  have hn : ComputableInPolyTime
      (fun t : ℕ × (List (ExtOp × List ℕ) × List ℕ) ↦ t.1) encR encUnary :=
    ComputableInPolyTime.fst _ _
  have hgates : ComputableInPolyTime (fun t : ℕ × (List (ExtOp × List ℕ) × List ℕ) ↦ t.2.1)
      encR (encList (Circuit.encGate Unbounded.encExtOp)) :=
    (ComputableInPolyTime.snd _ _).fst'
  have houts : ComputableInPolyTime (fun t : ℕ × (List (ExtOp × List ℕ) × List ℕ) ↦ t.2.2)
      encR (encList encNat) :=
    (ComputableInPolyTime.snd _ _).snd'
  have h1 := Circuits.computableInPolyTime_codeCheck computableInPolyTime_extOp_arity hn hgates
  have h2 := ComputableInPolyTime.decide_eq'
    ((ComputableInPolyTime.length encNat).comp houts) (ComputableInPolyTime.const 1)
  have h3 : ComputableInPolyTime
      (fun t : ℕ × (List (ExtOp × List ℕ) × List ℕ) ↦
        t.2.2.all fun o ↦ decide (o < t.1 + t.2.1.length))
      encR encBool := by
    refine ComputableInPolyTime.allWithInput houts ?_
    refine ComputableInPolyTime.binary_lt' (ComputableInPolyTime.snd _ _) ?_
    exact ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.unary_add' (hn.comp (ComputableInPolyTime.fst _ _))
        ((ComputableInPolyTime.length (Circuit.encGate Unbounded.encExtOp)).comp
          (hgates.comp (ComputableInPolyTime.fst _ _))))
  exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' h1 h2) h3

/-- Strict polynomial-time `PartialDecoder` for `Unbounded.encExtCircuit 1`. -/
def decExtCircuit : PartialDecoder (Unbounded.encExtCircuit 1) :=
  PartialDecoder.checked
    (fun word ↦
      (decRawExtCircuit.decode word).bind fun t ↦
        (Circuit.ofCode (σ := extSignature) t.1 1 t.2).map fun C ↦ ⟨t.1, C⟩)
    (fun ⟨n, C⟩ ↦ by
      have hraw : Unbounded.encExtCircuit 1 ⟨n, C⟩ =
          encPair encUnary (Circuit.encCode Unbounded.encExtOp) (n, C.code) := rfl
      rw [hraw, decRawExtCircuit.decode_enc]
      simp)
    (by
      let f_raw : List Bool → Option (ℕ × (List (ExtOp × List ℕ) × List ℕ)) :=
        fun word ↦ (decRawExtCircuit.decode word).elim none fun t ↦
          if rawExtCircuitWellFormed t then some t else none
      have hf_raw : ComputableInPolyTime f_raw encBits
          (encOption (encPair encUnary (Circuit.encCode Unbounded.encExtOp))) := by
        dsimp only [f_raw]
        refine decRawExtCircuit.computable.optionElimWithInput
          (ComputableInPolyTime.const none) ?_
        exact ComputableInPolyTime.ite'
          (computableInPolyTime_rawExtCircuitWellFormed.comp (ComputableInPolyTime.snd _ _))
          ((ComputableInPolyTime.optionSome _).comp (ComputableInPolyTime.snd _ _))
          (ComputableInPolyTime.const none)
      refine hf_raw.of_enc_eq fun word ↦ ?_
      dsimp only [f_raw]
      cases hdec : decRawExtCircuit.decode word with
      | none => rfl
      | some t =>
        simp only [Option.elim_some, Option.bind_some]
        cases hwf : rawExtCircuitWellFormed t with
        | false =>
          have hnone : Circuit.ofCode (σ := extSignature) t.1 1 t.2 = none := by
            rw [← Option.not_isSome_iff_eq_none, ← rawExtCircuitWellFormed_eq_true_iff, hwf]
            decide
          simp [hnone]
        | true =>
          obtain ⟨C, hC⟩ :=
            Option.isSome_iff_exists.mp (rawExtCircuitWellFormed_eq_true_iff.mp hwf)
          have hcode := Circuit.code_of_ofCode_eq_some hC
          simp only [↓reduceIte, hC, Option.map_some, encOption_some, Unbounded.encExtCircuit,
            Circuit.encCircuit_apply, hcode])

/-! ### Polynomial-time evaluation of `Unbounded.extSignature` circuits under `MOD_q` -/

/-- Evaluate one `Unbounded.ExtOp` gate with `MOD_q` semantics on a list of already-computed wire
values. -/
private def evalExtGate (q : ℕ) (vals : List Bool) (g : ExtOp × List ℕ) : Bool :=
  let args := g.2.map fun w ↦ vals.getD w false
  if g.1.toNat == 0 then !(args.headD false)
  else if g.1.toNat % 3 == 1 then args.all id
  else if g.1.toNat % 3 == 2 then args.any id
  else decide (args.count true % q ≠ 0)

private theorem evalExtGate_eq (q : ℕ) (vals : List Bool) {g : ExtOp × List ℕ}
    (harity : g.2.length = extSignature.Arity g.1) :
    evalExtGate q vals g =
      extInterpretation (modGate q) g.1 fun a ↦ g.2[a.val]?.elim false (vals.getD · false) := by
  rcases g with ⟨op, args⟩
  simp only [evalExtGate]
  cases op with
  | ac op' =>
    cases op' with
    | not =>
      simp only [ExtOp.toNat, beq_self_eq_true, ↓reduceIte, extInterpretation_ac,
        interpretation_not]
      simp only [ExtOp.arity, Op.arity] at harity
      cases args with
      | nil => simp at harity
      | cons w rest => simp
    | and m =>
      have hlen : args.length = m := by simpa [ExtOp.arity, Op.arity] using harity
      have hne0 : (3 * m + 1 == 0) = false := by simp
      have hmod1 : ((3 * m + 1) % 3 == 1) = true := by simp [Nat.add_mod, Nat.mul_mod_right]
      simp only [ExtOp.toNat, hne0, Bool.false_eq_true, ↓reduceIte, hmod1, extInterpretation_ac,
        interpretation_and]
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true, List.mem_map, id_eq, decide_eq_true_eq]
      constructor
      · intro hall j
        have hlt : j.val < args.length := j.isLt.trans_eq hlen.symm
        simp only [List.getElem?_eq_getElem hlt, Option.elim_some]
        exact hall _ ⟨args[j.val], List.getElem_mem hlt, rfl⟩
      · rintro hall _ ⟨w, hw, rfl⟩
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
        have h1 := hall ⟨j, hlen ▸ hj⟩
        simpa only [List.getElem?_eq_getElem hj, Option.elim_some] using h1
    | or m =>
      have hlen : args.length = m := by simpa [ExtOp.arity, Op.arity] using harity
      have hne0 : (3 * m + 2 == 0) = false := by simp
      have hmod1 : ((3 * m + 2) % 3 == 1) = false := by simp [Nat.add_mod, Nat.mul_mod_right]
      have hmod2 : ((3 * m + 2) % 3 == 2) = true := by simp [Nat.add_mod, Nat.mul_mod_right]
      simp only [ExtOp.toNat, hne0, hmod1, hmod2, Bool.false_eq_true, ↓reduceIte,
        extInterpretation_ac, interpretation_or]
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true, List.mem_map, id_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, htrue⟩
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
        exact ⟨⟨j, hlen ▸ hj⟩,
          by simpa only [List.getElem?_eq_getElem hj, Option.elim_some] using htrue⟩
      · rintro ⟨j, hj⟩
        have hlt : j.val < args.length := j.isLt.trans_eq hlen.symm
        simp only [List.getElem?_eq_getElem hlt, Option.elim_some] at hj
        exact ⟨_, ⟨args[j.val], List.getElem_mem hlt, rfl⟩, hj⟩
  | gate m =>
    have hlen : m = args.length := by simpa [ExtOp.arity] using harity.symm
    have hne0 : (3 * m + 3 == 0) = false := by simp
    have hmod1 : ((3 * m + 3) % 3 == 1) = false := by simp [Nat.mul_mod_right]
    have hmod2 : ((3 * m + 3) % 3 == 2) = false := by simp [Nat.mul_mod_right]
    simp only [ExtOp.toNat, hne0, hmod1, hmod2, Bool.false_eq_true, ↓reduceIte,
      extInterpretation_gate, modGate, decide_eq_decide]
    have hcnt : (args.map fun w ↦ vals.getD w false).count true =
        (Finset.univ.filter fun i : Fin m ↦
          args[i.val]?.elim false (vals.getD · false) = true).card := by
      subst hlen
      rw [List.count_eq_length_filter, List.filter_map]
      simp only [Function.comp_def, beq_true, List.length_map]
      rw [← card_fin_filter_eq_length_filter]
      congr 1
      ext i
      simp
    rw [hcnt]

/-- Evaluate a gate list over `Unbounded.extSignature` under `MOD_q` semantics. -/
private def evalExtCode (q : ℕ) (x : List Bool) (gates : List (ExtOp × List ℕ)) : List Bool :=
  gates.foldl (fun vals g ↦ vals ++ [evalExtGate q vals g]) x

private theorem evalExtCode_eq (q : ℕ) (x : List Bool) {gates : List (ExtOp × List ℕ)}
    (h : Program.IsCodeFrom extSignature x.length 0 gates) :
    evalExtCode q x gates = evalCode (extInterpretation (modGate q)) false x gates := by
  induction gates using List.reverseRecOn with
  | nil => rfl
  | append_singleton gates g ih =>
    rw [Program.isCodeFrom_append] at h
    rw [evalExtCode, List.foldl_append, List.foldl_cons, List.foldl_nil, ← evalExtCode, ih h.1,
      evalCode_append_singleton, evalExtGate_eq q _ h.2.1.1]

private theorem computableInPolyTime_evalExtGate (q : ℕ) :
    ComputableInPolyTime (fun p : List Bool × (ExtOp × List ℕ) ↦ evalExtGate q p.1 p.2)
      (encPair encBits (Circuit.encGate Unbounded.encExtOp)) encBool := by
  dsimp only [evalExtGate]
  let encP := encPair encBits (Circuit.encGate Unbounded.encExtOp)
  have hvals : ComputableInPolyTime (fun p : List Bool × (ExtOp × List ℕ) ↦ p.1) encP encBits :=
    ComputableInPolyTime.fst _ _
  have hopNat : ComputableInPolyTime (fun p : List Bool × (ExtOp × List ℕ) ↦ p.2.1.toNat)
      encP encUnary :=
    computableInPolyTime_extOp_toNat.comp (ComputableInPolyTime.snd _ _).fst'
  have hargs : ComputableInPolyTime
      (fun p : List Bool × (ExtOp × List ℕ) ↦ p.2.2.map fun w ↦ p.1.getD w false)
      encP encBits :=
    ComputableInPolyTime.mapToBitsWithInput
      (f := fun (p : List Bool × (ExtOp × List ℕ)) (w : ℕ) ↦ p.1.getD w false)
      (ComputableInPolyTime.snd _ _).snd'
      (ComputableInPolyTime.listGetD_binary (encA := encBool) (encL := encBits) false
        (hvals.comp (ComputableInPolyTime.fst _ _)) (ComputableInPolyTime.snd _ _))
  have hc0 : ComputableInPolyTime (fun p : List Bool × (ExtOp × List ℕ) ↦ p.2.1.toNat == 0)
      encP encBool := by fun_prop
  have hc1 : ComputableInPolyTime (fun p : List Bool × (ExtOp × List ℕ) ↦ p.2.1.toNat % 3 == 1)
      encP encBool := by fun_prop
  have hc2 : ComputableInPolyTime (fun p : List Bool × (ExtOp × List ℕ) ↦ p.2.1.toNat % 3 == 2)
      encP encBool := by fun_prop
  have hb0 : ComputableInPolyTime
      (fun p : List Bool × (ExtOp × List ℕ) ↦
        !((p.2.2.map fun w ↦ p.1.getD w false).headD false))
      encP encBool :=
    ComputableInPolyTime.bool_not.comp
      ((ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp hargs)
  have hb1 : ComputableInPolyTime
      (fun p : List Bool × (ExtOp × List ℕ) ↦ (p.2.2.map fun w ↦ p.1.getD w false).all id)
      encP encBool :=
    ComputableInPolyTime.bitsAllWithInput (test := fun _ b ↦ id b) hargs
      (ComputableInPolyTime.snd _ _)
  have hb2 : ComputableInPolyTime
      (fun p : List Bool × (ExtOp × List ℕ) ↦ (p.2.2.map fun w ↦ p.1.getD w false).any id)
      encP encBool :=
    ComputableInPolyTime.bitsAnyWithInput (test := fun _ b ↦ id b) hargs
      (ComputableInPolyTime.snd _ _)
  have hb3 : ComputableInPolyTime
      (fun p : List Bool × (ExtOp × List ℕ) ↦
        decide ((p.2.2.map fun w ↦ p.1.getD w false).count true % q ≠ 0))
      encP encBool := by
    have hcnt : ComputableInPolyTime
        (fun p : List Bool × (ExtOp × List ℕ) ↦ (p.2.2.map fun w ↦ p.1.getD w false).count true)
        encP encUnary :=
      ComputableInPolyTime.bitsCountWithInput hargs (ComputableInPolyTime.const true)
    have hmod : ComputableInPolyTime
        (fun p : List Bool × (ExtOp × List ℕ) ↦
          (p.2.2.map fun w ↦ p.1.getD w false).count true % q)
        encP encUnary :=
      ComputableInPolyTime.unary_mod.comp (hcnt.prod (ComputableInPolyTime.const q))
    exact (ComputableInPolyTime.bool_not.comp
      (ComputableInPolyTime.decide_eq' hmod (ComputableInPolyTime.const 0))).of_enc_eq fun p ↦ by
      simp
  exact ComputableInPolyTime.ite' hc0 hb0
    (ComputableInPolyTime.ite' hc1 hb1 (ComputableInPolyTime.ite' hc2 hb2 hb3))

private theorem computableInPolyTime_evalExtCode (q : ℕ) :
    ComputableInPolyTime (fun p : List Bool × List (ExtOp × List ℕ) ↦ evalExtCode q p.1 p.2)
      (encPair encBits (encList (Circuit.encGate Unbounded.encExtOp))) encBits := by
  dsimp only [evalExtCode]
  have hstep : ComputableInPolyTime
      (fun p : List Bool × (ExtOp × List ℕ) ↦ p.1 ++ [evalExtGate q p.1 p.2])
      (encPair encBits (Circuit.encGate Unbounded.encExtOp)) encBits :=
    ComputableInPolyTime.bitsAppend (ComputableInPolyTime.fst _ _)
      (ComputableInPolyTime.bitsCons (computableInPolyTime_evalExtGate q)
        (ComputableInPolyTime.const []))
  exact ComputableInPolyTime.foldl_of_bounded_growth (ComputableInPolyTime.snd _ _)
    (ComputableInPolyTime.fst _ _) hstep (growth := 1) fun _ _ ↦ by simp

/-- Evaluate an encoded `Unbounded.extSignature` circuit `w` on input word `x` under `MOD_q`
gates, returning `false` on malformed descriptions. -/
def evalRawExtCircuit (q : ℕ) (w x : List Bool) : Bool :=
  (decRawExtCircuit.decode w).elim false fun t ↦
    (evalExtCode q ((x ++ List.replicate t.1 false).take t.1) t.2.1).getD (t.2.2.headD 0) false

/-- **Evaluating an encoded `MOD_q` circuit is polynomial-time.** -/
theorem computableInPolyTime_evalRawExtCircuit (q : ℕ) :
    ComputableInPolyTime (fun p : List Bool × List Bool ↦ evalRawExtCircuit q p.1 p.2)
      (encPair encBits encBits) encBool := by
  dsimp only [evalRawExtCircuit]
  refine (decRawExtCircuit.computable.comp (ComputableInPolyTime.fst _ _)).optionElimWithInput
    (ComputableInPolyTime.const false) ?_
  let encS := encPair (encPair encBits encBits)
    (encPair encUnary (Circuit.encCode Unbounded.encExtOp))
  have hx : ComputableInPolyTime
      (fun s : (List Bool × List Bool) × (ℕ × (List (ExtOp × List ℕ) × List ℕ)) ↦ s.1.2)
      encS encBits := (ComputableInPolyTime.fst _ _).snd'
  have hn : ComputableInPolyTime
      (fun s : (List Bool × List Bool) × (ℕ × (List (ExtOp × List ℕ) × List ℕ)) ↦ s.2.1)
      encS encUnary := (ComputableInPolyTime.snd _ _).fst'
  have hgates : ComputableInPolyTime
      (fun s : (List Bool × List Bool) × (ℕ × (List (ExtOp × List ℕ) × List ℕ)) ↦ s.2.2.1)
      encS (encList (Circuit.encGate Unbounded.encExtOp)) :=
    ((ComputableInPolyTime.snd _ _).snd').fst'
  have hout : ComputableInPolyTime
      (fun s : (List Bool × List Bool) × (ℕ × (List (ExtOp × List ℕ) × List ℕ)) ↦
        s.2.2.2.headD 0)
      encS encNat :=
    (ComputableInPolyTime.headD (encA := encNat) (encL := encList encNat) 0).comp
      ((ComputableInPolyTime.snd _ _).snd').snd'
  have hpad : ComputableInPolyTime
      (fun s : (List Bool × List Bool) × (ℕ × (List (ExtOp × List ℕ) × List ℕ)) ↦
        (s.1.2 ++ List.replicate s.2.1 false).take s.2.1)
      encS encBits :=
    ComputableInPolyTime.bitsTakeWithInput
      (ComputableInPolyTime.bitsAppend hx ((ComputableInPolyTime.bitsReplicate false).comp hn)) hn
  have heval := (computableInPolyTime_evalExtCode q).comp (hpad.prod hgates)
  exact ComputableInPolyTime.listGetD_binary (encA := encBool) (encL := encBits) false heval hout

/-- On a valid encoded `Unbounded.extSignature` circuit `C` and input `x` of length `n`,
`evalRawExtCircuit q` agrees with `C.eval (extInterpretation (modGate q))`. -/
theorem evalRawExtCircuit_encExtCircuit (q : ℕ) {n : ℕ} (C : Circuit extSignature n 1)
    {x : List Bool} (hx : x.length = n) :
    evalRawExtCircuit q (Unbounded.encExtCircuit 1 ⟨n, C⟩) x =
      C.eval (extInterpretation (modGate q)) (BitString.ofList n x) 0 := by
  have hraw : Unbounded.encExtCircuit 1 ⟨n, C⟩ =
      encPair encUnary (Circuit.encCode Unbounded.encExtOp) (n, C.code) := rfl
  rw [evalRawExtCircuit, hraw, decRawExtCircuit.decode_enc]
  simp only [Option.elim_some]
  have htake : (x ++ List.replicate n false).take n = x := by
    rw [List.take_left' hx]
  have hfrom : Program.IsCodeFrom extSignature x.length 0 C.code.1 := by
    rw [hx]; exact C.isCodeFrom_code
  have hout0 : C.code.2.headD 0 = (C.outputs 0).toNat := by
    simp [Circuit.code, List.ofFn_succ]
  rw [htake, evalExtCode_eq q x hfrom, hout0, Circuit.eval_eq_getD _ _ false]
  congr 2
  rw [BitString.ofFn_ofList_eq_take, htake]

/-! ### Polynomial-time depth calculation and `ACMod` validity checking -/

private def listMax (l : List ℕ) : ℕ :=
  l.foldl max 0

private theorem listMax_eq_sup {m : ℕ} (f : Fin m → ℕ) :
    listMax (List.ofFn f) = Finset.univ.sup f := by
  have hle : ∀ (l : List ℕ) (acc : ℕ),
      acc ≤ l.foldl max acc ∧ ∀ x ∈ l, x ≤ l.foldl max acc := by
    intro l
    induction l with
    | nil => intro acc; exact ⟨le_rfl, fun _ h ↦ nomatch h⟩
    | cons a l ih =>
      intro acc
      obtain ⟨h1, h2⟩ := ih (max acc a)
      refine ⟨(le_max_left acc a).trans h1, fun x hx ↦ ?_⟩
      rcases List.mem_cons.mp hx with rfl | hxl
      · exact (le_max_right acc x).trans h1
      · exact h2 x hxl
  have hbound : ∀ (l : List ℕ) (acc B : ℕ),
      acc ≤ B → (∀ x ∈ l, x ≤ B) → l.foldl max acc ≤ B := by
    intro l
    induction l with
    | nil => intro acc B hacc _; exact hacc
    | cons a l ih =>
      intro acc B hacc hall
      exact ih (max acc a) B (max_le hacc (hall a (List.mem_cons_self ..)))
        (fun x hx ↦ hall x (List.mem_cons_of_mem a hx))
  apply le_antisymm
  · exact hbound _ 0 _ (Nat.zero_le _) fun x hx ↦ by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact Finset.le_sup (f := f) (Finset.mem_univ i)
  · exact Finset.sup_le fun i _ ↦ (hle _ 0).2 (f i) (List.mem_ofFn.mpr ⟨i, rfl⟩)

private theorem computableInPolyTime_listMax :
    ComputableInPolyTime listMax (encList encUnary) encUnary := by
  unfold listMax
  refine (ComputableInPolyTime.foldl_spec (encA := encUnary) (encB := encUnary)
    (encL := encList encUnary) ComputableInPolyTime.id' (ComputableInPolyTime.const 0)
    ComputableInPolyTime.unary_max
    (fun l _ acc ↦ acc ≤ (encList encUnary l).length)
    (fun _ ↦ Nat.zero_le _)
    (fun l consumed acc v hpref hacc ↦ ?_)
    (size := fun l ↦ (encList encUnary l).length) PolyBounded.self
    (fun _ _ _ _ h ↦ by simpa using h)).1
  have hv : v ≤ (encList encUnary l).length := by
    have hmem : v ∈ l := hpref.subset (by simp)
    simpa [encUnary_apply] using length_le_encList_of_mem encUnary hmem
  exact max_le hacc hv

/-- Compute wire depths of a gate list, capped at `gates.length`. On every well-formed circuit
code, no wire depth exceeds `gates.length`, so the cap is never active. -/
private def depthsExt (n : ℕ) (gates : List (ExtOp × List ℕ)) : List ℕ :=
  gates.foldl
    (fun ds g ↦ ds ++ [min gates.length (listMax (g.2.map fun w ↦ ds.getD w 0) + 1)])
    (List.replicate n 0)

private theorem evalCode_depth_le_length {n : ℕ} {gates : List (ExtOp × List ℕ)}
    (h : Program.IsCodeFrom extSignature n 0 gates) :
    ∀ w,
      (evalCode (depthInterpretation (σ := extSignature) 1) 0
        (List.replicate n 0) gates).getD w 0 ≤ gates.length := by
  induction gates using List.reverseRecOn with
  | nil =>
    intro w
    simp [evalCode, List.getD_eq_getElem?_getD]
  | append_singleton gates g ih =>
    rw [Program.isCodeFrom_append] at h
    have ih' := ih h.1
    set ds := evalCode (depthInterpretation (σ := extSignature) 1) 0 (List.replicate n 0) gates
    have hds_len : ds.length = n + gates.length := by simp [ds, length_evalCode]
    intro w
    rw [evalCode_append_singleton, List.length_append, List.length_singleton]
    rcases lt_trichotomy w (n + gates.length) with hlt | rfl | hgt
    · rw [List.getD_append _ _ _ _ (by rw [hds_len]; exact hlt)]
      exact (ih' w).trans (Nat.le_succ _)
    · rw [List.getD_append_right _ _ _ _ (by rw [hds_len]), hds_len, Nat.sub_self,
        List.getD_cons_zero]
      simp only [depthInterpretation, Fin.foldl_max_eq_max_sup, Nat.zero_max, Pi.one_apply]
      apply Nat.add_le_add_right
      apply Finset.sup_le
      intro a _
      rcases g.2[a.val]? with _ | i
      · exact Nat.zero_le _
      · exact ih' i
    · rw [List.getD_eq_default _ _
          (by rw [List.length_append, List.length_singleton, hds_len]; omega)]
      exact Nat.zero_le _

private theorem depthsExt_eq_evalCode (n : ℕ) {gates : List (ExtOp × List ℕ)}
    (h : Program.IsCodeFrom extSignature n 0 gates) :
    depthsExt n gates =
      evalCode (depthInterpretation (σ := extSignature) 1) 0 (List.replicate n 0) gates := by
  suffices hcap : ∀ cap, gates.length ≤ cap →
      gates.foldl (fun ds g ↦ ds ++ [min cap (listMax (g.2.map fun w ↦ ds.getD w 0) + 1)])
        (List.replicate n 0) =
      evalCode (depthInterpretation (σ := extSignature) 1) 0 (List.replicate n 0) gates from
    hcap gates.length le_rfl
  intro cap
  induction gates using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton gates g ih =>
    intro hcap
    rw [Program.isCodeFrom_append] at h
    have hcap1 : gates.length + 1 ≤ cap := by
      simpa only [List.length_append, List.length_singleton] using hcap
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih h.1 (by omega),
      evalCode_append_singleton]
    congr 2
    set ds := evalCode (depthInterpretation (σ := extSignature) 1) 0 (List.replicate n 0) gates
    have hmap : g.2.map (fun w ↦ ds.getD w 0) =
        List.ofFn (fun a : Fin (extSignature.Arity g.1) ↦ g.2[a.val]?.elim 0 (ds.getD · 0)) := by
      apply List.ext_getElem (by simp [h.2.1.1])
      intro i hi1 hi2
      simp only [List.getElem_map, List.getElem_ofFn,
        List.getElem?_eq_getElem (by simpa using hi1), Option.elim_some]
    rw [hmap, listMax_eq_sup]
    have hsup_le : (Finset.univ.sup fun a : Fin (extSignature.Arity g.1) ↦
        g.2[a.val]?.elim 0 (ds.getD · 0)) ≤ gates.length := by
      apply Finset.sup_le
      intro a _
      rcases g.2[a.val]? with _ | i
      · exact Nat.zero_le _
      · exact evalCode_depth_le_length h.1 i
    simp only [depthInterpretation, Fin.foldl_max_eq_max_sup, Nat.zero_max, Pi.one_apply]
    exact Nat.min_eq_right (Nat.le_trans (Nat.add_le_add_right hsup_le 1) hcap1)

private theorem computableInPolyTime_depthsExt :
    ComputableInPolyTime (fun p : ℕ × List (ExtOp × List ℕ) ↦ depthsExt p.1 p.2)
      (encPair encUnary (encList (Circuit.encGate Unbounded.encExtOp))) (encList encUnary) := by
  dsimp only [depthsExt]
  let encIn := encPair encUnary (encList (Circuit.encGate Unbounded.encExtOp))
  have hpar : ComputableInPolyTime
      (fun p : ℕ × List (ExtOp × List ℕ) ↦ p.2.length) encIn encUnary :=
    (ComputableInPolyTime.length (Circuit.encGate Unbounded.encExtOp)).comp
      (ComputableInPolyTime.snd _ _)
  let stepFn (cap : ℕ) (ds : List ℕ) (g : ExtOp × List ℕ) : List ℕ :=
    ds ++ [min cap (listMax (g.2.map fun w ↦ ds.getD w 0) + 1)]
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × List ℕ) × (ExtOp × List ℕ) ↦ stepFn q.1.1 q.1.2 q.2)
      (encPair (encPair encUnary (encList encUnary)) (Circuit.encGate Unbounded.encExtOp))
      (encList encUnary) := by
    dsimp only [stepFn]
    let encQ := encPair (encPair encUnary (encList encUnary))
      (Circuit.encGate Unbounded.encExtOp)
    have hcap : ComputableInPolyTime (fun q : (ℕ × List ℕ) × (ExtOp × List ℕ) ↦ q.1.1)
        encQ encUnary := (ComputableInPolyTime.fst _ _).fst'
    have hds : ComputableInPolyTime (fun q : (ℕ × List ℕ) × (ExtOp × List ℕ) ↦ q.1.2)
        encQ (encList encUnary) := (ComputableInPolyTime.fst _ _).snd'
    have hargs : ComputableInPolyTime (fun q : (ℕ × List ℕ) × (ExtOp × List ℕ) ↦ q.2.2)
        encQ (encList encNat) := (ComputableInPolyTime.snd _ _).snd'
    have hmap : ComputableInPolyTime
        (fun q : (ℕ × List ℕ) × (ExtOp × List ℕ) ↦ q.2.2.map fun w ↦ q.1.2.getD w 0)
        encQ (encList encUnary) :=
      ComputableInPolyTime.mapWithInput
        (f := fun (q : (ℕ × List ℕ) × (ExtOp × List ℕ)) (w : ℕ) ↦ q.1.2.getD w 0) hargs
        (ComputableInPolyTime.listGetD_binary (encA := encUnary) (encL := encList encUnary) 0
          (hds.comp (ComputableInPolyTime.fst _ _)) (ComputableInPolyTime.snd _ _))
    have hnew : ComputableInPolyTime
        (fun q : (ℕ × List ℕ) × (ExtOp × List ℕ) ↦
          min q.1.1 (listMax (q.2.2.map fun w ↦ q.1.2.getD w 0) + 1))
        encQ encUnary :=
      ComputableInPolyTime.unary_min.comp
        (hcap.prod (ComputableInPolyTime.unary_add'
          (computableInPolyTime_listMax.comp hmap) (ComputableInPolyTime.const 1)))
    exact ComputableInPolyTime.listAppend' hds
      (ComputableInPolyTime.cons' hnew (ComputableInPolyTime.const []))
  refine ComputableInPolyTime.foldlWith_of_bounded_growth
    (encA := Circuit.encGate Unbounded.encExtOp) (encB := encList encUnary)
    (encL := encList (Circuit.encGate Unbounded.encExtOp)) (encP := encUnary)
    (step := stepFn) hpar (ComputableInPolyTime.snd _ _)
    (ComputableInPolyTime.replicate (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.const 0))
    hstep (growth := fun p ↦ 2 * p.2.length + 1) ?_ ?_
  · exact ((PolyBounded.const 2).mul hpar.polyBounded).add (PolyBounded.const 1)
  · intro p ds g _
    simp only [stepFn, encList_append, encList_cons, encList_nil, List.append_nil,
      List.length_append, length_frame, encUnary_apply, List.length_replicate]
    have : min p.2.length (listMax (g.2.map fun w ↦ ds.getD w 0) + 1) ≤ p.2.length :=
      Nat.min_le_left _ _
    omega

/-- Polynomial-time checker verifying that `w` is the `Unbounded.encExtCircuit 1` encoding of a
valid `n`-input 1-output `Unbounded.extSignature` circuit of depth at most
`c * (⌊log₂ n⌋ + 1) ^ k`. -/
def checkACMod (c k : ℕ) (n : ℕ) (w : List Bool) : Bool :=
  (decRawExtCircuit.decode w).elim false fun t ↦
    decide (t.1 = n) &&
      rawExtCircuitWellFormed t &&
      decide ((depthsExt t.1 t.2.1).getD (t.2.2.headD 0) 0 ≤ c * (Nat.log 2 n + 1) ^ k)

/-- **Checking `AC^k[q]` circuit syntax and depth is polynomial-time.** -/
theorem computableInPolyTime_checkACMod (c k : ℕ) :
    ComputableInPolyTime (fun p : ℕ × List Bool ↦ checkACMod c k p.1 p.2)
      (encPair encUnary encBits) encBool := by
  dsimp only [checkACMod]
  refine (decRawExtCircuit.computable.comp (ComputableInPolyTime.snd _ _)).optionElimWithInput
    (ComputableInPolyTime.const false) ?_
  let encS := encPair (encPair encUnary encBits)
    (encPair encUnary (Circuit.encCode Unbounded.encExtOp))
  have hn : ComputableInPolyTime
      (fun s : (ℕ × List Bool) × (ℕ × (List (ExtOp × List ℕ) × List ℕ)) ↦ s.1.1)
      encS encUnary := (ComputableInPolyTime.fst _ _).fst'
  have ht : ComputableInPolyTime
      (fun s : (ℕ × List Bool) × (ℕ × (List (ExtOp × List ℕ) × List ℕ)) ↦ s.2)
      encS (encPair encUnary (Circuit.encCode Unbounded.encExtOp)) :=
    ComputableInPolyTime.snd _ _
  have h1 := ComputableInPolyTime.decide_eq' ht.fst' hn
  have h2 := computableInPolyTime_rawExtCircuitWellFormed.comp ht
  have hds := computableInPolyTime_depthsExt.comp (ht.fst'.prod ht.snd'.fst')
  have hout :=
    (ComputableInPolyTime.headD (encA := encNat) (encL := encList encNat) 0).comp ht.snd'.snd'
  have hdepth := ComputableInPolyTime.listGetD_binary (encA := encUnary) (encL := encList encUnary)
    0 hds hout
  have hbound : ComputableInPolyTime
      (fun s : (ℕ × List Bool) × (ℕ × (List (ExtOp × List ℕ) × List ℕ)) ↦
        c * (Nat.log 2 s.1.1 + 1) ^ k)
      encS encUnary := by
    have hlog : ComputableInPolyTime
        (fun s : (ℕ × List Bool) × (ℕ × (List (ExtOp × List ℕ) × List ℕ)) ↦
          Nat.log 2 s.1.1 + 1)
        encS encUnary :=
      ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_log_two.comp hn)
        (ComputableInPolyTime.const 1)
    exact ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const c)
      ((ComputableInPolyTime.unary_pow k).comp hlog)
  have h3 := ComputableInPolyTime.unary_le' hdepth hbound
  exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' h1 h2) h3

/-- **`checkACMod c k n w` characterizes valid depth-bounded `Unbounded.extSignature` circuit
encodings.** -/
theorem checkACMod_eq_true_iff {c k n : ℕ} {w : List Bool} :
    checkACMod c k n w = true ↔
      ∃ C : Circuit extSignature n 1,
        Unbounded.encExtCircuit 1 ⟨n, C⟩ = w ∧ C.depth ≤ c * (Nat.log 2 n + 1) ^ k := by
  constructor
  · intro h
    dsimp only [checkACMod] at h
    cases hdec : decRawExtCircuit.decode w with
    | none => simp [hdec] at h
    | some t =>
      simp only [hdec, Option.elim_some, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, hwf⟩, hdepth⟩ := h
      have hraw := (decRawExtCircuit.decode_eq_some_iff w t).mp hdec
      obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp (rawExtCircuitWellFormed_eq_true_iff.mp hwf)
      have hcode := Circuit.code_of_ofCode_eq_some hC
      refine ⟨C, ?_, ?_⟩
      · change encPair encUnary (Circuit.encCode Unbounded.encExtOp) (t.1, C.code) = w
        rw [hcode]
        exact hraw
      · rw [← Circuit.depthWith_one, Circuit.depthWith_le_iff]
        intro j
        rw [Subsingleton.elim j 0, ← Circuit.getD_evalCode_depthInterpretation,
          ← depthsExt_eq_evalCode t.1 C.isCodeFrom_code, hcode]
        have hout0 : t.2.2.headD 0 = (C.outputs 0).toNat := by
          have := congrArg Prod.snd hcode
          rw [← this]
          simp [Circuit.code, List.ofFn_succ]
        rwa [← hout0]
  · rintro ⟨C, rfl, hdepth⟩
    have hraw : Unbounded.encExtCircuit 1 ⟨n, C⟩ =
        encPair encUnary (Circuit.encCode Unbounded.encExtOp) (n, C.code) := rfl
    rw [checkACMod, hraw, decRawExtCircuit.decode_enc]
    simp only [Option.elim_some, decide_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨rawExtCircuitWellFormed_eq_true_iff.mpr (by rw [Circuit.ofCode_code]; rfl), ?_⟩
    have hout0 : C.code.2.headD 0 = (C.outputs 0).toNat := by
      simp [Circuit.code, List.ofFn_succ]
    rw [hout0, depthsExt_eq_evalCode n C.isCodeFrom_code,
      Circuit.getD_evalCode_depthInterpretation, Program.wireDepthsWith_one]
    exact (C.outputDepths_le_depth 0).trans hdepth

end CslibFrontier.Circuits.Boolean
