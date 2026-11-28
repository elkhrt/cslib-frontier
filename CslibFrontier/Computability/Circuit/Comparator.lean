module
-- upstream: candidate

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Tauto

/-!
# Boolean and Three-Valued Comparator Circuits

This module defines Boolean and three-valued (Kleene) comparator circuits and proves fundamental
structural and simulation theorems about them:

* Every comparator gate `(u, v)` updates wire `u` to `x_u ∧ x_v` and wire `v` to `x_u ∨ x_v`,
  preserving the total count of `true` wires (Hamming weight).
* Comparator circuits evaluate monotonically with respect to the pointwise Boolean order and
  commute with substituting `false` or `true` for the indeterminate value `*` in Kleene logic.
* Any comparator circuit with arbitrary gate directions can be compiled into a unidirectional
  comparator circuit (every gate satisfying `u ≤ v`) on `(C.gates.length + 1) * m` wires by
  routing each gate into the next layer of fresh `false`-initialized wires.
* Any three-valued comparator circuit can be simulated by a Boolean comparator circuit on doubled
  wires via the dual-bit encoding `0 ↦ (false, false)`, `1 ↦ (true, true)`, `* ↦ (false, true)`.

## Main definitions

* `CslibFrontier.Computability.Circuit.Comparator.ComparatorGate`: a comparator gate on `m` wires.
* `CslibFrontier.Computability.Circuit.Comparator.ComparatorCircuit`: a sequence of comparator gates
  on `m` wires.
* `CslibFrontier.Computability.Circuit.Comparator.ComparatorCircuit.eval`: Boolean evaluation.
* `CslibFrontier.Computability.Circuit.Comparator.TriBool`, `triAnd`, `triOr`, `TriBool.encode`,
  `TriBool.subst`: three-valued Kleene logic and dual-bit encoding.
* `CslibFrontier.Computability.Circuit.Comparator.ComparatorCircuit.evalTri`: three-valued
  evaluation.
* `CslibFrontier.Computability.Circuit.Comparator.ComparatorCircuit.toUnidirectional`:
  layered unidirectional compilation on `(C.gates.length + 1) * m` wires.
* `CslibFrontier.Computability.Circuit.Comparator.ComparatorCircuit.toDualBit`: dual-bit Boolean
  simulation of a three-valued comparator circuit.

## Main results

* `CslibFrontier.Computability.Circuit.Comparator.ComparatorCircuit.eval_count_true`: conservation
  of the number of `true` wires across comparator circuit evaluation.
* `CslibFrontier.Computability.Circuit.Comparator.ComparatorCircuit.eval_mono`: monotonicity of
  comparator circuit evaluation.
* `ComparatorCircuit.isUnidirectional_toUnidirectional` and
  `ComparatorCircuit.eval_toUnidirectional`: unidirectionality and soundness of the layered
  unidirectional compilation.
* `CslibFrontier.Computability.Circuit.Comparator.ComparatorCircuit.evalTri_subst`: substitution
  of `false` or `true` for `*` commutes with three-valued evaluation.
* `CslibFrontier.Computability.Circuit.Comparator.ComparatorCircuit.eval_toDualBit`: soundness of
  the dual-bit Boolean simulation of three-valued comparator circuits.
-/

public section

namespace CslibFrontier.Computability.Circuit.Comparator

/-- A single comparator gate on `m` wires: `minWire` receives the conjunction and `maxWire`
receives the disjunction of the two input wires. -/
@[ext]
structure ComparatorGate (m : ℕ) where
  /-- Wire receiving the conjunction (`∧`). -/
  minWire : Fin m
  /-- Wire receiving the disjunction (`∨`). -/
  maxWire : Fin m
  deriving DecidableEq, Repr

/-- Apply a single Boolean comparator gate to a wire state vector. -/
@[expose] def ComparatorGate.eval {m : ℕ} (g : ComparatorGate m) (x : Fin m → Bool) :
    Fin m → Bool :=
  fun w =>
    if w = g.minWire then x g.minWire && x g.maxWire
    else if w = g.maxWire then x g.minWire || x g.maxWire
    else x w

/-- A comparator circuit on `m` wires is a list of comparator gates applied sequentially. -/
@[ext]
structure ComparatorCircuit (m : ℕ) where
  /-- Ordered list of comparator gates. -/
  gates : List (ComparatorGate m)
  deriving DecidableEq, Repr

/-- A comparator circuit is unidirectional if every gate points in the non-decreasing direction
`minWire ≤ maxWire`. -/
@[expose] def ComparatorCircuit.IsUnidirectional {m : ℕ} (C : ComparatorCircuit m) : Prop :=
  ∀ g ∈ C.gates, g.minWire ≤ g.maxWire

/-- Evaluate a comparator circuit sequentially on a Boolean input assignment. -/
@[expose] def ComparatorCircuit.eval {m : ℕ} (C : ComparatorCircuit m) (x : Fin m → Bool) :
    Fin m → Bool :=
  C.gates.foldl (fun st g => g.eval st) x

@[simp]
theorem ComparatorCircuit.eval_nil {m : ℕ} (x : Fin m → Bool) :
    (ComparatorCircuit.mk []).eval x = x := rfl

@[simp]
theorem ComparatorCircuit.eval_cons {m : ℕ} (g : ComparatorGate m)
    (gs : List (ComparatorGate m)) (x : Fin m → Bool) :
    (ComparatorCircuit.mk (g :: gs)).eval x = (ComparatorCircuit.mk gs).eval (g.eval x) := rfl

theorem ComparatorCircuit.eval_append {m : ℕ} (gs₁ gs₂ : List (ComparatorGate m))
    (x : Fin m → Bool) :
    (ComparatorCircuit.mk (gs₁ ++ gs₂)).eval x =
      (ComparatorCircuit.mk gs₂).eval ((ComparatorCircuit.mk gs₁).eval x) := by
  simp [ComparatorCircuit.eval, List.foldl_append]

/-- Every Boolean comparator gate preserves the number of `true` wires. -/
theorem ComparatorGate.eval_count_true {m : ℕ} (g : ComparatorGate m) (x : Fin m → Bool) :
    (Finset.univ.filter fun w => g.eval x w = true).card =
      (Finset.univ.filter fun w => x w = true).card := by
  by_cases hsame : g.minWire = g.maxWire
  · congr 1; ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ComparatorGate.eval]
    by_cases hw : w = g.minWire
    · subst hw; simp [hsame]
    · have hw2 : w ≠ g.maxWire := by rwa [← hsame]
      simp [hw, hw2]
  · have hsum : ∀ (s : Finset (Fin m)) (f : Fin m → Bool),
        (s.filter fun w => f w = true).card = ∑ w ∈ s, (f w).toNat := by
      intro s f
      induction s using Finset.cons_induction with
      | empty => simp
      | cons a s ha ih =>
        rw [Finset.filter_cons, Finset.sum_cons]
        cases hfa : f a
        · simp [ih]
        · simp [ha, ih]; omega
    rw [hsum Finset.univ, hsum Finset.univ]
    have hpair : ∀ f : Fin m → Bool,
        ∑ w : Fin m, (f w).toNat =
          (f g.minWire).toNat + (f g.maxWire).toNat +
            ∑ w ∈ Finset.univ.filter (fun w => w ≠ g.minWire ∧ w ≠ g.maxWire), (f w).toNat := by
      intro f
      have h1 : Finset.univ =
          insert g.minWire (insert g.maxWire
            (Finset.univ.filter fun w => w ≠ g.minWire ∧ w ≠ g.maxWire)) := by
        ext w; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and, true_iff]
        tauto
      conv_lhs => rw [h1]
      rw [Finset.sum_insert (by simp [hsame]), Finset.sum_insert (by simp)]
      omega
    rw [hpair (g.eval x), hpair x]
    have hrest : ∑ w ∈ Finset.univ.filter (fun w => w ≠ g.minWire ∧ w ≠ g.maxWire),
          (g.eval x w).toNat =
        ∑ w ∈ Finset.univ.filter (fun w => w ≠ g.minWire ∧ w ≠ g.maxWire), (x w).toNat := by
      refine Finset.sum_congr rfl fun w hw => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      simp [ComparatorGate.eval, hw.1, hw.2]
    rw [hrest]
    simp only [ComparatorGate.eval, ↓reduceIte, Ne.symm hsame]
    cases x g.minWire <;> cases x g.maxWire <;> rfl

/-- Conservation of ones: evaluating any comparator circuit preserves the count of `true` wires. -/
theorem ComparatorCircuit.eval_count_true {m : ℕ} (C : ComparatorCircuit m) (x : Fin m → Bool) :
    (Finset.univ.filter fun w => C.eval x w = true).card =
      (Finset.univ.filter fun w => x w = true).card := by
  rcases C with ⟨gs⟩
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [ComparatorCircuit.eval_cons, ih, g.eval_count_true]

/-- Pointwise monotonicity of a single comparator gate. -/
theorem ComparatorGate.eval_mono {m : ℕ} (g : ComparatorGate m) {x y : Fin m → Bool}
    (h : ∀ w, x w ≤ y w) : ∀ w, g.eval x w ≤ g.eval y w := by
  intro w
  simp only [ComparatorGate.eval]
  split_ifs
  · have h1 := h g.minWire; have h2 := h g.maxWire
    cases hx1 : x g.minWire <;> cases hx2 : x g.maxWire <;>
      cases hy1 : y g.minWire <;> cases hy2 : y g.maxWire <;> simp_all
  · have h1 := h g.minWire; have h2 := h g.maxWire
    cases hx1 : x g.minWire <;> cases hx2 : x g.maxWire <;>
      cases hy1 : y g.minWire <;> cases hy2 : y g.maxWire <;> simp_all
  · exact h w

/-- Pointwise monotonicity of comparator circuit evaluation. -/
theorem ComparatorCircuit.eval_mono {m : ℕ} (C : ComparatorCircuit m) {x y : Fin m → Bool}
    (h : ∀ w, x w ≤ y w) : ∀ w, C.eval x w ≤ C.eval y w := by
  rcases C with ⟨gs⟩
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    exact ih (g.eval_mono h)

/-! ### Unidirectional simulation -/

/-- Wire index for wire `w : Fin m` in layer `k` of an `L`-layer circuit (`L * m` total wires). -/
@[expose] def layerWire {m L : ℕ} (k : ℕ) (hk : k < L) (w : Fin m) : Fin (L * m) :=
  ⟨k * m + w.1, by
    have hw := w.isLt
    have hmul : (k + 1) * m ≤ L * m := Nat.mul_le_mul_right m hk
    have hexp : (k + 1) * m = k * m + m := Nat.succ_mul k m
    omega⟩

/-- Gates implementing one layer transition from layer `k` to layer `k + 1` for comparator gate `g`
using unidirectional (`minWire ≤ maxWire`) gates only, assuming layer `k + 1` starts all `false`. -/
@[expose] def layerStepGates {m L : ℕ} (k : ℕ) (hk : k + 1 < L) (g : ComparatorGate m) :
    List (ComparatorGate (L * m)) :=
  have hk0 : k < L := by omega
  if g.minWire ≤ g.maxWire then
    ⟨layerWire k hk0 g.minWire, layerWire k hk0 g.maxWire⟩ ::
      (List.finRange m).map fun w => ⟨layerWire k hk0 w, layerWire (k + 1) hk w⟩
  else
    ⟨layerWire k hk0 g.maxWire, layerWire k hk0 g.minWire⟩ ::
      (List.finRange m).map fun w =>
        if w = g.minWire then ⟨layerWire k hk0 g.maxWire, layerWire (k + 1) hk g.minWire⟩
        else if w = g.maxWire then ⟨layerWire k hk0 g.minWire, layerWire (k + 1) hk g.maxWire⟩
        else ⟨layerWire k hk0 w, layerWire (k + 1) hk w⟩

private theorem layerStepGates_unidirectional {m L : ℕ} (k : ℕ) (hk : k + 1 < L)
    (g : ComparatorGate m) :
    ∀ g' ∈ layerStepGates k hk g, g'.minWire ≤ g'.maxWire := by
  intro g' hg'
  unfold layerStepGates at hg'
  split_ifs at hg' with hle
  · rcases List.mem_cons.mp hg' with rfl | hmem
    · change k * m + g.minWire.1 ≤ k * m + g.maxWire.1
      have : g.minWire.1 ≤ g.maxWire.1 := hle
      omega
    · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hmem
      change k * m + w.1 ≤ (k + 1) * m + w.1
      have : (k + 1) * m = k * m + m := Nat.succ_mul k m
      omega
  · rcases List.mem_cons.mp hg' with rfl | hmem
    · change k * m + g.maxWire.1 ≤ k * m + g.minWire.1
      have : ¬ g.minWire.1 ≤ g.maxWire.1 := hle
      omega
    · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hmem
      have hmul : (k + 1) * m = k * m + m := Nat.succ_mul k m
      split_ifs
      · change k * m + g.maxWire.1 ≤ (k + 1) * m + g.minWire.1
        have := g.maxWire.isLt; omega
      · change k * m + g.minWire.1 ≤ (k + 1) * m + g.maxWire.1
        have := g.minWire.isLt; omega
      · change k * m + w.1 ≤ (k + 1) * m + w.1; omega

/-- Helper compiling a suffix of `gs` starting at layer `k` inside an `L`-layer circuit. -/
@[expose] def compileUnidirectionalAux {m L : ℕ} (k : ℕ) :
    (gs : List (ComparatorGate m)) → k + gs.length < L → List (ComparatorGate (L * m))
  | [], _ => []
  | g :: gs, h =>
    layerStepGates k (by simp at h; omega) g ++
      compileUnidirectionalAux (k + 1) gs (by simp at h; omega)

/-- Layered unidirectional compilation of a comparator circuit `C` on `(C.gates.length + 1) * m`
wires. Every gate satisfies `minWire ≤ maxWire`. -/
@[expose] def ComparatorCircuit.toUnidirectional {m : ℕ} (C : ComparatorCircuit m) :
    ComparatorCircuit ((C.gates.length + 1) * m) :=
  ⟨compileUnidirectionalAux 0 C.gates (by omega)⟩

/-- Input vector on `(C.gates.length + 1) * m` wires placing `x` in layer `0` and `false` in all
higher layers. -/
@[expose] def padInput {m L : ℕ} (x : Fin m → Bool) : Fin (L * m) → Bool :=
  fun i => if h : i.1 < m then x ⟨i.1, h⟩ else false

private theorem compileUnidirectionalAux_unidirectional {m L : ℕ} :
    ∀ (k : ℕ) (gs : List (ComparatorGate m)) (h : k + gs.length < L),
      ∀ g' ∈ compileUnidirectionalAux k gs h, g'.minWire ≤ g'.maxWire
  | _, [], _, _, hg' => nomatch hg'
  | k, g :: gs, h, g', hg' => by
    simp only [compileUnidirectionalAux, List.mem_append] at hg'
    rcases hg' with h1 | h2
    · exact layerStepGates_unidirectional k _ g g' h1
    · exact compileUnidirectionalAux_unidirectional (k + 1) gs _ g' h2

/-- Every gate in `C.toUnidirectional` is unidirectional (`minWire ≤ maxWire`). -/
theorem ComparatorCircuit.isUnidirectional_toUnidirectional {m : ℕ} (C : ComparatorCircuit m) :
    C.toUnidirectional.IsUnidirectional :=
  compileUnidirectionalAux_unidirectional 0 C.gates (by omega)

private theorem layerWire_inj {m L k₁ k₂ : ℕ} {h₁ : k₁ < L} {h₂ : k₂ < L} {w₁ w₂ : Fin m}
    (h : layerWire k₁ h₁ w₁ = layerWire k₂ h₂ w₂) : k₁ = k₂ ∧ w₁ = w₂ := by
  have hv : k₁ * m + w₁.1 = k₂ * m + w₂.1 := congrArg Fin.val h
  have hw1 := w₁.isLt; have hw2 := w₂.isLt
  have hk : k₁ = k₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (k₁ + 1) * m ≤ k₂ * m := Nat.mul_le_mul_right m hlt
      have : (k₁ + 1) * m = k₁ * m + m := Nat.succ_mul k₁ m
      omega
    · have : (k₂ + 1) * m ≤ k₁ * m := Nat.mul_le_mul_right m hgt
      have : (k₂ + 1) * m = k₂ * m + m := Nat.succ_mul k₂ m
      omega
  subst hk
  exact ⟨rfl, Fin.ext (by omega)⟩

private theorem eval_copyGates {m L : ℕ} (k : ℕ) (hk0 : k < L) (hk : k + 1 < L)
    (src : Fin m → Fin m) (hsrc_inj : Function.Injective src) (ws : List (Fin m))
    (hnodup : ws.Nodup) (st : Fin (L * m) → Bool)
    (hzero : ∀ w ∈ ws, st (layerWire (k + 1) hk w) = false) :
    let gs : List (ComparatorGate (L * m)) :=
      ws.map fun w => ⟨layerWire k hk0 (src w), layerWire (k + 1) hk w⟩
    (∀ w ∈ ws, (ComparatorCircuit.mk gs).eval st (layerWire (k + 1) hk w) =
      st (layerWire k hk0 (src w))) ∧
    (∀ (k' : ℕ) (hk' : k' < L) (w : Fin m), k + 1 < k' →
      (ComparatorCircuit.mk gs).eval st (layerWire k' hk' w) = st (layerWire k' hk' w)) ∧
    (∀ w : Fin m, w ∉ ws →
      (ComparatorCircuit.mk gs).eval st (layerWire (k + 1) hk w) =
        st (layerWire (k + 1) hk w)) := by
  induction ws generalizing st with
  | nil => exact ⟨fun _ h => False.elim (List.not_mem_nil h), fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  | cons a ws ih =>
    simp only [List.nodup_cons] at hnodup
    obtain ⟨ha_notin, hws_nodup⟩ := hnodup
    set g₀ : ComparatorGate (L * m) := ⟨layerWire k hk0 (src a), layerWire (k + 1) hk a⟩
    have hstep_other : ∀ w ∈ ws, g₀.eval st (layerWire (k + 1) hk w) = false := by
      intro w hw
      have hne1 : layerWire (k + 1) hk w ≠ layerWire k hk0 (src a) := fun h => by
        have := (layerWire_inj h).1; omega
      have hne2 : layerWire (k + 1) hk w ≠ layerWire (k + 1) hk a := fun h =>
        ha_notin ((layerWire_inj h).2 ▸ hw)
      simp only [ComparatorGate.eval, g₀, hne1, hne2, ↓reduceIte]
      exact hzero w (List.mem_cons_of_mem a hw)
    obtain ⟨ih1, ih2, ih3⟩ := ih hws_nodup (g₀.eval st) hstep_other
    have hgs_cons : (ComparatorCircuit.mk
        ((a :: ws).map fun w => ⟨layerWire k hk0 (src w), layerWire (k + 1) hk w⟩)).eval st =
        (ComparatorCircuit.mk
          (ws.map fun w => ⟨layerWire k hk0 (src w), layerWire (k + 1) hk w⟩)).eval
          (g₀.eval st) := rfl
    refine ⟨fun w hw => ?_, fun k' hk' w hk'gt => ?_, fun w hwnot => ?_⟩
    · rw [hgs_cons]
      rcases List.mem_cons.mp hw with rfl | hw'
      · rw [ih3 w ha_notin]
        have hne : layerWire (k + 1) hk w ≠ layerWire k hk0 (src w) := fun h => by
          have := (layerWire_inj h).1; omega
        simp [ComparatorGate.eval, g₀, hne, hzero w List.mem_cons_self]
      · rw [ih1 w hw']
        have hne1 : layerWire k hk0 (src w) ≠ layerWire k hk0 (src a) := fun h =>
          ha_notin (hsrc_inj (layerWire_inj h).2 ▸ hw')
        have hne2 : layerWire k hk0 (src w) ≠ layerWire (k + 1) hk a := fun h => by
          have := (layerWire_inj h).1; omega
        simp [ComparatorGate.eval, g₀, hne1, hne2]
    · rw [hgs_cons, ih2 k' hk' w hk'gt]
      have hne1 : layerWire k' hk' w ≠ layerWire k hk0 (src a) := fun h => by
        have := (layerWire_inj h).1; omega
      have hne2 : layerWire k' hk' w ≠ layerWire (k + 1) hk a := fun h => by
        have := (layerWire_inj h).1; omega
      simp [ComparatorGate.eval, g₀, hne1, hne2]
    · rw [hgs_cons]
      have hne_a : w ≠ a := fun h => hwnot (h ▸ List.mem_cons_self)
      have hnot_ws : w ∉ ws := fun h => hwnot (List.mem_cons_of_mem a h)
      rw [ih3 w hnot_ws]
      have hne1 : layerWire (k + 1) hk w ≠ layerWire k hk0 (src a) := fun h => by
        have := (layerWire_inj h).1; omega
      have hne2 : layerWire (k + 1) hk w ≠ layerWire (k + 1) hk a := fun h =>
        hne_a (layerWire_inj h).2
      simp [ComparatorGate.eval, g₀, hne1, hne2]

private theorem eval_layerStepGates {m L : ℕ} (k : ℕ) (hk : k + 1 < L) (g : ComparatorGate m)
    (x : Fin m → Bool) (st : Fin (L * m) → Bool)
    (hcur : ∀ w : Fin m, st (layerWire k (by omega) w) = x w)
    (hzero : ∀ (k' : ℕ) (hk' : k' < L) (w : Fin m), k < k' → st (layerWire k' hk' w) = false) :
    (∀ w : Fin m,
      (ComparatorCircuit.mk (layerStepGates k hk g)).eval st (layerWire (k + 1) hk w) =
        g.eval x w) ∧
    (∀ (k' : ℕ) (hk' : k' < L) (w : Fin m), k + 1 < k' →
      (ComparatorCircuit.mk (layerStepGates k hk g)).eval st (layerWire k' hk' w) = false) := by
  have hk0 : k < L := by omega
  unfold layerStepGates
  dsimp only
  split_ifs with hle
  · set g₀ : ComparatorGate (L * m) := ⟨layerWire k hk0 g.minWire, layerWire k hk0 g.maxWire⟩
    have hst1_zero : ∀ w ∈ List.finRange m, g₀.eval st (layerWire (k + 1) hk w) = false := by
      intro w _
      have hne1 : layerWire (k + 1) hk w ≠ layerWire k hk0 g.minWire := fun h => by
        have := (layerWire_inj h).1; omega
      have hne2 : layerWire (k + 1) hk w ≠ layerWire k hk0 g.maxWire := fun h => by
        have := (layerWire_inj h).1; omega
      simp [ComparatorGate.eval, g₀, hne1, hne2, hzero (k + 1) hk w (by omega)]
    obtain ⟨hc1, hc2, -⟩ := eval_copyGates k hk0 hk (fun w => w) (fun _ _ h => h) (List.finRange m)
      (List.nodup_finRange m) (g₀.eval st) hst1_zero
    refine ⟨fun w => ?_, fun k' hk' w hk'gt => ?_⟩
    · rw [ComparatorCircuit.eval_cons]
      have h1 := hc1 w (List.mem_finRange w)
      rw [h1]
      simp only [ComparatorGate.eval, g₀]
      by_cases hw1 : w = g.minWire
      · subst hw1; simp [hcur]
      · have hne1 : layerWire k hk0 w ≠ layerWire k hk0 g.minWire := fun h =>
          hw1 (layerWire_inj h).2
        by_cases hw2 : w = g.maxWire
        · subst hw2; simp [hne1, hw1, hcur]
        · have hne2 : layerWire k hk0 w ≠ layerWire k hk0 g.maxWire := fun h =>
            hw2 (layerWire_inj h).2
          simp [hne1, hne2, hw1, hw2, hcur]
    · rw [ComparatorCircuit.eval_cons]
      have h2 := hc2 k' hk' w hk'gt
      rw [h2]
      have hne1 : layerWire k' hk' w ≠ layerWire k hk0 g.minWire := fun h => by
        have := (layerWire_inj h).1; omega
      have hne2 : layerWire k' hk' w ≠ layerWire k hk0 g.maxWire := fun h => by
        have := (layerWire_inj h).1; omega
      simp [ComparatorGate.eval, g₀, hne1, hne2, hzero k' hk' w (by omega)]
  · have hne_uv : g.minWire ≠ g.maxWire := fun h => hle (le_of_eq h)
    set g₀ : ComparatorGate (L * m) := ⟨layerWire k hk0 g.maxWire, layerWire k hk0 g.minWire⟩
    let src : Fin m → Fin m := fun w =>
      if w = g.minWire then g.maxWire else if w = g.maxWire then g.minWire else w
    have hsrc_inj : Function.Injective src := by
      intro a b h
      dsimp only [src] at h
      by_cases h1 : a = g.minWire <;> by_cases h2 : a = g.maxWire <;>
        by_cases h3 : b = g.minWire <;> by_cases h4 : b = g.maxWire <;> simp_all
    have hmap_eq :
        ((List.finRange m).map (fun w =>
          (if w = g.minWire then ⟨layerWire k hk0 g.maxWire, layerWire (k + 1) hk g.minWire⟩
          else if w = g.maxWire then ⟨layerWire k hk0 g.minWire, layerWire (k + 1) hk g.maxWire⟩
          else ⟨layerWire k hk0 w, layerWire (k + 1) hk w⟩ : ComparatorGate (L * m)))) =
        ((List.finRange m).map fun w => ⟨layerWire k hk0 (src w), layerWire (k + 1) hk w⟩) := by
      refine List.map_congr_left fun w _ => ?_
      dsimp only [src]
      split_ifs with h1 h2
      · subst h1; rfl
      · subst h2; rfl
      · rfl
    rw [hmap_eq]
    have hst1_zero : ∀ w ∈ List.finRange m, g₀.eval st (layerWire (k + 1) hk w) = false := by
      intro w _
      have hne1 : layerWire (k + 1) hk w ≠ layerWire k hk0 g.maxWire := fun h => by
        have := (layerWire_inj h).1; omega
      have hne2 : layerWire (k + 1) hk w ≠ layerWire k hk0 g.minWire := fun h => by
        have := (layerWire_inj h).1; omega
      simp [ComparatorGate.eval, g₀, hne1, hne2, hzero (k + 1) hk w (by omega)]
    obtain ⟨hc1, hc2, -⟩ := eval_copyGates k hk0 hk src hsrc_inj (List.finRange m)
      (List.nodup_finRange m) (g₀.eval st) hst1_zero
    refine ⟨fun w => ?_, fun k' hk' w hk'gt => ?_⟩
    · rw [ComparatorCircuit.eval_cons, hc1 w (List.mem_finRange w)]
      dsimp only [src]
      by_cases hw1 : w = g.minWire
      · subst hw1
        simp only [↓reduceIte, ComparatorGate.eval, g₀, hcur]
        cases x g.minWire <;> cases x g.maxWire <;> rfl
      · by_cases hw2 : w = g.maxWire
        · subst hw2
          have hne_lw : layerWire k hk0 g.minWire ≠ layerWire k hk0 g.maxWire := fun h =>
            hne_uv (layerWire_inj h).2
          simp only [hw1, ↓reduceIte, ComparatorGate.eval, g₀, hne_lw, hcur]
          cases x g.minWire <;> cases x g.maxWire <;> rfl
        · have hne1 : layerWire k hk0 w ≠ layerWire k hk0 g.maxWire := fun h =>
            hw2 (layerWire_inj h).2
          have hne2 : layerWire k hk0 w ≠ layerWire k hk0 g.minWire := fun h =>
            hw1 (layerWire_inj h).2
          simp [hw1, hw2, ComparatorGate.eval, g₀, hne1, hne2, hcur]
    · rw [ComparatorCircuit.eval_cons, hc2 k' hk' w hk'gt]
      have hne1 : layerWire k' hk' w ≠ layerWire k hk0 g.maxWire := fun h => by
        have := (layerWire_inj h).1; omega
      have hne2 : layerWire k' hk' w ≠ layerWire k hk0 g.minWire := fun h => by
        have := (layerWire_inj h).1; omega
      simp [ComparatorGate.eval, g₀, hne1, hne2, hzero k' hk' w (by omega)]

private theorem eval_compileUnidirectionalAux {m L : ℕ} :
    ∀ (gs : List (ComparatorGate m)) (k : ℕ) (h : k + gs.length < L)
      (x : Fin m → Bool) (st : Fin (L * m) → Bool),
      (∀ w : Fin m, st (layerWire k (by omega) w) = x w) →
      (∀ (k' : ℕ) (hk' : k' < L) (w : Fin m), k < k' → st (layerWire k' hk' w) = false) →
      ∀ w : Fin m,
        (ComparatorCircuit.mk (compileUnidirectionalAux k gs h)).eval st
          (layerWire (k + gs.length) h w) =
          (ComparatorCircuit.mk gs).eval x w
  | [], k, h, x, st, hcur, _, w => by
    simp only [compileUnidirectionalAux, ComparatorCircuit.eval_nil]
    exact hcur w
  | g :: gs, k, h, x, st, hcur, hzero, w => by
    simp only [compileUnidirectionalAux, ComparatorCircuit.eval_append, ComparatorCircuit.eval_cons]
    obtain ⟨h1, h2⟩ := eval_layerStepGates k (by simp at h; omega) g x st hcur hzero
    have hih := eval_compileUnidirectionalAux gs (k + 1) (by simp at h; omega) (g.eval x)
      ((ComparatorCircuit.mk (layerStepGates k (by simp at h; omega) g)).eval st) h1 h2 w
    have hidx : layerWire (k + (g :: gs).length) h w =
        layerWire (k + 1 + gs.length) (by simp at h; omega) w := by
      apply Fin.ext
      simp only [layerWire, List.length_cons]
      congr 1; congr 1; omega
    rw [hidx]
    exact hih

/-- Soundness of layered unidirectional compilation: evaluating `C.toUnidirectional` on
`padInput x` produces `C.eval x w` on the final layer wire `layerWire C.gates.length _ w`. -/
theorem ComparatorCircuit.eval_toUnidirectional {m : ℕ} (C : ComparatorCircuit m)
    (x : Fin m → Bool) (w : Fin m) :
    C.toUnidirectional.eval (padInput x)
      (layerWire C.gates.length (Nat.lt_succ_self _) w) = C.eval x w := by
  have hcur : ∀ u : Fin m, padInput (L := C.gates.length + 1) x
      (layerWire 0 (Nat.zero_lt_succ _) u) = x u := fun u => by
    simp [padInput, layerWire, u.isLt]
  have hzero : ∀ (k' : ℕ) (hk' : k' < C.gates.length + 1) (u : Fin m), 0 < k' →
      padInput (L := C.gates.length + 1) x (layerWire k' hk' u) = false := fun k' hk' u hk'pos => by
    have hnot : ¬ (k' * m + u.1 < m) := by
      have : 1 * m ≤ k' * m := Nat.mul_le_mul_right m hk'pos
      omega
    simp [padInput, layerWire, hnot]
  have hres := eval_compileUnidirectionalAux C.gates 0 (by omega) x
    (padInput (L := C.gates.length + 1) x) hcur hzero w
  have hidx : layerWire (0 + C.gates.length) (by omega) w =
      layerWire C.gates.length (Nat.lt_succ_self _) w := by
    apply Fin.ext; simp [layerWire]
  rw [← hidx]
  exact hres

/-! ### Three-valued Kleene comparator circuits and dual-bit Boolean simulation -/

/-- Three-valued Kleene logic values `{0, 1, *}`. -/
inductive TriBool : Type where
  | zero : TriBool
  | one : TriBool
  | star : TriBool
  deriving DecidableEq, Repr

/-- Three-valued Kleene conjunction. -/
@[expose] def triAnd : TriBool → TriBool → TriBool
  | .zero, _ | _, .zero => .zero
  | .one, .one => .one
  | _, _ => .star

/-- Three-valued Kleene disjunction. -/
@[expose] def triOr : TriBool → TriBool → TriBool
  | .one, _ | _, .one => .one
  | .zero, .zero => .zero
  | _, _ => .star

/-- Dual-bit encoding `0 ↦ (false, false)`, `1 ↦ (true, true)`, `* ↦ (false, true)`. -/
@[expose] def TriBool.encode : TriBool → Bool × Bool
  | .zero => (false, false)
  | .one => (true, true)
  | .star => (false, true)

/-- Substitute `v : Bool` for the indeterminate value `*`. -/
@[expose] def TriBool.subst (v : Bool) : TriBool → Bool
  | .zero => false
  | .one => true
  | .star => v

theorem triAnd_encode (p q : TriBool) :
    (triAnd p q).encode = (p.encode.1 && q.encode.1, p.encode.2 && q.encode.2) := by
  cases p <;> cases q <;> rfl

theorem triOr_encode (p q : TriBool) :
    (triOr p q).encode = (p.encode.1 || q.encode.1, p.encode.2 || q.encode.2) := by
  cases p <;> cases q <;> rfl

theorem triAnd_subst (v : Bool) (p q : TriBool) :
    (triAnd p q).subst v = (p.subst v && q.subst v) := by
  cases v <;> cases p <;> cases q <;> rfl

theorem triOr_subst (v : Bool) (p q : TriBool) :
    (triOr p q).subst v = (p.subst v || q.subst v) := by
  cases v <;> cases p <;> cases q <;> rfl

/-- Apply a comparator gate to a three-valued wire state vector. -/
@[expose] def ComparatorGate.evalTri {m : ℕ} (g : ComparatorGate m) (x : Fin m → TriBool) :
    Fin m → TriBool :=
  fun w =>
    if w = g.minWire then triAnd (x g.minWire) (x g.maxWire)
    else if w = g.maxWire then triOr (x g.minWire) (x g.maxWire)
    else x w

/-- Evaluate a comparator circuit sequentially on a three-valued input assignment. -/
@[expose] def ComparatorCircuit.evalTri {m : ℕ} (C : ComparatorCircuit m) (x : Fin m → TriBool) :
    Fin m → TriBool :=
  C.gates.foldl (fun st g => g.evalTri st) x

/-- Substituting `v : Bool` for `*` commutes with three-valued comparator circuit evaluation. -/
theorem ComparatorCircuit.evalTri_subst {m : ℕ} (C : ComparatorCircuit m) (x : Fin m → TriBool)
    (v : Bool) (w : Fin m) :
    (C.evalTri x w).subst v = C.eval (fun i => (x i).subst v) w := by
  rcases C with ⟨gs⟩
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [ComparatorCircuit.evalTri, ComparatorCircuit.eval, List.foldl_cons] at ih ⊢
    rw [ih (g.evalTri x)]
    have hfn : (fun i => (g.evalTri x i).subst v) = g.eval (fun i => (x i).subst v) := by
      funext i
      simp only [ComparatorGate.evalTri, ComparatorGate.eval]
      split_ifs
      · exact triAnd_subst v _ _
      · exact triOr_subst v _ _
      · rfl
    rw [hfn]

/-- Dual-bit encoding of a three-valued wire vector onto `2 * m` Boolean wires:
wire `2 * w` receives `(x w).encode.1` and wire `2 * w + 1` receives `(x w).encode.2`. -/
@[expose] def encodeTriVec {m : ℕ} (x : Fin m → TriBool) : Fin (2 * m) → Bool :=
  fun i => if i.1 % 2 =
    0 then (x ⟨i.1 / 2, by omega⟩).encode.1 else (x ⟨i.1 / 2, by omega⟩).encode.2

/-- Dual-bit Boolean comparator circuit simulating three-valued evaluation on `2 * m` wires. -/
@[expose] def ComparatorCircuit.toDualBit {m : ℕ} (C : ComparatorCircuit m) :
    ComparatorCircuit (2 * m) :=
  ⟨C.gates.flatMap fun g =>
    [⟨⟨2 * g.minWire.1, by omega⟩, ⟨2 * g.maxWire.1, by omega⟩⟩,
     ⟨⟨2 * g.minWire.1 + 1, by omega⟩, ⟨2 * g.maxWire.1 + 1, by omega⟩⟩]⟩

/-- Dual-bit Boolean simulation soundness: evaluating `C.toDualBit` on `encodeTriVec x` produces
`encodeTriVec (C.evalTri x)`. -/
theorem ComparatorCircuit.eval_toDualBit {m : ℕ} (C : ComparatorCircuit m) (x : Fin m → TriBool) :
    C.toDualBit.eval (encodeTriVec x) = encodeTriVec (C.evalTri x) := by
  rcases C with ⟨gs⟩
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [ComparatorCircuit.toDualBit, List.flatMap_cons, ComparatorCircuit.eval_append,
      ComparatorCircuit.evalTri, List.foldl_cons]
    have hstep :
        (ComparatorCircuit.mk
          [⟨⟨2 * g.minWire.1, by omega⟩, ⟨2 * g.maxWire.1, by omega⟩⟩,
           ⟨⟨2 * g.minWire.1 + 1, by omega⟩, ⟨2 * g.maxWire.1 + 1, by omega⟩⟩]).eval
            (encodeTriVec x) =
          encodeTriVec (g.evalTri x) := by
      funext i
      simp only [ComparatorCircuit.eval_cons, ComparatorCircuit.eval_nil]
      have henc0 : ∀ (y : Fin m → TriBool) (w : Fin m),
          encodeTriVec y ⟨2 * w.1, by have := w.isLt; omega⟩ = (y w).encode.1 := fun y w => by
        simp [encodeTriVec]
      have henc1 : ∀ (y : Fin m → TriBool) (w : Fin m),
          encodeTriVec y ⟨2 * w.1 + 1, by have := w.isLt; omega⟩ = (y w).encode.2 := fun y w => by
        simp only [encodeTriVec]
        have hodd : ¬ ((2 * w.1 + 1) % 2 = 0) := by omega
        simp only [hodd, ↓reduceIte]
        have hfin : (⟨(2 * w.1 + 1) / 2, by have := w.isLt; omega⟩ : Fin m) = w :=
          Fin.ext (by dsimp; omega)
        rw [hfin]
      have hne_eo : ∀ (u v : Fin m),
          (⟨2 * u.1, by have := u.isLt; omega⟩ : Fin (2 * m)) ≠
            ⟨2 * v.1 + 1, by have := v.isLt; omega⟩ := fun u v h => by
        have hv := congrArg Fin.val h; dsimp at hv; omega
      have hne_oe : ∀ (u v : Fin m),
          (⟨2 * u.1 + 1, by have := u.isLt; omega⟩ : Fin (2 * m)) ≠
            ⟨2 * v.1, by have := v.isLt; omega⟩ := fun u v h =>
        hne_eo v u h.symm
      by_cases hev : i.1 % 2 = 0
      · obtain ⟨w, hi_eq⟩ : ∃ w : Fin m, i = ⟨2 * w.1, by have := w.isLt; omega⟩ :=
          ⟨⟨i.1 / 2, by omega⟩, Fin.ext (by dsimp; omega)⟩
        rw [hi_eq, henc0]
        simp only [ComparatorGate.eval, hne_eo, ↓reduceIte]
        by_cases hw1 : w = g.minWire
        · subst hw1
          simp only [↓reduceIte, ComparatorGate.evalTri, henc0, triAnd_encode]
        · have hf1 : (⟨2 * w.1, by have := w.isLt; omega⟩ : Fin (2 * m)) ≠
              ⟨2 * g.minWire.1, by have := g.minWire.isLt; omega⟩ :=
            fun h => hw1 (Fin.ext (by have hv := congrArg Fin.val h; dsimp at hv; omega))
          by_cases hw2 : w = g.maxWire
          · subst hw2
            simp only [hf1, hw1, ↓reduceIte, ComparatorGate.evalTri, henc0, triOr_encode]
          · have hf2 : (⟨2 * w.1, by have := w.isLt; omega⟩ : Fin (2 * m)) ≠
                ⟨2 * g.maxWire.1, by have := g.maxWire.isLt; omega⟩ :=
              fun h => hw2 (Fin.ext (by have hv := congrArg Fin.val h; dsimp at hv; omega))
            simp only [hf1, hf2, hw1, hw2, ↓reduceIte, ComparatorGate.evalTri, henc0]
      · obtain ⟨w, hi_eq⟩ : ∃ w : Fin m, i = ⟨2 * w.1 + 1, by have := w.isLt; omega⟩ :=
          ⟨⟨i.1 / 2, by omega⟩, Fin.ext (by dsimp; omega)⟩
        rw [hi_eq, henc1]
        simp only [ComparatorGate.eval, hne_oe, ↓reduceIte]
        by_cases hw1 : w = g.minWire
        · subst hw1
          simp only [↓reduceIte, ComparatorGate.evalTri, henc1, triAnd_encode]
        · have hf1 : (⟨2 * w.1 + 1, by have := w.isLt; omega⟩ : Fin (2 * m)) ≠
              ⟨2 * g.minWire.1 + 1, by have := g.minWire.isLt; omega⟩ :=
            fun h => hw1 (Fin.ext (by have hv := congrArg Fin.val h; dsimp at hv; omega))
          by_cases hw2 : w = g.maxWire
          · subst hw2
            simp only [hf1, hw1, ↓reduceIte, ComparatorGate.evalTri, henc1, triOr_encode]
          · have hf2 : (⟨2 * w.1 + 1, by have := w.isLt; omega⟩ : Fin (2 * m)) ≠
                ⟨2 * g.maxWire.1 + 1, by have := g.maxWire.isLt; omega⟩ :=
              fun h => hw2 (Fin.ext (by have hv := congrArg Fin.val h; dsimp at hv; omega))
            simp only [hf1, hf2, hw1, hw2, ↓reduceIte, ComparatorGate.evalTri, henc1]
    rw [hstep]
    exact ih (g.evalTri x)

end CslibFrontier.Computability.Circuit.Comparator
