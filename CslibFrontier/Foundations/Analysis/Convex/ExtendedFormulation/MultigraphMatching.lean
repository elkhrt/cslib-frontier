module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite

import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Edmonds' Perfect Matching Polytope Theorem for Loopless Multigraphs

Formalizes Edmonds' perfect matching polytope theorem for finite loopless multigraphs:

- `LooplessMultigraph`: finite loopless multigraphs with vertex incidence `inc`, cuts `cut`,
  perfect matchings `IsPerfectMatching`, V-polytope `pmPolytope`, and Edmonds H-polytope
  `pmHPolytope`.
- `LooplessMultigraph.pmPolytope_eq_hPolytope`: Edmonds' perfect matching polytope theorem, proved
  by induction on `|V| + |E|` via Krein–Milman extreme points, odd-set shrinking, and a 2-regular
  cycle-parity argument.
-/

public section

namespace CslibFrontier.ExtendedFormulation

/-! ### Finite loopless multigraphs and Edmonds' Perfect Matching Polytope Theorem -/

section MultigraphMatching

/-- A loopless multigraph with vertex type `V` and edge index type `E`. -/
@[ext] structure LooplessMultigraph (V E : Type*) where
  /-- First endpoint of edge `e`. -/
  fst : E → V
  /-- Second endpoint of edge `e`. -/
  snd : E → V
  /-- No self-loops: endpoints of every edge are distinct. -/
  ne : ∀ e, fst e ≠ snd e

namespace LooplessMultigraph

variable {V E : Type*}

/-- Edge `e` is incident to vertex `v`. -/
@[expose] def inc (M : LooplessMultigraph V E) (e : E) (v : V) : Prop :=
  M.fst e = v ∨ M.snd e = v

/-- Endpoint characterization of vertex incidence in a loopless multigraph. -/
theorem inc_iff (M : LooplessMultigraph V E) (e : E) (v : V) :
    M.inc e v ↔ M.fst e = v ∨ M.snd e = v := Iff.rfl

instance instDecidableInc [DecidableEq V] (M : LooplessMultigraph V E) (e : E) (v : V) :
    Decidable (M.inc e v) :=
  inferInstanceAs (Decidable (M.fst e = v ∨ M.snd e = v))

/-- The cut `δ(U)` of a vertex subset `U ⊆ V`: edges with exactly one endpoint in `U`. -/
@[expose] def cut [DecidableEq V] [Fintype E] (M : LooplessMultigraph V E) (U : Finset V) :
    Finset E :=
  Finset.univ.filter fun e => (M.fst e ∈ U ∧ M.snd e ∉ U) ∨ (M.fst e ∉ U ∧ M.snd e ∈ U)

theorem mem_cut_iff [DecidableEq V] [Fintype E] (M : LooplessMultigraph V E) (U : Finset V)
    (e : E) :
    e ∈ M.cut U ↔ (M.fst e ∈ U ∧ M.snd e ∉ U) ∨ (M.fst e ∉ U ∧ M.snd e ∈ U) := by
  simp [cut]

theorem cut_singleton_eq_inc [DecidableEq V] [Fintype E] (M : LooplessMultigraph V E) (v : V) :
    M.cut {v} = Finset.univ.filter fun e => M.inc e v := by
  ext e
  rw [mem_cut_iff, Finset.mem_filter]
  simp only [Finset.mem_singleton, Finset.mem_univ, true_and, inc]
  have hne := M.ne e
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · exact Or.inl h1
    · exact Or.inr h2
  · rintro (h1 | h2)
    · exact Or.inl ⟨h1, fun h2 => hne (h1.trans h2.symm)⟩
    · exact Or.inr ⟨fun h1 => hne (h1.trans h2.symm), h2⟩

theorem cut_compl [Fintype V] [DecidableEq V] [Fintype E] (M : LooplessMultigraph V E)
    (U : Finset V) : M.cut Uᶜ = M.cut U := by
  ext e
  simp only [mem_cut_iff, Finset.mem_compl]
  tauto

theorem cut_univ [Fintype V] [DecidableEq V] [Fintype E] (M : LooplessMultigraph V E) :
    M.cut Finset.univ = ∅ := by
  ext e
  simp [mem_cut_iff]

/-- A subset of edges `S` is a perfect matching if every vertex is incident to exactly one edge
in `S`. -/
@[expose] def IsPerfectMatching [DecidableEq V] (M : LooplessMultigraph V E)
    (S : Finset E) : Prop :=
  ∀ v : V, (S.filter fun e => M.inc e v).card = 1

/-- Incidence vector `χ^S ∈ ℝ^E` of an edge set `S`. -/
@[expose] def edgeVec [DecidableEq E] (S : Finset E) : E → ℝ :=
  fun e => if e ∈ S then 1 else 0

/-- The perfect matching polytope of a multigraph `M`: convex hull of incidence vectors of its
perfect matchings. -/
@[expose] def pmPolytope [DecidableEq V] [DecidableEq E] (M : LooplessMultigraph V E) :
    Set (E → ℝ) :=
  convexHull ℝ (Set.range fun S : {S : Finset E // M.IsPerfectMatching S} => edgeVec S.1)

/-- Convex-hull range characterization of `M.pmPolytope`. -/
theorem pmPolytope_eq_convexHull_range [DecidableEq V] [DecidableEq E]
    (M : LooplessMultigraph V E) :
    M.pmPolytope =
      convexHull ℝ (Set.range fun S : {S : Finset E // M.IsPerfectMatching S} => edgeVec S.1) :=
  rfl

/-- Edmonds' linear inequality description of the perfect matching polytope of `M`. -/
@[expose] def pmHPolytope [DecidableEq V] [Fintype E] (M : LooplessMultigraph V E) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧
    (∀ v : V, ∑ e ∈ M.cut {v}, x e = 1) ∧
    (∀ U : Finset V, Odd U.card → 1 ≤ ∑ e ∈ M.cut U, x e)}

/-- Membership characterization of Edmonds' H-polytope `M.pmHPolytope`. -/
theorem mem_pmHPolytope_iff [DecidableEq V] [Fintype E] (M : LooplessMultigraph V E)
    (x : E → ℝ) :
    x ∈ M.pmHPolytope ↔
      (∀ e, 0 ≤ x e) ∧
      (∀ v : V, ∑ e ∈ M.cut {v}, x e = 1) ∧
      (∀ U : Finset V, Odd U.card → 1 ≤ ∑ e ∈ M.cut U, x e) := Iff.rfl

theorem sum_cut_add_two_mul_induced [DecidableEq V] [Fintype E] (M : LooplessMultigraph V E)
    (U : Finset V) (x : E → ℝ) :
    (∑ e ∈ M.cut U, x e) + 2 * (∑ e ∈ Finset.univ.filter fun e => M.fst e ∈ U ∧ M.snd e ∈ U, x e) =
      ∑ v ∈ U, ∑ e ∈ M.cut {v}, x e := by
  classical
  have h1 : ∀ v ∈ U, ∑ e ∈ M.cut {v}, x e =
      ∑ e : E, ((if M.fst e = v then (1 : ℝ) else 0) + if M.snd e = v then 1 else 0) * x e := by
    intro v _
    rw [cut_singleton_eq_inc, Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hne := M.ne e
    by_cases hf : M.fst e = v
    · have hs : M.snd e ≠ v := fun h => hne (hf.trans h.symm)
      simp [inc, hf, hs]
    · by_cases hs : M.snd e = v
      · simp [inc, hf, hs]
      · simp [inc, hf, hs]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have hinner : ∀ e : E,
      ∑ v ∈ U, ((if M.fst e = v then (1 : ℝ) else 0) + if M.snd e = v then 1 else 0) * x e =
        ((if M.fst e ∈ U then (1 : ℝ) else 0) + if M.snd e ∈ U then 1 else 0) * x e := by
    intro e
    rw [← Finset.sum_mul, Finset.sum_add_distrib]
    simp
  simp_rw [hinner]
  rw [cut, Finset.sum_filter, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hf : M.fst e ∈ U <;> by_cases hs : M.snd e ∈ U <;>
    simp only [hf, hs, ↓reduceIte, and_self, and_false, false_and, or_self, or_false, false_or,
      not_true_eq_false, not_false_eq_true, add_zero, zero_add, one_mul, zero_mul, mul_zero];
    ring

theorem pmPolytope_subset_pmHPolytope [DecidableEq V] [Fintype E] [DecidableEq E]
    (M : LooplessMultigraph V E) : M.pmPolytope ⊆ M.pmHPolytope := by
  refine convexHull_min ?_ ?_
  · rintro _ ⟨⟨S, hS⟩, rfl⟩
    refine ⟨fun e => by simp only [edgeVec]; split_ifs <;> norm_num, fun v => ?_, fun U hU => ?_⟩
    · rw [cut_singleton_eq_inc]
      simp only [edgeVec, Finset.sum_boole]
      have hfilt : (Finset.univ.filter fun e => M.inc e v).filter (fun e => e ∈ S) =
          S.filter fun e => M.inc e v := by
        ext e; simp [and_comm]
      rw [hfilt, hS v, Nat.cast_one]
    · have hsum := sum_cut_add_two_mul_induced M U (edgeVec S)
      have hdeg : ∑ v ∈ U, ∑ e ∈ M.cut {v}, edgeVec S e = (U.card : ℝ) := by
        have hv : ∀ v ∈ U, ∑ e ∈ M.cut {v}, edgeVec S e = 1 := fun v _ => by
          rw [cut_singleton_eq_inc]
          simp only [edgeVec, Finset.sum_boole]
          have hfilt : (Finset.univ.filter fun e => M.inc e v).filter (fun e => e ∈ S) =
              S.filter fun e => M.inc e v := by
            ext e; simp [and_comm]
          rw [hfilt, hS v, Nat.cast_one]
        rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hdeg] at hsum
      set a : ℕ := ((M.cut U).filter fun e => e ∈ S).card
      set b : ℕ := ((Finset.univ.filter fun e => M.fst e ∈ U ∧ M.snd e ∈ U).filter
        fun e => e ∈ S).card
      have ha : ∑ e ∈ M.cut U, edgeVec S e = (a : ℝ) := by
        simp [edgeVec, a, Finset.filter_mem_eq_inter]
      have hb : ∑ e ∈ Finset.univ.filter (fun e => M.fst e ∈ U ∧ M.snd e ∈ U), edgeVec S e =
          (b : ℝ) := by simp [edgeVec, b, Finset.filter_mem_eq_inter]
      rw [ha] at hsum ⊢
      rw [hb] at hsum
      have hnat : a + 2 * b = U.card := by exact_mod_cast hsum
      have ha_pos : 1 ≤ a := by
        obtain ⟨k, hk⟩ := hU
        omega
      exact_mod_cast ha_pos
  · intro x hx y hy a b ha hb hab
    refine ⟨fun e => add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e)), fun v => ?_,
      fun U hU => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
        hx.2.1 v, hy.2.1 v]
      nlinarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
      nlinarith [hx.2.2 U hU, hy.2.2 U hU]

private theorem isCompact_pmHPolytope [DecidableEq V] [Fintype E]
    (M : LooplessMultigraph V E) : IsCompact M.pmHPolytope := by
  have hsub : M.pmHPolytope ⊆ Set.univ.pi fun _ : E => Set.Icc (0 : ℝ) 1 := by
    intro x hx e _
    refine ⟨hx.1 e, ?_⟩
    have hmem : e ∈ M.cut {M.fst e} := by
      rw [cut_singleton_eq_inc, Finset.mem_filter]
      exact ⟨Finset.mem_univ e, Or.inl rfl⟩
    have hle := Finset.single_le_sum (fun e' _ => hx.1 e') hmem
    linarith [hx.2.1 (M.fst e)]
  have hcl : IsClosed M.pmHPolytope := by
    have h1 : IsClosed {x : E → ℝ | ∀ e, 0 ≤ x e} := by
      simpa [Set.ofPred_forall] using
        isClosed_iInter fun e : E => isClosed_le continuous_const (continuous_apply e)
    have h2 : IsClosed {x : E → ℝ | ∀ v : V, ∑ e ∈ M.cut {v}, x e = 1} := by
      simpa [Set.ofPred_forall] using
        isClosed_iInter fun v : V =>
          isClosed_eq (continuous_finsetSum (M.cut {v}) fun e _ => continuous_apply e)
            continuous_const
    have h3 : IsClosed {x : E → ℝ | ∀ U : Finset V, Odd U.card → 1 ≤ ∑ e ∈ M.cut U, x e} := by
      rw [Set.ofPred_forall]
      refine isClosed_iInter fun U : Finset V => ?_
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun _ =>
        isClosed_le continuous_const
          (continuous_finsetSum (M.cut U) fun e _ => continuous_apply e)
    exact h1.inter (h2.inter h3)
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hcl hsub

/-- Every 2-regular loopless multigraph on a nonempty finite vertex set either has a component of
odd cardinality (empty cut) or admits a nonzero alternating vector in the kernel of its
vertex-edge incidence map. -/
private theorem odd_component_or_kernel_of_two_regular [Finite V] [DecidableEq V] [Nonempty V]
    [Fintype E] (M : LooplessMultigraph V E)
    (hdeg : ∀ v : V, (M.cut {v}).card = 2) :
    (∃ U : Finset V, Odd U.card ∧ M.cut U = ∅) ∨
      ∃ d : E → ℝ, d ≠ 0 ∧ ∀ v : V, ∑ e ∈ M.cut {v}, d e = 0 := by
  classical
  -- Work on darts `D = {(v, e) | M.inc e v}` with the two fixed-point-free involutions `rev`
  -- (opposite endpoint of `e`) and `flip` (opposite edge at `v`), and `step = flip ∘ rev`.
  let D := {p : V × E // M.inc p.2 p.1}
  let otherV : E → V → V := fun e v => if M.fst e = v then M.snd e else M.fst e
  have hotherV_ne : ∀ e v, M.inc e v → otherV e v ≠ v := by
    intro e v hinc
    dsimp only [otherV]
    split_ifs with h
    · exact h ▸ (M.ne e).symm
    · rcases hinc with h1 | h2
      · exact absurd h1 h
      · exact h2 ▸ M.ne e
  have hotherV_inc : ∀ e v, M.inc e v → M.inc e (otherV e v) := by
    intro e v hinc
    dsimp only [otherV]
    split_ifs with h
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hotherV_inv : ∀ e v, M.inc e v → otherV e (otherV e v) = v := by
    intro e v hinc
    dsimp only [otherV]
    rcases hinc with rfl | rfl
    · have hne : M.fst e ≠ M.snd e := M.ne e
      simp [hne]
    · have hne : M.fst e ≠ M.snd e := M.ne e
      simp [hne]
  let rev : D → D := fun x => ⟨⟨otherV x.1.2 x.1.1, x.1.2⟩, hotherV_inc x.1.2 x.1.1 x.2⟩
  have hrev_inv : ∀ x : D, rev (rev x) = x := fun ⟨⟨v, e⟩, h⟩ => by
    apply Subtype.ext; apply Prod.ext
    · exact hotherV_inv e v h
    · rfl
  have hrev_ne : ∀ x : D, rev x ≠ x := fun ⟨⟨v, e⟩, h⟩ heq =>
    hotherV_ne e v h (congrArg (fun z : D => z.1.1) heq)
  let otherE : ∀ (v : V) (e : E), M.inc e v → E := fun v e h =>
    have hmem : e ∈ M.cut {v} := by
      rw [cut_singleton_eq_inc, Finset.mem_filter]; exact ⟨Finset.mem_univ e, h⟩
    have hcard : ((M.cut {v}).erase e).card = 1 := by
      rw [Finset.card_erase_of_mem hmem, hdeg v]
    (Finset.card_eq_one.1 hcard).choose
  have hotherE_spec : ∀ (v : V) (e : E) (h : M.inc e v),
      (M.cut {v}).erase e = {otherE v e h} := fun v e h => by
    have hmem : e ∈ M.cut {v} := by
      rw [cut_singleton_eq_inc, Finset.mem_filter]; exact ⟨Finset.mem_univ e, h⟩
    exact (Finset.card_eq_one.1 (by rw [Finset.card_erase_of_mem hmem, hdeg v])).choose_spec
  have hotherE_ne : ∀ (v : V) (e : E) (h : M.inc e v), otherE v e h ≠ e := fun v e h =>
    (Finset.mem_erase.1 (hotherE_spec v e h ▸ Finset.mem_singleton_self _)).1
  have hotherE_inc : ∀ (v : V) (e : E) (h : M.inc e v), M.inc (otherE v e h) v := fun v e h => by
    have hc := Finset.mem_of_mem_erase (hotherE_spec v e h ▸ Finset.mem_singleton_self _)
    rw [cut_singleton_eq_inc, Finset.mem_filter] at hc
    exact hc.2
  have hcut_pair : ∀ (v : V) (e : E) (h : M.inc e v),
      M.cut {v} = {e, otherE v e h} := fun v e h => by
    have hmem : e ∈ M.cut {v} := by
      rw [cut_singleton_eq_inc, Finset.mem_filter]; exact ⟨Finset.mem_univ e, h⟩
    rw [← Finset.insert_erase hmem, hotherE_spec v e h]
  have hotherE_inv : ∀ (v : V) (e : E) (h : M.inc e v),
      otherE v (otherE v e h) (hotherE_inc v e h) = e := fun v e h => by
    have hmem : e ∈ (M.cut {v}).erase (otherE v e h) := by
      rw [Finset.mem_erase, cut_singleton_eq_inc, Finset.mem_filter]
      exact ⟨(hotherE_ne v e h).symm, Finset.mem_univ e, h⟩
    rw [hotherE_spec v (otherE v e h) (hotherE_inc v e h), Finset.mem_singleton] at hmem
    exact hmem.symm
  let flip : D → D := fun x => ⟨⟨x.1.1, otherE x.1.1 x.1.2 x.2⟩, hotherE_inc x.1.1 x.1.2 x.2⟩
  have hflip_inv : ∀ x : D, flip (flip x) = x := fun ⟨⟨v, e⟩, h⟩ =>
    Subtype.ext (Prod.ext rfl (hotherE_inv v e h))
  have hflip_ne : ∀ x : D, flip x ≠ x := fun ⟨⟨v, e⟩, h⟩ heq =>
    hotherE_ne v e h (congrArg (fun z : D => z.1.2) heq)
  let step : D → D := fun x => flip (rev x)
  let stepInv : D → D := fun x => rev (flip x)
  have hstep_left : Function.LeftInverse stepInv step := fun x => by
    simp [step, stepInv, hflip_inv, hrev_inv]
  have hstep_right : Function.RightInverse stepInv step := fun x => by
    simp [step, stepInv, hflip_inv, hrev_inv]
  have hno_flip : ∀ (m : ℕ) (x : D), flip (step^[m] x) ≠ x := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro x heq
      cases m with
      | zero => exact hflip_ne x heq
      | succ m =>
        cases m with
        | zero => exact hrev_ne x (by simpa [step, hflip_inv] using heq)
        | succ m =>
          have h1 : flip (step^[m] (step x)) = step x := by
            have h2 := congrArg step heq
            rw [Function.iterate_succ_apply', Function.iterate_succ_apply] at h2
            simpa [step, hflip_inv, hrev_inv] using h2
          exact ih m (by omega) (step x) h1
  have hno_rev : ∀ (m : ℕ) (x : D), rev (step^[m] x) ≠ x := fun m x heq =>
    hno_flip (m + 1) x (by rw [Function.iterate_succ_apply']; simpa [step, hflip_inv] using heq)
  -- Pick any starting dart `d₀`.
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have hv₀_ne : (M.cut {v₀}).Nonempty := Finset.card_pos.1 (by rw [hdeg v₀]; omega)
  obtain ⟨e₀, he₀⟩ := hv₀_ne
  have hinc₀ : M.inc e₀ v₀ := by
    rw [cut_singleton_eq_inc, Finset.mem_filter] at he₀
    exact he₀.2
  let d₀ : D := ⟨⟨v₀, e₀⟩, hinc₀⟩
  have hper : Function.IsPeriodicPt step (Function.minimalPeriod step d₀) d₀ :=
    Function.isPeriodicPt_minimalPeriod step d₀
  have hk_pos : 0 < Function.minimalPeriod step d₀ :=
    Function.minimalPeriod_pos_of_mem_periodicPts (hstep_left.injective.mem_periodicPts d₀)
  set k := Function.minimalPeriod step d₀
  let orb : Fin k → D := fun i => step^[i.1] d₀
  have horb_inj : Function.Injective orb := fun i j hij => by
    have := Function.iterate_injOn_Iio_minimalPeriod (f := step) (x := d₀) i.2 j.2 hij
    exact Fin.ext this
  -- Vertices along the orbit are pairwise distinct.
  have hv_inj : Function.Injective (fun i : Fin k => (orb i).1.1) := by
    intro i j hij
    dsimp only at hij
    wlog hle : i ≤ j generalizing i j
    · exact (this hij.symm (le_of_not_ge hle)).symm
    rcases eq_or_lt_of_le hle with rfl | hlt
    · rfl
    -- `(orb j).1.1 = (orb i).1.1`, so `(orb j).1.2 ∈ M.cut {(orb i).1.1} = {(orb i).1.2, otherE
    -- ...}`.
    have hmem : (orb j).1.2 ∈ M.cut {(orb i).1.1} := by
      rw [cut_singleton_eq_inc, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hij.symm ▸ (orb j).2⟩
    rw [hcut_pair (orb i).1.1 (orb i).1.2 (orb i).2, Finset.mem_insert,
      Finset.mem_singleton] at hmem
    rcases hmem with heq | heq
    · have hd : orb j = orb i := Subtype.ext (Prod.ext hij.symm heq)
      exact (horb_inj hd).symm
    · have hflip_eq : orb j = flip (orb i) := Subtype.ext (Prod.ext hij.symm heq)
      have hdiff : step^[j.1 - i.1] (orb i) = flip (orb i) := by
        rw [← hflip_eq]
        dsimp only [orb]
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
      have hcontra : flip (step^[j.1 - i.1] (orb i)) = orb i := by
        rw [hdiff, hflip_inv]
      exact absurd hcontra (hno_flip (j.1 - i.1) (orb i))
  -- Edges along the orbit are pairwise distinct.
  have he_inj : Function.Injective (fun i : Fin k => (orb i).1.2) := by
    intro i j hij
    dsimp only at hij
    wlog hle : i ≤ j generalizing i j
    · exact (this hij.symm (le_of_not_ge hle)).symm
    rcases eq_or_lt_of_le hle with rfl | hlt
    · rfl
    -- Two darts on the same edge either share the vertex or are `rev` of each other.
    by_cases hv : (orb j).1.1 = (orb i).1.1
    · exact hv_inj hv.symm
    · have hrev_eq : orb j = rev (orb i) := by
        apply Subtype.ext
        dsimp only [rev]
        apply Prod.ext
        swap
        · exact hij.symm
        have hi := (orb i).2
        have hj := (orb j).2
        rw [hij.symm] at hj
        dsimp only [otherV]
        rcases hi with h1 | h2
        · simp only [h1, ↓reduceIte]
          rcases hj with h3 | h4
          · exact absurd (h3.symm.trans h1) hv
          · exact h4.symm
        · have hne : M.fst (orb i).1.2 ≠ (orb i).1.1 := by
            rw [← h2]; exact M.ne _
          simp only [hne, ↓reduceIte]
          rcases hj with h3 | h4
          · exact h3.symm
          · exact absurd (h4.symm.trans h2) hv
      have hdiff : step^[j.1 - i.1] (orb i) = rev (orb i) := by
        rw [← hrev_eq]
        dsimp only [orb]
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
      have hcontra : rev (step^[j.1 - i.1] (orb i)) = orb i := by
        rw [hdiff, hrev_inv]
      exact absurd hcontra (hno_rev (j.1 - i.1) (orb i))
  -- Step wraps modulo `k`.
  have hiter_mod : ∀ n : ℕ, step^[n % k] d₀ = step^[n] d₀ := fun n => by
    have hmul : ∀ q : ℕ, step^[q * k] d₀ = d₀ := fun q => by
      induction q with
      | zero => simp
      | succ q ih => rw [Nat.succ_mul, add_comm, Function.iterate_add_apply, ih, hper]
    conv_rhs => rw [← Nat.div_add_mod n k, add_comm, mul_comm]
    rw [Function.iterate_add_apply, hmul]
  have horb_succ : ∀ i : Fin k, step (orb i) = orb ⟨(i.1 + 1) % k, Nat.mod_lt _ hk_pos⟩ := by
    intro i
    change step (step^[i.1] d₀) = step^[((i.1 + 1) % k)] d₀
    rw [← Function.iterate_succ_apply' step i.1 d₀]
    exact (hiter_mod (i.1 + 1)).symm
  -- At vertex `(orb i).1.1`, the two incident edges are `(orb i).1.2` and `(orb (prev i)).1.2`.
  let prevIdx : Fin k → Fin k := fun i => ⟨(i.1 + k - 1) % k, Nat.mod_lt _ hk_pos⟩
  have hprev_succ : ∀ i : Fin k, (prevIdx i).1 + 1 ≡ i.1 [MOD k] := by
    intro i
    change ((i.1 + k - 1) % k + 1) % k = i.1 % k
    rw [Nat.mod_add_mod]
    have h : i.1 + k - 1 + 1 = i.1 + k := by omega
    rw [h, Nat.add_mod_right]
  have hstep_prev : ∀ i : Fin k, step (orb (prevIdx i)) = orb i := by
    intro i
    rw [horb_succ]
    congr 1
    apply Fin.ext
    simpa [Nat.ModEq, Nat.mod_eq_of_lt i.2] using hprev_succ i
  have hotherE_orb : ∀ i : Fin k,
      otherE (orb i).1.1 (orb i).1.2 (orb i).2 = (orb (prevIdx i)).1.2 := by
    intro i
    have h1 : flip (orb i) = rev (orb (prevIdx i)) := by
      rw [← hstep_prev i]
      simp [step, hflip_inv]
    exact congrArg (fun z : D => z.1.2) h1
  rcases Nat.even_or_odd k with hk_even | hk_odd
  · -- Even cycle: alternating `±1` vector lies in the kernel of vertex incidence.
    right
    let d : E → ℝ := fun e =>
      if h : ∃ i : Fin k, (orb i).1.2 = e then (-1 : ℝ) ^ h.choose.1 else 0
    have hd_orb : ∀ i : Fin k, d (orb i).1.2 = (-1 : ℝ) ^ i.1 := fun i => by
      have hex : ∃ j : Fin k, (orb j).1.2 = (orb i).1.2 := ⟨i, rfl⟩
      have hch : hex.choose = i := he_inj hex.choose_spec
      simp only [d, hex, ↓reduceDIte, hch]
    have hd_ne : d ≠ 0 := fun h0 => by
      have h := congrFun h0 (orb ⟨0, hk_pos⟩).1.2
      rw [hd_orb ⟨0, hk_pos⟩] at h
      norm_num at h
    refine ⟨d, hd_ne, fun v => ?_⟩
    by_cases hv : ∃ i : Fin k, (orb i).1.1 = v
    · obtain ⟨i, rfl⟩ := hv
      have hcut : M.cut {(orb i).1.1} = {(orb i).1.2, (orb (prevIdx i)).1.2} := by
        rw [hcut_pair (orb i).1.1 (orb i).1.2 (orb i).2, hotherE_orb i]
      have hne_e : (orb i).1.2 ≠ (orb (prevIdx i)).1.2 := by
        rw [← hotherE_orb i]
        exact (hotherE_ne _ _ (orb i).2).symm
      rw [hcut, Finset.sum_pair hne_e, hd_orb i, hd_orb (prevIdx i)]
      obtain ⟨m, hm⟩ := hk_even
      have hpar : (prevIdx i).1 % 2 ≠ i.1 % 2 := by
        have hmod := hprev_succ i
        have h2 : ((prevIdx i).1 + 1) % 2 = i.1 % 2 := by
          have hdvd : 2 ∣ k := ⟨m, by omega⟩
          have := Nat.ModEq.of_dvd hdvd hmod
          simpa [Nat.ModEq] using this
        omega
      rcases Nat.even_or_odd i.1 with ⟨t, ht⟩ | ⟨t, ht⟩
      · have hodd : Odd (prevIdx i).1 := Nat.odd_iff.2 (by omega)
        rw [ht, Even.neg_one_pow ⟨t, rfl⟩, Odd.neg_one_pow hodd]
        ring
      · have hev : Even (prevIdx i).1 := Nat.even_iff.2 (by omega)
        rw [ht, Odd.neg_one_pow ⟨t, rfl⟩, Even.neg_one_pow hev]
        ring
    · refine Finset.sum_eq_zero fun e he => ?_
      have hinc : M.inc e v := by
        rw [cut_singleton_eq_inc, Finset.mem_filter] at he
        exact he.2
      have hnot : ¬ ∃ i : Fin k, (orb i).1.2 = e := by
        rintro ⟨i, rfl⟩
        -- Both endpoints of `(orb i).1.2` lie in the vertex orbit (`(orb i).1.1` and `(orb (succ
        -- i)).1.1`).
        have hnext_v : (orb ⟨(i.1 + 1) % k, Nat.mod_lt _ hk_pos⟩).1.1 =
            otherV (orb i).1.2 (orb i).1.1 := by
          rw [← horb_succ i]
        rcases eq_or_ne v (orb i).1.1 with rfl | hne
        · exact hv ⟨i, rfl⟩
        · have hv2 : v = otherV (orb i).1.2 (orb i).1.1 := by
            dsimp only [otherV]
            rcases (orb i).2 with h1 | h2
            · simp only [h1, ↓reduceIte]
              rcases hinc with h3 | h4
              · exact absurd (h3.symm.trans h1) hne
              · exact h4.symm
            · have hne1 : M.fst (orb i).1.2 ≠ (orb i).1.1 := by
                rw [← h2]; exact M.ne _
              simp only [hne1, ↓reduceIte]
              rcases hinc with h3 | h4
              · exact h3.symm
              · exact absurd (h4.symm.trans h2) hne
          exact hv ⟨⟨(i.1 + 1) % k, Nat.mod_lt _ hk_pos⟩, hnext_v.trans hv2.symm⟩
      simp [d, hnot]
  · -- Odd cycle: `U = image (fun i => (orb i).1.1)` has odd size `k` and empty cut!
    left
    let U : Finset V := Finset.univ.image fun i : Fin k => (orb i).1.1
    refine ⟨U, ?_, ?_⟩
    · have hcard : U.card = k := by
        rw [Finset.card_image_of_injective _ hv_inj, Finset.card_univ, Fintype.card_fin]
      rwa [hcard]
    · refine Finset.eq_empty_of_forall_notMem fun e he => ?_
      have hmem := (mem_cut_iff M U e).1 he
      have hclosed : ∀ v ∈ U, M.inc e v → otherV e v ∈ U := by
        intro v hvU hinc
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hvU
        have he_in : e ∈ M.cut {(orb i).1.1} := by
          rw [cut_singleton_eq_inc, Finset.mem_filter]; exact ⟨Finset.mem_univ e, hinc⟩
        rw [hcut_pair (orb i).1.1 (orb i).1.2 (orb i).2, hotherE_orb i, Finset.mem_insert,
          Finset.mem_singleton] at he_in
        rcases he_in with rfl | rfl
        · have hnext : (orb ⟨(i.1 + 1) % k, Nat.mod_lt _ hk_pos⟩).1.1 =
              otherV (orb i).1.2 (orb i).1.1 := by rw [← horb_succ i]
          exact hnext ▸ Finset.mem_image.2 ⟨⟨(i.1 + 1) % k, Nat.mod_lt _ hk_pos⟩,
            Finset.mem_univ _, rfl⟩
        · have hprev_v : (orb (prevIdx i)).1.1 =
              otherV (orb (prevIdx i)).1.2 (orb i).1.1 := by
            have hstep' := congrArg (fun z : D => z.1.1) (hstep_prev i)
            change otherV (orb (prevIdx i)).1.2 (orb (prevIdx i)).1.1 = (orb i).1.1 at hstep'
            rw [← hstep', hotherV_inv _ _ (orb (prevIdx i)).2]
          exact hprev_v ▸ Finset.mem_image.2 ⟨prevIdx i, Finset.mem_univ _, rfl⟩
      rcases hmem with ⟨hf, hs⟩ | ⟨hf, hs⟩
      · have := hclosed (M.fst e) hf (Or.inl rfl)
        simp only [otherV, ↓reduceIte] at this
        exact hs this
      · have := hclosed (M.snd e) hs (Or.inr rfl)
        have hne := M.ne e
        simp only [otherV, hne, ↓reduceIte] at this
        exact hf this

/-- **Edmonds' Perfect Matching Polytope Theorem** for finite loopless multigraphs
.
-/
theorem pmPolytope_eq_hPolytope :
    ∀ (N : ℕ) {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (M : LooplessMultigraph V E), Fintype.card V + Fintype.card E ≤ N →
      M.pmPolytope = M.pmHPolytope := by
  intro N
  induction N with
  | zero =>
    intro V E _ _ _ _ M hN
    have hV0 : IsEmpty V := Fintype.card_eq_zero_iff.1 (by omega)
    have hE0 : IsEmpty E := Fintype.card_eq_zero_iff.1 (by omega)
    refine Set.Subset.antisymm M.pmPolytope_subset_pmHPolytope fun x _ => ?_
    have hx : x = edgeVec (∅ : Finset E) := funext fun e => hE0.elim e
    rw [hx]
    exact subset_convexHull ℝ _ ⟨⟨∅, fun v => hV0.elim v⟩, rfl⟩
  | succ N ih =>
    intro V E _ _ _ _ M hN
    classical
    refine Set.Subset.antisymm M.pmPolytope_subset_pmHPolytope ?_
    have hconvH : Convex ℝ M.pmHPolytope := by
      intro x hx y hy a b ha hb hab
      refine ⟨fun e => add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e)), fun v => ?_,
        fun U hU => ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hx.2.1 v, hy.2.1 v]
        nlinarith
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        nlinarith [hx.2.2 U hU, hy.2.2 U hU]
    have hcompP : IsCompact M.pmPolytope := (Set.finite_range _).isCompact_convexHull ℝ
    -- By Krein–Milman, it suffices to show every extreme point of `pmHPolytope` lies in
    -- `pmPolytope`.
    rw [← closure_convexHull_extremePoints M.isCompact_pmHPolytope hconvH]
    rw [← hcompP.isClosed.closure_eq]
    refine closure_mono (convexHull_min ?_ (convex_convexHull ℝ _))
    intro x hxExt
    have hx : x ∈ M.pmHPolytope := extremePoints_subset hxExt
    rcases isEmpty_or_nonempty V with hVempty | hVne
    · have hEempty : IsEmpty E := ⟨fun e => hVempty.elim (M.fst e)⟩
      have hx0 : x = edgeVec (∅ : Finset E) := funext fun e => hEempty.elim e
      rw [hx0]
      exact subset_convexHull ℝ _ ⟨⟨∅, fun v => hVempty.elim v⟩, rfl⟩
    -- Note `|V|` must be even (otherwise `U = univ` violates `1 ≤ x(δ(univ)) = 0`).
    have hVeven : Even (Fintype.card V) := by
      rcases Nat.even_or_odd (Fintype.card V) with h | hodd
      · exact h
      · have h1 := hx.2.2 Finset.univ (by simpa using hodd)
        rw [cut_univ, Finset.sum_empty] at h1
        linarith
    -- Case 0: some edge has `x e₀ = 0`. Delete `e₀`.
    by_cases h0 : ∃ e₀ : E, x e₀ = 0
    · obtain ⟨e₀, he₀⟩ := h0
      let E' := {e : E // e ≠ e₀}
      let M' : LooplessMultigraph V E' :=
        { fst := fun e => M.fst e.1, snd := fun e => M.snd e.1, ne := fun e => M.ne e.1 }
      have hcard' : Fintype.card V + Fintype.card E' ≤ N := by
        have hE' : Fintype.card E' + 1 = Fintype.card E := by
          have huniq : Fintype.card {e : E // e = e₀} = 1 := Fintype.card_unique
          rw [Fintype.card_subtype_compl, huniq]
          exact Nat.sub_add_cancel (Fintype.card_pos_iff.2 ⟨e₀⟩)
        omega
      let x' : E' → ℝ := fun e => x e.1
      have hcut_eq : ∀ U : Finset V, ∑ e ∈ M'.cut U, x' e = ∑ e ∈ M.cut U, x e := fun U => by
        have h1 : ∑ e ∈ M'.cut U, x' e = ∑ e ∈ (M.cut U).erase e₀, x e := by
          refine Finset.sum_bij (fun e _ => e.1) (fun e he => ?_)
            (fun a _ b _ h => Subtype.ext h) (fun f hf => ?_) (fun _ _ => rfl)
          · exact Finset.mem_erase.2 ⟨e.2, (mem_cut_iff M U e.1).2 ((mem_cut_iff M' U e).1 he)⟩
          · rw [Finset.mem_erase] at hf
            exact ⟨⟨f, hf.1⟩, (mem_cut_iff M' U ⟨f, hf.1⟩).2 ((mem_cut_iff M U f).1 hf.2), rfl⟩
        rw [h1]
        by_cases hmem : e₀ ∈ M.cut U
        · rw [← Finset.add_sum_erase _ _ hmem, he₀, zero_add]
        · rw [Finset.erase_eq_of_notMem hmem]
      have hx' : x' ∈ M'.pmHPolytope :=
        ⟨fun e => hx.1 e.1, fun v => (hcut_eq {v}).trans (hx.2.1 v),
          fun U hU => (hcut_eq U).symm ▸ hx.2.2 U hU⟩
      rw [← ih M' hcard'] at hx'
      let lift : (E' → ℝ) →ₗ[ℝ] (E → ℝ) :=
        { toFun := fun y e => if h : e = e₀ then 0 else y ⟨e, h⟩
          map_add' := fun y₁ y₂ => by ext e; by_cases h : e = e₀ <;> simp [h]
          map_smul' := fun c y => by ext e; by_cases h : e = e₀ <;> simp [h] }
      have hlift_x : lift x' = x := by
        ext e
        simp only [lift, LinearMap.coe_mk, AddHom.coe_mk, x']
        split_ifs with h
        · rw [h, he₀]
        · rfl
      have hsub : lift '' M'.pmPolytope ⊆ M.pmPolytope := by
        rw [pmPolytope, LinearMap.image_convexHull]
        refine convexHull_mono ?_
        rintro _ ⟨_, ⟨⟨S, hS⟩, rfl⟩, rfl⟩
        refine ⟨⟨S.map ⟨Subtype.val, Subtype.val_injective⟩, fun v => ?_⟩, ?_⟩
        · have hfilt : (S.map ⟨Subtype.val, Subtype.val_injective⟩).filter (fun e => M.inc e v) =
              (S.filter fun e => M'.inc e v).map ⟨Subtype.val, Subtype.val_injective⟩ := by
            ext e
            simp only [Finset.mem_filter, Finset.mem_map, Function.Embedding.coeFn_mk]
            constructor
            · rintro ⟨⟨a, ha, rfl⟩, hinc⟩; exact ⟨a, ⟨ha, hinc⟩, rfl⟩
            · rintro ⟨a, ⟨ha, hinc⟩, rfl⟩; exact ⟨⟨a, ha, rfl⟩, hinc⟩
          rw [hfilt, Finset.card_map, hS v]
        · ext e
          simp only [lift, LinearMap.coe_mk, AddHom.coe_mk, edgeVec, Finset.mem_map,
            Function.Embedding.coeFn_mk]
          by_cases h1 : e = e₀
          · subst h1
            simp only [↓reduceDIte]
            split_ifs with h
            · rcases h with ⟨a, _, ha⟩; exact absurd ha a.2
            · rfl
          · simp only [h1, ↓reduceDIte]
            by_cases h2 : ⟨e, h1⟩ ∈ S
            · simp only [h2, ↓reduceIte]
              split_ifs with h
              · rfl
              · exact absurd ⟨⟨e, h1⟩, h2, rfl⟩ h
            · simp only [h2, ↓reduceIte]
              split_ifs with h
              · rcases h with ⟨a, ha, rfl⟩; exact absurd ha h2
              · rfl
      exact hsub ⟨x', hx', hlift_x⟩
    push Not at h0
    have hx_pos : ∀ e : E, 0 < x e := fun e => lt_of_le_of_ne (hx.1 e) (Ne.symm (h0 e))
    -- Case 1: some edge has `x e₀ = 1`. Delete `{u₀, v₀}` and `e₀`.
    by_cases h1 : ∃ e₀ : E, x e₀ = 1
    · obtain ⟨e₀, he₀⟩ := h1
      set u₀ := M.fst e₀
      set v₀ := M.snd e₀
      have hdisj_e : ∀ e : E, e ≠ e₀ →
        M.fst e ≠ u₀ ∧ M.fst e ≠ v₀ ∧ M.snd e ≠ u₀ ∧ M.snd e ≠ v₀ := by
        intro e hne
        have hnot_inc : ∀ w, w = u₀ ∨ w = v₀ → ¬ M.inc e w := by
          intro w hw hinc
          have he₀_mem : e₀ ∈ M.cut {w} := by
            rw [cut_singleton_eq_inc, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hw.imp Eq.symm Eq.symm⟩
          have he_mem : e ∈ M.cut {w} := by
            rw [cut_singleton_eq_inc, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hinc⟩
          have hpair : x e₀ + x e ≤ ∑ f ∈ M.cut {w}, x f := by
            have hsub : ({e₀, e} : Finset E) ⊆ M.cut {w} :=
              Finset.insert_subset_iff.2 ⟨he₀_mem, Finset.singleton_subset_iff.2 he_mem⟩
            simpa [Finset.sum_pair hne.symm] using
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun f _ _ => hx.1 f
          linarith [hx.2.1 w, hx_pos e]
        exact ⟨fun h => hnot_inc u₀ (Or.inl rfl) (Or.inl h),
          fun h => hnot_inc v₀ (Or.inr rfl) (Or.inl h),
          fun h => hnot_inc u₀ (Or.inl rfl) (Or.inr h),
          fun h => hnot_inc v₀ (Or.inr rfl) (Or.inr h)⟩
      let V' := {v : V // v ≠ u₀ ∧ v ≠ v₀}
      let E' := {e : E // e ≠ e₀}
      let M' : LooplessMultigraph V' E' :=
        { fst := fun e => ⟨M.fst e.1, (hdisj_e e.1 e.2).1, (hdisj_e e.1 e.2).2.1⟩
          snd := fun e => ⟨M.snd e.1, (hdisj_e e.1 e.2).2.2.1, (hdisj_e e.1 e.2).2.2.2⟩
          ne := fun e h => M.ne e.1 (congrArg Subtype.val h) }
      have hcard' : Fintype.card V' + Fintype.card E' ≤ N := by
        have hVle : Fintype.card V' ≤ Fintype.card V := Fintype.card_subtype_le _
        have hE' : Fintype.card E' + 1 = Fintype.card E := by
          have huniq : Fintype.card {e : E // e = e₀} = 1 := Fintype.card_unique
          rw [Fintype.card_subtype_compl, huniq]
          exact Nat.sub_add_cancel (Fintype.card_pos_iff.2 ⟨e₀⟩)
        omega
      let x' : E' → ℝ := fun e => x e.1
      have hcut_eq : ∀ U : Finset V',
          ∑ e ∈ M'.cut U, x' e = ∑ e ∈ M.cut (U.map ⟨Subtype.val, Subtype.val_injective⟩), x e := by
        intro U
        have hmap_iff : ∀ (v : V) (hv : v ≠ u₀ ∧ v ≠ v₀),
            v ∈ U.map ⟨Subtype.val, Subtype.val_injective⟩ ↔ ⟨v, hv⟩ ∈ U := fun v hv => by
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
          exact ⟨fun ⟨a, ha, h⟩ => Subtype.ext (a2 := (⟨v, hv⟩ : V')) h ▸ ha,
            fun h => ⟨⟨v, hv⟩, h, rfl⟩⟩
        refine Finset.sum_bij (fun e _ => e.1) (fun e he => ?_)
          (fun a _ b _ h => Subtype.ext h) (fun f hf => ?_) (fun _ _ => rfl)
        · rw [mem_cut_iff] at he ⊢
          rw [hmap_iff (M.fst e.1) ⟨(hdisj_e e.1 e.2).1, (hdisj_e e.1 e.2).2.1⟩,
            hmap_iff (M.snd e.1) ⟨(hdisj_e e.1 e.2).2.2.1, (hdisj_e e.1 e.2).2.2.2⟩]
          exact he
        · have hfne : f ≠ e₀ := by
            rintro rfl
            rw [mem_cut_iff] at hf
            rcases hf with ⟨h, _⟩ | ⟨_, h⟩
            · obtain ⟨a, _, ha⟩ := Finset.mem_map.1 h; exact a.2.1 ha
            · obtain ⟨a, _, ha⟩ := Finset.mem_map.1 h; exact a.2.2 ha
          refine ⟨⟨f, hfne⟩, ?_, rfl⟩
          rw [mem_cut_iff] at hf ⊢
          rwa [hmap_iff (M.fst f) ⟨(hdisj_e f hfne).1, (hdisj_e f hfne).2.1⟩,
            hmap_iff (M.snd f) ⟨(hdisj_e f hfne).2.2.1, (hdisj_e f hfne).2.2.2⟩] at hf
      have hx' : x' ∈ M'.pmHPolytope := by
        refine ⟨fun e => hx.1 e.1, fun v => ?_, fun U hU => ?_⟩
        · have hmap : ({v} : Finset V').map ⟨Subtype.val, Subtype.val_injective⟩ = {v.1} := by
            ext w; simp
          rw [hcut_eq {v}, hmap]
          exact hx.2.1 v.1
        · rw [hcut_eq U]
          exact hx.2.2 _ (by simpa using hU)
      rw [← ih M' hcard'] at hx'
      let lift : (E' → ℝ) →ᵃ[ℝ] (E → ℝ) :=
        { toFun := fun y e => if h : e = e₀ then 1 else y ⟨e, h⟩
          linear :=
            { toFun := fun y e => if h : e = e₀ then 0 else y ⟨e, h⟩
              map_add' := fun _ _ => by ext e; by_cases h : e = e₀ <;> simp [h]
              map_smul' := fun _ _ => by ext e; by_cases h : e = e₀ <;> simp [h] }
          map_vadd' := fun p v => by
            ext e
            simp only [vadd_eq_add, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
            by_cases h : e = e₀ <;> simp [h] }
      have hlift_x : lift x' = x := by
        ext e
        simp only [lift, AffineMap.coe_mk, x']
        split_ifs with h
        · rw [h, he₀]
        · rfl
      have hsub : lift '' M'.pmPolytope ⊆ M.pmPolytope := by
        rw [pmPolytope, AffineMap.image_convexHull]
        refine convexHull_mono ?_
        rintro _ ⟨_, ⟨⟨S, hS⟩, rfl⟩, rfl⟩
        let S' : Finset E := insert e₀ (S.map ⟨Subtype.val, Subtype.val_injective⟩)
        refine ⟨⟨S', fun v => ?_⟩, ?_⟩
        · by_cases hv : v = u₀ ∨ v = v₀
          · have hfilt : S'.filter (fun e => M.inc e v) = {e₀} := by
              ext e
              simp only [S', Finset.mem_filter, Finset.mem_insert, Finset.mem_map,
                Function.Embedding.coeFn_mk, Finset.mem_singleton]
              constructor
              · rintro ⟨rfl | ⟨a, _, rfl⟩, hinc⟩
                · rfl
                · exfalso
                  have hd := hdisj_e a.1 a.2
                  rcases hv with rfl | rfl <;> rcases hinc with h | h <;> tauto
              · rintro rfl
                exact ⟨Or.inl rfl, hv.imp Eq.symm Eq.symm⟩
            rw [hfilt, Finset.card_singleton]
          · push Not at hv
            have hfilt : S'.filter (fun e => M.inc e v) =
                (S.filter fun e => M'.inc e ⟨v, hv⟩).map ⟨Subtype.val, Subtype.val_injective⟩ := by
              ext e
              simp only [S', Finset.mem_filter, Finset.mem_insert, Finset.mem_map,
                Function.Embedding.coeFn_mk]
              constructor
              · rintro ⟨rfl | ⟨a, ha, rfl⟩, hinc⟩
                · rcases hinc with h | h
                  · exact absurd h.symm hv.1
                  · exact absurd h.symm hv.2
                · refine ⟨a, ⟨ha, ?_⟩, rfl⟩
                  rcases hinc with h | h
                  · exact Or.inl (Subtype.ext h)
                  · exact Or.inr (Subtype.ext h)
              · rintro ⟨a, ⟨ha, hinc⟩, rfl⟩
                exact ⟨Or.inr ⟨a, ha, rfl⟩,
                  hinc.imp (congrArg Subtype.val) (congrArg Subtype.val)⟩
            rw [hfilt, Finset.card_map, hS ⟨v, hv⟩]
        · ext e
          simp only [lift, AffineMap.coe_mk, edgeVec, S', Finset.mem_insert, Finset.mem_map,
            Function.Embedding.coeFn_mk]
          by_cases he : e = e₀
          · simp [he]
          · simp only [he, ↓reduceDIte, false_or]
            by_cases hmem : ⟨e, he⟩ ∈ S
            · simp only [hmem, ↓reduceIte]
              split_ifs with h
              · rfl
              · exact absurd ⟨⟨e, he⟩, hmem, rfl⟩ h
            · simp only [hmem, ↓reduceIte]
              split_ifs with h
              · rcases h with ⟨a, ha, rfl⟩; exact absurd ha hmem
              · rfl
      exact hsub ⟨x', hx', hlift_x⟩
    push Not at h1
    have hx_lt_one : ∀ e : E, x e < 1 := fun e => by
      have hle : x e ≤ 1 := by
        have hmem : e ∈ M.cut {M.fst e} := by
          rw [cut_singleton_eq_inc, Finset.mem_filter]; exact ⟨Finset.mem_univ e, Or.inl rfl⟩
        linarith [Finset.single_le_sum (fun f _ => hx.1 f) hmem, hx.2.1 (M.fst e)]
      exact lt_of_le_of_ne hle (h1 e)
    -- Case 2a: there exists a tight nontrivial odd set `U` (`3 ≤ |U| ≤ |V| - 3`, `x(δ(U)) = 1`).
    by_cases htight : ∃ U : Finset V,
        Odd U.card ∧ 3 ≤ U.card ∧ U.card + 3 ≤ Fintype.card V ∧ ∑ e ∈ M.cut U, x e = 1
    · obtain ⟨U, hUodd, hU3, hUc3, hUsum⟩ := htight
      -- Shrink `U` to `none` -> `M₁`, and shrink `Uᶜ` to `none` -> `M₂`.
      let V₁ := Option {v : V // v ∉ U}
      let E₁ := {e : E // ¬ (M.fst e ∈ U ∧ M.snd e ∈ U)}
      let p₁ : V → V₁ := fun v => if hv : v ∈ U then none else some ⟨v, hv⟩
      let M₁ : LooplessMultigraph V₁ E₁ :=
        { fst := fun e => p₁ (M.fst e.1)
          snd := fun e => p₁ (M.snd e.1)
          ne := fun e h => by
            dsimp only [p₁] at h
            by_cases h1 : M.fst e.1 ∈ U <;> by_cases h2 : M.snd e.1 ∈ U
            · exact e.2 ⟨h1, h2⟩
            · simp [h1, h2] at h
            · simp [h1, h2] at h
            · simp only [h1, h2, ↓reduceDIte] at h
              exact M.ne e.1 (congrArg Subtype.val (Option.some.inj h)) }
      let V₂ := Option {v : V // v ∈ U}
      let E₂ := {e : E // ¬ (M.fst e ∉ U ∧ M.snd e ∉ U)}
      let p₂ : V → V₂ := fun v => if hv : v ∈ U then some ⟨v, hv⟩ else none
      let M₂ : LooplessMultigraph V₂ E₂ :=
        { fst := fun e => p₂ (M.fst e.1)
          snd := fun e => p₂ (M.snd e.1)
          ne := fun e h => by
            dsimp only [p₂] at h
            by_cases h1 : M.fst e.1 ∈ U <;> by_cases h2 : M.snd e.1 ∈ U
            · simp only [h1, h2, ↓reduceDIte] at h
              exact M.ne e.1 (congrArg Subtype.val (Option.some.inj h))
            · simp [h1, h2] at h
            · simp [h1, h2] at h
            · exact e.2 ⟨h1, h2⟩ }
      have hcard₁ : Fintype.card V₁ + Fintype.card E₁ ≤ N := by
        have hV₁ : Fintype.card V₁ = Fintype.card V - U.card + 1 := by
          rw [Fintype.card_option, Fintype.card_subtype_compl, Fintype.card_coe]
        have hE₁ : Fintype.card E₁ ≤ Fintype.card E := Fintype.card_subtype_le _
        omega
      have hcard₂ : Fintype.card V₂ + Fintype.card E₂ ≤ N := by
        have hV₂ : Fintype.card V₂ = U.card + 1 := by
          rw [Fintype.card_option, Fintype.card_coe]
        have hE₂ : Fintype.card E₂ ≤ Fintype.card E := Fintype.card_subtype_le _
        omega
      -- Helper lifting cuts from `M₁` to `M`.
      have hcut₁ : ∀ W : Finset V₁,
          ∑ e ∈ M₁.cut W, x e.1 = ∑ e ∈ M.cut (Finset.univ.filter fun v => p₁ v ∈ W), x e := by
        intro W
        refine Finset.sum_bij (fun e _ => e.1) (fun e he => ?_)
          (fun a _ b _ h => Subtype.ext h) (fun f hf => ?_) (fun _ _ => rfl)
        · rw [mem_cut_iff] at he ⊢
          simpa [M₁] using he
        · have hne : ¬ (M.fst f ∈ U ∧ M.snd f ∈ U) := by
            rintro ⟨h1, h2⟩
            rw [mem_cut_iff] at hf
            have hp : p₁ (M.fst f) = p₁ (M.snd f) := by simp [p₁, h1, h2]
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, hp] at hf
            tauto
          refine ⟨⟨f, hne⟩, ?_, rfl⟩
          rw [mem_cut_iff] at hf ⊢
          simpa [M₁] using hf
      have hcut₂ : ∀ W : Finset V₂,
          ∑ e ∈ M₂.cut W, x e.1 = ∑ e ∈ M.cut (Finset.univ.filter fun v => p₂ v ∈ W), x e := by
        intro W
        refine Finset.sum_bij (fun e _ => e.1) (fun e he => ?_)
          (fun a _ b _ h => Subtype.ext h) (fun f hf => ?_) (fun _ _ => rfl)
        · rw [mem_cut_iff] at he ⊢
          simpa [M₂] using he
        · have hne : ¬ (M.fst f ∉ U ∧ M.snd f ∉ U) := by
            rintro ⟨h1, h2⟩
            rw [mem_cut_iff] at hf
            have hp : p₂ (M.fst f) = p₂ (M.snd f) := by simp [p₂, h1, h2]
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, hp] at hf
            tauto
          refine ⟨⟨f, hne⟩, ?_, rfl⟩
          rw [mem_cut_iff] at hf ⊢
          simpa [M₂] using hf
      have hpre₁_card : ∀ W : Finset V₁,
          (Finset.univ.filter fun v => p₁ v ∈ W).card =
            if none ∈ W then W.card - 1 + U.card else W.card := by
        intro W
        have hdisj : Disjoint (Finset.univ.filter fun v => v ∈ U ∧ p₁ v ∈ W)
            (Finset.univ.filter fun v => v ∉ U ∧ p₁ v ∈ W) :=
          Finset.disjoint_filter.2 fun _ _ h1 h2 => h2.1 h1.1
        have hunion : (Finset.univ.filter fun v => p₁ v ∈ W) =
            (Finset.univ.filter fun v => v ∈ U ∧ p₁ v ∈ W) ∪
            (Finset.univ.filter fun v => v ∉ U ∧ p₁ v ∈ W) := by
          ext v; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
        have houtside : (Finset.univ.filter fun v => v ∉ U ∧ p₁ v ∈ W).card =
            (W.erase none).card := by
          refine Finset.card_bij (fun v _ => p₁ v) (fun v hv => ?_) (fun a ha b hb h => ?_)
            (fun w hw => ?_)
          · obtain ⟨hvU, hpW⟩ := (Finset.mem_filter.1 hv).2
            exact Finset.mem_erase.2 ⟨by simp [p₁, hvU], hpW⟩
          · obtain ⟨haU, _⟩ := (Finset.mem_filter.1 ha).2
            obtain ⟨hbU, _⟩ := (Finset.mem_filter.1 hb).2
            exact congrArg Subtype.val (Option.some.inj (by simpa [p₁, haU, hbU] using h))
          · rw [Finset.mem_erase] at hw
            cases w with
            | none => exact absurd rfl hw.1
            | some a =>
              exact ⟨a.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, a.2, by simpa [p₁,
                a.2] using hw.2⟩,
                by simp [p₁, a.2]⟩
        rw [hunion, Finset.card_union_of_disjoint hdisj, houtside]
        split_ifs with hnone
        · have hins : (Finset.univ.filter fun v => v ∈ U ∧ p₁ v ∈ W) = U := by
            ext v; by_cases hv : v ∈ U <;> simp [p₁, hv, hnone]
          rw [hins, Finset.card_erase_of_mem hnone, add_comm]
        · have hins : (Finset.univ.filter fun v => v ∈ U ∧ p₁ v ∈ W) = ∅ := by
            ext v; by_cases hv : v ∈ U <;> simp [p₁, hv, hnone]
          rw [hins, Finset.card_empty, zero_add, Finset.erase_eq_of_notMem hnone]
      have hpre₂_card : ∀ W : Finset V₂,
          (Finset.univ.filter fun v => p₂ v ∈ W).card =
            if none ∈ W then W.card - 1 + Uᶜ.card else W.card := by
        intro W
        have hdisj : Disjoint (Finset.univ.filter fun v => v ∉ U ∧ p₂ v ∈ W)
            (Finset.univ.filter fun v => v ∈ U ∧ p₂ v ∈ W) :=
          Finset.disjoint_filter.2 fun _ _ h1 h2 => h1.1 h2.1
        have hunion : (Finset.univ.filter fun v => p₂ v ∈ W) =
            (Finset.univ.filter fun v => v ∉ U ∧ p₂ v ∈ W) ∪
            (Finset.univ.filter fun v => v ∈ U ∧ p₂ v ∈ W) := by
          ext v; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
        have hinside : (Finset.univ.filter fun v => v ∈ U ∧ p₂ v ∈ W).card =
            (W.erase none).card := by
          refine Finset.card_bij (fun v _ => p₂ v) (fun v hv => ?_) (fun a ha b hb h => ?_)
            (fun w hw => ?_)
          · obtain ⟨hvU, hpW⟩ := (Finset.mem_filter.1 hv).2
            exact Finset.mem_erase.2 ⟨by simp [p₂, hvU], hpW⟩
          · obtain ⟨haU, _⟩ := (Finset.mem_filter.1 ha).2
            obtain ⟨hbU, _⟩ := (Finset.mem_filter.1 hb).2
            exact congrArg Subtype.val (Option.some.inj (by simpa [p₂, haU, hbU] using h))
          · rw [Finset.mem_erase] at hw
            cases w with
            | none => exact absurd rfl hw.1
            | some a =>
              exact ⟨a.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, a.2, by simpa [p₂,
                a.2] using hw.2⟩,
                by simp [p₂, a.2]⟩
        rw [hunion, Finset.card_union_of_disjoint hdisj, hinside]
        split_ifs with hnone
        · have hins : (Finset.univ.filter fun v => v ∉ U ∧ p₂ v ∈ W) = Uᶜ := by
            ext v; by_cases hv : v ∈ U <;> simp [p₂, hv, hnone]
          rw [hins, Finset.card_erase_of_mem hnone, add_comm]
        · have hins : (Finset.univ.filter fun v => v ∉ U ∧ p₂ v ∈ W) = ∅ := by
            ext v; by_cases hv : v ∈ U <;> simp [p₂, hv, hnone]
          rw [hins, Finset.card_empty, zero_add, Finset.erase_eq_of_notMem hnone]
      have hUcodd : Odd Uᶜ.card := by
        rw [Finset.card_compl]
        obtain ⟨a, ha⟩ := hVeven
        obtain ⟨b, hb⟩ := hUodd
        refine ⟨a - b - 1, ?_⟩
        omega
      let x₁ : E₁ → ℝ := fun e => x e.1
      let x₂ : E₂ → ℝ := fun e => x e.1
      have hx₁ : x₁ ∈ M₁.pmHPolytope := by
        refine ⟨fun e => hx.1 e.1, fun w => ?_, fun W hW => ?_⟩
        · rw [hcut₁ {w}]
          cases w with
          | none =>
            have hf : (Finset.univ.filter fun v => p₁ v ∈ ({none} : Finset V₁)) = U := by
              ext v; simp [p₁]
            rw [hf, hUsum]
          | some a =>
            have hf : (Finset.univ.filter fun v => p₁ v ∈ ({some a} : Finset V₁)) = {a.1} := by
              ext v
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, p₁]
              split_ifs with hv
              · exact ⟨by simp, fun h => absurd (h ▸ a.2) (not_not.2 hv)⟩
              · exact ⟨fun h => congrArg Subtype.val (Option.some.inj h),
                  fun h => congrArg some (Subtype.ext h)⟩
            rw [hf, hx.2.1 a.1]
        · rw [hcut₁ W]
          refine hx.2.2 _ ?_
          rw [hpre₁_card W]
          split_ifs with hnone
          · obtain ⟨a, ha⟩ := hW
            obtain ⟨b, hb⟩ := hUodd
            exact ⟨a + b, by omega⟩
          · exact hW
      have hx₂ : x₂ ∈ M₂.pmHPolytope := by
        refine ⟨fun e => hx.1 e.1, fun w => ?_, fun W hW => ?_⟩
        · rw [hcut₂ {w}]
          cases w with
          | none =>
            have hf : (Finset.univ.filter fun v => p₂ v ∈ ({none} : Finset V₂)) = Uᶜ := by
              ext v; simp [p₂]
            rw [hf, cut_compl, hUsum]
          | some a =>
            have hf : (Finset.univ.filter fun v => p₂ v ∈ ({some a} : Finset V₂)) = {a.1} := by
              ext v
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, p₂]
              split_ifs with hv
              · exact ⟨fun h => congrArg Subtype.val (Option.some.inj h),
                  fun h => congrArg some (Subtype.ext h)⟩
              · exact ⟨by simp, fun h => absurd (h ▸ a.2) hv⟩
            rw [hf, hx.2.1 a.1]
        · rw [hcut₂ W]
          refine hx.2.2 _ ?_
          rw [hpre₂_card W]
          split_ifs with hnone
          · obtain ⟨a, ha⟩ := hW
            obtain ⟨b, hb⟩ := hUcodd
            exact ⟨a + b, by omega⟩
          · exact hW
      rw [← ih M₁ hcard₁] at hx₁
      rw [← ih M₂ hcard₂] at hx₂
      -- Extract finite convex combinations for `x₁` and `x₂` and glue along `M.cut U`.
      rw [pmPolytope, mem_convexHull_iff_exists_fintype] at hx₁ hx₂
      obtain ⟨ι₁, _, w₁, z₁, hw₁0, hw₁1, hz₁, hx₁eq⟩ := hx₁
      obtain ⟨ι₂, _, w₂, z₂, hw₂0, hw₂1, hz₂, hx₂eq⟩ := hx₂
      choose S₁ hS₁_eq using hz₁
      choose S₂ hS₂_eq using hz₂
      -- Every `S₁ i` has a unique edge `e₁ i` incident to `none` (which lies in `M.cut U`).
      have he₁_uniq : ∀ i : ι₁, ∃! e : E₁, e ∈ (S₁ i).1 ∧ M₁.inc e none := fun i => by
        have hc := (S₁ i).2 none
        obtain ⟨e, he⟩ := Finset.card_eq_one.1 hc
        refine ⟨e, ?_, fun f hf => Finset.mem_singleton.1 (he ▸ Finset.mem_filter.2 hf)⟩
        have hmem : e ∈ (S₁ i).1.filter fun f => M₁.inc f none := by
          rw [he]; exact Finset.mem_singleton_self e
        exact Finset.mem_filter.1 hmem
      have he₂_uniq : ∀ j : ι₂, ∃! e : E₂, e ∈ (S₂ j).1 ∧ M₂.inc e none := fun j => by
        have hc := (S₂ j).2 none
        obtain ⟨e, he⟩ := Finset.card_eq_one.1 hc
        refine ⟨e, ?_, fun f hf => Finset.mem_singleton.1 (he ▸ Finset.mem_filter.2 hf)⟩
        have hmem : e ∈ (S₂ j).1.filter fun f => M₂.inc f none := by
          rw [he]; exact Finset.mem_singleton_self e
        exact Finset.mem_filter.1 hmem
      let cutE₁ : ι₁ → E := fun i => (he₁_uniq i).choose.1
      let cutE₂ : ι₂ → E := fun j => (he₂_uniq j).choose.1
      have hcutE₁_mem : ∀ i, cutE₁ i ∈ M.cut U := fun i => by
        have hinc := (he₁_uniq i).choose_spec.1.2
        have h1 : (he₁_uniq i).choose ∈ M₁.cut {none} := by
          rw [cut_singleton_eq_inc, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hinc⟩
        rw [mem_cut_iff] at h1 ⊢
        simpa [M₁, p₁, cutE₁] using h1
      have hcutE₂_mem : ∀ j, cutE₂ j ∈ M.cut U := fun j => by
        have hinc := (he₂_uniq j).choose_spec.1.2
        have h2 : (he₂_uniq j).choose ∈ M₂.cut {none} := by
          rw [cut_singleton_eq_inc, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hinc⟩
        rw [mem_cut_iff] at h2 ⊢
        change (p₂ (M.fst (cutE₂ j)) ∈ ({none} : Finset V₂) ∧
            p₂ (M.snd (cutE₂ j)) ∉ ({none} : Finset V₂)) ∨
          (p₂ (M.fst (cutE₂ j)) ∉ ({none} : Finset V₂) ∧
            p₂ (M.snd (cutE₂ j)) ∈ ({none} : Finset V₂)) at h2
        by_cases hf : M.fst (cutE₂ j) ∈ U <;> by_cases hs : M.snd (cutE₂ j) ∈ U <;>
          simp [p₂, hf, hs] at h2 ⊢
      have hcut_in_E₁ : ∀ e ∈ M.cut U, ¬ (M.fst e ∈ U ∧ M.snd e ∈ U) := fun e he ⟨h1, h2⟩ => by
        rw [mem_cut_iff] at he; tauto
      have hcut_in_E₂ : ∀ e ∈ M.cut U, ¬ (M.fst e ∉ U ∧ M.snd e ∉ U) := fun e he ⟨h1, h2⟩ => by
        rw [mem_cut_iff] at he; tauto
      have hcutE₁_iff : ∀ (i : ι₁) (e : E) (he : e ∈ M.cut U),
          cutE₁ i = e ↔ (⟨e, hcut_in_E₁ e he⟩ : E₁) ∈ (S₁ i).1 := fun i e he => by
        constructor
        · rintro rfl
          exact (he₁_uniq i).choose_spec.1.1
        · intro hmem
          have hinc : M₁.inc ⟨e, hcut_in_E₁ e he⟩ none := by
            rw [mem_cut_iff] at he
            rcases he with ⟨h1, _⟩ | ⟨_, h2⟩
            · exact Or.inl (by simp [M₁, p₁, h1])
            · exact Or.inr (by simp [M₁, p₁, h2])
          exact congrArg Subtype.val ((he₁_uniq i).choose_spec.2 ⟨e, hcut_in_E₁ e he⟩ ⟨hmem,
            hinc⟩).symm
      have hcutE₂_iff : ∀ (j : ι₂) (e : E) (he : e ∈ M.cut U),
          cutE₂ j = e ↔ (⟨e, hcut_in_E₂ e he⟩ : E₂) ∈ (S₂ j).1 := fun j e he => by
        constructor
        · rintro rfl
          exact (he₂_uniq j).choose_spec.1.1
        · intro hmem
          have hinc : M₂.inc ⟨e, hcut_in_E₂ e he⟩ none := by
            rw [mem_cut_iff] at he
            rcases he with ⟨_, h2⟩ | ⟨h1, _⟩
            · exact Or.inr (by simp [M₂, p₂, h2])
            · exact Or.inl (by simp [M₂, p₂, h1])
          exact congrArg Subtype.val ((he₂_uniq j).choose_spec.2 ⟨e, hcut_in_E₂ e he⟩ ⟨hmem,
            hinc⟩).symm
      have hsum₁_cut : ∀ e ∈ M.cut U, ∑ i : ι₁, (if cutE₁ i = e then w₁ i else 0) = x e := by
        intro e he
        have hx1e := congrFun hx₁eq ⟨e, hcut_in_E₁ e he⟩
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, x₁] at hx1e
        rw [← hx1e]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hS₁_eq i]
        simp only [edgeVec, hcutE₁_iff i e he]
        split_ifs <;> simp
      have hsum₂_cut : ∀ e ∈ M.cut U, ∑ j : ι₂, (if cutE₂ j = e then w₂ j else 0) = x e := by
        intro e he
        have hx2e := congrFun hx₂eq ⟨e, hcut_in_E₂ e he⟩
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, x₂] at hx2e
        rw [← hx2e]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← hS₂_eq j]
        simp only [edgeVec, hcutE₂_iff j e he]
        split_ifs <;> simp
      -- Glued matching for any compatible pair `(i, j)` with `cutE₁ i = cutE₂ j`.
      let glue (i : ι₁) (j : ι₂) : Finset E :=
        (S₁ i).1.map ⟨Subtype.val, Subtype.val_injective⟩ ∪
          (S₂ j).1.map ⟨Subtype.val, Subtype.val_injective⟩
      have hglue_pm : ∀ i j, cutE₁ i = cutE₂ j → M.IsPerfectMatching (glue i j) := by
        intro i j hmatch v
        by_cases hv : v ∈ U
        · have hfilt : (glue i j).filter (fun e => M.inc e v) =
              ((S₂ j).1.filter fun e => M₂.inc e (some ⟨v, hv⟩)).map
                ⟨Subtype.val, Subtype.val_injective⟩ := by
            ext e
            simp only [glue, Finset.mem_filter, Finset.mem_union, Finset.mem_map,
              Function.Embedding.coeFn_mk]
            constructor
            · rintro ⟨⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩, hinc⟩
              · -- `a ∈ S₁ i` is incident to `v ∈ U`, so `a` must be `cutE₁ i = cutE₂ j`.
                have hinc1 : M₁.inc a none := by
                  rcases hinc with h | h
                  · exact Or.inl (by simp [M₁, p₁, h, hv])
                  · exact Or.inr (by simp [M₁, p₁, h, hv])
                have ha_eq : a.1 = cutE₁ i :=
                  congrArg Subtype.val ((he₁_uniq i).choose_spec.2 a ⟨ha, hinc1⟩)
                have hmem2 : (⟨a.1, hcut_in_E₂ a.1 (ha_eq ▸ hcutE₁_mem i)⟩ : E₂) ∈ (S₂ j).1 :=
                  (hcutE₂_iff j a.1 (ha_eq ▸ hcutE₁_mem i)).1 (hmatch.symm.trans ha_eq.symm)
                refine ⟨⟨a.1, hcut_in_E₂ a.1 (ha_eq ▸ hcutE₁_mem i)⟩, ⟨hmem2, ?_⟩, rfl⟩
                rcases hinc with h | h
                · exact Or.inl (by simp [M₂, p₂, h, hv])
                · exact Or.inr (by simp [M₂, p₂, h, hv])
              · refine ⟨b, ⟨hb, ?_⟩, rfl⟩
                rcases hinc with h | h
                · exact Or.inl (by simp [M₂, p₂, h, hv])
                · exact Or.inr (by simp [M₂, p₂, h, hv])
            · rintro ⟨b, ⟨hb, hinc⟩, rfl⟩
              refine ⟨Or.inr ⟨b, hb, rfl⟩, ?_⟩
              rcases hinc with h | h
              · by_cases hf : M.fst b.1 ∈ U
                · simp only [M₂, p₂, hf, ↓reduceDIte] at h
                  exact Or.inl (congrArg Subtype.val (Option.some.inj h))
                · simp [M₂, p₂, hf] at h
              · by_cases hs : M.snd b.1 ∈ U
                · simp only [M₂, p₂, hs, ↓reduceDIte] at h
                  exact Or.inr (congrArg Subtype.val (Option.some.inj h))
                · simp [M₂, p₂, hs] at h
          rw [hfilt, Finset.card_map, (S₂ j).2 (some ⟨v, hv⟩)]
        · have hfilt : (glue i j).filter (fun e => M.inc e v) =
              ((S₁ i).1.filter fun e => M₁.inc e (some ⟨v, hv⟩)).map
                ⟨Subtype.val, Subtype.val_injective⟩ := by
            ext e
            simp only [glue, Finset.mem_filter, Finset.mem_union, Finset.mem_map,
              Function.Embedding.coeFn_mk]
            constructor
            · rintro ⟨⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩, hinc⟩
              · refine ⟨a, ⟨ha, ?_⟩, rfl⟩
                rcases hinc with h | h
                · exact Or.inl (by simp [M₁, p₁, h, hv])
                · exact Or.inr (by simp [M₁, p₁, h, hv])
              · have hinc2 : M₂.inc b none := by
                  rcases hinc with h | h
                  · exact Or.inl (by simp [M₂, p₂, h, hv])
                  · exact Or.inr (by simp [M₂, p₂, h, hv])
                have hb_eq : b.1 = cutE₂ j :=
                  congrArg Subtype.val ((he₂_uniq j).choose_spec.2 b ⟨hb, hinc2⟩)
                have hmem1 : (⟨b.1, hcut_in_E₁ b.1 (hb_eq ▸ hcutE₂_mem j)⟩ : E₁) ∈ (S₁ i).1 :=
                  (hcutE₁_iff i b.1 (hb_eq ▸ hcutE₂_mem j)).1 (hmatch.trans hb_eq.symm)
                refine ⟨⟨b.1, hcut_in_E₁ b.1 (hb_eq ▸ hcutE₂_mem j)⟩, ⟨hmem1, ?_⟩, rfl⟩
                rcases hinc with h | h
                · exact Or.inl (by simp [M₁, p₁, h, hv])
                · exact Or.inr (by simp [M₁, p₁, h, hv])
            · rintro ⟨a, ⟨ha, hinc⟩, rfl⟩
              refine ⟨Or.inl ⟨a, ha, rfl⟩, ?_⟩
              rcases hinc with h | h
              · by_cases hf : M.fst a.1 ∈ U
                · simp [M₁, p₁, hf] at h
                · simp only [M₁, p₁, hf, ↓reduceDIte] at h
                  exact Or.inl (congrArg Subtype.val (Option.some.inj h))
              · by_cases hs : M.snd a.1 ∈ U
                · simp [M₁, p₁, hs] at h
                · simp only [M₁, p₁, hs, ↓reduceDIte] at h
                  exact Or.inr (congrArg Subtype.val (Option.some.inj h))
          rw [hfilt, Finset.card_map, (S₁ i).2 (some ⟨v, hv⟩)]
      -- Combine compatible pairs `S = {(i, j) | cutE₁ i = cutE₂ j}` with weight `w₁ i * w₂ j / x
      -- (cutE₁ i)`.
      let S : Finset (ι₁ × ι₂) := Finset.univ.filter fun p => cutE₁ p.1 = cutE₂ p.2
      let wt : ι₁ × ι₂ → ℝ := fun p => w₁ p.1 * w₂ p.2 / x (cutE₁ p.1)
      have hwt0 : ∀ p ∈ S, 0 ≤ wt p := fun p _ =>
        div_nonneg (mul_nonneg (hw₁0 p.1) (hw₂0 p.2)) (hx.1 _)
      have hsum_by_i : ∀ f : ι₁ → ℝ,
          ∑ p ∈ S, f p.1 * (w₂ p.2 / x (cutE₁ p.1)) = ∑ i : ι₁, f i := by
        intro f
        rw [Finset.sum_filter, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hinner : ∑ j : ι₂, (if cutE₁ i = cutE₂ j then f i * (w₂ j / x (cutE₁ i)) else 0) =
            (f i / x (cutE₁ i)) * ∑ j : ι₂, (if cutE₂ j = cutE₁ i then w₂ j else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs with h1 h2 h3
          · ring
          · exact absurd h1.symm h2
          · exact absurd h3.symm h1
          · simp
        rw [hinner, hsum₂_cut (cutE₁ i) (hcutE₁_mem i)]
        exact div_mul_cancel₀ (f i) (hx_pos (cutE₁ i)).ne'
      have hsum_by_j : ∀ g : ι₂ → ℝ,
          ∑ p ∈ S, (w₁ p.1 / x (cutE₁ p.1)) * g p.2 = ∑ j : ι₂, g j := by
        intro g
        rw [Finset.sum_filter, Fintype.sum_prod_type_right]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hinner : ∑ i : ι₁, (if cutE₁ i = cutE₂ j then (w₁ i / x (cutE₁ i)) * g j else 0) =
            (g j / x (cutE₂ j)) * ∑ i : ι₁, (if cutE₁ i = cutE₂ j then w₁ i else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : cutE₁ i = cutE₂ j
          · simp [h]; ring
          · simp [h]
        rw [hinner, hsum₁_cut (cutE₂ j) (hcutE₂_mem j)]
        exact div_mul_cancel₀ (g j) (hx_pos (cutE₂ j)).ne'
      have hwt_sum : ∑ p ∈ S, wt p = 1 := by
        have h := hsum_by_i w₁
        rw [hw₁1] at h
        refine (Finset.sum_congr rfl fun p _ => ?_).trans h
        dsimp only [wt]; ring
      have hcenter : S.centerMass wt (fun p => edgeVec (glue p.1 p.2)) = x := by
        rw [Finset.centerMass_eq_of_sum_1 _ _ hwt_sum]
        ext e
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        by_cases hcut : e ∈ M.cut U
        · have hmem_iff : ∀ p ∈ S, e ∈ glue p.1 p.2 ↔ cutE₁ p.1 = e := by
            intro p hp
            have hmatch : cutE₁ p.1 = cutE₂ p.2 := (Finset.mem_filter.1 hp).2
            simp only [glue, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk]
            constructor
            · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
              · exact (hcutE₁_iff p.1 a.1 hcut).2 (by simpa using ha)
              · exact hmatch.trans ((hcutE₂_iff p.2 b.1 hcut).2 (by simpa using hb))
            · intro heq
              exact Or.inl ⟨⟨e, hcut_in_E₁ e hcut⟩, (hcutE₁_iff p.1 e hcut).1 heq, rfl⟩
          have heq_sum : ∑ p ∈ S, wt p * edgeVec (glue p.1 p.2) e =
              ∑ p ∈ S, (if cutE₁ p.1 = e then w₁ p.1 else 0) * (w₂ p.2 / x (cutE₁ p.1)) := by
            refine Finset.sum_congr rfl fun p hp => ?_
            simp only [wt, edgeVec, hmem_iff p hp]
            split_ifs <;> ring
          rw [heq_sum, hsum_by_i (fun i => if cutE₁ i = e then w₁ i else 0), hsum₁_cut e hcut]
        · by_cases hbothU : M.fst e ∈ U ∧ M.snd e ∈ U
          · have hE₂ : ¬ (M.fst e ∉ U ∧ M.snd e ∉ U) := by tauto
            have hmem_iff : ∀ p ∈ S, e ∈ glue p.1 p.2 ↔ (⟨e, hE₂⟩ : E₂) ∈ (S₂ p.2).1 := by
              intro p _
              simp only [glue, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk]
              constructor
              · rintro (⟨a, _, ha⟩ | ⟨b, hb, rfl⟩)
                · exfalso; exact a.2 (ha.symm ▸ hbothU)
                · exact hb
              · intro hb; exact Or.inr ⟨⟨e, hE₂⟩, hb, rfl⟩
            have heq_sum : ∑ p ∈ S, wt p * edgeVec (glue p.1 p.2) e =
                ∑ p ∈ S, (w₁ p.1 / x (cutE₁ p.1)) *
                  (if (⟨e, hE₂⟩ : E₂) ∈ (S₂ p.2).1 then w₂ p.2 else 0) := by
              refine Finset.sum_congr rfl fun p hp => ?_
              simp only [wt, edgeVec, hmem_iff p hp]
              split_ifs <;> ring
            rw [heq_sum, hsum_by_j (fun j => if (⟨e, hE₂⟩ : E₂) ∈ (S₂ j).1 then w₂ j else 0)]
            have hx2e := congrFun hx₂eq ⟨e, hE₂⟩
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, x₂] at hx2e
            rw [← hx2e]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← hS₂_eq j]
            simp only [edgeVec]
            split_ifs <;> simp
          · have hbothOut : M.fst e ∉ U ∧ M.snd e ∉ U := by
              rw [mem_cut_iff] at hcut
              tauto
            have hmem_iff : ∀ p ∈ S, e ∈ glue p.1 p.2 ↔ (⟨e, hbothU⟩ : E₁) ∈ (S₁ p.1).1 := by
              intro p _
              simp only [glue, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk]
              constructor
              · rintro (⟨a, ha, rfl⟩ | ⟨b, _, hb⟩)
                · exact ha
                · exfalso; exact b.2 (hb.symm ▸ hbothOut)
              · intro ha; exact Or.inl ⟨⟨e, hbothU⟩, ha, rfl⟩
            have heq_sum : ∑ p ∈ S, wt p * edgeVec (glue p.1 p.2) e =
                ∑ p ∈ S, (if (⟨e, hbothU⟩ : E₁) ∈ (S₁ p.1).1 then w₁ p.1 else 0) *
                  (w₂ p.2 / x (cutE₁ p.1)) := by
              refine Finset.sum_congr rfl fun p hp => ?_
              simp only [wt, edgeVec, hmem_iff p hp]
              split_ifs <;> ring
            rw [heq_sum, hsum_by_i (fun i => if (⟨e, hbothU⟩ : E₁) ∈ (S₁ i).1 then w₁ i else 0)]
            have hx1e := congrFun hx₁eq ⟨e, hbothU⟩
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, x₁] at hx1e
            rw [← hx1e]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← hS₁_eq i]
            simp only [edgeVec]
            split_ifs <;> simp
      rw [← hcenter, pmPolytope]
      exact S.centerMass_mem_convexHull hwt0 (hwt_sum ▸ zero_lt_one) fun p hp =>
        ⟨⟨glue p.1 p.2, hglue_pm p.1 p.2 (Finset.mem_filter.1 hp).2⟩, rfl⟩
    -- Case 2b: no tight nontrivial odd set!
    push Not at htight
    have hker : ∀ d : E → ℝ, (∀ v : V, ∑ e ∈ M.cut {v}, d e = 0) → d = 0 := by
      intro d hd
      by_contra hdne
      -- Choose `ε > 0` small enough so `x ± ε • d ∈ pmHPolytope M`.
      let Dmax : ℝ := 1 + ∑ e : E, |d e|
      have hDmax : 0 < Dmax := by
        have : 0 ≤ ∑ e : E, |d e| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        linarith
      let oddNonTriv : Finset (Finset V) :=
        Finset.univ.filter fun U => Odd U.card ∧ 3 ≤ U.card ∧ U.card + 3 ≤ Fintype.card V
      let sE : Finset ℝ := Finset.univ.image fun e : E => x e / Dmax
      let sU : Finset ℝ := oddNonTriv.image fun U => ((∑ e ∈ M.cut U, x e) - 1) / Dmax
      let sAll : Finset ℝ := insert 1 (sE ∪ sU)
      have hsAll_ne : sAll.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
      let ε : ℝ := sAll.min' hsAll_ne
      have hε_pos : 0 < ε := by
        rw [Finset.lt_min'_iff]
        intro r hr
        rw [Finset.mem_insert, Finset.mem_union] at hr
        rcases hr with rfl | h1 | h2
        · exact one_pos
        · obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 h1
          exact div_pos (hx_pos e) hDmax
        · obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 h2
          obtain ⟨hUodd, hU3, hUc3⟩ := (Finset.mem_filter.1 hU).2
          have hge := hx.2.2 U hUodd
          have hne := htight U hUodd hU3 hUc3
          exact div_pos (sub_pos.2 (lt_of_le_of_ne hge (Ne.symm hne))) hDmax
      have hpm_mem : ∀ s : ℝ, |s| ≤ ε → x + s • d ∈ M.pmHPolytope := by
        intro s hs
        have hsd_e : ∀ e : E, |s * d e| ≤ x e := fun e => by
          have hεe : ε ≤ x e / Dmax := Finset.min'_le _ _
            (Finset.mem_insert_of_mem (Finset.mem_union_left _
              (Finset.mem_image.2 ⟨e, Finset.mem_univ e, rfl⟩)))
          have hde : |d e| ≤ Dmax := by
            have h1 := Finset.single_le_sum (f := fun f : E => |d f|)
              (fun _ _ => abs_nonneg _) (Finset.mem_univ e)
            linarith
          calc |s * d e| = |s| * |d e| := abs_mul s (d e)
            _ ≤ (x e / Dmax) * Dmax :=
              mul_le_mul (hs.trans hεe) hde (abs_nonneg _) (div_nonneg (hx.1 e) hDmax.le)
            _ = x e := div_mul_cancel₀ _ hDmax.ne'
        refine ⟨fun e => ?_, fun v => ?_, fun U hU => ?_⟩
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          linarith [(abs_le.1 (hsd_e e)).1]
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
            ← Finset.mul_sum, hx.2.1 v, hd v, mul_zero, add_zero]
        · by_cases h1 : U.card = 1
          · obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 h1
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
              ← Finset.mul_sum, hx.2.1 v, hd v, mul_zero, add_zero, le_refl]
          · by_cases hcompl : U.card + 1 = Fintype.card V
            · have hccard : Uᶜ.card = 1 := by rw [Finset.card_compl]; omega
              obtain ⟨v, hv⟩ := Finset.card_eq_one.1 hccard
              have hcut_eq : M.cut U = M.cut {v} := by rw [← hv, cut_compl]
              rw [hcut_eq]
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
                ← Finset.mul_sum, hx.2.1 v, hd v, mul_zero, add_zero, le_refl]
            · have hU3 : 3 ≤ U.card := by obtain ⟨k, hk⟩ := hU; omega
              have hUc3 : U.card + 3 ≤ Fintype.card V := by
                have hle : U.card ≤ Fintype.card V := Finset.card_le_univ U
                obtain ⟨a, ha⟩ := hVeven
                obtain ⟨b, hb⟩ := hU
                omega
              have hUmem : U ∈ oddNonTriv :=
                Finset.mem_filter.2 ⟨Finset.mem_univ U, hU, hU3, hUc3⟩
              have hεU : ε ≤ ((∑ e ∈ M.cut U, x e) - 1) / Dmax := Finset.min'_le _ _
                (Finset.mem_insert_of_mem (Finset.mem_union_right _
                  (Finset.mem_image.2 ⟨U, hUmem, rfl⟩)))
              have hdU : |∑ e ∈ M.cut U, d e| ≤ Dmax := by
                calc |∑ e ∈ M.cut U, d e|
                    ≤ ∑ e ∈ M.cut U, |d e| := Finset.abs_sum_le_sum_abs _ _
                  _ ≤ ∑ e : E, |d e| :=
                      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                        fun _ _ _ => abs_nonneg _
                  _ ≤ Dmax := by linarith
              have hbound : |s * ∑ e ∈ M.cut U, d e| ≤ (∑ e ∈ M.cut U, x e) - 1 := by
                calc |s * ∑ e ∈ M.cut U, d e|
                    = |s| * |∑ e ∈ M.cut U, d e| := abs_mul _ _
                  _ ≤ (((∑ e ∈ M.cut U, x e) - 1) / Dmax) * Dmax :=
                      mul_le_mul (hs.trans hεU) hdU (abs_nonneg _)
                        (div_nonneg (sub_nonneg.2 (hx.2.2 U hU)) hDmax.le)
                  _ = (∑ e ∈ M.cut U, x e) - 1 := div_mul_cancel₀ _ hDmax.ne'
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
                ← Finset.mul_sum]
              linarith [(abs_le.1 hbound).1]
      have hplus : x + ε • d ∈ M.pmHPolytope := hpm_mem ε (by rw [abs_of_pos hε_pos])
      have hminus : x + (-ε) • d ∈ M.pmHPolytope :=
        hpm_mem (-ε) (by rw [abs_neg, abs_of_pos hε_pos])
      have hmid : x ∈ openSegment ℝ (x + ε • d) (x + (-ε) • d) := by
        refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
        ext e; simp; ring
      have heq := (mem_extremePoints.1 hxExt).2 _ hplus _ hminus hmid
      have hεd : ε • d = 0 := by
        have h := heq.1
        have : x + ε • d = x := h
        exact add_left_cancel (this.trans (add_zero x).symm)
      exact hdne ((smul_eq_zero.1 hεd).resolve_left hε_pos.ne')
    -- Rank-nullity on vertex incidence map gives `|E| ≤ |V|`.
    let incMap : (E → ℝ) →ₗ[ℝ] (V → ℝ) :=
      { toFun := fun d v => ∑ e ∈ M.cut {v}, d e
        map_add' := fun d₁ d₂ => by ext v; simp [Finset.sum_add_distrib]
        map_smul' := fun c d => by ext v; simp [Finset.mul_sum] }
    have hker_bot : LinearMap.ker incMap = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro d hd
      exact hker d (fun v => congrFun hd v)
    have hE_le_V : Fintype.card E ≤ Fintype.card V := by
      have h1 := LinearMap.finrank_range_add_finrank_ker incMap
      rw [hker_bot, finrank_bot, add_zero, Module.finrank_pi_fintype] at h1
      have h2 : Module.finrank ℝ (LinearMap.range incMap) ≤ Module.finrank ℝ (V → ℝ) :=
        Submodule.finrank_le _
      rw [Module.finrank_pi_fintype] at h2
      simpa using h1.symm.le.trans h2
    -- Every vertex has degree `≥ 2` (since `∀ e, x e < 1` and `∑_{δ(v)} x e = 1`).
    have hdeg_ge : ∀ v : V, 2 ≤ (M.cut {v}).card := by
      intro v
      by_contra hlt
      have hle : (M.cut {v}).card ≤ 1 := by omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h0 | h1
      · have hemp := Finset.card_eq_zero.1 h0
        have := hx.2.1 v
        rw [hemp, Finset.sum_empty] at this
        linarith
      · obtain ⟨e, he⟩ := Finset.card_eq_one.1 h1
        have := hx.2.1 v
        rw [he, Finset.sum_singleton] at this
        linarith [hx_lt_one e]
    -- Handshaking gives `∑ v, deg(v) = 2 * |E|`, forcing `deg(v) = 2` for all `v`.
    have hhandshake : ∑ v : V, (M.cut {v}).card = 2 * Fintype.card E := by
      have h1 := sum_cut_add_two_mul_induced M Finset.univ (fun _ => (1 : ℝ))
      rw [cut_univ, Finset.sum_empty, zero_add] at h1
      have hfilt : (Finset.univ.filter fun e : E => M.fst e ∈ (Finset.univ : Finset V) ∧
          M.snd e ∈ (Finset.univ : Finset V)) = Finset.univ := by
        ext e; simp
      rw [hfilt] at h1
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h1
      have hnat : 2 * Fintype.card E = ∑ v : V, (M.cut {v}).card := by
        have hR : 2 * (Fintype.card E : ℝ) = ∑ v : V, ((M.cut {v}).card : ℝ) := h1
        exact_mod_cast hR
      exact hnat.symm
    have hdeg_eq : ∀ v : V, (M.cut {v}).card = 2 := by
      intro v
      by_contra hne
      have hgt : 3 ≤ (M.cut {v}).card := by have := hdeg_ge v; omega
      have hsum_gt : 2 * Fintype.card V < ∑ w : V, (M.cut {w}).card := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
        have hrest : 2 * (Fintype.card V - 1) ≤ ∑ w ∈ Finset.univ.erase v, (M.cut {w}).card := by
          calc 2 * (Fintype.card V - 1)
              = ∑ _w ∈ Finset.univ.erase v, 2 := by
                rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ v),
                  Finset.card_univ, smul_eq_mul, mul_comm]
            _ ≤ ∑ w ∈ Finset.univ.erase v, (M.cut {w}).card :=
                Finset.sum_le_sum fun w _ => hdeg_ge w
        have hVpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 hVne
        omega
      omega
    -- Apply 2-regular dichotomy: either an odd component with empty cut or nonzero kernel vector.
    rcases odd_component_or_kernel_of_two_regular M hdeg_eq with ⟨U, hUodd, hUcut⟩ | ⟨d, hdne, hd⟩
    · have h1 := hx.2.2 U hUodd
      rw [hUcut, Finset.sum_empty] at h1
      linarith
    · exact (hdne (hker d hd)).elim

end LooplessMultigraph

end MultigraphMatching

end CslibFrontier.ExtendedFormulation
