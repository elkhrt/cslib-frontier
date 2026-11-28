module

public import CslibFrontier.Computability.Communication.DirectProduct.IntersectionDist
public import CslibFrontier.Computability.Communication.DirectProduct.LinearProgram
public import CslibFrontier.Computability.Communication.Operations
import Cslib.Probability.PMF
import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Limited-Ambiguity Arthur-Merlin Protocols and Direct Product for Search

Nondeterministic and Arthur-Merlin (AM) two-party communication protocols with bounded ambiguity,
together with strong direct product lower bounds for `k`-fold intersection search:

* `NondetProtocol` and `AMProtocol`: finite indexed families of deterministic protocols and
  public-coin mixtures (`PMF`) thereof, with ambiguity parameter `t` (`HasAmbiguity`).
* `protocolToNondet` and `publicCoinToAM`: canonical unambiguous (`t = 1`) embeddings of
  `Cslib.Communication.Protocol` and `Cslib.Communication.PublicCoin`.
* `am_dual_bound` and `am_search_choose_bound`: LP weak duality lower bounds for limited-ambiguity
  AM protocols solving `SEARCH_{C(N,k)}`.
* Random-permutation coordinate separation and `sdpt_searchK`: strong direct product theorem for
  randomized and limited-ambiguity AM protocols solving `SEARCH_n^(k)`.
-/

public section

namespace CslibFrontier.Computability.Communication

open Cslib Finset Cslib.Communication

/-! ### Nondeterministic and Arthur–Merlin protocols with ambiguity `t` -/

/-- A nondeterministic communication protocol: a finite indexed collection of
`size` combinatorial rectangles `alice r × bob r`, each labeled by an output `output r : Z`. -/
@[ext] structure NondetProtocol (X Y Z : Type*) where
  /-- Number of labeled rectangles (communication cost `c` means `size ≤ 2 ^ c`). -/
  size : ℕ
  /-- Alice's side of each rectangle. -/
  alice : Fin size → Set X
  /-- Bob's side of each rectangle. -/
  bob : Fin size → Set Y
  /-- Output label of each rectangle. -/
  output : Fin size → Z

namespace NondetProtocol

variable {X Y Z : Type*}

/-- Number of rectangles of `P` containing the input pair `(x, y)`. -/
@[expose] noncomputable def ambiguityAt (P : NondetProtocol X Y Z) (x : X) (y : Y) : ℕ := by
  classical
  exact #{r : Fin P.size | x ∈ P.alice r ∧ y ∈ P.bob r}

/-- Cardinality formula for `NondetProtocol.ambiguityAt`. -/
theorem ambiguityAt_eq_card (P : NondetProtocol X Y Z) (x : X) (y : Y)
    [DecidablePred fun r : Fin P.size => x ∈ P.alice r ∧ y ∈ P.bob r] :
    P.ambiguityAt x y = #{r : Fin P.size | x ∈ P.alice r ∧ y ∈ P.bob r} := by
  unfold ambiguityAt
  congr 1
  ext r
  simp

/-- `P` has ambiguity at most `t`: every input pair lies in at most `t` rectangles of `P`. -/
@[expose] def HasAmbiguity (P : NondetProtocol X Y Z) (t : ℕ) : Prop :=
  ∀ x y, P.ambiguityAt x y ≤ t

/-- `P` has communication cost at most `c`: it uses at most `2 ^ c` rectangles. -/
@[expose] def HasComm (P : NondetProtocol X Y Z) (c : ℕ) : Prop :=
  P.size ≤ 2 ^ c

/-- Characterization of `NondetProtocol.HasComm`. -/
theorem hasComm_iff (P : NondetProtocol X Y Z) (c : ℕ) :
    P.HasComm c ↔ P.size ≤ 2 ^ c := Iff.rfl

/-- `P` accepts a valid answer for relation `R` on `(x, y)` if some rectangle containing `(x, y)`
is labeled with an output `z` satisfying `R x y z`. -/
@[expose] def Accepts (P : NondetProtocol X Y Z) (R : X → Y → Z → Prop) (x : X) (y : Y) : Prop :=
  ∃ r : Fin P.size, x ∈ P.alice r ∧ y ∈ P.bob r ∧ R x y (P.output r)

/-- Pull back a nondeterministic protocol along local input maps `f : X' → X` and `g : Y' → Y`. -/
@[expose] def comap {X' Y' : Type*} (f : X' → X) (g : Y' → Y) (P : NondetProtocol X Y Z) :
    NondetProtocol X' Y' Z where
  size := P.size
  alice r := f ⁻¹' P.alice r
  bob r := g ⁻¹' P.bob r
  output := P.output

/-- Relabel the outputs of a nondeterministic protocol by `h : Z → Z'`. -/
@[expose] def map {Z' : Type*} (h : Z → Z') (P : NondetProtocol X Y Z) : NondetProtocol X Y Z' where
  size := P.size
  alice := P.alice
  bob := P.bob
  output r := h (P.output r)

theorem comap_hasComm {X' Y' : Type*} {f : X' → X} {g : Y' → Y} {P : NondetProtocol X Y Z}
    {c : ℕ} (h : P.HasComm c) : (P.comap f g).HasComm c := h

theorem comap_hasAmbiguity {X' Y' : Type*} {f : X' → X} {g : Y' → Y} {P : NondetProtocol X Y Z}
    {t : ℕ} (h : P.HasAmbiguity t) : (P.comap f g).HasAmbiguity t := fun x y => h (f x) (g y)

theorem map_hasComm {Z' : Type*} {h : Z → Z'} {P : NondetProtocol X Y Z} {c : ℕ}
    (hc : P.HasComm c) : (P.map h).HasComm c := hc

theorem map_hasAmbiguity {Z' : Type*} {h : Z → Z'} {P : NondetProtocol X Y Z} {t : ℕ}
    (ht : P.HasAmbiguity t) : (P.map h).HasAmbiguity t := ht

end NondetProtocol

/-- An Arthur–Merlin (AM) communication protocol: a convex combination (`PMF`)
of nondeterministic protocols. -/
abbrev AMProtocol (X Y Z : Type*) := PMF (NondetProtocol X Y Z)

namespace AMProtocol

variable {X Y Z : Type*}

/-- Every nondeterministic protocol in the support of `μ` has communication cost at most `c`. -/
@[expose] def HasComm (μ : AMProtocol X Y Z) (c : ℕ) : Prop :=
  ∀ P ∈ μ.support, P.HasComm c

/-- Every nondeterministic protocol in the support of `μ` has ambiguity at most `t`. -/
@[expose] def HasAmbiguity (μ : AMProtocol X Y Z) (t : ℕ) : Prop :=
  ∀ P ∈ μ.support, P.HasAmbiguity t

/-- The probability over Arthur's public coins that `P ~ μ` contains `(x, y)` in a rectangle
labeled with a valid answer for `R`. -/
@[expose] noncomputable def successProb (μ : AMProtocol X Y Z) (R : X → Y → Z →
  Prop) (x : X) (y : Y) : ℝ :=
  (μ.toOuterMeasure {P | P.Accepts R x y}).toReal

/-- Outer-measure characterization of `AMProtocol.successProb`. -/
theorem successProb_eq_toOuterMeasure (μ : AMProtocol X Y Z) (R : X → Y → Z → Prop)
    (x : X) (y : Y) :
    μ.successProb R x y = (μ.toOuterMeasure {P | P.Accepts R x y}).toReal := rfl

/-- `μ` achieves worst-case success probability at least `σ` for relation `R`. -/
@[expose] def SolvesWithSuccess (μ : AMProtocol X Y Z) (σ : ℝ) (R : X → Y → Z → Prop) : Prop :=
  ∀ x y, σ ≤ μ.successProb R x y

/-- Success probability of an AM protocol is at most `1`. -/
theorem successProb_le_one (μ : AMProtocol X Y Z) (R : X → Y → Z → Prop) (x : X) (y : Y) :
    μ.successProb R x y ≤ 1 :=
  Cslib.Probability.PMF.toOuterMeasure_toReal_le_one μ _

/-- On nonempty domains, any achievable worst-case AM success probability is at most `1`. -/
theorem solvesWithSuccess_le_one [Nonempty X] [Nonempty Y] {μ : AMProtocol X Y Z} {σ : ℝ}
    {R : X → Y → Z → Prop} (h : μ.SolvesWithSuccess σ R) : σ ≤ 1 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨y⟩ := ‹Nonempty Y›
  exact (h x y).trans (μ.successProb_le_one R x y)

end AMProtocol

/-- Convert a deterministic protocol `p` into an unambiguous (`t = 1`) nondeterministic protocol
using its leaf partition. -/
def protocolToNondet {X Y Z : Type*} (p : Protocol X Y Z) : NondetProtocol X Y Z where
  size := p.leafCount
  alice := p.leafAlice
  bob := p.leafBob
  output := p.leafOutput

/-- `protocolToNondet p` has communication cost at most `p.depth`. -/
theorem protocolToNondet_hasComm {X Y Z : Type*} (p : Protocol X Y Z) :
    (protocolToNondet p).HasComm p.depth :=
  p.leafCount_le_two_pow_depth

/-- `protocolToNondet p` is unambiguous (ambiguity at most `1`). -/
theorem protocolToNondet_hasAmbiguity {X Y Z : Type*} (p : Protocol X Y Z) :
    (protocolToNondet p).HasAmbiguity 1 := by
  intro x y
  classical
  unfold NondetProtocol.ambiguityAt protocolToNondet
  have hfl : (univ.filter fun r : Fin p.leafCount => x ∈ p.leafAlice r ∧ y ∈ p.leafBob r) =
      {p.leaf x y} := by
    ext r
    simp only [mem_filter, mem_univ, true_and, mem_singleton, ← Protocol.leaf_eq_iff, eq_comm]
  rw [hfl, card_singleton]

/-- `protocolToNondet p` accepts `R` on `(x, y)` iff `p.run x y` satisfies `R x y`. -/
theorem protocolToNondet_accepts_iff {X Y Z : Type*} (p : Protocol X Y Z)
    (R : X → Y → Z → Prop) (x : X) (y : Y) :
    (protocolToNondet p).Accepts R x y ↔ R x y (p.run x y) := by
  dsimp only [protocolToNondet, NondetProtocol.Accepts]
  constructor
  · rintro ⟨r, hx, hy, hR⟩
    rwa [Protocol.run_eq_leafOutput hx hy]
  · intro hR
    refine ⟨p.leaf x y, Protocol.mem_leafAlice_leaf, Protocol.mem_leafBob_leaf, ?_⟩
    rwa [← Protocol.run_eq_leafOutput_leaf]

/-- Canonical embedding of a public-coin protocol into an unambiguous AM protocol. -/
noncomputable def publicCoinToAM {X Y Z : Type*} (μ : PublicCoin X Y Z) : AMProtocol X Y Z :=
  μ.map protocolToNondet

/-- `publicCoinToAM μ` preserves the communication bound `c`. -/
theorem publicCoinToAM_hasComm {X Y Z : Type*} {μ : PublicCoin X Y Z} {c : ℕ}
    (hdepth : μ.depth ≤ c) : (publicCoinToAM μ).HasComm c := by
  intro P hP
  rw [publicCoinToAM, PMF.support_map] at hP
  obtain ⟨p, hp, rfl⟩ := hP
  have hd : p.depth ≤ c := Nat.cast_le (α := ℕ∞).mp ((PublicCoin.depth_le_depth hp).trans hdepth)
  exact (protocolToNondet_hasComm p).trans (Nat.pow_le_pow_right two_pos hd)

/-- `publicCoinToAM μ` is always unambiguous (`HasAmbiguity 1`). -/
theorem publicCoinToAM_hasAmbiguity {X Y Z : Type*} (μ : PublicCoin X Y Z) :
    (publicCoinToAM μ).HasAmbiguity 1 := by
  intro P hP
  rw [publicCoinToAM, PMF.support_map] at hP
  obtain ⟨p, _, rfl⟩ := hP
  exact protocolToNondet_hasAmbiguity p

/-- `publicCoinToAM μ` has the exact same success probability as `μ`. -/
theorem publicCoinToAM_successProb {X Y Z : Type*} (μ : PublicCoin X Y Z)
    (R : X → Y → Z → Prop) (x : X) (y : Y) :
    (publicCoinToAM μ).successProb R x y = successProb μ R x y := by
  rw [AMProtocol.successProb, publicCoinToAM, PMF.toOuterMeasure_map_apply,
    successProb_eq_toOuterMeasure]
  congr 2
  ext p
  exact protocolToNondet_accepts_iff p R x y

/-! ### AM LP dual bound for `SEARCH_{C(N,k)}` -/

/-- Single-instance nondeterministic dual bound with ambiguity `t`. -/
private theorem nondet_protocol_dual_bound {N k t : ℕ}
    (P : NondetProtocol (BitString N) (BitString N) (Option (Finset (Fin N))))
    (hamb : P.HasAmbiguity t) {D : DualSolution N} (hD : IsDualFeasible N k D) :
    ∑ x : BitString N, ∑ y : BitString N,
        (({Q : NondetProtocol (BitString N) (BitString N) (Option (Finset (Fin N))) |
            Q.Accepts (SearchChooseRel N k) x y}.indicator (fun _ => D.phi x y) P) +
          (t : ℝ) * D.psi x y) ≤ (P.size : ℝ) := by
  classical
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  obtain ⟨hDphi, hDpsi, hDsupp, hDrect⟩ := hD
  let goodRect (r : Fin P.size) : Prop :=
    match P.output r with
    | none => False
    | some I => I.card = k
  let rectA (r : Fin P.size) : Finset (BitString N) :=
    match P.output r with
    | none => ∅
    | some I => univ.filter fun x => x ∈ P.alice r ∧ I ⊆ supportSet x
  let rectB (r : Fin P.size) : Finset (BitString N) :=
    match P.output r with
    | none => ∅
    | some I => univ.filter fun y => y ∈ P.bob r ∧ I ⊆ supportSet y
  have hgood_le : ∀ r : Fin P.size, goodRect r →
      ∑ x ∈ rectA r, ∑ y ∈ rectB r, (D.phi x y + D.psi x y) ≤ 1 := by
    intro r hr
    cases ho : P.output r with
    | none => simp [goodRect, ho] at hr
    | some I =>
      simp only [goodRect, ho] at hr
      apply hDrect
      refine ⟨I, hr, ?_, ?_⟩
      · intro x hx; simp only [rectA, ho, mem_filter, mem_univ, true_and] at hx; exact hx.2
      · intro y hy; simp only [rectB, ho, mem_filter, mem_univ, true_and] at hy; exact hy.2
  have hsum_rects :
      ∑ r : Fin P.size with goodRect r,
        ∑ x ∈ rectA r, ∑ y ∈ rectB r, (D.phi x y + D.psi x y) ≤ (P.size : ℝ) := by
    calc
      _ ≤ ∑ r : Fin P.size with goodRect r, (1 : ℝ) :=
          sum_le_sum fun r hr => hgood_le r (mem_filter.mp hr).2
      _ = (#{r : Fin P.size | goodRect r} : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (P.size : ℝ) := by
          exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin P.size)
  have hswap :
      ∑ r : Fin P.size with goodRect r,
        ∑ x ∈ rectA r, ∑ y ∈ rectB r, (D.phi x y + D.psi x y) =
      ∑ x : BitString N, ∑ y : BitString N,
        (#(univ.filter fun r : Fin P.size => goodRect r ∧ x ∈ rectA r ∧ y ∈ rectB r) : ℝ) *
          (D.phi x y + D.psi x y) := by
    have h1 : ∀ r : Fin P.size,
        (if goodRect r then ∑ x ∈ rectA r, ∑ y ∈ rectB r, (D.phi x y + D.psi x y) else 0) =
        ∑ x : BitString N, ∑ y : BitString N,
          if goodRect r ∧ x ∈ rectA r ∧ y ∈ rectB r then D.phi x y + D.psi x y else 0 := by
      intro r
      by_cases hr : goodRect r
      · simp only [hr, ↓reduceIte, true_and]
        calc
          ∑ x ∈ rectA r, ∑ y ∈ rectB r, (D.phi x y + D.psi x y)
            = ∑ x : BitString N, if x ∈ rectA r then
                ∑ y : BitString N, if y ∈ rectB r then D.phi x y + D.psi x y else 0 else 0 := by
              have hA : (univ.filter fun x => x ∈ rectA r) = rectA r := by ext x; simp
              have hB : (univ.filter fun y => y ∈ rectB r) = rectB r := by ext y; simp
              rw [← sum_filter, hA]
              refine sum_congr rfl fun x _ => ?_
              rw [← sum_filter, hB]
          _ = ∑ x : BitString N, ∑ y : BitString N,
                if x ∈ rectA r ∧ y ∈ rectB r then D.phi x y + D.psi x y else 0 := by
              refine sum_congr rfl fun x _ => ?_
              by_cases hx : x ∈ rectA r
              · simp only [hx, true_and, ↓reduceIte]
              · simp only [hx, false_and, ↓reduceIte, sum_const_zero]
      · simp [hr]
    rw [sum_filter, sum_congr rfl fun r _ => h1 r]
    rw [sum_comm, sum_congr rfl fun x _ => sum_comm]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul]
  rw [hswap] at hsum_rects
  refine le_trans ?_ hsum_rects
  refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
  set goodSet := univ.filter fun r : Fin P.size => goodRect r ∧ x ∈ rectA r ∧ y ∈ rectB r
  set cnt := goodSet.card
  have hcnt_le_t : cnt ≤ t := by
    have hsub : goodSet ⊆ univ.filter fun r : Fin P.size => x ∈ P.alice r ∧ y ∈ P.bob r := by
      intro r hr
      obtain ⟨hgr, hx, hy⟩ := (mem_filter.mp hr).2
      cases ho : P.output r with
      | none => simp [goodRect, ho] at hgr
      | some I =>
        simp only [rectA, rectB, ho, mem_filter, mem_univ, true_and] at hx hy
        exact mem_filter.mpr ⟨mem_univ _, hx.1, hy.1⟩
    have hle1 : cnt ≤ (univ.filter fun r : Fin P.size => x ∈ P.alice r ∧ y ∈ P.bob r).card :=
      card_le_card hsub
    have heq : (univ.filter fun r : Fin P.size => x ∈ P.alice r ∧ y ∈ P.bob r).card =
        P.ambiguityAt x y := by
      unfold NondetProtocol.ambiguityAt
      congr 1
    exact (hle1.trans_eq heq).trans (hamb x y)
  have hpsi_le : (t : ℝ) * D.psi x y ≤ (cnt : ℝ) * D.psi x y :=
    mul_le_mul_of_nonpos_right (by exact_mod_cast hcnt_le_t) (hDpsi x y)
  have hphi_le : (if P.Accepts (SearchChooseRel N k) x y then D.phi x y else 0) ≤
      (cnt : ℝ) * D.phi x y := by
    split_ifs with hacc
    · by_cases hcard : (interSet x y).card = k
      · obtain ⟨r, hx, hy, hR⟩ := hacc
        have ho := (searchChooseRel_eq_card_iff hcard).mp hR
        have hr_mem : r ∈ goodSet := by
          refine mem_filter.mpr ⟨mem_univ _, ?_, ?_, ?_⟩
          · simp [goodRect, ho, hcard]
          · simp only [rectA, ho, mem_filter, mem_univ, true_and]
            exact ⟨hx, by rw [interSet_eq_inter]; exact inter_subset_left⟩
          · simp only [rectB, ho, mem_filter, mem_univ, true_and]
            exact ⟨hy, by rw [interSet_eq_inter]; exact inter_subset_right⟩
        have hcnt_ge1 : (1 : ℝ) ≤ (cnt : ℝ) := by
          exact_mod_cast (Finset.card_pos.mpr ⟨r, hr_mem⟩)
        nlinarith [hDphi x y]
      · rw [hDsupp x y hcard, mul_zero]
    · exact mul_nonneg (Nat.cast_nonneg _) (hDphi x y)
  linarith

/-- Averaging `nondet_protocol_dual_bound` over any AM protocol `μ`. -/
theorem am_dual_bound {N k c t : ℕ}
    {μ : AMProtocol (BitString N) (BitString N) (Option (Finset (Fin N)))}
    (hcomm : μ.HasComm c) (hamb : μ.HasAmbiguity t) {σ : ℝ}
    (hsolves : μ.SolvesWithSuccess σ (SearchChooseRel N k))
    {D : DualSolution N} (hD : IsDualFeasible N k D) :
    D.obj σ (t : ℝ) ≤ (2 : ℝ) ^ c := by
  classical
  have hμ_sum : ∑' P, (μ P).toReal = 1 := by
    have h := μ.tsum_coe
    rw [← ENNReal.tsum_toReal_eq (fun P => μ.apply_ne_top P), h, ENNReal.toReal_one]
  have hsumm_μ : Summable fun P => (μ P).toReal :=
    ENNReal.summable_toReal (by rw [μ.tsum_coe]; exact ENNReal.one_ne_top)
  have hpt : ∀ P, (μ P).toReal *
      (∑ x : BitString N, ∑ y : BitString N,
        ((if P.Accepts (SearchChooseRel N k) x y then D.phi x y else 0) +
          (t : ℝ) * D.psi x y)) ≤ (μ P).toReal * (2 : ℝ) ^ c := by
    intro P
    by_cases hP : P ∈ μ.support
    · have hs : (P.size : ℝ) ≤ (2 : ℝ) ^ c := by exact_mod_cast hcomm P hP
      have hnd := nondet_protocol_dual_bound P (hamb P hP) hD
      simp only [Set.indicator_apply, Set.mem_ofPred_eq] at hnd
      exact mul_le_mul_of_nonneg_left (hnd.trans hs) ENNReal.toReal_nonneg
    · have h0 : μ P = 0 := by simpa [PMF.mem_support_iff] using hP
      simp [h0]
  have hsumm_term : ∀ x y : BitString N,
      Summable fun P => (μ P).toReal *
        ((if P.Accepts (SearchChooseRel N k) x y then D.phi x y else 0) +
          (t : ℝ) * D.psi x y) := by
    intro x y
    refine Summable.of_norm_bounded
      (g := fun P => (μ P).toReal * (|D.phi x y| + (t : ℝ) * |D.psi x y|))
      (hsumm_μ.mul_right _) fun P => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    calc
      |(if P.Accepts (SearchChooseRel N k) x y then D.phi x y else 0) + (t : ℝ) * D.psi x y|
        ≤ |if P.Accepts (SearchChooseRel N k) x y then D.phi x y else 0| + |(t : ℝ) * D.psi x y| :=
          abs_add_le _ _
      _ ≤ |D.phi x y| + (t : ℝ) * |D.psi x y| := by
          have ht_abs : |(t : ℝ)| = (t : ℝ) := abs_of_nonneg (Nat.cast_nonneg t)
          rw [abs_mul, ht_abs]
          split_ifs <;> simp [abs_nonneg]
  have htsum_le :
      ∑' P, (μ P).toReal *
        (∑ x : BitString N, ∑ y : BitString N,
          ((if P.Accepts (SearchChooseRel N k) x y then D.phi x y else 0) +
            (t : ℝ) * D.psi x y)) ≤ (2 : ℝ) ^ c := by
    have hsumm_lhs : Summable fun P => (μ P).toReal *
        (∑ x : BitString N, ∑ y : BitString N,
          ((if P.Accepts (SearchChooseRel N k) x y then D.phi x y else 0) +
            (t : ℝ) * D.psi x y)) := by
      simp_rw [mul_sum]
      exact summable_sum fun x _ => summable_sum fun y _ => hsumm_term x y
    calc
      _ ≤ ∑' P, (μ P).toReal * (2 : ℝ) ^ c :=
          hsumm_lhs.tsum_le_tsum hpt (hsumm_μ.mul_right _)
      _ = (∑' P, (μ P).toReal) * (2 : ℝ) ^ c := tsum_mul_right
      _ = (2 : ℝ) ^ c := by rw [hμ_sum, one_mul]
  have hswap :
      ∑' P, (μ P).toReal *
        (∑ x : BitString N, ∑ y : BitString N,
          ((if P.Accepts (SearchChooseRel N k) x y then D.phi x y else 0) +
            (t : ℝ) * D.psi x y)) =
      ∑ x : BitString N, ∑ y : BitString N,
        (μ.successProb (SearchChooseRel N k) x y * D.phi x y + (t : ℝ) * D.psi x y) := by
    simp_rw [mul_sum]
    rw [Summable.tsum_finsetSum fun x _ => summable_sum fun y _ => hsumm_term x y]
    refine sum_congr rfl fun x _ => ?_
    rw [Summable.tsum_finsetSum fun y _ => hsumm_term x y]
    refine sum_congr rfl fun y _ => ?_
    have hsumm1 : Summable fun P => (μ P).toReal *
        (if P.Accepts (SearchChooseRel N k) x y then D.phi x y else 0) := by
      refine Summable.of_norm_bounded (g := fun P => (μ P).toReal * |D.phi x y|)
        (hsumm_μ.mul_right _) fun P => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      split_ifs <;> simp [abs_nonneg]
    have hsumm2 : Summable fun P => (μ P).toReal * ((t : ℝ) * D.psi x y) := hsumm_μ.mul_right _
    simp_rw [mul_add]
    rw [hsumm1.tsum_add hsumm2, tsum_mul_right, hμ_sum, one_mul]
    congr 1
    have hpt1 : ∀ P, (μ P).toReal *
        (if P.Accepts (SearchChooseRel N k) x y then D.phi x y else 0) =
        (if P.Accepts (SearchChooseRel N k) x y then (μ P).toReal else 0) * D.phi x y := by
      intro P; split_ifs <;> ring
    simp_rw [hpt1, tsum_mul_right]
    congr 1
    rw [AMProtocol.successProb, PMF.toOuterMeasure_apply]
    have hne : ∀ P, ({Q : NondetProtocol (BitString N) (BitString N) (Option (Finset (Fin N))) |
        Q.Accepts (SearchChooseRel N k) x y}.indicator (⇑μ) P) ≠ ⊤ := fun P => by
      by_cases hP : P.Accepts (SearchChooseRel N k) x y <;> simp [hP, PMF.apply_ne_top]
    rw [ENNReal.tsum_toReal_eq hne]
    refine tsum_congr fun P => ?_
    by_cases hP : P.Accepts (SearchChooseRel N k) x y <;> simp [hP]
  rw [hswap] at htsum_le
  refine le_trans ?_ htsum_le
  rw [DualSolution.obj_eq_sum]
  refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
  have := mul_le_mul_of_nonneg_right (hsolves x y) (hD.1 x y)
  linarith

/-- **AM Main Lemma** (`SEARCH_{C(N,k)}` with ambiguity `t ≤ (9 / 8) ^ k`):
every AM protocol of communication `c ≤ betaMain * N` and ambiguity `t ≤ (9 / 8) ^ k` for
`SEARCH_{C(N,k)}` with `k ≤ gammaMain * N` has success probability `σ ≤ 2 ^ (-alphaMain * k)`. -/
theorem am_search_choose_bound {N k c t : ℕ} (hk : (k : ℝ) ≤ gammaMain * (N : ℝ))
    (hc : (c : ℝ) ≤ betaMain * (N : ℝ)) (ht : (t : ℝ) ≤ (9 / 8 : ℝ) ^ k)
    {μ : AMProtocol (BitString N) (BitString N) (Option (Finset (Fin N)))}
    (hcomm : μ.HasComm c) (hamb : μ.HasAmbiguity t) {σ : ℝ}
    (hsolves : μ.SolvesWithSuccess σ (SearchChooseRel N k)) :
    σ ≤ (2 : ℝ) ^ (-alphaMain * (k : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp only [Nat.cast_zero, mul_zero, Real.rpow_zero]
    exact AMProtocol.solvesWithSuccess_le_one hsolves
  have hkN : k ≤ N := by
    have : (k : ℝ) ≤ (N : ℝ) := by nlinarith [gammaMain_mem.2]
    exact_mod_cast this
  set n := N - k
  have hNk : n + k = N := Nat.sub_add_cancel hkN
  have hk_isl : (k : ℝ) ≤ gammaISL * (n : ℝ) / 2 := by
    have hN : (N : ℝ) = (n : ℝ) + (k : ℝ) := by exact_mod_cast hNk.symm
    have hγ1 : gammaISL ≤ 1 := gammaISL_le_one
    rw [gammaMain_eq_div] at hk
    nlinarith [gammaISL_pos]
  have hkn4 : k ≤ n / 4 := by
    have hγ4 : gammaISL / 2 ≤ 1 / 8 := gammaISL_div_two_le
    have h4 : (4 * k : ℝ) ≤ (n : ℝ) := by nlinarith
    have h4nat : 4 * k ≤ n := by exact_mod_cast h4
    omega
  clear_value n
  subst hNk
  have hdual := am_dual_bound hcomm hamb hsolves (searchChooseDual_feasible hk_isl)
  rw [searchChooseDual_obj hkn4 σ (t : ℝ)] at hdual
  have hsub : n + k - k = n := Nat.add_sub_cancel n k
  have hC : ((2 : ℝ) ^ c) ≤ (2 : ℝ) ^ (betaMain * ((n + k : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two hc
  exact success_le_of_dual_bound hkpos hk ht hC (by simpa [hsub] using hdual)

/-! ### Small-`n` leaf/rectangle counting bound for AM protocols -/

/-- Generic counting bound for AM protocols: if there are `2 ^ k` inputs `(x b, y₀)` whose
valid output sets are disjoint (distinguished by `decode : Z → BitString k`), then any AM protocol
of communication `c` (regardless of ambiguity!) has worst-case success probability at most
`2 ^ (c - k)`. -/
private theorem am_counting_bound {X Y Z : Type*} {k c : ℕ}
    {μ : AMProtocol X Y Z} (hcomm : μ.HasComm c) {R : X → Y → Z → Prop}
    (xOf : BitString k → X) (y₀ : Y) (decode : Z → BitString k)
    (hdec : ∀ b z, R (xOf b) y₀ z → decode z = b)
    {σ : ℝ} (hsolves : μ.SolvesWithSuccess σ R) :
    σ ≤ (2 : ℝ) ^ ((c : ℝ) - (k : ℝ)) := by
  classical
  have hμ_sum : ∑' P, (μ P).toReal = 1 := by
    have h := μ.tsum_coe
    rw [← ENNReal.tsum_toReal_eq (fun P => μ.apply_ne_top P), h, ENNReal.toReal_one]
  have hsumm_μ : Summable fun P => (μ P).toReal :=
    ENNReal.summable_toReal (by rw [μ.tsum_coe]; exact ENNReal.one_ne_top)
  have hpt_P : ∀ P ∈ μ.support,
      (#{b : BitString k | P.Accepts R (xOf b) y₀} : ℝ) ≤ (2 : ℝ) ^ c := by
    intro P hP
    have hsub : (univ.filter fun b : BitString k => P.Accepts R (xOf b) y₀) ⊆
        univ.image (fun r : Fin P.size => decode (P.output r)) := by
      intro b hb
      obtain ⟨r, _, _, hR⟩ := (mem_filter.mp hb).2
      exact mem_image.mpr ⟨r, mem_univ _, hdec b (P.output r) hR⟩
    have hcard : #{b : BitString k | P.Accepts R (xOf b) y₀} ≤ 2 ^ c :=
      (card_le_card hsub).trans ((card_image_le).trans
        (by rw [card_univ, Fintype.card_fin]; exact hcomm P hP))
    exact_mod_cast hcard
  have havg : (2 : ℝ) ^ k * σ ≤ ∑ b : BitString k, μ.successProb R (xOf b) y₀ := by
    calc
      (2 : ℝ) ^ k * σ
        = ∑ _b : BitString k, σ := by
          rw [sum_const, card_univ, BitString.card, nsmul_eq_mul]; push_cast; rfl
      _ ≤ ∑ b : BitString k, μ.successProb R (xOf b) y₀ :=
          sum_le_sum fun b _ => hsolves (xOf b) y₀
  have hsumm_b : ∀ b : BitString k,
      Summable fun P => (μ P).toReal * if P.Accepts R (xOf b) y₀ then (1 : ℝ) else 0 := by
    intro b
    refine Summable.of_norm_bounded (g := fun P => (μ P).toReal) hsumm_μ fun P => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    split_ifs <;> simp [ENNReal.toReal_nonneg]
  have hsum_eq : ∑ b : BitString k, μ.successProb R (xOf b) y₀ =
      ∑' P, (μ P).toReal * (#{b : BitString k | P.Accepts R (xOf b) y₀} : ℝ) := by
    have h1 : ∀ b : BitString k, μ.successProb R (xOf b) y₀ =
        ∑' P, (μ P).toReal * if P.Accepts R (xOf b) y₀ then (1 : ℝ) else 0 := by
      intro b
      rw [AMProtocol.successProb, PMF.toOuterMeasure_apply]
      have hne : ∀ P, ({Q : NondetProtocol X Y Z | Q.Accepts R (xOf b) y₀}.indicator (⇑μ) P) ≠ ⊤ :=
        fun P => by by_cases h : P.Accepts R (xOf b) y₀ <;> simp [h, PMF.apply_ne_top]
      rw [ENNReal.tsum_toReal_eq hne]
      exact tsum_congr fun P => by by_cases h : P.Accepts R (xOf b) y₀ <;> simp [h]
    simp_rw [h1]
    rw [← Summable.tsum_finsetSum fun b _ => hsumm_b b]
    refine tsum_congr fun P => ?_
    rw [← mul_sum, sum_boole]
  have hupper : ∑' P, (μ P).toReal * (#{b : BitString k | P.Accepts R (xOf b) y₀} : ℝ) ≤
      (2 : ℝ) ^ c := by
    have hsumm_lhs : Summable fun P => (μ P).toReal *
        (#{b : BitString k | P.Accepts R (xOf b) y₀} : ℝ) := by
      have : (fun P => (μ P).toReal * (#{b : BitString k | P.Accepts R (xOf b) y₀} : ℝ)) =
          fun P => ∑ b : BitString k, (μ P).toReal *
            if P.Accepts R (xOf b) y₀ then (1 : ℝ) else 0 :=
        funext fun P => by rw [← mul_sum, sum_boole]
      rw [this]
      exact summable_sum fun b _ => hsumm_b b
    calc
      _ ≤ ∑' P, (μ P).toReal * (2 : ℝ) ^ c := by
          refine hsumm_lhs.tsum_le_tsum (fun P => ?_) (hsumm_μ.mul_right _)
          by_cases hP : P ∈ μ.support
          · exact mul_le_mul_of_nonneg_left (hpt_P P hP) ENNReal.toReal_nonneg
          · have h0 : μ P = 0 := by simpa [PMF.mem_support_iff] using hP
            simp [h0]
      _ = (2 : ℝ) ^ c := by rw [tsum_mul_right, hμ_sum, one_mul]
  have hcomb : (2 : ℝ) ^ k * σ ≤ (2 : ℝ) ^ c := havg.trans (hsum_eq.symm ▸ hupper)
  have hdiv : σ ≤ (2 : ℝ) ^ c / (2 : ℝ) ^ k := (le_div_iff₀' (by positivity)).mpr hcomb
  rwa [← Real.rpow_natCast (2 : ℝ) c, ← Real.rpow_natCast (2 : ℝ) k,
    ← Real.rpow_sub two_pos] at hdiv

/-- Small-`n` bound for `SearchKRel n k`: for any `n ≥ 1`, any AM protocol of communication `c`
solving `SearchKRel n k` has success probability at most `2 ^ (c - k)`. -/
private theorem am_searchK_small_n_bound {n k c : ℕ} (hn : 1 ≤ n)
    {μ : AMProtocol (Fin k → BitString n) (Fin k → BitString n) (Fin k → Option (Fin n))}
    (hcomm : μ.HasComm c) {σ : ℝ} (hsolves : μ.SolvesWithSuccess σ (SearchKRel n k)) :
    σ ≤ (2 : ℝ) ^ ((c : ℝ) - (k : ℝ)) := by
  let i₀ : Fin n := ⟨0, hn⟩
  let xOf (b : BitString k) : Fin k → BitString n :=
    fun r j => if j = i₀ then b r else false
  let y₀ : Fin k → BitString n := fun _ j => if j = i₀ then true else false
  let decode (out : Fin k → Option (Fin n)) : BitString k := fun r => (out r).isSome
  refine am_counting_bound hcomm xOf y₀ decode (fun b out hout => ?_) hsolves
  funext r
  have hr := hout r
  cases ho : out r with
  | none =>
    rw [ho] at hr
    cases hb : b r
    · simp [decode, ho]
    · exfalso
      exact disjoint_left.mp hr (show i₀ ∈ supportSet (xOf b r) by simp [xOf, hb]) (by simp [y₀])
  | some j =>
    rw [ho] at hr
    obtain ⟨hxj, hyj⟩ := hr
    have hj : j = i₀ := by
      by_contra hne; simp [y₀, hne] at hyj
    subst hj
    simp [xOf] at hxj
    simp [decode, ho, hxj]

/-- Small-`n` bound for `ndisjK n k`: for any `n ≥ 1`, any AM protocol of communication `c`
computing `ndisjK n k` has success probability at most `2 ^ (c - k)`. -/
theorem am_ndisjK_small_n_bound {n k c : ℕ} (hn : 1 ≤ n)
    {μ : AMProtocol (Fin k → BitString n) (Fin k → BitString n) (BitString k)}
    (hcomm : μ.HasComm c) {σ : ℝ}
    (hsolves : μ.SolvesWithSuccess σ (fun x y o => ndisjK n k x y = o)) :
    σ ≤ (2 : ℝ) ^ ((c : ℝ) - (k : ℝ)) := by
  let i₀ : Fin n := ⟨0, hn⟩
  let xOf (b : BitString k) : Fin k → BitString n :=
    fun r j => if j = i₀ then b r else false
  let y₀ : Fin k → BitString n := fun _ j => if j = i₀ then true else false
  refine am_counting_bound hcomm xOf y₀ id (fun b out hout => ?_) hsolves
  rw [← hout]
  funext r
  simp only [ndisjK_apply, id]
  cases hb : b r
  · rw [ndisj_eq_false_iff_disjoint, disjoint_left]
    intro j hj
    simp only [mem_supportSet, xOf, hb, ite_self, Bool.false_eq_true] at hj
  · rw [ndisj_eq_true_iff_exists]
    exact ⟨i₀, by simp [xOf, hb], by simp [y₀]⟩

/-! ### Random permutation separation and SDPT for `SEARCH_n^(k)` -/

/-- Exact count of permutations `π ∈ S_{kn}` that map a `K`-element set `J ⊆ Fin (k * n)` into `K`
distinct blocks of size `n`. -/
private theorem card_perm_separates {k n K : ℕ} (hKk : K ≤ k) (hn : 1 ≤ n)
    (J : Finset (Fin (k * n))) (hJ : J.card = K) :
    #{π : Equiv.Perm (Fin (k * n)) |
        ∀ a ∈ J, ∀ b ∈ J, (finProdFinEquiv.symm (π a)).1 = (finProdFinEquiv.symm (π b)).1 →
          a = b} = n ^ K * k.descFactorial K * (k * n - K).factorial := by
  classical
  have hKkn : K ≤ k * n := hKk.trans (Nat.le_mul_of_pos_right k hn)
  -- Equivalence `eJ : Fin K ≃ J`.
  let eJ : Fin K ≃ {x : Fin (k * n) // x ∈ J} := (Fintype.equivFinOfCardEq (by simp [hJ])).symm
  -- Type of block-distinct embeddings `Fin K ↪ Fin (k * n)`.
  let GoodEmb := {f : Fin K ↪ Fin (k * n) //
    Function.Injective fun r : Fin K => (finProdFinEquiv.symm (f r)).1}
  have hcard_goodEmb : Fintype.card GoodEmb = n ^ K * k.descFactorial K := by
    let equivPair : GoodEmb ≃ (Fin K ↪ Fin k) × (Fin K → Fin n) := {
      toFun := fun ⟨f, hf⟩ =>
        (⟨fun r => (finProdFinEquiv.symm (f r)).1, hf⟩, fun r => (finProdFinEquiv.symm (f r)).2)
      invFun := fun ⟨b, o⟩ =>
        ⟨⟨fun r => finProdFinEquiv (b r, o r), fun r₁ r₂ heq => by
          have h := congrArg (fun z => (finProdFinEquiv.symm z).1) heq
          simp only [Equiv.symm_apply_apply] at h
          exact b.injective h⟩,
        fun r₁ r₂ h => by
          change (finProdFinEquiv.symm (finProdFinEquiv (b r₁, o r₁))).1 =
            (finProdFinEquiv.symm (finProdFinEquiv (b r₂, o r₂))).1 at h
          simp only [Equiv.symm_apply_apply] at h
          exact b.injective h⟩
      left_inv := fun ⟨f, _⟩ => by
        apply Subtype.ext; apply Function.Embedding.ext; intro r
        change finProdFinEquiv ((finProdFinEquiv.symm (f r)).1,
          (finProdFinEquiv.symm (f r)).2) = f r
        simp only [Prod.mk.eta, Equiv.apply_symm_apply]
      right_inv := fun ⟨b, o⟩ => by
        apply Prod.ext
        · apply Function.Embedding.ext; intro r
          change (finProdFinEquiv.symm (finProdFinEquiv (b r, o r))).1 = b r
          simp only [Equiv.symm_apply_apply]
        · funext r
          change (finProdFinEquiv.symm (finProdFinEquiv (b r, o r))).2 = o r
          simp only [Equiv.symm_apply_apply]
    }
    rw [Fintype.card_congr equivPair, Fintype.card_prod, Fintype.card_embedding_eq,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, mul_comm]
  -- Map each separating permutation `π` to its restriction `f ∈ GoodEmb`, and show every fiber has
  -- size `(k * n - K)!`.
  let restrictPerm (π : Equiv.Perm (Fin (k * n)))
      (hπ : ∀ a ∈ J, ∀ b ∈ J, (finProdFinEquiv.symm (π a)).1 = (finProdFinEquiv.symm (π b)).1 →
        a = b) : GoodEmb :=
    ⟨⟨fun r => π (eJ r).1, fun r₁ r₂ h => eJ.injective (Subtype.ext (π.injective h))⟩,
      fun r₁ r₂ h => eJ.injective (Subtype.ext (hπ _ (eJ r₁).2 _ (eJ r₂).2 h))⟩
  let S := univ.filter fun π : Equiv.Perm (Fin (k * n)) =>
    ∀ a ∈ J, ∀ b ∈ J, (finProdFinEquiv.symm (π a)).1 = (finProdFinEquiv.symm (π b)).1 → a = b
  have hfiber : ∀ f : GoodEmb,
      #{π ∈ S | ∃ hπ, restrictPerm π hπ = f} = (k * n - K).factorial := by
    intro f
    let imgF : Finset (Fin (k * n)) := univ.image f.1
    have himgF : imgF.card = K := by
      rw [card_image_of_injective _ f.1.injective, card_univ, Fintype.card_fin]
    have hcard_c1 : Fintype.card {x : Fin (k * n) // x ∉ J} = k * n - K := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hJ]
    have hcard_c2 : Fintype.card {y : Fin (k * n) // y ∉ imgF} = k * n - K := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, himgF]
    let eCompl : {x : Fin (k * n) // x ∉ J} ≃ {y : Fin (k * n) // y ∉ imgF} :=
      Fintype.equivOfCardEq (by rw [hcard_c1, hcard_c2])
    -- Bijection with `Equiv.Perm {x : Fin (k * n) // x ∉ J}`.
    have hbij : #{π ∈ S | ∃ hπ, restrictPerm π hπ = f} =
        Fintype.card (Equiv.Perm {x : Fin (k * n) // x ∉ J}) := by
      rw [← card_univ]
      refine Finset.card_bij
        (fun π hπ => by
          have hmem := mem_filter.mp hπ
          let hrestrict : ∀ x : Fin (k * n), x ∈ J ↔ π x ∈ imgF := by
            intro x
            obtain ⟨hπS, hf⟩ := hmem.2
            have hfeq : ∀ r : Fin K, π (eJ r).1 = f.1 r := fun r => by
              have := congrArg (fun g : GoodEmb => g.1 r) hf
              exact this
            constructor
            · intro hx
              refine mem_image.mpr ⟨eJ.symm ⟨x, hx⟩, mem_univ _, ?_⟩
              rw [← hfeq, Equiv.apply_symm_apply]
            · intro hpx
              obtain ⟨r, _, hr⟩ := mem_image.mp hpx
              rw [← hfeq r] at hr
              have := π.injective hr
              rw [← this]
              exact (eJ r).2
          exact
            { toFun := fun x => eCompl.symm ⟨π x.1, by
                intro hmem'; exact x.2 ((hrestrict x.1).mpr hmem')⟩
              invFun := fun x => ⟨π.symm (eCompl x).1, by
                intro hmem'
                have := (hrestrict (π.symm (eCompl x).1)).mp hmem'
                rw [Equiv.apply_symm_apply] at this
                exact (eCompl x).2 this⟩
              left_inv := fun x => Subtype.ext (by simp)
              right_inv := fun x => Subtype.ext (by simp) })
        (fun _ _ => mem_univ _)
        (fun π₁ hπ₁ π₂ hπ₂ heq => by
          obtain ⟨_, h₁, hf₁⟩ := mem_filter.mp hπ₁
          obtain ⟨_, h₂, hf₂⟩ := mem_filter.mp hπ₂
          apply Equiv.ext
          intro x
          by_cases hx : x ∈ J
          · have h1 := congrArg (fun g : GoodEmb => g.1 (eJ.symm ⟨x, hx⟩)) hf₁
            change π₁ (eJ (eJ.symm ⟨x, hx⟩)).1 = f.1 (eJ.symm ⟨x, hx⟩) at h1
            rw [Equiv.apply_symm_apply] at h1
            have h2 := congrArg (fun g : GoodEmb => g.1 (eJ.symm ⟨x, hx⟩)) hf₂
            change π₂ (eJ (eJ.symm ⟨x, hx⟩)).1 = f.1 (eJ.symm ⟨x, hx⟩) at h2
            rw [Equiv.apply_symm_apply] at h2
            exact h1.trans h2.symm
          · have h := congrArg (fun σ : Equiv.Perm {x : Fin (k * n) // x ∉ J} =>
              (eCompl (σ ⟨x, hx⟩)).1) heq
            simpa using h)
        (fun σ _ => by
          -- Build `π` from `f` on `J` and `eCompl ∘ σ` outside `J`.
          let toF : Fin (k * n) → Fin (k * n) := fun x =>
            if hx : x ∈ J then f.1 (eJ.symm ⟨x, hx⟩) else (eCompl (σ ⟨x, hx⟩)).1
          have hinj : Function.Injective toF := by
            intro x₁ x₂ heq
            dsimp only [toF] at heq
            split_ifs at heq with h₁ h₂ h₂
            · have := eJ.symm.injective (f.1.injective heq)
              exact congrArg Subtype.val this
            · exfalso
              exact (eCompl (σ ⟨x₂, h₂⟩)).2 (heq ▸ mem_image.mpr ⟨eJ.symm ⟨x₁, h₁⟩, mem_univ _,
                rfl⟩)
            · exfalso
              exact (eCompl (σ ⟨x₁, h₁⟩)).2 (heq.symm ▸ mem_image.mpr ⟨eJ.symm ⟨x₂, h₂⟩, mem_univ _,
                rfl⟩)
            · have h := σ.injective (eCompl.injective (Subtype.ext heq))
              exact congrArg Subtype.val h
          let π : Equiv.Perm (Fin (k * n)) :=
            Equiv.ofBijective toF (Finite.injective_iff_bijective.mp hinj)
          have hπ_apply : ∀ x, π x = toF x := fun _ => rfl
          have hπS : π ∈ S := by
            refine mem_filter.mpr ⟨mem_univ _, fun a ha b hb hblk => ?_⟩
            rw [hπ_apply, hπ_apply] at hblk
            simp only [toF, ha, hb, ↓reduceDIte] at hblk
            have := eJ.symm.injective (f.2 hblk)
            exact congrArg Subtype.val this
          have hf_eq : restrictPerm π (mem_filter.mp hπS).2 = f := by
            apply Subtype.ext; ext r
            simp [restrictPerm, hπ_apply, toF]
          refine ⟨π, mem_filter.mpr ⟨hπS, (mem_filter.mp hπS).2, hf_eq⟩, ?_⟩
          ext ⟨x, hx⟩
          simp [hπ_apply, toF, hx])
    rw [hbij, Fintype.card_perm, hcard_c1]
  have hsum : S.card = ∑ f : GoodEmb, #{π ∈ S | ∃ hπ, restrictPerm π hπ = f} := by
    rw [← card_biUnion]
    · congr 1
      ext π
      simp only [mem_biUnion, mem_univ, true_and, mem_filter]
      constructor
      · intro hπ; exact ⟨restrictPerm π (mem_filter.mp hπ).2, hπ, (mem_filter.mp hπ).2, rfl⟩
      · rintro ⟨_, hπ, _⟩; exact hπ
    · intro f₁ _ f₂ _ hne
      dsimp only [Function.onFun]
      rw [disjoint_left]
      intro π h₁ h₂
      obtain ⟨_, _, hf₁⟩ := mem_filter.mp h₁
      obtain ⟨_, _, hf₂⟩ := mem_filter.mp h₂
      exact hne (hf₁.symm.trans hf₂)
  rw [hsum, sum_congr rfl fun f _ => hfiber f, sum_const, card_univ, hcard_goodEmb, smul_eq_mul]

/-- Lower bound on the probability that a uniformly random permutation `π ∈ S_{kn}` separates a
`K`-element subset `J` into `K` distinct blocks: at least `(1 - K / k) ^ K` (and `1` if `K = 1`).
-/
private theorem prob_perm_separates_ge {k n K : ℕ} (hKk : K ≤ k) (hn : 1 ≤ n)
    (J : Finset (Fin (k * n))) (hJ : J.card = K) :
    (1 - ((K - 1 : ℕ) : ℝ) / (k : ℝ)) ^ K ≤
      (#{π : Equiv.Perm (Fin (k * n)) |
        ∀ a ∈ J, ∀ b ∈ J, (finProdFinEquiv.symm (π a)).1 = (finProdFinEquiv.symm (π b)).1 →
          a = b} : ℝ) / ((k * n).factorial : ℝ) := by
  rw [card_perm_separates hKk hn J hJ]
  rcases Nat.eq_zero_or_pos K with rfl | hKpos
  · have hne : ((k * n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp [div_self hne]
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (hKpos.trans_le hKk)
  have hKkn : K ≤ k * n := hKk.trans (Nat.le_mul_of_pos_right k hn)
  have hdesc_kn : (k * n).factorial = (k * n).descFactorial K * (k * n - K).factorial := by
    have h1 := Nat.choose_mul_factorial_mul_factorial hKkn
    have h2 := Nat.descFactorial_eq_factorial_mul_choose (k * n) K
    calc
      (k * n).factorial
        = (k * n).choose K * K.factorial * (k * n - K).factorial := h1.symm
      _ = K.factorial * (k * n).choose K * (k * n - K).factorial := by ring
      _ = (k * n).descFactorial K * (k * n - K).factorial := by rw [← h2]
  have hfac_pos : (0 : ℝ) < (k * n - K).factorial := by positivity
  rw [hdesc_kn, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
    mul_div_mul_right _ _ hfac_pos.ne']
  have hdesc_le : ((k * n).descFactorial K : ℝ) ≤ ((k * n : ℕ) : ℝ) ^ K := by
    exact_mod_cast Nat.descFactorial_le_pow (k * n) K
  have hdesc_k : ((k - (K - 1) : ℕ) : ℝ) ^ K ≤ (k.descFactorial K : ℝ) := by
    have hnat : (k - (K - 1)) ^ K ≤ k.descFactorial K := by
      have hgen : ∀ j, j ≤ K → (k - (K - 1)) ^ j ≤ k.descFactorial j := by
        intro j hj
        induction j with
        | zero => simp
        | succ j ih =>
          rw [pow_succ, Nat.descFactorial_succ, mul_comm (k - j)]
          exact Nat.mul_le_mul (ih (by omega)) (by omega)
      exact hgen K le_rfl
    exact_mod_cast hnat
  have hkn_pos : (0 : ℝ) < (k * n).descFactorial K :=
    Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr hKkn)
  calc
    (1 - ((K - 1 : ℕ) : ℝ) / (k : ℝ)) ^ K
      = (((k - (K - 1) : ℕ) : ℝ) / (k : ℝ)) ^ K := by
        congr 1
        rw [Nat.cast_sub (by omega : K - 1 ≤ k)]
        field_simp
    _ = ((n : ℝ) ^ K * ((k - (K - 1) : ℕ) : ℝ) ^ K) / (((k * n : ℕ) : ℝ) ^ K) := by
        rw [div_pow, Nat.cast_mul, mul_pow]
        have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp
    _ ≤ ((n : ℝ) ^ K * (k.descFactorial K : ℝ)) / ((k * n).descFactorial K : ℝ) := by
        have h1 : (n : ℝ) ^ K * ((k - (K - 1) : ℕ) : ℝ) ^ K ≤
            (n : ℝ) ^ K * (k.descFactorial K : ℝ) := by gcongr
        have hkn_pow_pos : (0 : ℝ) < ((k * n : ℕ) : ℝ) ^ K := by
          have : 0 < k * n := Nat.mul_pos (hKpos.trans_le hKk) hn
          positivity
        exact (div_le_div_iff₀ hkn_pow_pos hkn_pos).mpr
          (mul_le_mul h1 hdesc_le (by positivity) (by positivity))

/-- Collect the discovered intersection coordinates from a `SearchKRel` output under `π`. -/
private def permReduceFound {k n : ℕ} (π : Equiv.Perm (Fin (k * n)))
    (out : Fin k → Option (Fin n)) : Finset (Fin (k * n)) :=
  (univ : Finset (Fin k)).biUnion fun b =>
    match out b with
    | none => ∅
    | some j => {π.symm (finProdFinEquiv (b, j))}

/-- Decode a `SearchKRel` output into a `K`-subset `Option (Finset (Fin (k * n)))` under `π`. -/
private def permReduceDecode {k n : ℕ} (K : ℕ) (π : Equiv.Perm (Fin (k * n)))
    (out : Fin k → Option (Fin n)) : Option (Finset (Fin (k * n))) :=
  let found := permReduceFound π out
  if h : K ≤ found.card then
    some ((univ : Finset (Fin K)).image fun r => found.orderEmbOfFin rfl ⟨r.val, by omega⟩)
  else none

/-- Given a nondeterministic protocol `P` for `SEARCH_n^(k)` and a permutation `π ∈ S_{kn}`,
construct the induced nondeterministic protocol for `SEARCH_{C(kn, K)}`. -/
private def permReduceSearch {k n : ℕ} (K : ℕ) (π : Equiv.Perm (Fin (k * n)))
    (P : NondetProtocol (Fin k → BitString n) (Fin k → BitString n) (Fin k → Option (Fin n))) :
    NondetProtocol (BitString (k * n)) (BitString (k * n)) (Option (Finset (Fin (k * n)))) :=
  let blockify (x : BitString (k * n)) : Fin k → BitString n :=
    fun b j => x (π.symm (finProdFinEquiv (b, j)))
  (P.comap blockify blockify).map (permReduceDecode K π)

/-- `permReduceDecode K π out` satisfies `SearchChooseRel (k * n) K x y` whenever every discovered
element lies in `x ∩ y` and either `|x ∩ y| < K` or at least `K` elements were discovered. -/
private theorem permReduceDecode_spec {k n : ℕ} (K : ℕ) (π : Equiv.Perm (Fin (k * n)))
    {x y : BitString (k * n)} {out : Fin k → Option (Fin n)}
    (hsub : permReduceFound π out ⊆ interSet x y)
    (hcard : (interSet x y).card < K ∨ K ≤ (permReduceFound π out).card) :
    SearchChooseRel (k * n) K x y (permReduceDecode K π out) := by
  unfold permReduceDecode
  dsimp only
  split_ifs with hK
  · refine ⟨?_, ?_⟩
    · rw [card_image_of_injective]
      · simp
      · intro t₁ t₂ heq
        have h := ((permReduceFound π out).orderEmbOfFin rfl).injective heq
        exact Fin.ext (Fin.mk.inj h)
    · intro u hu
      obtain ⟨t, _, rfl⟩ := mem_image.mp hu
      exact hsub (orderEmbOfFin_mem (permReduceFound π out) rfl _)
  · exact hcard.resolve_right hK

/-- If `π` separates a `K`-element subset `J ⊆ x ∩ y` into `K` distinct blocks and `P` accepts a
valid `SearchKRel` answer on `(blockify x, blockify y)`, then `permReduceSearch K π P` accepts a
valid `SearchChooseRel` answer on `(x, y)`. -/
private theorem permReduceSearch_accepts {k n : ℕ} (K : ℕ) (π : Equiv.Perm (Fin (k * n)))
    {P : NondetProtocol (Fin k → BitString n) (Fin k → BitString n) (Fin k → Option (Fin n))}
    {x y : BitString (k * n)}
    (hacc : P.Accepts (SearchKRel n k)
      (fun b j => x (π.symm (finProdFinEquiv (b, j))))
      (fun b j => y (π.symm (finProdFinEquiv (b, j)))))
    (hgood : (interSet x y).card < K ∨ ∃ J : Finset (Fin (k * n)), J.card = K ∧ J ⊆ interSet x y ∧
      ∀ a ∈ J, ∀ b ∈ J, (finProdFinEquiv.symm (π a)).1 = (finProdFinEquiv.symm (π b)).1 →
        a = b) :
    (permReduceSearch K π P).Accepts (SearchChooseRel (k * n) K) x y := by
  obtain ⟨r, hx, hy, hR⟩ := hacc
  refine ⟨r, hx, hy, ?_⟩
  let out := P.output r
  let found := permReduceFound π out
  have hfound_sub : found ⊆ interSet x y := by
    intro u hu
    obtain ⟨b, _, hub⟩ := mem_biUnion.mp hu
    have hb := hR b
    cases ho : out b with
    | none => simp [ho] at hub
    | some j =>
      simp only [ho, mem_singleton] at hub
      subst hub
      dsimp only [out] at ho
      rw [ho] at hb
      exact mem_interSet.mpr hb
  dsimp only [permReduceSearch, NondetProtocol.map, NondetProtocol.comap]
  refine permReduceDecode_spec K π hfound_sub ?_
  rcases hgood with hlt | ⟨J, hJc, hJsub, hJsep⟩
  · exact Or.inl hlt
  · right
    have hnonempty_blk : ∀ a ∈ J, ∃ j, out (finProdFinEquiv.symm (π a)).1 = some j := by
      intro a ha
      set b := (finProdFinEquiv.symm (π a)).1
      set j₀ := (finProdFinEquiv.symm (π a)).2
      cases ho : out b with
      | some j => exact ⟨j, rfl⟩
      | none =>
        exfalso
        have hb := hR b
        dsimp only [out] at ho
        rw [ho] at hb
        have hmem := mem_interSet.mp (hJsub ha)
        have heq : π.symm (finProdFinEquiv (b, j₀)) = a := by
          rw [show (b, j₀) = finProdFinEquiv.symm (π a) from rfl,
            Equiv.apply_symm_apply, Equiv.symm_apply_apply]
        have hxj : j₀ ∈ supportSet ((fun b j => x (π.symm (finProdFinEquiv (b, j)))) b) :=
          mem_supportSet.mpr (by dsimp only; rw [heq]; exact hmem.1)
        have hyj : j₀ ∈ supportSet ((fun b j => y (π.symm (finProdFinEquiv (b, j)))) b) :=
          mem_supportSet.mpr (by dsimp only; rw [heq]; exact hmem.2)
        exact disjoint_left.mp hb hxj hyj
    rw [← hJc]
    refine Finset.card_le_card_of_injOn
      (fun a =>
        let b := (finProdFinEquiv.symm (π a)).1
        match out b with
        | none => a
        | some j => π.symm (finProdFinEquiv (b, j))) ?_ ?_
    · intro a ha
      obtain ⟨j, hj⟩ := hnonempty_blk a ha
      dsimp only
      rw [hj]
      exact mem_biUnion.mpr ⟨(finProdFinEquiv.symm (π a)).1, mem_univ _, by
        dsimp only [out] at hj
        rw [hj]
        exact mem_singleton_self _⟩
    · intro a₁ ha₁ a₂ ha₂ heq
      obtain ⟨j₁, hj₁⟩ := hnonempty_blk a₁ ha₁
      obtain ⟨j₂, hj₂⟩ := hnonempty_blk a₂ ha₂
      dsimp only at heq
      rw [hj₁, hj₂] at heq
      have hpair := finProdFinEquiv.injective (π.symm.injective heq)
      exact hJsep a₁ ha₁ a₂ ha₂ (Prod.mk.inj hpair).1

/-- Explicit success-decay constant for `SEARCH_n^(k)`. -/
@[expose] noncomputable def alphaSearch : ℝ := 1 / 2048

/-- Numeric value of `alphaSearch`. -/
theorem alphaSearch_val : alphaSearch = 1 / 2048 := rfl

/-- Explicit small-`n` threshold `N₀` for the Search SDPT. -/
@[expose] def n0Search : ℕ := 72 * 2 ^ 42

/-- Explicit communication-rate constant for `SEARCH_n^(k)`. -/
@[expose] noncomputable def betaSearch : ℝ := min betaMain (1 / (2 * (n0Search : ℝ)))

/-- Explicit lower bound `2 ^ (-51) ≤ betaSearch`. -/
theorem betaSearch_ge : (1 : ℝ) / (2 ^ 51 : ℝ) ≤ betaSearch := by
  unfold betaSearch n0Search
  rw [betaMain_eq_div, gammaISL_eq_div, deltaRaz_eq_zpow]
  apply le_min <;> norm_num

/-- Explicit ambiguity exponent for AM-Search. -/
@[expose] noncomputable def epsSearch : ℝ := 1 / 1024

/-- Numeric value of `epsSearch`. -/
theorem epsSearch_val : epsSearch = 1 / 1024 := rfl

/-- `alphaSearch ∈ (0, 1]`. -/
theorem alphaSearch_mem : 0 < alphaSearch ∧ alphaSearch ≤ 1 := by
  unfold alphaSearch; norm_num

/-- `betaSearch ∈ (0, 1]`. -/
theorem betaSearch_mem : 0 < betaSearch ∧ betaSearch ≤ 1 := by
  unfold betaSearch n0Search
  refine ⟨lt_min betaMain_mem.1 (by positivity), (min_le_left _ _).trans betaMain_mem.2⟩

/-- **AM SDPT for `SEARCH_n^(k)`**: every AM protocol of communication `c ≤ betaSearch * k * n`
and ambiguity `t ≤ 2 ^ (epsSearch * k)` solving `SearchKRel n k` (for `n ≥ 1`) has worst-case
success probability `σ ≤ 2 ^ (-alphaSearch * k)`. -/
theorem am_searchK_bound {n k c t : ℕ} (hn : 1 ≤ n)
    (hc : (c : ℝ) ≤ betaSearch * (k : ℝ) * (n : ℝ))
    (ht : (t : ℝ) ≤ (2 : ℝ) ^ (epsSearch * (k : ℝ)))
    {μ : AMProtocol (Fin k → BitString n) (Fin k → BitString n) (Fin k → Option (Fin n))}
    (hcomm : μ.HasComm c) (hamb : μ.HasAmbiguity t) {σ : ℝ}
    (hsolves : μ.SolvesWithSuccess σ (SearchKRel n k)) :
    σ ≤ (2 : ℝ) ^ (-alphaSearch * (k : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp only [Nat.cast_zero, mul_zero, Real.rpow_zero]
    exact AMProtocol.solvesWithSuccess_le_one hsolves
  by_cases hsmall : n ≤ n0Search
  · have hβ : betaSearch ≤ 1 / (2 * (n0Search : ℝ)) := min_le_right _ _
    have hc_half : (c : ℝ) ≤ (k : ℝ) / 2 := by
      have hnR : (n : ℝ) ≤ (n0Search : ℝ) := by exact_mod_cast hsmall
      have hn0pos : (0 : ℝ) < n0Search := by unfold n0Search; positivity
      calc (c : ℝ) ≤ betaSearch * (k : ℝ) * (n : ℝ) := hc
        _ ≤ (1 / (2 * (n0Search : ℝ))) * (k : ℝ) * (n0Search : ℝ) := by gcongr
        _ = (k : ℝ) / 2 := by field_simp
    have hcnt := am_searchK_small_n_bound hn hcomm hsolves
    refine hcnt.trans (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
    unfold alphaSearch
    linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  · push Not at hsmall
    have hβm : betaSearch ≤ betaMain := min_le_left _ _
    have hc_main : (c : ℝ) ≤ betaMain * ((k * n : ℕ) : ℝ) := by
      rw [Nat.cast_mul]; nlinarith [show (0 : ℝ) ≤ (k : ℝ) * (n : ℝ) by positivity]
    have hgamma_n : (1 : ℝ) ≤ gammaMain * (n : ℝ) := by
      rw [gammaMain_eq_div, gammaISL_eq_div, deltaRaz_eq_zpow]
      unfold n0Search at hsmall
      have hnR : ((72 * 2 ^ 42 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsmall.le
      push_cast at hnR
      have h1 : (2 : ℝ) ^ (-42 : ℤ) / 6 / 12 * (72 * (2 : ℝ) ^ (42 : ℕ)) = 1 := by norm_num
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (-42 : ℤ) / 6 / 12 := by norm_num
      nlinarith
    -- Pick `K := max 1 (k / 64)`.
    set K := max 1 (k / 64)
    have hKpos : 1 ≤ K := le_max_left _ _
    have hKk : K ≤ k := max_le hkpos (Nat.div_le_self k 64)
    have hK_le_gamma : (K : ℝ) ≤ gammaMain * ((k * n : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      have hKkR : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hKk
      nlinarith
    -- Check ambiguity `t ≤ (9 / 8) ^ K`.
    have htK : (t : ℝ) ≤ (9 / 8 : ℝ) ^ K := by
      by_cases hk64 : k < 64
      · have hlt2 : (2 : ℝ) ^ (epsSearch * (k : ℝ)) < 2 := by
          have hexp : epsSearch * (k : ℝ) < 1 := by
            unfold epsSearch
            have : (k : ℝ) < 64 := by exact_mod_cast hk64
            linarith
          calc (2 : ℝ) ^ (epsSearch * (k : ℝ))
              < (2 : ℝ) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt one_lt_two hexp
            _ = 2 := by norm_num
        have ht1 : t ≤ 1 := by
          have : (t : ℝ) < 2 := ht.trans_lt hlt2
          have : t < 2 := by exact_mod_cast this
          omega
        have ht1R : (t : ℝ) ≤ 1 := by exact_mod_cast ht1
        have h98 : (1 : ℝ) ≤ (9 / 8 : ℝ) ^ K := one_le_pow₀ (by norm_num)
        linarith
      · push Not at hk64
        have hk_le_128K : (k : ℝ) ≤ 128 * (K : ℝ) := by
          have h1 : k / 64 ≤ K := le_max_right _ _
          have h2 : k ≤ 128 * (k / 64) := by omega
          exact_mod_cast h2.trans (Nat.mul_le_mul_left 128 h1)
        have hbase : (2 : ℝ) ^ ((1 : ℝ) / 8) ≤ 9 / 8 := by
          have hpow : ((2 : ℝ) ^ ((1 : ℝ) / 8)) ^ (8 : ℕ) ≤ (9 / 8 : ℝ) ^ (8 : ℕ) := by
            rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul zero_le_two]
            norm_num
          by_contra hgt
          push Not at hgt
          have : (9 / 8 : ℝ) ^ (8 : ℕ) < ((2 : ℝ) ^ ((1 : ℝ) / 8)) ^ (8 : ℕ) :=
            pow_lt_pow_left₀ hgt (by norm_num) (by norm_num)
          linarith
        calc
          (t : ℝ) ≤ (2 : ℝ) ^ (epsSearch * (k : ℝ)) := ht
          _ ≤ (2 : ℝ) ^ ((1 / 8 : ℝ) * (K : ℝ)) := by
              apply Real.rpow_le_rpow_of_exponent_le one_le_two
              unfold epsSearch; linarith
          _ = ((2 : ℝ) ^ ((1 : ℝ) / 8)) ^ K := by
              rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul zero_le_two]
          _ ≤ (9 / 8 : ℝ) ^ K := pow_le_pow_left₀ (by positivity) hbase K
    -- Construct the induced AM protocol `μ'` for `SEARCH_{C(kn, K)}`.
    let μ' : AMProtocol (BitString (k * n)) (BitString (k * n)) (Option (Finset (Fin (k * n)))) :=
      (Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm (Fin (k * n)))).bind fun π =>
        μ.map (permReduceSearch K π)
    have hcomm' : μ'.HasComm c := by
      intro Q hQ
      rw [PMF.mem_support_bind_iff] at hQ
      obtain ⟨π, _, hQ⟩ := hQ
      rw [PMF.support_map] at hQ
      obtain ⟨P, hP, rfl⟩ := hQ
      exact hcomm P hP
    have hamb' : μ'.HasAmbiguity t := by
      intro Q hQ
      rw [PMF.mem_support_bind_iff] at hQ
      obtain ⟨π, _, hQ⟩ := hQ
      rw [PMF.support_map] at hQ
      obtain ⟨P, hP, rfl⟩ := hQ
      exact NondetProtocol.map_hasAmbiguity (NondetProtocol.comap_hasAmbiguity (hamb P hP))
    -- Lower-bound the success probability of `μ'` by `σ * (1 - (K - 1) / k) ^ K`.
    set pSep : ℝ := (1 - ((K - 1 : ℕ) : ℝ) / (k : ℝ)) ^ K
    have hpSep_le1 : pSep ≤ 1 := by
      refine pow_le_one₀ ?_ ?_
      · have : ((K - 1 : ℕ) : ℝ) / (k : ℝ) ≤ 1 := by
          rw [div_le_one (Nat.cast_pos.mpr hkpos)]
          exact_mod_cast (show K - 1 ≤ k by omega)
        linarith
      · linarith [show (0 : ℝ) ≤ ((K - 1 : ℕ) : ℝ) / (k : ℝ) by positivity]
    have hsolves' : μ'.SolvesWithSuccess (σ * pSep) (SearchChooseRel (k * n) K) := by
      intro x y
      classical
      rw [AMProtocol.successProb, PMF.toOuterMeasure_bind_apply]
      have htsum : (∑' π : Equiv.Perm (Fin (k * n)),
          Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm (Fin (k * n))) π *
            (μ.map (permReduceSearch K π)).toOuterMeasure
              {Q | Q.Accepts (SearchChooseRel (k * n) K) x y}).toReal =
          (∑ π : Equiv.Perm (Fin (k * n)),
            ((μ.map (permReduceSearch K π)).toOuterMeasure
              {Q | Q.Accepts (SearchChooseRel (k * n) K) x y}).toReal) /
            ((k * n).factorial : ℝ) := by
        rw [tsum_fintype, ENNReal.toReal_sum (fun π _ =>
          ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
            (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _))]
        simp only [ENNReal.toReal_mul, Cslib.Probability.PMF.uniformOfFintype_apply,
          Fintype.card_perm, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast,
          ← mul_sum, div_eq_inv_mul]
      rw [htsum]
      by_cases hlt : (interSet x y).card < K
      · have hge : ∀ π : Equiv.Perm (Fin (k * n)),
            σ ≤ ((μ.map (permReduceSearch K π)).toOuterMeasure
              {Q | Q.Accepts (SearchChooseRel (k * n) K) x y}).toReal := by
          intro π
          rw [PMF.toOuterMeasure_map_apply]
          refine (hsolves (fun b j => x (π.symm (finProdFinEquiv (b, j))))
            (fun b j => y (π.symm (finProdFinEquiv (b, j))))).trans ?_
          exact Cslib.Probability.PMF.toOuterMeasure_toReal_mono μ fun P hP =>
            permReduceSearch_accepts K π hP (.inl hlt)
        have hfac_pos : (0 : ℝ) < (k * n).factorial := by positivity
        have hsum_ge : ((k * n).factorial : ℝ) * σ ≤
            ∑ π : Equiv.Perm (Fin (k * n)),
              ((μ.map (permReduceSearch K π)).toOuterMeasure
                {Q | Q.Accepts (SearchChooseRel (k * n) K) x y}).toReal := by
          calc
            ((k * n).factorial : ℝ) * σ = ∑ _π : Equiv.Perm (Fin (k * n)), σ := by
              rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
            _ ≤ _ := sum_le_sum fun π _ => hge π
        have hσ_le : σ ≤ (∑ π : Equiv.Perm (Fin (k * n)),
            ((μ.map (permReduceSearch K π)).toOuterMeasure
              {Q | Q.Accepts (SearchChooseRel (k * n) K) x y}).toReal) / ((k * n).factorial : ℝ) :=
          (le_div_iff₀ hfac_pos).mpr (by linarith)
        by_cases hσ0 : 0 ≤ σ
        · exact (mul_le_of_le_one_right hσ0 hpSep_le1).trans hσ_le
        · have hpSep0 : 0 ≤ pSep := pow_nonneg (by
            have : ((K - 1 : ℕ) : ℝ) / (k : ℝ) ≤ 1 := by
              rw [div_le_one (Nat.cast_pos.mpr hkpos)]
              exact_mod_cast (show K - 1 ≤ k by omega)
            linarith) K
          have hnn : 0 ≤ (∑ π : Equiv.Perm (Fin (k * n)),
              ((μ.map (permReduceSearch K π)).toOuterMeasure
                {Q | Q.Accepts (SearchChooseRel (k * n) K) x y}).toReal) /
              ((k * n).factorial : ℝ) :=
            div_nonneg (sum_nonneg fun _ _ => ENNReal.toReal_nonneg) (by positivity)
          nlinarith
      · push Not at hlt
        obtain ⟨J, hJsub, hJc⟩ := exists_subset_card_eq hlt
        set GoodP := univ.filter fun π : Equiv.Perm (Fin (k * n)) =>
          ∀ a ∈ J, ∀ b ∈ J, (finProdFinEquiv.symm (π a)).1 = (finProdFinEquiv.symm (π b)).1 →
            a = b
        have hge : ∀ π ∈ GoodP,
            σ ≤ ((μ.map (permReduceSearch K π)).toOuterMeasure
              {Q | Q.Accepts (SearchChooseRel (k * n) K) x y}).toReal := by
          intro π hπ
          rw [PMF.toOuterMeasure_map_apply]
          refine (hsolves (fun b j => x (π.symm (finProdFinEquiv (b, j))))
            (fun b j => y (π.symm (finProdFinEquiv (b, j))))).trans ?_
          exact Cslib.Probability.PMF.toOuterMeasure_toReal_mono μ fun P hP =>
            permReduceSearch_accepts K π hP
              (.inr ⟨J, hJc, hJsub, (mem_filter.mp hπ).2⟩)
        by_cases hσ0 : 0 ≤ σ
        · have hprob := prob_perm_separates_ge hKk hn J hJc
          calc
            σ * pSep ≤ σ * ((GoodP.card : ℝ) / ((k * n).factorial : ℝ)) :=
              mul_le_mul_of_nonneg_left hprob hσ0
            _ = (∑ _π ∈ GoodP, σ) / ((k * n).factorial : ℝ) := by
              rw [sum_const, nsmul_eq_mul, mul_div_assoc', mul_comm σ]
            _ ≤ (∑ π ∈ GoodP, ((μ.map (permReduceSearch K π)).toOuterMeasure
                  {Q | Q.Accepts (SearchChooseRel (k * n) K) x y}).toReal) /
                ((k * n).factorial : ℝ) := by
              gcongr with π hπ; exact hge π hπ
            _ ≤ (∑ π : Equiv.Perm (Fin (k * n)),
                  ((μ.map (permReduceSearch K π)).toOuterMeasure
                    {Q | Q.Accepts (SearchChooseRel (k * n) K) x y}).toReal) /
                ((k * n).factorial : ℝ) := by
              gcongr
              exact subset_univ GoodP
        · have hpSep0 : 0 ≤ pSep := pow_nonneg (by
            have : ((K - 1 : ℕ) : ℝ) / (k : ℝ) ≤ 1 := by
              rw [div_le_one (Nat.cast_pos.mpr hkpos)]
              exact_mod_cast (show K - 1 ≤ k by omega)
            linarith) K
          have hnn : 0 ≤ (∑ π : Equiv.Perm (Fin (k * n)),
              ((μ.map (permReduceSearch K π)).toOuterMeasure
                {Q | Q.Accepts (SearchChooseRel (k * n) K) x y}).toReal) /
              ((k * n).factorial : ℝ) :=
            div_nonneg (sum_nonneg fun _ _ => ENNReal.toReal_nonneg) (by positivity)
          nlinarith
    have hbound := am_search_choose_bound hK_le_gamma hc_main htK hcomm' hamb' hsolves'
    -- Lower-bound `pSep ≥ 2 ^ (-(alphaMain / 2) * K)` and deduce `σ ≤ 2 ^ (-alphaSearch * k)`.
    have hpSep_ge : (2 : ℝ) ^ (-(alphaMain / 2) * (K : ℝ)) ≤ pSep := by
      have hK_ratio : ((K - 1 : ℕ) : ℝ) / (k : ℝ) ≤ 1 / 64 := by
        by_cases hk64 : k < 64
        · have hK1 : K = 1 := by omega
          simp [hK1]
        · push Not at hk64
          have h1 : K = k / 64 := max_eq_right (by omega)
          have h2 : (K - 1) * 64 ≤ 1 * k := by omega
          rw [div_le_div_iff₀ (Nat.cast_pos.mpr hkpos) (by norm_num)]
          exact_mod_cast h2
      have h63 : (2 : ℝ) ^ (-(alphaMain / 2)) ≤ 63 / 64 := by
        have hpow : ((2 : ℝ) ^ (-(alphaMain / 2))) ^ (16 : ℕ) ≤ (63 / 64 : ℝ) ^ (16 : ℕ) := by
          rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul zero_le_two, alphaMain_val]
          norm_num
        by_contra hgt
        push Not at hgt
        have : (63 / 64 : ℝ) ^ (16 : ℕ) < ((2 : ℝ) ^ (-(alphaMain / 2))) ^ (16 : ℕ) :=
          pow_lt_pow_left₀ hgt (by norm_num) (by norm_num)
        linarith
      calc
        (2 : ℝ) ^ (-(alphaMain / 2) * (K : ℝ))
          = ((2 : ℝ) ^ (-(alphaMain / 2))) ^ K := by
            rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul zero_le_two]
        _ ≤ (63 / 64 : ℝ) ^ K := pow_le_pow_left₀ (by positivity) h63 K
        _ ≤ pSep := pow_le_pow_left₀ (by norm_num) (by linarith) K
    have hσ_K : σ ≤ (2 : ℝ) ^ (-(alphaMain / 2) * (K : ℝ)) := by
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-(alphaMain / 2) * (K : ℝ)) := by positivity
      have hmul : σ * (2 : ℝ) ^ (-(alphaMain / 2) * (K : ℝ)) ≤
          (2 : ℝ) ^ (-alphaMain * (K : ℝ)) := by
        by_cases hσ0 : 0 ≤ σ
        · exact (mul_le_mul_of_nonneg_left hpSep_ge hσ0).trans hbound
        · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) h2pos.le).trans (by positivity)
      have hsplit : (2 : ℝ) ^ (-alphaMain * (K : ℝ)) =
          (2 : ℝ) ^ (-(alphaMain / 2) * (K : ℝ)) * (2 : ℝ) ^ (-(alphaMain / 2) * (K : ℝ)) := by
        rw [← Real.rpow_add two_pos]; congr 1; ring
      rw [hsplit] at hmul
      exact le_of_mul_le_mul_right hmul h2pos
    refine hσ_K.trans (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
    have hk_le_128K : (k : ℝ) ≤ 128 * (K : ℝ) := by
      by_cases hk64 : k < 64
      · have : (k : ℝ) ≤ 64 := by exact_mod_cast hk64.le
        have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKpos
        linarith
      · have h1 : k / 64 ≤ K := le_max_right _ _
        have h2 : k ≤ 128 * (k / 64) := by omega
        exact_mod_cast h2.trans (Nat.mul_le_mul_left 128 h1)
    rw [alphaMain_val]
    unfold alphaSearch
    linarith

/-- Strong direct product theorem for `SEARCH_n^(k)`:
There are constants `0 < α', β ≤ 1` such that for all `n ≥ 1` and `k`, every randomized
public-coin protocol with communication `c ≤ β k n` for `SEARCH_n^(k)` has worst-case success
probability at most `2 ^ (-α' k)`. -/
theorem sdpt_searchK :
    ∃ α' β : ℝ, (0 < α' ∧ α' ≤ 1) ∧ (0 < β ∧ β ≤ 1) ∧
      ∀ (n k c : ℕ), 1 ≤ n → (c : ℝ) ≤ β * (k : ℝ) * (n : ℝ) →
        ∀ (μ : PublicCoin (Fin k → BitString n) (Fin k → BitString n) (Fin k → Option (Fin n))),
          μ.depth ≤ c → ∀ σ : ℝ, SolvesWithSuccess μ σ (SearchKRel n k) →
            σ ≤ (2 : ℝ) ^ (-α' * (k : ℝ)) := by
  refine ⟨alphaSearch, betaSearch, alphaSearch_mem, betaSearch_mem,
    fun n k c hn hc μ hdepth σ hsolves => ?_⟩
  have h1 : ((1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (epsSearch * (k : ℝ)) := by
    simpa using Real.one_le_rpow one_le_two (by unfold epsSearch; positivity)
  exact am_searchK_bound hn hc h1 (publicCoinToAM_hasComm hdepth) (publicCoinToAM_hasAmbiguity μ)
    (fun x y => by rw [publicCoinToAM_successProb]; exact hsolves x y)


end CslibFrontier.Computability.Communication
