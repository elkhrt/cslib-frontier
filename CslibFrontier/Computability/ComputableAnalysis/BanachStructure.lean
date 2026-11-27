/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.ComputableAnalysis.ComputableReal
public import Mathlib.Analysis.Normed.Module.Basic

import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pour-El–Richards Axiomatic Computability Structures on Banach Spaces

Axiomatic computability structures on real normed and Banach spaces in the sense of Pour-El and
Richards (closure of computable sequences under effective finite linear combinations, effective
uniform limits in norm, and norm evaluation), together with effective generating sets, effective
separability, and the canonical computability structure induced by a dense generating sequence with
computable finite-combination norms, proved under standard Lean axioms.

## Main definitions

* `CslibFrontier.ComputableAnalysis.EffectivelyConvergesInNorm`: effective dyadic norm convergence
  `‖x - f n‖ < 2 ^ (-M)` for `n ≥ e M` in a normed space.
* `CslibFrontier.ComputableAnalysis.BanachComputabilityStructure`: a family `IsComputableSeq` of
  sequences in a real normed space satisfying the three Pour-El–Richards axioms (`linear_comb`,
  `effective_limit`, `norm_computable`).
* `CslibFrontier.ComputableAnalysis.BanachComputabilityStructure.IsComputable`: computable elements
  (elements whose constant sequence is computable).
* `CslibFrontier.ComputableAnalysis.BanachComputabilityStructure.IsEffectiveGeneratingSet`,
  `CslibFrontier.ComputableAnalysis.BanachComputabilityStructure.IsEffectivelySeparable`: effective
  generating sets and effective separability.
* `CslibFrontier.ComputableAnalysis.IsGenCombSeq`,
  `CslibFrontier.ComputableAnalysis.IsGenComputable`,
  `CslibFrontier.ComputableAnalysis.IsGenComputableSeq`,
  `CslibFrontier.ComputableAnalysis.BanachComputabilityStructure.ofGeneratingSeq`: computable finite
  linear combinations of a generating sequence `g : ℕ → B` and the canonical Pour-El–Richards
  computability structure they generate.

## Main results

* `CslibFrontier.ComputableAnalysis.BanachComputabilityStructure.isComputableReal_norm`,
  `CslibFrontier.ComputableAnalysis.BanachComputabilityStructure.effectivelyConvergesTo_norm`:
  computability of `‖x‖` for every computable element `x` and effective convergence of `‖f n‖` to
  `‖x‖` whenever a computable sequence `f` effectively converges to `x`.
* `CslibFrontier.ComputableAnalysis.BanachComputabilityStructure.isComputable_ofGeneratingSeq_iff`:
  equivalence between single-element effective approximation by computable finite combinations and
  constant-sequence computability in `ofGeneratingSeq`.
* `ComputableAnalysis.BanachComputabilityStructure.isEffectivelySeparable_ofGeneratingSeq`:
  a dense generating sequence `g` forms an effective generating set for `ofGeneratingSeq`, making
  the space effectively separable.
-/

public section

namespace CslibFrontier.ComputableAnalysis

universe u

/-- A sequence `f : ℕ → B` in a normed group effectively converges to `x : B` if there exists a
total computable modulus `e : ℕ → ℕ` such that `‖x - f n‖ < 2 ^ (-M)` whenever `n ≥ e M`. -/
@[expose]
def EffectivelyConvergesInNorm {B : Type u} [NormedAddCommGroup B] (f : ℕ → B) (x : B) : Prop :=
  ∃ e : ℕ → ℕ, Computable e ∧ ∀ M n : ℕ, e M ≤ n → ‖x - f n‖ < (2 : ℝ) ^ (-(M : ℤ))

/-- Effective norm convergence follows from a non-strict bound `‖x - f n‖ ≤ 2 ^ (-M)`. -/
theorem effectivelyConvergesInNorm_of_le {B : Type u} [NormedAddCommGroup B]
    {f : ℕ → B} {x : B} {e : ℕ → ℕ} (he : Computable e)
    (h : ∀ M n : ℕ, e M ≤ n → ‖x - f n‖ ≤ (2 : ℝ) ^ (-(M : ℤ))) :
    EffectivelyConvergesInNorm f x :=
  ⟨fun M ↦ e (M + 1), he.comp Computable.succ, fun M n hn ↦
    (h (M + 1) n hn).trans_lt (zpow_lt_zpow_right₀ one_lt_two (by omega))⟩

/-- Effective norm convergence implies topological convergence in norm. -/
theorem EffectivelyConvergesInNorm.tendsto {B : Type u} [NormedAddCommGroup B]
    {f : ℕ → B} {x : B} (h : EffectivelyConvergesInNorm f x) :
    Filter.Tendsto f Filter.atTop (nhds x) := by
  obtain ⟨e, he, hconv⟩ := h
  have hreal : EffectivelyConvergesTo (fun n ↦ ‖x - f n‖) 0 :=
    .mk he fun M n hn ↦ by simpa [abs_of_nonneg (norm_nonneg _)] using hconv M n hn
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hreal.tendsto.congr fun n ↦ norm_sub_rev x (f n)

/-- A Pour-El–Richards axiomatic computability structure on a real normed space `B`: a family
`computableSeqs : Set (ℕ → B)` of computable sequences in `B` closed under effective linear
combinations (Axiom 1), uniformly effective limits in norm (Axiom 2), and termwise norm evaluation
(Axiom 3). -/
@[ext]
structure BanachComputabilityStructure (B : Type u) [NormedAddCommGroup B]
    [NormedSpace ℝ B] : Type u where
  /-- The set of computable sequences in `B`. -/
  computableSeqs : Set (ℕ → B)
  /-- Axiom 1 (Linear forms): computable sequences are closed under finite linear combinations
  `h n = ∑ k ∈ range (d n + 1), (α n k • f k + β n k • g k)` with computable double real sequences
  `α, β` and computable upper index `d : ℕ → ℕ`. -/
  linear_comb : ∀ {f g : ℕ → B} {α β : ℕ → ℕ → ℝ} {d : ℕ → ℕ},
    f ∈ computableSeqs → g ∈ computableSeqs →
    IsComputableRealDoubleSeq α → IsComputableRealDoubleSeq β → Computable d →
    (fun n ↦ ∑ k ∈ Finset.range (d n + 1), (α n k • f k + β n k • g k)) ∈ computableSeqs
  /-- Axiom 2 (Limits): computable sequences are closed under limits in norm that are effective in
  both `k` and `n`. -/
  effective_limit : ∀ {f : ℕ → ℕ → B} {g : ℕ → B} {e : ℕ → ℕ → ℕ},
    Nat.unpaired f ∈ computableSeqs → Computable₂ e →
    (∀ n N k : ℕ, e n N ≤ k → ‖f n k - g n‖ ≤ (2 : ℝ) ^ (-(N : ℤ))) →
    g ∈ computableSeqs
  /-- Axiom 3 (Norms): the norms of a computable sequence form a computable sequence of reals. -/
  norm_computable : ∀ {f : ℕ → B},
    f ∈ computableSeqs → IsComputableRealSeq fun n ↦ ‖f n‖

namespace BanachComputabilityStructure

variable {B : Type u} [NormedAddCommGroup B] [NormedSpace ℝ B]
variable (S : BanachComputabilityStructure B)

/-- Predicate stating that `f : ℕ → B` is a computable sequence in `S`. -/
@[expose]
def IsComputableSeq (f : ℕ → B) : Prop :=
  f ∈ S.computableSeqs

/-- A double sequence `f : ℕ → ℕ → B` is computable in `S` if its Cantor unpairing
`Nat.unpaired f : ℕ → B` is a computable sequence in `S`. -/
def IsComputableDoubleSeq (f : ℕ → ℕ → B) : Prop :=
  S.IsComputableSeq (Nat.unpaired f)

/-- An element `x : B` is computable in `S` if the constant sequence `fun _ ↦ x` is computable. -/
@[expose] def IsComputable (x : B) : Prop :=
  S.IsComputableSeq fun _ ↦ x

/-- The set `B_c` of all `S`-computable elements of `B`. -/
def computableSet : Set B := { x : B | S.IsComputable x }

/-- Membership in `S.computableSet` is `S.IsComputable`. -/
@[simp] theorem mem_computableSet_iff {x : B} : x ∈ S.computableSet ↔ S.IsComputable x := Iff.rfl

/-- A sequence `g : ℕ → B` is an effective generating set of `(B, S)` if `g` is a computable
sequence in `S` whose real linear span is dense in `B`. -/
@[expose] def IsEffectiveGeneratingSet (g : ℕ → B) : Prop :=
  S.IsComputableSeq g ∧ (Submodule.span ℝ (Set.range g)).topologicalClosure = ⊤

/-- `(B, S)` is effectively separable if it admits an effective generating set. -/
@[expose] def IsEffectivelySeparable : Prop :=
  ∃ g : ℕ → B, S.IsEffectiveGeneratingSet g

/-- For every computable element `x` of `(B, S)`, its norm `‖x‖` is a computable real number. -/
theorem isComputableReal_norm {x : B} (hx : S.IsComputable x) : IsComputableReal ‖x‖ :=
  (S.norm_computable hx).apply 0

/-- If `f` is a computable sequence in `(B, S)` that effectively converges in norm to `x`, then
`fun n ↦ ‖f n‖` is a computable sequence of reals that effectively converges to `‖x‖`, and `‖x‖`
is a computable real number. -/
theorem effectivelyConvergesTo_norm {f : ℕ → B} {x : B} (hf : S.IsComputableSeq f)
    (hconv : EffectivelyConvergesInNorm f x) :
    IsComputableRealSeq (fun n ↦ ‖f n‖) ∧
      EffectivelyConvergesTo (fun n ↦ ‖f n‖) ‖x‖ ∧
      IsComputableReal ‖x‖ := by
  have hnf : IsComputableRealSeq fun n ↦ ‖f n‖ := S.norm_computable hf
  obtain ⟨e, he, hle⟩ := hconv
  have heff : EffectivelyConvergesTo (fun n ↦ ‖f n‖) ‖x‖ :=
    .mk he fun M n hn ↦ (abs_norm_sub_norm_le x (f n)).trans_lt (hle M n hn)
  exact ⟨hnf, heff, IsComputableReal.of_effectivelyConvergesTo hnf heff⟩

/-- Computable sequences in `S` are closed under precomposition with computable index maps. -/
theorem comp {f : ℕ → B} (hf : S.IsComputableSeq f) {r : ℕ → ℕ} (hr : Computable r) :
    S.IsComputableSeq fun n ↦ f (r n) := by
  let α : ℕ → ℕ → ℝ := fun n k ↦ if k = r n then 1 else 0
  let β : ℕ → ℕ → ℝ := fun _ _ ↦ 0
  have hα : IsComputableRealDoubleSeq α := by
    simpa [α] using isComputableRealDoubleSeq_indicator
      (Primrec.beq.to_comp.comp .snd (hr.comp .fst)).to₂
  have hβ : IsComputableRealDoubleSeq β := isComputableReal_zero.constDoubleSeq
  have hlc := S.linear_comb hf hf hα hβ hr
  have heq : (fun n ↦ ∑ k ∈ Finset.range (r n + 1), (α n k • f k + β n k • f k)) =
      fun n ↦ f (r n) := by
    ext n
    simp only [α, β, zero_smul, add_zero, ite_smul, one_smul, Finset.sum_ite_eq',
      Finset.mem_range.mpr (Nat.lt_succ_self _), ↓reduceIte]
  exact heq ▸ hlc

/-- Every entry of a computable sequence in `(B, S)` is a computable element of `(B, S)`. -/
theorem apply {f : ℕ → B} (hf : S.IsComputableSeq f) (n : ℕ) : S.IsComputable (f n) :=
  S.comp hf (.const n)

/-- If a computable sequence `f` in `(B, S)` effectively converges in norm to `x`, then `x` is
computable in `(B, S)`. -/
theorem isComputable_of_effectivelyConvergesInNorm {f : ℕ → B} {x : B}
    (hf : S.IsComputableSeq f) (hconv : EffectivelyConvergesInNorm f x) :
    S.IsComputable x := by
  obtain ⟨e, he, hle⟩ := hconv
  refine S.effective_limit (f := fun _ k ↦ f k)
    (S.comp hf (Computable.snd.comp .unpair))
    (he.comp .snd).to₂ fun _ N k hk ↦ ?_
  rw [norm_sub_rev]; exact (hle N k hk).le

/-- Computable elements of `(B, S)` are closed under addition. -/
theorem isComputable_add {x y : B} (hx : S.IsComputable x) (hy : S.IsComputable y) :
    S.IsComputable (x + y) := by
  have h1 : IsComputableRealDoubleSeq fun _ _ ↦ (1 : ℝ) := isComputableReal_one.constDoubleSeq
  simpa [IsComputable, IsComputableSeq] using S.linear_comb hx hy h1 h1 (.const 0)

/-- Computable elements of `(B, S)` are closed under real scalar multiplication by computable
reals. -/
theorem isComputable_smul {c : ℝ} {x : B} (hc : IsComputableReal c) (hx : S.IsComputable x) :
    S.IsComputable (c • x) := by
  have hα : IsComputableRealDoubleSeq fun _ _ ↦ c := hc.constDoubleSeq
  have hβ : IsComputableRealDoubleSeq fun _ _ ↦ (0 : ℝ) := isComputableReal_zero.constDoubleSeq
  simpa [IsComputable, IsComputableSeq] using S.linear_comb hx hx hα hβ (.const 0)

/-- Computable elements of `(B, S)` are closed under subtraction. -/
theorem isComputable_sub {x y : B} (hx : S.IsComputable x) (hy : S.IsComputable y) :
    S.IsComputable (x - y) := by
  simpa [sub_eq_add_neg] using
    S.isComputable_add hx (S.isComputable_smul isComputableReal_one.neg hy)

end BanachComputabilityStructure

/-! ### Canonical computability structure generated by a dense sequence -/

section GeneratedStructure

variable {B : Type u} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- A sequence `φ : ℕ → B` is a computable sequence of finite `g`-combinations if
`φ n = ∑ k ∈ range (d n + 1), c n k • g k` for a computable double real sequence `c` and a
computable degree bound `d : ℕ → ℕ`. -/
@[expose] def IsGenCombSeq (g : ℕ → B) (φ : ℕ → B) : Prop :=
  ∃ (c : ℕ → ℕ → ℝ) (d : ℕ → ℕ), IsComputableRealDoubleSeq c ∧ Computable d ∧
    ∀ n : ℕ, φ n = ∑ k ∈ Finset.range (d n + 1), c n k • g k

/-- An element `x : B` is `g`-computable if there exists a computable sequence of finite
`g`-combinations that effectively converges in norm to `x`. -/
@[expose] def IsGenComputable (g : ℕ → B) (x : B) : Prop :=
  ∃ φ : ℕ → B, IsGenCombSeq g φ ∧ EffectivelyConvergesInNorm φ x

/-- A sequence `f : ℕ → B` is `g`-computable if there exist a computable double sequence `φ` of
finite `g`-combinations and a computable modulus `e : ℕ → ℕ → ℕ` such that
`‖φ n k - f n‖ ≤ 2 ^ (-N)` whenever `k ≥ e n N`. -/
@[expose] def IsGenComputableSeq (g : ℕ → B) (f : ℕ → B) : Prop :=
  ∃ (φ : ℕ → ℕ → B) (e : ℕ → ℕ → ℕ),
    IsGenCombSeq g (Nat.unpaired φ) ∧ Computable₂ e ∧
    ∀ n N k : ℕ, e n N ≤ k → ‖φ n k - f n‖ ≤ (2 : ℝ) ^ (-(N : ℤ))

/-- Every computable sequence of finite `g`-combinations is `g`-computable. -/
theorem IsGenCombSeq.isGenComputableSeq {g φ : ℕ → B} (hφ : IsGenCombSeq g φ) :
    IsGenComputableSeq g φ := by
  obtain ⟨c, d, hc, hd, hfeq⟩ := hφ
  refine ⟨fun n _ ↦ φ n, fun _ _ ↦ 0,
    ⟨fun i k ↦ c i.unpair.1 k, fun i ↦ d i.unpair.1,
      hc.comp (Primrec₂.natPair.to_comp.comp
        (Computable.fst.comp (Computable.unpair.comp (Computable.fst.comp .unpair)))
        (Computable.snd.comp .unpair)) |>.of_eq (fun m ↦ by simp [Nat.unpaired, Nat.unpair_pair]),
      hd.comp (Computable.fst.comp .unpair),
      fun i ↦ hfeq i.unpair.1⟩,
    .const 0, fun _ N _ _ ↦ by rw [sub_self, norm_zero]; exact (zpow_pos two_pos _).le⟩

/-- Pointwise equality preserves `IsGenCombSeq`. -/
theorem IsGenCombSeq.of_eq {g φ ψ : ℕ → B} (hφ : IsGenCombSeq g φ) (h : ∀ n, φ n = ψ n) :
    IsGenCombSeq g ψ :=
  funext h ▸ hφ

/-- Pointwise equality preserves `IsGenComputableSeq`. -/
theorem IsGenComputableSeq.of_eq {g φ ψ : ℕ → B} (hφ : IsGenComputableSeq g φ)
    (h : ∀ n, φ n = ψ n) : IsGenComputableSeq g ψ :=
  funext h ▸ hφ

/-- `IsGenCombSeq g` is closed under precomposition with computable index maps. -/
theorem IsGenCombSeq.comp {g φ : ℕ → B} (hφ : IsGenCombSeq g φ) {r : ℕ → ℕ} (hr : Computable r) :
    IsGenCombSeq g fun n ↦ φ (r n) := by
  obtain ⟨c, d, hc, hd, hfeq⟩ := hφ
  refine ⟨fun n k ↦ c (r n) k, fun n ↦ d (r n), ?_, hd.comp hr, fun n ↦ hfeq (r n)⟩
  exact (hc.comp (Primrec₂.natPair.to_comp.comp
    (hr.comp (Computable.fst.comp .unpair)) (Computable.snd.comp .unpair))).of_eq
    fun m ↦ by simp [Nat.unpaired, Nat.unpair_pair]

/-- The generating sequence `g` itself is a computable sequence of finite `g`-combinations. -/
theorem isGenCombSeq_self (g : ℕ → B) : IsGenCombSeq g g := by
  let c : ℕ → ℕ → ℝ := fun n k ↦ if k = n then 1 else 0
  have hc : IsComputableRealDoubleSeq c := by
    simpa [c] using isComputableRealDoubleSeq_indicator
      (Primrec.beq.to_comp.comp .snd .fst).to₂
  refine ⟨c, id, hc, .id, fun n ↦ ?_⟩
  simp only [c, id_eq, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_range.mpr (Nat.lt_succ_self n), ↓reduceIte]

/-- Equivalence between `IsGenComputable g x` and constant-sequence `IsGenComputableSeq g`. -/
theorem isGenComputableSeq_const_iff {g : ℕ → B} {x : B} :
    IsGenComputableSeq g (fun _ ↦ x) ↔ IsGenComputable g x := by
  constructor
  · rintro ⟨φ, e, hφ, he, hconv⟩
    have hrow : IsGenCombSeq g (φ 0) :=
      (hφ.comp (Primrec₂.natPair.to_comp.comp (.const 0) .id)).of_eq fun k ↦ by
        simp [Nat.unpaired, Nat.unpair_pair]
    refine ⟨φ 0, hrow, effectivelyConvergesInNorm_of_le (he.comp (.const 0) .id) fun M k hk ↦ ?_⟩
    rw [norm_sub_rev]; exact hconv 0 M k hk
  · rintro ⟨φ, hφ, e, he, hconv⟩
    refine ⟨fun _ k ↦ φ k, fun _ N ↦ e N, hφ.comp (Computable.snd.comp .unpair),
      (he.comp .snd).to₂, fun _ N k hk ↦ ?_⟩
    rw [norm_sub_rev]; exact (hconv N k hk).le

private lemma isGenComputableSeq_iff_rapid {g : ℕ → B} {f : ℕ → B} :
    IsGenComputableSeq g f ↔
      ∃ ψ : ℕ → ℕ → B, IsGenCombSeq g (Nat.unpaired ψ) ∧
        ∀ n N : ℕ, ‖ψ n N - f n‖ ≤ (2 : ℝ) ^ (-(N : ℤ)) := by
  constructor
  · rintro ⟨φ, e, hφ, he, hconv⟩
    refine ⟨fun n N ↦ φ n (e n N), ?_, fun n N ↦ hconv n N (e n N) le_rfl⟩
    have hidx : Computable fun i : ℕ ↦ Nat.pair i.unpair.1 (e i.unpair.1 i.unpair.2) :=
      Primrec₂.natPair.to_comp.comp (Computable.fst.comp .unpair)
        (he.comp (Computable.fst.comp .unpair) (Computable.snd.comp .unpair))
    exact (hφ.comp hidx).of_eq fun i ↦ by simp [Nat.unpaired, Nat.unpair_pair]
  · rintro ⟨ψ, hψ, hconv⟩
    refine ⟨ψ, fun _ N ↦ N, hψ, Computable.snd.to₂, fun n N k hk ↦ ?_⟩
    dsimp only at hk
    exact (hconv n k).trans (zpow_le_zpow_right₀ one_le_two (by omega))

private lemma computable_nat_sup_range {α : Type*} [Primcodable α] {b : α → ℕ} {f : α → ℕ → ℕ}
    (hb : Computable b) (hf : Computable₂ f) :
    Computable fun a ↦ (Finset.range (b a + 1)).sup (f a) :=
  (Computable.nat_rec hb (hf.comp .id (.const 0))
    (Primrec.nat_max.to_comp.comp (Computable.snd.comp .snd)
      (hf.comp .fst (Computable.succ.comp (Computable.fst.comp .snd)))).to₂).of_eq fun a ↦ by
    induction b a with
    | zero => simp
    | succ k ih =>
      dsimp only at ih ⊢; rw [ih]
      rw [show Finset.range (k + 1 + 1) = insert (k + 1) (Finset.range (k + 1)) from
        Finset.range_add_one, Finset.sup_insert, sup_comm]

private lemma isGenCombSeq_linear_comb {g φ ψ : ℕ → B} {α β : ℕ → ℕ → ℝ} {d : ℕ → ℕ}
    (hφ : IsGenCombSeq g φ) (hψ : IsGenCombSeq g ψ)
    (hα : IsComputableRealDoubleSeq α) (hβ : IsComputableRealDoubleSeq β) (hd : Computable d) :
    IsGenCombSeq g fun n ↦ ∑ j ∈ Finset.range (d n + 1), (α n j • φ j + β n j • ψ j) := by
  obtain ⟨cφ, dφ, hcφ, hdφ, hφeq⟩ := hφ
  obtain ⟨cψ, dψ, hcψ, hdψ, hψeq⟩ := hψ
  let D : ℕ → ℕ := fun n ↦ (Finset.range (d n + 1)).sup fun j ↦ max (dφ j) (dψ j)
  have hD : Computable D :=
    computable_nat_sup_range hd
      (Primrec.nat_max.to_comp.comp (hdφ.comp .snd) (hdψ.comp .snd)).to₂
  let cφ' : ℕ → ℕ → ℝ := fun j k ↦ if k ≤ dφ j then cφ j k else 0
  let cψ' : ℕ → ℕ → ℝ := fun j k ↦ if k ≤ dψ j then cψ j k else 0
  have hmask : ∀ {c : ℕ → ℕ → ℝ} {b : ℕ → ℕ}, IsComputableRealDoubleSeq c → Computable b →
      IsComputableRealDoubleSeq fun j k ↦ if k ≤ b j then c j k else 0 := by
    intro c b hc hb
    have hind : IsComputableRealDoubleSeq fun j k ↦ if k ≤ b j then (1 : ℝ) else 0 := by
      simpa using isComputableRealDoubleSeq_indicator
        (Primrec.nat_le.decide.to₂.to_comp.comp .snd (hb.comp .fst)).to₂
    exact (hind.mul hc).of_eq fun i ↦ by
      dsimp [Nat.unpaired]; split_ifs <;> ring
  have hcφ' : IsComputableRealDoubleSeq cφ' := hmask hcφ hdφ
  have hcψ' : IsComputableRealDoubleSeq cψ' := hmask hcψ hdψ
  let term : ℕ → ℕ → ℝ := fun p j ↦
    let n := p.unpair.1
    let m := p.unpair.2
    α n j * cφ' j m + β n j * cψ' j m
  have hterm : IsComputableRealDoubleSeq term := by
    have hn : Computable fun i : ℕ ↦ i.unpair.1.unpair.1 :=
      Computable.fst.comp (Computable.unpair.comp (Computable.fst.comp .unpair))
    have hm : Computable fun i : ℕ ↦ i.unpair.1.unpair.2 :=
      Computable.snd.comp (Computable.unpair.comp (Computable.fst.comp .unpair))
    have hj : Computable fun i : ℕ ↦ i.unpair.2 := Computable.snd.comp .unpair
    have h1 : IsComputableRealSeq fun i ↦ α i.unpair.1.unpair.1 i.unpair.2 :=
      (hα.comp (Primrec₂.natPair.to_comp.comp hn hj)).of_eq fun i ↦ by
        simp [Nat.unpaired, Nat.unpair_pair]
    have h2 : IsComputableRealSeq fun i ↦ cφ' i.unpair.2 i.unpair.1.unpair.2 :=
      (hcφ'.comp (Primrec₂.natPair.to_comp.comp hj hm)).of_eq fun i ↦ by
        simp [Nat.unpaired, Nat.unpair_pair]
    have h3 : IsComputableRealSeq fun i ↦ β i.unpair.1.unpair.1 i.unpair.2 :=
      (hβ.comp (Primrec₂.natPair.to_comp.comp hn hj)).of_eq fun i ↦ by
        simp [Nat.unpaired, Nat.unpair_pair]
    have h4 : IsComputableRealSeq fun i ↦ cψ' i.unpair.2 i.unpair.1.unpair.2 :=
      (hcψ'.comp (Primrec₂.natPair.to_comp.comp hj hm)).of_eq fun i ↦ by
        simp [Nat.unpaired, Nat.unpair_pair]
    exact (h1.mul h2).add (h3.mul h4)
  have hC : IsComputableRealDoubleSeq fun n m ↦
      ∑ j ∈ Finset.range (d n + 1), (α n j * cφ' j m + β n j * cψ' j m) := by
    have hs := hterm.sum_range
      (Computable.succ.comp (hd.comp (Computable.fst.comp .unpair)))
    exact hs.of_eq fun p ↦ rfl
  refine ⟨fun n m ↦ ∑ j ∈ Finset.range (d n + 1), (α n j * cφ' j m + β n j * cψ' j m),
    D, hC, hD, fun n ↦ ?_⟩
  have hextφ : ∀ j ∈ Finset.range (d n + 1),
      φ j = ∑ m ∈ Finset.range (D n + 1), cφ' j m • g m := fun j hj ↦ by
    have hle : dφ j ≤ D n :=
      (le_max_left _ _).trans (Finset.le_sup (f := fun j ↦ max (dφ j) (dψ j)) hj)
    rw [hφeq j, ← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hle))]
    · exact Finset.sum_congr rfl fun m hm ↦ by
        simp [cφ', Nat.le_of_lt_succ (Finset.mem_range.mp hm)]
    · intro m _ hnot
      have : ¬ m ≤ dφ j := fun h ↦ hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
      simp [cφ', this]
  have hextψ : ∀ j ∈ Finset.range (d n + 1),
      ψ j = ∑ m ∈ Finset.range (D n + 1), cψ' j m • g m := fun j hj ↦ by
    have hle : dψ j ≤ D n :=
      (le_max_right _ _).trans (Finset.le_sup (f := fun j ↦ max (dφ j) (dψ j)) hj)
    rw [hψeq j, ← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hle))]
    · exact Finset.sum_congr rfl fun m hm ↦ by
        simp [cψ', Nat.le_of_lt_succ (Finset.mem_range.mp hm)]
    · intro m _ hnot
      have : ¬ m ≤ dψ j := fun h ↦ hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
      simp [cψ', this]
  calc ∑ j ∈ Finset.range (d n + 1), (α n j • φ j + β n j • ψ j)
      = ∑ j ∈ Finset.range (d n + 1), ∑ m ∈ Finset.range (D n + 1),
          (α n j * cφ' j m + β n j * cψ' j m) • g m := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [hextφ j hj, hextψ j hj, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun m _ ↦ by rw [add_smul, mul_smul, mul_smul]
    _ = ∑ m ∈ Finset.range (D n + 1),
          (∑ j ∈ Finset.range (d n + 1), (α n j * cφ' j m + β n j * cψ' j m)) • g m := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ ↦ (Finset.sum_smul ..).symm

/-- Canonical Pour-El–Richards computability structure on `B` generated by a sequence `g : ℕ → B`
whose computable finite linear combinations have computable norm sequences. -/
def BanachComputabilityStructure.ofGeneratingSeq (g : ℕ → B)
    (hnorm : ∀ {φ : ℕ → B}, IsGenCombSeq g φ → IsComputableRealSeq fun n ↦ ‖φ n‖) :
    BanachComputabilityStructure B where
  computableSeqs := { f | IsGenComputableSeq g f }
  linear_comb := by
    intro f₁ f₂ α β d hf₁ hf₂ hα hβ hd
    obtain ⟨ψ₁, hψ₁, hc₁⟩ := isGenComputableSeq_iff_rapid.mp hf₁
    obtain ⟨ψ₂, hψ₂, hc₂⟩ := isGenComputableSeq_iff_rapid.mp hf₂
    obtain ⟨qα, hqα, hcα⟩ := isComputableRealDoubleSeq_iff_exists_rat_approx.mp hα
    obtain ⟨qβ, hqβ, hcβ⟩ := isComputableRealDoubleSeq_iff_exists_rat_approx.mp hβ
    let Bcoeff : ℕ → ℕ := fun n ↦
      (Finset.range (d n + 1)).sup fun j ↦ (qα (n, j) 0).num.natAbs + (qβ (n, j) 0).num.natAbs + 2
    have hBcoeff : Computable Bcoeff :=
      computable_nat_sup_range hd
        (Primrec.nat_add.to_comp.comp
          (Primrec.nat_add.to_comp.comp
            (primrec_int_natAbs.to_comp.comp (hqα.comp .id (.const 0)).num)
            (primrec_int_natAbs.to_comp.comp (hqβ.comp .id (.const 0)).num))
          (.const 2)).to₂
    let K : ℕ → ℕ → ℕ := fun n N ↦ N + d n + Bcoeff n + 2
    have hK : Computable fun p : ℕ × ℕ ↦ K p.1 p.2 :=
      Primrec.nat_add.to_comp.comp
        (Primrec.nat_add.to_comp.comp
          (Primrec.nat_add.to_comp.comp .snd (hd.comp .fst))
          (hBcoeff.comp .fst))
        (.const 2)
    let α' : ℕ → ℕ → ℝ := fun i p ↦
      if p.unpair.2 = K i.unpair.1 i.unpair.2 ∧ p.unpair.1 ≤ d i.unpair.1 then
        α i.unpair.1 p.unpair.1
      else 0
    let β' : ℕ → ℕ → ℝ := fun i p ↦
      if p.unpair.2 = K i.unpair.1 i.unpair.2 ∧ p.unpair.1 ≤ d i.unpair.1 then
        β i.unpair.1 p.unpair.1
      else 0
    let Dpair : ℕ → ℕ := fun i ↦ Nat.pair (d i.unpair.1) (K i.unpair.1 i.unpair.2)
    have hDpair : Computable Dpair :=
      Primrec₂.natPair.to_comp.comp (hd.comp (Computable.fst.comp .unpair)) (hK.comp .unpair)
    have hcond : Computable₂ fun i p : ℕ ↦
        decide (p.unpair.2 = K i.unpair.1 i.unpair.2) &&
          decide (p.unpair.1 ≤ d i.unpair.1) := by
      have hi : Computable fun q : ℕ × ℕ ↦ q.1.unpair := Computable.unpair.comp .fst
      have hp : Computable fun q : ℕ × ℕ ↦ q.2.unpair := Computable.unpair.comp .snd
      exact (Primrec.and.to_comp.comp
        (Primrec.beq.to_comp.comp (Computable.snd.comp hp) (hK.comp hi))
        (Primrec.nat_le.decide.to₂.to_comp.comp (Computable.fst.comp hp)
          (hd.comp (Computable.fst.comp hi)))).to₂
    have hind : IsComputableRealDoubleSeq fun i p ↦
        if p.unpair.2 = K i.unpair.1 i.unpair.2 ∧
          p.unpair.1 ≤ d i.unpair.1 then (1 : ℝ) else 0 := by
      refine (isComputableRealDoubleSeq_indicator hcond).of_eq fun m ↦ ?_
      dsimp only [Nat.unpaired]
      by_cases h1 : m.unpair.2.unpair.2 = K m.unpair.1.unpair.1 m.unpair.1.unpair.2 <;>
        by_cases h2 : m.unpair.2.unpair.1 ≤ d m.unpair.1.unpair.1 <;> simp [h1, h2]
    have hlift : ∀ {γ : ℕ → ℕ → ℝ}, IsComputableRealDoubleSeq γ →
        IsComputableRealDoubleSeq fun i p ↦ γ i.unpair.1 p.unpair.1 := fun hγ ↦
      (hγ.comp (Primrec₂.natPair.to_comp.comp
        (Computable.fst.comp (Computable.unpair.comp (Computable.fst.comp .unpair)))
        (Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp .unpair))))).of_eq
        fun m ↦ by simp [Nat.unpaired, Nat.unpair_pair]
    have hα' : IsComputableRealDoubleSeq α' :=
      (hind.mul (hlift hα)).of_eq fun m ↦ by dsimp [Nat.unpaired, α']; split_ifs <;> ring
    have hβ' : IsComputableRealDoubleSeq β' :=
      (hind.mul (hlift hβ)).of_eq fun m ↦ by dsimp [Nat.unpaired, β']; split_ifs <;> ring
    let Φ : ℕ → ℕ → B := fun n N ↦
      ∑ j ∈ Finset.range (d n + 1), (α n j • ψ₁ j (K n N) + β n j • ψ₂ j (K n N))
    have hΦ_comb : IsGenCombSeq g (Nat.unpaired Φ) := by
      refine (isGenCombSeq_linear_comb hψ₁ hψ₂ hα' hβ' hDpair).of_eq fun i ↦ ?_
      set n := i.unpair.1
      set N := i.unpair.2
      change ∑ p ∈ Finset.range (Nat.pair (d n) (K n N) + 1),
          (α' i p • ψ₁ p.unpair.1 p.unpair.2 + β' i p • ψ₂ p.unpair.1 p.unpair.2) =
        ∑ j ∈ Finset.range (d n + 1), (α n j • ψ₁ j (K n N) + β n j • ψ₂ j (K n N))
      let img := (Finset.range (d n + 1)).image fun j ↦ Nat.pair j (K n N)
      have hsub : img ⊆ Finset.range (Nat.pair (d n) (K n N) + 1) := by
        intro p hp
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
        rw [Finset.mem_range, Nat.lt_succ_iff] at hj ⊢
        dsimp only [Nat.pair]
        split_ifs with h1 h2 h2
        · omega
        · have hk : K n N ≤ d n := not_lt.mp h2
          exact (add_le_add (Nat.mul_le_mul hk hk) hj).trans (Nat.le_add_right _ _)
        · omega
        · exact add_le_add (add_le_add (Nat.mul_le_mul hj hj) hj) le_rfl
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_image fun j₁ _ j₂ _ heq ↦ by
          simpa [Nat.unpair_pair] using congrArg (fun p ↦ p.unpair.1) heq]
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        have hj' : j ≤ d n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        simp [α', β', n, N, Nat.unpair_pair, hj']
      · intro p _ hnot
        have hbad : ¬(p.unpair.2 = K n N ∧ p.unpair.1 ≤ d n) := by
          rintro ⟨h1, h2⟩
          apply hnot
          refine Finset.mem_image.mpr ⟨p.unpair.1, Finset.mem_range.mpr (Nat.lt_succ_of_le h2), ?_⟩
          rw [← h1, Nat.pair_unpair]
        simp [α', β', n, N, hbad]
    exact isGenComputableSeq_iff_rapid.mpr ⟨Φ, hΦ_comb, fun n N ↦ by
      dsimp only [Φ]
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      have hterm_le : ∀ j ∈ Finset.range (d n + 1),
          ‖(α n j • ψ₁ j (K n N) + β n j • ψ₂ j (K n N)) - (α n j • f₁ j + β n j • f₂ j)‖ ≤
            (2 : ℝ) ^ (-((N + d n + 1 : ℕ) : ℤ)) := fun j hj ↦ by
        have hB : |α n j| + |β n j| ≤ (2 : ℝ) ^ (Bcoeff n) := by
          have hj_le : (qα (n, j) 0).num.natAbs + (qβ (n, j) 0).num.natAbs + 2 ≤ Bcoeff n :=
            Finset.le_sup
              (f := fun j ↦ (qα (n, j) 0).num.natAbs + (qβ (n, j) 0).num.natAbs + 2) hj
          have hpow : (Bcoeff n : ℝ) ≤ (2 : ℝ) ^ (Bcoeff n) := by
            exact_mod_cast Nat.lt_two_pow_self.le
          have h0α : |α n j - (qα (n, j) 0 : ℝ)| < 1 := by simpa using hcα n j 0
          have h0β : |β n j - (qβ (n, j) 0 : ℝ)| < 1 := by simpa using hcβ n j 0
          have hq0α := abs_rat_le_natAbs_num (qα (n, j) 0)
          have hq0β := abs_rat_le_natAbs_num (qβ (n, j) 0)
          have htα := abs_add_le (α n j - (qα (n, j) 0 : ℝ)) (qα (n, j) 0 : ℝ)
          have htβ := abs_add_le (β n j - (qβ (n, j) 0 : ℝ)) (qβ (n, j) 0 : ℝ)
          simp at htα htβ
          have hj_le' : ((qα (n, j) 0).num.natAbs : ℝ) + ((qβ (n, j) 0).num.natAbs : ℝ) + 2 ≤
              (Bcoeff n : ℝ) := by exact_mod_cast hj_le
          linarith
        rw [show (α n j • ψ₁ j (K n N) + β n j • ψ₂ j (K n N)) - (α n j • f₁ j + β n j • f₂ j) =
          α n j • (ψ₁ j (K n N) - f₁ j) + β n j • (ψ₂ j (K n N) - f₂ j) by
          rw [smul_sub, smul_sub]; abel]
        calc ‖α n j • (ψ₁ j (K n N) - f₁ j) + β n j • (ψ₂ j (K n N) - f₂ j)‖
            ≤ |α n j| * ‖ψ₁ j (K n N) - f₁ j‖ + |β n j| * ‖ψ₂ j (K n N) - f₂ j‖ := by
              simpa [norm_smul] using norm_add_le (α n j • (ψ₁ j (K n N) - f₁ j))
                (β n j • (ψ₂ j (K n N) - f₂ j))
          _ ≤ (|α n j| + |β n j|) * (2 : ℝ) ^ (-(K n N : ℤ)) := by
              have h1 := mul_le_mul_of_nonneg_left (hc₁ j (K n N)) (abs_nonneg (α n j))
              have h2 := mul_le_mul_of_nonneg_left (hc₂ j (K n N)) (abs_nonneg (β n j))
              linarith
          _ ≤ (2 : ℝ) ^ (Bcoeff n) * (2 : ℝ) ^ (-(K n N : ℤ)) :=
              mul_le_mul_of_nonneg_right hB (zpow_pos two_pos _).le
          _ ≤ (2 : ℝ) ^ (-((N + d n + 1 : ℕ) : ℤ)) := by
              rw [← zpow_natCast (2 : ℝ) (Bcoeff n), ← zpow_add₀ two_ne_zero]
              refine zpow_le_zpow_right₀ one_le_two ?_
              dsimp [K]; omega
      calc ∑ j ∈ Finset.range (d n + 1),
              ‖(α n j • ψ₁ j (K n N) + β n j • ψ₂ j (K n N)) - (α n j • f₁ j + β n j • f₂ j)‖
          ≤ ∑ _j ∈ Finset.range (d n + 1), (2 : ℝ) ^ (-((N + d n + 1 : ℕ) : ℤ)) :=
            Finset.sum_le_sum hterm_le
        _ = ((d n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((N + d n + 1 : ℕ) : ℤ)) := by simp
        _ ≤ (2 : ℝ) ^ (d n + 1) * (2 : ℝ) ^ (-((N + d n + 1 : ℕ) : ℤ)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.lt_two_pow_self.le)
              (zpow_pos two_pos _).le
        _ = (2 : ℝ) ^ (-(N : ℤ)) := by
            rw [← zpow_natCast (2 : ℝ) (d n + 1), ← zpow_add₀ two_ne_zero]
            congr 1; push_cast; omega⟩
  effective_limit := by
    intro f h e hf he hconv
    obtain ⟨ψ, hψ, hcψ⟩ := isGenComputableSeq_iff_rapid.mp hf
    let Φ : ℕ → ℕ → B := fun n N ↦ ψ (Nat.pair n (e n (N + 1))) (N + 1)
    have hidx : Computable fun i : ℕ ↦
        Nat.pair (Nat.pair i.unpair.1 (e i.unpair.1 (i.unpair.2 + 1))) (i.unpair.2 + 1) := by
      have hn := Computable.fst.comp .unpair
      have hN1 := Computable.succ.comp (Computable.snd.comp .unpair)
      exact Primrec₂.natPair.to_comp.comp
        (Primrec₂.natPair.to_comp.comp hn (he.comp hn hN1)) hN1
    have hΦ : IsGenCombSeq g (Nat.unpaired Φ) :=
      (hψ.comp hidx).of_eq fun i ↦ by simp [Φ, Nat.unpaired, Nat.unpair_pair]
    refine isGenComputableSeq_iff_rapid.mpr ⟨Φ, hΦ, fun n N ↦ ?_⟩
    set k := e n (N + 1)
    have h1 : ‖ψ (Nat.pair n k) (N + 1) - f n k‖ ≤ (2 : ℝ) ^ (-((N + 1 : ℕ) : ℤ)) := by
      simpa [Nat.unpaired, Nat.unpair_pair] using hcψ (Nat.pair n k) (N + 1)
    have h2 : ‖f n k - h n‖ ≤ (2 : ℝ) ^ (-((N + 1 : ℕ) : ℤ)) := hconv n (N + 1) k le_rfl
    calc ‖Φ n N - h n‖
        ≤ ‖ψ (Nat.pair n k) (N + 1) - f n k‖ + ‖f n k - h n‖ := norm_sub_le_norm_sub_add_norm_sub ..
      _ ≤ (2 : ℝ) ^ (-((N + 1 : ℕ) : ℤ)) + (2 : ℝ) ^ (-((N + 1 : ℕ) : ℤ)) := add_le_add h1 h2
      _ = (2 : ℝ) ^ (-(N : ℤ)) := by
          rw [← two_mul, show (2 : ℝ) * (2 : ℝ) ^ (-((N + 1 : ℕ) : ℤ)) =
            (2 : ℝ) ^ (1 : ℤ) * (2 : ℝ) ^ (-((N + 1 : ℕ) : ℤ)) by rw [zpow_one],
            ← zpow_add₀ two_ne_zero]; congr 1; push_cast; omega
  norm_computable := by
    intro f ⟨φ, e, hφ, he, hconv⟩
    have hnφ : IsComputableRealDoubleSeq fun n k ↦ ‖φ n k‖ := hnorm hφ
    exact hnφ.effectiveLimit he fun n N k hk ↦
      (abs_norm_sub_norm_le (φ n k) (f n)).trans (hconv n N k hk)

/-- Sequence computability in `ofGeneratingSeq g hnorm` coincides with `IsGenComputableSeq g`. -/
theorem BanachComputabilityStructure.isComputableSeq_ofGeneratingSeq_iff (g : ℕ → B)
    (hnorm : ∀ {φ : ℕ → B}, IsGenCombSeq g φ → IsComputableRealSeq fun n ↦ ‖φ n‖) {f : ℕ → B} :
    (BanachComputabilityStructure.ofGeneratingSeq g hnorm).IsComputableSeq f ↔
      IsGenComputableSeq g f := by rfl

/-- Single-element computability in `ofGeneratingSeq g hnorm` coincides with `IsGenComputable g`. -/
theorem BanachComputabilityStructure.isComputable_ofGeneratingSeq_iff (g : ℕ → B)
    (hnorm : ∀ {φ : ℕ → B}, IsGenCombSeq g φ → IsComputableRealSeq fun n ↦ ‖φ n‖) (x : B) :
    (BanachComputabilityStructure.ofGeneratingSeq g hnorm).IsComputable x ↔
      IsGenComputable g x :=
  isGenComputableSeq_const_iff

/-- A dense sequence `g : ℕ → B` is an effective generating set of `ofGeneratingSeq g hnorm`. -/
theorem BanachComputabilityStructure.isEffectiveGeneratingSet_ofGeneratingSeq (g : ℕ → B)
    (hnorm : ∀ {φ : ℕ → B}, IsGenCombSeq g φ → IsComputableRealSeq fun n ↦ ‖φ n‖)
    (hdense : (Submodule.span ℝ (Set.range g)).topologicalClosure = ⊤) :
    (BanachComputabilityStructure.ofGeneratingSeq g hnorm).IsEffectiveGeneratingSet g :=
  ⟨(isGenCombSeq_self g).isGenComputableSeq, hdense⟩

/-- `(B, ofGeneratingSeq g hnorm)` is effectively separable whenever `g` has dense real span. -/
theorem BanachComputabilityStructure.isEffectivelySeparable_ofGeneratingSeq (g : ℕ → B)
    (hnorm : ∀ {φ : ℕ → B}, IsGenCombSeq g φ → IsComputableRealSeq fun n ↦ ‖φ n‖)
    (hdense : (Submodule.span ℝ (Set.range g)).topologicalClosure = ⊤) :
    (BanachComputabilityStructure.ofGeneratingSeq g hnorm).IsEffectivelySeparable :=
  ⟨g, isEffectiveGeneratingSet_ofGeneratingSeq g hnorm hdense⟩

end GeneratedStructure

end CslibFrontier.ComputableAnalysis
