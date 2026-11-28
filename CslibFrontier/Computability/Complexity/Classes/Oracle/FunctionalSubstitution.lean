module

public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Partial
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.Deterministic
import CslibFrontier.Computability.Complexity.Classes.Oracle.Lowness
import CslibFrontier.Computability.Complexity.Classes.Oracle.PolyTime
import CslibFrontier.Computability.Complexity.Classes.Oracle.Substitution
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Configuration
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Probabilistic.Oracle.Composition

/-!
# Functional oracle substitution and relativized `coNP`

Extends oracle substitution (`Cslib.Complexity.ComputableInPolyTimeWithOracle.of_mem_PWithOracle`)
from Boolean-valued functions to word-valued functions (`FP^{P^O} = FP^O`) and to arbitrary
codomains equipped with a strict polynomial-time partial decoder (`PartialDecoder`), and defines
relativized `coNP` (`coNPWithOracle`) with its oracle-complement invariance.

## Main definitions

* `CslibFrontier.Complexity.coNPWithOracle`: `coNP` relative to an oracle language.

## Main results

* `CslibFrontier.Complexity.computableInPolyTimeWithOracle_of_mem_PWithOracle_encoded`:
  substituting an oracle `O₁ ∈ P^{O₂}` preserves `FP` computability of encoded outputs.
* `CslibFrontier.Complexity.computableInPolyTimeWithOracle_of_bits_of_decoder`:
  upgrading an encoded-output `FP^O` computation to a typed `FP^O` computation via a
  `PartialDecoder`.
* `CslibFrontier.Complexity.computableInPolyTimeWithOracle_of_mem_PWithOracle`:
  `FP^{P^{O₂}} = FP^{O₂}` for every nonempty codomain with a `PartialDecoder`.
* `CslibFrontier.Complexity.NPWithOracle_compl_eq`,
  `CslibFrontier.Complexity.coNPWithOracle_compl_eq`,
  `CslibFrontier.Complexity.iUnion_NPWithOracle_coNPWithOracle_eq`:
  oracle-complement invariance for `NP^A` and `coNP^A`, yielding `NP^{coNP^A} = NP^{NP^A}`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

variable {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}

/-- One simulated instruction of a finite oracle machine `machine` when each query to its oracle is
answered by running the deterministic oracle program `prog`. -/
private def oracleAnswerStep {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (prog : List Bool → WordQueryComp Unit Bool)
    (cfg : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit) :
    WordQueryComp Unit (Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit) :=
  if (machine.pendingQuery cfg).isSome then
    (fun b ↦ machine.receiveBit (cfg, b)) <$> prog (machine.pendingRequest cfg)
  else
    pure (machine.localStep cfg)

private theorem interpret_oracleAnswerStep {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (prog : List Bool → WordQueryComp Unit Bool)
    (cfg : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit) :
    OracleComp.interpret ProbOracleComp.query (oracleAnswerStep machine prog cfg) =
      if (machine.pendingQuery cfg).isSome then
        (fun b ↦ machine.receiveBit (cfg, b)) <$>
          OracleComp.interpret ProbOracleComp.query (prog (machine.pendingRequest cfg))
      else
        pure (machine.localStep cfg) := by
  unfold oracleAnswerStep
  split <;> simp [OracleComp.interpret_map]

private theorem isOraclePPTOn_oracleAnswerStep {k : ℕ} {Control : Type} [Finite Control]
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    {prog : List Bool → WordQueryComp Unit Bool}
    (hprog : IsOraclePPTOn encBits encBool
      (fun w ↦ OracleComp.interpret ProbOracleComp.query (prog w))) :
    IsOraclePPTOn encFiniteConfig encFiniteConfig
      (fun cfg ↦
        OracleComp.interpret ProbOracleComp.query (oracleAnswerStep machine prog cfg)) := by
  simp only [interpret_oracleAnswerStep]
  exact IsOraclePPTOn.cond
    ((ComputableInPolyTime.of_finite Option.isSome).comp machine.pendingQuery_pt)
    ((hprog.preprocess machine.pendingRequest_pt).map_with
      (f := fun cfg b ↦ machine.receiveBit (cfg, b)) machine.receiveBit_pt)
    machine.localStep_pt.isOraclePPTOn

private theorem spaceBound_of_mem_support_oracleAnswerStep {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (prog : List Bool → WordQueryComp Unit Bool)
    {inputSize steps : ℕ}
    {cfg next : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit}
    (hcfg : Turing.MultiTapeMachine.FiniteConfig.SpaceBound inputSize steps 1 cfg)
    (hnext : next ∈ OracleComp.support
      (OracleComp.interpret ProbOracleComp.query (oracleAnswerStep machine prog cfg))) :
    Turing.MultiTapeMachine.FiniteConfig.SpaceBound inputSize (steps + 1) 1 next := by
  rw [interpret_oracleAnswerStep] at hnext
  split_ifs at hnext with hq
  · obtain ⟨b, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    have hstep := machine.spaceBound_answerStep (fun _ ↦ b) hcfg
    rw [machine.answerStep_bit (fun _ ↦ b)] at hstep
    simpa [hq] using hstep
  · rw [OracleComp.eq_of_mem_supportWith_pure hnext]
    have hstep := machine.spaceBound_answerStep (fun _ ↦ false) hcfg
    rw [machine.answerStep_bit (fun _ ↦ false)] at hstep
    simpa [hq] using hstep

private theorem interpret_id_oracleAnswerStep {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    {prog : List Bool → WordQueryComp Unit Bool} {O : Set (List Bool)} {g : List Bool → Bool}
    (hg : ∀ w, OracleComp.interpret (m := Id) (languageOracle O) (prog w) = g w)
    (cfg : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit) :
    OracleComp.interpret (m := Id) (languageOracle O) (oracleAnswerStep machine prog cfg) =
      machine.answerStep (fun q ↦ [g q.2]) cfg := by
  rw [machine.answerStep_bit]
  unfold oracleAnswerStep
  split_ifs with hq
  · rw [OracleComp.interpret_map, hg]
    rfl
  · rfl

/-- Interpret a finite oracle machine under a polynomial clock, returning its full output tape. -/
private theorem computableInPolyTimeWithOracle_run_output {O : Set (List Bool)}
    {g : List Bool → Bool} (hg : ComputableInPolyTimeWithOracle O g encBits encBool)
    {k m : ℕ} (machine : Turing.MultiTapePTM k Bool (Fin m) Unit) (c d : ℕ) :
    ComputableInPolyTimeWithOracle O (fun a ↦
      ((machine.answerStep (fun q ↦ [g q.2]))^[c * ((input a).length + 1) ^ d]
        (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (input a))).tapes.output)
      input encBits := by
  obtain ⟨prog, hprog, hg⟩ := hg
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Fin m) (Oracle := Unit)
  have hcount : ComputableInPolyTime (fun a ↦ c * ((input a).length + 1) ^ d) input encUnary :=
    ((ComputableInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      (ComputableInPolyTime.encoding_length input)).of_enc_eq fun a ↦ by simp
  have hinit : ComputableInPolyTime
      (fun a ↦ Turing.MultiTapeMachine.FiniteConfig.init (k := k) (Oracle := Unit)
        machine.initial (input a))
      input encFiniteConfig := by
    refine (((ComputableInPolyTime.of_eq fun _ ↦ rfl :
        ComputableInPolyTime input input encBits).prod
      (ComputableInPolyTime.const (encOut :=
        encPair (encFinite (Option (Fin m)))
          (encPair encUnary (encPair (encPi (Index := Fin k) (encBiTape encBool)) encBits)))
        (some machine.initial, 1, fun _ ↦ Cslib.Turing.BiTape.nil, []))).prod
      (ComputableInPolyTime.const
        (encOut := encPi (Index := Unit) (encPair encBits (encBiTape encBool)))
        fun _ : Unit ↦ ([], Cslib.Turing.BiTape.nil))).of_enc_eq fun a ↦ ?_
    simp [Turing.MultiTapeMachine.FiniteConfig.init, Turing.FiniteCfg.init]
  have hbound : PolyBounded (fun a ↦ (input a).length)
      (fun a ↦ cf * ((input a).length + c * ((input a).length + 1) ^ d + 1 + 1)) := by
    growth_poly
  have hit := (IsOraclePPTOn.iterate_spec hcount hinit
    (isOraclePPTOn_oracleAnswerStep machine hprog)
    (fun a i cfg ↦ Turing.MultiTapeMachine.FiniteConfig.SpaceBound (input a).length i 1 cfg)
    (fun _ ↦ Turing.MultiTapeMachine.FiniteConfig.spaceBound_init _ _ _)
    (fun _ _ _ _ hinv _ hnext ↦
      spaceBound_of_mem_support_oracleAnswerStep machine prog hinv hnext)
    hbound
    (fun _ _ _ hi hinv ↦ (hcf _ _ _ _ hinv).trans (Nat.mul_le_mul_left cf (by omega)))).1
  refine ⟨fun a ↦ (fun cfg ↦ cfg.tapes.output) <$>
    OracleComp.iterate (c * ((input a).length + 1) ^ d) (oracleAnswerStep machine prog)
      (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (input a)), ?_, fun a ↦ ?_⟩
  · simp only [OracleComp.interpret_map, OracleComp.interpret_iterate]
    exact hit.map (by fun_prop)
  · rw [OracleComp.interpret_map, OracleComp.interpret_id_iterate]
    simp only [interpret_id_oracleAnswerStep machine hg]
    rfl

private theorem exists_clocked_output_run {O : Set (List Bool)} {f : α → β}
    (hf : ComputableInPolyTimeWithOracle O f input output) :
    ∃ (k m : ℕ) (machine : Turing.MultiTapePTM k Bool (Fin m) Unit) (c d : ℕ),
      ∀ a, ((machine.answerStep (languageOracle O))^[c * ((input a).length + 1) ^ d]
        (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (input a))).tapes.output =
          output (f a) := by
  obtain ⟨program, hcert, hprogram⟩ := hf
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
  refine ⟨k, m, machine, c, d, fun a ↦ ?_⟩
  rw [← machine.interpret_run_pure_false, hrun a (languageOracle O), hprogram a]

/-- **Oracle substitution for encoded `FP` outputs**: if `O₁ ∈ P^{O₂}` and `f : α → β` is
computable in polynomial time relative to `O₁`, then `a ↦ output (f a)` is computable in
polynomial time relative to `O₂`. -/
theorem computableInPolyTimeWithOracle_of_mem_PWithOracle_encoded {O₁ O₂ : Set (List Bool)}
    {f : α → β} (hO₁ : O₁ ∈ PWithOracle O₂ encBits)
    (hf : ComputableInPolyTimeWithOracle O₁ f input output) :
    ComputableInPolyTimeWithOracle O₂ (fun a ↦ output (f a)) input encBits := by
  classical
  obtain ⟨g, ⟨prog, hprog, hg⟩, hgO₁⟩ := hO₁
  obtain rfl : g = fun w ↦ decide (w ∈ O₁) := funext fun w ↦
    Bool.eq_iff_iff.mpr ⟨fun h ↦ decide_eq_true ((hgO₁ w).mpr h),
      fun h ↦ (hgO₁ w).mp (of_decide_eq_true h)⟩
  obtain ⟨k, m, machine, c, d, hrun⟩ := exists_clocked_output_run hf
  exact funext hrun ▸
    computableInPolyTimeWithOracle_run_output (input := input) ⟨prog, hprog, hg⟩ machine c d

/-- **Oracle substitution for word-valued `FP` functions**: if `O₁ ∈ P^{O₂}`, then every
word-valued function computable in polynomial time relative to `O₁` is computable in polynomial
time relative to `O₂`. -/
theorem computableInPolyTimeWithOracle_of_mem_PWithOracle_bits {O₁ O₂ : Set (List Bool)}
    {f : α → List Bool} (hO₁ : O₁ ∈ PWithOracle O₂ encBits)
    (hf : ComputableInPolyTimeWithOracle O₁ f input encBits) :
    ComputableInPolyTimeWithOracle O₂ f input encBits :=
  computableInPolyTimeWithOracle_of_mem_PWithOracle_encoded hO₁ hf

/-- **Typed `FP^O` upgrade via a strict partial decoder**: if `output : β ↪ List Bool` admits a
polynomial-time `PartialDecoder` and `β` is nonempty, then computing `output ∘ f` in `FP^O`
yields a typed `FP^O` computation of `f` under `output`. -/
theorem computableInPolyTimeWithOracle_of_bits_of_decoder [Nonempty β]
    (D : PartialDecoder output) {O : Set (List Bool)} {f : α → β}
    (hf : ComputableInPolyTimeWithOracle O (fun a ↦ output (f a)) input encBits) :
    ComputableInPolyTimeWithOracle O f input output := by
  classical
  let b₀ : β := Classical.arbitrary β
  let dec : List Bool → β := fun w ↦ (D.decode w).getD b₀
  let sanitize : List Bool → List Bool := fun w ↦ (D.decode w).elim (output b₀) output
  have hdec_enc (w : List Bool) : output (dec w) = sanitize w := by
    dsimp only [dec, sanitize]
    cases D.decode w <;> rfl
  have hsan : ComputableInPolyTime sanitize encBits encBits :=
    D.computable.optionElimWithInput (ComputableInPolyTime.const (output b₀))
      ((ComputableInPolyTime.of_eq (f := output) fun _ ↦ rfl).comp
        (ComputableInPolyTime.snd encBits output))
  obtain ⟨program, hcert, hprogram⟩ := hf
  refine ⟨fun a ↦ dec <$> program a, ?_, fun a ↦ ?_⟩
  · rw [IsOraclePPTOn.iff_encoded]
    have hfun : (fun a ↦ output <$> OracleComp.interpret ProbOracleComp.query (dec <$> program a)) =
        fun a ↦ sanitize <$> OracleComp.interpret ProbOracleComp.query (program a) := by
      funext a
      rw [OracleComp.interpret_map, Functor.map_map]
      simp only [hdec_enc]
    rw [hfun]
    exact hcert.map hsan
  · rw [OracleComp.interpret_map, hprogram a]
    change dec (output (f a)) = f a
    simp [dec]

/-- **Typed oracle substitution (`FP^{P^{O₂}} = FP^{O₂}`)**: if `O₁ ∈ P^{O₂}` and `output` admits
a `PartialDecoder` on a nonempty codomain, then any function computable in polynomial time relative
to `O₁` is computable in polynomial time relative to `O₂`. -/
theorem computableInPolyTimeWithOracle_of_mem_PWithOracle [Nonempty β]
    (D : PartialDecoder output) {O₁ O₂ : Set (List Bool)} {f : α → β}
    (hO₁ : O₁ ∈ PWithOracle O₂ encBits)
    (hf : ComputableInPolyTimeWithOracle O₁ f input output) :
    ComputableInPolyTimeWithOracle O₂ f input output :=
  computableInPolyTimeWithOracle_of_bits_of_decoder D
    (computableInPolyTimeWithOracle_of_mem_PWithOracle_encoded hO₁ hf)

/-! ### Relativized `coNP` and oracle-complement invariance -/

/-- The problems whose complements lie in `NP` relative to an oracle language `A`, matching
`Cslib.Complexity.coNP` and `Cslib.Complexity.NPWithOracle`. -/
def coNPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | Lᶜ ∈ NPWithOracle A enc}

/-- Membership in `coNPWithOracle A enc` means membership of the complement in `NPWithOracle`. -/
theorem mem_coNPWithOracle {A : Set (List Bool)} {enc : α ↪ List Bool} {L : Set α} :
    L ∈ coNPWithOracle A enc ↔ Lᶜ ∈ NPWithOracle A enc :=
  Iff.rfl

/-- `P^A ⊆ coNP^A`: `P^A` is closed under complement and contained in `NP^A`. -/
theorem PWithOracle_subset_coNPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    PWithOracle A enc ⊆ coNPWithOracle A enc := fun _ hL ↦
  PWithOracle_subset_NPWithOracle A enc (compl_mem_PWithOracle hL)

/-- If `O₁ ∈ P^{O₂}`, then `coNP^{O₁} ⊆ coNP^{O₂}`. -/
theorem coNPWithOracle_subset_of_mem_PWithOracle {O₁ O₂ : Set (List Bool)}
    (hO₁ : O₁ ∈ PWithOracle O₂ encBits) (enc : α ↪ List Bool) :
    coNPWithOracle O₁ enc ⊆ coNPWithOracle O₂ enc := fun _ hL ↦
  NPWithOracle_subset_of_mem_PWithOracle hO₁ enc hL

/-- Complementing the oracle preserves `NP^A`. -/
theorem NPWithOracle_compl_eq (A : Set (List Bool)) (enc : α ↪ List Bool) :
    NPWithOracle Aᶜ enc = NPWithOracle A enc :=
  Set.Subset.antisymm
    (NPWithOracle_subset_of_mem_PWithOracle (mem_PWithOracle_compl_self A) enc)
    (NPWithOracle_subset_of_mem_PWithOracle
      (by simpa only [compl_compl] using mem_PWithOracle_compl_self Aᶜ) enc)

/-- Complementing the oracle preserves `coNP^A`. -/
theorem coNPWithOracle_compl_eq (A : Set (List Bool)) (enc : α ↪ List Bool) :
    coNPWithOracle Aᶜ enc = coNPWithOracle A enc := by
  ext L
  simp only [mem_coNPWithOracle, NPWithOracle_compl_eq]

/-- `NP^{coNP^A} = NP^{NP^A}`: an `NP` machine can negate answers to a `coNP^A` oracle. -/
theorem iUnion_NPWithOracle_coNPWithOracle_eq (A : Set (List Bool)) (enc : α ↪ List Bool) :
    (⋃ B ∈ coNPWithOracle A encBits, NPWithOracle B enc) =
      ⋃ B ∈ NPWithOracle A encBits, NPWithOracle B enc := by
  ext L
  simp only [Set.mem_iUnion, exists_prop, mem_coNPWithOracle]
  exact ⟨fun ⟨B, hB, hL⟩ ↦ ⟨Bᶜ, hB, by rwa [NPWithOracle_compl_eq]⟩,
    fun ⟨B, hB, hL⟩ ↦ ⟨Bᶜ, by simpa only [compl_compl] using hB, by rwa [NPWithOracle_compl_eq]⟩⟩

end CslibFrontier.Complexity
