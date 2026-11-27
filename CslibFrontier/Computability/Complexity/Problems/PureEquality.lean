/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space.TQBF
public import CslibFrontier.Computability.Complexity.Problems.TQBF
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Logics.FirstOrder.Raw.Sentence
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Tactic.Linarith

/-!
# `PSPACE`-hardness of the first-order theory of pure equality and equivalence-nontrivial theories

Every quantified Boolean formula `φ : QBF ℕ` translates in linear size and polynomial time into a
first-order sentence over pure equality (or over a binary equivalence relation symbol `r`) by
relativizing Boolean variables to two distinct elements `x₀ ≠ x₁` (or two inequivalent equivalence
classes `[x₀] ≠ [x₁]`). Combined with `Cslib.Complexity.TQBF_pspaceHard`, this proves that the
first-order validity problem of pure equality — as well as every consistent pure-equality or
equivalence-nontrivial raw first-order theory — is `PSPACE`-hard under polynomial-time many-one
reductions (`Cslib.Complexity.PSPACEHard`).

Formulas of `Cslib.Logic.FO.RawFormula` are encoded injectively as framed prefix-order token lists
(`CslibFrontier.Complexity.encRawFormula`), mirroring `Cslib.Complexity.encQBF`. Because every
derived connective of `RawFormula` uses each subformula at most once, evaluating a reversed `QBF`
token stream on an explicit RPN stack runs in polynomial time with bounded additive stack growth per
token (`Turing.MultiTapeTM.ComputableInPolyTime.foldlWith_of_bounded_growth`).

## Main definitions

* `CslibFrontier.Complexity.RawNodeKind`, `CslibFrontier.Complexity.RawToken`,
  `CslibFrontier.Complexity.rawTokens`, `CslibFrontier.Complexity.encRawFormula`: prefix-token
  encoding of `Cslib.Logic.FO.RawFormula`.
* `CslibFrontier.Complexity.PureEqualityValid`: closed pure-equality sentences valid in every
  nonempty domain.
* `CslibFrontier.Complexity.EquivAtomSpec`, `CslibFrontier.Complexity.qbfToEquivRaw`,
  `CslibFrontier.Complexity.qbfToPureEquality`: polynomial-time relativization reductions from
  `QBF ℕ` to `RawFormula`.

## Main results

* `CslibFrontier.Complexity.computableInPolyTime_qbfToEquivRaw`,
  `CslibFrontier.Complexity.computableInPolyTime_qbfToPureEquality`: the relativization reductions
  are computable in polynomial time.
* `CslibFrontier.Complexity.mem_TQBF_iff_qbfToPureEquality_mem_valid`: correctness of the
  pure-equality reduction.
* `CslibFrontier.Complexity.PureEqualityValid_pspaceHard`: validity in the first-order theory of
  pure equality is `PSPACE`-hard.
* `CslibFrontier.Complexity.pspaceHard_of_equivNontrivialRaw`: every equivalence-nontrivial raw
  first-order theory closed under logical validity is `PSPACE`-hard.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Cslib.Logic.FO Cslib.Logic.PL Turing Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

/-! ### Prefix-token encoding of `RawFormula` -/

/-- Constructor kinds of `Cslib.Logic.FO.RawFormula` in prefix order. -/
inductive RawNodeKind where
  /-- Propositional falsity `⊥`. -/
  | falsum
  /-- Variable equality `x = y`. -/
  | equal
  /-- Relational atom `R(args)`. -/
  | rel
  /-- Implication `φ → ψ`. -/
  | imp
  /-- Universal quantification `∀ x, φ`. -/
  | all
  deriving DecidableEq, Inhabited

instance instFintypeRawNodeKind : Fintype RawNodeKind :=
  ⟨{.falsum, .equal, .rel, .imp, .all}, fun k => by cases k <;> simp⟩

/-- Numeric tag `0..4` for `RawNodeKind`. -/
def rawNodeKindIndex : RawNodeKind → ℕ
  | .falsum => 0
  | .equal => 1
  | .rel => 2
  | .imp => 3
  | .all => 4

theorem rawNodeKindIndex_injective : Function.Injective rawNodeKindIndex :=
  fun k₁ k₂ h => by cases k₁ <;> cases k₂ <;> simp_all [rawNodeKindIndex]

/-- Unary encoding of `RawNodeKind` via `rawNodeKindIndex`. -/
def encRawNodeKind : RawNodeKind ↪ List Bool :=
  ⟨fun k => encUnary (rawNodeKindIndex k), encUnary.injective.comp rawNodeKindIndex_injective⟩

/-- One prefix-order token of a `RawFormula`: constructor kind, primary index (`0` for `falsum` and
`imp`, left variable for `equal`, relation index for `rel`, bound variable for `all`), and auxiliary
argument list (`[y]` for `equal x y`, `args` for `rel r args`, `[]` otherwise). -/
structure RawToken where
  /-- Node constructor kind. -/
  kind : RawNodeKind
  /-- Primary natural-number payload in binary. -/
  head : ℕ
  /-- Auxiliary natural-number argument list in binary. -/
  args : List ℕ
  deriving DecidableEq, Inhabited

/-- Framed binary-payload list encoding for `RawToken.args`. -/
abbrev encNatList : List ℕ ↪ List Bool := encList encNat

/-- Structure encoding of `RawToken`: unary node kind, binary `head`, and framed list of binary
`args`. -/
enc_structure encRawToken : RawToken where
  kind : encRawNodeKind, head : encNat, args : encNatList

/-- Framed list encoding of `List RawToken`. -/
abbrev encRawTokenList : List RawToken ↪ List Bool := encList encRawToken

/-- Prefix-order token serialization of `RawFormula`. -/
def rawTokens : RawFormula → List RawToken
  | .falsum => [⟨.falsum, 0, []⟩]
  | .equal x y => [⟨.equal, x, [y]⟩]
  | .rel r args => [⟨.rel, r, args⟩]
  | .imp φ ψ => ⟨.imp, 0, []⟩ :: (rawTokens φ ++ rawTokens ψ)
  | .all x φ => ⟨.all, x, []⟩ :: rawTokens φ

/-- Interpret one `RawToken` as a `Cslib.PrefixParser.Step`. -/
def readRawToken : RawToken → Option (Cslib.PrefixParser.Step RawFormula)
  | ⟨.falsum, 0, []⟩ => some (.atom .falsum)
  | ⟨.equal, x, [y]⟩ => some (.atom (.equal x y))
  | ⟨.rel, r, args⟩ => some (.atom (.rel r args))
  | ⟨.imp, 0, []⟩ => some (.binary .imp)
  | ⟨.all, x, []⟩ => some (.unary (.all x))
  | _ => none

/-- Parsing `rawTokens φ` leaves any trailing token suffix untouched. -/
theorem parseFuel_rawTokens (φ : RawFormula) (rest : List RawToken) (fuel : ℕ)
    (hf : (rawTokens φ).length ≤ fuel) :
    Cslib.PrefixParser.parseFuel readRawToken fuel (rawTokens φ ++ rest) = some (φ, rest) := by
  induction φ generalizing fuel rest with
  | falsum | equal _ _ | rel _ _ =>
    cases fuel <;> simp_all [rawTokens, Cslib.PrefixParser.parseFuel, readRawToken]
  | all x φ ih =>
    cases fuel with
    | zero => simp [rawTokens] at hf
    | succ fuel =>
      simp only [rawTokens, List.length_cons] at hf
      simp only [rawTokens, List.cons_append, Cslib.PrefixParser.parseFuel, readRawToken]
      rw [ih rest fuel (Nat.le_of_succ_le_succ hf)]
      rfl
  | imp φ ψ ihφ ihψ =>
    cases fuel with
    | zero => simp [rawTokens] at hf
    | succ fuel =>
      simp only [rawTokens, List.length_cons, List.length_append] at hf
      simp only [rawTokens, List.cons_append, List.append_assoc,
        Cslib.PrefixParser.parseFuel, readRawToken]
      rw [ihφ (rawTokens ψ ++ rest) fuel
        ((Nat.le_add_right _ _).trans (Nat.le_of_succ_le_succ hf))]
      dsimp only [Bind.bind, Option.bind]
      rw [ihψ rest fuel ((Nat.le_add_left _ _).trans (Nat.le_of_succ_le_succ hf))]
      rfl

theorem rawTokens_append_inj {φ ψ : RawFormula} {r r' : List RawToken}
    (h : rawTokens φ ++ r = rawTokens ψ ++ r') : φ = ψ ∧ r = r' :=
  Cslib.PrefixParser.append_injective parseFuel_rawTokens h

theorem rawTokens_injective : Function.Injective rawTokens := fun φ ψ h =>
  (Cslib.PrefixParser.append_injective parseFuel_rawTokens (rest := []) (rest' := [])
    (by simpa using h)).1

/-- Injective encoding of `RawFormula` as the framed list of its prefix-order `RawToken`s. -/
def encRawFormula : RawFormula ↪ List Bool :=
  ⟨fun φ => encRawTokenList (rawTokens φ),
    fun _ _ h => rawTokens_injective (encRawTokenList.injective h)⟩

theorem encRawFormula_apply (φ : RawFormula) :
    encRawFormula φ = encRawTokenList (rawTokens φ) := by
  rfl

/-! ### Polynomial-time constructors on `encRawFormula` -/

section PolyTimeConstructors

variable {γ : Type} {encIn : γ ↪ List Bool}

@[fun_prop]
theorem computableInPolyTime_rawTokens :
    ComputableInPolyTime rawTokens encRawFormula encRawTokenList :=
  of_eq fun _ => rfl

theorem computableInPolyTime_of_rawTokens {f : γ → RawFormula} {l : γ → List RawToken}
    (hl : ComputableInPolyTime l encIn encRawTokenList) (h : ∀ x, rawTokens (f x) = l x) :
    ComputableInPolyTime f encIn encRawFormula :=
  hl.of_enc_eq fun x => by rw [encRawFormula_apply, h]

@[fun_prop]
theorem computableInPolyTime_rawFalsum :
    ComputableInPolyTime (fun _ : γ => RawFormula.falsum) encIn encRawFormula :=
  const RawFormula.falsum

@[fun_prop]
theorem computableInPolyTime_rawEqual {x y : γ → ℕ}
    (hx : ComputableInPolyTime x encIn encNat) (hy : ComputableInPolyTime y encIn encNat) :
    ComputableInPolyTime (fun a => RawFormula.equal (x a) (y a)) encIn encRawFormula :=
  computableInPolyTime_of_rawTokens
    (l := fun a => [⟨.equal, x a, [y a]⟩]) (by fun_prop) fun _ => rfl

@[fun_prop]
theorem computableInPolyTime_rawRel {r : γ → ℕ} {args : γ → List ℕ}
    (hr : ComputableInPolyTime r encIn encNat)
    (hargs : ComputableInPolyTime args encIn encNatList) :
    ComputableInPolyTime (fun a => RawFormula.rel (r a) (args a)) encIn encRawFormula :=
  computableInPolyTime_of_rawTokens
    (l := fun a => [⟨.rel, r a, args a⟩]) (by fun_prop) fun _ => rfl

@[fun_prop]
theorem computableInPolyTime_rawImp {φ ψ : γ → RawFormula}
    (hφ : ComputableInPolyTime φ encIn encRawFormula)
    (hψ : ComputableInPolyTime ψ encIn encRawFormula) :
    ComputableInPolyTime (fun a => RawFormula.imp (φ a) (ψ a)) encIn encRawFormula :=
  computableInPolyTime_of_rawTokens
    (l := fun a => ⟨.imp, 0, []⟩ :: (rawTokens (φ a) ++ rawTokens (ψ a))) (by fun_prop)
    fun _ => rfl

@[fun_prop]
theorem computableInPolyTime_rawAll {x : γ → ℕ} {φ : γ → RawFormula}
    (hx : ComputableInPolyTime x encIn encNat)
    (hφ : ComputableInPolyTime φ encIn encRawFormula) :
    ComputableInPolyTime (fun a => RawFormula.all (x a) (φ a)) encIn encRawFormula :=
  computableInPolyTime_of_rawTokens
    (l := fun a => ⟨.all, x a, []⟩ :: rawTokens (φ a)) (by fun_prop) fun _ => rfl

@[fun_prop]
theorem computableInPolyTime_rawNeg {φ : γ → RawFormula}
    (hφ : ComputableInPolyTime φ encIn encRawFormula) :
    ComputableInPolyTime (fun a => RawFormula.neg (φ a)) encIn encRawFormula := by
  unfold RawFormula.neg
  fun_prop

@[fun_prop]
theorem computableInPolyTime_rawVerum :
    ComputableInPolyTime (fun _ : γ => RawFormula.verum) encIn encRawFormula :=
  const RawFormula.verum

@[fun_prop]
theorem computableInPolyTime_rawDisj {φ ψ : γ → RawFormula}
    (hφ : ComputableInPolyTime φ encIn encRawFormula)
    (hψ : ComputableInPolyTime ψ encIn encRawFormula) :
    ComputableInPolyTime (fun a => RawFormula.disj (φ a) (ψ a)) encIn encRawFormula := by
  unfold RawFormula.disj
  fun_prop

@[fun_prop]
theorem computableInPolyTime_rawConj {φ ψ : γ → RawFormula}
    (hφ : ComputableInPolyTime φ encIn encRawFormula)
    (hψ : ComputableInPolyTime ψ encIn encRawFormula) :
    ComputableInPolyTime (fun a => RawFormula.conj (φ a) (ψ a)) encIn encRawFormula := by
  unfold RawFormula.conj
  fun_prop

@[fun_prop]
theorem computableInPolyTime_rawEx {x : γ → ℕ} {φ : γ → RawFormula}
    (hx : ComputableInPolyTime x encIn encNat)
    (hφ : ComputableInPolyTime φ encIn encRawFormula) :
    ComputableInPolyTime (fun a => RawFormula.ex (x a) (φ a)) encIn encRawFormula := by
  unfold RawFormula.ex
  fun_prop

end PolyTimeConstructors

/-! ### Relativization of `QBF ℕ` to pure equality and equivalence relations -/

/-- Specification of the binary equivalence atom used in the two-class relativization: either
built-in equality `x = y` (`pureEq`) or a binary relation symbol `R_r(x, y)` (`binRel r`). -/
inductive EquivAtomSpec where
  /-- Built-in variable equality `equal x y`. -/
  | pureEq
  /-- Binary relation symbol `rel r [x, y]`. -/
  | binRel (r : ℕ)
  deriving DecidableEq, Inhabited

/-- Atomic equivalence formula `x ~ y` determined by `spec`. -/
def EquivAtomSpec.atom (spec : EquivAtomSpec) (x y : ℕ) : RawFormula :=
  match spec with
  | .pureEq => .equal x y
  | .binRel r => .rel r [x, y]

/-- Semantic equivalence relation on `M` induced by `spec` under relation interpretation `I`. -/
def EquivAtomSpec.Rel {M : Type*} (spec : EquivAtomSpec) (I : ℕ → List M → Prop) (a b : M) : Prop :=
  match spec with
  | .pureEq => a = b
  | .binRel r => I r [a, b]

theorem EquivAtomSpec.realize_atom {M : Type*} (spec : EquivAtomSpec) (I : ℕ → List M → Prop)
    (v : ℕ → M) (x y : ℕ) :
    (spec.atom x y).Realize I v ↔ spec.Rel I (v x) (v y) := by
  cases spec <;> rfl

/-- Vocabulary of relation symbol–arity pairs allowed by `spec`. -/
def EquivAtomSpec.vocab : EquivAtomSpec → Set (ℕ × ℕ)
  | .pureEq => ∅
  | .binRel r => {(r, 2)}

/-- Membership of variable `u` in the two equivalence classes `[x₀] ∪ [x₁]`. -/
def inTwoClassesRaw (spec : EquivAtomSpec) (u : ℕ) : RawFormula :=
  RawFormula.disj (spec.atom u 0) (spec.atom u 1)

/-- Relativize a `QBF ℕ` formula `φ` to the two equivalence classes of variables `0` (representing
`false`) and `1` (representing `true`), shifting `QBF` variable `v` to `v + 2`. -/
def relativizeQBFRaw (spec : EquivAtomSpec) : QBF ℕ → RawFormula
  | .var v => spec.atom (v + 2) 1
  | .top => .verum
  | .bot => .falsum
  | .not φ => (relativizeQBFRaw spec φ).neg
  | .and φ ψ => (relativizeQBFRaw spec φ).conj (relativizeQBFRaw spec ψ)
  | .or φ ψ => (relativizeQBFRaw spec φ).disj (relativizeQBFRaw spec ψ)
  | .ex v φ => .ex (v + 2) ((inTwoClassesRaw spec (v + 2)).conj (relativizeQBFRaw spec φ))
  | .all v φ => .all (v + 2) ((inTwoClassesRaw spec (v + 2)).imp (relativizeQBFRaw spec φ))

/-- List of free variables of a `QBF ℕ` formula (with repetitions), computed structurally alongside
the RPN translation to decide `QBF.Closed`. -/
def qbfFreeVarsList : QBF ℕ → List ℕ
  | .var v => [v]
  | .top => []
  | .bot => []
  | .not φ => qbfFreeVarsList φ
  | .and φ ψ => qbfFreeVarsList φ ++ qbfFreeVarsList ψ
  | .or φ ψ => qbfFreeVarsList φ ++ qbfFreeVarsList ψ
  | .ex v φ => (qbfFreeVarsList φ).filter (· != v)
  | .all v φ => (qbfFreeVarsList φ).filter (· != v)

theorem mem_qbfFreeVarsList_iff (φ : QBF ℕ) (v : ℕ) :
    v ∈ qbfFreeVarsList φ ↔ v ∈ φ.freeVars := by
  induction φ with
  | var w => simp [qbfFreeVarsList, QBF.freeVars]
  | top | bot => simp [qbfFreeVarsList, QBF.freeVars]
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp [qbfFreeVarsList, QBF.freeVars, ihφ, ihψ]
  | ex w φ ih | all w φ ih =>
    simp [qbfFreeVarsList, QBF.freeVars, ih, and_comm]

theorem qbfFreeVarsList_isEmpty_iff (φ : QBF ℕ) :
    (qbfFreeVarsList φ).isEmpty = true ↔ φ.Closed := by
  rw [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem, QBF.Closed,
    Finset.eq_empty_iff_forall_notMem]
  exact forall_congr' fun v => not_congr (mem_qbfFreeVarsList_iff φ v)

/-- Closed sentence `∀ x₀ ∀ x₁, ¬(x₀ ~ x₁) → relativizeQBFRaw spec φ` when `φ` is closed, and
`RawFormula.falsum` when `φ` has free variables. -/
def qbfToEquivRaw (spec : EquivAtomSpec) (φ : QBF ℕ) : RawFormula :=
  if (qbfFreeVarsList φ).isEmpty then
    RawFormula.all 0 (RawFormula.all 1
      (RawFormula.imp (RawFormula.neg (spec.atom 0 1)) (relativizeQBFRaw spec φ)))
  else
    RawFormula.falsum

/-- Pure-equality reduction mapping `φ : QBF ℕ` to a closed pure-equality `RawFormula`. -/
def qbfToPureEquality (φ : QBF ℕ) : RawFormula :=
  qbfToEquivRaw .pureEq φ

/-! ### Stack-based polynomial-time implementation of `qbfToEquivRaw` -/

/-- Entry on the RPN evaluation stack: translated `RawFormula` paired with its free-variable
list. -/
structure RPNEntry where
  /-- Translated raw formula for this subterm. -/
  formula : RawFormula
  /-- Free `QBF` variables of this subterm. -/
  freeVars : List ℕ
  deriving DecidableEq

/-- Structure encoding of `RPNEntry`. -/
enc_structure encRPNEntry : RPNEntry where
  formula : encRawFormula, freeVars : encNatList

/-- Framed list encoding of the RPN stack `List RPNEntry`. -/
abbrev encRPNStack : List RPNEntry ↪ List Bool := encList encRPNEntry

/-- One step of the RPN translator on a reversed `QBF` token stream. -/
def rpnStep (spec : EquivAtomSpec) (stack : List RPNEntry) (tok : QBF.Kind × ℕ) :
    List RPNEntry :=
  let dflt : RPNEntry := ⟨.falsum, []⟩
  let e₁ := stack.headD dflt
  let e₂ := stack.tail.headD dflt
  let v2 := tok.2 + 1 + 1
  match tok.1 with
  | .var => ⟨spec.atom v2 1, [tok.2]⟩ :: stack
  | .top => ⟨.verum, []⟩ :: stack
  | .bot => ⟨.falsum, []⟩ :: stack
  | .not => ⟨e₁.formula.neg, e₁.freeVars⟩ :: stack.tail
  | .and => ⟨e₁.formula.conj e₂.formula, e₁.freeVars ++ e₂.freeVars⟩ :: stack.tail.tail
  | .or => ⟨e₁.formula.disj e₂.formula, e₁.freeVars ++ e₂.freeVars⟩ :: stack.tail.tail
  | .ex =>
    ⟨.ex v2 ((inTwoClassesRaw spec v2).conj e₁.formula),
      e₁.freeVars.filter (· != tok.2)⟩ :: stack.tail
  | .all =>
    ⟨.all v2 ((inTwoClassesRaw spec v2).imp e₁.formula),
      e₁.freeVars.filter (· != tok.2)⟩ :: stack.tail

theorem foldl_rpnStep_tokens_reverse (spec : EquivAtomSpec) (φ : QBF ℕ) (stack : List RPNEntry) :
    φ.tokens.reverse.foldl (rpnStep spec) stack =
      ⟨relativizeQBFRaw spec φ, qbfFreeVarsList φ⟩ :: stack := by
  induction φ generalizing stack with
  | var v => rfl
  | top => rfl
  | bot => rfl
  | not φ ih =>
    simp only [QBF.tokens, List.reverse_cons, List.foldl_append, ih, List.foldl_cons,
      List.foldl_nil, rpnStep, List.headD_cons, List.tail_cons, relativizeQBFRaw, qbfFreeVarsList]
  | and φ ψ ihφ ihψ =>
    simp only [QBF.tokens, List.reverse_cons, List.reverse_append, List.append_assoc,
      List.foldl_append, ihψ, ihφ, List.foldl_cons, List.foldl_nil, rpnStep, List.headD_cons,
      List.tail_cons, relativizeQBFRaw, qbfFreeVarsList]
  | or φ ψ ihφ ihψ =>
    simp only [QBF.tokens, List.reverse_cons, List.reverse_append, List.append_assoc,
      List.foldl_append, ihψ, ihφ, List.foldl_cons, List.foldl_nil, rpnStep, List.headD_cons,
      List.tail_cons, relativizeQBFRaw, qbfFreeVarsList]
  | ex v φ ih =>
    simp only [QBF.tokens, List.reverse_cons, List.foldl_append, ih, List.foldl_cons,
      List.foldl_nil, rpnStep, List.headD_cons, List.tail_cons, relativizeQBFRaw, qbfFreeVarsList]
  | all v φ ih =>
    simp only [QBF.tokens, List.reverse_cons, List.foldl_append, ih, List.foldl_cons,
      List.foldl_nil, rpnStep, List.headD_cons, List.tail_cons, relativizeQBFRaw, qbfFreeVarsList]

private theorem computableInPolyTime_succ_encNat :
    ComputableInPolyTime (fun n : ℕ => n + 1) encNat encNat :=
  ComputableInDegree.natSucc.computableInPolyTime

private theorem computableInPolyTime_atom (spec : EquivAtomSpec) {γ : Type}
    {encIn : γ ↪ List Bool} {x y : γ → ℕ}
    (hx : ComputableInPolyTime x encIn encNat) (hy : ComputableInPolyTime y encIn encNat) :
    ComputableInPolyTime (fun a => spec.atom (x a) (y a)) encIn encRawFormula := by
  cases spec with
  | pureEq =>
    unfold EquivAtomSpec.atom
    fun_prop
  | binRel r =>
    unfold EquivAtomSpec.atom
    fun_prop

private theorem computableInPolyTime_inTwoClassesRaw (spec : EquivAtomSpec) {γ : Type}
    {encIn : γ ↪ List Bool} {u : γ → ℕ} (hu : ComputableInPolyTime u encIn encNat) :
    ComputableInPolyTime (fun a => inTwoClassesRaw spec (u a)) encIn encRawFormula := by
  have h0 := computableInPolyTime_atom spec hu (const 0)
  have h1 := computableInPolyTime_atom spec hu (const 1)
  unfold inTwoClassesRaw
  fun_prop

private theorem computableInPolyTime_rpnStep (spec : EquivAtomSpec) :
    ComputableInPolyTime (fun p : List RPNEntry × (QBF.Kind × ℕ) => rpnStep spec p.1 p.2)
      (encPair encRPNStack TQBF.encToken) encRPNStack := by
  let encIn := encPair encRPNStack TQBF.encToken
  have hstack : ComputableInPolyTime Prod.fst encIn encRPNStack := fst _ _
  have htok : ComputableInPolyTime Prod.snd encIn TQBF.encToken := snd _ _
  have hkind : ComputableInPolyTime (fun p : List RPNEntry × (QBF.Kind × ℕ) => p.2.1)
      encIn TQBF.encKind := htok.fst'
  have hv : ComputableInPolyTime (fun p : List RPNEntry × (QBF.Kind × ℕ) => p.2.2)
      encIn encNat := htok.snd'
  have hv1 : ComputableInPolyTime (fun p : List RPNEntry × (QBF.Kind × ℕ) => p.2.2 + 1)
      encIn encNat := computableInPolyTime_succ_encNat.comp hv
  have hv2 : ComputableInPolyTime (fun p : List RPNEntry × (QBF.Kind × ℕ) => p.2.2 + 1 + 1)
      encIn encNat := computableInPolyTime_succ_encNat.comp hv1
  have htest (k : QBF.Kind) : ComputableInPolyTime
      (fun p : List RPNEntry × (QBF.Kind × ℕ) => decide (p.2.1 = k)) encIn encBool :=
    (of_finite (encIn := TQBF.encKind) (encOut := encBool) fun q : QBF.Kind => decide (q = k)).comp
      hkind
  have hatomV2 := computableInPolyTime_atom spec hv2 (const 1)
  have hinTwo := computableInPolyTime_inTwoClassesRaw spec hv2
  have hvar : ComputableInPolyTime
      (fun p : List RPNEntry × (QBF.Kind × ℕ) =>
        (⟨spec.atom (p.2.2 + 1 + 1) 1, [p.2.2]⟩ : RPNEntry) :: p.1) encIn encRPNStack := by
    fun_prop
  have htop : ComputableInPolyTime
      (fun p : List RPNEntry × (QBF.Kind × ℕ) => (⟨.verum, []⟩ : RPNEntry) :: p.1)
      encIn encRPNStack := by fun_prop
  have hbot : ComputableInPolyTime
      (fun p : List RPNEntry × (QBF.Kind × ℕ) => (⟨.falsum, []⟩ : RPNEntry) :: p.1)
      encIn encRPNStack := by fun_prop
  have hdflt : ComputableInPolyTime
      (fun _ : List RPNEntry × (QBF.Kind × ℕ) => (⟨.falsum, []⟩ : RPNEntry))
      encIn encRPNEntry := const ({ formula := .falsum, freeVars := [] } : RPNEntry)
  have he1 : ComputableInPolyTime
      (fun p : List RPNEntry × (QBF.Kind × ℕ) => p.1.headD ⟨.falsum, []⟩)
      encIn encRPNEntry := listHeadDWithInput hstack hdflt
  have htail1 : ComputableInPolyTime
      (fun p : List RPNEntry × (QBF.Kind × ℕ) => p.1.tail)
      encIn encRPNStack := (listTail encRPNEntry).comp hstack
  have he2 : ComputableInPolyTime
      (fun p : List RPNEntry × (QBF.Kind × ℕ) => p.1.tail.headD ⟨.falsum, []⟩)
      encIn encRPNEntry := listHeadDWithInput htail1 hdflt
  have htail2 : ComputableInPolyTime
      (fun p : List RPNEntry × (QBF.Kind × ℕ) => p.1.tail.tail)
      encIn encRPNStack := (listTail encRPNEntry).comp htail1
  have hfilt : ComputableInPolyTime
      (fun p : List RPNEntry × (QBF.Kind × ℕ) =>
        (p.1.headD ⟨.falsum, []⟩).freeVars.filter (· != p.2.2)) encIn encNatList := by
    apply filterWithInput (by fun_prop)
    have hq2 := snd encIn encNat
    exact bne hq2 (hv.comp (fst encIn encNat))
  have hnot : ComputableInPolyTime
      (fun p : List RPNEntry × (QBF.Kind × ℕ) =>
        (⟨(p.1.headD ⟨.falsum, []⟩).formula.neg,
          (p.1.headD ⟨.falsum, []⟩).freeVars⟩ : RPNEntry) :: p.1.tail)
      encIn encRPNStack := by fun_prop
  have hand : ComputableInPolyTime
      (fun p : List RPNEntry × (QBF.Kind × ℕ) =>
        (⟨(p.1.headD ⟨.falsum, []⟩).formula.conj (p.1.tail.headD ⟨.falsum, []⟩).formula,
          (p.1.headD ⟨.falsum, []⟩).freeVars ++
            (p.1.tail.headD ⟨.falsum, []⟩).freeVars⟩ : RPNEntry) :: p.1.tail.tail)
      encIn encRPNStack := by fun_prop
  have hor : ComputableInPolyTime
      (fun p : List RPNEntry × (QBF.Kind × ℕ) =>
        (⟨(p.1.headD ⟨.falsum, []⟩).formula.disj (p.1.tail.headD ⟨.falsum, []⟩).formula,
          (p.1.headD ⟨.falsum, []⟩).freeVars ++
            (p.1.tail.headD ⟨.falsum, []⟩).freeVars⟩ : RPNEntry) :: p.1.tail.tail)
      encIn encRPNStack := by fun_prop
  have hex : ComputableInPolyTime
      (fun p : List RPNEntry × (QBF.Kind × ℕ) =>
        (⟨.ex (p.2.2 + 1 + 1)
            ((inTwoClassesRaw spec (p.2.2 + 1 + 1)).conj (p.1.headD ⟨.falsum, []⟩).formula),
          (p.1.headD ⟨.falsum, []⟩).freeVars.filter (· != p.2.2)⟩ : RPNEntry) :: p.1.tail)
      encIn encRPNStack := by fun_prop
  have hall : ComputableInPolyTime
      (fun p : List RPNEntry × (QBF.Kind × ℕ) =>
        (⟨.all (p.2.2 + 1 + 1)
            ((inTwoClassesRaw spec (p.2.2 + 1 + 1)).imp (p.1.headD ⟨.falsum, []⟩).formula),
          (p.1.headD ⟨.falsum, []⟩).freeVars.filter (· != p.2.2)⟩ : RPNEntry) :: p.1.tail)
      encIn encRPNStack := by fun_prop
  refine ((htest .var).ite' hvar ((htest .top).ite' htop ((htest .bot).ite' hbot
    ((htest .not).ite' hnot ((htest .and).ite' hand ((htest .or).ite' hor
      ((htest .ex).ite' hex hall))))))).of_enc_eq fun ⟨s, k, v⟩ => ?_
  cases k <;> rfl

private theorem length_encList_filter_le {α : Type*} (enc : α ↪ List Bool) (p : α → Bool)
    (l : List α) : (encList enc (l.filter p)).length ≤ (encList enc l).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons]
    split_ifs <;> simp only [encList_cons, List.length_append, length_frame] <;> omega

private theorem length_encNat_add_two_le (v : ℕ) :
    (encNat (v + 1 + 1)).length ≤ (encNat v).length + 2 := by
  have h1 : (encNat (v + 1)).length ≤ (encNat v).length + 1 := by
    rw [encNat_apply, encNat_apply, NatSucc.bits_succ]
    have hincr (c : Bool) (l : List Bool) : (NatSucc.incr c l).length ≤ l.length + 1 := by
      induction l generalizing c with
      | nil => cases c <;> simp [NatSucc.incr]
      | cons b l ih =>
        cases c <;> cases b <;> simp only [NatSucc.incr, List.length_cons] <;> have := ih true <;>
          have := ih false <;> omega
    exact hincr true v.bits
  have h2 : (encNat (v + 1 + 1)).length ≤ (encNat (v + 1)).length + 1 := by
    rw [encNat_apply, encNat_apply, NatSucc.bits_succ]
    have hincr (c : Bool) (l : List Bool) : (NatSucc.incr c l).length ≤ l.length + 1 := by
      induction l generalizing c with
      | nil => cases c <;> simp [NatSucc.incr]
      | cons b l ih =>
        cases c <;> cases b <;> simp only [NatSucc.incr, List.length_cons] <;> have := ih true <;>
          have := ih false <;> omega
    exact hincr true (v + 1).bits
  omega

private theorem length_encRawToken_const (k : RawNodeKind) :
    (encRawToken ⟨k, 0, []⟩).length ≤ 12 := by
  rw [encRawToken_apply, encRawTokenFields, length_encPair, length_encPair]
  dsimp only
  have hk : (encRawNodeKind k).length ≤ 4 := by
    change (List.replicate (rawNodeKindIndex k) true).length ≤ 4
    cases k <;> simp [rawNodeKindIndex]
  have h0 : (encNat 0).length = 0 := rfl
  have hnil : (encNatList []).length = 0 := by simp
  omega

private theorem length_encRawFormula_falsum : (encRawFormula .falsum).length ≤ 26 := by
  have htFal := length_encRawToken_const .falsum
  simp only [encRawFormula_apply, encRawTokenList, rawTokens, encList_cons, encList_nil,
    List.append_nil, length_frame]
  omega

private theorem length_encRawFormula_imp (φ ψ : RawFormula) :
    (encRawFormula (φ.imp ψ)).length ≤
      (encRawFormula φ).length + (encRawFormula ψ).length + 26 := by
  have htImp := length_encRawToken_const .imp
  simp only [encRawFormula_apply, encRawTokenList, rawTokens, encList_cons, encList_append,
    List.length_append, length_frame]
  omega

private theorem length_encRawFormula_neg (φ : RawFormula) :
    (encRawFormula φ.neg).length ≤ (encRawFormula φ).length + 52 := by
  have hI := length_encRawFormula_imp φ .falsum
  have hF := length_encRawFormula_falsum
  rw [RawFormula.neg]
  omega

private theorem length_encRawFormula_verum : (encRawFormula .verum).length ≤ 78 := by
  have hN := length_encRawFormula_neg .falsum
  have hF := length_encRawFormula_falsum
  rw [RawFormula.verum]
  omega

private theorem length_encRawFormula_disj (φ ψ : RawFormula) :
    (encRawFormula (φ.disj ψ)).length ≤
      (encRawFormula φ).length + (encRawFormula ψ).length + 78 := by
  have hI := length_encRawFormula_imp φ.neg ψ
  have hN := length_encRawFormula_neg φ
  rw [RawFormula.disj]
  omega

private theorem length_encRawFormula_conj (φ ψ : RawFormula) :
    (encRawFormula (φ.conj ψ)).length ≤
      (encRawFormula φ).length + (encRawFormula ψ).length + 130 := by
  have hOuter := length_encRawFormula_neg (φ.imp ψ.neg)
  have hI := length_encRawFormula_imp φ ψ.neg
  have hN := length_encRawFormula_neg ψ
  rw [RawFormula.conj]
  omega

private theorem length_encRawFormula_all (x : ℕ) (φ : RawFormula) :
    (encRawFormula (.all x φ)).length ≤
      (encRawFormula φ).length + 4 * (encNat x).length + 25 := by
  simp only [encRawFormula_apply, encRawTokenList, rawTokens, encList_cons, List.length_append,
    length_frame, encRawToken_apply, encRawTokenFields, length_encPair, encNatList, encList_nil,
    List.length_nil]
  have hk : (encRawNodeKind .all).length = 4 := rfl
  omega

private theorem length_encRawFormula_ex (x : ℕ) (φ : RawFormula) :
    (encRawFormula (.ex x φ)).length ≤
      (encRawFormula φ).length + 4 * (encNat x).length + 130 := by
  have hN1 := length_encRawFormula_neg (.all x φ.neg)
  have hA := length_encRawFormula_all x φ.neg
  have hN2 := length_encRawFormula_neg φ
  rw [RawFormula.ex]
  omega

private theorem length_encRPNEntry (e : RPNEntry) :
    (encRPNEntry e).length =
      2 * (encRawFormula e.formula).length + 1 + (encList encNat e.freeVars).length := by
  rw [encRPNEntry_apply, encRPNEntryFields, length_encPair]

private theorem length_rpnStep_growth (spec : EquivAtomSpec) (s : List RPNEntry)
    (tok : QBF.Kind × ℕ) :
    (encRPNStack (rpnStep spec s tok)).length ≤
      (encRPNStack s).length +
        (80 * (encNat tok.2).length + 80 * (encRawFormula (spec.atom 0 1)).length + 2000) := by
  dsimp only [encRPNStack]
  have hv2 := length_encNat_add_two_le tok.2
  have hatom (y : ℕ) (hy : (encNat y).length ≤ 1) :
      (encRawFormula (spec.atom (tok.2 + 1 + 1) y)).length ≤
        (encRawFormula (spec.atom 0 1)).length + 4 * (encNat tok.2).length + 40 := by
    have h0 : (encNat 0).length = 0 := rfl
    have h1 : (encNat 1).length = 1 := rfl
    cases spec <;>
      simp only [EquivAtomSpec.atom, encRawFormula_apply, encRawTokenList, rawTokens, encList_cons,
        encList_nil, List.append_nil, List.length_append, length_frame, encRawToken_apply,
        encRawTokenFields, length_encPair, encNatList] <;>
      omega
  have hatom0 := hatom 0 (Nat.zero_le 1)
  have hatom1 := hatom 1 (le_rfl)
  have hdflt := length_encRawFormula_falsum
  have hverum := length_encRawFormula_verum
  have hinTwo :
      (encRawFormula (inTwoClassesRaw spec (tok.2 + 1 + 1))).length ≤
        2 * (encRawFormula (spec.atom 0 1)).length + 8 * (encNat tok.2).length + 160 := by
    have hD := length_encRawFormula_disj (spec.atom (tok.2 + 1 + 1) 0)
      (spec.atom (tok.2 + 1 + 1) 1)
    rw [inTwoClassesRaw]
    omega
  have hexBound (φ : RawFormula) :
      (encRawFormula (.ex (tok.2 + 1 + 1)
        ((inTwoClassesRaw spec (tok.2 + 1 + 1)).conj φ))).length ≤
        (encRawFormula φ).length + 2 * (encRawFormula (spec.atom 0 1)).length +
          12 * (encNat tok.2).length + 430 := by
    have hE := length_encRawFormula_ex (tok.2 + 1 + 1)
      ((inTwoClassesRaw spec (tok.2 + 1 + 1)).conj φ)
    have hC := length_encRawFormula_conj (inTwoClassesRaw spec (tok.2 + 1 + 1)) φ
    omega
  have hallBound (φ : RawFormula) :
      (encRawFormula (.all (tok.2 + 1 + 1)
        ((inTwoClassesRaw spec (tok.2 + 1 + 1)).imp φ))).length ≤
        (encRawFormula φ).length + 2 * (encRawFormula (spec.atom 0 1)).length +
          12 * (encNat tok.2).length + 220 := by
    have hA := length_encRawFormula_all (tok.2 + 1 + 1)
      ((inTwoClassesRaw spec (tok.2 + 1 + 1)).imp φ)
    have hI := length_encRawFormula_imp (inTwoClassesRaw spec (tok.2 + 1 + 1)) φ
    omega
  cases htk : tok.1
  · simp only [rpnStep, htk, encList_cons, List.length_append, length_frame, length_encRPNEntry,
      encList_nil, List.append_nil]
    omega
  · simp only [rpnStep, htk, encList_cons, List.length_append, length_frame, length_encRPNEntry,
      encList_nil, List.length_nil]
    omega
  · simp only [rpnStep, htk, encList_cons, List.length_append, length_frame, length_encRPNEntry,
      encList_nil, List.length_nil]
    omega
  · cases s with
    | nil =>
      have hN := length_encRawFormula_neg .falsum
      simp only [rpnStep, htk, List.headD_nil, List.tail_nil, encList_cons, encList_nil,
        List.append_nil, length_frame, length_encRPNEntry, List.length_nil]
      omega
    | cons e₁ rest =>
      have hN := length_encRawFormula_neg e₁.formula
      simp only [rpnStep, htk, List.headD_cons, List.tail_cons, encList_cons, List.length_append,
        length_frame, length_encRPNEntry]
      omega
  · rcases s with _ | ⟨e₁, _ | ⟨e₂, rest⟩⟩
    · have hC := length_encRawFormula_conj .falsum .falsum
      simp only [rpnStep, htk, List.headD_nil, List.tail_nil, encList_cons, encList_nil,
        List.append_nil, length_frame, length_encRPNEntry, List.length_nil]
      omega
    · have hC := length_encRawFormula_conj e₁.formula .falsum
      simp only [rpnStep, htk, List.headD_cons, List.tail_cons, List.headD_nil, List.tail_nil,
        encList_cons, encList_nil, List.append_nil, length_frame, length_encRPNEntry]
      omega
    · have hC := length_encRawFormula_conj e₁.formula e₂.formula
      simp only [rpnStep, htk, List.headD_cons, List.tail_cons, encList_cons, List.length_append,
        length_frame, length_encRPNEntry, encList_append]
      omega
  · rcases s with _ | ⟨e₁, _ | ⟨e₂, rest⟩⟩
    · have hD := length_encRawFormula_disj .falsum .falsum
      simp only [rpnStep, htk, List.headD_nil, List.tail_nil, encList_cons, encList_nil,
        List.append_nil, length_frame, length_encRPNEntry, List.length_nil]
      omega
    · have hD := length_encRawFormula_disj e₁.formula .falsum
      simp only [rpnStep, htk, List.headD_cons, List.tail_cons, List.headD_nil, List.tail_nil,
        encList_cons, encList_nil, List.append_nil, length_frame, length_encRPNEntry]
      omega
    · have hD := length_encRawFormula_disj e₁.formula e₂.formula
      simp only [rpnStep, htk, List.headD_cons, List.tail_cons, encList_cons, List.length_append,
        length_frame, length_encRPNEntry, encList_append]
      omega
  · cases s with
    | nil =>
      have hexLen := hexBound .falsum
      simp only [rpnStep, htk, List.headD_nil, List.tail_nil, List.filter_nil, encList_cons,
        encList_nil, List.append_nil, length_frame, length_encRPNEntry, List.length_nil]
      omega
    | cons e₁ rest =>
      have hexLen := hexBound e₁.formula
      have hflt := length_encList_filter_le encNat (· != tok.2) e₁.freeVars
      simp only [rpnStep, htk, List.headD_cons, List.tail_cons, encList_cons, List.length_append,
        length_frame, length_encRPNEntry]
      omega
  · cases s with
    | nil =>
      have hallLen := hallBound .falsum
      simp only [rpnStep, htk, List.headD_nil, List.tail_nil, List.filter_nil, encList_cons,
        encList_nil, List.append_nil, length_frame, length_encRPNEntry, List.length_nil]
      omega
    | cons e₁ rest =>
      have hallLen := hallBound e₁.formula
      have hflt := length_encList_filter_le encNat (· != tok.2) e₁.freeVars
      simp only [rpnStep, htk, List.headD_cons, List.tail_cons, encList_cons, List.length_append,
        length_frame, length_encRPNEntry]
      omega

private theorem length_encNat_le_encQBF_of_mem_tokens {φ : QBF ℕ} {tok : QBF.Kind × ℕ}
    (htok : tok ∈ φ.tokens) : (encNat tok.2).length ≤ (encQBF φ).length := by
  have hmem := length_le_encList_of_mem TQBF.encToken htok
  have hp : (encNat tok.2).length ≤ (TQBF.encToken tok).length := by
    rw [TQBF.encToken, length_encPair]
    omega
  rw [encQBF_apply]
  exact hp.trans hmem

/-- **The two-class equivalence relativization `qbfToEquivRaw spec` is computable in polynomial
time.** -/
@[fun_prop]
theorem computableInPolyTime_qbfToEquivRaw (spec : EquivAtomSpec) :
    ComputableInPolyTime (qbfToEquivRaw spec) encQBF encRawFormula := by
  have htokId : ComputableInPolyTime QBF.tokens encQBF (encList TQBF.encToken) :=
    of_eq fun _ => rfl
  have htokens : ComputableInPolyTime (fun φ : QBF ℕ => φ.tokens.reverse)
      encQBF (encList TQBF.encToken) :=
    (listReverse TQBF.encToken).comp htokId
  let Cspec := 80 * (encRawFormula (spec.atom 0 1)).length + 2000
  have hfold : ComputableInPolyTime
      (fun φ : QBF ℕ => φ.tokens.reverse.foldl (rpnStep spec) []) encQBF encRPNStack :=
    foldlWith_of_bounded_growth (encP := encBool) (par := fun _ : QBF ℕ => false)
      (step := fun _ => rpnStep spec) (const false) htokens (const [])
      ((computableInPolyTime_rpnStep spec).comp
        (((fst (encPair encBool encRPNStack) TQBF.encToken).snd').prod (snd _ _)))
      (growth := fun φ => 80 * (encQBF φ).length + Cspec)
      (((PolyBounded.const 80).mul PolyBounded.self).add (.const Cspec))
      (fun φ s tok hmem => by
        have hlen := length_encNat_le_encQBF_of_mem_tokens (List.mem_reverse.mp hmem)
        have hgr := length_rpnStep_growth spec s tok
        dsimp only [encRPNStack, Cspec] at hgr ⊢
        linarith)
  have htopEntry : ComputableInPolyTime
      (fun φ : QBF ℕ => (φ.tokens.reverse.foldl (rpnStep spec) []).headD ⟨.falsum, []⟩)
      encQBF encRPNEntry :=
    listHeadDWithInput hfold (const ({ formula := .falsum, freeVars := [] } : RPNEntry))
  have hatom01 : ComputableInPolyTime (fun _ : QBF ℕ => spec.atom 0 1) encQBF encRawFormula :=
    const (spec.atom 0 1)
  have hfinal : ComputableInPolyTime
      (fun φ : QBF ℕ =>
        let top := (φ.tokens.reverse.foldl (rpnStep spec) []).headD ⟨.falsum, []⟩
        if top.freeVars.isEmpty then
          RawFormula.all 0 (RawFormula.all 1
            (RawFormula.imp (RawFormula.neg (spec.atom 0 1)) top.formula))
        else RawFormula.falsum) encQBF encRawFormula := by
    dsimp only
    fun_prop
  refine hfinal.of_enc_eq fun φ => ?_
  rw [foldl_rpnStep_tokens_reverse]
  rfl

/-- **The pure-equality reduction `qbfToPureEquality` is computable in polynomial time.** -/
@[fun_prop]
theorem computableInPolyTime_qbfToPureEquality :
    ComputableInPolyTime qbfToPureEquality encQBF encRawFormula :=
  computableInPolyTime_qbfToEquivRaw .pureEq

/-! ### Syntactic sentencehood and semantic correctness -/

theorem mem_freeVars_relativizeQBFRaw (spec : EquivAtomSpec) :
    ∀ (φ : QBF ℕ) {y : ℕ}, y ∈ (relativizeQBFRaw spec φ).freeVars →
      y = 0 ∨ y = 1 ∨ ∃ v ∈ φ.freeVars, y = v + 2
  | .var v, y, hy => by
    cases spec <;> simp only [relativizeQBFRaw, EquivAtomSpec.atom, RawFormula.freeVars,
      List.mem_cons, List.not_mem_nil, or_false] at hy
    · rcases hy with rfl | rfl
      · exact Or.inr (Or.inr ⟨v, by simp [QBF.freeVars], rfl⟩)
      · exact Or.inr (Or.inl rfl)
    · rcases hy with rfl | rfl
      · exact Or.inr (Or.inr ⟨v, by simp [QBF.freeVars], rfl⟩)
      · exact Or.inr (Or.inl rfl)
  | .top, y, hy => by simp [relativizeQBFRaw, RawFormula.verum, RawFormula.neg,
      RawFormula.freeVars] at hy
  | .bot, y, hy => by simp [relativizeQBFRaw, RawFormula.freeVars] at hy
  | .not φ, y, hy => by
    rw [relativizeQBFRaw, RawFormula.freeVars_neg] at hy
    exact mem_freeVars_relativizeQBFRaw spec φ hy
  | .and φ ψ, y, hy => by
    simp only [relativizeQBFRaw, RawFormula.conj, RawFormula.freeVars_neg, RawFormula.freeVars,
      List.mem_append] at hy
    rcases hy with hy | hy
    · rcases mem_freeVars_relativizeQBFRaw spec φ hy with rfl | rfl | ⟨v, hv, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨v, Finset.mem_union_left _ hv, rfl⟩)
    · rcases mem_freeVars_relativizeQBFRaw spec ψ hy with rfl | rfl | ⟨v, hv, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨v, Finset.mem_union_right _ hv, rfl⟩)
  | .or φ ψ, y, hy => by
    simp only [relativizeQBFRaw, RawFormula.disj, RawFormula.freeVars_neg, RawFormula.freeVars,
      List.mem_append] at hy
    rcases hy with hy | hy
    · rcases mem_freeVars_relativizeQBFRaw spec φ hy with rfl | rfl | ⟨v, hv, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨v, Finset.mem_union_left _ hv, rfl⟩)
    · rcases mem_freeVars_relativizeQBFRaw spec ψ hy with rfl | rfl | ⟨v, hv, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨v, Finset.mem_union_right _ hv, rfl⟩)
  | .ex v φ, y, hy => by
    rw [relativizeQBFRaw, RawFormula.ex, RawFormula.freeVars_neg, RawFormula.mem_freeVars_all,
      RawFormula.freeVars_neg] at hy
    simp only [RawFormula.conj, RawFormula.freeVars_neg, RawFormula.freeVars,
      List.mem_append] at hy
    obtain ⟨hy1 | hy2, hyne⟩ := hy
    · cases spec <;> simp only [inTwoClassesRaw, RawFormula.disj, EquivAtomSpec.atom,
        RawFormula.freeVars_neg, RawFormula.freeVars, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hy1 <;> omega
    · rcases mem_freeVars_relativizeQBFRaw spec φ hy2 with rfl | rfl | ⟨w, hw, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨w, Finset.mem_erase.mpr ⟨by omega, hw⟩, rfl⟩)
  | .all v φ, y, hy => by
    rw [relativizeQBFRaw, RawFormula.mem_freeVars_all] at hy
    simp only [RawFormula.freeVars, List.mem_append] at hy
    obtain ⟨hy1 | hy2, hyne⟩ := hy
    · cases spec <;> simp only [inTwoClassesRaw, RawFormula.disj, EquivAtomSpec.atom,
        RawFormula.freeVars_neg, RawFormula.freeVars, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hy1 <;> omega
    · rcases mem_freeVars_relativizeQBFRaw spec φ hy2 with rfl | rfl | ⟨w, hw, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨w, Finset.mem_erase.mpr ⟨by omega, hw⟩, rfl⟩)

theorem atoms_relativizeQBFRaw_subset (spec : EquivAtomSpec) :
    ∀ (φ : QBF ℕ) {a : ℕ × ℕ}, a ∈ (relativizeQBFRaw spec φ).atoms → a ∈ spec.vocab
  | .var _, _, ha => by
    cases spec <;> simp_all [relativizeQBFRaw, EquivAtomSpec.atom, RawFormula.atoms,
      EquivAtomSpec.vocab]
  | .top, _, ha => by simp [relativizeQBFRaw, RawFormula.verum, RawFormula.neg,
      RawFormula.atoms] at ha
  | .bot, _, ha => by simp [relativizeQBFRaw, RawFormula.atoms] at ha
  | .not φ, _, ha => by
    rw [relativizeQBFRaw, RawFormula.atoms_neg] at ha
    exact atoms_relativizeQBFRaw_subset spec φ ha
  | .and φ ψ, _, ha => by
    simp only [relativizeQBFRaw, RawFormula.conj, RawFormula.atoms_neg, RawFormula.atoms,
      List.mem_append] at ha
    exact ha.elim (atoms_relativizeQBFRaw_subset spec φ) (atoms_relativizeQBFRaw_subset spec ψ)
  | .or φ ψ, _, ha => by
    simp only [relativizeQBFRaw, RawFormula.disj, RawFormula.atoms_neg, RawFormula.atoms,
      List.mem_append] at ha
    exact ha.elim (atoms_relativizeQBFRaw_subset spec φ) (atoms_relativizeQBFRaw_subset spec ψ)
  | .ex _ φ, _, ha => by
    simp only [relativizeQBFRaw, RawFormula.ex, RawFormula.atoms_neg, RawFormula.atoms,
      RawFormula.conj, List.mem_append] at ha
    rcases ha with ha | ha
    · cases spec <;> simp_all [inTwoClassesRaw, RawFormula.disj, EquivAtomSpec.atom,
        RawFormula.atoms_neg, RawFormula.atoms, EquivAtomSpec.vocab]
    · exact atoms_relativizeQBFRaw_subset spec φ ha
  | .all _ φ, _, ha => by
    simp only [relativizeQBFRaw, RawFormula.atoms, List.mem_append] at ha
    rcases ha with ha | ha
    · cases spec <;> simp_all [inTwoClassesRaw, RawFormula.disj, EquivAtomSpec.atom,
        RawFormula.atoms_neg, RawFormula.atoms, EquivAtomSpec.vocab]
    · exact atoms_relativizeQBFRaw_subset spec φ ha

/-- `qbfToEquivRaw spec φ` is always a closed sentence over `spec.vocab`. -/
theorem isSentenceOver_qbfToEquivRaw (spec : EquivAtomSpec) (φ : QBF ℕ) :
    (qbfToEquivRaw spec φ).IsSentenceOver spec.vocab := by
  unfold qbfToEquivRaw
  by_cases h : (qbfFreeVarsList φ).isEmpty = true
  · simp only [h, ↓reduceIte]
    have hcl : φ.Closed := (qbfFreeVarsList_isEmpty_iff φ).mp h
    refine ⟨List.eq_nil_iff_forall_not_mem.mpr fun y hy => ?_, fun a ha => ?_⟩
    · rw [RawFormula.mem_freeVars_all, RawFormula.mem_freeVars_all] at hy
      simp only [RawFormula.freeVars, RawFormula.freeVars_neg, List.mem_append] at hy
      obtain ⟨⟨hy1 | hy2, hy1ne⟩, hy0ne⟩ := hy
      · cases spec <;> simp only [EquivAtomSpec.atom, RawFormula.freeVars, List.mem_cons,
          List.not_mem_nil, or_false] at hy1 <;> omega
      · rcases mem_freeVars_relativizeQBFRaw spec φ hy2 with rfl | rfl | ⟨v, hv, rfl⟩
        · exact hy0ne rfl
        · exact hy1ne rfl
        · rw [hcl] at hv
          exact Finset.notMem_empty v hv
    · simp only [RawFormula.atoms, RawFormula.atoms_neg, List.mem_append] at ha
      rcases ha with ha | ha
      · cases spec <;> simp_all [EquivAtomSpec.atom, RawFormula.atoms, EquivAtomSpec.vocab]
      · exact atoms_relativizeQBFRaw_subset spec φ ha
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact ⟨rfl, fun _ ha => by simp [RawFormula.atoms] at ha⟩

/-- Semantic coupling theorem for `relativizeQBFRaw`: whenever `spec.Rel I` is an equivalence
relation on `M` and `¬spec.Rel I (v 0) (v 1)`, `relativizeQBFRaw spec φ` holds under `v` iff
`φ.eval σ = true`. -/
theorem realize_relativizeQBFRaw_iff {M : Type*} {spec : EquivAtomSpec} {I : ℕ → List M → Prop}
    (hEqv : Equivalence (spec.Rel I)) (φ : QBF ℕ) {v : ℕ → M} {σ : ℕ → Bool}
    (hne : ¬spec.Rel I (v 0) (v 1))
    (hcoupl : ∀ x ∈ φ.freeVars, spec.Rel I (v (x + 2)) (cond (σ x) (v 1) (v 0))) :
    (relativizeQBFRaw spec φ).Realize I v ↔ φ.eval σ = true := by
  induction φ generalizing v σ with
  | var x =>
    have hx := hcoupl x (by simp [QBF.freeVars])
    rw [relativizeQBFRaw, EquivAtomSpec.realize_atom, QBF.eval_var]
    cases hσ : σ x
    · simp only [hσ, Bool.cond_false] at hx ⊢
      exact ⟨fun h1 => False.elim (hne (hEqv.trans (hEqv.symm hx) h1)), Bool.noConfusion⟩
    · simp only [hσ, Bool.cond_true] at hx ⊢
      exact ⟨fun _ => trivial, fun _ => hx⟩
  | top => simp [relativizeQBFRaw]
  | bot => simp [relativizeQBFRaw]
  | not φ ih =>
    rw [relativizeQBFRaw, RawFormula.realize_neg, ih hne hcoupl, QBF.eval_not, Bool.not_eq_true']
    cases φ.eval σ <;> simp
  | and φ ψ ihφ ihψ =>
    simp [relativizeQBFRaw, ihφ hne fun x hx => hcoupl x (Finset.mem_union_left _ hx),
      ihψ hne fun x hx => hcoupl x (Finset.mem_union_right _ hx)]
  | or φ ψ ihφ ihψ =>
    simp [relativizeQBFRaw, ihφ hne fun x hx => hcoupl x (Finset.mem_union_left _ hx),
      ihψ hne fun x hx => hcoupl x (Finset.mem_union_right _ hx)]
  | ex x φ ih =>
    simp only [relativizeQBFRaw, inTwoClassesRaw, RawFormula.realize_ex, RawFormula.realize_conj,
      RawFormula.realize_disj, EquivAtomSpec.realize_atom, Function.update_self,
      Function.update_of_ne (show (0 : ℕ) ≠ x + 2 by omega),
      Function.update_of_ne (show (1 : ℕ) ≠ x + 2 by omega), QBF.eval_ex_eq_true_iff]
    have hne' (m : M) :
        ¬spec.Rel I (Function.update v (x + 2) m 0) (Function.update v (x + 2) m 1) := by
      simpa [Function.update_of_ne (show (0 : ℕ) ≠ x + 2 by omega),
        Function.update_of_ne (show (1 : ℕ) ≠ x + 2 by omega)] using hne
    constructor
    · rintro ⟨m, hm0 | hm1, hreal⟩
      · refine ⟨false, (ih (hne' m) ?_).mp hreal⟩
        intro y hy
        rcases eq_or_ne y x with rfl | hyx
        · simpa [Function.update_of_ne (show (0 : ℕ) ≠ y + 2 by omega),
            Function.update_of_ne (show (1 : ℕ) ≠ y + 2 by omega)] using hm0
        · simpa [hyx, show y + 2 ≠ x + 2 by omega,
            Function.update_of_ne (show (0 : ℕ) ≠ x + 2 by omega),
            Function.update_of_ne (show (1 : ℕ) ≠ x + 2 by omega)] using
            hcoupl y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
      · refine ⟨true, (ih (hne' m) ?_).mp hreal⟩
        intro y hy
        rcases eq_or_ne y x with rfl | hyx
        · simpa [Function.update_of_ne (show (0 : ℕ) ≠ y + 2 by omega),
            Function.update_of_ne (show (1 : ℕ) ≠ y + 2 by omega)] using hm1
        · simpa [hyx, show y + 2 ≠ x + 2 by omega,
            Function.update_of_ne (show (0 : ℕ) ≠ x + 2 by omega),
            Function.update_of_ne (show (1 : ℕ) ≠ x + 2 by omega)] using
            hcoupl y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
    · rintro ⟨b, hb⟩
      let m := cond b (v 1) (v 0)
      refine ⟨m, ?_, (ih (hne' m) ?_).mpr hb⟩
      · cases b
        · exact Or.inl (hEqv.refl _)
        · exact Or.inr (hEqv.refl _)
      · intro y hy
        rcases eq_or_ne y x with rfl | hyx
        · simp [m, hEqv.refl]
        · simpa [hyx, show y + 2 ≠ x + 2 by omega,
            Function.update_of_ne (show (0 : ℕ) ≠ x + 2 by omega),
            Function.update_of_ne (show (1 : ℕ) ≠ x + 2 by omega)] using
            hcoupl y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
  | all x φ ih =>
    simp only [relativizeQBFRaw, inTwoClassesRaw, RawFormula.realize_all, RawFormula.realize_imp,
      RawFormula.realize_disj, EquivAtomSpec.realize_atom, Function.update_self,
      Function.update_of_ne (show (0 : ℕ) ≠ x + 2 by omega),
      Function.update_of_ne (show (1 : ℕ) ≠ x + 2 by omega), QBF.eval_all_eq_true_iff]
    have hne' (m : M) :
        ¬spec.Rel I (Function.update v (x + 2) m 0) (Function.update v (x + 2) m 1) := by
      simpa [Function.update_of_ne (show (0 : ℕ) ≠ x + 2 by omega),
        Function.update_of_ne (show (1 : ℕ) ≠ x + 2 by omega)] using hne
    constructor
    · intro hall b
      let m := cond b (v 1) (v 0)
      refine (ih (hne' m) ?_).mp (hall m ?_)
      · intro y hy
        rcases eq_or_ne y x with rfl | hyx
        · simp [m, hEqv.refl]
        · simpa [hyx, show y + 2 ≠ x + 2 by omega,
            Function.update_of_ne (show (0 : ℕ) ≠ x + 2 by omega),
            Function.update_of_ne (show (1 : ℕ) ≠ x + 2 by omega)] using
            hcoupl y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
      · cases b
        · exact Or.inl (hEqv.refl _)
        · exact Or.inr (hEqv.refl _)
    · intro hall m hm
      rcases hm with hm0 | hm1
      · refine (ih (hne' m) ?_).mpr (hall false)
        intro y hy
        rcases eq_or_ne y x with rfl | hyx
        · simpa [Function.update_of_ne (show (0 : ℕ) ≠ y + 2 by omega),
            Function.update_of_ne (show (1 : ℕ) ≠ y + 2 by omega)] using hm0
        · simpa [hyx, show y + 2 ≠ x + 2 by omega,
            Function.update_of_ne (show (0 : ℕ) ≠ x + 2 by omega),
            Function.update_of_ne (show (1 : ℕ) ≠ x + 2 by omega)] using
            hcoupl y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
      · refine (ih (hne' m) ?_).mpr (hall true)
        intro y hy
        rcases eq_or_ne y x with rfl | hyx
        · simpa [Function.update_of_ne (show (0 : ℕ) ≠ y + 2 by omega),
            Function.update_of_ne (show (1 : ℕ) ≠ y + 2 by omega)] using hm1
        · simpa [hyx, show y + 2 ≠ x + 2 by omega,
            Function.update_of_ne (show (0 : ℕ) ≠ x + 2 by omega),
            Function.update_of_ne (show (1 : ℕ) ≠ x + 2 by omega)] using
            hcoupl y (Finset.mem_erase.mpr ⟨hyx, hy⟩)

/-- Forward soundness on **every** equivalence structure (even 1-class structures): if `φ ∈ TQBF`,
then `qbfToEquivRaw spec φ` holds in `(M, I)` under every valuation `v`. -/
theorem realize_qbfToEquivRaw_of_mem_TQBF {M : Type*} {spec : EquivAtomSpec}
    {I : ℕ → List M → Prop} (hEqv : Equivalence (spec.Rel I)) {φ : QBF ℕ} (hφ : φ ∈ TQBF)
    (v : ℕ → M) : (qbfToEquivRaw spec φ).Realize I v := by
  obtain ⟨hcl, heval⟩ := hφ
  have hemp : (qbfFreeVarsList φ).isEmpty = true := (qbfFreeVarsList_isEmpty_iff φ).mpr hcl
  simp only [qbfToEquivRaw, hemp, ↓reduceIte, RawFormula.realize_all, RawFormula.realize_imp,
    RawFormula.realize_neg, EquivAtomSpec.realize_atom]
  intro m₀ m₁ hne
  have hne' : ¬spec.Rel I
      (Function.update (Function.update v 0 m₀) 1 m₁ 0)
      (Function.update (Function.update v 0 m₀) 1 m₁ 1) := by
    simpa using hne
  exact (realize_relativizeQBFRaw_iff hEqv φ hne' fun x hx => by
    rw [hcl] at hx
    exact absurd hx (Finset.notMem_empty x)).mpr heval

/-- Reverse completeness on any `spec.Rel I`-nontrivial equivalence structure: if
`qbfToEquivRaw spec φ` holds in `(M, I)` and `∃ c₀ c₁ : M, ¬spec.Rel I c₀ c₁`, then `φ ∈ TQBF`. -/
theorem mem_TQBF_of_realize_qbfToEquivRaw {M : Type*} {spec : EquivAtomSpec}
    {I : ℕ → List M → Prop} (hEqv : Equivalence (spec.Rel I)) {c₀ c₁ : M}
    (hne : ¬spec.Rel I c₀ c₁) {φ : QBF ℕ} {v : ℕ → M}
    (hreal : (qbfToEquivRaw spec φ).Realize I v) : φ ∈ TQBF := by
  unfold qbfToEquivRaw at hreal
  by_cases hemp : (qbfFreeVarsList φ).isEmpty = true
  · have hcl : φ.Closed := (qbfFreeVarsList_isEmpty_iff φ).mp hemp
    simp only [hemp, ↓reduceIte, RawFormula.realize_all, RawFormula.realize_imp,
      RawFormula.realize_neg, EquivAtomSpec.realize_atom] at hreal
    have hne' : ¬spec.Rel I
        (Function.update (Function.update v 0 c₀) 1 c₁ 0)
        (Function.update (Function.update v 0 c₀) 1 c₁ 1) := by
      simpa using hne
    have hbody := hreal c₀ c₁ hne'
    exact ⟨hcl, (realize_relativizeQBFRaw_iff hEqv φ hne' fun x hx => by
      rw [hcl] at hx
      exact absurd hx (Finset.notMem_empty x)).mp hbody⟩
  · simp [hemp] at hreal

/-! ### `PSPACE`-hardness of pure equality and equivalence-nontrivial theories -/

/-- Closed pure-equality sentences valid in every nonempty domain `M : Type`. -/
def PureEqualityValid : Set RawFormula :=
  {φ | φ.IsSentenceOver ∅ ∧
    ∀ (M : Type) [Nonempty M] (v : ℕ → M), φ.Realize (fun _ _ => False) v}

theorem mem_TQBF_iff_qbfToPureEquality_mem_valid (φ : QBF ℕ) :
    φ ∈ TQBF ↔ qbfToPureEquality φ ∈ PureEqualityValid := by
  constructor
  · intro hφ
    refine ⟨isSentenceOver_qbfToEquivRaw .pureEq φ, fun M _ v => ?_⟩
    exact realize_qbfToEquivRaw_of_mem_TQBF (spec := .pureEq) (I := fun _ _ => False)
      eq_equivalence hφ v
  · intro ⟨_, hval⟩
    exact mem_TQBF_of_realize_qbfToEquivRaw (M := Bool) (spec := .pureEq)
      (I := fun _ _ => False) eq_equivalence (c₀ := false) (c₁ := true) Bool.false_ne_true
      (hval Bool (fun _ => false))

/-- **`TQBF` reduces to `PureEqualityValid` in polynomial time.** -/
theorem polyTimeReducible_TQBF_PureEqualityValid :
    PolyTimeReducible encQBF encRawFormula TQBF PureEqualityValid :=
  ⟨qbfToPureEquality, computableInPolyTime_qbfToPureEquality,
    mem_TQBF_iff_qbfToPureEquality_mem_valid⟩

/-- **The first-order theory of pure equality is `PSPACE`-hard.** -/
theorem PureEqualityValid_pspaceHard : PSPACEHard encRawFormula PureEqualityValid :=
  TQBF_pspaceHard.trans polyTimeReducible_TQBF_PureEqualityValid

/-- General criterion: a set `T : Set RawFormula` of raw sentences is `spec`-equivalence-nontrivial
when `T` contains every closed `spec.vocab`-sentence valid on all `spec`-equivalence structures and
admits at least one `spec`-nontrivial model `(M, I)`. -/
def IsEquivNontrivialRawTheory (spec : EquivAtomSpec) (T : Set RawFormula) : Prop :=
  (∀ φ : RawFormula, φ.IsSentenceOver spec.vocab →
    (∀ (M : Type) (I : ℕ → List M → Prop), Equivalence (spec.Rel I) →
      ∀ v : ℕ → M, φ.Realize I v) → φ ∈ T) ∧
  ∃ (M : Type) (I : ℕ → List M → Prop),
    Equivalence (spec.Rel I) ∧ (∃ c₀ c₁ : M, ¬spec.Rel I c₀ c₁) ∧
      ∀ φ ∈ T, φ.IsSentenceOver spec.vocab → ∀ v : ℕ → M, φ.Realize I v

theorem polyTimeReducible_TQBF_of_equivNontrivialRaw {spec : EquivAtomSpec} {T : Set RawFormula}
    (hT : IsEquivNontrivialRawTheory spec T) :
    PolyTimeReducible encQBF encRawFormula TQBF T := by
  refine ⟨qbfToEquivRaw spec, computableInPolyTime_qbfToEquivRaw spec, fun φ => ?_⟩
  have hsent := isSentenceOver_qbfToEquivRaw spec φ
  constructor
  · intro hφ
    exact hT.1 _ hsent fun M I hEqv v => realize_qbfToEquivRaw_of_mem_TQBF hEqv hφ v
  · intro hmem
    obtain ⟨M, I, hEqv, ⟨c₀, c₁, hne⟩, hmod⟩ := hT.2
    exact mem_TQBF_of_realize_qbfToEquivRaw hEqv hne (hmod _ hmem hsent (fun _ => c₀))

/-- **Every equivalence-nontrivial raw first-order theory is `PSPACE`-hard.** -/
theorem pspaceHard_of_equivNontrivialRaw {spec : EquivAtomSpec} {T : Set RawFormula}
    (hT : IsEquivNontrivialRawTheory spec T) :
    PSPACEHard encRawFormula T :=
  TQBF_pspaceHard.trans (polyTimeReducible_TQBF_of_equivNontrivialRaw hT)

end CslibFrontier.Complexity
