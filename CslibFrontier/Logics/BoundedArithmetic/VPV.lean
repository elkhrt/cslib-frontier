module

public import Mathlib.ModelTheory.Satisfiability
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size

/-!
# The Two-Sorted Bounded Arithmetic Theory `VPV`

This module formalizes the syntax, semantics, and axioms of the two-sorted bounded arithmetic
theory `VPV` for polynomial-time reasoning: typed de Bruijn syntax for base polynomial number
terms `ℒ_A^2`, polynomial-time function terms `ℒ_FP` (closed under `Σ₀ᴮ`-comprehension, bounded
minimization, and Cobham limited recursion with `ℒ_A^2` length bounds), and bounded formulas
`Σ₀ᴮ(ℒ_FP)`.

## Main definitions

* `CslibFrontier.Logics.BoundedArithmetic.Sort2`: the two sorts (unary numbers and finite binary
  strings).
* `CslibFrontier.Logics.BoundedArithmetic.L2NumTerm`: base `ℒ_A^2` polynomial number terms
  (`0, 1, +, ·, |X|`).
* `CslibFrontier.Logics.BoundedArithmetic.LFPNumTerm`, `LFPStrTerm`, `Sigma0BFormula`, `TermEnv`:
  the mutually inductive syntax of `ℒ_FP` terms and `Σ₀ᴮ(ℒ_FP)` bounded formulas.
* `CslibFrontier.Logics.BoundedArithmetic.VPVModel`: a two-sorted model of `VPV` satisfying all 15
  `2-BASIC` axioms (`B1`–`B12`, `L1`, `L2`, `SE`) together with the defining axioms for `compStr`,
  `minNum`, and Cobham `limRec`.
* `CslibFrontier.Logics.BoundedArithmetic.standardVPVModel`: the standard model `(ℕ, ℕ)`
  (bitstrings via `Nat.testBit` and `Nat.size`), witnessing non-vacuity of `VPVModel`.
* `CslibFrontier.Logics.BoundedArithmetic.vpvLang`, `vpvStructureSatisfies`: encoding of `VPV` as
  a Mathlib `FirstOrder.Language` with `VPVModel.ofFirstOrderStructure`.

## Main results

* `CslibFrontier.Logics.BoundedArithmetic.VPVModel.sigma0B_ind_raw`: `Σ₀ᴮ(ℒ_FP)`-induction derived
  from `2-BASIC` and `minNum`.
* `CslibFrontier.Logics.BoundedArithmetic.VPVModel.le_trans`: transitivity of `≤` in any model of
  `VPV`.
* `CslibFrontier.Logics.BoundedArithmetic.VPVModel.str_ext`: full bit-extensionality in any model
  of `VPV`.
-/

public section

namespace CslibFrontier.Logics.BoundedArithmetic

universe u

/-! ### 1. Two-Sorted Syntax of `ℒ_A^2`, `ℒ_FP`, and `Σ₀ᴮ(ℒ_FP)` -/

/-- The two sorts of two-sorted bounded arithmetic: unary numbers and binary strings. -/
inductive Sort2 : Type
  | num
  | str
  deriving DecidableEq, Repr

/-- Typed de Bruijn variable into a two-sorted context `Γ`. -/
inductive Var : List Sort2 → Sort2 → Type
  | here {s : Sort2} {Γ : List Sort2} : Var (s :: Γ) s
  | there {s t : Sort2} {Γ : List Sort2} : Var Γ s → Var (t :: Γ) s
  deriving DecidableEq, Repr

/-- Number terms in the base two-sorted language `ℒ_A^2` (`0, 1, +, ·, |X|`).
Used strictly as polynomial length bounds in Cobham's limited recursion. -/
inductive L2NumTerm : List Sort2 → Type
  | var {Γ : List Sort2} : Var Γ .num → L2NumTerm Γ
  | zero {Γ : List Sort2} : L2NumTerm Γ
  | one {Γ : List Sort2} : L2NumTerm Γ
  | add {Γ : List Sort2} : L2NumTerm Γ → L2NumTerm Γ → L2NumTerm Γ
  | mul {Γ : List Sort2} : L2NumTerm Γ → L2NumTerm Γ → L2NumTerm Γ
  | len {Γ : List Sort2} : Var Γ .str → L2NumTerm Γ

mutual

/-- Number-valued terms in the vocabulary `ℒ_FP` of `VPV`. -/
inductive LFPNumTerm : List Sort2 → Type
  | var {Γ : List Sort2} : Var Γ .num → LFPNumTerm Γ
  | zero {Γ : List Sort2} : LFPNumTerm Γ
  | one {Γ : List Sort2} : LFPNumTerm Γ
  | add {Γ : List Sort2} : LFPNumTerm Γ → LFPNumTerm Γ → LFPNumTerm Γ
  | mul {Γ : List Sort2} : LFPNumTerm Γ → LFPNumTerm Γ → LFPNumTerm Γ
  | len {Γ : List Sort2} : LFPStrTerm Γ → LFPNumTerm Γ
  | minNum {Γ Δ : List Sort2} :
      LFPNumTerm Δ → Sigma0BFormula (.num :: Δ) → TermEnv Γ Δ → LFPNumTerm Γ

/-- String-valued terms in the vocabulary `ℒ_FP` of `VPV`, closed under `Σ₀ᴮ`-comprehension
and Cobham's limited recursion bounded by `ℒ_A^2` terms. -/
inductive LFPStrTerm : List Sort2 → Type
  | svar {Γ : List Sort2} : Var Γ .str → LFPStrTerm Γ
  | compStr {Γ Δ : List Sort2} :
      LFPNumTerm Δ → Sigma0BFormula (.num :: Δ) → TermEnv Γ Δ → LFPStrTerm Γ
  | limRec {Γ Δ : List Sort2} :
      LFPStrTerm Δ → LFPStrTerm (.num :: .str :: Δ) → L2NumTerm (.num :: Δ) →
      LFPNumTerm Γ → TermEnv Γ Δ → LFPStrTerm Γ

/-- Bounded quantifier formulas `Σ₀ᴮ(ℒ_FP)` with no string quantifiers. -/
inductive Sigma0BFormula : List Sort2 → Type
  | eqNum {Γ : List Sort2} : LFPNumTerm Γ → LFPNumTerm Γ → Sigma0BFormula Γ
  | eqStr {Γ : List Sort2} : LFPStrTerm Γ → LFPStrTerm Γ → Sigma0BFormula Γ
  | leNum {Γ : List Sort2} : LFPNumTerm Γ → LFPNumTerm Γ → Sigma0BFormula Γ
  | bit {Γ : List Sort2} : LFPStrTerm Γ → LFPNumTerm Γ → Sigma0BFormula Γ
  | not {Γ : List Sort2} : Sigma0BFormula Γ → Sigma0BFormula Γ
  | and {Γ : List Sort2} : Sigma0BFormula Γ → Sigma0BFormula Γ → Sigma0BFormula Γ
  | or {Γ : List Sort2} : Sigma0BFormula Γ → Sigma0BFormula Γ → Sigma0BFormula Γ
  | imp {Γ : List Sort2} : Sigma0BFormula Γ → Sigma0BFormula Γ → Sigma0BFormula Γ
  | bAll {Γ : List Sort2} : LFPNumTerm Γ → Sigma0BFormula (.num :: Γ) → Sigma0BFormula Γ
  | bEx {Γ : List Sort2} : LFPNumTerm Γ → Sigma0BFormula (.num :: Γ) → Sigma0BFormula Γ

/-- Simultaneous term substitution / argument tuple mapping variables of `Δ` to terms in `Γ`. -/
inductive TermEnv : List Sort2 → List Sort2 → Type
  | nil {Γ : List Sort2} : TermEnv Γ []
  | consNum {Γ Δ : List Sort2} : LFPNumTerm Γ → TermEnv Γ Δ → TermEnv Γ (.num :: Δ)
  | consStr {Γ Δ : List Sort2} : LFPStrTerm Γ → TermEnv Γ Δ → TermEnv Γ (.str :: Δ)

end

/-- Context renaming map from `Γ` to `Δ`. -/
@[ext]
structure Ren (Γ Δ : List Sort2) : Type where
  /-- Underlying variable renaming. -/
  map : ∀ {s : Sort2}, Var Γ s → Var Δ s

/-- Lift a renaming under a single bound variable of sort `t`. -/
@[expose] def Ren.lift {Γ Δ : List Sort2} {t : Sort2} (r : Ren Γ Δ) : Ren (t :: Γ) (t :: Δ) where
  map := fun {s} v => match v with
    | .here => .here
    | .there w => .there (r.map w)

/-- Weakening renaming `Γ → t :: Γ`. -/
@[expose] def Ren.wk {Γ : List Sort2} {t : Sort2} : Ren Γ (t :: Γ) where
  map := fun v => .there v

/-- Embed a variable from the left prefix `Γ` into `Γ ++ Δ`. -/
@[expose] def Var.inl {Γ Δ : List Sort2} {s : Sort2} : Var Γ s → Var (Γ ++ Δ) s
  | .here => .here
  | .there v => .there (Var.inl v)

/-- Embed a variable from the right suffix `Δ` into `Γ ++ Δ`. -/
@[expose] def Var.inr : {Γ Δ : List Sort2} → {s : Sort2} → Var Δ s → Var (Γ ++ Δ) s
  | [], _, _, v => v
  | _ :: _, _, _, v => .there (Var.inr v)

/-- Renaming embedding `Γ` into `Γ ++ Δ`. -/
@[expose] def Ren.inl {Γ Δ : List Sort2} : Ren Γ (Γ ++ Δ) where
  map := Var.inl

/-- Renaming embedding `Δ` into `Γ ++ Δ`. -/
@[expose] def Ren.inr {Γ Δ : List Sort2} : Ren Δ (Γ ++ Δ) where
  map := Var.inr

/-- Rename free variables in an `ℒ_A^2` term. -/
def L2NumTerm.ren {Γ Δ : List Sort2} (r : Ren Γ Δ) : L2NumTerm Γ → L2NumTerm Δ
  | .var v => .var (r.map v)
  | .zero => .zero
  | .one => .one
  | .add a b => .add (a.ren r) (b.ren r)
  | .mul a b => .mul (a.ren r) (b.ren r)
  | .len v => .len (r.map v)

mutual

/-- Rename free variables in an `ℒ_FP` number term. -/
def LFPNumTerm.ren {Γ Δ : List Sort2} (r : Ren Γ Δ) : LFPNumTerm Γ → LFPNumTerm Δ
  | .var v => .var (r.map v)
  | .zero => .zero
  | .one => .one
  | .add a b => .add (a.ren r) (b.ren r)
  | .mul a b => .mul (a.ren r) (b.ren r)
  | .len T => .len (T.ren r)
  | .minNum t φ args => .minNum t φ (args.ren r)

/-- Rename free variables in an `ℒ_FP` string term. -/
def LFPStrTerm.ren {Γ Δ : List Sort2} (r : Ren Γ Δ) : LFPStrTerm Γ → LFPStrTerm Δ
  | .svar v => .svar (r.map v)
  | .compStr t φ args => .compStr t φ (args.ren r)
  | .limRec G H t y args => .limRec G H t (y.ren r) (args.ren r)

/-- Rename free variables in a `Σ₀ᴮ(ℒ_FP)` formula. -/
def Sigma0BFormula.ren {Γ Δ : List Sort2} (r : Ren Γ Δ) : Sigma0BFormula Γ → Sigma0BFormula Δ
  | .eqNum a b => .eqNum (a.ren r) (b.ren r)
  | .eqStr T U => .eqStr (T.ren r) (U.ren r)
  | .leNum a b => .leNum (a.ren r) (b.ren r)
  | .bit T a => .bit (T.ren r) (a.ren r)
  | .not φ => .not (φ.ren r)
  | .and φ ψ => .and (φ.ren r) (ψ.ren r)
  | .or φ ψ => .or (φ.ren r) (ψ.ren r)
  | .imp φ ψ => .imp (φ.ren r) (ψ.ren r)
  | .bAll t φ => .bAll (t.ren r) (φ.ren r.lift)
  | .bEx t φ => .bEx (t.ren r) (φ.ren r.lift)

/-- Rename free variables in a term environment. -/
def TermEnv.ren {Γ Γ' Δ : List Sort2} (r : Ren Γ Γ') : TermEnv Γ Δ → TermEnv Γ' Δ
  | .nil => .nil
  | .consNum t σ => .consNum (t.ren r) (σ.ren r)
  | .consStr T σ => .consStr (T.ren r) (σ.ren r)

end

/-- Identity term environment for any context `Γ`. -/
def TermEnv.id : (Γ : List Sort2) → TermEnv Γ Γ
  | [] => .nil
  | .num :: Γ => .consNum (.var .here) ((TermEnv.id Γ).ren Ren.wk)
  | .str :: Γ => .consStr (.svar .here) ((TermEnv.id Γ).ren Ren.wk)

/-- Lift a term substitution under a bound number variable. -/
def TermEnv.liftNum {Γ Δ : List Sort2} (σ : TermEnv Γ Δ) : TermEnv (.num :: Γ) (.num :: Δ) :=
  .consNum (.var .here) (σ.ren Ren.wk)

/-- Look up a number variable in a term substitution. -/
def TermEnv.lookupNum {Γ : List Sort2} : {Δ : List Sort2} → TermEnv Γ Δ → Var Δ .num → LFPNumTerm Γ
  | .num :: _, .consNum t _, .here => t
  | .num :: _, .consNum _ σ, .there v => σ.lookupNum v
  | .str :: _, .consStr _ σ, .there v => σ.lookupNum v

/-- Look up a string variable in a term substitution. -/
def TermEnv.lookupStr {Γ : List Sort2} : {Δ : List Sort2} → TermEnv Γ Δ → Var Δ .str → LFPStrTerm Γ
  | .str :: _, .consStr T _, .here => T
  | .num :: _, .consNum _ σ, .there v => σ.lookupStr v
  | .str :: _, .consStr _ σ, .there v => σ.lookupStr v

mutual

/-- Simultaneous substitution on `ℒ_FP` number terms. -/
def LFPNumTerm.subst {Γ Δ : List Sort2} (σ : TermEnv Γ Δ) : LFPNumTerm Δ → LFPNumTerm Γ
  | .var v => σ.lookupNum v
  | .zero => .zero
  | .one => .one
  | .add a b => .add (a.subst σ) (b.subst σ)
  | .mul a b => .mul (a.subst σ) (b.subst σ)
  | .len T => .len (T.subst σ)
  | .minNum t φ args => .minNum t φ (args.comp σ)

/-- Simultaneous substitution on `ℒ_FP` string terms. -/
def LFPStrTerm.subst {Γ Δ : List Sort2} (σ : TermEnv Γ Δ) : LFPStrTerm Δ → LFPStrTerm Γ
  | .svar v => σ.lookupStr v
  | .compStr t φ args => .compStr t φ (args.comp σ)
  | .limRec G H t y args => .limRec G H t (y.subst σ) (args.comp σ)

/-- Simultaneous substitution on `Σ₀ᴮ(ℒ_FP)` formulas. -/
def Sigma0BFormula.subst {Γ Δ : List Sort2} (σ : TermEnv Γ Δ) :
    Sigma0BFormula Δ → Sigma0BFormula Γ
  | .eqNum a b => .eqNum (a.subst σ) (b.subst σ)
  | .eqStr T U => .eqStr (T.subst σ) (U.subst σ)
  | .leNum a b => .leNum (a.subst σ) (b.subst σ)
  | .bit T a => .bit (T.subst σ) (a.subst σ)
  | .not φ => .not (φ.subst σ)
  | .and φ ψ => .and (φ.subst σ) (ψ.subst σ)
  | .or φ ψ => .or (φ.subst σ) (ψ.subst σ)
  | .imp φ ψ => .imp (φ.subst σ) (ψ.subst σ)
  | .bAll t φ => .bAll (t.subst σ) (φ.subst σ.liftNum)
  | .bEx t φ => .bEx (t.subst σ) (φ.subst σ.liftNum)

/-- Compose two term environments. -/
def TermEnv.comp {Γ Δ Θ : List Sort2} (τ : TermEnv Δ Θ) (σ : TermEnv Γ Δ) : TermEnv Γ Θ :=
  match τ with
  | .nil => .nil
  | .consNum t τ' => .consNum (t.subst σ) (τ'.comp σ)
  | .consStr T τ' => .consStr (T.subst σ) (τ'.comp σ)

end

/-! ### 2. Two-Sorted Interpretations and Semantics -/

/-- Carrier type for a sort `s` given number sort `N` and string sort `S`. -/
@[expose] def SortCarrier (N S : Type u) : Sort2 → Type u
  | .num => N
  | .str => S

/-- Environment assigning values in `(N, S)` to all variables in context `Γ`. -/
@[ext]
structure Env (N S : Type u) (Γ : List Sort2) : Type u where
  /-- Lookup function for variables in `Γ`. -/
  get : ∀ {s : Sort2}, Var Γ s → SortCarrier N S s

/-- Empty environment. -/
@[expose] def Env.nil {N S : Type u} : Env N S [] where
  get := fun v => nomatch v

/-- Look up a number variable in an environment. -/
@[expose] def Env.num {N S : Type u} {Γ : List Sort2}
    (ρ : Env N S Γ) (v : Var Γ .num) : N := ρ.get v

/-- Look up a string variable in an environment. -/
@[expose] def Env.str {N S : Type u} {Γ : List Sort2}
    (ρ : Env N S Γ) (v : Var Γ .str) : S := ρ.get v

/-- Extend an environment with a number variable. -/
@[expose] def Env.consNum {N S : Type u} {Γ : List Sort2}
    (x : N) (ρ : Env N S Γ) : Env N S (.num :: Γ) where
  get := fun {s} v => match v with
    | .here => x
    | .there w => ρ.get w

/-- Extend an environment with a string variable. -/
@[expose] def Env.consStr {N S : Type u} {Γ : List Sort2}
    (X : S) (ρ : Env N S Γ) : Env N S (.str :: Γ) where
  get := fun {s} v => match v with
    | .here => X
    | .there w => ρ.get w

/-- Pull back an environment along a context renaming. -/
@[expose] def Env.pull {N S : Type u} {Γ Δ : List Sort2}
    (r : Ren Γ Δ) (ρ : Env N S Δ) : Env N S Γ where
  get := fun v => ρ.get (r.map v)

/-- Drop the head variable from an environment. -/
@[expose] def Env.tail {N S : Type u} {t : Sort2} {Γ : List Sort2}
    (ρ : Env N S (t :: Γ)) : Env N S Γ :=
  Env.pull Ren.wk ρ

/-- Concatenate two environments over `Γ` and `Δ`. -/
@[expose] def Env.append {N S : Type u} :
    {Γ Δ : List Sort2} → Env N S Γ → Env N S Δ → Env N S (Γ ++ Δ)
  | [], _, _, ρ₂ => ρ₂
  | .num :: _, _, ρ₁, ρ₂ => Env.consNum (ρ₁.num .here) (Env.append ρ₁.tail ρ₂)
  | .str :: _, _, ρ₁, ρ₂ => Env.consStr (ρ₁.str .here) (Env.append ρ₁.tail ρ₂)

@[simp]
theorem Env.num_consNum_here {N S : Type u} {Γ : List Sort2}
    (x : N) (ρ : Env N S Γ) : (Env.consNum x ρ).num .here = x := by
  rfl

@[simp]
theorem Env.num_consNum_there {N S : Type u} {Γ : List Sort2}
    (x : N) (ρ : Env N S Γ) (v : Var Γ .num) :
    (Env.consNum x ρ).num (.there v) = ρ.num v := by
  rfl

@[simp]
theorem Env.str_consNum_there {N S : Type u} {Γ : List Sort2}
    (x : N) (ρ : Env N S Γ) (v : Var Γ .str) :
    (Env.consNum x ρ).str (.there v) = ρ.str v := by
  rfl

@[simp]
theorem Env.str_consStr_here {N S : Type u} {Γ : List Sort2}
    (X : S) (ρ : Env N S Γ) : (Env.consStr X ρ).str .here = X := by
  rfl

@[simp]
theorem Env.str_consStr_there {N S : Type u} {Γ : List Sort2}
    (X : S) (ρ : Env N S Γ) (v : Var Γ .str) :
    (Env.consStr X ρ).str (.there v) = ρ.str v := by
  rfl

@[simp]
theorem Env.num_consStr_there {N S : Type u} {Γ : List Sort2}
    (X : S) (ρ : Env N S Γ) (v : Var Γ .num) :
    (Env.consStr X ρ).num (.there v) = ρ.num v := by
  rfl

@[simp]
theorem Env.pull_wk_consNum {N S : Type u} {Γ : List Sort2}
    (x : N) (ρ : Env N S Γ) : Env.pull Ren.wk (Env.consNum x ρ) = ρ := by
  ext s v; rfl

@[simp]
theorem Env.pull_wk_consStr {N S : Type u} {Γ : List Sort2}
    (X : S) (ρ : Env N S Γ) : Env.pull Ren.wk (Env.consStr X ρ) = ρ := by
  ext s v; rfl

theorem Env.pull_lift_consNum {N S : Type u} {Γ Δ : List Sort2}
    (r : Ren Γ Δ) (x : N) (ρ : Env N S Δ) :
    Env.pull r.lift (Env.consNum x ρ) = Env.consNum x (Env.pull r ρ) := by
  ext s v
  cases v <;> rfl

theorem Env.pull_lift_consStr {N S : Type u} {Γ Δ : List Sort2}
    (r : Ren Γ Δ) (X : S) (ρ : Env N S Δ) :
    Env.pull r.lift (Env.consStr X ρ) = Env.consStr X (Env.pull r ρ) := by
  ext s v
  cases v <;> rfl

theorem Env.append_inl {N S : Type u} {Γ Δ : List Sort2}
    (ρ₁ : Env N S Γ) (ρ₂ : Env N S Δ) {s : Sort2} (v : Var Γ s) :
    (Env.append ρ₁ ρ₂).get (Var.inl v) = ρ₁.get v := by
  induction Γ with
  | nil => cases v
  | cons t Γ ih =>
    cases t <;> cases v with
    | here => rfl
    | there w => exact ih ρ₁.tail w

theorem Env.append_inr {N S : Type u} {Γ Δ : List Sort2}
    (ρ₁ : Env N S Γ) (ρ₂ : Env N S Δ) {s : Sort2} (v : Var Δ s) :
    (Env.append ρ₁ ρ₂).get (Var.inr v) = ρ₂.get v := by
  induction Γ with
  | nil => rfl
  | cons t Γ ih =>
    cases t <;> exact ih ρ₁.tail

theorem Env.pull_inl_append {N S : Type u} {Γ Δ : List Sort2}
    (ρ₁ : Env N S Γ) (ρ₂ : Env N S Δ) :
    Env.pull Ren.inl (Env.append ρ₁ ρ₂) = ρ₁ := by
  ext s v; exact Env.append_inl ρ₁ ρ₂ v

theorem Env.pull_inr_append {N S : Type u} {Γ Δ : List Sort2}
    (ρ₁ : Env N S Γ) (ρ₂ : Env N S Δ) :
    Env.pull Ren.inr (Env.append ρ₁ ρ₂) = ρ₂ := by
  ext s v; exact Env.append_inr ρ₁ ρ₂ v

theorem Env.append_consNum {N S : Type u} {Γ Δ : List Sort2}
    (x : N) (ρ₁ : Env N S Γ) (ρ₂ : Env N S Δ) :
    Env.append (Env.consNum x ρ₁) ρ₂ = Env.consNum x (Env.append ρ₁ ρ₂) := by
  ext s v
  cases v <;> rfl

theorem Env.append_consStr {N S : Type u} {Γ Δ : List Sort2}
    (X : S) (ρ₁ : Env N S Γ) (ρ₂ : Env N S Δ) :
    Env.append (Env.consStr X ρ₁) ρ₂ = Env.consStr X (Env.append ρ₁ ρ₂) := by
  ext s v
  cases v <;> rfl

theorem Env.append_nil_left {N S : Type u} {Δ : List Sort2} (ρ : Env N S Δ) :
    Env.append (Env.nil (N := N) (S := S)) ρ = ρ := by
  rfl

/-- Raw two-sorted interpretation of the vocabulary `ℒ_FP`. -/
structure LFPInterp : Type (u + 1) where
  /-- Carrier of the number sort. -/
  Num : Type u
  /-- Carrier of the finite-string sort. -/
  Str : Type u
  /-- Constant `0` of the number sort. -/
  zero : Num
  /-- Constant `1` of the number sort. -/
  one : Num
  /-- Addition on numbers. -/
  add : Num → Num → Num
  /-- Multiplication on numbers. -/
  mul : Num → Num → Num
  /-- Order relation `≤` on numbers. -/
  le : Num → Num → Prop
  /-- Length function `|X|` of a binary string. -/
  len : Str → Num
  /-- Membership relation `y ∈ X` (written `X(y)`). -/
  bit : Str → Num → Prop
  /-- Interpretation of `Σ₀ᴮ`-comprehension function symbol `compStr t φ`. -/
  compStrVal : {Δ : List Sort2} → LFPNumTerm Δ → Sigma0BFormula (.num :: Δ) →
    Env Num Str Δ → Str
  /-- Interpretation of bounded minimization function symbol `minNum t φ`. -/
  minNumVal : {Δ : List Sort2} → LFPNumTerm Δ → Sigma0BFormula (.num :: Δ) →
    Env Num Str Δ → Num
  /-- Interpretation of Cobham limited recursion function symbol `limRec G H t`. -/
  limRecVal : {Δ : List Sort2} → LFPStrTerm Δ → LFPStrTerm (.num :: .str :: Δ) →
    L2NumTerm (.num :: Δ) → Num → Env Num Str Δ → Str

/-- Strict inequality `x < y` in `ℒ_A^2`, defined as `x ≤ y ∧ x ≠ y`. -/
@[expose] def LFPInterp.lt (I : LFPInterp.{u}) (x y : I.Num) : Prop :=
  I.le x y ∧ x ≠ y

/-- Evaluate an `ℒ_A^2` polynomial number term in an interpretation `I`. -/
@[expose] def L2NumTerm.eval (I : LFPInterp.{u}) {Γ : List Sort2} :
    L2NumTerm Γ → Env I.Num I.Str Γ → I.Num
  | .var v, ρ => ρ.num v
  | .zero, _ => I.zero
  | .one, _ => I.one
  | .add a b, ρ => I.add (a.eval I ρ) (b.eval I ρ)
  | .mul a b, ρ => I.mul (a.eval I ρ) (b.eval I ρ)
  | .len v, ρ => I.len (ρ.str v)

mutual

/-- Evaluate an `ℒ_FP` number term in an interpretation `I`. -/
@[expose] def LFPNumTerm.eval (I : LFPInterp.{u}) {Γ : List Sort2} :
    LFPNumTerm Γ → Env I.Num I.Str Γ → I.Num
  | .var v, ρ => ρ.num v
  | .zero, _ => I.zero
  | .one, _ => I.one
  | .add a b, ρ => I.add (a.eval I ρ) (b.eval I ρ)
  | .mul a b, ρ => I.mul (a.eval I ρ) (b.eval I ρ)
  | .len T, ρ => I.len (T.eval I ρ)
  | .minNum t φ args, ρ => I.minNumVal t φ (args.eval I ρ)

/-- Evaluate an `ℒ_FP` string term in an interpretation `I`. -/
@[expose] def LFPStrTerm.eval (I : LFPInterp.{u}) {Γ : List Sort2} :
    LFPStrTerm Γ → Env I.Num I.Str Γ → I.Str
  | .svar v, ρ => ρ.str v
  | .compStr t φ args, ρ => I.compStrVal t φ (args.eval I ρ)
  | .limRec G H t y args, ρ => I.limRecVal G H t (y.eval I ρ) (args.eval I ρ)

/-- Evaluate a term environment `TermEnv Γ Δ` to a semantic environment `Env I.Num I.Str Δ`. -/
@[expose] def TermEnv.eval (I : LFPInterp.{u}) {Γ : List Sort2} :
    {Δ : List Sort2} → TermEnv Γ Δ → Env I.Num I.Str Γ → Env I.Num I.Str Δ
  | [], .nil, _ => Env.nil
  | .num :: _, .consNum t σ, ρ => Env.consNum (t.eval I ρ) (σ.eval I ρ)
  | .str :: _, .consStr T σ, ρ => Env.consStr (T.eval I ρ) (σ.eval I ρ)

end

/-- Truth value of a `Σ₀ᴮ(ℒ_FP)` formula in an interpretation `I`. -/
@[expose] def Sigma0BFormula.Realize (I : LFPInterp.{u}) {Γ : List Sort2} :
    Sigma0BFormula Γ → Env I.Num I.Str Γ → Prop
  | .eqNum a b, ρ => a.eval I ρ = b.eval I ρ
  | .eqStr T U, ρ => T.eval I ρ = U.eval I ρ
  | .leNum a b, ρ => I.le (a.eval I ρ) (b.eval I ρ)
  | .bit T a, ρ => I.bit (T.eval I ρ) (a.eval I ρ)
  | .not φ, ρ => ¬ φ.Realize I ρ
  | .and φ ψ, ρ => φ.Realize I ρ ∧ ψ.Realize I ρ
  | .or φ ψ, ρ => φ.Realize I ρ ∨ ψ.Realize I ρ
  | .imp φ ψ, ρ => φ.Realize I ρ → ψ.Realize I ρ
  | .bAll t φ, ρ => ∀ z : I.Num, I.lt z (t.eval I ρ) → φ.Realize I (Env.consNum z ρ)
  | .bEx t φ, ρ => ∃ z : I.Num, I.lt z (t.eval I ρ) ∧ φ.Realize I (Env.consNum z ρ)

theorem L2NumTerm.eval_ren (I : LFPInterp.{u}) {Γ Δ : List Sort2} (r : Ren Γ Δ)
    (t : L2NumTerm Γ) (ρ : Env I.Num I.Str Δ) :
    (t.ren r).eval I ρ = t.eval I (Env.pull r ρ) := by
  induction t with
  | var _ => rfl
  | zero => rfl
  | one => rfl
  | add a b iha ihb => simp only [L2NumTerm.ren, L2NumTerm.eval, iha, ihb]
  | mul a b iha ihb => simp only [L2NumTerm.ren, L2NumTerm.eval, iha, ihb]
  | len _ => rfl

mutual

theorem LFPNumTerm.eval_ren (I : LFPInterp.{u}) {Γ Δ : List Sort2} (r : Ren Γ Δ)
    (t : LFPNumTerm Γ) (ρ : Env I.Num I.Str Δ) :
    (t.ren r).eval I ρ = t.eval I (Env.pull r ρ) := by
  match t with
  | .var _ => rfl
  | .zero => rfl
  | .one => rfl
  | .add a b => simp only [LFPNumTerm.ren, LFPNumTerm.eval, a.eval_ren I r ρ, b.eval_ren I r ρ]
  | .mul a b => simp only [LFPNumTerm.ren, LFPNumTerm.eval, a.eval_ren I r ρ, b.eval_ren I r ρ]
  | .len T => simp only [LFPNumTerm.ren, LFPNumTerm.eval, T.eval_ren I r ρ]
  | .minNum t₀ φ args => simp only [LFPNumTerm.ren, LFPNumTerm.eval, args.eval_ren I r ρ]

theorem LFPStrTerm.eval_ren (I : LFPInterp.{u}) {Γ Δ : List Sort2} (r : Ren Γ Δ)
    (T : LFPStrTerm Γ) (ρ : Env I.Num I.Str Δ) :
    (T.ren r).eval I ρ = T.eval I (Env.pull r ρ) := by
  match T with
  | .svar _ => rfl
  | .compStr t₀ φ args => simp only [LFPStrTerm.ren, LFPStrTerm.eval, args.eval_ren I r ρ]
  | .limRec G H t₀ y args =>
    simp only [LFPStrTerm.ren, LFPStrTerm.eval, y.eval_ren I r ρ, args.eval_ren I r ρ]

theorem TermEnv.eval_ren (I : LFPInterp.{u}) {Γ Γ' Δ : List Sort2} (r : Ren Γ Γ')
    (σ : TermEnv Γ Δ) (ρ : Env I.Num I.Str Γ') :
    (σ.ren r).eval I ρ = σ.eval I (Env.pull r ρ) := by
  match σ with
  | .nil => rfl
  | .consNum t σ' =>
    simp only [TermEnv.ren, TermEnv.eval, t.eval_ren I r ρ, σ'.eval_ren I r ρ]
  | .consStr T σ' =>
    simp only [TermEnv.ren, TermEnv.eval, T.eval_ren I r ρ, σ'.eval_ren I r ρ]

end

theorem Sigma0BFormula.realize_ren (I : LFPInterp.{u}) {Γ Δ : List Sort2} (r : Ren Γ Δ)
    (φ : Sigma0BFormula Γ) (ρ : Env I.Num I.Str Δ) :
    (φ.ren r).Realize I ρ ↔ φ.Realize I (Env.pull r ρ) := by
  match φ with
  | .eqNum a b =>
    simp only [Sigma0BFormula.ren, Sigma0BFormula.Realize, a.eval_ren I r ρ, b.eval_ren I r ρ]
  | .eqStr T U =>
    simp only [Sigma0BFormula.ren, Sigma0BFormula.Realize, T.eval_ren I r ρ, U.eval_ren I r ρ]
  | .leNum a b =>
    simp only [Sigma0BFormula.ren, Sigma0BFormula.Realize, a.eval_ren I r ρ, b.eval_ren I r ρ]
  | .bit T a =>
    simp only [Sigma0BFormula.ren, Sigma0BFormula.Realize, T.eval_ren I r ρ, a.eval_ren I r ρ]
  | .not ψ => simp only [Sigma0BFormula.ren, Sigma0BFormula.Realize, ψ.realize_ren I r ρ]
  | .and ψ χ =>
    simp only [Sigma0BFormula.ren, Sigma0BFormula.Realize, ψ.realize_ren I r ρ,
      χ.realize_ren I r ρ]
  | .or ψ χ =>
    simp only [Sigma0BFormula.ren, Sigma0BFormula.Realize, ψ.realize_ren I r ρ,
      χ.realize_ren I r ρ]
  | .imp ψ χ =>
    simp only [Sigma0BFormula.ren, Sigma0BFormula.Realize, ψ.realize_ren I r ρ,
      χ.realize_ren I r ρ]
  | .bAll t ψ =>
    simp only [Sigma0BFormula.ren, Sigma0BFormula.Realize, t.eval_ren I r ρ]
    refine forall_congr' fun z => imp_congr_right fun _ => ?_
    rw [ψ.realize_ren I r.lift, Env.pull_lift_consNum]
  | .bEx t ψ =>
    simp only [Sigma0BFormula.ren, Sigma0BFormula.Realize, t.eval_ren I r ρ]
    refine exists_congr fun z => and_congr_right fun _ => ?_
    rw [ψ.realize_ren I r.lift, Env.pull_lift_consNum]

theorem TermEnv.eval_id (I : LFPInterp.{u}) (Γ : List Sort2) (ρ : Env I.Num I.Str Γ) :
    (TermEnv.id Γ).eval I ρ = ρ := by
  induction Γ with
  | nil => ext s v; cases v
  | cons t Γ ih =>
    cases t with
    | num =>
      ext s v
      cases v with
      | here => rfl
      | there w =>
        simp only [TermEnv.id, TermEnv.eval, TermEnv.eval_ren, Env.consNum]
        rw [ih (Env.pull Ren.wk ρ)]
        rfl
    | str =>
      ext s v
      cases v with
      | here => rfl
      | there w =>
        simp only [TermEnv.id, TermEnv.eval, TermEnv.eval_ren, Env.consStr]
        rw [ih (Env.pull Ren.wk ρ)]
        rfl

theorem TermEnv.eval_liftNum (I : LFPInterp.{u}) {Γ Δ : List Sort2}
    (σ : TermEnv Γ Δ) (x : I.Num) (ρ : Env I.Num I.Str Γ) :
    σ.liftNum.eval I (Env.consNum x ρ) = Env.consNum x (σ.eval I ρ) := by
  simp only [TermEnv.liftNum, TermEnv.eval, LFPNumTerm.eval, Env.num_consNum_here,
    TermEnv.eval_ren, Env.pull_wk_consNum]

theorem TermEnv.eval_lookupNum (I : LFPInterp.{u}) {Γ Δ : List Sort2}
    (σ : TermEnv Γ Δ) (v : Var Δ .num) (ρ : Env I.Num I.Str Γ) :
    (σ.lookupNum v).eval I ρ = (σ.eval I ρ).num v := by
  match σ, v with
  | .consNum _ _, .here => rfl
  | .consNum _ σ', .there w => exact σ'.eval_lookupNum I w ρ
  | .consStr _ σ', .there w => exact σ'.eval_lookupNum I w ρ

theorem TermEnv.eval_lookupStr (I : LFPInterp.{u}) {Γ Δ : List Sort2}
    (σ : TermEnv Γ Δ) (v : Var Δ .str) (ρ : Env I.Num I.Str Γ) :
    (σ.lookupStr v).eval I ρ = (σ.eval I ρ).str v := by
  match σ, v with
  | .consNum _ σ', .there w => exact σ'.eval_lookupStr I w ρ
  | .consStr _ _, .here => rfl
  | .consStr _ σ', .there w => exact σ'.eval_lookupStr I w ρ

mutual

theorem LFPNumTerm.eval_subst (I : LFPInterp.{u}) {Γ Δ : List Sort2}
    (σ : TermEnv Γ Δ) (t : LFPNumTerm Δ) (ρ : Env I.Num I.Str Γ) :
    (t.subst σ).eval I ρ = t.eval I (σ.eval I ρ) := by
  match t with
  | .var v => exact σ.eval_lookupNum I v ρ
  | .zero => rfl
  | .one => rfl
  | .add a b =>
    simp only [LFPNumTerm.subst, LFPNumTerm.eval, a.eval_subst I σ ρ, b.eval_subst I σ ρ]
  | .mul a b =>
    simp only [LFPNumTerm.subst, LFPNumTerm.eval, a.eval_subst I σ ρ, b.eval_subst I σ ρ]
  | .len T => simp only [LFPNumTerm.subst, LFPNumTerm.eval, T.eval_subst I σ ρ]
  | .minNum t₀ φ args => simp only [LFPNumTerm.subst, LFPNumTerm.eval, args.eval_comp I σ ρ]

theorem LFPStrTerm.eval_subst (I : LFPInterp.{u}) {Γ Δ : List Sort2}
    (σ : TermEnv Γ Δ) (T : LFPStrTerm Δ) (ρ : Env I.Num I.Str Γ) :
    (T.subst σ).eval I ρ = T.eval I (σ.eval I ρ) := by
  match T with
  | .svar v => exact σ.eval_lookupStr I v ρ
  | .compStr t₀ φ args => simp only [LFPStrTerm.subst, LFPStrTerm.eval, args.eval_comp I σ ρ]
  | .limRec G H t₀ y args =>
    simp only [LFPStrTerm.subst, LFPStrTerm.eval, y.eval_subst I σ ρ, args.eval_comp I σ ρ]

theorem TermEnv.eval_comp (I : LFPInterp.{u}) {Γ Δ Θ : List Sort2}
    (τ : TermEnv Δ Θ) (σ : TermEnv Γ Δ) (ρ : Env I.Num I.Str Γ) :
    (τ.comp σ).eval I ρ = τ.eval I (σ.eval I ρ) := by
  match τ with
  | .nil => rfl
  | .consNum t τ' =>
    simp only [TermEnv.comp, TermEnv.eval, t.eval_subst I σ ρ, τ'.eval_comp I σ ρ]
  | .consStr T τ' =>
    simp only [TermEnv.comp, TermEnv.eval, T.eval_subst I σ ρ, τ'.eval_comp I σ ρ]

end

theorem Sigma0BFormula.realize_subst (I : LFPInterp.{u}) {Γ Δ : List Sort2}
    (σ : TermEnv Γ Δ) (φ : Sigma0BFormula Δ) (ρ : Env I.Num I.Str Γ) :
    (φ.subst σ).Realize I ρ ↔ φ.Realize I (σ.eval I ρ) := by
  match φ with
  | .eqNum a b =>
    simp only [Sigma0BFormula.subst, Sigma0BFormula.Realize, a.eval_subst I σ ρ,
      b.eval_subst I σ ρ]
  | .eqStr T U =>
    simp only [Sigma0BFormula.subst, Sigma0BFormula.Realize, T.eval_subst I σ ρ,
      U.eval_subst I σ ρ]
  | .leNum a b =>
    simp only [Sigma0BFormula.subst, Sigma0BFormula.Realize, a.eval_subst I σ ρ,
      b.eval_subst I σ ρ]
  | .bit T a =>
    simp only [Sigma0BFormula.subst, Sigma0BFormula.Realize, T.eval_subst I σ ρ,
      a.eval_subst I σ ρ]
  | .not ψ => simp only [Sigma0BFormula.subst, Sigma0BFormula.Realize, ψ.realize_subst I σ ρ]
  | .and ψ χ =>
    simp only [Sigma0BFormula.subst, Sigma0BFormula.Realize, ψ.realize_subst I σ ρ,
      χ.realize_subst I σ ρ]
  | .or ψ χ =>
    simp only [Sigma0BFormula.subst, Sigma0BFormula.Realize, ψ.realize_subst I σ ρ,
      χ.realize_subst I σ ρ]
  | .imp ψ χ =>
    simp only [Sigma0BFormula.subst, Sigma0BFormula.Realize, ψ.realize_subst I σ ρ,
      χ.realize_subst I σ ρ]
  | .bAll t ψ =>
    simp only [Sigma0BFormula.subst, Sigma0BFormula.Realize, t.eval_subst I σ ρ]
    refine forall_congr' fun z => imp_congr_right fun _ => ?_
    rw [ψ.realize_subst I σ.liftNum, σ.eval_liftNum]
  | .bEx t ψ =>
    simp only [Sigma0BFormula.subst, Sigma0BFormula.Realize, t.eval_subst I σ ρ]
    refine exists_congr fun z => and_congr_right fun _ => ?_
    rw [ψ.realize_subst I σ.liftNum, σ.eval_liftNum]

/-! ### 3. The Axioms of `VPV` and Models `VPVModel` -/

/-- A model of the two-sorted bounded arithmetic theory `VPV` for polynomial-time reasoning.

It satisfies all 15 `2-BASIC` axioms (`B1`–`B12`, `L1`, `L2`, `SE`) together with the defining
axioms of `Σ₀ᴮ(ℒ_FP)`-comprehension (`compStr`), bounded minimization (`minNum`), and Cobham's
limited recursion (`limRec`). -/
structure VPVModel : Type (u + 1) extends LFPInterp.{u} where
  /-- Axiom `B1`: `x + 1 ≠ 0`. -/
  b1 : ∀ x : Num, add x one ≠ zero
  /-- Axiom `B2`: `x + 1 = y + 1 → x = y`. -/
  b2 : ∀ x y : Num, add x one = add y one → x = y
  /-- Axiom `B3`: `x + 0 = x`. -/
  b3 : ∀ x : Num, add x zero = x
  /-- Axiom `B4`: `x + (y + 1) = (x + y) + 1`. -/
  b4 : ∀ x y : Num, add x (add y one) = add (add x y) one
  /-- Axiom `B5`: `x · 0 = 0`. -/
  b5 : ∀ x : Num, mul x zero = zero
  /-- Axiom `B6`: `x · (y + 1) = (x · y) + x`. -/
  b6 : ∀ x y : Num, mul x (add y one) = add (mul x y) x
  /-- Axiom `B7`: `x ≤ y ∧ y ≤ x → x = y`. -/
  b7 : ∀ x y : Num, le x y → le y x → x = y
  /-- Axiom `B8`: `x ≤ x + y`. -/
  b8 : ∀ x y : Num, le x (add x y)
  /-- Axiom `B9`: `0 ≤ x`. -/
  b9 : ∀ x : Num, le zero x
  /-- Axiom `B10`: `x ≤ y ∨ y ≤ x`. -/
  b10 : ∀ x y : Num, le x y ∨ le y x
  /-- Axiom `B11`: `x ≤ y ↔ x < y + 1`. -/
  b11 : ∀ x y : Num, le x y ↔ toLFPInterp.lt x (add y one)
  /-- Axiom `B12`: `x ≠ 0 → ∃ y ≤ x, y + 1 = x`. -/
  b12 : ∀ x : Num, x ≠ zero → ∃ y : Num, le y x ∧ add y one = x
  /-- Axiom `L1`: `X(y) → y < |X|`. -/
  l1 : ∀ (X : Str) (y : Num), bit X y → toLFPInterp.lt y (len X)
  /-- Axiom `L2`: `y + 1 = |X| → X(y)`. -/
  l2 : ∀ (X : Str) (y : Num), add y one = len X → bit X y
  /-- Axiom `SE`: string extensionality. -/
  se : ∀ X Y : Str, len X = len Y →
    (∀ i : Num, toLFPInterp.lt i (len X) → (bit X i ↔ bit Y i)) → X = Y
  /-- Length bound of `Σ₀ᴮ(ℒ_FP)`-comprehension: `|compStr t φ| ≤ t`. -/
  compStr_len : ∀ {Δ : List Sort2} (t : LFPNumTerm Δ) (φ : Sigma0BFormula (.num :: Δ))
    (ρ : Env Num Str Δ), le (len (compStrVal t φ ρ)) (t.eval toLFPInterp ρ)
  /-- Bit specification of `Σ₀ᴮ(ℒ_FP)`-comprehension. -/
  compStr_bit : ∀ {Δ : List Sort2} (t : LFPNumTerm Δ) (φ : Sigma0BFormula (.num :: Δ))
    (ρ : Env Num Str Δ) (z : Num),
    toLFPInterp.lt z (t.eval toLFPInterp ρ) →
      (bit (compStrVal t φ ρ) z ↔ φ.Realize toLFPInterp (Env.consNum z ρ))
  /-- Upper bound of bounded minimization: `minNum t φ ≤ t`. -/
  minNum_le : ∀ {Δ : List Sort2} (t : LFPNumTerm Δ) (φ : Sigma0BFormula (.num :: Δ))
    (ρ : Env Num Str Δ), le (minNumVal t φ ρ) (t.eval toLFPInterp ρ)
  /-- Witness property of bounded minimization when strictly below `t`. -/
  minNum_sat : ∀ {Δ : List Sort2} (t : LFPNumTerm Δ) (φ : Sigma0BFormula (.num :: Δ))
    (ρ : Env Num Str Δ),
    toLFPInterp.lt (minNumVal t φ ρ) (t.eval toLFPInterp ρ) →
      φ.Realize toLFPInterp (Env.consNum (minNumVal t φ ρ) ρ)
  /-- Minimality of `minNum t φ`. -/
  minNum_minimal : ∀ {Δ : List Sort2} (t : LFPNumTerm Δ) (φ : Sigma0BFormula (.num :: Δ))
    (ρ : Env Num Str Δ) (z : Num),
    toLFPInterp.lt z (minNumVal t φ ρ) → ¬ φ.Realize toLFPInterp (Env.consNum z ρ)
  /-- Base case of Cobham's limited recursion at `y = 0`. -/
  limRec_zero : ∀ {Δ : List Sort2} (G : LFPStrTerm Δ) (H : LFPStrTerm (.num :: .str :: Δ))
    (t : L2NumTerm (.num :: Δ)) (ρ : Env Num Str Δ),
    limRecVal G H t zero ρ = G.eval toLFPInterp ρ
  /-- Length bound of Cobham's limited recursion step: `|F(k+1)| ≤ t(k)`. -/
  limRec_succ_len : ∀ {Δ : List Sort2} (G : LFPStrTerm Δ) (H : LFPStrTerm (.num :: .str :: Δ))
    (t : L2NumTerm (.num :: Δ)) (k : Num) (ρ : Env Num Str Δ),
    le (len (limRecVal G H t (add k one) ρ)) (t.eval toLFPInterp (Env.consNum k ρ))
  /-- Bit specification of Cobham's limited recursion step: truncation to `< t(k)`. -/
  limRec_succ_bit : ∀ {Δ : List Sort2} (G : LFPStrTerm Δ) (H : LFPStrTerm (.num :: .str :: Δ))
    (t : L2NumTerm (.num :: Δ)) (k : Num) (ρ : Env Num Str Δ) (z : Num),
    toLFPInterp.lt z (t.eval toLFPInterp (Env.consNum k ρ)) →
      (bit (limRecVal G H t (add k one) ρ) z ↔
        bit (H.eval toLFPInterp (Env.consNum k (Env.consStr (limRecVal G H t k ρ) ρ))) z)

namespace VPVModel

variable (M : VPVModel.{u})

/-- Strict inequality in `M`. -/
@[expose] def lt (x y : M.Num) : Prop := M.toLFPInterp.lt x y

/-- Reflexivity of `≤` in `M` (from `B10`). -/
theorem le_refl (x : M.Num) : M.le x x := by
  rcases M.b10 x x with h | h <;> exact h

/-- `x < x + 1` in `M` (from `B11` and `le_refl`). -/
theorem lt_succ_self (x : M.Num) : M.lt x (M.add x M.one) :=
  (M.b11 x x).mp (M.le_refl x)

/-- Irreflexivity of `<` in `M`. -/
theorem lt_irrefl (x : M.Num) : ¬ M.lt x x := fun h => h.2 rfl

/-- `x ≤ y → ¬ y < x` in `M`. -/
theorem not_lt_of_le {x y : M.Num} (h : M.le x y) : ¬ M.lt y x :=
  fun hlt => hlt.2 (M.b7 y x hlt.1 h)

/-- `x < y → ¬ y ≤ x` in `M`. -/
theorem not_le_of_lt {x y : M.Num} (h : M.lt x y) : ¬ M.le y x :=
  fun hle => h.2 (M.b7 x y h.1 hle)

/-- `¬ x ≤ y ↔ y < x` in `M`. -/
theorem not_le_iff_lt {x y : M.Num} : ¬ M.le x y ↔ M.lt y x := by
  constructor
  · intro h
    rcases M.b10 x y with hxy | hyx
    · exact absurd hxy h
    · exact ⟨hyx, fun heq => h (heq ▸ M.le_refl x)⟩
  · exact M.not_le_of_lt

/-- `¬ x < y ↔ y ≤ x` in `M`. -/
theorem not_lt_iff_le {x y : M.Num} : ¬ M.lt x y ↔ M.le y x := by
  constructor
  · intro h
    rcases M.b10 x y with hxy | hyx
    · by_cases heq : x = y
      · rw [heq]; exact M.le_refl y
      · exact absurd ⟨hxy, heq⟩ h
    · exact hyx
  · exact M.not_lt_of_le

/-- No element is strictly less than `0`. -/
theorem not_lt_zero (x : M.Num) : ¬ M.lt x M.zero :=
  M.not_lt_of_le (M.b9 x)

/-- `x ≤ 0 → x = 0`. -/
theorem eq_zero_of_le_zero {x : M.Num} (h : M.le x M.zero) : x = M.zero :=
  M.b7 x M.zero h (M.b9 x)

/-- `Σ₀ᴮ(ℒ_FP)`-induction (`Σ₀ᴮ(ℒ_FP)-IND`) derived from `2-BASIC` and `minNum`. -/
theorem sigma0B_ind_raw {Δ : List Sort2} (φ : Sigma0BFormula (.num :: Δ))
    (ρ : Env M.Num M.Str Δ)
    (h0 : φ.Realize M.toLFPInterp (Env.consNum M.zero ρ))
    (hstep : ∀ x : M.Num, φ.Realize M.toLFPInterp (Env.consNum x ρ) →
      φ.Realize M.toLFPInterp (Env.consNum (M.add x M.one) ρ)) :
    ∀ y : M.Num, φ.Realize M.toLFPInterp (Env.consNum y ρ) := by
  intro y
  by_contra hny
  let t : LFPNumTerm (.num :: Δ) := .add (.var .here) .one
  let rSkip : Ren (.num :: Δ) (.num :: .num :: Δ) :=
    ⟨fun {s} v => match v with | .here => .here | .there w => .there (.there w)⟩
  let ψ : Sigma0BFormula (.num :: .num :: Δ) := .not (φ.ren rSkip)
  let ρ' : Env M.Num M.Str (.num :: Δ) := Env.consNum y ρ
  let m : M.Num := M.minNumVal t ψ ρ'
  have hψ_eval : ∀ z : M.Num,
      ψ.Realize M.toLFPInterp (Env.consNum z ρ') ↔
        ¬ φ.Realize M.toLFPInterp (Env.consNum z ρ) := by
    intro z
    simp only [ψ, Sigma0BFormula.Realize, Sigma0BFormula.realize_ren]
    have hpull : Env.pull rSkip (Env.consNum z ρ') = Env.consNum z ρ := by
      ext s v
      cases v <;> rfl
    rw [hpull]
  have hm_lt_y1 : M.lt m (M.add y M.one) := by
    by_contra hnot
    have hy1_le_m : M.le (M.add y M.one) m := M.not_lt_iff_le.mp hnot
    have hm_eq : m = M.add y M.one := M.b7 m (M.add y M.one) (M.minNum_le t ψ ρ') hy1_le_m
    have hy_lt_m : M.lt y m := hm_eq.symm ▸ M.lt_succ_self y
    exact M.minNum_minimal t ψ ρ' y hy_lt_m ((hψ_eval y).mpr hny)
  have hnm : ¬ φ.Realize M.toLFPInterp (Env.consNum m ρ) :=
    (hψ_eval m).mp (M.minNum_sat t ψ ρ' hm_lt_y1)
  have hm_ne0 : m ≠ M.zero := fun h0' => hnm (h0' ▸ h0)
  obtain ⟨k, _, hk⟩ := M.b12 m hm_ne0
  have hk_lt_m : M.lt k m := hk ▸ M.lt_succ_self k
  have hφk : φ.Realize M.toLFPInterp (Env.consNum k ρ) := by
    by_contra hnk
    exact M.minNum_minimal t ψ ρ' k hk_lt_m ((hψ_eval k).mpr hnk)
  exact hnm (hk ▸ hstep k hφk)

/-- Transitivity of `≤` in `M`, derived by `Σ₀ᴮ(ℒ_FP)`-induction. -/
theorem le_trans {x y z : M.Num} (hxy : M.le x y) (hyz : M.le y z) : M.le x z := by
  let φ : Sigma0BFormula [.num, .num, .num] :=
    .imp (.leNum (.var (.there (.there .here))) (.var .here))
         (.leNum (.var (.there .here)) (.var .here))
  let ρ : Env M.Num M.Str [.num, .num] := Env.consNum x (Env.consNum y Env.nil)
  have h := M.sigma0B_ind_raw φ ρ
    (by
      simp only [φ, Sigma0BFormula.Realize, LFPNumTerm.eval, ρ,
        Env.num_consNum_here, Env.num_consNum_there]
      intro hy0
      have hy_eq : y = M.zero := M.eq_zero_of_le_zero hy0
      exact hy_eq ▸ hxy)
    (by
      intro k ih
      simp only [φ, Sigma0BFormula.Realize, LFPNumTerm.eval, ρ,
        Env.num_consNum_here, Env.num_consNum_there] at ih ⊢
      intro hyk1
      by_cases heq : y = M.add k M.one
      · exact heq ▸ hxy
      · have hyk : M.le y k := (M.b11 y k).mpr ⟨hyk1, heq⟩
        exact ((M.b11 x k).mp (ih hyk)).1)
    z
  simp only [φ, Sigma0BFormula.Realize, LFPNumTerm.eval, ρ,
    Env.num_consNum_here, Env.num_consNum_there] at h
  exact h hyz

/-- `x < y → y ≤ z → x < z` in `M`. -/
theorem lt_of_lt_of_le {x y z : M.Num} (hxy : M.lt x y) (hyz : M.le y z) : M.lt x z :=
  ⟨M.le_trans hxy.1 hyz, fun hxz => hxy.2 (M.b7 x y hxy.1 (hxz ▸ hyz))⟩

/-- `x ≤ y → y < z → x < z` in `M`. -/
theorem lt_of_le_of_lt {x y z : M.Num} (hxy : M.le x y) (hyz : M.lt y z) : M.lt x z :=
  ⟨M.le_trans hxy hyz.1, fun hxz => hyz.2 (M.b7 y z hyz.1 (hxz ▸ hxy))⟩

/-- Transitivity of `<` in `M`. -/
theorem lt_trans {x y z : M.Num} (hxy : M.lt x y) (hyz : M.lt y z) : M.lt x z :=
  M.lt_of_lt_of_le hxy hyz.1

/-- Full bit-extensionality for strings in `M`: equal bit predicates imply equal strings. -/
theorem str_ext {X Y : M.Str} (h : ∀ i : M.Num, M.bit X i ↔ M.bit Y i) : X = Y := by
  have hlen : M.len X = M.len Y := by
    rcases M.b10 (M.len X) (M.len Y) with hxy | hyx
    · by_cases heq : M.len X = M.len Y
      · exact heq
      · have hlt : M.lt (M.len X) (M.len Y) := ⟨hxy, heq⟩
        have hY0 : M.len Y ≠ M.zero := fun h0 => M.not_lt_zero (M.len X) (h0 ▸ hlt)
        obtain ⟨y, _, hy⟩ := M.b12 (M.len Y) hY0
        have hXley : M.le (M.len X) y := (M.b11 (M.len X) y).mpr (hy.symm ▸ hlt)
        have hbx : M.bit X y := (h y).mpr (M.l2 Y y hy)
        exact absurd (M.l1 X y hbx) (M.not_lt_of_le hXley)
    · by_cases heq : M.len Y = M.len X
      · exact heq.symm
      · have hlt : M.lt (M.len Y) (M.len X) := ⟨hyx, heq⟩
        have hX0 : M.len X ≠ M.zero := fun h0 => M.not_lt_zero (M.len Y) (h0 ▸ hlt)
        obtain ⟨x, _, hx⟩ := M.b12 (M.len X) hX0
        have hYlex : M.le (M.len Y) x := (M.b11 (M.len Y) x).mpr (hx.symm ▸ hlt)
        have hby : M.bit Y x := (h x).mp (M.l2 X x hx)
        exact absurd (M.l1 Y x hby) (M.not_lt_of_le hYlex)
  exact M.se X Y hlen (fun i _ => h i)

/-- Bit characterization of `compStrVal` at every index `z`. -/
theorem bit_compStrVal_iff {Δ : List Sort2} (t : LFPNumTerm Δ) (φ : Sigma0BFormula (.num :: Δ))
    (ρ : Env M.Num M.Str Δ) (z : M.Num) :
    M.bit (M.compStrVal t φ ρ) z ↔
      M.lt z (t.eval M.toLFPInterp ρ) ∧ φ.Realize M.toLFPInterp (Env.consNum z ρ) := by
  constructor
  · intro hb
    have hlt : M.lt z (t.eval M.toLFPInterp ρ) :=
      M.lt_of_lt_of_le (M.l1 _ z hb) (M.compStr_len t φ ρ)
    exact ⟨hlt, (M.compStr_bit t φ ρ z hlt).mp hb⟩
  · rintro ⟨hlt, hφ⟩
    exact (M.compStr_bit t φ ρ z hlt).mpr hφ

/-- Bit characterization of `limRecVal` at `k + 1` for every index `z`. -/
theorem bit_limRecVal_succ_iff {Δ : List Sort2} (G : LFPStrTerm Δ)
    (H : LFPStrTerm (.num :: .str :: Δ)) (t : L2NumTerm (.num :: Δ))
    (k : M.Num) (ρ : Env M.Num M.Str Δ) (z : M.Num) :
    M.bit (M.limRecVal G H t (M.add k M.one) ρ) z ↔
      M.lt z (t.eval M.toLFPInterp (Env.consNum k ρ)) ∧
        M.bit (H.eval M.toLFPInterp (Env.consNum k (Env.consStr (M.limRecVal G H t k ρ) ρ))) z := by
  constructor
  · intro hb
    have hlt : M.lt z (t.eval M.toLFPInterp (Env.consNum k ρ)) :=
      M.lt_of_lt_of_le (M.l1 _ z hb) (M.limRec_succ_len G H t k ρ)
    exact ⟨hlt, (M.limRec_succ_bit G H t k ρ z hlt).mp hb⟩
  · rintro ⟨hlt, hb⟩
    exact (M.limRec_succ_bit G H t k ρ z hlt).mpr hb

/-- `minNumVal t φ ρ < t` iff there exists `z < t` satisfying `φ`. -/
theorem minNumVal_lt_iff {Δ : List Sort2} (t : LFPNumTerm Δ) (φ : Sigma0BFormula (.num :: Δ))
    (ρ : Env M.Num M.Str Δ) :
    M.lt (M.minNumVal t φ ρ) (t.eval M.toLFPInterp ρ) ↔
      ∃ z : M.Num, M.lt z (t.eval M.toLFPInterp ρ) ∧
        φ.Realize M.toLFPInterp (Env.consNum z ρ) := by
  constructor
  · intro hlt
    exact ⟨M.minNumVal t φ ρ, hlt, M.minNum_sat t φ ρ hlt⟩
  · rintro ⟨z, hz, hφz⟩
    by_contra hnot
    have ht_le : M.le (t.eval M.toLFPInterp ρ) (M.minNumVal t φ ρ) := M.not_lt_iff_le.mp hnot
    exact M.minNum_minimal t φ ρ z (M.lt_of_lt_of_le hz ht_le) hφz

/-- `minNumVal t φ ρ = t` iff no `z < t` satisfies `φ`. -/
theorem minNumVal_eq_bound_iff {Δ : List Sort2} (t : LFPNumTerm Δ) (φ : Sigma0BFormula (.num :: Δ))
    (ρ : Env M.Num M.Str Δ) :
    M.minNumVal t φ ρ = t.eval M.toLFPInterp ρ ↔
      ∀ z : M.Num, M.lt z (t.eval M.toLFPInterp ρ) →
        ¬ φ.Realize M.toLFPInterp (Env.consNum z ρ) := by
  constructor
  · intro heq z hz
    exact M.minNum_minimal t φ ρ z (heq.symm ▸ hz)
  · intro hall
    have hnot : ¬ M.lt (M.minNumVal t φ ρ) (t.eval M.toLFPInterp ρ) := by
      rw [M.minNumVal_lt_iff]
      rintro ⟨z, hz, hφz⟩
      exact hall z hz hφz
    exact M.b7 _ _ (M.minNum_le t φ ρ) (M.not_lt_iff_le.mp hnot)

/-- Uniqueness of `minNumVal`: two equivalent predicates and bounds yield the same minimum. -/
theorem minNumVal_congr {Δ₁ Δ₂ : List Sort2}
    (t₁ : LFPNumTerm Δ₁) (φ₁ : Sigma0BFormula (.num :: Δ₁)) (ρ₁ : Env M.Num M.Str Δ₁)
    (t₂ : LFPNumTerm Δ₂) (φ₂ : Sigma0BFormula (.num :: Δ₂)) (ρ₂ : Env M.Num M.Str Δ₂)
    (ht : t₁.eval M.toLFPInterp ρ₁ = t₂.eval M.toLFPInterp ρ₂)
    (hφ : ∀ z : M.Num, M.lt z (t₁.eval M.toLFPInterp ρ₁) →
      (φ₁.Realize M.toLFPInterp (Env.consNum z ρ₁) ↔
        φ₂.Realize M.toLFPInterp (Env.consNum z ρ₂))) :
    M.minNumVal t₁ φ₁ ρ₁ = M.minNumVal t₂ φ₂ ρ₂ := by
  apply M.b7
  · by_contra hnot
    have hlt21 : M.lt (M.minNumVal t₂ φ₂ ρ₂) (M.minNumVal t₁ φ₁ ρ₁) := M.not_le_iff_lt.mp hnot
    have hlt2t : M.lt (M.minNumVal t₂ φ₂ ρ₂) (t₂.eval M.toLFPInterp ρ₂) :=
      ht ▸ M.lt_of_lt_of_le hlt21 (M.minNum_le t₁ φ₁ ρ₁)
    have hsat2 := M.minNum_sat t₂ φ₂ ρ₂ hlt2t
    exact M.minNum_minimal t₁ φ₁ ρ₁ _ hlt21 ((hφ _ (ht.symm ▸ hlt2t)).mpr hsat2)
  · by_contra hnot
    have hlt12 : M.lt (M.minNumVal t₁ φ₁ ρ₁) (M.minNumVal t₂ φ₂ ρ₂) := M.not_le_iff_lt.mp hnot
    have hlt1t : M.lt (M.minNumVal t₁ φ₁ ρ₁) (t₁.eval M.toLFPInterp ρ₁) :=
      ht.symm ▸ M.lt_of_lt_of_le hlt12 (M.minNum_le t₂ φ₂ ρ₂)
    have hsat1 := M.minNum_sat t₁ φ₁ ρ₁ hlt1t
    exact M.minNum_minimal t₂ φ₂ ρ₂ _ hlt12 ((hφ _ hlt1t).mp hsat1)

end VPVModel

/-! ### 4. Standard Model `(ℕ, ℕ)` of `VPV` -/

/-- Build the finite binary string (as a natural number) whose bits `< n`
satisfy a predicate `P`. -/
private noncomputable def natCompStr (n : ℕ) (P : ℕ → Prop) : ℕ := by
  classical
  exact match n with
  | 0 => 0
  | k + 1 => natCompStr k P + if P k then 2 ^ k else 0

private theorem natCompStr_lt_two_pow (n : ℕ) (P : ℕ → Prop) :
    natCompStr n P < 2 ^ n := by
  classical
  induction n with
  | zero => simp [natCompStr]
  | succ k ih =>
    simp only [natCompStr, Nat.pow_succ]
    split_ifs <;> omega

private theorem natCompStr_size_le (n : ℕ) (P : ℕ → Prop) :
    (natCompStr n P).size ≤ n := by
  rw [Nat.size_le]
  exact natCompStr_lt_two_pow n P

private theorem testBit_add_two_pow_of_lt {a k z : ℕ} (ha : a < 2 ^ k) :
    (a + 2 ^ k).testBit z = if z = k then true else a.testBit z := by
  by_cases hzk : z = k
  · subst hzk
    simp only [↓reduceIte, Nat.testBit, Nat.shiftRight_eq_div_pow]
    have hdiv : (a + 2 ^ z) / 2 ^ z = 1 := by
      rw [Nat.add_div_right _ (Nat.two_pow_pos z), Nat.div_eq_of_lt ha]
    simp [hdiv]
  · simp only [hzk, ↓reduceIte, Nat.testBit, Nat.shiftRight_eq_div_pow]
    rcases lt_or_gt_of_ne hzk with hlt | hgt
    · have hpow : 2 ^ k = 2 ^ z * 2 ^ (k - z) := by
        rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hlt)]
      have hdiv : (a + 2 ^ k) / 2 ^ z = a / 2 ^ z + 2 ^ (k - z) := by
        rw [hpow, mul_comm (2 ^ z), Nat.add_mul_div_right _ _ (Nat.two_pow_pos z)]
      have heven : 2 ∣ 2 ^ (k - z) := dvd_pow_self 2 (by omega)
      rw [hdiv]
      obtain ⟨m, hm⟩ := heven
      rw [hm]
      have hmod : (a / 2 ^ z + 2 * m) % 2 = (a / 2 ^ z) % 2 := by omega
      simp [hmod]
    · have hpow : 2 ^ (k + 1) ≤ 2 ^ z := Nat.pow_le_pow_right (by omega) (by omega)
      have hlt1 : a + 2 ^ k < 2 ^ z := lt_of_lt_of_le (by rw [Nat.pow_succ]; omega) hpow
      have hlt2 : a < 2 ^ z := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.div_eq_of_lt hlt1, Nat.div_eq_of_lt hlt2]

private theorem natCompStr_testBit (n : ℕ) (P : ℕ → Prop) (z : ℕ) :
    (natCompStr n P).testBit z = true ↔ z < n ∧ P z := by
  classical
  induction n with
  | zero => simp [natCompStr]
  | succ k ih =>
    simp only [natCompStr]
    have hlt : natCompStr k P < 2 ^ k := natCompStr_lt_two_pow k P
    by_cases hPk : P k
    · simp only [hPk, ↓reduceIte, testBit_add_two_pow_of_lt hlt]
      by_cases hzk : z = k
      · subst hzk; simp [hPk]
      · simp only [hzk, ↓reduceIte, ih]
        exact ⟨fun ⟨h1, h2⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨by omega, h2⟩⟩
    · simp only [hPk, ↓reduceIte, Nat.add_zero, ih]
      refine ⟨fun ⟨h1, h2⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ?_⟩
      have hne : z ≠ k := fun h => hPk (h ▸ h2)
      exact ⟨by omega, h2⟩

/-- Least `z < n` satisfying `P`, or `n` if no such `z` exists. -/
private noncomputable def natMinNum (n : ℕ) (P : ℕ → Prop) : ℕ := by
  classical
  exact if h : ∃ z < n, P z then Nat.find h else n

private theorem natMinNum_le (n : ℕ) (P : ℕ → Prop) : natMinNum n P ≤ n := by
  classical
  unfold natMinNum
  split_ifs with h
  · exact Nat.le_of_lt (Nat.find_spec h).1
  · exact le_rfl

private theorem natMinNum_sat (n : ℕ) (P : ℕ → Prop) (hlt : natMinNum n P < n) :
    P (natMinNum n P) := by
  classical
  unfold natMinNum at hlt ⊢
  split_ifs at hlt ⊢ with h
  · exact (Nat.find_spec h).2
  · exact absurd hlt (Nat.lt_irrefl n)

private theorem natMinNum_minimal (n : ℕ) (P : ℕ → Prop) (z : ℕ)
    (hlt : z < natMinNum n P) : ¬ P z := by
  classical
  unfold natMinNum at hlt
  split_ifs at hlt with h
  · intro hPz
    have hzn : z < n := lt_trans hlt (Nat.find_spec h).1
    exact Nat.find_min h hlt ⟨hzn, hPz⟩
  · intro hPz
    exact h ⟨z, hlt, hPz⟩

/-- Standard-model evaluator for `ℒ_A^2` terms on `(ℕ, ℕ)`. -/
private def stdL2Eval {Γ : List Sort2} : L2NumTerm Γ → Env ℕ ℕ Γ → ℕ
  | .var v, ρ => ρ.num v
  | .zero, _ => 0
  | .one, _ => 1
  | .add a b, ρ => stdL2Eval a ρ + stdL2Eval b ρ
  | .mul a b, ρ => stdL2Eval a ρ * stdL2Eval b ρ
  | .len v, ρ => (ρ.str v).size

mutual

private noncomputable def stdNumEval {Γ : List Sort2} :
    LFPNumTerm Γ → Env ℕ ℕ Γ → ℕ
  | .var v, ρ => ρ.num v
  | .zero, _ => 0
  | .one, _ => 1
  | .add a b, ρ => stdNumEval a ρ + stdNumEval b ρ
  | .mul a b, ρ => stdNumEval a ρ * stdNumEval b ρ
  | .len T, ρ => (stdStrEval T ρ).size
  | .minNum t φ args, ρ =>
    let ρ' := stdEnvEval args ρ
    natMinNum (stdNumEval t ρ') (fun z => stdRealize φ (Env.consNum z ρ'))

private noncomputable def stdStrEval {Γ : List Sort2} :
    LFPStrTerm Γ → Env ℕ ℕ Γ → ℕ
  | .svar v, ρ => ρ.str v
  | .compStr t φ args, ρ =>
    let ρ' := stdEnvEval args ρ
    natCompStr (stdNumEval t ρ') (fun z => stdRealize φ (Env.consNum z ρ'))
  | .limRec G H t y args, ρ =>
    let ρ' := stdEnvEval args ρ
    let base := stdStrEval G ρ'
    let step : ℕ → ℕ → ℕ := fun k prev =>
      let next := stdStrEval H (Env.consNum k (Env.consStr prev ρ'))
      natCompStr (stdL2Eval t (Env.consNum k ρ')) (fun z => next.testBit z = true)
    Nat.rec base step (stdNumEval y ρ)

private noncomputable def stdRealize {Γ : List Sort2} :
    Sigma0BFormula Γ → Env ℕ ℕ Γ → Prop
  | .eqNum a b, ρ => stdNumEval a ρ = stdNumEval b ρ
  | .eqStr T U, ρ => stdStrEval T ρ = stdStrEval U ρ
  | .leNum a b, ρ => stdNumEval a ρ ≤ stdNumEval b ρ
  | .bit T a, ρ => (stdStrEval T ρ).testBit (stdNumEval a ρ) = true
  | .not φ, ρ => ¬ stdRealize φ ρ
  | .and φ ψ, ρ => stdRealize φ ρ ∧ stdRealize ψ ρ
  | .or φ ψ, ρ => stdRealize φ ρ ∨ stdRealize ψ ρ
  | .imp φ ψ, ρ => stdRealize φ ρ → stdRealize ψ ρ
  | .bAll t φ, ρ => ∀ z < stdNumEval t ρ, stdRealize φ (Env.consNum z ρ)
  | .bEx t φ, ρ => ∃ z < stdNumEval t ρ, stdRealize φ (Env.consNum z ρ)

private noncomputable def stdEnvEval {Γ : List Sort2} :
    {Δ : List Sort2} → TermEnv Γ Δ → Env ℕ ℕ Γ → Env ℕ ℕ Δ
  | [], .nil, _ => Env.nil
  | .num :: _, .consNum t σ, ρ => Env.consNum (stdNumEval t ρ) (stdEnvEval σ ρ)
  | .str :: _, .consStr T σ, ρ => Env.consStr (stdStrEval T ρ) (stdEnvEval σ ρ)

end

/-- Raw interpretation on `(ℕ, ℕ)` underlying `standardVPVModel`. -/
private noncomputable abbrev stdLFPInterp : LFPInterp.{0} where
  Num := ℕ
  Str := ℕ
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  le := (· ≤ ·)
  len := Nat.size
  bit := fun X y => X.testBit y = true
  compStrVal := fun t φ ρ =>
    natCompStr (stdNumEval t ρ) (fun z => stdRealize φ (Env.consNum z ρ))
  minNumVal := fun t φ ρ =>
    natMinNum (stdNumEval t ρ) (fun z => stdRealize φ (Env.consNum z ρ))
  limRecVal := fun G H t y ρ =>
    Nat.rec (stdStrEval G ρ) (fun k prev =>
      let next := stdStrEval H (Env.consNum k (Env.consStr prev ρ))
      natCompStr (stdL2Eval t (Env.consNum k ρ)) (fun z => next.testBit z = true)) y

private theorem stdLFPInterp_lt_iff (x y : ℕ) :
    stdLFPInterp.lt x y ↔ x < y := by
  change (x ≤ y ∧ x ≠ y) ↔ x < y
  omega

private theorem stdL2Eval_eq {Γ : List Sort2} (t : L2NumTerm Γ) (ρ : Env ℕ ℕ Γ) :
    t.eval stdLFPInterp ρ = stdL2Eval t ρ := by
  induction t with
  | var _ => rfl
  | zero => rfl
  | one => rfl
  | add a b iha ihb =>
    change a.eval stdLFPInterp ρ + b.eval stdLFPInterp ρ = stdL2Eval a ρ + stdL2Eval b ρ
    rw [iha, ihb]
  | mul a b iha ihb =>
    change a.eval stdLFPInterp ρ * b.eval stdLFPInterp ρ = stdL2Eval a ρ * stdL2Eval b ρ
    rw [iha, ihb]
  | len _ => rfl

mutual

private theorem stdNumEval_eq {Γ : List Sort2} (t : LFPNumTerm Γ) (ρ : Env ℕ ℕ Γ) :
    t.eval stdLFPInterp ρ = stdNumEval t ρ := by
  match t with
  | .var _ => rfl
  | .zero => rfl
  | .one => rfl
  | .add a b =>
    change a.eval stdLFPInterp ρ + b.eval stdLFPInterp ρ = stdNumEval a ρ + stdNumEval b ρ
    rw [stdNumEval_eq a ρ, stdNumEval_eq b ρ]
  | .mul a b =>
    change a.eval stdLFPInterp ρ * b.eval stdLFPInterp ρ = stdNumEval a ρ * stdNumEval b ρ
    rw [stdNumEval_eq a ρ, stdNumEval_eq b ρ]
  | .len T =>
    change (T.eval stdLFPInterp ρ).size = (stdStrEval T ρ).size
    rw [stdStrEval_eq T ρ]
  | .minNum t₀ φ args =>
    change natMinNum (stdNumEval t₀ (args.eval stdLFPInterp ρ)) _ =
      natMinNum (stdNumEval t₀ (stdEnvEval args ρ)) _
    rw [stdEnvEval_eq args ρ]

private theorem stdStrEval_eq {Γ : List Sort2} (T : LFPStrTerm Γ) (ρ : Env ℕ ℕ Γ) :
    T.eval stdLFPInterp ρ = stdStrEval T ρ := by
  match T with
  | .svar _ => rfl
  | .compStr t₀ φ args =>
    change natCompStr (stdNumEval t₀ (args.eval stdLFPInterp ρ)) _ =
      natCompStr (stdNumEval t₀ (stdEnvEval args ρ)) _
    rw [stdEnvEval_eq args ρ]
  | .limRec G H t₀ y args =>
    have h1 := stdNumEval_eq y ρ
    have h2 := stdEnvEval_eq args ρ
    change stdLFPInterp.limRecVal G H t₀ (y.eval stdLFPInterp ρ) (args.eval stdLFPInterp ρ) =
      stdLFPInterp.limRecVal G H t₀ (stdNumEval y ρ) (stdEnvEval args ρ)
    rw [h1, h2]

private theorem stdEnvEval_eq {Γ Δ : List Sort2} (σ : TermEnv Γ Δ) (ρ : Env ℕ ℕ Γ) :
    σ.eval stdLFPInterp ρ = stdEnvEval σ ρ := by
  match σ with
  | .nil => rfl
  | .consNum t σ' =>
    change Env.consNum (t.eval stdLFPInterp ρ) (σ'.eval stdLFPInterp ρ) =
      Env.consNum (stdNumEval t ρ) (stdEnvEval σ' ρ)
    rw [stdNumEval_eq t ρ, stdEnvEval_eq σ' ρ]
  | .consStr T σ' =>
    change Env.consStr (T.eval stdLFPInterp ρ) (σ'.eval stdLFPInterp ρ) =
      Env.consStr (stdStrEval T ρ) (stdEnvEval σ' ρ)
    rw [stdStrEval_eq T ρ, stdEnvEval_eq σ' ρ]

end

private theorem stdRealize_eq {Γ : List Sort2} (φ : Sigma0BFormula Γ) (ρ : Env ℕ ℕ Γ) :
    φ.Realize stdLFPInterp ρ ↔ stdRealize φ ρ := by
  match φ with
  | .eqNum a b =>
    change a.eval stdLFPInterp ρ = b.eval stdLFPInterp ρ ↔ stdNumEval a ρ = stdNumEval b ρ
    rw [stdNumEval_eq a ρ, stdNumEval_eq b ρ]
  | .eqStr T U =>
    change T.eval stdLFPInterp ρ = U.eval stdLFPInterp ρ ↔ stdStrEval T ρ = stdStrEval U ρ
    rw [stdStrEval_eq T ρ, stdStrEval_eq U ρ]
  | .leNum a b =>
    change a.eval stdLFPInterp ρ ≤ b.eval stdLFPInterp ρ ↔ stdNumEval a ρ ≤ stdNumEval b ρ
    rw [stdNumEval_eq a ρ, stdNumEval_eq b ρ]
  | .bit T a =>
    change (T.eval stdLFPInterp ρ).testBit (a.eval stdLFPInterp ρ) = true ↔
      (stdStrEval T ρ).testBit (stdNumEval a ρ) = true
    rw [stdStrEval_eq T ρ, stdNumEval_eq a ρ]
  | .not ψ =>
    change ¬ ψ.Realize stdLFPInterp ρ ↔ ¬ stdRealize ψ ρ
    rw [stdRealize_eq ψ ρ]
  | .and ψ χ =>
    change (ψ.Realize stdLFPInterp ρ ∧ χ.Realize stdLFPInterp ρ) ↔
      (stdRealize ψ ρ ∧ stdRealize χ ρ)
    rw [stdRealize_eq ψ ρ, stdRealize_eq χ ρ]
  | .or ψ χ =>
    change (ψ.Realize stdLFPInterp ρ ∨ χ.Realize stdLFPInterp ρ) ↔
      (stdRealize ψ ρ ∨ stdRealize χ ρ)
    rw [stdRealize_eq ψ ρ, stdRealize_eq χ ρ]
  | .imp ψ χ =>
    change (ψ.Realize stdLFPInterp ρ → χ.Realize stdLFPInterp ρ) ↔
      (stdRealize ψ ρ → stdRealize χ ρ)
    rw [stdRealize_eq ψ ρ, stdRealize_eq χ ρ]
  | .bAll t ψ =>
    change (∀ z : ℕ, stdLFPInterp.lt z (t.eval stdLFPInterp ρ) →
      ψ.Realize stdLFPInterp (Env.consNum z ρ)) ↔
      (∀ z < stdNumEval t ρ, stdRealize ψ (Env.consNum z ρ))
    rw [stdNumEval_eq t ρ]
    exact forall_congr' fun z =>
      imp_congr (stdLFPInterp_lt_iff z (stdNumEval t ρ)) (stdRealize_eq ψ _)
  | .bEx t ψ =>
    change (∃ z : ℕ, stdLFPInterp.lt z (t.eval stdLFPInterp ρ) ∧
      ψ.Realize stdLFPInterp (Env.consNum z ρ)) ↔
      (∃ z < stdNumEval t ρ, stdRealize ψ (Env.consNum z ρ))
    rw [stdNumEval_eq t ρ]
    exact exists_congr fun z =>
      and_congr (stdLFPInterp_lt_iff z (stdNumEval t ρ)) (stdRealize_eq ψ _)

/-- The standard model `(ℕ, ℕ)` of `VPV` (with strings represented as natural numbers via
`Nat.testBit` and length `Nat.size`), witnessing non-vacuity of `VPVModel`. -/
noncomputable def standardVPVModel : VPVModel.{0} where
  toLFPInterp := stdLFPInterp
  b1 := fun (x : ℕ) => Nat.succ_ne_zero x
  b2 := fun (_ _ : ℕ) h => Nat.succ.inj h
  b3 := fun (x : ℕ) => Nat.add_zero x
  b4 := fun (x y : ℕ) => (Nat.add_assoc x y 1).symm
  b5 := fun (x : ℕ) => Nat.mul_zero x
  b6 := fun (x y : ℕ) => Nat.mul_succ x y
  b7 := fun (_ _ : ℕ) h1 h2 => Nat.le_antisymm h1 h2
  b8 := fun (x y : ℕ) => Nat.le_add_right x y
  b9 := fun (x : ℕ) => Nat.zero_le x
  b10 := fun (x y : ℕ) => Nat.le_total x y
  b11 := fun (x y : ℕ) => by
    rw [stdLFPInterp_lt_iff]
    change x ≤ y ↔ x < y + 1
    omega
  b12 := fun (x : ℕ) hx => ⟨x - 1, Nat.sub_le x 1, Nat.sub_add_cancel (Nat.pos_of_ne_zero hx)⟩
  l1 := fun (X y : ℕ) hb => by
    rw [stdLFPInterp_lt_iff]
    by_contra hnot
    have hge : X.size ≤ y := Nat.le_of_not_lt hnot
    have hlt : X < 2 ^ y :=
      lt_of_lt_of_le (Nat.lt_size_self X) (Nat.pow_le_pow_right (by omega) hge)
    have hf : X.testBit y = false := Nat.testBit_lt_two_pow hlt
    exact absurd hb (by change X.testBit y ≠ true; rw [hf]; decide)
  l2 := fun (X y : ℕ) (hy : y + 1 = X.size) => by
    have hsz : X.size = y + 1 := hy.symm
    have hge : 2 ^ y ≤ X := by
      have hnotle : ¬ X.size ≤ y := by omega
      rw [Nat.size_le] at hnotle
      omega
    have hlt : X < 2 ^ (y + 1) := by
      rw [← hsz]; exact Nat.lt_size_self X
    change X.testBit y = true
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
    have hdiv : X / 2 ^ y = 1 := by
      have h1 : 1 ≤ X / 2 ^ y := Nat.div_pos hge (Nat.two_pow_pos y)
      have h2 : X / 2 ^ y < 2 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos y)]
        simpa [Nat.pow_succ, mul_comm] using hlt
      omega
    simp [hdiv]
  se := fun (X Y : ℕ) (hlen : X.size = Y.size) hbits => by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < X.size
    · have hiff := hbits i (by rw [stdLFPInterp_lt_iff]; exact hi)
      change X.testBit i = true ↔ Y.testBit i = true at hiff
      cases hX : X.testBit i <;> cases hY : Y.testBit i <;> simp_all
    · have hX : X.testBit i = false := by
        apply Nat.testBit_lt_two_pow
        exact lt_of_lt_of_le (Nat.lt_size_self X)
          (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi))
      have hY : Y.testBit i = false := by
        apply Nat.testBit_lt_two_pow
        have hiY : ¬ i < Y.size := hlen ▸ hi
        exact lt_of_lt_of_le (Nat.lt_size_self Y)
          (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hiY))
      rw [hX, hY]
  compStr_len := fun t φ ρ => by
    change (natCompStr (stdNumEval t ρ) _).size ≤ t.eval stdLFPInterp ρ
    rw [stdNumEval_eq]
    exact natCompStr_size_le _ _
  compStr_bit := fun t φ ρ z hz => by
    rw [stdLFPInterp_lt_iff, stdNumEval_eq] at hz
    change (natCompStr (stdNumEval t ρ) _).testBit z = true ↔ _
    rw [natCompStr_testBit, stdRealize_eq]
    exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩
  minNum_le := fun t φ ρ => by
    change natMinNum (stdNumEval t ρ) _ ≤ t.eval stdLFPInterp ρ
    rw [stdNumEval_eq]
    exact natMinNum_le _ _
  minNum_sat := fun t φ ρ hlt => by
    rw [stdLFPInterp_lt_iff, stdNumEval_eq] at hlt
    rw [stdRealize_eq]
    exact natMinNum_sat _ _ hlt
  minNum_minimal := fun t φ ρ z hlt => by
    rw [stdLFPInterp_lt_iff] at hlt
    rw [stdRealize_eq]
    exact natMinNum_minimal _ _ z hlt
  limRec_zero := fun G H t ρ => by
    change stdStrEval G ρ = G.eval stdLFPInterp ρ
    exact (stdStrEval_eq G ρ).symm
  limRec_succ_len := fun G H t k ρ => by
    change (natCompStr (stdL2Eval t (Env.consNum k ρ)) _).size ≤
      t.eval stdLFPInterp (Env.consNum k ρ)
    rw [stdL2Eval_eq]
    exact natCompStr_size_le _ _
  limRec_succ_bit := fun G H t k ρ z hz => by
    rw [stdLFPInterp_lt_iff, stdL2Eval_eq] at hz
    change (natCompStr (stdL2Eval t (Env.consNum k ρ)) _).testBit z = true ↔ _
    rw [natCompStr_testBit, stdStrEval_eq]
    exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩

/-- `VPVModel` is inhabited (witnessed by `standardVPVModel`). -/
noncomputable instance : Nonempty VPVModel.{0} := ⟨standardVPVModel⟩

/-! ### 5. Bridge to Mathlib's `FirstOrder.Language` -/

/-- Function symbols of the single-sorted first-order encoding of `ℒ_FP`. -/
inductive VPVFunc : ℕ → Type
  | zero : VPVFunc 0
  | one : VPVFunc 0
  | add : VPVFunc 2
  | mul : VPVFunc 2
  | len : VPVFunc 1
  | compStr {Δ : List Sort2} : LFPNumTerm Δ → Sigma0BFormula (.num :: Δ) → VPVFunc Δ.length
  | minNum {Δ : List Sort2} : LFPNumTerm Δ → Sigma0BFormula (.num :: Δ) → VPVFunc Δ.length
  | limRec {Δ : List Sort2} :
      LFPStrTerm Δ → LFPStrTerm (.num :: .str :: Δ) → L2NumTerm (.num :: Δ) →
      VPVFunc (Δ.length + 1)

/-- Relation symbols of the single-sorted first-order encoding of `ℒ_FP`:
sort predicates `isNum`, `isStr`, number order `le`, and string bit membership `bit`. -/
inductive VPVRel : ℕ → Type
  | isNum : VPVRel 1
  | isStr : VPVRel 1
  | le : VPVRel 2
  | bit : VPVRel 2

/-- The Mathlib `FirstOrder.Language` corresponding to the two-sorted vocabulary `ℒ_FP`. -/
def vpvLang : FirstOrder.Language.{0, 0} where
  Functions := VPVFunc
  Relations := VPVRel

/-- A Mathlib first-order structure for `vpvLang` satisfies the two-sorted `VPV` axioms when
its `isNum` and `isStr` predicates define a `VPVModel` agreeing with the relations of `vpvLang`. -/
def vpvStructureSatisfies (M : Type u) [S : vpvLang.Structure M] : Prop :=
  ∃ m : VPVModel.{u},
    m.Num = { x : M // S.RelMap VPVRel.isNum ![x] } ∧
    m.Str = { X : M // S.RelMap VPVRel.isStr ![X] } ∧
    (∀ (x y : M) (hx : S.RelMap VPVRel.isNum ![x]) (hy : S.RelMap VPVRel.isNum ![y]),
      S.RelMap VPVRel.le ![x, y] ↔
        ∃ x' y' : m.Num, HEq x' (⟨x, hx⟩ : { z : M // S.RelMap VPVRel.isNum ![z] }) ∧
          HEq y' (⟨y, hy⟩ : { z : M // S.RelMap VPVRel.isNum ![z] }) ∧ m.le x' y')

/-- Build a `VPVModel` from any Mathlib `vpvLang.Structure` satisfying `vpvStructureSatisfies`. -/
noncomputable def VPVModel.ofFirstOrderStructure (M : Type u) [vpvLang.Structure M]
    (h : vpvStructureSatisfies M) : VPVModel.{u} :=
  Classical.choose h

end CslibFrontier.Logics.BoundedArithmetic
