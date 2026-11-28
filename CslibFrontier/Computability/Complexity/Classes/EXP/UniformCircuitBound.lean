module

public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Computability.Circuit.Boolean.EvaluationTime
public import CslibFrontier.Computability.Circuit.Boolean.PPoly
public import CslibFrontier.Computability.Circuit.Boolean.SuccinctVerifier
public import CslibFrontier.Computability.Circuit.Boolean.Tableau.Decoder.Assembly
public import CslibFrontier.Computability.Circuit.Boolean.Tableau.Succinct
public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.HardnessEncoding.Program
public import CslibFrontier.Computability.MCSP.NP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import CslibFrontier.Computability.PolyTime.BinaryField
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.BitPolynomial
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Derandomization
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Complexity.AffineDisperser.PolyTime
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.LazyDiagonal
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.TimePolylog
import CslibFrontier.Computability.Complexity.Classes.MIP.Arithmetization
import CslibFrontier.Computability.Complexity.Classes.NP.Nondeterministic
import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Complexity.HardnessEncoding.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString.BinaryWord
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayVerdict
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Decode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Machine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.ResourceBound
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.Data.BitString.Counter
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Infrastructure for the Impagliazzo–Kabanets–Wigderson lower bound

Uniform circuit upper bounds for `NTIME(2^n)` under `NEXP ⊆ P/poly`, linear-bitwidth succinct
CNF decoders, and polynomial-time bit-indexed Nisan–Wigderson truth-table generation:
1. Uniform fixed-exponent circuit upper bound for all of `NTIME(2^n)` under `NEXP ⊆ P/poly`.
2. Linear-width succinct CNF and polynomial-time decoder reduction for `NTIME(2^n)`, together with
   a polynomial-time truth-table clause checker.
3. Explicit polynomial-time evaluation of the bit-indexed polynomial Nisan–Wigderson design
   `Design.binaryPolynomial` composed with `HardnessEncoding.encodedProgramAt` on an explicit
   truth table.

## Main definitions

* `CslibFrontier.Complexity.checkAllClauses`: polynomial-time verifier testing whether a padded
  truth table satisfies all clauses of a decoded succinct 3CNF.
* `CslibFrontier.Complexity.binPolyBit`, `CslibFrontier.Complexity.binPolyRestrict`: explicit
  coordinate evaluator for `Design.binaryPolynomial`.
* `CslibFrontier.Complexity.nwTableGen`: explicit Nisan–Wigderson generator evaluated on the
  hardness encoding of a truth table.

## Main results

* `CslibFrontier.Complexity.exists_fixed_exp_circuit_bound_of_NEXP_subset_PPoly`:
  uniform circuit exponent for `NTIME(2^n)` from `NEXP ⊆ P/poly`.
* `CslibFrontier.Complexity.exists_linear_succinctDecoder_of_mem_NTIME_two_pow`:
  linear-width succinct CNF and decoder for `NTIME(2^n)`.
* `CslibFrontier.Complexity.nwTableGen_eq`,
  `CslibFrontier.Complexity.computableInPolyTime_nwTableGen`:
  correctness and polynomial-time computability of the explicit Nisan–Wigderson generator.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity
open Cslib.Complexity.Diagonal Cslib.Crypto.PRG.NisanWigderson Cslib.HardnessEncoding
open Cslib.Logic.PL Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal
open scoped BigOperators

attribute [local irreducible] ComputableInPolyTime eDesc

/-! ### : Uniform fixed-exponent circuit bound from `NEXP ⊆ P/poly` -/

/-- Universal exponential-time verifier: decodes a verifier machine description from the doubly
framed prefix of `p.1`, runs it on `(dropFrame p.1, p.2)` for `2 ^ (2 * p.1.length)` steps, and
accepts when it halts with output `[true]`. -/
private def univNEVerifier (p : List Bool × List Bool) : Bool :=
  !verdict (universal (decodeDesc (unframe (unframe p.1)),
    (frame (dropFrame p.1) ++ p.2).map eBit, 2 ^ (2 * p.1.length)))

/-- Universal `NE` language decided by `univNEVerifier` with witness length `2 ^ z.length`. -/
private def univNE : Set (List Bool) :=
  {z | ∃ v : List Bool, v.length = 2 ^ z.length ∧ univNEVerifier (z, v) = true}

private theorem univNE_mem_NEXP : univNE ∈ NEXP encBits := by
  have hℓ_pt : ComputableInPolyTime (fun z : List Bool => z.length) encBits encUnary :=
    ComputableInPolyTime.length_bits
  obtain ⟨Cℓ, hℓ⟩ := ComputableInPolyTime.exists_computableInO_unary_two_pow hℓ_pt
  -- Build `ComputableInO` for `univNEVerifier`
  obtain ⟨dd, ed, hdec⟩ := exists_computableInDegree_decodeDesc
  have hu2_pt : ComputableInPolyTime (fun p : List Bool × List Bool => unframe (unframe p.1))
      (encPair encBits encBits) encBits :=
    ComputableInPolyTime.unframe.comp
      (ComputableInPolyTime.unframe.comp (ComputableInPolyTime.fst encBits encBits))
  have hdesc_pt : ComputableInPolyTime
      (fun p : List Bool × List Bool => decodeDesc (unframe (unframe p.1)))
      (encPair encBits encBits) eDesc :=
    (hdec.inO.computableInPolyTime
      ((PolyBounded.self.add (.const 1)).pow dd)
      ((PolyBounded.self.add (.const 1)).pow dd)).comp hu2_pt
  have hword_pt : ComputableInPolyTime
      (fun p : List Bool × List Bool => frame (dropFrame p.1) ++ p.2)
      (encPair encBits encBits) encBits :=
    ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.frame.comp
        (ComputableInPolyTime.dropFrame.comp (ComputableInPolyTime.fst encBits encBits)))
      (ComputableInPolyTime.snd encBits encBits)
  have hsym_pt : ComputableInPolyTime
      (fun p : List Bool × List Bool => (frame (dropFrame p.1) ++ p.2).map eBit)
      (encPair encBits encBits) (encList encUnary) :=
    (Universal.computableInO_map_eBit.computableInPolyTime
      (PolyBounded.self) (PolyBounded.self)).comp hword_pt
  have hclock_pt : ComputableInPolyTime
      (fun p : List Bool × List Bool => 2 ^ (2 * p.1.length))
      (encPair encBits encBits) encNat :=
    ComputableInPolyTime.binary_two_pow.comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
        (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.fst encBits encBits)))
  have hpre_pt : ComputableInPolyTime
      (fun p : List Bool × List Bool =>
        (decodeDesc (unframe (unframe p.1)),
          (frame (dropFrame p.1) ++ p.2).map eBit, 2 ^ (2 * p.1.length)))
      (encPair encBits encBits) eIn :=
    hdesc_pt.prod (hsym_pt.prod hclock_pt)
  obtain ⟨Tpre, Spre, hTpre_pb, hSpre_pb, hpre_O⟩ := hpre_pt.exists_computableInO
  have hpre_len_pb := hpre_pt.polyBounded_length
  have hU := computableInO_universal_polynomialBound.comp hpre_O
  have hv := computableInO_verdict_linear.comp_linear hU
  have hnot := (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool)
    (fun b : Bool => !b)).inO_one.comp_linear hv
  -- Extract polynomial bounds for `Tpre` and `eIn (pre p)`
  obtain ⟨cT, dT, hcT⟩ := hTpre_pb.exists_le
  obtain ⟨cL, dL, hcL⟩ := hpre_len_pb.exists_le
  -- Bound everything by `C * 2 ^ (K * p.1.length)` whenever `p.2.length = 2 ^ p.1.length`
  set D := max dT (4 * dL) + 1
  set K := max (D + 5) 8
  have hmem_NTIME : univNE ∈ NTIME encBits (fun n => 2 ^ (K * n)) := by
    refine setOf_exists_mem_NTIME hℓ hnot
      (C := Cℓ + (cT + 4 * (cL + 1) ^ 4) * 2 ^ (2 * D) + 4) ?_
    intro z v hvlen
    set n := z.length with hn_def
    have hpow1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hn_lt : n < 2 ^ n := Nat.lt_two_pow_self
    have henc_le : (encPair encBits encBits (z, v)).length + 1 ≤ 4 * 2 ^ n := by
      simp only [encPair_apply, encBits_apply, List.length_append, length_frame, hvlen, ← hn_def]
      omega
    have hpow_enc : ((encPair encBits encBits (z, v)).length + 1) ^ D ≤
        2 ^ (2 * D) * 2 ^ (D * n) := by
      calc ((encPair encBits encBits (z, v)).length + 1) ^ D
          ≤ (4 * 2 ^ n) ^ D := Nat.pow_le_pow_left henc_le D
        _ = 4 ^ D * (2 ^ n) ^ D := Nat.mul_pow 4 (2 ^ n) D
        _ = 2 ^ (2 * D) * 2 ^ (D * n) := by
            rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul, ← pow_mul, mul_comm n D]
    have hTpre_le : Tpre (z, v) ≤ cT * 2 ^ (2 * D) * 2 ^ (D * n) := by
      calc Tpre (z, v) ≤ cT * ((encPair encBits encBits (z, v)).length + 1) ^ dT := hcT (z, v)
        _ ≤ cT * ((encPair encBits encBits (z, v)).length + 1) ^ D :=
            Nat.mul_le_mul_left cT (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
        _ ≤ cT * (2 ^ (2 * D) * 2 ^ (D * n)) := Nat.mul_le_mul_left cT hpow_enc
        _ = cT * 2 ^ (2 * D) * 2 ^ (D * n) := by ring
    have heIn_le :
        (eIn (decodeDesc (unframe (unframe z)),
          (frame (dropFrame z) ++ v).map eBit, 2 ^ (2 * n))).length + 1 ≤
          (cL + 1) * ((encPair encBits encBits (z, v)).length + 1) ^ dL := by
      have h1 := hcL (z, v)
      have h2 : 1 ≤ ((encPair encBits encBits (z, v)).length + 1) ^ dL :=
        Nat.one_le_pow _ _ (Nat.succ_pos _)
      nlinarith
    have heIn4_le :
        ((eIn (decodeDesc (unframe (unframe z)),
          (frame (dropFrame z) ++ v).map eBit, 2 ^ (2 * n))).length + 1) ^ 4 ≤
          (cL + 1) ^ 4 * 2 ^ (2 * D) * 2 ^ (D * n) := by
      calc ((eIn (decodeDesc (unframe (unframe z)),
            (frame (dropFrame z) ++ v).map eBit, 2 ^ (2 * n))).length + 1) ^ 4
          ≤ ((cL + 1) * ((encPair encBits encBits (z, v)).length + 1) ^ dL) ^ 4 :=
            Nat.pow_le_pow_left heIn_le 4
        _ = (cL + 1) ^ 4 * ((encPair encBits encBits (z, v)).length + 1) ^ (4 * dL) := by
            rw [Nat.mul_pow, ← pow_mul, mul_comm dL 4]
        _ ≤ (cL + 1) ^ 4 * ((encPair encBits encBits (z, v)).length + 1) ^ D :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
        _ ≤ (cL + 1) ^ 4 * (2 ^ (2 * D) * 2 ^ (D * n)) := Nat.mul_le_mul_left _ hpow_enc
        _ = (cL + 1) ^ 4 * 2 ^ (2 * D) * 2 ^ (D * n) := by ring
    have hclk_le : (2 ^ (2 * n) + 1) ^ 2 ≤ 4 * 2 ^ (4 * n) := by
      have h1 : 2 ^ (2 * n) + 1 ≤ 2 * 2 ^ (2 * n) := by
        have := Nat.one_le_two_pow (n := 2 * n); omega
      calc (2 ^ (2 * n) + 1) ^ 2 ≤ (2 * 2 ^ (2 * n)) ^ 2 := Nat.pow_le_pow_left h1 2
        _ = 4 * 2 ^ (4 * n) := by rw [Nat.mul_pow, ← pow_mul]; ring
    have hUterm :
        ((eIn (decodeDesc (unframe (unframe z)),
          (frame (dropFrame z) ++ v).map eBit, 2 ^ (2 * n))).length + 1) ^ 4 *
          (2 ^ (2 * n) + 1) ^ 2 ≤
          4 * (cL + 1) ^ 4 * 2 ^ (2 * D) * 2 ^ ((D + 4) * n) := by
      calc _ ≤ ((cL + 1) ^ 4 * 2 ^ (2 * D) * 2 ^ (D * n)) * (4 * 2 ^ (4 * n)) :=
            Nat.mul_le_mul heIn4_le hclk_le
        _ = 4 * (cL + 1) ^ 4 * 2 ^ (2 * D) * (2 ^ (D * n) * 2 ^ (4 * n)) := by ring
        _ = 4 * (cL + 1) ^ 4 * 2 ^ (2 * D) * 2 ^ ((D + 4) * n) := by
            rw [← pow_add, ← Nat.add_mul]
    have hpow_mono : ∀ a, a ≤ K → 2 ^ (a * n) ≤ 2 ^ (K * n) := fun a ha =>
      Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_right n ha)
    have h1n : 2 ^ n ≤ 2 ^ (K * n) := by simpa using hpow_mono 1 (by omega)
    have h4n : 4 ^ n ≤ 2 ^ (K * n) := by
      rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]; exact hpow_mono 2 (by omega)
    have hDn : 2 ^ (D * n) ≤ 2 ^ (K * n) := hpow_mono D (by omega)
    have hD4n : 2 ^ ((D + 4) * n) ≤ 2 ^ (K * n) := hpow_mono (D + 4) (by omega)
    have hU1 : Tpre (z, v) + ((eIn (decodeDesc (unframe (unframe z)),
          (frame (dropFrame z) ++ v).map eBit, 2 ^ (2 * n))).length + 1) ^ 4 *
          (2 ^ (2 * n) + 1) ^ 2 ≤
        (cT + 4 * (cL + 1) ^ 4) * 2 ^ (2 * D) * 2 ^ (K * n) := by
      have ha : Tpre (z, v) ≤ cT * 2 ^ (2 * D) * 2 ^ (K * n) :=
        hTpre_le.trans (Nat.mul_le_mul_left _ hDn)
      have hb : ((eIn (decodeDesc (unframe (unframe z)),
            (frame (dropFrame z) ++ v).map eBit, 2 ^ (2 * n))).length + 1) ^ 4 *
            (2 ^ (2 * n) + 1) ^ 2 ≤
          4 * (cL + 1) ^ 4 * 2 ^ (2 * D) * 2 ^ (K * n) :=
        hUterm.trans (Nat.mul_le_mul_left _ hD4n)
      linarith
    have h1K : 1 ≤ 2 ^ (K * n) := Nat.one_le_two_pow
    simp only [encBits_apply, ← hn_def]
    set B := (cT + 4 * (cL + 1) ^ 4) * 2 ^ (2 * D)
    set E := 2 ^ (K * n)
    have hCℓ : Cℓ * 2 ^ n ≤ Cℓ * E := Nat.mul_le_mul_left Cℓ h1n
    have hnE : n ≤ E := hn_lt.le.trans h1n
    have hEq : (Cℓ + B + 4) * E = Cℓ * E + B * E + 4 * E := by ring
    rw [hEq]
    linarith only [hnE, hCℓ, h4n, hU1, h1K]
  exact NE_subset_NEXP (mem_NE_iff.mpr ⟨K, hmem_NTIME⟩)

/-- **Uniform fixed-exponent circuit upper bound for `NTIME(2^n)`**: if `NEXP ⊆ P/poly`, then
there exists a single exponent `cU` such that every language in `NTIME(2^n)` has Boolean circuits
of size `O((n + 1) ^ cU)`. -/
theorem exists_fixed_exp_circuit_bound_of_NEXP_subset_PPoly
    (hNEXP : NEXP encBits ⊆ PPolyOn encBits) :
    ∃ cU : ℕ, ∀ A : Set (List Bool), A ∈ NTIME encBits (fun n => 2 ^ n) →
      ∃ C : ℕ, ∀ n,
        complexity interpretation (single (Language.slice (A : Language Bool) n)) ≤
          C * (n + 1) ^ cU := by
  have hUnivPPoly : (univNE : Language Bool) ∈ PPoly :=
    mem_PPolyOn_encBits_iff.mp (hNEXP univNE_mem_NEXP)
  obtain ⟨cU, hCU⟩ := mem_PPoly_iff_exists_mem_SIZE.mp hUnivPPoly
  set CU := cU
  refine ⟨cU, fun A hA => ?_⟩
  obtain ⟨V, c, hV, hmem⟩ := exists_verifier_of_mem_NTIME hA
  obtain ⟨c₂, ⟨k, State, hfin, tm, htm⟩, -⟩ := hV
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  set code := eDesc (desc eS eBit tm) with hcode
  set P := 2 * c + 4 * c₂ + 8
  set u := frame (frame code ++ List.replicate P true) with hu
  have hP_le : 2 * c + 4 * c₂ + 8 ≤ 2 ^ P := Nat.lt_two_pow_self.le
  have hP_le_u : P ≤ u.length := by
    simp only [u, length_frame, List.length_append, List.length_replicate]
    omega
  have hred : ∀ x : List Bool, x ∈ A ↔ u ++ x ∈ univNE := by
    intro x
    set z := u ++ x
    have hu1 : unframe z = frame code ++ List.replicate P true := unframe_frame_append _ _
    have hu2 : unframe (unframe z) = code := by rw [hu1]; exact unframe_frame_append _ _
    have hdrop : dropFrame z = x := dropFrame_frame_append _ _
    have hzlen : z.length = u.length + x.length := List.length_append
    have h2u : 2 ^ P ≤ 2 ^ u.length := Nat.pow_le_pow_right two_pos hP_le_u
    have hL_ge : c * 2 ^ x.length + c ≤ 2 ^ z.length := by
      have h1 : 1 ≤ 2 ^ x.length := Nat.one_le_two_pow
      rw [hzlen, pow_add]
      nlinarith
    rw [hmem x (2 ^ z.length) (by simpa [encBits_apply] using hL_ge)]
    refine exists_congr fun v => and_congr_right fun hv => ?_
    have hsteps : c₂ * ((encPair encBits encBits (x, v)).length + 1) ≤ 2 ^ (2 * z.length) := by
      have hxlt : x.length < 2 ^ z.length :=
        (by omega : x.length ≤ z.length).trans_lt Nat.lt_two_pow_self
      have h1 : (encPair encBits encBits (x, v)).length + 1 ≤ 4 * 2 ^ z.length := by
        simp only [encPair_apply, encBits_apply, List.length_append, length_frame, hv]
        omega
      have h2 : 2 ^ z.length * 2 ^ z.length = 2 ^ (2 * z.length) := by
        rw [← pow_add, two_mul]
      have h3 : 4 * c₂ ≤ 2 ^ z.length :=
        (by omega : 4 * c₂ ≤ 2 ^ P).trans (h2u.trans (Nat.pow_le_pow_right two_pos (by omega)))
      nlinarith
    obtain ⟨hhalt, hout⟩ := (htm (x, v)).runFrom_of_le hsteps
    simp only [encPair_apply, encBits_apply, encBool_apply] at hhalt hout
    rw [univNEVerifier, hu2, hdrop, hcode, decodeDesc_eDesc, universal_desc, hout]
    simp only [List.map_cons, List.map_nil, Cfg.Halted] at hhalt ⊢
    rw [hhalt]
    cases V (x, v) <;> simp [verdict, eBit]
  refine ⟨CU * (u.length + 1) ^ cU + 2, fun n => ?_⟩
  let AL : Language Bool := A
  have hcomp := complexity_le_of_append_take (univNE : Language Bool) u le_rfl
    (f := Language.slice AL n) fun r => by
      rw [Language.slice_eq_true_iff, List.take_of_length_le (by simp)]
      exact hred (List.ofFn r)
  have hU := hCU (u.length + n)
  have hpow : (u.length + n + 1) ^ cU ≤ (u.length + 1) ^ cU * (n + 1) ^ cU := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by nlinarith) cU
  have h1 : 1 ≤ (n + 1) ^ cU := Nat.one_le_pow _ _ (Nat.succ_pos n)
  calc complexity interpretation (single (Language.slice (A : Language Bool) n))
      ≤ complexity interpretation
          (single (Language.slice (univNE : Language Bool) (u.length + n))) + 2 := hcomp
    _ ≤ CU * (u.length + n + 1) ^ cU + 2 := Nat.add_le_add_right hU 2
    _ ≤ CU * ((u.length + 1) ^ cU * (n + 1) ^ cU) + 2 * (n + 1) ^ cU := by nlinarith
    _ = (CU * (u.length + 1) ^ cU + 2) * (n + 1) ^ cU := by ring

/-! ### : Linear-width succinct CNF & decoder for `NTIME(2^n)` -/

/-- **Linear-width succinct CNF and decoder for `NTIME(2^n)`**: every language `A ∈ NTIME(2^n)`
reduces to satisfiability of a succinct 3CNF whose clause-address and variable-label bit widths
grow linearly (`≤ 2 * |x| + cW`) and whose decoder circuit code is computable in polynomial time. -/
theorem exists_linear_succinctDecoder_of_mem_NTIME_two_pow {A : Set (List Bool)}
    (hA : A ∈ NTIME encBits (fun n => 2 ^ n)) :
    ∃ (k : ℕ) (State : Type) (_ : Fintype State) (_ : DecidableEq State)
      (tm : MultiTapeTM k Bool State) (n T : List Bool → ℕ) (cW : ℕ),
      ComputableInPolyTime (fun x => Tableau.Decoder.decoderCode tm (frame x, n x, T x))
        encBits encCode ∧
      ComputableInPolyTime (fun x => Tableau.clauseBits k State (T x)) encBits encUnary ∧
      ComputableInPolyTime (fun x => Tableau.labelBits k State (T x)) encBits encUnary ∧
      (∀ x, Tableau.clauseBits k State (T x) ≤ 2 * x.length + cW ∧
        Tableau.labelBits k State (T x) ≤ Tableau.clauseBits k State (T x)) ∧
      ∀ x, ∃ D : Circuit signature (Tableau.clauseBits k State (T x))
          (3 * (Tableau.labelBits k State (T x) + 1)),
        D.code = Tableau.Decoder.decoderCode tm (frame x, n x, T x) ∧
        (x ∈ A ↔ (SuccinctVerifier.toCNF D).Satisfiable) := by
  obtain ⟨c₁, c₂, m, State₀, hfin₀, ntm, hdec⟩ := hA
  obtain ⟨C, hbigO, -⟩ := MultiTapePTM.computableInO_decide_runClosedCoins (enc := encBits)
    ntm.choiceTable
  obtain ⟨k, State, hfin, tm, htm⟩ := hbigO
  let hF : Fintype State := Fintype.ofFinite State
  let hD : DecidableEq State := Classical.decEq State
  let M : ℕ := Nat.card (Turing.Action m Bool State₀)
  let n : List Bool → ℕ := fun x => 2 * x.length + 1 + M * (c₁ * 2 ^ x.length + c₂)
  let T : List Bool → ℕ := fun x => C * (n x + 1) + n x + 1
  have hn_len (x : List Bool) : (frame x).length ≤ n x := by
    simp only [n, length_frame]; omega
  have hn_T (x : List Bool) : n x < 2 * T x := by
    simp only [T]; omega
  have hpow2 : ComputableInPolyTime (fun x : List Bool => 2 ^ x.length) encBits encNat :=
    ComputableInPolyTime.binary_two_pow.comp ComputableInPolyTime.length_bits
  have hlen_nat : ComputableInPolyTime (fun x : List Bool => x.length) encBits encNat :=
    ComputableInPolyTime.unary_to_binary.comp ComputableInPolyTime.length_bits
  have hn_pt : ComputableInPolyTime n encBits encNat :=
    ComputableInPolyTime.binary_add'
      (ComputableInPolyTime.binary_add'
        (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2) hlen_nat)
        (ComputableInPolyTime.const 1))
      (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const M)
        (ComputableInPolyTime.binary_add'
          (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const c₁) hpow2)
          (ComputableInPolyTime.const c₂)))
  have hT_pt : ComputableInPolyTime T encBits encNat :=
    ComputableInPolyTime.binary_add'
      (ComputableInPolyTime.binary_add'
        (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const C)
          (ComputableInPolyTime.binary_add' hn_pt (ComputableInPolyTime.const 1)))
        hn_pt)
      (ComputableInPolyTime.const 1)
  have h2T_pt : ComputableInPolyTime (fun x => 2 * T x) encBits encNat :=
    ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2) hT_pt
  have hcol_pt : ComputableInPolyTime (fun x => Tableau.colBits (T x)) encBits encUnary :=
    ComputableInPolyTime.binary_size.comp h2T_pt
  have htime_pt : ComputableInPolyTime (fun x => Tableau.timeBits (T x)) encBits encUnary :=
    ComputableInPolyTime.binary_size.comp hT_pt
  have hcb_pt : ComputableInPolyTime (fun x => Tableau.clauseBits k State (T x))
      encBits encUnary := by
    unfold Tableau.clauseBits
    exact ComputableInPolyTime.unary_add' (ComputableInPolyTime.const 4)
      (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_add'
          (ComputableInPolyTime.const (Tableau.slotBits k State)) hcol_pt)
        htime_pt)
  have hlb_pt : ComputableInPolyTime (fun x => Tableau.labelBits k State (T x))
      encBits encUnary := by
    unfold Tableau.labelBits
    exact ComputableInPolyTime.unary_add' (ComputableInPolyTime.const 2)
      (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_add'
          (ComputableInPolyTime.const (Tableau.slotBits k State)) hcol_pt)
        htime_pt)
  have hdec_pt : ComputableInPolyTime
      (fun x => Tableau.Decoder.decoderCode tm (frame x, n x, T x)) encBits encCode :=
    (@MIP.computableInPolyTime_decoderCode k State hF hD tm).comp
      (ComputableInPolyTime.frame.prod (hn_pt.prod hT_pt))
  set K := 2 * ((C + 1) * (M * (c₁ + c₂) + 5) + 2)
  set cW := 4 + Tableau.slotBits k State + 2 * (Nat.size K + 1)
  have hT_bound (x : List Bool) : 2 * T x < 2 ^ (x.length + Nat.size K + 1) := by
    have h1 : 1 ≤ 2 ^ x.length := Nat.one_le_two_pow
    have h2 : x.length ≤ 2 ^ x.length := Nat.lt_two_pow_self.le
    have h3 : n x ≤ (M * (c₁ + c₂) + 3) * 2 ^ x.length := by
      have hMc₂ : M * c₂ ≤ M * c₂ * 2 ^ x.length := Nat.le_mul_of_pos_right _ h1
      have hEq : (M * (c₁ + c₂) + 3) * 2 ^ x.length =
          M * c₁ * 2 ^ x.length + M * c₂ * 2 ^ x.length + 3 * 2 ^ x.length := by ring
      have hnEq : n x = 2 * x.length + 1 + M * c₁ * 2 ^ x.length + M * c₂ := by
        dsimp only [n]; ring
      linarith only [h1, h2, hMc₂, hEq, hnEq]
    have h4 : 2 * T x ≤ K * 2 ^ x.length := by
      simp only [T, K]; nlinarith
    have hKlt : K < 2 ^ Nat.size K := Nat.lt_size_self K
    calc 2 * T x ≤ K * 2 ^ x.length := h4
      _ < 2 ^ Nat.size K * 2 ^ x.length := Nat.mul_lt_mul_of_pos_right hKlt (Nat.two_pow_pos _)
      _ = 2 ^ (x.length + Nat.size K) := by rw [← pow_add, add_comm]
      _ ≤ 2 ^ (x.length + Nat.size K + 1) := Nat.pow_le_pow_right two_pos (by omega)
  have hwidths (x : List Bool) :
      Tableau.clauseBits k State (T x) ≤ 2 * x.length + cW ∧
      Tableau.labelBits k State (T x) ≤ Tableau.clauseBits k State (T x) := by
    have hcol : Tableau.colBits (T x) ≤ x.length + Nat.size K + 1 :=
      Nat.size_le.mpr (hT_bound x)
    have htime : Tableau.timeBits (T x) ≤ x.length + Nat.size K + 1 :=
      Nat.size_le.mpr ((by omega : T x ≤ 2 * T x).trans_lt (hT_bound x))
    simp only [Tableau.clauseBits, Tableau.labelBits, cW]
    omega
  refine ⟨k, State, hF, hD, tm, n, T, cW, hdec_pt, hcb_pt, hlb_pt, hwidths, fun x => ?_⟩
  have hsat : x ∈ A ↔ (Tableau.succinctCNF tm (frame x) (n x) (T x)).Satisfiable := by
    rw [@Tableau.satisfiable_succinctCNF_iff k State hF hD tm (n x) (T x) (hn_T x)
      (frame x) (hn_len x), hdec.mem_iff_exists_checkChoices le_rfl]
    constructor
    · rintro ⟨w, hw, hcheck⟩
      have hw_len : w.length = M * (c₁ * 2 ^ x.length + c₂) := hw
      refine ⟨frame x ++ w, ?_, List.prefix_append _ _, ?_⟩
      · simp only [n, List.length_append, length_frame, hw_len]
      · have hrun := (htm (x, w)).runFrom_of_le (J := T x) (by
          simp only [T, n, encPair_apply, List.length_append, length_frame, encBits_apply, hw_len]
          omega)
        have hcfg : (encPair encBits encBits) (x, w) = frame x ++ w := rfl
        rw [← hcfg, hrun.2]
        change OutView.ofList (encBool (ntm.checkChoices encBits (x, w))) = OutView.one true
        rw [hcheck]
        rfl
    · rintro ⟨y, hylen, hpre, hout⟩
      obtain ⟨w, rfl⟩ := hpre
      have hw_len : w.length = M * (c₁ * 2 ^ x.length + c₂) := by
        simp only [n, List.length_append, length_frame] at hylen; omega
      refine ⟨w, hw_len, ?_⟩
      have hrun := (htm (x, w)).runFrom_of_le (J := T x) (by
        simp only [T, n, encPair_apply, List.length_append, length_frame, encBits_apply, hw_len]
        omega)
      have hcfg : (encPair encBits encBits) (x, w) = frame x ++ w := rfl
      rw [← hcfg, hrun.2] at hout
      change OutView.ofList (encBool (ntm.checkChoices encBits (x, w))) = OutView.one true at hout
      cases hb : ntm.checkChoices encBits (x, w) with
      | true => rfl
      | false => rw [hb, encBool_apply] at hout; simp [OutView.ofList] at hout
  obtain ⟨D, hDcode, _, hDeval⟩ :=
    @Tableau.Decoder.exists_decoder k State hF hD tm (frame x) (n x) (T x) (hn_T x) (hn_len x)
  have htoCNF :=
    @MIP.satisfiable_toCNF_iff_succinctCNF k State hF hD tm (frame x) (n x) (T x)
      (hn_T x) (hn_len x) D hDeval
  exact ⟨D, hDcode, hsat.trans htoCNF.symm⟩

/-- Check whether one decoded 3-literal clause `decOut` of width `3 * (r + 1)` is satisfied by
truth table `T` on padded addresses of length `r + pad` (padding `pad` trailing `false`s). -/
def checkDecodedClause (r pad : ℕ) (decOut T : List Bool) : Bool :=
  let lit (j : ℕ) : Bool :=
    let addr := (decOut.drop (j * (r + 1))).take r ++ List.replicate pad false
    let sgn := decOut.getD (j * (r + 1) + r) false
    MCSP.tableValue T addr == sgn
  lit 0 || lit 1 || lit 2

/-- Check whether truth table `T` satisfies all `2 ^ q` clauses decoded by `decCode`. -/
def checkAllClauses (q r pad : ℕ) (decCode : CircuitCode) (T : List Bool) : Bool :=
  (BitString.enumList q).all fun idx =>
    checkDecodedClause r pad (evalCircuitOutputs decCode idx) T

/-- Semantic correctness of `checkAllClauses`: it returns `true` iff the padded table assignment
satisfies `SuccinctVerifier.toCNF D`. -/
theorem checkAllClauses_eq_true_iff {q r : ℕ} (pad : ℕ)
    (D : Circuit signature q (3 * (r + 1))) (T : List Bool) :
    checkAllClauses q r pad D.code T = true ↔
      (SuccinctVerifier.toCNF D).eval
        (fun x : BitString r => MCSP.tableValue T (List.ofFn x ++ List.replicate pad false)) =
        true := by
  rw [SuccinctVerifier.eval_toCNF_eq_true_iff, checkAllClauses, List.all_eq_true]
  constructor
  · intro hall x
    have hmem : List.ofFn x ∈ BitString.enumList q :=
      BitString.mem_enumList.mpr List.length_ofFn
    have hcl := hall (List.ofFn x) hmem
    rw [evalCircuitOutputs_code] at hcl
    rw [SuccinctVerifier.eval_clause_eq_true_iff]
    have hlit (j : Fin 3) :
        ((List.ofFn (D.eval interpretation x)).drop (j.val * (r + 1))).take r =
          List.ofFn (fun i : Fin r =>
            D.eval interpretation x (SuccinctVerifier.addressWire r j i)) ∧
        (List.ofFn (D.eval interpretation x)).getD (j.val * (r + 1) + r) false =
          D.eval interpretation x (SuccinctVerifier.signWire r j) := by
      have hjr : j.val * (r + 1) + r < 3 * (r + 1) := by
        have := Nat.mul_le_mul_right (r + 1) j.isLt
        rw [Nat.succ_mul] at this; omega
      constructor
      · apply List.ext_getElem
        · simp only [List.length_take, List.length_drop, List.length_ofFn]; omega
        · intro i hi₁ hi₂
          simp only [List.length_ofFn] at hi₂
          simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn,
            SuccinctVerifier.addressWire]
      · rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hjr), List.getElem_ofFn]
        rfl
    simp only [checkDecodedClause, Bool.or_eq_true, beq_iff_eq] at hcl
    rcases hcl with (h0 | h1) | h2
    · have h0' := hlit 0; simp only [Fin.val_zero] at h0'
      exact ⟨0, by rwa [h0'.1, h0'.2] at h0⟩
    · have h1' := hlit 1; simp only [Fin.val_one] at h1'
      exact ⟨1, by rwa [h1'.1, h1'.2] at h1⟩
    · have h2' := hlit 2; simp only [Fin.val_two] at h2'
      exact ⟨2, by rwa [h2'.1, h2'.2] at h2⟩
  · intro hall idx hidx
    have hlen : idx.length = q := BitString.mem_enumList.mp hidx
    let x : BitString q := BitString.ofList q idx
    have hx : List.ofFn x = idx := BitString.ofFn_ofList hlen
    rw [← hx, evalCircuitOutputs_code]
    have hcl := (SuccinctVerifier.eval_clause_eq_true_iff D _ x).mp (hall x)
    have hlit (j : Fin 3) :
        ((List.ofFn (D.eval interpretation x)).drop (j.val * (r + 1))).take r =
          List.ofFn (fun i : Fin r =>
            D.eval interpretation x (SuccinctVerifier.addressWire r j i)) ∧
        (List.ofFn (D.eval interpretation x)).getD (j.val * (r + 1) + r) false =
          D.eval interpretation x (SuccinctVerifier.signWire r j) := by
      have hjr : j.val * (r + 1) + r < 3 * (r + 1) := by
        have := Nat.mul_le_mul_right (r + 1) j.isLt
        rw [Nat.succ_mul] at this; omega
      constructor
      · apply List.ext_getElem
        · simp only [List.length_take, List.length_drop, List.length_ofFn]; omega
        · intro i hi₁ hi₂
          simp only [List.length_ofFn] at hi₂
          simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn,
            SuccinctVerifier.addressWire]
      · rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hjr), List.getElem_ofFn]
        rfl
    simp only [checkDecodedClause, Bool.or_eq_true, beq_iff_eq]
    obtain ⟨j, hj⟩ := hcl
    fin_cases j
    · dsimp only at hj
      have h0' := hlit ⟨0, by decide⟩; dsimp only at h0'
      exact Or.inl (Or.inl (by rwa [← h0'.1, ← h0'.2] at hj))
    · dsimp only at hj
      have h1' := hlit ⟨1, by decide⟩; dsimp only at h1'
      exact Or.inl (Or.inr (by rwa [← h1'.1, ← h1'.2] at hj))
    · dsimp only at hj
      have h2' := hlit ⟨2, by decide⟩; dsimp only at h2'
      exact Or.inr (by rwa [← h2'.1, ← h2'.2] at hj)

/-- `checkDecodedClause` is polynomial-time in all its inputs. -/
theorem computableInPolyTime_checkDecodedClause {γ : Type} {encIn : γ ↪ List Bool}
    {r pad : γ → ℕ} {decOut T : γ → List Bool}
    (hr : ComputableInPolyTime r encIn encUnary)
    (hpad : ComputableInPolyTime pad encIn encUnary)
    (hdec : ComputableInPolyTime decOut encIn encBits)
    (hT : ComputableInPolyTime T encIn encBits) :
    ComputableInPolyTime (fun a => checkDecodedClause (r a) (pad a) (decOut a) (T a))
      encIn encBool := by
  open ComputableInPolyTime in
  have hlit (j : ℕ) : ComputableInPolyTime
      (fun a =>
        let addr := ((decOut a).drop (j * (r a + 1))).take (r a) ++ List.replicate (pad a) false
        let sgn := (decOut a).getD (j * (r a + 1) + r a) false
        MCSP.tableValue (T a) addr == sgn) encIn encBool := by
    have hbase := unary_mul' (const j) (unary_add' hr (const 1))
    have haddr := bitsAppend
      (bitsTakeWithInput (bitsDropWithInput hdec hbase) hr)
      ((bitsReplicate false).comp hpad)
    have hsgn := bitsGetDWithInput hdec (unary_add' hbase hr) false
    exact beq (MCSP.computableInPolyTime_tableValue.comp (hT.prod haddr)) hsgn
  have h01 := ite (hlit 0) (const true) (hlit 1)
  have h012 := ite h01 (const true) (hlit 2)
  exact h012.of_enc_eq fun a => by
    unfold checkDecodedClause
    dsimp only [Function.comp_apply]
    cases MCSP.tableValue (T a)
      (((decOut a).drop (0 * (r a + 1))).take (r a) ++ List.replicate (pad a) false) ==
      (decOut a).getD (0 * (r a + 1) + r a) false <;>
    cases MCSP.tableValue (T a)
      (((decOut a).drop (1 * (r a + 1))).take (r a) ++ List.replicate (pad a) false) ==
      (decOut a).getD (1 * (r a + 1) + r a) false <;> rfl

/-- `checkAllClauses` is polynomial-time whenever `2 ^ q` is polynomially bounded in the input. -/
theorem computableInPolyTime_checkAllClauses {γ : Type} {encIn : γ ↪ List Bool}
    {q r pad : γ → ℕ} {decCode : γ → CircuitCode} {T : γ → List Bool}
    (hq : ComputableInPolyTime q encIn encUnary)
    (hr : ComputableInPolyTime r encIn encUnary)
    (hpad : ComputableInPolyTime pad encIn encUnary)
    (hdec : ComputableInPolyTime decCode encIn encCode)
    (hT : ComputableInPolyTime T encIn encBits)
    (hqBudget : PolyBounded (fun a => (encIn a).length) (fun a => 2 ^ q a)) :
    ComputableInPolyTime (fun a => checkAllClauses (q a) (r a) (pad a) (decCode a) (T a))
      encIn encBool := by
  open ComputableInPolyTime in
  have henum := bitsEnumList_of_polyBounded hq hqBudget
  have hstep : ComputableInPolyTime
      (fun p : γ × List Bool =>
        checkDecodedClause (r p.1) (pad p.1) (evalCircuitOutputs (decCode p.1) p.2) (T p.1))
      (encPair encIn encBits) encBool :=
    computableInPolyTime_checkDecodedClause
      (hr.comp (fst encIn encBits)) (hpad.comp (fst encIn encBits))
      (computableInPolyTime_evalCircuitOutputs (hdec.comp (fst encIn encBits)) (snd encIn encBits))
      (hT.comp (fst encIn encBits))
  exact (allWithInput henum hstep).of_enc_eq fun _ => rfl

/-! ### : Explicit poly-time `binPolyDesign` & `nwTableGen` -/

/-- Exposed degree `max 1 ⌈log₂ n⌉` of the explicit binary field for `n` rows. -/
@[expose] def binFieldDeg (n : ℕ) : ℕ := max 1 (Nat.clog 2 n)

/-- `binFieldDeg n` is always nonzero. -/
theorem binFieldDeg_ne_zero (n : ℕ) : binFieldDeg n ≠ 0 :=
  (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'

/-- The explicit binary field of degree `binFieldDeg n` has at least `n` elements. -/
theorem le_two_pow_binFieldDeg (n : ℕ) : n ≤ 2 ^ binFieldDeg n :=
  (Nat.le_pow_clog one_lt_two n).trans (Nat.pow_le_pow_right two_pos (le_max_right _ _))

/-- The explicit binary field of degree `binFieldDeg n` has at most `2 * n` elements for `n ≥ 1`. -/
theorem two_pow_binFieldDeg_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ binFieldDeg n ≤ 2 * n := by
  rcases hn.eq_or_lt with rfl | hn
  · simp [binFieldDeg, Nat.clog_one_right]
  rw [binFieldDeg, max_eq_right (Nat.clog_pos one_lt_two hn)]
  have hpos : 0 < Nat.clog 2 n := Nat.clog_pos one_lt_two hn
  have hlt : 2 ^ (Nat.clog 2 n - 1) < n := by
    by_contra h
    push Not at h
    have := Nat.clog_le_of_le_pow h
    omega
  have hmul : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  omega

/-- The seed length `n * 2 ^ binFieldDeg n` is at most `2 * n ^ 2`. -/
theorem binPolyDesign_seedLength_le (n : ℕ) : n * 2 ^ binFieldDeg n ≤ 2 * n ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  calc n * 2 ^ binFieldDeg n ≤ n * (2 * n) := Nat.mul_le_mul_left n (two_pow_binFieldDeg_le hn)
    _ = 2 * n ^ 2 := by ring

/-- Exposed numbering `BinaryField e ≃ Fin (2 ^ e)` by least-significant bits first. -/
noncomputable def binFieldNum {e : ℕ} (he : e ≠ 0) : BinaryField e ≃ Fin (2 ^ e) :=
  (BinaryField.equivBits he).toEquiv.trans (BitString.equivFin e)

/-- The distinct points `0, …, n - 1` embedded in `BinaryField (binFieldDeg n)`. -/
noncomputable def binFieldPoints (n : ℕ) : Fin n ↪ BinaryField (binFieldDeg n) :=
  (Fin.castLEEmb (le_two_pow_binFieldDeg n)).trans
    (binFieldNum (binFieldDeg_ne_zero n)).symm.toEmbedding

/-- Explicit bit-indexed polynomial design over `BinaryField (binFieldDeg n)`. -/
noncomputable def binPolyDesign (n ℓ : ℕ) :
    Design (n * 2 ^ binFieldDeg n) n (ℓ - 1) (2 ^ ℓ) :=
  Design.bitPolynomial ℓ (binFieldPoints n) (binFieldNum (binFieldDeg_ne_zero n))

/-- Compute the column index `num (bitPoly i (r_j))` of row `j` in block `iBits` of
`binPolyDesign N ℓ`, using the binary-field multiplication table `tab = fieldTable e`. -/
def binPolyBit (tab : List (List (List Bool))) (e ℓ : ℕ) (iBits : List Bool) (j : ℕ) : ℕ :=
  let rj := (BitString.binaryWord e j).reverse
  let res := (List.range ℓ).foldl
    (fun (st : List Bool × List Bool) (t : ℕ) =>
      let acc' := if iBits.getD t false then BitString.listXor e [st.1, st.2] else st.1
      (acc', BinaryField.fieldMul tab st.2 rj))
    (List.replicate e false, [true])
  BitString.lsbValue res.1

/-- Explicit restriction of seed `z` to block `iBits` of `binPolyDesign N ℓ`. -/
def binPolyRestrict (tab : List (List (List Bool))) (e N ℓ : ℕ) (iBits z : List Bool) :
    List Bool :=
  (List.range N).map fun j => z.getD (j * 2 ^ e + binPolyBit tab e ℓ iBits j) false

private theorem fieldOfBits_binaryWord_reverse {e : ℕ} (he : e ≠ 0) {j : ℕ} (hj : j < 2 ^ e) :
    BinaryField.fieldOfBits (BinaryField.basis he) (BitString.binaryWord e j).reverse =
      (binFieldNum he).symm ⟨j, hj⟩ := by
  have hlen : (BitString.binaryWord e j).reverse.length = e := by
    rw [List.length_reverse, BitString.length_binaryWord hj]
  have hval : BitString.lsbValue (BitString.binaryWord e j).reverse = j := by
    rw [BitString.lsbValue_eq_binaryValue_reverse, List.reverse_reverse,
      BitString.binaryValue_binaryWord]
  set v : BitString e := (BitString.equivFin e).symm ⟨j, hj⟩
  have hofFn : List.ofFn v = (BitString.binaryWord e j).reverse := by
    refine BitString.lsbValue_injective (by simp [hlen]) ?_
    rw [BitString.lsbValue_ofFn, Equiv.apply_symm_apply, hval]
  rw [← hofFn, BinaryField.fieldOfBits_ofFn]
  exact (binFieldNum he).injective (by
    simp [binFieldNum, v])

private theorem fieldOfBits_binPolyBit_fold {e : ℕ} (he : e ≠ 0) (ℓ : ℕ)
    (i : BitString ℓ) {j : ℕ} (hj : j < 2 ^ e) :
    ∀ k ≤ ℓ,
      let rj := (BitString.binaryWord e j).reverse
      let res := (List.range k).foldl
        (fun (st : List Bool × List Bool) (t : ℕ) =>
          let acc' := if (List.ofFn i).getD t false then
              BitString.listXor e [st.1, st.2] else st.1
          (acc', BinaryField.fieldMul (BinaryField.fieldTable e) st.2 rj))
        (List.replicate e false, [true])
      res.1.length = e ∧
      BinaryField.fieldOfBits (BinaryField.basis he) res.1 =
        ∑ t ∈ Finset.range k,
          (if h : t < ℓ then if i ⟨t, h⟩ then ((binFieldNum he).symm ⟨j, hj⟩) ^ t else 0
           else 0) ∧
      BinaryField.fieldOfBits (BinaryField.basis he) res.2 =
        ((binFieldNum he).symm ⟨j, hj⟩) ^ k := by
  intro k hk
  set x : BinaryField e := (binFieldNum he).symm ⟨j, hj⟩
  set rj := (BitString.binaryWord e j).reverse
  have hrj : BinaryField.fieldOfBits (BinaryField.basis he) rj = x :=
    fieldOfBits_binaryWord_reverse he hj
  have htab := BinaryField.isMulTable_fieldTable he
  induction k with
  | zero =>
    refine ⟨by simp, ?_, ?_⟩
    · simp only [List.range_zero, List.foldl_nil, Finset.range_zero, Finset.sum_empty,
        BinaryField.fieldOfBits_basis]
      have h0 : (fun c : Fin e => (List.replicate e false).getD c false) = 0 := by
        funext c
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_replicate]
        rfl
      rw [h0, map_zero]
    · simp [BinaryField.fieldOfBits_one he]
  | succ k ih =>
    obtain ⟨hlen, hacc, hpow⟩ := ih (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set st := (List.range k).foldl
      (fun (st : List Bool × List Bool) (t : ℕ) =>
        let acc' := if (List.ofFn i).getD t false then
            BitString.listXor e [st.1, st.2] else st.1
        (acc', BinaryField.fieldMul (BinaryField.fieldTable e) st.2 rj))
      (List.replicate e false, [true])
    have hkt : k < ℓ := by omega
    have hget : (List.ofFn i).getD k false = i ⟨k, hkt⟩ :=
      List.getD_ofFn_of_lt i hkt false
    have hpow' : BinaryField.fieldOfBits (BinaryField.basis he)
        (BinaryField.fieldMul (BinaryField.fieldTable e) st.2 rj) = x ^ (k + 1) := by
      rw [BinaryField.fieldOfBits_fieldMul htab, hpow, hrj, pow_succ]
    refine ⟨?_, ?_, hpow'⟩
    · split_ifs
      · exact BitString.length_listXor e _
      · exact hlen
    · rw [Finset.sum_range_succ, hget]
      simp only [hkt, ↓reduceDIte]
      cases hi : i ⟨k, hkt⟩ with
      | false => simpa [hi] using hacc
      | true =>
        simp only [↓reduceIte]
        rw [BinaryField.fieldOfBits_listXor]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hacc, hpow]

/-- `binPolyBit` computes the column index `binFieldNum (bitPoly i (binFieldPoints N j))`. -/
theorem binPolyBit_eq (N ℓ : ℕ) (i : BitString ℓ) (j : Fin N) :
    binPolyBit (BinaryField.fieldTable (binFieldDeg N)) (binFieldDeg N) ℓ
        (List.ofFn i) j.val =
      (binFieldNum (binFieldDeg_ne_zero N)
        (bitPoly i (binFieldPoints N j))).val := by
  set e := binFieldDeg N
  have he : e ≠ 0 := binFieldDeg_ne_zero N
  have hj : j.val < 2 ^ e := j.isLt.trans_le (le_two_pow_binFieldDeg N)
  obtain ⟨hlen, hacc, _⟩ := fieldOfBits_binPolyBit_fold he ℓ i hj ℓ le_rfl
  set res := (List.range ℓ).foldl
    (fun (st : List Bool × List Bool) (t : ℕ) =>
      let acc' := if (List.ofFn i).getD t false then
          BitString.listXor e [st.1, st.2] else st.1
      (acc', BinaryField.fieldMul (BinaryField.fieldTable e) st.2
        (BitString.binaryWord e j.val).reverse))
    (List.replicate e false, [true])
  have hpt : (binFieldNum he).symm ⟨j.val, hj⟩ = binFieldPoints N j := by
    unfold binFieldPoints; rfl
  have hbitPoly : BinaryField.fieldOfBits (BinaryField.basis he) res.1 =
      bitPoly i (binFieldPoints N j) := by
    rw [hacc, bitPoly, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [t.isLt, ↓reduceDIte, hpt]
  have hofFn : List.ofFn (BinaryField.equivBits he (bitPoly i (binFieldPoints N j))) = res.1 := by
    rw [← hbitPoly]
    apply List.ext_getElem (by simp [hlen])
    intro c hc₁ hc₂
    simp only [List.length_ofFn] at hc₁
    rw [List.getElem_ofFn, BinaryField.equivBits_fieldOfBits, List.getD_eq_getElem _ _ hc₂]
  have hnum : (binFieldNum he (bitPoly i (binFieldPoints N j))).val =
      (BitString.equivFin e (BinaryField.equivBits he (bitPoly i (binFieldPoints N j)))).val := by
    unfold binFieldNum; rfl
  rw [hnum, ← BitString.lsbValue_ofFn, hofFn]
  rfl

/-- `binPolyRestrict` computes `(binPolyDesign N ℓ).restrict` on bit-lists. -/
theorem binPolyRestrict_eq (N ℓ : ℕ) (i : BitString ℓ)
    (z : BitString (N * 2 ^ binFieldDeg N)) :
    binPolyRestrict (BinaryField.fieldTable (binFieldDeg N)) (binFieldDeg N) N ℓ
        (List.ofFn i) (List.ofFn z) =
      List.ofFn ((binPolyDesign N ℓ).restrict (BitString.equivFin ℓ i) z) := by
  have he : binFieldDeg N ≠ 0 := binFieldDeg_ne_zero N
  apply List.ext_getElem (by simp [binPolyRestrict])
  intro j hj₁ hj₂
  simp only [List.length_ofFn] at hj₂
  simp only [binPolyRestrict, List.getElem_map, List.getElem_range, List.getElem_ofFn]
  have hidx : j * 2 ^ binFieldDeg N +
      binPolyBit (BinaryField.fieldTable (binFieldDeg N)) (binFieldDeg N) ℓ (List.ofFn i) j =
      (finProdFinEquiv (⟨j, hj₂⟩,
        binFieldNum he (bitPoly i (binFieldPoints N ⟨j, hj₂⟩)))).val := by
    rw [binPolyBit_eq N ℓ i ⟨j, hj₂⟩, finProdFinEquiv_apply_val]
    ring
  rw [hidx, List.getD_ofFn_of_lt z (Fin.isLt _)]
  unfold binPolyDesign
  rw [Design.restrict_bitPolynomial, Equiv.symm_apply_apply]

/-- Language defined by a truth table `T` on inputs of length `r`. -/
def tableLang (r : ℕ) (T : List Bool) : Language Bool :=
  {z | z.length = r ∧ MCSP.tableValue T z = true}

/-- Membership characterization of `tableLang`. -/
theorem mem_tableLang_iff {r : ℕ} {T z : List Bool} :
    z ∈ tableLang r T ↔ z.length = r ∧ MCSP.tableValue T z = true :=
  Iff.rfl

/-- Evaluate the hardness encoding of truth table `T` at point `y` using precomputed multiplication
table `tab`, node list `E`, and accepted-input list `pts`. -/
def encodedTableEval (tab : List (List (List Bool))) (b M : ℕ)
    (E pts : List (List Bool)) (y : List Bool) : Bool :=
  if b = 0 then false else
    AffineDisperser.traceBit ((y.drop (M * (4 * b))).take (4 * b))
      (ldeVal tab (4 * b) b M E pts
        ((List.range M).map fun i => (y.drop (i * (4 * b))).take (4 * b)))

/-- Explicit Nisan–Wigderson generator on `out` output bits using `binPolyDesign N ℓ` and
the hardness encoding of truth table `T` with parameters `(M, b)`. -/
def nwTableGen (M b N ℓ out : ℕ) (T z : List Bool) : List Bool :=
  let e := binFieldDeg N
  let tabNW := BinaryField.fieldTable e
  let tabLDE := BinaryField.fieldTable (4 * b)
  let E := BitString.enumList b
  let pts := (BitString.enumList (M * b)).filter fun u => MCSP.tableValue T (u.take (M * b))
  ((BitString.enumList ℓ).take out).map fun iBits =>
    encodedTableEval tabLDE b M E pts (binPolyRestrict tabNW e N ℓ iBits z)

private theorem encodedSlice_congr_len {L : Language Bool} {M n₁ n₂ : ℕ} (h : n₁ = n₂)
    (f₁ : BitString n₁) (f₂ : BitString n₂)
    (hf : ∀ (i : ℕ) (hi₁ : i < n₁) (hi₂ : i < n₂), f₁ ⟨i, hi₁⟩ = f₂ ⟨i, hi₂⟩) :
    encodedSlice L M n₁ f₁ = encodedSlice L M n₂ f₂ := by
  subst h
  congr 1
  funext ⟨i, hi⟩
  exact hf i hi hi

/-- `nwTableGen` agrees with the first `out` bits of the Nisan–Wigderson generator for
`binPolyDesign N ℓ` and `HardnessEncoding.encodedSlice (tableLang (M * b) T) M N`. -/
theorem nwTableGen_eq {M b N ℓ out : ℕ} (hN : N = 4 * (M + 1) * b) (hout : out ≤ 2 ^ ℓ)
    (T : List Bool) (z : BitString (N * 2 ^ binFieldDeg N)) :
    nwTableGen M b N ℓ out T (List.ofFn z) =
      (List.ofFn (generator (binPolyDesign N ℓ)
        (HardnessEncoding.encodedSlice (tableLang (M * b) T) M N) z)).take out := by
  have hb_eq : blockLength M N = b := by
    rw [blockLength, hN]
    exact Nat.mul_div_cancel_left b (by omega)
  have hlen_lhs : (nwTableGen M b N ℓ out T (List.ofFn z)).length = out := by
    simp only [nwTableGen, List.length_map, List.length_take, BitString.length_enumList]
    omega
  have hlen_rhs :
      ((List.ofFn (generator (binPolyDesign N ℓ)
        (HardnessEncoding.encodedSlice (tableLang (M * b) T) M N) z)).take out).length = out := by
    simp only [List.length_take, List.length_ofFn]; omega
  apply List.ext_getElem (hlen_lhs.trans hlen_rhs.symm)
  intro k hk₁ hk₂
  have hk_out : k < out := hlen_lhs ▸ hk₁
  have hk_pow : k < 2 ^ ℓ := hk_out.trans_le hout
  simp only [nwTableGen, List.getElem_map, List.getElem_take, List.getElem_ofFn]
  -- Identify `(BitString.enumList ℓ)[k]` with `List.ofFn ((BitString.equivFin ℓ).symm ⟨k, hk_pow⟩)`
  set i : BitString ℓ := (BitString.equivFin ℓ).symm ⟨k, hk_pow⟩
  have henum_k : (BitString.enumList ℓ)[k]'(by simp [hk_pow]) = List.ofFn i := by
    simp only [BitString.enumList_eq_ofFn, List.getElem_ofFn, i]
  rw [henum_k, binPolyRestrict_eq N ℓ i z]
  set y : BitString N := (binPolyDesign N ℓ).restrict (BitString.equivFin ℓ i) z
  have hy_eq : encodedTableEval (BinaryField.fieldTable (4 * b)) b M (BitString.enumList b)
        ((BitString.enumList (M * b)).filter fun u => MCSP.tableValue T (u.take (M * b)))
        (List.ofFn y) =
      encodedProgram M (fun u => decide (u.length = M * b) && MCSP.tableValue T u)
        (List.ofFn y) (List.ofFn y).length := by
    rw [encodedProgram, List.length_ofFn, hb_eq, encodedProgramAt, encodedTableEval]
    have hfilt : ((BitString.enumList (M * b)).filter
          fun u => MCSP.tableValue T (u.take (M * b))) =
        ((BitString.enumList (M * b)).filter
          fun u => decide ((u.take (M * b)).length = M * b) &&
            MCSP.tableValue T (u.take (M * b))) := by
      refine List.filter_congr fun u hu => ?_
      have hulen : u.length = M * b := BitString.mem_enumList.mp hu
      simp [hulen]
    rw [hfilt]
  rw [hy_eq, encodedProgram_eq (L := tableLang (M * b) T) (fun u => by
    change (u.length = M * b ∧ MCSP.tableValue T u = true) ↔ _
    simp [Bool.and_eq_true])]
  have hidx_eq : BitString.equivFin ℓ i = ⟨k, hk_pow⟩ := Equiv.apply_symm_apply _ _
  rw [generator_apply, ← hidx_eq]
  exact encodedSlice_congr_len List.length_ofFn _ y fun j hj₁ _ => List.getElem_ofFn hj₁

/-- Polynomial-time computability of `BitString.lsbValue` into unary when `2 ^ w.length` is
polynomially bounded. -/
private theorem computableInPolyTime_lsbValue_bounded {γ : Type} {encIn : γ ↪ List Bool}
    {w : γ → List Bool} (hw : ComputableInPolyTime w encIn encBits)
    (hpow : PolyBounded (fun a => (encIn a).length) (fun a => 2 ^ (w a).length)) :
    ComputableInPolyTime (fun a => BitString.lsbValue (w a)) encIn encUnary := by
  open ComputableInPolyTime in
  have hrev := bitsReverseWithInput hw
  have hstep : ComputableInPolyTime (fun p : ℕ × Bool => 2 * p.1 + p.2.toNat)
      (encPair encUnary encBool) encUnary :=
    unary_add' (unary_mul' (const 2) (fst encUnary encBool))
      (bool_toUnary.comp (snd encUnary encBool))
  have hfold_eq : ∀ l : List Bool,
      l.reverse.foldl (fun acc (b : Bool) => 2 * acc + b.toNat) 0 = BitString.lsbValue l := by
    intro l
    induction l with
    | nil => rfl
    | cons b l ih =>
      simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
        BitString.lsbValue, ih]
      omega
  have hspec := (foldl_spec (encA := encBool) (encB := encUnary) (encL := encBits)
    (list := fun a => (w a).reverse) (init := fun _ => 0)
    (step := fun acc b => 2 * acc + b.toNat)
    hrev (const 0) hstep
    (fun _ consumed acc => acc < 2 ^ consumed.length)
    (fun _ => by simp)
    (fun _ consumed acc b _ hacc => by
      simp only [List.length_append, List.length_singleton, pow_succ]
      have := Bool.toNat_le b
      omega)
    (size := fun a => 2 ^ (w a).length) hpow
    (fun a consumed acc hpre hacc => by
      have hle : consumed.length ≤ (w a).length := by
        simpa [List.length_reverse] using hpre.length_le
      have hpow_le : 2 ^ consumed.length ≤ 2 ^ (w a).length :=
        Nat.pow_le_pow_right two_pos hle
      simp only [encUnary_apply, List.length_replicate]
      omega)).1
  exact hspec.of_enc_eq fun a => by rw [hfold_eq]

/-- Polynomial-time computability of `BinaryField.fieldTable w` when `2 ^ (w + 1)` is
polynomially bounded. -/
theorem computableInPolyTime_fieldTable_bounded {γ : Type} {encIn : γ ↪ List Bool}
    {w : γ → ℕ} (hw : ComputableInPolyTime w encIn encUnary)
    (hpow : PolyBounded (fun a => (encIn a).length) (fun a => 2 ^ (w a + 1))) :
    ComputableInPolyTime (fun a => BinaryField.fieldTable (w a)) encIn BinaryField.encTable := by
  open ComputableInPolyTime in
  obtain ⟨C, D, hCD⟩ := hpow.exists_le
  have hbound : ComputableInPolyTime (fun a => C * ((encIn a).length + 1) ^ D) encIn encUnary :=
    unary_mul' (const C) ((unary_pow D).comp (unary_add' (encoding_length encIn) (const 1)))
  have h2pow : ComputableInPolyTime (fun a => 2 ^ (w a + 1)) encIn encUnary :=
    binary_to_unary_bounded (binary_two_pow.comp (unary_add' hw (const 1))) hbound hCD
  have hmod : ComputableInPolyTime (fun a => BinaryField.modulusBits (w a)) encIn encBits := by
    unfold BinaryField.modulusBits
    exact BinaryField.computableInPolyTime_bits_unary.comp
      (BinaryField.computableInPolyTime_leastIrreducibleCode.comp (h2pow.prod hw))
  unfold BinaryField.fieldTable
  exact BinaryField.computableInPolyTime_powerMulTable.comp hmod

/-- Polynomial-time computability of `binPolyBit` when `2 ^ e` is polynomially bounded. -/
private theorem computableInPolyTime_binPolyBit {γ : Type} {encIn : γ ↪ List Bool}
    {tab : γ → List (List (List Bool))} {e ℓ : γ → ℕ} {iBits : γ → List Bool} {j : γ → ℕ}
    (htab : ComputableInPolyTime tab encIn BinaryField.encTable)
    (he : ComputableInPolyTime e encIn encUnary)
    (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hi : ComputableInPolyTime iBits encIn encBits)
    (hj : ComputableInPolyTime j encIn encUnary)
    (htab_len : ∀ a, (tab a).length = e a)
    (hePow : PolyBounded (fun a => (encIn a).length) (fun a => 2 ^ e a)) :
    ComputableInPolyTime (fun a => binPolyBit (tab a) (e a) (ℓ a) (iBits a) (j a))
      encIn encUnary := by
  open ComputableInPolyTime in
  have hrj : ComputableInPolyTime (fun a => (BitString.binaryWord (e a) (j a)).reverse)
      encIn encBits :=
    bitsReverseWithInput (binaryWord_polyTime he (unary_to_binary.comp hj))
  let encP := encPair (encPair BinaryField.encTable encUnary) (encPair encBits encBits)
  let par : γ → (List (List (List Bool)) × ℕ) × (List Bool × List Bool) :=
    fun a => ((tab a, e a), (iBits a, (BitString.binaryWord (e a) (j a)).reverse))
  have hpar : ComputableInPolyTime par encIn encP :=
    (htab.prod he).prod (hi.prod hrj)
  let encSt := encPair encBits encBits
  let encStep := encPair (encPair encP encSt) encUnary
  have hstep : ComputableInPolyTime
      (fun q : (((List (List (List Bool)) × ℕ) × (List Bool × List Bool)) ×
          (List Bool × List Bool)) × ℕ =>
        (if q.1.1.2.1.getD q.2 false then
            BitString.listXor q.1.1.1.2 [q.1.2.1, q.1.2.2] else q.1.2.1,
          BinaryField.fieldMul q.1.1.1.1 q.1.2.2 q.1.1.2.2))
      encStep encSt := by
    have hq1 := fst (encPair encP encSt) encUnary
    have hqp := hq1.fst'
    have hqs := hq1.snd'
    have hqt := snd (encPair encP encSt) encUnary
    have hcond := bitsGetDWithInput hqp.snd'.fst' hqt false
    have hpairList : ComputableInPolyTime
        (fun q : (((List (List (List Bool)) × ℕ) × (List Bool × List Bool)) ×
            (List Bool × List Bool)) × ℕ => [q.1.2.1, q.1.2.2])
        encStep (encList encBits) :=
      (cons encBits).comp (hqs.fst'.prod ((cons encBits).comp (hqs.snd'.prod (const []))))
    have hxor := bitsXorWithInput hqp.fst'.snd' hpairList
    have hacc' := ite hcond hxor hqs.fst'
    have hpow' := BinaryField.computableInPolyTime_fieldMul' hqp.fst'.fst' hqs.snd' hqp.snd'.snd'
    exact hacc'.prod hpow'
  have hinit : ComputableInPolyTime (fun a => (List.replicate (e a) false, [true])) encIn encSt :=
    ((bitsReplicate false).comp he).prod (const [true])
  have hsize_pb : PolyBounded (fun a => (encIn a).length) (fun a => 3 * (e a) + 3) :=
    ((PolyBounded.const 3).mul he.polyBounded).add (.const 3)
  have hfold := (foldlWith_spec (encIn := encIn) (encP := encP) (encA := encUnary)
    (encL := encList encUnary) (encB := encSt)
    (par := par) (list := fun a => List.range (ℓ a))
    (init := fun a => (List.replicate (e a) false, [true]))
    (step := fun p st t =>
      (if p.2.1.getD t false then BitString.listXor p.1.2 [st.1, st.2] else st.1,
        BinaryField.fieldMul p.1.1 st.2 p.2.2))
    hpar (unary_range' hℓ) hinit hstep
    (fun a _ st => st.1.length = e a ∧ st.2.length ≤ e a + 1)
    (fun a => by simp)
    (fun a _ st t _ hst => by
      refine ⟨?_, ?_⟩
      · split_ifs
        · exact BitString.length_listXor (e a) _
        · exact hst.1
      · rw [BinaryField.length_fieldMul, htab_len a]; omega)
    (size := fun a => 3 * (e a) + 3) hsize_pb
    (fun a _ st _ hst => by
      simp only [encSt, length_encPair, encBits_apply]
      omega))
  have hacc_pt : ComputableInPolyTime
      (fun a => ((List.range (ℓ a)).foldl
        (fun st t =>
          (if (iBits a).getD t false then BitString.listXor (e a) [st.1, st.2] else st.1,
            BinaryField.fieldMul (tab a) st.2 (BitString.binaryWord (e a) (j a)).reverse))
        (List.replicate (e a) false, [true])).1)
      encIn encBits := hfold.1.fst'
  have hacc_len : ∀ a,
      (((List.range (ℓ a)).foldl
        (fun st t =>
          (if (iBits a).getD t false then BitString.listXor (e a) [st.1, st.2] else st.1,
            BinaryField.fieldMul (tab a) st.2 (BitString.binaryWord (e a) (j a)).reverse))
        (List.replicate (e a) false, [true])).1).length = e a :=
    fun a => (hfold.2 a).1
  exact computableInPolyTime_lsbValue_bounded hacc_pt
    (hePow.mono fun a => by rw [hacc_len a])

/-- Polynomial-time computability of `nwTableGen` when `2 ^ (M * b)`, `2 ^ (4 * b + 1)`, and
`2 ^ (binaryFieldDegree N + 1)` are polynomially bounded in the input. -/
theorem computableInPolyTime_nwTableGen {γ : Type} {encIn : γ ↪ List Bool}
    {M b N ℓ out : γ → ℕ} {T z : γ → List Bool}
    (hM : ComputableInPolyTime M encIn encUnary)
    (hb : ComputableInPolyTime b encIn encUnary)
    (hN : ComputableInPolyTime N encIn encUnary)
    (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hout : ComputableInPolyTime out encIn encUnary)
    (hT : ComputableInPolyTime T encIn encBits)
    (hz : ComputableInPolyTime z encIn encBits)
    (hMbPow : PolyBounded (fun a => (encIn a).length) (fun a => 2 ^ (M a * b a)))
    (hbPow : PolyBounded (fun a => (encIn a).length) (fun a => 2 ^ (4 * b a + 1)))
    (hℓPow : PolyBounded (fun a => (encIn a).length) (fun a => 2 ^ ℓ a)) :
    ComputableInPolyTime
      (fun a => nwTableGen (M a) (b a) (N a) (ℓ a) (out a) (T a) (z a))
      encIn encBits := by
  open ComputableInPolyTime in
  have he_pt : ComputableInPolyTime (fun a => binFieldDeg (N a)) encIn encUnary := by
    unfold binFieldDeg
    have hclog : ComputableInPolyTime (fun a => Nat.clog 2 (N a)) encIn encUnary := by
      have hlog := binary_log_two.comp (unary_to_binary.comp (unary_sub' hN (const 1)))
      have h01 := ite_decide (decide_eq' hN (const 0)) (const 0)
        (ite_decide (decide_eq' hN (const 1)) (const 0) (unary_add' hlog (const 1)))
      exact h01.of_enc_eq fun a => by
        congr 1
        rcases hNa : N a with _ | n
        · simp
        · rcases n with _ | n
          · simp
          · simp only [Nat.add_eq_zero_iff, and_false, ↓reduceIte, Nat.add_eq_right, one_ne_zero,
              Function.comp_apply, hNa, Nat.add_sub_cancel]
            change Nat.clog 2 (n + 2) = Nat.log 2 (n + 1) + 1
            have hle1 : Nat.clog 2 (n + 2) ≤ Nat.log 2 (n + 1) + 1 :=
              Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self one_lt_two (n + 1))
            have hlt1 : 2 ^ Nat.log 2 (n + 1) < n + 2 :=
              Nat.lt_succ_of_le (Nat.pow_log_le_self 2 (Nat.succ_ne_zero n))
            have hlt2 : Nat.log 2 (n + 1) < Nat.clog 2 (n + 2) := by
              by_contra h
              push Not at h
              have := (Nat.le_pow_clog one_lt_two (n + 2)).trans (Nat.pow_le_pow_right two_pos h)
              omega
            omega
    exact unary_max.comp ((const 1).prod hclog)
  have hePow1 : PolyBounded (fun a => (encIn a).length)
      (fun a => 2 ^ (binFieldDeg (N a) + 1)) := by
    refine (((PolyBounded.const 4).mul hN.polyBounded).add (.const 4)).mono fun a => ?_
    rw [pow_succ]
    rcases Nat.eq_zero_or_pos (N a) with h0 | hpos
    · simp [h0, binFieldDeg]
    · have := two_pow_binFieldDeg_le hpos; omega
  have hePow : PolyBounded (fun a => (encIn a).length)
      (fun a => 2 ^ binFieldDeg (N a)) :=
    hePow1.mono fun a => Nat.pow_le_pow_right two_pos (Nat.le_succ _)
  have htabNW := computableInPolyTime_fieldTable_bounded he_pt hePow1
  have h4b := unary_mul' (const 4) hb
  have htabLDE := computableInPolyTime_fieldTable_bounded h4b hbPow
  have hbPow0 : PolyBounded (fun a => (encIn a).length) (fun a => 2 ^ b a) :=
    hbPow.mono fun a => Nat.pow_le_pow_right two_pos (by omega)
  have hE := bitsEnumList_of_polyBounded hb hbPow0
  have hMb := unary_mul' hM hb
  have hEn := bitsEnumList_of_polyBounded hMb hMbPow
  have hpts : ComputableInPolyTime
      (fun a => (BitString.enumList (M a * b a)).filter
        fun u => MCSP.tableValue (T a) (u.take (M a * b a)))
      encIn (encList encBits) :=
    filterWithInput hEn
      (MCSP.computableInPolyTime_tableValue.comp
        ((hT.comp (fst encIn encBits)).prod
          (bitsTakeWithInput (snd encIn encBits) (hMb.comp (fst encIn encBits)))))
  have hidxList : ComputableInPolyTime
      (fun a => (BitString.enumList (ℓ a)).take (out a)) encIn (encList encBits) :=
    listTakeWithInput (bitsEnumList_of_polyBounded hℓ hℓPow) hout
  -- For each `(a, iBits)`, compute `binPolyRestrict` then `encodedTableEval`
  let encAI := encPair encIn encBits
  have hfst : ComputableInPolyTime (fun p : γ × List Bool => p.1) encAI encIn := fst encIn encBits
  have hsnd : ComputableInPolyTime (fun p : γ × List Bool => p.2) encAI encBits := snd encIn encBits
  have hrestrict : ComputableInPolyTime
      (fun p : γ × List Bool =>
        binPolyRestrict (BinaryField.fieldTable (binFieldDeg (N p.1)))
          (binFieldDeg (N p.1)) (N p.1) (ℓ p.1) p.2 (z p.1))
      encAI encBits := by
    let encAIJ := encPair encAI encUnary
    have hp1 : ComputableInPolyTime (fun q : (γ × List Bool) × ℕ => q.1.1) encAIJ encIn :=
      hfst.comp (fst encAI encUnary)
    have hpi : ComputableInPolyTime (fun q : (γ × List Bool) × ℕ => q.1.2) encAIJ encBits :=
      hsnd.comp (fst encAI encUnary)
    have hpj : ComputableInPolyTime (fun q : (γ × List Bool) × ℕ => q.2) encAIJ encUnary :=
      snd encAI encUnary
    have hlen_le : PolyBounded (fun q : (γ × List Bool) × ℕ => (encAIJ q).length)
        (fun q => (encIn q.1.1).length) :=
      PolyBounded.self.mono fun q => by
        simp only [encAIJ, encAI, length_encPair]; omega
    have htab_len : ∀ q : (γ × List Bool) × ℕ,
        (BinaryField.fieldTable (binFieldDeg (N q.1.1))).length =
          binFieldDeg (N q.1.1) := fun q =>
      (BinaryField.isMulTable_fieldTable (binFieldDeg_ne_zero (N q.1.1))).1
    have hbit := computableInPolyTime_binPolyBit
      (htabNW.comp hp1) (he_pt.comp hp1) (hℓ.comp hp1) hpi hpj htab_len (hePow.comp hlen_le)
    obtain ⟨Ce, De, hCe⟩ := (hePow.comp hlen_le).exists_le
    have h2e_bound : ComputableInPolyTime (fun q : (γ × List Bool) × ℕ =>
        Ce * ((encAIJ q).length + 1) ^ De) encAIJ encUnary :=
      unary_mul' (const Ce) ((unary_pow De).comp (unary_add' (encoding_length encAIJ) (const 1)))
    have h2e := binary_to_unary_bounded (binary_two_pow.comp (he_pt.comp hp1)) h2e_bound hCe
    have hpos := unary_add' (unary_mul' hpj h2e) hbit
    have hget := bitsGetDWithInput (hz.comp hp1) hpos false
    exact mapToBitsWithInput (unary_range' (hN.comp hfst)) hget
  have heval : ComputableInPolyTime
      (fun p : γ × List Bool =>
        encodedTableEval (BinaryField.fieldTable (4 * b p.1)) (b p.1) (M p.1)
          (BitString.enumList (b p.1))
          ((BitString.enumList (M p.1 * b p.1)).filter
            fun u => MCSP.tableValue (T p.1) (u.take (M p.1 * b p.1)))
          (binPolyRestrict (BinaryField.fieldTable (binFieldDeg (N p.1)))
            (binFieldDeg (N p.1)) (N p.1) (ℓ p.1) p.2 (z p.1)))
      encAI encBool := by
    have h4b' := h4b.comp hfst
    have hM' := hM.comp hfst
    have hb' := hb.comp hfst
    have hxs : ComputableInPolyTime
        (fun p : γ × List Bool =>
          (List.range (M p.1)).map fun i =>
            ((binPolyRestrict (BinaryField.fieldTable (binFieldDeg (N p.1)))
              (binFieldDeg (N p.1)) (N p.1) (ℓ p.1) p.2 (z p.1)).drop
                (i * (4 * b p.1))).take (4 * b p.1))
        encAI (encList encBits) :=
      mapWithInput (unary_range' hM')
        (bitsTakeWithInput
          (bitsDropWithInput (hrestrict.comp (fst encAI encUnary))
            (unary_mul' (snd encAI encUnary) (h4b'.comp (fst encAI encUnary))))
          (h4b'.comp (fst encAI encUnary)))
    have hlde := computableInPolyTime_ldeVal' (htabLDE.comp hfst) h4b' hb' hM'
      (hE.comp hfst) (hpts.comp hfst) hxs
    have htail := bitsTakeWithInput (bitsDropWithInput hrestrict (unary_mul' hM' h4b')) h4b'
    have htr := AffineDisperser.computableInPolyTime_traceBit' htail hlde
    unfold encodedTableEval
    exact ite_decide (decide_eq' hb' (const 0)) (const false) htr
  exact mapToBitsWithInput hidxList heval

end CslibFrontier.Complexity
