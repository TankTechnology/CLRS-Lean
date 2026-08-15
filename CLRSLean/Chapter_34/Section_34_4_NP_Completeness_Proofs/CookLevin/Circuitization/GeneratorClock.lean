import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialClock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.EncodingBounds

/-!
# Exact unary dimensions for the Cook--Levin generator

This module instantiates the generic exact polynomial clock at every primary
dimension used by the verifier-circuit generator.  It also recovers finiteness
of the source alphabet from the finite input alphabet already carried by the
normalized verifier machine, so the universal reduction needs no additional
typeclass premise.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing
open PolyBuilder

/-- The verifier machine's finite pair-encoding alphabet implies finiteness of
the underlying language alphabet. -/
@[reducible] noncomputable def VerifierWitness.alphabetFintype {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) : Fintype Γ := by
  letI : Fintype (W.machine.tm.Γ W.machine.tm.k₀) :=
    W.machine.tm.Γk₀Fin
  letI : Fintype (Option Γ) :=
    Fintype.ofEquiv (W.machine.tm.Γ W.machine.tm.k₀)
      W.machine.inputAlphabet
  exact Fintype.ofInjective some (Option.some_injective Γ)

/-! ## Certificate and machine-shape dimensions -/

/-- Exact unary certificate-bound clock. -/
def certificateClock {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List Unit :=
  exactPolynomialClock W.certificateBound input

@[simp] theorem certificateClock_length {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    (certificateClock W input).length =
      W.certificateBound.eval input.length :=
  exactPolynomialClock_length W.certificateBound input

/-- Concrete polynomial-time implementation of the certificate clock. -/
noncomputable def certificateClock_computableInPolyTime {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) :
    TM2ComputableInPolyTime id id (certificateClock W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialClock_computableInPolyTime W.certificateBound

/-- Exact unary clock for the uniform pair-encoded verifier input bound. -/
def verifierInputClock {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List Unit :=
  exactPolynomialClock (verifierInputBound W) input

@[simp] theorem verifierInputClock_length {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    (verifierInputClock W input).length =
      (verifierInputBound W).eval input.length :=
  exactPolynomialClock_length (verifierInputBound W) input

/-- Concrete polynomial-time implementation of the verifier-input clock. -/
noncomputable def verifierInputClock_computableInPolyTime {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) :
    TM2ComputableInPolyTime id id (verifierInputClock W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialClock_computableInPolyTime (verifierInputBound W)

/-- Exact unary clock for the stuttering tableau horizon. -/
def verifierHorizonClock {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List Unit :=
  exactPolynomialClock (verifierHorizon W) input

@[simp] theorem verifierHorizonClock_length {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    (verifierHorizonClock W input).length =
      (verifierHorizon W).eval input.length :=
  exactPolynomialClock_length (verifierHorizon W) input

/-- Concrete polynomial-time implementation of the horizon clock. -/
noncomputable def verifierHorizonClock_computableInPolyTime {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) :
    TM2ComputableInPolyTime id id (verifierHorizonClock W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialClock_computableInPolyTime (verifierHorizon W)

/-- Exact unary clock for the uniform tableau stack height. -/
def verifierHeightClock {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List Unit :=
  exactPolynomialClock (verifierHeight W) input

@[simp] theorem verifierHeightClock_length {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    (verifierHeightClock W input).length =
      (verifierHeight W).eval input.length :=
  exactPolynomialClock_length (verifierHeight W) input

/-- Concrete polynomial-time implementation of the height clock. -/
noncomputable def verifierHeightClock_computableInPolyTime {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) :
    TM2ComputableInPolyTime id id (verifierHeightClock W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialClock_computableInPolyTime (verifierHeight W)

/-! ## Final circuit and serialization envelopes -/

/-- Exact unary clock for the published verifier-circuit gate bound. -/
def verifierGateBoundClock {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List Unit :=
  exactPolynomialClock (verifierCircuitGateBound W) input

@[simp] theorem verifierGateBoundClock_length {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) (input : List Γ) :
    (verifierGateBoundClock W input).length =
      (verifierCircuitGateBound W).eval input.length :=
  exactPolynomialClock_length (verifierCircuitGateBound W) input

/-- Concrete polynomial-time implementation of the gate-bound clock. -/
noncomputable def verifierGateBoundClock_computableInPolyTime {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) :
    TM2ComputableInPolyTime id id (verifierGateBoundClock W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialClock_computableInPolyTime
    (verifierCircuitGateBound W)

/-- Exact unary clock for the published serialized-circuit bound. -/
def verifierEncodingBoundClock {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List Unit :=
  exactPolynomialClock (verifierCircuitEncodingBound W) input

@[simp] theorem verifierEncodingBoundClock_length {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) (input : List Γ) :
    (verifierEncodingBoundClock W input).length =
      (verifierCircuitEncodingBound W).eval input.length :=
  exactPolynomialClock_length (verifierCircuitEncodingBound W) input

/-- Concrete polynomial-time implementation of the serialization-bound
clock. -/
noncomputable def verifierEncodingBoundClock_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    TM2ComputableInPolyTime id id (verifierEncodingBoundClock W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialClock_computableInPolyTime
    (verifierCircuitEncodingBound W)

end CLRS.Chapter34.Turing.CookLevin
