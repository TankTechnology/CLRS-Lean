import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.ValidityBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Bounds

/-!
# Polynomial gate bound for the verifier circuit

All coefficients below depend only on the fixed verifier machine.  The public
instance contributes only through its length and the verifier's published
certificate, horizon, and height polynomials.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Fixed-machine coefficient bounding the Boolean width of one row. -/
def cfgBitCoefficient (tm : _root_.Turing.FinTM2) : Nat := by
  letI := tm.kFin
  exact 1 + (labelCount tm + 1) + stateCount tm +
    ∑ k : tm.K, ((reachableAlphabet tm k).card + 3)

/-- One row has affine width in the public stack-height bound. -/
theorem cfgBitCount_le (tm : _root_.Turing.FinTM2) (H : Nat) :
    cfgBitCount tm H ≤ cfgBitCoefficient tm * (H + 1) := by
  letI := tm.kFin
  let fixed := 1 + (labelCount tm + 1) + stateCount tm
  have hfixed : fixed ≤ fixed * (H + 1) :=
    Nat.le_mul_of_pos_right fixed (by omega)
  have hstacks :
      (∑ k : tm.K,
        ((H + 1) + H * ((reachableAlphabet tm k).card + 1))) ≤
      ∑ k : tm.K, ((reachableAlphabet tm k).card + 3) * (H + 1) := by
    apply Finset.sum_le_sum
    intro k _
    nlinarith
  change fixed + (∑ k : tm.K,
      ((H + 1) + H * ((reachableAlphabet tm k).card + 1))) ≤ _
  change _ ≤ (fixed + ∑ k : tm.K,
    ((reachableAlphabet tm k).card + 3)) * (H + 1)
  rw [Nat.add_mul, Finset.sum_mul]
  exact Nat.add_le_add hfixed hstacks

/-- Fixed coefficient reducing the local-transition width expression to an
affine function of the public row height. -/
def transitionWidthCoefficient (tm : _root_.Turing.FinTM2) : Nat :=
  cfgBitCoefficient tm * (maxPushesPerStep tm + 1) +
    (maxPushesPerStep tm + 1) + cfgBitCoefficient tm + 2

/-- Fixed coefficient controlling the complete local transition cost. -/
def transitionHeightCoefficient (tm : _root_.Turing.FinTM2) : Nat :=
  transitionCircuitGateCoefficient tm * transitionWidthCoefficient tm

private theorem transitionWidth_le (tm : _root_.Turing.FinTM2) (H : Nat) :
    cfgBitCount tm (workHeight tm H) + workHeight tm H +
        cfgBitCount tm H + H + 1 ≤
      transitionWidthCoefficient tm * (H + 1) := by
  let M := maxPushesPerStep tm
  have hwork : workHeight tm H + 1 ≤ (M + 1) * (H + 1) := by
    simp only [workHeight, M]
    nlinarith
  have hcfgWork : cfgBitCount tm (workHeight tm H) ≤
      cfgBitCoefficient tm * ((M + 1) * (H + 1)) :=
    (cfgBitCount_le tm (workHeight tm H)).trans
      (Nat.mul_le_mul_left _ hwork)
  have hcfg := cfgBitCount_le tm H
  simp only [transitionWidthCoefficient]
  calc
    cfgBitCount tm (workHeight tm H) + workHeight tm H +
          cfgBitCount tm H + H + 1 ≤
        cfgBitCoefficient tm * ((M + 1) * (H + 1)) +
          (M + 1) * (H + 1) + cfgBitCoefficient tm * (H + 1) +
          (H + 1) + (H + 1) := by
      omega
    _ = (cfgBitCoefficient tm * (M + 1) + (M + 1) +
          cfgBitCoefficient tm + 2) * (H + 1) := by ring

/-- A local transition costs at most a fixed coefficient times `H + 1`. -/
theorem transitionCircuitGateCost_affine_le
    (tm : _root_.Turing.FinTM2) (H : Nat) :
    transitionCircuitGateCost tm H ≤
      transitionHeightCoefficient tm * (H + 1) := by
  calc
    transitionCircuitGateCost tm H ≤ transitionCircuitGateCoefficient tm *
        (cfgBitCount tm (workHeight tm H) + workHeight tm H +
          cfgBitCount tm H + H + 1) := transitionCircuitGateCost_le tm H
    _ ≤ transitionCircuitGateCoefficient tm *
        (transitionWidthCoefficient tm * (H + 1)) :=
      Nat.mul_le_mul_left _ (transitionWidth_le tm H)
    _ = transitionHeightCoefficient tm * (H + 1) := by
      simp [transitionHeightCoefficient, Nat.mul_assoc]

/-- The certificate-shape circuit is quadratic in the certificate bound and
linear in the fixed-instance length and row height. -/
theorem verifierInputShapeGateCost_le {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ) :
    verifierInputShapeGateCost W H x ≤
      H + (W.certificateBound.eval x.length + 1) *
        (W.certificateBound.eval x.length + x.length + 3) +
        W.certificateBound.eval x.length + 2 := by
  let B := W.certificateBound.eval x.length
  have harms : (∑ length : Fin (B + 1),
      verifierInputArmGateCost H x.length length.val) ≤
      ∑ _length : Fin (B + 1), (B + x.length + 3) := by
    apply Finset.sum_le_sum
    intro length _
    unfold verifierInputArmGateCost
    split <;> omega
  unfold verifierInputShapeGateCost
  change H + (∑ length : Fin (B + 1),
      verifierInputArmGateCost H x.length length.val) + (B + 2) ≤ _
  calc
    H + (∑ length : Fin (B + 1),
        verifierInputArmGateCost H x.length length.val) + (B + 2) ≤
      H + (∑ _length : Fin (B + 1), (B + x.length + 3)) +
        (B + 2) := Nat.add_le_add_right (Nat.add_le_add_left harms H) _
    _ = H + (B + 1) * (B + x.length + 3) + B + 2 := by
      rw [show (∑ _length : Fin (B + 1), (B + x.length + 3)) =
          (B + 1) * (B + x.length + 3) by simp]
      simp only [Nat.add_assoc]

private theorem acceptingOutputCircuitGateCost_le
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (output : List (tm.Γ tm.k₁)) :
    acceptingOutputCircuitGateCost tm H output ≤ 6 * cfgBitCount tm H + 1 := by
  unfold acceptingOutputCircuitGateCost
  split <;> omega

/-- Numeric form of the advertised polynomial bound. -/
def verifierCircuitGateBoundNat {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (n : Nat) : Nat :=
  let H := (verifierHeight W).eval n
  let T := (verifierHorizon W).eval n
  let B := W.certificateBound.eval n
  let width := cfgBitCoefficient W.machine.tm * (H + 1)
  let validity := validCfgGateCoefficient W.machine.tm * (H + 1)
  let transition := transitionHeightCoefficient W.machine.tm * (H + 1)
  (T + 1) * width + 2 + (T + 1) * validity + T * transition +
    (6 * width + 1) +
    (H + (B + 1) * (B + n + 3) + B + 2) +
    (6 * width + 1) + ((T + 1) + T + 3 + 1)

/-- Explicit fixed-verifier polynomial controlling the final gate count. -/
def verifierCircuitGateBound {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) : Polynomial Nat :=
  let heightFactor := verifierHeight W + 1
  let width := Polynomial.C (cfgBitCoefficient W.machine.tm) * heightFactor
  let validity := Polynomial.C (validCfgGateCoefficient W.machine.tm) *
    heightFactor
  let transition := Polynomial.C (transitionHeightCoefficient W.machine.tm) *
    heightFactor
  let T := verifierHorizon W
  let B := W.certificateBound
  (T + 1) * width + 2 + (T + 1) * validity + T * transition +
    (6 * width + 1) +
    (verifierHeight W + (B + 1) * (B + Polynomial.X + 3) + B + 2) +
    (6 * width + 1) + ((T + 1) + T + 3 + 1)

@[simp] theorem verifierCircuitGateBound_eval {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (n : Nat) :
    (verifierCircuitGateBound W).eval n = verifierCircuitGateBoundNat W n := by
  simp [verifierCircuitGateBound, verifierCircuitGateBoundNat,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_natCast]

/-- The generated verifier circuit has polynomially many gates in the public
instance length. -/
theorem verifierCircuit_gate_count_le {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (verifierCircuit W x).gates.length ≤
      (verifierCircuitGateBound W).eval x.length := by
  rw [verifierCircuit_gate_count_eq, verifierCircuitGateBound_eval]
  let H := (verifierHeight W).eval x.length
  let T := (verifierHorizon W).eval x.length
  let B := W.certificateBound.eval x.length
  let width := cfgBitCoefficient W.machine.tm * (H + 1)
  let validity := validCfgGateCoefficient W.machine.tm * (H + 1)
  let transition := transitionHeightCoefficient W.machine.tm * (H + 1)
  have hwidth : cfgBitCount W.machine.tm H ≤ width :=
    cfgBitCount_le W.machine.tm H
  have hrows : tableauInputCount W.machine.tm H T ≤ (T + 1) * width := by
    unfold tableauInputCount tableauRowCount
    exact Nat.mul_le_mul_left _ hwidth
  have hvalidity : (T + 1) * validCfgGateCost W.machine.tm H ≤
      (T + 1) * validity :=
    Nat.mul_le_mul_left _ (validCfgGateCost_le W.machine.tm H)
  have htransition : T * transitionCircuitGateCost W.machine.tm H ≤
      T * transition :=
    Nat.mul_le_mul_left _
      (transitionCircuitGateCost_affine_le W.machine.tm H)
  have hinitial : 6 * cfgBitCount W.machine.tm H + 1 ≤ 6 * width + 1 := by
    omega
  have hshape := verifierInputShapeGateCost_le W H x
  have haccept : acceptingOutputCircuitGateCost W.machine.tm H
      (List.map W.machine.outputAlphabet.invFun (boolEncoding true)) ≤
      6 * width + 1 :=
    (acceptingOutputCircuitGateCost_le W.machine.tm H _).trans hinitial
  unfold verifierCircuitGateCost verifierCircuitGateBoundNat
  dsimp only
  simp only [H, T, width, validity, transition] at hrows hvalidity htransition hinitial hshape haccept
  omega

end

end CLRS.Chapter34.Turing.CookLevin
