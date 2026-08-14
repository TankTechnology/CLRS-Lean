import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidity
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne.AffineRun

/-!
# Arithmetic one-hot groups for the Cook--Levin validity generator

This module turns each semantic one-hot group of an arithmetic tableau row
into the consecutive source interval expected by the contextual affine
exactly-one serializer.
-/

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open StateTransition

noncomputable section

/-- First source wire of one arithmetic row one-hot group. -/
noncomputable def arithmeticCfgOneHotGroupWireBase
    (tm : _root_.Turing.FinTM2) (H rowBase : Nat) :
    CfgOneHotGroup tm H → Nat
  | .inl _ => rowBase + 1
  | .inr (.inl _) => rowBase + 1 + (labelCount tm + 1)
  | .inr (.inr ⟨k, .inl _⟩) =>
      rowBase + 1 + (labelCount tm + 1) + stateCount tm +
        cfgStackBitOffset tm H k
  | .inr (.inr ⟨k, .inr i⟩) =>
      rowBase + 1 + (labelCount tm + 1) + stateCount tm +
        cfgStackBitOffset tm H k + (H + 1) +
          ((reachableAlphabet tm k).card + 1) * i.val

/-- Number of consecutive source wires in one arithmetic row one-hot group. -/
noncomputable def arithmeticCfgOneHotGroupWireCount
    (tm : _root_.Turing.FinTM2) (H : Nat) :
    CfgOneHotGroup tm H → Nat
  | .inl _ => labelCount tm + 1
  | .inr (.inl _) => stateCount tm
  | .inr (.inr ⟨_, .inl _⟩) => H + 1
  | .inr (.inr ⟨k, .inr _⟩) => (reachableAlphabet tm k).card + 1

private theorem list_ofFn_eq_affineWires
    {count base : Nat} (wires : Fin count → Nat)
    (hwires : ∀ i, wires i = base + i.val) :
    List.ofFn wires =
      affineSequentialExactlyOneWires base count := by
  apply List.ext_getElem
  · simp [affineSequentialExactlyOneWires]
  · intro i hleft hright
    simp [affineSequentialExactlyOneWires, hwires]

/-- Every semantic one-hot group in an arithmetic row is exactly a consecutive
affine source interval. -/
theorem arithmeticCfgOneHotGroupWires_eq_affine
    (tm : _root_.Turing.FinTM2) (H rowBase : Nat)
    (group : CfgOneHotGroup tm H) :
    cfgOneHotGroupWires (arithmeticCfgWires tm H rowBase) group =
      affineSequentialExactlyOneWires
        (arithmeticCfgOneHotGroupWireBase tm H rowBase group)
        (arithmeticCfgOneHotGroupWireCount tm H group) := by
  rcases group with (_ | _ | ⟨k, _ | i⟩)
  · simp only [cfgOneHotGroupWires, arithmeticCfgOneHotGroupWireBase,
      arithmeticCfgOneHotGroupWireCount]
    apply list_ofFn_eq_affineWires
    intro j
    rw [arithmeticCfgWires_label]
    omega
  · simp only [cfgOneHotGroupWires, arithmeticCfgOneHotGroupWireBase,
      arithmeticCfgOneHotGroupWireCount]
    apply list_ofFn_eq_affineWires
    intro j
    rw [arithmeticCfgWires_state]
    omega
  · simp only [cfgOneHotGroupWires, arithmeticCfgOneHotGroupWireBase,
      arithmeticCfgOneHotGroupWireCount]
    apply list_ofFn_eq_affineWires
    intro j
    rw [arithmeticCfgWires_stackHeight]
    omega
  · simp only [cfgOneHotGroupWires, arithmeticCfgOneHotGroupWireBase,
      arithmeticCfgOneHotGroupWireCount]
    apply list_ofFn_eq_affineWires
    intro j
    rw [arithmeticCfgWires_stackCell]
    omega

/-- The canonical semantic trace of any arithmetic row group is the public
affine exactly-one stream at its closed source base and count. -/
theorem arithmeticCfgOneHotGroupGateStream_eq_affine
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat)
    (group : CfgOneHotGroup tm H) :
    (exactlyOneGateTrace start
        (cfgOneHotGroupWires (arithmeticCfgWires tm H rowBase) group)).gates.flatMap
      encodeCircuitGate =
        affineSequentialExactlyOneGateStream start
          (arithmeticCfgOneHotGroupWireBase tm H rowBase group)
          (arithmeticCfgOneHotGroupWireCount tm H group) := by
  rw [arithmeticCfgOneHotGroupWires_eq_affine]
  rfl

/-- The concrete contextual serializer runs any arithmetic row one-hot group
to its canonical semantic stream. -/
def arithmeticCfgOneHotGroupRev_runFrom
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat)
    (group : CfgOneHotGroup tm H) (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineSequentialExactlyOneBodyCfg start
        (arithmeticCfgOneHotGroupWireBase tm H rowBase group)
        (arithmeticCfgOneHotGroupWireCount tm H group) output)
      (some (haltCfg sequentialExactlyOneRevProgram
        (((exactlyOneGateTrace start
          (cfgOneHotGroupWires (arithmeticCfgWires tm H rowBase) group)).gates.flatMap
            encodeCircuitGate).reverse ++ output)))
      (affineSequentialExactlyOneRevSteps start
        (arithmeticCfgOneHotGroupWireBase tm H rowBase group)
        (arithmeticCfgOneHotGroupWireCount tm H group)) := by
  rw [arithmeticCfgOneHotGroupGateStream_eq_affine]
  exact affineSequentialExactlyOneRev_runFrom _ _ _ output

/-- Every concrete arithmetic row group invocation inherits the uniform
quadratic contextual bound. -/
theorem arithmeticCfgOneHotGroupRev_steps_le
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat)
    (group : CfgOneHotGroup tm H) :
    affineSequentialExactlyOneRevSteps start
        (arithmeticCfgOneHotGroupWireBase tm H rowBase group)
        (arithmeticCfgOneHotGroupWireCount tm H group) ≤
      200 * (start +
        arithmeticCfgOneHotGroupWireBase tm H rowBase group +
        arithmeticCfgOneHotGroupWireCount tm H group + 1) ^ 2 :=
  affineSequentialExactlyOneRev_steps_le _ _ _

/-! ## Ordered affine family -/

/-- Serialize a finite family of affine exactly-one groups in its canonical
order.  The start of the last group is the initial gate index plus the exact
`3 * count + 4` costs of all preceding groups. -/
noncomputable def affineExactlyOneFamilyGateStream (start : Nat) :
    (n : Nat) → (bases counts : Fin n → Nat) → List CircuitSym
  | 0, _, _ => []
  | n + 1, bases, counts =>
      affineExactlyOneFamilyGateStream start n
          (fun i => bases i.castSucc) (fun i => counts i.castSucc) ++
        affineSequentialExactlyOneGateStream
          (start + ∑ i : Fin n, (3 * counts i.castSucc + 4))
          (bases (Fin.last n)) (counts (Fin.last n))

/-- A semantic exactly-one family over consecutive affine intervals is exactly
the ordered concatenation of the public affine streams. -/
theorem exactlyOneFamilyGateStream_eq_affine
    (start n : Nat) (groups : Fin n → List CircuitBuilder.Wire)
    (bases counts : Fin n → Nat)
    (hgroups : ∀ i, groups i =
      affineSequentialExactlyOneWires (bases i) (counts i)) :
    (exactlyOneFamilyGateTrace start n groups).gates.flatMap
        encodeCircuitGate =
      affineExactlyOneFamilyGateStream start n bases counts := by
  induction n with
  | zero => rfl
  | succ n ih =>
      let previousGroups : Fin n → List CircuitBuilder.Wire :=
        fun i => groups i.castSucc
      let previousBases : Fin n → Nat := fun i => bases i.castSucc
      let previousCounts : Fin n → Nat := fun i => counts i.castSucc
      have hprevious : ∀ i, previousGroups i =
          affineSequentialExactlyOneWires
            (previousBases i) (previousCounts i) := by
        intro i
        exact hgroups i.castSucc
      have hind := ih previousGroups previousBases previousCounts hprevious
      have hlength :
          (exactlyOneFamilyGateTrace start n previousGroups).gates.length =
            ∑ i : Fin n, (3 * counts i.castSucc + 4) := by
        rw [exactlyOneFamilyGateTrace_length]
        apply Finset.sum_congr rfl
        intro i _
        rw [hprevious i]
        simp [previousCounts, affineSequentialExactlyOneWires]
      simp only [exactlyOneFamilyGateTrace,
        affineExactlyOneFamilyGateStream, List.flatMap_append]
      rw [show
        (exactlyOneFamilyGateTrace start n
          (fun i => groups i.castSucc)).gates.flatMap encodeCircuitGate =
            affineExactlyOneFamilyGateStream start n
              (fun i => bases i.castSucc) (fun i => counts i.castSucc) by
          simpa [previousGroups, previousBases, previousCounts] using hind]
      rw [show
        (exactlyOneFamilyGateTrace start n
          (fun i => groups i.castSucc)).gates.length =
            ∑ i : Fin n, (3 * counts i.castSucc + 4) by
          simpa [previousGroups] using hlength]
      rw [hgroups (Fin.last n)]
      rfl

/-- Closed affine stream specification for every raw one-hot group of one
arithmetic configuration row. -/
noncomputable def arithmeticRawOneHotAffineGateStream
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    List CircuitSym :=
  let equiv := cfgOneHotGroupEquivFin tm H
  affineExactlyOneFamilyGateStream start (cfgOneHotGroupCount tm H)
    (fun i => arithmeticCfgOneHotGroupWireBase tm H rowBase (equiv.symm i))
    (fun i => arithmeticCfgOneHotGroupWireCount tm H (equiv.symm i))

/-- The complete semantic raw one-hot trace of an arithmetic row is exactly
the explicitly ordered family of affine serializer streams. -/
theorem arithmeticRawOneHotGateStream_eq_affineFamily
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    (rawOneHotGateTrace start
        (arithmeticCfgWires tm H rowBase)).gates.flatMap encodeCircuitGate =
      arithmeticRawOneHotAffineGateStream tm H start rowBase := by
  unfold rawOneHotGateTrace arithmeticRawOneHotAffineGateStream
  apply exactlyOneFamilyGateStream_eq_affine
  intro i
  exact arithmeticCfgOneHotGroupWires_eq_affine tm H rowBase _

/-! ## Exact boundary after the raw one-hot family -/

/-- The raw one-hot gates are the first gates of the complete canonical row
validity trace. -/
theorem arithmeticRawOneHotGates_isPrefix
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    (rawOneHotGateTrace start
        (arithmeticCfgWires tm H rowBase)).gates <+:
      (canonicalValidityGateTrace start
        (arithmeticCfgWires tm H rowBase)).gates := by
  unfold canonicalValidityGateTrace
  simp

/-- Exact encoded suffix of canonical row validity after all raw one-hot
groups.  It contains halted/label agreement, stack canonicality, and the final
conjunction. -/
noncomputable def arithmeticValidityPostOneHotGateStream
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    List CircuitSym :=
  let wires := arithmeticCfgWires tm H rowBase
  let raw := rawOneHotGateTrace start wires
  ((canonicalValidityGateTrace start wires).gates.drop raw.gates.length).flatMap
    encodeCircuitGate

/-- Lossless decomposition of one arithmetic row's canonical validity stream
at the end of the completed raw one-hot phase. -/
theorem validityRowGateStreamAt_eq_rawOneHot_append_post
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    validityRowGateStreamAt tm H start rowBase =
      arithmeticRawOneHotAffineGateStream tm H start rowBase ++
        arithmeticValidityPostOneHotGateStream tm H start rowBase := by
  let wires := arithmeticCfgWires tm H rowBase
  let raw := rawOneHotGateTrace start wires
  let full := canonicalValidityGateTrace start wires
  have hprefix : raw.gates <+: full.gates := by
    simpa [wires, raw, full] using
      arithmeticRawOneHotGates_isPrefix tm H start rowBase
  rcases hprefix with ⟨tail, htail⟩
  have hraw := arithmeticRawOneHotGateStream_eq_affineFamily
    tm H start rowBase
  unfold validityRowGateStreamAt
  change full.gates.flatMap encodeCircuitGate = _
  rw [← hraw]
  unfold arithmeticValidityPostOneHotGateStream
  change full.gates.flatMap encodeCircuitGate =
    raw.gates.flatMap encodeCircuitGate ++
      (full.gates.drop raw.gates.length).flatMap encodeCircuitGate
  rw [← htail]
  simp

/-- The completed affine raw one-hot stream is an encoded prefix of the full
canonical validity stream for one arithmetic row. -/
theorem arithmeticRawOneHotAffineGateStream_isPrefix
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    arithmeticRawOneHotAffineGateStream tm H start rowBase <+:
      validityRowGateStreamAt tm H start rowBase := by
  rw [validityRowGateStreamAt_eq_rawOneHot_append_post]
  exact List.prefix_append _ _

end

end CLRS.Chapter34.Turing.CookLevin
