import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowSeeds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneRowFamilySource

/-!
# Ordered one-hot operands for Cook--Levin validity rows

The concrete exactly-one controller consumes one frame per semantic one-hot
group.  This module gives those frames a positional specification: the frame
at group `i` uses the group's consecutive tableau interval, while its gate
start is the sum of the exact costs of all preceding groups.  It then lifts
that specification from one validity-row seed to the complete row-major
family.

This is the semantic contract for the following fixed source controller.  In
particular, it exposes the precise runtime loop invariant without replacing
the required concrete TM2 by an oracle computation.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Positional form of an affine exactly-one family -/

/-- The exact cost of all affine exactly-one groups preceding `index`. -/
def affineExactlyOnePrefixCost {n : Nat} (counts : Fin n → Nat)
    (index : Fin n) : Nat :=
  ∑ previous : Fin index.val,
    (3 * counts ⟨previous.val,
      Nat.lt_trans previous.isLt index.isLt⟩ + 4)

/-- Closed frame at one position of an ordered affine exactly-one family. -/
def affineExactlyOneRuntimeFrameAt (start : Nat) {n : Nat}
    (bases counts : Fin n → Nat) (index : Fin n) :
    AffineExactlyOneFrame :=
  { start := start + affineExactlyOnePrefixCost counts index
    rowBase := bases index
    count := counts index }

/-- The established snoc-recursive runtime family is exactly its positional
`List.ofFn` specification. -/
theorem affineExactlyOneRuntimeFrames_eq_ofFn
    (start n : Nat) (bases counts : Fin n → Nat) :
    affineExactlyOneRuntimeFrames start n bases counts =
      List.ofFn fun index : Fin n =>
        affineExactlyOneRuntimeFrameAt start bases counts index := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [affineExactlyOneRuntimeFrames]
      rw [ih, List.ofFn_succ']
      simp only [List.concat_eq_append]
      congr 1

/-! ## Arithmetic Cook--Levin group frames -/

/-- Exact runtime frame associated with one semantic row one-hot group. -/
noncomputable def arithmeticOneHotGroupFrame
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat)
    (group : CfgOneHotGroup tm H) : AffineExactlyOneFrame :=
  let equiv := cfgOneHotGroupEquivFin tm H
  affineExactlyOneRuntimeFrameAt start
    (fun index => arithmeticCfgOneHotGroupWireBase tm H rowBase
      (equiv.symm index))
    (fun index => arithmeticCfgOneHotGroupWireCount tm H
      (equiv.symm index))
    (equiv group)

/-- The raw row frames are exactly the semantic groups in their explicit
`cfgOneHotGroupEquivFin` order. -/
theorem arithmeticRawOneHotFrames_eq_groupFrames
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    arithmeticRawOneHotFrames tm H start rowBase =
      List.ofFn fun index : Fin (cfgOneHotGroupCount tm H) =>
        arithmeticOneHotGroupFrame tm H start rowBase
          ((cfgOneHotGroupEquivFin tm H).symm index) := by
  unfold arithmeticRawOneHotFrames arithmeticOneHotGroupFrame
  rw [affineExactlyOneRuntimeFrames_eq_ofFn]
  apply List.ofFn_inj.mpr
  funext index
  simp

/-! ## Row-seed and row-family contracts -/

/-- One seed expanded only to its ordered one-hot runtime frames. -/
noncomputable def validityRowSeedOneHotFrames
    (tm : _root_.Turing.FinTM2) (seed : ValidityRowSeed) :
    List AffineExactlyOneFrame :=
  arithmeticRawOneHotFrames tm seed.height seed.start seed.rowBase

/-- The one-hot seed expansion is exactly the one-hot field of the complete
canonical validity-row expansion. -/
theorem validityRowSeedOneHotFrames_eq_expand
    (tm : _root_.Turing.FinTM2) (seed : ValidityRowSeed) :
    validityRowSeedOneHotFrames tm seed =
      (expandValidityRowSeed tm seed).oneHotFrames := by
  rfl

/-- Row-major one-hot frames generated from every compiled validity seed. -/
noncomputable def validityRowSeedOneHotFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineExactlyOneFrame :=
  (verifierValidityRowSeeds W input).flatMap
    (validityRowSeedOneHotFrames W.machine.tm)

/-- Seed expansion gives byte-for-byte the canonical row-major one-hot frame
family consumed by the validity-row controller. -/
theorem validityRowSeedOneHotFamily_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    validityRowSeedOneHotFamily W input =
      (verifierValidityRowFramesByLength W input.length).flatMap
        (fun frame => frame.oneHotFrames) := by
  unfold validityRowSeedOneHotFamily
  rw [← verifierValidityRowSeeds_expand_eq_frames]
  rw [List.flatMap_map]
  congr 1

end CLRS.Chapter34.Turing.CookLevin
