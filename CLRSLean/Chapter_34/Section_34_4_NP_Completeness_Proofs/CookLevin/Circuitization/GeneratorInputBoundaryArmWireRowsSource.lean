import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmRowSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmSingletonRowsSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmSeparatorPrefixSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmCellRowsSource

/-!
# Complete arithmetic wire rows of verifier-input arms

The height singleton, growing separator prefix, blank separator singleton,
and content-dependent cell block are combined pointwise.  The resulting
machine emits the exact conjunction operands of every candidate-length arm.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Height singleton channel in the uniform arm-source interface. -/
noncomputable def verifierInputArmHeightRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    VerifierInputArmRowSource W :=
  { row := fun input arm =>
      encodeUnaryFrame [verifierInputArmHeightWire W input arm]
    family := verifierInputArmHeightWireFamily W
    rows_eq := fun input => by
      change (List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        verifierInputArmHeightWire W input arm).map
          (fun value => encodeUnaryFrame [value]) = _
      rw [List.map_ofFn]
      apply List.ofFn_inj.mpr
      funext arm
      rfl
    computableInPolyTime :=
      verifierInputArmHeightWireFamily_computableInPolyTime W }

/-- Growing separator-NOT prefix channel in the common interface. -/
noncomputable def verifierInputArmSeparatorPrefixRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    VerifierInputArmRowSource W :=
  { row := fun input arm =>
      encodeUnaryFrame (List.ofFn fun prefixIndex : Fin arm.val =>
        (verifierInitialBoundaryEndPolynomial W).eval input.length +
          prefixIndex.val)
    family := verifierInputArmSeparatorPrefixFamily W
    rows_eq := fun _ => rfl
    computableInPolyTime :=
      verifierInputArmSeparatorPrefixFamily_computableInPolyTime W }

/-- Blank-separator singleton channel in the common interface. -/
noncomputable def verifierInputArmSeparatorRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    VerifierInputArmRowSource W :=
  { row := fun input arm =>
      encodeUnaryFrame [verifierInputArmSeparatorWire W input arm]
    family := verifierInputArmSeparatorWireFamily W
    rows_eq := fun input => by
      change (List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        verifierInputArmSeparatorWire W input arm).map
          (fun value => encodeUnaryFrame [value]) = _
      rw [List.map_ofFn]
      apply List.ofFn_inj.mpr
      funext arm
      rfl
    computableInPolyTime :=
      verifierInputArmSeparatorWireFamily_computableInPolyTime W }

/-- Content-dependent public-input cell block in the common interface. -/
noncomputable def verifierInputArmCellRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    VerifierInputArmRowSource W :=
  { row := fun input arm =>
      encodeUnaryFrame (List.ofFn fun index : Fin input.length =>
        verifierInputArmCellWire W input arm index)
    family := verifierInputArmCellWireRowsFamily W
    rows_eq := verifierInputArmCellWireRowsFamily_rows W
    computableInPolyTime :=
      verifierInputArmCellWireRowsFamily_computableInPolyTime W }

/-- All four operand channels, joined row by row by concrete machines. -/
noncomputable def verifierInputArmArithmeticWireRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    VerifierInputArmRowSource W :=
  (((verifierInputArmHeightRowSource W).append
      (verifierInputArmSeparatorPrefixRowSource W)).append
    (verifierInputArmSeparatorRowSource W)).append
      (verifierInputArmCellRowSource W)

/-- Public typed family of complete arithmetic operand rows. -/
noncomputable def verifierInputArmArithmeticWireFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  (verifierInputArmArithmeticWireRowSource W).family input

private theorem encodeUnaryFrame_append_values
    (left right : List Nat) :
    encodeUnaryFrame (left ++ right) =
      encodeUnaryFrame left ++ encodeUnaryFrame right := by
  simp [encodeUnaryFrame, List.flatMap_append]

/-- One composite source row is the four channel encodings in execution
order. -/
theorem verifierInputArmArithmeticWireRowSource_row
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (arm : Fin (W.certificateBound.eval input.length + 1)) :
    (verifierInputArmArithmeticWireRowSource W).row input arm =
      encodeUnaryFrame [verifierInputArmHeightWire W input arm] ++
      encodeUnaryFrame (List.ofFn fun prefixIndex : Fin arm.val =>
        (verifierInitialBoundaryEndPolynomial W).eval input.length +
          prefixIndex.val) ++
      encodeUnaryFrame [verifierInputArmSeparatorWire W input arm] ++
      encodeUnaryFrame (List.ofFn fun index : Fin input.length =>
        verifierInputArmCellWire W input arm index) := by
  change (((((verifierInputArmHeightRowSource W).append
      (verifierInputArmSeparatorPrefixRowSource W)).append
    (verifierInputArmSeparatorRowSource W)).append
      (verifierInputArmCellRowSource W)).row input arm) = _
  rw [VerifierInputArmRowSource.append_row,
    VerifierInputArmRowSource.append_row,
    VerifierInputArmRowSource.append_row]
  rfl

/-- The joined marked rows are exactly the semantic conjunction operands of
every verifier-input arm. -/
theorem verifierInputArmArithmeticWireFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputArmArithmeticWireFamily W input).rows =
      List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        encodeUnaryFrame (verifierInputArmArithmeticWires W input arm) := by
  unfold verifierInputArmArithmeticWireFamily
  rw [(verifierInputArmArithmeticWireRowSource W).rows_eq]
  apply List.ofFn_inj.mpr
  funext arm
  rw [verifierInputArmArithmeticWireRowSource_row W input arm,
    verifierInputArmArithmeticWires_eq_channels W input arm]
  simp only [encodeUnaryFrame_append_values]
  simp [List.append_assoc]
  apply congrArg encodeUnaryFrame
  apply List.ofFn_inj.mpr
  funext index
  simpa [verifierInputStackSymbolWidth] using
    verifierInputArmCellWire_eq_layout W input arm index

/-- One fixed polynomial-time TM2 emits every complete arithmetic arm row
directly from the raw verifier word. -/
noncomputable def verifierInputArmArithmeticWireFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierInputArmArithmeticWireFamily W) :=
  (verifierInputArmArithmeticWireRowSource W).computableInPolyTime

end CLRS.Chapter34.Turing.CookLevin
