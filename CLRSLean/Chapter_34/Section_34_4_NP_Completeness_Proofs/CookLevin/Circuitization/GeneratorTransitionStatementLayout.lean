import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementPop

/-!
# Builder-free recursive statement layout

This module removes the remaining proof-carrying builder fields from the
wire payload threaded through recursive TM2 statements.  The first layer
collects reusable arithmetic forms of static control encodings, zero-gate
push, and finite one-hot lookup outputs.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-! ## Builder-free zero-gate wiring -/

/-- Static optional-label wires using only the two numeric pool coordinates. -/
def arithmeticLabelWires (tm : _root_.Turing.FinTM2)
    (falseWire trueWire : Nat) (label : Option tm.Λ) : LabelWires tm :=
  fun code => if code = encodeLabel tm label then trueWire else falseWire

/-- Static halted wire using only the two numeric pool coordinates. -/
def arithmeticLabelHaltedWire (falseWire trueWire : Nat) (halted : Bool) : Nat :=
  if halted then trueWire else falseWire

/-- Pool-backed optional-label encoding is definitionally the arithmetic
encoding once the proof-carrying pool is projected to its two wires. -/
theorem encodeLabelWires_eq_arithmetic
    {tm : _root_.Turing.FinTM2} {base : CircuitBuilder}
    (pool : base.BoolWirePool) (label : Option tm.Λ) :
    encodeLabelWires pool label =
      arithmeticLabelWires tm pool.falseWire pool.trueWire label := by
  rfl

/-- Pool-backed halted encoding has the same builder-free form. -/
theorem encodeLabelHaltedWire_eq_arithmetic
    {tm : _root_.Turing.FinTM2} {base : CircuitBuilder}
    (pool : base.BoolWirePool) (label : Option tm.Λ) :
    encodeLabelHaltedWire pool label =
      arithmeticLabelHaltedWire pool.falseWire pool.trueWire
        (labelHalted label) := by
  rfl

/-- Zero-gate push with the pool proof erased. -/
def arithmeticPushStackWires (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseWire : Nat) (symbol : SymbolWires tm k) :
    (height : Nat) → StackWires tm height k → StackWires tm height k
  | 0, _ =>
      { height := fun _ => falseWire
        cell := fun i => Fin.elim0 i }
  | _ + 1, stack =>
      { height := Fin.cases falseWire (fun i => stack.height i.castSucc)
        cell := Fin.cases
          (fun code => if h : code.val < (reachableAlphabet tm k).card then
            symbol ⟨code.val, h⟩ else falseWire)
          (fun i => stack.cell i.castSucc) }

/-- Complete-row form of the builder-free push wiring. -/
def arithmeticPushCfgWires (tm : _root_.Turing.FinTM2) (height : Nat)
    (k : tm.K) (falseWire : Nat) (symbol : SymbolWires tm k)
    (source : CfgWires tm height) : CfgWires tm height :=
  source.replaceStack k
    (arithmeticPushStackWires tm k falseWire symbol height (source.stack k))

/-- The semantic zero-gate stack push is exactly its builder-free form. -/
theorem pushStackWires_eq_arithmetic
    {tm : _root_.Turing.FinTM2} {height : Nat} {k : tm.K}
    {base : CircuitBuilder} (pool : base.BoolWirePool)
    (symbol : SymbolWires tm k) (source : StackWires tm height k) :
    pushStackWires pool symbol height source =
      arithmeticPushStackWires tm k pool.falseWire symbol height source := by
  cases height <;> rfl

/-- The complete-row push is likewise independent of its builder proof. -/
theorem pushCfgWires_eq_arithmetic
    {tm : _root_.Turing.FinTM2} {height : Nat} {k : tm.K}
    {base : CircuitBuilder} (pool : base.BoolWirePool)
    (symbol : SymbolWires tm k) (source : CfgWires tm height) :
    pushCfgWires pool symbol source =
      arithmeticPushCfgWires tm height k pool.falseWire symbol source := by
  unfold pushCfgWires arithmeticPushCfgWires
  rw [pushStackWires_eq_arithmetic]

/-! ## Builder-free finite-lookup outputs -/

/-- Unary finite lookup returns the complete output family of its pure trace. -/
theorem oneHotMap_wires_eq_trace
    (base : CircuitBuilder) {n m : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m)
    (hsource : ∀ i, base.WireValid (source i)) :
    (oneHotMap base source f hsource).wires =
      (oneHotMapGateTrace base.gates.length source f).wires := by
  funext target
  exact oneHotMap_wire_eq_trace base source f hsource target

/-- Binary finite lookup returns the complete output family of its pure trace. -/
theorem oneHotPairMap_wires_eq_trace
    (base : CircuitBuilder) {n p m : Nat}
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (f : Fin n → Fin p → Fin m)
    (hleft : ∀ i, base.WireValid (left i))
    (hright : ∀ j, base.WireValid (right j)) :
    (oneHotPairMap base left right f hleft hright).wires =
      (oneHotPairMapGateTrace base.gates.length left right f).wires := by
  funext target
  exact oneHotPairMap_wire_eq_trace base left right f hleft hright target

end CLRS.Chapter34.Turing.CookLevin
