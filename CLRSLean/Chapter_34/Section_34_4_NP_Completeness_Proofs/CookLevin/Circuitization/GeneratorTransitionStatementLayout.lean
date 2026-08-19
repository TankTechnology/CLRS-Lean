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

/-! ## Pure recursive output layout -/

/-- Complete output-row wiring of one fixed bundled statement.  Unlike
`compileStmt`, this recursion contains no builders, extension witnesses, or
wire-validity proofs.  Every fresh output is read from a pure gate trace or
from an exact arithmetic coordinate formula. -/
def transitionStmtOutputWires (tm : _root_.Turing.FinTM2) (height : Nat)
    (falseWire trueWire : Nat) :
    (start : Nat) → CfgWires tm height →
      (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) →
      (∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) →
      CfgWires tm height
  | _, source, halt, _ =>
      source.replaceStatus
        (arithmeticLabelHaltedWire falseWire trueWire
          (labelHalted (none : Option tm.Λ)))
        (arithmeticLabelWires tm falseWire trueWire (none : Option tm.Λ))
  | start, source, goto jump, _ =>
      let mapped := (oneHotMapGateTrace start source.state
        (stmtLabelTable tm jump)).wires
      source.replaceStatus
        (arithmeticLabelHaltedWire falseWire trueWire
          (labelHalted (some (jump default))))
        mapped
  | start, source, load update continuation, hsupport =>
      let hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      let mapped := (oneHotMapGateTrace start source.state
        (stmtStateTable tm update)).wires
      transitionStmtOutputWires tm height falseWire trueWire
        (start + stateCount tm + stateCount tm)
        (source.replaceState mapped) continuation hcontinuation
  | start, source, push k emit continuation, hsupport =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm k := fun code =>
        ⟨emit ((stateEquivFin tm).symm code), by
          apply hsupport k
          simp [stmtPushSet]⟩
      let mapped := (oneHotMapGateTrace start source.state
        (fun code => encodeSupportedSymbol (symbolAt code))).wires
      let wires := arithmeticPushCfgWires tm height k falseWire mapped source
      transitionStmtOutputWires tm height falseWire trueWire
        (start + stateCount tm + (reachableAlphabet tm k).card)
        wires continuation hcontinuation
  | start, source, peek k update continuation, hsupport =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      let head := arithmeticPeekCfgWires tm height falseWire trueWire source k
      let mapped := (oneHotPairMapGateTrace start source.state head
        (stmtHeadStateTable tm k update)).wires
      transitionStmtOutputWires tm height falseWire trueWire
        (start + 2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
          stateCount tm)
        (source.replaceState mapped) continuation hcontinuation
  | start, source, pop k update continuation, hsupport =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      let popped := arithmeticPopCfgWires tm height k falseWire trueWire
        start source
      let head := arithmeticPopHeadWires tm k falseWire trueWire height
        (source.stack k)
      let pairStart := start + popStackWireGateCost height
      let mapped := (oneHotPairMapGateTrace pairStart popped.state head
        (stmtHeadStateTable tm k update)).wires
      transitionStmtOutputWires tm height falseWire trueWire
        (pairStart +
          (2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
            stateCount tm))
        (popped.replaceState mapped) continuation hcontinuation
  | start, _source, branch test whenTrue whenFalse, _ =>
      let predicateCost :=
        (oneHotTruePreimage (stmtPredicateTable tm test)).card + 1
      let muxStart := start + predicateCost +
        compileStmtGateCost tm height whenTrue +
        compileStmtGateCost tm height whenFalse
      arithmeticMuxCfgWires tm height muxStart

/-- Proof-carrying statement compilation returns exactly the pure arithmetic
output layout.  In particular, the output coordinates are independent of all
builder contents and all validity/extension witnesses once the starting gate
index and Boolean-pool coordinates are fixed. -/
theorem compileStmt_wires_eq_transitionStmtOutputWires
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm height) (hvalid : source.ValidIn base)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    (compileStmt tm height base pool source hvalid q hsupport).wires =
      transitionStmtOutputWires tm height pool.falseWire pool.trueWire
        base.gates.length source q hsupport := by
  induction q generalizing base source with
  | halt =>
      simp only [compileStmt, transitionStmtOutputWires]
      rw [encodeLabelHaltedWire_eq_arithmetic,
        encodeLabelWires_eq_arithmetic]
  | goto jump =>
      simp only [compileStmt, transitionStmtOutputWires]
      rw [oneHotMap_wires_eq_trace,
        encodeLabelHaltedWire_eq_arithmetic]
      simp only [CircuitBuilder.BoolWirePool.mono_falseWire,
        CircuitBuilder.BoolWirePool.mono_trueWire]
  | load update continuation ih =>
      simp only [compileStmt, transitionStmtOutputWires]
      rw [ih]
      rw [oneHotMap_wires_eq_trace]
      rw [oneHotMap_gate_delta]
      simp only [CircuitBuilder.BoolWirePool.mono_falseWire,
        CircuitBuilder.BoolWirePool.mono_trueWire]
      simp only [Nat.add_assoc]
  | push k emit continuation ih =>
      simp only [compileStmt, transitionStmtOutputWires]
      rw [ih]
      rw [pushCfgWires_eq_arithmetic, oneHotMap_wires_eq_trace]
      rw [oneHotMap_gate_delta]
      simp only [CircuitBuilder.BoolWirePool.mono_falseWire,
        CircuitBuilder.BoolWirePool.mono_trueWire]
      simp only [Nat.add_assoc]
  | peek k update continuation ih =>
      simp only [compileStmt, transitionStmtOutputWires]
      rw [ih]
      rw [arithmeticPeekCfgWires_eq_peekCfgWires]
      rw [oneHotPairMap_wires_eq_trace]
      rw [oneHotPairMap_gate_delta]
      simp only [CircuitBuilder.BoolWirePool.mono_falseWire,
        CircuitBuilder.BoolWirePool.mono_trueWire]
      simp only [Nat.add_assoc]
  | pop k update continuation ih =>
      simp only [compileStmt, transitionStmtOutputWires]
      rw [ih]
      rw [oneHotPairMap_wires_eq_trace]
      rw [oneHotPairMap_gate_delta,
        (popCfgWires base pool source hvalid k).gate_delta]
      simp only [CircuitBuilder.BoolWirePool.mono_falseWire,
        CircuitBuilder.BoolWirePool.mono_trueWire]
      rw [popCfgWires_wires_eq_arithmetic,
        popCfgWires_head_eq_arithmetic]
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp only [compileStmt, transitionStmtOutputWires]
      rw [cfgMux_wires_eq_arithmetic]
      rw [compileStmt_gate_delta, compileStmt_gate_delta,
        oneHotPredicate_gate_delta]

end CLRS.Chapter34.Turing.CookLevin
