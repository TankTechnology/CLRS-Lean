import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits.Core

/-!
# Exact structural traces for recursive statement compilation

This module removes `List.drop` from the local statement-compiler acceptance
surface.  Each statement constructor exposes the literal ordered gates emitted
by its finite lookup, optional stack pop, recursive continuation, and final
whole-row mux.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

private noncomputable instance symbolDecidableEq
    (tm : _root_.Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) :=
  Classical.decEq _

/-- Literal zero/one-gate trace of complete-row pop. -/
def popCfgGateTrace {tm : _root_.Turing.FinTM2} {H : Nat}
    (source : CfgWires tm H) (k : tm.K) : List CircuitGate :=
  match H with
  | 0 => []
  | _ + 1 => [CircuitGate.or ((source.stack k).height 0)
      ((source.stack k).height 1)]

/-- Complete-row pop appends exactly its explicit height-merge trace. -/
theorem popCfgWires_gates_eq {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H) (hvalid : source.ValidIn base) (k : tm.K) :
    (popCfgWires base pool source hvalid k).builder.gates =
      base.gates ++ popCfgGateTrace source k := by
  cases H with
  | zero => simp [popCfgWires, popStackWires, popCfgGateTrace]
  | succ H =>
      change
        (base.or ((source.stack k).height 0) ((source.stack k).height 1)
          ((hvalid.stack k).height 0) ((hvalid.stack k).height 1)).1.gates =
        base.gates ++
          [CircuitGate.or ((source.stack k).height 0)
            ((source.stack k).height 1)]
      exact CircuitBuilder.or_gates base ((source.stack k).height 0)
        ((source.stack k).height 1) ((hvalid.stack k).height 0)
        ((hvalid.stack k).height 1)

/-- Exact ordered gate trace of one recursive bundled statement.  Runtime
configuration data occurs only in the supplied source wires; the statement
itself is fixed finite program data. -/
def compileStmtGateTrace (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H) (hvalid : source.ValidIn base)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    List CircuitGate :=
  match q with
  | halt => []
  | goto jump =>
      (oneHotMapGateTrace base.gates.length source.state
        (stmtLabelTable tm jump)).gates
  | load update continuation =>
      let hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      let mapped := oneHotMap base source.state (stmtStateTable tm update)
        hvalid.state
      let wires := source.replaceState mapped.wires
      let hwires : CfgWires.ValidIn wires mapped.builder :=
        (hvalid.mono mapped.extension).replaceState mapped.valid
      (oneHotMapGateTrace base.gates.length source.state
          (stmtStateTable tm update)).gates ++
        compileStmtGateTrace tm H mapped.builder
          (pool.mono mapped.extension) wires hwires continuation hcontinuation
  | push k emit continuation =>
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
      let mapped := oneHotMap base source.state
        (fun code => encodeSupportedSymbol (symbolAt code)) hvalid.state
      let nextPool := pool.mono mapped.extension
      let wires := pushCfgWires nextPool mapped.wires source
      let hwires : CfgWires.ValidIn wires mapped.builder :=
        pushCfgWires_valid nextPool mapped.wires source mapped.valid
          (hvalid.mono mapped.extension)
      (oneHotMapGateTrace base.gates.length source.state
          (fun code => encodeSupportedSymbol (symbolAt code))).gates ++
        compileStmtGateTrace tm H mapped.builder nextPool wires hwires
          continuation hcontinuation
  | peek k update continuation =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      let head := peekCfgWires k pool source
      let mapped := oneHotPairMap base source.state head
        (stmtHeadStateTable tm k update) hvalid.state
        (peekCfgWires_valid k pool source hvalid)
      let wires := source.replaceState mapped.wires
      let hwires : CfgWires.ValidIn wires mapped.builder :=
        (hvalid.mono mapped.extension).replaceState mapped.valid
      (oneHotPairMapGateTrace base.gates.length source.state head
          (stmtHeadStateTable tm k update)).gates ++
        compileStmtGateTrace tm H mapped.builder
          (pool.mono mapped.extension) wires hwires continuation hcontinuation
  | pop k update continuation =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      let popped := popCfgWires base pool source hvalid k
      let mapped := oneHotPairMap popped.builder popped.wires.state popped.head
        (stmtHeadStateTable tm k update) popped.valid.state popped.headValid
      let wires := popped.wires.replaceState mapped.wires
      let hwires : CfgWires.ValidIn wires mapped.builder :=
        (popped.valid.mono mapped.extension).replaceState mapped.valid
      let hext := popped.extension.trans mapped.extension
      popCfgGateTrace source k ++
        (oneHotPairMapGateTrace popped.builder.gates.length popped.wires.state
          popped.head (stmtHeadStateTable tm k update)).gates ++
        compileStmtGateTrace tm H mapped.builder (pool.mono hext) wires hwires
          continuation hcontinuation
  | branch test whenTrue whenFalse =>
      let htrueSupport :
          ∀ k, stmtPushSet tm whenTrue k ⊆ reachableAlphabet tm k := by
        intro k symbol hsymbol
        apply hsupport k
        simp only [stmtPushSet]
        exact Finset.mem_union_left _ hsymbol
      let hfalseSupport :
          ∀ k, stmtPushSet tm whenFalse k ⊆ reachableAlphabet tm k := by
        intro k symbol hsymbol
        apply hsupport k
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let predicate := oneHotPredicate base source.state
        (stmtPredicateTable tm test) hvalid.state
      let trueTrace := compileStmtGateTrace tm H predicate.builder
        (pool.mono predicate.extension) source
        (hvalid.mono predicate.extension) whenTrue htrueSupport
      let trueResult := compileStmt tm H predicate.builder
        (pool.mono predicate.extension) source
        (hvalid.mono predicate.extension) whenTrue htrueSupport
      let hbaseFalse := predicate.extension.trans trueResult.extension
      let falseTrace := compileStmtGateTrace tm H trueResult.builder
        (pool.mono hbaseFalse) source (hvalid.mono hbaseFalse)
        whenFalse hfalseSupport
      let falseResult := compileStmt tm H trueResult.builder
        (pool.mono hbaseFalse) source (hvalid.mono hbaseFalse)
        whenFalse hfalseSupport
      let hselectorExt := trueResult.extension.trans falseResult.extension
      (CircuitBuilder.disjunctionGateTrace base.gates.length
          (oneHotPredicateWires source.state (stmtPredicateTable tm test))).gates ++
        trueTrace ++ falseTrace ++
        CircuitBuilder.muxFinGateTrace falseResult.builder.gates.length
          predicate.wire
          (fun i => trueResult.wires ((cfgSlotEquivFin tm H).symm i))
          (fun i => falseResult.wires ((cfgSlotEquivFin tm H).symm i))

/-- Recursive statement compilation appends exactly its structural trace. -/
theorem compileStmt_gates_eq (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H) (hvalid : source.ValidIn base)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    (compileStmt tm H base pool source hvalid q hsupport).builder.gates =
      base.gates ++
        compileStmtGateTrace tm H base pool source hvalid q hsupport := by
  induction q generalizing base source with
  | halt => simp [compileStmt, compileStmtGateTrace]
  | goto jump =>
      simpa [compileStmt, compileStmtGateTrace] using
        oneHotMap_gates_eq base source.state (stmtLabelTable tm jump)
          hvalid.state
  | load update continuation ih =>
      classical
      simp only [compileStmt, compileStmtGateTrace]
      rw [ih]
      rw [oneHotMap_gates_eq]
      simp only [List.append_assoc]
  | push k emit continuation ih =>
      classical
      simp only [compileStmt, compileStmtGateTrace]
      rw [ih]
      rw [oneHotMap_gates_eq]
      simp only [List.append_assoc]
  | peek k update continuation ih =>
      classical
      simp only [compileStmt, compileStmtGateTrace]
      rw [ih]
      rw [oneHotPairMap_gates_eq]
      simp only [List.append_assoc]
  | pop k update continuation ih =>
      classical
      simp only [compileStmt, compileStmtGateTrace]
      rw [ih]
      rw [oneHotPairMap_gates_eq]
      rw [popCfgWires_gates_eq]
      simp only [List.append_assoc]
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      classical
      simp only [compileStmt, compileStmtGateTrace]
      rw [cfgMux_gates_eq]
      rw [ihFalse]
      rw [ihTrue]
      rw [oneHotPredicate_gates_eq]
      simp only [List.append_assoc]

/-- The structural trace has exactly the recursive compiler cost. -/
theorem compileStmtGateTrace_length (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H) (hvalid : source.ValidIn base)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    (compileStmtGateTrace tm H base pool source hvalid q hsupport).length =
      compileStmtGateCost tm H q := by
  have hgates := congrArg List.length
    (compileStmt_gates_eq tm H base pool source hvalid q hsupport)
  rw [compileStmt_gate_delta, List.length_append] at hgates
  omega

end

end CLRS.Chapter34.Turing.CookLevin
