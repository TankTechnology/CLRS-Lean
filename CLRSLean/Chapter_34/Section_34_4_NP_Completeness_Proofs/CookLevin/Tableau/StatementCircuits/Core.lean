import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.PrimitiveRowSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.FiniteLookup
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BundleCombinators

/-!
# CLRS Section 34.4 - Recursive TM2 statement compiler core

This module compiles one bundled {lit}`TM2.Stmt` into a complete symbolic
configuration row.  Every arbitrary Lean function occurring in a statement is
used only as fixed finite truth-table data for {lit}`oneHotMap`,
{lit}`oneHotPairMap`, or {lit}`oneHotPredicate`; configurations and stacks are
never enumerated.

Main results:

- Definition {lit}`compileStmtGateCost`: exact structural gate recurrence.
- Structure {lit}`CompileStmtResult`: builder, complete row, extension, validity,
  and exact gate delta.
- Definition {lit}`compileStmt`: all seven statement constructors over finite
  truth-table primitives.

Current gaps:

- Downstream {lit}`TransitionCircuits` now supplies finite-label dispatch and
  the complete local step check.  Non-aliasing row allocation and verified
  whole-tableau assembly remain milestone 8F.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-! ## Fixed finite truth tables -/

/-- Re-encode a fixed unary state transformation as a finite truth table. -/
def stmtStateTable (tm : _root_.Turing.FinTM2) (update : tm.σ → tm.σ) :
    Fin (stateCount tm) → Fin (stateCount tm) :=
  fun code => stateEquivFin tm (update ((stateEquivFin tm).symm code))

/-- Re-encode a fixed state-to-label transformation as a finite truth table. -/
def stmtLabelTable (tm : _root_.Turing.FinTM2) (jump : tm.σ → tm.Λ) :
    Fin (stateCount tm) → Fin (labelCount tm + 1) :=
  fun code => encodeLabel tm (some (jump ((stateEquivFin tm).symm code)))

/-- Re-encode a fixed state/head transformation as a finite binary truth table. -/
def stmtHeadStateTable (tm : _root_.Turing.FinTM2) (k : tm.K)
    (update : tm.σ → Option (tm.Γ k) → tm.σ) :
    Fin (stateCount tm) → Fin ((reachableAlphabet tm k).card + 1) →
      Fin (stateCount tm) :=
  fun state head => stateEquivFin tm
    (update ((stateEquivFin tm).symm state)
      ((decodeHeadCode head).map Subtype.val))

/-- Re-index a fixed state predicate by canonical finite state codes. -/
def stmtPredicateTable (tm : _root_.Turing.FinTM2)
    (test : tm.σ → Bool) : Fin (stateCount tm) → Bool :=
  fun code => test ((stateEquivFin tm).symm code)

/-! ## Exact structural gate cost -/

/-- Exact number of gates emitted while compiling one bundled statement.

Push and control replacement are zero-gate rewiring operations.  Every other
summand is the exact delta of the corresponding public finite-lookup, pop, or
whole-row mux primitive. -/
def compileStmtGateCost (tm : _root_.Turing.FinTM2) (H : Nat) :
    _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ → Nat
  | push k _ continuation =>
      stateCount tm + (reachableAlphabet tm k).card +
        compileStmtGateCost tm H continuation
  | peek k _ continuation =>
      2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
        stateCount tm + compileStmtGateCost tm H continuation
  | pop k _ continuation =>
      popStackWireGateCost H +
        (2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
          stateCount tm) + compileStmtGateCost tm H continuation
  | load _ continuation =>
      stateCount tm + stateCount tm +
        compileStmtGateCost tm H continuation
  | branch test whenTrue whenFalse =>
      (oneHotTruePreimage (stmtPredicateTable tm test)).card + 1 +
        compileStmtGateCost tm H whenTrue +
        compileStmtGateCost tm H whenFalse +
        (3 * cfgBitCount tm H + 1)
  | goto _ => stateCount tm + (labelCount tm + 1)
  | halt => 0

/-! ## Proof-carrying compiler -/

/-- Minimal proof-carrying result of compiling a complete bundled statement. -/
structure CompileStmtResult (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (source : CfgWires tm H)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) where
  /-- Builder after compiling the statement. -/
  builder : CircuitBuilder
  /-- Complete symbolic output row. -/
  wires : CfgWires tm H
  /-- Compilation preserves the complete input builder prefix. -/
  extension : base.Extends builder
  /-- Every output row wire belongs to the result builder. -/
  valid : wires.ValidIn builder
  /-- Compilation emits exactly the structural gate cost. -/
  gate_delta : builder.gates.length =
    base.gates.length + compileStmtGateCost tm H q

/-- Compile one statement by structural recursion over finite control and
symbol alphabets.  {lit}`hsupport` is explicit because a pushed symbol must be
packaged as a {lit}`SupportedSymbol`; the constant pool is only transported
monotonically and is deliberately not exposed as a result field. -/
def compileStmt (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H) (hvalid : source.ValidIn base)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    CompileStmtResult tm H base source q :=
  match q with
  | halt =>
      { builder := base
        wires := source.replaceStatus
          (encodeLabelHaltedWire pool (none : Option tm.Λ))
          (encodeLabelWires pool (none : Option tm.Λ))
        extension := .refl base
        valid := hvalid.replaceStatus
          (encodeLabelHaltedWire_valid pool (none : Option tm.Λ))
          (encodeLabelWires_valid pool (none : Option tm.Λ))
        gate_delta := by simp [compileStmtGateCost] }
  | goto jump => by
      let mapped := oneHotMap base source.state (stmtLabelTable tm jump)
        hvalid.state
      let nextPool := pool.mono mapped.extension
      let halted := encodeLabelHaltedWire nextPool (some (jump default))
      let wires := source.replaceStatus halted mapped.wires
      refine
        { builder := mapped.builder
          wires := wires
          extension := mapped.extension
          valid := (hvalid.mono mapped.extension).replaceStatus
            (encodeLabelHaltedWire_valid nextPool (some (jump default)))
            mapped.valid
          gate_delta := ?_ }
      rw [mapped.gate_delta]
      simp [compileStmtGateCost]
  | load update continuation => by
      classical
      have hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      let mapped := oneHotMap base source.state (stmtStateTable tm update)
        hvalid.state
      let wires := source.replaceState mapped.wires
      have hwires : CfgWires.ValidIn wires mapped.builder :=
        (hvalid.mono mapped.extension).replaceState mapped.valid
      let compiled := compileStmt tm H mapped.builder
        (pool.mono mapped.extension) wires hwires continuation hcontinuation
      refine
        { builder := compiled.builder
          wires := compiled.wires
          extension := mapped.extension.trans compiled.extension
          valid := compiled.valid
          gate_delta := ?_ }
      rw [compiled.gate_delta, mapped.gate_delta]
      simp only [compileStmtGateCost]
      omega
  | push k emit continuation => by
      classical
      have hcontinuation :
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
      have hwires : CfgWires.ValidIn wires mapped.builder :=
        pushCfgWires_valid nextPool mapped.wires source mapped.valid
          (hvalid.mono mapped.extension)
      let compiled := compileStmt tm H mapped.builder nextPool wires hwires
        continuation hcontinuation
      refine
        { builder := compiled.builder
          wires := compiled.wires
          extension := mapped.extension.trans compiled.extension
          valid := compiled.valid
          gate_delta := ?_ }
      rw [compiled.gate_delta, mapped.gate_delta]
      simp only [compileStmtGateCost]
      omega
  | peek k update continuation => by
      classical
      have hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      let head := peekCfgWires k pool source
      let mapped := oneHotPairMap base source.state head
        (stmtHeadStateTable tm k update) hvalid.state
        (peekCfgWires_valid k pool source hvalid)
      let wires := source.replaceState mapped.wires
      have hwires : CfgWires.ValidIn wires mapped.builder :=
        (hvalid.mono mapped.extension).replaceState mapped.valid
      let compiled := compileStmt tm H mapped.builder
        (pool.mono mapped.extension) wires hwires continuation hcontinuation
      refine
        { builder := compiled.builder
          wires := compiled.wires
          extension := mapped.extension.trans compiled.extension
          valid := compiled.valid
          gate_delta := ?_ }
      rw [compiled.gate_delta, mapped.gate_delta]
      simp only [compileStmtGateCost]
      omega
  | pop k update continuation => by
      classical
      have hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      let popped := popCfgWires base pool source hvalid k
      let mapped := oneHotPairMap popped.builder popped.wires.state popped.head
        (stmtHeadStateTable tm k update) popped.valid.state popped.headValid
      let wires := popped.wires.replaceState mapped.wires
      have hwires : CfgWires.ValidIn wires mapped.builder :=
        (popped.valid.mono mapped.extension).replaceState mapped.valid
      let hext := popped.extension.trans mapped.extension
      let compiled := compileStmt tm H mapped.builder
        (pool.mono hext) wires hwires continuation hcontinuation
      refine
        { builder := compiled.builder
          wires := compiled.wires
          extension := hext.trans compiled.extension
          valid := compiled.valid
          gate_delta := ?_ }
      rw [compiled.gate_delta, mapped.gate_delta, popped.gate_delta]
      simp only [compileStmtGateCost]
      omega
  | branch test whenTrue whenFalse => by
      classical
      have htrueSupport :
          ∀ k, stmtPushSet tm whenTrue k ⊆ reachableAlphabet tm k := by
        intro k symbol hsymbol
        apply hsupport k
        simp only [stmtPushSet]
        exact Finset.mem_union_left _ hsymbol
      have hfalseSupport :
          ∀ k, stmtPushSet tm whenFalse k ⊆ reachableAlphabet tm k := by
        intro k symbol hsymbol
        apply hsupport k
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let predicate := oneHotPredicate base source.state
        (stmtPredicateTable tm test) hvalid.state
      let trueResult := compileStmt tm H predicate.builder
        (pool.mono predicate.extension) source
        (hvalid.mono predicate.extension) whenTrue htrueSupport
      let hbaseFalse := predicate.extension.trans trueResult.extension
      let falseResult := compileStmt tm H trueResult.builder
        (pool.mono hbaseFalse) source (hvalid.mono hbaseFalse)
        whenFalse hfalseSupport
      let hselectorExt := trueResult.extension.trans falseResult.extension
      let selected := cfgMux falseResult.builder predicate.wire
        trueResult.wires falseResult.wires
        (hselectorExt.wireValid predicate.valid)
        (trueResult.valid.mono falseResult.extension) falseResult.valid
      refine
        { builder := selected.builder
          wires := selected.wires
          extension := predicate.extension.trans
            (trueResult.extension.trans
              (falseResult.extension.trans selected.extension))
          valid := selected.valid
          gate_delta := ?_ }
      rw [selected.gate_delta, falseResult.gate_delta,
        trueResult.gate_delta, predicate.gate_delta]
      simp only [compileStmtGateCost]
      omega

/-! ## Public structural wrappers -/

/-- The builder returned by statement compilation has the advertised exact
structural gate delta. -/
theorem compileStmt_gate_delta
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H) (hvalid : source.ValidIn base)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    (compileStmt tm H base pool source hvalid q hsupport).builder.gates.length =
      base.gates.length + compileStmtGateCost tm H q :=
  (compileStmt tm H base pool source hvalid q hsupport).gate_delta

/-- Compilation is independent of all proof choices supplied for source
validity and finite push support. -/
theorem compileStmt_proof_irrel
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H)
    (hvalid₁ hvalid₂ : source.ValidIn base)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport₁ hsupport₂ :
      ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    compileStmt tm H base pool source hvalid₁ q hsupport₁ =
      compileStmt tm H base pool source hvalid₂ q hsupport₂ := by
  rfl


end

end CLRS.Chapter34.Turing.CookLevin
