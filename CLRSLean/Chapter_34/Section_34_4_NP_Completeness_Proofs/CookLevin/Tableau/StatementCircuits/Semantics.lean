import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits.Core

/-!
# CLRS Section 34.4 - Recursive statement-circuit semantics

Exact {lit}`evalBundle` semantics for all seven bundled TM2 statement constructors,
under explicit per-stack prefix capacity.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-! ## Exact decoded semantics -/

/-- {lit}`evalBundle` depends on a valid bundle only through its evaluated bits.
This small bridge is useful after selecting one of two already decoded rows. -/
private theorem evalBundle_of_evalCfgBits_eq
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (leftBuilder rightBuilder : CircuitBuilder) (inputs : Nat → Bool)
    (left : CfgWires tm H) (hleft : left.ValidIn leftBuilder)
    (right : CfgWires tm H) (hright : right.ValidIn rightBuilder)
    {c : tm.Cfg}
    (heq : evalCfgBits leftBuilder inputs left =
      evalCfgBits rightBuilder inputs right)
    (hdecoded : evalBundle rightBuilder inputs right hright = some c) :
    evalBundle leftBuilder inputs left hleft = some c := by
  unfold evalBundle evalRawBundle at hdecoded ⊢
  rw [heq]
  exact hdecoded

/-- Successful source decoding and enough capacity for every remaining push
make recursive statement compilation evaluate exactly as {lit}`TM2.stepAux`.

The capacity premise is intentionally prefix-sensitive: it is stated at the
public height {lit}`H` for every stack and counts all pushes still possible along
the selected statement path. -/
theorem compileStmt_evalBundle
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (inputs : Nat → Bool) (source : CfgWires tm H)
    (hvalid : source.ValidIn base)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    {c : tm.Cfg} (hdecoded : evalBundle base inputs source hvalid = some c)
    (hcapacity : ∀ k, (c.stk k).length + stmtMaxPushes tm k q ≤ H) :
    evalBundle
        (compileStmt tm H base pool source hvalid q hsupport).builder inputs
        (compileStmt tm H base pool source hvalid q hsupport).wires
        (compileStmt tm H base pool source hvalid q hsupport).valid =
      some (_root_.Turing.TM2.stepAux q c.var c.stk) := by
  induction q generalizing base source c with
  | halt =>
      have hrow := evalBundle_replaceStatus base inputs source hvalid c hdecoded
        (encodeLabelHaltedWire pool (none : Option tm.Λ))
        (encodeLabelHaltedWire_valid pool (none : Option tm.Λ))
        (encodeLabelWires pool (none : Option tm.Λ))
        (encodeLabelWires_valid pool (none : Option tm.Λ))
        (none : Option tm.Λ)
        (encodeLabelHaltedWire_eval pool inputs (none : Option tm.Λ))
        (encodeLabelWires_eval pool inputs (none : Option tm.Λ))
      change evalBundle base inputs
        (source.replaceStatus
          (encodeLabelHaltedWire pool (none : Option tm.Λ))
          (encodeLabelWires pool (none : Option tm.Λ))) _ =
        some { c with l := none }
      convert hrow using 1
  | goto jump =>
      let mapped := oneHotMap base source.state (stmtLabelTable tm jump)
        hvalid.state
      let nextPool := pool.mono mapped.extension
      let halted := encodeLabelHaltedWire nextPool (some (jump default))
      let wires := source.replaceStatus halted mapped.wires
      have hdecodedMapped :
          evalBundle mapped.builder inputs source
              (hvalid.mono mapped.extension) = some c := by
        rw [evalBundle_extends mapped.extension inputs source hvalid]
        exact hdecoded
      have hmapped : evalLabelBits mapped.builder inputs mapped.wires =
          encodeOneHot (encodeLabel tm (some (jump c.var))) := by
        have hstate := evalStateBits_of_evalBundle base inputs source hvalid c
          hdecoded
        change (fun j => mapped.builder.evalWire inputs (mapped.wires j)) = _
        simpa [mapped, stmtLabelTable] using
          (oneHotMap_eval_encodeOneHot base source.state
            (stmtLabelTable tm jump) hvalid.state inputs
            (stateEquivFin tm c.var) hstate)
      have hhalted : mapped.builder.evalWire inputs halted =
          labelHalted (some (jump c.var)) := by
        simp [halted, nextPool, encodeLabelHaltedWire_eval, labelHalted]
      have hrow := evalBundle_replaceStatus mapped.builder inputs source
        (hvalid.mono mapped.extension) c hdecodedMapped halted
        (encodeLabelHaltedWire_valid nextPool (some (jump default)))
        mapped.wires mapped.valid (some (jump c.var)) hhalted hmapped
      change evalBundle mapped.builder inputs wires _ =
        some (_root_.Turing.TM2.stepAux (goto jump) c.var c.stk)
      dsimp only [wires]
      convert hrow using 1
      rfl
  | load update continuation ih =>
      classical
      have hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      let mapped := oneHotMap base source.state (stmtStateTable tm update)
        hvalid.state
      let wires := source.replaceState mapped.wires
      have hwires : CfgWires.ValidIn wires mapped.builder :=
        (hvalid.mono mapped.extension).replaceState mapped.valid
      let updated : tm.Cfg := { c with var := update c.var }
      have hdecodedMapped :
          evalBundle mapped.builder inputs source
              (hvalid.mono mapped.extension) = some c := by
        rw [evalBundle_extends mapped.extension inputs source hvalid]
        exact hdecoded
      have hmapped : evalStateBits mapped.builder inputs mapped.wires =
          encodeOneHot (stateEquivFin tm updated.var) := by
        have hstate := evalStateBits_of_evalBundle base inputs source hvalid c
          hdecoded
        change (fun j => mapped.builder.evalWire inputs (mapped.wires j)) = _
        simpa [mapped, stmtStateTable, updated] using
          (oneHotMap_eval_encodeOneHot base source.state
            (stmtStateTable tm update) hvalid.state inputs
            (stateEquivFin tm c.var) hstate)
      have hrow : evalBundle mapped.builder inputs wires hwires = some updated := by
        simpa [wires, updated] using
          (evalBundle_replaceState mapped.builder inputs source
            (hvalid.mono mapped.extension) c hdecodedMapped mapped.wires
            mapped.valid updated.var hmapped)
      have hupdatedCapacity :
          ∀ k, (updated.stk k).length + stmtMaxPushes tm k continuation ≤ H := by
        simpa [updated, stmtMaxPushes] using hcapacity
      let compiled := compileStmt tm H mapped.builder
        (pool.mono mapped.extension) wires hwires continuation hcontinuation
      have hcompiled := ih (base := mapped.builder)
        (pool := pool.mono mapped.extension) (source := wires)
        (hvalid := hwires) (hsupport := hcontinuation) (c := updated)
        hrow hupdatedCapacity
      change evalBundle compiled.builder inputs compiled.wires compiled.valid =
        some (_root_.Turing.TM2.stepAux (load update continuation) c.var c.stk)
      simpa [compiled, updated] using hcompiled
  | push k emit continuation ih =>
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
      let symbol := symbolAt (stateEquivFin tm c.var)
      have hmapped : evalSymbolBits mapped.builder inputs mapped.wires =
          encodeSymbolBits symbol := by
        have hstate := evalStateBits_of_evalBundle base inputs source hvalid c
          hdecoded
        change (fun j => mapped.builder.evalWire inputs (mapped.wires j)) = _
        simpa [mapped, symbol, encodeSymbolBits] using
          (oneHotMap_eval_encodeOneHot base source.state
            (fun code => encodeSupportedSymbol (symbolAt code)) hvalid.state
            inputs (stateEquivFin tm c.var) hstate)
      have hdecodedMapped :
          evalBundle mapped.builder inputs source
              (hvalid.mono mapped.extension) = some c := by
        rw [evalBundle_extends mapped.extension inputs source hvalid]
        exact hdecoded
      have hfree : (c.stk k).length < H := by
        have h := hcapacity k
        simp only [stmtMaxPushes, if_pos] at h
        omega
      let updated := cfgPushStack c k symbol.val
      have hrow : evalBundle mapped.builder inputs wires hwires = some updated := by
        simpa [wires, updated] using
          (pushCfgWires_evalBundle mapped.builder nextPool inputs mapped.wires
            source (hvalid.mono mapped.extension) mapped.valid hdecodedMapped
            symbol hmapped hfree)
      have hupdatedCapacity :
          ∀ j, (updated.stk j).length + stmtMaxPushes tm j continuation ≤ H := by
        intro j
        by_cases hj : j = k
        · subst j
          have h := hcapacity k
          simpa [updated, cfgPushStack_stack_same, stmtMaxPushes,
            Nat.add_assoc] using h
        · have h := hcapacity j
          rw [cfgPushStack_stack_other c k j symbol.val hj]
          simp only [stmtMaxPushes, if_neg (Ne.symm hj)] at h
          simpa only [Nat.zero_add] using h
      let compiled := compileStmt tm H mapped.builder nextPool wires hwires
        continuation hcontinuation
      have hcompiled := ih (base := mapped.builder) (pool := nextPool)
        (source := wires) (hvalid := hwires) (hsupport := hcontinuation)
        (c := updated) hrow hupdatedCapacity
      change evalBundle compiled.builder inputs compiled.wires compiled.valid =
        some (_root_.Turing.TM2.stepAux (push k emit continuation) c.var c.stk)
      simpa [compiled, updated, symbol, symbolAt, cfgPushStack] using hcompiled
  | peek k update continuation ih =>
      classical
      have hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      let headWires := peekCfgWires k pool source
      let mapped := oneHotPairMap base source.state headWires
        (stmtHeadStateTable tm k update) hvalid.state
        (peekCfgWires_valid k pool source hvalid)
      let wires := source.replaceState mapped.wires
      have hwires : CfgWires.ValidIn wires mapped.builder :=
        (hvalid.mono mapped.extension).replaceState mapped.valid
      rcases peekCfgWires_head_eq_encode_of_evalBundle base pool inputs source
        hvalid hdecoded k with ⟨head, hheadValue, hheadBits⟩
      let updated : tm.Cfg := { c with var := update c.var (c.stk k).head? }
      have hmapped : evalStateBits mapped.builder inputs mapped.wires =
          encodeOneHot (stateEquivFin tm updated.var) := by
        have hstate := evalStateBits_of_evalBundle base inputs source hvalid c
          hdecoded
        have hpair := oneHotPairMap_eval_encodeOneHot base source.state
          headWires (stmtHeadStateTable tm k update) hvalid.state
          (peekCfgWires_valid k pool source hvalid) inputs
          (stateEquivFin tm c.var) (encodeHeadCode head) hstate hheadBits
        change (fun j => mapped.builder.evalWire inputs (mapped.wires j)) = _
        simpa [mapped, headWires, stmtHeadStateTable, updated, ← hheadValue]
          using hpair
      have hdecodedMapped :
          evalBundle mapped.builder inputs source
              (hvalid.mono mapped.extension) = some c := by
        rw [evalBundle_extends mapped.extension inputs source hvalid]
        exact hdecoded
      have hrow : evalBundle mapped.builder inputs wires hwires = some updated := by
        simpa [wires, updated] using
          (evalBundle_replaceState mapped.builder inputs source
            (hvalid.mono mapped.extension) c hdecodedMapped mapped.wires
            mapped.valid updated.var hmapped)
      have hupdatedCapacity :
          ∀ j, (updated.stk j).length + stmtMaxPushes tm j continuation ≤ H := by
        simpa [updated, stmtMaxPushes] using hcapacity
      let compiled := compileStmt tm H mapped.builder
        (pool.mono mapped.extension) wires hwires continuation hcontinuation
      have hcompiled := ih (base := mapped.builder)
        (pool := pool.mono mapped.extension) (source := wires)
        (hvalid := hwires) (hsupport := hcontinuation) (c := updated)
        hrow hupdatedCapacity
      change evalBundle compiled.builder inputs compiled.wires compiled.valid =
        some (_root_.Turing.TM2.stepAux (peek k update continuation) c.var c.stk)
      simpa [compiled, updated] using hcompiled
  | pop k update continuation ih =>
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
      have hpopped : evalBundle popped.builder inputs popped.wires popped.valid =
          some (cfgPopStack c k) := by
        exact (popCfgWires_evalBundle base pool inputs source hvalid hdecoded k).1
      rcases popCfgWires_head_eq_encode_of_evalBundle base pool inputs source
        hvalid hdecoded k with ⟨head, hheadValue, hheadBits⟩
      let updated : tm.Cfg :=
        { cfgPopStack c k with var := update c.var (c.stk k).head? }
      have hmapped : evalStateBits mapped.builder inputs mapped.wires =
          encodeOneHot (stateEquivFin tm updated.var) := by
        have hstate := evalStateBits_of_evalBundle popped.builder inputs
          popped.wires popped.valid (cfgPopStack c k) hpopped
        have hpair := oneHotPairMap_eval_encodeOneHot popped.builder
          popped.wires.state popped.head (stmtHeadStateTable tm k update)
          popped.valid.state popped.headValid inputs
          (stateEquivFin tm (cfgPopStack c k).var) (encodeHeadCode head)
          hstate hheadBits
        change (fun j => mapped.builder.evalWire inputs (mapped.wires j)) = _
        simpa [mapped, popped, stmtHeadStateTable, updated, ← hheadValue]
          using hpair
      have hpoppedMapped :
          evalBundle mapped.builder inputs popped.wires
              (popped.valid.mono mapped.extension) = some (cfgPopStack c k) := by
        rw [evalBundle_extends mapped.extension inputs popped.wires popped.valid]
        exact hpopped
      have hrow : evalBundle mapped.builder inputs wires hwires = some updated := by
        simpa [wires, updated] using
          (evalBundle_replaceState mapped.builder inputs popped.wires
            (popped.valid.mono mapped.extension) (cfgPopStack c k)
            hpoppedMapped mapped.wires mapped.valid updated.var hmapped)
      have hupdatedCapacity :
          ∀ j, (updated.stk j).length + stmtMaxPushes tm j continuation ≤ H := by
        intro j
        by_cases hj : j = k
        · subst j
          have h := hcapacity k
          simp only [updated, cfgPopStack_stack_same]
          have htail : (c.stk k).tail.length ≤ (c.stk k).length := by simp
          simp only [stmtMaxPushes] at h
          omega
        · rw [show updated.stk j = c.stk j from by
            simp [updated, cfgPopStack_stack_other c k j hj]]
          simpa [stmtMaxPushes] using hcapacity j
      let compiled := compileStmt tm H mapped.builder (pool.mono hext) wires
        hwires continuation hcontinuation
      have hcompiled := ih (base := mapped.builder) (pool := pool.mono hext)
        (source := wires) (hvalid := hwires) (hsupport := hcontinuation)
        (c := updated) hrow hupdatedCapacity
      change evalBundle compiled.builder inputs compiled.wires compiled.valid =
        some (_root_.Turing.TM2.stepAux (pop k update continuation) c.var c.stk)
      simpa [compiled, updated, cfgPopStack] using hcompiled
  | branch test whenTrue whenFalse ihTrue ihFalse =>
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
      have hpredicate : predicate.builder.evalWire inputs predicate.wire =
          test c.var := by
        have hstate := evalStateBits_of_evalBundle base inputs source hvalid c
          hdecoded
        simpa [predicate, stmtPredicateTable] using
          (oneHotPredicate_eval_encodeOneHot base source.state
            (stmtPredicateTable tm test) hvalid.state inputs
            (stateEquivFin tm c.var) hstate)
      have hdecodedPredicate :
          evalBundle predicate.builder inputs source
              (hvalid.mono predicate.extension) = some c := by
        rw [evalBundle_extends predicate.extension inputs source hvalid]
        exact hdecoded
      have hdecodedFalseBase :
          evalBundle trueResult.builder inputs source
              (hvalid.mono hbaseFalse) = some c := by
        rw [evalBundle_extends hbaseFalse inputs source hvalid]
        exact hdecoded
      have htrueCapacity :
          ∀ k, (c.stk k).length + stmtMaxPushes tm k whenTrue ≤ H := by
        intro k
        have h := hcapacity k
        simp only [stmtMaxPushes] at h
        omega
      have hfalseCapacity :
          ∀ k, (c.stk k).length + stmtMaxPushes tm k whenFalse ≤ H := by
        intro k
        have h := hcapacity k
        simp only [stmtMaxPushes] at h
        omega
      have htrueDecoded := ihTrue (base := predicate.builder)
        (pool := pool.mono predicate.extension) (source := source)
        (hvalid := hvalid.mono predicate.extension)
        (hsupport := htrueSupport) (c := c) hdecodedPredicate htrueCapacity
      have hfalseDecoded := ihFalse (base := trueResult.builder)
        (pool := pool.mono hbaseFalse) (source := source)
        (hvalid := hvalid.mono hbaseFalse) (hsupport := hfalseSupport)
        (c := c) hdecodedFalseBase hfalseCapacity
      have htrueDecodedAtFalse :
          evalBundle falseResult.builder inputs trueResult.wires
              (trueResult.valid.mono falseResult.extension) =
            some (_root_.Turing.TM2.stepAux whenTrue c.var c.stk) := by
        rw [evalBundle_extends falseResult.extension inputs trueResult.wires
          trueResult.valid]
        exact htrueDecoded
      have hpredicateFinal :
          falseResult.builder.evalWire inputs predicate.wire = test c.var := by
        rw [hselectorExt.evalWire_eq inputs predicate.valid]
        exact hpredicate
      cases htest : test c.var with
      | false =>
          have hbits : evalCfgBits selected.builder inputs selected.wires =
              evalCfgBits falseResult.builder inputs falseResult.wires := by
            rw [selected.eval]
            rw [hpredicateFinal, htest]
            rfl
          change evalBundle selected.builder inputs selected.wires selected.valid =
            some (_root_.Turing.TM2.stepAux
              (branch test whenTrue whenFalse) c.var c.stk)
          rw [_root_.Turing.TM2.stepAux, htest]
          exact evalBundle_of_evalCfgBits_eq selected.builder falseResult.builder
            inputs selected.wires selected.valid falseResult.wires
            falseResult.valid hbits hfalseDecoded
      | true =>
          have hbits : evalCfgBits selected.builder inputs selected.wires =
              evalCfgBits falseResult.builder inputs trueResult.wires := by
            rw [selected.eval]
            rw [hpredicateFinal, htest]
            rfl
          change evalBundle selected.builder inputs selected.wires selected.valid =
            some (_root_.Turing.TM2.stepAux
              (branch test whenTrue whenFalse) c.var c.stk)
          rw [_root_.Turing.TM2.stepAux, htest]
          exact evalBundle_of_evalCfgBits_eq selected.builder falseResult.builder
            inputs selected.wires selected.valid trueResult.wires
            (trueResult.valid.mono falseResult.extension) hbits
            htrueDecodedAtFalse

end

end CLRS.Chapter34.Turing.CookLevin
