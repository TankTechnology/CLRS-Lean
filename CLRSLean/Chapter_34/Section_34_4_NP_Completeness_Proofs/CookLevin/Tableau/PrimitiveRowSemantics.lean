import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StackCircuits
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.ControlCircuits

/-!
# CLRS Section 34.4 - Complete-row stack primitive semantics

This module joins the independently verified stack-wire and canonical-row
layers.  It proves that push and pop update the complete decoded machine
configuration, not merely the selected stack projection, and exposes the old
pop head as an exact canonical one-hot family for downstream finite lookup.

Main results:

- Theorem {lit}`pushCfgWires_evalBundle`: complete-row push decodes exactly to
  dependent stack update by list cons.
- Theorem {lit}`peekCfgWires_head_eq_encode_of_evalBundle`: complete-row peek
  returns an exact canonical supported-head encoding.
- Theorems {lit}`popCfgWires_evalBundle` and
  {lit}`popCfgWires_head_eq_encode_of_evalBundle`: complete-row pop decodes
  exactly to list tail and returns an exact canonical old-head encoding.

The downstream {lit}`StatementCircuits` layer consumes these exact head
bridges to compile recursive machine statements.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Machine-configuration stack normal forms -/

/-- Update one machine-configuration stack by pushing one symbol. -/
def cfgPushStack {tm : _root_.Turing.FinTM2} (c : tm.Cfg) (k : tm.K)
    (symbol : tm.Γ k) : tm.Cfg :=
  { c with stk := Function.update c.stk k (symbol :: c.stk k) }

/-- Update one machine-configuration stack by removing its old head. -/
def cfgPopStack {tm : _root_.Turing.FinTM2} (c : tm.Cfg) (k : tm.K) : tm.Cfg :=
  { c with stk := Function.update c.stk k (c.stk k).tail }

/-- Push preserves the machine label. -/
@[simp] theorem cfgPushStack_label {tm : _root_.Turing.FinTM2}
    (c : tm.Cfg) (k : tm.K) (symbol : tm.Γ k) :
    (cfgPushStack c k symbol).l = c.l := rfl

/-- Push preserves the machine state. -/
@[simp] theorem cfgPushStack_state {tm : _root_.Turing.FinTM2}
    (c : tm.Cfg) (k : tm.K) (symbol : tm.Γ k) :
    (cfgPushStack c k symbol).var = c.var := rfl

/-- Push conses the symbol onto the selected stack. -/
@[simp] theorem cfgPushStack_stack_same {tm : _root_.Turing.FinTM2}
    (c : tm.Cfg) (k : tm.K) (symbol : tm.Γ k) :
    (cfgPushStack c k symbol).stk k = symbol :: c.stk k := by
  simp [cfgPushStack]

/-- Push preserves every nonselected dependent stack. -/
theorem cfgPushStack_stack_other {tm : _root_.Turing.FinTM2}
    (c : tm.Cfg) (k other : tm.K) (symbol : tm.Γ k)
    (hother : other ≠ k) :
    (cfgPushStack c k symbol).stk other = c.stk other := by
  simp [cfgPushStack, Function.update_of_ne hother]

/-- Pop preserves the machine label. -/
@[simp] theorem cfgPopStack_label {tm : _root_.Turing.FinTM2}
    (c : tm.Cfg) (k : tm.K) : (cfgPopStack c k).l = c.l := rfl

/-- Pop preserves the machine state. -/
@[simp] theorem cfgPopStack_state {tm : _root_.Turing.FinTM2}
    (c : tm.Cfg) (k : tm.K) : (cfgPopStack c k).var = c.var := rfl

/-- Pop replaces the selected stack by its list tail. -/
@[simp] theorem cfgPopStack_stack_same {tm : _root_.Turing.FinTM2}
    (c : tm.Cfg) (k : tm.K) :
    (cfgPopStack c k).stk k = (c.stk k).tail := by
  simp [cfgPopStack]

/-- Pop preserves every nonselected dependent stack. -/
theorem cfgPopStack_stack_other {tm : _root_.Turing.FinTM2}
    (c : tm.Cfg) (k other : tm.K) (hother : other ≠ k) :
    (cfgPopStack c k).stk other = c.stk other := by
  simp [cfgPopStack, Function.update_of_ne hother]

/-! ## Complete-row push -/

/-- A zero-gate complete-row push with one free cell decodes exactly to the
configuration obtained by consing the supported symbol on the selected stack. -/
theorem pushCfgWires_evalBundle
    {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    (builder : CircuitBuilder) (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (symbolWires : SymbolWires tm k)
    (source : CfgWires tm H) (hvalid : source.ValidIn builder)
    (hsymbolValid : SymbolWires.ValidIn symbolWires builder)
    {c : tm.Cfg} (hdecoded : evalBundle builder inputs source hvalid = some c)
    (symbol : SupportedSymbol tm k)
    (hsymbol : evalSymbolBits builder inputs symbolWires =
      encodeSymbolBits symbol)
    (hcapacity : (c.stk k).length < H) :
    evalBundle builder inputs (pushCfgWires pool symbolWires source)
      (pushCfgWires_valid pool symbolWires source hsymbolValid hvalid) =
        some (cfgPushStack c k symbol.val) := by
  classical
  rcases evalBundle_eq_some_canonical builder inputs source hvalid c hdecoded with
    ⟨hc, hheight, hbits⟩
  have hupdatedAlphabet : CfgAlphabetBounded tm (cfgPushStack c k symbol.val) := by
    intro other a ha
    by_cases hother : other = k
    · subst other
      simp only [cfgPushStack_stack_same, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact symbol.property
      · exact hc k a ha
    · rw [cfgPushStack_stack_other c k other symbol.val hother] at ha
      exact hc other a ha
  have hupdatedHeight :
      ∀ other, ((cfgPushStack c k symbol.val).stk other).length ≤ H := by
    intro other
    by_cases hother : other = k
    · subst other
      simp only [cfgPushStack_stack_same, List.length_cons]
      omega
    · rw [cfgPushStack_stack_other c k other symbol.val hother]
      exact hheight other
  have hconsAlphabet :
      ∀ a, a ∈ symbol.val :: c.stk k → a ∈ reachableAlphabet tm k := by
    simpa using hupdatedAlphabet k
  have hconsHeight : (symbol.val :: c.stk k).length ≤ H := by
    simpa using hupdatedHeight k
  have hselectedStack :
      pushStackBits (encodeSymbolBits symbol) H
          ((encodeRawCfgBits (encodeCfg tm hc hheight)).stack k) =
        (encodeRawCfgBits
          (encodeCfg tm hupdatedAlphabet hupdatedHeight)).stack k := by
    rw [encodeRawCfgBits_stack, encodeRawCfgBits_stack]
    simpa [encodeCfg, cfgPushStack] using
      pushStackBits_encodeBoundedStackBits symbol (c.stk k) (hc k)
        (hheight k) hcapacity hconsAlphabet hconsHeight
  apply evalBundle_encodeCfg builder inputs _ _ hupdatedAlphabet hupdatedHeight
  rw [pushCfgWires_eval, hbits, hsymbol]
  funext slot
  rcases slot with (_ | label | state | ⟨other, height | cell⟩)
  · rfl
  · rfl
  · rfl
  · classical
    by_cases hother : other = k
    · subst other
      simpa [CfgBundle.replaceStack, CfgBundle.stack,
        CfgBundle.stackHeight,
        CfgSlot.stackHeight] using
        congrFun (congrArg StackBundle.height hselectedStack) height
    · simp [CfgBundle.replaceStack, hother, encodeRawCfgBits, encodeCfg,
        cfgPushStack]
  · classical
    by_cases hother : other = k
    · subst other
      rcases cell with ⟨i, code⟩
      simpa [CfgBundle.replaceStack, CfgBundle.stack,
        CfgBundle.stackCell,
        CfgSlot.stackCell] using
        congrFun (congrFun (congrArg StackBundle.cell hselectedStack) i) code
    · rcases cell with ⟨i, code⟩
      simp [CfgBundle.replaceStack, hother, encodeRawCfgBits, encodeCfg,
        cfgPushStack]

/-! ## Complete-row peek -/

/-- A successful complete-row decode makes the zero-gate peek result an exact
canonical supported-head one-hot encoding.  The witness is obtained from the
decoder characterization, without exposing any choice-selected accessor. -/
theorem peekCfgWires_head_eq_encode_of_evalBundle
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (builder : CircuitBuilder) (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (source : CfgWires tm H)
    (hvalid : source.ValidIn builder) {c : tm.Cfg}
    (hdecoded : evalBundle builder inputs source hvalid = some c) (k : tm.K) :
    ∃ head : SupportedHead tm k,
      (c.stk k).head? = head.map Subtype.val ∧
        evalHeadBits builder inputs (peekCfgWires k pool source) =
          encodeHeadBits head := by
  have hdecode := peekCfgWires_represents_of_evalBundle k builder pool inputs
    source hvalid hdecoded
  rcases (decodeHeadValue_eq_some_iff
      (evalHeadBits builder inputs (peekCfgWires k pool source))
      (c.stk k).head?).mp hdecode with ⟨head, hvalue, htrue, hunique⟩
  refine ⟨head, hvalue, ?_⟩
  funext code
  by_cases hcode : code = encodeHeadCode head
  · subst code
    simp [encodeHeadBits, encodeOneHot, htrue]
  · have hfalse :
        evalHeadBits builder inputs (peekCfgWires k pool source) code = false :=
      Bool.eq_false_of_not_eq_true (fun h => hcode (hunique code h))
    simp [encodeHeadBits, encodeOneHot, hcode, hfalse]

/-! ## Complete-row pop -/

/-- The old head returned by a complete-row pop is an exact canonical
supported-head one-hot encoding, not merely a successfully decoded value. -/
theorem popCfgWires_head_eq_encode_of_evalBundle
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (builder : CircuitBuilder) (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (source : CfgWires tm H)
    (hvalid : source.ValidIn builder) {c : tm.Cfg}
    (hdecoded : evalBundle builder inputs source hvalid = some c) (k : tm.K) :
    ∃ head : SupportedHead tm k,
      (c.stk k).head? = head.map Subtype.val ∧
        evalHeadBits (popCfgWires builder pool source hvalid k).builder inputs
          (popCfgWires builder pool source hvalid k).head = encodeHeadBits head := by
  let result := popCfgWires builder pool source hvalid k
  have hdecode :=
    (popCfgWires_represents_of_evalBundle builder pool inputs source hvalid
      hdecoded k).2
  rcases (decodeHeadValue_eq_some_iff
    (evalHeadBits result.builder inputs result.head) (c.stk k).head?).mp
      hdecode with ⟨head, hvalue, htrue, hunique⟩
  refine ⟨head, hvalue, ?_⟩
  change evalHeadBits result.builder inputs result.head = encodeHeadBits head
  funext code
  by_cases hcode : code = encodeHeadCode head
  · subst code
    simp [encodeHeadBits, encodeOneHot, htrue]
  · have hfalse : evalHeadBits result.builder inputs result.head code = false :=
      Bool.eq_false_of_not_eq_true (fun h => hcode (hunique code h))
    simp [encodeHeadBits, encodeOneHot, hcode, hfalse]

/-- A complete-row pop decodes exactly to selected-stack tail and returns the
old head value. -/
theorem popCfgWires_evalBundle
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (builder : CircuitBuilder) (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (source : CfgWires tm H)
    (hvalid : source.ValidIn builder) {c : tm.Cfg}
    (hdecoded : evalBundle builder inputs source hvalid = some c) (k : tm.K) :
    evalBundle (popCfgWires builder pool source hvalid k).builder inputs
        (popCfgWires builder pool source hvalid k).wires
        (popCfgWires builder pool source hvalid k).valid =
      some (cfgPopStack c k) ∧
    decodeHeadValue?
        (evalHeadBits (popCfgWires builder pool source hvalid k).builder inputs
          (popCfgWires builder pool source hvalid k).head) =
      some (c.stk k).head? := by
  classical
  let result := popCfgWires builder pool source hvalid k
  rcases evalBundle_eq_some_canonical builder inputs source hvalid c hdecoded with
    ⟨hc, hheight, hbits⟩
  have hupdatedAlphabet : CfgAlphabetBounded tm (cfgPopStack c k) := by
    intro other a ha
    by_cases hother : other = k
    · subst other
      rw [cfgPopStack_stack_same] at ha
      exact hc k a (List.mem_of_mem_tail ha)
    · rw [cfgPopStack_stack_other c k other hother] at ha
      exact hc other a ha
  have hupdatedHeight :
      ∀ other, ((cfgPopStack c k).stk other).length ≤ H := by
    intro other
    by_cases hother : other = k
    · subst other
      rw [cfgPopStack_stack_same]
      rw [List.length_tail]
      have hold := hheight k
      omega
    · rw [cfgPopStack_stack_other c k other hother]
      exact hheight other
  have htailAlphabet :
      ∀ a, a ∈ (c.stk k).tail → a ∈ reachableAlphabet tm k := by
    simpa using hupdatedAlphabet k
  have htailHeight : (c.stk k).tail.length ≤ H := by
    simpa using hupdatedHeight k
  have hselectedStack :
      (popStackBits H
        ((encodeRawCfgBits (encodeCfg tm hc hheight)).stack k)).stack =
        (encodeRawCfgBits
          (encodeCfg tm hupdatedAlphabet hupdatedHeight)).stack k := by
    rw [encodeRawCfgBits_stack, encodeRawCfgBits_stack]
    simpa [encodeCfg, cfgPopStack] using
      popStackBits_encodeBoundedStackBits (c.stk k) (hc k)
        (hheight k) htailAlphabet htailHeight
  constructor
  · apply evalBundle_encodeCfg result.builder inputs _ _
      hupdatedAlphabet hupdatedHeight
    rw [result.eval, hbits]
    funext slot
    rcases slot with (_ | label | state | ⟨other, height | cell⟩)
    · rfl
    · rfl
    · rfl
    · by_cases hother : other = k
      · subst other
        simpa [CfgBundle.replaceStack, CfgBundle.stack,
          CfgBundle.stackHeight,
          CfgSlot.stackHeight] using
          congrFun (congrArg StackBundle.height hselectedStack) height
      · simp [CfgBundle.replaceStack, hother, encodeRawCfgBits, encodeCfg,
          cfgPopStack]
    · by_cases hother : other = k
      · subst other
        rcases cell with ⟨i, code⟩
        simpa [CfgBundle.replaceStack, CfgBundle.stack,
          CfgBundle.stackCell,
          CfgSlot.stackCell] using
          congrFun (congrFun (congrArg StackBundle.cell hselectedStack) i) code
      · rcases cell with ⟨i, code⟩
        simp [CfgBundle.replaceStack, hother, encodeRawCfgBits, encodeCfg,
          cfgPopStack]
  · exact (popCfgWires_represents_of_evalBundle builder pool inputs source
      hvalid hdecoded k).2

end

end CLRS.Chapter34.Turing.CookLevin
