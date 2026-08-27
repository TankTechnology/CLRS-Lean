import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StackSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder.ConstantPool

/-!
# CLRS Section 34.4 - Bounded-stack wire circuits

This module lifts the pure bounded-stack operations to valid circuit wires.
It reuses one explicit Boolean constant pool, keeps push and peek as zero-gate
wire rearrangements, allocates exactly one OR for positive-width pop, and one
NOT for a capacity query.

Main results:

- {lit}`pushStackWires_represents` and {lit}`peekStackWires_represents` connect
  zero-gate wire operations to canonical list semantics.
- {lit}`popStackWires` implements pop in zero gates at width zero and one gate
  at positive width, with exact evaluation and proof-irrelevance contracts.
- {lit}`popCfgWires` and {lit}`cfgStackCapacity` lift stack operations and
  semantic queries to complete configuration rows with explicit frame laws.

Layer boundary:

- Recursive statement compilation is supplied by downstream
  {lit}`StatementCircuits`; {lit}`TransitionCircuits` now supplies finite-label
  selection and the complete local step check.  Downstream fresh-row and
  assembly modules supply non-aliasing allocation and verified whole-tableau
  assembly.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Typed wire families and evaluation -/

/-- Circuit wires indexed by supported nonblank symbols. -/
abbrev SymbolWires (tm : _root_.Turing.FinTM2) (k : tm.K) :=
  SymbolBundle tm k CircuitBuilder.Wire

/-- Circuit wires indexed by supported symbols plus the legal blank head. -/
abbrev HeadWires (tm : _root_.Turing.FinTM2) (k : tm.K) :=
  HeadBundle tm k CircuitBuilder.Wire

namespace SymbolWires

/-- Every symbol wire belongs to the selected builder. -/
def ValidIn {tm : _root_.Turing.FinTM2} {k : tm.K}
    (wires : SymbolWires tm k) (builder : CircuitBuilder) : Prop :=
  ∀ i, builder.WireValid (wires i)

namespace ValidIn

/-- Symbol-wire validity is monotone under append-only builder extension. -/
theorem mono {tm : _root_.Turing.FinTM2} {k : tm.K}
    {wires : SymbolWires tm k} {base next : CircuitBuilder}
    (hvalid : wires.ValidIn base) (hext : base.Extends next) :
    wires.ValidIn next := fun i => hext.wireValid (hvalid i)

end ValidIn
end SymbolWires

namespace HeadWires

/-- Every optional-head wire belongs to the selected builder. -/
def ValidIn {tm : _root_.Turing.FinTM2} {k : tm.K}
    (wires : HeadWires tm k) (builder : CircuitBuilder) : Prop :=
  ∀ i, builder.WireValid (wires i)

namespace ValidIn

/-- Head-wire validity is monotone under append-only builder extension. -/
theorem mono {tm : _root_.Turing.FinTM2} {k : tm.K}
    {wires : HeadWires tm k} {base next : CircuitBuilder}
    (hvalid : wires.ValidIn base) (hext : base.Extends next) :
    wires.ValidIn next := fun i => hext.wireValid (hvalid i)

end ValidIn
end HeadWires

namespace StackWires

/-- Every height and physical-cell wire belongs to the selected builder. -/
structure ValidIn {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (wires : StackWires tm W k) (builder : CircuitBuilder) : Prop where
  /-- Every one-hot height-coordinate wire belongs to the selected builder. -/
  height : ∀ i, builder.WireValid (wires.height i)
  /-- Every physical-cell symbol-code wire belongs to the selected builder. -/
  cell : ∀ i code, builder.WireValid (wires.cell i code)

namespace ValidIn

/-- Stack-wire validity is monotone under append-only builder extension. -/
theorem mono {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    {wires : StackWires tm W k} {base next : CircuitBuilder}
    (hvalid : wires.ValidIn base) (hext : base.Extends next) :
    wires.ValidIn next :=
  ⟨fun i => hext.wireValid (hvalid.height i),
    fun i code => hext.wireValid (hvalid.cell i code)⟩

end ValidIn
end StackWires

/-- Evaluate a supported-symbol wire family. -/
def evalSymbolBits {tm : _root_.Turing.FinTM2} {k : tm.K}
    (builder : CircuitBuilder) (inputs : Nat → Bool)
    (wires : SymbolWires tm k) : SymbolBits tm k :=
  fun i => builder.evalWire inputs (wires i)

/-- Evaluate an optional-head wire family. -/
def evalHeadBits {tm : _root_.Turing.FinTM2} {k : tm.K}
    (builder : CircuitBuilder) (inputs : Nat → Bool)
    (wires : HeadWires tm k) : HeadBits tm k :=
  fun i => builder.evalWire inputs (wires i)

/-- Evaluate every coordinate of one bounded stack. -/
def evalStackBits {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (builder : CircuitBuilder) (inputs : Nat → Bool)
    (wires : StackWires tm W k) : StackBits tm W k where
  height i := builder.evalWire inputs (wires.height i)
  cell i code := builder.evalWire inputs (wires.cell i code)

/-- Evaluating an old valid symbol family is stable under extension. -/
theorem evalSymbolBits_extends {tm : _root_.Turing.FinTM2} {k : tm.K}
    {base next : CircuitBuilder} (hext : base.Extends next)
    (inputs : Nat → Bool) (wires : SymbolWires tm k)
    (hvalid : wires.ValidIn base) :
    evalSymbolBits next inputs wires = evalSymbolBits base inputs wires := by
  funext i
  exact hext.evalWire_eq inputs (hvalid i)

/-- Evaluating an old valid head family is stable under extension. -/
theorem evalHeadBits_extends {tm : _root_.Turing.FinTM2} {k : tm.K}
    {base next : CircuitBuilder} (hext : base.Extends next)
    (inputs : Nat → Bool) (wires : HeadWires tm k)
    (hvalid : wires.ValidIn base) :
    evalHeadBits next inputs wires = evalHeadBits base inputs wires := by
  funext i
  exact hext.evalWire_eq inputs (hvalid i)

/-- Evaluating an old valid stack is stable under extension. -/
theorem evalStackBits_extends {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    {base next : CircuitBuilder} (hext : base.Extends next)
    (inputs : Nat → Bool) (wires : StackWires tm W k)
    (hvalid : wires.ValidIn base) :
    evalStackBits next inputs wires = evalStackBits base inputs wires := by
  apply StackBundle.ext
  · funext i
    exact hext.evalWire_eq inputs (hvalid.height i)
  · funext i code
    exact hext.evalWire_eq inputs (hvalid.cell i code)

namespace CfgWires.ValidIn

/-- A valid complete row has a valid projection at every stack index. -/
theorem stack {tm : _root_.Turing.FinTM2} {H : Nat}
    {wires : CfgWires tm H} {builder : CircuitBuilder}
    (hvalid : wires.ValidIn builder) (k : tm.K) :
    StackWires.ValidIn (wires.stack k) builder :=
  ⟨fun _ => hvalid _, fun _ _ => hvalid _⟩

/-- Replacing one stack by valid wires preserves complete-row validity. -/
theorem replaceStack {tm : _root_.Turing.FinTM2} {H : Nat}
    {wires : CfgWires tm H} {builder : CircuitBuilder}
    (hvalid : wires.ValidIn builder) (k : tm.K)
    {replacement : StackWires tm H k}
    (hreplacement : replacement.ValidIn builder) :
    CfgWires.ValidIn (wires.replaceStack k replacement) builder := by
  intro slot
  rcases slot with (_ | label | state | ⟨other, height | cell⟩)
  · change builder.WireValid (wires (CfgSlot.halted tm H))
    exact hvalid _
  · change builder.WireValid (wires (CfgSlot.label label))
    exact hvalid _
  · change builder.WireValid (wires (CfgSlot.state state))
    exact hvalid _
  · by_cases hindex : other = k
    · subst other
      simpa [CfgBundle.replaceStack, CfgSlot.stackHeight] using
        hreplacement.height height
    · simpa [CfgBundle.replaceStack, CfgSlot.stackHeight, hindex] using
        hvalid (CfgSlot.stackHeight other height)
  · rcases cell with ⟨i, code⟩
    by_cases hindex : other = k
    · subst other
      simpa [CfgBundle.replaceStack, CfgSlot.stackCell] using
        hreplacement.cell i code
    · simpa [CfgBundle.replaceStack, CfgSlot.stackCell, hindex] using
        hvalid (CfgSlot.stackCell other i code)

end CfgWires.ValidIn

/-- Complete-row evaluation followed by stack projection equals direct stack
evaluation. -/
theorem evalStackBits_cfgStack {tm : _root_.Turing.FinTM2} {H : Nat}
    (builder : CircuitBuilder) (inputs : Nat → Bool)
    (wires : CfgWires tm H) (k : tm.K) :
    evalStackBits builder inputs (wires.stack k) =
      (evalCfgBits builder inputs wires).stack k := rfl

/-- Evaluation commutes with replacing one stack in a complete row. -/
theorem evalCfgBits_replaceStack {tm : _root_.Turing.FinTM2} {H : Nat}
    (builder : CircuitBuilder) (inputs : Nat → Bool)
    (wires : CfgWires tm H) (k : tm.K)
    (replacement : StackWires tm H k) :
    evalCfgBits builder inputs (wires.replaceStack k replacement) =
      (evalCfgBits builder inputs wires).replaceStack k
        (evalStackBits builder inputs replacement) := by
  funext slot
  rcases slot with (_ | label | state | ⟨other, height | cell⟩)
  · rfl
  · rfl
  · rfl
  · by_cases hindex : other = k
    · subst other
      simp [evalCfgBits, CfgBundle.replaceStack, evalStackBits]
    · simp [evalCfgBits, CfgBundle.replaceStack, hindex]
  · rcases cell with ⟨i, code⟩
    by_cases hindex : other = k
    · subst other
      simp [evalCfgBits, CfgBundle.replaceStack, evalStackBits]
    · simp [evalCfgBits, CfgBundle.replaceStack, hindex]

/-! ## Pool-backed static encodings -/

/-- Encode one supported symbol using existing true/false wires. -/
def encodeSymbolWires {tm : _root_.Turing.FinTM2} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (symbol : SupportedSymbol tm k) : SymbolWires tm k :=
  fun code => if code = encodeSupportedSymbol symbol then
    pool.trueWire else pool.falseWire

/-- A pool-backed static symbol encoding is valid without allocating gates. -/
theorem encodeSymbolWires_valid {tm : _root_.Turing.FinTM2} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (symbol : SupportedSymbol tm k) :
    (encodeSymbolWires pool symbol).ValidIn builder := by
  intro code
  by_cases hcode : code = encodeSupportedSymbol symbol
  · simp [encodeSymbolWires, hcode, pool.trueValid]
  · simp [encodeSymbolWires, hcode, pool.falseValid]

/-- Static symbol wires evaluate to the canonical one-hot symbol bits. -/
theorem encodeSymbolWires_eval {tm : _root_.Turing.FinTM2} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (symbol : SupportedSymbol tm k) :
    evalSymbolBits builder inputs (encodeSymbolWires pool symbol) =
      encodeSymbolBits symbol := by
  funext code
  by_cases hcode : code = encodeSupportedSymbol symbol
  · simp [evalSymbolBits, encodeSymbolWires, encodeSymbolBits, encodeOneHot,
      hcode, pool.true_eval]
  · simp [evalSymbolBits, encodeSymbolWires, encodeSymbolBits, encodeOneHot,
      hcode, pool.false_eval]

/-- Encode a supported optional head using existing true/false wires. -/
def encodeHeadWires {tm : _root_.Turing.FinTM2} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (head : SupportedHead tm k) : HeadWires tm k :=
  fun code => if code = encodeHeadCode head then pool.trueWire else pool.falseWire

/-- A pool-backed optional-head encoding is valid without allocating gates. -/
theorem encodeHeadWires_valid {tm : _root_.Turing.FinTM2} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (head : SupportedHead tm k) :
    (encodeHeadWires pool head).ValidIn builder := by
  intro code
  by_cases hcode : code = encodeHeadCode head
  · simp [encodeHeadWires, hcode, pool.trueValid]
  · simp [encodeHeadWires, hcode, pool.falseValid]

/-- Static optional-head wires evaluate to the canonical one-hot head bits. -/
theorem encodeHeadWires_eval {tm : _root_.Turing.FinTM2} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (head : SupportedHead tm k) :
    evalHeadBits builder inputs (encodeHeadWires pool head) =
      encodeHeadBits head := by
  funext code
  by_cases hcode : code = encodeHeadCode head
  · simp [evalHeadBits, encodeHeadWires, encodeHeadBits, encodeOneHot,
      hcode, pool.true_eval]
  · simp [evalHeadBits, encodeHeadWires, encodeHeadBits, encodeOneHot,
      hcode, pool.false_eval]

/-! ## Zero-gate push and peek -/

/-- Purely rearrange stack wires to push one symbol family. -/
def pushStackWires {tm : _root_.Turing.FinTM2} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (symbol : SymbolWires tm k) :
    (W : Nat) → StackWires tm W k → StackWires tm W k
  | 0, _ =>
      { height := fun _ => pool.falseWire
        cell := fun i => Fin.elim0 i }
  | _ + 1, stack =>
      { height := Fin.cases pool.falseWire (fun i => stack.height i.castSucc)
        cell := Fin.cases
          (fun code => if h : code.val < (reachableAlphabet tm k).card then
            symbol ⟨code.val, h⟩ else pool.falseWire)
          (fun i => stack.cell i.castSucc) }

/-- Zero-gate push preserves wire validity. -/
theorem pushStackWires_valid {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (symbol : SymbolWires tm k) (stack : StackWires tm W k)
    (hsymbol : symbol.ValidIn builder) (hstack : stack.ValidIn builder) :
    (pushStackWires pool symbol W stack).ValidIn builder := by
  cases W with
  | zero =>
      exact ⟨fun _ => pool.falseValid, fun i => Fin.elim0 i⟩
  | succ W =>
      constructor
      · intro i
        by_cases hi : i = 0
        · subst i
          exact pool.falseValid
        · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi
          exact hstack.height j.castSucc
      · intro i code
        by_cases hi : i = 0
        · subst i
          by_cases hcode : code.val < (reachableAlphabet tm k).card
          · simpa [pushStackWires, hcode] using hsymbol ⟨code.val, hcode⟩
          · simpa [pushStackWires, hcode] using pool.falseValid
        · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi
          exact hstack.cell j.castSucc code

/-- Evaluating zero-gate push gives the pure Boolean stack push. -/
theorem pushStackWires_eval {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (symbol : SymbolWires tm k)
    (stack : StackWires tm W k) :
    evalStackBits builder inputs (pushStackWires pool symbol W stack) =
      pushStackBits (evalSymbolBits builder inputs symbol) W
        (evalStackBits builder inputs stack) := by
  cases W with
  | zero =>
      apply StackBundle.ext
      · funext i
        simpa [evalStackBits, pushStackWires, pushStackBits] using
          pool.false_eval inputs
      · funext i
        exact Fin.elim0 i
  | succ W =>
      apply StackBundle.ext
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [evalStackBits, pushStackWires, pushStackBits] using
            pool.false_eval inputs
        · rfl
      · funext i code
        refine Fin.cases ?_ (fun j => ?_) i
        · by_cases hcode : code.val < (reachableAlphabet tm k).card
          · simp [evalStackBits, pushStackWires, pushStackBits,
              evalSymbolBits, hcode]
          · simpa [evalStackBits, pushStackWires, pushStackBits, hcode] using
              pool.false_eval inputs
        · rfl

/-- A wire push represents list cons when the old evaluated stack is
represented, the symbol wires encode the supplied symbol, and capacity holds. -/
theorem pushStackWires_represents {tm : _root_.Turing.FinTM2} {W : Nat}
    {k : tm.K} {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (symbolWires : SymbolWires tm k)
    (stack : StackWires tm W k) {xs : List (tm.Γ k)}
    (hstack : (evalStackBits builder inputs stack).Represents xs)
    (symbol : SupportedSymbol tm k)
    (hsymbol : evalSymbolBits builder inputs symbolWires =
      encodeSymbolBits symbol)
    (hcapacity : (evalStackBits builder inputs stack).HasCapacity) :
    (evalStackBits builder inputs
      (pushStackWires pool symbolWires W stack)).Represents
        (symbol.val :: xs) := by
  rw [pushStackWires_eval, hsymbol]
  exact pushStackBits_represents hstack symbol hcapacity

/-- Read old cell zero at positive width and a pool-backed legal empty head at
width zero, without allocating a gate. -/
def peekStackWires {tm : _root_.Turing.FinTM2} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool) :
    (W : Nat) → StackWires tm W k → HeadWires tm k
  | 0, _ => encodeHeadWires pool none
  | _ + 1, stack => stack.cell 0

/-- Zero-gate peek preserves wire validity. -/
theorem peekStackWires_valid {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (stack : StackWires tm W k) (hstack : stack.ValidIn builder) :
    (peekStackWires pool W stack).ValidIn builder := by
  cases W with
  | zero => exact encodeHeadWires_valid pool none
  | succ W => exact fun code => hstack.cell 0 code

/-- Evaluating zero-gate peek gives the pure Boolean stack peek. -/
theorem peekStackWires_eval {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (stack : StackWires tm W k) :
    evalHeadBits builder inputs (peekStackWires pool W stack) =
      peekStackBits W (evalStackBits builder inputs stack) := by
  cases W with
  | zero => exact encodeHeadWires_eval pool inputs none
  | succ W => rfl

/-- Peeking represented stack wires decodes to the represented list head. -/
theorem peekStackWires_represents {tm : _root_.Turing.FinTM2} {W : Nat}
    {k : tm.K} {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (stack : StackWires tm W k) {xs : List (tm.Γ k)}
    (hrep : (evalStackBits builder inputs stack).Represents xs) :
    decodeHeadValue? (evalHeadBits builder inputs
      (peekStackWires pool W stack)) = some xs.head? := by
  rw [peekStackWires_eval]
  exact peekStackBits_represents hrep

/-! ## Exact-cost pop and capacity circuits -/

/-- Exact number of gates allocated by wire-level pop. -/
def popStackWireGateCost : Nat → Nat
  | 0 => 0
  | _ + 1 => 1

/-- Width-zero pop allocates no gates. -/
@[simp] theorem popStackWireGateCost_zero : popStackWireGateCost 0 = 0 := rfl

/-- Every positive-width pop allocates exactly one height-merging OR. -/
@[simp] theorem popStackWireGateCost_succ (W : Nat) :
    popStackWireGateCost (W + 1) = 1 := rfl

/-- Proof-carrying result of popping one stack-wire bundle. -/
structure PopStackWiresResult {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (base : CircuitBuilder) (source : StackWires tm W k) where
  /-- Builder after the optional height-merging OR. -/
  builder : CircuitBuilder
  /-- Popped stack wires. -/
  stack : StackWires tm W k
  /-- The old stack head, or the legal empty head at width zero. -/
  head : HeadWires tm k
  /-- Pop preserves the complete input builder prefix. -/
  extension : base.Extends builder
  /-- Every popped stack wire is valid in the result builder. -/
  stackValid : stack.ValidIn builder
  /-- Every returned head wire is valid in the result builder. -/
  headValid : head.ValidIn builder
  /-- Pop has its exact zero/one-gate cost. -/
  gate_delta : builder.gates.length =
    base.gates.length + popStackWireGateCost W
  /-- Stack evaluation agrees exactly with pure Boolean pop. -/
  stack_eval : ∀ inputs, evalStackBits builder inputs stack =
    (popStackBits W (evalStackBits base inputs source)).stack
  /-- Head evaluation returns exactly the old pure Boolean head. -/
  head_eval : ∀ inputs, evalHeadBits builder inputs head =
    (popStackBits W (evalStackBits base inputs source)).head

/-- Pop stack wires, allocating only the positive-width height-zero OR and
reusing the supplied pool for blank cells. -/
def popStackWires {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : StackWires tm W k) (hsource : source.ValidIn base) :
    PopStackWiresResult base source := by
  cases W with
  | zero =>
      refine
        { builder := base
          stack := source
          head := encodeHeadWires pool none
          extension := .refl base
          stackValid := hsource
          headValid := encodeHeadWires_valid pool none
          gate_delta := by simp
          stack_eval := ?_
          head_eval := ?_ }
      · intro inputs
        rw [popStackBits_zero_stack]
      · intro inputs
        rw [popStackBits_zero_head]
        exact encodeHeadWires_eval pool inputs none
  | succ W =>
      let merged := base.or (source.height 0) (source.height 1)
        (hsource.height 0) (hsource.height 1)
      let hext : base.Extends merged.1 :=
        CircuitBuilder.or_extends base (source.height 0) (source.height 1)
          (hsource.height 0) (hsource.height 1)
      let nextPool := pool.mono hext
      let stack : StackWires tm (W + 1) k :=
        { height := fun i =>
            if i.val = 0 then merged.2
            else if hnext : i.val + 1 < W + 2 then
              source.height ⟨i.val + 1, hnext⟩
            else nextPool.falseWire
          cell := fun i =>
            if hnext : i.val + 1 < W + 1 then
              source.cell ⟨i.val + 1, hnext⟩
            else encodeHeadWires nextPool none }
      refine
        { builder := merged.1
          stack := stack
          head := source.cell 0
          extension := hext
          stackValid := ?_
          headValid := ?_
          gate_delta := ?_
          stack_eval := ?_
          head_eval := ?_ }
      · constructor
        · intro i
          by_cases hzero : i.val = 0
          · simpa [stack, hzero] using
              CircuitBuilder.or_wireValid base (source.height 0)
                (source.height 1) (hsource.height 0) (hsource.height 1)
          · by_cases hnext : i.val + 1 < W + 2
            · simpa [stack, hzero, hnext] using
                hext.wireValid (hsource.height ⟨i.val + 1, hnext⟩)
            · simpa [stack, hzero, hnext, nextPool] using nextPool.falseValid
        · intro i code
          by_cases hnext : i.val + 1 < W + 1
          · simpa [stack, hnext] using
              hext.wireValid (hsource.cell ⟨i.val + 1, hnext⟩ code)
          · simpa [stack, hnext] using
              encodeHeadWires_valid nextPool none code
      · exact fun code => hext.wireValid (hsource.cell 0 code)
      · simpa [merged, popStackWireGateCost] using
          CircuitBuilder.or_gate_delta base (source.height 0) (source.height 1)
            (hsource.height 0) (hsource.height 1)
      · intro inputs
        apply StackBundle.ext
        · funext i
          by_cases hzero : i.val = 0
          · have hi : i = 0 := Fin.ext hzero
            subst i
            simp only [stack, evalStackBits, popStackBits]
            simp only [Fin.val_zero, if_pos]
            rw [CircuitBuilder.or_eval base (source.height 0) (source.height 1)
              (hsource.height 0) (hsource.height 1)]
          · simp only [stack, evalStackBits, popStackBits]
            simp only [if_neg hzero]
            by_cases hnext : i.val + 1 < W + 2
            · simp only [dif_pos hnext]
              exact hext.evalWire_eq inputs
                (hsource.height ⟨i.val + 1, hnext⟩)
            · simp only [dif_neg hnext]
              exact nextPool.false_eval inputs
        · funext i code
          simp only [stack, evalStackBits, popStackBits]
          by_cases hnext : i.val + 1 < W + 1
          · rw [dif_pos hnext, dif_pos hnext]
            exact hext.evalWire_eq inputs
              (hsource.cell ⟨i.val + 1, hnext⟩ code)
          · rw [dif_neg hnext, dif_neg hnext]
            exact congrFun (encodeHeadWires_eval nextPool inputs none) code
      · intro inputs
        funext code
        exact hext.evalWire_eq inputs (hsource.cell 0 code)

/-- Pop construction is independent of the proof of source validity. -/
theorem popStackWires_proof_irrel
    {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : StackWires tm W k)
    (hsource₁ hsource₂ : source.ValidIn base) :
    popStackWires base pool source hsource₁ =
      popStackWires base pool source hsource₂ := by
  rfl

/-- Proof-carrying one-gate capacity query. -/
structure StackCapacityResult {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (base : CircuitBuilder) (source : StackWires tm W k) where
  /-- Builder after appending NOT full-height. -/
  builder : CircuitBuilder
  /-- Wire true exactly when the stack is not full. -/
  wire : CircuitBuilder.Wire
  /-- Capacity preserves the complete input prefix. -/
  extension : base.Extends builder
  /-- The result wire belongs to the result builder. -/
  valid : builder.WireValid wire
  /-- Capacity allocates exactly one NOT gate. -/
  gate_delta : builder.gates.length = base.gates.length + 1
  /-- Exact evaluation of the capacity wire. -/
  eval : ∀ inputs, builder.evalWire inputs wire =
    !(base.evalWire inputs (source.height (Fin.last W)))

/-- Allocate NOT full-height as the exact stack-capacity signal. -/
def stackCapacity {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (base : CircuitBuilder) (source : StackWires tm W k)
    (hsource : source.ValidIn base) : StackCapacityResult base source :=
  { builder := (base.not (source.height (Fin.last W))
      (hsource.height (Fin.last W))).1
    wire := (base.not (source.height (Fin.last W))
      (hsource.height (Fin.last W))).2
    extension := CircuitBuilder.not_extends base
      (source.height (Fin.last W)) (hsource.height (Fin.last W))
    valid := CircuitBuilder.not_wireValid base
      (source.height (Fin.last W)) (hsource.height (Fin.last W))
    gate_delta := CircuitBuilder.not_gate_delta base
      (source.height (Fin.last W)) (hsource.height (Fin.last W))
    eval := CircuitBuilder.not_eval base (source.height (Fin.last W))
      (hsource.height (Fin.last W)) }

/-- The one-gate capacity output is true exactly for the pure capacity
predicate. -/
theorem stackCapacity_eval_iff
    {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (base : CircuitBuilder) (inputs : Nat → Bool)
    (source : StackWires tm W k) (hsource : source.ValidIn base) :
    (stackCapacity base source hsource).builder.evalWire inputs
        (stackCapacity base source hsource).wire = true ↔
      (evalStackBits base inputs source).HasCapacity := by
  rw [(stackCapacity base source hsource).eval]
  simp [StackBits.HasCapacity, evalStackBits]

/-! ## Complete-row wrappers and frame laws -/

/-- Purely replace one row stack by its zero-gate pushed wires. -/
def pushCfgWires {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (symbol : SymbolWires tm k) (wires : CfgWires tm H) : CfgWires tm H :=
  wires.replaceStack k (pushStackWires pool symbol H (wires.stack k))

/-- Complete-row push preserves validity under symbol and row validity. -/
theorem pushCfgWires_valid {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (symbol : SymbolWires tm k) (wires : CfgWires tm H)
    (hsymbol : symbol.ValidIn builder) (hvalid : wires.ValidIn builder) :
    (pushCfgWires pool symbol wires).ValidIn builder :=
  hvalid.replaceStack k
    (pushStackWires_valid pool symbol (wires.stack k) hsymbol (hvalid.stack k))

/-- Evaluation of complete-row push is exactly pure stack replacement. -/
theorem pushCfgWires_eval {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (symbol : SymbolWires tm k)
    (wires : CfgWires tm H) :
    evalCfgBits builder inputs (pushCfgWires pool symbol wires) =
      (evalCfgBits builder inputs wires).replaceStack k
        (pushStackBits (evalSymbolBits builder inputs symbol) H
          ((evalCfgBits builder inputs wires).stack k)) := by
  rw [pushCfgWires, evalCfgBits_replaceStack, pushStackWires_eval]
  rfl

/-- A successfully decoded complete row, an exact evaluated symbol encoding,
and one free stack cell give the direct list-level semantics of complete-row
push. -/
theorem pushCfgWires_represents_of_evalBundle
    {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    (builder : CircuitBuilder) (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (symbolWires : SymbolWires tm k)
    (wires : CfgWires tm H) (hvalid : wires.ValidIn builder)
    {c : tm.Cfg} (hdecoded : evalBundle builder inputs wires hvalid = some c)
    (symbol : SupportedSymbol tm k)
    (hsymbol : evalSymbolBits builder inputs symbolWires =
      encodeSymbolBits symbol)
    (hcapacity : (c.stk k).length < H) :
    StackBits.Represents
      ((evalCfgBits builder inputs
        (pushCfgWires pool symbolWires wires)).stack k)
      (symbol.val :: c.stk k) := by
  rw [pushCfgWires_eval]
  simp only [CfgBundle.replaceStack_stack_same]
  rw [hsymbol]
  have hrep := evalBundle_stack_represents builder inputs wires hvalid hdecoded k
  exact pushStackBits_represents hrep symbol
    ((represents_hasCapacity_iff hrep).mpr hcapacity)

/-- Complete-row push preserves the halted wire. -/
@[simp] theorem pushCfgWires_halted
    {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (symbol : SymbolWires tm k) (wires : CfgWires tm H) :
    (pushCfgWires pool symbol wires).halted = wires.halted := by
  exact CfgBundle.replaceStack_halted wires k _

/-- Complete-row push preserves every label wire. -/
@[simp] theorem pushCfgWires_label
    {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (symbol : SymbolWires tm k) (wires : CfgWires tm H)
    (i : Fin (labelCount tm + 1)) :
    (pushCfgWires pool symbol wires).label i = wires.label i := by
  exact CfgBundle.replaceStack_label wires k _ i

/-- Complete-row push preserves every state wire. -/
@[simp] theorem pushCfgWires_state
    {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (symbol : SymbolWires tm k) (wires : CfgWires tm H)
    (i : Fin (stateCount tm)) :
    (pushCfgWires pool symbol wires).state i = wires.state i := by
  exact CfgBundle.replaceStack_state wires k _ i

/-- Complete-row push exposes the pushed selected stack. -/
@[simp] theorem pushCfgWires_stack_same
    {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (symbol : SymbolWires tm k) (wires : CfgWires tm H) :
    (pushCfgWires pool symbol wires).stack k =
      pushStackWires pool symbol H (wires.stack k) := by
  simp [pushCfgWires]

/-- Complete-row push preserves every different stack. -/
theorem pushCfgWires_stack_other
    {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (symbol : SymbolWires tm k) (wires : CfgWires tm H)
    (other : tm.K) (hother : other ≠ k) :
    (pushCfgWires pool symbol wires).stack other = wires.stack other :=
  CfgBundle.replaceStack_stack_other wires k other _ hother

/-- Read one selected row stack without allocating gates. -/
def peekCfgWires {tm : _root_.Turing.FinTM2} {H : Nat} (k : tm.K)
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (wires : CfgWires tm H) : HeadWires tm k :=
  peekStackWires pool H (wires.stack k)

/-- Complete-row peek returns valid head wires. -/
theorem peekCfgWires_valid {tm : _root_.Turing.FinTM2} {H : Nat} (k : tm.K)
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (wires : CfgWires tm H) (hvalid : wires.ValidIn builder) :
    (peekCfgWires k pool wires).ValidIn builder :=
  peekStackWires_valid pool (wires.stack k) (hvalid.stack k)

/-- Complete-row peek evaluates exactly to pure selected-stack peek. -/
theorem peekCfgWires_eval {tm : _root_.Turing.FinTM2} {H : Nat} (k : tm.K)
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (wires : CfgWires tm H) :
    evalHeadBits builder inputs (peekCfgWires k pool wires) =
      peekStackBits H ((evalCfgBits builder inputs wires).stack k) := by
  rw [peekCfgWires, peekStackWires_eval]
  rfl

/-- A successfully decoded complete row gives exact selected-stack peek
semantics. -/
theorem peekCfgWires_represents_of_evalBundle
    {tm : _root_.Turing.FinTM2} {H : Nat} (k : tm.K)
    (builder : CircuitBuilder) (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn builder) {c : tm.Cfg}
    (hdecoded : evalBundle builder inputs wires hvalid = some c) :
    decodeHeadValue? (evalHeadBits builder inputs
      (peekCfgWires k pool wires)) = some (c.stk k).head? := by
  rw [peekCfgWires_eval]
  exact peekStackBits_represents
    (evalBundle_stack_represents builder inputs wires hvalid hdecoded k)

/-- Query capacity of one selected complete-row stack. -/
def cfgStackCapacity {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) (k : tm.K) :
    StackCapacityResult base (wires.stack k) :=
  stackCapacity base (wires.stack k) (hvalid.stack k)

/-- For a successfully decoded row, selected-stack capacity is equivalent to
the decoded list length being strictly below the fixed width. -/
theorem cfgStackCapacity_eval_iff_length_lt
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (inputs : Nat → Bool)
    (wires : CfgWires tm H) (hvalid : wires.ValidIn base)
    {c : tm.Cfg} (hdecoded : evalBundle base inputs wires hvalid = some c)
    (k : tm.K) :
    (cfgStackCapacity base wires hvalid k).builder.evalWire inputs
        (cfgStackCapacity base wires hvalid k).wire = true ↔
      (c.stk k).length < H := by
  change
    (stackCapacity base (wires.stack k) (hvalid.stack k)).builder.evalWire inputs
        (stackCapacity base (wires.stack k) (hvalid.stack k)).wire = true ↔
      (c.stk k).length < H
  rw [stackCapacity_eval_iff]
  rw [evalStackBits_cfgStack]
  exact represents_hasCapacity_iff
    (evalBundle_stack_represents base inputs wires hvalid hdecoded k)

/-- Proof-carrying result of popping one selected stack in a complete row. -/
structure PopCfgWiresResult {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm H) (k : tm.K) where
  /-- Builder after the selected stack pop. -/
  builder : CircuitBuilder
  /-- Complete output row wires. -/
  wires : CfgWires tm H
  /-- Old selected-stack head. -/
  head : HeadWires tm k
  /-- Pop preserves the complete input builder prefix. -/
  extension : base.Extends builder
  /-- Every output row wire belongs to the result builder. -/
  valid : wires.ValidIn builder
  /-- Every returned head wire belongs to the result builder. -/
  headValid : head.ValidIn builder
  /-- Complete-row pop has the same exact cost as selected-stack pop. -/
  gate_delta : builder.gates.length =
    base.gates.length + popStackWireGateCost H
  /-- Complete output evaluation is pure selected-stack replacement by pop. -/
  eval : ∀ inputs, evalCfgBits builder inputs wires =
    (evalCfgBits base inputs source).replaceStack k
      (popStackBits H ((evalCfgBits base inputs source).stack k)).stack
  /-- Returned head evaluation is exactly the old selected-stack head. -/
  head_eval : ∀ inputs, evalHeadBits builder inputs head =
    (popStackBits H ((evalCfgBits base inputs source).stack k)).head

/-- Pop one selected complete-row stack, reusing all nonselected row wires. -/
def popCfgWires {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H) (hvalid : source.ValidIn base) (k : tm.K) :
    PopCfgWiresResult base source k := by
  let popped := popStackWires base pool (source.stack k) (hvalid.stack k)
  let wires := source.replaceStack k popped.stack
  refine
    { builder := popped.builder
      wires := wires
      head := popped.head
      extension := popped.extension
      valid := (hvalid.mono popped.extension).replaceStack k popped.stackValid
      headValid := popped.headValid
      gate_delta := popped.gate_delta
      eval := ?_
      head_eval := ?_ }
  · intro inputs
    rw [evalCfgBits_replaceStack]
    rw [popped.stack_eval]
    rw [evalCfgBits_extends popped.extension inputs source hvalid]
    rfl
  · intro inputs
    rw [popped.head_eval]
    rfl

/-- Complete-row pop is independent of the proof of source validity. -/
theorem popCfgWires_proof_irrel
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H) (hvalid₁ hvalid₂ : source.ValidIn base)
    (k : tm.K) :
    popCfgWires base pool source hvalid₁ k =
      popCfgWires base pool source hvalid₂ k := by
  rfl

/-- Complete-row pop preserves the halted wire. -/
@[simp] theorem popCfgWires_halted
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H) (hvalid : source.ValidIn base) (k : tm.K) :
    (popCfgWires base pool source hvalid k).wires.halted = source.halted := by
  exact CfgBundle.replaceStack_halted source k _

/-- Complete-row pop preserves every label wire. -/
@[simp] theorem popCfgWires_label
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H) (hvalid : source.ValidIn base) (k : tm.K)
    (i : Fin (labelCount tm + 1)) :
    (popCfgWires base pool source hvalid k).wires.label i = source.label i := by
  exact CfgBundle.replaceStack_label source k _ i

/-- Complete-row pop preserves every state wire. -/
@[simp] theorem popCfgWires_state
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H) (hvalid : source.ValidIn base) (k : tm.K)
    (i : Fin (stateCount tm)) :
    (popCfgWires base pool source hvalid k).wires.state i = source.state i := by
  exact CfgBundle.replaceStack_state source k _ i

/-- Complete-row pop exposes the selected popped stack. -/
@[simp] theorem popCfgWires_stack_same
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H) (hvalid : source.ValidIn base) (k : tm.K) :
    (popCfgWires base pool source hvalid k).wires.stack k =
      (popStackWires base pool (source.stack k) (hvalid.stack k)).stack := by
  simp [popCfgWires]

/-- Complete-row pop preserves every different stack. -/
theorem popCfgWires_stack_other
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H) (hvalid : source.ValidIn base) (k other : tm.K)
    (hother : other ≠ k) :
    (popCfgWires base pool source hvalid k).wires.stack other =
      source.stack other := by
  exact CfgBundle.replaceStack_stack_other source k other _ hother

/-- A successfully decoded input row gives exact list-level semantics for the
selected popped output stack and returned old head. -/
theorem popCfgWires_represents_of_evalBundle
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (inputs : Nat → Bool) (source : CfgWires tm H)
    (hvalid : source.ValidIn base) {c : tm.Cfg}
    (hdecoded : evalBundle base inputs source hvalid = some c) (k : tm.K) :
    StackBits.Represents
        ((evalCfgBits (popCfgWires base pool source hvalid k).builder inputs
          (popCfgWires base pool source hvalid k).wires).stack k)
        (c.stk k).tail ∧
      decodeHeadValue?
        (evalHeadBits (popCfgWires base pool source hvalid k).builder inputs
          (popCfgWires base pool source hvalid k).head) =
        some (c.stk k).head? := by
  let result := popCfgWires base pool source hvalid k
  have hrep := evalBundle_stack_represents base inputs source hvalid hdecoded k
  have hpop := popStackBits_represents hrep
  constructor
  · have heval := congrArg (fun bits => bits.stack k) (result.eval inputs)
    simp only [CfgBundle.replaceStack_stack_same] at heval
    rw [heval]
    exact hpop.1
  · rw [result.head_eval]
    exact hpop.2

end

end CLRS.Chapter34.Turing.CookLevin
