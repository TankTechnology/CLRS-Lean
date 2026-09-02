import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementHead

/-!
# Builder-free statement-pop layout

Statement recursion needs both the popped configuration and the old head.
This module gives closed wire formulas for both outputs, including the
zero-height branch and the unique positive-height OR wire.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Pool-backed blank-head wires with the proof-carrying pool erased. -/
def arithmeticBlankHeadWires (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseWire trueWire : Nat) : HeadWires tm k :=
  fun code => if code = encodeHeadCode none then trueWire else falseWire

/-- Exact selected-stack output of a pop at a builder of length `start`. -/
def arithmeticPopStackWires (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseWire trueWire start : Nat) :
    (height : Nat) → StackWires tm height k → StackWires tm height k
  | 0, source => source
  | height + 1, source =>
      { height := fun i =>
          if i.val = 0 then start
          else if hnext : i.val + 1 < height + 2 then
            source.height ⟨i.val + 1, hnext⟩
          else falseWire
        cell := fun i =>
          if hnext : i.val + 1 < height + 1 then
            source.cell ⟨i.val + 1, hnext⟩
          else arithmeticBlankHeadWires tm k falseWire trueWire }

/-- Exact old-head output returned alongside a pop. -/
def arithmeticPopHeadWires (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseWire trueWire : Nat) :
    (height : Nat) → StackWires tm height k → HeadWires tm k
  | 0, _ => arithmeticBlankHeadWires tm k falseWire trueWire
  | _ + 1, source => source.cell 0

/-- Exact complete-row output of popping stack `k`. -/
def arithmeticPopCfgWires (tm : _root_.Turing.FinTM2) (height : Nat)
    (k : tm.K) (falseWire trueWire start : Nat)
    (source : CfgWires tm height) : CfgWires tm height :=
  source.replaceStack k
    (arithmeticPopStackWires tm k falseWire trueWire start height
      (source.stack k))

/-- The semantic wire-level pop's selected stack is exactly the arithmetic
layout. -/
theorem popStackWires_stack_eq_arithmetic
    {tm : _root_.Turing.FinTM2} {height : Nat} {k : tm.K}
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : StackWires tm height k) (hsource : source.ValidIn base) :
    (popStackWires base pool source hsource).stack =
      arithmeticPopStackWires tm k pool.falseWire pool.trueWire
        base.gates.length height source := by
  cases height with
  | zero => rfl
  | succ height =>
      apply StackBundle.ext
      · funext i
        by_cases hzero : i = 0
        · subst i
          simp [popStackWires, arithmeticPopStackWires,
            CircuitBuilder.or_wire_eq]
        · by_cases hnext : i.val ≤ height
          · simp [popStackWires, arithmeticPopStackWires, hzero, hnext]
          · simp [popStackWires, arithmeticPopStackWires, hzero, hnext]
      · funext i code
        by_cases hnext : i.val < height
        · simp [popStackWires, arithmeticPopStackWires, hnext]
        · simp [popStackWires, arithmeticPopStackWires,
            arithmeticBlankHeadWires, encodeHeadWires, hnext]

/-- The returned old head is likewise builder-free. -/
theorem popStackWires_head_eq_arithmetic
    {tm : _root_.Turing.FinTM2} {height : Nat} {k : tm.K}
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : StackWires tm height k) (hsource : source.ValidIn base) :
    (popStackWires base pool source hsource).head =
      arithmeticPopHeadWires tm k pool.falseWire pool.trueWire height source := by
  cases height with
  | zero =>
      funext code
      simp [popStackWires, arithmeticPopHeadWires,
        arithmeticBlankHeadWires, encodeHeadWires]
  | succ height => rfl

/-- Complete-row pop output wires depend only on the initial wire layout and
the three numeric seed coordinates. -/
theorem popCfgWires_wires_eq_arithmetic
    {tm : _root_.Turing.FinTM2} {height : Nat}
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm height) (hvalid : source.ValidIn base) (k : tm.K) :
    (popCfgWires base pool source hvalid k).wires =
      arithmeticPopCfgWires tm height k pool.falseWire pool.trueWire
        base.gates.length source := by
  change source.replaceStack k
      (popStackWires base pool (source.stack k) (hvalid.stack k)).stack = _
  rw [popStackWires_stack_eq_arithmetic]
  rfl

/-- Complete-row pop's auxiliary head output has the same arithmetic form. -/
theorem popCfgWires_head_eq_arithmetic
    {tm : _root_.Turing.FinTM2} {height : Nat}
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm height) (hvalid : source.ValidIn base) (k : tm.K) :
    (popCfgWires base pool source hvalid k).head =
      arithmeticPopHeadWires tm k pool.falseWire pool.trueWire height
        (source.stack k) := by
  unfold popCfgWires
  exact popStackWires_head_eq_arithmetic base pool (source.stack k)
    (hvalid.stack k)

end CLRS.Chapter34.Turing.CookLevin
