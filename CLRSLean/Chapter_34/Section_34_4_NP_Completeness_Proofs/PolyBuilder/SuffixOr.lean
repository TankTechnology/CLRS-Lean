import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne.AffineRun

/-!
# Contextual affine suffix-OR serialization

The Cook--Levin stack-validity mask starts with one false seed and then scans
an affine source interval from right to left.  This module gives that exact
trace a concrete execution inside the shared three-counter serializer.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

namespace AffineSuffixOr

/-- Right-to-left OR gates over the affine interval
`base, ..., base + count - 1`. -/
def chunksFrom : Nat → Nat → Nat → List CircuitGate
  | _, _, 0 => []
  | start, base, count + 1 =>
      .or start (base + count) :: chunksFrom (start + 1) base count

theorem chunksFrom_tail (start base count : Nat) :
    chunksFrom start (base + 1) count ++ [.or (start + count) base] =
      chunksFrom start base (count + 1) := by
  induction count generalizing start base with
  | zero => simp [chunksFrom]
  | succ count ih =>
      change
        (CircuitGate.or start (base + 1 + count) ::
            chunksFrom (start + 1) (base + 1) count) ++
          [CircuitGate.or (start + (count + 1)) base] =
        CircuitGate.or start (base + (count + 1)) ::
          chunksFrom (start + 1) base (count + 1)
      rw [List.cons_append]
      have hhead : base + 1 + count = base + (count + 1) := by omega
      rw [hhead]
      apply congrArg (List.cons (CircuitGate.or start (base + (count + 1))))
      have hlast : start + (count + 1) = start + 1 + count := by omega
      rw [hlast]
      exact ih (start + 1) base

end AffineSuffixOr

/-- Exact forward encoding of an affine suffix-OR mask. -/
def affineSuffixOrGateStream (start base count : Nat) : List CircuitSym :=
  ([CircuitGate.const false] ++
    AffineSuffixOr.chunksFrom start base count).flatMap encodeCircuitGate

private theorem suffixOrGateTrace_range'_carry
    (start base count : Nat) :
    (suffixOrGateTrace start (List.range' base count)).carry =
      start + count := by
  induction count generalizing base with
  | zero => simp [suffixOrGateTrace]
  | succ count ih =>
      rw [List.range'_succ]
      simp only [suffixOrGateTrace]
      rw [suffixOrGateTrace_length]
      simp

private theorem suffixOrGateTrace_range'_gates
    (start base count : Nat) :
    (suffixOrGateTrace start (List.range' base count)).gates =
      [.const false] ++ AffineSuffixOr.chunksFrom start base count := by
  induction count generalizing base with
  | zero => simp [suffixOrGateTrace, AffineSuffixOr.chunksFrom]
  | succ count ih =>
      rw [List.range'_succ]
      simp only [suffixOrGateTrace]
      rw [ih, suffixOrGateTrace_range'_carry]
      change CircuitGate.const false ::
          (AffineSuffixOr.chunksFrom start (base + 1) count ++
            [CircuitGate.or (start + count) base]) =
        CircuitGate.const false ::
          AffineSuffixOr.chunksFrom start base (count + 1)
      exact congrArg (List.cons (CircuitGate.const false))
        (AffineSuffixOr.chunksFrom_tail start base count)

/-- The affine stream is exactly the semantic suffix-OR trace on its source
interval. -/
theorem affineSuffixOrGateStream_eq_trace (start base count : Nat) :
    affineSuffixOrGateStream start base count =
      (suffixOrGateTrace start (List.range' base count)).gates.flatMap
        encodeCircuitGate := by
  rw [suffixOrGateTrace_range'_gates]
  simp [affineSuffixOrGateStream]

/-- Contextual entry configuration for the reversed affine suffix-OR scan. -/
def affineSuffixOrBodyCfg (start base count : Nat)
    (output : List CircuitSym) : BuilderCfg sequentialExactlyOneRevProgram :=
  sequentialExactlyOneCfg (.suffixOr .next) none none false []
    (.constFalseMark :: output) (List.replicate count ()) []
    (List.replicate start ()) [] (List.replicate (base + count) ())

/-- Exact cost of the gate-producing loop, before final scratch cleanup. -/
def affineSuffixOrLoopSteps : Nat → Nat → Nat → Nat
  | _, _, 0 => 0
  | start, base, count + 1 =>
      5 * start + 5 * (base + count) + 12 +
        affineSuffixOrLoopSteps (start + 1) base count

private def suffixOrFinalBuffer
    (buffer₁ : Option Unit) : Nat → Option Unit
  | 0 => buffer₁
  | _ + 1 => some ()

@[simp] private theorem suffixOrFinalBuffer_some (count : Nat) :
    suffixOrFinalBuffer (some ()) count = some () := by
  cases count <;> rfl

@[simp] private theorem suffixOrFinalBuffer_succ
    (buffer₁ : Option Unit) (count : Nat) :
    suffixOrFinalBuffer buffer₁ (count + 1) = some () := by
  rfl

private def affineSuffixOr_loop
    (start base count : Nat) (buffer₁ : Option Unit)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg (.suffixOr .next) buffer₁ none false [] output
        (List.replicate count ()) [] (List.replicate start ()) []
        (List.replicate (base + count) ()))
      (some (sequentialExactlyOneCfg (.suffixOr .next)
        (suffixOrFinalBuffer buffer₁ count) none false []
        (((AffineSuffixOr.chunksFrom start base count).flatMap
          encodeCircuitGate).reverse ++ output) [] []
        (List.replicate (start + count) ()) [] (List.replicate base ())))
      (affineSuffixOrLoopSteps start base count) := by
  induction count generalizing start buffer₁ output with
  | zero =>
      exact ⟨⟨0, by simp [AffineSuffixOr.chunksFrom,
        suffixOrFinalBuffer]⟩, le_rfl⟩
  | succ count ih =>
      let afterPop := sequentialExactlyOneCfg (.suffixOr .decWire) (some ())
        none false [] output (List.replicate count ()) []
        (List.replicate start ()) [] (List.replicate (base + count + 1) ())
      have hpop : EvalsToInTime (step sequentialExactlyOneRevProgram)
          (sequentialExactlyOneCfg (.suffixOr .next) buffer₁ none false []
            output (List.replicate (count + 1) ()) []
            (List.replicate start ()) []
            (List.replicate (base + (count + 1)) ()))
          (some afterPop) 1 := by
        refine ⟨⟨1, ?_⟩, le_rfl⟩
        rw [show base + (count + 1) = base + count + 1 by omega]
        rw [Function.iterate_one]
        unfold afterPop
        rw [List.replicate_succ]
        rfl
      let beforePush := sequentialExactlyOneCfg (.suffixOr .push) (some ())
        none true [] output (List.replicate count ()) []
        (List.replicate start ()) [] (List.replicate (base + count) ())
      have hdec : EvalsToInTime (step sequentialExactlyOneRevProgram)
          afterPop (some beforePush) 1 := by
        refine ⟨⟨1, ?_⟩, le_rfl⟩
        change step sequentialExactlyOneRevProgram afterPop = some beforePush
        unfold afterPop beforePush
        rw [show base + count + 1 = Nat.succ (base + count) by omega,
          List.replicate_succ]
        rfl
      let c₀ := sequentialExactlyOneCfg (.encode .seen .suffixOrCarry)
        (some ()) none true [] (.orMark :: output)
        (List.replicate count ()) [] (List.replicate start ()) []
        (List.replicate (base + count) ())
      have hpush : EvalsToInTime (step sequentialExactlyOneRevProgram)
          beforePush (some c₀) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      let c₁ := sequentialExactlyOneCfg (.resume .suffixOrCarry)
        (some ()) none false []
        ((encNat start).reverse ++ .orMark :: output)
        (List.replicate count ()) [] (List.replicate start ()) []
        (List.replicate (base + count) ())
      have hcarry : EvalsToInTime (step sequentialExactlyOneRevProgram)
          c₀ (some c₁) (5 * start + 3) := by
        simpa [c₀, c₁] using
          encodeSeen_run start .suffixOrCarry (some ()) true []
            (.orMark :: output) (List.replicate count ()) []
            (List.replicate (base + count) ())
      let c₂ := sequentialExactlyOneCfg (.encode .wire .suffixOrWire)
        (some ()) none false []
        ((encNat start).reverse ++ .orMark :: output)
        (List.replicate count ()) [] (List.replicate start ()) []
        (List.replicate (base + count) ())
      have hjumpWire : EvalsToInTime (step sequentialExactlyOneRevProgram)
          c₁ (some c₂) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      let gateOutput :=
        (encodeCircuitGate (.or start (base + count))).reverse ++ output
      let c₃ := sequentialExactlyOneCfg (.resume .suffixOrWire)
        (some ()) none false [] gateOutput (List.replicate count ()) []
        (List.replicate start ()) [] (List.replicate (base + count) ())
      have hwire : EvalsToInTime (step sequentialExactlyOneRevProgram)
          c₂ (some c₃) (5 * (base + count) + 3) := by
        simpa [c₂, c₃, gateOutput, encodeCircuitGate, List.reverse_append,
          List.append_assoc] using
          encodeWire_run (base + count) .suffixOrWire (some ()) false []
            ((encNat start).reverse ++ .orMark :: output)
            (List.replicate count ()) (List.replicate start ()) []
      let c₄ := sequentialExactlyOneCfg (.suffixOr .incCarry) (some ()) none
        false [] gateOutput (List.replicate count ()) []
        (List.replicate start ()) [] (List.replicate (base + count) ())
      have hjumpInc : EvalsToInTime (step sequentialExactlyOneRevProgram)
          c₃ (some c₄) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      let afterInc := sequentialExactlyOneCfg (.suffixOr .next) (some ()) none
        false [] gateOutput (List.replicate count ()) []
        (List.replicate (start + 1) ()) []
        (List.replicate (base + count) ())
      have hinc : EvalsToInTime (step sequentialExactlyOneRevProgram)
          c₄ (some afterInc) 1 := by
        refine ⟨⟨1, ?_⟩, le_rfl⟩
        change step sequentialExactlyOneRevProgram c₄ = some afterInc
        unfold c₄ afterInc
        rw [show start + 1 = Nat.succ start by omega, List.replicate_succ]
        rfl
      have hremaining := ih (start + 1) (some ()) gateOutput
      let t₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
        1 1 _ afterPop _ hpop hdec
      let t₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
        2 1 _ beforePush _ t₁ hpush
      let t₃ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
        3 (5 * start + 3) _ c₀ _ t₂ hcarry
      let t₄ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
        _ 1 _ c₁ _ t₃ hjumpWire
      let t₅ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
        _ (5 * (base + count) + 3) _ c₂ _ t₄ hwire
      let t₆ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
        _ 1 _ c₃ _ t₅ hjumpInc
      let t₇ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
        _ 1 _ c₄ _ t₆ hinc
      let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
        _ (affineSuffixOrLoopSteps (start + 1) base count)
        _ afterInc _ t₇ hremaining
      convert full using 1
      · simp [gateOutput, AffineSuffixOr.chunksFrom,
          suffixOrFinalBuffer_some, List.flatMap_cons, List.reverse_append,
          List.append_assoc]
        rw [show start + (count + 1) = start + 1 + count by omega]
      · simp [affineSuffixOrLoopSteps]
        omega

/-- Exact total running time, including the empty-loop exit and cleanup. -/
def affineSuffixOrRevSteps (start base count : Nat) : Nat :=
  affineSuffixOrLoopSteps start base count + start + count + base + 5

/-- From arbitrary affine indices and output suffix, the shared counter
program emits the exact reversed suffix-OR encoding and clears all scratch
state before halting. -/
def affineSuffixOrRev_runFrom (start base count : Nat)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineSuffixOrBodyCfg start base count output)
      (some (haltCfg sequentialExactlyOneRevProgram
        ((affineSuffixOrGateStream start base count).reverse ++ output)))
      (affineSuffixOrRevSteps start base count) := by
  let seedOutput := .constFalseMark :: output
  have hloop := affineSuffixOr_loop start base count none seedOutput
  let beforeClear := sequentialExactlyOneCfg .clear₁
    none none false []
    (((AffineSuffixOr.chunksFrom start base count).flatMap
      encodeCircuitGate).reverse ++ seedOutput) [] []
    (List.replicate (start + count) ()) [] (List.replicate base ())
  have hexit : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg (.suffixOr .next)
        (suffixOrFinalBuffer none count) none false []
        (((AffineSuffixOr.chunksFrom start base count).flatMap
          encodeCircuitGate).reverse ++ seedOutput) [] []
        (List.replicate (start + count) ()) [] (List.replicate base ()))
      (some beforeClear) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hclear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeClear
      (some (haltCfg sequentialExactlyOneRevProgram
        (((AffineSuffixOr.chunksFrom start base count).flatMap
          encodeCircuitGate).reverse ++ seedOutput)))
      (start + count + base + 4) := by
    convert clearAllRegisters (start + count) 0 base
      none
      (((AffineSuffixOr.chunksFrom start base count).flatMap
        encodeCircuitGate).reverse ++ seedOutput) using 1 <;>
      simp [beforeClear]
  let throughExit := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (affineSuffixOrLoopSteps start base count) 1 _ _ _ hloop hexit
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (start + count + base + 4) _ beforeClear _ throughExit hclear
  convert full using 1
  · simp [affineSuffixOrBodyCfg, seedOutput]
  · simp [affineSuffixOrGateStream, seedOutput, List.append_assoc,
      encodeCircuitGate]
  · simp [affineSuffixOrRevSteps]
    omega

private theorem affineSuffixOrLoopSteps_le (start base count : Nat) :
    affineSuffixOrLoopSteps start base count ≤
      20 * count * (start + base + count + 1) := by
  induction count generalizing start with
  | zero => simp [affineSuffixOrLoopSteps]
  | succ count ih =>
      simp only [affineSuffixOrLoopSteps]
      have h := ih (start + 1)
      nlinarith

/-- Uniform quadratic envelope for the affine suffix-OR invocation. -/
theorem affineSuffixOrRev_steps_le (start base count : Nat) :
    affineSuffixOrRevSteps start base count ≤
      25 * (start + base + count + 1) ^ 2 := by
  have h := affineSuffixOrLoopSteps_le start base count
  simp [affineSuffixOrRevSteps]
  nlinarith

end CLRS.Chapter34.Turing.PolyBuilder
