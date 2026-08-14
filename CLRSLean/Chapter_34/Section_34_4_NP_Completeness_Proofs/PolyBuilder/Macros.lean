import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine

/-!
# Verified bounded-builder macros

This file starts the reusable macro layer over the independently verified
bounded-builder semantics.  The scan/copy program uses two reversals: moving
the input to {lit}`work₁` reverses it once, and prepending each popped work
symbol to the output reverses it again.  Thus the observable output preserves
the original order.

For an input of length {lit}`n`, the exact cost is {lit}`n + 1` steps for the move
phase, {lit}`2n + 1` for the alternating pop/push phase, and one final halt step,
totaling {lit}`3n + 3`.

The bounded-loop program extends the same two-reversal discipline to a
symbol-local list-valued body.  Its exact cost is {lit}`2n + L + 3`, where
{lit}`L` is the length of the forward flat-map output.  Finite control stores a
dependent finite cursor into the current chunk, so the output alphabet needs
no finiteness or inhabitance assumption.

The nested-loop program duplicates the input onto two work stacks, restores
the inner copy after each row, and clears all scratch storage after emitting
ordered pairs in row-major order.  Its exact cost is {lit}`2n² + 5n + L + 4`.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-! ## Scan/copy program -/

/-- Finite control for the scan/copy macro.  A pushed symbol is carried by its
own label, so the construction does not require an inhabited input alphabet. -/
inductive ScanLabel (Γ : Type)
  | move
  | emit
  | push (symbol : Γ)
  | halt
deriving DecidableEq, Fintype

/-- Copy the entire input to the output with no semantic shortcut.

The move phase reverses the input onto {lit}`work₁`.  The emit and push labels
then pop that reversed stack and prepend each symbol to the output, restoring
the input order while emptying all scratch storage.
-/
def scanCopy {Γ : Type} [Fintype Γ] : Program Γ Γ := by
  classical
  exact
    { Label := ScanLabel Γ
      main := .move
      op
        | .move => .moveInputWork₁ .emit (fun _ => .move)
        | .emit => .popWork₁ .halt .push
        | .push symbol => .pushOutput symbol .emit
        | .halt => .halt }

/-- Exact independent-semantics step count of {name}`scanCopy`. -/
def scanCopySteps {Γ : Type} (input : List Γ) : Nat :=
  3 * input.length + 3

/-- Intermediate scan/copy configuration while moving input symbols onto
{lit}`work₁`. -/
private def scanMoveCfg {Γ : Type} [Fintype Γ]
    (buffer : Option Γ) (input moved : List Γ) :
    BuilderCfg (scanCopy (Γ := Γ)) :=
  { initialCfg (scanCopy (Γ := Γ)) input with
      buffer₁ := buffer
      work₁ := moved }

/-- Intermediate scan/copy configuration while popping {lit}`work₁` and
prepending symbols to the output. -/
private def scanEmitCfg {Γ : Type} [Fintype Γ]
    (buffer : Option Γ) (work output : List Γ) :
    BuilderCfg (scanCopy (Γ := Γ)) :=
  { initialCfg (scanCopy (Γ := Γ)) [] with
      label := some .emit
      buffer₁ := buffer
      output := output
      work₁ := work }

/-- Iteration equation underlying the exact move-phase witness. -/
private theorem scanCopy_movePhase_eval {Γ : Type} [Fintype Γ]
    (buffer : Option Γ) (input moved : List Γ) :
    (flip Option.bind (step (scanCopy (Γ := Γ))))^[input.length + 1]
      (some (scanMoveCfg buffer input moved)) =
        some (scanEmitCfg none (input.reverse ++ moved) []) := by
  induction input generalizing buffer moved with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show (symbol :: rest).length + 1 = rest.length + 1 + 1 by simp,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step (scanCopy (Γ := Γ))))^[rest.length + 1]
          (some (scanMoveCfg (some symbol) rest (symbol :: moved))) =
            some (scanEmitCfg none ((symbol :: rest).reverse ++ moved) [])
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some symbol) (symbol :: moved)

/-- The move phase performs one move per input symbol and one empty-stack
transition.  It reaches {lit}`emit` with empty input and the reversed input on
{lit}`work₁` in exactly {lit}`input.length + 1` steps. -/
def scanCopy_movePhase {Γ : Type} [Fintype Γ] (input : List Γ) :
    EvalsToInTime (step (scanCopy (Γ := Γ)))
      (initialCfg (scanCopy (Γ := Γ)) input)
      (some { initialCfg (scanCopy (Γ := Γ)) [] with
        label := some .emit
        work₁ := input.reverse })
      (input.length + 1) := by
  refine ⟨⟨input.length + 1, ?_⟩, le_rfl⟩
  simpa [scanMoveCfg, scanEmitCfg, initialCfg] using
    scanCopy_movePhase_eval (Γ := Γ) none input []

/-- The move-phase witness stores its advertised exact step count. -/
private theorem scanCopy_movePhase_steps {Γ : Type} [Fintype Γ]
    (input : List Γ) :
    (scanCopy_movePhase input).steps = input.length + 1 := by
  rfl

/-- Iteration equation underlying the exact alternating emit/push witness. -/
private theorem scanCopy_emitPushPhase_eval {Γ : Type} [Fintype Γ]
    (buffer : Option Γ) (work output : List Γ) :
    (flip Option.bind (step (scanCopy (Γ := Γ))))^[2 * work.length + 1]
      (some (scanEmitCfg buffer work output)) =
        some { haltCfg (scanCopy (Γ := Γ)) (work.reverse ++ output) with
          label := some .halt } := by
  induction work generalizing buffer output with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show 2 * (symbol :: rest).length + 1 =
          (2 * rest.length + 1) + 1 + 1 by
            simp
            omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step (scanCopy (Γ := Γ))))^[2 * rest.length + 1]
          (some (scanEmitCfg (some symbol) rest (symbol :: output))) =
            some { haltCfg (scanCopy (Γ := Γ))
              ((symbol :: rest).reverse ++ output) with label := some .halt }
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some symbol) (symbol :: output)

/-- The emit/push phase consumes the reversed input in two steps per symbol,
then takes one empty-stack transition to the halt label.  Its second reversal
restores the original input order on the output stack. -/
def scanCopy_emitPushPhase {Γ : Type} [Fintype Γ] (input : List Γ) :
    EvalsToInTime (step (scanCopy (Γ := Γ)))
      { initialCfg (scanCopy (Γ := Γ)) [] with
        label := some .emit
        work₁ := input.reverse }
      (some { haltCfg (scanCopy (Γ := Γ)) input with
        label := some .halt })
      (2 * input.length + 1) := by
  refine ⟨⟨2 * input.length + 1, ?_⟩, le_rfl⟩
  simpa [scanEmitCfg, initialCfg, haltCfg] using
    scanCopy_emitPushPhase_eval (Γ := Γ) none input.reverse []

/-- The emit/push witness stores its advertised exact step count. -/
private theorem scanCopy_emitPushPhase_steps {Γ : Type} [Fintype Γ]
    (input : List Γ) :
    (scanCopy_emitPushPhase input).steps = 2 * input.length + 1 := by
  rfl

/-- The final halt instruction clears control state in exactly one step. -/
def scanCopy_haltStep {Γ : Type} [Fintype Γ] (input : List Γ) :
    EvalsToInTime (step (scanCopy (Γ := Γ)))
      { haltCfg (scanCopy (Γ := Γ)) input with label := some .halt }
      (some (haltCfg (scanCopy (Γ := Γ)) input)) 1 := by
  refine ⟨⟨1, ?_⟩, le_rfl⟩
  rfl

/-- The halt-step witness stores its advertised one-step count. -/
private theorem scanCopy_haltStep_steps {Γ : Type} [Fintype Γ]
    (input : List Γ) :
    (scanCopy_haltStep input).steps = 1 := by
  rfl

/-! ## Exact output and polynomial-time packaging -/

/-- Canonical independent-semantics execution of scan/copy.  Its stored step
count is the exact phase sum, not merely a witness bounded by that sum. -/
def scanCopy_run {Γ : Type} [Fintype Γ] (input : List Γ) :
    EvalsToInTime (step (scanCopy (Γ := Γ)))
      (initialCfg (scanCopy (Γ := Γ)) input)
      (some (haltCfg (scanCopy (Γ := Γ)) input))
      (scanCopySteps input) := by
  let hmoveEmit : EvalsToInTime (step (scanCopy (Γ := Γ)))
        (initialCfg (scanCopy (Γ := Γ)) input)
        (some { haltCfg (scanCopy (Γ := Γ)) input with
          label := some .halt })
        ((2 * input.length + 1) + (input.length + 1)) :=
    EvalsToInTime.trans (step (scanCopy (Γ := Γ)))
      (input.length + 1) (2 * input.length + 1)
      (initialCfg (scanCopy (Γ := Γ)) input)
      { initialCfg (scanCopy (Γ := Γ)) [] with
        label := some .emit
        work₁ := input.reverse }
      (some { haltCfg (scanCopy (Γ := Γ)) input with
        label := some .halt })
      (scanCopy_movePhase (Γ := Γ) input)
      (scanCopy_emitPushPhase (Γ := Γ) input)
  let hfull := EvalsToInTime.trans (step (scanCopy (Γ := Γ)))
    ((2 * input.length + 1) + (input.length + 1)) 1
    (initialCfg (scanCopy (Γ := Γ)) input)
    { haltCfg (scanCopy (Γ := Γ)) input with label := some .halt }
    (some (haltCfg (scanCopy (Γ := Γ)) input)) hmoveEmit
      (scanCopy_haltStep (Γ := Γ) input)
  have hfullSteps : hfull.steps = scanCopySteps input := by
    simp only [hfull, hmoveEmit, evalsToInTime_trans_steps,
      scanCopy_haltStep_steps, scanCopy_emitPushPhase_steps,
      scanCopy_movePhase_steps]
    simp [scanCopySteps]
    omega
  refine ⟨⟨scanCopySteps input, ?_⟩, le_rfl⟩
  rw [← hfullSteps]
  exact hfull.evals_in_steps

/-- The canonical independent run stores the exact advertised count. -/
theorem scanCopy_run_steps {Γ : Type} [Fintype Γ] (input : List Γ) :
    (scanCopy_run input).steps = scanCopySteps input := by
  rfl

/-- The independent builder semantics copies every input exactly in
{lit}`3 * input.length + 3` steps. -/
theorem scanCopy_builderOutputs {Γ : Type} [Fintype Γ] :
    BuilderOutputs (scanCopy (Γ := Γ)) id scanCopySteps := by
  intro input
  exact ⟨scanCopy_run input⟩

/-- Canonical compiled scan/copy execution obtained by exact builder-run
transport through the verified compiler. -/
def scanCopy_compiledRun {Γ : Type} [Fintype Γ] (input : List Γ) :
    _root_.Turing.TM2OutputsInTime (compile (scanCopy (Γ := Γ))) input
      (some input) (scanCopySteps input) := by
  let run := compile_evalsToInTime (scanCopy (Γ := Γ)) (scanCopy_run input)
  refine ⟨⟨scanCopySteps input, ?_⟩, le_rfl⟩
  have runSteps : run.steps = scanCopySteps input := by
    simp only [run, compile_evalsToInTime_steps, scanCopy_run_steps]
  have runEval := run.evals_in_steps
  rw [runSteps] at runEval
  simpa [_root_.Turing.TM2OutputsInTime] using runEval

/-- The canonical compiled run preserves the exact builder step count. -/
theorem scanCopy_compiledRun_steps {Γ : Type} [Fintype Γ]
    (input : List Γ) :
    (scanCopy_compiledRun input).steps = scanCopySteps input := by
  rfl

/-- Compiling {name}`scanCopy` transports its exact builder run to an exact TM2
output run without changing the step bound. -/
theorem scanCopy_outputs {Γ : Type} [Fintype Γ] :
    Outputs (scanCopy (Γ := Γ)) id scanCopySteps := by
  intro input
  exact ⟨scanCopy_compiledRun (Γ := Γ) input⟩

/-- The exact linear scan/copy count is bounded by {lit}`3X + 3`. -/
noncomputable def scanCopy_polyBound {Γ : Type} :
    PolyBound (@scanCopySteps Γ) where
  polynomial := 3 * Polynomial.X + 3
  bound input := by
    simp [scanCopySteps, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X]

/-- Machine-level polynomial-time computability of list identity, witnessed by
the compiled scan/copy builder. -/
noncomputable def scanCopy_computableInPolyTime {Γ : Type} [Fintype Γ] :
    _root_.Turing.TM2ComputableInPolyTime id id (@id (List Γ)) :=
  ComputableInPolyTime (scanCopy (Γ := Γ)) id scanCopySteps
    scanCopy_outputs scanCopy_polyBound

/-! ## Verified bounded loops -/

/-- A symbol-local body for the bounded-loop macro.

The semantic chunk is {lit}`emit`.  The natural number {lit}`cost` is a
possibly looser local cost envelope used only for the polynomial bound; exact
execution counts are stated using the actual emitted chunk length.
-/
structure LoopBody (Γ Δ : Type) where
  /-- Output chunk emitted for one input symbol. -/
  emit : Γ → List Δ
  /-- Symbol-local upper bound on the emitted chunk length. -/
  cost : Γ → Nat
  /-- The semantic output chunk fits inside its advertised local bound. -/
  emit_length_le_cost : ∀ symbol, (emit symbol).length ≤ cost symbol

/-- A finite position in the output chunk belonging to one input symbol.

Only the input symbol and a finite index enter control state.  In particular,
neither an output symbol nor a list of output symbols is required to form a
finite type.
-/
def BoundedLoopCursor {Γ Δ : Type} (body : LoopBody Γ Δ) :=
  Σ symbol : Γ, Fin (body.emit symbol).length

/-- The dependent finite cursor is finite whenever the input alphabet is. -/
instance boundedLoopCursorFintype {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) : Fintype (BoundedLoopCursor body) := by
  unfold BoundedLoopCursor
  infer_instance

/-- Control labels for a verified bounded loop.

Finiteness is supplied separately when a program is constructed, so the label
type itself is independent of a particular typeclass dictionary.
-/
inductive BoundedLoopLabel {Γ Δ : Type} (body : LoopBody Γ Δ)
  | move
  | emit
  | push (cursor : BoundedLoopCursor body)
  | halt

/-- Equivalence exposing that bounded-loop control contains only three fixed
labels and one finite dependent cursor family. -/
private def boundedLoopLabelEquiv {Γ Δ : Type}
    (body : LoopBody Γ Δ) :
    (Unit ⊕ (Unit ⊕ (BoundedLoopCursor body ⊕ Unit))) ≃
      BoundedLoopLabel body where
  toFun
    | .inl _ => .move
    | .inr (.inl _) => .emit
    | .inr (.inr (.inl cursor)) => .push cursor
    | .inr (.inr (.inr _)) => .halt
  invFun
    | .move => .inl ()
    | .emit => .inr (.inl ())
    | .push cursor => .inr (.inr (.inl cursor))
    | .halt => .inr (.inr (.inr ()))
  left_inv encoded := by rcases encoded with (_ | (_ | (_ | _))) <;> rfl
  right_inv label := by cases label <;> rfl

/-- Bounded-loop control remains finite without a finite output alphabet. -/
instance boundedLoopLabelFintype {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) : Fintype (BoundedLoopLabel body) :=
  Fintype.ofEquiv
    (Unit ⊕ (Unit ⊕ (BoundedLoopCursor body ⊕ Unit)))
    (boundedLoopLabelEquiv body)

/-- Classical equality on the finite dependent loop control. -/
noncomputable instance boundedLoopLabelDecidableEq {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) : DecidableEq (BoundedLoopLabel body) :=
  Classical.decEq _

/-- Continue at the preceding chunk position, or return to the work-stack pop
label after pushing position zero. -/
private def boundedLoopNextPushLabel {Γ Δ : Type}
    (body : LoopBody Γ Δ) (cursor : BoundedLoopCursor body) :
    BoundedLoopLabel body :=
  if hzero : cursor.2.val = 0 then .emit
  else .push ⟨cursor.1, ⟨cursor.2.val - 1, by omega⟩⟩

/-- Enter the last position of a nonempty emitted chunk, or immediately resume
the work-stack pop when the chunk is empty. -/
private def boundedLoopStartPushLabel {Γ Δ : Type}
    (body : LoopBody Γ Δ) (symbol : Γ) : BoundedLoopLabel body :=
  if hempty : (body.emit symbol).length = 0 then .emit
  else .push ⟨symbol, ⟨(body.emit symbol).length - 1, by omega⟩⟩

/-- Apply a bounded symbol-local body to every input symbol.

The program first reverses the input onto {lit}`work₁`.  It then pops symbols in
reverse input order and pushes each emitted chunk from its last position down
to zero.  These two reversals make the final output exactly
{lit}`input.flatMap body.emit` in forward order.
-/
def boundedLoop {Γ Δ : Type} [Fintype Γ] (body : LoopBody Γ Δ) :
    Program Γ Δ := by
  classical
  exact
    { Label := BoundedLoopLabel body
      labelFintype := by infer_instance
      main := .move
      op
        | .move => .moveInputWork₁ .emit (fun _ => .move)
        | .emit => .popWork₁ .halt (boundedLoopStartPushLabel body)
        | .push cursor =>
            .pushOutput ((body.emit cursor.1).get cursor.2)
              (boundedLoopNextPushLabel body cursor)
        | .halt => .halt }

/-- Exact independent-semantics step count of {name}`boundedLoop`. -/
def boundedLoopSteps {Γ Δ : Type} (body : LoopBody Γ Δ)
    (input : List Γ) : Nat :=
  2 * input.length + (input.flatMap body.emit).length + 3

/-- Intermediate bounded-loop configuration while moving input symbols onto
{lit}`work₁`. -/
private def boundedLoopMoveCfg {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (buffer : Option Γ) (input moved : List Γ) :
    BuilderCfg (boundedLoop body) :=
  { initialCfg (boundedLoop body) input with
      buffer₁ := buffer
      work₁ := moved }

/-- Intermediate bounded-loop configuration at the work-stack pop label. -/
private def boundedLoopEmitCfg {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (buffer : Option Γ) (work : List Γ)
    (output : List Δ) : BuilderCfg (boundedLoop body) :=
  { initialCfg (boundedLoop body) [] with
      label := some .emit
      buffer₁ := buffer
      work₁ := work
      output := output }

/-- Intermediate bounded-loop configuration at one finite chunk cursor. -/
private def boundedLoopPushCfg {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (buffer : Option Γ)
    (cursor : BoundedLoopCursor body) (work : List Γ) (output : List Δ) :
    BuilderCfg (boundedLoop body) :=
  { initialCfg (boundedLoop body) [] with
      label := some (.push cursor)
      buffer₁ := buffer
      work₁ := work
      output := output }

/-- Intermediate configuration selected immediately after popping one work
symbol: either the chunk's last finite cursor or the emit label for an empty
chunk. -/
private def boundedLoopChunkCfg {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (buffer : Option Γ) (symbol : Γ)
    (work : List Γ) (output : List Δ) : BuilderCfg (boundedLoop body) :=
  { initialCfg (boundedLoop body) [] with
      label := some (boundedLoopStartPushLabel body symbol)
      buffer₁ := buffer
      work₁ := work
      output := output }

/-- Iteration equation for the input-to-work move phase. -/
private theorem boundedLoop_movePhase_eval {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (buffer : Option Γ) (input moved : List Γ) :
    (flip Option.bind (step (boundedLoop body)))^[input.length + 1]
      (some (boundedLoopMoveCfg body buffer input moved)) =
        some (boundedLoopEmitCfg body none (input.reverse ++ moved) []) := by
  induction input generalizing buffer moved with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show (symbol :: rest).length + 1 = rest.length + 1 + 1 by simp,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step (boundedLoop body)))^[rest.length + 1]
          (some (boundedLoopMoveCfg body (some symbol) rest
            (symbol :: moved))) =
          some (boundedLoopEmitCfg body none
            ((symbol :: rest).reverse ++ moved) [])
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some symbol) (symbol :: moved)

/-- The move phase takes one transition per input symbol and one final empty
transition, leaving the reversed input on {lit}`work₁`. -/
def boundedLoop_movePhase {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (input : List Γ) :
    EvalsToInTime (step (boundedLoop body))
      (initialCfg (boundedLoop body) input)
      (some { initialCfg (boundedLoop body) [] with
        label := some .emit
        work₁ := input.reverse })
      (input.length + 1) := by
  refine ⟨⟨input.length + 1, ?_⟩, le_rfl⟩
  convert boundedLoop_movePhase_eval body none input [] using 1
  · simp [boundedLoopMoveCfg, initialCfg]
  · simp [boundedLoopEmitCfg, initialCfg]

/-- The bounded-loop move witness stores its exact advertised count. -/
private theorem boundedLoop_movePhase_steps {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (input : List Γ) :
    (boundedLoop_movePhase body input).steps = input.length + 1 := by
  rfl

/-- Taking one more element of a list appends exactly the indexed element to
the preceding prefix. -/
private theorem boundedLoop_take_succ {Δ : Type} (chunk : List Δ)
    (index : Fin chunk.length) :
    chunk.take (index.val + 1) =
      chunk.take index.val ++ [chunk.get index] := by
  rw [List.get_eq_getElem]
  rw [← List.concat_eq_append]
  exact (List.take_concat_get index.isLt).symm

/-- Iteration equation for descending a finite chunk cursor to position zero. -/
private theorem boundedLoop_pushPhase_eval {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (buffer : Option Γ)
    (cursor : BoundedLoopCursor body) (work : List Γ) (output : List Δ) :
    (flip Option.bind (step (boundedLoop body)))^[cursor.2.val + 1]
      (some (boundedLoopPushCfg body buffer cursor work output)) =
        some (boundedLoopEmitCfg body buffer work
          ((body.emit cursor.1).take (cursor.2.val + 1) ++ output)) := by
  generalize hn : cursor.2.val = n
  induction n generalizing cursor output with
  | zero =>
      have hzero : cursor.2.val = 0 := hn
      rw [Function.iterate_succ_apply]
      simp only [Function.iterate_zero_apply, flip, Option.bind_some]
      rw [show 0 + 1 = cursor.2.val + 1 by omega,
        boundedLoop_take_succ (body.emit cursor.1) cursor.2]
      simp [step, boundedLoop, boundedLoopPushCfg, boundedLoopEmitCfg,
        boundedLoopNextPushLabel, hzero, initialCfg]
      rfl
  | succ n ih =>
      have hpositive : cursor.2.val ≠ 0 := by omega
      let previous : BoundedLoopCursor body :=
        ⟨cursor.1, ⟨cursor.2.val - 1, by omega⟩⟩
      have hprevious : previous.2.val = n := by
        simp [previous]
        omega
      rw [Function.iterate_succ_apply]
      change
        (flip Option.bind (step (boundedLoop body)))^[n + 1]
          ((flip Option.bind (step (boundedLoop body)))
            (some (boundedLoopPushCfg body buffer cursor work output))) = _
      rw [show
        (flip Option.bind (step (boundedLoop body)))
            (some (boundedLoopPushCfg body buffer cursor work output)) =
          some (boundedLoopPushCfg body buffer previous work
            ((body.emit cursor.1).get cursor.2 :: output)) by
          simp only [flip, Option.bind_some, step]
          simp [boundedLoop, boundedLoopPushCfg,
            boundedLoopNextPushLabel, hpositive, previous, initialCfg]
          rfl]
      rw [ih previous ((body.emit cursor.1).get cursor.2 :: output) hprevious]
      congr 2
      simp only [previous]
      rw [show n + 1 + 1 = cursor.2.val + 1 by omega,
        boundedLoop_take_succ (body.emit cursor.1) cursor.2]
      simp only [hn, List.append_assoc, List.singleton_append]

/-- Iteration equation for emitting one complete symbol-local chunk. -/
private theorem boundedLoop_chunkPhase_eval {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (buffer : Option Γ) (symbol : Γ)
    (work : List Γ) (output : List Δ) :
    (flip Option.bind (step (boundedLoop body)))^[(body.emit symbol).length]
      (some (boundedLoopChunkCfg body buffer symbol work output)) =
        some (boundedLoopEmitCfg body buffer work
          (body.emit symbol ++ output)) := by
  by_cases hempty : (body.emit symbol).length = 0
  · have hchunk : body.emit symbol = [] := List.length_eq_zero_iff.mp hempty
    simp [hchunk, boundedLoopChunkCfg, boundedLoopEmitCfg,
      boundedLoopStartPushLabel]
  · let cursor : BoundedLoopCursor body :=
      ⟨symbol, ⟨(body.emit symbol).length - 1, by omega⟩⟩
    have hcursorSteps : cursor.2.val + 1 = (body.emit symbol).length := by
      simp [cursor]
      omega
    have run := boundedLoop_pushPhase_eval body buffer cursor work output
    rw [hcursorSteps] at run
    have hcfg :
        boundedLoopChunkCfg body buffer symbol work output =
          boundedLoopPushCfg body buffer cursor work output := by
      simp [boundedLoopChunkCfg, boundedLoopPushCfg,
        boundedLoopStartPushLabel, hempty, cursor]
    rw [hcfg]
    simpa [cursor] using run

/-- Iteration equation for consuming the reversed work stack and assembling
all chunks in forward input order. -/
private theorem boundedLoop_emitPhase_eval {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (buffer : Option Γ) (work : List Γ)
    (output : List Δ) :
    (flip Option.bind (step (boundedLoop body)))^[
        work.length + (work.reverse.flatMap body.emit).length + 1]
      (some (boundedLoopEmitCfg body buffer work output)) =
        some { haltCfg (boundedLoop body)
            (work.reverse.flatMap body.emit ++ output) with
          label := some .halt } := by
  induction work generalizing buffer output with
  | nil =>
      simp [boundedLoopEmitCfg, boundedLoop, haltCfg, initialCfg]
      rfl
  | cons symbol rest ih =>
      let remainingSteps :=
        rest.length + (rest.reverse.flatMap body.emit).length + 1
      have hsteps :
          (symbol :: rest).length +
                ((symbol :: rest).reverse.flatMap body.emit).length + 1 =
            remainingSteps + ((body.emit symbol).length + 1) := by
        simp [remainingSteps, List.reverse_cons, List.flatMap_append]
        omega
      rw [hsteps, Function.iterate_add_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step (boundedLoop body)))^[remainingSteps]
          ((flip Option.bind (step (boundedLoop body)))^[
              (body.emit symbol).length]
            (some (boundedLoopChunkCfg body (some symbol) symbol rest
              output))) = _
      rw [boundedLoop_chunkPhase_eval body (some symbol) symbol rest output,
        ih (some symbol) (body.emit symbol ++ output)]
      congr 2
      simp [List.reverse_cons, List.flatMap_append, List.append_assoc]

/-- After the move phase, the bounded loop consumes every work symbol and
assembles the exact forward {name}`List.flatMap` output. -/
def boundedLoop_emitPhase {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (input : List Γ) :
    EvalsToInTime (step (boundedLoop body))
      { initialCfg (boundedLoop body) [] with
        label := some .emit
        work₁ := input.reverse }
      (some { haltCfg (boundedLoop body) (input.flatMap body.emit) with
        label := some .halt })
      (input.length + (input.flatMap body.emit).length + 1) := by
  refine ⟨⟨input.length + (input.flatMap body.emit).length + 1, ?_⟩,
    le_rfl⟩
  simpa [boundedLoopEmitCfg, initialCfg] using
    boundedLoop_emitPhase_eval body none input.reverse []

/-- The bounded-loop emit witness stores its exact advertised count. -/
private theorem boundedLoop_emitPhase_steps {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (input : List Γ) :
    (boundedLoop_emitPhase body input).steps =
      input.length + (input.flatMap body.emit).length + 1 := by
  rfl

/-- The final bounded-loop halt instruction clears all finite control in one
exact step. -/
def boundedLoop_haltStep {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (output : List Δ) :
    EvalsToInTime (step (boundedLoop body))
      { haltCfg (boundedLoop body) output with label := some .halt }
      (some (haltCfg (boundedLoop body) output)) 1 := by
  refine ⟨⟨1, ?_⟩, le_rfl⟩
  rfl

/-- The bounded-loop halt witness stores its exact one-step count. -/
private theorem boundedLoop_haltStep_steps {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (output : List Δ) :
    (boundedLoop_haltStep body output).steps = 1 := by
  rfl

/-- Canonical exact independent-semantics run of a bounded loop. -/
def boundedLoop_run {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (input : List Γ) :
    EvalsToInTime (step (boundedLoop body))
      (initialCfg (boundedLoop body) input)
      (some (haltCfg (boundedLoop body) (input.flatMap body.emit)))
      (boundedLoopSteps body input) := by
  let hmoveEmit : EvalsToInTime (step (boundedLoop body))
      (initialCfg (boundedLoop body) input)
      (some { haltCfg (boundedLoop body) (input.flatMap body.emit) with
        label := some .halt })
      ((input.length + (input.flatMap body.emit).length + 1) +
        (input.length + 1)) :=
    EvalsToInTime.trans (step (boundedLoop body))
      (input.length + 1)
      (input.length + (input.flatMap body.emit).length + 1)
      (initialCfg (boundedLoop body) input)
      { initialCfg (boundedLoop body) [] with
        label := some .emit
        work₁ := input.reverse }
      (some { haltCfg (boundedLoop body) (input.flatMap body.emit) with
        label := some .halt })
      (boundedLoop_movePhase body input)
      (boundedLoop_emitPhase body input)
  let hfull := EvalsToInTime.trans (step (boundedLoop body))
    ((input.length + (input.flatMap body.emit).length + 1) +
      (input.length + 1)) 1
    (initialCfg (boundedLoop body) input)
    { haltCfg (boundedLoop body) (input.flatMap body.emit) with
      label := some .halt }
    (some (haltCfg (boundedLoop body) (input.flatMap body.emit)))
    hmoveEmit (boundedLoop_haltStep body (input.flatMap body.emit))
  have hfullSteps : hfull.steps = boundedLoopSteps body input := by
    simp only [hfull, hmoveEmit, evalsToInTime_trans_steps,
      boundedLoop_haltStep_steps, boundedLoop_emitPhase_steps,
      boundedLoop_movePhase_steps]
    simp [boundedLoopSteps]
    omega
  refine ⟨⟨boundedLoopSteps body input, ?_⟩, le_rfl⟩
  rw [← hfullSteps]
  exact hfull.evals_in_steps

/-- The canonical independent bounded-loop run stores the exact formula, not
merely a smaller witness beneath that upper bound. -/
theorem boundedLoop_run_steps {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (input : List Γ) :
    (boundedLoop_run body input).steps = boundedLoopSteps body input := by
  rfl

/-- Independent bounded-loop execution computes the exact forward flat-map
output within the exact advertised step count. -/
theorem boundedLoop_builderOutputs {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) :
    BuilderOutputs (boundedLoop body) (fun input => input.flatMap body.emit)
      (boundedLoopSteps body) := by
  intro input
  exact ⟨boundedLoop_run body input⟩

/-- Canonical compiled bounded-loop execution obtained by exact transport of
the independent builder run. -/
def boundedLoop_compiledRun {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (input : List Γ) :
    _root_.Turing.TM2OutputsInTime (compile (boundedLoop body)) input
      (some (input.flatMap body.emit)) (boundedLoopSteps body input) := by
  let run := compile_evalsToInTime (boundedLoop body)
    (boundedLoop_run body input)
  refine ⟨⟨boundedLoopSteps body input, ?_⟩, le_rfl⟩
  have runSteps : run.steps = boundedLoopSteps body input := by
    simp only [run, compile_evalsToInTime_steps, boundedLoop_run_steps]
  have runEval := run.evals_in_steps
  rw [runSteps] at runEval
  convert runEval using 1
  · simp
  · simp only [Option.map_some, Option.some.injEq]
    exact (encodeCfg_haltCfg (boundedLoop body)
      (input.flatMap body.emit)).symm

/-- Compilation preserves the exact stored bounded-loop step count. -/
theorem boundedLoop_compiledRun_steps {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (input : List Γ) :
    (boundedLoop_compiledRun body input).steps =
      boundedLoopSteps body input := by
  rfl

/-- The compiled bounded-loop TM2 computes the forward flat-map output at the
same exact step count as the independent builder semantics. -/
theorem boundedLoop_outputs {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) :
    Outputs (boundedLoop body) (fun input => input.flatMap body.emit)
      (boundedLoopSteps body) := by
  intro input
  exact ⟨boundedLoop_compiledRun body input⟩

/-- Finite sum of all symbol-local cost bounds.

This is a looser coefficient than a finite maximum, but it gives the same
linear envelope without a separate empty-input-alphabet case split.
-/
private def boundedLoopTotalCost {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) : Nat :=
  ∑ symbol : Γ, body.cost symbol

/-- Every local cost is bounded by the finite sum over the input alphabet. -/
private theorem boundedLoop_cost_le_total {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (symbol : Γ) :
    body.cost symbol ≤ boundedLoopTotalCost body := by
  classical
  unfold boundedLoopTotalCost
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ symbol)

/-- The exact total emitted length is at most input length times the finite
sum of the local cost envelope. -/
private theorem boundedLoop_flatMap_length_le {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) (input : List Γ) :
    (input.flatMap body.emit).length ≤
      input.length * boundedLoopTotalCost body := by
  rw [List.length_flatMap]
  calc
    (input.map fun symbol => (body.emit symbol).length).sum ≤
        (input.map fun _ => boundedLoopTotalCost body).sum :=
      List.sum_le_sum fun symbol _ =>
        le_trans (body.emit_length_le_cost symbol)
          (boundedLoop_cost_le_total body symbol)
    _ = input.length * boundedLoopTotalCost body := by simp

/-- Linear polynomial envelope derived from {lit}`LoopBody.cost` and its
proof that every emitted chunk fits that cost.

The coefficient uses the finite sum of local costs rather than their maximum.
This intentionally looser bound stays valid for an empty input alphabet
without choosing a default maximum or splitting on inhabitance.
-/
noncomputable def boundedLoop_polyBound {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) : PolyBound (boundedLoopSteps body) where
  polynomial :=
    ((2 + boundedLoopTotalCost body : Nat) : Polynomial Nat) *
      Polynomial.X + 3
  bound input := by
    have hflat := boundedLoop_flatMap_length_le body input
    simp only [boundedLoopSteps, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_natCast, Polynomial.eval_ofNat]
    calc
      2 * input.length + (input.flatMap body.emit).length + 3 ≤
          2 * input.length +
            input.length * boundedLoopTotalCost body + 3 := by omega
      _ = (2 + boundedLoopTotalCost body) * input.length + 3 := by ring

/-- Machine-level polynomial-time computability of the symbol-local flat-map,
witnessed by the compiled verified bounded loop. -/
noncomputable def boundedLoop_computableInPolyTime {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody Γ Δ) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => input.flatMap body.emit) :=
  ComputableInPolyTime (boundedLoop body)
    (fun input => input.flatMap body.emit) (boundedLoopSteps body)
    (boundedLoop_outputs body) (boundedLoop_polyBound body)

/-! ## Verified nested loops -/

/-- A finite position in the chunk emitted by one ordered input pair. -/
def NestedLoopCursor {Γ Δ : Type} (body : LoopBody (Γ × Γ) Δ) :=
  Σ pair : Γ × Γ, Fin (body.emit pair).length

/-- The nested-loop cursor is finite whenever the input alphabet is finite. -/
instance nestedLoopCursorFintype {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) : Fintype (NestedLoopCursor body) := by
  unfold NestedLoopCursor
  infer_instance

/-- Control labels for the verified nested loop.

The outer and inner labels carry input symbols, and a push label carries only
an ordered input pair plus a finite index into its emitted chunk.  The type is
independent of both a particular {name}`Fintype` dictionary and the output
alphabet's finiteness or inhabitance.
-/
inductive NestedLoopLabel {Γ Δ : Type} (body : LoopBody (Γ × Γ) Δ)
  | copy
  | outer
  | inner (outer : Γ)
  | push (cursor : NestedLoopCursor body)
  | restore
  | clear
  | halt

/-- Equivalence exposing the finite ingredients of nested-loop control. -/
private def nestedLoopLabelEquiv {Γ Δ : Type}
    (body : LoopBody (Γ × Γ) Δ) :
    (Unit ⊕ (Unit ⊕ (Γ ⊕ (NestedLoopCursor body ⊕
      (Unit ⊕ (Unit ⊕ Unit)))))) ≃ NestedLoopLabel body where
  toFun
    | .inl _ => .copy
    | .inr (.inl _) => .outer
    | .inr (.inr (.inl outer)) => .inner outer
    | .inr (.inr (.inr (.inl cursor))) => .push cursor
    | .inr (.inr (.inr (.inr (.inl _)))) => .restore
    | .inr (.inr (.inr (.inr (.inr (.inl _))))) => .clear
    | .inr (.inr (.inr (.inr (.inr (.inr _))))) => .halt
  invFun
    | .copy => .inl ()
    | .outer => .inr (.inl ())
    | .inner outer => .inr (.inr (.inl outer))
    | .push cursor => .inr (.inr (.inr (.inl cursor)))
    | .restore => .inr (.inr (.inr (.inr (.inl ()))))
    | .clear => .inr (.inr (.inr (.inr (.inr (.inl ())))))
    | .halt => .inr (.inr (.inr (.inr (.inr (.inr ())))))
  left_inv encoded := by
    rcases encoded with (_ | (_ | (_ | (_ | (_ | (_ | _)))))) <;> rfl
  right_inv label := by cases label <;> rfl

/-- Nested-loop control is finite when the input alphabet is finite. -/
instance nestedLoopLabelFintype {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) : Fintype (NestedLoopLabel body) :=
  Fintype.ofEquiv _ (nestedLoopLabelEquiv body)

/-- Classical equality for finite nested-loop control. -/
noncomputable instance nestedLoopLabelDecidableEq {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) : DecidableEq (NestedLoopLabel body) :=
  Classical.decEq _

/-- Continue at the preceding pair-chunk position, or resume the current inner
scan after pushing position zero. -/
private def nestedLoopNextPushLabel {Γ Δ : Type}
    (body : LoopBody (Γ × Γ) Δ) (cursor : NestedLoopCursor body) :
    NestedLoopLabel body :=
  if hzero : cursor.2.val = 0 then .inner cursor.1.1
  else .push ⟨cursor.1, ⟨cursor.2.val - 1, by omega⟩⟩

/-- Enter the last position of a nonempty pair chunk, or resume the inner scan
immediately when that chunk is empty. -/
private def nestedLoopStartPushLabel {Γ Δ : Type}
    (body : LoopBody (Γ × Γ) Δ) (pair : Γ × Γ) : NestedLoopLabel body :=
  if hempty : (body.emit pair).length = 0 then .inner pair.1
  else .push ⟨pair, ⟨(body.emit pair).length - 1, by omega⟩⟩

/-- Apply a pair-local body to every ordered input pair in row-major order.

The program first copies the reversed input to both work stacks.  It consumes
outer symbols from {lit}`work₁`; for each outer symbol it moves the full inner
copy from {lit}`work₂` to the input stack while emitting chunks, then restores
that copy.  Once all rows are emitted it clears the remaining inner copy and
halts with every scratch stack empty.
-/
def nestedLoop {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) : Program Γ Δ := by
  classical
  exact
    { Label := NestedLoopLabel body
      labelFintype := by infer_instance
      main := .copy
      op
        | .copy => .copyInputWorks .outer (fun _ => .copy)
        | .outer => .popWork₁ .clear (fun outer => .inner outer)
        | .inner outer => .moveWork₂Input .restore
            (fun inner => nestedLoopStartPushLabel body (outer, inner))
        | .push cursor =>
            .pushOutput ((body.emit cursor.1).get cursor.2)
              (nestedLoopNextPushLabel body cursor)
        | .restore => .moveInputWork₂ .outer (fun _ => .restore)
        | .clear => .popWork₂ .halt (fun _ => .clear)
        | .halt => .halt }

/-- Row-major semantic output of a nested loop. -/
def nestedLoopOutput {Γ Δ : Type} (body : LoopBody (Γ × Γ) Δ)
    (input : List Γ) : List Δ :=
  input.flatMap fun outer =>
    input.flatMap fun inner => body.emit (outer, inner)

/-- Exact independent-semantics step count of {name}`nestedLoop`. -/
def nestedLoopSteps {Γ Δ : Type} (body : LoopBody (Γ × Γ) Δ)
    (input : List Γ) : Nat :=
  2 * input.length ^ 2 + 5 * input.length +
    (nestedLoopOutput body input).length + 4

/-- Intermediate configuration during the initial two-work-stack copy. -/
private def nestedCopyCfg {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (buffer : Option Γ)
    (input work₁ work₂ : List Γ) : BuilderCfg (nestedLoop body) :=
  { initialCfg (nestedLoop body) input with
      buffer₁ := buffer
      work₁ := work₁
      work₂ := work₂ }

/-- Intermediate configuration at the outer-row pop label. -/
private def nestedOuterCfg {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (buffer₁ buffer₂ : Option Γ)
    (work₁ work₂ : List Γ) (output : List Δ) :
    BuilderCfg (nestedLoop body) :=
  { initialCfg (nestedLoop body) [] with
      label := some .outer
      buffer₁ := buffer₁
      buffer₂ := buffer₂
      work₁ := work₁
      work₂ := work₂
      output := output }

/-- Intermediate configuration while scanning the inner copy for one row. -/
private def nestedInnerCfg {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (buffer₁ buffer₂ : Option Γ)
    (outer : Γ) (input work₁ work₂ : List Γ) (output : List Δ) :
    BuilderCfg (nestedLoop body) :=
  { initialCfg (nestedLoop body) input with
      label := some (.inner outer)
      buffer₁ := buffer₁
      buffer₂ := buffer₂
      work₁ := work₁
      work₂ := work₂
      output := output }

/-- Intermediate configuration at one finite pair-chunk cursor. -/
private def nestedPushCfg {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (buffer₁ buffer₂ : Option Γ)
    (cursor : NestedLoopCursor body) (input work₁ work₂ : List Γ)
    (output : List Δ) : BuilderCfg (nestedLoop body) :=
  { initialCfg (nestedLoop body) input with
      label := some (.push cursor)
      buffer₁ := buffer₁
      buffer₂ := buffer₂
      work₁ := work₁
      work₂ := work₂
      output := output }

/-- Intermediate configuration selected after moving one inner symbol. -/
private def nestedChunkCfg {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (buffer₁ buffer₂ : Option Γ)
    (pair : Γ × Γ) (input work₁ work₂ : List Γ) (output : List Δ) :
    BuilderCfg (nestedLoop body) :=
  { initialCfg (nestedLoop body) input with
      label := some (nestedLoopStartPushLabel body pair)
      buffer₁ := buffer₁
      buffer₂ := buffer₂
      work₁ := work₁
      work₂ := work₂
      output := output }

/-- Intermediate configuration while restoring the inner input copy. -/
private def nestedRestoreCfg {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (buffer₁ buffer₂ : Option Γ)
    (input work₁ work₂ : List Γ) (output : List Δ) :
    BuilderCfg (nestedLoop body) :=
  { initialCfg (nestedLoop body) input with
      label := some .restore
      buffer₁ := buffer₁
      buffer₂ := buffer₂
      work₁ := work₁
      work₂ := work₂
      output := output }

/-- Intermediate configuration while clearing the retained inner copy. -/
private def nestedClearCfg {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (buffer₁ buffer₂ : Option Γ)
    (work₂ : List Γ) (output : List Δ) : BuilderCfg (nestedLoop body) :=
  { initialCfg (nestedLoop body) [] with
      label := some .clear
      buffer₁ := buffer₁
      buffer₂ := buffer₂
      work₂ := work₂
      output := output }

/-- Iteration equation for copying input to both work stacks. -/
private theorem nestedLoop_copyPhase_eval {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (buffer : Option Γ)
    (input work₁ work₂ : List Γ) :
    (flip Option.bind (step (nestedLoop body)))^[input.length + 1]
      (some (nestedCopyCfg body buffer input work₁ work₂)) =
        some (nestedOuterCfg body none none
          (input.reverse ++ work₁) (input.reverse ++ work₂) []) := by
  induction input generalizing buffer work₁ work₂ with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show (symbol :: rest).length + 1 = rest.length + 1 + 1 by simp,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step (nestedLoop body)))^[rest.length + 1]
          (some (nestedCopyCfg body (some symbol) rest
            (symbol :: work₁) (symbol :: work₂))) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some symbol) (symbol :: work₁) (symbol :: work₂)

/-- The copy phase duplicates the reversed input onto both work stacks in
exactly one step per symbol plus one empty-input transition. -/
def nestedLoop_copyPhase {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (input : List Γ) :
    EvalsToInTime (step (nestedLoop body))
      (initialCfg (nestedLoop body) input)
      (some { initialCfg (nestedLoop body) [] with
        label := some .outer
        work₁ := input.reverse
        work₂ := input.reverse })
      (input.length + 1) := by
  refine ⟨⟨input.length + 1, ?_⟩, le_rfl⟩
  convert nestedLoop_copyPhase_eval body none input [] [] using 1 <;>
    simp [nestedCopyCfg, nestedOuterCfg, initialCfg]

/-- The public copy-phase witness stores its exact advertised count. -/
private theorem nestedLoop_copyPhase_steps {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (input : List Γ) :
    (nestedLoop_copyPhase body input).steps = input.length + 1 := by
  rfl

/-- Iteration equation for descending one pair-chunk cursor to position zero. -/
private theorem nestedLoop_pushPhase_eval {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (buffer₁ buffer₂ : Option Γ)
    (cursor : NestedLoopCursor body) (input work₁ work₂ : List Γ)
    (output : List Δ) :
    (flip Option.bind (step (nestedLoop body)))^[cursor.2.val + 1]
      (some (nestedPushCfg body buffer₁ buffer₂ cursor
        input work₁ work₂ output)) =
      some (nestedInnerCfg body buffer₁ buffer₂ cursor.1.1
        input work₁ work₂
        ((body.emit cursor.1).take (cursor.2.val + 1) ++ output)) := by
  generalize hn : cursor.2.val = n
  induction n generalizing cursor output with
  | zero =>
      have hzero : cursor.2.val = 0 := hn
      rw [Function.iterate_succ_apply]
      simp only [Function.iterate_zero_apply, flip, Option.bind_some]
      rw [show 0 + 1 = cursor.2.val + 1 by omega,
        boundedLoop_take_succ (body.emit cursor.1) cursor.2]
      simp [step, nestedLoop, nestedPushCfg, nestedInnerCfg,
        nestedLoopNextPushLabel, hzero, initialCfg]
      rfl
  | succ n ih =>
      have hpositive : cursor.2.val ≠ 0 := by omega
      let previous : NestedLoopCursor body :=
        ⟨cursor.1, ⟨cursor.2.val - 1, by omega⟩⟩
      have hprevious : previous.2.val = n := by
        simp [previous]
        omega
      rw [Function.iterate_succ_apply]
      change
        (flip Option.bind (step (nestedLoop body)))^[n + 1]
          ((flip Option.bind (step (nestedLoop body)))
            (some (nestedPushCfg body buffer₁ buffer₂ cursor
              input work₁ work₂ output))) = _
      rw [show
        (flip Option.bind (step (nestedLoop body)))
            (some (nestedPushCfg body buffer₁ buffer₂ cursor
              input work₁ work₂ output)) =
          some (nestedPushCfg body buffer₁ buffer₂ previous
            input work₁ work₂ ((body.emit cursor.1).get cursor.2 :: output)) by
          simp only [flip, Option.bind_some, step]
          simp [nestedLoop, nestedPushCfg, nestedLoopNextPushLabel,
            hpositive, previous, initialCfg]
          rfl]
      rw [ih previous ((body.emit cursor.1).get cursor.2 :: output) hprevious]
      congr 2
      simp only [previous]
      rw [show n + 1 + 1 = cursor.2.val + 1 by omega,
        boundedLoop_take_succ (body.emit cursor.1) cursor.2]
      rw [show n + 1 = cursor.2.val by omega]
      simp only [List.append_assoc, List.singleton_append]

/-- Iteration equation for emitting one complete ordered-pair chunk. -/
private theorem nestedLoop_chunkPhase_eval {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (buffer₁ buffer₂ : Option Γ)
    (pair : Γ × Γ) (input work₁ work₂ : List Γ) (output : List Δ) :
    (flip Option.bind (step (nestedLoop body)))^[(body.emit pair).length]
      (some (nestedChunkCfg body buffer₁ buffer₂ pair
        input work₁ work₂ output)) =
      some (nestedInnerCfg body buffer₁ buffer₂ pair.1
        input work₁ work₂ (body.emit pair ++ output)) := by
  by_cases hempty : (body.emit pair).length = 0
  · have hchunk : body.emit pair = [] := List.length_eq_zero_iff.mp hempty
    simp [hchunk, nestedChunkCfg, nestedInnerCfg,
      nestedLoopStartPushLabel]
  · let cursor : NestedLoopCursor body :=
      ⟨pair, ⟨(body.emit pair).length - 1, by omega⟩⟩
    have hcursorSteps : cursor.2.val + 1 = (body.emit pair).length := by
      simp [cursor]
      omega
    have run := nestedLoop_pushPhase_eval body buffer₁ buffer₂ cursor
      input work₁ work₂ output
    rw [hcursorSteps] at run
    have hcfg :
        nestedChunkCfg body buffer₁ buffer₂ pair input work₁ work₂ output =
          nestedPushCfg body buffer₁ buffer₂ cursor input work₁ work₂ output := by
      simp [nestedChunkCfg, nestedPushCfg, nestedLoopStartPushLabel,
        hempty, cursor]
    rw [hcfg]
    simpa [cursor] using run

/-- Row emitted for one outer input symbol. -/
def nestedLoopRow {Γ Δ : Type} (body : LoopBody (Γ × Γ) Δ)
    (outer : Γ) (input : List Γ) : List Δ :=
  input.flatMap fun inner => body.emit (outer, inner)

/-- Iteration equation for moving and emitting an entire reversed inner copy. -/
private theorem nestedLoop_innerEmitPhase_eval {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (buffer₁ buffer₂ : Option Γ)
    (outer : Γ) (moved work₁ work₂ : List Γ) (output : List Δ) :
    (flip Option.bind (step (nestedLoop body)))^[
        work₂.length + (nestedLoopRow body outer work₂.reverse).length + 1]
      (some (nestedInnerCfg body buffer₁ buffer₂ outer
        moved work₁ work₂ output)) =
      some (nestedRestoreCfg body buffer₁ none
        (work₂.reverse ++ moved) work₁ []
        (nestedLoopRow body outer work₂.reverse ++ output)) := by
  induction work₂ generalizing buffer₂ moved output with
  | nil =>
      simp [nestedLoopRow, nestedInnerCfg, nestedRestoreCfg,
        nestedLoop, initialCfg]
      rfl
  | cons inner rest ih =>
      let remainingSteps :=
        rest.length + (nestedLoopRow body outer rest.reverse).length + 1
      have hsteps :
          (inner :: rest).length +
                (nestedLoopRow body outer (inner :: rest).reverse).length + 1 =
            remainingSteps + ((body.emit (outer, inner)).length + 1) := by
        simp [remainingSteps, nestedLoopRow, List.reverse_cons,
          List.flatMap_append]
        omega
      rw [hsteps, Function.iterate_add_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step (nestedLoop body)))^[remainingSteps]
          ((flip Option.bind (step (nestedLoop body)))^[
              (body.emit (outer, inner)).length]
            (some (nestedChunkCfg body buffer₁ (some inner) (outer, inner)
              (inner :: moved) work₁ rest output))) = _
      rw [nestedLoop_chunkPhase_eval body buffer₁ (some inner) (outer, inner)
        (inner :: moved) work₁ rest output,
        ih (some inner) (inner :: moved) (body.emit (outer, inner) ++ output)]
      congr 2
      · simp [List.reverse_cons, List.append_assoc]
      · simp [nestedLoopRow, List.reverse_cons, List.flatMap_append,
          List.append_assoc]

/-- For one outer symbol, consume the reversed inner copy, emit its row in
forward inner order, and reach the restore label with the input copy rebuilt.
-/
def nestedLoop_innerEmitPhase {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (outer : Γ)
    (input remainingOuters : List Γ) (output : List Δ) :
    EvalsToInTime (step (nestedLoop body))
      { initialCfg (nestedLoop body) [] with
        label := some (.inner outer)
        buffer₁ := some outer
        work₁ := remainingOuters
        work₂ := input.reverse
        output := output }
      (some { initialCfg (nestedLoop body) input with
        label := some .restore
        buffer₁ := some outer
        output := nestedLoopRow body outer input ++ output
        work₁ := remainingOuters })
      (input.length + (nestedLoopRow body outer input).length + 1) := by
  refine ⟨⟨input.length + (nestedLoopRow body outer input).length + 1, ?_⟩,
    le_rfl⟩
  convert nestedLoop_innerEmitPhase_eval body (some outer) none outer []
    remainingOuters input.reverse output using 1 <;>
      simp [nestedInnerCfg, nestedRestoreCfg, initialCfg]

/-- The public inner/emit witness stores its exact advertised count. -/
private theorem nestedLoop_innerEmitPhase_steps {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (outer : Γ)
    (input remainingOuters : List Γ) (output : List Δ) :
    (nestedLoop_innerEmitPhase body outer input remainingOuters output).steps =
      input.length + (nestedLoopRow body outer input).length + 1 := by
  rfl

/-- Iteration equation for restoring the consumed inner copy to
{lit}`work₂`. -/
private theorem nestedLoop_restorePhase_eval {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (buffer₁ buffer₂ : Option Γ)
    (input work₁ work₂ : List Γ) (output : List Δ) :
    (flip Option.bind (step (nestedLoop body)))^[input.length + 1]
      (some (nestedRestoreCfg body buffer₁ buffer₂
        input work₁ work₂ output)) =
      some (nestedOuterCfg body buffer₁ none work₁
        (input.reverse ++ work₂) output) := by
  induction input generalizing buffer₂ work₂ with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show (symbol :: rest).length + 1 = rest.length + 1 + 1 by simp,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step (nestedLoop body)))^[rest.length + 1]
          (some (nestedRestoreCfg body buffer₁ (some symbol)
            rest work₁ (symbol :: work₂) output)) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some symbol) (symbol :: work₂)

/-- Restore one full inner input copy in exact linear time. -/
def nestedLoop_restorePhase {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (outer : Γ)
    (input remainingOuters : List Γ) (output : List Δ) :
    EvalsToInTime (step (nestedLoop body))
      { initialCfg (nestedLoop body) input with
        label := some .restore
        buffer₁ := some outer
        work₁ := remainingOuters
        output := output }
      (some { initialCfg (nestedLoop body) [] with
        label := some .outer
        buffer₁ := some outer
        work₁ := remainingOuters
        work₂ := input.reverse
        output := output })
      (input.length + 1) := by
  refine ⟨⟨input.length + 1, ?_⟩, le_rfl⟩
  convert nestedLoop_restorePhase_eval body (some outer) none
    input remainingOuters [] output using 1 <;>
      simp [nestedRestoreCfg, nestedOuterCfg, initialCfg]

/-- The public restore witness stores its exact advertised count. -/
private theorem nestedLoop_restorePhase_steps {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (outer : Γ)
    (input remainingOuters : List Γ) (output : List Δ) :
    (nestedLoop_restorePhase body outer input remainingOuters output).steps =
      input.length + 1 := by
  rfl

/-- Iteration equation for all remaining outer rows. -/
private theorem nestedLoop_outerPhase_eval {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (buffer₁ : Option Γ)
    (input work₁ : List Γ) (output : List Δ) :
    (flip Option.bind (step (nestedLoop body)))^[
        work₁.length * (2 * input.length + 3) +
          (work₁.reverse.flatMap fun outer => nestedLoopRow body outer input).length + 1]
      (some (nestedOuterCfg body buffer₁ none
        work₁ input.reverse output)) =
      some (nestedClearCfg body none none input.reverse
        ((work₁.reverse.flatMap fun outer => nestedLoopRow body outer input) ++
          output)) := by
  induction work₁ generalizing buffer₁ output with
  | nil =>
      simp [nestedOuterCfg, nestedClearCfg, nestedLoop, initialCfg]
      rfl
  | cons outer rest ih =>
      let remainingSteps :=
        rest.length * (2 * input.length + 3) +
          (rest.reverse.flatMap fun symbol =>
            nestedLoopRow body symbol input).length + 1
      let rowSteps :=
        (input.length + 1) +
          (input.length + (nestedLoopRow body outer input).length + 1) + 1
      have hsteps :
          (outer :: rest).length * (2 * input.length + 3) +
              ((outer :: rest).reverse.flatMap fun symbol =>
                nestedLoopRow body symbol input).length + 1 =
            remainingSteps + rowSteps := by
        simp [remainingSteps, rowSteps, List.reverse_cons,
          List.flatMap_append, Nat.succ_mul]
        omega
      rw [hsteps, Function.iterate_add_apply]
      change
        (flip Option.bind (step (nestedLoop body)))^[remainingSteps]
          ((flip Option.bind (step (nestedLoop body)))^[rowSteps]
            (some (nestedOuterCfg body buffer₁ none
              (outer :: rest) input.reverse output))) = _
      let hinner := nestedLoop_innerEmitPhase body outer input rest output
      let hrestore := nestedLoop_restorePhase body outer input rest
        (nestedLoopRow body outer input ++ output)
      let hpop : EvalsToInTime (step (nestedLoop body))
          (nestedOuterCfg body buffer₁ none
            (outer :: rest) input.reverse output)
          (some { initialCfg (nestedLoop body) [] with
            label := some (.inner outer)
            buffer₁ := some outer
            work₁ := rest
            work₂ := input.reverse
            output := output }) 1 := by
        refine ⟨⟨1, ?_⟩, le_rfl⟩
        rfl
      let hpopInner := EvalsToInTime.trans (step (nestedLoop body))
        1 (input.length + (nestedLoopRow body outer input).length + 1)
        (nestedOuterCfg body buffer₁ none
          (outer :: rest) input.reverse output)
        { initialCfg (nestedLoop body) [] with
          label := some (.inner outer)
          buffer₁ := some outer
          work₁ := rest
          work₂ := input.reverse
          output := output }
        (some { initialCfg (nestedLoop body) input with
          label := some .restore
          buffer₁ := some outer
          output := nestedLoopRow body outer input ++ output
          work₁ := rest }) hpop hinner
      let hrow := EvalsToInTime.trans (step (nestedLoop body))
        ((input.length + (nestedLoopRow body outer input).length + 1) + 1)
        (input.length + 1)
        (nestedOuterCfg body buffer₁ none
          (outer :: rest) input.reverse output)
        { initialCfg (nestedLoop body) input with
          label := some .restore
          buffer₁ := some outer
          output := nestedLoopRow body outer input ++ output
          work₁ := rest }
        (some (nestedOuterCfg body (some outer) none rest input.reverse
          (nestedLoopRow body outer input ++ output))) hpopInner hrestore
      have hrowSteps : hrow.steps = rowSteps := by
        simp only [hrow, hpopInner, evalsToInTime_trans_steps]
        rfl
      have hrowEval := hrow.evals_in_steps
      rw [hrowSteps] at hrowEval
      have hrowEval' :
          (flip Option.bind (step (nestedLoop body)))^[rowSteps]
            (some (nestedOuterCfg body buffer₁ none
              (outer :: rest) input.reverse output)) =
            some (nestedOuterCfg body (some outer) none rest input.reverse
              (nestedLoopRow body outer input ++ output)) := hrowEval
      rw [hrowEval', ih (some outer)
        (nestedLoopRow body outer input ++ output)]
      congr 2
      simp [List.reverse_cons, List.flatMap_append, List.append_assoc]

/-- Consume all outer rows, preserving the retained reversed inner copy for a
separate final clear phase. -/
def nestedLoop_outerPhase {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (input : List Γ) :
    EvalsToInTime (step (nestedLoop body))
      { initialCfg (nestedLoop body) [] with
        label := some .outer
        work₁ := input.reverse
        work₂ := input.reverse }
      (some { initialCfg (nestedLoop body) [] with
        label := some .clear
        work₂ := input.reverse
        output := nestedLoopOutput body input })
      (2 * input.length ^ 2 + 3 * input.length +
        (nestedLoopOutput body input).length + 1) := by
  let runSteps :=
    input.reverse.length * (2 * input.length + 3) +
      (input.reverse.reverse.flatMap fun outer =>
        nestedLoopRow body outer input).length + 1
  have heval := nestedLoop_outerPhase_eval body none input input.reverse []
  have hsteps : runSteps =
      2 * input.length ^ 2 + 3 * input.length +
        (nestedLoopOutput body input).length + 1 := by
    simp [runSteps, nestedLoopOutput, nestedLoopRow]
    ring
  refine ⟨⟨2 * input.length ^ 2 + 3 * input.length +
    (nestedLoopOutput body input).length + 1, ?_⟩, le_rfl⟩
  rw [← hsteps]
  simpa [runSteps, nestedOuterCfg, nestedClearCfg, initialCfg,
    nestedLoopOutput, nestedLoopRow] using heval

/-- The public outer-phase witness stores its exact advertised count. -/
private theorem nestedLoop_outerPhase_steps {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (input : List Γ) :
    (nestedLoop_outerPhase body input).steps =
      2 * input.length ^ 2 + 3 * input.length +
        (nestedLoopOutput body input).length + 1 := by
  rfl

/-- Iteration equation for discarding the retained inner copy. -/
private theorem nestedLoop_clearPhase_eval {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (buffer₂ : Option Γ)
    (work₂ : List Γ) (output : List Δ) :
    (flip Option.bind (step (nestedLoop body)))^[work₂.length + 1]
      (some (nestedClearCfg body none buffer₂ work₂ output)) =
      some { haltCfg (nestedLoop body) output with label := some .halt } := by
  induction work₂ generalizing buffer₂ with
  | nil =>
      simp [nestedClearCfg, nestedLoop, haltCfg, initialCfg]
      rfl
  | cons symbol rest ih =>
      rw [show (symbol :: rest).length + 1 = rest.length + 1 + 1 by simp,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step (nestedLoop body)))^[rest.length + 1]
          (some (nestedClearCfg body none (some symbol) rest output)) = _
      exact ih (some symbol)

/-- Clear the retained inner copy in exactly one pop per symbol plus one
empty-stack transition. -/
def nestedLoop_clearPhase {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (input : List Γ) (output : List Δ) :
    EvalsToInTime (step (nestedLoop body))
      { initialCfg (nestedLoop body) [] with
        label := some .clear
        work₂ := input.reverse
        output := output }
      (some { haltCfg (nestedLoop body) output with label := some .halt })
      (input.length + 1) := by
  refine ⟨⟨input.length + 1, ?_⟩, le_rfl⟩
  convert nestedLoop_clearPhase_eval body none input.reverse output using 1
  · simp [nestedClearCfg, initialCfg]

/-- The public clear-phase witness stores its exact advertised count. -/
private theorem nestedLoop_clearPhase_steps {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (input : List Γ) (output : List Δ) :
    (nestedLoop_clearPhase body input output).steps = input.length + 1 := by
  rfl

/-- The final nested-loop halt clears control state in one exact step. -/
def nestedLoop_haltStep {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (output : List Δ) :
    EvalsToInTime (step (nestedLoop body))
      { haltCfg (nestedLoop body) output with label := some .halt }
      (some (haltCfg (nestedLoop body) output)) 1 := by
  refine ⟨⟨1, ?_⟩, le_rfl⟩
  rfl

/-- The public nested-loop halt witness stores one exact step. -/
private theorem nestedLoop_haltStep_steps {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (output : List Δ) :
    (nestedLoop_haltStep body output).steps = 1 := by
  rfl

/-- Canonical exact independent-semantics run of the verified nested loop. -/
def nestedLoop_run {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (input : List Γ) :
    EvalsToInTime (step (nestedLoop body))
      (initialCfg (nestedLoop body) input)
      (some (haltCfg (nestedLoop body) (nestedLoopOutput body input)))
      (nestedLoopSteps body input) := by
  let outerSteps :=
    2 * input.length ^ 2 + 3 * input.length +
      (nestedLoopOutput body input).length + 1
  let hcopyOuter := EvalsToInTime.trans (step (nestedLoop body))
    (input.length + 1) outerSteps
    (initialCfg (nestedLoop body) input)
    { initialCfg (nestedLoop body) [] with
      label := some .outer
      work₁ := input.reverse
      work₂ := input.reverse }
    (some { initialCfg (nestedLoop body) [] with
      label := some .clear
      work₂ := input.reverse
      output := nestedLoopOutput body input })
    (nestedLoop_copyPhase body input) (nestedLoop_outerPhase body input)
  let hthroughClear := EvalsToInTime.trans (step (nestedLoop body))
    (outerSteps + (input.length + 1)) (input.length + 1)
    (initialCfg (nestedLoop body) input)
    { initialCfg (nestedLoop body) [] with
      label := some .clear
      work₂ := input.reverse
      output := nestedLoopOutput body input }
    (some { haltCfg (nestedLoop body) (nestedLoopOutput body input) with
      label := some .halt }) hcopyOuter
    (nestedLoop_clearPhase body input (nestedLoopOutput body input))
  let hfull := EvalsToInTime.trans (step (nestedLoop body))
    ((input.length + 1) + (outerSteps + (input.length + 1))) 1
    (initialCfg (nestedLoop body) input)
    { haltCfg (nestedLoop body) (nestedLoopOutput body input) with
      label := some .halt }
    (some (haltCfg (nestedLoop body) (nestedLoopOutput body input)))
    hthroughClear (nestedLoop_haltStep body (nestedLoopOutput body input))
  have hfullSteps : hfull.steps = nestedLoopSteps body input := by
    simp only [hfull, hthroughClear, hcopyOuter,
      evalsToInTime_trans_steps, nestedLoop_haltStep_steps,
      nestedLoop_clearPhase_steps, nestedLoop_outerPhase_steps,
      nestedLoop_copyPhase_steps]
    simp [nestedLoopSteps]
    omega
  refine ⟨⟨nestedLoopSteps body input, ?_⟩, le_rfl⟩
  rw [← hfullSteps]
  exact hfull.evals_in_steps

/-- The canonical nested-loop run stores the exact quadratic-plus-output
formula, rather than only a smaller witness under that bound. -/
theorem nestedLoop_run_steps {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (input : List Γ) :
    (nestedLoop_run body input).steps = nestedLoopSteps body input := by
  rfl

/-- Independent nested-loop execution computes the exact row-major pair
flat-map output at the advertised exact step count. -/
theorem nestedLoop_builderOutputs {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) :
    BuilderOutputs (nestedLoop body) (nestedLoopOutput body)
      (nestedLoopSteps body) := by
  intro input
  exact ⟨nestedLoop_run body input⟩

/-- Canonical compiled nested-loop execution obtained by exact transport of
the independent run. -/
def nestedLoop_compiledRun {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (input : List Γ) :
    _root_.Turing.TM2OutputsInTime (compile (nestedLoop body)) input
      (some (nestedLoopOutput body input)) (nestedLoopSteps body input) := by
  let run := compile_evalsToInTime (nestedLoop body)
    (nestedLoop_run body input)
  refine ⟨⟨nestedLoopSteps body input, ?_⟩, le_rfl⟩
  have runSteps : run.steps = nestedLoopSteps body input := by
    simp only [run, compile_evalsToInTime_steps, nestedLoop_run_steps]
  have runEval := run.evals_in_steps
  rw [runSteps] at runEval
  convert runEval using 1
  · simp
  · simp only [Option.map_some, Option.some.injEq]
    exact (encodeCfg_haltCfg (nestedLoop body)
      (nestedLoopOutput body input)).symm

/-- Compilation preserves the canonical nested-loop run's exact step count. -/
theorem nestedLoop_compiledRun_steps {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (input : List Γ) :
    (nestedLoop_compiledRun body input).steps = nestedLoopSteps body input := by
  rfl

/-- The compiled nested-loop TM2 computes the exact row-major pair output at
the same exact step count as the independent semantics. -/
theorem nestedLoop_outputs {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) :
    Outputs (nestedLoop body) (nestedLoopOutput body)
      (nestedLoopSteps body) := by
  intro input
  exact ⟨nestedLoop_compiledRun body input⟩

/-- Finite sum of all ordered-pair local costs.

As for {name}`boundedLoopTotalCost`, the sum is intentionally looser than a
maximum but avoids any inhabitedness assumption or empty-alphabet case split.
-/
private def nestedLoopTotalCost {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) : Nat :=
  ∑ pair : Γ × Γ, body.cost pair

/-- Every ordered-pair local cost is bounded by the finite total cost. -/
private theorem nestedLoop_cost_le_total {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (pair : Γ × Γ) :
    body.cost pair ≤ nestedLoopTotalCost body := by
  classical
  unfold nestedLoopTotalCost
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ pair)

/-- One emitted row has length at most input length times the finite pair-cost
sum. -/
private theorem nestedLoop_row_length_le {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (outer : Γ) (input : List Γ) :
    (nestedLoopRow body outer input).length ≤
      input.length * nestedLoopTotalCost body := by
  rw [nestedLoopRow, List.length_flatMap]
  calc
    (input.map fun inner => (body.emit (outer, inner)).length).sum ≤
        (input.map fun _ => nestedLoopTotalCost body).sum :=
      List.sum_le_sum fun inner _ =>
        le_trans (body.emit_length_le_cost (outer, inner))
          (nestedLoop_cost_le_total body (outer, inner))
    _ = input.length * nestedLoopTotalCost body := by simp

/-- The row-major nested output has length at most {lit}`n²` times the finite
pair-cost sum. -/
private theorem nestedLoop_output_length_le {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) (input : List Γ) :
    (nestedLoopOutput body input).length ≤
      input.length ^ 2 * nestedLoopTotalCost body := by
  rw [nestedLoopOutput, List.length_flatMap]
  calc
    (input.map fun outer => (nestedLoopRow body outer input).length).sum ≤
        (input.map fun _ => input.length * nestedLoopTotalCost body).sum :=
      List.sum_le_sum fun outer _ => nestedLoop_row_length_le body outer input
    _ = input.length * (input.length * nestedLoopTotalCost body) := by simp
    _ = input.length ^ 2 * nestedLoopTotalCost body := by ring

/-- Quadratic polynomial envelope for the exact nested-loop step function.

The leading coefficient uses the finite sum of pair-local costs.  This is
looser than a maximum-based envelope but remains uniform and empty-alphabet
friendly while proving the same quadratic complexity class.
-/
noncomputable def nestedLoop_polyBound {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) : PolyBound (nestedLoopSteps body) where
  polynomial :=
    ((2 + nestedLoopTotalCost body : Nat) : Polynomial Nat) *
      Polynomial.X ^ 2 + 5 * Polynomial.X + 4
  bound input := by
    have hout := nestedLoop_output_length_le body input
    simp only [nestedLoopSteps, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_natCast,
      Polynomial.eval_ofNat]
    calc
      2 * input.length ^ 2 + 5 * input.length +
            (nestedLoopOutput body input).length + 4 ≤
          2 * input.length ^ 2 + 5 * input.length +
            input.length ^ 2 * nestedLoopTotalCost body + 4 := by omega
      _ = (2 + nestedLoopTotalCost body) * input.length ^ 2 +
          5 * input.length + 4 := by ring

/-- Machine-level polynomial-time computability of the row-major ordered-pair
flat-map, witnessed by the compiled verified nested loop. -/
noncomputable def nestedLoop_computableInPolyTime {Γ Δ : Type} [Fintype Γ]
    (body : LoopBody (Γ × Γ) Δ) :
    _root_.Turing.TM2ComputableInPolyTime id id (nestedLoopOutput body) :=
  ComputableInPolyTime (nestedLoop body) (nestedLoopOutput body)
    (nestedLoopSteps body) (nestedLoop_outputs body) (nestedLoop_polyBound body)

end CLRS.Chapter34.Turing.PolyBuilder
