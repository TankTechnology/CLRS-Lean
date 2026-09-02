import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder

namespace CLRS.Chapter34.Turing.PolyBuilder

#check ScanLabel
#check scanCopy
#check scanCopySteps
#check scanCopy_movePhase
#check scanCopy_emitPushPhase
#check scanCopy_haltStep
#check scanCopy_run
#check scanCopy_run_steps
#check scanCopy_builderOutputs
#check scanCopy_compiledRun
#check scanCopy_compiledRun_steps
#check scanCopy_outputs
#check scanCopy_polyBound
#check scanCopy_computableInPolyTime

example : scanCopySteps ([] : List Bool) = 3 := rfl

example : Nonempty (_root_.StateTransition.EvalsToInTime
    (step (scanCopy (Γ := Bool)))
    (initialCfg (scanCopy (Γ := Bool)) [])
    (some (haltCfg (scanCopy (Γ := Bool)) [])) 3) :=
  scanCopy_builderOutputs []

example : Nonempty (_root_.Turing.TM2OutputsInTime
    (compile (scanCopy (Γ := Bool))) [] (some []) 3) :=
  scanCopy_outputs []

example : Nonempty (_root_.StateTransition.EvalsToInTime
    (step (scanCopy (Γ := Bool)))
    (initialCfg (scanCopy (Γ := Bool)) [true])
    (some (haltCfg (scanCopy (Γ := Bool)) [true])) 6) :=
  scanCopy_builderOutputs [true]

example : Nonempty (_root_.Turing.TM2OutputsInTime
    (compile (scanCopy (Γ := Bool))) [true] (some [true]) 6) :=
  scanCopy_outputs [true]

example : Nonempty (_root_.StateTransition.EvalsToInTime
    (step (scanCopy (Γ := Bool)))
    (initialCfg (scanCopy (Γ := Bool)) [true, false, true])
    (some (haltCfg (scanCopy (Γ := Bool)) [true, false, true])) 12) :=
  scanCopy_builderOutputs [true, false, true]

example : Nonempty (_root_.Turing.TM2OutputsInTime
    (compile (scanCopy (Γ := Bool))) [true, false, true]
    (some [true, false, true]) 12) :=
  scanCopy_outputs [true, false, true]

example :
    (scanCopy_movePhase (Γ := Bool) [true, false, true]).steps = 4 := rfl

example :
    (scanCopy_emitPushPhase (Γ := Bool) [true, false, true]).steps = 7 := rfl

example :
    (scanCopy_haltStep (Γ := Bool) [true, false, true]).steps = 1 := rfl

example :
    (scanCopy_run (Γ := Bool) [true, false, true]).steps = 12 :=
  scanCopy_run_steps [true, false, true]

example :
    (scanCopy_compiledRun (Γ := Bool) [true, false, true]).steps = 12 :=
  scanCopy_compiledRun_steps [true, false, true]

example : Nonempty (_root_.StateTransition.EvalsToInTime
    (step (scanCopy (Γ := Empty)))
    (initialCfg (scanCopy (Γ := Empty)) [])
    (some (haltCfg (scanCopy (Γ := Empty)) [])) 3) :=
  scanCopy_builderOutputs []

example : Nonempty (_root_.Turing.TM2OutputsInTime
    (compile (scanCopy (Γ := Empty))) [] (some []) 3) :=
  scanCopy_outputs []

noncomputable example {Γ : Type} [Fintype Γ] :
    _root_.Turing.TM2ComputableInPolyTime id id (@id (List Γ)) :=
  scanCopy_computableInPolyTime

#check LoopBody
#check BoundedLoopLabel
#check boundedLoop
#check boundedLoopSteps
#check boundedLoop_movePhase
#check boundedLoop_emitPhase
#check boundedLoop_haltStep
#check boundedLoop_run
#check boundedLoop_run_steps
#check boundedLoop_builderOutputs
#check boundedLoop_compiledRun
#check boundedLoop_compiledRun_steps
#check boundedLoop_outputs
#check boundedLoop_polyBound
#check boundedLoop_computableInPolyTime

/-- A nonuniform Boolean loop body: false emits nothing, while true emits two
Boolean symbols. -/
def boolLoopBody : LoopBody Bool Bool where
  emit
    | false => []
    | true => [false, true]
  cost
    | false => 0
    | true => 2
  emit_length_le_cost symbol := by cases symbol <;> decide

/-- A one-symbol-emission Boolean loop body, covering the intermediate cursor
case separately from the zero- and two-symbol body above. -/
def boolSingletonBody : LoopBody Bool Bool where
  emit symbol := [symbol]
  cost _ := 1
  emit_length_le_cost _ := by simp

/-- The unique loop body over an empty input alphabet. -/
def emptyInputLoopBody : LoopBody Empty Bool where
  emit symbol := nomatch symbol
  cost symbol := nomatch symbol
  emit_length_le_cost symbol := nomatch symbol

/-- A loop body into the empty output alphabet necessarily emits nothing. -/
def emptyOutputLoopBody : LoopBody Bool Empty where
  emit _ := []
  cost _ := 0
  emit_length_le_cost _ := by simp

/-- A body whose output type has no finiteness or inhabitance assumptions. -/
def unconstrainedOutputLoopBody {Δ : Type} : LoopBody Bool Δ where
  emit _ := []
  cost _ := 0
  emit_length_le_cost _ := by simp

noncomputable example {Δ : Type} : Program Bool Δ :=
  boundedLoop (unconstrainedOutputLoopBody (Δ := Δ))

/-- The label type itself is independent of any finite-input dictionary. -/
example {Γ Δ : Type} (body : LoopBody Γ Δ) : Type :=
  BoundedLoopLabel body

/-- Two nonempty, unequal chunks make both cross-chunk and within-chunk order
observable. -/
def orderedChunkLoopBody : LoopBody Bool Nat where
  emit
    | false => [10, 11]
    | true => [20, 21, 22]
  cost
    | false => 2
    | true => 3
  emit_length_le_cost symbol := by cases symbol <;> decide

example : boundedLoopSteps boolLoopBody [] = 3 := rfl

example :
    (boundedLoop_run boolLoopBody []).steps = 3 :=
  boundedLoop_run_steps boolLoopBody []

example :
    (boundedLoop_run boolLoopBody [true, false, true]).steps = 13 :=
  boundedLoop_run_steps boolLoopBody [true, false, true]

example : Nonempty (_root_.StateTransition.EvalsToInTime
    (step (boundedLoop boolLoopBody))
    (initialCfg (boundedLoop boolLoopBody) [true, false, true])
    (some (haltCfg (boundedLoop boolLoopBody) [false, true, false, true])) 13) :=
  boundedLoop_builderOutputs boolLoopBody [true, false, true]

example : Nonempty (_root_.Turing.TM2OutputsInTime
    (compile (boundedLoop boolLoopBody)) [true, false, true]
    (some [false, true, false, true]) 13) :=
  boundedLoop_outputs boolLoopBody [true, false, true]

example : Nonempty (_root_.StateTransition.EvalsToInTime
    (step (boundedLoop orderedChunkLoopBody))
    (initialCfg (boundedLoop orderedChunkLoopBody) [false, true])
    (some (haltCfg (boundedLoop orderedChunkLoopBody)
      [10, 11, 20, 21, 22])) 12) :=
  boundedLoop_builderOutputs orderedChunkLoopBody [false, true]

example : Nonempty (_root_.Turing.TM2OutputsInTime
    (compile (boundedLoop orderedChunkLoopBody)) [false, true]
    (some ([10, 11, 20, 21, 22] : List Nat)) 12) :=
  boundedLoop_outputs orderedChunkLoopBody [false, true]

example :
    (boundedLoop_compiledRun boolLoopBody [true, false, true]).steps = 13 :=
  boundedLoop_compiledRun_steps boolLoopBody [true, false, true]

example : Nonempty (_root_.StateTransition.EvalsToInTime
    (step (boundedLoop boolSingletonBody))
    (initialCfg (boundedLoop boolSingletonBody) [false])
    (some (haltCfg (boundedLoop boolSingletonBody) [false])) 6) :=
  boundedLoop_builderOutputs boolSingletonBody [false]

example : Nonempty (_root_.StateTransition.EvalsToInTime
    (step (boundedLoop emptyInputLoopBody))
    (initialCfg (boundedLoop emptyInputLoopBody) [])
    (some (haltCfg (boundedLoop emptyInputLoopBody) [])) 3) :=
  boundedLoop_builderOutputs emptyInputLoopBody []

example : Nonempty (_root_.Turing.TM2OutputsInTime
    (compile (boundedLoop emptyInputLoopBody)) [] (some []) 3) :=
  boundedLoop_outputs emptyInputLoopBody []

example : Nonempty (_root_.StateTransition.EvalsToInTime
    (step (boundedLoop emptyOutputLoopBody))
    (initialCfg (boundedLoop emptyOutputLoopBody) [true, false])
    (some (haltCfg (boundedLoop emptyOutputLoopBody) [])) 7) :=
  boundedLoop_builderOutputs emptyOutputLoopBody [true, false]

noncomputable example :
    _root_.Turing.TM2ComputableInPolyTime id id
      (List.flatMap boolLoopBody.emit) :=
  boundedLoop_computableInPolyTime boolLoopBody

#check nestedLoop
#check NestedLoopLabel
#check NestedLoopCursor
#check nestedLoopOutput
#check nestedLoopRow
#check nestedLoopSteps
#check nestedLoop_copyPhase
#check nestedLoop_innerEmitPhase
#check nestedLoop_restorePhase
#check nestedLoop_outerPhase
#check nestedLoop_clearPhase
#check nestedLoop_haltStep
#check nestedLoop_run
#check nestedLoop_run_steps
#check nestedLoop_builderOutputs
#check nestedLoop_compiledRun
#check nestedLoop_compiledRun_steps
#check nestedLoop_outputs
#check nestedLoop_polyBound
#check nestedLoop_computableInPolyTime

/-- All four Boolean pairs emit distinct nonempty chunks of different lengths,
making row-major pair orientation and chunk order directly observable. -/
def pairChunkLoopBody : LoopBody (Bool × Bool) Nat where
  emit
    | (false, false) => [0]
    | (false, true) => [1, 2]
    | (true, false) => [3, 4, 5]
    | (true, true) => [6, 7, 8, 9]
  cost
    | (false, false) => 1
    | (false, true) => 2
    | (true, false) => 3
    | (true, true) => 4
  emit_length_le_cost pair := by rcases pair with ⟨a, b⟩; cases a <;> cases b <;> decide

/-- A nested body with empty output chunks. -/
def emptyPairChunkLoopBody : LoopBody (Bool × Bool) Bool where
  emit _ := []
  cost _ := 0
  emit_length_le_cost _ := by simp

/-- The unique nested body over an empty input alphabet. -/
def emptyNestedInputBody : LoopBody (Empty × Empty) Bool where
  emit pair := nomatch pair.1
  cost pair := nomatch pair.1
  emit_length_le_cost pair := nomatch pair.1

/-- A nested body into an empty output alphabet. -/
def emptyNestedOutputBody : LoopBody (Bool × Bool) Empty where
  emit _ := []
  cost _ := 0
  emit_length_le_cost _ := by simp

/-- An arbitrary output type need not be finite or inhabited. -/
def unconstrainedNestedOutputBody {Δ : Type} : LoopBody (Bool × Bool) Δ where
  emit _ := []
  cost _ := 0
  emit_length_le_cost _ := by simp

noncomputable example {Δ : Type} : Program Bool Δ :=
  nestedLoop (unconstrainedNestedOutputBody (Δ := Δ))

example {Γ Δ : Type} (body : LoopBody (Γ × Γ) Δ) : Type :=
  NestedLoopLabel body

example : nestedLoopSteps pairChunkLoopBody [] = 4 := rfl

example : (nestedLoop_run pairChunkLoopBody []).steps = 4 :=
  nestedLoop_run_steps pairChunkLoopBody []

example : Nonempty (_root_.StateTransition.EvalsToInTime
    (step (nestedLoop emptyPairChunkLoopBody))
    (initialCfg (nestedLoop emptyPairChunkLoopBody) [false])
    (some (haltCfg (nestedLoop emptyPairChunkLoopBody) [])) 11) :=
  nestedLoop_builderOutputs emptyPairChunkLoopBody [false]

example : Nonempty (_root_.StateTransition.EvalsToInTime
    (step (nestedLoop pairChunkLoopBody))
    (initialCfg (nestedLoop pairChunkLoopBody) [false, true])
    (some (haltCfg (nestedLoop pairChunkLoopBody)
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])) 32) :=
  nestedLoop_builderOutputs pairChunkLoopBody [false, true]

example : (nestedLoop_run pairChunkLoopBody [false, true]).steps = 32 :=
  nestedLoop_run_steps pairChunkLoopBody [false, true]

example : Nonempty (_root_.Turing.TM2OutputsInTime
    (compile (nestedLoop pairChunkLoopBody)) [false, true]
    (some ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : List Nat)) 32) :=
  nestedLoop_outputs pairChunkLoopBody [false, true]

example : (nestedLoop_compiledRun pairChunkLoopBody [false, true]).steps = 32 :=
  nestedLoop_compiledRun_steps pairChunkLoopBody [false, true]

example : Nonempty (_root_.StateTransition.EvalsToInTime
    (step (nestedLoop emptyNestedInputBody))
    (initialCfg (nestedLoop emptyNestedInputBody) [])
    (some (haltCfg (nestedLoop emptyNestedInputBody) [])) 4) :=
  nestedLoop_builderOutputs emptyNestedInputBody []

example : Nonempty (_root_.Turing.TM2OutputsInTime
    (compile (nestedLoop emptyNestedInputBody)) [] (some []) 4) :=
  nestedLoop_outputs emptyNestedInputBody []

example : Nonempty (_root_.StateTransition.EvalsToInTime
    (step (nestedLoop emptyNestedOutputBody))
    (initialCfg (nestedLoop emptyNestedOutputBody) [false, true])
    (some (haltCfg (nestedLoop emptyNestedOutputBody) [])) 22) :=
  nestedLoop_builderOutputs emptyNestedOutputBody [false, true]

noncomputable example :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Bool =>
        input.flatMap fun outer =>
          input.flatMap fun inner => pairChunkLoopBody.emit (outer, inner)) :=
  nestedLoop_computableInPolyTime pairChunkLoopBody

end CLRS.Chapter34.Turing.PolyBuilder
