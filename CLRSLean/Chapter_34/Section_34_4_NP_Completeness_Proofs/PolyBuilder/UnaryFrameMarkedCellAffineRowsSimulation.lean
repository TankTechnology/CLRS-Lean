import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedCellAffineRowsCore
import Mathlib.Tactic

/-!
# Affine copies of one marked-cell row: exact simulation
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private theorem unit_replicate_cons_append (count : Nat)
    (tail : List Unit) :
    List.replicate count () ++ () :: tail =
      List.replicate (count + 1) () ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons ()) ih

private theorem symbol_replicate_cons_append (symbol : UnaryFrameSym)
    (count : Nat) (tail : List UnaryFrameSym) :
    List.replicate count symbol ++ symbol :: tail =
      symbol :: (List.replicate count symbol ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons symbol) ih

private def markedCellAffineRowsLastBuffer
    (initial : Option UnaryFrameSym) (symbols : List UnaryFrameSym) :
    Option UnaryFrameSym :=
  symbols.foldl (fun _ symbol => some symbol) initial

private def markedCellAffineRowsCfg
    (label : UnaryFrameMarkedCellAffineRowsLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (temp stepCount rowCount : List Unit) :
    BuilderCfg unaryFrameMarkedCellAffineRowsRevProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := temp
  counter₂ := stepCount
  counter₃ := rowCount

private theorem markedCellAffineRows_loadStep_eval
    (amount : Nat) (tail output work₁ work₂ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (temp stepCount rowCount : List Unit) :
    (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
        2 * amount + 1]
      (some (markedCellAffineRowsCfg .loadStep buffer₁ buffer₂ test
        (List.replicate amount .tick ++ .separator :: tail)
        output work₁ work₂ temp stepCount rowCount)) =
      some (markedCellAffineRowsCfg .loadCount (some .separator) buffer₂ test
        tail output work₁ work₂ temp
        (List.replicate amount () ++ stepCount) rowCount) := by
  induction amount generalizing buffer₁ stepCount with
  | zero => rfl
  | succ amount ih =>
      rw [show 2 * (amount + 1) + 1 = (2 * amount + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
            2 * amount + 1]
          (some (markedCellAffineRowsCfg .loadStep (some .tick) buffer₂ test
            (List.replicate amount .tick ++ .separator :: tail)
            output work₁ work₂ temp (() :: stepCount) rowCount)) = _
      simpa [List.replicate_succ, List.append_assoc,
        unit_replicate_cons_append] using
        ih (buffer₁ := some .tick) (stepCount := () :: stepCount)

private theorem markedCellAffineRows_loadCount_eval
    (count : Nat) (tail output work₁ work₂ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (temp stepCount rowCount : List Unit) :
    (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
        2 * count + 1]
      (some (markedCellAffineRowsCfg .loadCount buffer₁ buffer₂ test
        (List.replicate count .tick ++ .separator :: tail)
        output work₁ work₂ temp stepCount rowCount)) =
      some (markedCellAffineRowsCfg .beginRows (some .separator) buffer₂ test
        tail output work₁ work₂ temp stepCount
        (List.replicate count () ++ rowCount)) := by
  induction count generalizing buffer₁ rowCount with
  | zero => rfl
  | succ count ih =>
      rw [show 2 * (count + 1) + 1 = (2 * count + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
            2 * count + 1]
          (some (markedCellAffineRowsCfg .loadCount (some .tick) buffer₂ test
            (List.replicate count .tick ++ .separator :: tail)
            output work₁ work₂ temp stepCount (() :: rowCount))) = _
      simpa [List.replicate_succ, List.append_assoc,
        unit_replicate_cons_append] using
        ih (buffer₁ := some .tick) (rowCount := () :: rowCount)

private theorem markedCellAffineRows_copyFree_eval
    (symbols tail output work₁ work₂ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (temp stepCount rowCount : List Unit)
    (hfree : ∀ symbol ∈ symbols,
      symbol ≠ UnaryFrameSym.frameEnd) :
    (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
        3 * symbols.length]
      (some (markedCellAffineRowsCfg .copyFirst buffer₁ buffer₂ test
        (symbols ++ tail) output work₁ work₂ temp stepCount rowCount)) =
      some (markedCellAffineRowsCfg .copyFirst
        (markedCellAffineRowsLastBuffer buffer₁ symbols) buffer₂ test tail
        (symbols.reverse ++ output) (symbols.reverse ++ work₁) work₂
        temp stepCount rowCount) := by
  induction symbols generalizing buffer₁ output work₁ with
  | nil => rfl
  | cons symbol rest ih =>
      have hsymbol := hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      rw [show 3 * (symbol :: rest).length =
          3 * rest.length + 1 + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      simp only [flip, Option.bind_some]
      rw [show step unaryFrameMarkedCellAffineRowsRevProgram
          (markedCellAffineRowsCfg .copyFirst buffer₁ buffer₂ test
            (symbol :: rest ++ tail) output work₁ work₂ temp stepCount
              rowCount) =
          some (markedCellAffineRowsCfg (.emitFirst symbol) (some symbol)
            buffer₂ test (rest ++ tail) output work₁ work₂ temp stepCount
              rowCount) by
        simp [step, unaryFrameMarkedCellAffineRowsRevProgram,
          markedCellAffineRowsCfg, stepOp, hsymbol]]
      simp only [Option.bind_some]
      change
        (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
            3 * rest.length]
          (some (markedCellAffineRowsCfg .copyFirst (some symbol) buffer₂ test
            (rest ++ tail) (symbol :: output) (symbol :: work₁) work₂
            temp stepCount rowCount)) = _
      simpa [markedCellAffineRowsLastBuffer, List.reverse_cons,
        List.append_assoc] using
        ih (buffer₁ := some symbol) (output := symbol :: output)
          (work₁ := symbol :: work₁) hrest

private theorem markedCellAffineRows_encodeUnaryFrame_free
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, _, hblock⟩
  simp [encodeUnaryFrameBlock] at hblock
  rcases hblock with ⟨_, rfl⟩ | rfl <;> decide

private def markedCellAffineRows_firstCopySteps : List Nat → Nat
  | [] => 1
  | value :: rest =>
      3 * (value + 1) + 1 + markedCellAffineRows_firstCopySteps rest

private theorem markedCellAffineRows_firstCopySteps_eq
    (cells : List Nat) :
    markedCellAffineRows_firstCopySteps cells =
      3 * (encodeUnaryFrame cells).length + cells.length + 1 := by
  induction cells with
  | nil => rfl
  | cons value rest ih =>
      simp [markedCellAffineRows_firstCopySteps, encodeUnaryFrame,
        encodeUnaryFrameBlock, ih]
      omega

private theorem markedCellAffineRows_copyCells_eval
    (cells : List Nat) (output work₁ work₂ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (temp stepCount rowCount : List Unit) :
    (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
        markedCellAffineRows_firstCopySteps cells]
      (some (markedCellAffineRowsCfg .copyFirst buffer₁ buffer₂ test
        (cells.flatMap fun value =>
          encodeUnaryFrame [value] ++ [.frameEnd])
        output work₁ work₂ temp stepCount rowCount)) =
      some (markedCellAffineRowsCfg .finishFirst none buffer₂ test []
        ((encodeUnaryFrame cells).reverse ++ output)
        ((encodeUnaryFrame cells).reverse ++ work₁) work₂
        temp stepCount rowCount) := by
  induction cells generalizing buffer₁ output work₁ with
  | nil => rfl
  | cons value rest ih =>
      let block := encodeUnaryFrame [value]
      have hfree := markedCellAffineRows_encodeUnaryFrame_free [value]
      have hcopy := markedCellAffineRows_copyFree_eval block
        (.frameEnd :: (rest.flatMap fun item =>
          encodeUnaryFrame [item] ++ [.frameEnd]))
        output work₁ work₂ buffer₁ buffer₂ test temp stepCount rowCount hfree
      let afterBlock := markedCellAffineRowsCfg .copyFirst
        (markedCellAffineRowsLastBuffer buffer₁ block) buffer₂ test
        (.frameEnd :: (rest.flatMap fun item =>
          encodeUnaryFrame [item] ++ [.frameEnd]))
        (block.reverse ++ output) (block.reverse ++ work₁) work₂
        temp stepCount rowCount
      let afterMarker := markedCellAffineRowsCfg .copyFirst
        (some .frameEnd) buffer₂ test
        (rest.flatMap fun item => encodeUnaryFrame [item] ++ [.frameEnd])
        (block.reverse ++ output) (block.reverse ++ work₁) work₂
        temp stepCount rowCount
      let hcopy' : EvalsToInTime
          (step unaryFrameMarkedCellAffineRowsRevProgram)
          (markedCellAffineRowsCfg .copyFirst buffer₁ buffer₂ test
            (block ++ .frameEnd :: (rest.flatMap fun item =>
              encodeUnaryFrame [item] ++ [.frameEnd]))
            output work₁ work₂ temp stepCount rowCount)
          (some afterBlock) (3 * block.length) :=
        ⟨⟨3 * block.length, by simpa [afterBlock] using hcopy⟩, le_rfl⟩
      let hmarker : EvalsToInTime
          (step unaryFrameMarkedCellAffineRowsRevProgram)
          afterBlock (some afterMarker) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have hrest := ih (buffer₁ := some UnaryFrameSym.frameEnd)
        (output := block.reverse ++ output)
        (work₁ := block.reverse ++ work₁)
      let full := EvalsToInTime.trans
        (step unaryFrameMarkedCellAffineRowsRevProgram)
        (3 * block.length) 1 _ afterBlock _ hcopy' hmarker
      let full' := EvalsToInTime.trans
        (step unaryFrameMarkedCellAffineRowsRevProgram)
        _ _ _ afterMarker _ full
        ⟨⟨markedCellAffineRows_firstCopySteps rest, hrest⟩, le_rfl⟩
      have hblockLength : block.length = value + 1 := by
        simp [block, encodeUnaryFrame, encodeUnaryFrameBlock]
      have hsteps : full'.steps =
          markedCellAffineRows_firstCopySteps (value :: rest) := by
        dsimp [full', full, EvalsToInTime.trans, EvalsTo.trans]
        change markedCellAffineRows_firstCopySteps rest +
            (1 + 3 * block.length) =
          markedCellAffineRows_firstCopySteps (value :: rest)
        rw [hblockLength]
        simp only [markedCellAffineRows_firstCopySteps]
        omega
      rw [← hsteps]
      convert full'.evals_in_steps using 1 <;>
        simp [markedCellAffineRows_firstCopySteps, block,
          encodeUnaryFrame, encodeUnaryFrameBlock,
          List.reverse_append, List.append_assoc]

private theorem markedCellAffineRows_transfer_eval
    (source target input output : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (temp stepCount rowCount : List Unit) :
    (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
        source.length + 1]
      (some (markedCellAffineRowsCfg .transfer buffer₁ buffer₂ test
        input output source target temp stepCount rowCount)) =
      some (markedCellAffineRowsCfg .scan none buffer₂ test input output []
        (source.reverse ++ target) temp stepCount rowCount) := by
  induction source generalizing buffer₁ target with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show (symbol :: rest).length + 1 =
          (rest.length + 1) + 1 by simp,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
            rest.length + 1]
          (some (markedCellAffineRowsCfg .transfer (some symbol) buffer₂ test
            input output rest (symbol :: target) temp stepCount rowCount)) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih (buffer₁ := some symbol) (target := symbol :: target)

private theorem markedCellAffineRows_scanTicks_eval
    (count : Nat) (tail input output work₁ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (stepCount rowCount : List Unit) :
    (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
        3 * count]
      (some (markedCellAffineRowsCfg .scan buffer₁ buffer₂ test input output
        work₁ (List.replicate count .tick ++ tail) [] stepCount rowCount)) =
      some (markedCellAffineRowsCfg .scan buffer₁
        (if count = 0 then buffer₂ else some .tick) test input
        (List.replicate count .tick ++ output)
        (List.replicate count .tick ++ work₁) tail [] stepCount rowCount) := by
  induction count generalizing buffer₂ output work₁ with
  | zero => rfl
  | succ count ih =>
      rw [show 3 * (count + 1) = 3 * count + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
            3 * count]
          (some (markedCellAffineRowsCfg .scan buffer₁ (some .tick) test input
            (.tick :: output) (.tick :: work₁)
            (List.replicate count .tick ++ tail) [] stepCount rowCount)) = _
      simpa [List.replicate_succ, List.append_assoc,
        symbol_replicate_cons_append] using
        ih (buffer₂ := some UnaryFrameSym.tick)
          (output := UnaryFrameSym.tick :: output)
          (work₁ := UnaryFrameSym.tick :: work₁)

private theorem markedCellAffineRows_addTicks_eval
    (amount : Nat) (input output work₁ work₂ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (temp rowCount : List Unit) :
    (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
        4 * amount + 1]
      (some (markedCellAffineRowsCfg .addStep buffer₁ buffer₂ test input
        output work₁ work₂ temp (List.replicate amount ()) rowCount)) =
      some (markedCellAffineRowsCfg .restoreStep buffer₁ buffer₂ false input
        (List.replicate amount .tick ++ output)
        (List.replicate amount .tick ++ work₁) work₂
        (List.replicate amount () ++ temp) [] rowCount) := by
  induction amount generalizing output work₁ temp test with
  | zero => rfl
  | succ amount ih =>
      rw [show 4 * (amount + 1) + 1 =
          (4 * amount + 1) + 1 + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
            4 * amount + 1]
          (some (markedCellAffineRowsCfg .addStep buffer₁ buffer₂ true input
            (.tick :: output) (.tick :: work₁) work₂ (() :: temp)
            (List.replicate amount ()) rowCount)) = _
      simpa [List.replicate_succ, List.append_assoc,
        unit_replicate_cons_append, symbol_replicate_cons_append] using
        ih (output := UnaryFrameSym.tick :: output)
          (work₁ := UnaryFrameSym.tick :: work₁) (temp := () :: temp)
          (test := true)

private theorem markedCellAffineRows_restoreStep_eval
    (amount : Nat) (input output work₁ work₂ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (stepTail rowCount : List Unit) :
    (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
        2 * amount + 1]
      (some (markedCellAffineRowsCfg .restoreStep buffer₁ buffer₂ test
        input output work₁ work₂ (List.replicate amount ()) stepTail rowCount)) =
      some (markedCellAffineRowsCfg .emitSeparator buffer₁ buffer₂ false
        input output work₁ work₂ []
        (List.replicate amount () ++ stepTail) rowCount) := by
  induction amount generalizing stepTail test with
  | zero => rfl
  | succ amount ih =>
      rw [show 2 * (amount + 1) + 1 =
          (2 * amount + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
            2 * amount + 1]
          (some (markedCellAffineRowsCfg .restoreStep buffer₁ buffer₂ true
            input output work₁ work₂ (List.replicate amount ())
            (() :: stepTail)
            rowCount)) = _
      simpa [List.replicate_succ, unit_replicate_cons_append,
        List.append_assoc] using ih (stepTail := () :: stepTail) (test := true)

private theorem markedCellAffineRows_addSeparator_eval
    (amount : Nat) (input output work₁ work₂ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (rowCount : List Unit) :
    (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
        6 * amount + 4]
      (some (markedCellAffineRowsCfg .addStep buffer₁ buffer₂ test input
        output work₁ work₂ [] (List.replicate amount ()) rowCount)) =
      some (markedCellAffineRowsCfg .scan buffer₁ buffer₂ false input
        (.separator :: List.replicate amount .tick ++ output)
        (.separator :: List.replicate amount .tick ++ work₁) work₂ []
        (List.replicate amount ()) rowCount) := by
  have hadd := markedCellAffineRows_addTicks_eval amount input output work₁ work₂
    buffer₁ buffer₂ test [] rowCount
  have hrestore := markedCellAffineRows_restoreStep_eval amount input
    (List.replicate amount .tick ++ output)
    (List.replicate amount .tick ++ work₁) work₂ buffer₁ buffer₂ false
    [] rowCount
  let h₁ : EvalsToInTime (step unaryFrameMarkedCellAffineRowsRevProgram)
      (markedCellAffineRowsCfg .addStep buffer₁ buffer₂ test input output work₁
        work₂ [] (List.replicate amount ()) rowCount)
      (some (markedCellAffineRowsCfg .restoreStep buffer₁ buffer₂ false input
        (List.replicate amount .tick ++ output)
        (List.replicate amount .tick ++ work₁) work₂
        (List.replicate amount ()) [] rowCount))
      (4 * amount + 1) :=
    ⟨⟨4 * amount + 1, by simpa using hadd⟩, le_rfl⟩
  let h₂ : EvalsToInTime (step unaryFrameMarkedCellAffineRowsRevProgram)
      (markedCellAffineRowsCfg .restoreStep buffer₁ buffer₂ false input
        (List.replicate amount .tick ++ output)
        (List.replicate amount .tick ++ work₁) work₂
        (List.replicate amount ()) [] rowCount)
      (some (markedCellAffineRowsCfg .emitSeparator buffer₁ buffer₂ false input
        (List.replicate amount .tick ++ output)
        (List.replicate amount .tick ++ work₁) work₂ []
        (List.replicate amount ()) rowCount))
      (2 * amount + 1) :=
    ⟨⟨2 * amount + 1, by simpa using hrestore⟩, le_rfl⟩
  let h₃ : EvalsToInTime (step unaryFrameMarkedCellAffineRowsRevProgram)
      (markedCellAffineRowsCfg .emitSeparator buffer₁ buffer₂ false input
        (List.replicate amount .tick ++ output)
        (List.replicate amount .tick ++ work₁) work₂ []
        (List.replicate amount ()) rowCount)
      (some (markedCellAffineRowsCfg .scan buffer₁ buffer₂ false input
        (.separator :: List.replicate amount .tick ++ output)
        (.separator :: List.replicate amount .tick ++ work₁) work₂ []
        (List.replicate amount ()) rowCount)) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  let h₁₂ := EvalsToInTime.trans
    (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ _ _ h₁ h₂
  let full := EvalsToInTime.trans
    (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ _ _ h₁₂ h₃
  have hsteps : full.steps = 6 * amount + 4 := by
    dsimp [full, h₁₂, h₁, h₂, h₃, EvalsToInTime.trans, EvalsTo.trans]
    omega
  rw [← hsteps]
  exact full.evals_in_steps

private def markedCellAffineRows_scanCellsSteps (amount : Nat) : List Nat → Nat
  | [] => 1
  | value :: rest =>
      3 * value + 1 + (6 * amount + 4) +
        markedCellAffineRows_scanCellsSteps amount rest

private def markedCellAffineRows_scanCellsLastTest
    (initial : Bool) : List Nat → Bool
  | [] => initial
  | _ :: _ => false

private theorem markedCellAffineRows_shiftedCons_reverse
    (amount value : Nat) (rest : List Nat) (tail : List UnaryFrameSym) :
    (encodeUnaryFrame ((value :: rest).map fun item => item + amount)).reverse ++
        tail =
      (encodeUnaryFrame (rest.map fun item => item + amount)).reverse ++
        (.separator :: List.replicate amount .tick ++
          (List.replicate value .tick ++ tail)) := by
  simp only [List.map_cons]
  rw [show value + amount = amount + value by omega]
  simp only [encodeUnaryFrame, List.flatMap_cons,
    encodeUnaryFrameBlock, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.reverse_replicate]
  rw [List.replicate_add]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

private theorem markedCellAffineRows_scanCellsLastTest_false
    (cells : List Nat) :
    markedCellAffineRows_scanCellsLastTest false cells = false := by
  cases cells <;> rfl

private theorem markedCellAffineRows_scanCells_eval
    (amount : Nat) (cells : List Nat)
    (input output work₁ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (rowCount : List Unit) :
    (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
        markedCellAffineRows_scanCellsSteps amount cells]
      (some (markedCellAffineRowsCfg .scan buffer₁ buffer₂ test input output
        work₁ (encodeUnaryFrame cells) [] (List.replicate amount ()) rowCount)) =
      some (markedCellAffineRowsCfg .finishRow buffer₁ none
        (markedCellAffineRows_scanCellsLastTest test cells) input
        ((encodeUnaryFrame (cells.map fun value => value + amount)).reverse ++
          output)
        ((encodeUnaryFrame (cells.map fun value => value + amount)).reverse ++
          work₁)
        [] [] (List.replicate amount ()) rowCount) := by
  induction cells generalizing buffer₂ test output work₁ with
  | nil => rfl
  | cons value rest ih =>
      let tailStream := encodeUnaryFrame rest
      have hticks := markedCellAffineRows_scanTicks_eval value
        (.separator :: tailStream) input output work₁ buffer₁ buffer₂ test
        (List.replicate amount ()) rowCount
      let afterTicks := markedCellAffineRowsCfg .scan buffer₁
        (if value = 0 then buffer₂ else some .tick) test input
        (List.replicate value .tick ++ output)
        (List.replicate value .tick ++ work₁)
        (.separator :: tailStream) [] (List.replicate amount ()) rowCount
      let beforeAdd := markedCellAffineRowsCfg .addStep buffer₁ (some .separator)
        test input (List.replicate value .tick ++ output)
        (List.replicate value .tick ++ work₁) tailStream []
        (List.replicate amount ()) rowCount
      let hseparator : EvalsToInTime
          (step unaryFrameMarkedCellAffineRowsRevProgram) afterTicks
          (some beforeAdd) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have hadd := markedCellAffineRows_addSeparator_eval amount input
        (List.replicate value .tick ++ output)
        (List.replicate value .tick ++ work₁) tailStream buffer₁
        (some UnaryFrameSym.separator) test rowCount
      let afterAdd := markedCellAffineRowsCfg .scan buffer₁
        (some .separator) false input
        (.separator :: List.replicate amount .tick ++
          (List.replicate value .tick ++ output))
        (.separator :: List.replicate amount .tick ++
          (List.replicate value .tick ++ work₁))
        tailStream [] (List.replicate amount ()) rowCount
      let hticks' : EvalsToInTime
          (step unaryFrameMarkedCellAffineRowsRevProgram)
          (markedCellAffineRowsCfg .scan buffer₁ buffer₂ test input output
            work₁ (List.replicate value .tick ++ .separator :: tailStream) []
            (List.replicate amount ()) rowCount)
          (some afterTicks) (3 * value) :=
        ⟨⟨3 * value, by simpa [afterTicks] using hticks⟩, le_rfl⟩
      let hadd' : EvalsToInTime
          (step unaryFrameMarkedCellAffineRowsRevProgram) beforeAdd
          (some afterAdd) (6 * amount + 4) :=
        ⟨⟨6 * amount + 4, by
            change
              (flip Option.bind
                (step unaryFrameMarkedCellAffineRowsRevProgram))^[
                  6 * amount + 4] (some beforeAdd) = some afterAdd
            simpa only [beforeAdd, afterAdd] using hadd⟩,
          le_rfl⟩
      have hrest := ih (buffer₂ := some UnaryFrameSym.separator)
        (test := false)
        (output := .separator :: List.replicate amount .tick ++
          (List.replicate value .tick ++ output))
        (work₁ := .separator :: List.replicate amount .tick ++
          (List.replicate value .tick ++ work₁))
      let h₁ := EvalsToInTime.trans
        (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ afterTicks _
          hticks' hseparator
      let h₂ := EvalsToInTime.trans
        (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ beforeAdd _ h₁ hadd'
      let full := EvalsToInTime.trans
        (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ afterAdd _ h₂
          ⟨⟨markedCellAffineRows_scanCellsSteps amount rest, hrest⟩, le_rfl⟩
      have hsteps : full.steps =
          markedCellAffineRows_scanCellsSteps amount (value :: rest) := by
        dsimp [full, h₂, h₁, hticks', hseparator, hadd',
          EvalsToInTime.trans, EvalsTo.trans]
        simp [markedCellAffineRows_scanCellsSteps]
        omega
      rw [← hsteps]
      convert full.evals_in_steps using 1
      · simp [tailStream, encodeUnaryFrame, encodeUnaryFrameBlock]
      · rw [markedCellAffineRows_scanCellsLastTest_false]
        simp only [markedCellAffineRows_shiftedCons_reverse,
          markedCellAffineRows_scanCellsLastTest]

private def markedCellAffineRows_successorRows
    (amount : Nat) : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | remaining + 1, cells =>
      let next := cells.map fun value => value + amount
      next :: markedCellAffineRows_successorRows amount remaining next

private def markedCellAffineRows_finalCells
    (amount : Nat) : Nat → List Nat → List Nat
  | 0, cells => cells
  | remaining + 1, cells =>
      markedCellAffineRows_finalCells amount remaining
        (cells.map fun value => value + amount)

private def markedCellAffineRows_rowsSteps
    (amount : Nat) : Nat → List Nat → Nat
  | 0, _ => 1
  | remaining + 1, cells =>
      1 + ((encodeUnaryFrame cells).length + 1) +
        markedCellAffineRows_scanCellsSteps amount cells + 1 +
        markedCellAffineRows_rowsSteps amount remaining
          (cells.map fun value => value + amount)

private theorem markedCellAffineRows_rows_eval
    (amount remaining : Nat) (cells : List Nat)
    (input output : List UnaryFrameSym) (test : Bool) :
    (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
        markedCellAffineRows_rowsSteps amount remaining cells]
      (some (markedCellAffineRowsCfg .nextRow none none test input output
        (encodeUnaryFrame cells).reverse [] [] (List.replicate amount ())
        (List.replicate remaining ()))) =
      some (markedCellAffineRowsCfg .clearInput none none false input
        (((markedCellAffineRows_successorRows amount remaining cells).flatMap
          fun row => encodeUnaryFrame row ++ [.frameEnd]).reverse ++ output)
        (encodeUnaryFrame
          (markedCellAffineRows_finalCells amount remaining cells)).reverse
        [] [] (List.replicate amount ()) []) := by
  induction remaining generalizing cells output test with
  | zero => rfl
  | succ remaining ih =>
      let nextCells := cells.map fun value => value + amount
      let source := (encodeUnaryFrame cells).reverse
      let afterDec := markedCellAffineRowsCfg .transfer none none true input output
        source [] [] (List.replicate amount ()) (List.replicate remaining ())
      let beforeScan := markedCellAffineRowsCfg .scan none none true input output []
        (encodeUnaryFrame cells) [] (List.replicate amount ())
        (List.replicate remaining ())
      let hdec : EvalsToInTime
          (step unaryFrameMarkedCellAffineRowsRevProgram)
          (markedCellAffineRowsCfg .nextRow none none test input output source [] []
            (List.replicate amount ()) (List.replicate (remaining + 1) ()))
          (some afterDec) 1 := ⟨⟨1, by
            simp only [Function.iterate_one, flip, Option.bind_some]
            rfl⟩, le_rfl⟩
      have htransferRaw := markedCellAffineRows_transfer_eval source [] input output
        none none true [] (List.replicate amount ())
        (List.replicate remaining ())
      let htransfer : EvalsToInTime
          (step unaryFrameMarkedCellAffineRowsRevProgram) afterDec
          (some beforeScan) ((encodeUnaryFrame cells).length + 1) :=
        ⟨⟨(encodeUnaryFrame cells).length + 1, by
            change
              (flip Option.bind
                (step unaryFrameMarkedCellAffineRowsRevProgram))^[
                  (encodeUnaryFrame cells).length + 1]
                (some afterDec) = some beforeScan
            simpa [afterDec, beforeScan, source] using htransferRaw⟩,
          le_rfl⟩
      have hscanRaw := markedCellAffineRows_scanCells_eval amount cells input
        output [] none none true (List.replicate remaining ())
      let afterScan := markedCellAffineRowsCfg .finishRow none none
        (markedCellAffineRows_scanCellsLastTest true cells) input
        ((encodeUnaryFrame nextCells).reverse ++ output)
        (encodeUnaryFrame nextCells).reverse [] []
        (List.replicate amount ()) (List.replicate remaining ())
      let hscan : EvalsToInTime
          (step unaryFrameMarkedCellAffineRowsRevProgram) beforeScan
          (some afterScan) (markedCellAffineRows_scanCellsSteps amount cells) :=
        ⟨⟨markedCellAffineRows_scanCellsSteps amount cells, by
            change
              (flip Option.bind
                (step unaryFrameMarkedCellAffineRowsRevProgram))^[
                  markedCellAffineRows_scanCellsSteps amount cells]
                (some beforeScan) = some afterScan
            simpa [beforeScan, afterScan, nextCells] using hscanRaw⟩,
          le_rfl⟩
      let beforeRest := markedCellAffineRowsCfg .nextRow none none
        (markedCellAffineRows_scanCellsLastTest true cells) input
        (.frameEnd :: (encodeUnaryFrame nextCells).reverse ++ output)
        (encodeUnaryFrame nextCells).reverse [] []
        (List.replicate amount ()) (List.replicate remaining ())
      let hfinish : EvalsToInTime
          (step unaryFrameMarkedCellAffineRowsRevProgram) afterScan
          (some beforeRest) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have hrest := ih (cells := nextCells)
        (output := .frameEnd :: (encodeUnaryFrame nextCells).reverse ++ output)
        (test := markedCellAffineRows_scanCellsLastTest true cells)
      let h₁ := EvalsToInTime.trans
        (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ afterDec _ hdec htransfer
      let h₂ := EvalsToInTime.trans
        (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ beforeScan _ h₁ hscan
      let h₃ := EvalsToInTime.trans
        (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ afterScan _ h₂ hfinish
      let full := EvalsToInTime.trans
        (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ beforeRest _ h₃
          ⟨⟨markedCellAffineRows_rowsSteps amount remaining nextCells, hrest⟩,
            le_rfl⟩
      have hsteps : full.steps =
          markedCellAffineRows_rowsSteps amount (remaining + 1) cells := by
        dsimp [full, h₃, h₂, h₁, hdec, htransfer, hscan, hfinish,
          EvalsToInTime.trans, EvalsTo.trans, nextCells]
        simp [markedCellAffineRows_rowsSteps, source]
        omega
      rw [← hsteps]
      convert full.evals_in_steps using 1 <;>
        simp [source, nextCells, afterDec, beforeScan, afterScan, beforeRest,
          markedCellAffineRows_successorRows, markedCellAffineRows_finalCells,
          List.reverse_append, List.append_assoc]

private theorem markedCellAffineRows_clearInput_eval
    (symbols output work₁ work₂ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (temp stepCount rowCount : List Unit) :
    (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
        symbols.length + 1]
      (some (markedCellAffineRowsCfg .clearInput buffer₁ buffer₂ test symbols
        output work₁ work₂ temp stepCount rowCount)) =
      some (markedCellAffineRowsCfg .clearWork₁ none buffer₂ test [] output
        work₁ work₂ temp stepCount rowCount) := by
  induction symbols generalizing buffer₁ with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show (symbol :: rest).length + 1 = rest.length + 1 + 1 by simp,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
            rest.length + 1]
          (some (markedCellAffineRowsCfg .clearInput (some symbol) buffer₂ test
            rest output work₁ work₂ temp stepCount rowCount)) = _
      exact ih (buffer₁ := some symbol)

private theorem markedCellAffineRows_clearWork₁_eval
    (symbols input output work₂ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (temp stepCount rowCount : List Unit) :
    (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
        symbols.length + 1]
      (some (markedCellAffineRowsCfg .clearWork₁ buffer₁ buffer₂ test input
        output symbols work₂ temp stepCount rowCount)) =
      some (markedCellAffineRowsCfg .clearWork₂ none buffer₂ test input output
        [] work₂ temp stepCount rowCount) := by
  induction symbols generalizing buffer₁ with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show (symbol :: rest).length + 1 = rest.length + 1 + 1 by simp,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
            rest.length + 1]
          (some (markedCellAffineRowsCfg .clearWork₁ (some symbol) buffer₂ test
            input output rest work₂ temp stepCount rowCount)) = _
      exact ih (buffer₁ := some symbol)

private theorem markedCellAffineRows_clearStep_eval
    (amount : Nat) (input output work₁ work₂ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (temp rowCount : List Unit) :
    (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
        amount + 1]
      (some (markedCellAffineRowsCfg .clearStep buffer₁ buffer₂ test input
        output work₁ work₂ temp (List.replicate amount ()) rowCount)) =
      some (markedCellAffineRowsCfg .clearCount buffer₁ buffer₂ false input
        output work₁ work₂ temp [] rowCount) := by
  induction amount generalizing test with
  | zero => rfl
  | succ amount ih =>
      rw [show amount + 1 + 1 = (amount + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
            amount + 1]
          (some (markedCellAffineRowsCfg .clearStep buffer₁ buffer₂ true input
            output work₁ work₂ temp (List.replicate amount ()) rowCount)) = _
      exact ih (test := true)

private def markedCellAffineRows_cleanupSteps
    (input work₁ : List UnaryFrameSym) (amount : Nat) : Nat :=
  input.length + work₁.length + amount + 7

private theorem markedCellAffineRows_cleanup_eval
    (input output work₁ : List UnaryFrameSym) (amount : Nat)
    (buffer₁ : Option UnaryFrameSym) :
    (flip Option.bind (step unaryFrameMarkedCellAffineRowsRevProgram))^[
        markedCellAffineRows_cleanupSteps input work₁ amount]
      (some (markedCellAffineRowsCfg .clearInput buffer₁ none false input output
        work₁ [] [] (List.replicate amount ()) [])) =
      some (haltCfg unaryFrameMarkedCellAffineRowsRevProgram output) := by
  let c₁ := markedCellAffineRowsCfg .clearWork₁ none none false [] output
    work₁ [] [] (List.replicate amount ()) []
  let c₂ := markedCellAffineRowsCfg .clearWork₂ none none false [] output
    [] [] [] (List.replicate amount ()) []
  let c₃ := markedCellAffineRowsCfg .clearTemp none none false [] output
    [] [] [] (List.replicate amount ()) []
  let c₄ := markedCellAffineRowsCfg .clearStep none none false [] output
    [] [] [] (List.replicate amount ()) []
  let c₅ := markedCellAffineRowsCfg .clearCount none none false [] output
    [] [] [] [] []
  let c₆ := markedCellAffineRowsCfg .halt none none false [] output [] [] [] [] []
  let h₁ : EvalsToInTime (step unaryFrameMarkedCellAffineRowsRevProgram)
      (markedCellAffineRowsCfg .clearInput buffer₁ none false input output work₁ []
        [] (List.replicate amount ()) []) (some c₁) (input.length + 1) :=
    ⟨⟨input.length + 1, by
        simpa [c₁] using markedCellAffineRows_clearInput_eval input output work₁ []
          buffer₁ none false [] (List.replicate amount ()) []⟩, le_rfl⟩
  let h₂ : EvalsToInTime (step unaryFrameMarkedCellAffineRowsRevProgram)
      c₁ (some c₂) (work₁.length + 1) :=
    ⟨⟨work₁.length + 1, by
        simpa [c₁, c₂] using markedCellAffineRows_clearWork₁_eval work₁ []
          output [] none none false [] (List.replicate amount ()) []⟩, le_rfl⟩
  let h₃ : EvalsToInTime (step unaryFrameMarkedCellAffineRowsRevProgram)
      c₂ (some c₃) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let h₄ : EvalsToInTime (step unaryFrameMarkedCellAffineRowsRevProgram)
      c₃ (some c₄) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let h₅ : EvalsToInTime (step unaryFrameMarkedCellAffineRowsRevProgram)
      c₄ (some c₅) (amount + 1) :=
    ⟨⟨amount + 1, by
        simpa [c₄, c₅] using
          (markedCellAffineRows_clearStep_eval amount [] output [] [] none none
            false [] [])⟩, le_rfl⟩
  let h₆ : EvalsToInTime (step unaryFrameMarkedCellAffineRowsRevProgram)
      c₅ (some c₆) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let h₇ : EvalsToInTime (step unaryFrameMarkedCellAffineRowsRevProgram)
      c₆ (some (haltCfg unaryFrameMarkedCellAffineRowsRevProgram output)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁₂ := EvalsToInTime.trans
    (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ c₁ _ h₁ h₂
  let h₁₂₃ := EvalsToInTime.trans
    (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ c₂ _ h₁₂ h₃
  let h₁₂₃₄ := EvalsToInTime.trans
    (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ c₃ _ h₁₂₃ h₄
  let h₁₂₃₄₅ := EvalsToInTime.trans
    (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ c₄ _ h₁₂₃₄ h₅
  let h₁₂₃₄₅₆ := EvalsToInTime.trans
    (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ c₅ _ h₁₂₃₄₅ h₆
  let full := EvalsToInTime.trans
    (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ c₆ _ h₁₂₃₄₅₆ h₇
  have hsteps : full.steps =
      markedCellAffineRows_cleanupSteps input work₁ amount := by
    dsimp [full, h₁₂₃₄₅₆, h₁₂₃₄₅, h₁₂₃₄, h₁₂₃,
      h₁₂, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
      EvalsToInTime.trans, EvalsTo.trans, markedCellAffineRows_cleanupSteps]
    omega
  rw [← hsteps]
  exact full.evals_in_steps

/-- Rows emitted by the controller, before identifying the recursion with
`List.ofFn` in the public specification. -/
def unaryFrameMarkedCellAffineGeneratedRows
    (amount count : Nat) (cells : List Nat) : List (List Nat) :=
  match count with
  | 0 => []
  | remaining + 1 =>
      cells :: markedCellAffineRows_successorRows amount remaining cells

private def unaryFrameMarkedCellAffineGeneratedStream
    (family : UnaryFrameMarkedCellAffineRows) : List UnaryFrameSym :=
  (unaryFrameMarkedCellAffineGeneratedRows family.step family.count
    family.cells).flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]

/-- Exact step count of the reverse-output controller. -/
def unaryFrameMarkedCellAffineRowsRevSteps
    (family : UnaryFrameMarkedCellAffineRows) : Nat :=
  let payload := family.cells.flatMap fun value =>
    encodeUnaryFrame [value] ++ [.frameEnd]
  2 * family.step + 1 + (2 * family.count + 1) +
    match family.count with
    | 0 =>
        1 + markedCellAffineRows_cleanupSteps payload [] family.step
    | remaining + 1 =>
        1 + markedCellAffineRows_firstCopySteps family.cells + 1 +
          markedCellAffineRows_rowsSteps family.step remaining family.cells +
          markedCellAffineRows_cleanupSteps []
            (encodeUnaryFrame
              (markedCellAffineRows_finalCells family.step remaining
                family.cells)).reverse
            family.step

/-- Exact clean-halt execution against the controller's recursive row
description. -/
def unaryFrameMarkedCellAffineRowsRev_runGenerated
    (family : UnaryFrameMarkedCellAffineRows) :
    EvalsToInTime (step unaryFrameMarkedCellAffineRowsRevProgram)
      (initialCfg unaryFrameMarkedCellAffineRowsRevProgram
        (encodeUnaryFrameMarkedCellAffineRows family))
      (some (haltCfg unaryFrameMarkedCellAffineRowsRevProgram
        (unaryFrameMarkedCellAffineGeneratedStream family).reverse))
      (unaryFrameMarkedCellAffineRowsRevSteps family) := by
  let payload := family.cells.flatMap fun value =>
    encodeUnaryFrame [value] ++ [.frameEnd]
  let countInput := encodeUnaryFrameBlock family.count ++ payload
  let afterStep := markedCellAffineRowsCfg .loadCount (some .separator) none false
    countInput [] [] [] [] (List.replicate family.step ()) []
  have hstepRaw := markedCellAffineRows_loadStep_eval family.step countInput [] [] []
    none none false [] [] []
  let hstep : EvalsToInTime (step unaryFrameMarkedCellAffineRowsRevProgram)
      (initialCfg unaryFrameMarkedCellAffineRowsRevProgram
        (encodeUnaryFrameMarkedCellAffineRows family))
      (some afterStep) (2 * family.step + 1) :=
    ⟨⟨2 * family.step + 1, by
        change
          (flip Option.bind
            (step unaryFrameMarkedCellAffineRowsRevProgram))^[
              2 * family.step + 1]
            (some (initialCfg unaryFrameMarkedCellAffineRowsRevProgram
              (encodeUnaryFrameMarkedCellAffineRows family))) = some afterStep
        simpa [initialCfg, afterStep, countInput, payload,
          encodeUnaryFrameMarkedCellAffineRows, encodeUnaryFrame,
          encodeUnaryFrameBlock, unaryFrameMarkedCellAffineRowsRevProgram,
          markedCellAffineRowsCfg, List.append_assoc] using hstepRaw⟩, le_rfl⟩
  let afterParams := markedCellAffineRowsCfg .beginRows (some .separator) none
    false payload [] [] [] [] (List.replicate family.step ())
    (List.replicate family.count ())
  have hcountRaw := markedCellAffineRows_loadCount_eval family.count payload [] [] []
    (some UnaryFrameSym.separator) none false [] (List.replicate family.step ()) []
  let hcount : EvalsToInTime (step unaryFrameMarkedCellAffineRowsRevProgram)
      afterStep (some afterParams) (2 * family.count + 1) :=
    ⟨⟨2 * family.count + 1, by
        change
          (flip Option.bind
            (step unaryFrameMarkedCellAffineRowsRevProgram))^[
              2 * family.count + 1] (some afterStep) = some afterParams
        simpa [afterStep, afterParams, countInput, encodeUnaryFrameBlock] using
          hcountRaw⟩, le_rfl⟩
  let hparams := EvalsToInTime.trans
    (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ afterStep _ hstep hcount
  cases hcountValue : family.count with
  | zero =>
      let beforeCleanup := markedCellAffineRowsCfg .clearInput
        (some .separator) none false payload [] [] [] []
        (List.replicate family.step ()) []
      let hbegin : EvalsToInTime
          (step unaryFrameMarkedCellAffineRowsRevProgram) afterParams
          (some beforeCleanup) 1 := ⟨⟨1, by
            simp only [Function.iterate_one, flip]
            simp [afterParams, beforeCleanup, hcountValue]
            rfl⟩, le_rfl⟩
      have hcleanupRaw := markedCellAffineRows_cleanup_eval payload [] []
        family.step (some UnaryFrameSym.separator)
      let hcleanup : EvalsToInTime
          (step unaryFrameMarkedCellAffineRowsRevProgram) beforeCleanup
          (some (haltCfg unaryFrameMarkedCellAffineRowsRevProgram []))
          (markedCellAffineRows_cleanupSteps payload [] family.step) :=
        ⟨⟨markedCellAffineRows_cleanupSteps payload [] family.step, by
            change
              (flip Option.bind
                (step unaryFrameMarkedCellAffineRowsRevProgram))^[
                  markedCellAffineRows_cleanupSteps payload [] family.step]
                (some beforeCleanup) =
                  some (haltCfg unaryFrameMarkedCellAffineRowsRevProgram [])
            simpa [beforeCleanup] using hcleanupRaw⟩, le_rfl⟩
      let hbody := EvalsToInTime.trans
        (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ beforeCleanup _
          hbegin hcleanup
      let full := EvalsToInTime.trans
        (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ afterParams _
          hparams hbody
      convert full using 1 <;>
        simp [unaryFrameMarkedCellAffineRowsRevSteps,
          unaryFrameMarkedCellAffineGeneratedStream,
          unaryFrameMarkedCellAffineGeneratedRows, hcountValue, payload] <;>
        omega
  | succ remaining =>
      let afterBegin := markedCellAffineRowsCfg .copyFirst
        (some .separator) none true payload [] [] [] []
        (List.replicate family.step ()) (List.replicate remaining ())
      let hbegin : EvalsToInTime
          (step unaryFrameMarkedCellAffineRowsRevProgram) afterParams
          (some afterBegin) 1 := ⟨⟨1, by
            simp only [Function.iterate_one, flip]
            simp [afterParams, afterBegin, hcountValue, List.replicate_succ]
            rfl⟩,
          le_rfl⟩
      have hcopyRaw := markedCellAffineRows_copyCells_eval family.cells [] [] []
        (some UnaryFrameSym.separator) none true []
        (List.replicate family.step ()) (List.replicate remaining ())
      let afterCopy := markedCellAffineRowsCfg .finishFirst none none true []
        (encodeUnaryFrame family.cells).reverse
        (encodeUnaryFrame family.cells).reverse [] []
        (List.replicate family.step ()) (List.replicate remaining ())
      let hcopy : EvalsToInTime
          (step unaryFrameMarkedCellAffineRowsRevProgram) afterBegin
          (some afterCopy) (markedCellAffineRows_firstCopySteps family.cells) :=
        ⟨⟨markedCellAffineRows_firstCopySteps family.cells, by
            change
              (flip Option.bind
                (step unaryFrameMarkedCellAffineRowsRevProgram))^[
                  markedCellAffineRows_firstCopySteps family.cells]
                (some afterBegin) = some afterCopy
            simpa [afterBegin, afterCopy, payload] using hcopyRaw⟩, le_rfl⟩
      let beforeRows := markedCellAffineRowsCfg .nextRow none none true []
        (.frameEnd :: (encodeUnaryFrame family.cells).reverse)
        (encodeUnaryFrame family.cells).reverse [] []
        (List.replicate family.step ()) (List.replicate remaining ())
      let hfinish : EvalsToInTime
          (step unaryFrameMarkedCellAffineRowsRevProgram) afterCopy
          (some beforeRows) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have hrowsRaw := markedCellAffineRows_rows_eval family.step remaining
        family.cells [] (.frameEnd :: (encodeUnaryFrame family.cells).reverse) true
      let generated := unaryFrameMarkedCellAffineGeneratedStream family
      let finalWork := (encodeUnaryFrame
        (markedCellAffineRows_finalCells family.step remaining
          family.cells)).reverse
      let afterRows := markedCellAffineRowsCfg .clearInput none none false []
        generated.reverse finalWork [] [] (List.replicate family.step ()) []
      let hrows : EvalsToInTime
          (step unaryFrameMarkedCellAffineRowsRevProgram) beforeRows
          (some afterRows)
          (markedCellAffineRows_rowsSteps family.step remaining family.cells) :=
        ⟨⟨markedCellAffineRows_rowsSteps family.step remaining family.cells, by
            change
              (flip Option.bind
                (step unaryFrameMarkedCellAffineRowsRevProgram))^[
                  markedCellAffineRows_rowsSteps family.step remaining family.cells]
                (some beforeRows) = some afterRows
            simpa [beforeRows, afterRows, generated,
              unaryFrameMarkedCellAffineGeneratedStream,
              unaryFrameMarkedCellAffineGeneratedRows, hcountValue,
              List.reverse_append, List.append_assoc] using hrowsRaw⟩, le_rfl⟩
      have hcleanupRaw := markedCellAffineRows_cleanup_eval [] generated.reverse
        finalWork family.step none
      let hcleanup : EvalsToInTime
          (step unaryFrameMarkedCellAffineRowsRevProgram) afterRows
          (some (haltCfg unaryFrameMarkedCellAffineRowsRevProgram
            generated.reverse))
          (markedCellAffineRows_cleanupSteps [] finalWork family.step) :=
        ⟨⟨markedCellAffineRows_cleanupSteps [] finalWork family.step, by
            change
              (flip Option.bind
                (step unaryFrameMarkedCellAffineRowsRevProgram))^[
                  markedCellAffineRows_cleanupSteps [] finalWork family.step]
                (some afterRows) = some (haltCfg
                  unaryFrameMarkedCellAffineRowsRevProgram generated.reverse)
            simpa [afterRows] using hcleanupRaw⟩, le_rfl⟩
      let h₁ := EvalsToInTime.trans
        (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ afterBegin _
          hbegin hcopy
      let h₂ := EvalsToInTime.trans
        (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ afterCopy _ h₁ hfinish
      let h₃ := EvalsToInTime.trans
        (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ beforeRows _ h₂ hrows
      let hbody := EvalsToInTime.trans
        (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ afterRows _ h₃ hcleanup
      let full := EvalsToInTime.trans
        (step unaryFrameMarkedCellAffineRowsRevProgram) _ _ _ afterParams _
          hparams hbody
      convert full using 1 <;>
        simp [unaryFrameMarkedCellAffineRowsRevSteps, hcountValue,
          finalWork, generated] <;> omega

private theorem markedCellAffineRows_successorRows_eq_generated
    (amount count : Nat) (cells : List Nat) :
    markedCellAffineRows_successorRows amount count cells =
      unaryFrameMarkedCellAffineGeneratedRows amount count
        (cells.map fun value => value + amount) := by
  cases count <;> rfl

/-- The recursive controller rows have the closed arm-indexed affine form. -/
theorem unaryFrameMarkedCellAffineGeneratedRows_eq_ofFn
    (amount count : Nat) (cells : List Nat) :
    unaryFrameMarkedCellAffineGeneratedRows amount count cells =
      List.ofFn fun row : Fin count =>
        cells.map fun value => value + amount * row.val := by
  induction count generalizing cells with
  | zero => rfl
  | succ count ih =>
      rw [unaryFrameMarkedCellAffineGeneratedRows, List.ofFn_succ]
      congr 1
      · simp
      · rw [markedCellAffineRows_successorRows_eq_generated, ih]
        apply List.ofFn_inj.mpr
        funext row
        simp only [Fin.val_succ, List.map_map]
        apply List.map_congr_left
        intro value _
        simp only [Function.comp_apply]
        rw [Nat.mul_succ]
        omega

/-- The recursively simulated byte stream is exactly the public affine row
specification. -/
theorem unaryFrameMarkedCellAffineGeneratedStream_eq
    (family : UnaryFrameMarkedCellAffineRows) :
    unaryFrameMarkedCellAffineGeneratedStream family =
      unaryFrameMarkedCellAffineRowsStream family := by
  unfold unaryFrameMarkedCellAffineGeneratedStream
    unaryFrameMarkedCellAffineRowsStream unaryFrameMarkedCellAffineRowValues
  rw [unaryFrameMarkedCellAffineGeneratedRows_eq_ofFn]

/-- Public exact clean-halt execution theorem. -/
def unaryFrameMarkedCellAffineRowsRev_runFrom
    (family : UnaryFrameMarkedCellAffineRows) :
    EvalsToInTime (step unaryFrameMarkedCellAffineRowsRevProgram)
      (initialCfg unaryFrameMarkedCellAffineRowsRevProgram
        (encodeUnaryFrameMarkedCellAffineRows family))
      (some (haltCfg unaryFrameMarkedCellAffineRowsRevProgram
        (unaryFrameMarkedCellAffineRowsStream family).reverse))
      (unaryFrameMarkedCellAffineRowsRevSteps family) := by
  simpa only [unaryFrameMarkedCellAffineGeneratedStream_eq] using
    unaryFrameMarkedCellAffineRowsRev_runGenerated family

end CLRS.Chapter34.Turing.PolyBuilder
