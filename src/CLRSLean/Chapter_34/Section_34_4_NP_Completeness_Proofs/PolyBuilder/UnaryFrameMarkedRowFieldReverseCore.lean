import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowDuplicate

/-!
# Reversing unary fields inside marked rows: core definitions

The transform reverses the order of unary naturals in every row while
preserving the `tick* separator` representation of each individual value.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Structured natural-number rows whose physical representation uses the
ordinary unary encoding inside `frameEnd`-delimited outer rows. -/
structure UnaryFrameValueRowFamily where
  rows : List (List Nat)

private theorem fieldReverse_encodeUnaryFrame_frameEnd_free
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, _, hblock⟩
  simp [encodeUnaryFrameBlock] at hblock
  rcases hblock with ⟨_, rfl⟩ | rfl <;> decide

/-- Typed marked view of the source value rows. -/
def UnaryFrameValueRowFamily.marked
    (family : UnaryFrameValueRowFamily) : UnaryFrameMarkedRowFamily :=
  { rows := family.rows.map encodeUnaryFrame
    frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨values, _, rfl⟩
      exact fieldReverse_encodeUnaryFrame_frameEnd_free values symbol hsymbol }

/-- Physical input stream of a structured value-row family. -/
def encodeUnaryFrameValueRowFamily
    (family : UnaryFrameValueRowFamily) : List UnaryFrameSym :=
  encodeUnaryFrameMarkedRowFamily family.marked

/-- Typed result after reversing the natural-number fields of every row. -/
def UnaryFrameValueRowFamily.fieldReversed
    (family : UnaryFrameValueRowFamily) : UnaryFrameMarkedRowFamily :=
  { rows := family.rows.map fun values => encodeUnaryFrame values.reverse
    frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨values, _, rfl⟩
      exact fieldReverse_encodeUnaryFrame_frameEnd_free values.reverse
        symbol hsymbol }

/-- Public forward stream produced by the field-order reverser. -/
def unaryFrameMarkedRowFieldReverseStream
    (family : UnaryFrameValueRowFamily) : List UnaryFrameSym :=
  encodeUnaryFrameMarkedRowFamily family.fieldReversed

inductive UnaryFrameMarkedRowFieldReverseLabel
  | scan
  | checkRow
  | saveSeparator
  | moveTicks
  | saveInputTick
  | saveMovedTick
  | transfer
  | transferEmit (symbol : UnaryFrameSym)
  | mark
  | finish
  | invalid
deriving DecidableEq, Fintype

/-- The first pass builds every reversed-field row on `work₁`; prepend-only
output then produces the reverse of the complete target stream. -/
def unaryFrameMarkedRowFieldReverseRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameMarkedRowFieldReverseLabel
  main := .scan
  op
    | .scan => .popInput .finish fun
        | .tick => .saveInputTick
        | .separator => .saveSeparator
        | .frameEnd => .checkRow
    | .saveInputTick => .pushWork₂ .tick .scan
    | .saveSeparator => .pushWork₁ .separator .moveTicks
    | .moveTicks => .popWork₂ .scan (fun _ => .saveMovedTick)
    | .saveMovedTick => .pushWork₁ .tick .moveTicks
    | .checkRow => .popWork₂ .transfer (fun _ => .invalid)
    | .transfer => .popWork₁ .mark .transferEmit
    | .transferEmit symbol => .pushOutput symbol .transfer
    | .mark => .pushOutput .frameEnd .scan
    | .finish => .halt
    | .invalid => .halt

/-- Uniform proof configuration. -/
def unaryFrameMarkedRowFieldReverseCfg
    (label : UnaryFrameMarkedRowFieldReverseLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym) :
    BuilderCfg unaryFrameMarkedRowFieldReverseRevProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := []
  counter₂ := []
  counter₃ := []

def unaryFrameMarkedRowFieldReverseLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg unaryFrameMarkedRowFieldReverseRevProgram :=
  unaryFrameMarkedRowFieldReverseCfg .scan none none false input output [] []

end CLRS.Chapter34.Turing.PolyBuilder
