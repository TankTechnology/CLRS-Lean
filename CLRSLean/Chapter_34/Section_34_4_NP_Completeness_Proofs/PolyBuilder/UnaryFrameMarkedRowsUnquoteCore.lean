import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameUnquoteCore

/-!
# Decoding a family of quoted marked rows

Unlike the singleton decoder, this controller treats a literal `frameEnd` at
a codeword boundary as a decoded row terminator and continues with the next
quoted row.  Thus one physical marked-row family becomes the original stream
with every row boundary retained.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Total decoder for a sequence of quoted, `frameEnd`-delimited rows. -/
def unquoteUnaryFrameMarkedRows : List UnaryFrameSym → List UnaryFrameSym
  | [] => []
  | .frameEnd :: rest =>
      .frameEnd :: unquoteUnaryFrameMarkedRows rest
  | [.tick] => []
  | .tick :: .tick :: rest =>
      .tick :: unquoteUnaryFrameMarkedRows rest
  | .tick :: .separator :: rest =>
      .separator :: unquoteUnaryFrameMarkedRows rest
  | .tick :: .frameEnd :: _ => []
  | [.separator] => []
  | .separator :: .tick :: rest =>
      .frameEnd :: unquoteUnaryFrameMarkedRows rest
  | .separator :: .separator :: _ => []
  | .separator :: .frameEnd :: _ => []

/-- One quoted payload followed by further marked rows decodes compositionally. -/
theorem unquoteUnaryFrameMarkedRows_quote_append
    (payload rest : List UnaryFrameSym) :
    unquoteUnaryFrameMarkedRows
        (quoteUnaryFrameStream payload ++ rest) =
      payload ++ unquoteUnaryFrameMarkedRows rest := by
  induction payload with
  | nil => rfl
  | cons symbol payload ih =>
      cases symbol <;>
        simp [quoteUnaryFrameStream_cons, quoteUnaryFrameSym,
          unquoteUnaryFrameMarkedRows, ih]

/-- Decoding a marked quoted row retains its boundary and continues. -/
theorem unquoteUnaryFrameMarkedRows_quote_boundary_append
    (payload rest : List UnaryFrameSym) :
    unquoteUnaryFrameMarkedRows
        (quoteUnaryFrameStream payload ++ .frameEnd :: rest) =
      payload ++ .frameEnd :: unquoteUnaryFrameMarkedRows rest := by
  rw [unquoteUnaryFrameMarkedRows_quote_append]
  rfl

/-- Exact family-level semantics of the multi-row decoder. -/
theorem unquoteUnaryFrameMarkedRows_encode_family
    (rows : List (List UnaryFrameSym)) :
    unquoteUnaryFrameMarkedRows
        (rows.flatMap fun row =>
          quoteUnaryFrameStream row ++ [.frameEnd]) =
      rows.flatMap fun row => row ++ [.frameEnd] := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.flatMap_cons]
      rw [show quoteUnaryFrameStream row ++ [.frameEnd] ++
              List.flatMap
                (fun next => quoteUnaryFrameStream next ++ [.frameEnd]) rows =
            quoteUnaryFrameStream row ++ .frameEnd ::
              List.flatMap
                (fun next => quoteUnaryFrameStream next ++ [.frameEnd]) rows by
        simp [List.append_assoc]]
      rw [unquoteUnaryFrameMarkedRows_quote_boundary_append, ih]
      simp [List.append_assoc]

/-- Finite control of the reverse-output marked-row decoder. -/
inductive UnaryFrameMarkedRowsUnquoteLabel
  | scan
  | afterTick
  | afterSeparator
  | emit (symbol : UnaryFrameSym)
  | drain
  | finish
deriving DecidableEq, Fintype

/-- Reverse-output decoder which copies valid outer row boundaries. -/
def unaryFrameMarkedRowsUnquoteRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameMarkedRowsUnquoteLabel
  main := .scan
  op
    | .scan => .popInput .finish fun
        | .tick => .afterTick
        | .separator => .afterSeparator
        | .frameEnd => .emit .frameEnd
    | .afterTick => .popInput .finish fun
        | .tick => .emit .tick
        | .separator => .emit .separator
        | .frameEnd => .drain
    | .afterSeparator => .popInput .finish fun
        | .tick => .emit .frameEnd
        | .separator => .drain
        | .frameEnd => .drain
    | .emit symbol => .pushOutput symbol .scan
    | .drain => .popInput .finish fun _ => .drain
    | .finish => .halt

/-- Uniform configuration surface for simulations. -/
def unaryFrameMarkedRowsUnquoteCfg
    (label : UnaryFrameMarkedRowsUnquoteLabel)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    BuilderCfg unaryFrameMarkedRowsUnquoteRevProgram :=
  { label := some label
    buffer₁ := buffer
    buffer₂ := none
    test := false
    input := input
    output := output
    work₁ := []
    work₂ := []
    counter₁ := []
    counter₂ := []
    counter₃ := [] }

end CLRS.Chapter34.Turing.PolyBuilder
