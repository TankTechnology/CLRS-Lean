import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import Mathlib.Tactic.DeriveFintype

/-!
# Boolean selection of delimited binary fields

The left input is one Boolean per field.  The right input is a flattened list
of binary fields with explicit absence delimiters.  The fixed controller retains exactly
the fields whose aligned Boolean is true and stops safely at the shorter side.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder.SelectDelimitedFields

inductive InputSym
  | flag (value : Bool)
  | field (value : Option Bool)
deriving DecidableEq, Fintype

def inputEncoding (input : List Bool × List (Option Bool)) :
    List (Option InputSym) :=
  (input.1.map InputSym.flag).map some ++
    none :: (input.2.map InputSym.field).map some

mutual
  def selectFields : List Bool → List (Option Bool) → List (Option Bool)
    | [], _ => []
    | flag :: flags, fields => selectCurrent flag flags fields
  termination_by flags fields => flags.length + fields.length

  def selectCurrent (flag : Bool) (flags : List Bool) :
      List (Option Bool) → List (Option Bool)
    | [] => []
    | some bit :: fields =>
        if flag then some bit :: selectCurrent flag flags fields
        else selectCurrent flag flags fields
    | none :: fields =>
        if flag then none :: selectFields flags fields
        else selectFields flags fields
  termination_by fields => flags.length + fields.length
end

mutual
  def filterSteps : List Bool → List (Option Bool) → Nat
    | [], fields => fields.length + 2
    | flag :: flags, fields => 1 + currentSteps flag flags fields
  termination_by flags fields => flags.length + fields.length

  def currentSteps (flag : Bool) (flags : List Bool) :
      List (Option Bool) → Nat
    | [] => flags.length + 2
    | some _ :: fields =>
        (if flag then 2 else 1) + currentSteps flag flags fields
    | none :: fields =>
        (if flag then 2 else 1) + filterSteps flags fields
  termination_by fields => flags.length + fields.length
end

inductive Label
  | scanFlags
  | saveFlag (flag : Bool)
  | transfer
  | nextField
  | scanField (selected : Bool)
  | saveField (selected : Bool) (field : Option Bool)
  | clearFlags
  | drain
  | restore
  | emit (field : Option Bool)
  | halt
deriving DecidableEq, Fintype

def program : Program (Option InputSym) (Option Bool) where
  Label := Label
  main := .scanFlags
  op
    | .scanFlags => .popInput .transfer fun
        | none => .transfer
        | some (.flag flag) => .saveFlag flag
        | some (.field _) => .drain
    | .saveFlag flag => .pushWork₁ (some (.flag flag)) .scanFlags
    | .transfer => .moveWork₁Work₂ .nextField fun _ => .transfer
    | .nextField => .popWork₂ .drain fun
        | some (.flag flag) => .scanField flag
        | _ => .nextField
    | .scanField selected => .popInput .clearFlags fun
        | some (.field field) =>
            match field with
            | some bit =>
                if selected then .saveField selected (some bit)
                else .scanField selected
            | none =>
                if selected then .saveField selected none
                else .nextField
        | _ => .drain
    | .saveField selected field =>
        .pushWork₁ (some (.field field))
          (if field.isSome then .scanField selected else .nextField)
    | .clearFlags => .popWork₂ .restore fun _ => .clearFlags
    | .drain => .popInput .restore fun _ => .drain
    | .restore => .popWork₁ .halt fun
        | some (.field field) => .emit field
        | _ => .restore
    | .emit field => .pushOutput field .restore
    | .halt => .halt

def cfg (label : Label) (buffer₁ buffer₂ : Option (Option InputSym))
    (test : Bool) (input : List (Option InputSym))
    (output : List (Option Bool))
    (work₁ work₂ : List (Option InputSym)) : BuilderCfg program where
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

def storedFlags (flags : List Bool) : List (Option InputSym) :=
  flags.map fun flag => some (.flag flag)

def storedFields (fields : List (Option Bool)) : List (Option InputSym) :=
  fields.map fun field => some (.field field)

end CLRS.Chapter34.Turing.PolyBuilder.SelectDelimitedFields
