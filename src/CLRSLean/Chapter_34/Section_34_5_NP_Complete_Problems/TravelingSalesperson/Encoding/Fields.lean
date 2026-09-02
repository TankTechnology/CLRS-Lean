import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding.Basic

/-!
# Delimited compact-natural fields for TSP records
-/

namespace CLRS.Chapter34

def encodeTSPField (n : Nat) : List TSPSym :=
  .numberMark :: (encodeBinaryNat n).map .bit ++ [.fieldEnd]

def encodeTSPFields (values : List Nat) : List TSPSym :=
  values.flatMap encodeTSPField

/-- Consume the maximal leading run of bit tokens. -/
def consumeTSPBits : List TSPSym → List Bool × List TSPSym
  | .bit value :: rest =>
      let result := consumeTSPBits rest
      (value :: result.1, result.2)
  | input => ([], input)

@[simp] theorem consumeTSPBits_map_append (bits : List Bool)
    (suffix : List TSPSym) :
    consumeTSPBits (bits.map TSPSym.bit ++ .fieldEnd :: suffix) =
      (bits, .fieldEnd :: suffix) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simp only [List.map_cons, List.cons_append, consumeTSPBits, ih]

mutual
  /-- Parse all number fields and require one final record terminator. -/
  def decodeTSPFields : List TSPSym → Option (List Nat)
    | [.recordEnd] => some []
    | .numberMark :: input => decodeTSPField [] input
    | _ => none

  /-- Parse one compact field while accumulating its bits in reverse. -/
  def decodeTSPField (reversed : List Bool) :
      List TSPSym → Option (List Nat)
    | .bit value :: rest => decodeTSPField (value :: reversed) rest
    | .fieldEnd :: rest =>
        match decodeBinaryNat reversed.reverse, decodeTSPFields rest with
        | some value, some values => some (value :: values)
        | _, _ => none
    | _ => none
end

private theorem decodeTSPField_map_append (reversed bits : List Bool)
    (suffix : List TSPSym) :
    decodeTSPField reversed
        (bits.map TSPSym.bit ++ .fieldEnd :: suffix) =
      match decodeBinaryNat (reversed.reverse ++ bits),
          decodeTSPFields suffix with
      | some value, some values => some (value :: values)
      | _, _ => none := by
  induction bits generalizing reversed with
  | nil => simp [decodeTSPField]
  | cons bit bits ih =>
      simp only [List.map_cons, List.cons_append, decodeTSPField]
      rw [ih (bit :: reversed)]
      simp [List.reverse_cons, List.append_assoc]

@[simp] theorem decodeTSPFields_encode (values : List Nat) :
    decodeTSPFields (encodeTSPFields values ++ [.recordEnd]) =
      some values := by
  induction values with
  | nil => simp [encodeTSPFields, decodeTSPFields]
  | cons value values ih =>
      simp only [encodeTSPFields, List.flatMap_cons, encodeTSPField,
        List.cons_append, List.append_assoc]
      rw [decodeTSPFields, decodeTSPField_map_append]
      simp only [List.reverse_nil, List.nil_append, decodeBinaryNat_encode]
      change decodeTSPFields
        (List.flatMap encodeTSPField values ++ [.recordEnd]) =
          some values at ih
      rw [ih]

end CLRS.Chapter34
