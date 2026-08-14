import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Basic

/-!
# General Circuit Encoding

This file gives general acyclic Boolean circuits a finite-symbol wire format.
Natural numbers use unary `argMark` symbols terminated by `endMark`; a circuit
then stores its input arity, its gates in order, and one final output marker and
output index.  The decoder is total, and
`encodeCircuit_of_decodeCircuit_eq_some` proves that every successful decode is
exactly the canonical encoding of its result.  Thus malformed strings and
strings with trailing data are honest no-instances of `GeneralCircuitSAT`.

Main results:

- `decNat_encNat`: unary natural-number encoding round-trips with any suffix.
- `decodeCircuit_encodeCircuit`: circuit encoding round-trips exactly.
- `encodeCircuit_of_decodeCircuit_eq_some`: every successful decode reconstructs
  the complete canonical encoding, including the absence of trailing data.
- `inputCount_lt_length_of_decodeCircuit_eq_some`: every accepted string is
  longer than its decoded circuit's input count.
- `encodeCircuit_length_le`: well-formed circuit encodings have a polynomial
  length bound.
- `encodeCircuit_mem_generalCircuitSAT_iff`: encoded circuits belong to the
  language exactly when they are satisfiable.
- `not_mem_generalCircuitSAT_of_decode_none`: malformed strings are not in the
  language.
-/

namespace CLRS

namespace Chapter34

/-! ## Finite wire format -/

/-- The finite alphabet for general acyclic Boolean-circuit encodings. -/
inductive CircuitSym : Type
  | inputMark | constFalseMark | constTrueMark
  | notMark | andMark | orMark
  | outputMark | argMark | endMark
deriving DecidableEq, Repr, Fintype, Inhabited

/-- Encode a natural number in unary, terminated by `endMark`. -/
def encNat (n : Nat) : List CircuitSym :=
  List.replicate n .argMark ++ [.endMark]

/-- Decode one terminated unary natural number, returning the unused suffix. -/
def decNat : List CircuitSym → Option (Nat × List CircuitSym)
  | [] => none
  | .argMark :: xs => (decNat xs).map fun (n, rest) => (n + 1, rest)
  | .endMark :: xs => some (0, xs)
  | _ => none

/-- Decoding an encoded natural number preserves the exact following suffix. -/
lemma decNat_encNat (n : Nat) (rest : List CircuitSym) :
    decNat (encNat n ++ rest) = some (n, rest) := by
  induction n generalizing rest with
  | zero => simp [encNat, decNat]
  | succ n ih =>
      rw [show encNat (n + 1) ++ rest =
        .argMark :: (encNat n ++ rest) by
          simp [encNat, List.replicate_succ, List.append_assoc]]
      simp [decNat, ih]

/-- Every successful unary decode reconstructs the exact consumed prefix. -/
private lemma eq_encNat_append_of_decNat_eq_some
    {xs rest : List CircuitSym} {n : Nat}
    (h : decNat xs = some (n, rest)) :
    xs = encNat n ++ rest := by
  induction xs generalizing n rest with
  | nil => simp [decNat] at h
  | cons sym xs ih =>
      cases sym with
      | argMark =>
          simp only [decNat] at h
          rcases Option.map_eq_some_iff.mp h with ⟨⟨m, suffix⟩, hdec, hpairs⟩
          simp only [Prod.mk.injEq] at hpairs
          rcases hpairs with ⟨rfl, rfl⟩
          rw [ih hdec]
          simp [encNat, List.replicate_succ, List.append_assoc]
      | endMark =>
          simp only [decNat, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp [encNat]
      | inputMark => simp [decNat] at h
      | constFalseMark => simp [decNat] at h
      | constTrueMark => simp [decNat] at h
      | notMark => simp [decNat] at h
      | andMark => simp [decNat] at h
      | orMark => simp [decNat] at h
      | outputMark => simp [decNat] at h

/-- Encode one circuit gate as its tag followed by its unary arguments. -/
def encodeCircuitGate : CircuitGate → List CircuitSym
  | .input inputIndex => .inputMark :: encNat inputIndex
  | .const false => [.constFalseMark]
  | .const true => [.constTrueMark]
  | .not source => .notMark :: encNat source
  | .and left right => .andMark :: (encNat left ++ encNat right)
  | .or left right => .orMark :: (encNat left ++ encNat right)

/-- Encode a circuit as input arity, ordered gates, and its output index. -/
def encodeCircuit (c : Circuit) : List CircuitSym :=
  encNat c.inputCount ++
    c.gates.flatMap encodeCircuitGate ++
      .outputMark :: encNat c.output

/-- Decode one non-output circuit gate, returning the unused suffix. -/
def decodeCircuitGate : List CircuitSym → Option (CircuitGate × List CircuitSym)
  | .inputMark :: xs => do
      let (inputIndex, rest) ← decNat xs
      pure (.input inputIndex, rest)
  | .constFalseMark :: xs => some (.const false, xs)
  | .constTrueMark :: xs => some (.const true, xs)
  | .notMark :: xs => do
      let (source, rest) ← decNat xs
      pure (.not source, rest)
  | .andMark :: xs => do
      let (left, rest) ← decNat xs
      let (right, rest) ← decNat rest
      pure (.and left right, rest)
  | .orMark :: xs => do
      let (left, rest) ← decNat xs
      let (right, rest) ← decNat rest
      pure (.or left right, rest)
  | _ => none

/-- Every successful gate decode reconstructs the exact tagged gate prefix. -/
private lemma eq_encodeCircuitGate_append_of_decodeCircuitGate_eq_some
    {xs rest : List CircuitSym} {gate : CircuitGate}
    (h : decodeCircuitGate xs = some (gate, rest)) :
    xs = encodeCircuitGate gate ++ rest := by
  cases xs with
  | nil => simp [decodeCircuitGate] at h
  | cons sym xs =>
      cases sym with
      | inputMark =>
          cases hdec : decNat xs with
          | none => simp [decodeCircuitGate, hdec] at h
          | some decoded =>
              rcases decoded with ⟨inputIndex, suffix⟩
              simp only [decodeCircuitGate, hdec] at h
              rcases h with ⟨rfl, rfl⟩
              rw [eq_encNat_append_of_decNat_eq_some hdec]
              simp [encodeCircuitGate]
      | constFalseMark =>
          simp only [decodeCircuitGate, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp [encodeCircuitGate]
      | constTrueMark =>
          simp only [decodeCircuitGate, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp [encodeCircuitGate]
      | notMark =>
          cases hdec : decNat xs with
          | none => simp [decodeCircuitGate, hdec] at h
          | some decoded =>
              rcases decoded with ⟨source, suffix⟩
              simp only [decodeCircuitGate, hdec] at h
              rcases h with ⟨rfl, rfl⟩
              rw [eq_encNat_append_of_decNat_eq_some hdec]
              simp [encodeCircuitGate]
      | andMark =>
          cases hleft : decNat xs with
          | none => simp [decodeCircuitGate, hleft] at h
          | some decodedLeft =>
              rcases decodedLeft with ⟨left, middle⟩
              simp only [decodeCircuitGate, hleft, Option.bind_eq_bind,
                Option.bind_some] at h
              cases hright : decNat middle with
              | none => simp [hright] at h
              | some decodedRight =>
                  rcases decodedRight with ⟨right, suffix⟩
                  simp only [hright, Option.bind_some] at h
                  rcases h with ⟨rfl, rfl⟩
                  rw [eq_encNat_append_of_decNat_eq_some hleft,
                    eq_encNat_append_of_decNat_eq_some hright]
                  simp [encodeCircuitGate, List.append_assoc]
      | orMark =>
          cases hleft : decNat xs with
          | none => simp [decodeCircuitGate, hleft] at h
          | some decodedLeft =>
              rcases decodedLeft with ⟨left, middle⟩
              simp only [decodeCircuitGate, hleft, Option.bind_eq_bind,
                Option.bind_some] at h
              cases hright : decNat middle with
              | none => simp [hright] at h
              | some decodedRight =>
                  rcases decodedRight with ⟨right, suffix⟩
                  simp only [hright, Option.bind_some] at h
                  rcases h with ⟨rfl, rfl⟩
                  rw [eq_encNat_append_of_decNat_eq_some hleft,
                    eq_encNat_append_of_decNat_eq_some hright]
                  simp [encodeCircuitGate, List.append_assoc]
      | outputMark => simp [decodeCircuitGate] at h
      | argMark => simp [decodeCircuitGate] at h
      | endMark => simp [decodeCircuitGate] at h

/-- Decode gates structurally on a gate-count fuel.  Only `outputMark` ends the
gate stream; every ordinary gate consumes one unit of fuel. -/
private def decodeCircuitGates : Nat → List CircuitSym →
    Option (List CircuitGate × Nat × List CircuitSym)
  | _, [] => none
  | _, .outputMark :: xs => do
      let (output, rest) ← decNat xs
      pure ([], output, rest)
  | 0, _ => none
  | fuel + 1, xs => do
      let (gate, rest) ← decodeCircuitGate xs
      let (gates, output, trailing) ← decodeCircuitGates fuel rest
      pure (gate :: gates, output, trailing)

/-- Away from `outputMark`, a positive-fuel stream decode first decodes one
ordinary gate and then recurses on the unused suffix. -/
private lemma decodeCircuitGates_succ_of_ne_output
    (fuel : Nat) (sym : CircuitSym) (xs : List CircuitSym)
    (h : sym ≠ .outputMark) :
    decodeCircuitGates (fuel + 1) (sym :: xs) = (do
      let (gate, rest) ← decodeCircuitGate (sym :: xs)
      let (gates, output, trailing) ← decodeCircuitGates fuel rest
      pure (gate :: gates, output, trailing)) := by
  cases sym <;> simp_all [decodeCircuitGates]

/-- Every successful gate-stream decode reconstructs the exact consumed gate
prefix, output marker, output number, and unused trailing suffix. -/
private lemma eq_encodeCircuitGates_append_of_decodeCircuitGates_eq_some
    {fuel : Nat} {xs trailing : List CircuitSym}
    {gates : List CircuitGate} {output : Nat}
    (h : decodeCircuitGates fuel xs = some (gates, output, trailing)) :
    xs = gates.flatMap encodeCircuitGate ++
      .outputMark :: encNat output ++ trailing := by
  induction fuel generalizing xs gates output trailing with
  | zero =>
      cases xs with
      | nil => simp [decodeCircuitGates] at h
      | cons sym xs =>
          by_cases hout : sym = .outputMark
          · subst sym
            cases hdec : decNat xs with
            | none => simp [decodeCircuitGates, hdec] at h
            | some decoded =>
                rcases decoded with ⟨decodedOutput, suffix⟩
                simp only [decodeCircuitGates, hdec, Option.bind_eq_bind,
                  Option.bind_some] at h
                rcases h with ⟨rfl, rfl, rfl⟩
                rw [eq_encNat_append_of_decNat_eq_some hdec]
                simp
          · cases sym <;> simp_all [decodeCircuitGates]
  | succ fuel ih =>
      cases xs with
      | nil => simp [decodeCircuitGates] at h
      | cons sym xs =>
          by_cases hout : sym = .outputMark
          · subst sym
            cases hdec : decNat xs with
            | none => simp [decodeCircuitGates, hdec] at h
            | some decoded =>
                rcases decoded with ⟨decodedOutput, suffix⟩
                simp only [decodeCircuitGates, hdec, Option.bind_eq_bind,
                  Option.bind_some] at h
                rcases h with ⟨rfl, rfl, rfl⟩
                rw [eq_encNat_append_of_decNat_eq_some hdec]
                simp
          · rw [decodeCircuitGates_succ_of_ne_output fuel sym xs hout] at h
            cases hgate : decodeCircuitGate (sym :: xs) with
            | none => simp [hgate] at h
            | some decodedGate =>
                rcases decodedGate with ⟨gate, rest⟩
                simp only [hgate, Option.bind_eq_bind, Option.bind_some] at h
                cases hrest : decodeCircuitGates fuel rest with
                | none => simp [hrest] at h
                | some decodedRest =>
                    rcases decodedRest with ⟨decodedGates, decodedOutput, suffix⟩
                    simp only [hrest, Option.bind_some] at h
                    rcases h with ⟨rfl, rfl, rfl⟩
                    rw [eq_encodeCircuitGate_append_of_decodeCircuitGate_eq_some hgate,
                      ih hrest]
                    simp [List.append_assoc]

/-- Decode a complete circuit and reject every unconsumed trailing symbol. -/
def decodeCircuit (input : List CircuitSym) : Option Circuit := do
  let (inputCount, rest) ← decNat input
  let (gates, output, trailing) ← decodeCircuitGates rest.length rest
  match trailing with
  | [] => some { inputCount, gates, output }
  | _ => none

/-! ## Codec correctness -/

/-- A gate decoder consumes exactly one encoded gate and preserves its suffix. -/
private lemma decodeCircuitGate_encodeCircuitGate (gate : CircuitGate)
    (rest : List CircuitSym) :
    decodeCircuitGate (encodeCircuitGate gate ++ rest) = some (gate, rest) := by
  cases gate with
  | input inputIndex => simp [encodeCircuitGate, decodeCircuitGate, decNat_encNat]
  | const value =>
      cases value <;> simp [encodeCircuitGate, decodeCircuitGate]
  | not source => simp [encodeCircuitGate, decodeCircuitGate, decNat_encNat]
  | and left right =>
      simp [encodeCircuitGate, decodeCircuitGate, decNat_encNat, List.append_assoc]
  | or left right =>
      simp [encodeCircuitGate, decodeCircuitGate, decNat_encNat, List.append_assoc]

/-- An encoded ordinary gate takes exactly one fuel step in the gate stream. -/
private lemma decodeCircuitGates_encodeCircuitGate_step
    (fuel : Nat) (gate : CircuitGate) (rest : List CircuitSym) :
    decodeCircuitGates (fuel + 1) (encodeCircuitGate gate ++ rest) = (do
      let (gates, output, trailing) ← decodeCircuitGates fuel rest
      pure (gate :: gates, output, trailing)) := by
  cases gate with
  | input inputIndex =>
      simp [encodeCircuitGate, decodeCircuitGate, decodeCircuitGates, decNat_encNat]
  | const value =>
      cases value <;> simp [encodeCircuitGate, decodeCircuitGate, decodeCircuitGates]
  | not source =>
      simp [encodeCircuitGate, decodeCircuitGate, decodeCircuitGates, decNat_encNat]
  | and left right =>
      simp [encodeCircuitGate, decodeCircuitGate, decodeCircuitGates,
        decNat_encNat, List.append_assoc]
  | or left right =>
      simp [encodeCircuitGate, decodeCircuitGate, decodeCircuitGates,
        decNat_encNat, List.append_assoc]

/-- A gate stream followed by an output marker round-trips with any extra fuel
and preserves the suffix after the output index. -/
private lemma decodeCircuitGates_encodeCircuitGates
    (gates : List CircuitGate) (output fuel : Nat) (rest : List CircuitSym) :
    decodeCircuitGates (gates.length + fuel)
        (gates.flatMap encodeCircuitGate ++ .outputMark :: encNat output ++ rest) =
      some (gates, output, rest) := by
  induction gates generalizing fuel with
  | nil => simp [decodeCircuitGates, decNat_encNat]
  | cons gate gates ih =>
      simp only [List.length_cons, List.flatMap_cons]
      rw [show gates.length + 1 + fuel = (gates.length + fuel) + 1 by omega]
      simp only [List.append_assoc]
      rw [decodeCircuitGates_encodeCircuitGate_step]
      have hih := ih fuel
      simp only [List.append_assoc] at hih
      rw [hih]
      rfl

/-- Every encoded gate contributes at least one symbol. -/
private lemma gates_length_le_encoded_length (gates : List CircuitGate) :
    gates.length ≤ (gates.flatMap encodeCircuitGate).length := by
  induction gates with
  | nil => simp
  | cons gate gates ih =>
      have hgate : 1 ≤ (encodeCircuitGate gate).length := by
        cases gate with
        | input inputIndex => simp [encodeCircuitGate]
        | const value => cases value <;> simp [encodeCircuitGate]
        | not source => simp [encodeCircuitGate]
        | and left right => simp [encodeCircuitGate]
        | or left right => simp [encodeCircuitGate]
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      omega

/-- Encoding a circuit and then decoding it recovers the original circuit. -/
theorem decodeCircuit_encodeCircuit (c : Circuit) :
    decodeCircuit (encodeCircuit c) = some c := by
  let stream := c.gates.flatMap encodeCircuitGate ++ .outputMark :: encNat c.output
  have hfuel : c.gates.length ≤ stream.length := by
    have hgate := gates_length_le_encoded_length c.gates
    simp only [stream, List.length_append, List.length_cons]
    omega
  obtain ⟨fuel, hfuel⟩ := Nat.exists_eq_add_of_le hfuel
  have hencoding : encodeCircuit c = encNat c.inputCount ++ stream := by
    simp [encodeCircuit, stream, List.append_assoc]
  rw [hencoding]
  unfold decodeCircuit
  rw [decNat_encNat]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [hfuel]
  have hdecode :=
    decodeCircuitGates_encodeCircuitGates c.gates c.output fuel ([] : List CircuitSym)
  simp only [List.append_nil] at hdecode
  rw [hdecode]
  rfl

/-- Every successfully decoded string is the canonical encoding of the
resulting circuit.  In particular, the decoder accepts no alternate or
trailing-data representation of a circuit. -/
theorem encodeCircuit_of_decodeCircuit_eq_some {x : List CircuitSym} {c : Circuit}
    (h : decodeCircuit x = some c) :
    encodeCircuit c = x := by
  unfold decodeCircuit at h
  cases hinput : decNat x with
  | none => simp [hinput] at h
  | some decodedInput =>
      rcases decodedInput with ⟨inputCount, rest⟩
      simp only [hinput, Option.bind_eq_bind, Option.bind_some] at h
      cases hstream : decodeCircuitGates rest.length rest with
      | none => simp [hstream] at h
      | some decodedStream =>
          rcases decodedStream with ⟨gates, output, trailing⟩
          simp only [hstream, Option.bind_some] at h
          cases trailing with
          | nil =>
              simp only [Option.some.injEq] at h
              subst c
              apply Eq.symm
              calc
                x = encNat inputCount ++ rest :=
                  eq_encNat_append_of_decNat_eq_some hinput
                _ = encNat inputCount ++
                      (gates.flatMap encodeCircuitGate ++
                        .outputMark :: encNat output) := by
                    rw [eq_encodeCircuitGates_append_of_decodeCircuitGates_eq_some
                      hstream]
                    simp
                _ = encodeCircuit { inputCount, gates, output } := by
                    simp [encodeCircuit, List.append_assoc]
          | cons sym trailing => simp at h

/-- A successfully decoded circuit's unary input-count prefix makes its input
count strictly smaller than the complete encoded string. -/
lemma inputCount_lt_length_of_decodeCircuit_eq_some
    {x : List CircuitSym} {c : Circuit}
    (h : decodeCircuit x = some c) :
    c.inputCount < x.length := by
  rw [← encodeCircuit_of_decodeCircuit_eq_some h]
  simp [encodeCircuit, encNat]

/-! ## Polynomial encoding bound -/

/-- A valid gate's encoding is bounded by the circuit's gate and input counts.
The input case uses the declared input bound, and dependency cases use the
gate-position predecessor bound. -/
private lemma encodeCircuitGate_length_le_of_valid
    (gate : CircuitGate) (inputCount gateCount index : Nat)
    (hindex : index < gateCount) (hvalid : gate.ValidAt inputCount index) :
    (encodeCircuitGate gate).length ≤ 2 * (gateCount + inputCount + 1) := by
  cases gate with
  | input inputIndex =>
      simp [CircuitGate.ValidAt, encodeCircuitGate, encNat] at hvalid ⊢
      omega
  | const value =>
      cases value <;> simp [encodeCircuitGate] <;> omega
  | not source =>
      simp [CircuitGate.ValidAt, encodeCircuitGate, encNat] at hvalid ⊢
      omega
  | and left right =>
      simp [CircuitGate.ValidAt, encodeCircuitGate, encNat] at hvalid ⊢
      omega
  | or left right =>
      simp [CircuitGate.ValidAt, encodeCircuitGate, encNat] at hvalid ⊢
      omega

/-- A pointwise gate-encoding bound sums to a bound for the flattened stream. -/
private lemma flatMap_encodeCircuitGate_length_le
    (gates : List CircuitGate) (bound : Nat)
    (h : ∀ i (hi : i < gates.length),
      (encodeCircuitGate (gates.get ⟨i, hi⟩)).length ≤ bound) :
    (gates.flatMap encodeCircuitGate).length ≤ gates.length * bound := by
  induction gates with
  | nil => simp
  | cons gate gates ih =>
      have hhead : (encodeCircuitGate gate).length ≤ bound := by
        simpa using h 0 (by simp)
      have htail : ∀ i (hi : i < gates.length),
          (encodeCircuitGate (gates.get ⟨i, hi⟩)).length ≤ bound := by
        intro i hi
        simpa using h (i + 1) (by simp [hi])
      have hrest := ih htail
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [Nat.add_mul, one_mul]
      omega

/-- The flattened gate stream of a well-formed circuit has a uniform
quadratic bound obtained from every gate's valid input/predecessor indices. -/
private lemma encodeCircuitGates_length_le (c : Circuit) (h : c.WellFormed) :
    (c.gates.flatMap encodeCircuitGate).length ≤
      c.gates.length * (2 * (c.gates.length + c.inputCount + 1)) := by
  apply flatMap_encodeCircuitGate_length_le
  intro i hi
  exact encodeCircuitGate_length_le_of_valid
    (c.gates.get ⟨i, hi⟩) c.inputCount c.gates.length i hi (h.2 i hi)

/-- A well-formed circuit has an encoding polynomial in its gate and input
counts.  Well-formedness bounds input indices by `inputCount`, predecessor
indices by the current gate position, and the output index by gate count. -/
lemma encodeCircuit_length_le (c : Circuit) (h : c.WellFormed) :
    (encodeCircuit c).length ≤
      12 * (c.gates.length + 1) *
        (c.gates.length + c.inputCount + 1) := by
  have hgates := encodeCircuitGates_length_le c h
  have houtput := h.1
  simp only [encodeCircuit, encNat, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  nlinarith

/-! ## Honest language -/

/-- The language of exactly decoded, well-formed, satisfiable general circuits. -/
def GeneralCircuitSAT : Language CircuitSym :=
  { input | ∃ c, decodeCircuit input = some c ∧ GeneralCircuitSatisfiable c }

/-- A circuit's canonical encoding is in the general-circuit language exactly
when the circuit is well formed and satisfiable. -/
lemma encodeCircuit_mem_generalCircuitSAT_iff (c : Circuit) :
    encodeCircuit c ∈ GeneralCircuitSAT ↔ GeneralCircuitSatisfiable c := by
  simp [GeneralCircuitSAT, decodeCircuit_encodeCircuit]

/-- Any string rejected by the total circuit decoder is outside the language. -/
lemma not_mem_generalCircuitSAT_of_decode_none {x : List CircuitSym}
    (h : decodeCircuit x = none) : x ∉ GeneralCircuitSAT := by
  simp [GeneralCircuitSAT, h]

end Chapter34

end CLRS
