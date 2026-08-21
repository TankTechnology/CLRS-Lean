import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros

/-!
# Fixed two-symbol codecs

A finite output alphabet can often be embedded in pairs over a smaller
alphabet.  This file defines the semantic codec and the small streaming
decoder used by the polynomial-time closure theorem.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Expand one source symbol into its fixed two-symbol codeword. -/
def fixedPairEncodeBody {Γ Δ : Type} (encode : Γ → Δ × Δ) :
    LoopBody Γ Δ where
  emit symbol := [encode symbol |>.1, encode symbol |>.2]
  cost _ := 2
  emit_length_le_cost _ := by simp

/-- Concatenate the fixed two-symbol codewords of a source word. -/
def fixedPairEncode {Γ Δ : Type} (encode : Γ → Δ × Δ)
    (input : List Γ) : List Δ :=
  input.flatMap (fixedPairEncodeBody encode).emit

@[simp] theorem fixedPairEncode_nil {Γ Δ : Type}
    (encode : Γ → Δ × Δ) :
    fixedPairEncode encode [] = [] := rfl

@[simp] theorem fixedPairEncode_cons {Γ Δ : Type}
    (encode : Γ → Δ × Δ) (symbol : Γ) (rest : List Γ) :
    fixedPairEncode encode (symbol :: rest) =
      [encode symbol |>.1, encode symbol |>.2] ++
        fixedPairEncode encode rest := rfl

@[simp] theorem fixedPairEncode_append {Γ Δ : Type}
    (encode : Γ → Δ × Δ) (left right : List Γ) :
    fixedPairEncode encode (left ++ right) =
      fixedPairEncode encode left ++ fixedPairEncode encode right := by
  simp [fixedPairEncode, List.flatMap_append]

/-- Total pair decoder.  A final unmatched symbol is ignored. -/
def fixedPairDecode {Γ Δ : Type} (decode : Δ → Δ → Γ) :
    List Δ → List Γ
  | first :: second :: rest =>
      decode first second :: fixedPairDecode decode rest
  | _ => []

/-- A left-inverse symbol table makes the stream codec a left inverse. -/
@[simp] theorem fixedPairDecode_encode {Γ Δ : Type}
    (encode : Γ → Δ × Δ) (decode : Δ → Δ → Γ)
    (hleft : ∀ symbol, decode (encode symbol).1 (encode symbol).2 = symbol)
    (input : List Γ) :
    fixedPairDecode decode (fixedPairEncode encode input) = input := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      simp [fixedPairEncode_cons, fixedPairDecode, hleft, ih]

/-- Finite control for the direct reverse-output decoder. -/
inductive FixedPairDecodeLabel (Δ : Type)
  | scan
  | afterFirst (first : Δ)
  | emit (first second : Δ)
  | finish
deriving Fintype

/-- Classical equality is available because the carried alphabet is finite. -/
noncomputable instance fixedPairDecodeLabelDecidableEq
    {Δ : Type} [Fintype Δ] : DecidableEq (FixedPairDecodeLabel Δ) :=
  Classical.decEq _

/-- A streaming decoder for fixed two-symbol codewords.

The output stack prepends, so this direct pass produces the reverse of
`fixedPairDecode decode input`.
-/
def fixedPairDecodeRevProgram {Γ Δ : Type} [Fintype Δ]
    (decode : Δ → Δ → Γ) : Program Δ Γ where
  Label := FixedPairDecodeLabel Δ
  main := .scan
  op
    | .scan => .popInput .finish .afterFirst
    | .afterFirst first => .popInput .finish (.emit first)
    | .emit first second => .pushOutput (decode first second) .scan
    | .finish => .halt

/-- Uniform configuration surface for exact decoder simulations. -/
def fixedPairDecodeCfg {Γ Δ : Type} [Fintype Δ]
    (decode : Δ → Δ → Γ) (label : FixedPairDecodeLabel Δ)
    (buffer : Option Δ) (input : List Δ) (output : List Γ) :
    BuilderCfg (fixedPairDecodeRevProgram decode) :=
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
