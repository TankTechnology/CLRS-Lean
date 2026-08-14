import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BundleCombinators

/-!
# CLRS Section 34.4 - Pure bounded-stack primitives

This module fixes the Boolean-level stack operations used by later symbolic
Cook--Levin transition circuits.  Supported symbols are separated from the
distinguished blank head code, malformed one-hot bundles remain distinct from
the legal empty head, and every operation has one type-correct definition at
height zero and positive heights.

Main results:

- The supported-symbol and optional-head codecs round-trip exactly, while
  optional decoders distinguish malformed outer {lean}`none` from the legal
  empty value {lean}`some none`.
- Definitions {lit}`pushStackBits`, {lit}`peekStackBits`, and
  {lit}`popStackBits` implement fixed-width stack movement, including explicit
  overflow loss and height-zero behavior.
- Theorems {lit}`popStackBits_rawDecodable` and
  {lit}`pushStackBits_rawDecodable` preserve raw one-hot structure under their
  exact premises; {lit}`pushStackBits_not_rawDecodable_of_full` exposes the
  full-stack overflow boundary.

Current gaps:

- These theorems concern raw one-hot stack structure only.  They do not claim
  canonical active/nonblank cell semantics or machine-level push/pop/peek
  correctness; the downstream {lit}`StackSemantics` layer supplies that
  bounded-stack validity bridge.
- Circuit allocation and recursive statement compilation are supplied by
  downstream {lit}`StackCircuits` and {lit}`StatementCircuits`, and
  {lit}`TransitionCircuits` supplies the local step check.  Non-aliasing row
  allocation and verified whole-tableau assembly remain milestone 8F.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Supported-symbol and optional-head codecs -/

/-- A stack symbol accompanied by evidence that it belongs to the fixed
machine's finite program support. -/
abbrev SupportedSymbol (tm : _root_.Turing.FinTM2) (k : tm.K) :=
  {a : tm.Γ k // a ∈ reachableAlphabet tm k}

/-- A bundle indexed only by the nonblank supported symbols of one stack. -/
abbrev SymbolBundle (tm : _root_.Turing.FinTM2) (k : tm.K) (α : Type) :=
  Fin (reachableAlphabet tm k).card → α

/-- Boolean values indexed by the nonblank supported symbols of one stack. -/
abbrev SymbolBits (tm : _root_.Turing.FinTM2) (k : tm.K) :=
  SymbolBundle tm k Bool

/-- A bundle indexed by every supported symbol plus the final blank code. -/
abbrev HeadBundle (tm : _root_.Turing.FinTM2) (k : tm.K) (α : Type) :=
  Fin ((reachableAlphabet tm k).card + 1) → α

/-- Boolean values indexed by supported symbols plus the final blank code. -/
abbrev HeadBits (tm : _root_.Turing.FinTM2) (k : tm.K) :=
  HeadBundle tm k Bool

/-- A supported nonblank symbol or the legal empty-stack head. -/
abbrev SupportedHead (tm : _root_.Turing.FinTM2) (k : tm.K) :=
  Option (SupportedSymbol tm k)

/-- Encode one supported symbol by the canonical finite alphabet equivalence. -/
def encodeSupportedSymbol {tm : _root_.Turing.FinTM2} {k : tm.K}
    (symbol : SupportedSymbol tm k) : Fin (reachableAlphabet tm k).card :=
  alphabetEquivFin tm k symbol

/-- Decode one finite supported-symbol coordinate. -/
def decodeSupportedSymbol {tm : _root_.Turing.FinTM2} {k : tm.K}
    (code : Fin (reachableAlphabet tm k).card) : SupportedSymbol tm k :=
  (alphabetEquivFin tm k).symm code

/-- Decoding a supported-symbol encoding recovers the symbol. -/
@[simp] theorem decodeSupportedSymbol_encode {tm : _root_.Turing.FinTM2}
    {k : tm.K} (symbol : SupportedSymbol tm k) :
    decodeSupportedSymbol (encodeSupportedSymbol symbol) = symbol :=
  (alphabetEquivFin tm k).symm_apply_apply symbol

/-- Re-encoding a supported-symbol coordinate recovers the coordinate. -/
@[simp] theorem encodeSupportedSymbol_decode {tm : _root_.Turing.FinTM2}
    {k : tm.K} (code : Fin (reachableAlphabet tm k).card) :
    encodeSupportedSymbol (decodeSupportedSymbol code) = code :=
  (alphabetEquivFin tm k).apply_symm_apply code

/-- Encode an optional supported head, reserving the final coordinate for the
legal empty head. -/
def encodeHeadCode {tm : _root_.Turing.FinTM2} {k : tm.K}
    (head : SupportedHead tm k) :
    Fin ((reachableAlphabet tm k).card + 1) :=
  match head with
  | some symbol => Fin.castSucc (encodeSupportedSymbol symbol)
  | none => Fin.last (reachableAlphabet tm k).card

/-- Decode the final head coordinate as empty and every earlier coordinate as
a supported nonblank symbol. -/
def decodeHeadCode {tm : _root_.Turing.FinTM2} {k : tm.K}
    (code : Fin ((reachableAlphabet tm k).card + 1)) : SupportedHead tm k :=
  if h : code.val < (reachableAlphabet tm k).card then
    some (decodeSupportedSymbol ⟨code.val, h⟩)
  else none

/-- Decoding an optional-head code recovers the original supported head. -/
@[simp] theorem decodeHeadCode_encode {tm : _root_.Turing.FinTM2} {k : tm.K}
    (head : SupportedHead tm k) : decodeHeadCode (encodeHeadCode head) = head := by
  cases head with
  | none => simp [encodeHeadCode, decodeHeadCode]
  | some symbol => simp [encodeHeadCode, decodeHeadCode, Fin.castSucc]

/-- Re-encoding a decoded optional-head coordinate recovers that coordinate. -/
@[simp] theorem encodeHeadCode_decode {tm : _root_.Turing.FinTM2} {k : tm.K}
    (code : Fin ((reachableAlphabet tm k).card + 1)) :
    encodeHeadCode (decodeHeadCode code) = code := by
  unfold decodeHeadCode
  split
  next h =>
    simp only [encodeHeadCode, encodeSupportedSymbol_decode, Fin.castSucc]
    apply Fin.ext
    rfl
  next h =>
    simp only [encodeHeadCode]
    apply Fin.ext
    simp
    omega

/-- One-hot encode one nonblank supported symbol. -/
def encodeSymbolBits {tm : _root_.Turing.FinTM2} {k : tm.K}
    (symbol : SupportedSymbol tm k) : SymbolBits tm k :=
  encodeOneHot (encodeSupportedSymbol symbol)

/-- Decode a nonblank supported-symbol family, rejecting malformed one-hot
families. -/
def decodeSymbolBits? {tm : _root_.Turing.FinTM2} {k : tm.K}
    (bits : SymbolBits tm k) : Option (SupportedSymbol tm k) :=
  (decodeOneHot bits).map decodeSupportedSymbol

/-- A supported symbol survives one-hot encoding and optional decoding. -/
@[simp] theorem decodeSymbolBits_encode {tm : _root_.Turing.FinTM2} {k : tm.K}
    (symbol : SupportedSymbol tm k) :
    decodeSymbolBits? (encodeSymbolBits symbol) = some symbol := by
  unfold decodeSymbolBits? encodeSymbolBits
  rw [decodeOneHot_encodeOneHot]
  simp

/-- Successful symbol decoding is exactly selection of the encoded symbol
coordinate and uniqueness of that selection. -/
theorem decodeSymbolBits_eq_some_iff {tm : _root_.Turing.FinTM2} {k : tm.K}
    (bits : SymbolBits tm k) (symbol : SupportedSymbol tm k) :
    decodeSymbolBits? bits = some symbol ↔
      bits (encodeSupportedSymbol symbol) = true ∧
        ∀ i, bits i = true → i = encodeSupportedSymbol symbol := by
  constructor
  · intro hdecode
    simp only [decodeSymbolBits?, Option.map_eq_some_iff] at hdecode
    rcases hdecode with ⟨code, hcode, hsymbol⟩
    have hencode : code = encodeSupportedSymbol symbol := by
      rw [← hsymbol, encodeSupportedSymbol_decode]
    subst code
    exact (decodeOneHot_eq_some_iff bits _).mp hcode
  · intro hselected
    have hcode := (decodeOneHot_eq_some_iff bits _).mpr hselected
    simp [decodeSymbolBits?, hcode]

/-- If the reachable support is empty, no nonblank symbol family can decode. -/
theorem decodeSymbolBits_of_card_eq_zero {tm : _root_.Turing.FinTM2} {k : tm.K}
    (bits : SymbolBits tm k)
    (hzero : (reachableAlphabet tm k).card = 0) :
    decodeSymbolBits? bits = none := by
  unfold decodeSymbolBits?
  have hnone : decodeOneHot bits = none := by
    rw [decodeOneHot_eq_none_iff]
    rintro ⟨chosen, _⟩
    have := chosen.isLt
    omega
  simp [hnone]

/-- One-hot encode a supported symbol or the legal empty head. -/
def encodeHeadBits {tm : _root_.Turing.FinTM2} {k : tm.K}
    (head : SupportedHead tm k) : HeadBits tm k :=
  encodeOneHot (encodeHeadCode head)

/-- Decode a head family.  Outer {lean}`none` means malformed one-hot data;
{lean}`some none` is the well-formed empty head. -/
def decodeHeadBits? {tm : _root_.Turing.FinTM2} {k : tm.K}
    (bits : HeadBits tm k) : Option (SupportedHead tm k) :=
  (decodeOneHot bits).map decodeHeadCode

/-- An optional supported head survives one-hot encoding and decoding. -/
@[simp] theorem decodeHeadBits_encode {tm : _root_.Turing.FinTM2} {k : tm.K}
    (head : SupportedHead tm k) :
    decodeHeadBits? (encodeHeadBits head) = some head := by
  unfold decodeHeadBits? encodeHeadBits
  rw [decodeOneHot_encodeOneHot]
  simp

/-- Successful head decoding is exactly selection of the encoded head
coordinate and uniqueness of that selection. -/
theorem decodeHeadBits_eq_some_iff {tm : _root_.Turing.FinTM2} {k : tm.K}
    (bits : HeadBits tm k) (head : SupportedHead tm k) :
    decodeHeadBits? bits = some head ↔
      bits (encodeHeadCode head) = true ∧
        ∀ i, bits i = true → i = encodeHeadCode head := by
  constructor
  · intro hdecode
    simp only [decodeHeadBits?, Option.map_eq_some_iff] at hdecode
    rcases hdecode with ⟨code, hcode, hhead⟩
    have hencode : code = encodeHeadCode head := by
      rw [← hhead, encodeHeadCode_decode]
    subst code
    exact (decodeOneHot_eq_some_iff bits _).mp hcode
  · intro hselected
    have hcode := (decodeOneHot_eq_some_iff bits _).mpr hselected
    simp [decodeHeadBits?, hcode]

/-- Decode a head family to the original machine alphabet while retaining the
outer malformed/valid distinction. -/
def decodeHeadValue? {tm : _root_.Turing.FinTM2} {k : tm.K}
    (bits : HeadBits tm k) : Option (Option (tm.Γ k)) :=
  (decodeHeadBits? bits).map (Option.map Subtype.val)

/-- Encoding a supported optional head and decoding its underlying machine
value gives the corresponding nested option. -/
@[simp] theorem decodeHeadValue_encode {tm : _root_.Turing.FinTM2} {k : tm.K}
    (head : SupportedHead tm k) :
    decodeHeadValue? (encodeHeadBits head) =
      some (head.map Subtype.val) := by
  simp [decodeHeadValue?]

/-- Machine-value head decoding succeeds exactly through a supported head
whose one-hot coordinate is selected uniquely. -/
theorem decodeHeadValue_eq_some_iff {tm : _root_.Turing.FinTM2} {k : tm.K}
    (bits : HeadBits tm k) (value : Option (tm.Γ k)) :
    decodeHeadValue? bits = some value ↔
      ∃ head : SupportedHead tm k,
        value = head.map Subtype.val ∧
        bits (encodeHeadCode head) = true ∧
        ∀ i, bits i = true → i = encodeHeadCode head := by
  constructor
  · intro hdecode
    simp only [decodeHeadValue?, Option.map_eq_some_iff] at hdecode
    rcases hdecode with ⟨head, hhead, hvalue⟩
    exact ⟨head, hvalue.symm, (decodeHeadBits_eq_some_iff bits head).mp hhead⟩
  · rintro ⟨head, rfl, hselected⟩
    simp only [decodeHeadValue?, Option.map_eq_some_iff]
    exact ⟨head, (decodeHeadBits_eq_some_iff bits head).mpr hselected, rfl⟩

/-! ## Pure fixed-width push, peek, and pop -/

/-- Push one nonblank symbol family into a fixed-width stack.

Height and cell coordinates shift upward, the new cell zero receives the
supported-symbol bits with blank forced false, and a full stack loses its top
height flag rather than silently becoming another valid stack. -/
def pushStackBits {tm : _root_.Turing.FinTM2} {k : tm.K}
    (symbol : SymbolBits tm k) : (W : Nat) → StackBits tm W k → StackBits tm W k
  | 0, _ =>
      { height := fun _ => false
        cell := fun i => Fin.elim0 i }
  | _ + 1, stack =>
      { height := Fin.cases false (fun i => stack.height i.castSucc)
        cell := Fin.cases
          (fun code => if h : code.val < (reachableAlphabet tm k).card then
            symbol ⟨code.val, h⟩ else false)
          (fun i => stack.cell i.castSucc) }

/-- A pushed stack never selects height zero. -/
@[simp] theorem pushStackBits_height_zero {tm : _root_.Turing.FinTM2}
    {k : tm.K} {W : Nat} (symbol : SymbolBits tm k)
    (stack : StackBits tm W k) :
    (pushStackBits symbol W stack).height 0 = false := by
  cases W <;> rfl

/-- Every positive pushed height is the preceding old height coordinate. -/
@[simp] theorem pushStackBits_height_succ {tm : _root_.Turing.FinTM2}
    {k : tm.K} {W : Nat} (symbol : SymbolBits tm k)
    (stack : StackBits tm (W + 1) k) (i : Fin (W + 1)) :
    (pushStackBits symbol (W + 1) stack).height i.succ =
      stack.height i.castSucc := by
  rfl

/-- Cell zero receives each supported-symbol bit in the same direction. -/
@[simp] theorem pushStackBits_cell_zero_supported
    {tm : _root_.Turing.FinTM2} {k : tm.K} {W : Nat}
    (symbol : SymbolBits tm k) (stack : StackBits tm (W + 1) k)
    (code : Fin (reachableAlphabet tm k).card) :
    (pushStackBits symbol (W + 1) stack).cell 0 code.castSucc = symbol code := by
  simp [pushStackBits]

/-- Cell zero forces the distinguished blank coordinate to false. -/
@[simp] theorem pushStackBits_cell_zero_blank
    {tm : _root_.Turing.FinTM2} {k : tm.K} {W : Nat}
    (symbol : SymbolBits tm k) (stack : StackBits tm (W + 1) k) :
    (pushStackBits symbol (W + 1) stack).cell 0
      (Fin.last (reachableAlphabet tm k).card) = false := by
  simp [pushStackBits]

/-- Encoding a supported symbol and pushing it writes exactly the corresponding
optional-head encoding into physical cell zero. -/
theorem pushStackBits_cell_zero_encodeSymbol
    {tm : _root_.Turing.FinTM2} {k : tm.K} {W : Nat}
    (symbol : SupportedSymbol tm k) (stack : StackBits tm (W + 1) k) :
    (pushStackBits (encodeSymbolBits symbol) (W + 1) stack).cell 0 =
      encodeHeadBits (some symbol) := by
  funext code
  refine Fin.lastCases ?_ (fun supported => ?_) code
  · simp [pushStackBits, encodeHeadBits, encodeHeadCode, encodeOneHot]
    intro heq
    have hval : (reachableAlphabet tm k).card =
        (encodeSupportedSymbol symbol).val := by
      simpa using congrArg Fin.val heq
    exact (encodeSupportedSymbol symbol).isLt.ne hval.symm
  · simp [pushStackBits, encodeSymbolBits, encodeHeadBits, encodeHeadCode,
      encodeOneHot]

/-- Every higher pushed cell reuses the preceding old physical cell. -/
@[simp] theorem pushStackBits_cell_succ {tm : _root_.Turing.FinTM2}
    {k : tm.K} {W : Nat} (symbol : SymbolBits tm k)
    (stack : StackBits tm (W + 1) k) (i : Fin W) :
    (pushStackBits symbol (W + 1) stack).cell i.succ =
      stack.cell i.castSucc := by
  rfl

/-- Read cell zero at positive width; at width zero return the legal empty-head
one-hot encoding. -/
def peekStackBits {tm : _root_.Turing.FinTM2} {k : tm.K} :
    (W : Nat) → StackBits tm W k → HeadBits tm k
  | 0, _ => encodeHeadBits none
  | _ + 1, stack => stack.cell 0

/-- Peeking a zero-width stack yields the legal empty head. -/
@[simp] theorem peekStackBits_zero {tm : _root_.Turing.FinTM2} {k : tm.K}
    (stack : StackBits tm 0 k) : peekStackBits 0 stack = encodeHeadBits none := rfl

/-- Peeking a positive-width stack returns physical cell zero unchanged. -/
@[simp] theorem peekStackBits_of_pos {tm : _root_.Turing.FinTM2} {k : tm.K}
    {W : Nat} (stack : StackBits tm (W + 1) k) :
    peekStackBits (W + 1) stack = stack.cell 0 := rfl

/-- Pure result of popping one fixed-width stack. -/
structure PopStackBitsResult (tm : _root_.Turing.FinTM2) (W : Nat) (k : tm.K) where
  /-- Stack bits after merging heights zero and one, shifting later heights,
  and shifting cells left. -/
  stack : StackBits tm W k
  /-- The old stack head, or the legal empty head at width zero. -/
  head : HeadBits tm k

/-- Pop one fixed-width stack, returning the old head.

Height zero merges old heights zero and one; higher heights read the next old
coordinate when it exists.  Cells shift left and the last cell becomes blank. -/
def popStackBits {tm : _root_.Turing.FinTM2} {k : tm.K} :
    (W : Nat) → StackBits tm W k → PopStackBitsResult tm W k
  | 0, stack =>
      { stack :=
          { height := fun _ => stack.height 0 || false
            cell := fun i => Fin.elim0 i }
        head := encodeHeadBits none }
  | W + 1, stack =>
      { stack :=
          { height := fun i =>
              if i.val = 0 then stack.height 0 || stack.height 1
              else if hnext : i.val + 1 < W + 2 then
                stack.height ⟨i.val + 1, hnext⟩
              else false
            cell := fun i =>
              if hnext : i.val + 1 < W + 1 then
                stack.cell ⟨i.val + 1, hnext⟩
              else encodeHeadBits none }
        head := stack.cell 0 }

/-- Popping returns precisely the old pure peek result. -/
@[simp] theorem popStackBits_head {tm : _root_.Turing.FinTM2} {k : tm.K}
    {W : Nat} (stack : StackBits tm W k) :
    (popStackBits W stack).head = peekStackBits W stack := by
  cases W <;> rfl

/-- Popped height zero is old height zero OR old height one, with the absent
old height one interpreted as false at width zero. -/
theorem popStackBits_height_zero {tm : _root_.Turing.FinTM2} {k : tm.K}
    {W : Nat} (stack : StackBits tm W k) :
    (popStackBits W stack).stack.height 0 =
      (stack.height 0 ||
        (if h : 0 < W then stack.height ⟨1, by omega⟩ else false)) := by
  cases W with
  | zero => simp [popStackBits]
  | succ W => simp [popStackBits]

/-- A positive popped height reads the next old coordinate when present and
is false at the final height coordinate. -/
theorem popStackBits_height_succ {tm : _root_.Turing.FinTM2} {k : tm.K}
    {W : Nat} (stack : StackBits tm (W + 1) k) (i : Fin (W + 1)) :
    (popStackBits (W + 1) stack).stack.height i.succ =
      if hnext : i.val + 2 < W + 2 then
        stack.height ⟨i.val + 2, hnext⟩ else false := by
  simp only [popStackBits, Fin.val_succ]
  rw [if_neg (by omega)]

/-- A popped cell with a physical successor receives that old successor. -/
theorem popStackBits_cell_of_next {tm : _root_.Turing.FinTM2} {k : tm.K}
    {W : Nat} (stack : StackBits tm (W + 1) k) (i : Fin (W + 1))
    (hnext : i.val + 1 < W + 1) :
    (popStackBits (W + 1) stack).stack.cell i =
      stack.cell ⟨i.val + 1, hnext⟩ := by
  simp only [popStackBits]
  rw [dif_pos (by omega)]

/-- The last physical cell becomes the legal blank one-hot family after pop. -/
@[simp] theorem popStackBits_cell_last {tm : _root_.Turing.FinTM2} {k : tm.K}
    {W : Nat} (stack : StackBits tm (W + 1) k) :
    (popStackBits (W + 1) stack).stack.cell (Fin.last W) =
      encodeHeadBits none := by
  simp [popStackBits]

/-- At width zero, pop preserves the sole height coordinate and has no cells. -/
@[simp] theorem popStackBits_zero_stack {tm : _root_.Turing.FinTM2} {k : tm.K}
    (stack : StackBits tm 0 k) : (popStackBits 0 stack).stack = stack := by
  apply StackBundle.ext
  · funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp [popStackBits]
  · funext i
    exact Fin.elim0 i

/-- At width zero, pop returns the legal empty head. -/
@[simp] theorem popStackBits_zero_head {tm : _root_.Turing.FinTM2} {k : tm.K}
    (stack : StackBits tm 0 k) :
    (popStackBits 0 stack).head = encodeHeadBits none := rfl

/-! ## Raw one-hot preservation -/

namespace StackBits

/-- Raw stack decodability: the height family and every physical cell family
are independently one-hot.  This does not assert active/nonblank canonicality. -/
structure RawDecodable {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (stack : StackBits tm W k) : Prop where
  /-- The bounded height has one selected coordinate. -/
  height : OneHot stack.height
  /-- Every physical cell has one selected supported-or-blank coordinate. -/
  cell : ∀ i, OneHot (stack.cell i)

/-- A fixed-width stack has push capacity exactly when its full-height flag is
false.  For width zero this premise is incompatible with a one-hot height. -/
def HasCapacity {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (stack : StackBits tm W k) : Prop :=
  stack.height (Fin.last W) = false

end StackBits

private theorem symbolHead_oneHot {tm : _root_.Turing.FinTM2} {k : tm.K}
    (symbol : SymbolBits tm k) (hone : OneHot symbol) :
    OneHot (fun code : Fin ((reachableAlphabet tm k).card + 1) =>
      if h : code.val < (reachableAlphabet tm k).card then
        symbol ⟨code.val, h⟩ else false) := by
  refine ⟨(hone.choose).castSucc, ?_, ?_⟩
  · simp [hone.choose_spec.1]
  · intro code htrue
    by_cases h : code.val < (reachableAlphabet tm k).card
    · change (if h' : code.val < (reachableAlphabet tm k).card then
          symbol ⟨code.val, h'⟩ else false) = true at htrue
      rw [dif_pos h] at htrue
      apply Fin.ext
      simpa using congrArg Fin.val (hone.choose_spec.2 ⟨code.val, h⟩ htrue)
    · change (if h' : code.val < (reachableAlphabet tm k).card then
          symbol ⟨code.val, h'⟩ else false) = true at htrue
      rw [dif_neg h] at htrue
      contradiction

/-- A raw positive-width stack has a one-hot peek head. -/
theorem peekStackBits_oneHot {tm : _root_.Turing.FinTM2} {k : tm.K} {W : Nat}
    (stack : StackBits tm (W + 1) k) (hraw : stack.RawDecodable) :
    OneHot (peekStackBits (W + 1) stack) := by
  simpa [peekStackBits] using hraw.cell 0

/-- A zero-width peek is one-hot without any premise because it is the
canonical blank head. -/
theorem peekStackBits_zero_oneHot {tm : _root_.Turing.FinTM2} {k : tm.K}
    (stack : StackBits tm 0 k) : OneHot (peekStackBits 0 stack) := by
  simpa [peekStackBits, encodeHeadBits] using
    oneHot_encodeOneHot (encodeHeadCode (tm := tm) (k := k) none)

private theorem pushHeight_oneHot {tm : _root_.Turing.FinTM2} {k : tm.K}
    {W : Nat} (symbol : SymbolBits tm k) (stack : StackBits tm W k)
    (hone : OneHot stack.height) (hcapacity : stack.HasCapacity) :
    OneHot (pushStackBits symbol W stack).height := by
  cases W with
  | zero =>
      exfalso
      have hchosen := hone.choose_spec.1
      have heq : hone.choose = Fin.last 0 := Fin.eq_zero _
      rw [heq, hcapacity] at hchosen
      contradiction
  | succ W =>
      let chosen : Fin (W + 1) :=
        ⟨hone.choose.val, by
          have hnotLast : hone.choose ≠ Fin.last (W + 1) := by
            intro heq
            have hchosen := hone.choose_spec.1
            rw [heq, hcapacity] at hchosen
            contradiction
          have hne : hone.choose.val ≠ W + 1 := by
            intro hval
            apply hnotLast
            apply Fin.ext
            simpa using hval
          omega⟩
      refine ⟨chosen.succ, ?_, ?_⟩
      · change stack.height chosen.castSucc = true
        have heq : chosen.castSucc = hone.choose := by apply Fin.ext; rfl
        rw [heq]
        exact hone.choose_spec.1
      · intro i hi
        have hizero : i ≠ 0 := by
          intro heq
          subst i
          simp at hi
        obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hizero
        change stack.height j.castSucc = true at hi
        have hj := hone.choose_spec.2 j.castSucc hi
        apply Fin.ext
        simpa [chosen] using congrArg Fin.val hj

/-- Pushing a one-hot symbol into a raw stack with capacity preserves raw
one-hot decodability. -/
theorem pushStackBits_rawDecodable {tm : _root_.Turing.FinTM2} {k : tm.K}
    {W : Nat} (symbol : SymbolBits tm k) (stack : StackBits tm W k)
    (hsymbol : OneHot symbol) (hraw : stack.RawDecodable)
    (hcapacity : stack.HasCapacity) :
    (pushStackBits symbol W stack).RawDecodable := by
  refine ⟨pushHeight_oneHot symbol stack hraw.height hcapacity, ?_⟩
  cases W with
  | zero => intro i; exact Fin.elim0 i
  | succ W =>
      intro i
      by_cases hi : i = 0
      · subst i
        simpa [pushStackBits] using symbolHead_oneHot symbol hsymbol
      · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi
        simpa [pushStackBits] using hraw.cell j.castSucc

/-- If a one-hot old height selects the full coordinate, every pushed height
bit is false.  This overflow fact is independent of symbol one-hotness. -/
theorem pushStackBits_height_eq_false_of_full
    {tm : _root_.Turing.FinTM2} {k : tm.K} {W : Nat}
    (symbol : SymbolBits tm k) (stack : StackBits tm W k)
    (hone : OneHot stack.height)
    (hfull : stack.height (Fin.last W) = true) :
    ∀ i, (pushStackBits symbol W stack).height i = false := by
  intro i
  cases W with
  | zero => rfl
  | succ W =>
      by_cases hi : i = 0
      · subst i
        rfl
      · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi
        change stack.height j.castSucc = false
        apply Bool.eq_false_of_not_eq_true
        intro hj
        have heq := hone.choose_spec.2 j.castSucc hj
        have hlast := hone.choose_spec.2 (Fin.last (W + 1)) hfull
        have : j.castSucc = Fin.last (W + 1) := heq.trans hlast.symm
        have hval := congrArg Fin.val this
        simp at hval
        omega

/-- Pushing a full one-hot stack cannot produce raw one-hot stack data,
regardless of the supplied symbol family. -/
theorem pushStackBits_not_rawDecodable_of_full
    {tm : _root_.Turing.FinTM2} {k : tm.K} {W : Nat}
    (symbol : SymbolBits tm k) (stack : StackBits tm W k)
    (hone : OneHot stack.height)
    (hfull : stack.height (Fin.last W) = true) :
    ¬ (pushStackBits symbol W stack).RawDecodable := by
  intro hraw
  rcases hraw.height with ⟨chosen, hchosen, _⟩
  rw [pushStackBits_height_eq_false_of_full symbol stack hone hfull chosen] at hchosen
  contradiction

private theorem popHeight_oneHot {tm : _root_.Turing.FinTM2} {k : tm.K}
    {W : Nat} (stack : StackBits tm W k) (hone : OneHot stack.height) :
    OneHot (popStackBits W stack).stack.height := by
  cases W with
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · have hbit := hone.choose_spec.1
        have heq : hone.choose = (0 : Fin 1) := Fin.eq_zero _
        rw [heq] at hbit
        simpa [popStackBits] using hbit
      · intro i _
        exact Fin.eq_zero i
  | succ W =>
      by_cases hsmall : hone.choose.val ≤ 1
      · refine ⟨0, ?_, ?_⟩
        · have hcases : hone.choose.val = 0 ∨ hone.choose.val = 1 := by omega
          rcases hcases with hzero | honeVal
          · have heq : hone.choose = (0 : Fin (W + 2)) := Fin.ext hzero
            have hbit := hone.choose_spec.1
            rw [heq] at hbit
            simp [popStackBits, hbit]
          · have heq : hone.choose = (1 : Fin (W + 2)) := by
              apply Fin.ext
              simpa using honeVal
            have hbit := hone.choose_spec.1
            rw [heq] at hbit
            simp [popStackBits, hbit]
        · intro i hi
          by_contra hine
          have hizero : i.val ≠ 0 := by
            intro hval
            apply hine
            apply Fin.ext
            simpa using hval
          simp only [popStackBits] at hi
          rw [if_neg hizero] at hi
          by_cases hnext : i.val + 1 < W + 2
          · rw [dif_pos hnext] at hi
            have heq := hone.choose_spec.2 ⟨i.val + 1, hnext⟩ hi
            have hval : i.val + 1 = hone.choose.val := by
              simpa using congrArg Fin.val heq
            omega
          · rw [dif_neg hnext] at hi
            contradiction
      · let chosen : Fin (W + 2) :=
          ⟨hone.choose.val - 1, by omega⟩
        refine ⟨chosen, ?_, ?_⟩
        · have hchosenZero : chosen.val ≠ 0 := by
            simp only [chosen]
            omega
          have hnext : chosen.val + 1 < W + 2 := by
            simp only [chosen]
            omega
          simp only [popStackBits]
          rw [if_neg hchosenZero, dif_pos hnext]
          have heq : (⟨chosen.val + 1, hnext⟩ : Fin (W + 2)) =
              hone.choose := by
            apply Fin.ext
            simp only [chosen]
            omega
          rw [heq]
          exact hone.choose_spec.1
        · intro i hi
          simp only [popStackBits] at hi
          by_cases hizero : i.val = 0
          · rw [if_pos hizero] at hi
            have hzeroNe : (0 : Fin (W + 2)) ≠ hone.choose := by
              intro heq
              have hval := congrArg Fin.val heq
              simp at hval
              omega
            have honeNe : (1 : Fin (W + 2)) ≠ hone.choose := by
              intro heq
              have hval := congrArg Fin.val heq
              simp at hval
              omega
            have hzero : stack.height 0 = false :=
              Bool.eq_false_of_not_eq_true
                (fun htrue => hzeroNe (hone.choose_spec.2 0 htrue))
            have hone' : stack.height 1 = false :=
              Bool.eq_false_of_not_eq_true
                (fun htrue => honeNe (hone.choose_spec.2 1 htrue))
            rw [hzero, hone'] at hi
            contradiction
          · rw [if_neg hizero] at hi
            by_cases hnext : i.val + 1 < W + 2
            · rw [dif_pos hnext] at hi
              have heq := hone.choose_spec.2 ⟨i.val + 1, hnext⟩ hi
              apply Fin.ext
              have hval : i.val + 1 = hone.choose.val := by
                simpa using congrArg Fin.val heq
              simp only [chosen]
              omega
            · rw [dif_neg hnext] at hi
              contradiction

/-- Pop preserves raw one-hot height and cell structure. -/
theorem popStackBits_rawDecodable {tm : _root_.Turing.FinTM2} {k : tm.K}
    {W : Nat} (stack : StackBits tm W k) (hraw : stack.RawDecodable) :
    (popStackBits W stack).stack.RawDecodable := by
  refine ⟨popHeight_oneHot stack hraw.height, ?_⟩
  cases W with
  | zero => intro i; exact Fin.elim0 i
  | succ W =>
      intro i
      by_cases hnext : i.val + 1 < W + 1
      · simp only [popStackBits]
        rw [dif_pos hnext]
        exact hraw.cell ⟨i.val + 1, hnext⟩
      · simp only [popStackBits]
        rw [dif_neg hnext]
        simpa [encodeHeadBits] using
          oneHot_encodeOneHot
            (encodeHeadCode (tm := tm) (k := k) none)

end

end CLRS.Chapter34.Turing.CookLevin
