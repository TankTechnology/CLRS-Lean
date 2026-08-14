import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne

/-!
# Affine sequential exactly-one traces

This file lifts the zero-based sequential exactly-one trace to an arbitrary
gate start and a consecutive source-wire interval.  The explicit arithmetic
gate list is the specification consumed by the contextual concrete runner.

Main results:

- `affineSequentialExactlyOneGateStream_eq_trace`: the public stream is the
  canonical semantic exactly-one encoding.
- `affineSequentialExactlyOneGateList_eq_trace`: the explicit arithmetic
  chunks are exactly the canonical semantic gate trace.
-/

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- Consecutive source wires beginning at `rowBase`. -/
def affineSequentialExactlyOneWires (rowBase count : Nat) : List Nat :=
  (List.range count).map (fun wire => rowBase + wire)

/-- Exact forward encoding of an affine sequential exactly-one trace. -/
def affineSequentialExactlyOneGateStream
    (start rowBase count : Nat) : List CircuitSym :=
  (exactlyOneGateTrace start
    (affineSequentialExactlyOneWires rowBase count)).gates.flatMap
      encodeCircuitGate

/-- The public affine stream is definitionally the semantic trace. -/
theorem affineSequentialExactlyOneGateStream_eq_trace
    (start rowBase count : Nat) :
    affineSequentialExactlyOneGateStream start rowBase count =
      (exactlyOneGateTrace start
        ((List.range count).map (fun wire => rowBase + wire))).gates.flatMap
          encodeCircuitGate := by
  rfl

namespace AffineExactlyOne

/-- First three-gate update from the two affine false seeds. -/
def firstChunk (start wire : Nat) : List CircuitGate :=
  [.and start wire, .or (start + 1) (start + 2), .or start wire]

/-- Later three-gate update after `phase` source wires have been scanned. -/
def laterChunk (start phase wire : Nat) : List CircuitGate :=
  [.and (start + 3 * phase + 1) wire,
    .or (start + 3 * phase) (start + 3 * phase + 2),
    .or (start + 3 * phase + 1) wire]

/-- Current seen-wire index after `phase` updates. -/
def seen (start phase : Nat) : Nat :=
  if phase = 0 then start else start + 3 * phase + 1

/-- Current duplicate-wire index after `phase` updates. -/
def duplicate (start phase : Nat) : Nat :=
  if phase = 0 then start + 1 else start + 3 * phase

/-- One affine scan chunk, including the special first update. -/
def chunk (start phase wire : Nat) : List CircuitGate :=
  if phase = 0 then firstChunk start wire else laterChunk start phase wire

/-- Tail-first affine chunks for `remaining` consecutive source wires. -/
def chunksFrom (start rowBase : Nat) : Nat → Nat → List CircuitGate
  | _, 0 => []
  | phase, remaining + 1 =>
      chunk start phase (rowBase + remaining) ++
        chunksFrom start rowBase (phase + 1) remaining

private theorem arithmeticScanFrom_affineRange
    (start rowBase phase remaining : Nat)
    (scan : ExactlyOneArithmeticScan)
    (hgates : scan.gates.length = 3 * phase + 2)
    (hseen : scan.seen = seen start phase)
    (hduplicate : scan.duplicate = duplicate start phase) :
    let result := (affineSequentialExactlyOneWires rowBase remaining).reverse.foldl
      (exactlyOneArithmeticStep start) scan
    result.gates = scan.gates ++
        chunksFrom start rowBase phase remaining ∧
      result.gates.length = 3 * (phase + remaining) + 2 ∧
      result.seen = seen start (phase + remaining) ∧
      result.duplicate = duplicate start (phase + remaining) := by
  induction remaining generalizing phase scan with
  | zero =>
      simp [affineSequentialExactlyOneWires, chunksFrom, hgates, hseen,
        hduplicate]
  | succ remaining ih =>
      have hrange :
          (affineSequentialExactlyOneWires rowBase (remaining + 1)).reverse =
            (rowBase + remaining) ::
              (affineSequentialExactlyOneWires rowBase remaining).reverse := by
        simp [affineSequentialExactlyOneWires, List.range_succ,
          List.reverse_append]
      rw [hrange]
      simp only [List.foldl]
      let nextScan := exactlyOneArithmeticStep start scan (rowBase + remaining)
      have hnextGates : nextScan.gates = scan.gates ++
          chunk start phase (rowBase + remaining) := by
        unfold nextScan exactlyOneArithmeticStep chunk
        rw [hgates, hseen, hduplicate]
        by_cases hphase : phase = 0
        · subst phase
          rfl
        · simp only [hphase, ↓reduceIte, laterChunk, seen, duplicate]
          simp [Nat.add_left_comm, Nat.add_comm]
      have hnextLength : nextScan.gates.length =
          3 * (phase + 1) + 2 := by
        rw [hnextGates, List.length_append]
        unfold chunk
        by_cases hphase : phase = 0
        · subst phase
          have hg : scan.gates.length = 2 := by omega
          simp [firstChunk, hg]
        · simp [hphase, laterChunk, hgates]
          omega
      have hnextSeen : nextScan.seen = seen start (phase + 1) := by
        unfold nextScan exactlyOneArithmeticStep seen
        rw [hgates]
        rw [if_neg (by omega : phase + 1 ≠ 0)]
        change start + (3 * phase + 2) + 2 =
          start + 3 * (phase + 1) + 1
        omega
      have hnextDuplicate :
          nextScan.duplicate = duplicate start (phase + 1) := by
        unfold nextScan exactlyOneArithmeticStep duplicate
        rw [hgates]
        rw [if_neg (by omega : phase + 1 ≠ 0)]
        change start + (3 * phase + 2) + 1 = start + 3 * (phase + 1)
        omega
      rcases ih (phase + 1) nextScan hnextLength hnextSeen hnextDuplicate with
        ⟨hresultGates, hresultLength, hresultSeen, hresultDuplicate⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hresultGates, hnextGates]
        simp [chunksFrom, List.append_assoc]
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hresultLength
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hresultSeen
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hresultDuplicate

private theorem arithmeticScan_affineRange (start rowBase count : Nat) :
    let scan := exactlyOneArithmeticScan start
      (affineSequentialExactlyOneWires rowBase count)
    scan.gates = [.const false, .const false] ++
        chunksFrom start rowBase 0 count ∧
      scan.gates.length = 3 * count + 2 ∧
      scan.seen = seen start count ∧
      scan.duplicate = duplicate start count := by
  simpa [exactlyOneArithmeticScan, affineSequentialExactlyOneWires, seen,
    duplicate] using
    arithmeticScanFrom_affineRange start rowBase 0 count
      ({ gates := [.const false, .const false],
          seen := start, duplicate := start + 1 } : ExactlyOneArithmeticScan)
      rfl rfl rfl

/-- Explicit arithmetic gate list for the complete affine constraint. -/
def gateList (start rowBase count : Nat) : List CircuitGate :=
  [.const false, .const false] ++ chunksFrom start rowBase 0 count ++
    [.not (duplicate start count),
      .and (seen start count) (start + 3 * count + 2)]

end AffineExactlyOne

/-- The explicit affine chunks are exactly the semantic exactly-one trace. -/
theorem affineSequentialExactlyOneGateList_eq_trace
    (start rowBase count : Nat) :
    AffineExactlyOne.gateList start rowBase count =
      (exactlyOneGateTrace start
        (affineSequentialExactlyOneWires rowBase count)).gates := by
  rw [exactlyOneGateTrace_gates_eq_arithmeticScan]
  rcases AffineExactlyOne.arithmeticScan_affineRange start rowBase count with
    ⟨hgates, hlength, hseen, hduplicate⟩
  simp only [AffineExactlyOne.gateList]
  rw [hduplicate, hseen, hlength, hgates]
  simp [Nat.add_assoc]

end CLRS.Chapter34.Turing.PolyBuilder
