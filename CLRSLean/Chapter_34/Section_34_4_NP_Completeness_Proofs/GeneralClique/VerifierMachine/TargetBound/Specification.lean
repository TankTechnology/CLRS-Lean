import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.TargetBound.Basic

/-!
# General CLIQUE verifier: raw target-bound specification

The controller's recursive Boolean semantics agrees with an explicit scan of
the first two unary fields on every raw input, not only on encoder output.
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.TargetBound

private theorem targetResult_eq_scan (count : Nat) (input : List CliqueSym) :
    targetResult count input =
      match ticksThroughSeparator input with
      | none => false
      | some (targetSize, _) => decide (targetSize ≤ count) := by
  induction input generalizing count with
  | nil => simp [targetResult, ticksThroughSeparator]
  | cons symbol input ih =>
      cases symbol <;>
        try simp [targetResult, ticksThroughSeparator, ih]
      case tick =>
        cases count with
        | zero =>
            cases hscan : ticksThroughSeparator input with
            | none => simp [targetResult, ticksThroughSeparator, hscan]
            | some result =>
                rcases result with ⟨targetSize, rest⟩
                simp [targetResult, ticksThroughSeparator, hscan]
        | succ count =>
            cases hscan : ticksThroughSeparator input with
            | none =>
                simpa [targetResult, ticksThroughSeparator, hscan] using
                  ih count
            | some result =>
                rcases result with ⟨targetSize, rest⟩
                simpa [targetResult, ticksThroughSeparator, hscan] using
                  ih count

private theorem vertexResult_eq_scan (count : Nat) (input : List CliqueSym) :
    vertexResult count input =
      match ticksThroughSeparator input with
      | none => false
      | some (vertexTicks, targetField) =>
          targetResult (count + vertexTicks) targetField := by
  induction input generalizing count with
  | nil => simp [vertexResult, ticksThroughSeparator]
  | cons symbol input ih =>
      cases symbol <;>
        try simp [vertexResult, ticksThroughSeparator, ih]
      case tick =>
        cases hscan : ticksThroughSeparator input with
        | none =>
            simpa [vertexResult, ticksThroughSeparator, hscan] using
              ih (count + 1)
        | some result =>
            rcases result with ⟨vertexTicks, targetField⟩
            simpa [vertexResult, ticksThroughSeparator, hscan,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              ih (count + 1)

/-- Exact raw-string characterization of the Boolean computed by the fixed
target-bound machine. -/
theorem targetBoundPass_eq_scan (certificate input : List CliqueSym) :
    targetBoundPass certificate input =
      match input with
      | [] => false
      | _ :: fields =>
          match ticksThroughSeparator fields with
          | none => false
          | some (vertexCount, targetField) =>
              match ticksThroughSeparator targetField with
              | none => false
              | some (targetSize, _) => decide (targetSize ≤ vertexCount) := by
  cases input with
  | nil => rfl
  | cons marker fields =>
      simp only [targetBoundPass]
      rw [vertexResult_eq_scan]
      cases hvertices : ticksThroughSeparator fields with
      | none => simp [hvertices]
      | some result =>
          rcases result with ⟨vertexCount, targetField⟩
          simp only [hvertices, Nat.zero_add]
          rw [targetResult_eq_scan]

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.TargetBound
