# Chapter 34 Transition Equality Module Split Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that the fixed-TM2-generated transition equality frame stream is byte-for-byte the canonical `transitionScriptFromSeed ... .eqFrames` stream, using small independently compilable Lean modules.

**Architecture:** Separate natural interval and stack-offset arithmetic from explicit slot enumeration, then relate runtime progressions to that enumeration, and only in the final module unfold the canonical transition-script decomposition. `GeneratorTransitionEqAlignment.lean` remains a facade and `GeneratorTransitionInputCompiler.lean` imports only that facade.

**Tech Stack:** Lean 4, Mathlib `List`/`Fin` arithmetic, CLRS-Lean Cook--Levin circuitization, focused `lake env lean` interface tests.

---

### Task 1: Fixed-stack interval arithmetic

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorTransitionEqSlotIntervals.lean`
- Modify: `Tests/Chapter_34_CookLevin_TransitionInputCompiler.lean`

- [ ] **Step 1: Add failing public interface checks**

```lean
#check transitionEqOfFnAdd_eq_range
#check transitionEq_cfgStackBitOffset_equiv_symm
#check transitionEqStackIntervals_eq_range
```

- [ ] **Step 2: Verify the checks fail for missing declarations**

Run:

```bash
lake env lean Tests/Chapter_34_CookLevin_TransitionInputCompiler.lean
```

Expected: failure naming `transitionEqOfFnAdd_eq_range` as unknown.

- [ ] **Step 3: Implement interval and prefix-sum theorems**

Create a focused module importing `GeneratorTransitionEqSource` and expose:

```lean
theorem transitionEqOfFnAdd_eq_range (base count : Nat) :
    (List.ofFn fun index : Fin count => base + index.val) =
      List.range' base count

theorem transitionEq_cfgStackBitOffset_equiv_symm
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (position : Fin (arithmeticStackCount tm)) :
    cfgStackBitOffset tm height
        ((arithmeticStackEquiv tm).symm position) =
      ∑ prior : Fin position.val,
        cfgStackBitWidth tm height
          ((arithmeticStackEquiv tm).symm
            (Fin.castLE position.isLt.le prior))

theorem transitionEqStackIntervals_eq_range
    (tm : _root_.Turing.FinTM2) (height base : Nat) :
    (List.ofFn fun position : Fin (arithmeticStackCount tm) =>
      List.range' (base + cfgStackBitOffset tm height
        ((arithmeticStackEquiv tm).symm position))
        (cfgStackBitWidth tm height
          ((arithmeticStackEquiv tm).symm position))).flatten =
      List.range' base
        ((List.ofFn fun position : Fin (arithmeticStackCount tm) =>
          cfgStackBitWidth tm height
            ((arithmeticStackEquiv tm).symm position)).sum)
```

Prove the last theorem by induction over the `List.ofFn` prefix, using
`List.range'_append` and the exact stack-offset sum theorem.

- [ ] **Step 4: Verify the small module and focused interface**

```bash
lake env lean CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorTransitionEqSlotIntervals.lean
lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqSlotIntervals
lake env lean Tests/Chapter_34_CookLevin_TransitionInputCompiler.lean
```

Expected: all three declarations elaborate and the commands exit zero.

- [ ] **Step 5: Audit, commit, and push**

```bash
git diff --check
rg -n '\b(sorry|admit)\b' CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorTransitionEqSlotIntervals.lean Tests/Chapter_34_CookLevin_TransitionInputCompiler.lean
git add CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorTransitionEqSlotIntervals.lean Tests/Chapter_34_CookLevin_TransitionInputCompiler.lean
git commit -m "feat(ch34): enumerate transition equality intervals"
git push origin codex/ch34-validity-row-source
```

Expected: no unfinished markers and one pushed checkpoint.

### Task 2: Canonical public-slot enumeration

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorTransitionEqSlotEnumeration.lean`
- Modify: `Tests/Chapter_34_CookLevin_TransitionInputCompiler.lean`

- [ ] **Step 1: Add failing checks**

```lean
#check transitionEqPrefixSlots_values
#check transitionEqStackSlots_values
#check transitionEqPublicSlots_values
#check transitionEqPublicSlots_eq_canonical
```

- [ ] **Step 2: Verify the expected unknown declaration**

Run the focused test and require failure at `transitionEqPrefixSlots_values`.

- [ ] **Step 3: Define the three explicit slot lists**

```lean
def transitionEqPrefixSlots (tm : _root_.Turing.FinTM2) (height : Nat) :
    List (CfgSlot tm height)

def transitionEqStackSlots (tm : _root_.Turing.FinTM2) (height : Nat)
    (k : tm.K) : List (CfgSlot tm height)

def transitionEqPublicSlots (tm : _root_.Turing.FinTM2) (height : Nat) :
    List (CfgSlot tm height)
```

The prefix list is halted/labels/states. Each stack list is heights followed by
cell-major/symbol-minor cells. The public list follows `arithmeticStackEquiv`.

- [ ] **Step 4: Prove local and global numeric order**

Use `cfgSlotEquivFin_*_val`, `List.ofFn_mul`, and Task 1 intervals to prove:

```lean
theorem transitionEqPublicSlots_values
    (tm : _root_.Turing.FinTM2) (height : Nat) :
    (transitionEqPublicSlots tm height).map
        (fun slot => (cfgSlotEquivFin tm height slot).val) =
      List.range' 0 (cfgBitCount tm height)

theorem transitionEqPublicSlots_eq_canonical
    (tm : _root_.Turing.FinTM2) (height : Nat) :
    transitionEqPublicSlots tm height =
      List.ofFn fun coordinate : Fin (cfgBitCount tm height) =>
        (cfgSlotEquivFin tm height).symm coordinate
```

Derive the second theorem by mapping both lists through the injective
`cfgSlotEquivFin` and using the numeric-order theorem.

- [ ] **Step 5: Verify, audit, commit, and push**

Run the new module, focused interface test, `git diff --check`, unfinished-proof
scan, and `#print axioms` checks; commit as:

```bash
git commit -m "feat(ch34): align transition equality slots"
git push origin codex/ch34-validity-row-source
```

### Task 3: Runtime segment-to-slot alignment

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorTransitionEqSegmentAlignment.lean`
- Modify: `Tests/Chapter_34_CookLevin_TransitionInputCompiler.lean`

- [ ] **Step 1: Add failing checks**

```lean
#check transitionEqProgressionRows_eq_slots
#check transitionEqCoordinateSeeds_eq_slots
#check transitionEqGeneratedFrames_eq_slotFrames
```

- [ ] **Step 2: Verify failure at the first missing theorem**

Run the focused test and confirm the unknown identifier is
`transitionEqProgressionRows_eq_slots`.

- [ ] **Step 3: Prove one-segment progression semantics**

Use `affineUnaryTripleProgressionRows_eq_ofFn` together with
`transitionEqSegmentProgression_base₁`, `base₂`, and `base₃` to prove each row
has the exact carry, arithmetic final-mux source, and next-public-row source at
the corresponding segment offset.

- [ ] **Step 4: Concatenate segments in explicit slot order**

Prove:

```lean
theorem transitionEqCoordinateSeeds_eq_slots
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    transitionEqCoordinateSeeds tm seed =
      (transitionEqPublicSlots tm seed.height).map fun slot =>
        { first := transitionEqStart tm seed.height seed.start +
            6 * (cfgSlotEquivFin tm seed.height slot).val
          second := narrowCfgWireProjection
            (transitionDispatchOutputWires tm seed) slot
          third := seed.rowBase + cfgBitCount tm seed.height +
            (cfgSlotEquivFin tm seed.height slot).val }
```

Then map `transitionEqCoordinateFrame` over both sides to obtain
`transitionEqGeneratedFrames_eq_slotFrames`.

- [ ] **Step 5: Verify, audit, commit, and push**

Build only this module during repair, then run the focused interface test and
the standard diff/unfinished-proof/axiom gates. Commit as:

```bash
git commit -m "feat(ch34): align equality segments with tableau slots"
git push origin codex/ch34-validity-row-source
```

### Task 4: Canonical script equality and verifier family lift

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorTransitionEqCanonicalAlignment.lean`
- Replace: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorTransitionEqAlignment.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorTransitionInputCompiler.lean`
- Modify: `Tests/Chapter_34_CookLevin_TransitionInputCompiler.lean`

- [ ] **Step 1: Add failing headline checks**

```lean
#check transitionEqGeneratedFrames_eq_script
#check verifierTransitionEqInvocationInput_eq_scripts
```

- [ ] **Step 2: Verify failure at `transitionEqGeneratedFrames_eq_script`**

Run the focused test before creating the canonical-alignment module.

- [ ] **Step 3: Prove one-row canonical frame equality**

Unfold only `transitionScriptFromSeed`, `transitionScriptOfDecomposition`, and
`transitionScriptDecompositionFromSeed`. Rewrite its three `List.ofFn` operand
views using `transitionEqPublicSlots_eq_canonical` and the Task 3 slot-frame
theorem. Prove:

```lean
theorem transitionEqGeneratedFrames_eq_script
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    transitionEqGeneratedFrames tm seed =
      (transitionScriptFromSeed tm seed
        (seed.rowBase + cfgBitCount tm seed.height)).eqFrames
```

- [ ] **Step 4: Lift byte equality to all verifier rows**

Combine the one-row theorem with
`verifierTransitionEqInvocationInput_eq_generatedFrames` and
`verifierTransitionRowSeeds_height_eq`:

```lean
theorem verifierTransitionEqInvocationInput_eq_scripts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionEqInvocationInput W input =
      encodeAffineEqFinFrames
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionScriptFromSeed W.machine.tm seed
            (seed.rowBase + cfgBitCount W.machine.tm seed.height)).eqFrames)
```

- [ ] **Step 5: Replace the facade and verify the chapter root**

Make `GeneratorTransitionEqAlignment.lean` import only
`GeneratorTransitionEqCanonicalAlignment`. Keep
`GeneratorTransitionInputCompiler.lean` importing the facade. Run:

```bash
lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionInputCompiler
lake env lean Tests/Chapter_34_CookLevin_TransitionInputCompiler.lean
lake env lean CLRSLean/Chapter_34.lean
git diff --check
```

Expected: all exit zero; axiom output contains only accepted Mathlib foundations
such as `propext`, `Classical.choice`, and `Quot.sound`.

- [ ] **Step 6: Commit and push the closed alignment chain**

```bash
git add CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorTransitionEqCanonicalAlignment.lean CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorTransitionEqAlignment.lean CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorTransitionInputCompiler.lean Tests/Chapter_34_CookLevin_TransitionInputCompiler.lean
git commit -m "feat(ch34): align generated transition equality frames"
git push origin codex/ch34-validity-row-source
```

### Task 5: Transition-family continuation

**Files:**
- Modify: `docs/superpowers/plans/2026-08-16-ch34-cook-levin-textbook-closure.md`
- Create or modify the next focused `GeneratorTransition*` module selected by the closed equality interface.

- [ ] **Step 1: Record equality alignment as complete**

Mark only the equality-frame source boundary complete and retain the continuous
transition-family and full verifier-circuit generator as open.

- [ ] **Step 2: Select the next exact theorem**

The next implementation theorem is the byte-exact one-row packet equality:

```lean
transitionRowGeneratedUnaryInput tm seed =
  transitionSeedLocalUnaryInput tm seed
```

It must join dispatch, narrowing, equality, final-and, and the row terminator.

- [ ] **Step 3: Start the next red-green checkpoint**

Add the theorem name to the focused transition-input test, confirm the expected
unknown-identifier failure, and create the next small module rather than adding
the theorem to any of the four alignment files.
