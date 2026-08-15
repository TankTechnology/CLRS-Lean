# Ch34 Raw One-Hot Family Controller Plan

**Goal:** Execute every arithmetic row one-hot group with one fixed
delimiter-driven PolyBuilder program, preserving exact semantic gate order and
leaving a redirectable boundary for whole-row composition.

## Acceptance boundary

- [x] Refactor the affine exactly-one kernel to expose a clean public halt-label
      exit while preserving the original standalone run theorem.
- [x] Define a finite-control family program whose runtime frame carries
      `start`, `start + 2`, `rowBase`, and `count` in unary.
- [x] Prove exact loading, core execution, loop-back, family output, and both
      standalone and redirectable termination theorems.
- [x] Prove a uniform quadratic bound in the delimiter-bearing family input
      length.
- [x] Instantiate the family with all arithmetic label, state, height, and
      stack-cell one-hot groups and prove exact agreement with the canonical
      raw-row stream.
- [x] Add focused interface and axiom tests; register the module in the chapter
      import surface and literate site navigation.

## Known failed or rejected routes

- Storing the runtime group list in a control label is not a fixed TM2: the
  number and values of groups depend on runtime dimensions.
- Reusing independently halting group runs cannot compose a family because the
  machine has no transition after the first halt.  The accepted refactor stops
  first at the kernel's public halt label and lets the family program redirect
  it.
- Leaving the frame separator buffered while entering the exactly-one kernel
  breaks the kernel-lifting invariant, whose source and target configurations
  require the borrowed buffers and test bit to be normalized.
- Moving `count` directly onto `work₁` before clearing the fourth-field
  separator fails: the only safe buffer-clear instruction needs `work₁` empty.
  The accepted loader stages count ticks on `work₂`, clears the buffer with
  empty `work₁`, then transfers the ticks.
- Treating list equality as execution is insufficient.  The accepted interface
  includes an exact `EvalsToInTime` theorem and an explicit runtime bound for
  the single fixed controller.

## Completed downstream link

`AffineValidityRow` now links `affineExactlyOneFamily_runToFinish` to the
arithmetic halted/label agreement controller and then to
`affineValidityTail_run`.  The continuous arithmetic theorem outputs exactly
`validityRowGateStreamAt` and carries a quadratic bound over its concrete
runtime frame. `AffineValidityRowFamily` now supplies that formerly open
iteration boundary: one fixed marked-frame controller emits exactly
`validityGateStreamAt` for all tableau rows and has an explicit quadratic
runtime bound. The next open generator boundary is the transition family.
