# Inline Chapter Reader Implementation Plan

**Goal:** Show direct section proofs on every fourth-edition chapter page and
remove the navigation state layout shift.

### Task 1: Specify chapter composition

- [x] Add failing tests for ordered direct-section embedding.
- [x] Require same-page section anchors and preserved standalone pages.
- [x] Require deterministic, idempotent output and structural errors.

### Task 2: Implement chapter composition

- [x] Add a focused HTML composition module.
- [x] Integrate composition into the shared Pages/local preparation command.
- [x] Add reader styling for embedded section boundaries.

### Task 3: Stabilize first paint

- [x] Add failing tests for closed static disclosures and a pre-paint bootstrap.
- [x] Align generated HTML with the default navigation state.
- [x] Reveal the navigation only after saved state has been applied.

### Task 4: Verify and publish

- [x] Run repository and Lean checks.
- [x] Build the Pages-equivalent site and verify all combined chapter pages.
- [x] Run desktop and mobile browser tests for content, URLs, console errors,
      overflow, and layout shift.
- [ ] Merge to `main`, push, deploy Pages, and verify the public site.
