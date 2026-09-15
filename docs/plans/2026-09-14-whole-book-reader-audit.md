# Whole-book reader audit

Scope: all 35 chapters, all 136 canonical reader sections, introduction, and their supporting implementation pages. Chapter 1 intentionally owns two expository sections in its single guide. This audits publication completeness against the existing formalization, not new mathematical claims.

1. Compare compiled module declarations and command bodies with published HTML; check every local link including cross-page fragments.
2. Correct the renderer configuration that hides theorem-bearing `set_option ... in` commands. Reuse trusted compiled renderer inputs through a render-only deployment path; never silently recompile during refresh.
3. Include section-owned companion implementations and externally referenced prose results even when the facade already has declarations. Preserve explicit focused selections for exceptionally large facades.
4. Add a permanent full-book audit covering inventory, original command/proof preservation, standalone/chapter correspondence, declaration and source links, duplicate IDs and cross-page anchors. Record every chapter in an audit report.
5. Exercise every chapter and section in the browser, including mobile widths; fix any failures. Review the changes, push, merge, deploy, then verify the whole public reader.

Initial evidence: 173 reader pages contain 152,293 local links; 18 broken link occurrences point to six missing anchors. Nine canonical declarations wrapped by scoped options are omitted by the renderer. Twelve native sections have prose references to declarations on other pages; owned companion modules also require coverage beyond a nonempty-code check.
