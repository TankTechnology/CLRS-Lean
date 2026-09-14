# Show concrete definitions and proofs in reader sections

The chapter assembler currently embeds facade prose without the imported implementation. The public reader audit found 25 of 136 canonical sections with no declaration anchors, including 16.3.

- [x] Enrich standalone facade pages from existing verified rendered implementation pages before composing chapters.
- [x] Preserve full definition/theorem code blocks and proof bodies, source links, unique anchors, and same-page result links.
- [x] Include the potential-method trace, prefix sum, amortized cost, telescoping proof, and upper-bound proof in 16.3.
- [x] Select public result blocks for the two very large Chapter 34 facades; expose source links for supporting implementation.
- [x] Add coverage checks so a facade cannot publish only a result list again.
- [x] Verify all 25 affected sections, combined chapters, duplicate IDs, links, browser navigation, mobile layout, and no-JavaScript reading.
Rollout: push, merge, deploy through presentation refresh with no Lean compilation, and verify live 16.3.

The existing Lean definitions and proofs remain the authoritative source. This change exposes the already rendered code; it does not invent or reprove results.

Local validation: all 136 sections checked; 25 enriched with 2,456 imported declaration anchors and 31 local result links. The largest composed chapter is 7.24 MiB. Standalone/chapter potential-method proof navigation, desktop/mobile rendering, and no-JavaScript proof reading passed.
