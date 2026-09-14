# Book presentation release package

## What this package introduces

An ivory-and-green frontispiece, two original algorithm illustrations, a clearer
contents layout, sequential links for all 35 chapters, and illustrated closing
matter. Existing source prose, scope statements and theorem anchors are retained.
The previous public reader release is `8419ff26`; this package is a new
presentation revision with no changes to Lean definitions or proofs.

## Launch material

- [English announcement and two replies](2026-09-13-twitter-draft.md).
- [1200-by-630 sharing image](../literate/assets/book-social.png).
- [Editable social-card source](assets/share-card.html).
- [Desktop cover](assets/book-cover-desktop.png).
- [Contents](assets/book-contents.png).
- [Insertion-sort proof](assets/book-proof.png).
- [Machine-learning chapter](assets/book-chapter-33.png).
- [Closing matter](assets/book-closing.png).
- [Mobile cover](assets/book-cover-mobile.png).
- [Dark cover](assets/book-cover-dark.png).
- [Actual reading walkthrough, MP4](assets/book-walkthrough.mp4).

The main post and its two replies are approximately 226, 240 and 194 characters
respectively when each URL is counted as 23 characters. The main image avoids
an evolving theorem count. The reply's 1,689 selected entries must be checked
against the ledger at the final release snapshot.

## Completion boundary

The milestone is the reviewed selected proof inventory spanning 35 fourth-edition
chapter guides. Chapter 1 is expository. The project does not claim to reproduce
every textbook theorem, exercise or concrete machine implementation. Chapter
scope notes and the checked Lean statements remain the authoritative boundary.

## Release sequence

1. Review the prepared cover, walkthrough and English wording together.
2. Freeze the chosen Git commit. Record a release tag and release notes for that
   exact commit, with its scope and validation evidence.
3. Deploy that commit through the existing Pages workflow. Verify `revision.txt`
   against the selected commit and check the public cover, contents, Chapters 2,
   26, 33 and 35, full-text search, mobile navigation and social image URL.
4. Publish the main post with the cover image, followed by the demonstration and
   scope replies. Link directly to the book and repository.

No tweet has been sent by this preparation. A deployment dispatch is not itself
evidence that the new cover is publicly available.

## Local verification

- Shared site assembly completed: 2,198 pages, with 136 sections in 34 chapter
  pages; the remaining Chapter 1 is an expository guide.
- Repository metadata, scope, documentation and regression checks passed.
- All 35 chapters passed rendered navigation, section, heading, anchor and local
  link checks, including the new book assets and closing matter.
- Chromium smoke tests passed at the `/CLRS-Lean/` subpath: cover image loading,
  contents, next/previous navigation, full-text and declaration search, mobile
  menu, dark mode and JavaScript-disabled reading.
- Desktop, mobile, dark cover, proof and closing screenshots were inspected.

The book-presentation revision is prepared for review. Production rollout and
social publication remain separate next steps.

## Reproduction

Use the shared site assembly and validation commands in
[Site Architecture](../site-architecture.md). Regenerate the stills and walkthrough
with `scripts/prepare_release_media.py` against that prepared site. The video
shows actual browser navigation; no proof result is simulated or composited.
