# Book release presentation implementation plan

**Goal:** Prepare the accepted book design and a reviewable English launch package.

**Architecture:** Extend the shared Python site assembly with static front/back
matter and chapter navigation; keep the existing Verso content and scope intact.
Use a dedicated stylesheet and original SVG artwork, with a browser-rendered
social PNG. Execute locally on `codex/book-release-presentation`.

**Stack:** Python, generated HTML, CSS, SVG, Playwright, GitHub Pages.

- [x] Add `scripts/book_presentation.py` for cover, colophon, sequential links
  and sharing metadata. Test Chapter 1/35 boundaries and preservation of anchors
  and source scope in `scripts/test_book_presentation.py`.
- [x] Add `docs/literate/clrs-book.css` and `docs/literate/assets/book-*.svg`.
  Wire copying and post-composition presentation into `prepare_literate_site.py`.
- [x] Extend `check_reader_site.py` and `smoke_reader_site.py` to check the new
  cover, image sizing/loading, navigation boundaries and closing content.
- [x] Assemble from `.lake/build/literate-html-merged` into `_site`; run
  `python3 scripts/check_repository.py`, `python3 scripts/check_reader_site.py
  _site`, and the browser smoke test against the `/CLRS-Lean/` subpath.
- [x] Inspect homepage, contents, chapter and closing screenshots at desktop
  and mobile sizes; export the social card and a short browser walkthrough.
- [x] Finalize `docs/releases/2026-09-13-twitter-draft.md` and a release runbook
  with completed/pending work and the exact scope wording. Commit in English
  using TankTechnology identity. Distinguish local readiness, deployment and
  the unsent social announcement in the handoff.
