# Whole-book publication audit — September 15, 2026

This audit checks publication completeness against the existing compiled Lean formalization. It does not claim a new mathematical review of the textbook or new theorem proofs. Lean sources are unchanged from `5631cc7d`; the publication fixes are in the accompanying commit.

## Scope and result

- All 35 chapters, 136 canonical section pages, introduction, and book contents checked.
- All 2,196 generated module pages compared with 25,047 definition-bearing compiled commands (25,489 highlighted code chunks). No missing command or proof body.
- All 236,033 local-link occurrences on the 173 reader pages checked, including fragments on other pages. No broken target.
- Every standalone section code block and prose paragraph checked against its own embedded chapter body.
- All 171 chapter/section pages visited at 1,440 px and 390 px widths with JavaScript disabled. No missing declarations, hidden first declarations, or page overflow.
- Maximum composed chapter size: 13.07 MiB (Chapter 26).

## Repairs

The previous nonempty-code check missed partially exposed sections. Source-directory inventory now includes all owned split files, including 95 omitted from explicit navigation/mapping lists. Shared source mappings include the red-black-tree correctness package, counted matrix algorithms, and six retained legacy cores used by seven reader sections. In total, 87 sections now include supporting definitions and proofs, including the 25 earlier facade repairs.

Broad `set_option` filtering hid whole scoped declarations. Removing that filter restores nine missing canonical declarations across Chapters 24, 27, and 28, as well as affected supporting-module commands. Prose result links on native sections now reach visible declarations. Ordinary proof dependencies keep valid source-page links.

The explicit selections for §§16.3, 34.4, and 34.5 remain focused: all 5, 46, and 52 configured declaration selections respectively were checked against complete compiled command bodies. Their supporting source pages are also fully audited; unselected internal helpers are not all concatenated into those reader pages.

## Chapter inventory

Chapter 1 is intentionally expository: its two mapped textbook sections are owned by one chapter guide. The remaining 34 chapters contain the 136 canonical section pages. Visible declaration counts include structure fields and repeated supporting declarations; they are not counts of distinct theorems.

| Chapter | Section pages | Visible declaration anchors | Publication and browser checks |
| --- | ---: | ---: | --- |
| 1 | 0 | 0 | Passed |
| 2 | 3 | 128 | Passed |
| 3 | 3 | 232 | Passed |
| 4 | 7 | 344 | Passed |
| 5 | 4 | 237 | Passed |
| 6 | 5 | 284 | Passed |
| 7 | 4 | 172 | Passed |
| 8 | 4 | 307 | Passed |
| 9 | 3 | 202 | Passed |
| 10 | 3 | 88 | Passed |
| 11 | 5 | 271 | Passed |
| 12 | 3 | 654 | Passed |
| 13 | 4 | 277 | Passed |
| 14 | 5 | 326 | Passed |
| 15 | 4 | 705 | Passed |
| 16 | 4 | 254 | Passed |
| 17 | 3 | 499 | Passed |
| 18 | 3 | 450 | Passed |
| 19 | 4 | 344 | Passed |
| 20 | 5 | 535 | Passed |
| 21 | 2 | 407 | Passed |
| 22 | 5 | 162 | Passed |
| 23 | 3 | 360 | Passed |
| 24 | 6 | 704 | Passed |
| 25 | 3 | 447 | Passed |
| 26 | 3 | 1087 | Passed |
| 27 | 3 | 205 | Passed |
| 28 | 3 | 161 | Passed |
| 29 | 3 | 260 | Passed |
| 30 | 3 | 372 | Passed |
| 31 | 8 | 234 | Passed |
| 32 | 5 | 333 | Passed |
| 33 | 3 | 51 | Passed |
| 34 | 5 | 144 | Passed |
| 35 | 5 | 322 | Passed |

## Reproduction

```sh
python3 scripts/check_repository.py
python3 scripts/check_reader_site.py _site
python3 scripts/audit_reader_book.py --site _site --compiled .lake/build/literate
python3 scripts/smoke_reader_site.py --base-url http://127.0.0.1:8765/
python3 scripts/smoke_reader_book.py --base-url http://127.0.0.1:8765/
```

`reader-book-audit.json` is generated with every assembled website; render/full deployment also includes the compiled-command evidence. The browser command writes a per-page JSON report and one mobile screenshot per chapter. Deployment retains these checks and uses cached compiled inputs instead of recompiling the book.
