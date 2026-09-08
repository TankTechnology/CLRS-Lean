---
name: semantic-fidelity-audit
description: Audit a CLRS-Lean chapter for semantic fidelity to the textbook using an adversarial two-agent process: a ten-dimensional primary audit followed by a challenge review of every MATCH verdict. Produce an assertion-level report and update the audit index. Trigger for chapter audits, semantic-fidelity audits, and textbook-alignment reviews.
---

# Semantic-Fidelity Audit

Check whether formal definitions and theorems mean the same thing as the source
algorithm or definition. This complements `check_book_coverage.py`: the structural
check confirms that expected files and counts exist, while this skill checks their
meaning.

## Preconditions

1. Work from the CLRS-Lean repository root and update to the latest `main`.
2. `python3 scripts/check_book_coverage.py --report` must pass. Repair structural
   failures before starting the semantic audit.
3. The first line of `~/.config/clrs-audit/config` may name a corpus directory
   outside the repository. If the configuration or chapter corpus is absent,
   label every conclusion `NOT-INDEPENDENTLY-VERIFIED` and state prominently that
   the review relies on model knowledge rather than an independent textbook check.

## Chapter workflow

1. **Extract:** run
   `bash .claude/skills/semantic-fidelity-audit/scripts/extract_chapter.sh N`.
2. **Audit:** fill in `references/auditor-prompt.md`. Obtain `CHAPTER_NO` and
   `CHAPTER_TITLE` from `docs/clrs-fourth-edition-map.csv`; expand `SOURCE_FILES`
   from the chapter's `source_modules`; use the extracted path for `CORPUS_TEXT`,
   or `missing` when extraction is unavailable.
3. **Challenge:** run an independent review using
   `references/adversary-prompt.md` and the auditor's comparison table.
4. **Merge:** downgrade a MATCH verdict when the challenge establishes at least
   two independent discrepancies. Preserve UNCERTAIN verdicts and record the
   challenge review.
5. **Report:** use `references/report-template.md` for
   `docs/audits/chNN-semantic-fidelity.md` and update `docs/audits/index.md`.
6. **Commit:** stage and commit only the audit report and index.

## Non-negotiable rules

- Never commit corpus files, extracted text, or corpus paths.
- Cite at most two or three lines per source item, refer neutrally to the relevant
  section, and do not disclose corpus filenames or provenance.
- Include issue drafts for MAJOR and CRITICAL defects. Do not create issues without
  user authorization.
- The audit is read-only: do not modify Lean sources or Chapter 34 files.
