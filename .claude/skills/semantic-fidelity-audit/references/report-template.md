# Report Template

Write the report to `docs/audits/chNN-semantic-fidelity.md`.

# ChNN: <Chapter title> Semantic-Fidelity Audit

- Audit date and time zone, skill version, and reference basis; use
  `NOT-INDEPENDENTLY-VERIFIED` when no independently checked corpus is available.
- Verdict distribution: MATCH, MINOR, MAJOR, CRITICAL, and UNCERTAIN counts.
- Structural prerequisite: result of `check_book_coverage.py`.

## Assertion comparison table

Create one subsection per textbook section.

| Textbook item | Lean location | Verdict | Explanation |
| --- | --- | --- | --- |

## Defects

For each item include severity, location, discrepancy, recommended repair, and an
issue draft for MAJOR or CRITICAL findings.

## Adversarial review

Record the number of MATCH entries reviewed, discrepancies proposed, and final
downgrades. Quote at most two or three lines per item, refer neutrally to the
relevant section, and do not name or describe corpus files.
