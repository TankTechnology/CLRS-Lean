# Verdict Definitions

| Verdict | Meaning |
| --- | --- |
| MATCH | Semantically aligned after adversarial review. |
| MINOR | An explainable representational, naming, or documentation difference that does not alter the mathematics. Repair is recommended but not required. |
| MAJOR | A mathematical difference, such as a stronger or weaker theorem, non-equivalent definition, or missing premise, that does not invalidate the chapter's main conclusion. |
| CRITICAL | A core definition or theorem conflicts with the source and may invalidate or mislead the chapter conclusion. |
| UNCERTAIN | A verdict cannot be reached because the reference is missing or ambiguous, or the Lean source resists reliable interpretation. The blocker must be stated. |

`NOT-INDEPENDENTLY-VERIFIED` is a global label used when no independently checked
corpus is available. It may accompany any verdict.
