# CLRS-Lean milestone announcement draft

This draft describes the selected proof-library milestone and the September 8
chapter repairs. The [repair record](../plans/2026-09-08-chapter-repairs/index.md)
owns current verification and integration status; the
[original audit](../audits/2026-09-08-chapter-review/index.md) remains historical
evidence for its base commit. This draft does not assert a published post or a
deployed website.

## Short Chinese post

CLRS-Lean 迎来一个里程碑：用 Lean 4 形式化《算法导论》第四版的选定核心内容，覆盖 35 章导读、1,689 项清单内证明。我们也完成了本轮逐章审查发现的问题修复，补齐多处算法执行、正确性与成本证明之间的连接。

欢迎阅读、复用和参与：[CLRS-Lean](https://tanktechnology.github.io/CLRS-Lean/)

## Optional follow-up

“完成”指项目选定的证明清单和本轮修复范围，不代表全书所有结论、习题或底层实现均已形式化。每章公开具体模型、成本单位和适用前提，修复记录附有构建、回归及公理依赖检查。教材原文尚未逐页独立核对。

[形式化范围](https://github.com/TankTechnology/CLRS-Lean/blob/main/docs/scope.md) ·
[修复记录](https://github.com/TankTechnology/CLRS-Lean/blob/main/docs/plans/2026-09-08-chapter-repairs/index.md) ·
[GitHub](https://github.com/TankTechnology/CLRS-Lean)

## Short English post

CLRS-Lean milestone: selected core formalizations for CLRS (4th ed.), with 35
chapter guides and 1,689 tracked proof entries in Lean 4. This chapter-repair
round connects more algorithms to their correctness and counted execution,
with explicit model boundaries. Explore the library:
https://tanktechnology.github.io/CLRS-Lean/

## Evidence and claim boundary

| Claim | Evidence |
| --- | --- |
| 35 chapter guides; Chapter 1 expository | [Canonical chapter ledger](../clrs-proof-progress.csv) |
| 1,689 selected entries recorded as proved | Tracked/proved ledger totals; helpers added during repairs do not inflate this inventory |
| 137 mapped section entries | [Edition map](../clrs-fourth-edition-map.csv) and structural checker |
| Chapter repairs and verification | [Repair record](../plans/2026-09-08-chapter-repairs/index.md) |
| Scope is not every textbook statement or implementation | [Scope](../scope.md); exact-real, charged-operation and representation boundaries in chapter guides |

The original audit's defects are addressed by later code and proof changes,
with explicit scope corrections where the issue allowed them. Neither the
ledger label nor a successful build alone establishes whole-book semantic
fidelity. The textbook correspondence remains NOT-INDEPENDENTLY-VERIFIED.

## Release validation

Use the final verification results in the repair record. Before describing the
public website as updated, deploy and validate that checkout using the
[site build and preview runbook](../site-architecture.md#local-preview).

The earlier local website cleanup passed repository checks, library build
(10,700 jobs), all 35 chapter trust surfaces, Verso build/four-shard rendering
(2,120 modules), and 2,122 prepared HTML pages/sitemap entries. Chromium checks
covered navigation, 161 internal links, and mobile width. The fourth-edition
chapter index was then checked with all 35 names expanded, including saved
collapsed state and JavaScript disabled; third-edition compatibility chapters
were absent from the default sidebar. Those site checks predate the Lean
repairs and do not certify a freshly rendered repair checkout.

No tweet has been posted and no website deployment is recorded by this work.
