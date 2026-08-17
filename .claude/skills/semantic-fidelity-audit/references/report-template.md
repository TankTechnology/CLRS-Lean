# 报告模板

文件:`docs/audits/chNN-semantic-fidelity.md`

# ChNN <章名> 语义忠实性审计

- 审计日期(北京时间)/ skill 版本 / 基准来源(课本章节号,或 NOT-INDEPENDENTLY-VERIFIED)
- 结论分布:MATCH x · MINOR x · MAJOR x · CRITICAL x · UNCERTAIN x
- 结构前提:check_book_coverage.py 结果(通过/失败)

## 断言对照表(每节一个小节)

| 书条目 | Lean 位置 | 判定 | 说明 |

## 缺陷清单

每条:严重度 / 位置 / 差异描述 / 建议修法 / (MAJOR+CRITICAL 附 issue 草稿)

## 反驳记录

反驳员复核的 MATCH 条目数、提出的差异数、最终降级数

引用规则:单条引用 ≤2-3 行,用「参考第 X.X 节」中性表述,不出现语料文件名或来源。
