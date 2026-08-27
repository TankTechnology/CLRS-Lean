# 语义忠实性审计索引

以下报告是对应日期与提交状态的不可变快照，不是实时进度台账。

| 章号 | 审计日期（北京时间） | 判定分布 | 缺陷数 | 基准来源 |
|------|---------------------|----------|--------|----------|
| 2 | 2026-08-27 | MATCH 24 · MINOR 10 · MAJOR 0 · CRITICAL 0 · UNCERTAIN 0 | 10 MINOR | 参考第 2.1–2.3 节 |
| 3 | 2026-08-27 | MATCH 59 · MINOR 0 · MAJOR 0 · CRITICAL 0 · UNCERTAIN 0 | 0 | 参考第 3.1–3.3 节；保留 2026-08-17 历史基线 |
| 4 | 2026-08-18 | MATCH 57 · MINOR 13 · MAJOR 0 · CRITICAL 0 · UNCERTAIN 0 | 13 MINOR | 参考第 4.1–4.7 节 |
| 6 | 2026-08-27 | MATCH 39 · MINOR 12 · MAJOR 2 · CRITICAL 0 · UNCERTAIN 0 | 2 MAJOR, 12 MINOR | 参考第 6.1–6.5 节 |
| 5 | 2026-08-18 | MATCH 21 · MINOR 15 · MAJOR 1 · CRITICAL 0 · UNCERTAIN 1 | 1 MAJOR, 15 MINOR | 参考第 5.1–5.4 节 |
| 15 | 2026-08-17；2026-08-27 闭合复核 | MATCH 48 · MINOR 0 · MAJOR 0 · CRITICAL 0 · UNCERTAIN 0 | 0 | 参考第 15.1–15.4 节 |

## 实时闭合说明

表中的 Chapter 5 与 Chapter 6 数字仍是对应审计文件记录的历史判定分布，
不能当作当前章节状态。实时分类见
[`v1-trust-gate.md`](v1-trust-gate.md) 的 “Fresh MAJOR closure record”：
Chapter 5 的编号错误和 Chapter 6 的 checked insert 已修复，Chapter 6
剩余两个历史 MAJOR 属于明确排除的持久化 List/RAM 实现边界；当前宣称范围内
没有仍然成立且未解释的 MAJOR。章节完成度始终以
[`clrs-proof-progress.csv`](../clrs-proof-progress.csv) 为准。
