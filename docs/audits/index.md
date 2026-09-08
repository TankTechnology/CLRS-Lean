# 语义忠实性审计索引

以下报告是对应日期与提交状态的不可变快照，不是实时进度台账。

## 全书审计

- [2026-09-08 第四版逐章内容审查](2026-09-08-chapter-review/index.md)：
  35 章、137 个映射节条目，审查定义、公共定理与选取的证明依赖，并进行独立交叉复核。
  包含源码可复现的缓存接口空前提、指针旋转及区间插入缺陷，以及运行时间声明缺口。
  全部教材对应结论标记为 NOT-INDEPENDENTLY-VERIFIED；不是教材全文或全部辅助证明的逐行审计。

- [2026-08-28 全书证明缺口审计](2026-08-28-whole-book-proof-gap-audit.md)：
  按算法语义、正确性与不变量、最优性或下界、成本附着、模型来源和公共证据
  六个维度复核第四版全部 35 章。报告是提交时点的证据快照；仍需推进的证明
  以 GitHub issue 为实时追踪入口。

| 章号 | 审计日期（北京时间） | 判定分布 | 缺陷数 | 基准来源 |
|------|---------------------|----------|--------|----------|
| 2 | 2026-08-27 | MATCH 24 · MINOR 10 · MAJOR 0 · CRITICAL 0 · UNCERTAIN 0 | 10 MINOR | 参考第 2.1–2.3 节 |
| 3 | 2026-08-27 | MATCH 59 · MINOR 0 · MAJOR 0 · CRITICAL 0 · UNCERTAIN 0 | 0 | 参考第 3.1–3.3 节；保留 2026-08-17 历史基线 |
| 4 | 2026-08-18 | MATCH 57 · MINOR 13 · MAJOR 0 · CRITICAL 0 · UNCERTAIN 0 | 13 MINOR | 参考第 4.1–4.7 节 |
| 6 | 2026-08-27 | MATCH 39 · MINOR 12 · MAJOR 2 · CRITICAL 0 · UNCERTAIN 0 | 2 MAJOR, 12 MINOR | 参考第 6.1–6.5 节 |
| 5 | 2026-08-18 | MATCH 21 · MINOR 15 · MAJOR 1 · CRITICAL 0 · UNCERTAIN 1 | 1 MAJOR, 15 MINOR | 参考第 5.1–5.4 节 |
| 15 | 2026-08-17；2026-08-27 闭合复核 | MATCH 48 · MINOR 0 · MAJOR 0 · CRITICAL 0 · UNCERTAIN 0 | 0 | 参考第 15.1–15.4 节 |

## 历史闭合记录与当前结论

上表及 [`v1-trust-gate.md`](v1-trust-gate.md) 的 “Fresh MAJOR closure record”
记录早期审查及修复情况。Chapter 5 编号、Chapter 6 checked insert 等历史修复仍然有效；
明确排除的持久化 List/RAM 成本也不因本次审查自动成为缺陷。

但历史记录不能支持“当前范围没有未解释的 MAJOR”这一全书结论。
[2026-09-08 审查](2026-09-08-chapter-review/index.md) 发现了新的实质性问题。
[`clrs-proof-progress.csv`](../clrs-proof-progress.csv) 是现有声明账本，尚未按本次发现重新分类；
不能把其完成标签或计数替代语义审查结论。
