# 2026-09-08 逐章修复跟踪

[总跟踪 issue](https://github.com/TankTechnology/CLRS-Lean/issues/376) · [实施计划](plan.md) · [原始审查快照](../../audits/2026-09-08-chapter-review/index.md)

已提交并逐一回读确认 **31 个章节 issue + 1 个总跟踪 issue**，正文与准备稿一致。
覆盖全部 54 个非 MATCH 主判定节，并含部分 MATCH 章节的文档修正；第 7、9、33、34 章
没有本次新增的确定性修复项，保留审查范围限制。历史审计文件不因修复而改写。

| 章 | 严重度 | Issue | 本地修复状态 |
| --- | --- | --- | --- |
| 1 | MINOR | [#345](https://github.com/TankTechnology/CLRS-Lean/issues/345) | 已提交，待合并 |
| 2 | UNCERTAIN | [#346](https://github.com/TankTechnology/CLRS-Lean/issues/346) | 已提交，待合并 |
| 3 | MINOR | [#347](https://github.com/TankTechnology/CLRS-Lean/issues/347) | 已提交，待合并 |
| 4 | UNCERTAIN | [#348](https://github.com/TankTechnology/CLRS-Lean/issues/348) | 已提交，待合并 |
| 5 | MINOR | [#349](https://github.com/TankTechnology/CLRS-Lean/issues/349) | 已提交，待合并 |
| 6 | MINOR | [#350](https://github.com/TankTechnology/CLRS-Lean/issues/350) | 已提交，待合并 |
| 8 | MAJOR | [#351](https://github.com/TankTechnology/CLRS-Lean/issues/351) | 已提交，待合并 |
| 10 | MINOR | [#352](https://github.com/TankTechnology/CLRS-Lean/issues/352) | 已提交，待合并 |
| 11 | MAJOR | [#353](https://github.com/TankTechnology/CLRS-Lean/issues/353) | 已提交，待合并 |
| 12 | MINOR | [#354](https://github.com/TankTechnology/CLRS-Lean/issues/354) | 已提交，待合并 |
| 13 | MAJOR | [#355](https://github.com/TankTechnology/CLRS-Lean/issues/355) | 已提交，待合并 |
| 14 | MAJOR | [#356](https://github.com/TankTechnology/CLRS-Lean/issues/356) | 已提交，待合并 |
| 15 | MINOR | [#357](https://github.com/TankTechnology/CLRS-Lean/issues/357) | 已提交，待合并 |
| 16 | MINOR | [#358](https://github.com/TankTechnology/CLRS-Lean/issues/358) | 已提交，待合并 |
| 17 | MAJOR | [#359](https://github.com/TankTechnology/CLRS-Lean/issues/359) | 已提交，待合并 |
| 18 | MINOR | [#360](https://github.com/TankTechnology/CLRS-Lean/issues/360) | 已提交，待合并 |
| 19 | MINOR | [#361](https://github.com/TankTechnology/CLRS-Lean/issues/361) | 已提交，待合并 |
| 20 | MINOR | [#362](https://github.com/TankTechnology/CLRS-Lean/issues/362) | 已提交，待合并 |
| 21 | MAJOR | [#363](https://github.com/TankTechnology/CLRS-Lean/issues/363) | 已提交，待合并 |
| 22 | MAJOR | [#364](https://github.com/TankTechnology/CLRS-Lean/issues/364) | 已提交，待合并 |
| 23 | MAJOR | [#365](https://github.com/TankTechnology/CLRS-Lean/issues/365) | 已提交，待合并 |
| 24 | MAJOR | [#366](https://github.com/TankTechnology/CLRS-Lean/issues/366) | 已提交，待合并 |
| 25 | MINOR | [#367](https://github.com/TankTechnology/CLRS-Lean/issues/367) | 已提交，待合并 |
| 26 | MINOR | [#368](https://github.com/TankTechnology/CLRS-Lean/issues/368) | 已提交，待合并 |
| 27 | CRITICAL | [#369](https://github.com/TankTechnology/CLRS-Lean/issues/369) | 已提交，待合并 |
| 28 | MINOR | [#370](https://github.com/TankTechnology/CLRS-Lean/issues/370) | 已提交，待合并 |
| 29 | MINOR | [#371](https://github.com/TankTechnology/CLRS-Lean/issues/371) | 已提交，待合并 |
| 30 | MINOR | [#372](https://github.com/TankTechnology/CLRS-Lean/issues/372) | 已提交，待合并 |
| 31 | MAJOR | [#373](https://github.com/TankTechnology/CLRS-Lean/issues/373) | 已提交，待合并 |
| 32 | MAJOR | [#374](https://github.com/TankTechnology/CLRS-Lean/issues/374) | 已提交，待合并 |
| 35 | MINOR | [#375](https://github.com/TankTechnology/CLRS-Lean/issues/375) | 已提交，待合并 |

31 个章节分别提交，逐章 SHA 见 [提交映射](commits.csv)。修复位于
`codex/chapter-audit-repairs-2026-09-08` 分支，等待 PR 审查与合并；章节 issue
在合并前保持开放。早期批次记录的“本地待提交”是阶段状态。
修复记录：[第 1–3 章](first-batch.md)、[第 4–6 章](chapters-04-06.md)、
[第 8 章](chapter-08-results.md)、[第 10–12 章](chapters-10-12.md)。

[第 11、13–16 章验证记录](chapters-11-16.md)：全库构建 10,724 项通过，章节接口、
重点执行回归、公理依赖与仓库元数据检查通过，另有独立源码复核。

[第 17–20 章验证记录](chapters-17-20.md)：全库构建 10,728 项通过，章节接口、重点回归、公理依赖与仓库元数据检查通过。

[第 21–30、32 章修复记录](chapters-21-32.md)、[第 31 章专项记录](chapter-31.md)、
[第 35 章专项记录](chapter-35.md) 已补齐其余章节。31 个章节 issue 的当前验收项均已完成本地修复与验证；没有新增修复项的第 7、9、33、34 章不被改称为全面审计通过。

[统一验收记录](verification.md)：最终全库构建 10,768 项通过，35 章信任门及第 31 章最终扩展信任表面通过，新增针对性回归和仓库校验通过。章节独立提交记录在 [commits.csv](commits.csv)；是否已合并以关联 PR 和远端 issue 为准。
