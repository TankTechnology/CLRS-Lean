---
name: semantic-fidelity-audit
description: 按章审计 CLRS-Lean 形式化定义与原著算法的语义忠实性——双代理对抗流程(审计员 10 维对照 + 反驳员攻 MATCH),产出逐条对照报告与汇总索引。触发:审计第X章、语义忠实性审计、semantic fidelity audit。
---

# 语义忠实性审计

检查形式化定义/定理的**含义**是否忠实于原著算法与定义。这是 check_book_coverage.py(结构对应)之上的补充层:结构检查保证"文件在、计数对",本 skill 保证"含义对"。

## 前置
1. 仓库根 = CLRS-Lean 仓库,`git pull` 至最新 main
2. 结构前提:`python3 scripts/check_book_coverage.py --report` 必须通过;不通过则先修结构,不进入审计
3. 语料:本机 `~/.config/clrs-audit/config` 第 1 行为语料目录(仓库外)。config 缺失或该章语料缺失 → 全部结论附加 NOT-INDEPENDENTLY-VERIFIED,报告头部显著声明"基于模型知识,未经课本核对"

## 流程(章号 N)
1. **提取**:`bash .claude/skills/semantic-fidelity-audit/scripts/extract_chapter.sh N` → 语料文本路径
2. **审计员**:读 references/auditor-prompt.md,填模板变量,用 Agent 工具派发 subagent(变量:CHAPTER_NO、CHAPTER_TITLE 来自 docs/clrs-fourth-edition-map.csv;SOURCE_FILES 为该章 source_modules 展开的 .lean 路径;CORPUS_TEXT 为第 1 步产物路径,若不存在则填"不存在")
3. **反驳员**:读 references/adversary-prompt.md,输入为审计员对照表,同样用 Agent 工具派发
4. **合并**:反驳成立(≥2 条独立差异)的 MATCH 条目降级为 MINOR;UNCERTAIN 保留;把反驳记录写进报告
5. **报告**:按 references/report-template.md 写 `docs/audits/chNN-semantic-fidelity.md`;更新 `docs/audits/INDEX.md`(每章一行:章号/审计日期(北京时间)/判定分布/缺陷数/基准来源)
6. **提交**:`git add docs/audits/` 并 commit(只提交报告与索引)

## 红线(违反即失败)
- 语料文件/提取文本/语料路径绝不允许进入 git 或出现在仓库任何文件中
- 报告引用原文用中性表述「参考第 X.X 节」,单条 ≤2-3 行;不得出现可推断参考材料存在的表述、文件名、来源
- MAJOR/CRITICAL 缺陷:报告附 issue 草稿,**不自动开 issue**,由用户决定
- 审计只读:不修改任何 Lean 源文件;不触碰 Chapter_34 文件
