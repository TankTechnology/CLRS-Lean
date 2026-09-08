# 第 1–3 章第一批修复记录

对应 [#345](https://github.com/TankTechnology/CLRS-Lean/issues/345)、
[#346](https://github.com/TankTechnology/CLRS-Lean/issues/346)、
[#347](https://github.com/TankTechnology/CLRS-Lean/issues/347)。
状态：**本地已验证，尚未提交或推送；issues 保持开放。**
基于 `c8b074e961fb204ab50b9ea123b864260dafde38` 的共享工作区，分支
`codex/chapter-audit-repairs-2026-09-08`；保留此前网站、文档整理改动。

## 改动与语义

第 1 章把 Huffman/MST 阅读建议改为第四版第 15/21 章，并明确 `Option` 失败接口
与带输入前提的总函数都存在。第 3 章将标准函数的旧 §3.2 引用对齐到映射中的 §3.3，
兼容模块名和 import 未变。

第 2 章保留 `insertionSort`、`insertSorted` 与原比较计数的定义，新增以下公开连接：

- `insertionSortComparisons_le_worst xs`：任意输入的比较数不超过其长度的三角数预算。
- `insertionSortWorstInput n`：`[n-1, ..., 0]`；证明长度为 n，且此族在每个长度达到预算。
- `insertionSortWorstComparisons_isGreatest n`：该预算是所有长度 n 输入实际比较次数的可达最大值。
- `insertionSortComparisons_worst_case_theta`：将这个最大值的语义与原 Θ(n²) 结论放在同一接口。

见[比较分析源码](../../../src/CLRSLean/FourthEdition/Chapter_02/Section_02_2_Analyzing_Algorithms.lean)
与[新接口检查](../../../tests/Chapter_02_WorstCase_Interface.lean)。
空输入、单元素和重复键保持原行为。这里计的是函数式递归的键比较次数，
不声称完整 List 分配/遍历或机器运行时间。符号行成本的 t_i 仍由调用者给定，
不宣称任意 t_i 都是可实现的输入执行轨迹。

导读、行成本说明和第 2 章 CSV 证据已同步。新增证明完善既有选定定理组，
没有把帮助引理自动算作新的 tracked entries：全库账本仍为 1,689 项。

## 验证

先加入公共接口测试，确认它因上述新接口不存在而失败，再实现证明。
之后完成以下检查，退出码均为 0：

- 第 1、2、3 章规范模块及第 2 章兼容入口构建：8,617 个 Lake jobs。
- 完整 `lake build CLRSLean`：10,700 个 Lake jobs。
- `tests/Chapter_02_WorstCase_Interface.lean`：带任意输入上界、任意长度达到界、IsGreatest 的类型化使用，以及空/单元素/降序/重复键例子。
- 既有 `Chapter_02_Interface`、`Chapter_02_Legacy_Imports`、`Chapter_02_LineCost_Interface`、`Chapter_03_Textbook_Identities_Interface`。
- 第 1、2、3 章 Trust 文件；第 2 章为四个新增公共闭合定理增加 `#assert_axioms`。
- `uv run python scripts/check_repository.py`；包括占位符规则、映射、状态、README 生成块、导航元数据及 Markdown 链接。
- `git diff --check`；归档后的文档链接与 issue 清单覆盖检查。

构建有 Verso 文档角色提示等警告；没有将警告或编译通过当作语义闭合证据。
另一位审查者只读复核本批差异、相关定义与新接口，未发现可操作的正确性缺陷；
该复核未重复全量构建，也未审查无关网站差异。

## 后续边界

本记录只闭合上述三个章节的本次问题单义务。第 4 章起的缺口，以及第 13、17、27 章
已复现的严重缺陷均未因本批改动解决。全局状态/发布声明的重新分类由
[总跟踪 #376](https://github.com/TankTechnology/CLRS-Lean/issues/376) 保持开放。
历史审计快照不改写；本记录作为随后新增的修复证据。
