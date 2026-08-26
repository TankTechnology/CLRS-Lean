# Ch15 Greedy Algorithms 语义忠实性审计

- 初次审计日期（北京时间）：2026-08-17
- 闭合复核日期（北京时间）：2026-08-27
- 基准范围：CLRS 第四版第 15.1–15.4 节
- 实时结论：MATCH 48 · MINOR 0 · MAJOR 0 · CRITICAL 0 · UNCERTAIN 0

初次审计记录了 37 个 MATCH 和 11 个 MINOR。闭合复核保留原有通用模型，
在小型教材接口模块中补齐输入条件、算法版本、复杂度模型和教材定理名称；
11 个 MINOR 均有内核检查过的对应结果。本文是历史审计及其闭合记录，章节
实时计数仍以 `docs/clrs-proof-progress.csv` 为准。

## 闭合证据

| 原审计项 | 复核 | Lean 证据 | 闭合说明 |
|---|---|---|---|
| §15.1 活动未强制 `start < finish` | MATCH | `TextbookValid`, `TextbookInput`, `TextbookActivity` | 教材输入层精确表达正长度活动；通用 `Activity` 保持向后兼容。 |
| §15.1 缺少迭代选择器 | MATCH | `greedySelectIterative`, `greedySelectIterative_eq_greedySelect` | 一次扫描实现与递归选择器在排序且教材合法的输入上相同。 |
| §15.1 缺少线性运行界 | MATCH | `greedySelectIterativeCost_steps` | 成本化迭代器恰好检查输入中的每个活动一次。 |
| §15.2 使用错误的引理编号 | MATCH | `Section_15_2_Greedy_Meta.lean` 模块说明 | 文档改用教材概念名 “greedy-choice property” 和 “optimal substructure”。 |
| §15.2 `OptimalSubstructure` 依赖求解器 | MATCH | `OptimalSubstructure` | 新谓词只描述最优解分解及残余子问题，不提具体求解器。 |
| §15.2 两个性质被合并 | MATCH | `GreedyProblem.greedy_choice`, `.optimal_substructure`, `.replace_optimal_tail` | 贪心选择、最优子结构和替换桥分别陈述，`gsolve_optimal` 由它们组合得到。 |
| §15.2 缺少活动选择实例 | MATCH | `activityGreedyProblem`, `activityGsolve_eq_greedySelect`, `greedySelect_maxCardinality_via_meta` | 泛型框架与 §15.1 的具体算法、最优性定理已连接。 |
| §15.3 式 (15.4) 与内部代价未连接 | MATCH | `textbookCost`, `textbookCost_eq_cost` | 对一致的满二叉前缀码树证明叶频率乘深度之和等于内部节点频率和。 |
| §15.3 Lemma 15.2/15.3 无独立接口 | MATCH | `lemma15_2_greedy_choice`, `lemma15_3_optimal_substructure` | 两个教材引理分别作为已有交换/拆叶证明的命名接口公开。 |
| §15.3 缺少复杂度说明 | MATCH | `huffmanOfFreqsComparisons_le_quadratic`, `textbookHeapHuffmanWork_le_nlogn` | 已验证列表实现有 `2n²` 比较上界；教材二叉堆实现另有 `3n(log₂ n+1)` 操作包络，二者不混同。 |
| §15.4 未覆盖空初始缓存 | MATCH | `misses_empty_eq_singleton_add_one`, `fifo_optimal_from_empty`, `fifo_optimal_after_compulsory_fill` | 当前语义下空缓存恰多一次强制缺失；之后复用非空交换定理。任意容量预填充只以共同成本桥表达。 |

## 教材主链复核

### §15.1 Activity selection

核心 `greedySelect_maxCardinality` 仍证明按完成时间排序的递归选择器返回最大基数
可行子序列。教材接口另外要求每个活动 `start < finish`，并证明迭代选择器与
递归选择器等价、迭代扫描步数恰为输入长度。因此模型合法性、两种教材伪代码
和线性扫描结论均有可直接定位的接口。

### §15.2 Elements of the greedy strategy

`GreedyProblem` 将局部贪心选择的存在性、最优解尾部的最优性以及最优尾部的
可替换性分开。`gsolve_optimal` 是由这三个结构事实和严格变小的子问题推出的
泛型最优性定理。`activityGreedyProblem` 证明这些字段在活动选择问题中成立，
且泛型求解器确实计算 §15.1 的 `greedySelect`。

### §15.3 Huffman codes

`optimum_huffman_v2` 和 `optimum_huffman_freqs` 继续承担 Huffman 最优性主定理。
`textbookCost_eq_cost` 补上式 (15.4) 与原内部节点代价之间的语义桥；
`lemma15_2_greedy_choice` 和 `lemma15_3_optimal_substructure` 给出教材编号接口。
复杂度结论刻意分层：仓库中的可执行有序列表算法证明二次比较界，教材的
优先队列实现证明基于每次堆操作对数预算的 `n log n` 包络。

### §15.4 Offline caching

迹交换与耦合证明继续给出 `fifo_optimal`：对非空初始驻留集，最远未来策略
的缺失数不超过任意策略。`fifo_optimal_from_empty` 把教材的字面空起点纳入
当前一步换入语义；首个请求对所有策略都是一次共同强制缺失。对容量大于一
的缓存，仓库没有冒充一个尚未定义的自动填满执行器，而是用
`fifo_optimal_after_compulsory_fill` 证明共同预填充成本不会改变后续最优性。

## 范围边界

- `fifoPolicy` 是历史名称，语义是 farthest-in-future/Belady 策略，不是通常
  所说的 first-in-first-out。
- Huffman 的 `n log n` 结论是教材堆操作模型；当前列表程序的已验证比较界是
  二次的。
- 指针、内存分配、字级 RAM、硬件缓存和并发实现不属于本章宣称的数学边界。
- 章节习题和章末问题未因本次 11 项审计闭合而自动宣称完成。

## 结论

Chapter 15 的四条教材主线现在均具有可定位、可复用且公理透明的 Lean 接口。
初次审计的 11 个 MINOR 已全部闭合；剩余差异仅是明确排除在章节数学验收边界
之外的低层实现或习题增强项。
