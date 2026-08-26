# Ch2 Getting Started 语义忠实性审计

- **审计日期（北京时间）**: 2026-08-17 13:06 CST（原始审计），2026-08-27 更新（反映逐行成本表与显式 MERGE 闭合）
- **Skill 版本**: semantic-fidelity-audit v1
- **基准来源**: 参考第 2.1–2.3 节（课本语料已核对）
- **结论分布**: MATCH 24 · MINOR 10 · MAJOR 0 · CRITICAL 0 · UNCERTAIN 0
- **结构前提**: `check_book_coverage.py` 通过（Book coverage OK, 35 chapters）

## 断言对照表

### §2.1 Insertion Sort

| # | 书条目 | Lean 位置 | 判定 | 说明 |
|---|--------|-----------|------|------|
| 1.1 | 插入排序伪代码：数组 A[1..n]，1-起始可变原地排序 | `Section_02_1_Insertion_Sort.lean:42-44` `insertionSort` | MINOR | 使用不可变 List Nat 替代可变数组；模块文档已声明（"recursive list algorithm"） |
| 1.2 | 算法参数 A 与 n | `Section_02_1_Insertion_Sort.lean:42` | MINOR | 无显式长度参数 n；列表长度隐式蕴含 |
| 1.3 | 外层循环不变量：「A[1..i-1] 由原元素组成，且已排序」 | 无直接对应行 | MINOR | 不变量未作为独立定理陈述；语义分解为 `insertSorted_ordered`（行 89–105）和 `insertSorted_perm`（行 108–117） |
| 1.4 | 初始化：i=2 时 A[1..1] 单元素平凡有序 | `Section_02_1_Insertion_Sort.lean:46-52` `ordered_tail` / 行 119–125 nil 分支 | MATCH | 单元素有序性由 `Ordered [_] = True` 覆盖 |
| 1.5 | 维护：for 循环体将 A[i] 插入已排序子数组，保持有序性 | `Section_02_1_Insertion_Sort.lean:89-105` `insertSorted_ordered` | MATCH | 插入到有序列表保持有序性——与书中维护性质等价 |
| 1.6 | 终止：i=n+1 时 A[1..n] 为原元素排序结果 | `Section_02_1_Insertion_Sort.lean:119-125` `insertionSort_sorted` | MATCH | 递归版本的终止对应归纳基始与步骤完成 |
| 1.7 | 算法输出已排序且为原输入排列 | `Section_02_1_Insertion_Sort.lean:119-125` + 行 128–135 | MATCH | `insertionSort_sorted` + `insertionSort_perm` 完整覆盖 |
| 1.8 | 伪代码步骤逐行对应（for i=2 to n / while j>0 / 移位 / 插入） | 无逐行对应 | MINOR | 采用递归函数式版本，非逐行翻译；模块文档已声明 |
| 1.9 | 边界情况：空输入 | `Section_02_1_Insertion_Sort.lean:43` `[] => []` | MATCH | 空列表直接返回空列表，有序性平凡成立 |
| 1.10 | 边界情况：单元素 | `Section_02_1_Insertion_Sort.lean:28` `Ordered [_] = True` | MATCH | 单元素列表有序性平凡成立 |

### §2.2 Analyzing Algorithms

| # | 书条目 | Lean 位置 | 判定 | 说明 |
|---|--------|-----------|------|------|
| 2.1 | RAM 模型定义（统一指令成本、顺序执行、整数/浮点/字符类型） | `LineCost/Definitions.lean` | MINOR | 已形式化课本本节实际使用的符号单位成本表；未声称数组、字长或存储层面的完整 operational RAM 语义 |
| 2.2 | 插入排序逐行成本分析：每行伪代码标注成本 c_k 与执行次数 | `LineCost/Definitions.lean` `InsertionSortLineCosts` / `InsertionSortLineCounts` | MATCH | `c₁,c₂,c₄,...,c₈` 与七行执行次数均有独立字段，并由 `n` 和 `tᵢ` 轨迹生成 |
| 2.3 | 完整运行时间公式 T(n) = c1·n + c2·(n-1) + c4·(n-1) + c5·Σti + c6·Σ(ti-1) + c7·Σ(ti-1) + c8·(n-1) | `LineCost/Formula.lean` `insertionSortRunningTime_eq_textbook_sum` | MATCH | 逐项证明完整七项公式；`BestWorst.lean` 进一步证明 `tᵢ=1` 与 `tᵢ=i` 的精确计数表和完整运行时间公式 |
| 2.4 | 最坏情况分析：ti = i，T(n) = an² + bn + c（式 2.2） | `Section_02_2_Analyzing_Algorithms.lean:55-56` `insertionSortWorstComparisons` + 行 137-140 `insertionSortWorstComparisons_theta_quadratic` | MATCH | 比较次数正确（triangular(n-1) = n(n-1)/2）；O(n²) 上界和 Ω(n²) 下界均已证明；`ThetaBoundedBy` 谓词将二者打包为 Θ(n²) 断言 |
| 2.5 | 最坏情况为 Θ(n²)（书中明确使用 Θ-记法） | `Section_02_2_Analyzing_Algorithms.lean:137-140` `insertionSortWorstComparisons_theta_quadratic` | MATCH | `ThetaBoundedBy` 谓词定义为 O ∩ Ω，直接给出 Θ(n²) 紧确界 |
| 2.6 | 最好情况分析：已排序数组，ti = 1，T(n) = an + b（式 2.1），Θ(n) | `Section_02_2_Analyzing_Algorithms.lean:167-196` `insertionSortComparisons_best_case` + 行 225-228 `insertionSortBestComparisons_theta_linear` | MATCH | 已排序输入比较次数 = n-1 精确证明（行 167）；`ThetaBoundedBy` 打包上界和下界给出 Θ(n) |
| 2.7 | 平均情况分析：ti ≈ i/2，仍为 Θ(n²) | 无对应 | MINOR | 书中平均情况讨论较简短（"roughly as bad as the worst case"），未形式化属合理省略 |
| 2.8 | 增长量级讨论：忽略低阶项与常数系数，仅关注主导项 n² | `Section_02_2_Analyzing_Algorithms.lean:58-75`（上界）+ 行 89-115（下界）+ 行 137-140（Θ 包装） | MATCH | 原始审计中反驳员发现 Θ vs O 差异并降级为 MINOR；现上下界均已证明，`ThetaBoundedBy` 提供直接 Θ(n²) 断言，异议完全解决 |
| 2.9 | Θ-记法非正式引入：「roughly proportional when n is large」 | `Section_02_2_Analyzing_Algorithms.lean:47-52` `ThetaBoundedBy` | MATCH | `ThetaBoundedBy` 定义为 O ∩ Ω，比书中 §2.2 的非正式 Θ 使用更精确；正式 Θ-记法在 Ch3 才定义，但本谓词等价于标准定义 |
| 2.10 | 最坏情况分析优于平均情况的三条理由 | 无对应 | MINOR | 属论述性内容，非形式化数学断言 |
| 2.11 | Ω(n²) 最坏情况下界 | `Section_02_2_Analyzing_Algorithms.lean:85-101` `triangular_ge_quarter_square` + 行 104-114 | MATCH | 证明 triangular(n-1) ≥ n²/4（n≥2），与上界组合给出紧确 Θ(n²) |
| 2.12 | 最好情况精确比较次数 = n-1 | `Section_02_2_Analyzing_Algorithms.lean:141-170` `insertionSortComparisons_best_case` | MATCH | 对已排序输入，insertionSort 比较次数精确等于 n-1，与 CLRS eq. (2.1) 一致 |
| 2.13 | 最好情况 Θ(n) | `Section_02_2_Analyzing_Algorithms.lean:175-190` | MATCH | 线性上界（`insertionSortBestComparisons_eventually_linear_upper`）+ 线性下界（`insertionSortBestComparisons_eventually_linear_lower`） |

### §2.3 Designing Algorithms

| # | 书条目 | Lean 位置 | 判定 | 说明 |
|---|--------|-----------|------|------|
| 3.1 | 分治法三步：Divide / Conquer / Combine | `Section_02_3_Designing_Algorithms.lean:30-31` `mergeSort` | MINOR | 委托给 `List.mergeSort`，未显式展示三步结构；模块文档声明 "we use Lean's verified List.mergeSort implementation" |
| 3.2 | MERGE 过程伪代码（27 行，含临时数组 L/R、三个 while 循环） | `Merge/Definitions.lean` `mergeWithCost` | MATCH | 按审计建议采用显式双列表 MERGE；每步比较表头并消费一个元素，空侧分支复制剩余后缀，不再委托 `List.merge` |
| 3.3 | MERGE 运行时间 Θ(n) 的分析 | `Merge/Cost.lean` | MATCH | `merge_comparisons_le` 给出线性比较上界，`merge_outputWrites_eq` 给出恰好 `left.length + right.length` 次输出写入；合并后的列表级工作量上下界均为线性 |
| 3.4 | MERGE-SORT 伪代码（递归，p<r 时分裂，p=r 时基始） | `Section_02_3_Designing_Algorithms.lean:30-31` | MINOR | 委托 `List.mergeSort`；递归结构等价但未显式对应伪代码 |
| 3.5 | 归并排序正确性：输出有序且保持原元素 | `Section_02_3_Designing_Algorithms.lean:34-39` | MATCH | `mergeSort_sortedLE` + `mergeSort_perm` 完整覆盖 |
| 3.6 | 递推关系 T(n) = 2T(n/2) + Θ(n)，T(1) = Θ(1)（n 为 2 的幂时） | `Section_02_3_Designing_Algorithms.lean:47-49` `mergeSortRecurrenceOnPowersOfTwo` | MATCH | 递推式正确：T(2⁰)=1, T(2^(k+1)) = 2·T(2^k) + 2^(k+1) |
| 3.7 | 递推求解：T(n) = Θ(n log n)（通过递推树） | `Section_02_3_Designing_Algorithms.lean:52-77` `mergeSortRecurrenceOnPowersOfTwo_closedForm` | MATCH | 封闭解 T(2^k) = (k+1)·2^k = n log₂ n + n 精确证明 |
| 3.8 | 任意 n 的递推 T(n) = T(⌊n/2⌋) + T(⌈n/2⌉) + Θ(n) | `Merge_Sort_Recurrence.lean:64-65` `Recurrence` | MATCH | 使用 n/2 取地板、(n+1)/2 取天花板，加法项为 n（更精确于 Θ(n)） |
| 3.9 | 任意 n 的 Θ(n log n) 界 | `Merge_Sort_Recurrence.lean:174-203` `theta_n_log_n_all_inputs` | MATCH | 通过 Ch4 主定理 + §4.6 地板/天花板夹逼桥证明了任意输入规模的 Θ(n log n) |
| 3.10 | 精确幂上的 Θ(n log n)（通过主定理） | `Merge_Sort_Recurrence.lean:121-138` `theta_n_log_n_on_exact_powers` | MATCH | 通过主定理情形 2（常数正规化强制项）证明 |
| 3.11 | MonotoneAbs 额外假设 | `Merge_Sort_Recurrence.lean:176` `hT_mono` | MINOR | `theta_n_log_n_all_inputs` 要求 `MonotoneAbs T`，书中未显式陈述此条件；但运行时间函数单调是合理的隐含假设 |

## 缺陷清单

### MAJOR（0 条）

2026-08-27 复核关闭原四条 MAJOR：M1/M3 由 `LineCost` 模块组的七行
符号成本、执行次数表、完整 `T(n)` 公式及 best/worst 特化闭合；M2/M4
由显式 `mergeWithCost`、排序/排列正确性、线性比较上界和精确输出写入
计数闭合。数组分配和 word-RAM 指令语义仍是可选的更低层 refinement，
不再构成本审计所要求的课本层 MAJOR 缺口。

### 已解决（原 MAJOR，现已在 `feat/ch02-fixes` 中修复）

**R1. （原 M2）Ω(n²) 最坏情况下界**
- 位置: `Section_02_2_Analyzing_Algorithms.lean:99-115`
- 新增定理: `triangular_ge_quarter_square`（行 99），`insertionSortWorstComparisons_quadratic_lower`（行 118），`insertionSortWorstComparisons_eventually_quadratic_lower`（行 124）
- 与原有上界组合给出 Θ(n²) 最坏情况界

**R2. （原 M3）最好情况分析**
- 位置: `Section_02_2_Analyzing_Algorithms.lean:142-196`
- 新增定理: `insertionSortComparisons_best_case`（行 167，精确比较次数 = n-1），`insertionSortBestComparisons_eventually_linear_upper`（行 201），`insertionSortBestComparisons_eventually_linear_lower`（行 211）
- 完整覆盖 CLRS eq. (2.1) 的最好情况 Θ(n) 分析

**R3. Θ-记法包装（`ThetaBoundedBy`）**
- 位置: `Section_02_2_Analyzing_Algorithms.lean:47-52`（定义），行 137-140（Θ(n²)），行 225-228（Θ(n)）
- 新增谓词: `ThetaBoundedBy` 定义为 `EventuallyBoundedBy f g ∧ EventuallyBoundedBy g f`（O ∩ Ω）
- 新增定理: `insertionSortWorstComparisons_theta_quadratic`，`insertionSortBestComparisons_theta_linear`
- 解决了 m4、m9、m10、m13、m14 中记录的 `EventuallyBoundedBy` O-记法局限性——现在有直接的 Θ 断言

### MINOR（14 条）

**m1. 严重度: MINOR** — `Section_02_1_Insertion_Sort.lean:42-44`：使用不可变 List 替代可变数组；1-起始索引变为 0-起始列表。无需修改，台账已记录。

**m2. 严重度: MINOR** — `Section_02_1_Insertion_Sort.lean:42`：无显式长度参数 n，列表长度由类型隐式携带。可忽略。

**m3. 严重度: MINOR** — `Section_02_1_Insertion_Sort.lean`：循环不变量未作为独立定理陈述，语义分解为 `insertSorted_ordered` 和 `insertSorted_perm`。优先级低。

**m4. 严重度: MINOR** — `Section_02_2_Analyzing_Algorithms.lean:43-45`：`EventuallyBoundedBy` 仅是 O-记法上界包装。`ThetaBoundedBy` 谓词（行 47-52）现提供 Θ-记法包装，但 `EventuallyBoundedBy` 自身的 O-记法局限保留为台账记录。

**m5. 严重度: MINOR** — `Section_02_3_Designing_Algorithms.lean:30-31`：委托 `List.mergeSort` 而非显式实现分治三步。无需修改，模块文档已声明。

**m6. 严重度: MINOR** — `Merge_Sort_Recurrence.lean:176`：`MonotoneAbs T` 要求书中未显式陈述，属合理技术条件。

**m7. 严重度: MINOR** — `Section_02_2_Analyzing_Algorithms.lean`：论述性内容（三条理由、RAM 模型指令集）未形式化，属合理省略。

**m8. 严重度: MINOR** — `Section_02_2_Analyzing_Algorithms.lean:41-43`：n=0 时 Nat 减法截断为 0，结果合理但书中未讨论。

**m9. 严重度: MINOR** — `Section_02_2_Analyzing_Algorithms.lean`（原条目 2.8）：原反驳员发现 Θ vs O 差异；现上下界 + `ThetaBoundedBy` 均已齐全，异议已解决。条目降级为台账记录，标注已通过 `insertionSortWorstComparisons_theta_quadratic` 获得直接 Θ(n²) 断言。

**m10. 严重度: MINOR** — `Section_02_2_Analyzing_Algorithms.lean:43-45`：`EventuallyBoundedBy` 为 O-记法。`ThetaBoundedBy` 谓词（行 47-52）现提供直接 Θ 包装，`insertionSortWorstComparisons_theta_quadratic`（行 137-140）为 Θ(n²) 断言。此条目降级为台账记录。

**m11. 严重度: MINOR** — `LineCost/BestWorst.lean` 已给出含全部 `cᵢ`
的最坏情况精确式；尚未另行引入存在量词系数 `a,b,c`，把同一表达式重包装
成字面形式 `an²+bn+c`。该省略不影响精确公式或 Θ(n²) 结论。

**m12. 严重度: MINOR** — `Section_02_1_Insertion_Sort.lean`：采用递归函数式版本，非伪代码逐行翻译。模块文档已声明。

**m13. 严重度: MINOR** — `Section_02_2_Analyzing_Algorithms.lean:19-23`：原模块 doc 声明 `EventuallyBoundedBy` 为 O-记法。现已更新为反映 `ThetaBoundedBy` 谓词直接提供 Θ 包装，声明已反映当前状态。

**m14. 严重度: MINOR** — `Section_02_2_Analyzing_Algorithms.lean:47-52`：`ThetaBoundedBy` 现提供 Θ-记法包装（O ∩ Ω），等价于标准 Θ 定义。建议未来迁移到 Ch3 的正式 Θ-记法时替换，但当前语义已完整。

## 反驳记录

- **反驳员复核**: 原始审计 13 条 MATCH，提出 1 条差异
- **差异条目**: 2.8（增长量级讨论）——书中声明 Θ(n²) 含上下界，Lean 仅证明 O(n²) 上界
- **降级决定**: 1 条差异未达 ≥2 条独立差异的正式降级阈值，但差异具体可验证，采纳降级（MATCH → MINOR）
- **更新**: `feat/ch02-fixes` 已添加 Ω(n²) 下界，2.8 异议的数学实质已解决，条目恢复为 MATCH

## 各节分布

| 节 | MATCH | MINOR | MAJOR | CRITICAL |
|----|-------|-------|-------|----------|
| §2.1 Insertion Sort | 6 | 4 | 0 | 0 |
| §2.2 Analyzing Algorithms | 10 | 3 | 0 | 0 |
| §2.3 Designing Algorithms | 8 | 3 | 0 | 0 |

**关键发现（2026-08-27 更新）**: 课本层四条 MAJOR 均已闭合。§2.2
现在从符号行成本和 `tᵢ` 轨迹推出完整 `T(n)`，并验证 best/worst
执行表；§2.3 现在具有本地可执行 MERGE、正确性和列表级线性工作量。
保留的 MINOR 主要是不可变 List 与可变数组之间的实现表示差异、论述性
RAM 内容，以及任意规模递推所需的合理单调性技术假设。
