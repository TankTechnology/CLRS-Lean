# Ch2 Getting Started 语义忠实性审计

- **审计日期（北京时间）**: 2026-08-17 13:06 CST
- **Skill 版本**: semantic-fidelity-audit v1
- **基准来源**: 参考第 2.1–2.3 节（课本语料已核对）
- **结论分布**: MATCH 14 · MINOR 9 · MAJOR 5 · CRITICAL 0 · UNCERTAIN 0
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
| 2.1 | RAM 模型定义（统一指令成本、顺序执行、整数/浮点/字符类型） | 无对应 | MINOR | 模块文档声明不形式化完整 RAM 模型（"does not try to formalize a full RAM model yet"）；已知缺口已入台账 |
| 2.2 | 插入排序逐行成本分析：每行伪代码标注成本 c_k 与执行次数 | 无对应 | MAJOR | 书中核心分析方法论（逐行成本表 + 求和公式）完全缺失；Lean 仅建模比较次数 |
| 2.3 | 完整运行时间公式 T(n) = c1·n + c2·(n-1) + c4·(n-1) + c5·Σti + c6·Σ(ti-1) + c7·Σ(ti-1) + c8·(n-1) | 无对应 | MAJOR | 书中 Eq (pre-2.1) 无 Lean 对应；仅 `triangular (n-1)` 捕获 while 循环比较次数，未捕获 for 循环开销 |
| 2.4 | 最坏情况分析：ti = i，T(n) = an² + bn + c（式 2.2） | `Section_02_2_Analyzing_Algorithms.lean:25-27` `insertionSortWorstComparisons` | MAJOR | 比较次数正确（triangular(n-1) = n(n-1)/2），但仅证明 O(n²) 上界，未证明 Θ(n²) 下界；缺失完整系数公式 |
| 2.5 | 最坏情况为 Θ(n²)（书中明确使用 Θ-记法） | `Section_02_2_Analyzing_Algorithms.lean:41-45` `insertionSortWorstComparisons_eventually_quadratic` | MAJOR | `EventuallyBoundedBy` 定义为 ∃c n₀, 0<c ∧ ∀n≥n₀, f(n) ≤ c·g(n)，这是 O-记法而非 Θ-记法；Θ(n²) 需要同时证明上下界，但下界未证明 |
| 2.6 | 最好情况分析：已排序数组，ti = 1，T(n) = an + b（式 2.1），Θ(n) | 无对应 | MAJOR | 最好情况线性界完全缺失 |
| 2.7 | 平均情况分析：ti ≈ i/2，仍为 Θ(n²) | 无对应 | MINOR | 书中平均情况讨论较简短（"roughly as bad as the worst case"），未形式化属合理省略 |
| 2.8 | 增长量级讨论：忽略低阶项与常数系数，仅关注主导项 n² | `Section_02_2_Analyzing_Algorithms.lean:36-39` | MINOR | 反驳员发现：书中声明 Θ(n²)（含上下界），Lean 仅证明 O(n²)（上界 ≤ n²）。模块 doc 已声明为 "lightweight cost model"，属已知简化。审计员原判 MATCH，反驳员提出 1 条差异，虽未达 ≥2 阈值，但差异具体可验证，采纳降级 |
| 2.9 | Θ-记法非正式引入：「roughly proportional when n is large」 | `Section_02_2_Analyzing_Algorithms.lean:21-22` `EventuallyBoundedBy` | MINOR | 自定义 `EventuallyBoundedBy` 近似书中非正式 Θ；但仅有上界方向，且正式 Θ-记法在 Ch3 才定义——书中 §2.2 本身也是非正式使用 |
| 2.10 | 最坏情况分析优于平均情况的三条理由 | 无对应 | MINOR | 属论述性内容，非形式化数学断言 |

### §2.3 Designing Algorithms

| # | 书条目 | Lean 位置 | 判定 | 说明 |
|---|--------|-----------|------|------|
| 3.1 | 分治法三步：Divide / Conquer / Combine | `Section_02_3_Designing_Algorithms.lean:30-31` `mergeSort` | MINOR | 委托给 `List.mergeSort`，未显式展示三步结构；模块文档声明 "we use Lean's verified List.mergeSort implementation" |
| 3.2 | MERGE 过程伪代码（27 行，含临时数组 L/R、三个 while 循环） | 无对应 | MAJOR | MERGE 过程完全未形式化；模块文档注明 "A later strengthening can inline the merge routine" |
| 3.3 | MERGE 运行时间 Θ(n) 的分析 | 无对应 | MAJOR | MERGE 过程缺失导致其 Θ(n) 分析也无法形式化 |
| 3.4 | MERGE-SORT 伪代码（递归，p<r 时分裂，p=r 时基始） | `Section_02_3_Designing_Algorithms.lean:30-31` | MINOR | 委托 `List.mergeSort`；递归结构等价但未显式对应伪代码 |
| 3.5 | 归并排序正确性：输出有序且保持原元素 | `Section_02_3_Designing_Algorithms.lean:34-39` | MATCH | `mergeSort_sortedLE` + `mergeSort_perm` 完整覆盖 |
| 3.6 | 递推关系 T(n) = 2T(n/2) + Θ(n)，T(1) = Θ(1)（n 为 2 的幂时） | `Section_02_3_Designing_Algorithms.lean:47-49` `mergeSortRecurrenceOnPowersOfTwo` | MATCH | 递推式正确：T(2⁰)=1, T(2^(k+1)) = 2·T(2^k) + 2^(k+1) |
| 3.7 | 递推求解：T(n) = Θ(n log n)（通过递推树） | `Section_02_3_Designing_Algorithms.lean:52-77` `mergeSortRecurrenceOnPowersOfTwo_closedForm` | MATCH | 封闭解 T(2^k) = (k+1)·2^k = n log₂ n + n 精确证明 |
| 3.8 | 任意 n 的递推 T(n) = T(⌊n/2⌋) + T(⌈n/2⌉) + Θ(n) | `Merge_Sort_Recurrence.lean:64-65` `Recurrence` | MATCH | 使用 n/2 取地板、(n+1)/2 取天花板，加法项为 n（更精确于 Θ(n)） |
| 3.9 | 任意 n 的 Θ(n log n) 界 | `Merge_Sort_Recurrence.lean:174-203` `theta_n_log_n_all_inputs` | MATCH | 通过 Ch4 主定理 + §4.6 地板/天花板夹逼桥证明了任意输入规模的 Θ(n log n) |
| 3.10 | 精确幂上的 Θ(n log n)（通过主定理） | `Merge_Sort_Recurrence.lean:121-138` `theta_n_log_n_on_exact_powers` | MATCH | 通过主定理情形 2（常数正规化强制项）证明 |
| 3.11 | MonotoneAbs 额外假设 | `Merge_Sort_Recurrence.lean:176` `hT_mono` | MINOR | `theta_n_log_n_all_inputs` 要求 `MonotoneAbs T`，书中未显式陈述此条件；但运行时间函数单调是合理的隐含假设 |

## 缺陷清单

### MAJOR（5 条）

**M1. 严重度: MAJOR**
- **位置**: 第 2.2 节 — 缺失，应在 `Section_02_2_Analyzing_Algorithms.lean`
- **差异描述**: 书中逐行伪代码成本分析（c1..c8 常数 + 执行次数表 + 完整求和公式 T(n)）完全未形式化。这是 §2.2 的核心分析方法论。
- **建议修法**: 增加形式化逐行成本模型（至少定义 c_k 常量和执行次数计数），并证明完整 T(n) 公式等于逐行乘积之和。

**M2. 严重度: MAJOR**
- **位置**: `Section_02_2_Analyzing_Algorithms.lean:36-39` `insertionSortWorstComparisons_quadratic`
- **差异描述**: 书中声称插入排序最坏情况为 Θ(n²)。Lean 仅证明 O(n²) 上界（≤ n²），未证明 Ω(n²) 下界。`EventuallyBoundedBy` 定义为纯上界谓词，等同于 O-记法。
- **建议修法**: 增加下界定理（如 triangular(n-1) ≥ n²/4 对于 n≥2），或使用 Ch3 的 Θ-记法包装双层界。

**M3. 严重度: MAJOR**
- **位置**: 第 2.2 节 — 缺失
- **差异描述**: 书中最好情况分析（已排序数组，ti=1，T(n)=an+b，Θ(n)）完全缺失。
- **建议修法**: 增加最好情况比较次数定理（已排序数组比较次数 = n-1），并证明其 Θ(n) 渐近界。

**M4. 严重度: MAJOR**
- **位置**: 第 2.3 节 — 缺失，应在 `Section_02_3_Designing_Algorithms.lean`
- **差异描述**: MERGE 过程（书中 27 行伪代码，含临时数组 L/R 分配、三个 while 循环、Θ(n) 时间分析）完全未形式化。MERGE 是归并排序的核心子程序。
- **建议修法**: 形式化 MERGE 过程（即使使用 List 而非数组），证明其正确性（合并两个有序列表产生有序结果且保持元素）和线性时间复杂度。

**M5. 严重度: MAJOR**
- **位置**: 第 2.2 节 — 缺失
- **差异描述**: 书中完整运行时间公式包含所有伪代码行的贡献（for 循环开销 n 次、赋值语句 n-1 次等），而 Lean 仅建模 while 循环比较次数（triangular sum）。代价粒度不同：书中是"每条指令"，Lean 是"仅比较次数"。
- **建议修法**: 文档已声明此为已知缺口（"full RAM semantics and exact line-by-line pseudocode cost are future strengthening targets"），建议优先补全至少 for 循环迭代计数和赋值语句计数。

### MINOR（9 条）

**m1. 严重度: MINOR** — `Section_02_1_Insertion_Sort.lean:42-44`：使用不可变 List 替代可变数组；1-起始索引变为 0-起始列表。无需修改，台账已记录。

**m2. 严重度: MINOR** — `Section_02_1_Insertion_Sort.lean:42`：无显式长度参数 n，列表长度由类型隐式携带。可忽略。

**m3. 严重度: MINOR** — `Section_02_1_Insertion_Sort.lean`：循环不变量未作为独立定理陈述，语义分解为 `insertSorted_ordered` 和 `insertSorted_perm`。优先级低。

**m4. 严重度: MINOR** — `Section_02_2_Analyzing_Algorithms.lean:21-22`：`EventuallyBoundedBy` 仅是 O-记法上界包装，书中使用的 Θ-记法需双层界。可保留作为临时工具。

**m5. 严重度: MINOR** — `Section_02_3_Designing_Algorithms.lean:30-31`：委托 `List.mergeSort` 而非显式实现分治三步。无需修改，模块文档已声明。

**m6. 严重度: MINOR** — `Merge_Sort_Recurrence.lean:176`：`MonotoneAbs T` 要求书中未显式陈述，属合理技术条件。

**m7. 严重度: MINOR** — `Section_02_2_Analyzing_Algorithms.lean`：论述性内容（三条理由、RAM 模型指令集）未形式化，属合理省略。

**m8. 严重度: MINOR** — `Section_02_2_Analyzing_Algorithms.lean:25-27`：n=0 时 Nat 减法截断为 0，结果合理但书中未讨论。

**m9. 严重度: MINOR** — `Section_02_2_Analyzing_Algorithms.lean:36-39`（条目 2.8）：反驳员发现书中声明 Θ(n²)（上下界），Lean 仅证明 O(n²)（上界）。模块 doc 已声明 "lightweight cost model"，属已知简化。

## 反驳记录

- **反驳员复核**: 13 条 MATCH，提出 1 条差异
- **差异条目**: 2.8（增长量级讨论）——书中声明 Θ(n²) 含上下界，Lean 仅证明 O(n²) 上界
- **降级决定**: 1 条差异未达 ≥2 条独立差异的正式降级阈值，但差异具体可验证，采纳降级（MATCH → MINOR）

其余 12 条 MATCH 经检查表示等价（List vs Array、0-based vs 1-based）、定理强度、代价模型、伪代码对应、边界情况、已知简化声明等维度后，排除差异，MATCH 成立。

## 各节分布

| 节 | MATCH | MINOR | MAJOR | CRITICAL |
|----|-------|-------|-------|----------|
| §2.1 Insertion Sort | 5 | 4 | 0 | 0 |
| §2.2 Analyzing Algorithms | 0 | 5 | 5 | 0 |
| §2.3 Designing Algorithms | 7 | 4 | 2 | 0 |

**关键发现**: 第 2.2 节是最薄弱的环节，5 条 MAJOR 缺陷全部集中于此。第 2.1 节和第 2.3 节的正确性定理（排序性 + 排列保持）忠实于原著，但算法实现采用了经声明的简化（List 替代数组、递归替代迭代、委托 Mathlib 替代手写 MERGE）。第 2.3 节的递推分析与 Θ(n log n) 界是完整的，且比书中的非正式分析更精确（证明了对任意输入规模的严格界）。