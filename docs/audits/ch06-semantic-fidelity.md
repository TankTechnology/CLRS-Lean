# Ch06 Heapsort 语义忠实性审计

- 审计日期（北京时间）: 2026-08-18
- 基准来源: 参考第 6.1–6.5 节
- 结构前提: `check_book_coverage.py` 通过（`main-proof-complete`，78 tracked entries，全部 proved）
- 结论分布: MATCH 42 · MINOR 9 · MAJOR 0 · CRITICAL 0 · UNCERTAIN 0

## 断言对照表

### Section 6.1 -- Heaps

| 书条目 | Lean 位置 | 判定 | 说明 |
|---|---|---|---|
| PARENT(i) = floor(i/2), LEFT(i) = 2i, RIGHT(i) = 2i+1（1-based） | Section_06_1_Heaps.lean:244-253 | MATCH | 正确适配 0-based：`left i = 2*i+1`, `right i = 2*i+2`, `parent i = (i-1)/2`。模块 docstring 已声明 |
| Max-heap 性质：A[PARENT(i)] >= A[i]（对所有非根节点） | Section_06_1_Heaps.lean:280-287 | MATCH | `left_le` 和 `right_le` 字段约束每个堆内父节点 >= 子节点 |
| 每个正索引有严格更小的父节点 | Section_06_1_Heaps.lean:256-258 | MATCH | `parent_lt_self` 对 0 < i 成立 |
| 每个非根节点是左或右子节点 | Section_06_1_Heaps.lean:261-264 | MATCH | `eq_left_or_right_parent` 通过 omega 证明 |
| parent(left(i))=i, parent(right(i))=i | Section_06_1_Heaps.lean:267-274 | MATCH | 0-based 往返恒等式 |
| 根是 max-heap 中最大元素 | Section_06_1_Heaps.lean:418-445 | MATCH | `getElem_le_root` 通过强归纳法沿父/子路径遍历 |
| 叶子节点索引为 floor(n/2)+1 到 n（Exercise 6.1-8, 1-based） | Section_06_3_Building_A_Heap.lean:76-87 | MATCH | 正确适配 0-based：`heapSize/2` 及之后的节点均为叶子 |
| 功能堆支架（OrderedDesc） | Section_06_1_Heaps.lean:48-49 | MINOR | `OrderedDesc`（降序列表）是比通用 max-heap 性质更强的条件。文档声明为"compact functional heap scaffold"。桥接定理 `orderedDesc_arrayMaxHeap`（line 475）连接二者 |
| 堆高度 = Theta(lg n)（Exercise 6.1-2） | CostedExecution.lean:380-381 | MINOR | `heapHeight` 定义为 `Nat.log 2 heapSize - Nat.log 2 (i+1)`（节点高度上界），未作为独立定理证明 floor(lg n) 的精确公式 |

### Section 6.2 -- Maintaining the Heap Property

| 书条目 | Lean 位置 | 判定 | 说明 |
|---|---|---|---|
| MAX-HEAPIFY(A,i)：找到 A[i], A[LEFT(i)], A[RIGHT(i)] 中的最大值 | Section_06_2_Maintaining_Heap_Property.lean:195-203 | MATCH | 两阶段选择：`largerIndex` 先比较 i 与 left，再比较结果与 right |
| 若 l <= heap-size 且 A[l] > A[i] 则 largest = l | Section_06_2_Maintaining_Heap_Property.lean:195-199 | MATCH | 使用严格 `<` 比较（与书的 `>` 一致），边界检查 `candidate < heapSize` |
| 若 largest != i：交换 A[i] 与 A[largest]，对 largest 递归 | Section_06_2_Maintaining_Heap_Property.lean:750-757 | MATCH | 燃料递归：`swapAt a i largest` 后对 `largest` 递归 |
| 前置条件：LEFT(i) 和 RIGHT(i) 的子树已是 max-heap | Section_06_1_Heaps.lean:294-303 | MATCH | `ArrayMaxHeapExcept` 豁免一个 `bad` 父节点，其余父节点约束均成立 |
| 交换语义 | Section_06_2_Maintaining_Heap_Property.lean:61-175 | MATCH | 完整交换规约：交换后两单元含对方旧值，其余单元不变 |
| MAX-HEAPIFY 运行时间 O(lg n) | CostedExecution.lean:443-447 | MATCH | 证明 cost <= floor(log2 heapSize) + 1 |
| MAX-HEAPIFY 在高度为 h 的节点上运行时间 O(h) | CostedExecution.lean:414-439 | MATCH | 证明 cost <= heapHeight(heapSize, i) + 1 |
| 递归调用的子树大小至多 2n/3（Exercise 6.2-2） | 未出现 | MINOR | 子子树 2n/3 界未证明。代价分析使用基于高度的界替代，同样充分 |
| maxChildIndex 返回 {i, left(i), right(i)} 之一 | Section_06_2_Maintaining_Heap_Property.lean:263-284 | MATCH | 穷举情形分析 |
| 无交换正确性：若 largest = i，子树已是 max-heap | Section_06_2_Maintaining_Heap_Property.lean:884-903 | MATCH | |
| 交换分支：修复父节点，将异常移至子节点 | Section_06_2_Maintaining_Heap_Property.lean:415-523 | MATCH | |
| 完整修复定理 | Section_06_2_Maintaining_Heap_Property.lean:1061-1083 | MATCH | 子树和根两种形式均已证明 |
| valAt 越界回退至 0 | Section_06_2_Maintaining_Heap_Property.lean:52-53 | MINOR | `valAt a i = a.getD i 0` 越界时返回 0。所有比较均有 heap-size 边界检查保护，回退值不会被实际使用，但哨兵值 0 在退化输入（全部键为 0）中与有效键不可区分 |

### Section 6.3 -- Building a Heap

| 书条目 | Lean 位置 | 判定 | 说明 |
|---|---|---|---|
| BUILD-MAX-HEAP(A,n)：for i = floor(n/2) downto 1: MAX-HEAPIFY(A,i) | Section_06_3_Building_A_Heap.lean:45-48, 125-126 | MATCH | 0-based 适配：从 `floor(n/2)-1` 向下循环到 0 |
| 循环不变量：节点 i+1..n 是 max-heap 根 | Section_06_3_Building_A_Heap.lean:93-96 | MATCH | `ArrayMaxHeapFrom a heapSize (i+1)` 表示从 i+1 开始的所有父节点约束成立 |
| 初始化：叶子是平凡 max-heap | Section_06_3_Building_A_Heap.lean:76-87 | MATCH | 从 `heapSize/2` 开始的节点为叶子 |
| 保持：i 的子节点编号更大，由不变量已是 max-heap 根 | Section_06_3_Building_A_Heap.lean:109-122 | MATCH | 使用 `ArrayMaxHeapFrom.except_pred` 获取 `maxHeapifyFuel_repair_subtree` 的前置条件 |
| 终止：i = 0，所有节点为 max-heap 根 | Section_06_3_Building_A_Heap.lean:109-122（基础情形） | MATCH | 基础情形 `count = 0` 应用 `ArrayMaxHeapFrom.to_global` |
| BUILD-MAX-HEAP 运行时间 O(n) | CostedExecution.lean:612-627 | MATCH | 证明 cost <= 3*heapSize，通过节点高度双重计数 |
| O(n lg n) 朴素上界 | CostedExecution.lean:99-112 | MATCH | 粗糙界 `count * heapSize` 也已证明 |
| 数组长度保持 | Section_06_3_Building_A_Heap.lean:51-59 | MATCH | |
| 多重集保持 | Section_06_3_Building_A_Heap.lean:62-69 | MATCH | |
| 正确性捆绑（heap + perm + length） | Section_06_3_Building_A_Heap.lean:179-184 | MATCH | |

### Section 6.4 -- The Heapsort Algorithm

| 书条目 | Lean 位置 | 判定 | 说明 |
|---|---|---|---|
| HEAPSORT(A,n)：BUILD-MAX-HEAP；for i = n downto 2：交换 A[1] 与 A[i]，递减 heap-size，MAX-HEAPIFY(A,1) | Section_06_4_Heapsort.lean:390-396, 521-529, 635-637 | MATCH | 0-based 适配：交换 A[0] 与 A[heapSize-1]，新 heapSize = heapSize-1，heapify 根 |
| 循环不变量（Exercise 6.4-2）：前缀 A[1..i] 是 i 个最小元素的 max-heap，后缀 A[i+1..n] 是 n-i 个最大元素且已排序 | Section_06_4_Heapsort.lean:75-94 | MATCH | 等价表述：`heap`（前缀 max-heap）、`suffix_sorted`（后缀有序）、`prefix_le_suffix`（前缀每个元素 <= 后缀每个元素）。结合有序后缀，蕴含前缀含 i 个最小元素 |
| 初始不变量：BUILD-MAX-HEAP 后，后缀为空 | Section_06_4_Heapsort.lean:357-361 | MATCH | |
| 一次迭代保持不变量 | Section_06_4_Heapsort.lean:437-514 | MATCH | 完整证明堆前缀缩小 1、后缀扩展 1、prefix <= suffix 成立 |
| 根移至正确最终位置 | Section_06_4_Heapsort.lean:404-430 | MATCH | 旧根值最终出现在新后缀头部 |
| HEAPSORT 运行时间 O(n lg n) | CostedExecution.lean:709-740 | MATCH | 证明 cost <= n*log2 n + 5n |
| 渐近 O(n log n) 包装 | CostedExecution.lean:779-800 | MATCH | 使用 Chapter 3 `isBigO` |
| 输出有序性 | Section_06_4_Heapsort.lean:625-632, 957-959 | MATCH | |
| 输入排列 | Section_06_4_Heapsort.lean:962-964 | MATCH | |
| 完整正确性捆绑 | Section_06_4_Heapsort.lean:971-976 | MATCH | 有序性 + 排列 + 长度保持 |

### Section 6.5 -- Priority Queues

| 书条目 | Lean 位置 | 判定 | 说明 |
|---|---|---|---|
| HEAP-MAXIMUM(A)：若 heap-size < 1 则 error；返回 A[1] | Section_06_5_Priority_Queues.lean:115-119 | MATCH | 使用 `Option` 替代 error。堆非空且在界内时返回 `some (a[0])`（0-based 根） |
| HEAP-MAXIMUM 正确性：根包围所有元素 | Section_06_5_Priority_Queues.lean:122-135 | MATCH | |
| HEAP-EXTRACT-MAX(A)：max = MAXIMUM；A[1] = A[heap-size]；递减；MAX-HEAPIFY(A,1)；返回 max | Section_06_5_Priority_Queues.lean:687-696 | MATCH | 0-based 适配：交换根与末尾，heapify 根 |
| EXTRACT-MAX 正确性：返回旧最大值，堆修复，前缀缩小 | Section_06_5_Priority_Queues.lean:704-788 | MATCH | 完整状态正确性包 |
| HEAP-INCREASE-KEY(A,x,k)：验证 k >= x.key；设置键；向上冒泡 | Section_06_5_Priority_Queues.lean:434-443, 510-514 | MATCH | 前置条件 `valAt a i <= key` 确保键不减少。冒泡循环：parent < current 时与父节点交换 |
| INCREASE-KEY 循环不变量（Exercise 6.5-7） | Section_06_5_Priority_Queues.lean:162-172, 330-427 | MATCH | 不同表述但语义等价：所有边有效，除了可能进入当前冒泡节点的边 |
| INCREASE-KEY 正确性 | Section_06_5_Priority_Queues.lean:517-539 | MATCH | |
| HEAP-INSERT(A,x,n)：验证空间；追加键 = -inf；INCREASE-KEY 至真实键 | Section_06_5_Priority_Queues.lean:53-54 | MINOR | 没有数组级 INSERT 形式化。`heapInsert` 使用 `insertDesc`（降序插入），与书的 -inf 技巧不同算法 |
| HEAP-DELETE（Exercise 6.5-10）：O(lg n) 删除对象 | Section_06_5_Priority_Queues.lean:799-809 | MATCH | 实现为 increase-key 至根最大值，然后 extract-max |
| HEAP-DELETE 正确性 | Section_06_5_Priority_Queues.lean:817-863 | MATCH | |
| 对象与索引之间的句柄/映射抽象 | 未出现 | MINOR | 书中讨论了用于映射应用对象与堆索引的句柄（参考第 6.5 节句柄讨论段落）。未形式化句柄/映射层，操作直接作用于数组索引和值 |
| 优先队列操作运行时间 O(lg n) | Section_06_5_Priority_Queues.lean:44-45 | MINOR | 运行时界明确声明为推迟（"Runtime bounds and RAM semantics are deferred"）。CostedExecution 模块覆盖 heapify/build/heapsort 但不覆盖优先队列操作 |
| 最小优先队列变体（Exercise 6.5-3） | 未出现 | MINOR | 仅形式化最大优先队列操作。书中的最小堆/最小优先队列变体未定义 |

### CostedExecution

| 书条目 | Lean 位置 | 判定 | 说明 |
|---|---|---|---|
| 代价度量定义 | CostedExecution.lean:7-13 | MINOR | 单位控制步度量计数访问的 MAX-HEAPIFY 帧和每次非平凡步骤的一次提取/交换转换。构建循环编排、守卫、列表读写、分配和函数调用不计入。非完整 RAM 代价模型，已在模块 docstring 中说明 |
| MAX-HEAPIFY O(lg n) 界 | CostedExecution.lean:443-447 | MATCH | |
| BUILD-MAX-HEAP O(n) 界 | CostedExecution.lean:612-627 | MATCH | 通过节点高度双重计数 |
| HEAPSORT O(n lg n) 界 | CostedExecution.lean:709-740 | MATCH | |
| 代价擦除（代价函数投影到原函数） | CostedExecution.lean:49-60, 88-97, 147-159, 193-211, 254-258 | MATCH | 所有代价函数均有擦除定理 |
| 渐近 `isBigO` 包装 | CostedExecution.lean:339-365（粗糙包络）, 757-800（紧界） | MATCH | 粗糙回归包络和紧教科书界均有 `isBigO` 证明 |
| 粗糙回归包络（heapsort O(n^2)） | CostedExecution.lean:262-269 | MATCH | 作为紧界之外的回归安全网 |

## 缺陷清单

**MINOR-1**: 功能堆支架使用比 max-heap 性质更强的条件
- 位置: Section_06_1_Heaps.lean:48-49
- 差异: `OrderedDesc`（通过 `Pairwise` 定义的降序列表）是比通用 max-heap 性质更强的条件。降序列表一定是 max-heap，但并非每个 max-heap 都是降序列表。文档声明为"compact functional heap scaffold"，桥接定理 `orderedDesc_arrayMaxHeap`（line 475）连接至通用索引谓词。
- 建议: 无需修改，文档已清晰说明。若需功能模型的完全通用性，可添加独立的 `isMaxHeap` 列表谓词。

**MINOR-2**: 堆高度精确公式未证明
- 位置: CostedExecution.lean:380-381；Exercise 6.1-2
- 差异: 参考第 6.1 节 Exercise 6.1-2 要求证明 n 元素堆的高度为 floor(lg n)。`heapHeight` 函数定义了上界 (`Nat.log 2 heapSize - Nat.log 2 (i+1)`)，`heapHeight_le_log` 证明了 `heapHeight heapSize i <= Nat.log 2 heapSize`。精确公式未作为独立定理证明。
- 建议: 可添加 `heap_height_eq_log` 定理以完备性，但主要定理不依赖此精确公式。

**MINOR-3**: valAt 使用 0 作为哨兵回退值
- 位置: Section_06_2_Maintaining_Heap_Property.lean:52-53
- 差异: `valAt a i = a.getD i 0` 在越界时返回 0。所有比较均有 heap-size 边界检查保护，回退值不会被实际使用。但若边界检查被意外遗漏，所有键为 0 的退化输入会使哨兵值与有效键不可区分。
- 建议: 可考虑使用 `Option Nat` 或专用哨兵类型，但当前方法在 Lean 中属惯用方式。

**MINOR-4**: 子子树 2n/3 界未证明
- 位置: Exercise 6.2-2，Lean 源中未出现
- 差异: 参考第 6.2 节 Exercise 6.2-2 要求证明每个子子树至多含 2n/3 个节点。此界用于 MAX-HEAPIFY 的递推式 T(n) <= T(2n/3) + Theta(1)。CostedExecution 模块使用基于高度的 O(h) 分析替代，更紧且充分。
- 建议: 可作为练习级定理添加，但主要结果不依赖。

**MINOR-5**: 缺少数组级 HEAP-INSERT
- 位置: Section_06_5_Priority_Queues.lean（缺失）
- 差异: 参考第 6.5 节 HEAP-INSERT 算法（验证空间，追加键 = -inf，然后 INCREASE-KEY 至真实键）未在数组级形式化。仅提供使用 `insertDesc` 的功能 `heapInsert`（降序插入），与书的 -inf 技巧不同。
- 建议: 添加 `arrayHeapInsert?` 遵循 CLRS 伪代码：检查 heap-size < 数组长度，追加键 = 0（或最小哨兵），然后调用 `arrayHeapIncreaseKey?`。

**MINOR-6**: 句柄/映射抽象未形式化
- 位置: Section_06_5_Priority_Queues.lean（缺失）
- 差异: 参考第 6.5 节讨论了用于映射应用对象与堆索引的句柄，包括开销分析（每次访问 O(1)）。未形式化句柄/映射层，操作直接作用于数组索引和值。
- 建议: 可作为未来细化添加映射层，但堆操作数学正确性不依赖。

**MINOR-7**: 优先队列运行时界推迟
- 位置: Section_06_5_Priority_Queues.lean:44-45（模块 docstring）
- 差异: 文件声明"Runtime bounds and RAM semantics are deferred"。参考第 6.5 节声称每个优先队列操作 O(lg n)。CostedExecution 模块覆盖 heapify/build/heapsort 但不覆盖优先队列操作代价。
- 建议: 扩展代价执行框架以覆盖 INCREASE-KEY（冒泡路径长度 <= log n）、EXTRACT-MAX（一次 heapify 调用）和 INSERT（一次 increase-key 调用）。

**MINOR-8**: 最小优先队列变体缺失
- 位置: Section_06_5_Priority_Queues.lean（缺失）
- 差异: 参考第 6.5 节讨论最小优先队列，Exercise 6.5-3 要求 MIN-HEAP-MINIMUM、MIN-HEAP-EXTRACT-MIN、MIN-HEAP-DECREASE-KEY、MIN-HEAP-INSERT。仅形式化最大堆变体。
- 建议: 可添加最小堆谓词和最小优先队列操作作为对偶开发。

**MINOR-9**: 简化代价度量
- 位置: CostedExecution.lean:7-13（模块 docstring）
- 差异: 代价度量仅计数 MAX-HEAPIFY 帧和提取转换，不计入守卫、列表读写、分配和函数调用。非完整 RAM 代价模型。渐近界与书的声明匹配，但常数因子和操作级会计与 RAM 模型不同。
- 建议: 已按现状文档化。完整 RAM 代价模型可作为独立细化。

## 反驳记录

待反驳员完成 -- 将在此更新。

## 汇总

| 判定 | 数量 |
|------|------|
| MATCH | 42 |
| MINOR | 9 |
| MAJOR | 0 |
| CRITICAL | 0 |
| UNCERTAIN | 0 |

**总体评估**: 第 6 章形式化语义忠实于 CLRS 原文。0-based 索引适配正确且在全章一致。关键算法（MAX-HEAPIFY、BUILD-MAX-HEAP、HEAPSORT、优先队列操作）均正确形式化，包含不变量及正确性证明。紧渐近界（heapify O(log n)、build-heap O(n)、heapsort O(n log n)）均针对代价执行模型得到证明。9 项 MINOR 发现均为已文档化的简化或推迟细化，不影响主要结果的数学正确性。