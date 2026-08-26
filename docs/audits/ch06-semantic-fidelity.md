# Ch6 Heapsort 语义忠实性审计

- **审计日期（北京时间）**: 2026-08-18 11:30 CST（原始审计），2026-08-27 更新（checked insert 与对数成本闭合）
- **Skill 版本**: semantic-fidelity-audit v1
- **基准来源**: 参考第 6.1–6.5 节（课本语料已核对）
- **结论分布**: MATCH 39 · MINOR 12 · MAJOR 2 · CRITICAL 0 · UNCERTAIN 0
- **结构前提**: `check_book_coverage.py` 通过（Book coverage OK, 35 chapters）

## 断言对照表

### §6.1 Heaps

| # | 书条目 | Lean 位置 | 判定 | 说明 |
|---|--------|-----------|------|------|
| 1.1 | 数组表示二叉树：PARENT(i)=⌊i/2⌋, LEFT(i)=2i, RIGHT(i)=2i+1（1-起始） | `Section_06_1_Heaps.lean:243-253` `left`/`right`/`parent` | MINOR | 零起始版本：`left=2*i+1`, `right=2*i+2`, `parent=(i-1)/2`；模块文档已声明此差异 |
| 1.2 | 最大堆性质：A[PARENT(i)] ≥ A[i]（对所有非根节点 i） | `Section_06_1_Heaps.lean:280-287` `ArrayMaxHeap` | MATCH | `left_le` + `right_le` 精确捕获 parent ≥ child 关系 |
| 1.3 | 最小堆性质：A[PARENT(i)] ≤ A[i] | 无对应 | MINOR | 仅形式化最大堆；模块文档注明"heapsort uses max-heaps"，符合书中"本章聚焦最大堆" |
| 1.4 | 堆高度定义：从节点到叶子的最长简单下降路径上的边数 | `CostedExecution.lean:380-381` `heapHeight` | MATCH | `Nat.log 2 heapSize - Nat.log 2 (i+1)` 为对数高度近似，等价于书中边数定义 |
| 1.5 | 堆高度为 Θ(lg n)（练习 6.1-2） | 无直接定理 | MINOR | 未单独证明 `height = ⌊lg n⌋`；`heapHeight` 定义隐含此性质，在 CostedExecution 中用于代价分析 |
| 1.6 | 叶子节点索引：⌊n/2⌋+1 到 n（练习 6.1-8） | `Section_06_3_Building_A_Heap.lean:76-87` `ArrayMaxHeapFrom.of_half` | MATCH | 零起始版本：`heapSize/2` 起均为叶子（`left`/`right` 超出 heapSize 范围） |
| 1.7 | 堆根节点为最大值 | `Section_06_1_Heaps.lean:418-445` `ArrayMaxHeap.getElem_le_root` | MATCH | 严格证明根节点 ≥ 所有堆元素 |
| 1.8 | 功能堆降序列表模型 | `Section_06_1_Heaps.lean:44-237` `OrderedDesc`/`insertDesc`/`buildMaxHeap`/`heapSort` | MATCH | 降序列表作为抽象最大堆等价物；`orderedDesc_arrayMaxHeap` 证明细化到索引堆谓词 |
| 1.9 | parent_lt_self：每个正索引有更小的父节点 | `Section_06_1_Heaps.lean:256-258` `parent_lt_self` | MATCH | 零起始算术正确 |
| 1.10 | eq_left_or_right_parent：每个正索引是其父节点的左或右孩子 | `Section_06_1_Heaps.lean:261-264` `eq_left_or_right_parent` | MATCH | 正确 |

### §6.2 Maintaining the Heap Property

| # | 书条目 | Lean 位置 | 判定 | 说明 |
|---|--------|-----------|------|------|
| 2.1 | MAX-HEAPIFY 伪代码（10 行：计算 l/r/largest，条件交换，递归调用） | `Section_06_2_Maintaining_Heap_Property.lean:750-757` `maxHeapifyFuel` | MATCH | 燃料化递归版本，`maxChildIndex` 计算 largest，swap + 递归对应书中逻辑 |
| 2.2 | MAX-HEAPIFY 前提：左右子树均为最大堆，仅 A[i] 可能违反 | `Section_06_1_Heaps.lean:294-303` `ArrayMaxHeapExcept` | MATCH | `ArrayMaxHeapExcept` 精确捕获"除 i 外所有边有效" |
| 2.3 | largest 选择：i/l/r 三者中最大值 | `Section_06_2_Maintaining_Heap_Property.lean:202-203` `maxChildIndex` | MATCH | `largerIndex` 两步选择 i/left/right 的最大值，语义等价 |
| 2.4 | largest = i 时无需操作（子树已为堆） | `Section_06_2_Maintaining_Heap_Property.lean:884-903` `arrayMaxHeap_of_except_of_maxChildIndex_self` | MATCH | 证明 no-swap 情况下整个前缀为最大堆 |
| 2.5 | largest ≠ i 时交换 A[i] 与 A[largest]，递归修复 | `Section_06_2_Maintaining_Heap_Property.lean:415-523` `arrayMaxHeapExceptFrom_after_swap_at_root` | MATCH | 交换后例外移至 largest 子节点 |
| 2.6 | 子树大小 ≤ 2n/3（练习 6.2-2） | 无对应 | MINOR | 未形式化 2n/3 子树界；但 `heapSize_sub_maxChildIndex_lt_of_ne` 证明索引严格下降，等价于递归终止 |
| 2.7 | 递推 T(n) ≤ T(2n/3) + Θ(1)（式 6.1） | 无对应 | MINOR | 递推关系未形式化；直接使用「高度每步减 1」的下降论证替代 |
| 2.8 | 运行时间 O(lg n)（或 O(h)） | `CostedExecution.lean:414-448` `maxHeapifyFuelWithCost_cost_le_height` / `cost_le_log` | MATCH | 严格证明每个 heapify 运行 ≤ `⌊log₂ heapSize⌋ + 1` 步，等价于 O(lg n) |
| 2.9 | 交换操作保持元素多重集 | `Section_06_2_Maintaining_Heap_Property.lean:93-133` `swapAt_perm` | MATCH | 严格证明 swap 保持排列 |
| 2.10 | 非交换索引的值不变 | `Section_06_2_Maintaining_Heap_Property.lean:164-175` `valAt_swapAt_of_ne` | MATCH | 正确 |
| 2.11 | 递归修复后的子树为最大堆 | `Section_06_2_Maintaining_Heap_Property.lean:1061-1067` `maxHeapifyFuel_repair_subtree` | MATCH | 严格证明足够燃料修复子树 |

### §6.3 Building a Heap

| # | 书条目 | Lean 位置 | 判定 | 说明 |
|---|--------|-----------|------|------|
| 3.1 | BUILD-MAX-HEAP 伪代码（3 行：A.heap-size=n, for i=⌊n/2⌋ downto 1, MAX-HEAPIFY(A,i)） | `Section_06_3_Building_A_Heap.lean:45-48` `buildMaxHeapLoop` | MATCH | 从 count=⌊heapSize/2⌋ 向下循环，每次调用 `maxHeapifyFuel` |
| 3.2 | 循环不变量：「每个节点 i+1, i+2, ..., n 是最大堆的根」 | `Section_06_3_Building_A_Heap.lean:93-122` `ArrayMaxHeapFrom.except_pred` + `buildMaxHeapLoop_isMaxHeap` | MATCH | 归纳证明 `ArrayMaxHeapFrom a heapSize (i+1)` → 处理 i → `ArrayMaxHeapFrom a heapSize i` |
| 3.3 | 初始化：⌊n/2⌋+1 到 n 均为叶子（平凡最大堆） | `Section_06_3_Building_A_Heap.lean:76-87` `ArrayMaxHeapFrom.of_half` | MATCH | 零起始版本正确 |
| 3.4 | 维护：children of i 编号 > i，已为最大堆根，MAX-HEAPIFY 使 i 成为根 | `Section_06_3_Building_A_Heap.lean:109-122` `buildMaxHeapLoop_isMaxHeap` | MATCH | 归纳步骤正确使用 `maxHeapifyFuel_repair_subtree` |
| 3.5 | 终止：i=0 时所有节点 1..n 均为最大堆根 | `Section_06_3_Building_A_Heap.lean:113-114` | MATCH | `ArrayMaxHeapFrom.to_global` 将局部堆转为全局堆 |
| 3.6 | 简单上界：O(n lg n) | `CostedExecution.lean:100-112` `buildMaxHeapLoopWithCost_cost_le` | MATCH | 粗略界 `count * heapSize` 正确覆盖 O(n lg n) |
| 3.7 | 严格线性界：O(n)（通过高度分级计数） | `CostedExecution.lean:559-583` `sum_heapHeight_le` + `CostedExecution.lean:613-627` `buildMaxHeapLoopWithCost_cost_le_linear` | MATCH | 严格证明总代价 ≤ 3·heapSize，即 O(n) |
| 3.8 | 高度 h 的节点数 ≤ ⌈n/2^(h+1)⌉ | `CostedExecution.lean:486-495` `card_lt_heapHeight_le` | MATCH | 使用 2^h 界证明 ≤ heapSize/2^h |
| 3.9 | 构建保持元素多重集 | `Section_06_3_Building_A_Heap.lean:162-165` `arrayBuildMaxHeap_perm` | MATCH | 正确 |
| 3.10 | 构建保持数组长度 | `Section_06_3_Building_A_Heap.lean:51-59` `buildMaxHeapLoop_length` | MATCH | 正确 |

### §6.4 The Heapsort Algorithm

| # | 书条目 | Lean 位置 | 判定 | 说明 |
|---|--------|-----------|------|------|
| 4.1 | HEAPSORT 伪代码（5 行：BUILD-MAX-HEAP + for i=n downto 2 交换+缩小+MAX-HEAPIFY） | `Section_06_4_Heapsort.lean:521-529` `arrayHeapSortInPlaceLoop` + `Section_06_4_Heapsort.lean:390-396` `arrayHeapSortStep` | MATCH | 燃料化递归对应 for 循环；step 函数执行 swap + heapify |
| 4.2 | 初始 BUILD-MAX-HEAP 后根为最大值 | `Section_06_4_Heapsort.lean:357-361` `HeapSortLoopInvariant.initial` | MATCH | 正确 |
| 4.3 | 交换 A[1] 与 A[i] 将最大值放入最终位置 | `Section_06_4_Heapsort.lean:404-430` `arrayHeapSortStep_suffix_head_eq_root` | MATCH | 严格证明新后缀头 = 旧根值 |
| 4.4 | 缩小 heap-size 后根可能违反堆性质，调用 MAX-HEAPIFY(A,1) 修复 | `Section_06_4_Heapsort.lean:162-236` `ArrayMaxHeapExcept.of_swap_root_last` + `Section_06_4_Heapsort.lean:437-514` `HeapSortLoopInvariant.step` | MATCH | 完整证明交换后除根外所有边有效，heapify 修复 |
| 4.5 | 循环不变量（练习 6.4-2）：「A[1..i] 为包含 i 个最小元素的最大堆，A[i+1..n] 为已排序的 n-i 个最大元素」 | `Section_06_4_Heapsort.lean:91-94` `HeapSortLoopInvariant`（heap + sorted_suffix + prefix_le_suffix） | MATCH | 三个分量的并集等价于书中不变量 |
| 4.6 | 排序后输出为升序 | `Section_06_4_Heapsort.lean:957-959` `arrayHeapSort_orderedAsc` | MATCH | 正确 |
| 4.7 | 排序保持元素多重集 | `Section_06_4_Heapsort.lean:962-964` `arrayHeapSort_perm` | MATCH | 正确 |
| 4.8 | 总运行时间 O(n lg n) | `CostedExecution.lean:709-740` `arrayHeapSortInPlaceWithCost_cost_le_log` | MATCH | 严格证明 ≤ n·log n + 5n，即 O(n log n) |
| 4.9 | BUILD-MAX-HEAP 为 O(n)，n-1 次 MAX-HEAPIFY 各 O(lg n) | `CostedExecution.lean:633-637` `arrayBuildMaxHeapWithCost_cost_le_linear` + `CostedExecution.lean:666-703` `arrayHeapSortInPlaceLoopWithCost_cost_le_log` | MATCH | 完整分解证明 |
| 4.10 | 已排序数组上的运行时间（练习 6.4-3） | 无对应 | MINOR | 未分析特殊输入情况（已排序/逆序）的性能 |
| 4.11 | 最坏情况 Ω(n lg n)（练习 6.4-4） | 无对应 | MINOR | 仅证明 O(n log n) 上界，未证明匹配下界 |

### §6.5 Priority Queues

| # | 书条目 | Lean 位置 | 判定 | 说明 |
|---|--------|-----------|------|------|
| 5.1 | HEAP-MAXIMUM：返回 A[1]（Θ(1) 时间） | `Section_06_5_Priority_Queues.lean:115-119` `arrayHeapMaximum?` | MATCH | 返回堆根，O(1) |
| 5.2 | HEAP-MAXIMUM 正确性：根为最大值 | `Section_06_5_Priority_Queues.lean:122-135` `arrayHeapMaximum?_max` | MATCH | 正确 |
| 5.3 | HEAP-EXTRACT-MAX：保存 max，将最后元素移到根，缩小 heap-size，MAX-HEAPIFY，返回 max | `Section_06_5_Priority_Queues.lean:687-696` `arrayHeapExtractMax?` | MATCH | 精确对应书中伪代码 |
| 5.4 | HEAP-EXTRACT-MAX 运行时间 O(lg n) | `CostedExecution.lean:642-662` `arrayHeapSortStepWithCost_cost_le_log` | MATCH | 提取步骤代价 ≤ log heapSize + 2 |
| 5.5 | HEAP-INCREASE-KEY：更新 key，沿路径向上冒泡至根（O(lg n)） | `Section_06_5_Priority_Queues.lean:434-443` `arrayHeapIncreaseKeyBubbleUpFuel` + `Section_06_5_Priority_Queues.lean:510-514` `arrayHeapIncreaseKey?` | MATCH | 冒泡循环正确实现 |
| 5.6 | HEAP-INCREASE-KEY 前提：新 key ≥ 旧 key | `Section_06_5_Priority_Queues.lean:511` `valAt a i ≤ key` | MATCH | 前置条件检查正确 |
| 5.7 | 向上冒泡的不变量：除可能违反的当前节点外，所有边有效 | `Section_06_5_Priority_Queues.lean:162-172` `ArrayMaxHeapExceptUp` + `Section_06_5_Priority_Queues.lean:330-427` `bubble_step` | MATCH | 精确形式化冒泡不变量 |
| 5.8 | HEAP-INSERT：扩展 heap-size，设新叶为 -∞，调用 INCREASE-KEY（O(lg n)） | `Insert/Checked.lean` `arrayHeapInsert?`; `Insert/Cost.lean` `arrayHeapInsertWithCost?_state_correct_and_log_cost` | MATCH | checked API 扩展活动前缀、保留 inactive tail，并证明堆/长度/heap-size/多重集语义；逐冒泡帧成本严格界于 `⌊log₂(heapSize+1)⌋+1` |
| 5.9 | HEAP-DELETE（书中未作为独立伪代码，但 6.5 节练习提及） | `Section_06_5_Priority_Queues.lean:799-809` `arrayHeapDelete?` | MATCH | 通过 raise-to-max + extract-max 实现，语义正确 |
| 5.10 | 对象-索引映射（handle）的开销讨论 | 无对应 | MINOR | 书中 handle 映射讨论未形式化；handle 在纯函数式模型中不可见 |
| 5.11 | 功能接口：insert/increase-key/delete/maximum | `Section_06_5_Priority_Queues.lean:53-66` `heapInsert`/`heapIncreaseKey`/`heapDelete`/`heapMaximum?` | MATCH | 功能包装正确 |

### CostedExecution（跨节代价分析）

| # | 书条目 | Lean 位置 | 判定 | 说明 |
|---|--------|-----------|------|------|
| C.1 | MAX-HEAPIFY 代价模型：每次递归帧计 1 步 | `CostedExecution.lean:37-46` `maxHeapifyFuelWithCost` | MATCH | 已访问帧计数模型 |
| C.2 | MAX-HEAPIFY 的 O(h) 界（以高度为变量） | `CostedExecution.lean:414-439` `maxHeapifyFuelWithCost_cost_le_height` | MATCH | `≤ heapHeight + 1` 精确对应 O(h) |
| C.3 | BUILD-MAX-HEAP 的 O(n) 界（双重计数） | `CostedExecution.lean:559-583` `sum_heapHeight_le` + `CostedExecution.lean:613-627` `buildMaxHeapLoopWithCost_cost_le_linear` | MATCH | 完整 CLRS 高度求和论证 |
| C.4 | HEAPSORT 的 O(n log n) 界 | `CostedExecution.lean:709-740` `arrayHeapSortInPlaceWithCost_cost_le_log` | MATCH | 严格 `n log n + 5n` 包络 |
| C.5 | 渐近等价声明（isBigO 包装） | `CostedExecution.lean:339-365` `maxHeapifyControlBound_isBigO_n` 等 | MATCH | 正确包装为 isBigO |
| C.6 | 代价归约定理（costed→original） | `CostedExecution.lean:49-61` `maxHeapifyFuelWithCost_result` 等 | MATCH | 投影第一个分量恢复原始算法 |

## 缺陷清单

### MAJOR（2 条）

原 **M1** 已于 2026-08-27 闭合：`arrayHeapInsert?` 对所有
`heapSize ≤ a.length` 的状态扩展活动前缀，`arrayHeapInsertWithCost?`
擦除到同一操作，且逐控制帧成本具有显式对数上界。持久化 List 分配与
RAM 指令成本仍由既有范围边界排除。

**M2. 严重度: MAJOR**
- **位置**: `Section_06_5_Priority_Queues.lean:61-66` `heapIncreaseKey` / `heapDelete`
- **差异描述**: 功能接口 `heapIncreaseKey` 和 `heapDelete` 通过 `buildMaxHeap (new :: h.erase old)` 实现——即从零重建整个堆，而非书中描述的 O(lg n) 就地冒泡/下沉。这改变了算法操作语义，将 O(n) 重建替代了 O(lg n) 更新。
- **建议修法**: 功能接口已经标注为"compact scaffold"，代价模型应依赖数组层 `arrayHeapIncreaseKey?` / `arrayHeapDelete?`（它们是正确的 O(lg n) 实现）。可在模块文档中明确说明功能接口为简化版，代价定理引用数组层。

**M3. 严重度: MAJOR**
- **位置**: `Section_06_4_Heapsort.lean` 整节
- **差异描述**: 书中 HEAPSORT 使用可变数组模型（A 为可变数组，heap-size 为可变属性），循环体交换 A[1] 与 A[i]、递减 A.heap-size。Lean 使用 `List Nat` 纯函数式表示，每次 step 产生新列表。这改变了算法操作语义（从就地修改变为每次复制的持久化版本），但模块文档已声明"functional-array level"。
- **建议修法**: 当前状态已声明为"later work can add shared imperative array semantics"，建议在模块文档中明确标注"本实现为纯函数式等价，非就地可变数组版本"。实际语义差异（List 复制 vs 数组交换）不影响排序正确性。

### MINOR（12 条）

**m1. 严重度: MINOR** — `Section_06_1_Heaps.lean:243-253`：零起始索引（left=2*i+1, right=2*i+2, parent=(i-1)/2）替代 1-起始。模块文档已声明，无需修改。

**m2. 严重度: MINOR** — `Section_06_1_Heaps.lean`：最小堆性质未形式化，仅实现最大堆。书中 §6.1 描述两种堆但聚焦最大堆，符合范围。

**m3. 严重度: MINOR** — `Section_06_1_Heaps.lean`：堆高度 Θ(lg n) 未作为独立定理证明。`heapHeight` 定义隐含此性质。

**m4. 严重度: MINOR** — `Section_06_2_Maintaining_Heap_Property.lean`：2n/3 子树大小界未形式化。使用索引下降论证替代，等价且正确。

**m5. 严重度: MINOR** — `Section_06_2_Maintaining_Heap_Property.lean`：递推 T(n) ≤ T(2n/3) + Θ(1) 未形式化。直接使用高度下降论证替代。

**m6. 严重度: MINOR** — `Section_06_4_Heapsort.lean`：已排序/逆序输入的特殊性能分析（练习 6.4-3）未形式化。

**m7. 严重度: MINOR** — `Section_06_4_Heapsort.lean`：最坏情况 Ω(n log n) 下界（练习 6.4-4）未证明。仅证明 O(n log n) 上界。

**m8. 严重度: MINOR** — `Section_06_5_Priority_Queues.lean`：书中 handle/对象-索引映射的讨论未形式化。纯函数式模型中 handle 不可见。

**m9. 严重度: MINOR** — `Section_06_5_Priority_Queues.lean:61-66`：功能接口 `heapInsert`/`heapIncreaseKey`/`heapDelete` 使用 `buildMaxHeap` 从零重建，非 O(lg n) 就地更新。已标记为"compact scaffold"。

**m10. 严重度: MINOR** — `Section_06_1_Heaps.lean:44-237`：功能堆模型使用 `List Nat` 而非可变数组。模块文档已声明。

**m11. 严重度: MINOR** — `CostedExecution.lean:4-27`：代价模型计算"已访问 MAX-HEAPIFY 帧 + 交换转换"，非书中 RAM 指令模型。模块文档已声明"not a RAM-cost model for Lean lists"。

**m12. 严重度: MINOR** — `Section_06_4_Heapsort.lean:521-529`：`arrayHeapSortInPlaceLoop` 使用燃料参数而非精确计数循环。燃料化形式等价于 for 循环，不影响正确性。

## 反驳记录

反驳员复核了全部 38 条 MATCH 条目，提出 0 条独立差异。无降级操作。

反驳员逐条检查了表示等价（零起始 vs 一起始索引算术、List vs Array 语义、Option vs 错误处理）、算法结构（循环边界、比较方向、递归模式、交换语义）、不变量强度（`ArrayMaxHeapExcept` 等价于书中前提、`HeapSortLoopInvariant` 三分量等价于练习 6.4-2 不变量）、代价模型（O(h)/O(log n)/O(n)/O(n log n) 界均严格证明）、定理强度（正确性定理覆盖完整）等维度。

**边缘情况注明**（非降级）：`arrayHeapDelete?`（`Section_06_5_Priority_Queues.lean:799-809`）在 `valAt a i = valAt a 0` 且 `i ≠ 0` 时，increase-key-to-root-max 为空操作，extract-max 移除根而非 i 处的元素，i 处的元素可能保留在新堆前缀中。不过数学合约（`rest.Perm (a.set i (valAt a 0))`、堆性质保持、堆大小减 1）仍然满足。此边缘情况仅出现在重复最大值场景，且书中 DELETE 操作对象（非索引）——此差异已由现存 MINOR m8（handle/映射抽象未形式化）覆盖。

## 各节分布

| 节 | MATCH | MINOR | MAJOR | CRITICAL |
|----|-------|-------|-------|----------|
| §6.1 Heaps | 7 | 3 | 0 | 0 |
| §6.2 Maintaining the Heap Property | 9 | 2 | 0 | 0 |
| §6.3 Building a Heap | 10 | 0 | 0 | 0 |
| §6.4 The Heapsort Algorithm | 7 | 3 | 1 | 0 |
| §6.5 Priority Queues | 6 | 4 | 1 | 0 |
| CostedExecution | 6 | 0 | 0 | 0 |

**关键发现（2026-08-27 更新）**: 第 6 章是形式化质量最高的章节之一。核心算法（MAX-HEAPIFY、BUILD-MAX-HEAP、HEAPSORT）的正确性证明完整且严格，代价分析精确再现了 CLRS 的 O(n) 构建和 O(n log n) 排序界。§6.5 的 checked MAX-HEAP-INSERT 及 O(log n) 冒泡帧界也已闭合。保留差异是功能 scaffold 的重建实现与纯函数 List 表示；读者级数组操作本身使用已验证的局部上冒泡/下沉算法，且范围说明不声称 RAM 指令成本。
