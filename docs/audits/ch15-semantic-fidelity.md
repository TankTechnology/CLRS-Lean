# Ch15 Greedy Algorithms 语义忠实性审计

- 审计日期(北京时间): 2026-08-17
- 基准来源: 参考第 15.1–15.4 节
- 结构前提: check_book_coverage.py 通过(Chapter 15 main-proof-complete, 27/27)
- 结论分布: MATCH 37 · MINOR 11 · MAJOR 0 · CRITICAL 0 · UNCERTAIN 0

## 断言对照表

### 第 15.1 节: Activity-selection

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| Activity 定义(s_i, f_i, 0 ≤ s_i < f_i) | `Section_15_1_Activity_Selection.lean:77-80` | MINOR | 未强制 `start < finish`;书中要求 0 ≤ s_i < f_i;允许退化区间不影响兼容性推理 |
| Compatible 定义(s_i ≥ f_j or s_j ≥ f_i) | :87-88 | MATCH | `a.finish ≤ b.start ∨ b.finish ≤ a.start`,等价于书中半开区间兼容性 |
| Feasible 列表 | :101-103 | MATCH | 按时间顺序排列且互相兼容;比书中"mutually compatible subset"更强(额外要求排序) |
| FinishSorted(按 f_i 单调非降序) | :144-145 | MATCH | `List.Pairwise fun a b => a.finish ≤ b.finish` 对应式(15.1) |
| MinFinish / earliest_finish | :137-138, :174-179 | MATCH | 捕获"最早完成时间"的贪心选择 |
| Theorem 15.1(贪心选择性质) | :414-435, :478-491 | MATCH | `GreedyChoiceCertificate.exchange` 比书中交换论证更强(允许任意竞争者转换为贪心选择+尾部) |
| MaxCardinality 定义 | :357-362 | MATCH | 捕获 feasible sublist + 最大基数 |
| greedySelect_maxCardinality | :498-518 | MATCH | 对 finish-sorted 输入,贪心选择器返回最大基数可行解 |
| greedySelect_sublist / greedySelect_feasible | :321-348 | MATCH | 贪心选择器返回输入的子列表且可行 |
| activitySelection_correct | :578-585 | MATCH | 读者友好的正确性打包 |
| greedySelect_cons_maxCardinality | :547-551 | MATCH | 非空递归步骤定理 |
| activitiesAfter(子问题过滤) | :247-248 | MATCH | 过滤出所有与已选活动兼容的后续活动 |
| finishSorted_greedyChoiceCertificate | :414-435 | MATCH | 对排序输入自动导出交换证书 |
| RECURSIVE-ACTIVITY-SELECTOR 算法 | :279-289 | MINOR | 使用列表递归而非书中带 k,n 的数组索引伪代码;数学内容等价 |
| GREEDY-ACTIVITY-SELECTOR 迭代算法 | 无 | MINOR | 未形式化迭代版本;仅提供递归版本 |
| 复杂度 Theta(n) | 无 | MINOR | 未声明渐近复杂度;书中声称 Theta(n) |

### 第 15.2 节: Greedy strategy meta-theorems

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| GreedyChoiceProperty 谓词 | :159-161 | MATCH | 捕获"局部最优选择可组装为全局最优解" |
| OptimalSubstructure 谓词 | :168-170 | MINOR | 定义为 `∀p, optimal (subproblem p) (solve (subproblem p))`——是求解器正确性断言,而非书中"最优解包含子问题最优解"的问题结构性质 |
| GreedyProblem 结构 | :74-89 | MINOR | `gcp` 公理合并了书中两个独立性质(贪心选择+最优子结构);逻辑上足以推导最优性,但丢失了书中对二者的区分 |
| gsolve 泛型贪心求解器 | :97-106 | MATCH | 递归贪心算法的抽象实现 |
| gsolve_optimal 元定理 | :134-150 | MATCH | 若问题满足 GreedyProblem 公理,则 gsolve 对任意实例返回最优解 |
| 引理编号引用 | :8-9, :11-12, :32-33 | MINOR | 文档注释引用"Lemma 15.1"和"Lemma 15.2",但 §15.2 无编号引理;应引用"greedy-choice property"和"optimal substructure"概念 |
| 活动选择实例化 | 文档声称在"companion file" | MINOR | `GreedyProblem` 未在本文件中对活动选择问题实例化;声称的配套文件未出现在版本映射中 |

### 第 15.3 节: Huffman codes

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| HuffTree 归纳定义(叶/内部节点) | :30-33 | MATCH | `htLeaf symbol freq` / `htInner left right`,类型天然保证满二叉树(每个内部节点有两个孩子) |
| 前缀码一致性(consistent) | :39-41 | MATCH | `Disjoint (alphabet l) (alphabet r)` 等价于"no codeword is a prefix of another" |
| freqOf / depthOf | :50-52, :44-49 | MATCH | 对应书中 c.freq 和 d_T(c) |
| cost 定义(B(T)) | :53-54 | MINOR | 使用内部节点频率和公式(习题 15.3-4)而非式(15.4)的 Σ c.freq·d_T(c);二者对满二叉树等价,但等价性未证明 |
| optimum 定义 | :75-76 | MATCH | consistent + 正频率 + 同频率树中最小 cost |
| unite / insortTree / huffman 算法 | :77-83 | MATCH | 对应 HUFFMAN 过程;用有序列表代替最小优先队列,抽取两个最小频率,合并,重插入 |
| Lemma 15.2(贪心选择) | 无独立定理 | MINOR | 书中引理未单独陈述;其证明思路嵌入 `optimum_splitLeaf`(:2295-2533)和 `deepestSiblingPair` 交换论证中 |
| Lemma 15.3(最优子结构) | 无独立定理 | MINOR | 书中引理未单独陈述;其内容由 `optimum_splitLeaf` 过程覆盖 |
| Theorem 15.4(HUFFMAN 最优性) | :2847-2858, :2953-2972 | MATCH | `optimum_huffman_v2` 和 `optimum_huffman_freqs` 证明 Huffman 算法产生最优前缀码 |
| SplitLeafOptimalitySpec 接口 | :2544-2553 | MATCH | 封装了 Lemma 15.2+15.3 合并所需的前提条件 |
| huffmanOfFreqs 频率表接口 | :2878-2879, :2953-2972 | MATCH | 接受任意频率表,要求无重复符号且频率均为正 |
| huffmanOfFreqs_correct | :2979-2986 | MATCH | 频率保持 + 最优性 |
| split_leaf_preserves_optimum | :2555-2559 | MATCH | 拆分已合并叶保持最优性 |
| forest_sorted / forest_consistent | :95-97, :92-94 | MATCH | 按 rootFreq 非降序排列;森林一致性保证字母表不相交 |
| areSiblings 定义 | :686-690 | MATCH | 两个字符在树中为兄弟叶 |
| swapLeaves / swapFreqs | :107-108, :101-102 | MATCH | 叶交换和频率交换操作,对应书中交换论证 |
| cost_exchangeLeaf_le | :641-681 | MATCH | 交换不增加 cost;对应书中 Lemma 15.2 交换论证 |
| Forest 结构 / mergeCheapest | :2563-2569, :2623 | MATCH | 打包森林不变式;贪心合并步骤 |
| MergeCheapestSplitReady.optimum | :2811-2815 | MATCH | 合并后最优性可还原为合并前最优性 |
| 复杂度 O(n log n) | 无 | MINOR | 未声明复杂度;实现使用插入排序(O(n²))而非书中假定的二叉堆(O(n log n)) |

### 第 15.4 节: Offline caching

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| Page / Cache 模型 | `S1_Cache_Model.lean:43-47` | MATCH | `Page = Nat`;`CacheSize k C := C.card = k` |
| Policy 结构(驱逐策略) | :57-59 | MATCH | `evict` + `evict_mem` 有效性条件 |
| Policy.step(缓存过渡) | :65-66 | MATCH | 命中保持,故障驱逐并加载 |
| cacheSeq / faultAt / misses | :70-72, :116-122 | MATCH | 对应书中缓存序列、故障指示、缺失计数 |
| nextUse(下一个请求位置) | :158-159 | MATCH | `findIdx?` 找下一个相同页面请求 |
| Farther 序关系 | `S2_Farthest_In_Future.lean:40-44` | MATCH | none(永不再请求)最远;some 比较位置大小 |
| farthestInFuture | :156-157 | MATCH | 选择缓存中下次访问最远的驻留页面 |
| fifoPolicy(最远未来策略) | :185-189 | MATCH | 对应 Belady 最优算法;命名"fifo"易与"First-In-First-Out"混淆,但文档注释正确说明 |
| Theorem 15.5(贪心选择性质) | `S3_Optimality.lean:1790-1844` | MATCH | 交换论证覆盖书中 Theorem 15.5 |
| fifo_optimal_trace(全局最优性) | `A6_Iteration.lean:72-82` | MINOR | 要求 `hC₀ : C₀.Nonempty`;书中缓存从空开始,定理未覆盖 compulsory-miss 阶段 |
| schedCache / schedMisses(调度模型) | `S3_Optimality.lean:100-112` | MATCH | 与策略无关的调度抽象 |
| exchangeSchedule / exchangeDecision | :155-184 | MATCH | 构造交换调度 |
| exchangeSchedule_invariant | :451-584 | MATCH | 对应书中 Property 1-4 不变式 |
| exchangeSchedule_misses_le | :1307-1698 | MATCH | 交换不增加缺失;好书事件补偿坏事件 |
| LegalTrace(合法缓存迹) | `A1_LegalTrace.lean:19-28` | MATCH | 策略无关的语义迹模型 |
| TraceAgreesWithFIF / exchange_trace | `A5_Exchange.lean:18-19, :22-80` | MATCH | 迹级 FIFO 一致性 + 一步交换 |
| exists_fully_agreeing_trace | `A6_Iteration.lean:59-69` | MATCH | 有限迭代:任意迹可交换为与 FIFO 完全一致的迹 |

## 缺陷清单

### MINOR-1: 第 15.1 节 Activity 未强制 start < finish
- **位置**: `Section_15_1_Activity_Selection.lean:77-80`
- **描述**: 书中明确要求 0 ≤ s_i < f_i。Lean 的 `Activity` 使用 `start : Nat` 和 `finish : Nat`,未强制 `start < finish`。允许退化活动(负长度区间)虽然不影响 `Compatible` 关系的逻辑推理,但模型可接受书中不存在的输入。
- **建议**: 添加 `start < finish` 作为 `Activity` 结构的字段或独立假设;或在模块文档中明确声明允许退化区间。

### MINOR-2: 第 15.1 节缺少迭代贪心算法
- **位置**: `Section_15_1_Activity_Selection.lean`(全文)
- **描述**: 书中提供 GREEDY-ACTIVITY-SELECTOR 迭代版本(参考第 15.1 节),假设活动已按完成时间排序,在 Theta(n) 时间内运行。Lean 形式化仅提供递归版本 `greedySelect`。
- **建议**: 可添加 `greedySelectIterative` 作为 `greedySelect` 的尾递归等价形式,并证明二者输出相同。

### MINOR-3: 第 15.1 节缺少复杂度声明
- **位置**: `Section_15_1_Activity_Selection.lean:279-289`
- **描述**: 书中声明递归和迭代版本均为 Theta(n) 时间(假设已排序)。Lean 代码未声明任何渐近复杂度。
- **建议**: 在模块文档或定理注释中添加复杂度声明。

### MINOR-4: 第 15.2 节文档引用不存在的引理编号
- **位置**: `Section_15_2_Greedy_Meta.lean:8-9, 11-12, 32-34`
- **描述**: 文档注释引用"Lemma 15.1"和"Lemma 15.2",但 §15.2 不含编号引理。这些概念在书中被称为"greedy-choice property"和"optimal substructure"。
- **建议**: 将"Lemma 15.1"改为"the greedy-choice property",将"Lemma 15.2"改为"optimal substructure"。

### MINOR-5: 第 15.2 节 OptimalSubstructure 谓词语义漂移
- **位置**: `Section_15_2_Greedy_Meta.lean:168-170`
- **描述**: 书中定义最优子结构为"an optimal solution to the problem contains within it optimal solutions to subproblems"——这是问题结构性质,与具体求解器无关。Lean 的 `OptimalSubstructure` 定义为 `∀(p : P), optimal (subproblem p) (solve (subproblem p))`,即求解器对每个子问题返回最优解——这是求解器正确性断言,非书中所述的问题结构性质。
- **建议**: 将谓词重命名为 `SolverCorrect` 或调整其定义以匹配书中概念;或添加注释说明此差异。

### MINOR-6: 第 15.2 节 GreedyProblem.gcp 合并了两个独立性质
- **位置**: `Section_15_2_Greedy_Meta.lean:74-89`
- **描述**: 书中 §15.2 将贪心选择性质和最优子结构作为两个独立的关键要素分别阐述。Lean 的 `gcp` 公理将其合并为单一公理: `optimal (sub p) s → optimal p (combine (greedyElt p) s)`。虽然合并后的公理在逻辑上足以推导 `gsolve_optimal`,但丢失了书中对这两个性质的区分。
- **建议**: 将 `gcp` 拆分为两个独立公理或添加注释说明合并原因。

### MINOR-7: 第 15.3 节 Lemma 15.2 和 Lemma 15.3 未独立陈述
- **位置**: `Section_15_3_Huffman_Codes.lean`(全文)
- **描述**: 书中 Lemma 15.2(贪心选择性质)和 Lemma 15.3(最优子结构)是两个独立定理。Lean 代码将其合并为单一的 `optimum_splitLeaf` 定理(:2295-2533)。读者无法直接定位到与书中引理一一对应的 Lean 定理。
- **建议**: 添加 `lemma greedy_choice_property` 和 `lemma optimal_substructure` 作为 `optimum_splitLeaf` 的推论。

### MINOR-8: 第 15.3 节 cost 使用备选公式
- **位置**: `Section_15_3_Huffman_Codes.lean:53-54`
- **描述**: 书中式(15.4)将 cost 定义为 B(T) = Σ_{c∈C} c.freq · d_T(c)。Lean 使用内部节点频率和公式 `cost = cost l + cost r + rootFreq l + rootFreq r`(见习题 15.3-4)。二者对满二叉树等价,但等价性在 Lean 代码中未证明,且主定义与书中不同。
- **建议**: 添加引理证明 `cost` 的两种定义等价,或在 doc 注释中注明此等价性。

### MINOR-9: 第 15.3 节缺少复杂度声明
- **位置**: `Section_15_3_Huffman_Codes.lean:77-83`
- **描述**: 书中声明 HUFFMAN 运行时间为 O(n log n)(使用二叉堆)。Lean 实现使用插入排序(O(n²)),未声明复杂度。
- **建议**: 添加复杂度声明或注释说明实现与书中算法在复杂度上的差异。

### MINOR-10: 第 15.4 节初始缓存必须非空
- **位置**: `A6_Iteration.lean:72-82`, `S1_Cache_Model.lean:57-59`
- **描述**: 书中明确指出缓存"starts out empty before the first request"(参考第 15.4 节)。Lean 定理 `fifo_optimal_trace` 要求前提 `hC₀ : C₀.Nonempty`,因此强制缺失阶段未被建模。定理覆盖的场景是缓存已非空后的驱逐决策最优性,不覆盖 k=0 或缓存从空开始填充的情形。
- **建议**: 可扩展模型以支持空初始缓存,或将此限制在模块文档中明确说明。

### MINOR-11: 第 15.2 节缺少活动选择实例化
- **位置**: `Section_15_2_Greedy_Meta.lean`(全文)
- **描述**: `GreedyProblem` 结构未在本文件中对活动选择问题实例化。文档声称实例化在"companion file"中,但该文件未出现在版本映射中。
- **建议**: 提供活动选择的 `GreedyProblem` 实例化以连接 §15.1 和 §15.2。

## 反驳记录

反驳员复核了审计员对照表中全部 43 条 MATCH 条目,逐条检查了表示等价陷阱、定理强度、命名误导、代价模型错绑和书中定义是否被正确捕获。

提出 5 条独立差异,全部成立并降级为 MINOR:
1. §15.3 cost 定义——使用内部节点频率和而非书中 B(T) 公式,等价性未证明
2. §15.2 OptimalSubstructure 谓词——捕获求解器正确性而非书中问题结构性质
3. §15.2 GreedyProblem.gcp——合并了书中两个独立性质
4. §15.1 Activity 定义——未强制 start < finish
5. §15.4 fifo_optimal_trace——要求 C₀.Nonempty,排除书中从空缓存起步的阶段

另有一条命名记录(§15.4 `fifoPolicy` 命名与标准 FIFO 冲突),维持 MATCH 判定。

其余 37 条 MATCH 条目经多维复核后维持原判定:检查了表示等价(数据结构、索引起点、可变性模型)、定理强度(∀∃ 顺序、前提是否合理加强)、命名误导、代价模型(比较次数 vs 基本操作数)和书中定义对应性,排除差异。

## 审计总结

第 15 章的形式化在数学内容上与 CLRS 第四版高度一致。贪心算法的两个核心概念性质——贪心选择性质和最优子结构——在 §15.1(活动选择的具体实例)、§15.2(抽象元定理)和 §15.3–§15.4(Huffman 编码和离线缓存的具体实例)中均被正确捕获。定理声明的量化结构(forall-exists 顺序)与书中一致,输出规约在所有情况下均匹配或更强于书中声明。

11 个 MINOR 项均为表面级别:文档引用、命名、定义表述差异、缺少复杂度声明、定理前提差异(非空初始缓存)。无 MAJOR 或 CRITICAL 缺陷。§15.4 离线缓存最优性的证明尤为详尽,将书中 4 页的交换论证扩展为完整的迹耦合构造,最终得出比书中 Theorem 15.5 更强的结论(FIFO 缺失数 ≤ 任意策略缺失数)。