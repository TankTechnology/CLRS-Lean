# Geometric Proof Patterns in CLRS-Lean

这份 atlas 记录当前 CLRS-Lean 证明中反复出现的“几何结构”。
这里的几何不是指欧氏几何，而是指证明对象的形状：边界如何移动、局部如何替换、区间如何嵌套、表格如何依赖。

目标有两层：

- 让读者能按 proof shape 搜索已有证明，而不只是按章节搜索。
- 把已经重复出现的形状沉淀成小型 Lean 工具，而不是过早设计一个巨大的算法证明框架。

当前已经抽出的 Lean 模块位于 `CLRSLean/ProofPatterns/`：

- `Boundary.lean`：一维边界推进，目前是教学骨架，尚无章节消费者。
- `Exchange.lean`：通用最优性与交换传递内核，Chapter 16 和 Chapter 23
  已通过各自的领域证书实际使用。
- `Fiber.lean`：bucket/fiber 分解，Chapter 8 已通过精确 bridge 使用。
- `Interval.lean`：严格区间先后与嵌套，Chapter 22 DFS 已实际使用。

摊还分析的势能望远镜已经在 `CLRSLean/Chapter_17/Section_17_1_Amortized_Framework.lean`
里形成通用框架，因此暂时不重复迁移。

公共库的所有权、兼容面和 theorem-group 计数规则见
[`common-proof-library-decision-matrix.md`](common-proof-library-decision-matrix.md)。

## 1. Boundary Shift

**几何直觉**

一个对象被边界切成两部分：已处理/未处理，前缀/后缀，左区/右区，已扫描/未扫描。
证明的主动作是“边界移动一步，不变式仍成立”。

**Lean 骨架**

`CLRS.ProofPatterns.BoundaryTrace` 把状态写成按自然数索引的 trace：

```lean
BoundaryTrace.state : Nat -> State
```

核心定理：

```lean
CLRS.ProofPatterns.boundary_holds
CLRS.ProofPatterns.boundary_holds_upto
CLRS.ProofPatterns.terminal_of_boundary
```

**项目实例**

- Heapsort：`SortedSuffix` 和 `PrefixLeSuffix` 把数组切成 heap prefix 与 sorted suffix。
  关键定理包括 `arrayHeapSortStep_suffix_head_bounds_prefix`、
  `arrayHeapSortInPlaceLoop_exact_state_correct`。
- Quicksort：`partitionLoop_invariant` 维护 pivot 左右分区。
- Counting sort：按 key 从低到高扫描 bucket。
- Kruskal：按边权扫描 processed prefix，逐步扩展森林。

**复用方式**

新证明里只要出现“第 `i` 步状态”和“第 `i+1` 步状态”，优先写成：

```lean
Invariant i (state i) ->
Invariant (i + 1) (state (i + 1))
```

最后再用 `boundary_holds` 或 `boundary_holds_upto` 推到终点。

## 2. Exchange Optimality and Certificates

**几何直觉**

拿一个任意可行解，把其中一小块换成 greedy 选择，得到一个结构上更接近 greedy 解、且不更差的新可行解。
这是一种“局部替换四边形”：

```text
old feasible solution
        |
        | exchange
        v
new feasible solution containing greedy choice
```

**Lean 骨架**

`Optimal feasible noWorse chosen` 统一表示“`chosen` 可行，并且不劣于每个
可行竞争者”。核心传递定理是：

```lean
CLRS.ProofPatterns.Optimal.of_noWorse
CLRS.ProofPatterns.optimal_of_exchange
```

`Optimal.of_noWorse` 处理一次可行且不变差的替换；
`optimal_of_exchange` 处理“每个竞争者先交换到一个中间 target，再由
`chosen` 支配 target”的证明。

原有 `CLRS.ProofPatterns.ExchangeCertificate` 继续提供适合全函数交换的
最小公共形状：

```lean
exchange : Solution -> Solution
feasible_exchange : feasible s -> feasible (exchange s)
target_exchange : feasible s -> target (exchange s)
noWorse_exchange : feasible s -> noWorse (exchange s) s
```

`target` 是交换后获得的结构性质；`noWorse` 由具体问题决定。
最大化问题可以用 `NoLessScore`，最小化问题可以用 `NoGreaterCost`。

**项目实例**

- Activity selection：`MaxCardinality.toOptimal` 把章节最优性证书投影到
  通用内核，`greedy_choice_optimal_from_certificate` 调用
  `optimal_of_exchange`。
- Huffman：通过 split-leaf/exchange 把两个最低频率符号放进 sibling leaves。
- MST/Kruskal：`IsMSTExtending.toOptimal` 投影前缀最优性，
  `mst_exchange_preserves_prefix` 调用 `Optimal.of_noWorse`。

**复用方式**

新的 greedy 证明先写领域侧 exchange certificate，证明任意 competitor
都能被换成含有 greedy 局部选择的 competitor，再用 `Optimal` 内核组合
最终的 no-worse 关系。Chapter 16 保留活动 tail witness；Chapter 23 保留
cut、path 和换边 witness。公共库不选择 witness，也不引入 classical choice。

## 3. Fiber Decomposition

**几何直觉**

用一个 key 把列表分成若干 fiber/bucket；先证明每个 fiber 内部正确，再按 key 顺序拼回全局结果。

**Lean 骨架**

`CLRS.ProofPatterns.fiber` 是 key-generic 的 bucket：

```lean
fiber key xs k
```

核心引理：

```lean
fiber_sublist
fiber_append
mem_fiber_iff
fiber_all_keys_eq
fiber_eq_nil_of_forall_ne
fiber_fiber_eq
```

**项目实例**

- Counting sort：`bucket_eq_fiber` 已证明自然数 key 的 `bucket` 与通用
  `fiber` 完全相同；`bucket_append`、`mem_bucket_iff`、
  `bucket_all_keys_eq`、`bucket_bucket_eq` 已委托给通用引理。
- Radix sort：digit class 是多层 fiber 叠加。
- Bucket sort：bucket index 决定元素落点，期望分析里还要数 bucket size。
- Hash tables：链地址法的每条链可以看成 hash key 的 fiber。

**复用方式**

Chapter 8 保留教材侧 `bucket` 语言，并通过精确 bridge 使用通用库：

```lean
bucket key xs k = fiber key xs k
```

旧 theorem 名继续作为稳定接口。下一步只有在 radix、bucket sort 或 hash
chain 出现新的共同需求时，才扩充 `Fiber` API。

## 4. Interval Nesting

**几何直觉**

时间戳、递归区间、相邻 power 区间之间通常只有两种干净关系：

- 一个区间严格在另一个区间之前。
- 一个区间严格嵌套在另一个区间内部。

DFS 的 parenthesis theorem 就是这个结构最明显的版本。

**Lean 骨架**

`CLRS.ProofPatterns.NatInterval` 给出最小区间模型：

```lean
NatInterval.Valid
NatInterval.StrictlyBefore
NatInterval.NestedInside
```

核心引理：

```lean
NatInterval.nestedInside_trans
NatInterval.nestedInside_irrefl
NatInterval.nestedInside_asymm
NatInterval.strictlyBefore_trans
NatInterval.strictlyBefore_asymm
```

**项目实例**

- DFS：`dfsInterval` 把 discovery/finish timestamps 投影到
  `NatInterval`；`finishesBeforeDiscovered_iff_strictlyBefore` 和
  `intervalNestedInside_iff_nestedInside` 提供定义级等价，
  `intervalNestedInside_asymm` 已复用通用反对称引理。
- Maximum subarray：left/right/crossing 是围绕边界的区间分解。
- Master theorem all-input bridge：任意输入被夹在相邻 exact powers 之间。

**复用方式**

遇到新的 timestamp 或 index-interval 证明时，沿用 Chapter 22 已验证的方式，
先定义到 `NatInterval` 的投影：

```lean
def dfsInterval (s : DFSState V) (u : V) : NatInterval := ...
```

然后复用通用的 asymmetry/transitivity 引理，把算法专属事实留给原章节。
Chapter 22 的 parenthesis、ancestor 和 edge-classification 证明仍然保持
DFS 语言，没有为抽象统一而整体重写。

## 5. Local Surgery

**几何直觉**

只修改树或堆的一小块，证明外部 frame 不变、全局 invariant 被保留。

**当前状态**

这一类暂时只写进 atlas，没有抽 Lean 模块。原因是它很容易被具体数据结构污染：

- 红黑树 rotation 关心颜色、黑高、BST order。
- Order-statistic tree rotation 关心 stored size 与 rank/select。
- B-tree split child 关心 child bounds、key order、membership。
- Heapify 关心 array index 与 heap prefix。

**项目实例**

- `rankSelect?_rotateLeft` / `rankSelect?_rotateRight`
- `splitChild_preserves_childBounded`
- `PrefixLeBound.of_maxHeapifyFuel`

**复用方式**

这一类先继续按章节保留局部 lemma。
等两个不同章节都需要“frame-preserving edit”接口时，再抽：

```lean
before --local edit--> after
outside patch unchanged
Invariant before -> Invariant after
```

## 6. Table/Grid Dynamic Programming

**几何直觉**

DP 证明通常是在二维表上移动：一个 cell 的值由左、上、左上，或由某个 split point 决定。
reconstruction 则是在表格里走出一条 path 或 split tree。

**当前状态**

暂时不抽 Lean 模块，因为不同 DP 的 value、certificate、reconstruction 形状差异较大。
但文档上已经可以按这个 pattern 搜索。

**项目实例**

- Matrix-chain multiplication：`MatrixChainLowerBound`、`MatrixChainSplitOptimal`、`matrixChain_correct`。
- LCS：`LCSCertificate`、table recurrence、`lcs_correct`。
- Rod cutting / optimal BST：一维或二维 table optimality certificate。

**复用方式**

新 DP 证明优先分成三层：

1. local recurrence lower/upper bound；
2. table satisfies recurrence；
3. reconstruction certificate consumes table recurrence。

## 7. Potential Telescope

**几何直觉**

摊还分析把真实代价和势能变化相加：

```text
actual_i + Phi_{i+1} - Phi_i
```

沿 trace 求和后，中间势能项全部抵消。

**已有 Lean 框架**

Chapter 17 已经有通用版本：

```lean
CLRS.Chapter17.AccountingTrace
CLRS.Chapter17.PotentialTrace
CLRS.Chapter17.potential_totalCost_eq_totalAmortized_sub_delta
CLRS.Chapter17.potential_totalCost_le_totalAmortized
```

**项目实例**

- Stack/multipop aggregate analysis。
- Binary counter flips。
- Dynamic table insert/delete。
- Fibonacci heap potential。

**复用方式**

新摊还证明直接 import Chapter 17 framework，除非未来决定把它上移到 `ProofPatterns`。
当前不迁移，是为了避免扰动已经稳定的 Chapter 17 API。

## 8. Scale Sandwich

**几何直觉**

复杂度证明里常见“精确点”和“任意输入点”的夹逼：

```text
exact power <= n < next exact power
```

先在整齐的 spine 上证明，再把所有输入夹进相邻 spine 点之间。

**项目实例**

- Recursion-tree exact powers。
- Master theorem floor/ceiling all-input transfer。
- Randomized quicksort 的 harmonic bound 可以看成另一种 envelope。

**复用方式**

这一类保留在 Chapter 4，因为它强依赖 asymptotic notation 和 exact-power
recurrence。Chapter 27 已直接复用 `monotoneAbs_natCast` 和
`monotone_power_sandwich`，删除了自己的私有通用副本。只有当非递归领域也
需要同一接口、且导入 Chapter 4 不再合理时，才考虑继续上移。

## Extraction Rule

沉淀规则保持保守：

- 一个 pattern 先进入这份 atlas。
- 至少两个章节独立复用后，再抽 Lean 小模块；对已经存在的候选模块，允许先用
  一个精确 bridge 建立真实消费者，但不因此扩张其 API。
- 小模块只抽几何骨架和通用代数，不抽具体算法语义。
- 已稳定章节不为“漂亮抽象”做大重构；新证明优先使用这些模块，等自然重复后再回收旧 lemma。

当前优先级：

1. Chapter 8 新的 bucket/fiber 引理优先落到 `Fiber`，再保留章节 wrapper。
2. Chapter 22 新的纯区间代数优先通过 `dfsInterval` 复用 `NatInterval`。
3. 有限期望代数统一进入 `CLRS.Probability`；Chapter 4 和 Chapter 17 继续
   作为已经有跨章节消费者的 domain library。
4. `Exchange` 已由 Chapter 16 和 Chapter 23 实际复用；`Boundary` 继续作为
   候选骨架，等真实 proof site 能无损接入后再推广。
5. `LocalSurgery` 和 DP grid 暂时维持文档模式，等复用压力更明确再抽代码。
