# Geometric Proof Patterns in CLRS-Lean

这份 atlas 记录当前 CLRS-Lean 证明中反复出现的“几何结构”。
这里的几何不是指欧氏几何，而是指证明对象的形状：边界如何移动、局部如何替换、区间如何嵌套、表格如何依赖。

目标有两层：

- 让读者能按 proof shape 搜索已有证明，而不只是按章节搜索。
- 把已经重复出现的形状沉淀成小型 Lean 工具，而不是过早设计一个巨大的算法证明框架。

当前已经抽出的 Lean 模块位于 `CLRSLean/ProofPatterns/`：

- `Boundary.lean`：一维边界推进。
- `Exchange.lean`：贪心交换证书。
- `Fiber.lean`：bucket/fiber 分解。
- `Interval.lean`：严格区间先后与嵌套。

摊还分析的势能望远镜已经在 `CLRSLean/Chapter_17/Section_17_1_Amortized_Framework.lean`
里形成通用框架，因此暂时不重复迁移。

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

## 2. Exchange Certificate

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

`CLRS.ProofPatterns.ExchangeCertificate` 只固定最小公共形状：

```lean
exchange : Solution -> Solution
feasible_exchange : feasible s -> feasible (exchange s)
target_exchange : feasible s -> target (exchange s)
noWorse_exchange : feasible s -> noWorse (exchange s) s
```

`target` 是交换后获得的结构性质；`noWorse` 由具体问题决定。
最大化问题可以用 `NoLessScore`，最小化问题可以用 `NoGreaterCost`。

**项目实例**

- Activity selection：把任意最优选择交换成以最早结束活动开头的选择。
- Huffman：通过 split-leaf/exchange 把两个最低频率符号放进 sibling leaves。
- MST/Kruskal：把 light crossing edge 加入生成树，再删除路径上的一条边。

**复用方式**

新的 greedy 证明不要先写“算法一定最优”的大定理。
先写一个 exchange certificate，证明任意 competitor 都能被换成含有 greedy 局部选择的 competitor。
然后把递归子问题或 cut property 接上。

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

- Counting sort：当前的 `bucket` 是自然数 key 的专用版本。
- Radix sort：digit class 是多层 fiber 叠加。
- Bucket sort：bucket index 决定元素落点，期望分析里还要数 bucket size。
- Hash tables：链地址法的每条链可以看成 hash key 的 fiber。

**复用方式**

后续如果要重构 Chapter 8，可以先把局部 `bucket` 定义替换或桥接到 `fiber`：

```lean
bucket key xs k = fiber key xs k
```

不要急着改现有已证定理；更稳的做法是在新 theorem 中用 `fiber_*` 引理，等重复出现两三次后再回收旧局部 lemma。

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

- DFS：`intervalNestedInside` 比较 discovery/finish intervals。
- Maximum subarray：left/right/crossing 是围绕边界的区间分解。
- Master theorem all-input bridge：任意输入被夹在相邻 exact powers 之间。

**复用方式**

遇到新的 timestamp 或 index-interval 证明时，可以先定义一个到 `NatInterval` 的投影：

```lean
def dfsInterval (s : DFSState V) (u : V) : NatInterval := ...
```

然后复用通用的 asymmetry/transitivity 引理，把 DFS 专属事实留给发现/完成时间本身。

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

这一类目前保留在 Chapter 4，因为它强依赖 asymptotic notation 和 exact-power recurrence。
如果 Chapter 24-26 的复杂度证明再次需要“exact spine -> all input”的桥，再考虑抽到 ProofPatterns。

## Extraction Rule

沉淀规则保持保守：

- 一个 pattern 先进入这份 atlas。
- 至少两个章节独立复用后，再抽 Lean 小模块。
- 小模块只抽几何骨架和通用代数，不抽具体算法语义。
- 已稳定章节不为“漂亮抽象”做大重构；新证明优先使用这些模块，等自然重复后再回收旧 lemma。

当前优先级：

1. 新证明优先使用 `Boundary`、`Fiber`、`Interval`、`Exchange`。
2. Chapter 8 后续重构可把 `bucket` 和 `fiber` 桥接起来。
3. Chapter 22 DFS parenthesis/white-path 后续证明可用 `NatInterval` 做外层区间语言。
4. Chapter 23/24 的图算法 greedy/cut 证明继续试用 `ExchangeCertificate`。
5. `LocalSurgery` 和 DP grid 暂时维持文档模式，等复用压力更明确再抽代码。
