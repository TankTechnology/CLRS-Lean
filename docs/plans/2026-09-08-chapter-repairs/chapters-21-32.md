# 第 21–32 章修复证据与范围

对应审查 issue：#363–#374。本文记录第 21–30、32 章当前源码中的修复；第 31 章单列为待负责代理最终交付。本文不修改基于 `c8b074e961fb204ab50b9ea123b864260dafde38` 的历史审计、issue 清单或索引，也不宣称已独立逐页核对教材。代码中的旧版命名空间与第四版章节号不一定相同。

本轮既有实质执行/证明修复，也有原证明已成立、仅需校正范围的项目。以下明确区分两者；没有把声明成本模型的边界当成未实现的机器成本证明。

## 第 21 章：Prim 完成性与实际队列执行（#363）

[完成性模块](../../../src/CLRSLean/FourthEdition/Chapter_21/Section_21_2_Kruskal_And_Prim/S4_Completion.lean)在 `CLRS.MST.ExecutablePrim` 中证明每次加入跨割边会严格减少未覆盖顶点。队列返回空时，由连通性和最小键性质推出已覆盖全部顶点；充足 fuel 因而给出实际运行的生成树证书。初始最优树也由已有 Kruskal 生成树和自然数权重最小化构造，不再作为调用者假设。

关键接口：`crossing_uncovered_lt`、`run_covers`、`frontierRun_certificate`、`exists_mstExtending_empty`、`frontierRun_minimum_spanning_tree_of_card`。`component_insert_crossing` 额外要求原选边两端都在根分量内，才推出新增一个外部顶点；没有把一般的分量合并误写成单顶点增长。

[计数 frontier](../../../src/CLRSLean/FourthEdition/Chapter_21/Section_21_2_Kruskal_And_Prim/S5_CountedFrontier.lean)的 `CountedFrontier.execute_refines` 保留参考执行的实际全边重扫。[ArrayPrim](../../../src/CLRSLean/FourthEdition/Chapter_21/Section_21_2_Kruskal_And_Prim/S6_ArrayPrim.lean)另行维护邻接行、键及父指针数组。`execute_minimum_spanning_tree`、`execute_cost_bound`、`execute_edgeVisits_le`、`execute_extracts_le` 连接同一执行的 MST 输出、至多 `2n² + 5n + 6|E|` cell work、`2|E|` 邻接访问及 `n` 次提取。

范围：连通图、精确分量解释和已有 crossing-edge 标识合法性前提仍显式存在。`n` 是环境数组大小，只有完整索引宇宙时等于图的顶点数。邻接表示是输入；没有从无序边集构造它的成本证明。旧 heap 表达式仍是条件后端预算，Kruskal 总公式仍包含独立排序预算。数组分配、权重函数内部计算及 bit 成本不在计数内。

回归：[PrimCompletion](../../../tests/Chapter_21_PrimCompletion.lean)覆盖 fuel 不足、充足/多余 fuel、单顶点、零权边；[CountedPrim](../../../tests/Chapter_21_CountedPrim.lean)覆盖需要降低已有键的三角形、平行边、自环、单点、实际字段计数及 MST 接口。相关窄构建、测试和公理检查已报告通过。

## 第 22 章：零权环上的源根前驱树（#364）

[PredecessorTree](../../../src/CLRSLean/FourthEdition/Chapter_22/Section_22_5_Shortest_Path_Properties/PredecessorTree.lean)不再从“每条父边 tight”推断树。`CLRS.Chapter24.WeightedGraph.shortestPathTree` 计算距离，构造 tight-edge 图，再取实际 BFS 父指针和深度。

`shortestPathTree_parent_depth_lt` 给出严格递减秩；`shortestPathTree_acyclic` 排除父环；`tightGraph_reachable_iff`、`shortestPathTree_path`、`shortestPathTree_correct` 证明可达覆盖、源根路径以及路径权重等于最短距离。[回归](../../../tests/Chapter_22_PredecessorTree.lean)保留零权 `a↔b` 的真实 tight 环反例，验证新父指针选源、不可达点无父/深度、非零权路径权重。

范围修正：Bellman–Ford 仍是全局 `NoNegCycle` 下的同步距离接口，未添加“仅源可达负环”的失败检测；DAG SSSP 仍要求给定完整拓扑序；Dijkstra 的 heap 公式仍不是具体队列计数。差分约束的新源可达所有变量，故其全局无负环条件适当。新树构造使用经典选择，不附带运行时间结论。直接测试及 trust 检查已报告通过。

## 第 23 章：负环等价检测、存储矩阵与 Johnson（#365）

[NegativeCycle](../../../src/CLRSLean/FourthEdition/Chapter_23/Section_23_2_Floyd_Warshall/NegativeCycle.lean)增加 `cycleWeightMatrix`，对自边使用 `min 0 w`，修复单顶点负自环被旧零对角线掩盖的问题。`floydFrom` 是可共享的初始化参数化递推。`cycleFloydWarshall_negative_iff`、`cycleFloydWarshall_negative_iff_closed_walk`、`detectsNegativeCycle_iff` 真正证明检测的双向等价，不把两个互为逆否的单向定理当成完备性。在 `NoNegCycle` 下，`cycleD_eq_D` 等接口证明与旧距离结果一致。

[MatrixExecution.Reindex](../../../src/CLRSLean/FourthEdition/Chapter_23/MatrixExecution/Reindex.lean)将每阶段结果实际保存在表中并复用上一阶段。`MatrixExecution.floyd_read`、`square_read` 给出值精化；`cycleFloydOn_visits_eq_budget`、`fasterOn_visits_eq_budget` 连接实际循环计数：Floyd 为 `n³` 更新，重复平方为 `numSquarings * n³` 候选访问。初始化/中间写入及最终 `n` 次对角探测单独计数；`diagonalScan_negative_iff` 连接实际检测结果。显式顶点与索引等价支持任意有限载体。

[JohnsonExecution](../../../src/CLRSLean/FourthEdition/Chapter_23/Section_23_3_Johnsons_Algorithm/Execution.lean)在 `Fin n` 上保存 Bellman–Ford potential、重赋权矩阵、每个源的 scan-queue 结果行。`johnsonStored_read`、`johnsonStored_correct`、`johnsonStored_row` 给出精化/正确性；`johnsonStored_work_le_polynomial` 的界为 `4n³ + 14n² + 12n + 4`，另有 `16(n+1)³` 包络。

范围：Johnson 仍要求全局 `NoNegCycle`，没有失败返回，也未实现旧 heap 预算。矩阵/Johnson 均使用精确实数及索引访问原语，不计枚举构造、有限集合查找内部、持久数组复制、分配或 bit 成本。负环 detector 自身不要求 `NoNegCycle`。

[负环测试](../../../tests/Chapter_23_NegativeCycle.lean)覆盖负自环、普通负环、隔离分量内负环及无负环；[矩阵测试](../../../tests/Chapter_23_MatrixExecution.lean)检查值及真实计数；[Johnson 测试](../../../tests/Chapter_23_JohnsonExecution.lean)覆盖空/单点、合法负边、不可达距离、实际准备/扫描计数。三个目标的正式窄构建和测试均已通过；Johnson 最后一次 Chapter 23 构建报告 8,601 jobs。

## 第 24 章：同一轨迹的稀疏 EK 与初始化 RTF（#366）

[SparseEK](../../../src/CLRSLean/FourthEdition/Chapter_24/Section_24_2_Edmonds_Karp/S5_SparseExecution.lean)要求输入不重复且完整的正容量边列表。它构造正反支持桶，在每次增广中使用实际 costed support BFS 保存的父链、瓶颈扫描及正反流量更新。`CLRS.Chapter26.SparseEK.execute_maximal`、`execute_augmentations_le`、`execute_work_bound`、`execute_work_empty`、`execute_work_uniform` 分别证明最大流、至多 `2VE` 次增广、`E>0` 时 `130VE²` work、`E=0` 时 `V+2` work 及统一界。证明针对实际 BFS 所选 Timeline，不声称与旧经典选择序列相等；`V` 包含孤立顶点，`E` 是正容量边数。

[RelabelExecution](../../../src/CLRSLean/FourthEdition/Chapter_24/Section_24_5_Relabel_To_Front/Execution.lean)构造源饱和初始化、非源 excess 缓存、当前邻居游标及内部顶点列表。push 实际进行两个索引弧写入；relabel 用计数最小值扫描；完成 discharge 时使用反向已处理前缀，move-to-front 使用计数 reverse-onto 循环。顺序、安静前缀和跳过邻居不变式由控制器保持。

`Trace.toRelabelToFrontRun` 从实际轨迹推出 discharge discipline；`execute_terminal` 用 `9V³+1` fuel 和原基本操作界证明终止；`initialized_maximum_flow` 不要求调用者给定合法初始状态、调度或终止证书。`initialized_work_le_cubic` 给出 `864V³` 界，`initialized_correct_and_cost` 汇总同一构造的输出与费用。

精确成本边界：RTF 的 `864V³` 是对实际初始化写入、控制/游标访问、最小值扫描和移动单元赋予固定 **32 单位 allowance** 的模型界，不是另行精化出的机器指令条数。EK 使用既有单位 dictionary/queue/bucket/精确实数原语模型。两者均不要求整数容量，均不声称持久容器求值/复制或 bit 运行时间；RTF 不是 mutable-array 精化。

[RTF 回归](../../../tests/Chapter_24_RelabelExecution.lean)验证初始化向中点送入 5、最终瓶颈流量 2，分数容量返回 `1/2`，空网络返回 0，零 fuel 未完成、无内部点的一次 dispatch 完成，以及缓存/扫描/移动计数。该文件及 8 项公理检查通过。[SparseEK 回归](../../../tests/Chapter_24_SparseExecution.lean)和所属模块由负责代理报告通过。RTF 模块窄构建 8,584 jobs、规范 Chapter 24 构建 8,612 jobs、`tests/Trust/Chapter_24.lean` 均通过。独立源码复核未发现可操作问题。

导读、旧 Chapter 26 的“deferred”文字、Chapter 24 两份元数据行及 trust 已同步。CSV 编辑逐行保留所有非 Chapter 24 原始行，两个 CSV 重新解析通过。

## 第 25 章：保留既有匹配执行，修正范围与方向说明（#367）

已有 [CostedRun](../../../src/CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/FlowExecution/CostedRun.lean)的 `costedMatchingRun_work_le_product` 和 `flowMethod_finds_maximum_matching_with_attached_cost` 已连接实际支持 BFS/增广、最大匹配、整数最大流及费用。本轮移除“adjacency execution 仍未闭合”的旧备注，并准确写成变换后网络 `20 * V_f * (E_f+1)`，其中 `V_f=|V|+2`、`E_f=|L|+|E|+|R|=|V|+|E|`。不能在有大量原图孤立点时直接宣称原图 `O(VE)`。

`CLRS.StableMarriage.gs_woman_pessimal` 的正确方向保持不变，注释改为女人不严格偏好 GS 伴侣胜过其他稳定伴侣；等基数完美性解除已配对前提。Hungarian 仍是经典实数选择下的终止数学构造，不新增低层多项式时间结论。本项是说明/元数据修复，不把先前完成的算法重复计算为新增成果。

## 第 26 章：矩阵维度域（#368）

[规范导读](../../../src/CLRSLean/FourthEdition/Chapter_26.lean)明确区分深度 `k`、维度 `2^k` 的实际 `pMatMul` 执行与任意 `n` 的数值递推包络。`pMatMul_value`、`pMatMul_correct` 及已存在的 carried work/span 证明保留；本轮没有构造任意维度矩阵的 padding/unpadding 执行。

已经连接执行的 completing greedy scheduler、并行归并/排序及 worst-family span 下界保留。不可变值上的 fork/work/span 不等于实际线程实现；list indexing、take/drop、append 分配不是已计入的 RAM 成本。该 issue 采用其允许的显式算法域修正。

## 第 27 章：合法缓存、历史策略与非空下界（#369）

旧 `CLRS.OnlineCaching.Algorithm.step_size/step_hit` 现在只对容量合法状态提出约束；`algorithm_nonempty` 和 `flushAlgorithm` 给出真实非空实例，原 `Fin(k+1)` 的全缓存矛盾不再成立。新 `Policy` 具有任意辅助 `State`，`lruPolicy` 的 recency 列表区分同驻留集合的不同历史；`Schedule` 独立表达可依赖未来的离线轨迹。

`Schedule.lru_k_competitive` 对每个合法离线 schedule 证明实际 LRU miss 界，`Policy.lru_k_competitive` 专用于在线策略运行；`offline_schedule_valid` 证明用于下界的 phase 离线构造合法。`Policy.no_real_competitive` 对正容量 `k`、任意历史策略、任意实数 `0≤c<k` 和任意实数加性常数 `b`，在 `Fin(k+1)` 上给出非空请求序列，满足 `c*offline+b < online`；两方从空缓存开始。

租赁的 `skiRental_lower_bound` 保留正 horizon 和严格正 offline cost；`skiRental_not_competitive_below` 排除严格小于 **`2-r/p`** 的比例，没有把离散固定参数结论写成无条件严格 2 下界。list-update 的集合相等接口保持；物理位置/最少相邻交换解释限于 Nodup permutations，未推广到任意离线列表轨迹。

[CacheValidity](../../../tests/Chapter_27_CacheValidity.lean)覆盖合法域实例、超容量输入不再导致矛盾、相同驻留集不同淘汰、命中更新历史，以及任意加性常数的 `3/2` 下界实例；[RentalPositive](../../../tests/Chapter_27_RentalPositive.lean)覆盖正代价见证。Chapter 27 构建（2,981 jobs）、这两个测试、旧 rental 接口与 trust 27 已报告通过。成本是竞争性 miss/租赁模型，不是机器运行时间。

## 第 28 章：BigO 与已有 costed LUP（#370）

修正旧 §28.1 对 `substitutionCost_isBigO`、`lupDecompositionCost_isBigO`、`matrixInversionCost_isBigO`、`choleskyCost_isBigO` 的 `Θ` 误述：这些定理只给上界，逆矩阵/Cholesky 数值预算不因此成为执行计数。

已有 `CLRS.Chapter28.lupDecomposeWithCost_correct`、`lupDecomposeWithCost_eq_none_iff`、`lupDecomposeWithCost_work_le` 及 `lupSolveWithCost_correct/work_le` 保留。求解的置换通过 `permuteVector_eq_permMatrix_mulVec` 证明直接索引精化，费用至多 `2n²` field operations。范围是 exact-field、可判零模型；不含浮点稳定性、分配、mutable storage 或 bit/RAM 内部费用。本轮为范围校正，并非重新实现 LUP。

## 第 29 章：已存在的规范求解包装（#371）

[SolverWrapper](../../../src/CLRSLean/FourthEdition/Chapter_29/Section_29_1_Standard_And_Slack_Forms/SolverWrapper.lean)早已把 general-form normalization 和 initialized SIMPLEX 组合。导读/入口不再声称完整 dictionary 支持仍在里程碑外。`CLRS.Chapter29.GeneralLP.solve` 返回 infeasible、optimal 或 unbounded，`solve_complete` 证明结果证书。

详细 simplex/初始化保留为 online material，经规范包装被主章使用。这是经典实数选择下的数学求解器；没有多项式 SIMPLEX、可计算实数实现或机器运行时间声明。

## 第 30 章：FFT 算术共享和 root setup（#372）

迭代 FFT 的 `omega ^ 2` child-root 构造明确列为未计入字段的 setup。递归/迭代蝶形字段采用共享乘积算术模型；函数值两个输出槽的独立求值并不证明 memoization。bit-reversal movement 有独立计数，parallel circuit 将 roots 视为常量。

`CLRS.Chapter30.recursiveFFT_eq_dft`、`complexFFTMultiply_correct`、`iterativeRadix2FFTExec_totalWork`、`iterativeRadix2FFTTotalWork_bigTheta` 保持各自正确性和模型内成本结论。本轮没有声称 DFT 正确性或既有 `Θ(n log n)` 被推翻，也没有把 `totalWork` 写成 literal evaluator 每条操作的精确计数。第 28–30 章联合正式窄构建已报告通过（8,729 jobs）；本轮范围修改经独立源码复核，无可操作问题。

## 第 31 章：Miller–Rabin、Euclid 与生成 RSA 密钥（#373）

后续完成的接口与最终验证见 [第 31 章专项记录](chapter-31.md)。本批 10,764 项构建发生在该章最终接入之前；接入后的全库结果见 [统一验收](verification.md)。

## 第 32 章：RK 缓存幂与 DFA 单表扫描（#374）

[CachedPower](../../../src/CLRSLean/FourthEdition/Chapter_32/Section_32_2_Rabin_Karp/CachedPower.lean)的 `CLRS.Chapter32.RKExecution.execute` 一次计算 `d^m` 和两个 seed hashes，把缓存幂传入每次 slide。slide 没有幂或窗口长度遍历，确含两次乘、两次加、一次减及两次余数。`execute_preparation`、`execute_refines`、`execute_correct`、`execute_chargedWork` 连接返回记录：power 乘法数 `m`、hash 字符数 `2m`、slide 数 `n-m`，以及旧 shift/confirmation 预算。确认仍按命中收取预算，list 移动、symbol-map 和 bit 成本排除；Nat 的 `x%0=x` 注释已纠正。

[CachedScan](../../../src/CLRSLean/FourthEdition/Chapter_32/Section_32_3_Finite_Automata/CachedScan.lean)的 `DFAExecution.execute` 只构造一次 transition table 并显式传给 scan。`execute_correct`、`execute_transitions`、`execute_cells` 证明匹配结果、每文本字符一次转移请求及 `(m+1)*|alphabet|` 格子数。格子计数不包含 `delta` 后缀搜索，alphabet/list 查找也不是常数时间；没有高效表构造运行时间声明。

后缀数组仍按整后缀比较计数，query 排除构造/list 索引/结果材料化；空模式只返回存储位置 `0,…,n-1`，不含末端 `n`。KMP 原控制步证明保留。[CachedExecution 回归](../../../tests/Chapter_32_CachedExecution.lean)覆盖模 1 全碰撞但精确确认、准备/slide/费用字段、空/过长模式、单表 DFA 及 `%0`。规范章构建（8,595 jobs）、该测试及公共公理检查已报告通过；独立源码复核无可操作问题。

## 阶段验证记录

本文撰写时已读取并核对以下日志末尾，而非仅根据文件存在推断通过：

- `/tmp/clrs-all-repairs-full-build.log`：`lake build CLRSLean` 成功，10,764 jobs。该里程碑含本记录第 21–30/32 章相关 companion，**发生在第 31 章最终新集成之前**。
- `/tmp/clrs-all-repairs-repo-check.log`：`scripts/check_repository.py` 报告 `Repository checks passed`，含当时的 Markdown local links 检查。
- `/tmp/ch28-30build.log`：第 28–30 章联合正式窄构建成功，8,729 jobs。
- `/tmp/ch32tests.log`：负责代理报告 exit 0；日志只有既有 Verso 工作树警告。
- 本记录作者执行的 RTF 源模块、`tests/Chapter_24_RelabelExecution.lean`、规范 Chapter 24 及 `tests/Trust/Chapter_24.lean` 检查均 exit 0；规范构建日志为 `/tmp/rtf-canonical-build.log`，trust 日志为 `/tmp/rtf-trust24.log`。

其余上述“已报告通过”的定向检查来自相应负责代理的交付记录，并以当前源文件、回归文件和 trust 表面列明证据。旧命名空间不代表测试属于同号第四版章节，例如旧 Chapter 26 最大流对应第四版 Chapter 24。

最终全库构建、仓库元数据/链接检查和集成状态见 [统一验收记录](verification.md) 与 [修复索引](index.md)。原始审查快照不因修复而改写。
