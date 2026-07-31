# 卡壳案例复盘（截至 2026-07-24）

> 本文是提交历史与证明攻坚路径的时间点复盘，不是当前待办清单。
> “后续结果”按 2026-07-31 的仓库状态补记。

本文依据 2026-06-23 至 2026-07-24 的提交时间线、提交说明和当时的项目台账，
整理七个代表性证明卡壳案例。时间跨度和提交数量是该时间点的近似观察；
“沉默期”也可能包含其他章节的并行工作，因此这里只把提交顺序当作证据，
不把它解释成单一原因或精确工时。

## 七个代表性案例

### 案例 1：Chapter 18.1 `splitChild` 的四类保持定理

- **跨度**：2026-07-06 至 2026-07-08，约两天半、约二十个提交。
- **提交观察**：`6da958f` 尝试用 `match` 分解 `splitChild`，约七分钟后的
  `65a6d09` 恢复干净状态；提交说明点名了 `Sublist.subset` 和
  `List.get_mem` 的接口障碍。随后形成了 `docs/sorted-childbounded-notes.md`
  这份攻坚笔记。
- **当时的主要障碍**：提交说明与后续改写共同表明，`splitChild` 中的
  `let` 绑定妨碍了 `rw`、`dsimp` 和类型类搜索；`SameDepth` 的旧定义形态
  也不便解构。
- **收口路径**：`SameDepth` 改为归纳定义，`splitChild` 改成无 `let`
  的形态，再以 `sameDepth_take`、`sameDepth_drop`、`pairwise_get_mono`
  等铺路引理分别完成深度、占用、排序和子区间界。
- **模块与结果**：
  `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model.lean` 中的
  `splitChild_preserves_sameDepth`、`splitChild_preserves_occupancy`、
  `splitChild_preserves_sorted`、`splitChild_preserves_childBounded` 和
  `splitChild_preserves_wellFormed`。

### 案例 2：Chapter 25 Floyd–Warshall 的 `WithTop ℝ` coercion

- **跨度**：2026-07-13 至 2026-07-23，约十天。
- **提交观察**：`d94d83b` 记录“并非所有证明都能编译”，`dc50d37` 记录
  尚有约十五个错误；约一周后重新铺设基础设施，并在两天内完成核心证明。
  复盘随后还专门纠正了“缺少 `AddRightMono`”这一判断。
- **当时的主要障碍**：官方复盘记录了 `WithTop ℝ` 的隐式与显式 coercion
  使 `rw` 难以匹配、`subst` 在相关等式上不适用，以及过度展开造成的长分支。
- **收口路径**：以 `Through` 命名路径中间点条件；用
  `Option.ne_none_iff_exists'` 回到实数见证；用
  `revert`、`induction`、`intro` 重新排列归纳变量；在最小独立文件里诊断
  coercion。该顺序与证明收口相伴出现，但仅凭提交时间线不能把它归结为某一
  个技巧的单独作用。
- **模块与结果**：
  `CLRSLean/Chapter_25/Section_25_2_Floyd_Warshall.lean` 中的 `Through`、
  `floydWarshall_le_walk` 和 `floydWarshall_isShortestDist`；详细复盘见
  `docs/superpowers/lessons/ch25-proof-retrospective.md`。

### 案例 3：Chapter 22 Kosaraju SCC 的跨层 DFS 不变量

- **跨度**：2026-07-05 至 2026-07-10，约五天、约三十个主体提交，随后还有
  一批重构提交。
- **提交观察**：`d112984` 记录还剩五处占位，`b2452d6` 新开桥接文件并记录
  `v ≠ u` 分支仍未完成；燃料归纳随后完成
  `dfsVisit_white_to_nonwhite_disc_ge_time`，`79791d0` 修复桥接并完成
  `scc_finish_time_order`。`exists_discovery_state` 的返回包在过程中多次加入
  nonwhite、black-finish、`f` 保持和 suffix 字段。
- **当时的主要障碍**：DFS 的 fold 累积器跨越多层递归，中间状态不变量无法
  直接由外层结构归纳取得；收尾阶段还需要对齐 merge sort 使用的严格关系与
  非严格关系。
- **收口路径**：把跨层性质移到
  `CLRSLean/Chapter_22/Section_22_3_DFS/S3_Bridge.lean`，以 fuel 归纳穿透
  `dfsVisit`，并用 `dfsVisit_fold_blackens_loc_prefix` 处理 fold 前缀。
- **模块与结果**：除桥接模块外，
  `CLRSLean/Chapter_22/Section_22_3_DFS/S4_SCC.lean` 提供
  `exists_discovery_state`，
  `CLRSLean/Chapter_22/Section_22_5_Strongly_Connected_Components.lean`
  提供 `scc_finish_time_order`。

### 案例 4：Chapter 13/14 红黑树删除的表示转换

- **跨度**：2026-06-24 至 2026-07-20，约二十六天。
- **提交观察**：2026-07-11 的提交说明把完整可执行的删除修复循环留作后续；
  次日引入 `baldL`、`baldR` 和弱化不变量 `NoRedRed2`；2026-07-13 完成
  可执行删除与 membership，2026-07-20 再由 `baldL_shape`、
  `splitMin_invariant` 和 `del_invariant` 补齐形状保持，Chapter 14 随后镜像。
- **当时的主要障碍**：提交序列显示，命令式双黑循环难以直接组合进当前的
  函数式树模型。
- **收口路径**：改用 Okasaki/Kahrs 风格的函数式删除，让 `baldL` 与
  `baldR` 吸收一层黑高赤字，以 `NoRedRed2` 容纳局部暂时弱化，再通过
  `splitMin` 与 `join` 组合。先完成 membership、后完成形状保持，是这段
  历史中可直接观察到的两阶段顺序。
- **模块与结果**：
  `CLRSLean/Chapter_13/Section_13_1_Red_Black_Trees.lean` 中的
  `baldL_shape`、`baldR_shape`、`splitMin_invariant` 和 `del_invariant`。

### 案例 5：Chapter 20 vEB 递归删除的语义不变量

- **跨度**：2026-07-13 至 2026-07-15，共三天。
- **提交观察**：`ed68dda` 记录四个 deferred 分支并指出需要
  `WellFormed`；同日出现设计文档、计划文档和接口测试，随后完成全部删除
  证明。文档还识别出 detached-minimum 子句缺失时，无条件删除定理并不成立。
- **当时的主要障碍**：没有表示不变量时，summary 与缓存 min/max 分支无法
  使用足够强的递归假设。
- **收口路径**：引入 `MinCorrect`、`MaxCorrect`、`WellFormed`，并在
  `delete_correct` 中同时归纳“不变量保持”和 `Finset.erase` 语义。后续
  insert 证明还暴露了重复插入会丢失 detached minimum 的实现问题。
- **模块与材料**：
  `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean` 中的
  `delete_correct`、`delete_wellFormed`、`delete_toFinset`；设计见
  [vEB 删除正确性设计](../superpowers/specs/2026-07-14-ch20-veb-delete-correctness-design.md)，
  实施计划见
  [vEB 删除正确性计划](../superpowers/plans/2026-07-14-ch20-veb-delete-correctness-plan.md)。

### 案例 6：Chapter 4 主定理的离散到连续桥接

- **跨度**：2026-06-24 至 2026-07-06，约十二天。
- **提交观察**：`524fb76` 的说明称三个 case 已完成，同日的 `b009222`
  又澄清 Chapter 4 和 Chapter 5 仍是部分结果，实际边界是 exact powers；
  次日连续出现 transfer bridge 与 wrapper 提交，2026-07-06 收口 case 3
  的 regularity bridge。
- **当时的主要障碍**：离散尺度与教科书实指数尺度之间需要显式渐近等价；
  case 3 还要把 CLRS regularity 条件连接到尾项支配。
- **收口路径**：以
  `criticalPowerScale_isBigTheta_realLogScale`、`isBigTheta_trans` 和
  `Case3Regularity` 分层组合。提交顺序支持“桥接层逐步补齐”的描述，但不支持
  把每一个 wrapper 都解释为不可替代的因果步骤。
- **模块与结果**：
  `CLRSLean/Chapter_04/Section_04_6_Master_Theorem_All_Input.lean` 中的
  `criticalPowerScale_isBigTheta_realLogScale` 与 `Case3Regularity`。

### 案例 7：Chapter 18.3 `composedDelete` 良构性

- **跨度**：2026-06-25 至 2026-07-24，约三十天，是本次时间窗中跨度最长的
  攻坚记录。
- **提交观察**：2026-07-12 得到 leaf removal 与 internal merge-recurse
  的部分结果，次日解决一版终止性问题；2026-07-20 重做辅助引理，
  `22ffcee` 在 2026-07-24 建立四组件框架。当时
  `composedDelete_key_bound_lo` 仍是占位。
- **当时的主要障碍**：一方面 merge 分支不呈现简单的结构缩小；另一方面
  `WellFormed` 同时包含 `SameDepth`、`Sorted`、`ChildBounded` 与
  `Occupancy`，单体目标很难维护。
- **截至时间点的部分进展**：`heightOf_mergeNodes_eq_max` 支持基于高度的
  终止性论证；四个组件分别推进，并复用插入侧的 occupancy 与 child-bounded
  基础设施；把依赖式 `if` 改成普通条件后，`rw [composedDelete]` 更容易展开。
  当时剩余问题集中在 merge 的 child-bounded 与 key-bound transfer。
- **模块**：
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion.lean`，以及后续拆出的
  `ComposedPreservation`、`Exact`、`WellFormed`、`SameDepthHeight` 等删除
  子模块。AFP B-tree 删除架构的后续对照见
  `docs/research/afp-btree-deletion-architecture-2026-07-27.md`。

**后续结果（截至 2026-07-31）**：Chapter 18 的搜索、插入、结构删除、
精确删除与高度闭环均已完成，当前进度为 `134/134`。结构保持由
`composedDelete_packet` 汇总，精确语义由 `composedDelete_keyBag` 与
`composedDeleteRoot_correct` 收口，高度结果由
`wellFormed_height_log_bound` 给出。因此本案例描述的是 2026-07-24 的
历史卡点，不是当前开放问题。

## 附：流程性碰撞——Chapter 14 并行 PR 重复

2026-07-11，同一工作被并行 agent 重复实现，PR #8 与 #15、PR #16 与 #17
分别重叠，随后又出现两次 “reconcile status after main merge” 修复。
worktree 隔离、并行 agent runbook 和 QA agent 在时间线上紧随其后；这说明
该碰撞与流程加固存在明确关联，但现有记录不足以断言它是这些流程变化的唯一
原因。

## 截至 2026-07-24 的五类卡壳

| 类型 | 当时的代表案例 | 当时可复用的处理方式 |
|---|---|---|
| coercion / 类型层 | Chapter 25 的 `WithTop ℝ` | 用 `simpa` 避免脆弱 `rw`，用 `set` 命名中间项，最小复现诊断 coercion |
| 表示设计 | Chapter 13/14 的函数式删除、Chapter 20 的 `WellFormed`、当时仍 deferred 的一般尺寸 Strassen | 换成证明友好的等价表示，分开规范层与实现层，并显式登记低层细化边界 |
| 归纳强度不足 | Chapter 9 的双燃料、Chapter 20 的捆绑定理、Chapter 22 的 fuel 桥接 | 加强归纳命题，把不变量与语义一起打包，或显式 fuel 化递归 |
| 大目标难以整体维护 | Chapter 4 的尺度桥、Chapter 18 的四组件不变量、Chapter 23 Kruskal | 拆组件、分层桥接，再以小型 wrapper 汇总 |
| 数学层实质缺口 | 当时的 Chapter 7 期望和恒等式、Chapter 5.4 对数界、floor/ceiling 一般递推 | 在该快照中尚未全部突破；应先冻结精确定理边界，再补数学桥 |

**后续结果（截至 2026-07-31）**：Chapter 7 的期望桥
`sum_compared_prob_eq_expectedComparisons` 和 `Θ(n log n)` 结果
`expectedComparisons_isBigTheta_nlogn` 已完成，不能再列作开放数学缺口。
按当前进度台账，partial 章节恰为 **19、26、27、33**；这份当前列表不应从
上表的历史例子反推。

## 截至 2026-07-24 的节奏信号

在案例 1、2、5 的提交时间线上，都能看到近似序列：

**wip/partial 提交 → 一段低密度期 → design、plan 或攻坚笔记增加 → 随后密集收口。**

这是值得用于项目管理的关联信号：卡住后把目标、表示不变量和接口写成文档，
常与后续证明收口同时出现。不过样本很小，低密度期可能在推进其他工作，
因此它不能证明文档工作单独导致了收口。相对地，案例 6 中“完成”与
“澄清 partial”在同日相邻，是应触发范围复核的提交信号，而不是对作者动机
或证明质量的因果判断。

## 解读边界

- 本文保留的是截至 2026-07-24 的提交与证明路径观察，不承担当前状态台账的
  角色。
- deferred 项常常是主动延迟的 RAM、数组或指针细化；不能仅凭 deferred 标签
  判断曾经“卡死”。
- 提交之间的时间间隔不等于投入时长，表示调整与证明完成的先后关系也不自动
  构成因果证明。
