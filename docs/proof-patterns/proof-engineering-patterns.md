# CLRS-Lean 证明工程模式

本文只收录从卡壳案例中提炼、目前仍有独立复用价值的证明工程结构。它与
[几何证明模式](./geometric-proof-patterns.md) 和
[CLRS-Lean 活页手册](./clrs-lean-playbook.md) 互补，而不重复前者的
Boundary、Exchange、Fiber、Interval 等 proof shape，也不重复后者的通用
战术速查与章节推进计划。循环不变式通用模板、渐近桥接堆叠和几何 atlas 条目
因此不在本 catalog 中另立模式。

## 1. 按字段证明 fold 保持性

**结构**：record 状态经过列表 fold 时，先固定一个前置状态条件，再为每个字段
分别证明单步不变和 fold 不变。各证明共享
`induction l generalizing s`、分支判定和 `simp` 骨架，只替换字段投影与局部
保持引理。

**当前实例**：
`CLRSLean/Chapter_22/Section_22_3_DFS.lean` 中的
`dfsVisit_fold_preserves_d_of_black`、
`dfsVisit_fold_preserves_f_of_black`、
`dfsVisit_fold_preserves_d_of_not_white` 和
`dfsVisit_fold_preserves_f_of_not_white`；parent 字段的对应结果位于
`CLRSLean/Chapter_22/Section_22_3_DFS/S2_Intervals.lean`。

**使用准则**：当状态更新函数只改少数字段，而后续证明频繁查询未改字段时，
优先建立字段级 API。字段很多且证明骨架稳定后，可以考虑生成模板；在确认至少
两个独立消费者前，不必把它提升成重型框架。

## 2. 枚举式关系引理族

**结构**：对一个更新操作系统覆盖 `x = y`、`x ≠ y`、`mem`、`not_mem`、
布尔查询与命题查询之间的组合。核心语义定理只证明一次，其余结果通过对称、
改写或单行转发组成可搜索的接口族。

**当前实例**：
`CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion.lean` 中的
`delete_mem_iff`、`delete_mem_iff_ne`、`delete_search_iff`、
`delete_search_iff_ne`、`delete_search_of_mem_ne` 和
`delete_search_false_of_not_mem`。同章插入模块为 `splitChild` 与
`insert` 提供同形的 membership/search 接口。

**使用准则**：树的 insert、delete、split、join 一旦同时服务布尔查询和
`Prop` 规范，就应先列关系矩阵，选择一两个核心 iff 作为事实源，再生成或转发
其余命名定理。这样能避免下游反复展开实现定义。

## 3. 复合不变量的组件分解

**结构**：把复合良构性拆成可以独立保持的分量，为每个分量建立局部修复、
递归调用和重组引理，最后再打包。组件边界应跟实际递归分支需要的假设一致，
而不是为了表面简短把所有条件塞进一个不可分解谓词。

**当前实例**：Chapter 18 的 B-tree 删除把 `SameDepth`、`Sorted`、
`ChildBounded`、`Occupancy` 分别交给
`composedDelete_sameDepth_height`、`composedDelete_sorted`、
`composedDelete_childBounded`、`composedDelete_occupancy`，再由
`CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ComposedPreservation.lean`
中的 `composedDelete_packet` 汇总。

红黑树必须区分形状与顺序：

```text
RedBlackShape = RootBlack ∧ NoRedRed ∧ BalancedBlackHeight
```

`BST` 排序是独立的前提或不变量，不属于 `RedBlackShape`。相关定义位于
`CLRSLean/Chapter_13/Section_13_1_Red_Black_Trees.lean`。

**使用准则**：如果一个递归分支只消费复合不变量的一部分，就公开该组件引理；
只有公共入口和最终正确性定理应重新打包完整条件。

## 4. 不变量与语义的捆绑归纳

**结构**：递归定理的归纳结论同时返回
`PreservesInvariant ∧ RefinesToSpec`。递归调用后，保持性投影为后续缓存、
summary 或局部修复提供合法性，语义投影负责最终规格等式；二者不是两次独立
遍历。

**当前实例**：
`CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean` 中的
`delete_correct` 同时给出 `WellFormed` 保持和 `toFinset = Finset.erase`
语义，`delete_wellFormed` 与 `delete_toFinset` 是其投影。Chapter 18 的
`composedDelete_packet` 也一次返回多个结构组件；精确多重集语义随后由
`CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Exact.lean` 中的
`composedDelete_keyBag` 接上。

**使用准则**：带缓存、摘要或冗余字段的数据结构，如果语义证明的递归分支需要
“递归结果仍良构”，应直接加强归纳结论；不要在完成单一语义定理后再复制整套
归纳来追补保持性。

## 5. fuel 化递归与双燃料加强归纳

**结构**：显式 fuel 把递归深度变成普通自然数归纳参数；当算法内部还有一个
递归子过程时，归纳命题同时量化外层 fuel 与内层 fuel，并保留“当前输入长度
不超过两种 fuel”的假设。真正的加强点是归纳假设可用于任意足量 fuel，而不是
把两个参数机械地设成同一个长度。

**当前实例**：
`CLRSLean/Chapter_22/Section_22_3_DFS/S3_Bridge.lean` 中的
`dfsVisit_white_to_nonwhite_disc_ge_time` 用 fuel 穿透 DFS；
`CLRSLean/Chapter_09/Section_09_3_Deterministic_Select.lean` 中的
`recursiveMedianOfMediansPivotFuel?` 与 `selectCostFuel` 分别表达 pivot
和 selector 的递归预算，双燃料加强最终支撑公开结果
`recursiveMedianOfMediansComparisonCost_linear_bound`。

**使用准则**：非结构递归、nested recursion 或同一输入经不同子过程递减时，
先问“哪几个递归预算需要在归纳假设中独立变化”。fuel 不替代终止性事实；
公共 wrapper 仍应选择足量 fuel，并证明它与无 fuel 的规格一致。

## 6. 弱化不变量与赤字吸收

**结构**：局部删除或修复会暂时破坏强不变量时，定义只放宽一个明确位置的弱化
谓词，让赤字向父层传播；再平衡器每次吸收一层赤字，最终在根处恢复强不变量。
弱化的范围和恢复点必须写进接口，不能以模糊的“几乎良构”代替。

**当前实例**：
`CLRSLean/Chapter_13/Section_13_1_Red_Black_Trees.lean` 中的 `NoRedRed2`
允许通过重涂根处理局部红红冲突，`baldL` 与 `baldR` 吸收左右黑高赤字，
`baldL_shape`、`baldR_shape`、`del_invariant` 连接局部修复与最终形状。

**使用准则**：平衡树或堆的删除中，如果每层都要求完整不变量导致组合失败，
寻找一个可单步偿还的 deficit，并证明“传播量至多一层”。不要一次弱化多个
互不相关的性质，否则最终恢复定理会重新变成单体大目标。

## 7. 用谓词包装归纳条件

**结构**：把长而反复出现的归纳侧条件命名成谓词，为它提供 base、step、
单调性和终点引理。归纳命题于是围绕一个稳定概念陈述，而不是携带易变的展开式。

**当前实例**：
`CLRSLean/Chapter_25/Section_25_2_Floyd_Warshall.lean` 中的 `Through S i j p`
表示路径 `p` 的中间顶点受集合 `S` 限制；它使 Floyd–Warshall 的逐顶点归纳
能直接连接 `floydWarshall_le_walk` 与 `floydWarshall_isShortestDist`。

**使用准则**：图路径、受限可达性或阶段化动态规划中，如果同一侧条件出现在
三个以上定理签名中，先为其命名。谓词应暴露恰好够归纳使用的构造和消去 API，
不要只把复杂表达式换一个名字后仍在每个证明里完全展开。

## 8. 按定义形态选择 tactic

**结构**：当 `rw`、`simp` 或归纳原则持续失配时，先检查定义生成的表达式形状，
再决定改 tactic 还是改定义。目标是让定义拥有稳定的展开式和可用的消去原则，
而不是依赖脆弱的化简偶然性。

**当前实例**：

- `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model.lean` 把 `SameDepth` 设为
  归纳定义，并让 `splitChild` 采用便于改写的无 `let` 形态；其接口由
  `splitChild_preserves_sameDepth` 等保持定理封装。
- Chapter 18 删除的 `composedDelete` 使用非依赖式条件，便于在选定分支后
  展开；后续证明优先经 `composedDelete_packet` 与组件投影使用它。
- Chapter 25 的复盘记录显示，coercion 目标常更适合 `simpa` 或先用 `set`
  固定中间项；需要改变归纳变量顺序时，`revert`、`induction`、`intro`
  比在原目标上强行 `generalizing` 更稳定。

**使用准则**：先做最小复现并查看实际 goal；只有当多个下游证明都被同一形态
阻塞时才调整定义。定义调整后，以命名 theorem 作为长期接口，避免消费者再次
依赖内部展开细节。
