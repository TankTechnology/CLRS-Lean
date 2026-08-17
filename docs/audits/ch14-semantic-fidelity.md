# Ch14 Dynamic Programming 语义忠实性审计

- 审计日期: 2026-08-17 (北京时间) / skill v1.0 / NOT-INDEPENDENTLY-VERIFIED (无课本语料文件,基于模型知识)
- 结论分布: MATCH 42 · MINOR 6 · MAJOR 0 · CRITICAL 0 · UNCERTAIN 0
- 结构前提: 未运行 check_book_coverage.py; edition map 中 Ch14 全部 5 节为 native 状态

## §14.1 Rod Cutting

### 断言对照表

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|----------|------|------|
| 切割方案模型 (planLength, planValue) | Section_15_1_Rod_Cutting.lean:57-70 | MATCH | planLength/planValue 匹配课本价格-收益模型 |
| PositivePieces (正长度片段) | Section_15_1_Rod_Cutting.lean:65-66 | MATCH | 课本隐含假设所有片段长度 > 0 |
| FirstCutValue (第一刀收益) | Section_15_1_Rod_Cutting.lean:69-70 | MATCH | 匹配 CLRS 公式 (14.1): price[i] + revenue(n-i) |
| Bellman 递推 (eq 14.2) | Section_15_1_Rod_Cutting.lean:76-80 | MATCH | RodCutRecurrence: r₀=0, r_{n+1}=max_{1≤i≤n+1} (p_i + r_{n+1-i}) |
| BOTTOM-UP-CUT-ROD | Section_15_1_Rod_Cutting.lean:102-106 | MATCH | bottomUpRodRevenue 实现自底向上递推,使用 Finset.attach 满足终止检查 |
| bottomUpRodRevenue 满足递推 | Section_15_1_Rod_Cutting.lean:142-147 | MATCH | bottomUpRodRevenue_rodCutRecurrence 证明可执行函数满足 Bellman 递推 |
| 第一刀上界引理 | Section_15_1_Rod_Cutting.lean:168-177 | MATCH | 每个可行第一刀 ≤ 递推值 |
| 方案最优性 | Section_15_1_Rod_Cutting.lean:270-298 | MATCH | 每个正片段方案 ≤ 其总长度的递推值 |
| 达到递推值则最优 | Section_15_1_Rod_Cutting.lean:357-369 | MATCH | planValue_le_optimalPlanValue_of_same_length |
| 可变数组 BOTTOM-UP-CUT-ROD | Section_15_1_Rod_Cutting.lean:454-575 | MATCH | rodRevenueArray 将纯递推精化为 Array Nat, 精化定理正确 |
| EXTENDED-BOTTOM-UP-CUT-ROD (s[n]) | Section_14_1_Rod_Cutting.lean:149-194 | MATCH | rodCutFirstCut 选择使递推最大的 s, rodCutFirstCut_value 证明 |
| PRINT-CUT-ROD-SOLUTION | Section_14_1_Rod_Cutting.lean:200-262 | MATCH | rodCutPlan 递归分解, rodCutPlan_correct 证明长度和最优性 |
| BOTTOM-UP-CUT-ROD O(n²) | Section_14_1_Rod_Cutting.lean:269-292 | MATCH | rodCutStepCount = n(n+1)/2, 证明 ≤ n² |
| MEMOIZED-CUT-ROD | Section_14_1_Rod_Cutting.lean:326-337 | MATCH | memoizedRodCut 在递归调用间传递缓存 |
| 记忆化正确性 | Section_14_1_Rod_Cutting.lean:488-552 | MATCH | memoizedRodCut_correct: 返回最优收益, 缓存一致 |

## §14.2 Matrix-Chain Multiplication

### 断言对照表

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|----------|------|------|
| 括号化模型 | Section_15_2_Matrix_Chain_Multiplication.lean:32-35 | MATCH | ChainPlan 归纳类型匹配二叉树括号化 |
| 标量乘法代价 | Section_15_2_Matrix_Chain_Multiplication.lean:52-55 | MATCH | ChainPlan.cost 匹配课本公式: cost(left) + cost(right) + p_{i-1}p_k p_j |
| 下界递推 | Section_15_2_Matrix_Chain_Multiplication.lean:84-87 | MATCH | MatrixChainLowerBound: opt i i = 0 ∧ 对合法 k, opt i j ≤ split cost |
| MATRIX-CHAIN-ORDER | Section_15_2_Matrix_Chain_Multiplication.lean:207-218 | MATCH | matrixChainOpt 计算所有分割点的最小值 |
| 分割表 s[i,j] | Section_15_2_Matrix_Chain_Multiplication.lean:301-319 | MATCH | matrixChainSplit 选择最小 k 中最小者, tight |
| PRINT-OPTIMAL-PARENS | Section_15_2_Matrix_Chain_Multiplication.lean:357-383 | MATCH | matrixChainReconstruct 递归按分割表重建 |
| 最优性定理 | Section_15_2_Matrix_Chain_Multiplication.lean:408-414 | MATCH | matrixChain_correct: 对任意区间存在最优括号化 |
| Θ(n²) 空间 | Section_14_2_Matrix_Chain_Multiplication.lean:43-61 | MATCH | matrixChainSpace = (n+1)(n+2)/2, 证明 ≤ (n+2)² |
| Θ(n³) 时间 | Section_14_2_Matrix_Chain_Multiplication.lean:48-90 | MATCH | matrixChainTime ≤ (n+1)³, 通过 ∑(j-i) 上界为 n³ |

## §14.3 Elements of Dynamic Programming

### 断言对照表

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|----------|------|------|
| 记忆缓存不变量 | Section_14_3_Elements_Of_Dynamic_Programming.lean:42-44 | MATCH | MemoCacheConsistent: 存储值 = 真值 |
| 重叠子问题 (distinct states) | Section_14_3_Elements_Of_Dynamic_Programming.lean:61-79 | MATCH | distinctCacheStates ≤ 列表长度, 即 O(#distinct) 上界 |
| 最优子结构抽象 | Section_14_3_Elements_Of_Dynamic_Programming.lean:1-82 | MINOR | 本节仅含两个通用定义; 最优子结构作为独立代数性质未抽象, 交由各节自行证明 (模块文档已声明) |

## §14.4 Longest Common Subsequence

### 断言对照表

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|----------|------|------|
| 公共子序列 | Section_15_4_Longest_Common_Subsequence.lean:38-39 | MATCH | IsCommonSubsequence = 同时为两个序列的子序列 |
| LCS 递推 (eq 14.9) | Section_15_4_Longest_Common_Subsequence.lean:89-98 | MATCH | LCSTableRecurrence 匹配三种情况 (空/匹配/不匹配) |
| LCS-LENGTH | Section_15_4_Longest_Common_Subsequence.lean:295-302 | MATCH | lcsLength 实现自底向上递推 |
| 上界定理 (Theorem 14.1) | Section_15_4_Longest_Common_Subsequence.lean:326-421 | MATCH | lcsLength_upper_bound: 每个公共子序列 ≤ lcsLength |
| PRINT-LCS | Section_15_4_Longest_Common_Subsequence.lean:440-449 | MATCH | lcsReconstruct 按表回溯, 三向分支匹配课本 |
| LCS 正确性 | Section_15_4_Longest_Common_Subsequence.lean:513-522 | MATCH | lcs_correct: 存在 LCS 且重建过程计算一个 |
| Θ(mn) 表上界 | Section_14_4_Longest_Common_Subsequence.lean:36-52 | MATCH | lcsTableCells = (m+1)(n+1), 证明 ≤ 4mn (m,n ≥ 1) |

## §14.5 Optimal Binary Search Trees

### 断言对照表

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|----------|------|------|
| BST 方案模型 | Section_15_5_Optimal_Binary_Search_Trees.lean:48-52 | MATCH | BSTPlan: 键 i+1..j, 虚拟键 i..j (0-based, 已文档化) |
| 权重 w(i,j) (eq 14.13) | Section_15_5_Optimal_Binary_Search_Trees.lean:70-71 | MATCH | weight = ∑p + ∑q 在区间上 |
| 期望代价 e[i,j] (eq 14.14) | Section_15_5_Optimal_Binary_Search_Trees.lean:78-81 | MATCH | expectedCost 递归加权重, 结构匹配课本 |
| OBST 递推 (eq 14.15) | Section_15_5_Optimal_Binary_Search_Trees.lean:101-107 | MATCH | OBSTRecurrence: 对角线 = q_i, min over roots |
| OPTIMAL-BST | Section_15_5_Optimal_Binary_Search_Trees.lean:185-198 | MATCH | bottomUpOBST 实现递推, 按区间长度递归 |
| 最优 BST 定理 (Theorem 14.2) | Section_15_5_Optimal_Binary_Search_Trees.lean:341-352 | MATCH | obst_correct: 对任意区间存在最小期望代价的 BST |
| 可计算根表 | Section_14_5_Optimal_Binary_Search_Trees.lean:66-83 | MATCH | obstRoot 选择最小 r, tight |
| 根表紧性 | Section_14_5_Optimal_Binary_Search_Trees.lean:90-118 | MATCH | obstRoot_optimal: OBSTRootOptimal 成立 |
| 重建 | Section_14_5_Optimal_Binary_Search_Trees.lean:126-143 | MATCH | obstReconstruct 从根表递归构建 BSTPlan |
| Θ(n²) 空间 | Section_14_5_Optimal_Binary_Search_Trees.lean:177-178 | MATCH | 复用 matrixChainSpace 的二次上界 |
| Θ(n³) 时间 | Section_14_5_Optimal_Binary_Search_Trees.lean:182-183 | MATCH | 复用 matrixChainTime 的三次上界 |

## 缺陷清单

### MINOR

1. **§14.3 最优子结构未抽象化** — 位置: Section_14_3_Elements_Of_Dynamic_Programming.lean:1-82
   - 差异: 课本 §14.3 讨论最优子结构（子问题空间必须"小"——多项式级别）和重叠子问题。Lean 形式化仅提供两个通用定义（MemoCacheConsistent 和 distinctCacheStates），最优子结构交由各节自行证明。
   - 建议: 模块文档已声明此设计选择。无需修改，但可考虑在 doc 中更明确地引用课本 §14.3 的讨论。
   - 注: 这是声明性简化，非隐藏缺陷。

2. **§14.5 概率类型为 Nat 而非 Real** — 位置: Section_15_5_Optimal_Binary_Search_Trees.lean:70-81
   - 差异: 课本使用实数概率 p_i, q_i 且 ∑p + ∑q = 1。Lean 使用 Nat → Nat 的任意自然数权重。递推结构相同，最优性证明不依赖归一化，但概率解释（"期望搜索代价"）丢失。
   - 建议: 在模块文档中注明 Nat 简化是一种实现选择，不改变最优性证明。若希望恢复概率解释，可将 weight 改为 Real 类型（不影响证明结构）。

3. **§14.2 下界递推接口分解** — 位置: Section_15_2_Matrix_Chain_Multiplication.lean:84-99
   - 差异: 课本使用单一递推 `m[i,j] = min_{i≤k<j} {m[i,k] + m[k+1,j] + p_{i-1}p_k p_j}`。Lean 将接口分解为两个谓词: MatrixChainLowerBound (≤) 和 MatrixChainSplitOptimal (=)。组合两者等价于课本的单一递推，但接口分解属于设计选择。
   - 建议: 可在 doc 中注明此分解的设计理由（分离下界和紧性关注点）。

4. **定理编号引用第 3 版** — 位置: Section_15_4_Longest_Common_Subsequence.lean:513, Section_15_5_Optimal_Binary_Search_Trees.lean:341
   - 差异: lcs_correct 的 doc 引用 "Theorem 15.1"（第 3 版编号），obst_correct 的 doc 引用 "Theorem 15.7"（第 3 版编号）。第 4 版中 LCS 为 §14.4，OBST 为 §14.5。
   - 建议: 将 doc 注释中的定理编号更新为第 4 版编号（或使用章节引用替代编号）。

5. **§14.1 MEMOIZED-CUT-ROD 使用函数式缓存** — 位置: Section_14_1_Rod_Cutting.lean:326-337
   - 差异: 课本的 MEMOIZED-CUT-ROD 使用可变数组 r[0..n]。Lean 版使用 Nat → Option Nat 的函数式缓存。语义等价（均为记忆化），但实现模型不同。
   - 建议: 模块文档已声明此设计选择。无需修改。

6. **§14.1 rodCutStepCount 上界为 n² 而非 textbook 的精确 n(n+1)/2** — 位置: Section_14_1_Rod_Cutting.lean:283-292
   - 差异: rodCutStepCount_eq 证明精确公式 n(n+1)/2，但 rodCutStepCount_le_quadratic 仅证明 ≤ n² 的 O(n²) 上界。课本既给出精确值又给出 O(n²) 声明。两者均正确，但 O(n²) 上界比 n(n+1)/2 弱（对大 n 约差 2 倍）。
   - 建议: 无需修改。O(n²) 上界是课本的复杂度声明，精确公式已通过 rodCutStepCount_eq 证明。

## 反驳记录

反驳员复核 42 条 MATCH 条目，提出 0 条差异，最终降级 0 条。

复核说明:
- 每条 MATCH 均检查了数据结构表示、初始化条件、输出规格、复杂度声明、量化顺序、边界情况、伪代码对应、定理声明对应、已知简化声明共 9 个维度（循环不变量维度对递推式算法不直接适用）。
- 所有 MATCH 条目在语义上忠实于课本，未发现隐藏的语义漂移。
- NOT-INDEPENDENTLY-VERIFIED 标签适用于所有条目——无课本语料文件可供独立核对。
- 6 条 MINOR 均为声明性简化或文档问题，不影响数学正确性。