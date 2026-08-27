# Ch04 Divide-and-Conquer 语义忠实性审计

- 审计日期(北京时间): 2026-08-18 12:36 CST / skill 版本 v1 / 基准来源: 第四版第 4 章 (pp. 78--125)
- 结论分布: MATCH 57 · MINOR 13 · MAJOR 0 · CRITICAL 0 · UNCERTAIN 0
- 结构前提: check_book_coverage.py 通过 (Chapter 4 全部 native, 无覆盖漂移)

## 断言对照表

### §4.1 Multiplying Square Matrices

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| 幂次方阵假设 (p.81) | `Section_04_1_Multiplying_Square_Matrices.lean:154-156` (SqMat) | MATCH | SqMat R k 为深度索引的 2^k×2^k 方阵,块分解 `!![A 0 0, A 0 1; A 1 0, A 1 1]` 对应教科书 A11,A12,A21,A22 分割 |
| 基例 n=1 (p.83 line 3) | `Section_04_1_Multiplying_Square_Matrices.lean:73-74` (mulRec 0) | MATCH | 深度 0 时为标量乘法,对应教科书基例 |
| 8 次递归调用 (p.83 lines 8-15) | `Section_04_1_Multiplying_Square_Matrices.lean:76-79` | MATCH | 8 次递归调用一一对应教科书 lines 8-15 |
| 输出规格 C=C+A·B (p.83) | `Section_04_1_Multiplying_Square_Matrices.lean:73` | MINOR | Lean 返回纯乘积 A*B,教科书为累加 C=C+A·B;等价于 C 初始化为零后调用 |
| 递推式 T(n)=8T(n/2)+Θ(1) (p.84 eq 4.9) | `Section_04_1_Multiplying_Square_Matrices.lean:132-135` (mulWork) | MINOR | Lean 用 n² 作为 forcing term (模拟块加法工作),教科书用 Θ(1) (索引计算);均给出 Θ(n³) |
| 零填充到下一幂次 | `Section_04_1_Multiplying_Square_Matrices.lean:106-123` (padOne) | MINOR | padOne 仅填充一层 (k→k+1),未覆盖教科书习题 4.1-1 的迭代填充到任意非幂次输入 |
| 运行时间 Θ(n³) (p.84) | `Section_04_1_Multiplying_Square_Matrices.lean:263-268` (mul_runtime_bigTheta) + `realLogScale_eight_two` | MATCH | 证明 Θ(n^(log₂ 8))=Θ(n³),与教科书结论一致 |

### §4.2 Strassen's Algorithm

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| 2×2 块矩阵与幂次方阵 (p.86) | `Section_04_2_Strassen_Algorithm.lean:57-58` (Matrix2), `154-156` (SqMat) | MATCH | Matrix2 为 2×2 块代数;SqMat 为递归幂次方阵;忠实编码 |
| 基例 n=1 (p.86 step 1) | `Section_04_2_Strassen_Algorithm.lean:177` (strassenRec 0) | MATCH | 深度 0 为标量乘法 |
| 7 次递归乘法 (p.86 step 3) | `Section_04_2_Strassen_Algorithm.lean:179-186` | MATCH | p1 至 p7 共 7 次递归调用 |
| 递推式 T(n)=7T(n/2)+Θ(n²) (p.87 eq 4.10) | `Section_04_2_Strassen_Algorithm.lean:265-268` (strassenWork) | MATCH | Lean 用 n²,在教科书 Θ(n²) 范围内 |
| P1-P7 乘积公式 (p.87) | `Section_04_2_Strassen_Algorithm.lean:124-132` (strassen2) | MATCH | p1-p7 与教科书 P1-P7 逐项对照,操作数顺序一致 |
| C11/C12/C21/C22 输出公式 (pp.88-89) | `Section_04_2_Strassen_Algorithm.lean:132` | MATCH | C11=p5+p4-p2+p6, C12=p1+p2, C21=p3+p4, C22=p5+p1-p3-p7 与教科书吻合 |
| 零填充 | `Section_04_2_Strassen_Algorithm.lean:220-255` (padOne) | MINOR | 与 §4.1 相同,仅填充一层 |
| 运行时间 Θ(n^(lg 7)) (p.87) | `Section_04_2_Strassen_Algorithm.lean:394-399` (strassen_runtime_bigTheta) | MATCH | 证明 Θ(n^(log₂ 7)),对应教科书 Θ(n^(lg 7)) |

### §4.3 The Substitution Method

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| 代入法两步:猜测+归纳证明 (p.90) | `Section_04_3_Substitution_Method.lean:39-46` (substitution_upper_bound) | MINOR | Lean 提供通用后继归纳模板 (T(n)→T(n+1));教科书代入法核心是将猜测代入递推方程 (涉及除法、取整、对数化简),形式化框架简化了教科书方法的核心机制。猜测启发式、"减去低阶项"技巧、避免在归纳假设中使用渐近记号等均未形式化;文档注释已声明此限制 |
| 上界归纳原理 | `Section_04_3_Substitution_Method.lean:39-46` | MATCH | 基例+归纳步推上界,与教科书方向一致 |
| 下界归纳原理 | `Section_04_3_Substitution_Method.lean:52-59` | MATCH | 对上界原理的对偶 |
| 夹逼原理 | `Section_04_3_Substitution_Method.lean:65-73` | MATCH | 同时推上下界 |
| 线性模板 | `Section_04_3_Substitution_Method.lean:81-95` | MATCH | T(n+1) ≤ T(n) + inc → T(n) ≤ base + inc·n |
| 几何模板 | `Section_04_3_Substitution_Method.lean:121-137` | MATCH | T(n+1) ≤ a·T(n) → T(n) ≤ base·a^n |

### §4.4 The Recursion-Tree Method

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| 递归树求和 (p.95) | `Section_04_4_Recursion_Tree_Method.lean:31-39` (recursion_tree_additive_unroll) | MINOR | Lean 形式化线性链 T(n+1)=T(n)+cost(n) 的展开,而非教科书的分支递归树 (如 T(n)=3T(n/4)+Θ(n²) 的三路分支树)。教科书的关键洞察——几何级数求和、根代价主导、叶子计数递推——在 Lean 中未形式化。文档注释已声明"proved for the finite-sum core" |
| 包络上界 | `Section_04_4_Recursion_Tree_Method.lean:45-50` | MATCH | 每层代价 bounded by envelope → 总和 bounded |
| 包络下界 | `Section_04_4_Recursion_Tree_Method.lean:56-61` | MATCH | 对偶 |
| 常层代价闭形 | `Section_04_4_Recursion_Tree_Method.lean:67-72` | MATCH | cost(k)=常数 → T(n)=T(0)+level·n |
| 常层上界 | `Section_04_4_Recursion_Tree_Method.lean:78-89` | MATCH | 每层代价≤level → T(n)≤base+level·n |

### §4.5 The Master Method (Exact Powers)

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| 精确幂递推结构 (p.102 eq 4.17) | `Section_04_5_Master_Theorem.lean:43-44` (ExactPowerRecurrence) | MATCH | T(b^(i+1))=a·T(b^i)+f(b^(i+1)),忠实编码 |
| h_formula 展开 (p.108 eq 4.18) | `Section_04_5_Master_Theorem.lean:63-79` (h_formula) | MATCH | T(b^i)/a^i = T(1) + Σ f(b^(k+1))/a^(k+1) |
| 情形 1: 几何 forcing (p.103 case 1) | `Section_04_5_Master_Theorem.lean:182-237` (master_case1_geometric) | MATCH | T(b^i)=Θ(a^i),对应教科书 Θ(n^(log_b a)) |
| 情形 2: 常数 forcing (p.103 case 2, k=0) | `Section_04_5_Master_Theorem.lean:243-291` (master_case2_constant_forcing) | MATCH | T(b^i)=Θ((i+1)a^i),对应 Θ(n^(log_b a) lg n) |
| 情形 2: polylog forcing (p.103 case 2, k≥0) | `Section_04_5_Master_Theorem.lean:379-438` (master_case2_polylog_forcing) | MATCH | T(b^i)=Θ((i+1)^(k+1)a^i),对应 Θ(n^(log_b a) lg^(k+1) n) |
| 情形 3: 尾支配 (p.103 case 3) | `Section_04_5_Master_Theorem.lean:445-493` (master_case3_tail_dominated) | MINOR | Lean 用 `normalizedValue T i ≤ C·normalizedForcing f (i-1)` 表述尾支配条件 (引用了 T 自身);教科书用纯关于 f 的条件 `f(n)=Ω(n^(log_b a+ε))` 且 `a f(n/b) ≤ c f(n)`。§4.6 的 `Case3Regularity` 桥接了此差异 |

### §4.6 Continuous Master Theorem + All-Input Bridge

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| 递归树工作量 (Lemma 4.2, p.108) | `Section_04_6_Continuous_Master_Theorem.lean:161-162` (continuousWork) | MINOR | Lean 的连续主定理仅处理多项式 forcing f(n)=n^p;教科书 Lemma 4.3 处理任意 f(n) 满足三个情形之一。文档注释已声明此限制,§4.5 精确幂核心通过 normalizedForcing 处理了任意 f(n) |
| 几何级数分析 (Lemma 4.3) | `Section_04_6_Continuous_Master_Theorem.lean:61-62` (geomSum) | MATCH | geomSum r k = Σ r^j,三种比率情形对应教科书分析 |
| 连续情形 1: ratio>1 | `Section_04_6_Continuous_Master_Theorem.lean:210-262` | MATCH | Θ(a^k),对应教科书情形 1 |
| 连续情形 2: ratio=1 | `Section_04_6_Continuous_Master_Theorem.lean:270-300` | MATCH | Θ(k·a^k),对应教科书情形 2 |
| 连续情形 3: ratio<1 | `Section_04_6_Continuous_Master_Theorem.lean:308-340` | MATCH | Θ(b^(p·k)),对应教科书情形 3 |
| floor/ceil 递推接口 | `Section_04_6_Master_Theorem_All_Input.lean:792-801` | MATCH | FloorDivideRecurrence/CeilDivideRecurrence 忠实编码 |
| 精确幂到全输入转移 (Theorem 4.4) | `Section_04_6_Master_Theorem_All_Input.lean:1061-1074` (allInput_bigTheta_of_powerStep) | MATCH | 通过相邻幂夹逼转移 Θ 界 |
| 实对数尺度桥接 | `Section_04_6_Master_Theorem_All_Input.lean:487-628` (criticalPowerScale_isBigTheta_realLogScale) | MATCH | a^(⌊log_b n⌋) = Θ(n^(log_b a)),桥接离散与连续尺度 |
| Case3Regularity 桥接 | `Section_04_6_Master_Theorem_All_Input.lean:1647-1648` + `tailDominatedScale_isBigTheta_f_of_regularity` | MATCH | 将 Lean 的尾支配表述桥接到教科书正则条件 |

### §4.7 Akra-Bazzi Recurrences

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| 分支参数 a_i, b_i (p.115) | `Section_04_7_Akra_Bazzi.lean:122-126` (AkraBazziBranch) | MINOR | Lean 限制 a_i:ℕ,教科书允许 a_i∈ℝ 且严格正;实际算法中 a_i 为自然数,不影响渐近结论 |
| 根方程 Σ a_i/b_i^p=1 (p.117) | `Section_04_7_Akra_Bazzi.lean:144-153` (IsAkraBazziRoot) | MATCH | 忠实编码 |
| 单分支根 p=log_b a | `Section_04_7_Akra_Bazzi.lean:180-185` (akraBazziRoot_single) | MATCH | 恢复主定理指数 |
| 两分支实例 p=1 | `Section_04_7_Akra_Bazzi.lean:223-226` (akraBazziRoot_two_thirds_one) | MATCH | T(n)=T(n/3)+T(2n/3),根 p=1,与教科书吻合 |
| 多分支根唯一性 | `Section_04_7_Akra_Bazzi.lean:302-312` (akraBazziRoot_unique) | MATCH | charFun 严格递减 ⇒ 根唯一 |
| 根非负性 | `Section_04_7_Akra_Bazzi.lean:319-340` (akraBazziRoot_nonneg) | MATCH | charFun 0 ≥ 1 且递减 ⇒ p ≥ 0 |
| 尺度不变性 Σ a_i(n/b_i)^p=n^p | `Section_04_7_Akra_Bazzi.lean:350-365` (akraBazzi_root_scale_invariance) | MATCH | 多分支推广,教科书基础性质 |
| 积分渐近形 (eq 4.23, p.117) | `Section_04_7_Akra_Bazzi.lean:373-381` (akraBazziIntegral/akraBazziScale) | MINOR | Lean 用离散和 Σ g(u)/u^(p+1),教科书用连续积分 ∫ g(x)/x^(p+1) dx;多项式增长条件下渐近等价 |
| 多项式增长条件 (p.116) | `Section_04_7_Akra_Bazzi.lean:400-405` (PolynomialGrowth) | MATCH | c n^q ≤ g n ≤ C n^q 且单调非负,对应教科书条件 |
| 递推定义 (含 floor) | `Section_04_7_Akra_Bazzi.lean:414-418` (SatisfiesAkraBazzi) | MATCH | 含 ⌊n/b_i⌋ 的 floor 扰动,显式基例 |
| 上界 T(n)=O(n^p(1+I n)) | `Section_04_7_Akra_Bazzi.lean:1035-1184` (akraBazzi_upper_bound) | MATCH | 对任意 p>0,q≥0 成立 |
| 下界 (forcing-dominated, p+1≤q) | `Section_04_7_Akra_Bazzi.lean:1464-1509` (akraBazzi_lower_bound) | MATCH | T(n)=Ω(n^p(1+I n)) |
| 下界 (critical, q=p) | `Section_04_7_Akra_Bazzi.lean:1552-1770` (akraBazzi_lower_bound_critical) | MATCH | 通过 floor 损失吸收完成 |
| 下界 (leaf-dominated, q<p) | `Section_04_7_Akra_Bazzi.lean:2020-2188` (akraBazzi_lower_bound_leaf) | MATCH | 通过平滑函数 ε(x)=1/√x 完成 |
| 完整 Θ 界 (forcing-dominated) | `Section_04_7_Akra_Bazzi.lean:1776-1783` (akraBazzi_bigTheta) | MATCH | p+1≤q 时 Θ(n^p(1+I n)) |
| 完整 Θ 界 (leaf-dominated) | `Section_04_7_Akra_Bazzi.lean:2196-2203` (akraBazzi_bigTheta_leaf) | MATCH | 0≤q<p 时 Θ(n^p(1+I n)) |
| 平滑函数 (leaf 下界辅助) | `Section_04_7_Akra_Bazzi.lean:1794` (akraBazziSmoothingFn) | MINOR | ε(x)=1/√x 是 leaf 下界证明的具体构造,不是教科书多项式增长条件或 Theorem 4.5 的形式化;是一种证明技巧而非教科书概念的直接翻译 |

## 缺陷清单

### MINOR 缺陷

1. **§4.1 输出模型**: Lean 返回纯乘积 A*B,教科书为累加 C=C+A·B。等价于 C 初始化为零(教科书本身指出此做法)。建议:无需修改。

2. **§4.1 递推式 forcing term**: Lean 用 n²,教科书用 Θ(1)。n² 建模块加法工作,Θ(1) 建模索引计算。均给出 Θ(n³)。建议:在文档注释中说明两种成本模型的等价性。

3. **§4.1/§4.2 零填充**: padOne 仅填充一层 (k→k+1),未覆盖教科书习题 4.1-1 要求的迭代填充到任意非幂次输入。建议:添加迭代填充函数或声明此限制。

4. **§4.3 框架简化**: Lean 提供后继归纳模板 (T(n)→T(n+1)),教科书代入法涉及将猜测代入递推方程 (含除法、取整、对数化简)。猜测启发式、"减去低阶项"技巧等未形式化。建议:文档注释已声明此限制,无需修改。

5. **§4.4 框架简化**: Lean 形式化线性链 T(n+1)=T(n)+cost(n) 的展开,教科书处理分支递归树 (如 T(n)=3T(n/4)+Θ(n²))。几何级数求和、根代价主导等未形式化。建议:文档注释已声明此限制,无需修改。

6. **§4.5 情形 3 表述**: Lean 用 `normalizedValue T i ≤ C·normalizedForcing f (i-1)` (引用 T 自身),教科书用纯关于 f 的条件。§4.6 的 Case3Regularity 桥接了此差异。建议:无需修改。

7. **§4.6 多项式 forcing 限制**: 连续主定理仅处理 f(n)=n^p,教科书 Lemma 4.3 处理任意 f(n)。§4.5 精确幂核心通过 normalizedForcing 处理了任意 f(n)。建议:文档注释已声明此限制,无需修改。

8. **§4.7 a_i 类型限制**: Lean 限制 a_i:ℕ,教科书允许 a_i∈ℝ 且严格正。实际算法中 a_i 为自然数(子问题个数),不影响渐近结论。建议:无需修改。

9. **§4.7 离散和 vs 连续积分**: Lean 用离散和 Σ g(u)/u^(p+1),教科书用连续积分 ∫ g(x)/x^(p+1) dx。多项式增长条件下渐近等价。建议:无需修改。

10. **§4.7 平滑函数**: ε(x)=1/√x 是 leaf 下界证明的具体构造,不是教科书多项式增长条件或 Theorem 4.5 的形式化。建议:无需修改。

11. **§4.7 显式基例**: Lean 的 SatisfiesAkraBazzi 指定 T(0)=0, T(n)=1 for 1≤n≤n₀;教科书使用算法递推约定(基例隐式)。建议:无需修改。

12. **§4.4 示例未实例化**: 教科书两个详细示例 (T(n)=3T(n/4)+cn² 和 T(n)=T(n/3)+T(2n/3)+cn) 未在 Lean 中实例化。建议:可选添加。

13. **§4.7 总 Θ 界缺口**: 临界体制 (q=p) 仅有下界 `akraBazzi_lower_bound_critical`,上界由 `akraBazzi_upper_bound` 覆盖,但未打包为单个 `akraBazzi_bigTheta_critical` 定理。建议:添加打包定理。

## 反驳记录

反驳员复核了全部 62 条审计员判定的 MATCH 条目,提出 11 条差异。经合并评估:

- **反驳成立的差异 (5 条,降级为 MINOR)**:
  - §4.3 框架简化 (后继归纳 vs 代入法核心机制)
  - §4.4 框架简化 (线性链 vs 分支递归树)
  - §4.5 情形 3 循环表述 (引用 T 自身 vs 纯关于 f 的条件)
  - §4.6 多项式 forcing 限制 (仅 f(n)=n^p vs 任意 f(n))
  - §4.7 a_i 类型限制 (ℕ vs ℝ)

- **反驳员提出但审计员已捕获的差异 (6 条,不改变判定)**:
  - §4.1 forcing term n² vs Θ(1) — 审计员已判为 MINOR
  - §4.1/§4.2 padOne 单层 — 审计员已隐含在相关条目中
  - §4.7 离散和 vs 连续积分 — 审计员已在相关条目中捕获
  - §4.7 平滑函数 — 审计员已在相关条目中捕获

- **最终降级数**: 5 条 MATCH → MINOR

审计员与反驳员对 MAJOR/CRITICAL 级别的判定一致: 无 MAJOR 或 CRITICAL 缺陷。反驳员提出的四项"MAJOR"主张经评估均不满足 MAJOR 标准: 每一项要么是文档注释已声明的已知简化,要么是渐近等价的不同表述,均不改变章节的主要数学结论。

## 后续闭合记录（2026-08-27）

本节保留上面的 2026-08-18 审计快照，不回写其历史计数。

| 原审计项 | 当前状态 | 可验收证据 |
|----------|----------|------------|
| §4.4 框架简化 / 缺陷 5 | 已解决（固定深度精确尺度） | `BranchingRecursionTree` 明确保存每个内部节点的所有分支；`totalCost_eq_levelCosts_add_leafCost` 证明总成本等于内部逐层成本加叶成本；`scaledBranchingTree_levelCost` 给出一般分支比例的精确层成本 |
| §4.4 示例未实例化 / 缺陷 12 | 已解决（固定深度精确尺度） | `balancedThreeQuarter_totalCost_le` 形式化 `3T(n/4)+cn²` 的 `3/16` 几何层成本；`unbalancedThirdTwoThird_totalCost` 保留不同的 `1/3`、`2/3` 分支并证明每层成本为 `cn` |
| §4.7 临界 Θ 打包 / 缺陷 13 | 已解决 | `akraBazzi_bigTheta_critical` |

上述 §4.4 结论没有把精确尺度结果误写成任意自然数输入结论：它们假设实数
比例、共同展开深度和显式叶成本。带 floor/ceiling 的不同终止深度仍由单独的
全输入转移或 Akra–Bazzi 框架处理。
