# Ch5 Probabilistic Analysis and Randomized Algorithms 语义忠实性审计

- 审计日期（北京时间）：2026-08-18
- skill 版本：semantic-fidelity-audit v1
- 基准来源：参考第 5.1–5.4 节
- 结论分布：MATCH 21 · MINOR 15 · MAJOR 1 · CRITICAL 0 · UNCERTAIN 1
- 结构前提：check_book_coverage.py 通过

## 断言对照表

### §5.1 The Hiring Problem

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| 候选人随机顺序假设（均匀随机排列） | §5.1 文档 | MATCH | 使用 `Equiv.Perm (Fin n)` 均匀分布，与书一致 |
| HIRE-ASSISTANT 伪代码 | §5.1:204 `hireAssistant` | MINOR | 仅返回录用次数（左到右极大值计数），不跟踪最佳候选人身份；书中伪代码维护 `best` 变量并执行录用操作。概率分析等价 |
| 录用概率 = 1/(i+1)（第 i+1 步） | §5.1:86 `hireProbability_eq` | MATCH | 零索引：`hireProbability n = 1/(n+1)`，对应书中第 n+1 个候选人概率 1/(n+1) |
| 期望录用次数 = H_n | §5.1:123 `expectedHiresByIndicators_eq_harmonic` | MATCH | 通过对指标期望求和得到调和数 |
| 期望录用次数递推解 = H_n | §5.1:139 `expectedHires_eq_harmonic` | MATCH | 递推定义与调和数闭式等价 |
| 期望录用次数 = Θ(log n) | §5.1:177 `expectedHires_isBigTheta_log` | MATCH | 比书中的 O(ln n) 更强（Θ 双向界） |
| Lemma 5.2（平均情况录用成本） | §5.1:177（隐含） | MINOR | 书中陈述成本 O(c_h ln n)，Lean 证明期望录用次数 Θ(log n)，未显式乘 c_h |
| 录用问题指标分析（式 5.3–5.6） | §5.1:123（已覆盖） | MATCH | 已在 §5.1 中通过 `expectedHiresByIndicators_eq_harmonic` 完成 |

### §5.2 Indicator Random Variables

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| 指标随机变量定义 I{A}（式 5.1） | 概率工具包 `CLRS.Probability.indicator` | MATCH | 共享工具包中定义，语义一致。ℝ 值指标与书的 {0,1} 整数指标在期望计算中等价 |
| Lemma 5.1（E[X_A] = Pr{A}） | 概率工具包（非显式命名） | MINOR | 书中 Lemma 5.1 在 Ch5 源文件中无对应的显式命名定理；结论隐含在 `fintypeExpect_indicator_singleton` 等基元中 |
| 固定点概率 = 1/n | §5.2:112 `probFixesPoint` | MATCH | 均匀随机排列固定给定点的概率恰为 1/n。群作用对称性论证与书一致 |
| 帽检问题：期望不动点数 = 1 | §5.2:166 `expectedFixedPoints_eq_one` | MATCH | 对 n≥1，期望不动点数恒为 1，n·(1/n) = 1 |
| 书中硬币抛掷示例 | 未形式化 | MINOR | 书中用硬币抛掷作为指标变量入门示例，Lean 直接跳到帽检问题；数学实质无损 |

### §5.3 Randomized Algorithms

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| RANDOMLY-PERMUTE 伪代码 | §5.3:77 `randomizeInPlace` | MINOR | 使用非构造性基数双射（`Fintype.equivFin`），非 Fisher-Yates 具体算法；循环不变式证明被绕过。输出分布均匀性成立 |
| Lemma 5.4（RANDOMLY-PERMUTE 产生均匀随机排列） | §5.3:86 `randomizeInPlace_uniform` | **MAJOR** | **引理编号错误**：第 4 版仅有 Lemma 5.1–5.4，Lean 代码多处标注为 "Lemma 5.5"（§5.3:7, :14, :81；Chapter_05.lean:35, :55；§5.1:37）。不存在 Lemma 5.5 |
| Lemma 5.4 循环不变量证明 | §5.3:63–78（双射论证） | MINOR | 书中用循环不变量详细证明，Lean 用双射论证，证明技术不同但结论一致 |
| RANDOMIZED-HIRE-ASSISTANT 组合函数 | 未实现 | MINOR | 组成部件 `randomizeInPlace` 和 `hireAssistant` 都存在，但未提供组合函数 |
| Lemma 5.3（RANDOMIZED-HIRE-ASSISTANT 期望成本） | 未显式形式化 | MINOR | 可由 §5.1 的 Θ(log n) 与均匀排列引理推出，但未作为独立定理陈述 |
| PERMUTE-WITHOUT-IDENTITY 等练习 | 未形式化 | MINOR | 练习 5.3-2 至 5.3-5 未形式化；属练习范围 |

### §5.4 Probabilistic Analysis

#### §5.4.1 Birthday Paradox

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| 两人同生日概率 = 1/n（式 5.7） | §5.4:161 `pairSameProb` | MATCH | 乘积分解证明独立性，与书一致 |
| 期望同生日对数量 = k(k-1)/(2n)（式 5.8） | §5.4:237 `expectedCollisions_eq` | MATCH | C(k,2)/n，通过指标变量和线性期望 |
| 互补事件概率分析（Pr{B_k} ≤ 1/2 当 k ≥ 23） | 未形式化 | MINOR | 书中用概率直接分析得到 k≥23 时匹配概率 ≥1/2；Lean 仅形式化了指标变量版本的期望分析 |

#### §5.4.2 Balls and Bins

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| 给定箱子中期望球数 = k/n | §5.4:283 `expectedBallsInBin_eq` | MATCH | 期望球数恰为 k/n（参数命名：Lean k 球/n 箱，书 n 球/b 箱） |
| 单球落入给定箱概率 = 1/n | §5.4:106 `singleBinProb` | MATCH | 基础概率 |
| 几何分布与优惠券收集问题 | 未形式化 | MINOR | 书中 §5.4.2 讨论的几何分布期望和 b ln b 调和级数未形式化 |

#### §5.4.3 Streaks

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| 长度为 k 的连续正面概率 = 1/2^k（式 5.9） | §5.4:423 `prob_run_at` | MATCH | t 个连续正面的概率 = 1/2^t |
| 最长连续正面期望上界 E[L] = O(lg n) | §5.4:777 `expectedLongestStreak_le` | MATCH | 具体界：E[L] ≤ log₂ n + 2，比书中 O(lg n) 更强（书中常数 ≈ 2，Lean 常数 ≈ 1） |
| 最长连续正面期望下界 E[L] = Ω(lg n) | §5.4:1318 `expectedLongestStreak_lowerBound` | MATCH | 具体界：E[L] ≥ log₂ n / 8（n ≥ 16），与书渐近下界一致 |
| 尾界 Pr[L ≥ t] ≤ n/2^t | §5.4:626 `longestStreak_upperBound` | MATCH | Union Bound 论证 |
| 层饼恒等式（tail-sum formula） | §5.4:756 `expectedLongestStreak_eq_tailSum` | MATCH | E[L] = Σ_{t≥1} Pr[L ≥ t] |
| 块划分下界 | §5.4:1172 `prob_noFullHeadBlock` 等 | MATCH | 精确计数 (2^k-1)^m·2^(n-mk)，比书的 O(1/n) 更强 |
| 指标变量近似分析（E[X_k] = (n-k+1)/2^k） | 未形式化 | MINOR | 书中 §5.4.3 末尾的指标变量近似方法未形式化 |
| r⌈lg n⌉ 长度连续正面的概率界 | 未形式化 | MINOR | 书中 n^(1-r) 概率界未形式化 |

#### §5.4.4 Online Hiring

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| ONLINEMAXIMUM 伪代码 | OnlineHiring:68 `hiringStrategy` | MINOR | 书中始终录用某人（第 n 人为后备），Lean 返回 `Option (Fin n)`，无可录用记录时返回 `none`。成功概率公式不受影响 |
| 成功概率闭式 | OnlineHiring:847 `probHireBest_eq` | MINOR | 闭式 (k/n)(H_{n-1} - H_{k-1}) 与书一致，但底层 `hiringStrategy` 的操作语义不同（`Option` vs 始终录用） |
| 下界与上界积分近似 | 未显式形式化 | MINOR | 书中用积分近似给出上下界，Lean 直接证明闭式再取极限 |
| 最优阈值 k = n/e 时成功概率 → 1/e | OnlineHiring:1166 `probHireBest_asymptotic` | MATCH | 证明极限精确等于 1/e（比书的下界 ≥1/e 更强），通过 Euler-Mascheroni 渐近分析 |
| 最优阈值导数推导 | 未形式化 | MINOR | 书中通过对 (k/n)(ln n - ln k) 求导得到 k = n/e 最优；Lean 直接证明渐近结果 |
| 得分模型方向 | OnlineHiring:36–37 | MINOR | 书中 score 越高越好，Lean 用 0=最优（值越小越好），数学等价 |

## 缺陷清单

### MAJOR 缺陷

**M1. 引理编号错误：Lemma 5.4 被标注为 Lemma 5.5**
- 严重度：MAJOR
- 位置：`Section_05_3_Randomized_Algorithms.lean:7, :14, :81`；`Chapter_05.lean:35, :55`；`Section_05_1_Hiring_Problem.lean:37`
- 差异描述：CLRS 第 4 版第 5 章仅有四条引理（Lemma 5.1 至 5.4）。Lemma 5.4 是「Procedure RANDOMLY-PERMUTE computes a uniform random permutation」。Lean 代码在多处将同一引理标注为 "Lemma 5.5"。第 4 版中不存在 Lemma 5.5。
- 建议修法：将所有 "Lemma 5.5" 改为 "Lemma 5.4"，涉及文件：`Section_05_3_Randomized_Algorithms.lean`（模块文档注释第 7 行、第 14 行，`randomizeInPlace_uniform` 的 doc 注释第 81 行）、`Chapter_05.lean`（第 35 行、第 55 行）、`Section_05_1_Hiring_Problem.lean`（第 37 行模块文档注释）。
- issue 草稿：
  ```
  title: fix(ch05): Lemma 5.4 mislabeled as Lemma 5.5 in 6 locations
  body: |
    CLRS 4th edition Chapter 5 has Lemmas 5.1–5.4 only.  The Fisher-Yates
    shuffle proof is Lemma 5.4, not 5.5.  Six doc-comment / module-doc
    references need `s/Lemma 5.5/Lemma 5.4/`.
    
    Files:
    - CLRSLean/FourthEdition/Chapter_05/Section_05_3_Randomized_Algorithms.lean
      (lines 7, 14, 81 in module doc and theorem doc)
    - CLRSLean/FourthEdition/Chapter_05.lean (lines 35, 55)
    - CLRSLean/FourthEdition/Chapter_05/Section_05_1_Hiring_Problem.lean (line 37)
  ```

### MINOR 缺陷

**m1. Lemma 5.1 无显式命名定理**
- 严重度：MINOR
- 位置：`Section_05_2_Indicator_Random_Variables.lean`（缺失）
- 差异描述：书中 Lemma 5.1（E[X_A] = Pr{A}）在 Ch5 源文件中无对应的显式命名定理。结论依赖于概率工具包。
- 建议修法：在 §5.2 中添加 `lemma indicator_expectation_eq_prob` 并标注对应 Lemma 5.1。

**m2. Lemma 5.2 未作为独立命名定理陈述**
- 严重度：MINOR
- 位置：`Section_05_1_Hiring_Problem.lean`
- 差异描述：书中 Lemma 5.2 陈述「平均情况录用总成本 O(c_h ln n)」。Lean 未显式乘录用成本常数 c_h 形成完整成本陈述。
- 建议修法：添加定理 `expectedHiringCost_isBigO` 将 `expectedHires` 乘以常数 c_h。

**m3. Lemma 5.3 未显式形式化**
- 严重度：MINOR
- 位置：`Section_05_3_Randomized_Algorithms.lean`（缺失）
- 差异描述：书中 Lemma 5.3（RANDOMIZED-HIRE-ASSISTANT 期望成本 O(c_h ln n)）无对应 Lean 定理。
- 建议修法：添加 `lemma randomizedHireAssistant_expectedCost_isBigO`。

**m4. RANDOMIZED-HIRE-ASSISTANT 组合函数缺失**
- 严重度：MINOR
- 位置：`Section_05_3_Randomized_Algorithms.lean`
- 差异描述：`randomizeInPlace` 和 `hireAssistant` 两个部件都存在，但未提供组合函数。
- 建议修法：添加 `def randomizedHireAssistant (ranks : List ℕ) : ℕ`。

**m5. Lemma 5.4 证明技术差异**
- 严重度：MINOR
- 位置：`Section_05_3_Randomized_Algorithms.lean:63–78`
- 差异描述：书中用循环不变量详细证明，Lean 使用非构造性基数双射。结论一致但未复现循环不变量推理。
- 建议修法：在模块文档中注明「证明技术采用双射论证而非书中的循环不变量」。

**m6. 生日悖论互补事件概率分析缺失**
- 严重度：MINOR
- 位置：`Section_05_4_Probabilistic_Analysis.lean`
- 差异描述：书中 §5.4.1 有两套分析，Lean 仅形式化了指标变量版本。
- 建议修法：添加 `lemma prob_all_distinct_le_half` 证明当 k ≥ 23 且 n = 365 时的概率界。

**m7. 球与箱：几何分布与优惠券收集问题缺失**
- 严重度：MINOR
- 位置：`Section_05_4_Probabilistic_Analysis.lean`
- 差异描述：书中 §5.4.2 的几何分布期望和优惠券收集问题未形式化。
- 建议修法：添加 `expectedTossesUntilBin` 和 `expectedCouponCollector` 定理。

**m8. 连续正面指标变量近似分析缺失**
- 严重度：MINOR
- 位置：`Section_05_4_Probabilistic_Analysis.lean`
- 差异描述：书中 §5.4.3 末尾的 E[X_k] = (n - k + 1)/2^k 近似分析未形式化。
- 建议修法：添加 `expectedNumStreaks_ge_k` 定理。

**m9. ONLINEMAXIMUM 返回值类型差异**
- 严重度：MINOR
- 位置：`OnlineHiring.lean:68`
- 差异描述：书中总是返回一个整数索引（最后一人为后备）；Lean 返回 `Option (Fin n)`。
- 建议修法：当前设计已足够，可在模块文档中注明此差异。

**m10. 在线录用得分方向约定相反**
- 严重度：MINOR
- 位置：`OnlineHiring.lean:36–37`
- 差异描述：书中 score 越高越好，Lean 用 0=最优。数学等价但不直观。
- 建议修法：在模块文档中注明「得分越低表示越好（0 = 最优）」。

**m11. 在线录用最优阈值导数推导缺失**
- 严重度：MINOR
- 位置：`OnlineHiring.lean`
- 差异描述：书中通过求导得到 k = n/e 最优，Lean 直接证明渐近结果。
- 建议修法：添加 `lemma optimalThreshold_derivative`。

**m12. 录用成本常数 c_h 未显式建模**
- 严重度：MINOR
- 位置：`Section_05_1_Hiring_Problem.lean`
- 差异描述：书中区分面试成本 c_i 和录用成本 c_h，Lean 仅计数录用次数。
- 建议修法：在模块文档中注明「当前模型仅计数录用次数，成本常数乘法因子为直截了当的扩展」。

**m13. HIRE-ASSISTANT 仅计数录用次数（反驳员发现）**
- 严重度：MINOR
- 位置：`Section_05_1_Hiring_Problem.lean:204–206`
- 差异描述：`hireAssistant` 仅返回左到右极大值的计数，不跟踪被录用候选人身份。书中伪代码维护 `best` 变量并执行录用操作。
- 建议修法：概率分析等价，可在模块文档中注明此简化。

**m14. RANDOMLY-PERMUTE 使用非构造性双射（反驳员发现）**
- 严重度：MINOR
- 位置：`Section_05_3_Randomized_Algorithms.lean:63–71`
- 差异描述：`randomizeInPlace_equiv` 使用 `Fintype.equivFin`（基数双射），未指定具体是哪个双射。书中 Fisher-Yates 算法的具体步骤和循环不变式被完全绕过。
- 建议修法：在模块文档中注明「证明技术采用基数双射，非 Fisher-Yates 构造性算法」。

**m15. 在线录用策略操作语义差异（反驳员发现）**
- 严重度：MINOR
- 位置：`OnlineHiring.lean:68–71`
- 差异描述：`hiringStrategy` 返回 `Option`（可失败），书 ON-LINE-MAXIMUM 始终录用第 n 人为回退。成功概率公式相同，但算法行为语义有实质差异。
- 建议修法：在模块文档中注明此差异。

## 反驳记录

反驳员复核了审计员判定的 25 条 MATCH 条目。提出 3 条独立差异，均使相关 MATCH 条目降级为 MINOR：

| 条目 | 反驳要点 | 降级 |
|------|---------|------|
| A2（HIRE-ASSISTANT 伪代码） | `hireAssistant` 仅返回录用次数，不跟踪最佳候选人身份 | MATCH → MINOR |
| A11/A12（RANDOMLY-PERMUTE） | 使用非构造性基数双射，非 Fisher-Yates 算法 | MATCH → MINOR |
| A24（成功概率闭式） | `hiringStrategy` 返回 `Option`，书始终录用某人 | MATCH → MINOR |

反驳员另发现 2 条增强（非漂移）：A19（上界 log₂ n + 2 比书紧一倍）和 A25（极限精确等于 1/e，比书的下界 ≥1/e 更强），均保留 MATCH。

最终降级数：3 条。反驳员确认其余 20 条 MATCH 经多维度检查无语义漂移。

## UNCERTAIN 条目

**U1. 第 4 版与第 3 版第 5 章的引理编号差异**
- 阻塞原因：对照语料为第 4 版文本，第 5 章仅有 Lemmas 5.1–5.4。如果历史上第 3 版或某些印刷版本有 Lemma 5.5，则 M1 可能不是缺陷。建议双重确认目标版本。

## 后续闭合记录（2026-08-27）

本节保留上面的 2026-08-18 审计快照，不回写其历史计数；下表记录此后已验收的修复。

| 原审计项 | 当前状态 | 可验收证据 |
|----------|----------|------------|
| M1：Lemma 5.4 编号 | 已解决 | 第四版公开接口统一标为 Lemma 5.4 |
| m1：指标期望接口 | 已解决 | `indicator_expectation_eq_probability` |
| m2 / m12：录用成本常数 | 已解决 | `expectedHiringCost_eq_harmonic`、`expectedHiringCost_isBigO_log` |
| m3：随机化录用成本 | 部分解决 | `randomizedExpectedHiringCost_eq_uniform` 已把具体执行传输到均匀排列空间；最后的记录数期望桥由 `HiringExpectationBridge` 明示并在 issue #332 跟踪 |
| m4：RANDOMIZED-HIRE-ASSISTANT | 已解决 | `randomizedHireAssistant` |
| m5 / m14：非构造双射与循环不变量 | 已解决 | `fisherYates` 是可执行的函数式 Fisher–Yates；`fisherYates_succ_invariant` 给出逐层一步交换不变量，`fisherYates_first_uniform` 给出当前选择均匀性，`fisherYates_uniform` 给出最终排列均匀性 |

这里的“可执行”指递归的函数式算法：每层把均匀选中的元素放到当前
位置，再在剩余后缀上递归。它与教材的原地数组循环具有同样的一步交换
结构和随机选择空间，但没有额外引入可变数组状态。
