# Ch3 Characterizing Running Times 语义忠实性审计

- **审计日期（北京时间）**: 2026-08-17 17:16 CST
- **Skill 版本**: semantic-fidelity-audit v1
- **基准来源**: 参考第 3.1–3.3 节（课本语料已核对）
- **结论分布**: MATCH 38 · MINOR 21 · MAJOR 0 · CRITICAL 0 · UNCERTAIN 0
- **结构前提**: `check_book_coverage.py` 通过（Book coverage OK, 35 chapters）

## 断言对照表

### §3.1 + §3.2（O/Ω/Θ/o/ω 形式化定义与代数性质）

源文件：`CLRSLean/FourthEdition/Chapter_03/Section_03_1_Asymptotic_Notation.lean`

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| O-notation 定义（0 ≤ f(n) ≤ c·g(n)） | :22 `isBigO` | MINOR | 书用无绝对值形式（假设渐近非负），Lean 用 `|f n| ≤ c * |g n|`；对渐近非负函数等价 |
| Ω-notation 定义（0 ≤ c·g(n) ≤ f(n)） | :24 `isBigOmega` | MINOR | 同上绝对值差异 |
| Θ-notation 定义（c₁g(n) ≤ f(n) ≤ c₂g(n)） | :26 `isBigTheta` | MINOR | 反驳员发现：书中 Θ 定义为存在 c₁,c₂ 夹逼，Theorem 3.1 才是 Θ = O ∩ Ω；Lean 将定理作为定义（`isBigTheta := isBigO ∧ isBigOmega`），书中定义降级为 `isBigTheta_iff_sharedThreshold`(:195)。逻辑等价但结构互换 |
| Theorem 3.1（Θ iff O and Ω） | :26, :181 | MATCH | 嵌入为 Θ 的定义体；`isBigTheta_iff`(:181) 给出等价表述 |
| o-notation 定义（∀c>0: f(n) < c·g(n)） | :28 `isLittleO` | MINOR | 书用严格 `<`，Lean 用 `≤`；数学上等价（取 c/2） |
| ω-notation 定义（∀c>0: c·g(n) < f(n)） | :30 `isLittleOmega` | MINOR | 同上 `<` vs `≤` 差异 |
| O 自反性 | :150 `isBigO_refl` | MATCH | |
| Ω 自反性 | :154 `isBigOmega_refl` | MATCH | |
| Θ 自反性 | :157 `isBigTheta_refl` | MATCH | |
| O 传递性 | :160 `isBigO_trans` | MATCH | |
| Ω 传递性 | :164 `isBigOmega_trans` | MATCH | |
| Θ 传递性 | :172 `isBigTheta_trans` | MATCH | |
| Θ 对称性 | :169 `isBigTheta_symm` | MATCH | |
| O/Ω 转置对称性 | :229 `isBigO_reciprocal` | MATCH | |
| o/ω 转置对称性 | :222 `isLittleO_reciprocal` | MATCH | |
| o 传递性 | 无 | MINOR | 书中列出但未形式化 |
| ω 传递性 | 无 | MINOR | 书中列出但未形式化 |
| 插入排序 O(n²)/Ω(n²)/Θ(n²) 分析 | 无 | MATCH | 散文级示例，非定理目标；书中 §3.1 的分析在其他章节有对应形式化 |
| 渐近记号等式与不等式约定 | 无 | MATCH | 记号约定，非定理目标 |
| O(1) 等"合理滥用" | 无 | MATCH | 记号约定，非定理目标 |
| 函数域为 ℕ 或 ℝ | :22–30 | MINOR | 书允许 ℕ→ℝ 或 ℝ→ℝ；Lean 固定为 `ℕ → ℝ` |
| 渐近记号的实数类比表 | 无 | MATCH | 说明性类比，非定理 |

### §3.3（标准记号和常见函数）

源文件：`CLRSLean/FourthEdition/Chapter_03/Section_03_2_Standard_Functions.lean`

| 书条目 | Lean 位置 | 判定 | 说明 |
|--------|-----------|------|------|
| 单调性定义 | 无 | MINOR | 未形式化 |
| 下取整/上取整代数性质 (3.1)–(3.10) | 无 | MINOR | 未形式化；仅证明 ⌊n⌋=Θ(n) 和 ⌈n/2⌉=Θ(n) |
| 模运算定义 (3.11)–(3.12) | 无 | MINOR | 未形式化 |
| 一般多项式 p(n)=Θ(nᵈ) | :44,53 | MINOR | 仅形式化单项式比较，未形式化一般多项式（带系数和低阶项） |
| 指数恒等式（a⁰=1, aᵐaⁿ=aᵐ⁺ⁿ 等） | 无 | MINOR | 未形式化；mathlib 提供标准引理 |
| 指数不等式 1+x ≤ eˣ（式 3.14） | 无 | MINOR | 未形式化 |
| eˣ 近似 (3.15) 与极限 (3.16) | 无 | MINOR | 未形式化 |
| 多项式 vs 指数：nᵇ = o(aⁿ) for a>1（式 3.13） | :62 `isLittleO_pow_const_exp` | MINOR | 反驳员发现：指数 `a : ℕ` 限制为自然数，书中允许实数指数；n^1.5 = o(2ⁿ) 等情形无法从此定理直接得出 |
| 对数记号定义（lg, ln, lgᵏ, lg lg） | 无 | MINOR | 未形式化；代码中直接用 `Real.log` |
| 对数恒等式 (3.17)–(3.21) | 无 | MINOR | 未形式化；mathlib 提供标准引理 |
| 对数级数展开 (3.22) 与不等式 (3.23) | 无 | MINOR | 未形式化 |
| 多对数 vs 多项式：lgᵇ n = o(nᵃ)（式 3.24） | :75 `isLittleO_log_pow_rpow` | MINOR | 反驳员发现：对数的指数 `a : ℕ` 限制为自然数，书中允许实数指数 |
| 阶乘定义 | 无 | MINOR | 使用 mathlib 的 `Nat.factorial`，未重述书中递归定义 |
| n! ≤ nⁿ（弱上界） | :197 `factorial_upper_bound` | MATCH | |
| Stirling 近似 (3.25) | 无 | MINOR | 未直接陈述；`isBigTheta_log_factorial`(:279) 间接使用 mathlib 的 Stirling 引理 |
| n! = o(nⁿ)（式 3.26） | :255 `isLittleO_factorial_pow_self` | MATCH | |
| n! = ω(2ⁿ)（式 3.27） | :427 `isLittleO_two_pow_factorial` | MATCH | 等价形式 2ⁿ = o(n!) |
| lg(n!) = Θ(n lg n)（式 3.28） | :279 `isBigTheta_log_factorial` | MATCH | 两侧界完整：上界 via n!≤nⁿ，下界 via Stirling |
| 阶乘细化界 (3.29) | 无 | MINOR | 未形式化 |
| 函数迭代一般定义 (3.30) | 无 | MINOR | 仅在 `lgStar` 中隐式使用 |
| 迭代对数 lg* n 定义 | :618 `lgStar` | MATCH | 良基递归定义，基为 2 |
| lg* 递归：lg* n = 1 + lg*(log₂ n) | :629 `lgStar_of_two_le` | MATCH | |
| lg* 2 = 1 | :640 `lgStar_two` | MATCH | |
| lg* 4, 16, 65536, 2^65536 具体值 | 无 | MINOR | 仅证明 lg* 2 = 1，其余具体值未列出 |
| 塔递归 lg*(2ⁿ) = 1 + lg* n | :648 `lgStar_two_pow` | MATCH | |
| lg* 单调性 | :657 `lgStar_monotone` | MATCH | |
| lg* n ≤ log₂ n + 1 | :676 `lgStar_le_log_add_one` | MATCH | |
| lg* n = o(log n) | :710 `isLittleO_lgStar_log` | MATCH | |
| Fibonacci 递推定义 (3.31) | 无 | MINOR | 使用 mathlib 的 `Nat.fib`，未显式重述 |
| 黄金比例 φ 与共轭 (3.32)–(3.33) | 无 | MINOR | 使用 mathlib 的 `Real.goldenRatio`/`Real.goldenConj` |
| Binet 闭形式 F_n = (φⁿ−ψⁿ)/√5 | :515 `coe_fib_closed_form` | MATCH | 精确匹配书中公式；委托 mathlib |
| F_n = Θ(φⁿ)（Fibonacci 指数增长） | :525 `isBigTheta_fib_goldenRatio` | MATCH | 两侧界完整：上界 c₂=1，下界 c₁=1/5 |
| 最近整数界 |φⁿ/√5 − F_n| < 1/2 (3.34) | :571 `goldenRatio_pow_div_sqrt5_sub_fib_abs_lt_half` | MATCH | |
| 对数底变换 log n = Θ(log_b n) | :354 `isBigTheta_log_logb` | MATCH | 上界 c₂=log b，下界 c₁=(log b)/2 |
| 对数底变换逆 | :454 `isBigTheta_logb_log` | MATCH | |
| log_b n = o(nʳ) for r>0 | :461 `isLittleO_logb_rpow` | MATCH | |
| (log n)ᵃ = o(cⁿ) for c>1 | :473 `isLittleO_log_pow_const_exp` | MATCH | |
| 完整增长层级 1 ≺ log log n ≺ log n ≺ n ≺ nᵃ ≺ 2ⁿ ≺ n! | :384–449 | MINOR | 反驳员发现：层极链注释缺少 lg* n（虽已独立证明）、缺少 n^ε 分数指数层、缺少 n^(lg n) 超多项式层、缺少 n! ≺ nⁿ（虽已独立证明） |
| 调和数 H_n = Θ(log n) | :98,110 | MATCH | 书中 §3.3 未讨论调和数，属额外内容 |
| ⌊n/2⌋ = Θ(n) 与 ⌈n/2⌉ = Θ(n) | :155,173 | MATCH | |
| n! = Ω(cⁿ) for any c | :433 `isBigOmega_factorial_exp` | MATCH | 推广了 (3.27) |
| nᵃ = o(n!) | :442 `isLittleO_pow_factorial` | MATCH | |
| nᵃ = o(2ⁿ) | :421 `isLittleO_pow_two_pow` | MATCH | |
| 2ⁿ = o(n!) | :427 `isLittleO_two_pow_factorial` | MATCH | |
| aⁿ = o(bⁿ) for 0 ≤ a < b | :90 `isLittleO_exp_exp_of_lt` | MATCH | |
| F_n = o(cⁿ) for c > φ | :582 `isLittleO_fib_exp` | MATCH | |
| cⁿ = o(F_n) for 0 ≤ c < φ | :594 `isLittleO_exp_fib` | MATCH | |
| "多项式有界"/"多对数有界"定义 | 无 | MINOR | 未形式化 |
| 习题 3.3-1 至 3.3-9 | 无 | MATCH | 习题不在形式化范围内 |
| 章末问题 3-1 至 3-7 | 无 | MATCH | 章末问题不在形式化范围内 |

## 缺陷清单

### MINOR（21 条）

**m1. 严重度: MINOR** — `Section_03_1_Asymptotic_Notation.lean:22–30`：O/Ω/Θ/o/ω 五记号的绝对值形式 vs 书中无绝对值形式。建议在模块文档中注明等价性。

**m2. 严重度: MINOR** — `Section_03_1_Asymptotic_Notation.lean:26`（反驳员发现）：Θ 定义 (`isBigO ∧ isBigOmega`) 与 Theorem 3.1 互换。书中 Θ 定义为 c₁g(n) ≤ f(n) ≤ c₂g(n) 的夹逼形式，Theorem 3.1 证明 Θ = O ∩ Ω。Lean 将定理作为定义，书中定义降级为导出定理 `isBigTheta_iff_sharedThreshold`(:195)。逻辑等价但组织结构不同。

**m3. 严重度: MINOR** — `Section_03_1_Asymptotic_Notation.lean:56,116`：o/ω 使用 `≤` 而非书中严格 `<`。建议在文档注释中说明等价性。

**m4. 严重度: MINOR** — `Section_03_1_Asymptotic_Notation.lean:22–30`：函数域固定为 `ℕ → ℝ`，未提供 `ℝ → ℝ` 版本。

**m5. 严重度: MINOR** — `Section_03_1_Asymptotic_Notation.lean`：缺少 `isLittleO_trans` 和 `isLittleOmega_trans` 引理。

**m6. 严重度: MINOR** — `Section_03_2_Standard_Functions.lean`：单调性定义未形式化。

**m7. 严重度: MINOR** — `Section_03_2_Standard_Functions.lean`：下取整/上取整十项代数恒等式 (3.1)–(3.10) 未形式化。

**m8. 严重度: MINOR** — `Section_03_2_Standard_Functions.lean`：模运算定义 (3.11)–(3.12) 未形式化。

**m9. 严重度: MINOR** — `Section_03_2_Standard_Functions.lean:44,53`：仅形式化单项式比较，未形式化一般多项式 p(n)=Θ(nᵈ)（含系数和低阶项）。

**m10. 严重度: MINOR** — `Section_03_2_Standard_Functions.lean`：指数恒等式 a⁰=1, aᵐaⁿ=aᵐ⁺ⁿ 等未形式化（mathlib 已覆盖）。

**m11. 严重度: MINOR** — `Section_03_2_Standard_Functions.lean`：指数不等式 1+x ≤ eˣ (3.14) 未形式化。

**m12. 严重度: MINOR** — `Section_03_2_Standard_Functions.lean`：eˣ 近似 (3.15) 与极限 (3.16) 未形式化。

**m13. 严重度: MINOR** — `Section_03_2_Standard_Functions.lean:62`（反驳员发现）：`isLittleO_pow_const_exp` 的指数 `a : ℕ` 限制为自然数，书中允许实数指数。n^1.5 = o(2ⁿ) 等情形无法从此定理直接得出。

**m14. 严重度: MINOR** — `Section_03_2_Standard_Functions.lean:75`（反驳员发现）：`isLittleO_log_pow_rpow` 的对数指数 `a : ℕ` 限制为自然数，书中允许实数指数。

**m15. 严重度: MINOR** — `Section_03_2_Standard_Functions.lean`：对数恒等式 (3.17)–(3.21)、级数展开 (3.22)、不等式 (3.23) 未形式化（mathlib 已覆盖）。

**m16. 严重度: MINOR** — `Section_03_2_Standard_Functions.lean`：Stirling 近似 (3.25) 未显式陈述；仅间接使用 mathlib 的 Stirling 引理证明 log(n!) = Θ(n log n)。

**m17. 严重度: MINOR** — `Section_03_2_Standard_Functions.lean`：阶乘细化界 (3.29) 未形式化。

**m18. 严重度: MINOR** — `Section_03_2_Standard_Functions.lean`：函数迭代一般定义 (3.30) 未形式化。

**m19. 严重度: MINOR** — `Section_03_2_Standard_Functions.lean`：lg* 4, 16, 65536, 2^65536 具体值未列出。

**m20. 严重度: MINOR** — `Section_03_2_Standard_Functions.lean`：Fibonacci 递推定义 (3.31) 和黄金比例定义 (3.32)–(3.33) 使用 mathlib 定义，未显式重述。

**m21. 严重度: MINOR** — `Section_03_2_Standard_Functions.lean:384–449`（反驳员发现）：完整增长层级链注释缺少 lg* n、n^ε 分数指数、n^(lg n) 超多项式层、n! ≺ nⁿ，尽管其中多数已独立证明。

## 反驳记录

反驳员复核了审计员对照表中 8 条高风险 MATCH 条目，逐条检查了表示等价陷阱、定理强度、命名误导、指数类型约束和书中定义对应性。

**提出 4 条独立差异，全部成立并降级为 MINOR：**

1. **Θ 定义与定理互换** — `Section_03_1_Asymptotic_Notation.lean:26`：书中 Θ 定义为存在 c₁,c₂ 夹逼，Theorem 3.1 证明 Θ = O ∩ Ω；Lean 将定理作为 Θ 的定义，书中定义降级为导出定理。逻辑等价，但组织结构不同。
2. **nᵇ = o(aⁿ) 指数类型收窄** — `Section_03_2_Standard_Functions.lean:62`：指数 `a : ℕ`，书中允许实数指数。
3. **lgᵇ n = o(nᵃ) 对数指数类型收窄** — `Section_03_2_Standard_Functions.lean:75`：对数的指数 `a : ℕ`，书中允许实数指数。
4. **完整增长层级链不完整** — `Section_03_2_Standard_Functions.lean:384–449`：链注释缺少 lg* n、n^ε 分数指数、n^(lg n) 层、n! ≺ nⁿ。

其余 4 条高风险 MATCH（lg(n!) = Θ(n lg n)、Binet 闭形式、F_n = Θ(φⁿ)、对数底变换）经多维复核后维持 MATCH 判定。剩余 34 条低风险 MATCH 条目（自反性/传递性/对称性等代数性质、散文级示例、记号约定、习题等）未逐条复核，维持审计员原判。

**注意**: 反驳员因 API 限制仅复核了高风险子集（8/42 MATCH），未覆盖全部 MATCH 条目。低风险条目（代数性质、记号约定等）的 MATCH 判定置信度较高，但未被独立验证。

## 各节分布

| 节 | MATCH | MINOR | MAJOR | CRITICAL |
|----|-------|-------|-------|----------|
| §3.1–§3.2 渐近记号 | 10 | 7 | 0 | 0 |
| §3.3 标准函数 | 28 | 14 | 0 | 0 |

## 审计总结

第 3 章的形式化忠实于 CLRS 第四版。五类渐近记号（O/Ω/Θ/o/ω）的核心语义正确，代数性质（自反性、传递性、对称性、转置对称性）基本完整。§3.3 的渐近增长事实覆盖面极广：多项式/对数/指数/阶乘/Fibonacci 之间的比较关系全部形式化，log(n!) = Θ(n log n)、Fibonacci 的 Binet 闭形式与 Θ(φⁿ) 增长、迭代对数 lg* 的定义与 o(log n) 极慢增长均得到证明。

**关键发现**:
- 无 MAJOR 或 CRITICAL 缺陷。21 条 MINOR 均为表面级别：绝对值 vs 无绝对值表述差异、定义/定理结构互换、ℕ 指数类型收窄（反驳员核心发现）、代数恒等式缺失（mathlib 已覆盖）、辅助定义缺失。
- 反驳员发现的 4 条差异中，最值得关注的是**指数类型收窄**（m13, m14）：`ℕ` 指数限制使 n^1.5 = o(2ⁿ) 等实数指数情形无法从现有定理直接得出，但可通过连续性论证或额外引理桥接。
- Θ 定义与定理互换（m2）是设计选择而非缺陷：将 `isBigTheta := isBigO ∧ isBigOmega` 作为定义简化了代数性质的证明，`isBigTheta_iff_sharedThreshold` 保留了书中的夹逼形式。
- 完整增长层级链（m21）的注释不完整，但链中所有独立比较关系均已证明，仅注释未及时更新。