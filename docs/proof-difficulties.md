# Ch28-32 证明难点分析

本文档记录 CLRS-Lean 项目 Chapter 28-32 中 24 个剩余 `sorry` 的困难所在。

## 一、已修复的问题

### Ch29 对偶定义错误
- **问题**：`StandardLP.dual` 中约束方向为 Aᵀy ≤ c，标准 LP 对偶要求 Aᵀy ≥ c
- **修复**：将 dual 的 A 改为 `-lp.A.transpose`，b 改为 `-lp.c`

### Ch32 KMP 算法 bug
- **问题**：`buildPi` 递归实现了错误的 π 值（π(2)=1 而非 0）
- **根因**：proper prefix 约束未正确处理

### Ch30 FFT 占位定义
- **问题**：`iterativeFFT` 和 `fft` 函数体为 `sorry`
- **修复**：提供 noncomputable 的骨架实现

---

## 二、剩余难点

### Ch28：矩阵运算（4 sorries）

| 定理 | 难点 |
|------|------|
| `lupDecomp_exists` | **构造性算法**：需要逐列选主元、Schur 补更新。Lean 中 Fin n 矩阵的列操作繁琐，需要反复 `Fin.cases`/`Fin.cons` 分解矩阵 |
| `lupSolve_correct` | **置换矩阵代数**：A = P⁻¹LU，需证 Ax = b ⇔ P⁻¹LUx = b。`Matrix.mulVec` 和 `dotProduct` 两套 API 不统一，`simp` 无法自动展开 |
| `ldltDecomp_exists` | **SPD 不变量**：列递推需证 D[j,j] > 0 保持正定性，涉及 `xᵀAx > 0` 的展开 |
| `leastSquares_optimal` | **正交分解**：需证 ‖Ay-b‖² = ‖r‖² + ‖d‖² 且 ⟨r,d⟩ = 0。`Finset.sum` 与 `dotProduct` 转换繁琐 |

**核心障碍**：Mathlib `Matrix` API 在 Lean 4.32 版本中 `dotProduct` 已被 `mulVec` 替代，但项目中两套 API 混用，导致 `simp` 和 `rw` 频繁失败。

### Ch29：线性规划（4 sorries）

| 定理 | 难点 |
|------|------|
| `weak_duality` | **修复后应可证**：cᵀx ≤ bᵀy 的证明是标准双和不等式链 |
| `strong_duality` | **需单纯形终止**：需从最终单纯形表的 reduced costs 提取对偶变量。Bland 规则保证终止，但循环不变量证明冗长 |
| `strong_duality_converse` | 对偶的对偶，依赖 `strong_duality` |
| `simplex_correct` | **算法正确性**：可行不变、目标不减、最优条件 (cⱼ ≤ 0)。需要 `Finset` 上的循环不变量 |

**核心障碍**：单纯形算法涉及大量索引操作（`Fin n` 上的基本/非基本变量分划），`Finset` 证明冗长。

### Ch30：FFT（5 sorries）

| 定理 | 难点 |
|------|------|
| `fftPow2_eq_dft` | **强归纳**：需证 Cooley-Tukey 蝶形分解保持 DFT。已证 `dft_split_even_odd` 是关键引理 |
| `iterativeFFT` 定义 | **算法实现**：位反转排列 + lg n 层蝶形对。`Fin` 索引和 `Nat` 位运算交错 |
| `fft` 定义 | 包装函数，技术性不难 |
| `iterativeFFT_eq_dft` | **归纳不变式**：每层蝶形保持 DFT 等价性 |
| `idft_fft_eq` | 组合 `idft_dft`（已证）和 `iterativeFFT_eq_dft` |

**核心障碍**：位反转函数 `bitReverse` 的归纳性质易证，但 `iterativeFFT` 的三层嵌套循环（位反转 → 阶段 → 块内蝶形）在 Lean 中很难写终止证明。可行方案：用 `Finset` 上的迭代代替 `for` 循环。

### Ch31：数论算法（6 sorries）

| 定理 | 难点 |
|------|------|
| `modularExponentiation_spec` | **Lean 4 限制**：`go` 用 `where` 定义的局部函数无法用 `dsimp`/`unfold` 展开，导致归纳假设无法使用 |
| `factorOutTwos_spec` (偶数情况) | 数论不难（n'·2ˢ = 2ˢ'·d），但 `generalize` 导致依赖类型问题 |
| `prime_implies_no_witnesses` | **费马小定理** + 域性质。`ZMod` API 丰富，理论上可证 |
| `miller_rabin_error_bound` | **研究级难度**：≤1/4 界需要分析 (ℤ/nℤ)^× 的子群结构。即使是 Coq/Isabelle 中也少见完整形式化 |
| `millerRabinTest_soundness` | 依赖 `prime_implies_no_witnesses` |
| `pollardRho_factor_divides` | **算法不变式**：Floyd 判圈 + gcd 因子。`pollardRhoGo.induct` 自动生成，但 `let` 绑定展开问题 |

**核心障碍**：
- Lean 4 的 `where` 定义展开是已知限制（https://github.com/leanprover/lean4/issues/2756）
- Miller-Rabin 误差界是真正的研究级形式化挑战

### Ch32：KMP（5 sorries）

| 定理 | 难点 |
|------|------|
| `prefixFunction_lt` | `buildPi` 的 `findK` 子循环归纳 |
| `prefixFunction_le_length` | 同上 |
| `prefixFunction_spec` | **核心正确性**：P[0..π[q]) 是 P[0..q) 的后缀。需要 `findK` 循环的完整不变式 |
| `kmpMatcher_correct` | KMP 匹配正确性，依赖 `prefixFunction_spec` |
| `prefixFunction_example_values` | 实现 bug 修复后用 `native_decide` |

**核心障碍**：`buildPi` → `findK` 的嵌套递归归纳。方案：将 `findK` 提升为顶层函数，分离不变量证明。

---

## 三、建议优先级

| 优先级 | 章节 | 预期难度 | 预计工作量 |
|--------|------|---------|-----------|
| P0 | Ch29 weak_duality | 低 | 已修复，待验证 |
| P0 | Ch30 FFT stubs | 低 | noncomputable 占位 |
| P0 | Ch32 KMP bug | 中 | 算法修正 + 重新验证 |
| P1 | Ch28 lupSolve_correct | 中 | 需统一 Matrix API |
| P1 | Ch32 KMP 证明 | 中 | 提升 findK + 归纳 |
| P2 | Ch28 其余 3 个 | 高 | 构造性算法 |
| P2 | Ch29 其余 3 个 | 高 | 单纯形不变式 |
| P2 | Ch30 fftPow2_eq_dft | 高 | 强归纳 + 位运算 |
| P3 | Ch31 全部 | 极高 | 数论深度形式化 |
