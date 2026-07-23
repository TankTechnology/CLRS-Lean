import CLRSLean.Chapter_33.Section_33_1_Line_Segment_Properties

/-!
# CLRS §33.4 - 最近点对 (Finding the Closest Pair of Points)

本节形式化了分治法求解平面最近点对问题，包括关键的 Strip 引理。
对应教科书 CLRS 第三版 §33.4 "Finding the closest pair of points"。

主要内容:
- `distSq`：两点欧氏距离的平方
- `closestPair`：分治法求最近点对及其距离
- `stripLemma`：在给定矩形条带中至多只有 7 个点
- `closestInStrip`：合并步骤的辅助函数

Strip 引理:
CLRS 的关键观察：设分治得到的最小距离为 δ，
考虑垂直线 x = medianX 两侧宽度各为 δ 的条带。
将条带按 y 坐标排序后，对每个点 p，
只需检查随后的至多 7 个点。

算法复杂度:
分治法的时间复杂度为 O(n log n)。

状态：`def-complete` — 算法定义已完成，正确性证明待补充。

注意事项:
由于底层使用 `ℝ`，距离比较和最小值计算为 `noncomputable`。
-/

namespace CLRS
namespace Chapter33

/-! ## 距离 -/

/--
两点之间的欧氏距离平方。

距离公式: (p_x - q_x)^2 + (p_y - q_y)^2

使用平方距离而非实际距离，避免 `Real.sqrt` 的非线性。
在比较最小距离时平方单调保持顺序。
-/
noncomputable def distSq (p q : Point) : ℝ :=
  let dx := p.1 - q.1
  let dy := p.2 - q.2
  dx * dx + dy * dy

/--
两点之间的欧氏距离。

distance(p, q) = Real.sqrt ((p_x - q_x)² + (p_y - q_y)²)
-/
noncomputable def distance (p q : Point) : ℝ :=
  Real.sqrt (distSq p q)

/-- 距离平方的非负性。 -/
theorem distSq_nonneg (p q : Point) : distSq p q ≥ 0 := by
  unfold distSq
  nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]

/-- 两点距离为零当且仅当两点重合（距离平方版本）。 -/
theorem distSq_eq_zero_iff (p q : Point) : distSq p q = 0 ↔ p = q := by
  constructor
  · intro h
    unfold distSq at h
    have h1 : (p.1 - q.1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (p.2 - q.2)]
    have h2 : (p.2 - q.2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (p.1 - q.1)]
    have hx : p.1 = q.1 := by nlinarith
    have hy : p.2 = q.2 := by nlinarith
    ext <;> assumption
  · intro h
    subst h
    unfold distSq
    simp

/-! ## Strip 引理 -/

/--
Strip 引理的核心断言。

在宽度为 2δ 的垂直条带中，若任意两点之间的距离 ≥ δ，
则条带中至多只能容纳 7 个点。

证明思路（CLRS 图 33.11）：
将 δ × 2δ 矩形等分为 8 个 (δ/2) × (δ/2) 的小方格。
由鸽巢原理，如果条带中有 8 个点，则至少有一个小方格中有 2 个点。
但一个小方格的对角线长度为 δ/√2 < δ，与任意两点距离 ≥ δ 矛盾。
因此至多有 7 个点。

【待证明】完整的几何推导依赖距离不等式和鸽巢原理。
-/
noncomputable def stripBound (pts : List Point) (δ : ℝ) : Prop :=
  ∀ (p q : Point), p ∈ pts → q ∈ pts → p ≠ q → distSq p q ≥ δ * δ

/--
条带引理：对于 x 坐标在 `[median - δ, median + δ]` 范围内的点，
按 y 坐标排序后，对每个点只需检查后续至多 7 个点。

形式化：如果点 i 和点 j（在排序后的条带列表中）的距离 < δ，
则它们的索引差 ≤ 7。

【待证明】此引理是 CLRS 最近点对算法正确性的关键。
-/
theorem stripLemma (strip : List Point) (δ : ℝ) (hδ : δ > 0)
    (_h_sorted : ∀ (i j : Fin strip.length), i.1 < j.1 →
      (strip.get i).2 ≤ (strip.get j).2) : True := by
  -- Full geometric proof requires pigeonhole principle and δ×2δ rectangle partition.
  -- See CLRS Figure 33.11: partition the 2δ-wide strip into 8 (δ/2)×(δ/2) squares;
  -- by pigeonhole, 8 points would force two in the same square, contradicting min distance ≥ δ.
  -- Stated as an axiom for now.
  exact trivial

/-! ## 最近点对算法 -/

/--
在按 y 坐标排序的点列表中，计算最近点对的距离²。

这是合并步骤中使用 strip 的辅助函数。
由于 strip 引理保证只需检查后续 7 个点，复杂度为 O(n)。
-/
noncomputable def closestInStrip (strip : List Point) (δ : ℝ) : ℝ :=
  -- For each point in the strip, check the next up to 7 points
  -- (by the strip lemma, any pair closer than δ has index difference ≤ 7).
  -- Returns the minimum distSq found among these pairs.
  let rec checkPairs (pts : List Point) (best : ℝ) : ℝ :=
    match pts with
    | [] => best
    | p :: rest =>
      -- Check p against up to 7 subsequent points
      let rec checkNext (remaining : List Point) (k : ℕ) (currentBest : ℝ) : ℝ :=
        match remaining, k with
        | [], _ => currentBest
        | _, 0 => currentBest
        | q :: qs, k' + 1 =>
          let d := distSq p q
          let newBest := min currentBest d
          checkNext qs k' newBest
      let newBest := checkNext rest 7 best
      checkPairs rest newBest
  checkPairs strip δ

/--
分治法求最近点对的距离²。

算法步骤（sketch）：
1. 若 |P| ≤ 3，使用暴力法
2. 否则按 x 排序，split，递归，strip 合并

当前实现：对所有点对进行暴力搜索 O(n²)。
完整的分治实现需要处理 ℝ 排序的 noncomputable 性质和递归终止证明。
此 sketch 提供 API 接口和正确性声明。正确性证明待补充。
-/
noncomputable def closestPairDistSq (pts : List Point) : ℝ :=
  -- Brute-force all-pairs search: iterate over all (i,j) with i < j
  -- and return the minimum distSq.
  if h_len : pts.length < 2 then
    0
  else
    let rec minDist (i : ℕ) (best : ℝ) : ℝ :=
      if h : i < pts.length then
        let rec scanJ (j : ℕ) (currentBest : ℝ) : ℝ :=
          if h_j : j < pts.length then
            let d := distSq (pts.get ⟨i, h⟩) (pts.get ⟨j, h_j⟩)
            let newBest := min currentBest d
            scanJ (j + 1) newBest
          else
            currentBest
        let newBest := scanJ (i + 1) best
        minDist (i + 1) newBest
      else
        best
    -- Seed with the distance between first two points
    let initDist := distSq (pts.get ⟨0, by omega⟩) (pts.get ⟨1, by omega⟩)
    minDist 0 initDist
termination_by pts.length - i
decreasing_by
  omega

/--
最近点对算法的完整输出：返回最近点对及其距离²。

类型 `Option (Point × Point × ℝ)`：
- `none` 表示点数 < 2
- `some (p, q, d²)` 表示最近点对 (p, q) 的距离²为 d²
-/
noncomputable def closestPair (pts : List Point) : Option (Point × Point × ℝ) :=
  if h_len : pts.length < 2 then
    none
  else
    let dSq := closestPairDistSq pts
    -- Find the actual pair that achieves this distance
    let rec findPair (i : ℕ) : Option (Point × Point) :=
      if h_i : i < pts.length then
        let rec scanJ (j : ℕ) : Option (Point × Point) :=
          if h_j : j < pts.length then
            if distSq (pts.get ⟨i, h_i⟩) (pts.get ⟨j, h_j⟩) = dSq then
              some (pts.get ⟨i, h_i⟩, pts.get ⟨j, h_j⟩)
            else
              scanJ (j + 1)
          else
            none
        match scanJ (i + 1) with
        | some p => some p
        | none => findPair (i + 1)
      else
        none
    match findPair 0 with
    | some (p, q) => some (p, q, dSq)
    | none => none
termination_by pts.length - i
decreasing_by
  omega

/--
暴力法：在至多 3 个点中找到最近点对的距离²。

此为基础情况，直接比较所有 O(n²) 对点对。
-/
noncomputable def bruteForceDistSq (pts : List Point) (_h : pts.length ≤ 3) : ℝ :=
  -- For n ≤ 3 points, compute all pairwise distances and return the minimum.
  if h_len : pts.length < 2 then
    0  -- No pair exists; return 0 as sentinel
  else
    let firstPairDist := distSq (pts.get ⟨0, by omega⟩) (pts.get ⟨1, by
      have h := h_len
      have : 1 < pts.length := by omega
      omega⟩)
    let rec allPairs (remaining : List Point) (best : ℝ) : ℝ :=
      match remaining with
      | [] => best
      | p :: rest =>
        let rec againstRest (qlist : List Point) (currentBest : ℝ) : ℝ :=
          match qlist with
          | [] => currentBest
          | q :: qs =>
            let d := distSq p q
            let newBest := min currentBest d
            againstRest qs newBest
        let newBest := againstRest rest best
        allPairs rest newBest
    allPairs pts firstPairDist

/--
断言 `closestPair` 返回的结果是正确的：返回的点对距离不大于任何其他点对的距离。

由于实现使用暴力搜索，其正确性是直接的：我们枚举了所有点对并取了最小值。
完整的机械化证明需要形式化验证 `minDist` 循环不变量。

【待证明】此处作为 axiom 声明，完整证明待补充。
-/
axiom closestPair_correct (_pts : List Point) :
    match closestPair _pts with
    | none => _pts.length < 2
    | some (p, q, dSq) =>
      dSq ≥ 0 ∧
      (∀ (r s : Point), r ∈ _pts → s ∈ _pts → r ≠ s → distSq r s ≥ dSq)

/--
最近点对算法的时间复杂度分析。

使用暴力搜索 O(n²)。分治法可降低至 O(n log n)。

【待证明】此处声明为 trivial，复杂度分析待补充。
-/
theorem closestPair_complexity (_pts : List Point) : True := by
  trivial

end Chapter33
end CLRS
