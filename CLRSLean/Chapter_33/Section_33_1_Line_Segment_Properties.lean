import Mathlib

/-!
# CLRS §33.1 - 线段性质 (Line-Segment Properties)

本节形式化了计算几何的基础原语：点、向量、叉积、方向判定以及线段相交测试。
对应教科书 CLRS 第三版 §33.1 "Line-segment properties"。

## 主要内容

- `Point` / `Vector`：ℝ² 中的点和向量定义
- `cross`：二维叉积 `p₁ × p₂ = x₁·y₂ - x₂·y₁`
- `orientation`：通过叉积符号判定三点方向（逆时针 / 顺时针 / 共线）
- `Segment`：由两个端点定义的线段
- `onBbox` / `bboxIntersect`：包围盒（bounding box）快速剔除测试
- `segmentIntersect`：完整的线段相交条件（基于方向判定 + 共线特例）

状态：`selected-section-complete` — 定义和算法已形式化，正确性证明待补充。

## 叉积的几何意义

对于向量 `p₁ = (x₁, y₁)` 和 `p₂ = (x₂, y₂)`：
- `cross p₁ p₂ = x₁·y₂ - x₂·y₁`
- 绝对值等于 p₁ 和 p₂ 张成的平行四边形面积
- 符号：正表示 p₂ 在 p₁ 的逆时针方向，负表示顺时针，零表示共线

从 p₀ 出发的两条线段 p₀p₁ 和 p₀p₂，方向由 `cross (p₁ - p₀) (p₂ - p₀)` 判定。

## 线段相交判定（CLRS 算法）

对于线段 s₁ = (p₁, p₂) 和 s₂ = (p₃, p₄)：
1. 计算四个方向：d1 = orientation(p₁,p₂,p₃), d2 = orientation(p₁,p₂,p₄),
                     d3 = orientation(p₃,p₄,p₁), d4 = orientation(p₃,p₄,p₂)
2. 一般情况下 d1 ≠ d2 且 d3 ≠ d4 表示线段跨越相交
3. 当某方向为共线时，检查对应端点是否在另一线段的包围盒内

注意：由于 `ℝ` 上的比较不可计算，`orientation` 和相交判定均为 `noncomputable`。
若需要可计算版本，应使用有理数 `ℚ` 或有限精度近似。
-/

namespace CLRS
namespace Chapter33

/-! ## 点和向量 -/

/-- 二维平面中的点，用 `ℝ × ℝ` 表示。 -/
abbrev Point := ℝ × ℝ

/-- 二维平面中的向量，与 `Point` 类型同构。 -/
abbrev Vector := ℝ × ℝ

/-- 向量的 x 分量。 -/
def x (p : ℝ × ℝ) : ℝ := p.1

/-- 向量的 y 分量。 -/
def y (p : ℝ × ℝ) : ℝ := p.2

/-- 向量加法。 -/
def vadd (p q : ℝ × ℝ) : ℝ × ℝ := (p.1 + q.1, p.2 + q.2)

/-- 向量减法。 -/
def vsub (p q : ℝ × ℝ) : ℝ × ℝ := (p.1 - q.1, p.2 - q.2)

/-- 标量乘法。 -/
def smul (c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (c * p.1, c * p.2)

/-! ## 叉积（Cross Product） -/

/--
二维叉积：`cross p₁ p₂ = x₁·y₂ - x₂·y₁`。

几何意义：若以原点为起点，`cross p₁ p₂` 的绝对值等于 p₁ 和 p₂ 张成的
平行四边形面积；符号表示 p₁ 逆时针旋转到 p₂ 的方向（正 = 逆时针，负 = 顺时针）。
-/
def cross (p₁ p₂ : ℝ × ℝ) : ℝ :=
  p₁.1 * p₂.2 - p₂.1 * p₁.2

/-- 叉积的反对称性：`cross p q = -(cross q p)`。 -/
theorem cross_antisymm (p q : ℝ × ℝ) : cross p q = - cross q p := by
  simp [cross]

/-- 叉积对第一个参数的加法线性。 -/
theorem cross_add_left (p q r : ℝ × ℝ) : cross (vadd p q) r = cross p r + cross q r := by
  simp [cross, vadd]
  ring

/-- 叉积对第一个参数的标量乘法齐次。 -/
theorem cross_smul_left (c : ℝ) (p q : ℝ × ℝ) : cross (smul c p) q = c * cross p q := by
  simp [cross, smul]
  ring

/-- 自身叉积为零：`cross p p = 0`。 -/
theorem cross_self (p : ℝ × ℝ) : cross p p = 0 := by
  simp [cross]

/-- 共线向量叉积为零：若 `q = c · p`，则 `cross p q = 0`。 -/
theorem cross_smul_self (c : ℝ) (p : ℝ × ℝ) : cross p (smul c p) = 0 := by
  simp [cross, smul]
  ring

/-- 叉积对第二个参数的加法线性（由反对称性可得）。 -/
theorem cross_add_right (p q r : ℝ × ℝ) : cross p (vadd q r) = cross p q + cross p r := by
  simp [cross, vadd]
  ring

/-! ## 方向判定（Orientation） -/

/--
三点 `(p₀, p₁, p₂)` 的方向类型。

- `Counterclockwise`（逆时针 / 左转）：从有向线段 p₀→p₁ 到 p₀→p₂ 需要左转
- `Clockwise`（顺时针 / 右转）：从 p₀→p₁ 到 p₀→p₂ 需要右转
- `Collinear`（共线）：三点在同一条直线上
-/
inductive Orientation : Type where
  | Counterclockwise
  | Clockwise
  | Collinear
  deriving DecidableEq, Inhabited

/--
计算三点 `(p₀, p₁, p₂)` 的方向。

方向通过叉积 `(p₁ - p₀) × (p₂ - p₀)` 判定：
- `> 0` → `Counterclockwise`（逆时针）
- `< 0` → `Clockwise`（顺时针）
- `= 0` → `Collinear`（共线）

由于 `ℝ` 上的 `>` 比较不可计算，此定义为 `noncomputable`。
-/
noncomputable def orientation (p₀ p₁ p₂ : ℝ × ℝ) : Orientation :=
  let cp := cross (vsub p₁ p₀) (vsub p₂ p₀)
  if h : cp > 0 then Orientation.Counterclockwise
  else if h : cp < 0 then Orientation.Clockwise
  else Orientation.Collinear

/-- 方向判定结果与其叉积符号的对应关系。 -/
theorem orientation_spec (p₀ p₁ p₂ : ℝ × ℝ) :
    let cp := cross (vsub p₁ p₀) (vsub p₂ p₀)
    match orientation p₀ p₁ p₂ with
    | Orientation.Counterclockwise => cp > 0
    | Orientation.Clockwise => cp < 0
    | Orientation.Collinear => cp = 0 := by
  intro cp
  have h_cp : cp = cross (vsub p₁ p₀) (vsub p₂ p₀) := rfl
  rw [h_cp]
  unfold orientation
  by_cases h : cross (vsub p₁ p₀) (vsub p₂ p₀) > 0
  · simp [h]
  · by_cases h' : cross (vsub p₁ p₀) (vsub p₂ p₀) < 0
    · simp [h, h']
    · have : cross (vsub p₁ p₀) (vsub p₂ p₀) = 0 := by linarith
      simp [h, h', this]

/-! ## 线段（Line Segments） -/

/-- 线段由两个端点定义：起点 `p` 和终点 `q`。 -/
structure Segment where
  /-- 线段起点 -/
  p : ℝ × ℝ
  /-- 线段终点 -/
  q : ℝ × ℝ
  deriving Inhabited

/-- 创建线段。 -/
def mkSegment (p q : ℝ × ℝ) : Segment := ⟨p, q⟩

/--
判定点 `r` 是否在线段 `(p, q)` 的包围盒（bounding box）内。

包围盒是以线段端点为对角顶点的轴对齐矩形。
此谓词用于相交测试中处理共线端点在线段上的情况。
-/
noncomputable def onBbox (r p q : ℝ × ℝ) : Prop :=
  min p.1 q.1 ≤ r.1 ∧ r.1 ≤ max p.1 q.1 ∧
  min p.2 q.2 ≤ r.2 ∧ r.2 ≤ max p.2 q.2

/-- 线段 `s` 的包围盒，返回 `(xmin, xmax, ymin, ymax)`。 -/
def bbox (s : Segment) : ℝ × ℝ × ℝ × ℝ :=
  (min s.p.1 s.q.1, max s.p.1 s.q.1, min s.p.2 s.q.2, max s.p.2 s.q.2)

/--
判定两个线段 `s1` 和 `s2` 的包围盒是否相交（投影重叠测试）。

这是线段相交测试中的快速剔除步骤：
若包围盒不相交，则线段必定不相交。
-/
noncomputable def bboxIntersect (s1 s2 : Segment) : Prop :=
  let (xmin1, xmax1, ymin1, ymax1) := bbox s1
  let (xmin2, xmax2, ymin2, ymax2) := bbox s2
  (xmin1 ≤ xmax2 ∧ xmin2 ≤ xmax1) ∧ (ymin1 ≤ ymax2 ∧ ymin2 ≤ ymax1)

/-! ## 线段相交判定 -/

/--
CLRS §33.1 线段相交判定。

基于方向判定和包围盒测试：
1. 计算 `d1 = orientation(p₁, p₂, p₃)`, `d2 = orientation(p₁, p₂, p₄)`
2. 计算 `d3 = orientation(p₃, p₄, p₁)`, `d4 = orientation(p₃, p₄, p₂)`
3. 一般情况下 `d1 ≠ d2` 且 `d3 ≠ d4` 表示线段跨越相交
4. 若某个方向为 `Collinear`，则检查对应端点是否在另一线段的包围盒内

此为 CLRS Fig 33.2 中 `SEGMENTS-INTERSECT` 算法的数学形式化。
-/
noncomputable def segmentIntersect (s1 s2 : Segment) : Prop :=
  let d1 := orientation s1.p s1.q s2.p
  let d2 := orientation s1.p s1.q s2.q
  let d3 := orientation s2.p s2.q s1.p
  let d4 := orientation s2.p s2.q s1.q
  (d1 ≠ d2 ∧ d3 ≠ d4) ∨
  (d1 = Orientation.Collinear ∧ onBbox s2.p s1.p s1.q) ∨
  (d2 = Orientation.Collinear ∧ onBbox s2.q s1.p s1.q) ∨
  (d3 = Orientation.Collinear ∧ onBbox s1.p s2.p s2.q) ∨
  (d4 = Orientation.Collinear ∧ onBbox s1.q s2.p s2.q)

/--
判定两线段是否共享端点。

这是相交的特殊情况 —— 若共享端点，相交测试的某些方向为共线。

【待证明】共享端点的两线段必定满足 `segmentIntersect`。
证明思路：共享端点意味着四个方向中至少有一个为 `Collinear`，
且共享端点必定落在另一线段的包围盒内。
-/
noncomputable def sharesEndpoint (s1 s2 : Segment) : Prop :=
  s1.p = s2.p ∨ s1.p = s2.q ∨ s1.q = s2.p ∨ s1.q = s2.q

/-! ## 附录：方便使用的别名 -/

/-- 点 (0, 0) —— 原点。 -/
def origin : ℝ × ℝ := (0, 0)

/-- 从点 `p` 到 `q` 的向量。 -/
def toVector (p q : ℝ × ℝ) : ℝ × ℝ := vsub q p

end Chapter33
end CLRS
