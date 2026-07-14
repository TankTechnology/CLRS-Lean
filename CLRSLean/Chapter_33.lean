import CLRSLean.Chapter_33.Section_33_1_Line_Segment_Properties
import CLRSLean.Chapter_33.Section_33_2_3_Segment_Intersection_Convex_Hull
import CLRSLean.Chapter_33.Section_33_4_Closest_Pair

/-!
# Chapter 33 - 计算几何 (Computational Geometry)

Chapter 33 是 CLRS 的计算几何章节，涵盖了线段相交判定、凸包构建
和最近点对问题的基础算法。

## 章节

* 33.1 线段性质 (Line-Segment Properties)：`selected-section-complete`。
  主要定义：
  {lit}`CLRS.Chapter33.Point`，
  {lit}`CLRS.Chapter33.cross`，
  {lit}`CLRS.Chapter33.orientation`，
  {lit}`CLRS.Chapter33.Segment`，
  {lit}`CLRS.Chapter33.onBbox`，
  {lit}`CLRS.Chapter33.bboxIntersect`，
  {lit}`CLRS.Chapter33.segmentIntersect`。

* 33.2-33.3 线段相交判定与凸包：`def-complete`。
  主要定义：
  {lit}`CLRS.Chapter33.SweepEvent`，
  {lit}`CLRS.Chapter33.anySegmentIntersect`，
  {lit}`CLRS.Chapter33.convexHull`，
  {lit}`CLRS.Chapter33.polarLess`。

* 33.4 最近点对：`def-complete`。
  主要定义：
  {lit}`CLRS.Chapter33.distSq`，
  {lit}`CLRS.Chapter33.closestPair`，
  {lit}`CLRS.Chapter33.stripLemma`。

## 当前状态

§33.1 已完成几何原语的形式化：点和向量的定义、叉积及其基本代数性质、
三点方向判定、包围盒测试、以及完整的 CLRS 线段相交判定算法。

§33.2-33.3 已完成扫描线相交判定和 Graham 扫描的数据结构定义。
凸包构建的主算法体因 `ℝ` 上极角比较不可计算而标记为 `sorry`。

§33.4 已完成最近点对算法的数据结构定义和 strip 引理的形式化。
分治算法体和正确性证明待补充（`sorry`）。

## 待办工作

* §33.1 相交判定正确性证明（CLRS 定理 33.1）
* §33.2 扫描线算法的正确性和不变式维护
* §33.3 Graham 扫描的正确性证明（使用 `ℚ` 实现可计算版本）
* §33.4 分治法最近点对的正确性证明（含 strip 引理）
-/

namespace CLRS
namespace Chapter33

end Chapter33
end CLRS
