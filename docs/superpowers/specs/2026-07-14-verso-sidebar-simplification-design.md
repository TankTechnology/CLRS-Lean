# Verso 全站侧栏简化设计

日期：2026-07-14

状态：设计已在对话中批准，等待书面规格复核

## 背景

CLRS-Lean 的 Verso 站点会把 Lean 模块层级直接呈现在侧栏中。随着证明被拆成更小的模块，读者目录开始暴露实现结构。例如 Chapter 22 的 `22.3. Depth-First Search` 下出现五个证明辅助页，`22.5. Strongly Connected Components` 下出现 `Merge-Sort Congruence`。其他章节、`Proof Patterns` 和 `Probability` 也有相同问题。

这些页面本身有审计价值，不应删除；问题只在于它们占用了主阅读目录，使 CLRS 的章、节结构难以辨认。

## 目标

1. 保留当前一级入口及其顺序，不增加新的导航分组。
2. 所有 Chapter 继续默认展开。
3. 每章侧栏只展示章页面和直属的 CLRS `Section_*` 页面。
4. `Proof Patterns`、`Probability` 保留一级入口，但隐藏它们的子模块。
5. 隐藏页继续生成并保留搜索、sitemap、直接 URL、源码和父页入口。
6. 访问隐藏页时，侧栏高亮最近的可见父页面。
7. 规则自动覆盖以后新增的辅助模块，避免维护逐页黑名单。

## 非目标

- 不移动或重命名 Lean 文件和模块。
- 不修改 import 结构或定理接口。
- 不使用 Verso `exclude`；它会删除页面本身。
- 不改变一级入口顺序、章节默认展开策略、正文样式或搜索排序。
- 不把站点迁移为独立前端应用。

## 导航可见性规则

导航链接以 `title` 属性中的完整 Lean 模块名为准。一个模块仅在满足以下任一条件时出现在侧栏：

1. 模块是站点根 `CLRSLean`；
2. 模块是 `CLRSLean` 的直属子模块，例如 `CLRSLean.Chapter_22`、`CLRSLean.ProofPatterns`、`CLRSLean.Progress`；
3. 模块是某个 `CLRSLean.Chapter_NN` 的直属 `Section_*` 子模块，例如 `CLRSLean.Chapter_22.Section_22_3_DFS`。

其他更深层模块全部从侧栏裁剪。若导航节点没有可识别的完整模块名，优化器采用“保留”策略避免误删，渲染检查则把该节点作为未分类错误并阻止部署。

裁剪子节点后不保留空的展开控件。原本因存在辅助模块而渲染为 `<details>` 的 Section、`Proof Patterns` 或 `Probability`，若不再有可见子节点，将转换为普通 `.leaf` 链接。

### 当前会隐藏的模块

该规则目前会隐藏 22 个模块：

- `CLRSLean.ProofPatterns.{Boundary,Exchange,Fiber,Interval}`
- `CLRSLean.Probability.FiniteExpectation`
- `CLRSLean.Chapter_07.Section_07_3_Randomized_Quicksort.Comparison_Probability`
- `CLRSLean.Chapter_08.Section_08_2_Counting_Sort.{CountTables,MutableOutputArray}`
- `CLRSLean.Chapter_09.Section_09_3_Deterministic_Select.Randomized_Select`
- `CLRSLean.Chapter_17.Section_17_1_Amortized_Framework.Section_17_2_Stack_And_Counter`
- `CLRSLean.Chapter_17.Section_17_4_Dynamic_Tables.Section_17_4_Mutable_Array_Tables`
- `CLRSLean.Chapter_21.Section_21_4_Analysis.{CostedExecution,InverseAckermann}`
- `CLRSLean.Chapter_22.Section_22_3_DFS.{S1_WhitePath,S2_Intervals,S3_Bridge,S4_SCC,S5_EdgeClassification}`
- `CLRSLean.Chapter_22.Section_22_5_Strongly_Connected_Components.MergeSortCongr`
- `CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim.{S1_UnionFindBridge,S2_StatefulKruskal,S3_ExecutablePrim}`

这个清单用于审阅当前影响面，不作为运行时黑名单。

## 构建架构

部署链路保持为：

```text
Lean source
  -> Verso literate HTML
  -> optimize_literate_html.py
       1. 原有长页面优化
       2. 侧栏导航树裁剪
       3. 导航状态和父级高亮脚本注入
  -> rendered HTML checks
  -> sitemap
  -> GitHub Pages
```

新增一个可复用的导航可见性判定函数，供优化器、渲染检查和测试共同调用，避免多个脚本复制规则。

侧栏裁剪只解析 `.module-tree` 子树。它按完整模块名移除不可见节点、保留原顺序，并把没有可见子节点的 `<details>` 降级为 `.leaf`。正文、代码块、资源引用和其他导航结构不参与裁剪。

导航状态存储键升级一个版本，使改版后的首次访问不会继承与旧树结构不一致的状态。新版本仍以“所有 Chapter 展开”为默认值，继续保存用户手动展开、折叠和侧栏滚动位置。

## 隐藏页的父级定位

Verso 在当前页对应的导航节点上添加 `.current`。如果该节点因策略被隐藏，运行时导航脚本比较当前 URL 与所有可见导航链接的规范化路径，选择最长的目录前缀作为最近可见父级，并把 `.current` 应用到该父级的 `.leaf` 或 `<summary>`。

该逻辑只在裁剪后没有可见 `.current` 时运行，不覆盖 Verso 对普通章、节页面的原生高亮。

## Implementation details 入口

包含隐藏子页的父模块在模块级文档中增加统一的 `## Implementation details` 小节，使用相对链接指向各隐藏页面。当前涉及：

- `CLRSLean/ProofPatterns.lean`
- `CLRSLean/Probability.lean`
- Chapter 7 的 7.3 页面
- Chapter 8 的 8.2 页面
- Chapter 9 的 9.3 页面
- Chapter 17 的 17.1–17.3 与 17.4 页面
- Chapter 21 的 21.4 页面
- Chapter 22 的 22.3 与 22.5 页面
- Chapter 23 的 23.2 页面

已有的纯代码模块名说明会转换为可点击的页面链接。隐藏页仍可通过搜索、sitemap、直接 URL 和这些父页链接进入。前后页导航保持 Verso 当前行为。

## 容错

- 缺少或无法解析 `title` 模块名：优化器保留节点，渲染检查报告未分类错误并失败。
- 裁剪后仍有可见子节点：保留 `<details>` 及原有展开状态。
- 裁剪后没有可见子节点：转换为 `.leaf`，不显示无效的折叠箭头。
- 隐藏页不存在：父页链接和站点完整性检查失败，阻止部署。
- 优化脚本重复运行：输出必须保持不变。

## 验证与验收标准

### 单元测试

- 可见性判定覆盖根、一级入口、直属 Section、Section 后代和非 Chapter 子模块。
- 导航裁剪保留原顺序并删除所有不可见节点。
- 空 `<details>` 正确降级为 `.leaf`。
- 无模块名节点不会被误删。
- 普通 Section 保留原生 `.current`；隐藏页使用最近可见父级。
- 优化器重复运行保持幂等。

### 生成站点检查

- 每个生成页面的 `.module-tree` 中只允许符合可见性规则的模块链接。
- Chapter 22 侧栏只包含 22.1–22.5，不包含六个辅助证明页。
- 当前 22 个隐藏模块的 HTML 文件仍存在并进入 sitemap。
- 11 个父页面的 `Implementation details` 链接全部可解析到现存页面。
- 搜索资产仍覆盖隐藏页。

### 浏览器检查

- 桌面端和移动端均无空折叠箭头或残留空白层级。
- 所有 Chapter 默认展开，手动状态和滚动位置继续持久化。
- 普通 Section 与隐藏页的父级高亮均正确。
- 父页链接可进入隐藏页，并可通过面包屑返回章、节阅读路径。

### 验证命令

```bash
python3 -m unittest scripts.test_optimize_literate_html scripts.test_literate_config
python3 scripts/check_repository.py
lake build :literateHtml
python3 scripts/optimize_literate_html.py <generated-site>
python3 scripts/check_literate_rendering.py <generated-site>
python3 scripts/generate_sitemap.py <generated-site> --base-url "https://tanktechnology.github.io/CLRS-Lean/"
```

## 预期改动面

- 导航可见性辅助模块或等价的共享函数
- `scripts/optimize_literate_html.py`
- `scripts/test_optimize_literate_html.py`
- `scripts/check_literate_rendering.py` 及相关测试
- 上述 11 个父级 `.lean` 页面中的文档链接
- `docs/site-architecture.md` 中的读者导航说明

不会修改证明声明、证明项、模块路径或部署触发条件。
