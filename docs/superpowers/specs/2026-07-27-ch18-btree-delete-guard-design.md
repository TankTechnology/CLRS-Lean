# Ch18.3 `composedDelete` 证明闭环设计（2026-07-30 修订）

> **状态：已完成。** 本文记录 2026-07-27 至 2026-07-30 的结构保持设计。结构保持与删除高度闭环由提交 `f3f61b4` 完成；精确删除语义随后完成，2026-07-31 又完成全章最小键数与对数高度界，当前进度为 `134/134`。

## 设计目标（历史）

本文在设计阶段的目标是关闭 Chapter 18.3 节点级 B-tree 删除实现周围的全部证明占位，
同时保持以下边界：

- 不弱化 `Sorted`、`ChildBounded`、`Occupancy`、`SameDepth` 或 `WellFormed`；
- 不把算法替换成恒等函数或规范层的列表删除；
- raw 节点删除仍使用已经实现的 CLRS 预修复分支；
- 公共根删除补上 CLRS 要求的 root contraction；
- 2026-07-30 的结构里程碑只证明结构不变量、raw 高度保持和结果 key 子集，不把当时
  尚未证明的精确删除语义伪装成已完成。精确语义后来已单独闭环。

## 设计阶段确认的五个契约/模型错误

设计起点中的 19 个 `sorry` 当时不能原样填补，因为外层定理中有四类假命题或缺失
前提，并且基础 `Occupancy` 定义遗漏了一项根节点特例。这 19 个缺口已由
`f3f61b4` 闭环；以下五项保留为契约修正的反例证据，而不是当前仓库的未完成项。

### 1. 无条件 key 子集为假

`maxKey` / `minKey` 在任意 `BTree` 上是总函数，沿空键后代读取时会得到 `getLast!` /
`head!` 的默认值。对不满足占用率的畸形树，case 1a/1b 因此可能把输入中不存在的
`0` 写入父分隔键。

所以 `keysOf_composedDelete_subset` 不能对任意树无条件成立。证明必须携带
`AllKeysPos`，或从完整的 `Occupancy` bundle 中派生它。

### 2. 非根占用率需要删除入口就绪条件

对 `t = 2` 和非根叶 `node [1] []`，输入满足 `Occupancy 2 false`，直接删除 `1`
后却只有 `0` 个键。父节点的预修复守卫管不到“直接调用这个非根节点”的场景。

正确的入口条件是：

```lean
def DeleteReady (t : Nat) (isRoot : Bool) (tr : BTree) : Prop :=
  isRoot = true ∨ t ≤ numKeys tr
```

所有递归调用都满足右支：直接下降由 guard 给出，borrow 后接收方有至少 `t` 个键，
merge 后有 `2 * t - 1` 个键；顶层根调用满足左支。

### 3. 占用率证明还需要同深条件

仅有 `ChildBounded + Occupancy` 仍允许相邻 sibling 一边是叶、一边是内部节点。
这种输入执行 borrow 会把一个孙节点搬进叶接收方，产生不合法的 children 数。
rotation 的占用率保持本来就依赖 sibling 等高，因此 `SameDepth` 是数学前提，
不是证明便利条件。

### 4. raw 根删除不保持现有 `WellFormed`

对 `t = 2`：

```lean
node [5] [node [1] [], node [9] []]
```

是 `WellFormed`。raw `composedDelete 2 5` 得到：

```lean
node [] [node [1, 9] []]
```

这正是 CLRS 删除的暂态空根，但它不满足本项目的 `Occupancy 2 true`：零键根只有在
同时没有 children 时才被允许。因此旧的
`WellFormed t tr → WellFormed t (composedDelete t x tr)` 为假，必须增加 root
contraction。

### 5. 内部根的 children 下界不能沿用非根的 `t`

原 `Occupancy` 只特殊处理了根的 key 下界，却对所有非叶节点统一要求至少 `t` 个
children。该定义在 `t > 2` 时错误拒绝标准 B-tree 根。例如 `t = 3` 时，一键、两个
最小叶孩子的内部根是合法的；而删除导致三孩子根合并为两孩子根后，算法结果也仍然
合法。

修正后的 children 下界是：

```lean
let childLower := if isRoot then 2 else minDegree
children.isEmpty ∨
  (childLower ≤ children.length ∧ children.length ≤ 2 * minDegree)
```

叶子继续由 `children.isEmpty` 分支放行，非根仍要求至少 `t` 个 children，暂态
`node [] [child]` 仍不属于普通 root occupancy，必须由 `normalizeRoot` 收缩。
这项修正不会弱化 CLRS 不变量；它补回了标准定义中根节点独有的下界。

## 保留并实施的算法语义

raw `composedDelete` 保持当前实现：

- 叶：`sortedRemove`；
- separator 命中：
  - 左 child 至少 `t` 个键：以前驱 `maxKey` 替换并递归删除前驱；
  - 否则右 child 至少 `t` 个键：以后继 `minKey` 替换并递归删除后继；
  - 两边都极小：merge 后递归；
- 普通下降：
  - child 至少 `t` 个键：直接下降；
  - 否则优先向可借 sibling 做 rotation；
  - 无 sibling 可借时 merge，再下降。

raw 函数对任意 `BTree` 保持 total；证明在良构输入上排除 lookup fallback 分支，
不依赖这些 fallback 的伪不变量。

## 结构保持契约（已实施）

### 输入 bundle

```lean
def NodeWF (t : Nat) (isRoot : Bool) (tr : BTree) : Prop :=
  Sorted tr ∧
  ChildBounded tr ∧
  Occupancy t isRoot tr ∧
  SameDepth tr

def KeysSubset (after before : BTree) : Prop :=
  ∀ k, k ∈ keysOf after → k ∈ keysOf before
```

### raw 根的暂态输出

```lean
def RootDeleteResult (t : Nat) (tr : BTree) : Prop :=
  Sorted tr ∧
  ChildBounded tr ∧
  SameDepth tr ∧
  (Occupancy t true tr ∨
    ∃ child, tr = node [] [child] ∧ Occupancy t false child)
```

### 一次性 bundled core（已实施）

核心归纳同时产出 key 子集、四类结构信息和 raw 高度，避免五份强归纳重复展开同一组
删除分支。最终实现在
[`ComposedPreservation.lean`](../../../CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ComposedPreservation.lean)
中由 `composedDelete_packet` 一次性给出，并通过
`composedDelete_nonRoot_preserves` 与 `composedDelete_rootResult` 投影。归纳 motive
量化实际递归删除键；case 1a/1b 会分别递归删除 `maxKey left` / `minKey right`，
固定外层 `x` 的旧 motive 不可用。

对非根公开：

```lean
theorem composedDelete_nonRoot_preserves
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hinv : NodeWF t false tr)
    (hready : t ≤ numKeys tr) :
    let out := composedDelete t x tr
    KeysSubset out tr ∧
    NodeWF t false out ∧
    heightOf out = heightOf tr
```

对根公开：

```lean
theorem composedDelete_rootResult
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    let out := composedDelete t x tr
    KeysSubset out tr ∧
    RootDeleteResult t out ∧
    heightOf out = heightOf tr
```

旧组件名作为这些 bundled theorem 的投影保留，并采用数学上正确的前提：

- subset / Sorted / ChildBounded 使用 `NodeWF`；
- occupancy 额外暴露 `DeleteReady`，并包含 `SameDepth`；
- SameDepth + raw height 使用 `ChildBounded + SameDepth`；
- key-bound wrapper 从有前提的 subset 投影，不再是无条件结论。

## 根规范化与公共删除（已实施）

```lean
def normalizeRoot : BTree → BTree
  | node [] [child] => child
  | tr => tr

def composedDeleteRoot (t x : Nat) (tr : BTree) : BTree :=
  normalizeRoot (composedDelete t x tr)
```

公开良构定理使用与 normalized operation 一致的名字：

```lean
theorem composedDeleteRoot_wellFormed
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    WellFormed t (composedDeleteRoot t x tr)
```

同时给出：

- `composedDeleteRoot_keys_subset`；
- `composedDeleteRoot_height`：输出高度等于输入，或恰好低一层；
- `Occupancy t false child → Occupancy t true child` 的 contraction bridge。

`composedDelete` 明确作为 raw node operation；`composedDeleteRoot` 是可对根调用的
CLRS algorithm operation。旧名 `composedDelete_wellFormed` 未保留，因为它会暗示
raw operation 保持 `WellFormed`，而该命题已有上面的反例。

## 原设计的证明分层

### 1. 索引与投影

先证明以下小引理，消去良构输入下不可达的 total-function fallback：

- 从 `NodeWF` 投影 child 的四个不变量；
- `findChild` 在内部良构节点的 children 范围内；
- `i > 0` 时 separator `ks[i - 1]?` 必然存在；
- 所需 sibling lookup 存在；
- guard 失败加 occupancy 下界推出 child 恰有 `t - 1` 个键；
- parent `SameDepth` 推出相邻 siblings 等高。

### 2. repair packets

显式导入 `Rotation.lean`，组合现有引理：

- merge：`mergeNodes_{sorted,childBounded,occupancy,sameDepth,height}`；
- rotation：占用率/同深/高度 bundled 引理，加 `Rotation.lean` 中 8 条
  Sorted/ChildBounded 引理；
- key：`mem_keysOf_mergeNodes`、`mem_keysOf_rotateLeft/Right`；
- 正键：`allKeysPos_*`、`maxKey_mem`、`minKey_mem`、`maxKey_ge`、`minKey_le`。

形成 merge、borrow-left、borrow-right 三个完整 packet。

### 3. parent reassembly

证明并复用：

- 单 child 替换；
- predecessor / successor 分隔键替换；
- 相邻 children rotation 后替换；
- merge 后 keys/children splice。

每个 packet 一次性组装 Sorted、ChildBounded、Occupancy、SameDepth、height 和 subset，
主归纳只负责编排语义分支。

### 4. 主归纳

原设计计划使用 generalized `Nat.strongRecOn`：

```lean
∀ x' tr' isRoot,
  heightOf tr' = n →
  NodeWF t isRoot tr' →
  DeleteReady t isRoot tr' →
  ...
```

该方案原本希望不直接使用 35 case 的 `composedDelete.induct`，并在良构前提下只保留
叶、separator 的三种分支、`j > 0` 的四种下降和 `j = 0` 的三种下降。最终实现改用
生成的 `composedDelete.induct`；这是实现相对设计最明确的偏差。

## 公共接口兼容（设计起点与结果）

设计起点的 Chapter 18 接口测试要求 12 个真实 `splitChild` wrapper；它们是早先从
identity stub 迁移到三参数实现时遗漏的独立问题，并非当前仍缺失的接口。最终实现已
恢复这些名称，签名显式包含 `minDegree`、child index 和 `Valid` 前提，证明由
`splitChild_keys_perm` 的键多重集置换推出；`Tests/Chapter_18_Interface.lean` 现已
锁定这 12 个公共名称。

## 实施结果与设计偏差

| 项目 | 实施结果 |
| --- | --- |
| 主归纳 | 原提案为 generalized `Nat.strongRecOn`；最终采用生成的 `composedDelete.induct`。 |
| bundled core | [`ComposedPreservation.lean`](../../../CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ComposedPreservation.lean) 中的 `composedDelete_packet` 同时给出 key containment、root-sensitive 结构结果与 raw 高度保持。 |
| 根规范化 | raw 根接口 `composedDelete_rootResult` 返回 `RootDeleteResult`；公共根删除 API `composedDeleteRoot` 经 `normalizeRoot` 收缩暂态空根，并由 `composedDeleteRoot_{keys_subset,height,wellFormed}` 封装。 |
| `splitChild` API | 12 个 wrapper 在设计起点缺失；现已恢复，并由 `Tests/Chapter_18_Interface.lean` 锁定接口。 |
| 精确删除语义 | 不属于原结构里程碑；随后按[精确删除语义计划](../plans/2026-07-30-ch18-exact-deletion-semantics.md)以 `keyBag` / `Multiset.erase` 完成，已不再是 remaining work。 |
| 删除高度 | `f3f61b4` 同时完成 raw 删除同深/同高保持，以及公共根删除高度不变或恰好减一。 |
| 全章高度 | 2026-07-31 的后续里程碑完成最小键数与对数高度界；[Chapter 18 当前状态](../../chapters/chapter-18.md)记录全章闭环，进度为 `134/134`。 |

## 验收记录

设计阶段要求回归覆盖：

1. `t = 3` 的一键、两孩子内部根满足 root occupancy，而对应非根形状仍受 `t`
   下界约束；
2. 非根最小叶反例证明旧 occupancy 契约不成立，并检查新 theorem 必须接收 ready；
3. 空键后代反例证明无条件 subset 不成立；
4. 单 separator 根 merge 后 raw 结果是暂态空根，`normalizeRoot` 后良构；
5. separator predecessor、successor、merge；
6. direct、borrow-left、borrow-right、merge-left、merge-right；
7. 12 个 `splitChild` 公共名称可用。

以下 Chapter 18 build/interface 检查仍可用于实现回归：

```bash
lake build CLRSLean
lake env lean Tests/Chapter_18_Interface.lean
lake env lean Tests/Chapter_18_Root_Occupancy.lean
lake env lean Tests/Chapter_18_Deletion_Interface.lean
lake env lean Tests/Chapter_18_Deletion_Exact_Interface.lean
lake env lean Tests/Chapter_18_Deletion_Root_Exact_Interface.lean
lake env lean Tests/Chapter_18_Height_Interface.lean
git diff --check
```

实现闭环时还对 headline theorem 执行了 `#print axioms`，确认不存在 `sorryAx`。
原设计门禁曾包含 `lake build :literateHtml` 的全站 HTML 生成；那是当时的文档发布
检查，不是本文归档后的当前验收要求。

## 原结构里程碑的语义边界（历史）

`KeysSubset` 只说明“结果没有凭空新增 key”，不等于精确删除语义。因此
2026-07-30 的结构里程碑没有声称已经证明：

- `x` 在结果中不存在；
- 每个 `y ≠ x` 的旧 key 都仍然存在；
- `keysOf` 与 multiset/list deletion 精确相等。

这些内容当时被明确留给独立的 semantic-correctness theorem，而不是结构不变量证明
的隐藏前提；随后已通过 `keyBag (composedDelete ...) = (keyBag ...).erase x` 及公共
根删除 wrapper 完成，当前仓库不再存在这项精确删除语义缺口。
