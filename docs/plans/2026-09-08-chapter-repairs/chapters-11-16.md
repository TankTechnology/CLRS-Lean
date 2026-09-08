# 第 11、13–16 章修复与验证

关联 issues：[#353](https://github.com/TankTechnology/CLRS-Lean/issues/353)、
[#355](https://github.com/TankTechnology/CLRS-Lean/issues/355)、
[#356](https://github.com/TankTechnology/CLRS-Lean/issues/356)、
[#357](https://github.com/TankTechnology/CLRS-Lean/issues/357)、
[#358](https://github.com/TankTechnology/CLRS-Lean/issues/358)。

状态：本地已验证，待提交与远端集成。历史审查快照不改写，远端 issue 保持开放。

## 第 11 章

- `PerfectHashTable.sec_inj` 只要求已存储且属于相应主桶的键单射；允许未存储键碰撞。
- `PerfectConstruction` 实际分配主桶、一次缓存桶大小、尝试次级散列并返回成功的数组表。
  有限随机候选用尽时使用确定性单射 fallback，实际尝试数等于旧有限模型。
  候选按需读取；长度十亿的未使用后缀不会先被物化。
- 实际碰撞检查、空槽初始化、放置和组装的条件期望至多 `9 * constructionCost`，
  两层有限均匀期望小于 `45n`。旧 `<5n` 定理只界定抽象预算。
- 可以从返回的次级数组和桶内索引恢复原始 payload；没有证明任意原始键到桶内索引的
  常数时间逆映射或具体散列程序生成，也没有无限重试等待时间定理。
- 修正 open-addressing 文档的过时延期说明。

## 第 13 章

- 左右指针旋转重接根或旧父节点，并更新中间子树的 parent；保留另一父子链接和无关节点。
- `StoreReprAt` 要求非零节点、孩子 footprint 不交、排除根别名、符合记录的 parent；
  `Represents` 还要求哨兵未分配。证明树及 footprint 唯一性。
- 根、子树和任意深度上下文旋转都精化到函数式旋转。回归覆盖左右根、四种内部节点方向、
  中间子树、无效节点/孩子空操作，以及拒绝哨兵、循环、共享孩子、错误根 parent。
- `StoreRepr` 保留参数个数，但不再保留旧的宽松构造器 API；这是修复不健全表示所需的变化。
- 旋转的 6 是指针赋值上界；`insertCost/deleteCost` 明确为分析预算，未连接完整再平衡、
  join 或指针执行。函数式 `WellFormed` 插入、删除及精确成员性证明保留。

## 第 14 章

- 钢条切割的实际 bottom-up 数组填充共享前一数组，并返回候选次数 `n(n+1)/2`、
  写入次数 `n+1`；每个存储值精化到旧收入规范。已有 top-down 缓存值正确性保留，
  新计数没有被宣称为 top-down 执行计数。
- LCS 逐行只读取已算好的前驱，完整行不变量精化到旧递归规范；实际访问
  `(m+1)(n+1)` 个边界/内部单元格。旧递归重建不享有该运行时间界。
- 矩阵链与 OBST 使用按区间长度追加的数组行，记录代价及分割点/根；重建只读取
  存储的选择器。OBST 权重每区间只用前一权重计算一次。
- 公共 `DPExecution` 给出依赖顺序不变量、实际访问状态无重复、写入/候选计数，
  由上述两种区间算法实例化。`2*cells=(N+1)(N+2)`、
  `6*candidates=N(N+1)(N+2)`，并有对应二次/三次双边界。
- OBST 仅使用非负整数权重；没有任意实数概率或缩放桥。所有计数明确排除底层位运算、
  持久结构复制、分配及最大栈/堆占用。

## 第 15–16 章

- 空缓存核心第一次载入后容量恒为 1，补充通用定理。一般容量的 fill 成本、resident
  和 suffix 是给定参数，不能解释成已经实现任意容量的空启动。
- 混合栈执行返回最终状态、逐条命令移除值及实际 push/pop/command 计数。精确守恒式
  `finalSize+pops=initialSize+pushes` 推出空栈总弹出数不超过成功压入数；按命令和
  压入/弹出单元收费的总 work 至多 `3n+initialSize`。

## 验证

- `lake build CLRSLean`：成功，10,724 个任务。
- 11/13/14/16 既有公共接口，11/13/14/15/16 trust 检查全部成功。
- 新 perfect-hash、pointer-rotation、LCS、rod、interval-DP、mixed-stack 回归成功；
  空缓存接口与容量定理检查成功。
- `uv run python scripts/check_repository.py` 与 `git diff --check` 成功。
- 独立源码复核覆盖完全散列、LCS/rod、空缓存/混合栈；旋转和区间 DP 逐项检查了
  实际状态及同一执行计数。既有 Verso 文档提示不影响构建结果。

教材原文仍未逐条独立核对（NOT-INDEPENDENTLY-VERIFIED）；修复闭合不等于整本教材
所有算法、习题或机器级实现已形式化。
