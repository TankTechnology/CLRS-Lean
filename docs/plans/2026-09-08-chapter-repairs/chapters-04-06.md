# 第 4–6 章修复与验证

对应 [#348](https://github.com/TankTechnology/CLRS-Lean/issues/348)、[#349](https://github.com/TankTechnology/CLRS-Lean/issues/349)、[#350](https://github.com/TankTechnology/CLRS-Lean/issues/350)。本地验证通过；尚未推送，因此远端 issue 保持开放。

第 4 章新增 `MatrixExecution`：标量叶操作、八乘法和 Strassen 执行都同时返回结果和计数。擦除计数得到原算法；八乘法计数等于旧预算，Strassen 的 18 次块加减令实际计数位于旧预算的 1–5 倍之间。对任意输入族，实际侧长 `2^k` 上分别证明 Θ(n³)、Θ(n^(log₂7))。2×2 非对称矩阵乘积、标量零值和两层计数都有回归用例；计数不含索引、分配或标量操作内部位成本，`padOne` 仅作单层嵌入。

整数平衡/不平衡树现在从实际生成树的总成本证明 Θ(n²)/Θ(n log n)，前提为正内部成本系数、非负基础成本。Master case 3 从 forcing 正则性推导尾部支配，不再把解的上界作为新接口的前提。Akra–Bazzi 的新接口覆盖全部非负 p、q，包括 p=0 和 p<q<p+1；仍明确保留单项式夹逼、单调性及 floor recurrence，未宣称一般扰动版本。

第 5 章将既有最长连续段上下界加入 §5.4 导读和公开检查，保留下界 n≥16 的条件。第 6 章更正文档：`ArrayMaxHeapFrom` 约束所有父节点 index≥start，强于仅约束 start 的后代子树。原定义和证明接口不变。

验证：第 4 章构建通过（8611 jobs），第 5–6 章构建通过（8616 jobs）；第 4 章四个新增语义/接口测试、原兼容接口及 trust 测试通过；第 5–6 章各自接口及 trust 测试通过。全库 `lake build CLRSLean` 通过（10706 jobs），`uv run python scripts/check_repository.py` 通过，`git diff --check` 通过。现有文档提示和 Verso 依赖工作区提示仍存在。

独立只读复核覆盖第 4 章所有新增证明及矩阵计数实现，未发现可执行的修正项；复核未重跑构建。构建和测试由实施侧完成。教材原文等价性仍未逐条独立验证；历史审查快照不随这些修复改写。
