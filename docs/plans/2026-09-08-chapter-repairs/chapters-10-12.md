# 第 10–12 章修复进度

第 10 章 [#352](https://github.com/TankTechnology/CLRS-Lean/issues/352)：合法容量/指针谓词、空构造器、成功更新保持；循环队列拒绝无效状态。`arrayEnqueue_tail_wraps` 增加合法状态前提，原函数签名不变。链表搜索补 none 完备性、首匹配前缀和最小下标，删除仍明确为全部相等值；rooted tree 改为第四版 §10.3。独立复核未发现问题，章节构建及新语义测试、trust 测试通过。

第 11 章 [#353](https://github.com/TankTechnology/CLRS-Lean/issues/353)：`sec_inj` 已限制于存储键，合法非成员碰撞实例及查询验证通过；trial 文档纠正为有限下截断。构造器/实际成本桥接仍在开发，尚未完成该 issue。

第 12 章 [#354](https://github.com/TankTechnology/CLRS-Lean/issues/354)：明确严格序/抑制重复的集合语义；`RepresentsW` 只约束 child structure 和 footprint，不保证存储的 parent 一致性。期望高度改为补充旧版主题，不作为第四版 §12.4。章节构建、原接口、期望高度接口及 trust 检查通过。

包含第 8、10、12 章修改及第 11 章域修复的全库 `lake build CLRSLean` 通过（10711 jobs）。后续构造器和第 13 章新改动须另行验证。本地结果尚未提交或推送，远端 issue 保持开放。
