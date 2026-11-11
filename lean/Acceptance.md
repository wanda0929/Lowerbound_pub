# 第一档验收：固定证书与逐字段清单

本档的含义是：**Lean 证明物理模型及上下界推理；明确列出的有限数据检查由外部程序完成。**
不是所有数值证书都由 Lean 内核重放，也没有无条件的 `Acceptance` 证明项。

最终入口为 `LowerBoundCZ.Certification.FixedArchive.lab_window`：
给定 `FixedArchive.Acceptance`，推出
**2.931287735220 ≤ labCstar < 2.935875225844105**。
`labCstar` 仍是实验室积分模型的物理目标；本次没有修改它、脉冲类或论文。

## 独立审计后的两项修复与重新验收

2026-11-10 的独立审计确认：旧 `--write` 可以用旧报告接受修改后的终端矩阵，
且 interface 的单位行权重条件未进入自动检查。旧版“第一档已完成”的判断因此暂缓。
本次分别以执行绑定记录和全量 `unitRows` 检查补齐，没有改动数值证书或物理模型。

独立子代理复核修复实现，未发现新的确认阻塞项；其复核不代替主线程实际运行。
随后主线程完成以下验收：

- `check_acceptance.py --replay ... --write` 成功：完整构建 8,262 jobs，八个 Lean 审计
  产生九份 dump；六类复用输入哈希全部匹配；四个外部对应检查全部成功。
- `acceptance-replay.json` 保存 13 个成功运行记录及源文件、证据和 dump 的绑定。
- 普通清单检查通过：65 个叶字段、290 个本地文件哈希匹配。
- `python -B -m unittest -v test_acceptance`：五项真实 CLI 测试全部通过，涵盖不变输入
  正例以及负终端对角元、改变界面行权重、改变报告和缺失执行记录的拒绝。
- 界面审计在全部 536 个 source 上验证单位行权重，并执行缩放和排列负例。

两项已知缺口已解决，按本文明确的第一档信任边界，本轮重新验收通过。
这不是没有任何未知缺陷的保证，也不是所有数值计算由 Lean 内核重放。
独立复核未逐行重新推导所有底层分析定理；本轮未重算全部昂贵数值证书。

## Archive 不再是任意输入

`FixedArchive.archive` 直接使用固定的 `RegionalData.sources`、
`InterfaceData.sources` 和新导入的 `ArchiveData.terminal`。
它只接收基底合法性的证明，不接收用户选择的矩阵。

- 五个 occupation cell：每个 153 个 moment 块、583 个 interval 块，共 3,680 块。
- 四个界面：每个 134 块，共 536 块。
- 五组终端证书：每组一个 8×8 矩阵和一个 7×7 矩阵，共 10 个矩阵、565 个完整条目。
- `FixedArchiveAudit.lean` 检查非空、charge、正规形、次数、零成本面或界面条件，以及相位和 localizer。
- `bind_archive.py` 比对所有 4,216 个使用列映射、所有终端条目及 75 个终端系数恒等式。
- `RawBlock.polynomial_eq` 是已有的内核证明：把原始块送入目标基底不会改变整个 Gram 多项式，包括非对角项。

`InterfaceDataAudit.lean` 还显式检查全部 536 个 source 的 `rows` 为单位行映射。
这对应 source checker 的单位列展开，不能仅由 used-column 索引相同替代。
审计同时要求缩放行权重及交换行的反例被拒绝。

原始证书 SHA-256：
`1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52`。
外部仓库固定于 `139dfc0aeb39fbc09d9352a3cbfcd603cb6612e2`。

## 65 个叶字段均有明确证据归属

下表列出 `Acceptance` 下的全部字段。重复族以集合表示；
`acceptance-manifest.json` 逐个展开 65 个完整字段名，并记录证据文件及源码哈希。
这些字段的状态统一称为 **external-evidence**，不是 Lean 的已构造证明项。

| 字段路径 | 数量 | 外部检查及证据 |
|---|---:|---|
| `layout.{moment,interval,interface}.{nonempty,keep,charge_eq,membership}` | 12 | 固定 Archive 的全块基底审计；`archive-binding.json`、`acceptance-evidence/archive-lean.txt` |
| `base.{moment_psd,interval_psd,interface_psd,terminal_psd}` | 4 | 原始全部 Gram 的 PSD 重放；`certificate-bindings.json`，经固定 Archive 对应使用 |
| `base.{drift,interface_identity}` | 2 | 全部 source 多项式精确恒等式；`source-identities.json`，经固定 Archive 对应使用 |
| `base.terminal_identity` | 1 | 五个终端限制多项式与矩阵系数的 75 项比较；`archive-binding.json` |
| `traversal.full.{width,join,start,bounds}`、`traversal.reached` | 5 | 全分区布局与 319 个已到达前缀；`acceptance-evidence/prefix-lean.txt` |
| `bootstrap.{gap,cap,identity,positive}` | 4 | 非循环 bootstrap、14 项恒等式和严格正系数；`prefix-binding.txt`、`prefix-lean.txt` |
| `endpoint` | 1 | 最终 321-profile 端点多项式及重标度恒等式；`endpoint-binding.txt`、`prefix-lean.txt` |
| `coverage.{grids,widths,local_bounds,endpoints,coefficients,assignments,discarded}` | 7 | 321 个 profile、23,088 个盒子：10,752 保留、12,336 排除；`coverage-lean.txt`、`coverage-binding.txt` |
| `allocation.source_psd` | 1 | 同一原始 Gram PSD 记录 |
| `allocation.domination` | 1 | 1,078 个投影、626 个原始块，384-bit Arb；`AllocationData/domination.json` |
| `allocation.{weights_nonneg,budgets}` | 2 | 所有权重和逐原始块预算；全数据解码检查与分配恒等式检查 |
| `allocation.{source_identity,tensor_identity,tensor_nonneg}` | 3 | `source-identities.json`、`allocated-identities.json`、`residual-correspondence.json` |
| `regional.widths` | 1 | 全部 9,728 区域的严格宽度；全数据解码检查 |
| `regional.blocks.{psd,domination,nonneg,budget}` | 4 | 原始 PSD；6,190 投影、3,171 原始块的支配检查；全部权重/预算 |
| `regional.{source_identity,tensor_identity,tensor_nonneg}` | 3 | 同上三个精确多项式/系数报告 |
| `interfaces.{source_psd,domination}` | 2 | 原始 PSD；530 个非零分配的支配检查，另 6 个零分配由源 PSD 支持；`InterfaceData.json` |
| `interfaces.{source_identity,tensor_identity,tensor_nonneg}` | 3 | 四界面 source、全部盒子恒等式、保留盒子系数符号；同上三个报告 |
| `upper.{radius_pos,duration_pos,contraction_nonneg,contraction_lt_one,defect_bound,krawczyk_interior,cz_branch,exposure_bound,jacobian_enclosure}` | 9 | 固定脉冲的区间 AD、Krawczyk 包含、分支和 exposure 包络；`certificate-bindings.json` |

表中未带前缀的文本记录位于 `acceptance-evidence/`；
`AllocationData/`、`RegionalData/`、`InterfaceData.json` 位于 `LowerBoundCZ/`。
物理轨迹的存在、模型压缩、必经前缀、crossing、积分总账及从这些字段到物理界的推理，
由 Lean 定理承担，不作为外部输入。

## 还需要信任什么

1. Python、python-flint/FLINT/Arb、外部区间算术与精确代数检查器。
2. Lean 可执行解码/审计程序及其结果与数学定义的对应；运行程序不等于内核证书。
3. residual 的完整组合式计算：共比较 11,370,496 个系数，检查其中需要非负的
   10,937,216 个。有限和重组仍属于外部边界，不是逐索引执行巨大 Lean 原式的内核证明。
4. 历史数值报告的来源与保存。解码重放绑定当前源码及程序，要求数值报告所用的
   potential、allocation、regional、interface、factor 和 archive 输入哈希完全一致；
   coverage 和两类 endpoint 的外部对应检查重新运行。原始 PSD、矩阵支配、
   上界区间计算和完整 residual 数值计算复用此前的报告，并非全部重算。

因此可称为“论文主界的第一档形式化：Lean 推理链 + 固定外部证书检查”。
不能称为“全部数值和解析步骤均由 Lean 内核无条件验证”。
进入后一档还需要把这些外部字段生成或证明为内核可检查的 `Acceptance` 实例；
不能通过新增公理、`sorry` 或信任报告字符串来完成。

## 复现与防止报告漂移

从 `lean/` 运行。Python 环境需要 python-flint；`PUBLICATION` 为上述固定版本的外部仓库。
完整的先前 source、allocation、residual、upper 重放命令见 `CertificateContracts.md`；
重新验收使用以下入口。源码、检查器或报告改变后，单独 `--write` 不再足以恢复通过。

```bash
python check_acceptance.py --replay "$PUBLICATION" --write
python check_acceptance.py
python -m unittest -v test_acceptance
```

`--replay` 顺序运行完整构建、八个 Lean 审计（九份 dump），再运行四个外部对应检查。
它在执行前后核对源码和旧数值报告没有漂移；只有所有命令成功、六类复用输入哈希完全
一致，才原子写入 `acceptance-replay.json`。该记录绑定所有本地 Lean 数据/定义、
Python 检查器、工具链配置、数值报告、日志及输出 dump 哈希。

不带参数的检查以及 `--write` 都必须先验证这份执行记录；`--write` 只汇总它，不能
自行给旧数值报告绑定新的源码。界面审计旧报告中的历史程序哈希保留不改；新程序增加了
单位行权重检查，其输出必须在新执行记录中证明与旧数值报告输入逐字节相同。

`test_acceptance.py` 在隔离副本上执行真实 CLI：保持数据不变时允许刷新并验证；
负终端对角元、改变界面权重、更换报告或缺少执行记录时，刷新必须失败且不改写清单。
执行记录仍是外部程序产物，不是数字签名或 Lean 内核证明；第一档信任检查器执行，
不声称能够防御同时恶意篡改检查器和全部证据的行为。
