# Appendix E：第二档条件式验证与第三档完整证明

## 验收边界

本文记录两档目标、原工期估算、外部输入的逐字段说明，以及第二档的验收入口。
它只涉及 Appendix E，不等于整篇论文或固定数值证书的验收。
不修改论文正文，不把文献引用当成 Lean 证明项。

**2026-11-11 文献桥接补正：**此前本文件的简略对应说明不足以支持
“文献到接口的数学核查已经完成”。完整的逐字段数学论证现另见
[外部流分解接口：文献核对与数学桥接](ExternalSuperpositionJustification.md)。
该说明核对 AK 11.1、PS 3.8/5.1/4.17，并补出一维局部质量保持、
可测单位速代表、测度核及全部有界 Borel 向量测试的转换。
下文保留历史编译结果；它们验证条件式 Lean 证明，不验证这份外部数学论证。

**第二档：**在明确列出的外部流分解假设下，Appendix E 自己的推导经 Lean 验证。
本档选择的外部输入是 `CZExposure.EuclideanCurrentSuperposition`：
有限维向量测度版本的弧分解，包含参数化、局部质量与向量积分恒等式。
这些组成部分全部在外部边界内，不声称只假设文献 Theorem 5.1 原文便已完成所有转换。
本档不要求证明该命题存在一个 Lean inhabitant。

**第三档：**进一步在 Lean 中证明上述外部输入，最终结论不再接收它，
也不依赖替代它的自定义公理。允许 Lean 标准基础公理
`propext`、`Classical.choice`、`Quot.sound`。
不必建立适用于所有度量空间的通用几何测度论库。

## 工期估算：规划范围，不是交付承诺

以下为核查后给出的历史规划估算，一人日指熟悉本项目、Lean 和相关数学者的有效工作日。
它们不是实测工时，不能以此推断现有实现还缺同样数量的工作。
现有条件式连接已比原计划充分，第二档本轮主要任务是收拢正式入口、说明边界并重新验收。

| 第二档任务 | 原估算 |
| --- | --- |
| 2.1 固定外部陈述，逐字段核对文献，说明原定理和组合推论的区别 | 2–4 人日 |
| 2.2 接到方向一致性、物理实现、证书和最终收敛；核对量词和有限性 | 1–3 人日 |
| 2.3 传递依赖审计、完整构建及验收 | 2–4 人日 |
| 合计 | 5–11 人日，约 1–3 工作周 |

第三档按直接处理本项目有限维向量测度的路线估算，不把通用度量流库作为前置项目。

| 第三档新增证明 | 原估算 |
| --- | --- |
| 3.1 连续流的有限／多面体近似，同时控制流、质量、边界与分解所需条件 | 20–40 人日 |
| 3.2 近似路径测度的紧性、极限提取、长度控制及质量不逃逸 | 15–30 人日 |
| 3.3 极限保留原流、局部质量及源汇边界，排除抵消或质量损失 | 20–40 人日 |
| 3.4 可测单位速参数化、停止延拓及实际弧族构造 | 10–20 人日 |
| 3.5 有界可测向量测试函数积分恒等式、剩余环流的极分解、接口拼接 | 5–12 人日 |
| 3.6 无外部输入的最终定理、去除旧公理依赖及全链验收 | 3–7 人日 |
| 新增证明合计 | 73–149 人日 |
| 加上第二档原规划 | 78–160 人日，单人约 4–8 个月 |

第三档估算置信度低，尤其 3.1–3.3；路线选择可能改变项目之间的划分。
没有足够证据给出可靠的逐项完成日期。

## 已有证明：不重复计为待办

- 本系统局部可控性：有限脉冲、交换子、带符号根 C¹ 曲线、六维逆函数定理及统一四次根时长界。
- 端点修复、闭合脉冲存在、物理 `Cstar` 有限性。
- 多元 Bernstein C¹ 逼近、统一阶数与盒子缩放。
- 标量及矩阵正性表示、严格余项修正及矩阵 SOS 合成。
- 保边界去环、有限图路径分解、有限路径几何实现。
- 从完整质量和向量积分恒等式推出弧切向与母流极方向一致：
  `EuclideanCurrentArcData.CurrentIdentity.isDirected`。
- 从该方向一致性接到曝光时间轨迹、物理脉冲、上下最优值相等及最终收敛。

有限图结果本身不构成连续流分解存在性证明。

## 外部假设的完整数学边界

代码入口：`RequestProject/AppendixE/PolarAlignment.lean` 中的
`EuclideanCurrentSuperposition`；验收脚本打印它及所有组成结构的完整声明。

### 输入：任意满足以下条件的流

固定空间是本项目的十一维欧氏曝光空间 `ExposureEuclidean`。
`EuclideanNormalCurrentData` 给出：

1. 有限全变差的向量测度 `vectorMeasure`。
2. 可测、可积、全变差几乎处处单位长度的极方向 `direction`，且
   `vectorMeasure = vectorMeasure.variation.withDensityᵥ direction`。
3. 有限正边界测度 `boundaryPlus`、`boundaryMinus`，对所有光滑紧支集测试函数满足分布边界恒等式。
4. 当前外部命题另要求源汇不同、正边界为汇点 Dirac 测度、负边界为源点 Dirac 测度，
   并要求全变差紧支撑。

该结构不是 Ambrosio–Kirchheim 度量流的定义。一般的正负边界字段未声明为 Jordan 分解；
在此特例中不同源汇的两个 Dirac 测度互相奇异，因而与相应符号边界的 Jordan 部分一致。
这个文献对应解释不是新增的 Lean 度量流转换定理。

### 输出：分解及恒等式，而非物理结论

存在索引类型及可测结构、弧族和 `D : EuclideanCurrentArcData T source sink A`，满足：

| 字段 | 精确内容 | 第二档归属 |
| --- | --- | --- |
| `retained`, `subcurrent` | 保留向量子流，无质量抵消意义下的子流关系 | 外部输入 |
| `ensemble` | 弧的分布测度 | 外部输入；概率性由端点律导出 |
| `massDecomposition.component` | 可测的分量测度核 | 外部输入 |
| `massDecomposition.localized` | 对每个可测集合，保留流全变差等于分量测度的积分 | 外部输入 |
| `arc`, `component_eq` | 几乎每个分量是实际弧的弧长推前测度 | 外部输入 |
| `EuclideanArc` | 正长度、全局 1-Lipschitz 路径、有效区间上单射、几乎处处单位速导数 | 外部输入 |
| 起终点可测性及 `initial_law`、`terminal_law` | 起终点推前分别为源点和汇点的 Dirac 测度 | 外部输入 |
| `CurrentIdentity.remainderDirection` | 母流减去保留流的余项，具有可测、几乎处处单位的极方向 | 外部输入 |
| `CurrentIdentity.pairing_measurable` | 对每个可测且范数不超过 1 的向量测试函数，弧配对关于索引几乎强可测 | 外部输入；已有可测弧族可构造此字段 |
| `CurrentIdentity.current` | 对全部上述测试函数，母流配对等于余项配对加弧配对的集合积分 | 外部输入 |
| 弧长度与配对的可积性、质量总账 | 由上述字段导出 | 已有 Lean 证明 |
| 母流极方向与弧切向一致 | `CurrentIdentity.isDirected` | 已有 Lean 证明，不额外假设 |

`EuclideanArc` 本身没有要求有效区间外恒定；`ArcSpace` 提供停止延拓表示。
外部数学桥接现从恒弧长速度单射路径的 Borel 子集构造可测代表，
再构造停止延拓、测度核、端点及配对；没有把可测选择另列为未证数学假设。
这些构造尚未在 Lean 中实现，仍属于下游 Lean 定理的外部输出接口。

外部输入**不包含**：成功物理脉冲、成本界、局部可控性、`Cstar ≤ pRelaxed`、
光滑次解、SOS 证书或任一最终收敛结论。
因此不是把 Appendix E 的待证结论重新包装为假设。

## 文献逐项对应与没有形式化的转换

核查来源：Paolini–Stepanov,
*Decomposition of acyclic normal currents in a metric space*，
[arXiv:1303.5664v2](https://arxiv.org/html/1303.5664v2)，
[期刊 DOI](https://doi.org/10.1016/j.jfa.2012.08.009)。

| 组成部分 | 文献依据 | 对应说明与边界 |
| --- | --- | --- |
| 去环并保留边界 | Proposition 3.8 | 本地另有去环证明；外部命题的保留流可由此与弧分解组合取得 |
| 无环流分解成弧 | Theorem 5.1 | 空间完备；有限维欧氏空间满足，且为 Polish 空间，无需另加 Ulam 型集合论假设 |
| 保留流的总质量等于积分弧长 | Definition 4.4，式 (4.3)，由 Theorem 5.1 保证 | 配合弧单射性排除单弧抵消 |
| 起终点律 | Definition 4.4，式 (4.4) | 文献使用边界 Jordan 部分；本项目源汇不同，见上文 |
| 局部质量而非仅总质量 | Lemma 4.17，式 (4.14) | 对应全部可测区域的 `localized`；不能仅以总质量相等代替 |
| 局部流积分 | Lemma 4.17，式 (4.15) | 桥接说明第 7–8 节从坐标向量测度等式推出全部有界 Borel 测试；尚未形式化 |
| 欧氏向量测度与度量正规流 | Ambrosio–Kirchheim Theorem 11.1 原文 pp.68–70 | 本次直接核对原文；桥接说明第 3 节另证一维局部质量保持，尚无 Lean 同构 |
| 单位速可测代表 | PS §2.1，加 Lusin–Souslin 与弧长参数化 | 桥接说明第 5–6 节构造可测代表、停止延拓及测度核；不是 Theorem 5.1 的逐字陈述，尚未形式化 |

数学翻译的依据是：有限维向量测度逐坐标确定；对局部化的坐标微分形式使用流恒等式，
再由有限质量和可测函数逼近扩展到有界可测向量测试函数。
去环后保留流和余项的极分解给出 `CurrentIdentity.current` 中的两个部分。
单位速参数化不改变弧长测度、流作用及端点；零长度弧不承载不同的源汇端点。
这些是所采用外部组合推论的数学说明，**不是声称本项目已经用 Lean 证明了这些翻译**。
第二档的结论必须以完整组合推论为条件，不能缩写成“Lean 已从 PS5.1 原文推出全部结论”。

## Lean 库核查范围

- 本地 Lean/mathlib 为 v4.28.0；mathlib 固定提交为
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365`。
- 对作者名及 normal/metric/polyhedral current 的源码搜索未找到所需分解存在性证明。
  这不是“所有公开库都不存在”的断言。
- 检查了公开项目
  [metric-surgery-lean 固定版本](https://github.com/Inspectordaniel/metric-surgery-lean/tree/91c2fc65884c9b284fdc6ba4071aa63c12ded471)。
  `Tablet/PaoliniStepanovExists.lean` 明确把 `PaoliniStepanovExistsStatement E`
  定义为使用者须提供的命题，不证明它。
  其接口针对零边界流，不能直接替代本项目的源汇流接口。
  它使用 Lean v4.33.0、Apache-2.0 许可；本轮只读检查源码，没有编译或导入它。
- 仅看到标准公理列表，就认为它给外部假设“提供了证明”，是错误的：
  定理可以把一个尚未证明的命题作为显式参数，仍只依赖标准公理。
  本验收同时检查**定理类型和传递公理依赖**。

## 正式第二档入口与论文对应

模块：`RequestProject.AppendixE.ConditionalAcceptance`。
全部定理显式接收 `h : EuclideanCurrentSuperposition`，不实例化旧 `External` 公理。

| 论文结果 | 第二档入口 |
| --- | --- |
| 物理与松弛最优值相等 | `ConditionalAcceptance.relaxed_equality` |
| 光滑次解引理 | `ConditionalAcceptance.smooth_bounds` |
| 任意 ε 精度的有限阶多项式证书 | `ConditionalAcceptance.certificates` |
| 驻定层级单调界及收敛 | `ConditionalAcceptance.stationary` |
| 固定分区单调界及收敛 | `ConditionalAcceptance.partitioned` |
| 具体实矩阵驻定程序的有限实数 ε 结论 | `ConditionalAcceptance.concrete_stationary` |
| 具体实矩阵分区程序的收敛 | `ConditionalAcceptance.concrete_partitioned` |

分区结果额外保留论文原条件 `∃ γ : Pulse, γ.exposure < U`，即有成功脉冲严格低于选定上限。
这是定理适用条件，不是新的未证明通用数学定理；不能由“存在某个成功脉冲”直接抹掉。
阶数范围为正整数，系数为实数，完整多项式空间；不声称有限阶精确取到物理最优值。
具体程序与抽象程序各有收敛证明，不靠未证明的可行域相等。
固定数值证书、序列化 Gram 数据、软件求解器及论文其余附录不在这一验收范围。

## 可复现验收

在 `lean/appendix-e` 目录执行：

```sh
lake build RequestProject
lake env lean ConditionalAcceptanceAudit.lean
lake env lean CompletenessAudit.lean
lake env lean PolarAlignmentAudit.lean
lake env lean ExposureArcAudit.lean
```

`ConditionalAcceptanceAudit.lean` 打印完整外部接口和最终定理类型，
并对最终结论与关键连接递归执行 `Lean.collectAxioms`。
任何不在 `propext`、`Classical.choice`、`Quot.sound` 中的公理都会使验收失败，
包括 `sorryAx` 和 `External.euclideanDirectedArcSuperposition`。
旧便捷包装仍可包含该公理；验收声明针对上述条件式入口，不声称整个源码树不存在公理。

### 本轮执行记录

**历史记录：条件式 Lean 部分通过。** 当时实际完成以下检查；
不能由这些执行结果推断当时已经完成文献到接口的数学桥接：

| 检查 | 实际结果 |
| --- | --- |
| `lake build RequestProject` | 退出 0；`Build completed successfully (8143 jobs).` |
| `lake env lean ConditionalAcceptanceAudit.lean` | 退出 0；18 个指定声明的传递公理检查全部 PASS |
| `lake env lean CompletenessAudit.lean` | 退出 0 |
| `lake env lean PolarAlignmentAudit.lean` | 退出 0 |
| `lake env lean ExposureArcAudit.lean` | 退出 0 |
| 旧公理注入反例 | 构造依赖 `External.euclideanDirectedArcSuperposition` 的无参数最优值等式；同一允许列表检查以非零退出拒绝，并准确报告该公理 |

18 个检查结果均只包含 `[propext, Quot.sound, Classical.choice]`。
反例仅用于临时验证，未放入正式库。
构建包含原有 linter 警告，不将“构建成功”描述为“没有警告”。
这不是一次从零独立重证或外部审稿人的签字；是本轮实际执行的类型、编译及传递依赖验收。

完整类型输出同时确认：`Pulse` 使用有限实数时长、可测单位圆控制、积分动力学及精确终端闭合，
`Cstar` 是这些物理脉冲曝光的下确界；未替换目标定义。
分区结论的上限见证仍在类型中。

本轮验收源码快照：按相对路径排序，对 `RequestProject/**/*.lean`、根目录 `*Audit.lean`、
`lean-toolchain`、`lakefile.toml`、`lake-manifest.json` 共 175 个文件，依次连接
UTF-8 相对路径、NUL 字节、文件内容 SHA-256 的二进制摘要，再计算 SHA-256：

`c85cf6a92bb2f74cef7f9c1516fac07b87f0fa20b35324cb1178282657ec7941`

入口源码 SHA-256：
`52eaa9d1ce6e4b1b6ab8a7a4ec769759850dbf7bd86788d0c137ae2951236486`。
验收脚本 SHA-256：
`f18355c51039e2ee305057312728b1d32eac0731746ed4fc944e20580a9cb5b3`。

当时已完成 2.2 条件式最终接口、2.3 构建与依赖审计；
2.1 中的外部接口已有完整声明，但文献转换只有简略说明，原完成判断过强。
2026-11-11 的桥接说明补充了该项的普通数学证明，没有把它说成 Lean 证明项。
当时没有修改论文或为流分解新增公理；该次记录时尚未提交或推送代码。

### 通过后可使用的准确表述

> Appendix E 的物理／松弛最优值相等、光滑次解、多项式证书及驻定／固定分区收敛，
> 已在明确列出的有限维正规流弧分解假设 `EuclideanCurrentSuperposition` 下经 Lean 验证。
> 该外部输入由已发表定理及另附的逐字段数学桥接支持，包含所需参数化、局部质量与向量积分恒等式；
> 其存在性及桥接论证未在本项目中形式化。
> 固定分区结论保留成功脉冲严格低于上限的原条件。

不能改写成“Appendix E 无额外数学假设的完整形式化证明已经完成”。

## 第三档推进记录：有限路径测度，不是连续流分解

第二档上面的源码摘要和执行记录是其验收时的历史快照。
后续新增 `FinitePathMeasure.lean`，将有限图路径列表实际构造成
`Measure StoppedPathSpace`，而不是仅保留形式加权列表。
已证明任意实值测试函数的有限积分公式、源汇端点积分公式、
时长积分等于逐边几何长度总账、总质量等于总源质量，
以及总源质量为 1 时该测度为概率测度。

验证：`lake build RequestProject` 成功（8144 jobs）；
`lake env lean FinitePathMeasureAudit.lean` 成功，8 项传递公理检查
仅包含 `propext`、`Quot.sound`、`Classical.choice`。
新文件没有 `sorry` 或新增公理，未改写最终分解假设。

这只推进七项清单中的第 2 项，不能宣布第 2 项整体完成，更不能宣布第三档完成。

| 第三档任务 | 当前剩余 |
| --- | --- |
| 1 连续流有限几何近似 | 未构造；需同时控制流、质量、边界，并处理无环化后的几何有限性 |
| 2 有限图的测度／流总账 | 已有实际有限路径测度、端点积分及总长度；尚缺完整局部质量与向量流恒等式 |
| 3 极限测度 | 有紧性工具，未对所需近似序列完成极限构造 |
| 4 极限保持质量和流 | 未完成；不能用一阶矩有界代替长度加权尾部控制 |
| 5 极限路径成为可测简单单位速弧 | 未完成；简单性与单位速度不自动在路径极限下保留 |
| 6 填满一般流的 CurrentIdentity | 未完成；已有配对可测性工具与由该恒等式推出方向一致性的证明 |
| 7 消除最终外部参数 | 未完成，依赖前六项 |

再次读取 Paolini–Stepanov Appendix C 的 Lemma C.1 及证明后，
第 1 项的具体阻塞更明确：原证明不仅用平滑化和线段离散化，
还用 flat-norm 控制下的小质量边界修正，并在去环后证明近似仍为多面体流。
目前没有完成这些步骤的本地 Lean 证明；本轮也没有通过假设一个这样的近似序列来掩盖缺口。
现有有限图结果和 Prokhorov 工具不能直接补足它们。

### 第一项的新增子证明：有限原子边界修正

依据 Paolini–Stepanov Lemma C.1 的 Step 2，新增
`RequestProject/AppendixE/AtomicBoundaryCorrection.lean`。
对给定的有限配对 `(wᵢ, xᵢ, yᵢ)`，实际构造加权有向线段向量测度 `Y`，证明：

- 对每个光滑紧支集标量测试函数，作用于其梯度得到
  `∑ᵢ wᵢ ψ(yᵢ) − ∑ᵢ wᵢ ψ(xᵢ)`；这是修正的分布边界公式。
- 局部常值一形式的作用等于对同一向量测度在该可测区域的取值施加线性泛函。
  因而边界作用不是与质量估计无关的另造函数。
- 全变差质量不超过 `∑ᵢ |wᵢ| ‖yᵢ−xᵢ‖`；同时证明局部全变差支配、有限质量和紧支撑。
- 单段的向量积分为 `y−x`、质量为 `‖y−x‖`；零长度段直接构造为零流。
- 若每个原子的位移不超过 ε，质量不超过 ε 乘总绝对权重。
- 对原子数允许增长的序列，若上述搬运成本趋零，修正流的质量趋零。

支持负权重、重复／重合端点与线段间抵消；质量使用上界而非错误地声称无抵消的等式。

验证：`lake build RequestProject` 成功（8145 jobs）；
`lake env lean AtomicBoundaryCorrectionAudit.lean` 退出 0，17 项传递公理检查通过。
额外检查零长度段以及不对称有符号权重、反向线段的向量积分，均通过。
无新增公理、`sorry`，没有改写最终弧分解输入。

**限制：这还不是 Lemma C.1 的 Step 2 全部，更不是第一项全部。**
原文用 Federer 4.2.23 从小 flat-norm 边界误差取得小质量修正；本轮只完成
给定有限配对时的显式修正与估计，没有证明这种低成本配对必然存在，
也没有证明任意连续流的初始多面体近似及其无环化。
这些存在性问题仍是第一项的剩余工作，不能用本轮的条件式估计替代。

### 第一项续进：构造有限空间离散化，2026-11-11

新增 `RequestProject/AppendixE/CompactQuantization.lean`，本轮证明的最强入口为
`CompactQuantization.exists_current_sampling`。从任意
`EuclideanNormalCurrentData` 的紧支撑出发，实际构造可测有限值映射序列 qₙ：

- 在紧支撑 K 上，qₙ(x)∈K，且 dist(x,qₙ(x))<1/(n+1)。
- 有限向量系数为原向量测度在互不相交网格单元上的取值，
  其范数总和不超过原流质量。
- 对每个连续一形式 ω，有限和
  `∑ z ∈ (q n).range, ω z (T.vectorMeasure (q n ⁻¹' {z}))`
  收敛到原流 `T.action ω`。同一序列同时适用于所有这些测试形式。
- 正测度推前确实是有限 Dirac 和，保持总质量与紧支撑；证明了
  Lipschitz 测试的定量误差界、连续测试的积分收敛及趋零搬运成本。
- 对紧支撑中总绝对权重一致有界的有限有符号原子序列，
  构造其网格化线段修正并证明修正质量趋零，允许原子数随 n 增长。
  这里无需额外假设配对位移小；位移界来自实际构造的 qₙ。

验证：`lake build RequestProject` 成功（8146 jobs）；
`lake env lean CompactQuantizationAudit.lean` 退出 0，15 项传递公理审计通过，
只包含标准基础公理。测试包括空支撑、非单位且不等的原子权重合并，以及带方向的积分误差。
新模块没有新增公理或 `sorry`。

**第一项仍未完成。** 上述有限向量系数不是有限线段组成的正规一维流；
该采样证明没有使用输入的分布边界字段，因而不能推出边界质量控制。
范数总和的上界也不是质量收敛。剩余关键步骤是构造保留流与边界控制的
有限线段／多面体近似，证明严格质量逼近和所需边界收敛，
再处理小质量边界修正以及无环化后保留有限几何结构。
本轮没有以弱向量采样替代这些步骤，未改变第二档外部接口或第三档验收标准。

### 第一项后续：实际有限线段的弱逼近

`ShortSegmentApproximation.lean` 将每个向量系数 v、位置 x 实现为
从 x 到 x+h·v 的实际线段，权重为 1/h（h>0），不是点向量测度。
已证明单线段作用误差、有限和误差、质量上界及精确端点边界公式。
`exists_segment_sampling` 从紧支撑原流直接构造同一有限线段序列，
对所有 Lipschitz 一形式作用收敛，且每个近似流的质量不超过原流质量。
误差估计为 C·h·M²，其中 C 是测试形式的 Lipschitz 常数，
M 是原流质量；没有把近似序列的存在作为输入。

**这仍未完成第一项。** 精确端点公式含有 1/h 权重；
上述构造没有给出边界总变差的一致上界，更没有证明边界正负部分收敛。
不能把光滑梯度测试下的边界收敛当作这些更强结论。
尚缺严格质量收敛、flat 收敛、边界正负部分的弱收敛，
以及无环目标所需的无环多面体近似。
后续必须补上能同时控制边界的近似构造，或证明相应小质量边界修正的存在；
仅继续缩短这些互不连接的线段不足以获得该控制。

本模块没有新增公理或 `sorry`；`ShortSegmentApproximationAudit.lean`
检查六个公开结论的传递公理，并检查零位移和保留符号的常一形式作用。
这些结论不构成 `EuclideanCurrentSuperposition` 的 Lean 证明项，
第二档的条件式验收及外部文献支持的信任边界保持不变。
