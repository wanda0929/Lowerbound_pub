# Appendix E 外部流分解接口：文献核对与数学桥接

日期：2026-11-11。范围：`PolarAlignment.lean` 中的
`CZExposure.EuclideanCurrentSuperposition`，不是全论文或数值证书验收。

本说明给出从已发表定理到**当前接口全部字段**的普通数学证明。
它不构造该命题的 Lean 证明项，不把这里的论证冒充机器核验。
下游条件式 Lean 证明与这里的外部数学论证是两个不同层次。

## 1. 实际核对的来源及适用范围

**[PS]** E. Paolini and E. Stepanov, *Decomposition of acyclic normal currents
in a metric space*, J. Funct. Anal. 263 (2012), 3358–3390.
[DOI](https://doi.org/10.1016/j.jfa.2012.08.009)，
[作者全文 arXiv:1303.5664v2](https://arxiv.org/html/1303.5664v2)。
本次读取正文中的以下陈述及相关证明，不只读取摘要：

- §2.1、式 (2.1)：Lipschitz 路径的保向重参数化商空间 Θ 及其距离。
- Definition 3.1：子流的质量不抵消条件。
- Proposition 3.8：去掉一个子环流后得到无环流。
- Theorem 5.1：完备度量空间中的无环正规一维实流分解为弧；
  明确保证 Definition 4.4 的式 (4.3)、(4.4)。
- 式 (4.3)：总质量等于积分弧长；式 (4.4)：端点推前是边界的 Jordan 部分。
- Lemma 4.17、式 (4.14)：局部质量恒等式；式 (4.15)：Borel 局部化的流恒等式。
  本文只使用有界局部化函数，不需要把原文对任意 Borel 函数的写法
  解释成没有可积性要求的有限实数积分。

**[AK]** L. Ambrosio and B. Kirchheim, *Currents in metric spaces*,
Acta Math. 185 (2000), 1–80，Theorem 11.1 及证明，印刷页 68–70。
[原文 PDF](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6597-11511_2006_Article_BF02392711.pdf)。
这里实际需要的是**紧支撑正规流**的经典／度量表示互逆，不是所有有限质量流的互逆。
一般维度的定理陈述含质量比较常数；不能把它直接引用成局部质量相等。
下面第 3 节另证本问题的一维情形质量测度精确相等。

另使用通常的有限维测度论和曲线分析：有限 Borel 测度的 Radon 正则性、
Radon–Nikodym 定理、Lusin–Souslin 定理、Lipschitz 曲线的几乎处处可微性
及长度积分公式、Tonelli/Fubini 定理。它们不是新假设的流分解结论。
Lusin–Souslin 在固定 mathlib 中已有
`Measurable.measurableEmbedding`，文件
`Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`；
本说明没有声称已把下面整个参数化论证接成 Lean 证明。

## 2. 要推出的命题和输入没有遗漏的条件

令 E 为项目的十一维欧氏空间，V 为输入向量测度，μ=|V| 为全变差，σ 为输入极方向。
接口给出 μ(E)<∞、σ Borel 可测、σ 对 μ 可积、|σ|=1 μ-a.e.，以及 V=σμ。
存在紧集 K 使 μ(Kᶜ)=0。不同源汇记为 a、b，边界条件是

\[
\int \nabla\psi\cdot\sigma\,d\mu=\psi(b)-\psi(a)
\quad(\psi\in C_c^\infty(E)).
\]

这正是代码对光滑紧支撑测试函数的条件，而非预先给出的度量流结构。
一般 `boundaryPlus/Minus` 字段不保证 Jordan 性；在当前命题中
δ_b 与 δ_a 因 a≠b 互相奇异，故它们确实是该符号边界的 Jordan 正负部分。
以下构造对任意这样的输入成立，不只对曝光模型的某一个特例成立。

## 3. 向量测度成为正规流，且质量没有换掉

先定义经典一维流 T：对光滑紧支撑一形式 ω，令
T(ω)=∫⟨ω,σ⟩dμ。有限 μ 保证这是分布，且具有有限质量。
一形式的 comass 在一维就是欧氏对偶范数，因此 T 的经典质量测度等于 μ。
具体地，上界来自 |σ|=1；反向由在有限 Radon 测度下用光滑紧支撑向量函数
逼近可测单位极方向取得，或等价地由向量测度全变差的对偶刻画取得。
输入边界式给出 ∂T=δ_b−δ_a，边界质量为 2，所以 T 是紧支撑经典正规流。
正规流本身属于 [AK] 的 flat 类，不需要额外证明任意有限质量流的 flat 性。

由 [AK] Theorem 11.1 得对应的正规度量流 T̂；光滑形式的作用保持不变。
记其质量测度为 ν。原证明第 70 页给出局部测度不等式 ν≤μ，
不是仅给总质量估计。反向不等式在这里如下证明。

取任意单位向量 e。对光滑紧支撑标量 f，

\[
\widehat T(f\,d\langle e,x\rangle)
=\int f\langle e,\sigma\rangle\,d\mu,
\qquad
\left|\widehat T(f\,d\langle e,x\rangle)\right|
\le\int |f|\,d\nu.
\]

由有限 Radon 测度的正则性与光滑测试函数逼近，得
|⟨e,σ⟩|μ≤ν。令 λ=μ+ν，h=dμ/dλ、k=dν/dλ。
对单位球面一个可数稠密集同时去除零测集，有
h|⟨e,σ⟩|≤k；在 h>0 处 |σ|=1，取 e 的上确界即得 h≤k。
在 h=0 处该不等式自动成立。因此 μ≤ν，故 ν=μ。
这也证明**所有 Borel 区域**上的质量保持。

逆向也适用：紧支撑正规度量流经 [AK] 变成经典正规流，其一形式系数
由有限维 Riesz 表示给出向量测度；再用互逆性和上段论证，质量测度等于其全变差。
因此后续去环所得的两个正规流都可以返回项目的向量测度表示。
边界在转换中保持：先在光滑标量测试函数上验证，再由有限 Radon 测度的唯一性确定。

## 4. 去环、端点和局部质量

对 T̂ 应用 [PS] Proposition 3.8，得子环流 C 和无环流 S=T̂−C。
由 Definition 3.1、三角不等式及有限质量，

\[
\mathbb M(C)+\mathbb M(S)=\mathbb M(\widehat T),
\quad \partial S=\delta_b-\delta_a.
\]

这个等式还局部化：质量测度有 ν_T≤ν_C+ν_S，而两侧总质量相等；
差是总质量零的非负测度，故 ν_T=ν_C+ν_S。
所以 C、S 都支撑于 K。按第 3 节转回向量测度，记 S 对应 R，C 对应 V−R。
便有 |V|=|R|+|V−R|，特别满足代码 `IsVectorSubcurrent R V` 的全空间不等式。

对 S 应用 [PS] Theorem 5.1，得到 Θ 上的有限正 transport η：

\[
S=\int [\![\theta]\!]\,d\eta(\theta),\qquad
\int\ell(\theta)\,d\eta=|R|(E)<\infty,
\qquad (e_0)_\#\eta=\delta_a,\ (e_1)_\#\eta=\delta_b.
\]

η-a.e. 曲线是单射弧；η(Θ)=1 由任一端点律得到。
Lemma 4.17 给出每个 Borel B 的

\[
|R|(B)=\int \mu_{[\![\theta]\!]}(B)\,d\eta(\theta).
\]

单射弧的流质量是弧长测度。可直接看其单位速参数化：
参数上的单位切向量没有同一空间点的重复原像，故其推前向量测度
不会抵消，全变差就是 ds 的推前。具体地，单射连续路径从紧参数区间到其像
是同胚；空间像上的 Borel 分割与参数区间上的 Borel 分割互相拉回，
全变差定义中的分割上确界因此保持。参数侧全变差为 |γ′|ds=ds。
此处不能去掉单射条件。
由 B=Kᶜ 的等式可知几乎每条弧在 K 外的弧长为零。
其连续性和单位速参数化进一步说明整条弧都在闭集 K 内：
若某点在 K 外，相对开参数邻域也在 K 外，且该邻域有正长度，包括端点情形。

## 5. 可测单位速代表：不把逐条参数化当成可测选择

在 Polish 空间 P=C([0,1],E) 中定义 B₀ 为正长度、单射、恒弧长速度的
Lipschitz 路径集合。这里“恒弧长速度”指
len(c|[u,v])=(v−u)len(c)，而不是仅要求 Lipschitz 常数有上界。

**B₀ 是 Borel 集。** Lipschitz 路径集合是各整数 Lipschitz 常数闭集的可数并。
长度是有理分割对应的弦长和的可数上确界，因此是 Borel 函数；
限制区间长度也如此。只需在有理 u<v 上检查上述长度等式，
再用 Lipschitz 性延拓到所有端点。
单射性等价于对每个正整数 m，
min{|c(s)−c(t)|: |s−t|≥1/m}>0；这些最小值是 c 的连续函数。
再加 len(c)>0，得到 Borel 条件。因此 B₀ 是标准 Borel 空间。

令 Q:B₀→Θ 为取重参数化等价类的映射。
d_Θ(Qc,Qd)≤‖c−d‖∞，所以 Q 连续。
它单射：一条定向单射弧的累计弧长严格递增，归一化弧长参数唯一；
两条这样的恒速代表若等价，必处处相等。
它的像恰为非退化弧类：任意 Lipschitz 单射代表的累计弧长连续严格递增，
用其逆参数化就得到 B₀ 中的唯一代表。

Θ 在欧氏情形可分：有理顶点、有理折点的分段线性路径在一致距离中
稠密于 Lipschitz 路径，故其等价类在 d_Θ 中稠密。
把 Θ 等距嵌入它的完备化（一个 Polish 空间），对 Q 应用
Lusin–Souslin 定理，得 Q(B₀) 为 Borel，且逆映射 Q⁻¹ 在该像上 Borel。
因此不需要假定 Θ 本身完备，也不需要一个未经证明的“可测选择”。

将 η 限制到其满测度弧类集合，再经 Q⁻¹ 推前。
进一步限制到 c(0)=a、c(1)=b、c([0,1])⊂K 的集合 A。
这些条件在 P 中闭，因而 A 是 B₀ 的 Borel 子集；第 4 节说明限制不丢质量。
记所得概率测度为 ξ。源汇不同保证每个 c∈A 的 L(c)=len(c)>0。
这样 `arc` 对**每个**索引都有定义，不必在零测坏集上选择任意退化曲线。

对 c∈A 定义实参数停止延拓

\[
\gamma_c(s)=c\!\left(\min(1,\max(0,s/L(c)))\right).
\]

归一化恒速定义给出全局 1-Lipschitz，且在 [0,L(c)] 单射。
Lipschitz 曲线的可微性及长度积分公式给出 |γ′_c|=1 ds-a.e.：
任一子区间的长度等于其参数长度，而长度也等于 ∫|γ′_c|；
结合 |γ′_c|≤1，即得结论。两个端点是零测集，停止延拓在那里无需可微。
因此这恰好是 `EuclideanArc` 的全部条件。

L 是 Borel，P×[0,1] 的求值映射连续，所以 (c,s)↦γ_c(s) 联合 Borel。
端点映射分别为 c(0)、c(1)，可测且推前为 δ_a、δ_b。

重参数化保持定向流作用的具体换元如下。取原 Lipschitz 单射代表 θ，
令 l(t)=len(θ|[0,t])=∫₀ᵗ|θ′(u)|du，L=l(1)，
则 l 连续严格递增、绝对连续，θ(t)=γ(l(t))。
对任意 Lebesgue 零测集 Z⊂[0,L]，单调绝对连续换元给出
∫1_Z(l(t))l′(t)dt=0。
因此在 l′>0 处，γ 的不可微点的原像是零测集；通常的链式法则给出
θ′(t)=γ′(l(t))l′(t)。在 l′=0 处，|θ′|=l′=0，故同一式也成立，
其中可在 γ 不可微点将 γ′ 设为零。
对有界 Borel 向量 q 再次换元，得到

\[
\int_0^1\langle q(\theta(t)),\theta'(t)\rangle\,dt
=\int_0^1\langle q(\gamma(l(t))),\gamma'(l(t))\rangle l'(t)\,dt
=\int_0^L\langle q(\gamma(s)),\gamma'(s)\rangle\,ds.
\]

同样对非负 Borel 标量函数换元得到弧长推前测度保持；端点由定义保持。
这个证明允许原速度在正测度集上为零，不假设 l 的逆绝对连续。

## 6. 可测测度核和可测切向量

定义 m_c=(γ_c)_#(ds|[0,L(c)])。对任意 Borel B，

\[
m_c(B)=\int_{\mathbb R}
\mathbf1_{[0,L(c)]}(s)\mathbf1_B(\gamma_c(s))\,ds.
\]

被积函数联合可测且非负，故 c↦m_c(B) 可测。
测度空间的标准评价 σ-代数由这些评价映射生成；这证明
c↦m_c 本身可测，对应 `measurable_component`，不是只证明总长度可测。
第 4 节的局部等式经推前变为 |R|(B)=∫m_c(B)dξ(c)，
且 m_c 对每个索引就是 `lengthMeasure`。

取联合 Borel 差商
d_n(c,s)=n(γ_c(s+1/n)−γ_c(s))。
其收敛集由可数 Cauchy 条件刻画，故为 Borel；在收敛处取极限，其他地方置零，
得到联合 Borel 向量函数 v(c,s)。在路径可微处 v=γ′_c。
每条路径 Lipschitz，故对每个 c，在 [0,L(c)] 上几乎处处如此；且处处 |v|≤1。
这构造了 `MeasurableArcs` 所需的切向量，未假定其已与 σ 对齐。

对任意 Borel q:E→E、|q|≤1，

\[
P_q(c)=\int_0^{L(c)}\langle q(\gamma_c(s)),v(c,s)\rangle\,ds
\]

是可测函数，且 |P_q(c)|≤L(c)、∫L dξ=|R|(E)<∞。
因此 P_q 对 ξ 可积，在实数目标中也几乎强可测。
它与代码使用 `deriv` 定义的 `arcPairing` 相等：每条弧上只改了零测参数集。
这同时解决配对可测性和 Fubini 的绝对可积条件。

## 7. 从流形式恒等式到全部有界 Borel 向量测试

取光滑紧支撑 χ，在 K 的邻域上恒等于 1；取坐标 π_i(x)=x_i。
χ dπ_i 是合法的度量流测试。对任意 Borel B，在 [PS] (4.15) 中取
φ=1_B，得到

\[
R_i(B)=\int_A\int_0^{L(c)}
\mathbf1_B(\gamma_c(s))\,\gamma'_{c,i}(s)\,ds\,d\xi(c).
\tag{*}
\]

左侧的解释也有依据：光滑 f 的 χf dπ_i 由第 3 节识别为
向量测度的第 i 分量；有限 Radon 测度的唯一性使此识别延伸到 Borel 局部化。
χ 不改变任一项，因为 R 和全部所选弧都支撑于 K。

为避免把 (*) 的指标函数恒等式直接冒充任意 q 的恒等式，
在 A×ℝ 上定义有限正测度
dρ(c,s)=1_[0,L(c)](s)dξ(c)ds；其质量为 |R|(E)。
由第 6 节，联合位置 γ 和切向量 v 可测，且 |v|≤1。
故 N=γ_#(vρ) 是有限向量测度。
(*) 对每个坐标、每个 Borel B 说明 N=R。
向量测度积分的推前公式及有限和的线性性于是对所有有界 Borel q 给出

\[
\int\langle q,dR\rangle
=\int_A\int_0^{L(c)}\langle q(\gamma_c(s)),\gamma'_c(s)\rangle\,ds\,d\xi(c).
\]

也可以先对简单 q 验证，再以受控收敛延伸；绝对控制测度正是有限 ρ。
这不使用“光滑函数对任意 Borel 函数一致稠密”这种错误断言。

## 8. 余项的极分解与最终接口

令 W=V−R。有限维 Radon–Nikodym 定理逐坐标给出
W=r|W|，r 可取 Borel 代表。向量测度的变差密度公式
|r|W||=|r|·|W| 给出 |r|=1 |W|-a.e.。
若 W=0，取 r=0，单位条件对零测度真；不需要非零余项假设。
有限 |W| 也保证 r 可积。

由 V=W+R、输入 V=σμ 以及第 7 节，得对每个 Borel q、|q|≤1：

\[
\int\langle q,\sigma\rangle\,d|V|
=\int\langle q,r\rangle\,d|V-R|
+\int_A\operatorname{arcPairing}(\gamma_c,q)\,d\xi(c).
\]

三项都是绝对可积的有限实数积分。
这就是 `CurrentIdentity.current`，而不是仅光滑测试函数的版本。
第 6 节给 `pairing_measurable`，本节给余项方向三个字段。
此时 `CurrentIdentity.isDirected` 的现有 Lean 证明才推出切向对齐；
本论证没有预先假设对齐，也没有使用待证的物理脉冲或最优值等式。

## 9. 逐字段验收及结论边界

| 当前接口字段 | 数学出处／本说明中的证明 |
| --- | --- |
| 输入向量测度可应用 PS | 第 3 节；AK 11.1，加一维局部质量相等论证 |
| `retained`, `subcurrent` | 第 4 节；PS 3.8、3.1 及有限质量局部化 |
| `ensemble` | 第 4–5 节；PS 5.1 的 transport 经可测逆映射推前 |
| `arc` 的正长度、Lipschitz、单射、单位速 | 第 5 节，弧长参数化及长度积分公式 |
| `massDecomposition.component`, `measurable_component` | 第 6 节，联合可测推前核 |
| `localized`, `component_eq` | 第 4–6 节；PS 4.17 (4.14)，单射消除单弧抵消 |
| `measurable_initial/terminal`, `initial_law/terminal_law` | 第 2、4、5 节；不同 Dirac 的 Jordan 性及 PS (4.4) |
| `remainderDirection`, `remainder_measurable`, `remainder_unit` | 第 8 节，有限维极分解，包括零余项 |
| `pairing_measurable` | 第 6 节，联合差商、参数积分、逐弧零测集处理 |
| `current` 的所有有界可测测试 | 第 7–8 节；PS (4.15) 先给坐标测度，再作有限测度积分 |

因此，**所需外部命题有已发表定理加上述数学桥接的支持**，
不是仅把期望结论写成一个假设。引用 PS Theorem 5.1 一项仍然不够；
必须包含 AK 表示、去环、局部化以及本说明的可测参数化和积分转换。

这里的结论是文献支持及普通数学证明；**没有新增
`EuclideanCurrentSuperposition` 的 Lean inhabitant**。
现有下游 Lean 定理仍显式接收这一命题。第三档仍未完成。
本说明也不声称已经重新从基础证明 PS/AK 的全部原文定理，或取得外部专家审稿认证。

先前 `ConditionalAcceptance.md` 把简略对应说明写成第二档完整验收，
其文献桥接完成度被高估；本文件补的是此前遗漏的数学论证。
原有编译记录只能证明条件式 Lean 部分，不能作为本文件数学正确性的机器证明。

## 10. 本次核查记录

Amp 独立审计子代理只读核查了上述数学论证、六个相关 Lean 接口文件，
以及 PS 和 AK 原件；未发现阻塞性数学缺口或循环论证。
其审查正文版本（加入本节之前）的 SHA-256 为
`a0285b64b85ac2b15fc17379da45b8146a60a14a616cfa8bf2ea34d6414ff3f7`。
这是一项独立模型审计，不是外部专家签字或机器证明。

本次另在 `lean/appendix-e` 实际重跑：

- `lake build RequestProject`：退出 0，`Build completed successfully (8145 jobs).`；仍有原有 linter 警告。
- `lake env lean ConditionalAcceptanceAudit.lean`：退出 0，18 项 `PASS`；
  传递公理均仅为 `propext`、`Quot.sound`、`Classical.choice`。
  输出仍明确保留 `EuclideanCurrentSuperposition` 参数，不能以标准公理列表掩盖它。

核查的 `PolarAlignment.lean` SHA-256：
`3f5d08fd1cfc4b867716ede67cc2411c28459b354e35ff94f397e4969a69f70f`。
本次下载的 AK PDF SHA-256：
`5c1d0d461fb5cf7141197e4619d91d4e23a5291d4f3c3deae88b0d11b052fa68`；
PS HTML SHA-256：
`9d2be4908bf78485c68938fa10d01ce95493b55390f6e538b75484617850fee4`。
来源 URL 和具体定理定位见第 1 节；网页字节哈希仅用于标识本次读取版本。

本轮只新增／修正文档，没有更改 Lean 定理、目标定义、外部接口或论文正文。
因此验收结论是：文献到当前接口的书面数学桥接已补齐，条件式 Lean 验收再次通过；
外部存在性定理的 Lean 形式化仍未完成。
