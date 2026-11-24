# 零拓扑熵符号障碍、离散流体输运与有理底 $p/q$ 的定量 Weyl 衰减

- **作者**：Su MingKai
- **代码仓库**：<https://github.com/3y3y3y-huaiji/mahler32>
- **Zenodo DOI**：[10.5281/zenodo.24491265](https://doi.org/10.5281/zenodo.24491265)
- **对应英文 LaTeX 原文**：[`main.tex`](main.tex)

---

## 摘要

本文针对 Mahler 映射 $Tx = \{3x/2\}$ 及其任意互素有理底推广 $\alpha = \pm p/q$（$2 \le q < p$），形式化证明了三类核心障碍：

1. **符号动力学与零拓扑熵自动机**：严格区分 $[2/7,5/7)$ 上的确定性单分支退出与真实的双分支联合关系 $\mathrm{Step}(x,y) \iff y = T_0 x \lor y = T_1 x$，给出显式联合周期轨与有限核证书，并建立面向任意符号有理底 $\pm p/q$ 与有限区间并集的通用零熵自动机母定理（`zero_entropy_of_no_branching_scc`），使用 Lean 内核 `decide` 完成 $-5/3$（$0.2880$）、$-3/2$ 带洞并集（$0.5660 > 1/2$）、$-3/2$ 居中（$0.4284$）与 $+5/3$ 居中（$0.3030$）的机检证书验证；
2. **离散流体输运**：机检验证 $\bmod\,\frac12$ 杯映射自映射性、精确 $3$-周期轨 $4/19 \mapsto 6/19 \mapsto 9/19 \mapsto 4/19$、局域 $\frac32$ 扩张率以及 $2{:}1$ 质量分配守恒；
3. **有限顶板阻塞与一般 $(p,q)$ 定量 Weyl 衰减**：无条件证明 $9/4$ 模型的镜像守恒、偶阶消逝与全奇数阶 Klein-4 排斥定理；在 Issue #12 中证明 $36^K$ 周期中点双 Cantor 交集（$18 \in A_K$）与奇频 Fourier 衰减 $\|\hat\mu_K(u)\| \le C K^{-c}$；在 Issue #17 中推广至一般互素 $(p,q)$（覆盖 $3/2, 4/3, 5/4, 5/3, 7/4, 8/3$）及 Karp 对偶势函数环平均上界 `karp_cycle_bound`。

所有经验数值观察（如混沌阈值与谱隙估计）均显式标注为未证明的实验观测；任何地方均不声称证明 Mahler 原始猜想。

---

## 1. 确定性单分支退出 vs. 双分支联合符号障碍

设 $T_q(x)$ 为偶分支 $T_0(x)=\{3x/2\}$ 的有理实现，$T_1(x)=\{3x/2+1/2\}$ 为奇分支。真实 Mahler 轨道允许每一步在两个分支间自由切换，因此动力学对象必须是**联合关系**：

$$\mathrm{Step}(x,y) \iff y = T_0 x \;\lor\; y = T_1 x.$$

- **整数消去判据（`exclusion_integer`）**：若 $2^N \mid M$ 且 $|M| < 2^N$，则 $M = 0$。
- **确定性 $T_q$ 四项不存定理（`cage_two_sevenths`）**：不存在 $x \in \mathbb{Q}$ 使 $x, T_q x, T_q^2 x, T_q^3 x$ 全部落在 $[2/7, 5/7)$ 内。
- **联合关系的真实存活（`joint_orbit_two_sevenths` 等）**：单分支退出**并不**阻断联合关系 $\mathrm{Step}$！在同一个区间 $[2/7,5/7)$ 内，存在长度为 $6$ 的交替联合轨道

$$\frac{3}{7} \xrightarrow{T_0} \frac{9}{14} \xrightarrow{T_1} \frac{13}{28} \xrightarrow{T_0} \frac{39}{56} \xrightarrow{T_1} \frac{61}{112} \xrightarrow{T_1} \frac{71}{224},$$

以及精确有理周期轨 $2/5 \leftrightarrow 3/5$ 和 $4/13 \mapsto 6/13 \mapsto 9/13 \mapsto 7/13 \mapsto 4/13$。相反，带洞区域 $[5/24,11/24)\cup[13/24,19/24)$ 在 $\mathrm{Step}$ 下的联合存活集**严格有限**，恰为 $\{4/15, 2/5, 3/5, 11/15\}$。

- **阈值 $8/57$ 的精确算术起源**：在左洞族 $[\delta, 1/2)$（受限于杯映射 $F$）下，$\delta^* = 8/57 = \frac23 \cdot \frac{4}{19} = T_0^{-1}(4/19)$ 划分出三个精确区间：$\delta > 4/19$ 有限步清空；$8/57 < \delta \le 4/19$ 保留包含 $3$-周期轨的零熵有限集；$\delta < 8/57$ 因折叠复合 $T_1 \circ T_0^3$ 将 $[8/81,8/57)$ 映入 $[0,4/19)$ 而产生正拓扑熵反馈回路。

---

## 2. 通用带符号有理零拓扑熵自动机（Issue #17）

为了对任意有理底 $\alpha = \pm p/q$（$p,q\in\mathbb{N}, q\ge 1$）与 $[0,1)$ 上的有限有理区划 $\mathcal{I} = \{I_0,\dots,I_{N-1}\}$ 进行内核级零熵认证，`Mahler32.RationalBaseDefs` 与 `Mahler32.ZeroEntropyAutomaton` 建立了纯整数交叉乘积区间重叠判定 `hasBranchOverlap`：

- **可靠性定理（`hasBranchOverlap_sound`）**：只要 $\mathrm{StepPQ}\,p\,q\,\mathrm{neg}\,x\,y$ 成立且 $x \in I_i,\, y \in I_j$，转移邻接边必被自动机捕获。
- **零拓扑熵母定理（`totalPaths_poly_bound`、`zero_entropy_of_no_branching_scc`）**：若转移有向图具备拓扑序（`adj i j = true -> comp i <= comp j`）且每个强连通分量（SCC）内部每个顶点至多有一条分量内出边，则长度 $L$ 的路径总数满足多项式界

$$\texttt{totalPaths}\;\mathrm{adj}\;L \le N \cdot \bigl(N(L+1)\bigr)^M,$$

从而拓扑熵严格为零（对任意 $\varepsilon > 0$，存在 $C > 0$ 使路径数 $\le C(1+\varepsilon)^L$）。

借助递归表查找与纯整数交叉乘法，全部 4 个有理底零熵证书直接在 Lean 4 内核中通过 `decide` 一次算证（**零 `native_decide`、零外部公理**），并由 `scripts/generate_certificates.py --verify` 在精确 `Fraction` 算术下互锁复现：

| 有理底 $\alpha$ | 区间与结构 | 总宽度 | 划分单元 / SCC 数 | Lean 机检定理 |
| :-- | :-- | :-- | :-- | :-- |
| $-5/3$ | $[89/250, 161/250)$ | $0.2880$ | $3$ 单元 / $3$ SCC | `cert_neg_5_3_zero_entropy` |
| $-3/2$ | $[147/1000, 43/100)\cup[57/100, 853/1000)$ | **$0.5660 > 1/2$** | $18$ 单元 / $15$ SCC | `cert_neg_3_2_holed_zero_entropy` |
| $-3/2$ | $[1429/5000, 3571/5000)$ | $0.4284$ | $26$ 单元 / $16$ SCC | `cert_neg_3_2_centered_zero_entropy` |
| $+5/3$ | $[697/2000, 1303/2000)$ | $0.3030$ | $13$ 单元 / $9$ SCC | `cert_pos_5_3_centered_zero_entropy` |

（`scripts/generate_certificates.py` 亦同时校核了 $+5/3$ 深度 $7$ 加细到总宽 $0.3040$、$83$ 单元 / $72$ SCC 的全零内部支化条件。）

> **文献对比注记（未入 Lean 核心的伴随实验数据按实验观测标明）**：
> 经典分布理论分别在正有理底给出 $1/p$ 禁区上界（Flatto–Lagarias–Pollington 1995）及在负有理底给出 $(1+r-r^2)/p$ 禁区下界（Lu–Zheng, `arXiv:2603.16794`, 2026）。零拓扑熵符号自动机可突破这一门槛：伴随有理搜索测得正底居中零熵宽度达 $0.428$（$+3/2$）、$0.310$（$+4/3$）、$0.240$（$+5/4$）、$0.304$（$+5/3$，超出 $1/p=0.200$ 达 $+52.0\%$）、$0.186$（$+7/4$）、$0.157$（$+8/3$）；负底居中达 $0.4284$（$-3/2$，超出 Lu–Zheng 达 $+5.15\%$）、$0.3106$（$-4/3$）、$0.2408$（$-5/4$）、$0.2880$（$-5/3$，超出 $+16.13\%$）、$0.1862$（$-7/4$）、$0.1579$（$-8/3$），另有 $280$-态负底 $-3/2$ 变体 $[0.157,0.440)\cup[0.560,0.843)$。其中 $-5/3\ (0.2880)$、$-3/2$ 带洞 $(0.5660>1/2)$、$-3/2$ 居中 $(0.4284)$ 与 $+5/3$ 居中 $(0.3030 / 0.3040)$ 均已由 Lean 内核 `decide` 与 `scripts/generate_certificates.py --verify` 严格核验。

---

## 3. 离散流体输运与经验数值注记

杯映射 $T_{\mathrm{cup}}(x) = (3x/2) \bmod \frac12$ 保持 $[0, 1/2)$（`Tcup_mem`），在精确有理点处闭合为 $3$-周期轨 $4/19 \mapsto 6/19 \mapsto 9/19 \mapsto 4/19$（`cup_cycle`、`cup_period_three`），并在各分片分支上以 $3/2$ 均匀扩张（`Tcup_dist`），给出 $2{:}1$ 输运守恒 $\mu([1/6,1/4]) = \mu([1/3,1/2])$（`two_one_split`）。

实验注记中提到的混沌阈值 $L_{\text{chaos}} \approx 0.428705$、谱隙 $\approx 0.2898$、Hausdorff 维数迁移 $\approx 0.8548$、有限深度余弦乘积上界 $\le 0.7409$，以及各底的数值衰减指数/对偶势收缩率参数（$3/2$: $c \approx 0.69539$；$4/3$: $c \approx 0.22039, \lambda = 0.955$；$5/3$: $c \approx 0.18468, \lambda = 0.969$；$5/4$: $c \approx 0.10726, \lambda = 0.969$；$8/3$: $c \approx 0.10536, \lambda = 0.989$；$7/4$: $c \approx 0.08368, \lambda = 0.984$；$9/4$: $c \approx 0.06240, \lambda = 0.990$），在本文中严格作为**未形式化的经验观测值**记录，不混作定理。

---

## 4. $9/4$ 有限顶板阻塞与无进位 base-9 守恒律

针对 $4g_{k+1} = 9g_k + d_k$（$d_k \in \{2,3\}$），`Mahler32.Model94Obstructions` 无条件证明了七组代数/同余阻塞结论：镜像和守恒 $g_k + \tilde g_k = 9^k 4^{N-k} - 1$、偶数阶孪生轨道终止定理、模 $4$ 禁用和排斥、**对所有奇数 $N \ge 3$ 一致成立**的 Klein-4 四元组至多 3 点存活定理（`odd_rung_klein4_no_four`）、差分/和影子映射精准对应、无进位 base-9 转换器数字和守恒，以及 $4^4=256$ 窗口下的顶板比界 $8|S_{N+2}| \le 3|S_N|$ 与全周期 $4^k$ 提升引理。

---

## 5. 中点 Cantor 交集与一般 $(p,q)$ 定量 Weyl 衰减（Issues #12 & #17）

### 5.1 Issue #12：$36^K$ 中点交集与 $9/4$ 奇频衰减

`Mahler32.Model94GlobalDecay` 证明了 $36^K$ 周期提升与中点双 Cantor 交集非空性 $18 \in A_K$（核心算术基于 $5 \mid 9^K - 4^K$，`midpoint_double_cantor`）、放缩对径直径界 $\le (9^K-4^K)/5$（`inAK_antipodal_exclusion`）、精确 $4$-缩并恒等式、余弦乘积公式与定量多项式级傅里叶衰减 $\|\hat\mu_K(u)\| \le C K^{-c}$（`global_odd_freq_decay`、`cert42_path_decay`）。

### 5.2 Issue #17：一般互素 $(p,q)$ 隧道衰减与 Karp 势函数界

`Mahler32.GeneralPQDecay` 将整套隧道傅里叶衰减理论推广至任意互素 $p > q \ge 2$ 的模型 `TunnelModelPQ`：
- 证明一般精确 $q$-缩并 `hatMuPQ_mul_q`、$|S_K| = 2^K$（`card_survivorsSetPQ`）、$p$-倍乘余弦递归 `norm_hatMuPQ_cosine_product` 与不相交块下距命中引理；
- 确立一般定量 Weyl 衰减定理 `global_coprime_freq_decay_pq` 与 `global_freq_decay_of_q_pow_pq`，并在有理底 **$3/2,\, 4/3,\, 5/4,\, 5/3,\, 7/4,\, 8/3$** 上全部具体实例化（`weyl_decay_3_2` 至 `weyl_decay_8_3`）；
- 建立普适图环均上界定理 `karp_cycle_bound`：对任意 `DualPotentialCert n` 上的有效环 $p$，消去严格正势函数 $\varphi(u)$ 后即得路径乘积 $\le \lambda^{|p|}$，并配以 44 顶点基线容器实例 `cert44`（`cert44_path_decay`、`cert44_cycle_bound`）。

---

## 6. 核验摘要与模块目录

所有声明均在零自定义公理核心下通过 Lean 4.36.0 + `lake build -KwarningAsError=true`、`#lint`、`AuditAxioms.lean`、`SpecCheck.lean` 与 `leanchecker` / `nanoda` 内核回放检查；核心新增模块分布如下：
- [`Mahler32/RationalBaseDefs.lean`](../../Mahler32/RationalBaseDefs.lean)：一般 $(p,q)$ 与符号有理自动机纯定义层；
- [`Mahler32/GeneralPQDecay.lean`](../../Mahler32/GeneralPQDecay.lean)：$(p,q)$ $\log_q p$ 临界排斥、Weyl 傅里叶衰减与 Karp 环上界证明；
- [`Mahler32/ZeroEntropyAutomaton.lean`](../../Mahler32/ZeroEntropyAutomaton.lean)：区间重叠可靠性、SCC 零熵母定理与 $-5/3$、$\pm 5/3$、$-3/2$ 四组内核 `decide` 证书。
