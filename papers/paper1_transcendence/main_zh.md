# 基于 Archimedean 与 $q$-adic 联合评价的有理底 $p/q$ Padé 比较与代数对分支

- **作者**：Su MingKai
- **代码仓库**：<https://github.com/3y3y3y-huaiji/mahler32>
- **Zenodo DOI**：[10.5281/zenodo.24491265](https://doi.org/10.5281/zenodo.24491265)
- **对应英文 LaTeX 原文**：[`main.tex`](main.tex)

---

## 摘要

本文针对底数 $3/2$ 建立了实数域（Archimedean）与 $2$-adic 域的联合 Padé 比较准则，并将底层的双位点隔离（two-place isolation）机制一般化推广到任意互素有理底 $p/q$（$2 \le q < p$）。通过单一的代数恒等式，系统同时导出 $q$-adic 整除条件与 Archimedean 上界估计；结合整数消去引理，证明所有超越临界重复指数 $\log_q p$ 的最终周期符号轨道必退化为零。

Stephan 纲领中的“代数对分支（algebraic–pair branch）”已在 Lean 4 / Mathlib 中以条件形式形式化（显式隔离依赖 Schlickewei $p$-adic 子空间定理的单条公理 `schlickewei_subspace_Q3`）；而 Padé 偏差恒等式、$\bmod\,9$ 非退化同余判据，以及一般 $(p,q)$ 临界重复指数排斥界（`repetition_exponent_bound_pq`）均在零额外公理核心内无条件获证。本文**不**声称解决了 Mahler 原始分布猜想。

---

## 1. 引言与研究边界

Mahler $3/2$ 问题关注序列 $\{\xi(3/2)^n\}$ 在 $[0,1)$ 上的分布规律，至今仍属公开难题。若 $\xi > 0$ 对所有 $n \ge 0$ 均满足 $\{\xi(3/2)^n\} \in [0, 1/2)$，则称之为 **Z-数（Z-number）**。围绕这一主题，Stephan 提出将潜在极小存活字拆分为有理情况与代数对情况；Strauch、Lagarias–Sloane、Andrieu–Eliahou–Vivion、Cassaigne 等人发展了符号组合视角，Cook 与 Calegari–Dimitrov–Tang、Einsiedler–Lindenstrauss–Michel–Venkatesh 则分别刻画了局部同余边界与等分布障碍。

**学术边界声明**：
- 第 2 至第 4 节的所有结论均在 Lean 4 零公理核心（`Mahler32Core`）中无条件机检通过，仅依赖 Lean 标准公理三元组 `{propext, Quot.sound, Classical.choice}`。
- 第 5 节严格对应条件分支 `Mahler32Conditional.AlgebraicPairBranch`，显式标注唯一外部公理 `schlickewei_subspace_Q3`。

---

## 2. Archimedean 与 $2$-adic 联合 Padé 比较

设 $e, c \in \mathbb{Q}$，考虑几何级数 $S(z) = e(1 + z + z^2 + \cdots) = e / (1 - z)$。其在 $1$-阶与 $2$-阶对角截断下呈现两种评价形式：

$$\texttt{pade12}(e, c) = \frac{e}{1 - c}, \qquad \texttt{pade11}(e, c) = e(1 + c)$$

其中前者对应 Archimedean 解析求值，后者对应基数 $3/2$ 的进位截断（$2$-adic 逼近）。

- **命题 2.1（Padé 偏差恒等式，`two_world_identity`）**：对任意 $e, c \in \mathbb{Q}$ 且 $c \neq 1$，有

$$\texttt{pade12}(e,c) - \texttt{pade11}(e,c) = \frac{e\,c^2}{1-c}.$$

- **定理 2.2（一致退化唯一性，`two_world_iff`）**：当 $e \neq 0$ 且 $c \neq 1$ 时，$\texttt{pade12}(e,c) = \texttt{pade11}(e,c) \iff c = 0$。

为在数值上分隔这两个尺度，$\sqrt{2}$ 的严格有理上下界 $(140/99)^2 < 2 < (17/12)^2$ 已作为无条件引理（`sqrt_two_gt_140_99`、`sqrt_two_lt_17_12`）机检验证；同时，Padé 多项式望远镜的 **$\bmod\,9$ 非退化同余判据**（`mod_nine_gate_rat`、`mod_nine_anti_misfire`）证明：若首项系数 $9 \nmid c_{0,d}$ 且 $9 \mid q$，则 $L(4/9) \neq 0$。

---

## 3. 同时 Archimedean 与 $q$-adic 整数消去引擎

给定整化 Padé 余项 $M = D \cdot 3^d \cdot \bigl(Q(2/3)S(2/3) - P(2/3)\bigr)$，$2$-adic 整除性迫使 $2^N \mid M$，而 Archimedean 估计压低 $|M| < 2^N$：

- **引理 3.1（整数消去判据，`two_pow_dvd_eq_zero`）**：若 $M \in \mathbb{Z}$、$N \in \mathbb{N}$ 满足 $2^N \mid M$ 且 $|M| < 2^N$，则 $M = 0$。

由此可知，任何能够产生任意高阶 $2$-adic 整除性却受制于 Archimedean 指数级衰减的符号容许字族，其对应 $z = 2/3$ 处的解析余项必恒为零。

---

## 4. 一般互素有理底 $(p,q)$ 的重复指数排斥与 $\log_q p$ 临界门槛

将上述双位点隔离方法直接推广到任意满足 $2 \le q < p$ 且 $\gcd(p,q)=1$ 的有理底：对线性递推 $q\,g_{k+1} = p\,g_k + d_k$（$d_{\min} \le d_k \le d_{\max}$），定义符号字加权累积量 `wordWeightPQ p q W` 与伴随极点 `qStarPQ p q U V`（满足 $-d_{\max}/(p-q) \le q^*(U,V) \le -d_{\min}/(p-q)$）。

- **定理 4.1（一般 $(p,q)$ 双位点隔离与 $\log_q p$ 临界排斥界）**：设 $g_0 \ge 1$、$|V| \ge 1$ 且 $g_0$ 匹配周期扩展字 $U V^w$，则：
  1. **无穷周期字排斥（`no_eventually_periodic_pq`）**：不存在满足对所有 $w \in \mathbb{N}$ 均匹配 $U V^w$ 的初始值 $g_0$；
  2. **$\log_q p$ 临界重复指数界（`repetition_exponent_bound_pq`）**：

$$w < \frac{\log p}{\log q} + \left(\frac{\log p}{\log q} - 1\right)\frac{|U|}{|V|} + \frac{\log\bigl(g_0 + d_{\max}/(p-q)\bigr)}{|V|\,\log q}.$$

该证明在 `Mahler32.GeneralPQDecay` 中完全无条件完成：利用 $\gcd(p,q)=1$ 与等式

$$p^{w|V|} N = q^{|U|+w|V|}\bigl((p^{|V|}-q^{|V|})g_L + \texttt{wordWeightPQ}(p,q,V)\bigr)$$

同步榨取 $q$-adic 下界 $q^{|U|+w|V|} \le N$ 与 Archimedean 上界 $N < (g_0 + d_{\max}/(p-q)) p^{|U|+|V|}$，取对数即得精确斜率 $\log_q p$。对应各主要互素有理底的临界斜率数值如下（与 Flatto–Lagarias–Pollington 1995 及 Lu–Zheng `arXiv:2603.16794` 的分布下界互补）：
- $5/4$: $w_{\mathrm{crit}} \approx 1.1610$；$4/3$: $1.2619$；$7/4$: $1.4037$；$5/3$: $1.4650$；$3/2$ 与 $9/4$: $1.5850$；$8/3$: $1.8928$。

---

## 5. 核心条件定理：代数对分支的有限性

在 Stephan 的分析框架中，对于代数无理乘子 $\delta$ 与 $\vartheta \in (0,1)$，若一对指标 $2 \le a < c$ 具有互异间隔 $c - a$ 且使 $\delta\bigl((3/2)^c - (3/2)^a\bigr)$ 落在某整数的 $\vartheta^c$ 邻域内，则：

- **定理 5.1（代数对分支有限性，条件定理，`algebraic_pair_branch_finite`）**：在公理 `schlickewei_subspace_Q3` 下，上述违例指标对 $(a,c)$ 至多只有有限个。

其证明归结为两个**零公理**子引理：
- **齐次情形（$C = 0$，`lemma1_no_C_zero`）**：若 $A(3/2)^c + B(3/2)^a = 0$ 且 $(A,B)\neq(0,0)$，则 $(3/2)^{c-a}$ 在无限个互异间隔上取定值，由单调性矛盾；
- **非齐次情形（$C \neq 0$，`lemma2_no_C_ne_zero`）**：由 $|\delta - \alpha| \le |\delta + \beta|(2/3)^{c-a} + (2\vartheta/3)^c \to 0$ 迫使 $\delta \in \mathbb{Q}$，与无理性矛盾。

---

## 6. 形式化追踪与核验声明

| 数学结论 | Lean 4 声明标识符 | 公理状态 |
| :-- | :-- | :-- |
| Padé 偏差恒等式 | `TwoWorldPadeCriterion.two_world_identity` | 零额外公理 |
| 一致退化唯一性（$c=0$） | `TwoWorldPadeCriterion.two_world_iff` | 零额外公理 |
| 整数消去判据 | `TwoWorldPadeCriterion.two_pow_dvd_eq_zero` | 零额外公理 |
| $9/4$ 重复指数排斥界 | `TwoWorldPadeCriterion.repetition_exponent_bound` | 零额外公理 |
| $\bmod\,9$ 同余非退化判据 | `TwoWorldPadeCriterion.mod_nine_gate_rat`、`mod_nine_anti_misfire` | 零额外公理 |
| 一般 $(p,q)$ 纯定义 | `RationalBaseDefs.wordWeightPQ`、`qStarPQ` | 纯函数定义 |
| 一般 $(p,q)$ 双位点隔离 | `GeneralPQDecay.two_place_isolation_pq` | 零额外公理 |
| 一般 $(p,q)$ 临界界 $\log_q p$ | `GeneralPQDecay.no_eventually_periodic_pq`、`repetition_exponent_bound_pq` | 零额外公理 |
| 齐次/非齐次子引理 | `Mahler32Conditional.lemma1_no_C_zero`、`lemma2_no_C_ne_zero` | 零额外公理 |
| 代数对分支有限性 | `Mahler32Conditional.algebraic_pair_branch_finite` | 条件依赖 `schlickewei_subspace_Q3` |
