# Decision log（ADR）

每条只保留三件事：**决定 / 原因 / 禁止回退**。改动前先读一遍；与本文冲突的“优化”一律视为漂移。

---

## 1. 双分支零拓扑熵符号障碍（Two-Branch Zero-Entropy Obstruction）必须用联合关系 `Step`

**决定.** 所有关于 Mahler `3/2` 双分支零拓扑熵符号障碍（原工作注记中称为“双分支笼”）的陈述，都建模为

```lean
Step x y := y = T0 x ∨ y = T1 x
```

而 `Tq = T0` 的单分支迭代只用于确定性结论，不得冒充双分支联合关系的结论。

**原因.** 真实轨道每一步都可以在偶/奇分支间切换；单分支在 `[2/7, 5/7)` 的 3 步终止性
对 `Step` 不成立（`ZeroEntropyCages.joint_orbit_two_sevenths` 给出 6 项 `Step`-轨道，
`joint_cycle_two_fifths`、`joint_cycle_four_thirteenths` 给出真正的周期轨）。

**禁止回退.** 不得把 `cage_two_sevenths` 或“`[2/7, 5/7)` 3 步终止/清空”写成双分支结论；
`SpecCheck.ZeroEntropyCages` 的 `Step` 定义锁与轨道/周期锁必须保持通过。

---

## 2. 核心零公理、零 `native_decide`；单公理隔离

**决定.** `Mahler32Core` 及其导入的全部 `Mahler32/*.lean` 只允许标准公理
`propext`、`Quot.sound`、`Classical.choice`，不得出现 `sorry`、`admit`、`native_decide`
或新 `axiom`。唯一额外公理 `schlickewei_subspace_Q3` 只能存在于
`Mahler32Conditional/AlgebraicPairBranch.lean`。

**原因.** 核心结论要能被独立 `leanchecker` / nanoda 双内核复核；把条件性公理混入核心会
让“零公理”声明失真，`decide` 已足以支撑本仓库的全部有限计算。

**禁止回退.** 不得在核心模块引入 `native_decide` 或任何 `axiom`；不得让
`Mahler32Core`、`Solution`、`SpecCheck` 直接或间接导入 `Mahler32Conditional`。
`AuditAxioms.lean` 的公理白名单是最终裁决。

---

## 3. `Mahler32/QuiverMonotone.lean` 是上游镜像，合并后替换

**决定.** `Mahler32/QuiverMonotone.lean` 逐字镜像
`Mathlib/Combinatorics/Quiver/Monotone.lean`（mathlib4#44885）。

**原因.** 当前 Mathlib `v4.36.0` 尚未包含该文件，而 task 5 的确定性残基 DAG 需要
`Quiver.StrictMono` 与 `StrictMono.isPartialOrder_reachable`。

**禁止回退.** 在 `mathlib4#44885` 合入并升级工具链之前，不得删改该镜像的命名空间或
定理签名；合入之后应删除本文件，并把 `import Mahler32.QuiverMonotone` 统一替换为
`import Mathlib.Combinatorics.Quiver.Monotone`（同时更新 `README.md` 与
`SpecCheck.lean`）。
