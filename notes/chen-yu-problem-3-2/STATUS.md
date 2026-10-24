# 论文内部证明：显式外部结果下的形式化

本版本按用户确定的范围工作：允许引用著名定理、标准几何事实和外部文章结论；本文的局部计算、同构构造、核比较、除子运算和最终推论由 Lean 检查。

入口为 Main.lean。它导入新的证明模块，不导入原始有限基模型。D 盘原文件尚未替换，本目录未自动发布到 GitHub。

| 论文内容 | 主要结果 |
|---|---|
| 定理 2.1：截面分解、自旋奇偶公式 | PaperSpinGlobal.spinSectionDecomposition, theorem_2_1_floor |
| 局部分类覆盖全部允许的奇点阶 | PaperSignatureData.classify_spin_order |
| 引理 3.1：半拉回除子整性 | PaperSignatureData.lemma_3_1 |
| 定理 3.2：乘除 ω 的互逆和两侧极点界 | PaperOrientationGlobal.theorem_3_2 |
| 定理 4.1：主部障碍核及非单射判据 | PaperObstructionGlobal.theorem_4_1, orientation_obstruction_criterion |
| 周期商构造及提升无关性 | PaperPeriodComparison.periodObstruction, period_class_independent_of_lift |
| 反不变提升、正合性、周期核比较 | PaperAntiPeriod.anti_period_kernel_eq |
| 主部求导相容、反不变周期检测 | PaperDifferentialBridge.differentiated_principal_identity, anti_cycles_determine_periods |
| 全局原函数的极点界恢复 | PaperBoundedPrimitive.bounded_exactness |
| 引理 5.2：R、θ 的构造、有效性、次数及反向证明 | PaperResidualGlobal.lemma_5_2 |
| 八个例外型的次数、RR 阈值、分支判别 | PaperSignatureData.degree_equals_genus, PaperComponentCriterion.theorem_5_3 |
| 定向覆盖、残余三次和分支名称的组合 | PaperSynthesis.complete_component_criterion |

这些同构、核、商和维数是实际 Lean 向量空间上的对象，不是预设基的标签计数。

## 范围说明

这是**相对于显式外部输入的形式化**。精确边界见 EXTERNAL_INPUTS.md。没有从零建立紧黎曼曲面、解析层上同调、曲线积分或模空间理论，也没有在 Lean 中构造这些接口的具体黎曼曲面实例。外部输入适用于几何对象的正确性属于引用边界。

定理参数不会显示在 `#print axioms` 中，不能仅凭没有 `sorryAx` 宣称没有外部前提。本文目标的有界截面同构、核相等和残余三次等价性没有被列为外部前提。

定理 2.1 采用实际有界截面空间的分解证明维数公式；没有另外实现 Mathlib 层范畴中的推前线丛同构对象。论文的层记号通过标准截面、局部阶数与下降接口解释。亏格 4 的最终判别明确要求非双曲范围。

## 检查

Lean 版本为 4.33.1，Mathlib 固定版本为 0df444a360eaa60ab8c11dca51a86af692955474。完整检查记录见 VALIDATION.md 和 logs/current/。Verify.ps1 提供标准 Lake 构建和主入口审计。

旧五轮进度仅作为历史保存在 HISTORY-through-v5.md；其中旧的未完成事项不能作为本版本状态。
