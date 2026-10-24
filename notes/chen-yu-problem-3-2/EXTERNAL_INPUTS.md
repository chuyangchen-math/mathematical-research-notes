# 外部输入及假设审计

所有外部结果通过定理参数传入；本工程没有自行声明 `axiom`。参数不出现在 `#print axioms` 中，必须同时审查本清单和定理类型。

## 几何表示接口

`F` 表示连通定向双覆盖的亚纯函数域，`t` 为覆盖对合。原始二次微分的标准连通双覆盖构造、亚纯对象的 Laurent 展开及不变对象的下降采用标准几何事实。

- `Germ.ring`、`Germ.scalar`：展开尊重域运算和复标量；不声称任意形式级数都收敛。
- `hpull`：用非零亚纯参考一形式写微分时的拉回系数关系；不假设有界截面同构。
- `homega`：平方根微分在规范坐标中的单项式表达。分歧处 z=w² 的 2w 因子已包含。坐标逐图选择，不要求不同图采用相同规范化。
- `hplus`：不变函数在底曲线坐标中的标准下降表达。
- `ht`、`hdeck`、`hkind`：对合、图交换/反射和阶数相容。ChartAction 允许交换图时同时反射。
- `stable`：不变除子所定义的有界函数空间对覆盖作用稳定。
- `FiniteDimensional`：紧曲线的除子截面空间及有限主部空间的标准有限维性。

局部商运算、奇偶支撑、取整及阶数正反界在 PaperOrientationLocal、PaperSpinLocal 中证明。全局有界空间是满足所有图上界限的子空间；乘除 ω 的映射与逆映射由代码构造。

PaperSynthesis 实际构造不变子域。其 `valuation` 是任意整数 n 的局部阶数判据：展开属于 bounded n 当且仅当微分除子系数至少为 n；`point` 满射表达覆盖全部点，`orders` 表达 D 的系数。`section_definition` 据此证明局部界与除子定义相同，没有另设截面空间等价假设。

未为具体黎曼曲线构造接口实例。这些标准事实适用于几何对象的正确性属于明确引用边界。

## Riemann–Roch 与除子

引用紧连通光滑复曲线上的标准公式：

`h⁰(O(D)) − h⁰(K(−D)) = deg D + 1 − g`。

自旋部分的两项是已定义的实际截面空间维数；特征子空间对应、总维数分解与模 2 计算由代码证明。例外型的八个次数计算由 degree_equals_genus 验证；signature_degree 是 D 按零点重数除以 3 定义的数据条件。

DivisorTheory 只输入非零亚纯函数的乘法和逆元除子法则。权重 k 微分除子定义为 principal(f)+kK。canonical_degree 引用非零亚纯一形式除子次数为 2g−2。立方商公式、R 的有效性与次数、θ 的全纯性及恢复 q 的等式由代码证明。

## 主部正合列与常值定理

引用普通 Mittag–Leffler 上同调正合列在主部处的正合性：range(principal)=ker(delta)，delta 的几何目标是 H¹(O)。

反不变部分的满射性由 (f−t f)/2 平均化证明。零主部函数全纯，再用紧致连通常值定理得常数；fixed_kernel_from_constants 证明常数对覆盖作用固定。compact_constants 是该常值结论的固定核形式，不是“反不变映射单射”的假设。所得同构与已证明的定理 3.2 组合。

## 第二类微分与周期

外部分析结果为：

1. 有限微分主部满足总留数条件时的亚纯微分存在性；这里主部是 dP，各留数为零。
2. 零留数亚纯微分全部闭路周期为零，当且仅当它是全局亚纯函数的微分。
3. 积分线性、拉回与循环作用相容，以及同调坐标检测周期。

内部推导为：

- derivative_residue_zero 证明 dP 的留数为零。
- secondKindLift 从普通存在性构造线性提升，anti_surjective 通过平均化构造反不变提升。
- periodObstruction 构造周期向量模全纯微分周期的商；全纯微分对应积分主部映射 b 的核。
- period_class_independent_of_lift 证明提升选择不影响商类。
- differentiated_principal_identity 从真实 Laurent 求导及主部坐标定义证明 b(df)=p(f)。
- primitive_bound_from_principal、bounded_exactness 从外部无界原函数定理恢复所需函数极点界。
- anti_exact 平均化推出反不变正合性。
- anti_cycles_determine_periods 证明反不变形式只需检验反不变循环。
- anti_period_kernel_eq 推出反不变周期商核等于主部障碍核。

通用组合结果中的 zero_period_primitive、local_derivative 是由上述桥接引理提供的中间条件，不是需要再引用的本文结论。几何积分、收敛和同调理论本身属于标准外部接口。

周期检测在复化循环空间上表达，平均化中的 1/2 因而有定义。形式化不要求整数反不变同调格存在幺模辛基；论文的周期坐标在这里仅承担检测零周期的作用。选取该向量空间的基后得到通常的有限维周期坐标，核判据不依赖基的选择。

## 陈–默勒分支定理

引用 Chen–Möller, *Quadratic differentials in low genus: exceptional and non-varying strata*, Theorems 6.1 and 7.1：三个亏格 3 例外型，以及五个亏格 4 例外型的非双曲 regular/irregular 部分，h⁰(O(D)) 在 regular 部分为 1，在 irregular 部分为 2。

来源：[arXiv:1204.1707](https://arxiv.org/abs/1204.1707)，[全文](https://arxiv.org/html/1204.1707v1)。正式出版为 Ann. Sci. Éc. Norm. Supér. (4) 47 (2014), no. 2, 309–369。

ExceptionalSignature 枚举全部八型；Eligible 明确限制亏格 4 的非双曲范围。chen_moeller 仅输入 1/2 截面数，不输入定向覆盖、残余三次或周期障碍判别。后者由 complete_component_criterion 和已证明的同构、核比较推出。

## 检查边界

没有占位证明不等于没有外部前提。标准结果作为参数意味着相对证明，不表示 Lean 已证明它们适用于具体曲线。本文目标的同构、极点界、残余三次等价性和周期核相等均由代码推导。本机编译与干净依赖复现不同，实际执行记录见 VALIDATION.md。
