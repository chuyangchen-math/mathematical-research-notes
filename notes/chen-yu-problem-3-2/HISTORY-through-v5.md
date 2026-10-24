# Problem 3.2：形式化补全进度

**状态：未完成完整形式化。此目录是新的基础模块，不是替代原论文的完整证明。**

原始 Main.lean 未修改；GitHub 未发布。

2026-10-21：第一轮的四个核心构造均只依赖 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。该轮输出保存在 verification.log；后续各轮见下文。

## 新增内容

### 第五轮（2026-10-22）：原函数、常数修正与覆盖作用

- `LocalPrimitiveGluing.lean`：证明 Laurent 导数为零恰好等价于常数，导数相同的两个级数只差常数；构造零留数形式的归一化局部原函数族，以及它们的粘合障碍。证明障碍消失恰好等价于能逐图减去常数使重叠差消失。还证明：若某微分的主部是 `dP`，则其原函数的主部恰为 `P`。
- `ChartDifferential.lean`：对形式微分系数定义包含雅可比负号的覆盖作用，证明求导和归一化原函数与该作用相容，且保持相应反不变条件。这里微分系数的作用不同于函数的作用。
- `AntiPrimitiveGluing.lean`：通过平均化构造反不变的兼容原函数，并将这一结论接入原函数粘合障碍的消失判据。
- `ResidualCubicLocal.lean`：在实际 Laurent 级数域上定义 `θ = η³/q`，证明商的阶数和恢复等式 `q = η³/θ`；若 `ord(q)=3d-p` 且 `0≤p≤1`，证明 `θ` 无负次项当且仅当 `η` 的阶至少为 `d`。构造非负的局部残余阶 `r`，证明 `ord(θ)=3r+p`。还验证权重一、权重二的形式坐标变换下，商具有权重一并保持给定的转移相容性。

**尚未跨越的边界：**重叠差映射仍是输入，并未构造实际曲线的解析限制映射；形式级数没有收敛性结论；上述粘合障碍未与拓扑闭路上的积分、论文的周期商空间或 `H¹` 完成比较。局部零留数只保证局部可积，不能代替全局周期消失条件。论文需要的第二类亚纯微分存在性也尚未证明。

残余三次结果同样是局部形式结果：尚未构造全局典范线丛截面、证明 Laurent 展开忠实反映全局亚纯微分，或证明有效残余除子的次数为 `g-2`。不能据此将论文 Lemma 5.2 或 Theorem 5.3 标为完整形式化。

本轮四个新增模块均编译通过，核心公理审计仅有 `propext`、`Classical.choice`、`Quot.sound`。本机依赖环境与前轮相同；尚未执行干净环境复现。第五版包含累计 16 个证明模块及统一入口 `All.lean`，原工程 `Main.lean` 仍未修改。

### 第四轮（2026-10-22）：交换局部图的覆盖作用

新增 `ChartCoverAction.lean`，已通过编译及核心公理审计：

- `ChartAction` 记录图指标上的对合和反射标志，`action_twice` 证明作用两次为恒等。
- `ramified`、`unramified`、`mixed` 分别给出固定图内反射、成对交换图、以及两者并存的显式模型。
- `unramified_anti_iff`、`mixed_anti_iff` 证明反不变条件在交换图上确实等价于两张图的级数互为相反数。
- `principal_equivariant` 证明实际主部投影与此作用相容。
- `compactAntiObstructionEquiv` 将推广后的作用接入已构造的障碍映射，使用紧致全纯函数常值定理处理零主部核。

这消除了第三版“仅支持每张图内反射”的形式局部模型限制，但**没有构造几何双覆盖**。重叠差映射的几何来源、忠实函数表示、零主部的全纯性仍是组合定理的明确前提。

`MixedPrincipalParts.lean` 把既有的分歧反不变主部和交换对反不变主部组成实际向量空间，证明其维数为分歧贡献 `∑ (m+1)/2` 加上非分歧交换对贡献 `∑ m`。各处极点界是输入，尚未证明它们由本文的几何除子给出。

本轮两个新增模块编译退出码均为 0，核心公理审计只有 `propext`、`Classical.choice`、`Quot.sound`。`obstruction_rank_nullity` 另行给出混合空间上实际线性映射的秩—零度定理；它与总维数公式分开陈述。源码仍有风格提示，不影响证明检查。完整论文状态仍为 PARTIAL；仍使用同一本机依赖环境，未验证干净环境复现。

### 第三轮：主部、留数、粘合障碍与紧致性

- `PrincipalParts.lean`：从 Laurent 系数定义主部投影；证明核为无负次项的形式级数、像为负次主部，并构造商空间同构。极点阶至多 m 的主部与 `Fin m → ℂ` 显式同构，维数为 m。
- `AntiPrincipalParts.lean`：用奇数负次项构造反不变主部的坐标，证明维数为 `(m+1)/2`；交换两张局部分支的反不变主部维数为 m；证明有限个分歧点的维数可求和。也给出反不变局部全纯级数非零的例子，防止把局部主部映射误认为单射。
- `ResidueMatrix.lean`：实际计算主部与 Laurent 形式乘积的留数，证明留数映射等于由偶次系数组成的矩阵，并证明秩—零度及满秩判据。尚未证明此矩阵就是论文的全局障碍映射。
- `Gluing.lean`：证明覆盖上的兼容函数可以粘合；证明兼容的局部线性同构诱导兼容截面空间同构。尚未包含解析收敛性或实际曲线的坐标变换。
- `OverlapObstruction.lean`：从重叠差映射及零主部修正构造商值障碍映射，证明其核恰为兼容截面的主部像，且与提升选择无关。未将这个商识别为曲线上的 `H¹(O)`。
- `CompactHolomorphic.lean`：使用 Mathlib 的紧连通复流形全纯函数常值定理，证明反不变全纯函数为零；证明有忠实全局函数表示和全纯性条件时，零主部核不变。这不是新增的常值公理。
- `LaurentOverlap.lean`：把实际 Laurent 主部投影和显式提升接入障碍构造，证明正合性及反不变障碍核同构。这里只实现每张局部图内的 `w ↦ -w`；交换局部图的全局作用仍待实现。
- `CompactBridge.lean`：进一步使用紧致性定理证明所需的不变核条件，组合得到 `compactAntiObstructionEquiv`。仍明确要求忠实全局函数表示、作用相容性，以及零主部截面的全纯性；这些几何实现没有被隐藏或自动消除。

以上新增八个模块均在本机 Lean 4.33.1 下编译退出码 0，审计输出只有 `propext`、`Classical.choice`、`Quot.sound`。完整日志在 `logs/`。组合入口为 `All.lean`。编译使用原工程已有的本机 Mathlib 依赖，不能代替干净依赖环境的独立复现。部分源码仍有不影响证明的风格提示。

这些结论分别解决实际局部空间和一般障碍构造，但还没有构造本文的定向双覆盖。形式 Laurent 级数与收敛亚纯截面不能在没有证明的情况下视为同一对象。

### 第二轮：形式 Laurent 级数局部构造

新增 `LocalLaurent.lean`。它使用 Mathlib 的 `LaurentSeries ℂ`（具有下有界支撑的形式 Laurent 级数），不是只操作极点阶数的整数模型。

本轮实际编译退出码为 0，打印的九项核心公理审计均只有 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。日志保存在 `local-laurent-verification.log`，源码哈希保存在 `LOCAL_CHECK.txt`。仍有本机依赖改动警告及一条不影响证明的代码风格警告。

- `boundedDoubleShiftEquiv`：实际构造 `f(z) ↦ w^b f(w²)`，并用抽取系数构造下降；在带阶数界的子空间上证明互逆。
- `deck`、`parity_odd_iff_anti`、`parity_even_iff_fixed`：实现 `w ↦ -w` 的系数作用，证明奇偶支撑分别等价于反不变和不变条件。
- `ramifiedQuotient_eq_div`：证明分歧局部模型中的映射确实是拉回微分系数除以平方根微分系数，包含雅可比因子 `2w`；同时证明正向与反向极点界。
- `boundedShiftEquiv`：用真正的 Laurent 单项式乘法处理非分歧局部模型，并验证相应极点界。
- `simplePoleSectionEquiv`：证明简单极点处的正向、下降和互逆；反不变性排除常数项。
- 四个 `spinInvariant/AntiFourRPlusOne/Three` 构造：证明分歧情形下 spin 局部截面对应的有界级数空间同构，包括 `4r+3` 情形被奇偶性排除的最高极点项。
- `derivativeEquiv` 和 `exists_primitive_iff_residue_zero`：对真正的 Laurent 导数构造归一化原函数，证明局部可积性恰好等价于留数为零，并证明积分、求导的阶数界。

**边界仍然明确：**形式级数没有收敛性证明，也未证明每个几何截面在坐标下给出这些模型，以及坐标变换、全局粘合的相容性。局部原函数存在不蕴含全局原函数存在；全局周期消失条件尚未形式化。上述结果尚未接入原始 Main.lean 的最终几何定理，整篇状态仍为 PARTIAL。

### 第一轮：线性代数基础

GeometricAlgebra.lean 使用真正的复向量空间、子空间、线性映射和核，而不是有限基标签的集合。

1. `involutionDecomposition`：构造 `(x+t(x))/2` 与 `(x-t(x))/2`，证明对合的正负特征空间直和分解及维数公式。没有预先假设基集合的分解。
2. `divideByAntiEquiv`：在有复代数自同构的域上，用除以非零反不变元与乘回该元素，证明不变空间与反不变空间的线性同构。两个互逆关系是证明，不是接口字段。
3. `antiKernelEquiv`：给定实际正合的线性映射、等变性及不变核，通过平均化证明反不变部分到障碍核的双射，再构造线性同构。没有直接假设这个同构。
4. `rank_nullity` 及两个推论：对实际线性映射使用 Mathlib 的秩—零度定理，推出满秩和余秩一的判据。
5. `spin_parity_of_eigenspace_riemann_roch`：从已证明的特征空间维数分解推出奇偶性；Riemann–Roch 数值关系仍明确列为前提。

## 为什么还不是完整形式化

以上定理尚未实例化到论文中的具体曲线与微分。它们并未自动消除原始 Main.lean 最终定理的假设。特别是域上的乘除同构，尚未包含除子极点界、微分线丛、拉回及下降。

真正完成至少还需要：

- 定义紧曲线上的亚纯二次微分、除子、典范线丛及极点有界截面空间。
- 构造由 q 决定的定向双覆盖、deck involution 与平方根微分，证明局部标准形和分歧性质。
- 将不变截面下降到基曲线，并证明两种特征截面空间分别对应论文指定的线丛；这包括局部证明与全局粘合。
- 将已构造的形式主部空间和重叠障碍映射实例化到实际亚纯截面，识别 Mittag–Leffler 边界映射，证明零主部对应全纯函数，以应用已证明的紧致性结论。
- 构造第二类微分、周期商空间与实际周期映射，证明零周期可积成为全局亚纯函数，并证明两个核是同一主部空间中的相同子空间。
- 构造残余三次微分表示，并证明商的全纯性与除子关系。
- 将 Riemann–Roch 和 Chen–Möller 分支定理连接到上述具体对象；若要求完全无外部数学假设，必须有这些定理的正式证明。
- 为实际几何对象实例化所有模型，链接到论文终结论，并修正原 PDF 与 Lean 的定理编号对应。

本机固定版本 Mathlib 的源码检索没有找到可直接承担上述整条几何链的现成库。已有亚纯函数除子模块主要处理赋范域的子集上的函数；一般层论和线性代数模块不能直接代替曲线与微分的几何实现。此结论限于本次本机检索，不声称所有外部 Lean 项目均不存在相关工作。

## 编译

使用用户已有开发环境：

```powershell
Set-Location 'D:\Projects\PaperFormalization'
lake env lean 'C:\Users\陈初阳\Documents\Codex\2026-10-21\w\outputs\Problem32\GeometricAlgebra.lean'
lake env lean 'C:\Users\陈初阳\Documents\Codex\2026-10-21\w\outputs\Problem32\LocalLaurent.lean'
```

独立复现（需要网络和 Mathlib 缓存空间）：

```powershell
Set-Location 'C:\Users\陈初阳\Documents\Codex\2026-10-21\w\outputs\Problem32'
lake exe cache get
lake build
```

Lean 版本固定为 4.33.1，Mathlib 固定为 0df444a360eaa60ab8c11dca51a86af692955474。本机依赖目录存在 local changes 警告；独立干净环境复现未在此轮执行。
