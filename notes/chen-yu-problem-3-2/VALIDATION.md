# 当前验证记录

检查完成时间：2026-10-24T12:52:08.8115663+08:00

- 编译器：Lean (version 4.33.1, x86_64-w64-windows-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
- 全部 **32 个 Lean 文件**（30 个证明模块、All/Main 两个入口）从源码重新编译，退出码均为 0。
- 项目编译输出使用新的 work/lean-verified-20261024 目录，没有复用本项目旧的 olean 文件。
- 共检查 132 条公理依赖输出，出现的公理只有 propext、Classical.choice、Quot.sound；没有 sorryAx。
- 源码未发现 sorry、admit、新增 axiom 或 unsafe 声明。
- 源码 SHA256 与逐模块退出码见 logs/current/modules.csv；每个模块的完整编译及审计日志在同一目录。
- 仍有不影响证明的代码风格提示，日志如实保留。

## 依赖环境边界

Mathlib 在配置中固定为 0df444a360eaa60ab8c11dca51a86af692955474。本次检查使用 D:/Projects/PaperFormalization 的现有依赖缓存。**没有重新获取干净 Mathlib 源码、重建全部依赖，或验证所有依赖工作树无本地改动。** 新建的是本项目的构建目录，不是一个全新的依赖环境。

Verify.ps1 提供标准 Lake 构建步骤。发布脚本还会在新仓库副本中获取固定依赖、完整构建并审计后才允许推送。发布脚本本次仅完成语法检查，没有执行网络发布流程。

## 2026-10-24 发布副本复核

在新克隆的发布副本中取得固定版本依赖，并使用 Mathlib 编译缓存。9 个依赖仓库的 HEAD 均与 lake-manifest.json 一致，工作树均无修改。没有从源码重编译整个 Mathlib。

首次构建遇到 Mathlib `.olean.private` 文件读取错误。修复发布流程后，以 LEAN_NUM_THREADS=1 依次补建缺失模块，再执行完整 `lake build`，退出码为 0；随后 `lake env lean Main.lean` 退出码为 0，未出现 sorryAx。32 个 Lean 源码哈希均与 logs/current/modules.csv 一致，修复没有修改证明源码。完整记录见 logs/reproduction-20261024.log，初次失败记录保留于发布副本的 verification.initial-failure.log。

以上补充了前述历史验证的依赖环境检查。本次尚未向 GitHub 推送。

## 数学边界（保持不变）

这是相对于 EXTERNAL_INPUTS.md 中明确列出的标准结果和几何表示接口的证明。定理参数不会出现在公理依赖打印中。上述检查不表示已经构造具体黎曼曲面实例，或消除了所列外部前提；也不代替独立人工的语义对应审查。

原始 D 盘 Main.lean 未修改；本次没有向 GitHub 推送。原文件与随附 PDF 的来源哈希见 PROVENANCE.md。
