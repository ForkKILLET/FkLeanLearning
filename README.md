# Lean 学习项目

个人 Lean 4 学习笔记与习题解答，记录证明思路以及 term、tactic 等不同写法。
目前主要学习 Emily Riehl 的 **Reintroduction to Proofs**。

本仓库包含习题答案；希望独立完成练习时，建议先在游戏中尝试。

## 学习来源

- [Reintroduction to Proofs 在线游戏](https://adam.math.hhu.de/#/g/emilyriehl/reintroductiontoproofs)
- [游戏源码](https://github.com/emilyriehl/ReintroductionToProofs)

题目陈述、章节标题与部分说明来自上述项目，解答在学习过程中编写和调整。
本仓库是个人学习记录，不是游戏的官方版本；本地使用的 Lean、mathlib 版本和
游戏提供的 tactic 可能不同。

## 内容

| 文件 | 内容 |
| --- | --- |
| [Quantifier.lean](src/ReintroductionToProofs/Quantifier.lean) | 全称量词、存在量词及其否定 |
| [AdvancedFunction.lean](src/ReintroductionToProofs/AdvancedFunction.lean) | 单射、满射、逆函数、函数外延性与 Lawvere 不动点定理 |
| [Equivalence.lean](src/ReintroductionToProofs/Equivalence.lean) | 类型等价、积与和、柯里化 |
| [NaturalNumbers.lean](src/ReintroductionToProofs/NaturalNumbers.lean) | 自然数、递归、归纳与加法 |
| [Dependent.lean](src/ReintroductionToProofs/Dependent.lean) | 依赖类型族、依赖函数、依赖对、柯里化与类型论选择公理 |
| [MultiProof.lean](src/MultiProof.lean) | 共用签名的一题多解宏 `proofs` |

[ReintroductionToProofs.lean](src/ReintroductionToProofs.lean) 是所有现有章节的导入入口。
练习中的具名声明位于 `ReintroductionToProofs` 命名空间，避免与标准库和 mathlib 重名。

## 本地使用

需要 Git 和 [elan](https://github.com/leanprover/elan)，编辑时可安装 VS Code 的
[Lean 4 扩展](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)。

```sh
git clone https://github.com/ForkKILLET/FkLeanLearning.git lean-learning
cd lean-learning
lake exe cache get
lake build
```

本项目使用 Lean 4.34.1 和 mathlib v4.34.1：

- [lean-toolchain](lean-toolchain) 指定 Lean 版本，elan 会按需安装对应工具链。
- [lakefile.toml](lakefile.toml) 声明项目和 mathlib 依赖。
- [lake-manifest.json](lake-manifest.json) 锁定依赖提交，应一同保留。

`lake exe cache get` 下载 mathlib 的预编译缓存；`lake build` 检查全部现有练习。
首次下载需要网络和数 GB 磁盘空间。依赖与构建产物保存在 `.lake/`，不纳入版本控制。

用 VS Code 打开仓库根目录，即包含 `lakefile.toml` 的目录。
也可以在根目录检查单个文件：

```sh
lake env lean src/ReintroductionToProofs/Quantifier.lean
```

## 一题多解

`proofs` 让多份解答共用参数和结论，每份解答分别接受 Lean 检查：

```lean
import MultiProof

/-- 从假设直接得到结论。 -/
proofs identityProof (P : Prop) (h : P) : P where
  | term := h
  | tactic := by exact h

proofs : True where
  | term := True.intro
  | tactic := by constructor
```

- 语法为 `proofs [名称] [参数...] : 结论 where ...`，结论前始终需要冒号。
- 参数直接进入每份解答的上下文，无须在每个分支重复 `intro`。
- 有名称时，第一份解答生成具名 `theorem`，其余生成 `example`。
- 省略名称时，所有解答均生成 `example`；具名形式的结论必须是命题。
- `term`、`tactic` 等标签用于区分解法，不会创建同名声明。
- 文档注释附到第一份解答生成的声明上。

## mathlib 导入

按需要导入模块，例如：

```lean
import Mathlib.Tactic.Use
import Mathlib.Tactic.Constructor
```

这两个模块分别提供 `use` 和 `fconstructor`。也可以用 `import Mathlib.Tactic`
导入更多 tactic，或用 `import Mathlib` 导入整个库。
引用练习中自行证明的定理时，可使用完整名称，例如
`ReintroductionToProofs.Nat.succ_injective`，以区别于库中的同类结论。

## 许可证

本项目采用 [MIT 许可证](LICENSE)。原创贡献署名为 forkkillet。
来自 Reintroduction to Proofs 的内容遵循其
[上游 MIT 许可证](https://github.com/emilyriehl/ReintroductionToProofs/blob/main/LICENSE)，
本仓库保留了 Jon Eugster（Game Skeleton）和 Emily Riehl（游戏内容）的版权声明。
