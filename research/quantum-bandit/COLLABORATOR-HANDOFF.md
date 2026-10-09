# Quantum Bandit frontier: collaborator handoff

Snapshot date: 2026-10-09. **Public research prototype; neither A nor B is complete.**

## 给懂 Bandit 的合作者：为什么做这两个题

经典 Bandit 的主要统计成本是区分很接近的臂。把均值估计到误差 r，普通有界独立样本通常需要约 r⁻² 次观测。量子幅度估计在特定访问模型下能把查询依赖降到约 r⁻¹：环境必须提供奖励生成的酉电路 U 及其匹配逆 U†，算法在测量之前可以相干地反复调用它们。只有普通奖励样本、量子态副本或一台量子计算机，并不自动提供这个能力。

“相干”可以先理解为：在测量之前，若干操作共同作用于一个量子态，其振幅能够发生干涉。测量只给经典结果；本课题要求块末丢弃量子态，下一块重新开始，经典历史仍保留。因此 D 是一块中 U/U† 合计调用数的上限，不是自适应轮数，也不是物理门深度。

**A 问有限相干能力能换来多少累计遗憾改善。** 用有文献依据、但尚未本地形式化的估计成本插值

    q_D(r, δ) ≈ 1/r + 1/(D r²)，另含置信对数和整数取整，

把 elimination 的经典决策层接到真实量子估计器。D=1 应回到经典抽样；相干块足够长时才接近理想幅度估计。对次优臂估计到 gap 量级，每次查询都按该臂 gap 计遗憾，得到候选 gap-dependent 以及 gap-free 上界。证明还必须覆盖截断、ties、K>T、失败概率和所有自适应历史，不能只代入一个 oracle 复杂度公式。上下界匹配目前未完成；不能声称最优。

**B 问电路不精确且价格不同的时候，实际应该用哪个档位。** 低成本电路的固定偏差不会靠多测几次消失。若实现偏差证书为 b、统计估计半径为 s，目标均值的有效半径是 b+s。要共同选择档位、相干长度和查询次数，并计入双向制备、已知反射门和其他所声明的成本。classical multi-fidelity BAI 已有强先例；我们的研究价值必须来自真实量子电路资源模型或新成本/下界定理，不能只把经典样本成本替换为一个量子公式。

两个库的分工是：QuantumComputinglib 产生“这个电路实际测得什么、用了多少资源、实现误差是多少”的证明；BanditRLlib 复用置信、淘汰、拉臂计数、遗憾和 testing 的决策骨架。形式化特别有用，因为量子加速对访问模型很敏感；遗漏 inverse、反射、状态装载或相干记忆，就可能证明了比真实问题更容易的问题。

最近参考：Erle–Koczor [arXiv:2608.24434v1](https://arxiv.org/html/2608.24434v1) 的任意深度幅度估计；Liu–Li–Lui [arXiv:2608.14319v1](https://arxiv.org/html/2608.14319v1) 的量子 Bandit 下界；Poiani 等 [arXiv:2406.03033v2](https://arxiv.org/html/2406.03033v2) 的 classical multi-fidelity BAI。详细版本、模型区别和未获取全文的 NeurIPS 2026 记录见 [literature-audit.md](evidence/literature-audit.md)。这不是全球首次或蓝海已确认的声明。

## 当前可靠进度

- 已 kernel-check：Born effect stability，aligned Ry 电路的 reward bias，forward/inverse 查询字及原语门数，自适应 reset 历史的实际 PMF 与 Hellinger 信息累积；跨库 adapter 和 canary。
- 条件式：bias+statistical radius 的 recommendation correctness。统计尾概率仍需要真实估计器生产，不能升格为完整算法。
- 未证：A 估计器/策略/遗憾上下界，B 档位选择/停止/总成本/混合 fidelity 下界。
- 最新信息定理限定为固定有限块数、计算基测量、确定性经典历史策略、自然数路径预算。它含两个环境的期望查询成本；不能直接推出 K-arm minimax 下界。
- 精确边界：[research-boundaries.md](research-boundaries.md)。历史编译凭据和独立七槽审计：[evidence/adaptive/](evidence/adaptive/)。公开可获取不等于主库发表验收。

## 在自己的电脑建立独立环境

前提是 Git 和 elan 可用。两库和 joint Lake 项目固定 Lean 4.29.1，Mathlib commit 为 `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。Samplinglib 当前版本不兼容，不是这个 checkpoint 的依赖。不要复制别人的 `.lake`、本地 junction 或 Python 环境。

在一个新目录中执行下列 PowerShell 命令。两个文件夹必须分别叫 `bandit` 和 `quantum` 并互为同级，这是 joint Lake 路径依赖的要求。

```powershell
git clone --branch research/qb261009 https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep.git bandit
git clone --branch research/qb261009 https://github.com/DakeBU/Quantum-Computing-Block-Encoding.git quantum

Set-Location quantum
git switch --detach b541c64bfbc0c1f416db8959d306d360508e2cf6
git switch -c collab/yourname-quantum-measurement
lake exe cache get
lake build
lake build Tests

Set-Location ../bandit
# 固定数学与证据快照，避免研究分支后来前移导致复现版本变化。
git switch --detach 64eb285ebecbdc4bf236318776aabc6160fb1851
git rev-parse HEAD
git switch -c collab/yourname-bandit-measurement
lake exe cache get
lake build
lake build Tests

Set-Location research/quantum-bandit
lake build QuantumBanditAdapter Canary AdaptiveTranscript AdaptiveTranscriptCanary
lake exe adaptive_dependency_export evidence/adaptive/reproduced-proof-term-graph.json
```

每次检查退出状态。网络/缓存失败与 Lean 数学失败分开记录。Bandit 最新已证数学父节点 commit 是 `5638277b618ee4bf0d3c61aae12991f4f2cbdf01`；固定公开快照 `64eb285ebecbdc4bf236318776aabc6160fb1851` 在其上仅增加说明及历史证据，本交接说明的后续修订不改变这份数学快照。先比对 ancestry 与 `evidence/adaptive/release-index.json` 中源码/证据 hashes，再把两个实际 checkout 的 HEAD 写入个人 run receipt。不要在他人的活动分支或已有脏工作区 checkout/reset。

## 可以直接交给自己 coding agent 的接续 goal

下面是一个有明确验收点的默认 goal。若已有合作者领取它，先在研究 tracking issue 中认领另一个 leaf，避免重复工作；agent 不得擅自给其他协作者发消息。

> 目标：从 BanditRLlib 与 QuantumComputinglib 的公开 research/qb261009 checkpoint 接续 Quantum Bandit frontier。先阅读本库 AGENTS.md/CONTRIBUTING.md、Statement Seal/source-fidelity/semantic-roundtrip/实际 proof-graph 协议和 research/quantum-bandit/README.md、research-boundaries.md、evidence/adaptive/。冻结当前两个 commit、Lean 4.29.1 和 Mathlib pin；在个人分支工作，不改 main、不覆盖协作者，不合并 main。首个有界增量是“真实低深度幅度估计测量模型生产器”，不是重新证明已完成的 Born stability 或 adaptive Hellinger。
>
> 精确模型：每块从已知初始态重新开始，经典选一个臂；块内只调用该臂 U/U† 与明确已知 unitary，正向和逆向都按一次查询计入块上限 D、总预算 T 和该臂 gap；块末测量并丢弃全部量子态，经典历史保留。不免费提供关于未知制备态的反射、不免费状态装载或 unitary synthesis，不把置信区间假设成无偏/独立次高斯输出。
>
> 从 Erle–Koczor arXiv:2608.24434v1 Measurement Model Eq.(1)、Algorithm 1 开始。预先冻结一般有限维酉 U、已知初始基向量和已知 good-coordinate projector 的完整 Lean root signature，再独立抽取/复核 source proof topology。构造已知对角反射的实际酉证书、奇数和偶数查询的字、实际 Born 输出概率与 ±1 response 期望。偶数查询方案须计入最后 U†，把关于未知 U|0> 的测量还原为已知初始态测量。证明 literal query count 不超过所声明的 m；m=0 无查询，D=1 单次抽样。不能只做 odd-depth 后直接引用要求完整深度窗口的 WLSAE confidence theorem。
>
> 优先复用 QuantumQueryWord、QueryCircuitCost、PrimitiveSemantics、BornStability、ResetBlockProcess。先在一个实际一比特 Ry/反射原语电路上做 canary 和 gate-count certificate；一般维度的反射合成若尚未完成必须公开列为未证 supplier，不得变成一个假设来伪装闭合总门成本。未知均值/角度只用于数学分析，不能作为算法已知输入。若范围必须收缩，保持原目标并另命名 refined model、给准确 mismatch。
>
> 持续完成这个测量语义与查询成本增量：真实 lake 编译、可运行 canary、#print axioms、sorry/admit/new axiom 扫描、actual compiled type/value dependency graph、distinct blind decoder 和 source reviewer 的七槽审计、两库要求的 build/Tests 和读者/图/Frontier 同步。保留失败尝试和准确 obstruction。验收报告分别标 compiled / conditional / speculative / refuted；WLSAE 窗口与最小二乘置信证明、A 遗憾主定理和 B 成本主定理在生产器没有完成时仍为 open leaves。公开提交走个人分支和 draft PR，不宣称最优/首次，不合并 main。

第二位合作者适合领取 B 的 finite feasible-fidelity selector：先对空可行集、b<r、integer query/shot caps、known-gate 计费建立实际选择和成本证书，明确依赖尚未完成的 estimator；不要把条件式成本比较报成完整 ε-BAI。第三条独立 leaf 是停止/单环境信息比较及 hard-oracle/testing reduction；现有双环境 Hellinger 界不能直接产生 K 因子。

## 本机结果如何交回

交回 exact source/version/anchor、两个 base/head commits、冻结签名、实际 Lean declarations、proof dependencies、canary、完整验证命令/退出状态、独立审计和未证 leaves。先 push 自己的 branch 再开 draft PR；不要推送环境缓存或提交全部分支。研究公开授权不等于绕过各库发表验收。
