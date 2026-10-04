# Algorithm 2.2 policy contract — v3 source review

**Verdict: accepted-with-explicit-delta.** Stabilize the 21 frozen mathematical signatures and finite-history definition context only. No target proof, public module, canary, combined gate, reader, immutable binding, PR, or chapter/book acceptance is certified. No mathematical header repair is required after the clean v3 blind-context repair.

Actor `/root/source_reviewer`: distinct automated source reviewer, separate from root formalizer and fresh `/root/normal_blind` decoder. Requested GPT-6 Astra / medium; runtime model identity is not independently attested. Neither external-human nor external-model review is claimed. Checkout `E:/ABRL/worktrees/research-online-book`, branch `codex/research-online-osd-policy`, HEAD `b1ffe6322ceef5492c3931a0e40f7e7d5fa5ff21`. Existing dirty/untracked drafting material was preserved.

## Source and actual inspection

Independently hashed original Orabona v10 PDF: `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. Read the actual supplied pages and re-extracted original physical25–27,28,31–33: Theorem2.13 and its proof/fixed-unbounded-domain remark; Eq2.1 tuning and future-gradient warning; properness/Definition2.20; transfer paragraph, Lemma2.31, Algorithm2.2, and coarser fixed-step formula. The source is not inferred from previously accepted packages.

All53 original input rows,58 v2 rows, and62 final v3 input rows match independently computed raw SHA256. All21 native fences match their frozen headers and use actual premise fragments. All21 neutral v3 signatures match the same headers modulo declaration renaming. The scoped context is unchanged. The actual signature probe has that context and exactly21 Prop-valued definitions corresponding to the targets; its exit0 validates typing only. Its unused-premise warnings are expected for Prop definitions and are not proof evidence.

The fresh v3 decoder read only the clean v3 packet and reconstructed every target in seven slots. Its raw input/report hashes match its receipt. Its explicit recovery of global properness, all-query support, finite values, off-path versus actual legality, exact residuals and conditional strict-prefix invariance agrees with my source/API inspection.

## Preserved packet failures and repair

V1 decoder correctly found opaque imported semantics; its result was a diagnostic, not source acceptance. I independently found that v2's claimed proof-free supplement actually included the full numbered `lemma_2_31` proof four times through overlong definition extraction. That is a blocking blind-provenance defect, even though none of the21 mathematical targets changed. V2 is contaminated history and cannot support clean-blind acceptance. Its repair prose claiming omitted proofs is historical incorrect evidence, not adopted here.

V3 uses exact definition boundaries and two existing theorem headers without theorem bodies. I checked the actual supplied definitions against the relevant shared Lean/mathlib interfaces and mechanically checked all neutral signatures. No upstream numbered-lemma/proof leakage remains. The different fresh decoder `/root/normal_blind` reports reading only this clean v3 packet, not the earlier contaminated material. V2 contamination and v1 missing-context history are preserved. The v3 source-review packet retains an earlier v2 paragraph, explicitly superseded by its final v3 instruction; the current verdict relies only on v3 clean reconstruction for blind evidence.

## Seven-slot source comparison

1. **Objects/spaces.** Finite-dimensional real inner-product E is the coordinate-free form of source R^d; dimension zero is allowed. Domain carries exactly nonempty/closed/convex. The shared project is genuine nearest projection, not an assumed desired update. EReal has an extra bottom constructor, excluded by SourceProper; support globally quantifies every ambient y, not only feasible y. A policy receives time, strictly past whole losses, realized output history including the current output, and the current whole loss.
2. **Quantifiers/order.** Policies are arbitrary function parameters, not restricted to the canonical selector. Performance uses only actual-run LegalFeedback up to T; universal off-path OracleLaw is optional and occurs only in its sufficient adapter. Fixed/variable estimates apply to every feasible comparator; the all-comparator tuned terminal fixes the schedule/run before quantifying u. The one-step targets impose no initial/query-feasibility premise: actual support plus properness gives finite query values even at an ambient outside initial point.
3. **Assumptions/regularity.** SubdifferentiableOn includes global properness inherited from Definition2.20 and global support existence on V. No extra global convexity, differentiability, boundedness for the fixed bound, assumed one-step inequality, or universal oracle law is added to performance. Feasible initialization and comparator, played positive steps, and nonincreasing played steps for variable bounds are explicit. Boundedness is retained for the Metric.diam wrapper, avoiding its totalized infinite-diameter trap. The pairwise-D helper implies D>=0 from nonemptiness.
4. **Conclusion/metric.** Actual recursive history appends projection of the actual current output minus eta times the actual selected support. Both eta-scaled inequalities and the divided one-step result use that successor. Regret is real subtraction of truly finite EReal losses under performance hypotheses; trajectory_finite_loss exposes both finite embeddings. Fixed and variable conclusions retain the negative terminal squared-distance term. The coarse bound is separately weaker. No selected-vector existence alone is substituted for performance.
5. **Constants/normalization/asymptotics.** Coefficients1/2, eta^2 in the chain, eta/2 in summed energy, and the terminal denominator2*eta(T-1) are correct. Lean t=0 represents source round1, terminal output T represents source x_(T+1). Fixed T=0 is an algebraic extension; variable requires T>0. Tuning explicitly requires D,G,T>0 and eta=D/(G sqrtT), producing DG sqrtT with coefficient1 on that same trajectory. G bounds actually selected vectors, not a different run or all boundary supports inferred from Lipschitzness. No future-energy minimizer, anytime rate, or signed convergence is claimed.
6. **Probability/feedback/stopping.** Deterministic pathwise statements; no stochastic law, measurability, stopping time, or expectation. Output uses only strict past losses for a fixed policy and initialization. Current loss is observed before selection for the next update. Policy and schedule are exogenous parameters: prefix equality does not prove their external construction cannot encode future data. Full current functions are available, matching full-information source feedback, not a scalar-only bandit oracle. Arbitrary legal realized support choices can be represented pathwise by policies; a randomized-policy distribution or joint adaptive-adversary construction is not a supplied interface.
7. **Boundary/excluded regimes.** Structural definitions and prefix/feasibility identities allow zero or negative schedules and arbitrary earlier losses without asserting performance. Fixed unbounded domains are allowed; variable bounds require bounded diameter. Singleton/zero-dimensional spaces remain allowed; zero D/G tuning is excluded rather than interpreting a zero denominator. Canonical bridge statements must work even outside legal regimes using the defined zero fallback, without claiming the fallback is a subgradient. Whole Chapter2, future book work and acceptance gates remain open.

## Target-by-target contract assessment

Common space, deterministic quantification and feedback qualifications are as above. Every row was compared to its exact frozen header and corresponding neutral result, not merely a planned theorem name.

| Target / neutral result | Objects and quantifiers | Assumptions | Exact conclusion and constants | Feedback/order | Boundary and assessment |
|---|---|---|---|---|---|
| history_zero /1 | Every run, Fin1 history | Shared types/domain only | Constant x1 | No loss read | Infeasible x1 allowed; faithful structural extension |
| history_succ /2 | Every run,t | None extra | Append actual project(output-eta*selected) | Current selection before next output | Any real eta; exact recursion |
| output_zero /3 | Every run | None extra | output0=x1 | Initialization fixed | No initial projection; correct |
| output_succ /4 | Every run,t | None extra | Actual next projected point | Same selected vector/run | Not a step-bound assumption; correct |
| history_mem /5 | Every t and history coordinate | x1 feasible | All stored outputs feasible | Projection supplies successors | No legality/eta sign needed; correct |
| output_mem /6 | Every t | x1 feasible | Current output feasible | No oracle law | Structural strengthening; correct |
| history_prefix /7 | Two runs, same p,x1,V | Equal eta/loss for s<t | Whole histories equal | Strict past; whole-function equality | Exogenous common-policy caveat; correct |
| output_prefix /8 | Same paired runs | Same strict-prefix equalities | Current outputs equal | Current loss may differ | Does not equate current selections; correct |
| oracle_feedback /9 | Every actual run,T | Initial feasibility, universal law, subdifferentiable prefix | Played LegalFeedback | Off-path law sufficient only | T0 vacuous; not required in performance |
| trajectory_finite_loss /10 | Every run,t,u | Feasible initial/u, current subdifferentiability | Both values equal embedded toReal | Current loss at output/u | No legal-policy premise needed; no infinity shortcut |
| one_step_chain /11 | Every run,t,u | Positive played eta, current regularity, actual hg, feasible u | Two inequalities, exact half-squares and eta² energy | Actual successor/selection | No hx1 restriction; source Lemma preserved |
| one_step /12 | Same local objects | Same premises | Gap <= distance difference/(2eta)+eta norm²/2 | Same actual step | Positive denominator explicit; correct |
| regret_fixed /13 | Constant-step run,T,u | eta>0, feasible endpoints, regular/legal played prefix | Initial/(2eta)+eta energy/2-terminal/(2eta) | Same selected sequence | T0 and unbounded V allowed; full source bound |
| regret_fixed_coarse /14 | Same constant run | Same premises | Drop nonpositive residual only | Same energy | Separate printed21 consequence; correct |
| regret_variable_bound /15 | Variable run,T,D,u | T>0, positive decreasing prefix, regular/legal prefix, pairwise bound | D²/(2eta_last)+weighted energy-terminal/(2eta_last) | eta_last=eta(T-1) | D0 allowed; stronger diameter-upper-bound wrapper |
| regret_variable /16 | Variable run,T,u | As15 plus bounded V replacing supplied D | Same formula with Metric.diam | Same history and last step | Infinite diameter excluded; exact source form |
| regret_tuned_distance /17 | Tuned run and one u | D,G,T>0, initial distance<=D, actual tuned legal/norm prefix | <=DGsqrtT with eta=D/(GsqrtT) | All premises refer to this run | Distance-only strengthening; not future optimizer |
| regret_tuned /18 | Fix tuned run then all u | Positive D,G,T, pairwiseD, actual tuned legal/norm prefix | Uniform <=DGsqrtT | No retuning for u | Source all-comparator guarantee; not anytime |
| canonicalPolicy_legal /19 | Every domain and off-path inputs | Regular f and last-point feasibility inside law | Canonical policy satisfies OracleLaw | Uses current f,last output | No numerical tie value specified; correct adapter |
| canonical_output /20 | All run inputs,t | None extra | Equals existing canonical iterate | Same eta/loss/x1 | Invalid regimes included as identity; correct |
| canonical_selected /21 | All run inputs,t | None extra | Equals existing current chooser at iterate | Current-time loss/index | Equality alone not legality; correct |

The proposed dependency DAG is feasible in scope: structural recursion/feasibility/prefix leaves precede actual support/finite conversion and one-step transfer; summation and existing weighted_potential_sum precede variable bounds; fixed bound precedes tuning; canonical bridges are separate. The actual weighted-potential API is in OnlineGradientDescentVariable under the advertised namespace. This review does not certify a compiled proof graph for targets that do not yet have bodies.

## Required next evidence and remaining deltas

No new target version is required for the mathematical headers. Keep the explicit coordinate/index/T0/positive-tuning, exogenous-policy/full-information and pathwise-only scope in downstream reader/acceptance metadata. Produce all21 actual bodies without silently adding OracleLaw, global convexity, feasible-current restrictions to the one-step leaf, or dropping residuals. Body review should test a genuinely history-dependent noncanonical legal policy, nonzero gradient energy/residual, terminal eta indexing, invalid future inputs, and on-path legality without universal off-path legality. Canonical bridges alone cannot witness the new policy generality.

Next proof/canary/public/root/Tests/harness/axiom/dependency/site/reader/immutable/PR gates are unresolved. A proof of these contracts can close the stated deterministic legal-policy family, not a stochastic adaptive-law interface or the entire chapter/book. Source/body/publication stages must remain distinct. No native trial or frontier mutation was performed by this review.

## Exact raw inspected files

All62 fixed input rows are included, plus the actual clean blind report/receipt and additional inspected source/API/probe/provenance files. Whole-file raw hashes bind bytes; semantic read scope for shared modules/mathlib is the named definitions/interfaces, and for the original PDF is the listed pages. The receipt does not certify unrelated declarations. Historical v2 rows are bound as rejected provenance, not clean evidence. No JSON reserialization or newline normalization was used for hashing.

| Path | SHA256 raw |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean` | `bf69a9ed4bc39134bbefac1a43b187e2f1e66fd43f352d0810ab89474f054922` |
| `.lake/packages/mathlib/Mathlib/Topology/Bornology/Basic.lean` | `f997a90d63f89d1408d41a59013cbfdf91cbdfcb754fe875fcbbaf01b6ff1efa` |
| `.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean` | `c48649a49c61e45bc9bb5b702b026786430c18e3f9d8952e557d0ca538b621a9` |
| `.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean` | `335de2c940e85c657f308cf0fd0039bfb7884f79c936e6a07ac446ecbe4058d3` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `BanditRLProof/OnlineGradientDescent.lean` | `e7edba540c2f60032bb4a34aaf0768b3107b94276b67b6f41fc289009c8924c1` |
| `BanditRLProof/OnlineGradientDescentVariable.lean` | `674bbb07ace34bfb03019fa6a933d3ea02cf7ebf0972e1e36a9c65b82efe772f` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `BanditRLProof/OnlineSubgradientDescent.lean` | `6ba8586e1691babc2db3e0c0fcddb69b4236e16f9f192c464b4c04262e854f1c` |
| `docs/contracts/online-osd-policy-v1/canonicalPolicy_legal-header.txt` | `26d18639d611207579e0ab562a6033e1e2dd0c8ef2bdab6fc9aaed8634ec70f2` |
| `docs/contracts/online-osd-policy-v1/canonicalPolicy_legal.json` | `e99d2bb591ec42b6624a0a2e12bcf5dafa7cf5b151a28393ca57c9d9682efb0f` |
| `docs/contracts/online-osd-policy-v1/canonical_output-header.txt` | `fc6fdc7275144b35ec71e288e3ae7514d6384a6f7212e1f63c8032b9b6941543` |
| `docs/contracts/online-osd-policy-v1/canonical_output.json` | `408b28026d1c63eb7c3eac3414c37571e2e2424d02609d785a30c460d84d6285` |
| `docs/contracts/online-osd-policy-v1/canonical_selected-header.txt` | `472b4e1ea27e71766fe921e97ff9752c0118fc63da611e59f3b12ab952b34fab` |
| `docs/contracts/online-osd-policy-v1/canonical_selected.json` | `e4dab383fe7725cb7c2adffd433256364336ec3d7cf4461ec913ba8cda51442d` |
| `docs/contracts/online-osd-policy-v1/context.lean.txt` | `ee72b114bb52c78457ab2ebe40f50b92d4fa57fd2cb31f61bff817857b5d6955` |
| `docs/contracts/online-osd-policy-v1/history_mem-header.txt` | `9468a05fdb0220c548b125edce2cdb6f0f34b800af9e5dafde513a543232e161` |
| `docs/contracts/online-osd-policy-v1/history_mem.json` | `3921cc2f4e6c037c2b02a5fd1276bf0d85f930dd54d3da7230b81c6de7414bf4` |
| `docs/contracts/online-osd-policy-v1/history_prefix-header.txt` | `1ca72256d383ab8d1e37713d389469a4fbfc8fee39048d5db8be4043b60da7fb` |
| `docs/contracts/online-osd-policy-v1/history_prefix.json` | `235c485ed22f716fadfea56725d28847b6aadfd5dacd00930b51a90c7e7efa8f` |
| `docs/contracts/online-osd-policy-v1/history_succ-header.txt` | `5eae2449132cfdef3384d03567d9042a1759a2e40f30b7be6f4bfb2eacb6979e` |
| `docs/contracts/online-osd-policy-v1/history_succ.json` | `b134690216d09fbd8be0e73bdd959d2f6d28ae7337e5ab5f595d426625dcebe7` |
| `docs/contracts/online-osd-policy-v1/history_zero-header.txt` | `d63910bf80ed414eb9332b01948f47b43a1f5552df1fd728b204c6d866947a67` |
| `docs/contracts/online-osd-policy-v1/history_zero.json` | `d13e02d9949e036236fa7f08a97bf03e568cd2c711453030c8b3bf30cedb98fa` |
| `docs/contracts/online-osd-policy-v1/one_step-header.txt` | `fcfaf7d9ec3a58e78927639b14d14f800212d6af8d5da7772a37232b9d9e0f9a` |
| `docs/contracts/online-osd-policy-v1/one_step.json` | `65798cb678f7192285a1a3cadc9fb1f973b88011c44439eaed88f02191169591` |
| `docs/contracts/online-osd-policy-v1/one_step_chain-header.txt` | `1796e67373a24b89353a64956396bb1060d0b2ab1f00c8482d5400d803fde41a` |
| `docs/contracts/online-osd-policy-v1/one_step_chain.json` | `e1a0c8b53ab431e061e799f691a5d265c4a950fd4d532a1925fe821ee35da72f` |
| `docs/contracts/online-osd-policy-v1/oracle_feedback-header.txt` | `a1df9e198e87f0e700cadd42bd025d15c4ce40ea19a9007953090fe063b8ca7b` |
| `docs/contracts/online-osd-policy-v1/oracle_feedback.json` | `17caf1dfcf88dca7820a4e700361c27c9e6d5e14ef0b791ce070d3eb004ab3db` |
| `docs/contracts/online-osd-policy-v1/output_mem-header.txt` | `1bcd9773a20c778839c473ce4c377531b555051cba7ed1a4c4066fc4763a657a` |
| `docs/contracts/online-osd-policy-v1/output_mem.json` | `7ce02843f330bf09fe36dce90b635151dbc3dee82a79e98d45b24996e69d2bed` |
| `docs/contracts/online-osd-policy-v1/output_prefix-header.txt` | `1ed169261ba2cab28c36752102861146be49c277b27689d90cb1ac15c6579f20` |
| `docs/contracts/online-osd-policy-v1/output_prefix.json` | `4da01f6c5786e2bdd963de645e404ba901758db3abaa30fa325beec268728d4f` |
| `docs/contracts/online-osd-policy-v1/output_succ-header.txt` | `f22f6c538f980ac448a20f42db832c3f2a0f0c15fa65b669054dddcff7749863` |
| `docs/contracts/online-osd-policy-v1/output_succ.json` | `a4623134cd3cc77cf21d3b8c33ddc19eabfd90c0c503cb958092629388efee15` |
| `docs/contracts/online-osd-policy-v1/output_zero-header.txt` | `dad71d11b63884ce10acc85a4ea13e6f654af9a6836f0295ad57261270f04863` |
| `docs/contracts/online-osd-policy-v1/output_zero.json` | `85065091fab587b1d5fc6b9600bbdab0e26c96a7d9bf476b4ec874012272b2c9` |
| `docs/contracts/online-osd-policy-v1/regret_fixed-header.txt` | `1e489df9b030fd45da35e6039ab47034df6f4c6a0feed66fd0cefc5e81970594` |
| `docs/contracts/online-osd-policy-v1/regret_fixed.json` | `301c7bbd2f942c138d33c87691fcdcbca1321f511471df58e572d06f730181a7` |
| `docs/contracts/online-osd-policy-v1/regret_fixed_coarse-header.txt` | `f4271fae5c084793fb36d24f24cba5964d43318a05c21ffc99c4ed3a84c9eb83` |
| `docs/contracts/online-osd-policy-v1/regret_fixed_coarse.json` | `c2d2e352c56c0c891c9c32009f1f0f42f6101d2ad5a2d120676a5793875319e6` |
| `docs/contracts/online-osd-policy-v1/regret_tuned-header.txt` | `7a469e76a8cbbdc07919c6dceeabb50c87a70f6ba52212c8ffeffab630884192` |
| `docs/contracts/online-osd-policy-v1/regret_tuned.json` | `3412f9eff9663a85186db07f6228613b1694995030361fc97810f9c96d9c6dfc` |
| `docs/contracts/online-osd-policy-v1/regret_tuned_distance-header.txt` | `df0b87a329d3e27e5d16f0de063142d22afd39b79b7d1ecb297b9a6113dd201a` |
| `docs/contracts/online-osd-policy-v1/regret_tuned_distance.json` | `9a597bd2a4282d696ce346a6e7ca142689c9c76a6c012feae6d453c9a8eafc21` |
| `docs/contracts/online-osd-policy-v1/regret_variable-header.txt` | `e72d28e3ea73f00d64c7ea88decf56de951383cf66da77d83553d64d420dc7d2` |
| `docs/contracts/online-osd-policy-v1/regret_variable.json` | `39091cb2a39306fef3aa9221440d67958518a837e9c1516f4815fa8aa77676d9` |
| `docs/contracts/online-osd-policy-v1/regret_variable_bound-header.txt` | `e67b0da485e6cf69e0a788146bc692af708c3cfff170f022a33058bcfa7d7361` |
| `docs/contracts/online-osd-policy-v1/regret_variable_bound.json` | `275396a5b0edad4254045b08e5dbb1afeb158382b9d1a7881853e16877941278` |
| `docs/contracts/online-osd-policy-v1/trajectory_finite_loss-header.txt` | `70712b8a584a197c6b433802afcd64a05f64325479e166b68f064deddf82481e` |
| `docs/contracts/online-osd-policy-v1/trajectory_finite_loss.json` | `7c0b92f5925ce4e03c6ad8c0bc1787d2c408011ce7c00b2954aff3e732d74d08` |
| `runs/online-osd-policy-20261004/blind-context-extraction-audit-v3.json` | `5712d530050057bc9c9e4852d89a20e8688426a89abc1c2b710b9ae3e2de23e1` |
| `runs/online-osd-policy-20261004/blind-context-repair-v3.md` | `e51781513af24a9e9edda7762940630c3861ca89c20a30b55e6ec35cf9a83c47` |
| `runs/online-osd-policy-20261004/blind-context-repair.md` | `af01a158dde2ca35ebc214798eea41edce65efdd14dbe940c28f78af0f4c2c77` |
| `runs/online-osd-policy-20261004/blind-imported-context-v2.md` | `2dbc2ee0a8126000fe92750e3487c7af604fb59158779faffb6619d1b8f0ce3f` |
| `runs/online-osd-policy-20261004/blind-imported-context-v3.md` | `bd1bd489ab50d9ce880ba1067266fa60f10b7a2f955040c356a9090fdc292b50` |
| `runs/online-osd-policy-20261004/blind-neutral-name-map.json` | `7dd91a0eb1ab717b4081ce36390eefca4025a4811c23f71dcb7e4f7ee0e79058` |
| `runs/online-osd-policy-20261004/blind-packet-v1.md` | `256e2b80e7d3b4c7862edf64659376bde9dfe55cd9855f3b1ed38645e24a2abc` |
| `runs/online-osd-policy-20261004/blind-packet-v2.md` | `b265670fd56efa3b97dbeef650703ab6eb47aaac186c16e91dba1969d83cadec` |
| `runs/online-osd-policy-20261004/blind-packet-v3.md` | `652d0efc210cf8f2e26e5d822095e7df7128cae7899fc432f627b315333c41f2` |
| `runs/online-osd-policy-20261004/blind-receipt-v1.json` | `4447da85a835c4d46c20cbaa10674f3ebf15c3b269d99c15878d0ffdb7bf2b60` |
| `runs/online-osd-policy-20261004/blind-receipt-v3.json` | `dd0fc7283a9853d27d71eb72859f291928aa193b651b33a6b0517050b575f6e5` |
| `runs/online-osd-policy-20261004/blind-reconstruction-v1.md` | `86f5d6c24a1ea6ab6b2888ce845d87f33e7fddf6ee6c8c97d8ec7c2d1c1ca4a1` |
| `runs/online-osd-policy-20261004/blind-reconstruction-v3.md` | `d15c6760f2c0523f866f036f47f9ffb1d6b1f4d950dd465dc9692536c8bd29a6` |
| `runs/online-osd-policy-20261004/contract-source-inputs-v1.json` | `ddd8fe1611e9bfa8311b1228d89fc2ceab31fd402140c018a7605c5eb18abe35` |
| `runs/online-osd-policy-20261004/contract-source-inputs-v2.json` | `d260e6cdbae5bcf339b44bcd0c2c8ddaecd3eb25748aad341b2ff64293cf038f` |
| `runs/online-osd-policy-20261004/contract-source-inputs-v3.json` | `14c0f6ee9ed0c0490126ea4f0407a0186605a789d9e6e2b3be2ee197d504594d` |
| `runs/online-osd-policy-20261004/draft-freeze.json` | `6511db7d8ec2a1771859332186466d608dad5ca31b4baba67344a958a61043f7` |
| `runs/online-osd-policy-20261004/ogd-source-pages.txt` | `9eb73c470ca04f3cee26996847bb9ea0851004dbcd745265e5cb0efeb87c7894` |
| `runs/online-osd-policy-20261004/packet-contamination-v2.md` | `f2fca99bfd4344c85bdd15cb66a3d363d55f7a6a818b504782e8af74940f8f79` |
| `runs/online-osd-policy-20261004/proof-obligations.json` | `a09ae91ba23ebd39a8554fab27d31d603ad1066e84be76cb3cff743a8747b3d4` |
| `runs/online-osd-policy-20261004/signature-probe-01-exit.json` | `fe34781dd07788b4fd807fda911f279e6a319976e3312b56e3ec84529e677d24` |
| `runs/online-osd-policy-20261004/signature-probe-01.log` | `85f94e67c55660b4c182e79b4b9a5dfc46eeee322956569a9a4a5cac5f045496` |
| `runs/online-osd-policy-20261004/source-card.md` | `2612f0fe7d4f2a58c471aca3f648b38e1f023532917ebfa9ebc8d83c40f45d9e` |
| `runs/online-osd-policy-20261004/source-pages.txt` | `0c251c80c372ea61d3c83a867ad584edb813315ba3b4ffa64b29d5a323de8539` |
| `runs/online-osd-policy-20261004/source-review-packet-v1.md` | `3d1a0ecfa3125be57476e052f30393d91518abe35ae4de1e9861c10109e8075e` |
| `runs/online-osd-policy-20261004/source-review-packet-v2.md` | `dd884b483c6fefd9e34eddda99108d700e83c4ff5439238ad6eeebba4f525ac7` |
| `runs/online-osd-policy-20261004/source-review-packet-v3.md` | `1a8f68e05be036fff452dd15509bf707e861332906c88d8a7c490bd2f477378c` |
| `runs/online-osd-policy-20261004/workflow-audit.json` | `f282730842b924aec578d88845aa6090779597727cb8099e542afa65220bc910` |
| `tmp/online-osd-policy-signature-v1.lean` | `f36ca271bce614126737780c7d1319b2c46ee819f5a5c469de65a3cf3f4542e0` |
