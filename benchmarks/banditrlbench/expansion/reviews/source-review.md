# First-expansion anti-anchored source review

Reviewer: **Codex subagent `/root/source_reviewer`**. Author: **Codex `/root`**. Blind decoder: **Codex subagent `/root/blind_decoder`**. Review date: 2026-11-06.

This is an independent-role **agent review**, not independent human expert gold admission, a calibrated judge, a model trial, or a runtime-isolation certificate. I inspected the pinned owning sources, original questions, references, rubrics, fixtures, target files, plan, family manifest, and the decoder's completed seven-slot reconstruction. I did not execute Lean proofs or alter questions, rubrics, references, or production code.

## Verdict

- **IW semantic verdict: `accepted-with-explicit-delta`.** The NL probability questions are correct. The Lean companion is a normalized signed-weight centered-square identity, with no probability-space or conditional-law claim. It is not formal certification of every NL statement.
- **BE semantic verdict: `accepted-with-explicit-delta`.** The NL questions correctly concern finite, undiscounted, fixed-policy evaluation and uniqueness. The Lean companion identifies a recursively specified function with the library's zero-terminal construction; it is not a trajectory-return or optimality theorem.
- **NL reference/negative-fixture review: accepted for these public-dev controls.** Every reference earns 2 on every stated criterion; every blank, supplied wrong-answer, and placeholder earns 0 on every criterion. These are actual judgments, not scores copied from expected outcomes. No NL question/rubric/reference correction was needed.
- **Family/access verdict: public-dev grouping is coherent; no held-out or access-enforced admission.** A previously omitted IW near-solution alias was found, then verified in the corrected family and task provenance. The current search corpus exposes the proof strategy, so IW-L cannot support an independent-synthesis difficulty claim.
- **Lean agentic rubric remains incomplete.** Kernel replay and genuine tool-trajectory assessment are different gates; this reviewer grants no agentic completion.

## Pinned source identity

The source snapshot is `abc2959ff7c866c47e8bee5714d43a336a857353`. Direct `git show` comparisons verified that the four owning source files below equal their pinned Git blobs after CRLF-to-LF normalization. These are source inspections, not new compiler evidence.

| Source | Pinned Git blob | LF-normalized SHA-256 |
| --- | --- | --- |
| `BanditRLProof/Exp3ImportanceWeighted.lean` | `467601d8cca0100764b7d2243f3a9e95f95af8f3` | `47ea170890f794da1591e25d0ea64859a28ae4cf39df14a80605efa755e29fd4` |
| `BanditRLProof/Exp3ConditionalMoments.lean` | `9b53d79c3d31a631900c533961bc8e8a3f59c7fe` | `c440a156aacdb41b744cb70c84f8d7d722f15e34390dd4105b2c0806c8b53b4e` |
| `BanditRLProof/RL/FiniteHorizonMDP.lean` | `7c9279f560e12f40ea297bfd9cba0e09f2e384d7` | `b69ff6315a120272f572428b4d2aea61022e6433488419d5be7ee4af8e4bd9c1` |
| `BanditRLProof/RL/FiniteHorizonPolicy.lean` | `728166843ef8e8bcd646b79ca916ce6bd55825bd` | `5466b1a517fec04bbedb8e77466622855589a1c57c3369ede5493631b3df6fc6` |
| `BanditRLProof/Exp3ComparatorBernstein.lean` | `45c647ddf53584fff0b0cfeb30d9ab400e36592f` | `6023057b65b5c4551af9e70de08d74c01d01d1db4ca10e82b2d7e51756d95ea0` |

The fifth source was located independently during alias search. Its theorem `BanditRLProof.Exp3.sum_prob_mul_sq_comparatorEstimatorDeviation_eq` at lines 115-148 is materially relevant even though it is outside the target's import closure.

## IW: source, target, and decoder comparison

| Semantic slot | Independent comparison and verdict |
| --- | --- |
| Objects/spaces | `importanceWeightedLoss` is exactly the selected-coordinate quotient, zero otherwise. The target ranges over a finite `Finset` inside an arbitrary action type; the NL question uses a finite nonempty arm model. The decoder correctly avoids assuming the whole action type is finite. **Match with declared representation/generalization delta.** |
| Quantifiers | One arbitrary named coordinate belongs to the finite support. `prob` and `loss` are fixed real functions; no time, random process, adversarial timing, or simultaneous zero-support recovery appears in Lean. The NL conditional question fixes history before drawing one action. **Match.** |
| Assumptions | The target has membership, sum of weights exactly one, and nonzero weight of the named coordinate only. Nonnegativity, positivity of all arms, and bounded losses are absent. The decoder identifies all omissions correctly. Membership already excludes an empty support. Normalization is a genuine premise of the original centered-square question, not an imported proof conclusion. **No EXCESS binder; explicit generalization from probability weights.** |
| Conclusion | The target equals `l_i^2(1/p_i-1)`. Source coordinate cancellation gives mean `l_i`; isolating the named arm gives second moment `l_i^2/p_i`; expanding the square and normalization gives the result. The mixed-square source anchor is related context, not the exact coordinate-variance target or automatically a proof dependency. **Match.** |
| Constants/normalization | Denominator is the named coordinate's actual weight. There is no arm-count factor, exploration floor, horizon factor, or asymptotic claim. The decoder's expression is algebraically identical to the target and to `l_i^2/p_i-l_i^2`. **Match.** |
| Probability/feedback | `Exp3ImportanceWeighted` explicitly labels its results deterministic finite sums. `Exp3ConditionalMoments` additionally identifies an actual conditional action kernel, supplies measurability/integrability, and represents losses as history functions; its displayed results are integrated identities, not the entire NL conditional-moment answer. That module assumes positivity on all support points, while the named-coordinate NL claim needs positivity only at that coordinate. Its ambient `mu` is a finite measure, not intrinsically a probability measure. The decoder correctly refuses to infer conditional expectation, filtration, or observation-law correctness from target A. **Explicit scope delta retained.** |
| Boundary | Signed weights can make the centered weighted sum negative; it is a variance only under a probability-law interpretation. Zero named-coordinate weight is excluded. One-round moments alone establish neither independence across rounds nor a regret rate. **Match.** |

The NL examples withstand direct recomputation. In IW-K, the fair-arm action-dependent loss `L_i=1{I=i}` has estimator mean 1 but loss mean 1/2. In IW-R, `p=(1/4,3/4)`, `l=(1,0)` gives estimates 4 and 0, mean 1, and variance `(1/4)9+(3/4)1=3`. Defining division by zero cannot recover an arm's unobserved nonzero loss.

### Material alias finding

`BanditRLProof.Exp3.sum_prob_mul_sq_comparatorEstimatorDeviation_eq` in `Exp3ComparatorBernstein.lean` already proves the same centered-moment formula under `FiniteActionDistribution arms prob` (nonnegativity plus normalization). Its proof uses only the normalization field and the same coordinate moments and square expansion. IW-L weakens its assumptions to permit signed normalized weights, so the exact stated target is not supplied as an imported theorem. Nevertheless, the permitted full-library text search exposes a near-complete proof. An import restriction does not remove text/proof retrieval leakage.

Correction verified: the family manifest and all three IW task records now include this exact declaration alias, a commit-pinned source link at line 115, the source-file hash in their environment manifests, and the signed-weight assumption delta. PLAN.md records the independent inventory correction. All IW views remain public dev, and difficulty is explicitly unmeasured. This resolves the identified provenance omission without changing a question or target. IW-L is retrieval/adaptation, with no independent-synthesis claim.

## BE: source, target, and decoder comparison

| Semantic slot | Independent comparison and verdict |
| --- | --- |
| Objects/spaces | `MDP` has finite state/action types with measurable spaces, a Markov transition kernel, a natural horizon, and deterministic measurable real reward. The pinned signatures use time-homogeneous `reward : State -> Action -> Real` and `transition : Kernel (State x Action) State`; only policy kernels vary by stage. The decoder prudently called those signatures unspecified in its abbreviated packet. Source inspection resolves the ambiguity and agrees with the NL model. **Match with source clarification.** |
| Quantifiers | For every supplied MDP, fixed Markov policy, and sequence `v : Nat -> State -> Real`, terminal and step equalities imply equality to `valueAt` at every queried stage `stage <= horizon`. The step premise covers every earlier stage, with whole-function equality. Values after the horizon are unconstrained. **Match.** |
| Assumptions | Zero terminal data and the Bellman recurrence are source premises of this uniqueness question. They are not smuggled proof ingredients for an existence/trajectory theorem. There is no discount, bounded-reward, contraction, or extra continuity requirement. No explicit nonempty-type premise is added. The decoder's audit agrees. **No EXCESS binder.** |
| Conclusion | `v stage = policy.valueAt stage hstage` asserts uniqueness relative to the library construction. Source `valueAt_horizon` and `valueAt_bellman` supply the canonical sequence's terminal and step facts. The NL two-sequence proof follows by backward substitution of equal continuations. No maximization appears. **Match.** |
| Constants/normalization | Terminal function is zero, chronological decision stages are `0,...,H-1`, and both reward and continuation coefficients are one. Policy and transition normalizations come from Markov-kernel structure. Horizon zero is included. **Match.** |
| Probability/feedback | `bellman` integrates `reward + transitionValue` under the stage's policy kernel. The conclusion is a deterministic equality of recursively defined functions. Finite carrier types do not force discrete measurable spaces, and the target does not itself establish an expected-trajectory-return representation or a general singleton-sum formula. The NL probability-table model is the usual discrete specialization. The decoder correctly distinguishes these. **Explicit representation/scope delta retained.** |
| Boundary | No infinite-horizon, nonzero-terminal, approximate-recursion, optimal-control, learning/regret, or unrestricted history-dependent-policy guarantee follows. The zero-reward one-state self-loop is the identity operator, so it is nonexpansive, not strictly contractive. With no terminal condition, both all-zero and all-one sequences satisfy every finite recursion. **Match.** |

The absence of an explicit measurability premise on arbitrary `v` does not invalidate this uniqueness proof: equal terminal data and repeated application of the same total Bellman map determine every valid stage. A trajectory interpretation needs its own semantic theorem. No source repair is proposed.

## Natural-language criterion review

The four `tests/review.json` files bind each response using SHA-256 of the exact UTF-8 `read_text` result, and bind each rubric using SHA-256 after CRLF-to-LF normalization. Every criterion has its own score and reason. Running `nl_check` over all 16 fixtures confirmed the review bindings and axis arithmetic; that check does not validate mathematical meaning.

| Task | Reference by axis | Each of no-op, wrong-answer, placeholder |
| --- | --- | --- |
| BRB-IW-K | factual-accuracy 4/4; understanding 6/6 | factual-accuracy 0/4; understanding 0/6 |
| BRB-IW-R | reasoning 6/6; understanding 2/2 | reasoning 0/6; understanding 0/2 |
| BRB-BE-K | factual-accuracy 4/4; understanding 4/4 | factual-accuracy 0/4; understanding 0/4 |
| BRB-BE-R | reasoning 6/6; understanding 2/2 | reasoning 0/6; understanding 0/2 |

These totals are development-control judgments on supplied answers, not model capability scores, difficulty estimates, or human agreement. The two Lean rubrics also require authentic search/dependency/construction/compiler trajectories as criterion c2. A successful reference compile alone cannot satisfy that criterion or the full rubric's all-criteria rule. The corrected runner now labels Lean reference results `fixed-target kernel control only` and explicitly reports c2 as unassessed pending independent trajectory review. This resolves the reporting ambiguity; c2 and agentic completion remain pending.

## Family, alias, split, and staging audit

All six tasks are `draft`, `dev`, and map to their declared family. Each family contains K/R/L views and its listed reference aliases; no listed alias crosses a split. All four legacy cores are also public dev. BRB-004 shares the broad topic of estimator semantics but asks about interval coverage, bias, and dependent errors, not inverse-probability moments; no exact duplicated answer was found in those four legacy cores. The new IW source alias above is stronger and must be tracked. The local search is not an exhaustive web/training-corpus contamination audit.

I executed the prompt-only exporter in temporary scratch and checked all six rows. Every row contained only the allowed metadata, exact `instruction.md`, and exact `environment/workspace` contents; there was no `training_solution`, reference, test, rubric, or review field. NL workspaces contained only the closed-book `README.txt`; Lean workspaces contained only `target.json`. The inspected package trees had no linked files. This is an export/staging inventory check only. The full accessible library, repository checkout, Git history, compiled artifacts, image layers, filesystem permissions, and a live agent's tools were not isolated by this check.

A public checkout contains answers, tests, and reviews. In admitted runs these must be excluded from every reachable image layer, mount, history, workspace, and retrieval service; NL closed-book access and Lean-only permitted corpora need runtime enforcement. A network prohibition printed in an instruction does not disable the network. The declared image digest, isolation receipt, process-tree CPU/memory/time limits, token/tool-call enforcement, and executed Harbor/container adapter remain admission gates, not accomplishments of these local controls. Compiled imported artifacts remain trusted build inputs unless independently rebuilt and bound to source/toolchain evidence.

Additional gaps before capability or held-out claims: genuine agent trajectories and repeated trials; independent human expert review/agreement and judge calibration if an automatic judge is used; reviewed family/near-solution grouping against all release corpora; and executed adversarial solution/verifier access probes. The current public-dev export is appropriate only with these limits visible.

## Bound review inputs

Hashes below are SHA-256 of file bytes after CRLF-to-LF normalization. Each Lean `target.json` binds both the exact signature and its imports list; the imported owning-source files are separately bound above. Role/evidence updates to `task.json` do not alter these reviewed mathematical inputs. Any change to a question, reference, rubric, target, or decoder report requires a fresh binding/review rather than silently inheriting this verdict.

| Input relative to `benchmarks/banditrlbench` | LF-normalized SHA-256 |
| --- | --- |
| `expansion/reviews/blind-packet.txt` | `5fdfb11fd94f4ff48332a3f59e54f3ce7a6d0f03d3045ebb11dd4d377f7e8389` |
| `expansion/reviews/blind-decoder.md` | `3c3dc0fc2c2c24bb7219a161d118b0aef7ce67b85df01a8f83cdb5296d7b255d` |
| `expansion/PLAN.md` | `7f164c2872410fcd231af46f77be7028f4b1ab8a93c2d2e0626a7af4118a3a20` |
| `expansion/families.json` | `23fdb4c88cbcc90f8c11f36a48a9cd82b5a6f67be699c69357b8ed1b43e97726` |
| `tasks/BRB-IW-K/instruction.md` | `b5a31e66a9603aefa1c38238918922f8961dd377aad8ecba5c214c87fb20fb97` |
| `tasks/BRB-IW-K/solution/reference.txt` | `00307129851e481065d24d57124c62e45769c91ed6bf1b7047a76c1aab43cadf` |
| `tasks/BRB-IW-K/tests/rubric.json` | `1deaf3db8f1ca02df1c298c6dd08e74e9548a80aea27bacbfcf7b75ff09f155a` |
| `tasks/BRB-IW-K/tests/review.json` | `308214fe22603f96e5c3bcafedf94fd3ac77833ba296589d52e290f325ad5852` |
| `tasks/BRB-IW-R/instruction.md` | `9617eff72ea2ad5f54dbc22235d73e500800b9b388d4a067bb7e1a8b0332be19` |
| `tasks/BRB-IW-R/solution/reference.txt` | `6d0471cc306c5aa69fad1b24d20c139f2f22716990eaf77504fb1fbc51a0713f` |
| `tasks/BRB-IW-R/tests/rubric.json` | `6e0f86c11e1c5218e2b8ea046bb3be49610f4765379c2102cf2a97b197d50f8c` |
| `tasks/BRB-IW-R/tests/review.json` | `116542e4a560ceae1fc73834cca55c8bcbb469ac34eb800a7a7c3e2532ea6ee0` |
| `tasks/BRB-IW-L/instruction.md` | `9ad89ac0536f30cebc7e9c518bb7742c28f798bd87912225167d50ab74b875a9` |
| `tasks/BRB-IW-L/solution/reference.txt` | `ef9d8a3f84223fd04f2d0a0d3402902460e493f5f13a1b0554fdf069022b798f` |
| `tasks/BRB-IW-L/tests/rubric.json` | `5199acdec0c3a68d20c669353aa8584cf28381beb747ee6ae2746120aac68d7d` |
| `tasks/BRB-IW-L/environment/workspace/target.json` | `c7bc192e3980f5a4f8c0e98196339353c596d60fa57a4eed432f9249f3f02f3e` |
| `tasks/BRB-BE-K/instruction.md` | `808b8b2e5efc0d2309a9886b0a3f02f128bba4e2c3d3a77e203a519ef8c3a79b` |
| `tasks/BRB-BE-K/solution/reference.txt` | `4caa3d3af871a3e07580c1832ab7ec9a538fd532ab3f100cef734ac1b86ba499` |
| `tasks/BRB-BE-K/tests/rubric.json` | `4a47efd7fe79f1f6cf5d7fb339ce117045dba4ba70504969bf4c816502c404d7` |
| `tasks/BRB-BE-K/tests/review.json` | `4ca24ea58f6657e3f1cacac08676fd3e94f84069d1c5c6e512dabee21445789e` |
| `tasks/BRB-BE-R/instruction.md` | `be0375b22aae06feb7e7430614e4b6cc04d75ea68ecd744ebeabe858da9412ee` |
| `tasks/BRB-BE-R/solution/reference.txt` | `54b537c855f73a643351680fbc1af467aabd8495678cad4e44a698ee3b90aa60` |
| `tasks/BRB-BE-R/tests/rubric.json` | `04b7822f637b4f3741c006406e1d974d1185609d35f6e87e22198ce660ab2703` |
| `tasks/BRB-BE-R/tests/review.json` | `488ad81b29be4b5687f41a9fd58811cd1726c313235f55b468cf337b91b7dba3` |
| `tasks/BRB-BE-L/instruction.md` | `a5da0cb6b9383f0d7dcb0df94e9d55aa2dd97bcb6d78d84156eef1e9ff036817` |
| `tasks/BRB-BE-L/solution/reference.txt` | `53fc2d4715bd7739263bcb673608f5d0a9da1bfa1b85ef98ec7cedf65f114dc5` |
| `tasks/BRB-BE-L/tests/rubric.json` | `5199acdec0c3a68d20c669353aa8584cf28381beb747ee6ae2746120aac68d7d` |
| `tasks/BRB-BE-L/environment/workspace/target.json` | `d4c01d68bfdef0bd5704639d5af5ea6903c4e673e2a82bceddc4130e0623bf4a` |

This report grants semantic acceptance only with the stated deltas and development limits. Human expert gold admission, isolated evaluation, full agentic rubric completion, and held-out eligibility remain **not granted**.
