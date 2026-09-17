# Extended topics: frozen development and evaluation contract

**Scope amendment, 2026-09-17:** the user has now made ALL TEN directory topics
mandatory under a persistent active Goal. `ALL-TOPICS-LEDGER.json` governs this
expanded program. The two-target controlled design below is retained as an
unexecuted historical protocol; it does not delimit the new target set. A v2
all-topic evaluation protocol must be frozen before any formal runs. The primary
heavy-tail contract and all unresolved obligations remain in force. Earlier
triage decisions to defer a topic describe ordering only, not exemptions.

Freeze date: 2026-09-17, before new interface implementation. Base library:
`eedcda1db4d84f6bd69ec6ee50e174f6cf4056ac`; Lean/Mathlib 4.29.1 and the committed
lake manifest. Online Learning branches are excluded. This is a descriptive
development case, NOT a randomized productivity experiment.

## Primary scientific endpoint (HT-TRUNC)

Reconstruct the known robust-UCB truncated-mean route of Bubeck, Cesa-Bianchi,
Lugosi, *Bandits with heavy tail*, arXiv:1209.1727v1, Sections 2 and 2.1,
cross-checked against the 2013 IEEE version. Source discrepancies must remain
visible: the preprint's t^-2 index schedule and its t^-3 failure calculation
do not directly agree; no literal source-constant theorem is frozen as valid
until this is resolved. Preserve the endpoint obligation rather than silently
replacing it by a conditional regret consumer.

Model: finite K>0, stationary independent arm streams, known epsilon in (0,1]
and known u>0, E|X_i|^(1+epsilon)<=u (RAW absolute moment). Actual reward is
the next unused coordinate of the selected arm; action depends on preceding
history. At round t the truncated estimator uses sample-index thresholds
B(s,t)=(u*(s+1)/log(1/delta_t))^(1/(1+epsilon)). A selected-prefix identity
must retain BOTH sample index and evaluation time. The infinite stream is a
construction device, not an assertion that adaptively observed rewards are IID.

Required chain: measurable causal policy/history; transformed observed-prefix
identity; moment-derived bias and truncated second moment; two-sided Bernstein
concentration at every fixed prefix; finite union at the random count; selection
and count bounds; expected finite-horizon pseudo-regret with explicit constants.
Raw realized-reward regret and unbounded stopping horizons are not this target.
General conditional-moment noise and unknown-parameter adaptivity are separate
targets, not implicit consequences. No sub-Gaussian assumption on X is allowed.

Lifecycle starts draft. Stabilized requires exact source/version/constants and
semantic review; proving requires frozen definitions; candidate requires all
obligations and gates; accepted requires independent semantic review. Compiled
leaves may coexist with an incomplete endpoint. Record failed routes and repairs.

## Reserved transfer target (TRANSFER-CLIP)

Freeze before interface design: replace hard truncation by winsorization
clip_B(x)=max(-B,min(B,x)), and allow an observed prefix corrupted by c_s with
sum |c_s|<=C. Prove the actual selected-prefix estimator perturbation <=C/n
and consume a common estimator-error interface with moment bias plus fluctuation
plus corruption. Derivation is an adaptation, not a claim to reproduce a
published corruption-robust algorithm. Acceptance requires a proof importing and
using the new interface with nonzero B,C and n; an alias is insufficient.
Only this target statement is reserved; its solution has not been inspected.
This is a prospective development transfer, not a blinded independent benchmark.

## Claim--evidence matrix

| Claim | Required evidence | Unit | Current status |
|---|---|---|---|
| Faithful new-setting guarantee | entire HT-TRUNC chain, source audit, no missing producer | source contract | unproved |
| Useful existing library | elaborated type/value references to frozen-base declarations and explanation of mathematical role | endpoint | unmeasured |
| Reusable new interface | actual TRANSFER-CLIP producer and consumer | reserved target | unproved |
| Diagnosis | source/assumption gaps with counterexample or explicit proof obligation | diagnosis | source schedule discrepancy to check |
| Efficiency benefit | matched independent runs, equal model/budget/tool access | target, repeats nested | NOT RUN |

## Controlled evaluation protocol v1 (execution disabled)

Arms: Mathlib-only versus Mathlib+frozen base BanditRLlib. Same exact target
statement, primary-source packet, Lean version and dependencies. Optional
documentation-only arm must not contain proof bodies. Target set initially
HT-TRUNC and TRANSFER-CLIP; because the present developer has seen both, subsequent
runs must use fresh isolated agents with no conversation/cache/retrieval carryover.
Do not count these development attempts as repeats.

Requested model/thinking: the task's configured model, medium; actual model ID
and accessible effort must be recorded by runner, never inferred. Three matched
repeats per target, 120-minute wall limit and 60,000 observable-token cap each;
if token usage unavailable, token cap cannot be enforced and the run is invalid
for the frozen token-budget comparison. No paid execution authorized here.
Run order randomized within each pair with recorded seed 20260917.

Allowed inputs: frozen target packet and arm-specific source tree. Mathlib-only
must have no project oleans, indirect project imports, retrieval index, generated
answers, common build directory or external home-cache access. Rebuild isolated
environments; audit actual import closure, not just textual imports. A baseline
may develop its own correct mathematics. Do not intentionally weaken it.

Primary scoring: binary exact-contract endpoint completion after compiler,
axiom and semantic audit. Also report required obligations still open, repairs,
timeout/failure, wall time, tool calls, observed tokens (null if unavailable),
human intervention and build cost. Compile success is not semantic acceptance.
Aggregate repeats within each target; equal weight across targets. With two
related targets use descriptive paired differences only, no significance claim.
All failed and timed-out runs remain in the denominator. Any protocol change
requires a new version before affected execution; no retrospective retuning.

Acceptance gates: public root, Tests, axiom audit, full `python tools/bandit.py
check`, website validation; bind graph and counts to exact source commit. Keep
teaching edges, source mapping and elaborated type/value references separate.
