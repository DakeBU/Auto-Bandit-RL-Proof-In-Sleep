from common import *
fixed()
assert load(RUN/'draft-type-probe-inspected-v3.json')['actual_exit']==0
capture('retrieval-EReal-corrected-v2','rg','-n','theorem coe_toReal','.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean')
historical=ROOT/'runs/online-ch2-prescient-cumulative-20261009/director-architect-draft-v1.md'
assert 'Full unconditional choiceability' in historical.read_text(encoding='utf8')
write(CONTRACT/'source-obligation-classification-proposal-v1.json',dict(
 status='PROPOSED; no canonical closure or old contract edit',
 pinned_source=rows([CONTRACT/'source-card-v1.json',RUN/'source-pdf277.txt',RUN/'source-pdf278.txt']),
 historical_artifact=rows([historical]),
 historical_phrase='Full unconditional choiceability, sourceclosedness packaging, all chapter containers remain required/open.',
 source_theorem_intention='Algorithm15.8 argmin updates and Theorem15.30 valid interior run imply both exact fixed/variable printed regret inequalities. No separate universal existence theorem is stated there.',
 proposed_classification='Keep actual valid-run/update, source loss/generator transport and both printed endpoint obligations REQUIRED. Once six frozen terminals and full canaries/gates/review are accepted, historical unconditional-choiceability phrase is classified overbroad draft intent, not a source theorem weakened to fit API. Universal attainment is false in the existing exponential example; keep counterexample and generic failure semantics visible. Do not infer chapter completion or close any of eight containers now.',
 mathematical_obstruction='V=(-infinity,0], X=R, psi(z)=exp(z), loss(z)=z, x0=0, eta=1: penalized objective exp(z)-1 has unattained infimum -1 on V. Strict convexity and closedness do not give coercivity. Existing public canary proves this with actual source regularizer assumptions.',
 source_erratum_claim=False,
 review_required='Separate anti-anchored source intention classification; do not silently delete hard obligations. Accepted old proof terminal contracts unchanged.'
))
write(CONTRACT/'semantic-signature-draft-v1.json',dict(
 objects='Helpers arbitrary/inner-product/complete spaces as individually scoped; source endpoints real finite-dimensional E, V subset X, canonical extended losses and ordered divergence.',
 quantifiers='One fixed actual algorithm, all comparator u in V. Given trajectory x is input to theorem but identified with current-loss recursion by uniqueness; no assumed hseq or future-aware algorithm existence.',
 assumptions='Source loss codomain no-bottom globally; finite on nonempty V; global source supports at each feasible point. Strict psi on X, closed restriction encoded by canonical indicator, differentiable on interior X. Actual feasible extended-real minima and interior states, positive played steps. Source wrappers explicitly retain closedness/nonempty/finite-dimensional assumptions.',
 conclusions='Properness producer, strict actual real objective, unique selected minimum, exact actual iterate identity, printed fixed and variable finite-max bounds preserving negative movement terms.',
 normalization='Lean loss t/source loss_(t+1), x(t+1) paid after loss t, x0 initial. Divergence target first/base second. T=0 fixed allowed; variable T>0 with max over previous states0..T-1, denominator eta(T-1), played-pair monotonicity. toReal only on finite feasible compared points.',
 information='Prescient current WHOLE-loss feedback before paying current action; causal prefix certified upstream. Noncomputable classical mathematical minimizer, not executable/measurable optimizer.',
 evidence_authority='Types only currently. Distinct decoder/reviewer required. Proof/body/axiom/full-root-Test-harness/site/publication gates later. Native conversion window exists contemporaneously before stabilization, conventions not all runtime-enforced.',
 boundary='No universal attainment/interior preservation claim, no bounded V assumption, no future feedback, no arbitrary loss-toReal convexity outside V, no source Bregman validity at nondifferentiable boundary. Generic strict helper total-fderiv linearity is algebra only. Chapter2/allCh1-16Goal incomplete.'
))
write(RUN/'source-review-request-v1.md','''# Anti-anchored contract review request

Root formalizer requests independent contract review, not proof acceptance. Inspect pinned source pages277/278, page26 Chapter2 forward context, pages28/29 definitions, pages75/76 Bregman conventions, source-card/headers-draft-v2 exact contexts, draft-type-probe-inspected-v3 (actual0), dependency-DAG and semantic-signature drafts, contemporaneous native conversion receipts/window, neutral-packet-v2 and distinct blind reconstruction when ready. Source source-obligation-classification-proposal-v1 is a separate proposed correction of historical DRAFT wording, not a source erratum or accepted theorem edit.

Search seven slots for mismatch, especially valid-run vs universal attainment, source loss no-bottom/finite feasible domain, canonical closed generator on X, no topology on proper helper, scopes/completeness, source indexing/current whole-loss information, finite MAX previous states and signed movements, fixed T0. Decide separately on six target contracts and historical wording classification. Do not infer chapter/container closure. Root can direct/architect/formalize/worker, but not self-certify decoder/source review. Reused actor history limits, requested Astra/medium, no human/external/absolute-blind/runtime attestation. Body/canary/full integration review must follow later.
''')
write(RUN/'retrieval-failures-v1.json',dict(failures=[
 dict(step='first v1 EReal source query',actual_exit=2,reason='literal leading backslash path typo; corrected v2 actual0'),
 dict(step='read-only guessed helper filenames',reason='OnlineExtendedProximal absent; later tools/statement_fence.py, lean_source.py, lifecycle.py absent; actual files found via rg --files as OnlineBregmanExtended.lean and tools/abrl_lifecycle.py'),
 dict(step='read-only old package glob queries',reason='literal PowerShell wildcard rejected OS123; explicit located file read instead')],proof_failures=0))
fixed()
