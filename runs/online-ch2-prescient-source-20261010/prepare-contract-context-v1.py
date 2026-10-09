from common import *
fixed()
window = ROOT/'conversion-windows'/(TASK+'.md')
assert not window.exists()
capture('native-conversion-window-create-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','conversion-window',TASK,'--title','Source losses and unique prescient updates')
write(RUN/'native-conversion-window-exact-before-v1.json',dict(path=window.relative_to(ROOT).as_posix(),sha256=sha(window),before_raw_base64=base64.b64encode(window.read_bytes()).decode('ascii'), provenance='Contemporaneous actual native CLI template, before filling, before stabilization/proof.'))
nodes=[
 ['sourceProper_of_domain',[], 'nonempty feasible witness, EReal.coe_toReal, no-bottom globally'],
 ['penalized_strictConvex',['finitePart_convex_of_subdifferentiable'], 'positive inverse, strict convexity on V, affine derivative cancellation'],
 ['advance_eq_some_of_minimizer',['penalized_strictConvex','proximal_finitePart_minimizer_iff','StrictConvexOn.eq_of_isMinOn'], 'finite feasible values; actual selected minimum equals supplied unique minimum'],
 ['iterate_eq_of_source_updates',['advance_eq_some_of_minimizer','iterate'], 'induction through T; no hseq input, current loss only'],
 ['source_fixed_regret',['sourceProper_of_domain','iterate_eq_of_source_updates','iterate_fixed_regret'], 'source finite-domain/no-bottom to properness, actual recursive identity, printed fixed conclusion'],
 ['source_variable_regret',['sourceProper_of_domain','iterate_eq_of_source_updates','iterate_variable_regret'], 'same actual identity; played-pair monotonicity; exact previous-state finite maximum']
]
write(CONTRACT/'dependency-DAG-draft-v1.json',dict(nodes=[dict(name=n,dependencies=d,route=r,status='draft-open') for n,d,r in nodes], lower_routes=1, count_boundary='Six Lean terminals, not six source results or chapter coverage denominator.'))
text = '''# Conversion Window: Source losses and unique prescient updates

Task id: `ONLINE-CH2-PRESCIENT-SOURCE-20261010`
Source card: `docs/contracts/online-ch2-prescient-source-v1/source-card-v1.json`
Scenario: prescient current whole-loss feedback before the paid action; deterministic, no probabilistic semantics.

## Natural-Language Statement

Orabona v10 Algorithm15.8 and Theorem15.30, printed265-266/PDF277-278, required Chapter2 forward dependency. A valid source argmin run is identified with the existing partial canonical recursion using uniqueness, then receives the printed fixed and variable bounds. It is not a claim of universal argmin attainment. Exact draft headers and binder contexts are in headers-draft-v2.json. Finite-dimensional source endpoints infer completeness; helper scopes are separately listed.

## Lean Mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| loss_t | current extended-real loss with no minus infinity | loss t : E -> EReal | source t=1..T maps to Lean t=0..T-1 | draft |
| x_t | paid current minimizer | x (t+1) | base is x t, initial x0 | draft |
| B_psi(a;b) | target first, interior base second | OnlineBregman.divergence psi a b | ambient representative restricted to X | existing |
| argmin | actual attained extended-real minimum | IsMinOn plus feasible point | not a regret/stability premise | draft |
| psi closed on X | closed extended-real restriction | SourceClosed (coe psi + extendedIndicator X) | canonical zero/top indicator | draft |

## Assumption Ledger

Source endpoints: real finite-dimensional inner-product space, V nonempty/closed/convex subset X, real ambient representative psi strictly convex on X and differentiable on interior X, canonical restricted generator closed, x0 in interior X, all supplied updated states in interior X, positive played steps, global no-bottom losses and V subset effective domain, global supporting subgradients at all feasible points. Variable endpoint requires T>0 and nonincrease only between played steps. Fixed endpoint allows T=0. Given actual attained minima are the algorithm's run hypothesis. No bounded V, future feedback input, global convexity of total toReal, source regularizer value outside X, or source attainment from closedness/strictness is assumed.

The strict objective helper has no interior/differentiability/closedness premise: its total derivative is linear, so this is algebraic strict convexity only. Source endpoints license the intended Bregman semantics at their interior bases. The initial state need not lie in V or a loss domain. Comparator lies in V. T=0 fixed loss sum is empty; variable finite maximum is never taken over an empty set.

## Local API And Proof Route

Reuse canonical divergence/advance/iterate and actual-minimum bridge. First prove the properness producer, then strict objective, uniqueness, recursive identification, and source endpoint transports. Readiness is the DAG below; one lower route. No external dependency/toolchain change. No theorem bodies before distinct contract review and stabilization.

## Proof-DAG

See `docs/contracts/online-ch2-prescient-source-v1/dependency-DAG-draft-v1.json`. SourceProper producer has two real endpoint consumers. No extra shared clone, no per-Book library. Global SGB frontier and registry remain unchanged during draft/proving.

## Gaps

All six terminals remain open before proving. Full chapter and eight required forward containers remain open. The historical unconditional-choiceability wording versus source conditional valid-run guarantee needs a separate source audit/classification, not silent deletion. Closedness assumptions remain in source wrappers even when the conditional argument does not use them. No universal attainment or new source erratum is claimed.
'''
window.write_bytes(text.encode('utf8'))
write(RUN/'conversion-window-filled-v1.json',dict(after=rows([window]), before_receipt='native-conversion-window-exact-before-v1.json', status='draft-filled, not stabilized'))
write(RUN/'upper-director-v1.md','''# Director

One integration-node package, required Chapter2 prescient forward chain; Chapters1-16 Goal active. Preserve all parent contracts and all eight chapter forward containers open. Source theorem guarantee is conditional on an actual valid interior argmin run; audit historical universal attainment wording independently before classification. Six fixed terminal candidates have finite scope and actual consumers. Root directs/formalizes/proves in separated phases; distinct reused decoder/reviewer are mandatory under AGENTS, not parallel proof arms.

Reader delta later: source-vs-Lean hypotheses, prescient feedback timing, properness and uniqueness argument, both exact printed bounds, nonattainment boundary. Lean graph: new integration nodes only after compiler proof edges. Overview: bounded dependency advance, chapter still partial. Functor: none-found-with-reason; transports representation of the same algorithm, not a new cross-setting mechanism. No publication/registry edits until focused evidence and approved plan. No merge/deploy authorization.
''')
write(RUN/'lower-architect-v1.md','''# Architect

Route is finite witness -> strict penalized objective -> unique actual selected minimum -> induction identifying the given source run -> source fixed/variable endpoint transport through existing cumulative proofs. SourceProper helper arbitrary E; strict helper inner-product E; actual algorithm helpers CompleteSpace; source endpoints FiniteDimensional (no independent CompleteSpace premise). Existing finitePart convexity uses global supports only on V, not convexity of outside toReal. Strictness plus eta inverse positivity handles affine Bregman terms without regularity at arbitrary helper base. Actual EReal minimizers transport to finite real objective before StrictConvexOn.eq_of_isMinOn. No endpoint edits in tactic repair; repeated failure triggers typed audit. First ready leaf sourceProper_of_domain; not yet authorized by stabilization.
''')
event('native-draft-event-v1','draft',dict(task=TASK,contract=str(CONTRACT.relative_to(ROOT)),terminal_count=6,goal_scope='Chapters1-16 active; chapter2 incomplete',conversion_window=str(window.relative_to(ROOT))))
write(RUN/'memory_digest.md','''# Working digest

Draft six-terminal source-run transport package on exact unmerged PR212 head547137ea. Six types under probe, no theorem proof yet. Native conversion window actually created/fill recorded before stabilization. Preserve all eight required source forward containers until distinct source classification review. First ready leaf is properness from nonempty finite feasible domain/global no-bottom. Later gates: neutral reconstruction, independent anti-anchored review, frozen fingerprints, actual proofs and nondegenerate public canaries, axioms/root/Tests/full harness, shared registry/reader publication/site/review/PR. Whole-book Goal remains active.
''')
fixed()
