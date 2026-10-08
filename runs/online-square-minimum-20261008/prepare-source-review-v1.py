from common_v1 import *
fixed()
b=load(RUN/'blind-receipt-v1.json')
assert b['actor']['task']=='/root/osd_blind' and sha(b['report'])==b['report_sha256']
assert not b.get('ambiguities',[])
required=[
 ('R1','Keep source printed2 square minimum, printed3 actual empirical-mean minimizer, printed4 theorem1.3 and printed5 refined bound distinct; six derived producers/representation/adapters are not six printed theorems.'),
 ('R2','The real sInf benchmark must be proved nonempty and attained by the actual feasible empirical mean; no assumed minimizer or totalized-inf shortcut. Positive-horizon uniqueness is separate; T0 is only the explicitly disclosed empty-prefix extension.'),
 ('R3','Retain interval targets for the same finite prefix, source rounds1..T versus Lean0..T-1, and refined source2..T versus range(T-1) with real denominator t+2; performance endpoints require T>0.'),
 ('R4','Generic identities/order consume an arbitrary supplied real prediction trace and do not assert its feasibility or causality. Performance endpoints use the actual meanPredict first1/2 and later strict-past empirical mean, not an arbitrary future-aware algorithm or arbitrary initialization.'),
 ('R5','Keep signed pathwise best-fixed and comparator regret; their values may be negative. No nonnegative regret, absolute-value/rate/ordinary-limit claim follows from the minimum representation.'),
 ('R6','Do not interchange expectation and a hindsight minimum. Printed1-2 minimum of expected fixed loss and causal cumulative IID variance benchmark remain required next, distinct from this produced pathwise minimum.'),
 ('R7','Reuse the actual shared empiricalMean/comparatorRegret/meanPredict and existing theorem1.3/refined proofs in the same library and registry. Draft closed-Prop/whole-definition equality compilation is separate from actual theorem-body proof; disclose every actual source delta.'),
 ('R8','Keep source/compiled-body/canary/kernel/combined/root/Tests/harness/reader/site/native/PR gates separately evidenced. Only bounded square-minimum hinge may close;16C1sourceitems/proof-totalnull, five main-relative modules, full C1, incompleteC2,3-16/necessaryappendices and active totalGoal remain required. OPENunmergedPR192stack is not main/live completion.')]
write(CONTRACT/'reader-requirements-v1.json',[dict(id=i,requirement=r,status='future-required') for i,r in required])
write(RUN/'canary-plan-v1.json',dict(status='prospective only, no canary proof yet',
    cases=['ActualT0 empty minimum and regret0 without uniqueness',
      'Fixed infinite alternating0/1 targets: T2 actual empiricalmean1/2 and minimumcost1/2',
      'PositiveT2 uniqueness instantiated from existing empiricalMean_unique, not asserted atT0',
      'Actual strict-past meanPredict T1 regret1/4 andT2 regret3/4 with same produced minimum',
      'Fixed time-only alternating prediction, independent of losses/comparator: T2 actual signed best regret -1/2',
      'Actual fixed comparators0/1 order relative to produced same-horizon minimum',
      'Nonbinary finite data1/4,3/4: actual mean1/2 and minimum1/8',
      'Actual theorem1.3 and refined endpoint calls at nondegenerate prefixes'],
    no_IID_simulation_or_future_trace_substitution=True, source_package_accepted=False,chapter_complete=False,goal_complete=False))
write(RUN/'source-contract-packet-v1.md','''# Mandatory distinct source/type CONTRACT review

Reuse /root/source_reviewer, GPT-6 Astra/medium, disclosed prior automated staged history, no human/external/runtime claim. Source Orabona1912.13213v10/2026-06-21 pinned PDF SHAcef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Independently read/view current source14-17 caches and pinned PDF as needed, rehash every input. Search for mismatches against source rather than endorse formalizer; read six exact prospective headers, ONE real sInf best-regret definition, four neutral definitions/six reconstructed propositions, actual pinned type/API/definition identity logs, and actual reused Mean/FTL/Regret/Foundations bodies. No new theorem bodies exist yet. Compile0 alone does not prove math or source fidelity.

Audit first finite prefix producer: hy only prefix[0,1], positiveT actual meanfeas/globalmin; T0 empty sum/defaultmean0 explicitly library-only/no uniqueness. Source argmin atpositiveT has uniqueness proved by oldempiricalMean_unique, reused canary planned; this package only claims a produced attained minimum/real value, not a new generic argmin existence theorem or closure of allC1mean obligations. No actual sInf empty/unbounded set premise is hidden. Providedprediction equality/order can be any real trace: representation generalization, not feasible/causal learner producer. Actual two performance endpoints are exactly first1/2 strict-past source strategy; source any-initial family already separate/does not inheritsharpquarter.

Four representation/order results and two literal-minimum adapters have purpose: close explicit source best-fixed-minimum representation, not inflate rate math. Same prefix/horizon/actual losses/comparator. Source4+4lnT and sharpquartertail/source2..T preserved. Signed bestregret can be negative; canary prospective time-only learner on fixed exogenous alternatingtargets produces -1/2 atT2 without futureinput. Do not infer sourceIID expected-excess nonnegativity or swap min/expectation: source printed1-2 expectation outsidefixedminimum is REQUIRED next. Five older main-relative audits unwaived,16C1sourceitems/prooftotalnull/Chapter1open/2incomplete/3-16unenumerated/necessaryappendicesrequired/GoalACTIVE. ExactOPENdraft/unmergedPR192stack notmain/live. Old inventories/previous accepted receipts/math/globalSGB/pins/sharedlinks untouched.

Evaluate exact R1-R8 reader-requirements-v1 and retain their ORIGINAL text as future corrections, not yet discharge since reader/BODY/FINAL gates absent. Sourcecontract can stabilize only if math target/source delta explicit. If needed propose precise versioned repair, never weaken six terminal headers silently. Write ONLY source-contract-review-v1.md and source-contract-receipt-v1.json. actor.task=/root/source_reviewer; verdict accepted|accepted-with-explicit-delta|rejected; report/report_sha256;fixed_input_count; reviewed_files every row+manifest+report; required_repairs/required_mathematical_repairs/required_metadata_repairs; required_reader_corrections EXACT original array; source/type-only scope, proof/reader/chapter/Goal not accepted. Rehashbefore/after; return raw hashes. No other edits.
''')
files=[p for root in [RUN,CONTRACT] for p in sorted(root.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
files += [Path(p) for p in load(RUN/'draft-baseline-v1.json')['fixed_files']]
files += [Path(folder)/(TASK+'.md') for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']]
files += [PDF]
paths=list(dict.fromkeys(p.resolve().as_posix() for p in files))
rows=[dict(path=p,sha256=sha(p)) for p in paths]
write(RUN/'source-contract-inputs-v1.json',dict(stage='CONTRACT',rows=rows,fixed_input_count=len(rows),
    six_header_fingerprint=sha(CONTRACT/'targets-v1.json'),one_definition_context_fingerprint=sha(CONTRACT/'public-context-v1.lean'),
    source_review_pending=True,body_proof_pending=True,chapter_complete=False,goal_complete=False))
for row in rows:assert sha(row['path'])==row['sha256']
fixed();print('Mandatory source CONTRACT',len(rows),'fixed raw rows, decoder only reconstructed; source/body acceptance pending.')
