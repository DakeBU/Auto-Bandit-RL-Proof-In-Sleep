"""Bind actual retained bodies and distinct reconstruction to the frozen comparison contracts."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
for label in ['actual-types-v1-01','retained-modules-v1-01','retained-scoped-graph-v1-01','normalize-draft-fingerprints-v2-01','search-memory-v1-01','local-lookup-v1-01','mean-local-lookup-v1-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0,label
freeze=load(run/'draft-freeze-v2.json')
for p,h in dict(freeze['module'],**freeze['canary']).items():assert sha(p)==h,p
blind=load(run/'blind-receipt-v1.json')
assert sha(run/'blind-packet-v1.md') in json.dumps(blind) and sha(run/'blind-reconstruction-v1.md') in json.dumps(blind)
gp=Path('tmp/online-guessing-migration-retained-graph-v1.json');g=load(gp)
assert g['extraction']['source']=='compiled-environment' and len(g['nodes'])==10 and len(g['edges'])==1733
assert sum(n['kind']=='theorem' and n['has_value'] for n in g['nodes'])==9
assert sum(n['kind']=='definition' and n['has_value'] for n in g['nodes'])==1
(run/'compiled-retained-graph-v1.json').write_bytes(gp.read_bytes())
write('ready-dependencies-v1.json',dict(status='retained-frontier-actual-compiled',scope_nodes=10,actual_edges=1733,graph_sha256=sha(gp),retained_proofs=9,retained_definitions=1,new_targets_type_checked=3,new_bodies_compiled=False,full_graph_export=False,canary_graph_export=False,edge_boundary='Direct type/value references include definition uses, not all theorem-to-theorem pairs.',first_ready_new_leaf='meanPredict_zero_cumulativeLoss'))
write('source-review-packet-v1.md','''Required distinct anti-anchored CONTRACT review, requested GPT-6 Astra/medium. Independently hash ALL contract-source-inputs-v1.json rows; source re-read exact cached Orabona v10 Example2.14 printed15/PDF27 AND source real-valued guessing game/actual strict-prefix mean predictor/Theorem1.3 printed4/PDF16. Check 12 target contracts in headers-native-v2.json:9 RETAINED public proofs and3 PLANNED exact type expressions, actual types-v1 compiled but no new proof body or named-public theorem exists. Nine native fences and actual retained graph10nodes1733directtype/valueedges include unitInterval definition, not full/canary graph. Existing historical same-actor acceptance is not current distinct review. Blind current packet restricted/supplied notation, history not erased. Fingerprint correction v2 ONLY native whitespace normalization for3plannedheaders before source stabilization, original raw v1 retained/exact mathematical tokens identical, no target weakening or body repair.

Review seven slots PER TARGET. Source x/y are real[0,1], not binary-only. Actual global square regularity is PRODUCED, not an extra consumer premise or stronger source neighborhood assumption. True interval projection/ambient gradient/clamp before same-causal-trajectory tuned2sqrtT. Source prints O(sqrtT), explicit constant2 is derived D1/G2/T>=1; tuning knows horizon/envelopes only, never future loss sequence/comparator. Clamp/gradient/regularity unrestricted-real helper regimes distinct from bound feasibility/positive-step conditions. Existing square eta identity allows n0 totaldivision convention, trajectory/lower require n>0; no zero-horizon tuned guarantee.

Source comparison is NOT implied merely by two UPPER bounds. Retained geometric trajectory/lower n/4 on squarehorizon allzeros initial1 comparator0 supplies real sqrtT/8 witness, admissible fixed initialization NOT every initialization/all algorithms/Chapter4 minimax. Three planned derived comparisons explicitly separate attribution: actual source meanPredict has initial1/2 then true prefix mean0 on this SAME zero stream, exact positive-horizon cumulative loss1/4 (zero comparator loss0 is actually optimal). Actual OGD lower minus exact mean loss yields n/4-1/4 gap; actual Archimedean witness for EVERY C real and N natural will produce n>N with gap>C. No new algorithm/loss/step/sequence, no presupposed lossgap/regret oracle. Is this sufficient valid strengthening of comparative prose with visible initialization/stream/constant boundaries? Request genuine repair separately if not; do not silently reinterpret as all-initializations, same-initialization, log-vs-sqrt asymptotic theorem, all-stream gap or minimax result. Existing source Theorem1.3 global log bound/minimizer/feasibility/prefix declarations are actually inspected dependencies, not whole Chapter1 acceptance. New direct unbounded zero-stream comparison does not rely on an unproved asymptotic log/sqrt substitution.

Allowed window after source stabilization: retain nine headers/proof tokens/unitInterval definition/context unchanged except source/scope qualification comments; THREE new bodies in OnlineGuessingComparison with exactv2 planned headers, one genuine fixed-n same-stream gap canary/new root/Tests import. Original two whole canaries bytefixed5proofs2defs: step1 clampsabove/below versus DIFFERENT tunedT4eta1/4 sourcebound4; lower n4T64eta1/16 actualfirst7/8/regret>=1. Planned newcanary n4 gap>=3/4. Planned21namedaxes12publicproofs+1domain+6canaryproofs+2canarydefs and12nativeguards; complete freshgates pending. Retained9proofs1def not12newproof-count gain; only3new proofs if truly closed. Old native types/focused builds are readiness, not final source acceptance. Current reader has two source boxes and existing comparison; identify corrections independently from mathematical repairs, source vs derived result/initialization/zero horizon/new unbounded gap/remaining source migrations visible.

Single lower ready zero-mean finite sum -> lossgap lower -> arbitrary threshold/witness, no branch explosion. Goal wholeChapters1–16 ACTIVE/unbudgeted; Chapter2totalnull/incomplete, Chapter1migration/future3–16unenumeratedmandatory. Legacy13 before; eventual two retained-module migration delta13→11 ONLY if all gates accepted. Stack OPENdraft163 exact25c77a837c849eb78832673063483db5f663a73a, notmain; no merge/live/retirement. Shared graph/registry/book root retained. No prior receipts/reports edits; exact raw history snapshots will preserve changed public/global surfaces before integration. Task-only frontier/globalSGB protected. Native command gates distinct from prompt/file roles. reference-index global rewrite deliberatelynotrun outside bounded window, scopedcurrentCLI/type/graphretrieval fresh, no runtime/model/independenthuman claim. Write ONLY source-contract-review-v1.md/source-contract-receipt-v1.json here, actor.task=/root/source_reviewer, verdict,12 target_verdicts/sevenslots/classifications, mathematical_repairs and required_reader_corrections separately, all reviewed_files/report SHA. Do not edit inputs or accept new bodies/wholechapter/wholebook.''')
paths={p.as_posix() for p in run.rglob('*') if p.is_file()}
for folder in ['docs/contracts/online-guessing-migration-v1','docs/contracts/online-guessing-ogd-v2','docs/contracts/online-guessing-lower-v2']:
 paths.update(p.as_posix() for p in Path(folder).rglob('*') if p.is_file())
paths.update(['BanditRLProof/OnlineGuessingOGD.lean','BanditRLProof/OnlineGuessingLower.lean','Tests/OnlineGuessingOGDCanary.lean','Tests/OnlineGuessingLowerCanary.lean',
 'BanditRLProof/OnlineGradientDescent.lean','BanditRLProof/OnlineGradientDescentSource.lean','BanditRLProof/OnlineLearningFTL.lean','BanditRLProof/OnlineLearningMean.lean','BanditRLProof/OnlineLearningFoundations.lean',
 '.lake/packages/mathlib/Mathlib/Algebra/Order/Archimedean/Basic.lean','.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean','.lake/packages/mathlib/Mathlib/NumberTheory/Harmonic/Bounds.lean',
 '../research-online-ogd/tmp/pdfs/orabona-v10.pdf','tmp/online-guessing-migration-retained-graph-v1.json',
 'website/content/readings.json','website/content/highlights.json','website/content/chapters.json','BanditRLProof.lean','Tests.lean',
 'lean-toolchain','lakefile.lean','lake-manifest.json','runs/active_frontier.json','.agents/skills/bandit-semantic-roundtrip/SKILL.md',
 'tasks/ONLINE-GUESSING-MIGRATION-20261006.md','conversion-windows/ONLINE-GUESSING-MIGRATION-20261006.md','proof-obligations/ONLINE-GUESSING-MIGRATION-20261006.md',
 'runs/online-guessing-ogd-20260914/acceptance-decision.md','runs/online-guessing-ogd-20260914/04_reviewer.md',
 'runs/online-ogd-migration-20261005/accepted-decision-v1.json','runs/online-jensen-migration-20261005/accepted-decision-v1.json','runs/online-jensen-migration-20261005/delivery-v1.md'])
for p in paths:assert Path(p).is_file(),p
write('contract-source-inputs-v1.json',dict(scope='One source Example2.14 and3planned genuine same-stream comparisons/9retainedproofs1def; not chapter/book',authoritative_headers='docs/contracts/online-guessing-migration-v1/headers-native-v2.json',rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Contract fixed inputs',len(paths),'actualretained10nodes/1733edges; new3body proofs pending.')
