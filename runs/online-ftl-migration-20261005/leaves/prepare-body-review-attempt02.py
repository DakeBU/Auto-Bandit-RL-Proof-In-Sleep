"""Bind fresh retained-body/canary elaborations for a separate semantic review."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
run=Path(__file__).parent
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
    with (run/n).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
gates=['retained-body-elaboration-v1-01','public-canary-elaboration-v1-01','public-axioms-v1-01',
    'focused-build-v1-01','verify-public-fences-v1-01']
for g in gates:assert load(run/(g+'-exit.json'))['exit_code']==0,g
frozen=load(run/'draft-freeze-v1.json')
assert sha('BanditRLProof/OnlineFTLFailure.lean')==frozen['original_public_module_sha256']
assert sha('Tests/OnlineFTLFailureCanary.lean')==frozen['original_public_canary_sha256']
names=load(run/'public-named-declarations-v1.json')['axiom_probe']
raw=(run/'public-axioms-v1-01.log').read_text(encoding='utf-8')
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
assert len(matches)==12 and {n for n,_ in matches}==set(names)
axioms={n:[s.strip() for s in a.split(',') if s.strip()] for n,a in matches}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
gate('retained-body-trial-v1-02',sys.executable,'-X','utf8','tools/bandit.py','trial-log',
    '--task','ONLINE-FTL-MIGRATION-20261005','--role','lower','--kind','build','--status','passed',
    '--run-id',run.name,'--lean','BanditRLProof/OnlineFTLFailure.lean',
    '--statement-hash',frozen['headers']['example_2_10'],'--reused-declaration','BanditRL.OnlineLearning.example_2_10',
    '--verifier-evidence',str(run/'retained-body-elaboration-v1-01.log'),
    '--progress-class','retrieval-reuse','--notes','Fresh actual public body elaboration, two nondegenerate canaries and12 named axioms passed; retained7 proofs, zero new bodies; body/package review pending.')
write('public-actual-bindings-v1.json',dict(status='freshly-elaborated-retained-proof-candidate',
    public_module_sha256=sha('BanditRLProof/OnlineFTLFailure.lean'),public_canary_sha256=sha('Tests/OnlineFTLFailureCanary.lean'),
    unchanged_headers=frozen['headers'],actual_named_lookup_and_axioms=axioms,actual_axiom_count=12,
    native_safe_guards=7,actual_passed_gates=gates,retained_proofs=7,definitions=3,canary_proofs=2,new_proofs=0,
    graph='reused prior actual compiled shared graph; readiness retrieval, not fresh export',
    body_review='pending',integrated_root_Tests_harness='pending',reader_site='pending',PR='pending',
    chapter_complete=False,goal_complete=False,main_updated=False,live_updated=False))
write('public-body-review-packet-v1.md',
    'Required distinct actual-body/canary review, GPT-6 Astra / medium. Independently verify raw public-body-inputs-v1.json rows. '
    'Seven retained proof bodies/three definitions: recursive prefix identity, strict-past equality for fixed x0, feasible output, actual historical linear minimization, '
    'actual failure prefix/parity, actual prediction, and played-loss sum exact equality AND uniform lower bound. '
    'Challenge missing dependencies, desired-bound consumers, quantifiers/index and first loss. Only comparator0 and T>=1 source terminal; not all algorithms lower bound. '
    'Generic minimization inequality allows infeasible x0 at time0 because empty objectives vanish; source terminal/feasibility restores x0 interval membership. '
    'Positive-time zero-prefix tie is concrete -1, allowed selection; failure prefixes neverzero. '
    'Actual current public bodies and two nonzero-initial canaries were freshly elaborated, focused Lake build passed, twelve #check/#print axioms exact names standard3 or none, seven actual safe guards passed. '
    'Shared compiled graph reused from OGD package gives10 actual FTL nodes/six required proof-value pairs, not a new export or canary graph. '
    'Original module/canary raw bytes unchanged and snapshots exact; zero new proof claims. Body review is separate from earlier accepted-with-delta contract review. '
    'Shared reader highlights currently have imprecise equations: prefix highlight currently repeats minimization rather than equality of predictions; minimization highlight argmin requires feasibility separately at time0. '
    'These must be corrected/qualified in forthcoming comment and reader integration, which has NOT happened or been accepted yet. '
    'Fresh root/Tests/full harness, final reader/shared registry/site/contributor/raw supersession/package/PR gates remain pending; chapter and whole Goal remain incomplete. '
    'Write ONLY public-body-review-v1.md/public-body-receipt-v1.json here, with per-target bodies/canary verdicts, required repairs, exact raw reviewed_files/reportSHA, explicit source and evidence limits. '
    'First body-review preparation failed solely because native trial role lower-worker is invalid (allowed lower); original script/log retained. Corrected native role lower is administrative repair, not mathematical weakening. '
    'No input edit or human/external review claim.')
paths={r['path'] for r in load(run/'contract-source-inputs-v1.json')['rows']}
paths.update(p.as_posix() for p in run.rglob('*') if p.is_file())
paths.update(['tmp/online-ogd-migration-full-graph.json','website/content/readings.json','website/content/chapters.json','website/content/highlights.json'])
paths.discard((run/'public-body-inputs-v1.json').as_posix())
write('public-body-inputs-v1.json',dict(scope='actual retained7 bodies/3definitions/two canaries; package gates pending',
    rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Fresh retained7 bodies/2 public canaries/12 named axioms frozen for distinct body review; zero new proofs.')
