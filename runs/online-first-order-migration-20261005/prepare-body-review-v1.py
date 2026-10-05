"""Freeze fresh public elaboration and unchanged body/canary evidence for distinct review."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-FIRST-ORDER-MIGRATION-20261005'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
    p=run/n;assert not p.exists(),p
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
labels=['focused-v1-01','public-body-v1-01','public-canary-v1-01','public-axioms-v1-01','verify-public-fences-v1-01']
for label in labels:assert load(run/(label+'-exit.json'))['exit_code']==0,label
freeze=load(run/'draft-freeze-v1.json');module=Path('BanditRLProof/OnlineConvexFirstOrder.lean')
token=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert token(module.read_text(encoding='utf-8'))==token((run/'original-OnlineConvexFirstOrder.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(module,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
old=load(run/'source-contract-receipt-v1.json');assert sha(old['report'])==old['report_sha256']
snap={(r['path'],r['raw_sha256']):r['snapshot'] for r in load(run/'historical-raw-supersession-v1.json')['rows']}
original_rows=[]
for row in old['reviewed_files']:
    p,h=row['path'],row['sha256'];resolved=p if sha(p)==h else snap[(p,h)]
    assert sha(resolved)==h;original_rows.append(dict(path=p,sha256=h,resolved=resolved))
write('prior-contract-binding-v1.json',dict(status='passed',rows=original_rows,explicit_module_comment_supersession=True,original_receipt_immutable=True))
raw=(run/'public-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
names=load(run/'public-named-declarations-v1.json')['axiom_probe'];assert len(matches)==12 and {n for n,a in matches}==set(names)
axioms={n:([a for a in re.sub(r'\s+','',s).split(',') if a]) for n,s in matches}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
write('public-actual-bindings-v1.json',dict(status='freshly-elaborated-retained-body-candidate',public_module={module.as_posix():sha(module)},
    canary=freeze['canary'],headers=freeze['headers'],axioms=axioms,named_axiom_count=12,native_guards=3,actual_passed_gates=labels,
    retained_proofs=3,new_proofs=0,new_registry_nodes=0,canary_definitions=1,canary_proofs=8,anonymous_canary_instance=1,
    body_review='pending',root_Tests_harness='pending',reader_site_PR='pending',chapter_complete=False,goal_complete=False))
gate('retained-body-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','lower','--kind','build','--status','compiled',
    '--run-id',run.name,'--attempt-id','FIRST-ORDER-RETAINED-BODIES-V1','--lean',module.as_posix(),
    '--statement-hash',freeze['headers']['theorem_2_7'],'--reused-declaration','BanditRL.OnlineConvex.theorem_2_7',
    '--verifier-evidence',str(run/'public-body-v1-01.log'),'--progress-class','retrieval-reuse',
    '--notes','Fresh actual retained three-body module, byte-unchanged meaningful public canary,12 named axioms and3 native guards; no new proof code. Distinct body review/full package pending.')
write('public-body-review-packet-v1.md','''Distinct BODY review requested GPT-6 Astra / medium. Independently raw-rehash every public-body-inputs-v1.json row. Verify prior source CONTRACT receipt through explicit historical snapshot for leading-comment module delta, not current bytes mislabeled old. Audit3 retained actual bodies, all actual canary proofs/definition/anonymous top comparator instance, unchanged frozen headers/code tokens/canary bytes,12 named checks/axioms,3 native guards and actual focused/direct public module/canary elaboration. Challenge gradient canonical real conversion versus source extended function, global noBottom, ambient interior versus relative interior, all-y/top case, real helper V/ambient derivative and no open V assumption. Actual scoped compiled shared-root3node416edge graph/value pairs is direct proof boundary, not full export/canary graph. Local neighborhood bridge and real helper are library helpers, only theorem_2_7 printed terminal. Body must use actual derivative/convex slope, not desired supporting premise; meaningful positive-halfline loss has distinct finite1/2, nonzero derivative1, outside-1top, open unbounded domain. Original source-contract reader corrections are still pending, not body repairs unless mathematical mismatch found. Body review separate from contract acceptance; combined root/Tests/full harness/readers/site/registry/contributor/raw/package/PR remain pending. Whole Goal active/Chapter2totalnull. Write ONLY public-body-review-v1.md/public-body-receipt-v1.json with actor.task=/root/source_reviewer, verdict, mathematical_repairs, per-target/seven-slot body/canary audit, required_reader_corrections, reviewed_files exactSHA, report path/SHA, remaining gates. No source/input edits/human/external/runtime model attestation.''')
paths={row['path'] for row in load(run/'contract-source-inputs-v1.json')['rows']}
paths.update(p.as_posix() for p in run.rglob('*') if p.is_file())
paths.update(['BanditRLProof/OnlineGradientDescent.lean','BanditRLProof/OnlineGradientDescentSource.lean'])
write('public-body-inputs-v1.json',dict(scope='three retained actual bodies/unchanged nondegenerate public canary/12 actual named axiom results',rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Fresh unchanged3body/canary proof evidence and12 named axioms frozen for distinct BODY review.')
