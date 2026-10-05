"""Freeze actual retained proof/canary evidence for separate source-body review."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
run=Path(__file__).parent;task='ONLINE-CONVEX-MIGRATION-20261005'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
    with (run/n).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
freeze=load(run/'draft-freeze-v1.json')
labels=['body-'+g+'-v1-01' for g in freeze['groups']]+['canary-'+g+'-v1-01' for g in freeze['groups']]+['public-axioms-v1-01','focused-build-v1-01','verify-public-fences-v1-01']
for label in labels:assert load(run/(label+'-exit.json'))['exit_code']==0,label
for p,h in dict(freeze['modules'],**freeze['canaries']).items():assert sha(p)==h,p
names=load(run/'public-named-declarations-v1.json')['axiom_probe'];raw=(run/'public-axioms-v1-01.log').read_text(encoding='utf-8')
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
assert len(matches)==53 and {n for n,_ in matches}==set(names)
axioms={n:[s.strip() for s in a.split(',') if s.strip()] for n,a in matches}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
for g,targets in freeze['groups'].items():
    gate('retained-body-trial-v1-'+g,sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','lower','--kind','build','--status','compiled',
        '--run-id',run.name,'--lean','BanditRLProof/'+g+'.lean','--statement-hash',freeze['headers'][targets[-1]],
        '--reused-declaration','BanditRL.OnlineConvex.'+targets[-1],'--verifier-evidence',str(run/('body-'+g+'-v1-01.log')),
        '--progress-class','retrieval-reuse','--notes','Fresh actual retained-body elaboration, public canary and named axioms passed; no new proof code; separate body/package review pending.')
write('public-actual-bindings-v1.json',dict(status='freshly-elaborated-retained-proof-candidate',public_modules=freeze['modules'],public_canaries=freeze['canaries'],
    unchanged_headers=freeze['headers'],actual_named_lookup_and_axioms=axioms,actual_axiom_count=53,native_safe_guards=22,actual_passed_gates=labels,
    retained_proofs=22,definitions=5,canary_named_items=26,new_proofs=0,new_registry_nodes=0,body_review='pending',
    integrated_root_Tests_harness='pending',reader_site='pending',PR='pending',chapter_complete=False,goal_complete=False,main_updated=False,live_updated=False))
write('public-body-review-packet-v1.md','Required distinct actual BODY/canary review, requested GPT-6 Astra / medium. Independently raw-rehash public-body-inputs-v1.json. Audit22 retained actual bodies/five definitions and four public canaries against frozen source CONTRACT/decoder; separate verdict from contract acceptance. Challenge real heights/infinity conversion/noBottom/domain points/strict weights/empty regimes, actual affine/sup/composition proof, all nine EReal cases in height witnesses, zero/positive scalar split and full upperAdd terminal. Explicit Rockafellar convention is an interpretation, not literal Orabona. Fresh actual four module bodies/four canaries and53 named lookup/#print axioms succeeded with standard3-or-none; focused Lake and22 native guards passed. Reused actual shared graph27 nodes/13 required value pairs is readiness, no new export/canary graph. Exact public bytes unchanged, no new proof claims. Review nondegenerate canaries including ordinary+ counterexample and whether existing unnamed zero/empty cases actually instantiate claimed endpoints. Distinguish mathematical repairs from required future reader corrections, including finite-domain wording, real-valued composition qualification and stale closure-pending boundary; integration has not happened. Whole Chapter2/Goal/main/live incomplete; root/Tests/full harness/reader/registry/site/contributor/raw supersession/package/PR gates remain pending. Write ONLY public-body-review-v1.md/public-body-receipt-v1.json here, per-target actual proof/canary verdicts, mathematical_repairs, required_reader_corrections, exact reviewed_files/reportSHA and scope limits. No input edits/human/external review/runtime model attestation.')
paths={r['path'] for r in load(run/'contract-source-inputs-v1.json')['rows']}
paths.update(p.as_posix() for p in run.rglob('*') if p.is_file())
paths.discard((run/'public-body-inputs-v1.json').as_posix())
write('public-body-inputs-v1.json',dict(scope='actual retained22 proofs/5definitions/four existing canaries; package pending',rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Fresh actual22 retained bodies/four canary modules/53 named axioms frozen for separate source BODY review; no new proofs.')
