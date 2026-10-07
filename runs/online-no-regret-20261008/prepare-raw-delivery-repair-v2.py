from common_accepted_v1 import *
accepted_fixed()
d=load(RUN/'committed-raw-line-ending-diagnosis-v3.json')
assert d['owned_new_task_evidence_count']==193 and d['inherited_appendonly_count']==4
globals=['MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl']
source=(RUN/'audit-committed-raw-v1.py').read_text(encoding='utf8')
source=source.replace("p!=APPEND_PATH]", "p!=APPEND_PATH and p not in "+repr(globals)+"]")
insert="""inherited_globals=[]
for p in ['MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl']:
    w=Path(p).read_bytes();g=subprocess.check_output(['git','show',head+':'+p])
    snapshot=RUN/'snapshots'/(p.replace('/','--')+'.raw')
    old=snapshot.read_bytes();base_bytes_global=subprocess.check_output(['git','show',BASE+':'+p])
    assert w.startswith(old) and g.startswith(base_bytes_global),p
    inherited_globals.append(dict(path=p,worktree_raw_sha256=sha(p),Git_blob_raw_sha256=hashlib.sha256(g).hexdigest(),
        original_worktree_prefix_raw_sha256=sha(snapshot),original_Git_prefix_raw_sha256=hashlib.sha256(base_bytes_global).hexdigest(),
        original_worktree_prefix_bytes=len(old),original_Git_prefix_bytes=len(base_bytes_global),both_exact_old_prefixes_preserved=True,
        worktree_append_raw_sha256=hashlib.sha256(w[len(old):]).hexdigest(),Git_append_raw_sha256=hashlib.sha256(g[len(base_bytes_global):]).hexdigest(),
        hashes_distinct_and_not_normalized=True,owned_append_guard='source-scope-delivery-v1.json/audit-scope-v3.py'))
"""
source=source.replace("if len(sys.argv)>1 and sys.argv[1]=='direct':",insert+"if len(sys.argv)>1 and sys.argv[1]=='direct':")
source=source.replace("Asymptotic_exact_two_representation_prefixes_plus_same_addition=True,", "Asymptotic_exact_two_representation_prefixes_plus_same_addition=True,inherited_global_exact_prefixes=4,")
source=source.replace("committed-raw-audit-v1.json", "committed-raw-audit-v2.json")
source=source.replace("inherited_Asymptotic_exact_raw_and_Git_representations=representations,", "inherited_Asymptotic_exact_raw_and_Git_representations=representations,inherited_global_appendonly_representations=inherited_globals,")
write(RUN/'audit-committed-raw-v2.py',source)
paths=[RUN/n for n in ['committed-raw-line-ending-diagnosis-v3.json','diagnose-committed-raw-v2.py','diagnose-committed-raw-v3.py',
 'audit-committed-raw-v1.py','audit-committed-raw-v2.py','prepare-raw-delivery-repair-v2.py','diff-raw-evidence-exceptions-v6.json',
 'check-scoped-diff-v6.py','repair-delivery-diff-v6.py','resume-close-delivery-v2.py','scoped-diff-delivery-v5.log',
 'scoped-diff-delivery-v5-exit.json','scoped-diff-delivery-v6.log','scoped-diff-delivery-v6-exit.json',
 'source-scope-delivery-v1.json','created-PR-v1.json','app-attach-v1.json','delivery-obligations-overlay-v1.json',
 'publication-receipt-v2.json','accepted-decision-v1.json','final-reader-receipt-v1.json']]+[PUBLIC,CANARY,Path(APPEND_PATH)]
rows=[dict(path=p.resolve().as_posix(),sha256=sha(p)) for p in paths]
write(RUN/'raw-delivery-review-inputs-v2.json',dict(stage='exact byte-preservation operational repair, no math change',rows=rows,fixed_input_count=len(rows),chapter_complete=False,goal_complete=False))
write(RUN/'raw-delivery-review-packet-v2.md','''# Mandatory scoped evidence/source-binding repair review

Reuse distinct reviewer GPT-6 Astra/medium. PR192 actual OPENdraft/appattached on PR191 exact stack; proofs/readers/frozen CONTRACT/BODY/FINAL/PR prose unchanged. First direct raw audit rightly failed because system core.autocrlf=true silently staged LF versions of193 newly owned task evidence files. Diagnosticv2 wrongly assumed every difference new; v3 identifies193owned files plus4 inherited global append-only files. Proposed repair stages ONLY193 listed new evidence paths using per-command core.autocrlf=false add --renormalize, recording the actual independently reviewed WORKING RAW bytes; no file content/receipt/hash rewrite/global config/attribute change. Then ordinary scoped commit includes new metadata helper/evidence. Source bodies and reader bytes unchanged; no new Lean gate claim.

Audit v2 requires all newly owned RUN/contract/public/canary and applicable roots/readers exact raw Git identity. Original inherited Asymptotic Git1374byteLF and worktree1407byte33CRLF prefixes separately preserved plus SAMEexact677byte reviewed comment. Four inherited global MANIFEST/journals each retain exact BASE Git prefix and exact original worktree snapshot prefix. Their entire work/Git raw hashes and append hashes remain DISTINCT explicitly, never normalized or claimed equal; audit-scope-v3 separately enforces ownTASK and eight exact native reference-index append cells. No inherited global prefix is restaged under disabled conversion.

Closed successful diff stdout two extra exact hash-bound logs had one empty trailing line from print(emptystdout); v6 preserves all11 exact raw evidence exceptions and fixes only future stdout emission, still checks production/reader/contracts/scripts. No blanket exception. All failures retained, previous source/prose acceptance remains intact. Acceptance here approves only exact operational evidence repair, not new mathematical progress/chapter/program/integration/main/live. Final actual v2 raw audit and localremoteREST check still required.

Write ONLY raw-delivery-review-v2.md and raw-delivery-receipt-v2.json with actor.task,verdict,report/report_sha256,fixed_input_count,reviewed_files every row+manifest+report,required_repairs/required_mathematical_repairs/required_metadata_repairs arrays,chapter_complete=false,goal_complete=false. Rehash every raw row before/after. No other edits.
''')
print('Exact operational evidence repair',len(rows),'fixed raw inputs, distinct review pending.')
