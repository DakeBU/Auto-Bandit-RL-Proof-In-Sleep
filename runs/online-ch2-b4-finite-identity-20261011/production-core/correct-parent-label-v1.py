from pathlib import Path
import hashlib,json,datetime
root=Path('E:/ABRL/worktrees/research-online-book');out=root/'tmp/online-ch2-b4-finite-identity-core-20261011'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(n,obj):
 with (out/n).open('xb') as f:f.write((json.dumps(obj,indent=2)+'\n').encode('utf-8'))
core=root/'BanditRLProof/OnlineCumulativePotential.lean'
assert sha(core)=='61c811c0b1f941ec22ac41f64e555a0e4d4d8dc32b8145ea53808dbdc0fc17da'
export=out/'compiled-constant-occurrences-v3.json';deps=json.loads(export.read_text())
assert 'Nat.recAux' in deps['VALUE'] and 'Nat.rec' not in deps['VALUE']
old=out/'core-report-v1.json';report=json.loads(old.read_text())
assert report['full_proof_print_bytes']==20815000
assert (out/'public-compiled-probe-full-v2.stdout.raw').stat().st_size==20815000
report['actual_named_mathematical_parents']=['Nat.recAux' if x=='Nat.rec' else x for x in report['actual_named_mathematical_parents']]
report['evidence_label_correction']='Nat.rec in v1 was an induction-concept label incorrectly listed among actual parents. Exact direct VALUE constant is Nat.recAux; no mathematical statement/proof change.'
report['supersedes_report_sha256']=sha(old)
report['UTC']=datetime.datetime.now(datetime.timezone.utc).isoformat()
put('core-report-v2.json',report)
rows=json.loads((root/'tmp/online-ch2-b4-finite-identity-preproof-20261011/capture-v3/source-RAW-before.json').read_text())
for r in rows: assert sha(root/r['path'])==r['sha256'],r['path']
put('parent-label-correction-v1.json',dict(UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),old_report_sha256=sha(old),new_report_sha256=sha(out/'core-report-v2.json'),old_label='Nat.rec',correct_direct_VALUE_constant='Nat.recAux',export_path=export.name,export_sha256=sha(export),Nat_rec_present_in_direct_VALUE=False,Nat_recAux_present_in_direct_VALUE=True,full_successful_probe_stdout_bytes=20815000,byte_count_note='v1/v2 report numeric field was already correct; earlier collaboration message incorrect byte count was corrected separately.',production_sha256=sha(core),production_unchanged=True,preproof_rows_verified_unchanged=len(rows),Lean_rerun=False,old_artifacts_retained=True))
exclude={'artifact-manifest-v2.json','artifact-manifest-verification-v2.json'}
items=[dict(path=p.relative_to(out).as_posix(),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(out.rglob('*')) if p.is_file() and p.relative_to(out).as_posix() not in exclude]
put('artifact-manifest-v2.json',dict(excluded_self_and_verifier=sorted(exclude),rows=items))
for r in items:
 p=out/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
actual={p.relative_to(out).as_posix() for p in out.rglob('*') if p.is_file() and p.relative_to(out).as_posix() not in exclude}
assert actual=={r['path'] for r in items}
put('artifact-manifest-verification-v2.json',dict(UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(out/'artifact-manifest-v2.json'),all_rows_verified=True,rows=len(items),exact_file_set_matches=True,excluded=sorted(exclude),core_sha256=sha(core)))
for n in ['core-report-v2.json','artifact-manifest-v2.json','parent-label-correction-v1.json']:print(n,sha(out/n))
print('rows',len(items))