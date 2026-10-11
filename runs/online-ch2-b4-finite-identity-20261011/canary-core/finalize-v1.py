from pathlib import Path
import json,hashlib,datetime,subprocess,re
root=Path('E:/ABRL/worktrees/research-online-book');out=root/'tmp/online-ch2-b4-finite-identity-canary-core-20261011'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,obj):
 with (out/n).open('xb') as f:f.write((json.dumps(obj,indent=2)+'\n').encode('utf-8'))
core=root/'BanditRLProof/OnlineCumulativePotential.lean';target=root/'Tests/OnlineCumulativePotentialCanary.lean'
assert sha(core)=='61c811c0b1f941ec22ac41f64e555a0e4d4d8dc32b8145ea53808dbdc0fc17da'
rawrows=json.loads((root/'tmp/online-ch2-b4-finite-identity-precanary-v2-20261011/context-v2/pre-source-inputs.json').read_text())
seal=json.loads((root/'docs/contracts/online-ch2-b4-finite-identity-v1/canary-freeze-receipt-v1.json').read_text())
add=json.loads((root/'docs/contracts/online-ch2-b4-finite-identity-v1/precanary-preparation-addendum-v1.json').read_text())
for r in rawrows+seal['frozen_inputs']+add['added_inputs']:assert sha(root/r['path'])==r.get('sha256',r.get('raw_sha256')),r['path']
HEAD=subprocess.check_output(['git','rev-parse','HEAD'],cwd=str(root)).decode().strip();assert HEAD=='cb4fe8ec8b979a698c31d3ebf5a350ac7242a66a'
status=subprocess.check_output(['git','status','--short'],cwd=str(root)).decode().strip();assert status=='?? Tests/OnlineCumulativePotentialCanary.lean'
constants=json.loads((out/'compiled-constant-occurrences-v1.json').read_text())
for row in constants:
 assert 'BanditRL.OnlineCumulativePotential.finite_regret_identity' in row['VALUE']
 assert 'BanditRL.OnlineCumulativePotential.finite_regret_identity' not in row['TYPE']
text=(out/'public-compiled-canary-probe-v1.stdout.raw').read_text(encoding='utf-8');axioms=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",text)
assert len(axioms)==2
for n,a in axioms:assert [x.strip() for x in a.split(',')]==['propext','Classical.choice','Quot.sound']
assert target.read_text(encoding='utf-8').count('exact BanditRL.OnlineCumulativePotential.finite_regret_identity')==2
assert not any(line.endswith(b' ') for line in target.read_bytes().splitlines());assert b'\r' not in target.read_bytes()
dump('context-after-v1.json',dict(UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),HEAD=HEAD,git_status=status,original_RAW_rows_unchanged=len(rawrows),original_canary_frozen_rows_unchanged=len(seal['frozen_inputs']),addendum_rows_unchanged=len(add['added_inputs']),core_sha256=sha(core),test_sha256=sha(target),full_RAW_rows=rawrows,toolchain_pins={p:sha(root/p) for p in ['lean-toolchain','lakefile.lean','lake-manifest.json']},core_olean_sha256=sha(root/'tmp/online-ch2-b4-finite-identity-core-20261011/compiled/BanditRLProof/OnlineCumulativePotential.olean'),Test_olean_sha256=sha(out/'compiled/Tests/OnlineCumulativePotentialCanary.olean')))
report=dict(status='TWO CANARIES PROVED_LOCAL; distinct BODY review pending',UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),canonical_source='E:/ABRL/research',worktree=str(root),branch=subprocess.check_output(['git','branch','--show-current'],cwd=str(root)).decode().strip(),HEAD=HEAD,git_status=status,Test_path='Tests/OnlineCumulativePotentialCanary.lean',Test_sha256=sha(target),core_unchanged_sha256=sha(core),public_declarations=[r['declaration'] for r in constants],new_public_helpers_or_definitions=0,whole_complete_headers_reconstructed_exact=True,native_fences='native-fences-v1.json: both ok; closed concrete propositions have zero input premises, all statement-local lets retained',source_BODY='candidate-v2.lean is complete successful source; each constructor first branch directly exact-applies production core and remaining branch norm_num',compiled_constant_inventory=[dict(declaration=r['declaration'],TYPE_count=len(r['TYPE']),VALUE_count=len(r['VALUE']),core_in_VALUE=True,core_in_TYPE=False) for r in constants],constant_scope='Actual direct Expr.getUsedConstantsAsSet occurrences; not necessity or transitive graph. Visible first constructor branch proves that core is used for first equality, not an unused consumer.',actual_axioms={n:[x.strip() for x in a.split(',')] for n,a in axioms},focused_exit=0,olean_exit=0,public_import_check_print_axioms_exit=0,public_print_boundary='Ordinary #print retains Lean default proof elisions; full readable source BODY and complete structural TYPE/VALUE constant sets retained. No huge full pretty-printer log generated.',failed_candidates=[dict(candidate='candidate-v1.lean',receipt='focused-v1.json',classification='IMPLEMENTATION_FAILED',reason='Proof application lambda annotation assigned time binder Real instead of Nat; changed only proof binder annotations to explicit Nat/Real. Frozen declarations unchanged.')],original_context_rows_unchanged=len(rawrows),canary_seal_rows_unchanged=len(seal['frozen_inputs']),addendum_rows_unchanged=len(add['added_inputs']),scope='Only new Test source and ignored evidence. No shared cache/core/root/DOC/RUN/site edits; no fullgate/commit/push.',remaining=['distinct canary BODY review','authorized root/harness/site integration and full gates','full B4/EReal adapter/attainment/producer/sharp Young endpoints','seven containers and six future claims; Chapter2 partial; Goal ACTIVE'],worktree_disposition='Retained active; Test untracked, no commit/push',requested_model_effort='GPT-6 Astra / medium; runtime not independently attested')
dump('canary-core-report-v1.json',report)
excluded={'artifact-manifest-v1.json','artifact-manifest-verification-v1.json'}
rows=[dict(path=p.relative_to(out).as_posix(),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(out.rglob('*')) if p.is_file() and p.name not in excluded]
dump('artifact-manifest-v1.json',dict(excluded=sorted(excluded),rows=rows))
for r in rows:assert sha(out/r['path'])==r['sha256'] and (out/r['path']).stat().st_size==r['bytes']
assert {p.relative_to(out).as_posix() for p in out.rglob('*') if p.is_file() and p.name not in excluded}=={r['path'] for r in rows}
dump('artifact-manifest-verification-v1.json',dict(manifest_sha256=sha(out/'artifact-manifest-v1.json'),rows=len(rows),all_rows_verified=True,exact_file_set_matches=True,excluded=sorted(excluded)))
print('Test',sha(target))
for n in ['canary-core-report-v1.json','artifact-manifest-v1.json']:print(n,sha(out/n))
print('manifest rows',len(rows))