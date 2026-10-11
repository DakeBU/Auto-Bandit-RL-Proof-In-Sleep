from pathlib import Path
import hashlib,importlib.util,json,subprocess
ROOT=Path(__file__).resolve().parents[2];TMP=Path(__file__).resolve().parent
RUN=ROOT/'runs/online-ch2-b4-strong-convex-growth-20261011';DEST=RUN/'native-diff-aware-repair-v1'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*a):
 p=subprocess.run(['git',*a],cwd=ROOT,capture_output=True);assert p.returncode==0,p.stderr.decode('utf-8','replace');return p.stdout
assert git('rev-parse','HEAD').decode().strip()=='cf1a424f2312e7c5b730717cf0a96d65837894bd'
assert not git('status','--porcelain=v1') and not git('diff','--cached','--name-only')
review=ROOT/'tmp/online-ch2-b4-strong-convex-growth-reader-review-20261011/native-content-review-v4.json'
assert h(review)=='8fac5590ca1d17b74a0428ced7a84f880cb3c641e79e3d39a6b2ca4f4ada0624'
assert not json.loads(review.read_text(encoding='utf-8'))['blockers']
candidate=TMP/'native-contribution-candidate-v4.json';assert h(candidate)=='a07f4b350c3162253d06d9b09b930072a8187d42a5cd5a34c0805db732960e4d'
target=ROOT/'research-wiki/contribution-contracts/online-ch2-b4-strong-convex-growth-20261011.json'
assert h(target)=='5a84c194ce958e7b5ffa8e89924c40dafca2f438ee9469141ed5d64b0e99bd14'
bindings=['BanditRLProof/OnlineStrongConvexMinimum.lean','BanditRLProof.lean','Tests/OnlineStrongConvexMinimumCanary.lean','Tests.lean',
 'website/content/chapters.json','website/content/highlights.json','website/content/readings.json','tools/check_contributor_contract.py']
pre={p:h(ROOT/p) for p in bindings};target.write_bytes(candidate.read_bytes())
spec=importlib.util.spec_from_file_location('native_validator',ROOT/'tools/check_contributor_contract.py');checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
_,errors=checker.validate_contract(target);assert not errors,errors
sources=[candidate,review,TMP/'native-diff-aware-failure-v1.json',Path(__file__).resolve()]
gd=ROOT/'tmp/online-ch2-b4-strong-convex-growth-gates-20261011/contributor-actual-main-base-v1'
sources += [gd/x for x in ('receipt.json','stdout.raw','stderr.raw')]
ports=[]
for p in sources:
 dst=DEST/'archive'/p.relative_to(ROOT);dst.parent.mkdir(parents=True,exist_ok=True)
 with dst.open('xb') as f:f.write(p.read_bytes())
 ports.append({'source':p.relative_to(ROOT).as_posix(),'copy':dst.relative_to(ROOT).as_posix(),'sha256':h(p),'bytes':p.stat().st_size})
post={p:h(ROOT/p) for p in bindings};assert pre==post
receipt=DEST/'application-receipt-v1.json';receipt.parent.mkdir(parents=True,exist_ok=True)
receipt.write_text(json.dumps({'parent_HEAD':'cf1a424f2312e7c5b730717cf0a96d65837894bd','review_sha256':h(review),
 'exact_change':'Remove two nonprotected Test paths from native affected_files only; actual Test files/import and consumer/verification fields unchanged. No checker change.',
 'before_native_sha256':'5a84c194ce958e7b5ffa8e89924c40dafca2f438ee9469141ed5d64b0e99bd14','after_native_sha256':h(target),
 'unchanged_active_source_bindings':pre,'ports':ports,'port_boundary':'Later exact archive copies; original v1 failed actual gate and all successes remain historical at cf1.',
 'actual_pure_native_validator_errors':errors,'fresh_gates_pending':True,'Goal':'ACTIVE'},indent=2)+'\n',encoding='utf-8')
owned=[target.relative_to(ROOT).as_posix(),receipt.relative_to(ROOT).as_posix()]+[r['copy'] for r in ports]
for p in owned:git('add','-f','--',p)
assert set(git('diff','--cached','--name-only').decode().splitlines())==set(owned)
git('diff','--cached','--check')
for row in ports:assert hashlib.sha256(git('show',':'+row['copy'])).hexdigest()==row['sha256']
git('commit','-m','Repair native affected-file metadata without changing proofs or Tests')
assert not git('status','--porcelain=v1')
out={'HEAD':git('rev-parse','HEAD').decode().strip(),'parent':'cf1a424f2312e7c5b730717cf0a96d65837894bd','changed_active_path':target.relative_to(ROOT).as_posix(),'mathematics_and_Tests_unchanged':True,'fresh_gates_pending':True,'Goal':'ACTIVE'}
(TMP/'native-metadata-repair-commit-receipt-v1.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out,indent=2))
