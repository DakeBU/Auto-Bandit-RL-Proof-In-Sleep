from pathlib import Path
import datetime, hashlib, importlib.util, json, subprocess

ROOT=Path(__file__).resolve().parents[2]
TMP=ROOT/'tmp/online-ch2-b4-strong-convex-growth-body-20261011'
RUN=ROOT/'runs/online-ch2-b4-strong-convex-growth-20261011'
DOC=ROOT/'docs/contracts/online-ch2-b4-strong-convex-growth-v1'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text(encoding='utf-8'))
def git(*a):
 p=subprocess.run(['git',*a],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 assert p.returncode==0,(a,p.stdout.decode(errors='replace'),p.stderr.decode(errors='replace'))
 return p.stdout
def create(p,b):
 p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb') as f:f.write(b)
def record(p,o):create(p,(json.dumps(o,ensure_ascii=False,indent=2)+'\n').encode())
pre={'HEAD':git('rev-parse','HEAD').decode().strip(),'status':git('status','--porcelain=v1').decode()}
assert pre['HEAD']=='01c66c0bbfd1e8536939d1ca5c2a67fa092352a1'
assert sha(ROOT/'BanditRLProof/OnlineStrongConvexMinimum.lean')=='55b37c648437e231f1b967cdc9cfa4102ce1bea6efde3ed81b23884604f89317'
rr=ROOT/'tmp/online-ch2-b4-strong-convex-growth-reader-review-20261011'
reader=load(rr/'reader-content-review-v3.json'); assert reader['reader_content_application_eligible'] and not reader['blockers']
canary=load(ROOT/'tmp/online-ch2-b4-strong-convex-growth-canary-review-20261011/canary-compiled-body-review-v1.json')
assert canary['canonical_Tests_installation_eligible'] and not canary['blockers']
native_review=load(rr/'native-content-review-v3.json')
assert not native_review['blockers']
candidate=TMP/'native-contribution-candidate-v3.json'
assert sha(candidate)=='5a84c194ce958e7b5ffa8e89924c40dafca2f438ee9469141ed5d64b0e99bd14'
manifest=load(TMP/'reader-candidates-v3/manifest-v3.json')
changes=[]
for row in manifest['inputs']:
 src=ROOT/row['candidate']; dst=ROOT/row['source']
 assert sha(src)==row['candidate_sha256'] and sha(dst)==row['source_sha256']
 dst.write_bytes(src.read_bytes());changes.append(row['source'])
src=ROOT/'tmp/online-ch2-b4-strong-convex-growth-canary-20261011/Canary.lean'
assert sha(src)==canary['candidate_sha256']
test=ROOT/'Tests/OnlineStrongConvexMinimumCanary.lean';create(test,src.read_bytes());changes.append(test.relative_to(ROOT).as_posix())
testroot=ROOT/'Tests.lean';before=testroot.read_bytes()
assert b'import Tests.OnlineStrongConvexMinimumCanary' not in before
testroot.write_bytes(before+b'\r\nimport Tests.OnlineStrongConvexMinimumCanary\r\n');changes.append('Tests.lean')
native=ROOT/'research-wiki/contribution-contracts/online-ch2-b4-strong-convex-growth-20261011.json'
create(native,candidate.read_bytes());changes.append(native.relative_to(ROOT).as_posix())
spec=importlib.util.spec_from_file_location('native_validator',ROOT/'tools/check_contributor_contract.py')
check=importlib.util.module_from_spec(spec);spec.loader.exec_module(check)
_,errors=check.validate_contract(native);assert not errors,errors
probe=(ROOT/'docs/contracts/online-main-reconciliation-v1/axiom-audit-probe.lean').read_text(encoding='utf-8')
probe=probe.replace('import Tests.OnlineCumulativePotentialCanary\n','import Tests.OnlineCumulativePotentialCanary\nimport Tests.OnlineStrongConvexMinimumCanary\n')
probe+='\n#print axioms BanditRL.OnlineConvex.stronglyConvex_minimum_growth\n#print axioms BanditRL.Tests.OnlineStrongConvexMinimumCanary.square_two_exact_growth\n#print axioms BanditRL.Tests.OnlineStrongConvexMinimumCanary.interval_zero_extended_domain\n'
pp=DOC/'combined-axiom-audit-probe-v1.lean';create(pp,probe.encode());changes.append(pp.relative_to(ROOT).as_posix())
ports=[]
folders=['online-ch2-b4-strong-convex-growth-body-20261011','online-ch2-b4-strong-convex-growth-body-review-20261011',
 'online-ch2-b4-strong-convex-growth-canary-20261011','online-ch2-b4-strong-convex-growth-canary-review-20261011',
 'online-ch2-b4-strong-convex-growth-reader-review-20261011']
for folder in folders:
 for src in sorted((ROOT/'tmp'/folder).rglob('*')):
  if not src.is_file() or '__pycache__' in src.parts:continue
  rel=src.relative_to(ROOT);dst=RUN/'archive'/rel;b=src.read_bytes()
  if dst.exists():assert dst.read_bytes()==b
  else:create(dst,b)
  ports.append({'historical_source':rel.as_posix(),'canonical_copy':dst.relative_to(ROOT).as_posix(),'sha256':sha(src),'bytes':len(b)})
auth={'scope':'Exact reviewed production module/root, two reviewed canonical canaries/shared Tests import, approved reader V3 three appends, native V3 and immutable evidence; no full leaf/chapter acceptance.',
 'author':'/root','pre_git':pre,'reader_review_sha256':sha(rr/'reader-content-review-v3.json'),
 'canary_review_sha256':sha(ROOT/'tmp/online-ch2-b4-strong-convex-growth-canary-review-20261011/canary-compiled-body-review-v1.json'),
 'native_review_sha256':sha(rr/'native-content-review-v3.json'),'production_source_sha256':sha(ROOT/'BanditRLProof/OnlineStrongConvexMinimum.lean'),
 'changed_paths':changes,'ports':ports,'port_boundary':'Exact later copies of historical tmp evidence, not contemporaneous RUN execution. Historical origins remain unchanged; RAW archive attributes preserve every byte.',
 'state':'SOURCE_CANDIDATE_INSTALLED_COMBINED_GATES_PENDING','chapter2_accepted':False,'Goal':'ACTIVE','time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
receipt=RUN/'reviewed-source-application-receipt-v1.json';record(receipt,auth)
owned=['BanditRLProof/OnlineStrongConvexMinimum.lean','BanditRLProof.lean',*changes,
 'docs/contracts/online-ch2-b4-strong-convex-growth-v1/canary-freeze-and-candidate-compile-authorization-v1.json']
owned+= [p.relative_to(ROOT).as_posix() for p in (RUN/'canary-freeze-v1').rglob('*') if p.is_file()]
owned+= [p['canonical_copy'] for p in ports]+[receipt.relative_to(ROOT).as_posix()]
owned=sorted(set(owned))
assert not git('diff','--cached','--name-only'), 'Unexpected staged files'
for name in owned:git('add','-f','--',name)
staged=set(git('diff','--cached','--name-only').decode().splitlines());assert staged==set(owned),(staged^set(owned))
git('diff','--cached','--check')
for row in ports:
 assert hashlib.sha256(git('show',':'+row['canonical_copy'])).hexdigest()==row['sha256']
git('commit','-m','Prove conditional strong-convex minimum growth with real public consumers')
assert not git('status','--porcelain=v1')
result={'HEAD':git('rev-parse','HEAD').decode().strip(),'parent':pre['HEAD'],'source_candidate_only':True,
 'combined_gates_pending':True,'owned_files':len(owned),'ports':len(ports),'receipt_sha256':sha(receipt),'dirty':False}
record(TMP/'reviewed-source-commit-receipt-v1.json',result);print(json.dumps(result,indent=2))
