import hashlib, json, subprocess
from pathlib import Path
from datetime import datetime, timezone

ROOT=Path.cwd()
DOC=Path('docs/contracts/online-ch2-b4-finite-identity-v1')
RUN=Path('runs/online-ch2-b4-finite-identity-20261011')
def sha(b): return hashlib.sha256(b).hexdigest()
def now(): return datetime.now(timezone.utc).isoformat()
def git(*args): return subprocess.check_output(['git',*args]).decode().strip()
def put(p,b):
 p=Path(p);p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb') as f:f.write(b)
def js(p,o):put(p,(json.dumps(o,ensure_ascii=False,indent=2)+'\n').encode())
def row(p):
 p=Path(p);b=p.read_bytes();return {'path':p.as_posix(),'sha256':sha(b),'bytes':len(b)}
def check(p,h):assert sha(Path(p).read_bytes())==h,str(p)
assert git('rev-parse','HEAD')=='40c2f30f7cee38c9d2f716ffdac18a459a5af25a'
assert git('status','--porcelain')=='?? BanditRLProof/OnlineCumulativePotential.lean'
assert not Path('Tests/OnlineCumulativePotentialCanary.lean').exists()
check('BanditRLProof/OnlineCumulativePotential.lean','61c811c0b1f941ec22ac41f64e555a0e4d4d8dc32b8145ea53808dbdc0fc17da')
old=json.loads((DOC/'leaf-freeze-receipt-v1.json').read_bytes())
for r in old['frozen_inputs']:check(r['path'],r['sha256'])
for folder,manifest,exclude in [
 ('core-20261011','artifact-manifest-v2.json','excluded_self_and_verifier'),
 ('canary-header-elaboration-20261011','artifact-manifest-v1.json','excluded')]:
 base=Path('tmp/online-ch2-b4-finite-identity-'+folder)
 j=json.loads((base/manifest).read_bytes())
 for r in j['rows']:
  check(base/r['path'],r['sha256']);assert (base/r['path']).stat().st_size==r['bytes']
 actual={p.relative_to(base).as_posix() for p in base.rglob('*') if p.is_file()}
 assert actual=={r['path'] for r in j['rows']}|set(j[exclude])
ports=[]
groups=[('actual-preproof','preproof-20261011/capture-v3'),
 ('independent-preproof','preproof-review-20261011'),('production-authorization','body-authorization-20261011'),
 ('actual-freeze-commit-v2','freeze-commit-v2-20261011'),('production-core','core-20261011'),
 ('independent-production-body','body-review-20261011'),('canary-proposal','canary-proposal-20261011'),
 ('canary-neutral-blind','canary-blind-20261011'),('canary-source-header','canary-source-review-20261011'),
 ('canary-header-elaboration','canary-header-elaboration-20261011')]
for label,suffix in groups:
 src=Path('tmp/online-ch2-b4-finite-identity-'+suffix)
 for p in sorted(src.rglob('*')):
  if not p.is_file():continue
  q=RUN/label/p.relative_to(src);b=p.read_bytes();put(q,b)
  ports.append({'original':p.as_posix(),'destination':q.as_posix(),'sha256':sha(b),'bytes':len(b)})
 put(RUN/label/'.gitattributes',b'* -text\n*.raw -diff\n*.olean -diff\n')
js(RUN/'exact-proof-and-canary-input-port-manifest-v1.json',{'UTC':now(),'rows':ports,
 'all_exact_bytes':all(Path(r['original']).read_bytes()==Path(r['destination']).read_bytes() for r in ports),
 'chronology':'Exact copies of earlier tmp execution and reviews; all original paths/receipts unchanged. No canonical RUN execution claim.',
 'old_statement_frozen_inputs_unchanged':True,'compiled_artifact':'production-core/compiled/BanditRLProof/OnlineCumulativePotential.olean; own exact artifact must be explicitly staged despite global ignore.'})
for tag in ['one-round','two-round']:
 p=RUN/'canary-proposal'/('neutral-'+tag+'-complete-header-v1.txt')
 put(DOC/('canary-neutral-'+tag+'-frozen-header-v1.txt'),p.read_bytes())
checks=[('independent-production-body/fresh-production-body-review-v1.json','4b3246ef699eba8c3df7a8063e12342f86211c43b60efd121ce2bccb58c8aac6'),
 ('canary-neutral-blind/fresh-canary-blind-v1.json',None),
 ('canary-source-header/canary-source-header-review-v1.json',None),
 ('canary-header-elaboration/canary-header-elaboration-report-v1.json','e9602bd4e769c44a00e458372d8f0e4fc833bddccfc846532710b461a06e32a7')]
# Resolve authoritative review names by their previously verified unique SHA, avoiding guessed filenames.
reviews=[]
for folder,h in [('canary-neutral-blind','f29ac0fd3ed86e73cb5cc0ff52600750c86505f03fb7547f3d028790bc431428'),
 ('canary-source-header','b581b3fff2379b4805fd7e472b12bd7d4cca4e2dc13d519b3d2e4f7f3b364939'),
 ('independent-production-body','4b3246ef699eba8c3df7a8063e12342f86211c43b60efd121ce2bccb58c8aac6')]:
 matches=[p for p in (RUN/folder).glob('*.json') if sha(p.read_bytes())==h]
 assert len(matches)==1;reviews.append(row(matches[0]))
check(DOC/'canary-neutral-one-round-frozen-header-v1.txt','7d10ab86d93f97a5ac03db64ce96b8759a0a64d7bd440fa5bfbbe666717be75e')
check(DOC/'canary-neutral-two-round-frozen-header-v1.txt','718a2eb714597c34033cc4d35af06b00b3718768cd60799800c6e487c777af64')
proposal={'UTC':now(),'status':'CANARY FREEZE PROPOSAL; independent review pending; NO Test BODY AUTHORIZATION',
 'requested_model_effort':'GPT-6 Astra / medium; runtime not independently attested',
 'production_core':row('BanditRLProof/OnlineCumulativePotential.lean'),
 'production_header':row(DOC/'neutral-frozen-header-v1.txt'),'production_statement_seal':row(DOC/'leaf-freeze-receipt-v1.json'),
 'production_report':row(RUN/'production-core/core-report-v2.json'),
 'reviews':reviews,'header_elaboration':row(RUN/'canary-header-elaboration/canary-header-elaboration-report-v1.json'),
 'headers':[row(DOC/('canary-neutral-'+tag+'-frozen-header-v1.txt')) for tag in ['one-round','two-round']],
 'test_module':'Tests/OnlineCumulativePotentialCanary.lean','public_theorems':2,'public_definitions':0,
 'semantic_delta':'Concrete finite-real algebra witnesses only. No optimizer/actual algorithm/EReal/analytic performance theorem asserted.',
 'consumer_requirement':'FIRST conjunct of EACH theorem must specialize BanditRL.OnlineCumulativePotential.finite_regret_identity directly; numeric remaining conjuncts may use norm_num. Actual compiled VALUE occurrence of the production theorem must be verified.',
 'source_witnesses':['T=1 positive retained terminal gap 1/36, truncated bound false.','T=2 signed regularizer drift -1/2 and terminal y2=2 differs from unscored x2=100.'],
 'shared_context':'Each complete header retains its exact three imports, noncomputable section/open Finset/namespace and all local lets. Shared combined Test file may deduplicate common context only with exact per-theorem reconstruction.',
 'chapter_state':{'chapter2':'partial','accepted':False,'required_open_containers':7,'future_claims_open':6,'whole_B4':'OPEN','Goal':'ACTIVE','main_live_updated':False},
 'authorization':'Independent contract audit, exact canary seal, clean committed context, independent pre-canary review, then explicit parent authorization are required before Test BODY.',
 'ports':row(RUN/'exact-proof-and-canary-input-port-manifest-v1.json')}
js(DOC/'canary-freeze-proposal-v1.json',proposal)
put(RUN/'prepared/prepare-b4-canary-freeze-v1.py',Path(__file__).read_bytes())
print(json.dumps({'ports':len(ports),'bytes':sum(r['bytes'] for r in ports),'proposal':row(DOC/'canary-freeze-proposal-v1.json'),'old_seal_inputs_unchanged':len(old['frozen_inputs'])}))
