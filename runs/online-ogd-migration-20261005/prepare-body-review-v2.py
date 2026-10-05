"""Bind the actual public producer chain and tests for a distinct body review."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header, _strip_lean_comments
run=Path(__file__).parent
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,obj):
    with Path(p).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(obj,str):f.write(obj+'\n')
        else:json.dump(obj,f,indent=2);f.write('\n')
snap={r['path']:r for r in load(run/'historical-raw-supersession-v2.json')['rows']}
historical=[]
for version in [1,2]:
    receipt=load(run/('source-contract-receipt-v'+str(version)+'.json'))
    assert sha(receipt['report'])==receipt['report_sha256']
    for row in receipt['reviewed_files']:
        actual=sha(row['path'])
        if actual!=row['sha256']:
            assert row['path'] in snap,row['path']
            s=snap[row['path']]
            assert s['raw_sha256']==row['sha256']==sha(s['snapshot']),row['path']
            historical.append(dict(receipt_version=version,path=row['path'],
                original_sha256=row['sha256'],preserved_original=s['snapshot'],
                current_sha256=actual,explicit_delta='public imports or old source comment only'))
gates=['root-v2-01','Tests-v2-01','public-canary-v2-01','public-axioms-v2-01',
       'prepare-public-gates-v2-01','body-adapters-v2-01','body-one-step-v2-01','body-cumulative-v2-01']
for label in gates:assert load(run/(label+'-exit.json'))['exit_code']==0,label
inventory=load(run/'public-named-declarations-v2.json')
raw=(run/'public-axioms-v2-01.log').read_text(encoding='utf-8')
rows=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
assert len(rows)==75 and {n for n,_ in rows}==set(inventory['axiom_probe'])
allowed={'propext','Classical.choice','Quot.sound'}
axioms={n:[a.strip() for a in xs.split(',') if a.strip()] for n,xs in rows}
assert all(set(xs)<=allowed for xs in axioms.values())
freeze=load(run/'freeze-review-v2.json')
module=Path('BanditRLProof/OnlineGradientDescentSource.lean')
headers={n:lean_declaration_header(module,n) for n in freeze['headers']}
assert all(hashlib.sha256(h.encode()).hexdigest()==freeze['headers'][n] for n,h in headers.items())
write(run/'public-actual-bindings-v2.json',dict(status='compiled-local-candidate',
    public_module_sha256=sha(module),public_canary_sha256=sha('Tests/OnlineGradientDescentSourceCanary.lean'),
    public_headers=headers,public_theorems=12,public_definitions=2,canary_theorems=30,
    canary_context_definitions_and_alias=7,actual_named_lookup_and_axioms=axioms,actual_axiom_count=75,
    root_jobs=9087,Tests_jobs=9228,actual_passed_gates=gates,
    preserved_historical_review_deltas=historical,
    native_actual_public_fences_and_safe_guards=12,old16_headers_and_all_code_tokens_unchanged=True,
    body_review='pending',full_harness='pending',graph='pending',site='pending',PR='pending',
    chapter_complete=False,book_complete=False,goal_complete=False,main_updated=False,live_updated=False))
write(run/'30_lower_worker-v2.md',
    'Actual source/compatibility adapters compiled in body-adapters-v2-01. Genuine continuous-dual '
    'linear regularity/gradient and existing feasible convex gradient bound supply both one-step '
    'inequalities in body-one-step-v2-01. Six actual old telescopes adapted to the new frozen '
    'premise compiled in body-cumulative-v2-01: same old iterate/variable recurrence, weighted '
    'potential, sharp negative residuals and actual tuned gradients. No consumer-bound premise. '
    'All12 frozen native public headers unchanged and actual context tokens unchanged. '
    'Old16 headers/all code tokens unchanged; old comment qualified with exact supersession '
    'snapshots. Actual30 public canaries/seven definitions,75 named lookup/axiom outputs, '
    'root9087/Tests9228/public-canary passed. Max-exp plane canary proves open nonconvex U, '
    'unbounded feasible line, actual gradient=-e0, played next=e0, positive regret and terminal '
    'square1; no Lean nonexistence-of-alternative-convex-U claim. Active interval and '
    'decreasing/tuned/T0/T1/zero-diameter/future-prefix regimes tested. Canary API01 and '
    'source01/02 failures retained, source03/04 repaired without target weakening. '
    'Original draft fence creation is header capture only; source-intent paths are not '
    'hypothesis substrings for native safe-verify. Separate public fences use actual Lean '
    'hypotheses and all12 actual checks pass. Body/source-qualified reader/full harness/graph/'
    'site/contributor/final immutable/PR gates remain pending. Whole Goal active.')
write(run/'public-body-review-packet-v2.md',
    'Required distinct actual body/canary review, GPT-6 Astra / medium. Read actual '
    'public-body-inputs-v2.json raw rows and actual source/blind/repaired contract. Challenge '
    'all12 new bodies/two definitions plus old16 audited OGD declarations/eight definitions; '
    'new context/header fingerprints remain unchanged. SourceRegularLoss producer must '
    'really derive every feasible ambient derivative from arbitrary open U. Compatibility '
    'only forward. Genuine affine gradient/regularity specialization of old lemma yields '
    'the quadratic part of the SAME original step; actual first-order producer and fixed/'
    'variable telescopes close sharp negative endpoints and tuned bounds. Old16 whole code '
    'tokens and headers unchanged, stronger RegularLoss is explicitly qualified in current '
    'comment; exact pre-integration raw bytes preserved for historical receipts. Review '
    'historical/raw supersession, do not falsely report drift-free live originals after '
    'authorized imports/comment. Exact75 actual #check/#print axioms standard3 or none, '
    'root9087/Tests9228/public canary compiled. Thirty actual canaries cover max-exp '
    'arbitrary-open regime in Euclidean Fin2, nonconvex U/unbounded V/actual gradient,'
    'step/positive regret/terminal1, active projection, decreasing and tuned paths, T0,'
    'T1 zero diameter and strict-prefix future change. Nonconvex supplied U is not a '
    'Lean proof that no alternative convex U exists; keep mathematical counterexample '
    'and formal canary scopes distinct. All failed API/canary proofs retained, no sorry '
    'in final code or axioms. Valid public safe fences preserve actual hypothesis '
    'fragments; original draft capture path metadata was not a safe-verify gate. '
    'Source-qualified reader correction/shared registry/full harness/actual graph/site/'
    'contributor/final immutable/PR gates separately pending. Body acceptance does not '
    'certify chapter/Goal/main/live. Write ONLY public-body-review-v2.md and '
    'public-body-receipt-v2.json with per-target verdicts, actual reviewed_files raw '
    'SHA inventory/reportSHA, required repairs and explicit semantic deltas. No edits '
    'to inputs; no human/external-model review claim.')
paths={r['path'] for r in load(run/'contract-source-inputs-v2.json')['rows']}
paths.update(str(p).replace('\\','/') for p in run.rglob('*') if p.is_file())
paths.update(['BanditRLProof/OnlineGradientDescentSource.lean',
    'Tests/OnlineGradientDescentSourceCanary.lean',
    'conversion-windows/ONLINE-OGD-MIGRATION-20261005.md',
    'proof-obligations/ONLINE-OGD-MIGRATION-20261005.md'])
paths.discard(str(run/'public-body-inputs-v2.json').replace('\\','/'))
write(run/'public-body-inputs-v2.json',dict(scope='actual12 public bodies/30 canaries and old16 exact audit',
    rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Actual12 public bodies/30 canaries/75 named axioms bound for independent body review.')
