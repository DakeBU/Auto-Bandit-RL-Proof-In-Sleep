"""Preserve historical review bytes before explicit public/source-reader supersession."""
from pathlib import Path
import hashlib, json, re, sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header, _strip_lean_comments
run = Path(__file__).parent
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p, obj):
    with Path(p).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(obj,str): f.write(obj)
        else: json.dump(obj,f,indent=2);f.write('\n')
fixed = json.loads((run/'contract-source-inputs-v2.json').read_text())['rows']
expected = {r['path']:r['sha256'] for r in fixed}
paths = ['BanditRLProof.lean','Tests.lean','BanditRLProof/OnlineGradientDescent.lean',
    'BanditRLProof/OnlineGradientDescentVariable.lean', 'website/content/books.json',
    'website/content/chapters.json','website/content/readings.json','website/content/highlights.json',
    'docs/contracts/online-book-v1/source-inventory.json']
supersessions = []
for path in paths:
    original = Path(path)
    if path in expected: assert sha(original)==expected[path], path
    snapshot = run/'leaves'/('pre-integration-'+path.replace('/','--')+'.txt')
    assert not snapshot.exists(), snapshot
    snapshot.write_bytes(original.read_bytes())
    supersessions.append(dict(path=path,raw_sha256=sha(original),snapshot=str(snapshot),
        snapshot_sha256=sha(snapshot),bound_by_v2_fixed_inputs=path in expected,
        reason='later root import, explicit comment/source-reader qualification or inventory reconciliation; '
               'original review remains bound to its historical bytes, never rewritten'))
write(run/'historical-raw-supersession-v2.json',dict(rows=supersessions,
    source_receipts=['source-contract-receipt-v1.json','source-contract-receipt-v2.json'],
    receipt_bytes_unchanged=True,semantic_body_changes_authorized=False))
module=Path('BanditRLProof/OnlineGradientDescentSource.lean')
current=module.read_text(encoding='utf-8')
freeze=json.loads((run/'freeze-review-v2.json').read_text())
names=['theorem_2_13_fixed','variable_one_step','theorem_2_13_variable_bound',
       'theorem_2_13_variable','equation_2_1_distance','equation_2_1']
for name in names:
    original=Path('BanditRLProof/OnlineGradientDescent.lean' if name.endswith('_fixed')
        or name.startswith('equation') else 'BanditRLProof/OnlineGradientDescentVariable.lean')
    header=re.search(r'(?ms)^theorem '+name+r'\b.*?(?= := by)',original.read_text(encoding='utf-8')).group()
    header=header.replace('RegularLoss','FeasibleRegularLoss')
    current=re.sub(r'(?ms)^theorem '+name+r'\b.*?(?= := by)',lambda _:header,current,count=1)
write(module,current)
for name,expected_hash in freeze['headers'].items():
    assert hashlib.sha256(lean_declaration_header(module,name).encode()).hexdigest()==expected_hash,name
old=Path('BanditRLProof/OnlineGradientDescent.lean')
before=old.read_text(encoding='utf-8')
after=before.replace('/-- Source regularity: convex and differentiable on an open neighborhood of the domain. -/',
    '/-- Historical stronger regularity: convex and differentiable on a convex open neighborhood.\n'
    'For the source arbitrary-open hypothesis, use `OnlineGradientDescentSource.SourceRegularLoss`\n'
    'and its proved `source_to_feasible` adapter. This predicate is retained for compatibility. -/')
after=after.replace('The Hilbert-space interfaces specialize to finite-dimensional real Euclidean spaces.',
    'The Hilbert-space interfaces specialize to finite-dimensional real Euclidean spaces.\n'
    'Loss-dependent declarations below use the stronger historical `RegularLoss` predicate.\n'
    '`OnlineGradientDescentSource` supplies the arbitrary-open source regularity interface\n'
    'on the same algorithms. Projection and causal feasibility statements need no loss regularity.')
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(before)==tokens(after)
write(old,after)
for path,imp in [('BanditRLProof.lean','import BanditRLProof.OnlineGradientDescentSource'),
                 ('Tests.lean','import Tests.OnlineGradientDescentSourceCanary')]:
    p=Path(path);s=p.read_text(encoding='utf-8');assert imp not in s
    write(p,s.rstrip()+'\n'+imp+'\n')
canary=Path('Tests/OnlineGradientDescentSourceCanary.lean')
(run/'leaves/canary-source-v2-04.lean').write_bytes(canary.read_bytes())
s=canary.read_text(encoding='utf-8')
assert s.startswith('import BanditRLProof.OnlineGradientDescentSource\n')
write(canary,s.replace('import BanditRLProof.OnlineGradientDescentSource\n','import BanditRLProof\n',1))
write(run/'public-integration-v2.json',dict(frozen_headers_unchanged=12,
    old_lean_code_tokens_unchanged=True, old_comment_explicitly_qualified=True,
    snapshots=str(run/'historical-raw-supersession-v2.json'),
    public_module_sha256=sha(module), public_canary_sha256=sha(canary),
    root_gate='pending',Tests_gate='pending',combined_harness='pending',body_review='pending',
    package_accepted=False,chapter_complete=False,goal_complete=False))
print('Public imports added, all12 headers unchanged; historical bytes retained, old code tokens unchanged.')
