"""Repair a real manifest gate failure; preserve prior manifest and old code tokens."""
from pathlib import Path
import hashlib,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import _strip_lean_comments
run=Path(__file__).parent
p=Path('research-wiki/contribution-contracts/ONLINE-OGD-MIGRATION-20261005.json')
raw=p.read_bytes();snapshot=run/'leaves/pre-contributor-repair-manifest-v2.json'
assert not snapshot.exists();snapshot.write_bytes(raw)
x=json.loads(raw)
x['affected_files']=[n for n in x['affected_files'] if not n.startswith('Tests')]
x['verification']['focused_checks'].append('Tests.lean imports Tests/OnlineGradientDescentSourceCanary.lean; these tested paths are not classified as production by the actual contributor checker.')
x['verification']['bandit_check']='Combined root9087jobs, Tests9228jobs and complete tools/bandit.py check passed:466 tests/7 existing skips. Source-comment qualification only, fresh integrated gate follows.'
x['verification']['site_check']='Exact stacked manifest scope repaired after real failure; clean registry/reader/immutable gates pending.'
with p.open('w',encoding='utf-8',newline='\n') as f:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
old=Path('BanditRLProof/OnlineGradientDescentVariable.lean');before=old.read_bytes()
source=before.decode('utf-8')
comment='''/-!
The variable-step recurrence is shared by both OGD interfaces. The historical
performance theorems below use `RegularLoss`, which requires convexity on an open
differentiability neighborhood. The source-facing bounds in
`BanditRL.OnlineGradientDescentSource` instead accept convexity on the feasible
set and ambient derivatives there; `source_to_feasible` produces these premises
from a supplied extension differentiable on an arbitrary open neighborhood.
They use this same `iterateVariable` and retain the negative terminal residual.
-/

'''
assert comment not in source
marker='noncomputable section'
source=source.replace(marker,comment+marker,1)
assert ' '.join(_strip_lean_comments(before.decode('utf-8')).split())==' '.join(_strip_lean_comments(source).split())
with old.open('w',encoding='utf-8',newline='\n') as f:f.write(source)
original=run/'leaves/pre-integration-BanditRLProof--OnlineGradientDescentVariable.lean.txt'
assert original.read_bytes()==before
record=dict(status='repair-authored',failed_gate='contributor-exact-v2-02',
    candidate_manifest_snapshot=snapshot.as_posix(),candidate_manifest_sha256=hashlib.sha256(raw).hexdigest(),
    actual_production_scope=x['affected_files'],tested_nonproduction_paths=['Tests.lean','Tests/OnlineGradientDescentSourceCanary.lean'],
    old_variable_raw_before_sha256=hashlib.sha256(before).hexdigest(),old_variable_snapshot=original.as_posix(),
    old_variable_raw_after_sha256=hashlib.sha256(old.read_bytes()).hexdigest(),
    old_variable_code_tokens_unchanged=True,
    reason='Actual checker only permits changed protected/production paths. Tests are evidence rather than production manifest paths. Retained variable API receives the same explicit historical stronger-regularity qualification as the fixed module; all old code/header tokens remain unchanged. No source boundary or theorem weakening.',
    pending='Fresh root/Tests/full harness, commit and actual exact-base contributor rerun; final reader independently checks comment delta and raw supersession.')
with (run/'contributor-scope-repair-v2.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(record,f,indent=2);f.write('\n')
print('Real manifest scope repair and source qualification authored; all old variable code tokens unchanged.')
