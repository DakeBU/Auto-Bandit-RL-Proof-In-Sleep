"""Bound contract review to the two targets and their actual source/context."""
from pathlib import Path
import hashlib,json,re
run=Path(__file__).parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
    p=run/n;assert not p.exists(),p
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
assert load(run/'draft-header-types-v2-01-exit.json')['exit_code']==1
raw=(run/'draft-header-types-v2-01.log').read_text(encoding='utf-8')
errors=re.findall(r'error: ([^\n]+)',raw)
assert errors==['unsolved goals','unsolved goals'],errors
assert 'unexpected token' not in raw
write('private-probe-typing-assessment-v2.json',dict(status='two headers elaborate; intentionally unproved',
    errors=errors,raw_log_sha256=sha(run/'draft-header-types-v2-01.log'),exit_code=1,compiled_proofs=False,
    original_parser_failure_preserved=True,header_change=False,source_accepted=False))
blind=load(run/'blind-receipt-v1.json')
assert sha(run/'blind-packet-v1.md') in json.dumps(blind)
assert sha(run/'blind-reconstruction-v1.md') in json.dumps(blind)
packet='''Distinct source CONTRACT review, requested GPT-6 Astra / medium. Read contract-source-inputs-v1.json and independently rehash every row. Seek mismatch rather than confirm root. Review the two frozen unproved target headers/scoped context, restricted-input reconstruction, Orabona v10 printed9-10/PDF21-22, and actual pinned prerequisites. Primary is the finite-loss main-text sentence; supporting domain identity is separate library foundation. Source necessary direction is explicitly refined to an iff, not attributed as a numbered printed theorem. General arbitrary carrier is explicit algebraic generalization of Rd.

Finite means exists REAL equality, not merely below-top. The exact iff requires membership AND original finite value. Membership alone fails for f=top. f may attain either infinity; no noBottom needed for the primary iff, since bottom+top=bottom is still not finite. Ordinary EReal addition is retained; upperAdd is NOT substituted. Effective domain is the shared f<top definition, includes bottom, and the separate intersection equality keeps GLOBAL noBottom; dropping it permits bottom outside V to leak into the domain. No convexity/topology/nonempty or finite-dimensional assumption is needed for this algebra. Do not treat either desired conclusion as an assumed consumer premise.

There are ZERO actual new public proofs now. The repaired private probe v2 has exactly two intended unsolved-goal errors and no parser errors. Original probe v1 and parser failure remain unchanged. Probe typing/fences are not proof compilation. Assess source intention and actual contract before stabilization; proof/canary/body/integrated/reader acceptance follows separately. Existing prerequisite module is read as context, not a newly accepted package. Future public canaries must cover nonconstant finite inside, finite outside, top inside, bottom both sides, empty V, and a domain counterexample without hbot. Distinct actors have prior history; no history-blind/human/external/runtime model attestation claim.

Return accepted|rejected|accepted-with-explicit-delta, all seven slots per exact target, required mathematical repairs and reader qualifications separately. Write ONLY source-contract-review-v1.md and source-contract-receipt-v1.json here. Receipt: actor.task=/root/source_reviewer, verdict, target_verdicts keyed by qualified names, mathematical_repairs, required_reader_corrections, reviewed_files raw path/SHA list, report path/SHA. Whole book Goal active, Chapter2 countnull/incomplete, no main/live/merge/deploy.
'''
write('source-review-packet-v1.md',packet)
paths={p.as_posix() for p in run.rglob('*') if p.is_file()}
paths.update(p.as_posix() for p in Path('docs/contracts/online-finite-loss-v1').rglob('*') if p.is_file())
paths.update(['../research-online-ogd/tmp/pdfs/orabona-v10.pdf','BanditRLProof/OnlineConvexExtended.lean',
 '.lake/packages/mathlib/Mathlib/Data/EReal/Operations.lean','.agents/skills/bandit-semantic-roundtrip/SKILL.md',
 'lean-toolchain','lakefile.lean','lake-manifest.json','runs/online-convex-migration-20261005/finite-loss-constraint-gap-v1.json',
 'tasks/ONLINE-FINITE-LOSS-20261005.md','conversion-windows/ONLINE-FINITE-LOSS-20261005.md',
 'proof-obligations/ONLINE-FINITE-LOSS-20261005.md'])
for p in paths:assert Path(p).is_file(),p
write('contract-source-inputs-v1.json',dict(scope='two finite-loss/domain unproved contracts only',
    rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Fixed',len(paths),'raw inputs; clean header typing assessment; source review pending.')
