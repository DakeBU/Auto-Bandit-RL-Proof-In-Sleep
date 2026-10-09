from common import *
fixed()
test=ROOT/'Tests/OnlineAdaptiveSummationCanary.lean'
assert load(RUN/'canary-focused-build-v3.json')['actual_exit']==0
assert load(RUN/'canary-full-public-axioms-v1.json')['actual_exit']==0
values=load(RUN/'canary-compiled-conjunct-VALUE-v1.json')
assert len(values['nodes'])==3 and len(values['selected_conjuncts'])==3
assert all(r['required_present'] for r in values['selected_conjuncts'])
import re
for name,expected in [('production-public-value-axioms-v1',1),('canary-full-public-axioms-v1',2)]:
    receipt=load(RUN/(name+'.json'));raw=base64.b64decode(receipt['stdout_base64']);assert hashlib.sha256(raw).hexdigest()==receipt['stdout_sha256']
    brackets=re.findall(r'depends on axioms: \[([^]]*)\]',raw.decode('utf8'))
    assert len(brackets)==expected
    for bracket in brackets: assert set(x.strip() for x in bracket.split(','))<={'propext','Classical.choice','Quot.sound'}
write(RUN/'three-public-axiom-brackets-inspected-v1.json',dict(production=1,full_Test=2,all_only_standard_baseline_axioms=True,source_placeholders=False,whole_Goal='active'))
paths=list(CONTRACT.rglob('*'))+list(RUN.rglob('*'))+[PUBLIC,test]
paths += [ROOT/d/(TASK+'.md') for d in ['tasks','conversion-windows','proof-obligations','research-wiki/retrieval-index']]
write(RUN/'canary-BODY-review-inputs-v1.json',dict(rows=rows(paths),actual_compiled_public_values=3,selected_inequality_branches=3,Test_private_helpers=0,production_proofs=1,full_canaries=2,scope='Canary BODY/source semantics only; no integration or package acceptance.',chapter_complete=False,whole_Goal='active'))
write(RUN/'canary-BODY-review-request-v1.md','''# Complete canary BODY review

Independently audit both complete canary bodies against exact reviewed canary-v1 headers/context and pinned source Lemma4.13. Main production remains fixed at SHA802b9dfef436477f7abf32907ddd0da357862f5d9f7607c8febfcfc3890ae1a3. Verify the exact rational right-endpoint sum1/4 and integral1/2 for nonconstant max(1-x,0) with [1/2,0,1/2]; strict comparison and all eight conjuncts. Check integral congruence on Icc0,1 and actual global integral_id. Second full canary has both horizon0 and nonempty allzero cases with offset2/nonzero integrand. No private Test helpers or local hidden premises. Actual compiled environment extraction selects the three relevant inequality conjunction branches and finds the public production theorem in each; read actual values and proof source, do not infer reuse from imports alone or call presence proof necessity.

Read failed attempts v1/v2 and exact v2/v3 API repair records, snapshots and native logs. One route and frozen types preserved; no theorem repair or excluded degenerate cases. Actual focused build v3/3323jobs, full public probes, three total public axiom brackets, all three fences/safe-verifies and compiled VALUE/conjunction exports pass. Exit0 of wrapper does not erase nested failed build receipts. Four retrospective lower attempt logs preserve two compiled/two failed executions; unaccepted obligations remain1/1 or2/2 and no reviewer-validated acceptance. OWN .gitattributes delta adds only one exact native trials.jsonl CRLF recognition rule with original RAW retained, default checks preserved. Prior live-native changes resolve using pre-transition snapshots and exact event receipts; prior attrs via native-attempts-and-attributes-inspected-v1.

Check all current fixed RAW rows before/after and all old34997 baseline. Record exact mathematical/BODY semantic verdict, full source/type/context/hash agreement, all actually read inputs and no chapter/native/package closure. If accepted authorize only prospective NEW OWN integration proposals/evidence next; editing old roots/reader/coverage and publishing require a separately exact reviewed integration plan. Produce only canary-BODY-review-v1.md/json here. Whole Goal active, Chapter2 partial/null, Chapter4 unenumerated/null, all eightforward/sixfuture required/open. Reused automated distinct reviewer history disclosed; no human/external/runtime attestation.
''')
fixed()
print('Canary BODY index',sha(RUN/'canary-BODY-review-inputs-v1.json'),flush=True)
