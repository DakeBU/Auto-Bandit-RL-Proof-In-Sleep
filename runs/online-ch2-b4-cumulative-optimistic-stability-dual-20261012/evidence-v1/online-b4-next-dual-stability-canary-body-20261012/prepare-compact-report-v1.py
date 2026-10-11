from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parent;R=P.parent.parent
def bind(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda:f.read(1048576),b''):h.update(c)
    return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=h.hexdigest())
def load(p):return json.loads(p.read_text(encoding='utf-8'))
body=load(P/'focused-v2/receipt.json');imp=load(P/'imported-v1/receipt.json');fail=load(P/'focused-v1/receipt.json')
assert body['actual_exit']==imp['actual_exit']==0 and body['integrity_pass'] and imp['integrity_pass']
assert fail['actual_exit']==1 and fail['integrity_pass']
audit=load(P/'imported-audit-v2.json');orig=load(P/'imported-origins-v2.json');closure=load(P/'closure-manifest-v1.json')
expected={x['module']:Path(x['olean']).resolve() for x in closure['origins']}
expected['CumulativeOptimisticStabilityDualCanary']=(P/'CumulativeOptimisticStabilityDualCanary.olean').resolve()
assert len(orig)==len(expected) and {x['module'] for x in orig}==set(expected)
assert all(Path(x['olean']).resolve()==expected[x['module']] for x in orig)
stdout=Path(imp['stdout']['path']).read_text(encoding='utf-8')
axioms=[[x.strip() for x in a.split(',')] for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',stdout)]
assert len(axioms)==2 and all(set(a)<=set(['propext','Classical.choice','Quot.sound']) for a in axioms)
assert 'sorryAx' not in stdout and 'error:' not in stdout
candidate=(P/'candidate-v2.lean').read_bytes()
extracted=re.sub(rb' := by\n.*?(?=\nend (?:Tight|ZeroCurvature))',b'',candidate,flags=re.S)
frozen=R/'tmp/online-b4-next-dual-stability-canary-freeze-20261012/scratch-frozen-context-and-statements-v1.txt'
assert extracted==frozen.read_bytes()
canonical=extracted.replace(b'import CumulativeOptimisticStabilityDualCandidate',b'import BanditRLProof.OnlineCumulativeOptimisticStabilityDual',1)
assert hashlib.sha256(canonical).hexdigest()=='cd505b523c0124de97f76a59bdbf24e840d0bb40aa6a6d8a7074e86cdca7fb16'
assert audit['first_conjunction_actual_bound'] and len(audit['provider_operands'])==1
assert audit['zero_case']['conjunct_count']==14 and audit['zero_case']['no_invalid_dual_call']
rows=[]
for label,a in [('tight',audit),('zero',audit['zero_case'])]:
    rows.append(dict(declaration=a['declaration'],TYPE=dict(constants=len(a['TYPE']),stream=bind(P/(label+'-TYPE-normalized-v1.txt'))),VALUE=dict(constants=len(a['VALUE']),stream=bind(P/(label+'-VALUE-normalized-v1.txt')))))
report=dict(status='EXPERIMENTAL_CANARY_COMPILED_IMPORTED_AUDITED_PENDING_SOURCE_REVIEW',candidate=bind(P/'candidate-v2.lean'),olean=bind(P/'CumulativeOptimisticStabilityDualCanary.olean'),header_receipt=bind(P/'header-v1/receipt.json'),body_receipt=bind(P/'focused-v2/receipt.json'),import_receipt=bind(P/'imported-v1/receipt.json'),probe=bind(P/'ImportedAudit-v2.lean'),audit=bind(P/'imported-audit-v2.json'),header=dict(canonical_bytes=len(canonical),canonical_sha256=hashlib.sha256(canonical).hexdigest(),scratch_bytes=len(extracted),scratch_sha256=hashlib.sha256(extracted).hexdigest(),exact_LF_bytes=True,sole_import_transport=True),rows=rows,axioms=axioms,provider_operands=audit['provider_operands'],first_conjunction_actual_bound=True,zero_case=dict(conjunct_count=14,internal_conjunct_proofs=audit['zero_case']['internal_conjunct_proofs'],no_invalid_dual_call=True),module_origins=audit['module_origins'],closure=dict(manifest=bind(P/'closure-manifest-v1.json'),actual_imported_origins=bind(P/'imported-origins-v2.json'),input_modules=len(closure['origins']),input_files=len(closure['inputs']),actual_modules=len(orig),exact_declared_closure_plus_canary=True,header_BODY_import_full_prepost_equal=True),failures=[dict(candidate=bind(P/'candidate-v1.lean'),receipt=bind(P/'focused-v1/receipt.json'),actual_exit=1,integrity_pass=True,errors=['Tight local-support coe-product toReal simplification','Zero-curvature reflexive inequality left after ring_nf'],repair='BODY-only candidate-v2: simplify coe.toReal before general simp; close reflexive inequality with le_rfl')],warnings=['Retained unused EReal.coe_le_coe_iff simp argument in Tight prediction proof; no new warning suppression'],audit_limits=['All actual explicit21-slot provider operands checked via concrete constants/numerals/internal binders and E=Real. The two implicit instance expressions are exported for review rather than separately identified by a predicate.','Zero-case internal facts for global no-bottom/domain/curvature/minimum/support/membership/norm/objective values are checked as returned conjunction proofs; final numeric arithmetic is source-review evidence plus exact closed TYPE/VALUE, not separate arithmetic-procedure audit.','Normalized streams remove binder names and mdata only; no proof irrelevance/equality substitution.'],source_boundaries=['No canonical installation or source/reader acceptance implied','lambda0 counterexample invalidates only dropping strict positivity from divided bound; sharp parent lambda0 remains valid','No attainment/global support producer/full7.47/full15.31/terminal ghost cancellation'],chapter_accepted=False,global_goal_complete=False)
out=P/'compiled-canary-report-v1.json'
with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(report,f,indent=2);f.write('\n')
print(json.dumps(dict(report=bind(out),counts=[dict(declaration=x['declaration'],TYPE=x['TYPE']['constants'],VALUE=x['VALUE']['constants']) for x in rows])))
