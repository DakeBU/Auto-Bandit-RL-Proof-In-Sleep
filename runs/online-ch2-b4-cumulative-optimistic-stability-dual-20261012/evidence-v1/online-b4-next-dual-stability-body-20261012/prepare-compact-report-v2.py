from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parent
def bind(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda:f.read(1048576),b''):h.update(c)
    return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=h.hexdigest())
def load(p):return json.loads(p.read_text(encoding='utf-8'))
body=load(P/'focused-v1/receipt.json');imp=load(P/'imported-v1/receipt.json')
assert body['actual_exit']==imp['actual_exit']==0 and body['integrity_pass'] and imp['integrity_pass']
audit=load(P/'imported-audit-v2.json');orig=load(P/'imported-origins-v2.json');closure=load(P/'closure-manifest-v1.json')
expected={x['module']:Path(x['olean']).resolve() for x in closure['origins']}
expected['CumulativeOptimisticStabilityDualCandidate']=(P/'CumulativeOptimisticStabilityDualCandidate.olean').resolve()
assert len(orig)==len(expected) and {x['module'] for x in orig}==set(expected)
assert all(Path(x['olean']).resolve()==expected[x['module']] for x in orig)
stdout=Path(imp['stdout']['path']).read_text(encoding='utf-8')
assert re.search(r'\[propext,\s*Classical\.choice,\s*Quot\.sound\]',stdout)
assert 'sorryAx' not in stdout and 'error:' not in stdout
candidate=(P/'candidate-v1.lean').read_bytes();suffix=b'\n\nend BanditRL.OnlineConvex\n'
extracted=candidate.split(b' := by\n',1)[0]+suffix
assert extracted==(P/'scratch-frozen-header-v1.txt').read_bytes()
canonical=extracted.replace(b'import CumulativeOptimisticStabilityCandidate',b'import BanditRLProof.OnlineCumulativeOptimisticStability',1)
assert hashlib.sha256(canonical).hexdigest()=='6dd6994aca1486626223fe94d723a2cd951d8fa94e489627af9cd68b5e5e0cf5'
rows=audit['provider_operands'];assert len(rows)==2 and all(x['passed'] for x in rows)
report=dict(status='EXPERIMENTAL_COMPILED_IMPORTED_AUDITED_NOT_SOURCE_ACCEPTED',candidate=bind(P/'candidate-v1.lean'),olean=bind(P/'CumulativeOptimisticStabilityDualCandidate.olean'),header_receipt=bind(P/'header-v1/receipt.json'),body_receipt=bind(P/'focused-v1/receipt.json'),import_receipt=bind(P/'imported-v1/receipt.json'),import_probe=bind(P/'ImportedAudit-v2.lean'),import_report=bind(P/'imported-audit-v2.json'),header=dict(canonical_bytes=len(canonical),canonical_sha256=hashlib.sha256(canonical).hexdigest(),scratch_bytes=len(extracted),scratch_sha256=hashlib.sha256(extracted).hexdigest(),transport='Only canonical parent import changed to actual accepted scratch module; remaining bytes exact LF',no_line_ending_normalization=True),TYPE=dict(constants=len(audit['TYPE']),stream=bind(P/'TYPE-normalized-v1.txt')),VALUE=dict(constants=len(audit['VALUE']),stream=bind(P/'VALUE-normalized-v1.txt')),standard_axioms=['propext','Classical.choice','Quot.sound'],provider_operands=rows,module_origins=audit['module_origins'],full_import_origins=dict(file=bind(P/'imported-origins-v2.json'),module_count=len(orig),exact_header_closure_plus_candidate=True),full_input_provenance=dict(manifest=bind(P/'closure-manifest-v1.json'),modules=len(closure['origins']),files=len(closure['inputs']),before_after_equal=True,header_trial_scope='Initial header trial pins declared parents; complete actual closure was discovered there and pinned before BODY/import.'),normalization='Binder names and mdata only; no proof irrelevance/equality substitution. SHA256 is of full normalized Expr text, not source RAW.',body_proof_route=['Actual parent at all identical parameters; lambda nonnegativity internally derived from strict positivity','Operator norm at actual g and original E displacement p-q','Positive denominator and scalar square completion'],failures=bind(P/'construction-failure-ledger-v1.json'),source_boundaries=['lambda strictly positive; zero curvature remains only in parent','No support existence/attainment/ghost/full7.47/full15.31 or terminal cancellation','No canonical install/source review/reader acceptance inferred'],chapter_accepted=False,global_goal_complete=False)
out=P/'compiled-core-report-v1.json'
with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(report,f,indent=2);f.write('\n')
print(json.dumps(dict(report=bind(out),TYPE_constants=report['TYPE']['constants'],VALUE_constants=report['VALUE']['constants'],provider_rows=rows)))
