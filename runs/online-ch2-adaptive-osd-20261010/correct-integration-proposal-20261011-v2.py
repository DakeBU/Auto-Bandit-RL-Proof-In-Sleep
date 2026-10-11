from common import *
import copy,re
sys.path.insert(0,str(ROOT))
from tools.check_contributor_contract import validate_contract
production_review=RUN/'fresh-production-source-review-20261011-v1.json'
canary_review=RUN/'fresh-canary-BODY-review-20261011-v1.json'
blind=RUN/'fresh-canary-blind-decoder-20261011-v1.json'
assert load(production_review)['verdict']=='accepted-with-explicit-delta'
assert load(canary_review)['canary_verdict']=='accepted-with-explicit-delta' and not load(canary_review)['blocking_repairs']
assert load(blind)['actor']=='/root/adaptive_decoder'
assert load(canary_review)['verification_manifest_raw_sha256']==sha(RUN/'algorithm-canary-verification-manifest-v4.json')
plan=load(RUN/'exact-integration-proposal-20261011-v1.json')
manifest=load(RUN/'prospective-contribution-20261011-v1.json')
manifest['semantic_roundtrip'].update(status='accepted',blind_decoder='/root/adaptive_decoder',verdict='accepted-with-explicit-delta')
manifest['semantic_roundtrip']['remaining_semantic_delta'] += ' Current distinct fresh production/source and complete canary BODY reviews accepted-with-explicit-delta; exact receipts: '+json.dumps(rows([production_review,canary_review,blind]),separators=(',',':'))+'. This semantic status does not assert combined gates, native/package acceptance or chapter closure.'
manifest['verification']['focused_checks']=['Seven complete actual-run canaries focused compiled; seven full public statements/standard axiom audits/fences/safe-verifies passed; ten selected lexical VALUE branch parent occurrences verified by V4 exporter. Exact manifest '+sha(RUN/'algorithm-canary-verification-manifest-v4.json')+'. Original V1/V2 exporter failures and V3 diagnostic retained. Syntactic branch occurrence is not a closed independent subproof or necessity certificate.']
manifest['verification']['independent_review']='Fresh distinct current production/source and seven complete canary BODY reviews accepted-with-explicit-delta. Exact6file integration proposal, combined root/Tests/full harness/site, native/package and delivery remain pending. '+json.dumps(rows([production_review,canary_review]),separators=(',',':'))
records=[]
for module in ['OnlineAdaptivePotential','OnlineAdaptiveOSD','OnlineAdaptiveBenchmark']:
    p=ROOT/('BanditRLProof/'+module+'.lean')
    for kind,name in re.findall(r'^(theorem|def|abbrev) ([A-Za-z0-9_]+)',p.read_text(encoding='utf8'),re.M):
        full='BanditRL.'+module+'.'+name
        records.append(dict(name=full,kind=kind,shared_registry_id='declaration:'+full))
assert len(records)==40 and sum(r['kind']=='abbrev' for r in records)==2 and sum(r['kind']=='def' for r in records)==8 and sum(r['kind']=='theorem' for r in records)==30
manifest['declarations']=[r['name'] for r in records]
manifest['reuse_plan']['new_shared_declarations']=[r['name'] for r in records]
mapping=load(RUN/'shared-book-mapping-proposal-20261011-v1.json')
mapping['canonical_declarations']=records
mapping['structural_counts']=dict(canonical_scanner_nodes=40,alias_abbreviations=2,definitions=8,theorem_declarations=30,boundary='Structural declaration counts, not40source results or30independent source obligations. Three reader cards combine algebraic generalization/source guarantees/separate benchmark repair; chapter denominator remains null.')
write(RUN/'shared-book-mapping-proposal-20261011-v2.json',mapping)
# Improve information-interface precision in the new appended cards/highlights only.
old='Fixed SupportPolicy receives time, played point, current loss and strict-past history; it is not reselected for different futures.'
new='Fixed SupportPolicy receives time, the entire strict-past loss functions, the played-point history through the current point, and the current loss; it is not reselected for different futures.'
reader=load(RUN/'reader-integration-proposal-20261011-v1.json')
reader_text=json.dumps(reader,ensure_ascii=False)
assert old in reader_text
reader=json.loads(reader_text.replace(old,new))
write(RUN/'reader-integration-proposal-20261011-v2.json',reader)
for row in plan['rows']:
    if row['path'].endswith('readings.json') or row['path'].endswith('highlights.json'):
        oldap=Path(row['after_snapshot']);text=oldap.read_text(encoding='utf8')
        assert old in text
        ap=RUN/'integration-proposal-snapshots-20261011-v2'/oldap.name
        write(ap,text.replace(old,new))
        row['after_snapshot']=ap.as_posix();row['after_sha256']=sha(ap)
manifest['semantic_roundtrip']['remaining_semantic_delta']=manifest['semantic_roundtrip']['remaining_semantic_delta'].replace(old,new)
write(RUN/'prospective-contribution-20261011-v2.json',manifest)
_,errors=validate_contract(RUN/'prospective-contribution-20261011-v2.json')
write(RUN/'prospective-contribution-schema-check-20261011-v2.json',dict(manifest=rows([RUN/'prospective-contribution-20261011-v2.json']),errors=errors,scope='Manifest validator only; diff-aware/global/combined/reader gates remain pending.'))
assert not errors,errors
plan.update(prospective_manifest=rows([RUN/'prospective-contribution-20261011-v2.json']),reader_proposal=rows([RUN/'reader-integration-proposal-20261011-v2.json']),mapping=rows([RUN/'shared-book-mapping-proposal-20261011-v2.json']),semantic_reviews=rows([production_review,canary_review,blind]),supersedes=rows([RUN/'exact-integration-proposal-20261011-v1.json']),changes_from_v1='Correct fresh decoder actor; bind actual independent reviews and successful V4 verification; include2aliases in40structural nodes; state exact policy input interface. No original source/Lean/header edits. Semantic accepted does not promote package/chapter/native.')
write(RUN/'exact-integration-proposal-20261011-v2.json',plan)
print('v2 manifest validator passed. Plan SHA '+sha(RUN/'exact-integration-proposal-20261011-v2.json'))
