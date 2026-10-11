from common import *
import json
plan=load(RUN/'exact-integration-proposal-20261011-v2.json')
replacements={
'Distinct current semantic/BODY/integration review, combined root/Tests/full harness, contributor and site/registry checks remain required.':'Current distinct production/source and canary BODY reviews are accepted-with-explicit-delta; exact integration review, combined root/Tests/full harness, contributor and site/registry checks remain required.',
'Compiled candidate; independent current review and combined gates pending':'Source/BODY-reviewed candidate; exact integration and combined gates pending',
'Historical staged reviews retained; current independent reviews and exact integration review pending; no runtime model attestation.':'Historical staged reviews retained; current independent production/source and canary BODY reviews are accepted-with-explicit-delta. Exact integration and combined/publication gates remain pending; no runtime model attestation.',
'candidate-pending-independent-review-and-gates':'source-body-reviewed-candidate-pending-integration-and-gates',
'compiled-candidate-pending-current-review-and-joint-gates':'source-body-reviewed-candidate-pending-integration-and-joint-gates'
}
def correct(s):
    for old,new in replacements.items(): s=s.replace(old,new)
    return s
for row in plan['rows']:
    if row['path'].endswith('.json'):
        before=Path(row['before_snapshot']).read_bytes()
        ap=RUN/'integration-proposal-snapshots-20261011-v3'/Path(row['after_snapshot']).name
        text=correct(Path(row['after_snapshot']).read_text(encoding='utf8'))
        write(ap,text)
        row['after_snapshot']=ap.as_posix();row['after_sha256']=sha(ap)
        # Preserve all older list entries and old boundary text as a prefix.
        old=json.loads(before);new=json.loads(text)
        if row['path'].endswith('highlights.json'): assert new['highlights'][:-3]==old['highlights']
        elif row['path'].endswith('readings.json'):
            a=next(x for x in old['readings'] if x['slug']=='online-ogd');b=next(x for x in new['readings'] if x['slug']=='online-ogd')
            assert b['source_theorems'][:-3]==a['source_theorems']
        elif row['path'].endswith('coverage.json'):
            a=next(x for x in old['chapters'] if x['chapter']==2);b=next(x for x in new['chapters'] if x['chapter']==2)
            assert b['boundary'].startswith(a['boundary']) and b['accepted']==False and b['mandatory_count'] is None and b['required_open_forward_containers']==8
        else:
            a=next(x for x in old['chapters'] if x['slug']=='online-ogd');b=next(x for x in new['chapters'] if x['slug']=='online-ogd')
            assert b['completion_definition'].startswith(a['completion_definition'])
reader=json.loads(correct((RUN/'reader-integration-proposal-20261011-v2.json').read_text(encoding='utf8')))
write(RUN/'reader-integration-proposal-20261011-v3.json',reader)
manifest=json.loads(correct((RUN/'prospective-contribution-20261011-v2.json').read_text(encoding='utf8')))
manifest['semantic_roundtrip']['formalizer']='Historical production definitions/proofs: /root; current algorithm canary BODY repair/completion: /root/adaptive_formalizer.'
manifest['semantic_roundtrip']['blind_decoder']='Historical production source-blind reconstruction: /root/osd_blind; fresh seven-canary restricted-input reconstruction only: /root/adaptive_decoder.'
manifest['semantic_roundtrip']['source_reviewer']='Historical staged source/BODY actors retained in original receipts; current fresh three-production-module source/BODY and seven-canary BODY reviewer: /root/adaptive_reviewer.'
manifest['semantic_roundtrip']['remaining_semantic_delta'] += ' Fresh canary decoder did not decode the production package; historical production reconstructions remain their own evidence. Current production source reviewer inspected actual source and all three production modules independently. Role scopes are not interchangeable.'
write(RUN/'prospective-contribution-20261011-v3.json',manifest)
sys.path.insert(0,str(ROOT))
from tools.check_contributor_contract import validate_contract
_,errors=validate_contract(RUN/'prospective-contribution-20261011-v3.json')
write(RUN/'prospective-contribution-schema-check-20261011-v3.json',dict(manifest=rows([RUN/'prospective-contribution-20261011-v3.json']),errors=errors,scope='Manifest validator only; global gates pending.'))
assert not errors,errors
plan.update(prospective_manifest=rows([RUN/'prospective-contribution-20261011-v3.json']),reader_proposal=rows([RUN/'reader-integration-proposal-20261011-v3.json']),supersedes=rows([RUN/'exact-integration-proposal-20261011-v2.json']),changes_from_v2='Scope actor roles to historical production vs fresh canary; new candidate suffixes acknowledge actual favorable source/BODY review while exact integration and combined/publication remain pending; old objects/text retained.')
write(RUN/'exact-integration-proposal-20261011-v3.json',plan)
print('v3 proposal SHA '+sha(RUN/'exact-integration-proposal-20261011-v3.json'))
