from common import *
plan=load(RUN/'exact-integration-proposal-20261011-v4.json')
reader=load(RUN/'reader-integration-proposal-20261011-v4.json')
old='Complete exact folded Lean and displayed proof are exposed by the adjacent teaching highlight.'
new='The exact Lean statement is folded in the adjacent teaching highlight; its natural-language/formula proof is in the teaching notes, and the complete Lean proof BODY is available through the source link.'
for card in reader['source_cards']:
    assert old in card['contract']['guarantee'];card['contract']['guarantee']=card['contract']['guarantee'].replace(old,new)
write(RUN/'reader-integration-proposal-20261011-v5.json',reader)
for row in plan['rows']:
    if row['path'].endswith('readings.json'):
        obj=load(row['after_snapshot']);before=load(row['before_snapshot'])
        item=next(x for x in obj['readings'] if x['slug']=='online-ogd')
        item['source_theorems'][-3:]=reader['source_cards']
        assert item['source_theorems'][:-3]==next(x for x in before['readings'] if x['slug']=='online-ogd')['source_theorems']
        ap=RUN/'integration-proposal-snapshots-20261011-v5'/Path(row['after_snapshot']).name
        write(ap,obj);row['after_snapshot']=ap.as_posix();row['after_sha256']=sha(ap)
manifest=load(RUN/'prospective-contribution-20261011-v4.json')
manifest['verification']['site_check']+=' Renderer boundary: folded exact statement, explanatory formula proof, full Lean BODY through source link; no new folded proof-BODY renderer claim.'
write(RUN/'prospective-contribution-20261011-v5.json',manifest)
plan.update(prospective_manifest=rows([RUN/'prospective-contribution-20261011-v5.json']),reader_proposal=rows([RUN/'reader-integration-proposal-20261011-v5.json']),supersedes=rows([RUN/'exact-integration-proposal-20261011-v4.json']),changes_from_v4='Three NEW source-card guarantee strings accurately distinguish folded exact statement, explanatory formula proof, full Lean BODY source link; no renderer modification. Historical source-card objects unchanged.')
write(RUN/'exact-integration-proposal-20261011-v5.json',plan)
sys.path.insert(0,str(ROOT))
from tools.check_contributor_contract import validate_contract
_,errors=validate_contract(RUN/'prospective-contribution-20261011-v5.json')
write(RUN/'prospective-contribution-schema-check-20261011-v5.json',dict(manifest=rows([RUN/'prospective-contribution-20261011-v5.json']),errors=errors))
assert not errors,errors
print('v5 plan SHA '+sha(RUN/'exact-integration-proposal-20261011-v5.json'))
