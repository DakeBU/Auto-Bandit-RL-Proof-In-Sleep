from common_canary_v1 import *
import gzip
canary_contract_fixed()
scope=load(RUN/'body-future-integration-scope-v1.json')
paths=list(scope['exact_root_additions'])+scope['reader_files']+[
    'research-wiki/retrieval-index/'+n+'.json' for n in ['bandit_paper_cards','bandit_scenario_cards',
        'bandit_textbook_cards','proof_weapon_cards','local_leaf_cards','local_lean_declarations']]
baseline=[]
for rel in paths:
    p=ROOT/rel;raw=p.read_bytes();committed=subprocess.check_output(['git','show',BASE+':'+rel])
    assert raw.replace(b'\r\n',b'\n')==committed.replace(b'\r\n',b'\n'),rel
    snap=RUN/'integration-baseline'/(rel.replace('/','--')+'.raw');write(snap,raw)
    baseline.append(dict(path=rel,sha256=sha(p),snapshot=snap.as_posix()))
write(RUN/'integration-baseline-v1.json',dict(rows=baseline,old_production_registry_nodes=10964,
    before_BODY_frozen=True,root_reader_edits_performed=False))
oldregistry=ROOT/'tmp/online-ftl-limit-site-v1/books/registry.json';old=load(oldregistry)
assert len(old['nodes'])==10964 and old['lean_verified']
write(RUN/'registry-baseline-v1.json.gz',gzip.compress(oldregistry.read_bytes(),mtime=0))
write(RUN/'registry-baseline-bindings-v1.json',dict(path=oldregistry.as_posix(),raw_sha256=sha(oldregistry),
    gzip_sha256=sha(RUN/'registry-baseline-v1.json.gz'),old_complete_node_records=10964,
    identity=old['identity'],source_commit=old['source_commit'],cached_old_site_not_fresh_current_build=True))
print('Exact old root/readers/global indexes and10964 complete shared registry frozen before BODY; no integration edits.',flush=True)
