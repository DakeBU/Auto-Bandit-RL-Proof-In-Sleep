from common_integrated_v2 import *

fixed_integrated()
assert load(RUN/'full-harness-v3-exit.json')['exit_code']==0
names=['bandit_paper_cards.json','bandit_scenario_cards.json','bandit_textbook_cards.json',
    'proof_weapon_cards.json','local_leaf_cards.json','local_lean_declarations.json']
before={}
for name in names:
    p=Path('research-wiki/retrieval-index')/name
    write(RUN/'snapshots'/('pre-body-registry-refresh--'+name+'.raw'),p.read_bytes())
    before[name]=load(p)
native('actual-body-reference-index-v2','reference-index')
canonical=lambda row:json.dumps(row,sort_keys=True,ensure_ascii=False)
bindings=[]
for name in names:
    p=Path('research-wiki/retrieval-index')/name
    key='declarations' if name=='local_lean_declarations.json' else 'cards'
    old=Counter(map(canonical,before[name][key]));now=Counter(map(canonical,load(p)[key]))
    assert all(now[k]>=v for k,v in old.items()),p
    bindings.append(dict(path=p.as_posix(),old_rows=sum(old.values()),current_rows=sum(now.values()),
        every_old_row_preserved_with_exact_multiplicity=True,new_rows=sum((now-old).values()),sha256=sha(p)))
declarations=load('research-wiki/retrieval-index/local_lean_declarations.json')['declarations']
for name in load(MANIFEST)['declarations']:
    assert any(r.get('full_name',r.get('name'))==name for r in declarations),name
write(RUN/'actual-body-shared-retrieval-preservation-v2.json',dict(bindings=bindings,
    own_new_public_declarations=8,original_stale_BASE_inventory_refresh_counts_not_math_progress=True,
    source_chapter1_items=16,required_proof_total=None,chapter_complete=False,goal_complete=False))
fixed_integrated()
print('Actual native shared reference index refresh preserves every prior row; all eight own public declarations are retrievable.')
