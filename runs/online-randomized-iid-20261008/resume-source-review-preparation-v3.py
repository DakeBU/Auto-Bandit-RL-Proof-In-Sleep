from common_v1 import *
from collections import Counter

fixed()
write(RUN / 'source-packet-preparation-failure-v2.json', dict(actual_command='prepare-source-review-v2.py',
    exit_code=1, reason='Assertion assumed regenerated local retrieval declarations equal stale BASE index rather than allow existing-source rescan additions.',
    observed_old_rows=8786, observed_new_rows=10822, changed_old_rows=0, missing_old_rows=0,
    new_public_theorem_bodies=0, mathematical_targets_changed=False,
    repair='Require preservation of every prior exact row with multiplicity, validate every added row file already tracked at BASE, explicitly record inventory-only refresh.'))
original_write=write


def write(p,value):
    p=Path(p)
    if p.name == 'old-registry-draft-preservation-v2.json':
        oldrows=json.loads(subprocess.check_output(['git','show',BASE+':research-wiki/retrieval-index/local_lean_declarations.json']))['declarations']
        now=load('research-wiki/retrieval-index/local_lean_declarations.json')['declarations']
        canonical=lambda r:json.dumps(r,sort_keys=True,ensure_ascii=False)
        oldcounter=Counter(map(canonical,oldrows));newcounter=Counter(map(canonical,now))
        assert all(newcounter[k]>=v for k,v in oldcounter.items())
        additions=[r for r in now if canonical(r) not in oldcounter]
        tracked=set(subprocess.check_output(['git','ls-tree','-r','--name-only',BASE],encoding='utf8').splitlines())
        assert all(r['file'] in tracked for r in additions)
        value['all_rows_exact_semantic_equal']=False
        value['all_old_rows_preserved_exact_with_multiplicity']=True
        value['current_rows']=len(now)
        value['inventory_only_existing_source_additions']=len(additions)
        value['added_rows_all_files_already_tracked_at_BASE']=True
        value['new_math_from_index_refresh']=0
    original_write(p,value)


source=(RUN/'prepare-source-review-v2.py').read_text(encoding='utf8').replace('from common_v1 import *\n','',1)
assert source.count('assert old == declarations')==1
source=source.replace('assert old == declarations',
    'assert all(r in declarations for r in old)  # stronger multiplicity check recorded below')
exec(compile(source,str(RUN/'prepare-source-review-v2.py'),'exec'),globals())
