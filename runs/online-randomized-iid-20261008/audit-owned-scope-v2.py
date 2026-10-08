from common_integrated_v2 import *

fixed_integrated()
globals=['MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl']
singles=set(globals+['BanditRLProof.lean','Tests.lean',PUBLIC.as_posix(),CANARY.as_posix(),MANIFEST.as_posix(),
    'website/content/readings.json','website/content/highlights.json','website/content/chapters.json'])
singles.update(p.as_posix() for p in OWN_METADATA)
index_names=['bandit_paper_cards.json','bandit_scenario_cards.json','bandit_textbook_cards.json',
    'proof_weapon_cards.json','local_leaf_cards.json','local_lean_declarations.json']
singles.update('research-wiki/retrieval-index/'+n for n in index_names)
prefixes=[RUN.relative_to(ROOT).as_posix()+'/',CONTRACT.as_posix()+'/']
paths=sorted({line[3:] for line in subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').splitlines()})
for p in paths: assert p in singles or any(p.startswith(x) for x in prefixes),'Unowned path: '+p
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
assert subprocess.check_output(['git','merge-base','HEAD',BASE],encoding='utf8').strip()==BASE
bindings=[]
for p in globals:
    baseline=(RUN/'snapshots'/(p.replace('/','--')+'.raw')).read_bytes()
    current=Path(p).read_bytes()
    assert current.startswith(baseline),p
    addition=current[len(baseline):]
    if p.endswith('.jsonl'):
        for row in [json.loads(line) for line in addition.decode('utf8').splitlines() if line.strip()]:
            assert row.get('task',row.get('session_id'))==TASK,(p,row)
    else:
        for line in addition.decode('utf8').splitlines():
            if not line.strip(): continue
            assert ('`tasks/'+TASK+'.md`' in line and '`bandit.py new-task`' in line) or (
                '`proof-blueprints/'+TASK+'.md`' in line and '`bandit.py blueprint-refresh`' in line) or (
                '`bandit.py reference-index`' in line and ('`research-wiki/retrieval-index/' in line or '`runs/'+RUN.name+'/' in line)),line
    git_old=subprocess.check_output(['git','show',BASE+':'+p])
    bindings.append(dict(path=p,working_original_sha256=hashlib.sha256(baseline).hexdigest(),
        working_original_bytes=len(baseline),current_working_sha256=sha(p),working_append_sha256=hashlib.sha256(addition).hexdigest(),
        base_git_original_sha256=hashlib.sha256(git_old).hexdigest(),base_git_original_bytes=len(git_old),
        representations_are_separate=True,historical_prefix_preserved=True,owned_append_only=True))
for filename in index_names[:4]:
    p=Path('research-wiki/retrieval-index')/filename
    before=json.loads(subprocess.check_output(['git','show',BASE+':'+p.as_posix()]))
    assert before['cards']==load(p)['cards'],p
write(RUN/('owned-scope-'+sys.argv[1]+'.json'),dict(paths=paths,global_prefix_bindings=bindings,
    exact_stacked_base=BASE,canonical_other_worktrees_private_untouched=True,worktree_retained=True,
    chapter_complete=False,goal_complete=False))
print('Exact own scope:',len(paths),'paths; historical raw/Git global prefixes remain separately preserved.')
