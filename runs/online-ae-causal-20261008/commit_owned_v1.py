from common_body_v1 import *

EXACT_OWNED={PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix(),
    'BanditRLProof.lean','Tests.lean','MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl',
    MANIFEST.relative_to(ROOT).as_posix()}
EXACT_OWNED.update(p.relative_to(ROOT).as_posix() for p in READERS)
EXACT_OWNED.update(d+'/'+TASK+'.md' for d in ['tasks','proof-obligations','proof-blueprints','conversion-windows'])
EXACT_OWNED.update('research-wiki/retrieval-index/'+p+'.json' for p in [
    'bandit_paper_cards','bandit_scenario_cards','bandit_textbook_cards','local_leaf_cards','local_lean_declarations','proof_weapon_cards'])
PREFIX_OWNED=[RUN.relative_to(ROOT).as_posix()+'/',CONTRACT.relative_to(ROOT).as_posix()+'/']

def owned(p):return p in EXACT_OWNED or any(p.startswith(x) for x in PREFIX_OWNED)

def stage_owned():
    changed=subprocess.check_output(['git','diff','HEAD','--name-only','-z']).decode('utf8').split('\0')
    untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard','-z']).decode('utf8').split('\0')
    paths=sorted(set(x for x in changed+untracked if x))
    assert all(owned(p) for p in paths),[p for p in paths if not owned(p)]
    for i in range(0,len(paths),60):subprocess.run(['git','add','--',*paths[i:i+60]],check=True,stdout=subprocess.DEVNULL,stderr=subprocess.PIPE)
    staged=subprocess.check_output(['git','diff','--cached','--name-only','-z']).decode('utf8').split('\0')
    assert all(owned(p) for p in staged if p)
    return paths

def commit_owned(message):
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    stage_owned()
    staged=subprocess.check_output(['git','diff','--cached','--name-only'],encoding='utf8').splitlines()
    assert staged
    subprocess.run(['git','commit','-m',message],check=True)
    assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
