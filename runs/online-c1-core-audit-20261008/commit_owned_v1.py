from common_integrated_v1 import *

APPEND_METADATA=[Path(d)/(TASK+'.md') for d in ['tasks','proof-obligations','proof-blueprints','conversion-windows']]
RETRIEVAL_FILES=[Path('research-wiki/retrieval-index')/(n+'.json') for n in
    ['bandit_paper_cards','bandit_scenario_cards','bandit_textbook_cards','proof_weapon_cards','local_leaf_cards','local_lean_declarations']]
JOURNALS={'MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl'}

def current_owned_paths():
    singles=JOURNALS | {MANIFEST.as_posix(),CANARY.as_posix(),'Tests.lean'}
    singles.update(p.as_posix() for p in MODULES+READERS+RETRIEVAL_FILES+APPEND_METADATA)
    singles.add('research-wiki/retrieval-index/'+TASK+'.md')
    paths=[s[3:] for s in subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').splitlines()]
    for p in paths:
        assert p in singles or p.startswith(RUN.relative_to(ROOT).as_posix()+'/') or p.startswith(CONTRACT.as_posix()+'/'),p
    return paths

def stage_owned():
    fixed_integrated()
    paths=current_owned_paths()
    # Preserve review-bound raw logs/snapshots; preserve LF Git production bodies separately.
    portable={p.as_posix() for p in MODULES}|{'Tests.lean'}|JOURNALS
    for group,raw in [([p for p in paths if p not in portable],True),([p for p in paths if p in portable],False)]:
        for start in range(0,len(group),40):
            child=subprocess.run(['git']+(['-c','core.autocrlf=false'] if raw else [])+
                ['add','--']+group[start:start+40],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            assert child.returncode==0,child.stdout.decode('utf8',errors='replace')
        for p in group:
            blob=subprocess.check_output(['git','show',':'+p]);live=Path(p).read_bytes()
            if raw: assert blob==live,p
            else:
                assert blob==live.replace(b'\r\n',b'\n'),p
                base=subprocess.check_output(['git','show',BASE+':'+p])
                if p in JOURNALS: assert blob.startswith(base),p
                elif p in PLAN:
                    comment=PLAN[p]['comment_utf8'].encode('utf8')
                    assert blob.count(comment)==1 and blob.replace(comment,b'',1)==base,p
                elif p=='Tests.lean': assert blob==base+b'\nimport Tests.OnlineLearningCoreAuditCanary\n'
    return paths

def commit_owned(message):
    paths=stage_owned();assert paths
    child=subprocess.run(['git','commit','-m',message],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    print('\n'.join(child.stdout.decode('utf8',errors='replace').splitlines()[:4]),flush=True)
    assert child.returncode==0
    assert not current_owned_paths()
