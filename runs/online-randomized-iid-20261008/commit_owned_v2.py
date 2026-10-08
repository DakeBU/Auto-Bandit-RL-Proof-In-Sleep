from common_integrated_v2 import *


def current_owned_paths():
    singles={'MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl',
        MANIFEST.as_posix(),PUBLIC.as_posix(),CANARY.as_posix(),'BanditRLProof.lean','Tests.lean',
        'website/content/readings.json','website/content/highlights.json','website/content/chapters.json'}
    singles.update(p.as_posix() for p in OWN_METADATA)
    singles.update('research-wiki/retrieval-index/'+n for n in ['bandit_paper_cards.json','bandit_scenario_cards.json',
        'bandit_textbook_cards.json','proof_weapon_cards.json','local_leaf_cards.json','local_lean_declarations.json'])
    paths=[line[3:] for line in subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').splitlines()]
    for p in paths:
        assert p in singles or p.startswith(RUN.relative_to(ROOT).as_posix()+'/') or p.startswith(CONTRACT.as_posix()+'/'),p
    return paths


def stage_owned():
    paths=current_owned_paths()
    globals={'MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl'}
    for group,raw in [([p for p in paths if p not in globals],True),([p for p in paths if p in globals],False)]:
        for start in range(0,len(group),48):
            command=['git']+(['-c','core.autocrlf=false'] if raw else [])+['add','--']+group[start:start+48]
            child=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            assert child.returncode==0,child.stdout.decode('utf8',errors='replace')
        for p in group:
            content=subprocess.check_output(['git','show',':'+p])
            if raw: assert content==Path(p).read_bytes(),p
            else: assert content.startswith(subprocess.check_output(['git','show',BASE+':'+p])),p
    return paths


def commit_owned(message):
    paths=stage_owned()
    assert paths
    child=subprocess.run(['git','commit','-m',message],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    sys.stdout.write('\n'.join(child.stdout.decode('utf8',errors='replace').splitlines()[:4])+'\n')
    assert child.returncode==0
    assert not current_owned_paths()


if __name__=='__main__':
    fixed_integrated()
    commit_owned(sys.argv[1])
