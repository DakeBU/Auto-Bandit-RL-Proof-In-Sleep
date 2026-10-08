from common_integrated_v2 import *

def current_owned_paths():
    singles={'MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl',MANIFEST.as_posix(),
        PUBLIC.as_posix(),CANARY.as_posix(),'BanditRLProof.lean','Tests.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json'}
    singles.update(folder+'/'+TASK+'.md' for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index'])
    paths=[line[3:] for line in subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').splitlines()]
    for p in paths: assert p in singles or p.startswith(RUN.relative_to(ROOT).as_posix()+'/') or p.startswith(CONTRACT.as_posix()+'/'),p
    return paths

def commit_owned(message):
    paths=current_owned_paths()
    assert paths
    globals={'MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl'}
    raw=[p for p in paths if p not in globals]
    for start in range(0,len(raw),48):
        child=subprocess.run(['git','-c','core.autocrlf=false','add','--']+raw[start:start+48],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        assert child.returncode==0,child.stdout.decode('utf8',errors='replace')
    changed=[p for p in paths if p in globals]
    if changed:
        child=subprocess.run(['git','add','--']+changed,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        assert child.returncode==0
    for p in raw: assert subprocess.check_output(['git','show',':'+p])==Path(p).read_bytes(),p
    for p in changed: assert subprocess.check_output(['git','show',':'+p]).startswith(subprocess.check_output(['git','show',BASE+':'+p])),p
    child=subprocess.run(['git','commit','-m',message],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    sys.stdout.write('\n'.join(child.stdout.decode('utf8',errors='replace').splitlines()[:4])+'\n')
    assert child.returncode==0
    assert not current_owned_paths()

if __name__=='__main__':
    fixed_integrated()
    commit_owned(sys.argv[1])
