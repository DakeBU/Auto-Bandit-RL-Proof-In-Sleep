"""Construction recipe: requires a separately hashed root imported-only lease."""
from pathlib import Path
import argparse, copy, hashlib, json, subprocess, sys
if not __debug__:
    raise RuntimeError('Optimized Python forbidden')
P=Path(__file__).resolve().parent
R=P.parent.parent
def bind(p):
    p=Path(p).resolve();h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return dict(path=str(p),bytes=p.stat().st_size,sha256=h.hexdigest())
def put(name,value):
    raw=value if isinstance(value,bytes) else (json.dumps(value,indent=2)+'\n').encode()
    with (P/name).open('xb') as f:f.write(raw)
def git(*args):return subprocess.check_output(['git','-c','core.longpaths=true',*args],cwd=R).decode().strip()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--release',required=True);ap.add_argument('--release-sha256',required=True);a=ap.parse_args()
    release=Path(a.release).resolve();assert release.is_relative_to(R/'tmp')
    assert bind(release)['sha256']==a.release_sha256
    auth=json.loads(release.read_text())
    assert auth['scope']=='IMPORTED_ONLY_REUSE_EXACT_PASSED_V3_HEADER_BODY'
    assert auth['Lean_resources_released'] is True and auth['attainment_canary_Lean_authorized'] is True
    assert auth['independent_tool_review_accepted'] is True
    assert bind(auth['independent_tool_review']['path'])==auth['independent_tool_review']
    root_return=R/'tmp/online-support-resume-20261012/attainment-canary-v3-resource-return-v2.json'
    assert bind(root_return)['sha256']=='af57721df0dad004827b5e9623a003536cf9135f961c0a16b5ebe33bd895427f'
    assert auth['prior_resource_return']==bind(root_return)
    names=['prepare-import-v4.py','capture-template-import-v4.py','ImportedAudit-construction-v2.lean','import-lineage-fixed-v4.json']
    assert auth['recipe']=={n:bind(P/n) for n in names}
    assert bind(P/'capture-template-import-v4.py')['sha256']=='fccb520d6e04b3d9b8748153e4aa827ddfd949f4ad68106fc452cd2e7cdd11b5'
    assert bind(P/'import-lineage-fixed-v4.json')['sha256']=='6ce6e874ab23bd21d17b32d21b365ee950bcde7080712350f063bee0aa303d36'
    assert sys.version_info[:3]==(3,12,14) and bind(sys.executable)['sha256']=='31073dad142bc7f3374e3122aa668270052c9ad37d0aaab803ae73f184c3a43b'
    assert dict(head=git('rev-parse','HEAD'),branch=git('branch','--show-current'),status=git('status','--porcelain','--untracked-files=all'))==dict(head=auth['expected_head'],branch=auth['expected_branch'],status='')
    history=json.loads((P/'import-lineage-fixed-v4.json').read_text());assert auth['history']==history
    for row in history.values():assert bind(row['path'])==row
    oldpins=json.loads(Path(history['pins']['path']).read_text());pins=copy.deepcopy(oldpins)
    hr=json.loads(Path(history['header']['path']).read_text());br=json.loads(Path(history['body']['path']).read_text())
    for stage,rec in [('header',hr),('body',br)]:
        assert rec['stage']==stage and rec['actual_exit']==0 and rec['integrity_pass'] is True
        assert rec['before_RAW']==rec['after_RAW'] and rec['pre_git']==rec['post_git']==dict(head=auth['expected_head'],branch=auth['expected_branch'],status='')
    prior_manifest=json.loads(Path(history['manifest']['path']).read_text())
    assert prior_manifest['receipt']==history['body'] and prior_manifest['candidate']==history['candidate']
    assert prior_manifest['probe']==history['probe_v1'] and prior_manifest['inputs']==[history['probe_v1']]
    old=Path(history['probe_v1']['path']).read_bytes();new=Path(history['probe_v2']['path']).read_bytes()
    assert old.count(b'.natLit?')==2 and old.replace(b'.natLit?',b'.rawNatLit?')==new
    names=['capture-import-v4.py','capture-pins-import-v4.json','import-input-manifest-v2.json']
    assert all(not (P/n).exists() for n in names)
    capture=(P/'capture-template-import-v4.py').read_bytes();put('capture-import-v4.py',capture)
    pins.update(release=bind(release),capture=bind(P/'capture-import-v4.py'),imported_probe=history['probe_v2'],history=history)
    mi=copy.deepcopy(prior_manifest);mi.update(probe=history['probe_v2'],inputs=[history['probe_v2']])
    put('import-input-manifest-v2.json',mi);put('capture-pins-import-v4.json',pins)
    print(json.dumps(dict(status='PREPARED_IMPORTED_ONLY_NOT_EXECUTED',pins=bind(P/'capture-pins-import-v4.json'),manifest=bind(P/'import-input-manifest-v2.json'))))
if __name__=='__main__':main()
