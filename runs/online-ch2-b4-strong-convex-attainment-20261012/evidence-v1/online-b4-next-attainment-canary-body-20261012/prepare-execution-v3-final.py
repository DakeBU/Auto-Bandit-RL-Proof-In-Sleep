"""Prospective adapter only. No scan or execution until separate parent canary lease."""
from pathlib import Path
import argparse,json,hashlib,subprocess,sys,os
if not __debug__:raise RuntimeError('Optimized Python forbidden')
P=Path(__file__).resolve().parent;R=P.parent.parent
C=R/'tmp/online-b4-next-attainment-body-20261012'
F=R/'tmp/online-b4-next-attainment-canary-freeze-20261012'
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def bind(p):
 p=Path(p).resolve();return dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p))
def read(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def key(p):return os.path.normcase(str(Path(p).resolve()))
def pinned(p,h):assert sha(p)==h;return read(p)
def put(n,data):
 with (P/n).open('xb') as f:f.write(data)
def enc(x):return (json.dumps(x,indent=2)+'\n').encode()
def git(*a):return subprocess.check_output(['git','-c','core.longpaths=true',*a],cwd=R).decode().strip()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--release',required=True);ap.add_argument('--release-sha256',required=True);a=ap.parse_args()
 release=Path(a.release).resolve();assert release.is_relative_to(R/'tmp')
 auth=pinned(release,a.release_sha256)
 assert auth['Lean_resources_released'] is True and auth['attainment_canary_Lean_authorized'] is True
 assert auth['core_SOURCE_accepted'] is True
 assert bind(auth['core_source_review']['path'])==auth['core_source_review']
 assert auth['recipe']=={n:bind(P/n) for n in ['prepare-execution-v3-final.py','capture-template-v3-final.py','ImportedAudit-construction-v1.lean','HeaderElaboration-v1.lean','scratch-frozen-whole-v1.txt']}
 assert sys.version_info[:3]==(3,12,14) and sha(sys.executable)=='31073dad142bc7f3374e3122aa668270052c9ad37d0aaab803ae73f184c3a43b'
 expected=dict(head=auth['expected_head'],branch=auth['expected_branch'],status='')
 actual=dict(head=git('rev-parse','HEAD'),branch=git('branch','--show-current'),status=git('status','--porcelain','--untracked-files=all'));assert actual==expected
 report=pinned(C/'compiled-core-report-v1.json','3131ed9ef7bfbe355ae85708f6f80ea02e0c9ca1738a57701d3353d81f2253c1')
 pins=pinned(C/'capture-pins-v4.json','a2cd0df7046c42df52f4746bbb0ce4adf71e9c378290fbe5c5dc1400178153e7')
 assert auth['accepted_core_report']==bind(C/'compiled-core-report-v1.json')
 for k in ['candidate','olean','closure_manifest','all_module_origins','audit','probe','import_input_manifest']:
  assert bind(report[k]['path'])==report[k]
 for attempt in ['focused-v3','imported-v1']:
  row=next(x for x in report['receipts'] if x['attempt']==attempt);assert bind(row['receipt']['path'])==row['receipt'];rec=read(row['receipt']['path'])
  assert rec['actual_exit']==0 and rec['integrity_pass'] is True and rec['pre_git']==rec['post_git']==expected
  assert rec['before_RAW']==rec['after_RAW'] and rec['runtime_before']==rec['runtime_after'] and len(rec['runtime_before'])==19
 cl=read(report['closure_manifest']['path']);observed=read(report['all_module_origins']['path'])
 assert len(observed)==len({x['module'] for x in observed})==5327
 known={x['module']:x for x in cl['origins']};assert len(known)==5326
 op=Path(report['olean']['path']);companions=sorted(op.parent.glob(op.stem+'.*'))
 assert {x.name for x in companions}=={'StrongConvexAttainmentCandidate.olean'},'New core companions require independently reviewed inventory successor'
 known['StrongConvexAttainmentCandidate']=dict(module='StrongConvexAttainmentCandidate',root=str(C),olean=str(op),source=report['candidate']['path'],companions=[str(op)])
 for row in observed:assert key(row['olean'])==key(known[row['module']]['olean'])
 origins=[known[x['module']] for x in observed]
 inputs={key(x['path']):x for x in cl['inputs']};assert len(inputs)==len(cl['inputs'])
 additional=[C/'compiled-core-report-v1.json',C/'capture-pins-v4.json',Path(report['candidate']['path']),op,Path(report['all_module_origins']['path']),Path(report['audit']['path']),Path(report['probe']['path'])]
 additional += [Path(x['receipt']['path']) for x in report['receipts'] if x['attempt'] in ['focused-v3','imported-v1']]
 additional += [Path(auth['core_source_review']['path'])]
 for path in additional:inputs[key(path)]=bind(path)
 for row in inputs.values():assert bind(row['path'])==row,'Current input changed'
 cl.update(origins=origins,inputs=list(inputs.values()),scope='Accepted actual core imported5327 origins and complete original closure plus authentic core source/olean/review/receipt evidence. No guessed source mapping or binary copy.')
 assert sha(F/'canonical-frozen-whole-v1.txt')=='2ad7eaec6f4192869c3f6a823d5ba1db140ee0317e7985e2ff53b592f968c91e'
 assert sha(F/'local-header-freeze-v1.json')=='7f807bf90399cb4cb1fdbc6d6bf21b05d509804414c4e3ad49026e5dbe0d8f51'
 assert (P/'scratch-frozen-whole-v1.txt').read_bytes().replace(b'import StrongConvexAttainmentCandidate',b'import BanditRLProof.OnlineStrongConvexAttainment')==(F/'canonical-frozen-whole-v1.txt').read_bytes()
 for n in ['closure-manifest-v3.json','capture-v3.py','capture-pins-v3.json']:assert not (P/n).exists()
 put('closure-manifest-v3.json',enc(cl))
 put('capture-v3.py',(P/'capture-template-v3-final.py').read_bytes())
 pins.update(release=bind(release),freeze=bind(F/'local-header-freeze-v1.json'),frozen_header=bind(P/'scratch-frozen-whole-v1.txt'),canonical_header=bind(F/'canonical-frozen-whole-v1.txt'),header_probe=bind(P/'HeaderElaboration-v1.lean'),capture=bind(P/'capture-v3.py'),closure_manifest_sha256=sha(P/'closure-manifest-v3.json'),scratch_parent_roots=[str(C)]+pins['scratch_parent_roots'])
 pins['parents'] += [bind(x) for x in additional]
 pins['imported_probe']=auth['recipe']['ImportedAudit-construction-v1.lean']
 assert pins['imported_probe']==bind(P/'ImportedAudit-construction-v1.lean')
 put('capture-pins-v3.json',enc(pins));print(json.dumps(dict(status='PREPARED_NOT_EXECUTED',pins=bind(P/'capture-pins-v3.json'))))
if __name__=='__main__':main()
