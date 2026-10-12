"""Construction only: consumes a separately reviewed, parent-sealed actual discovery.
Never launches Lean. V1/V2 are preserved and remain unexecuted.
"""
from pathlib import Path
import argparse, ast, hashlib, json, os, subprocess, sys
if not __debug__: raise RuntimeError('Optimized Python is forbidden')
P=Path(__file__).resolve().parent; R=P.parent.parent
D=R/'tmp/online-b4-next-weierstrass-canary-body-20261012'
F=R/'tmp/online-b4-next-attainment-header-freeze-20261012'
A=R/'tmp/online-b4-next-weierstrass-body-20261012'
def need(x,m):
 if not x: raise RuntimeError(m)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def bind(p):
 p=Path(p).resolve();return dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p))
def read(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sealed(row):
 p=Path(row['path']).resolve();need(bind(p)==row,'Sealed file changed: '+str(p));return p
def key(p):return os.path.normcase(str(Path(p).resolve()))
def unique(rows):
 result={key(x['path']):x for x in rows};need(len(result)==len(rows),'Duplicate normalized paths');return result
def put(name,data):
 with (P/name).open('xb') as f:f.write(data)
def enc(x):return (json.dumps(x,indent=2)+'\n').encode()
def git(*a):return subprocess.check_output(['git','-c','core.longpaths=true',*a],cwd=R).decode().strip()
def state():return dict(head=git('rev-parse','HEAD'),branch=git('branch','--show-current'),status=git('status','--porcelain','--untracked-files=all'))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--release',required=True);ap.add_argument('--release-sha256',required=True);a=ap.parse_args()
 release=Path(a.release).resolve();need(release.is_relative_to(R/'tmp'),'Release must be ignored local authority')
 need(sha(release)==a.release_sha256,'Parent release hash differs');auth=read(release)
 need(auth['Lean_resources_released'] is True and auth['Theorem6_9_Lean_execution_authorized'] is True,'No execution authority')
 need(auth['prepare_recipe']==bind(__file__),'Release must pin this exact preparation')
 need(sys.version_info[:3]==(3,12,14) and sha(sys.executable)=='31073dad142bc7f3374e3122aa668270052c9ad37d0aaab803ae73f184c3a43b','Exact Python required')
 expected=dict(head=auth['expected_head'],branch=auth['expected_branch'],status='');need(state()==expected,'Wrong clean Git state')
 baseline=D/'capture-pins-v2.json';historical=D/'capture-v2.py';template=P/'capture-template-v3.py'
 for path,digest in [(baseline,'26d908ba565b26d36d13137380be87fe8dafe88a17acaad4c950c4e2056b22ca'),(historical,'c8bdd8c02e2c86e7c0f2db046b2a372c4c6b23f5f1ef62cf7408e883be98679d'),(template,'16969d4b4e0a78c4f1ffb21f8e567e3503a7b3a6ae29705c6fe542c5dc837264')]:need(sha(path)==digest,'Historical/template hash differs')
 pins=read(baseline);cap=template.read_bytes();ast.parse(cap)
 need(bind(sys.executable)==pins['python'],'Python binding differs')
 # These bindings are supplied by the parent after independent actual-discovery review.
 # Caller-supplied receipt hashes alone are not authority.
 seal=auth['reviewed_actual_discovery'];need(seal['accepted'] is True,'Discovery not independently accepted')
 paths={k:sealed(seal[k]) for k in ['review','recipe','receipt','manifest','potential_inventory','capture_authority']}
 need(sha(paths['recipe'])=='a3dca4e9492260566bd1bdb6157f8fe333c7d08412b40116be33e5762eed4d7d','Reviewed discovery implementation differs')
 dr=read(paths['receipt']);cl=read(paths['manifest']);inv=read(paths['potential_inventory']);da=read(paths['capture_authority'])
 need(dr['actual_exit']==0 and dr['integrity_pass'] is True,'Discovery did not pass')
 need(dr['authority']==bind(paths['capture_authority']),'Capture authority mismatch')
 need(da['ready_for_execution'] is True and da['parent_resource_release'] is True and da['exclusive_input_ownership'] is True and da['mode']=='capture','Wrong discovery authority')
 recipe={str(paths['recipe']):sha(paths['recipe'])}
 need(da['recipe']==dr['recipe']==inv['recipe']==recipe,'Discovery recipe mismatch')
 need(da['inventory']==cl['full_potential_inventory']==bind(paths['potential_inventory']),'Potential inventory mismatch')
 need(da['expected_git']==dr['pre_git']==dr['post_git']==expected,'Discovery Git mismatch')
 probe=P/'HeaderImportDiscovery-v2.lean';need(sha(probe)=='0296043aee3f9616aa26811bd3ae967a5df47e84232a7834ef4675895e071bef','Probe differs')
 roots=[str(A.resolve())]+[str(Path(x).resolve()) for x in pins['ordered_search_roots']]
 need(inv['ordered_roots']==roots and len(set(map(key,roots)))==len(roots),'Search roots differ')
 need(dr['argv']==[pins['compiler']['path'],str(probe)] and key(dr['cwd'])==key(R),'Wrong discovery command/cwd')
 need(dr['env_overrides']==dict(LEAN_NUM_THREADS='2',LEAN_PATH=os.pathsep.join(roots)),'Wrong discovery environment')
 need(cl['origin_probe']==inv['probe']==bind(probe) and dr['discovery_manifest']==bind(paths['manifest']),'Discovery outputs differ')
 need(cl['origin_output']==bind(P/'header-import-origins-v2.json'),'Origin stream differs')
 need(dr['before_RAW']==dr['after_RAW']==inv['inputs'],'Complete discovery input map differs')
 before=unique(inv['inputs']);need(dr['companion_membership_before']==dr['companion_membership_after']==inv['catalogue'],'Catalogue drift')
 runtime=read(sealed(pins['runtime_inventory']));need(len(runtime['files'])==19 and dr['runtime_before']==dr['runtime_after']==inv['runtime']==runtime['files'],'Runtime map differs')
 observed=read(P/'header-import-origins-v2.json');need(len(observed)==len({x['module'] for x in observed}),'Duplicate actual modules')
 catalogue={}
 for x in inv['catalogue']:catalogue.setdefault(x['module'],[]).append(x)
 actual=[];required=set()
 for x in observed:
  choices=catalogue.get(x['module'],[]);need(len(choices)==1,'Missing/shadowed actual module')
  row=choices[0];need(key(row['olean'])==key(x['olean']),'Resolved module differs')
  if key(row['root'])==key(A):need(row['module']=='WeierstrassExtendedCandidate','Unapproved scratch parent')
  actual.append(row);required.update(map(key,[row['source'],*row['companions']]))
 need(cl['origins']==actual,'Manifest origin list differs')
 need({'BanditRLProof.OnlineStrongConvexSourceSubgradient','BanditRLProof.OnlineStrongConvexMinimum','WeierstrassExtendedCandidate','Mathlib.Analysis.Normed.Module.FiniteDimension'}<={x['module'] for x in actual},'Missing direct frozen import')
 policy=[pins[k] for k in ['python','compiler','operative_search_pins','runtime_inventory']]+pins['parents']+pins['project']
 required.update(key(x['path']) for x in policy);required.update(map(key,inv['runtime']));required.update(map(key,[baseline,probe,paths['recipe'],F/'Theorem6.9-frozen-context-and-header-v1.txt',F/'Theorem6.9-local-header-freeze-v1.json']))
 closure=unique(cl['inputs']);need(set(closure)==required,'Actual closure incomplete or substituted')
 for k,row in closure.items():need(before[k]==row and bind(row['path'])==row,'Current actual input differs')
 # Exact whole frozen header, with one separately authorized import transport.
 frozenpath=F/'Theorem6.9-frozen-context-and-header-v1.txt';canonical=frozenpath.read_bytes()
 need(sha(frozenpath)=='58decad0d7dbd318b0c21949d2f699893df9059cb70dfd3fcee020a8ee12b1a5','Frozen header differs')
 old=b'import BanditRLProof.OnlineWeierstrassExtended';need(canonical.count(old)==1,'Import transport count')
 frozen=canonical.replace(old,b'import WeierstrassExtendedCandidate')
 header=frozen.decode();old='theorem stronglyConvex_existsUnique_minimizer {E : Type*}';need(header.count(old)==1,'Header declaration count')
 header=header.replace(old,'#check ∀ {E : Type*}');need(header.count(' :\n    ∃! p')==1,'Header result separator count')
 header=header.replace(' :\n    ∃! p',',\n    ∃! p')+'\nend BanditRL.OnlineConvex\n'
 need(state()==expected,'Git drift during preparation')
 # No artifacts are written before the entire discovery boundary is authenticated.
 names=['scratch-frozen-header-v3.txt','HeaderElaboration-v3.lean','closure-manifest-v1.json','capture-v3.py','capture-pins-v3.json']
 need(all(not (P/n).exists() for n in names),'Exclusive preparation output already exists')
 put(names[0],frozen);put(names[1],header.encode());put(names[2],enc(cl));put(names[3],cap)
 pins.update(release=bind(release),freeze=bind(F/'Theorem6.9-local-header-freeze-v1.json'),frozen_header=bind(P/names[0]),canonical_header=bind(frozenpath),header_probe=bind(P/names[1]),capture=bind(P/names[3]),closure_manifest_sha256=sha(P/names[2]),scratch_parent_roots=[str(A)],reviewed_actual_discovery=seal,prepare_recipe=bind(__file__))
 pins['project']=[bind(R/n) for n in ['lean-toolchain','lakefile.lean','lake-manifest.json','BanditRLProof.lean','Tests.lean']]
 put(names[4],enc(pins));print(json.dumps(dict(status='PREPARED_NOT_EXECUTED',pins=bind(P/names[4]))))
if __name__=='__main__':main()
