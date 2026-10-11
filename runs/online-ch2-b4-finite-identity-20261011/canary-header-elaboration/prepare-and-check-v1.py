from pathlib import Path
import hashlib,json,subprocess,datetime,os
root=Path('E:/ABRL/worktrees/research-online-book');out=root/'tmp/online-ch2-b4-finite-identity-canary-header-elaboration-20261011';out.mkdir(exist_ok=True)
core=root/'BanditRLProof/OnlineCumulativePotential.lean'
compiled=root/'tmp/online-ch2-b4-finite-identity-core-20261011/compiled'
olean=compiled/'BanditRLProof/OnlineCumulativePotential.olean'
proposal=root/'tmp/online-ch2-b4-finite-identity-canary-proposal-20261011'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(n,s):
 b=s.encode('utf-8') if isinstance(s,str) else s
 with (out/n).open('xb') as f:f.write(b)
def dump(n,obj):put(n,json.dumps(obj,indent=2)+'\n')
inputs=[('one-round','finite_identity_one_round_positive_gap','7d10ab86d93f97a5ac03db64ce96b8759a0a64d7bd440fa5bfbbe666717be75e'),('two-round','finite_identity_two_round_terminal_splice','718a2eb714597c34033cc4d35af06b00b3718768cd60799800c6e487c777af64')]
assert sha(core)=='61c811c0b1f941ec22ac41f64e555a0e4d4d8dc32b8145ea53808dbdc0fc17da'
paths=[core,olean,root/'lean-toolchain',root/'lakefile.lean',root/'lake-manifest.json']+[proposal/('neutral-'+tag+'-complete-header-v1.txt') for tag,name,h in inputs]
def context():
 return dict(UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),HEAD=subprocess.check_output(['git','rev-parse','HEAD'],cwd=str(root)).decode().strip(),branch=subprocess.check_output(['git','branch','--show-current'],cwd=str(root)).decode().strip(),git_status=subprocess.check_output(['git','status','--short'],cwd=str(root)).decode(),files={p.relative_to(root).as_posix():sha(p) for p in paths},mathlib_commit=subprocess.check_output(['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],cwd=str(root)).decode().strip())
before=context();assert before['HEAD']=='40c2f30f7cee38c9d2f716ffdac18a459a5af25a';assert before['git_status'].strip()=='?? BanditRLProof/OnlineCumulativePotential.lean';dump('context-before-v1.json',before)
def run(n,argv,env=None):
 start=datetime.datetime.now(datetime.timezone.utc).isoformat();p=subprocess.run(argv,cwd=str(root),env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 put(n+'.stdout.raw',p.stdout);put(n+'.stderr.raw',p.stderr)
 dump(n+'.json',dict(argv=argv,cwd=str(root),startUTC=start,endUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),actual_exit=p.returncode,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stderr_sha256=hashlib.sha256(p.stderr).hexdigest(),LEAN_PATH=None if env is None else env.get('LEAN_PATH'),core_source_sha256=sha(core),core_olean_sha256=sha(olean)))
 print(n,p.returncode);return p
p=run('capture-lake-path-v1',['lake','env','python','-c','import os; print(os.environ.get("LEAN_PATH", ""))']);assert p.returncode==0
version=run('lean-version-v1',['lake','env','lean','--version']);assert version.returncode==0
env=os.environ.copy();env['LEAN_PATH']=str(compiled)+os.pathsep+p.stdout.decode().strip()
results=[]
for tag,name,h in inputs:
 src=proposal/('neutral-'+tag+'-complete-header-v1.txt');assert sha(src)==h
 raw=src.read_bytes();assert b'\r' not in raw
 old=('theorem '+name+' :').encode();new=('def '+name+'_typeprobe : Prop :=').encode()
 assert raw.count(old)==1
 commands=('\n#check '+name+'_typeprobe\n#print '+name+'_typeprobe\n').encode()
 end=b'\nend BanditRL.OnlineCumulativePotentialCanary\n';assert raw.count(end)==1
 probe=raw.replace(old,new,1).replace(end,commands+end,1)
 undo=probe.replace(commands+end,end,1).replace(new,old,1);assert undo==raw
 file=tag+'-typeprobe.lean';put(file,probe)
 result=run(tag+'-elaboration-v1',['lean',str((out/file).relative_to(root)).replace('\\','/')],env)
 results.append(dict(case=tag,original_header_sha256=h,probe_sha256=sha(out/file),reverse_conversion_exact=True,actual_exit=result.returncode))
after=context();dump('context-after-v1.json',after)
assert all(before[k]==after[k] for k in ['HEAD','branch','git_status','files','mathlib_commit'])
dump('canary-header-elaboration-report-v1.json',dict(status='HEADER TYPE ELABORATION READY' if all(r['actual_exit']==0 for r in results) else 'HEADER ELABORATION FAILED',UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),results=results,context_stable=True,HEAD=after['HEAD'],git_status=after['git_status'],actual_imported_core_source_sha256=sha(core),actual_imported_core_olean_sha256=sha(olean),LEAN_PATH=env['LEAN_PATH'],scope='Only Prop-valued type definitions and check/print commands. No proof BODY, production/Test/root/DOC/RUN/site changes. No canary freeze, clean pre-canary context certification, or Test BODY authorization.',awaiting=['production BODY acceptance','parent canary freeze','later clean committed context','independent review','explicit Test authorization']))
excluded={'artifact-manifest-v1.json','artifact-manifest-verification-v1.json'}
rows=[dict(path=p.relative_to(out).as_posix(),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(out.rglob('*')) if p.is_file() and p.name not in excluded]
dump('artifact-manifest-v1.json',dict(excluded=sorted(excluded),rows=rows))
for r in rows:assert sha(out/r['path'])==r['sha256'] and (out/r['path']).stat().st_size==r['bytes']
assert {p.relative_to(out).as_posix() for p in out.rglob('*') if p.is_file() and p.name not in excluded}=={r['path'] for r in rows}
dump('artifact-manifest-verification-v1.json',dict(manifest_sha256=sha(out/'artifact-manifest-v1.json'),rows=len(rows),all_rows_verified=True,exact_file_set_matches=True,excluded=sorted(excluded)))
for n in ['canary-header-elaboration-report-v1.json','artifact-manifest-v1.json']:print(n,sha(out/n))