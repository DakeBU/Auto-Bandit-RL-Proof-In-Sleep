from pathlib import Path
import hashlib,json,subprocess,datetime,os
root=Path('E:/ABRL/worktrees/research-online-book');out=root/'tmp/online-ch2-b4-finite-identity-canary-core-20261011';out.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(n,s):
 b=s.encode('utf-8') if isinstance(s,str) else s
 with (out/n).open('xb') as f:f.write(b)
def dump(n,obj):put(n,json.dumps(obj,indent=2)+'\n')
def run(n,argv,env=None):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat();p=subprocess.run(argv,cwd=str(root),env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 put(n+'.stdout.raw',p.stdout);put(n+'.stderr.raw',p.stderr);dump(n+'.json',dict(argv=argv,cwd=str(root),startUTC=t,endUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),actual_exit=p.returncode,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stderr_sha256=hashlib.sha256(p.stderr).hexdigest(),LEAN_PATH=None if env is None else env.get('LEAN_PATH')));print(n,p.returncode);return p
checks={'tmp/online-ch2-b4-finite-identity-canary-body-authorization-20261011/parent-authorization-v1.json':'dbe595b40df2df4753292d78f87439d6ddad37b4c6c7e7315b1e89a625e8c549','tmp/online-ch2-b4-finite-identity-precanary-v2-review-20261011/fresh-independent-precanary-review-v2.json':'37bd948cc6963e34b3218a791131b4078545bd3c2b1f946eaa9a1babc04a0336','docs/contracts/online-ch2-b4-finite-identity-v1/canary-freeze-receipt-v1.json':'7d69c7a32df454ab91324c7b2aeb120e6bc736847fc3c429695711e2678504e8','docs/contracts/online-ch2-b4-finite-identity-v1/precanary-preparation-addendum-v1.json':'8938af95be946da376e2c0906c9f53fee73bf207e8ec6a45d3600ac9ffb402b1','BanditRLProof/OnlineCumulativePotential.lean':'61c811c0b1f941ec22ac41f64e555a0e4d4d8dc32b8145ea53808dbdc0fc17da','tmp/online-ch2-b4-finite-identity-core-20261011/compiled/BanditRLProof/OnlineCumulativePotential.olean':'5f57b1aaced956d81cb1f9307ee3bd2278e2df29e7ac61c3fcecd27e493ff9f1','tmp/online-ch2-b4-finite-identity-precanary-v2-20261011/context-v2/receipt.json':'a7426c9728db5e66f4aecc1c502115817396400344c0c778615a9c1da5267b87'}
for p,h in checks.items():assert sha(root/p)==h,p
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=str(root)).decode().strip()=='cb4fe8ec8b979a698c31d3ebf5a350ac7242a66a'
assert not subprocess.check_output(['git','status','--porcelain'],cwd=str(root)).strip()
target=root/'Tests/OnlineCumulativePotentialCanary.lean';assert not target.exists()
rawrows=json.loads((root/'tmp/online-ch2-b4-finite-identity-precanary-v2-20261011/context-v2/pre-source-inputs.json').read_text())
seal=json.loads((root/'docs/contracts/online-ch2-b4-finite-identity-v1/canary-freeze-receipt-v1.json').read_text())
add=json.loads((root/'docs/contracts/online-ch2-b4-finite-identity-v1/precanary-preparation-addendum-v1.json').read_text())
for r in rawrows+seal['frozen_inputs']+add['added_inputs']:assert sha(root/r['path'])==r.get('sha256',r.get('raw_sha256')),r['path']
dump('authorization-and-context-before-v1.json',dict(UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),HEAD='cb4fe8ec8b979a698c31d3ebf5a350ac7242a66a',clean=True,Test_absent=True,verified_inputs=checks,RAW_rows=len(rawrows),seal_rows=len(seal['frozen_inputs']),addendum_rows=len(add['added_inputs'])))
header=[]
for tag,h in [('one-round','7d10ab86d93f97a5ac03db64ce96b8759a0a64d7bd440fa5bfbbe666717be75e'),('two-round','718a2eb714597c34033cc4d35af06b00b3718768cd60799800c6e487c777af64')]:
 p=root/('docs/contracts/online-ch2-b4-finite-identity-v1/canary-neutral-'+tag+'-frozen-header-v1.txt');assert sha(p)==h;header.append(p.read_text(encoding='utf-8'))
context=header[0].split('theorem ',1)[0];end='\nend BanditRL.OnlineCumulativePotentialCanary\n';assert header[1].split('theorem ',1)[0]==context
statements=[h[len(context):-len(end)].rstrip('\n') for h in header]
bodies=['''  dsimp only
  constructor
  · exact BanditRL.OnlineCumulativePotential.finite_regret_identity
      (fun _ v : ℝ => v ^ 2 / 2) (fun _ v : ℝ => (v - 1) ^ 2 / 2)
      (fun _ => (1 / 2 : ℝ)) (1 / 2) (2 / 3) 1 (by decide)
  · norm_num [Finset.sum_range_succ]
''','''  dsimp only
  constructor
  · exact BanditRL.OnlineCumulativePotential.finite_regret_identity
      (fun t v : ℝ => ((t : ℝ) + 1) * v ^ 2 / 2)
      (fun t v : ℝ => if t = 0 then v else if t = 1 then -2 * v + 1 else 0)
      (fun t => if t = 0 then (0 : ℝ) else if t = 1 then 1 else 100)
      3 2 2 (by decide)
  · norm_num [Finset.sum_range_succ]
''']
for i in range(2):assert context+statements[i]+'\n'+end==header[i]
candidate=context+'\n\n'.join(s+' := by\n'+b.rstrip('\n') for s,b in zip(statements,bodies))+'\n'+end
put('candidate-v1.lean',candidate);target.write_bytes(candidate.encode('utf-8'))
p=run('lake-search-path-v1',['lake','env','python','-c','import os; print(os.environ.get("LEAN_PATH", ""))']);assert p.returncode==0
env=os.environ.copy();env['LEAN_PATH']=str(root/'tmp/online-ch2-b4-finite-identity-core-20261011/compiled')+os.pathsep+p.stdout.decode().strip()
run('focused-v1',['lean','Tests/OnlineCumulativePotentialCanary.lean'],env)