from pathlib import Path
import hashlib,json,subprocess,datetime,os,sys
root=Path('E:/ABRL/worktrees/research-online-book');out=root/'tmp/online-ch2-b4-finite-identity-core-20261011'
def sha(b):return hashlib.sha256(b).hexdigest()
def put(n,b):
 if isinstance(b,str):b=b.encode('utf-8')
 with (out/n).open('xb') as f:f.write(b)
def run(n,argv,env=None):
 start=datetime.datetime.now(datetime.timezone.utc).isoformat();p=subprocess.run(argv,cwd=str(root),env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 put(n+'.stdout.raw',p.stdout);put(n+'.stderr.raw',p.stderr)
 put(n+'.json',json.dumps(dict(argv=argv,cwd=str(root),startUTC=start,endUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),actual_exit=p.returncode,stdout_sha256=sha(p.stdout),stderr_sha256=sha(p.stderr),LEAN_PATH=None if env is None else env.get('LEAN_PATH'),core_sha256=sha((root/'BanditRLProof/OnlineCumulativePotential.lean').read_bytes())),indent=2)+'\n')
 print(n,p.returncode);return p
sys.path.insert(0,str(root/'tools'));import abrl_lifecycle as native
h=(root/'docs/contracts/online-ch2-b4-finite-identity-v1/neutral-frozen-header-v1.txt').read_text(encoding='utf-8');statement=h[h.index('theorem finite_regret_identity'):h.index('\n\nend BanditRL.OnlineCumulativePotential')]
fence=native.make_statement_fence(declaration='BanditRL.OnlineCumulativePotential.finite_regret_identity',file='BanditRLProof/OnlineCumulativePotential.lean',statement=statement,source_assumptions=['hT : 0 < T'])
put('native-statement-fence-v1.json',json.dumps(fence,indent=2)+'\n')
v=native.safe_verify(root,fence,lean_files=[root/'BanditRLProof/OnlineCumulativePotential.lean'])
put('native-safe-verify-v1.json',json.dumps(v,indent=2)+'\n');assert v['ok']
compiled=out/'compiled';(compiled/'BanditRLProof').mkdir(parents=True,exist_ok=True)
assert run('focused-olean-v1',['lake','env','lean','-o',str(compiled/'BanditRLProof/OnlineCumulativePotential.olean'),'BanditRLProof/OnlineCumulativePotential.lean']).returncode==0
probe='''import BanditRLProof.OnlineCumulativePotential
import Lean.Util.FoldConsts
open Lean Elab Command
#check BanditRL.OnlineCumulativePotential.finite_regret_identity
#print BanditRL.OnlineCumulativePotential.finite_regret_identity
#print axioms BanditRL.OnlineCumulativePotential.finite_regret_identity
run_cmd do
  let env ← getEnv
  let name := `BanditRL.OnlineCumulativePotential.finite_regret_identity
  let some info := env.find? name | throwError "Missing compiled target"
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let some value := info.value? (allowOpaque := true) | throwError "Missing proof value"
  let obj := Json.mkObj [
    ("declaration", toJson name.toString),
    ("TYPE", toJson (deps info.type)),
    ("VALUE", toJson (deps value))]
  liftIO <| IO.FS.writeFile "tmp/online-ch2-b4-finite-identity-core-20261011/compiled-constant-occurrences-v1.json" (obj.pretty ++ "\\n")
'''
put('PublicCompiledProbe.lean',probe)
env=os.environ.copy();env['LEAN_PATH']=str(compiled)+os.pathsep+env.get('LEAN_PATH','')
run('public-compiled-probe-v1',['lake','env','lean','tmp/online-ch2-b4-finite-identity-core-20261011/PublicCompiledProbe.lean'],env)