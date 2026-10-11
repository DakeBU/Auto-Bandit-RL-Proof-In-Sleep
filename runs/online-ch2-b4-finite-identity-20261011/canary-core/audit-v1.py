from pathlib import Path
import os,sys
p=Path('tmp/online-ch2-b4-finite-identity-canary-core-20261011');s=(p/'prepare-v1.py').read_text(encoding='utf-8').split('checks=')[0];exec(s)
sys.path.insert(0,str(root/'tools'));import abrl_lifecycle as native
path=root/'Tests/OnlineCumulativePotentialCanary.lean';source=path.read_text(encoding='utf-8');ctx=source.split('theorem ',1)[0];end='\nend BanditRL.OnlineCumulativePotentialCanary\n'
names=['finite_identity_one_round_positive_gap','finite_identity_two_round_terminal_splice'];fences=[]
for tag,name in zip(['one-round','two-round'],names):
 frozen=(root/('docs/contracts/online-ch2-b4-finite-identity-v1/canary-neutral-'+tag+'-frozen-header-v1.txt')).read_bytes()
 statement='theorem '+source.split('theorem '+name,1)[1].split(' := by\n',1)[0]
 statement=statement.replace('theorem ','theorem '+name,1)
 assert (ctx+statement+'\n'+end).encode()==frozen
 fence=native.make_statement_fence(declaration='BanditRL.OnlineCumulativePotentialCanary.'+name,file='Tests/OnlineCumulativePotentialCanary.lean',statement=statement,source_assumptions=[])
 result=native.safe_verify(root,fence,lean_files=[path]);assert result['ok'];fences.append(dict(declaration=name,frozen_complete_header_sha256=hashlib.sha256(frozen).hexdigest(),whole_header_reconstructed_exact=True,fence=fence,result=result,source_assumptions_reason='Closed concrete canary: no logical input binders; all objects are explicit statement-local lets preserved by full byte fence.'))
dump('native-fences-v1.json',fences)
compiled=out/'compiled';(compiled/'Tests').mkdir(parents=True,exist_ok=True)
env=os.environ.copy();env['LEAN_PATH']=str(root/'tmp/online-ch2-b4-finite-identity-core-20261011/compiled')+os.pathsep+(out/'lake-search-path-v1.stdout.raw').read_text().strip()
assert run('focused-olean-v1',['lean','-o',str(compiled/'Tests/OnlineCumulativePotentialCanary.olean'),'Tests/OnlineCumulativePotentialCanary.lean'],env).returncode==0
probe='''import Tests.OnlineCumulativePotentialCanary
import Lean.Util.FoldConsts
open Lean Elab Command
#check BanditRL.OnlineCumulativePotentialCanary.finite_identity_one_round_positive_gap
#print BanditRL.OnlineCumulativePotentialCanary.finite_identity_one_round_positive_gap
#print axioms BanditRL.OnlineCumulativePotentialCanary.finite_identity_one_round_positive_gap
#check BanditRL.OnlineCumulativePotentialCanary.finite_identity_two_round_terminal_splice
#print BanditRL.OnlineCumulativePotentialCanary.finite_identity_two_round_terminal_splice
#print axioms BanditRL.OnlineCumulativePotentialCanary.finite_identity_two_round_terminal_splice
run_cmd do
  let env ← getEnv
  let names := #[`BanditRL.OnlineCumulativePotentialCanary.finite_identity_one_round_positive_gap,
    `BanditRL.OnlineCumulativePotentialCanary.finite_identity_two_round_terminal_splice]
  let deps := fun (e : Expr) => (e.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.find? name | throwError "Missing compiled target"
    let some value := info.value? (allowOpaque := true) | throwError "Missing proof"
    rows := rows.push <| Json.mkObj [("declaration", toJson name.toString),
      ("TYPE", toJson (deps info.type)), ("VALUE", toJson (deps value))]
  liftIO <| IO.FS.writeFile "tmp/online-ch2-b4-finite-identity-canary-core-20261011/compiled-constant-occurrences-v1.json" ((toJson rows).pretty ++ "\\n")
'''
put('PublicCompiledCanaryProbe.lean',probe);env['LEAN_PATH']=str(compiled)+os.pathsep+env['LEAN_PATH']
run('public-compiled-canary-probe-v1',['lean','tmp/online-ch2-b4-finite-identity-canary-core-20261011/PublicCompiledCanaryProbe.lean'],env)