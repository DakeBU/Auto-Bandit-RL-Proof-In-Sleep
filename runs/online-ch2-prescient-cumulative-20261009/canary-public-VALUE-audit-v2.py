from common import *
import re
fixed()
st = load(CONTRACT/'stabilized-v1.json')
cs = load(CONTRACT/'canary-stabilized-v1.json')
assert load(RUN/'two-canaries-projection-focused-inspected-v3.json')['compiled']
test = ROOT/cs['targets'][0]['file']
assert sha(test) == load(RUN/'two-canaries-projection-focused-inspected-v3.json')['canary_sha256']
probe = '''import Tests.OnlinePrescientBregmanRegretCanary
noncomputable section
open Set Finset
namespace BanditRL.OnlinePrescientBregmanRegretCanary
open BanditRL.OnlineConvex BanditRL.OnlineBregman BanditRL.OnlinePrescientBregman
'''
for t in cs['targets']:
    probe += t['exact_header'].replace('theorem '+t['name'],'example',1)+' := by\n  exact '+t['name']+'\n\n#check @'+t['declaration']+'\n#print axioms '+t['declaration']+'\n\n'
probe += 'end BanditRL.OnlinePrescientBregmanRegretCanary\n'
write(RUN/'canary-public-probe-v2.lean',probe)
code,out = capture('canary-public-probe-command-v2','lake','env','lean',RUN/'canary-public-probe-v2.lean',required=False)
assert code == 0, out
ax = re.findall(r'depends on axioms: \[([^\]]*)\]',out)
assert len(ax)==2 and all(set(map(str.strip,s.split(',')))=={'propext','Classical.choice','Quot.sound'} for s in ax)
parent = ROOT/'runs/online-ch2-prescient-causal-20261009/export-selected-dependencies-v1.lean'
graphsource = parent.read_text(encoding='utf8')
start = graphsource.index('def targets : Array Name := #[')
end = graphsource.index('\n\ndef moduleName',start)
names = [t['declaration'] for t in st['targets']+cs['targets']]
graphsource = graphsource[:start]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']'+graphsource[end:]
graphsource = graphsource.replace('Tests.OnlinePrescientBregmanCanary','Tests.OnlinePrescientBregmanRegretCanary')
graphsource = graphsource.replace('Eight frozen production proofs/two exact definitions and four complete concrete Test conjunctions plus referenced compiler-generated Test auxiliaries.', 'Five frozen production proofs and two complete concrete Test conjunctions plus referenced compiler-generated Test auxiliaries.')
write(RUN/'export-selected-dependencies-v2.lean',graphsource)
capture('selected-graph-export-command-v2','lake','env','lean','--run',RUN/'export-selected-dependencies-v2.lean',RUN/'selected-value-graph-v2.json')
numeric = '''import Tests.OnlinePrescientBregmanRegretCanary
import Lean
import Lean.Util.FoldConsts
open Lean

partial def peel (e : Expr) : Expr :=
  match e with
  | .letE _ _ value body _ => peel (body.instantiate1 value)
  | .mdata _ body => peel body
  | _ => if e.getAppFn.isConstOf ``id && e.getAppArgs.size == 2 then peel e.getAppArgs[1]! else e

partial def conjunct (e : Expr) (index : Nat) : Except String Expr := do
  let p := peel e
  if p.getAppFn.isConstOf ``And.intro && p.getAppArgs.size == 4 then
    if index == 0 then return peel p.getAppArgs[2]!
    else conjunct p.getAppArgs[3]! (index - 1)
  else if index == 0 then return p
  else throw "conjunction spine ended before requested index"

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one create-only output path"
  if ← System.FilePath.pathExists output then throw <| IO.userError "output already exists"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{module := `Tests.OnlinePrescientBregmanRegretCanary}] {} (loadExts := true)
  let mut rows : Array Json := #[]
  for (name,index,required) in #[
    (`BanditRL.OnlinePrescientBregmanRegretCanary.fixed_signed_run,14,`BanditRL.OnlinePrescientBregman.iterate_fixed_sharp),
    (`BanditRL.OnlinePrescientBregmanRegretCanary.fixed_signed_run,15,`BanditRL.OnlinePrescientBregman.iterate_fixed_regret),
    (`BanditRL.OnlinePrescientBregmanRegretCanary.decreasing_signed_run,20,`BanditRL.OnlinePrescientBregman.iterate_variable_sharp),
    (`BanditRL.OnlinePrescientBregmanRegretCanary.decreasing_signed_run,21,`BanditRL.OnlinePrescientBregman.iterate_variable_regret)] do
    let some info := env.find? name | throw <| IO.userError s!"missing {name}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"missing value {name}"
    let tail ← match conjunct value index with | .ok e => pure e | .error err => throw <| IO.userError err
    let deps := tail.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    let head := match tail.getAppFn with | .const n _ => n.toString | _ => "nonconstant-head"
    if !deps.contains required then throw <| IO.userError s!"numeric branch {name}/{index} lacks {required}"
    rows := rows.push <| Json.mkObj [
      ("declaration",toJson name.toString),("zero_based_conjunct_index",toJson index),
      ("selected_proof_head",toJson head),("required_production_VALUE",toJson required.toString),
      ("required_present",toJson true),("selected_proof_direct_constants",toJson <| deps.map Name.toString)]
  IO.FS.writeFile output ((Json.mkObj [
    ("source",toJson "actual-compiled-environment"),
    ("selection",toJson "Substitute top-level lets, remove metadata/explicit id, select each specified And.intro conjunct independently. No theorem unfolding or proof-irrelevance normalization. Whole-conjunction dependencies do not certify selected numeric branches."),
    ("rows",Json.arr rows)]).pretty ++ "\\n")
  return 0
'''
write(RUN/'audit-four-numeric-branches-v2.lean',numeric)
capture('four-numeric-branches-command-v2','lake','env','lean','--run',RUN/'audit-four-numeric-branches-v2.lean',RUN/'four-numeric-branches-v2.json')
g=load(RUN/'selected-value-graph-v2.json')
nd={n['name']:n for n in g['nodes']}
assert set(names).issubset(nd)
assert all(nd[n]['has_value'] for n in names)
pairs=[(cs['targets'][0]['declaration'],st['targets'][i]['declaration']) for i in [0,1,3]]+[(cs['targets'][1]['declaration'],st['targets'][i]['declaration']) for i in [2,4]]
for a,b in pairs: assert b in nd[a]['value_dependencies'],(a,b)
nr=load(RUN/'four-numeric-branches-v2.json')['rows']
assert len(nr)==4 and all(r['required_present'] for r in nr)
for i,(t,f) in enumerate(zip(cs['targets'],['fixed-canary-fence-v1.json','decreasing-canary-fence-v1.json'])):
    assert t['exact_header'] in test.read_text(encoding='utf8')
    capture('two-canary-safe-verify-%d-v2'%i,sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--fence',CONTRACT/f)
write(RUN/'two-canaries-exact-public-v2.lean',test.read_bytes())
write(RUN/'canary-public-VALUE-inspected-v2.json',dict(complete_public_canary_examples=2,public_conjunction_sizes=[16,22],selected_public_nodes=len(names),selected_total_nodes=len(nd),selected_coalesced_direct_TYPE_VALUE_presences=len(g['edges']),required_canary_VALUE_pairs=pairs,individually_selected_numeric_branches=nr,actual_standard_axiom_lists=2,standard_only_axioms=['propext','Classical.choice','Quot.sound'],production_sha256=sha(PUBLIC),canary_sha256=sha(test),frozen_headers_unchanged=True,full_combined_gates='pending',semantic_BODY_review='pending',source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Two complete public canaries, two standard axiom lists, five canary VALUE parents, four independently selected numeric branches passed. Not package/source/chapter acceptance.')
