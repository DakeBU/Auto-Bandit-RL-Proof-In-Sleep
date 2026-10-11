from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash
public = ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean'
frozen = load(CONTRACT/'algorithm-stabilized-v1.json')
probe = '''import BanditRLProof.OnlineAdaptiveOSD
noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace BanditRL.OnlineAdaptiveOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance : DecidableEq E := Classical.decEq E
'''
for name, arguments in [
    ('state_succ', 'V α D loss x₁ p t'),
    ('state_prefix', "V α D loss loss' x₁ p t hloss")]:
    header = Path(frozen['headers'][name]['path']).read_text(encoding='utf8')
    assert statement_hash(lean_declaration_header(public, name)) == frozen['headers'][name]['normalized_statement_hash']
    probe += '\n'+header.replace('theorem '+name, 'example', 1)
    probe += '  exact BanditRL.OnlineAdaptiveOSD.'+name+' '+arguments+'\n'
    probe += '#check BanditRL.OnlineAdaptiveOSD.'+name+'\n'
    probe += '#print axioms BanditRL.OnlineAdaptiveOSD.'+name+'\n'
probe += '\nend BanditRL.OnlineAdaptiveOSD\n'
write(RUN/'CausalStatePublicProbeV1.lean', probe)
capture('causal-state-public-probe-v1', 'lake', 'env', 'lean', RUN/'CausalStatePublicProbeV1.lean')
for name in ['state_succ', 'state_prefix']:
    args = [sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py', 'statement-fence',
        '--declaration', name, '--file', public, '--output', RUN/(name+'-fence-native-v1.json')]
    if name == 'state_prefix':
        args += ['--source-assumption', "hloss : ∀ s < t, loss s = loss' s"]
    capture(name+'-fence-v1', *args)
    capture(name+'-safe-verify-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
        'safe-verify', '--fence', RUN/(name+'-fence-native-v1.json'), '--lean-file', public)
capture('causal-state-named-declarations-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'list-lean-decls', 'OnlineAdaptiveOSD', '--statement')
exporter = '''import BanditRLProof.OnlineAdaptiveOSD
import Lean
import Lean.Util.FoldConsts
open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [output] := args | throw <| IO.userError "expected one create-only output path"
  if ← System.FilePath.pathExists output then throw <| IO.userError "output already exists"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{module := `BanditRLProof.OnlineAdaptiveOSD}] {} (loadExts := true)
  let mut rows : Array Json := #[]
  for n in #[`BanditRL.OnlineAdaptiveOSD.state, `BanditRL.OnlineAdaptiveOSD.history,
      `BanditRL.OnlineAdaptiveOSD.energy, `BanditRL.OnlineAdaptiveOSD.output,
      `BanditRL.OnlineAdaptiveOSD.selected, `BanditRL.OnlineAdaptiveOSD.eta,
      `BanditRL.OnlineAdaptiveOSD.LegalFeedback, `BanditRL.OnlineAdaptiveOSD.regret,
      `BanditRL.OnlineAdaptiveOSD.state_succ, `BanditRL.OnlineAdaptiveOSD.state_prefix] do
    let some info := env.find? n | throw <| IO.userError s!"missing {n}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"no VALUE {n}"
    let td := info.type.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    let vd := value.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    if n == `BanditRL.OnlineAdaptiveOSD.state_prefix && !vd.contains `BanditRL.OnlineAdaptiveOSD.state_succ then
      throw <| IO.userError "prefix missing actual compiled recurrence parent"
    rows := rows.push <| Json.mkObj [
      ("declaration",toJson n.toString), ("has_value",toJson true),
      ("TYPE_constants",toJson <| td.map Name.toString),
      ("VALUE_constants",toJson <| vd.map Name.toString)]
  IO.FS.writeFile output ((Json.mkObj [
    ("source",toJson "actual compiled environment"), ("lean_version",toJson Lean.versionString),
    ("rows",Json.arr rows),
    ("boundary",toJson "Eight actual definitions and two structural theorem values; not ten source claims, not full graph/proof necessity or same-run regret closure. Fixed external parameter/policy prefix boundary retained.")]).pretty ++ "\\n")
  return 0
'''
write(RUN/'ExportCausalStateValuesV1.lean', exporter)
capture('causal-state-value-export-v1', 'lake', 'env', 'lean', '--run', RUN/'ExportCausalStateValuesV1.lean',
    RUN/'causal-state-values-native-v1.json')
data = load(RUN/'causal-state-values-native-v1.json')
assert len(data['rows']) == 10 and all(r['has_value'] for r in data['rows'])
assert 'BanditRL.OnlineAdaptiveOSD.state_succ' in data['rows'][-1]['VALUE_constants']
capture('causal-state-compiled-trial-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'compiled',
    '--attempt-id', 'causal-state-body-v1', '--harness', 'hierarchical', '--progress-class', 'compiled-leaf',
    '--obligations-before', '2', '--obligations-after', '2',
    '--verifier-evidence', RUN/'state-succ-focused-build-v1.json',
    '--verifier-evidence', RUN/'state-prefix-focused-build-v1.json',
    '--verifier-evidence', RUN/'causal-state-values-native-v1.json',
    '--notes', 'Eight actual recursive definitions, exact recurrence then strict-past whole-state theorem compile sequentially. Two frozen structural terminals remain pending separate BODY review; main regret terminal absent/unproved.')
print('Actual causal state definitions/public generic applications/fences/axioms/VALUEs verified; parent performance open.', flush=True)
