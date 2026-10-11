from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash
public = ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean'
frozen = load(CONTRACT/'bootstrap-stabilized-v1.json')
headers = frozen['exact_headers']
probe = '''import BanditRLProof.OnlineAdaptiveOSD
noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace BanditRL.OnlineAdaptiveOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance : DecidableEq E := Classical.decEq E
'''
arguments = {
    'energy_succ':'V α D loss x₁ p t', 'output_succ':'V α D loss x₁ p t',
    'energy_eq_sum':'V α D loss x₁ p T', 'history_mem':'V α D loss x₁ p hx₁ t i',
    'output_mem':'V α D loss x₁ p hx₁ t', 'energy_nonneg':'V α D loss x₁ p T',
    'eta_eq_energy':'V α D loss x₁ p t',
    'trajectory_finite_loss':'V α D loss x₁ p hx₁ t hloss u hu',
    'oracle_feedback':'V α D loss x₁ p hx₁ T hp hloss',
    'canonical_feedback':'V α D loss x₁ hx₁ T hloss'}
for name, row in headers.items():
    assert sha(row['path']) == row['raw_sha256']
    assert statement_hash(lean_declaration_header(public, name)) == row['normalized_statement_hash']
    header = Path(row['path']).read_text(encoding='utf8')
    probe += '\n'+header.replace('theorem '+name, 'example', 1)
    probe += '  exact BanditRL.OnlineAdaptiveOSD.'+name+' '+arguments[name]+'\n'
    probe += '#check BanditRL.OnlineAdaptiveOSD.'+name+'\n'
    probe += '#print axioms BanditRL.OnlineAdaptiveOSD.'+name+'\n'
probe += '\nend BanditRL.OnlineAdaptiveOSD\n'
write(RUN/'BootstrapPublicProbeV1.lean', probe)
code, out = capture('bootstrap-public-probe-v1', 'lake', 'env', 'lean', RUN/'BootstrapPublicProbeV1.lean')
print(out, flush=True)
for name in headers:
    capture('bootstrap-'+name+'-fence-v1', sys.executable, '-B', '-X', 'utf8',
        RUN/'native-scoped.py', 'statement-fence', '--declaration', name, '--file', public,
        '--output', RUN/('bootstrap-'+name+'-fence-native-v1.json'))
    capture('bootstrap-'+name+'-safe-verify-v1', sys.executable, '-B', '-X', 'utf8',
        RUN/'native-scoped.py', 'safe-verify', '--fence', RUN/('bootstrap-'+name+'-fence-native-v1.json'),
        '--lean-file', public)
capture('bootstrap-named-declarations-v1', sys.executable, '-B', '-X', 'utf8',
    RUN/'native-scoped.py', 'list-lean-decls', 'OnlineAdaptiveOSD', '--statement')
expected = {
    'energy_succ':['BanditRL.OnlineAdaptiveOSD.state_succ'],
    'output_succ':['BanditRL.OnlineAdaptiveOSD.state_succ'],
    'energy_eq_sum':['BanditRL.OnlineAdaptiveOSD.energy_succ'],
    'history_mem':['BanditRL.OnlineAdaptiveOSD.state_succ', 'BanditRL.OnlineGradientDescent.project_spec'],
    'output_mem':['BanditRL.OnlineAdaptiveOSD.history_mem'],
    'energy_nonneg':['BanditRL.OnlineAdaptiveOSD.energy_eq_sum'],
    'eta_eq_energy':['BanditRL.OnlineAdaptiveOSD.energy_succ'],
    'trajectory_finite_loss':['BanditRL.OnlineAdaptiveOSD.output_mem', 'BanditRL.OnlineSubgradientDescent.finite_loss'],
    'oracle_feedback':['BanditRL.OnlineAdaptiveOSD.output_mem'],
    'canonical_feedback':['BanditRL.OnlineAdaptiveOSD.oracle_feedback', 'BanditRL.OnlineSubgradientPolicy.canonicalPolicy_legal']}
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
  for n in #['''+', '.join('`BanditRL.OnlineAdaptiveOSD.'+n for n in headers)+'''] do
    let some info := env.find? n | throw <| IO.userError s!"missing {n}"
    let some value := info.value? (allowOpaque := true) | throw <| IO.userError s!"no VALUE {n}"
    let td := info.type.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    let vd := value.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    rows := rows.push <| Json.mkObj [
      ("declaration",toJson n.toString), ("has_value",toJson true),
      ("TYPE_constants",toJson <| td.map Name.toString),
      ("VALUE_constants",toJson <| vd.map Name.toString)]
  IO.FS.writeFile output ((Json.mkObj [
    ("source",toJson "actual compiled environment"), ("lean_version",toJson Lean.versionString),
    ("rows",Json.arr rows),
    ("boundary",toJson "Ten actual same-run structural/support bootstrap proof VALUEs, not ten source results; direct used-constant evidence, not a full graph or proof necessity. Parent regret remains unproved.")]).pretty ++ "\\n")
  return 0
'''
write(RUN/'ExportBootstrapValuesV1.lean', exporter)
capture('bootstrap-value-export-v1', 'lake', 'env', 'lean', '--run', RUN/'ExportBootstrapValuesV1.lean',
    RUN/'bootstrap-values-native-v1.json')
data = load(RUN/'bootstrap-values-native-v1.json')
assert len(data['rows']) == 10
for row in data['rows']:
    name = row['declaration'].rsplit('.', 1)[1]
    assert row['has_value']
    assert set(expected[name]).issubset(row['VALUE_constants']), (name, row)
write(RUN/'bootstrap-direct-parent-checks-v1.json', dict(expected_direct_VALUE_parents=expected,
    actual_VALUE_sha256=sha(RUN/'bootstrap-values-native-v1.json'), all_expected_found=True,
    boundary='Selected explicit direct compiled dependencies only, not necessity/full graph.'))
capture('bootstrap-compiled-trial-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'compiled',
    '--attempt-id', 'bootstrap-body-v1', '--harness', 'hierarchical', '--progress-class', 'compiled-leaf',
    '--obligations-before', '10', '--obligations-after', '10',
    '--verifier-evidence', RUN/'bootstrap-group-E-focused-build-v1.json',
    '--verifier-evidence', RUN/'bootstrap-public-probe-v1.json',
    '--verifier-evidence', RUN/'bootstrap-values-native-v1.json',
    '--notes', 'Five sequential focused builds and ten exact generic public applications/axiom/fences/direct VALUEs. BODY review and package gates pending; parent regret unproved, no source/chapter closure.')
print('Ten public generic applications/axioms/fences and compiled VALUE parents verified.', flush=True)
