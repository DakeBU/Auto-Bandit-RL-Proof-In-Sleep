from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash
public = ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean'
headers = load(CONTRACT/'actual-step-stabilized-v1.json')['exact_headers']
assert load(RUN/'actual-step-group-D-focused-build-v2.json')['actual_exit'] == 0
probe = '''import BanditRLProof.OnlineAdaptiveOSD
noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace BanditRL.OnlineAdaptiveOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance : DecidableEq E := Classical.decEq E
'''
arguments = {
    'energy_step_mono':'V α D loss x₁ p t',
    'energy_pos_of_selected_ne_zero':'V α D loss x₁ p t hg',
    'eta_pos_of_selected_ne_zero':'V α D hα hD loss x₁ p t hg',
    'zero_feedback_step':'V α D loss x₁ p t hloss hg hz u hu',
    'one_step_chain':'V α D hα hD loss x₁ p t hloss hg hnz u hu',
    'one_step':'V α D hα hD loss x₁ p t hloss hg u hu',
    'regret_zero_diameter':'V α loss x₁ p hx₁ T hdiam u hu'}
for name, row in headers.items():
    assert sha(row['path']) == row['raw_sha256']
    assert statement_hash(lean_declaration_header(public, name)) == row['normalized_statement_hash']
    probe += '\n'+Path(row['path']).read_text(encoding='utf8').replace('theorem '+name, 'example', 1)
    probe += '  exact BanditRL.OnlineAdaptiveOSD.'+name+' '+arguments[name]+'\n'
    probe += '#check BanditRL.OnlineAdaptiveOSD.'+name+'\n'
    probe += '#print axioms BanditRL.OnlineAdaptiveOSD.'+name+'\n'
probe += '\nend BanditRL.OnlineAdaptiveOSD\n'
write(RUN/'ActualStepPublicProbeV1.lean', probe)
code, out = capture('actual-step-public-probe-v1', 'lake', 'env', 'lean', RUN/'ActualStepPublicProbeV1.lean')
print(out, flush=True)
for name in headers:
    capture('actual-step-'+name+'-fence-v1', sys.executable, '-B', '-X', 'utf8',
        RUN/'native-scoped.py', 'statement-fence', '--declaration', name, '--file', public,
        '--output', RUN/('actual-step-'+name+'-fence-native-v1.json'))
    capture('actual-step-'+name+'-safe-verify-v1', sys.executable, '-B', '-X', 'utf8',
        RUN/'native-scoped.py', 'safe-verify', '--fence', RUN/('actual-step-'+name+'-fence-native-v1.json'),
        '--lean-file', public)
capture('actual-step-named-declarations-v1', sys.executable, '-B', '-X', 'utf8',
    RUN/'native-scoped.py', 'list-lean-decls', 'OnlineAdaptiveOSD', '--statement')
expected = {
    'energy_step_mono':['BanditRL.OnlineAdaptiveOSD.energy_succ'],
    'energy_pos_of_selected_ne_zero':['BanditRL.OnlineAdaptiveOSD.energy_succ', 'BanditRL.OnlineAdaptiveOSD.energy_nonneg'],
    'eta_pos_of_selected_ne_zero':['BanditRL.OnlineAdaptiveOSD.eta_eq_energy', 'BanditRL.OnlineAdaptiveOSD.energy_pos_of_selected_ne_zero'],
    'zero_feedback_step':['BanditRL.OnlineAdaptiveOSD.output_succ', 'BanditRL.OnlineSubgradientDescent.lemma_2_31'],
    'one_step_chain':['BanditRL.OnlineAdaptiveOSD.output_succ', 'BanditRL.OnlineAdaptiveOSD.eta_pos_of_selected_ne_zero', 'BanditRL.OnlineSubgradientDescent.lemma_2_31'],
    'one_step':['BanditRL.OnlineAdaptiveOSD.zero_feedback_step', 'BanditRL.OnlineAdaptiveOSD.one_step_chain',
        'BanditRL.OnlineAdaptiveOSD.eta_eq_energy', 'BanditRL.OnlineAdaptiveOSD.energy_pos_of_selected_ne_zero'],
    'regret_zero_diameter':['BanditRL.OnlineAdaptiveOSD.output_mem']}
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
    ("boundary",toJson "Seven actual same-run one-step dependency proof VALUEs; direct selected constants, not seven source results, a full graph or proof necessity. Parent regret not yet proved.")]).pretty ++ "\\n")
  return 0
'''
write(RUN/'ExportActualStepValuesV1.lean', exporter)
capture('actual-step-value-export-v1', 'lake', 'env', 'lean', '--run', RUN/'ExportActualStepValuesV1.lean',
    RUN/'actual-step-values-native-v1.json')
data = load(RUN/'actual-step-values-native-v1.json')
assert len(data['rows']) == 7
for row in data['rows']:
    name = row['declaration'].rsplit('.', 1)[1]
    assert row['has_value']
    assert set(expected[name]).issubset(row['VALUE_constants']), (name, row)
write(RUN/'actual-step-direct-parent-checks-v1.json', dict(expected_direct_VALUE_parents=expected,
    actual_VALUE_sha256=sha(RUN/'actual-step-values-native-v1.json'), all_expected_found=True,
    boundary='Selected direct compiled parents only, not necessity/full graph.'))
capture('actual-step-compiled-trial-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'compiled',
    '--attempt-id', 'actual-step-body-v1', '--harness', 'hierarchical', '--progress-class', 'compiled-leaf',
    '--obligations-before', '7', '--obligations-after', '7',
    '--verifier-evidence', RUN/'actual-step-group-D-focused-build-v2.json',
    '--verifier-evidence', RUN/'actual-step-public-probe-v1.json',
    '--verifier-evidence', RUN/'actual-step-values-native-v1.json',
    '--notes', 'Four sequential focused builds plus successful group D lint-only cleanup rebuild; seven FULL public applications/standard axioms/frozen fences/direct VALUE parents. Distinct BODY review/package gates pending; parent regret unproved.')
print('Seven exact public one-step interfaces and actual compiled parents verified.', flush=True)
