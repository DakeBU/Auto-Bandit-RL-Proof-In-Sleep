from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash
public = ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean'
w = load(CONTRACT/'parent-stabilized-v1.json')['allowed_window']
assert load(RUN/'parent-focused-build-v1.json')['actual_exit'] == 0
before = public.read_bytes()
assert before == (RUN/'parent-body-attempt-v1.lean.txt').read_bytes()
old = b'      field_simp [ne_of_gt h\xce\xb1, ne_of_gt hDpos]\n      <;> ring\n'
new = b'      field_simp [ne_of_gt h\xce\xb1, ne_of_gt hDpos]\n      ring\n'
assert before.count(old) == 1
public.write_bytes(before.replace(old, new, 1))
write(RUN/'parent-body-attempt-v2.lean.txt', public.read_bytes())
assert statement_hash(lean_declaration_header(public, 'regret_bound')) == w['normalized_statement_hash']
assert public.read_bytes().startswith((RUN/'actual-step-group-D-body-attempt-v2.lean.txt').read_bytes().rsplit(b'end BanditRL.OnlineAdaptiveOSD\n', 1)[0])
code, out = capture('parent-focused-build-v2', 'lake', 'build', 'BanditRLProof.OnlineAdaptiveOSD')
print('\n'.join(out.splitlines()[-6:]), flush=True)
assert 'Build completed successfully' in out
write(RUN/'parent-tactic-sequence-cleanup-v2.json', dict(
    before_sha256=hashlib.sha256(before).hexdigest(), after_sha256=sha(public),
    change='Only use sequential ring after field_simp instead of unnecessary <;> ring.',
    v1_actual_exit=0, v2_actual_exit=0, is_compile_failure=False, header_unchanged=True))
probe = '''import BanditRLProof.OnlineAdaptiveOSD
noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace BanditRL.OnlineAdaptiveOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance : DecidableEq E := Classical.decEq E
'''
probe += '\n'+Path(w['header_path']).read_text(encoding='utf8').replace('theorem regret_bound', 'example', 1)
probe += '  exact BanditRL.OnlineAdaptiveOSD.regret_bound V α D hα hD loss x₁ p hx₁ T hloss hlegal hdiam u hu\n'
probe += '#check BanditRL.OnlineAdaptiveOSD.regret_bound\n#print axioms BanditRL.OnlineAdaptiveOSD.regret_bound\n'
probe += 'end BanditRL.OnlineAdaptiveOSD\n'
write(RUN/'ParentPublicProbeV1.lean', probe)
code, out = capture('parent-public-probe-v1', 'lake', 'env', 'lean', RUN/'ParentPublicProbeV1.lean')
print(out, flush=True)
assert 'sorryAx' not in out
assert 'depends on axioms: [propext, Classical.choice, Quot.sound]' in out
capture('parent-regret_bound-fence-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'statement-fence', '--declaration', 'regret_bound', '--file', public,
    '--output', RUN/'parent-regret_bound-fence-native-v1.json')
capture('parent-regret_bound-safe-verify-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'safe-verify', '--fence', RUN/'parent-regret_bound-fence-native-v1.json', '--lean-file', public)
capture('parent-named-declarations-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'list-lean-decls', 'OnlineAdaptiveOSD.regret_bound', '--statement')
exporter = (RUN/'ExportActualStepValuesV1.lean').read_text(encoding='utf8')
a = exporter.index('  for n in #[')
b = exporter.index('] do', a)
exporter = exporter[:a]+'  for n in #[`BanditRL.OnlineAdaptiveOSD.regret_bound'+exporter[b:]
exporter = exporter.replace('Seven actual same-run one-step dependency proof VALUEs; direct selected constants, not seven source results, a full graph or proof necessity. Parent regret not yet proved.',
    'Actual same-run cumulative parent proof VALUE. Selected direct constants only, not a full graph or proof necessity; source specializations and combined package gates remain pending.')
write(RUN/'ExportParentValueV1.lean', exporter)
capture('parent-value-export-v1', 'lake', 'env', 'lean', '--run', RUN/'ExportParentValueV1.lean',
    RUN/'parent-value-native-v1.json')
data = load(RUN/'parent-value-native-v1.json')
assert len(data['rows']) == 1 and data['rows'][0]['has_value']
expected = ['BanditRL.OnlineAdaptiveOSD.'+n for n in [
    'one_step', 'regret_zero_diameter', 'energy_eq_sum', 'energy_step_mono', 'output_mem']]
expected += ['BanditRL.OnlineAdaptivePotential.weighted_potential_sum',
    'BanditRL.OnlineAdaptiveEnergy.norm_sq_sum_div_sqrt_prefix']
assert set(expected).issubset(data['rows'][0]['VALUE_constants'])
write(RUN/'parent-direct-parent-checks-v1.json', dict(expected_direct_VALUE_parents=expected,
    actual_VALUE_sha256=sha(RUN/'parent-value-native-v1.json'), all_expected_found=True,
    boundary='Selected direct compiled parents only, not necessity/full graph.'))
capture('parent-compiled-trial-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'compiled',
    '--attempt-id', 'parent-body-v1', '--harness', 'hierarchical', '--progress-class', 'compiled-leaf',
    '--obligations-before', '1', '--obligations-after', '1',
    '--verifier-evidence', RUN/'parent-focused-build-v2.json',
    '--verifier-evidence', RUN/'parent-public-probe-v1.json',
    '--verifier-evidence', RUN/'parent-value-native-v1.json',
    '--notes', 'Actual full frozen parent compiles with public application/standard axioms/fence/direct compiled parents. Independent BODY review and full package gates pending; no source/chapter acceptance.')
print('Full parent public application, standard axioms, unchanged header and seven direct compiled parents verified.', flush=True)
