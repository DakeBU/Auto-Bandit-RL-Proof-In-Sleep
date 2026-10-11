from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash
public = ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean'
headers = load(CONTRACT/'specialization-stabilized-v1.json')['exact_headers']
for name in headers:
    assert load(RUN/('specialization-'+name+'-focused-build-v1.json'))['actual_exit'] == 0
probe = '''import BanditRLProof.OnlineAdaptiveOSD
noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace BanditRL.OnlineAdaptiveOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance : DecidableEq E := Classical.decEq E
'''
args = {n:'V D hD loss x₁ '+('p ' if n.startswith('source_') else '')+
    'hx₁ T hconvex hloss '+('hlegal ' if n.startswith('source_') else '')+'hdiam u hu' for n in headers}
for name, row in headers.items():
    assert sha(row['path']) == row['raw_sha256']
    assert statement_hash(lean_declaration_header(public, name)) == row['normalized_statement_hash']
    probe += '\n'+Path(row['path']).read_text(encoding='utf8').replace('theorem '+name, 'example', 1)
    probe += '  exact BanditRL.OnlineAdaptiveOSD.'+name+' '+args[name]+'\n'
    probe += '#check BanditRL.OnlineAdaptiveOSD.'+name+'\n#print axioms BanditRL.OnlineAdaptiveOSD.'+name+'\n'
probe += '\nend BanditRL.OnlineAdaptiveOSD\n'
write(RUN/'SpecializationPublicProbeV1.lean', probe)
code, out = capture('specialization-public-probe-v1', 'lake', 'env', 'lean', RUN/'SpecializationPublicProbeV1.lean')
print(out, flush=True)
assert out.count('depends on axioms: [propext, Classical.choice, Quot.sound]') == 4
for name in headers:
    capture('specialization-'+name+'-fence-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
        'statement-fence', '--declaration', name, '--file', public,
        '--source-assumption', '(hconvex : ∀ t < T, IsConvexExtended (loss t))',
        '--output', RUN/('specialization-'+name+'-fence-native-v1.json'))
    capture('specialization-'+name+'-safe-verify-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
        'safe-verify', '--fence', RUN/('specialization-'+name+'-fence-native-v1.json'), '--lean-file', public)
capture('specialization-named-declarations-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'list-lean-decls', 'OnlineAdaptiveOSD', '--statement')
exporter = (RUN/'ExportParentValueV1.lean').read_text(encoding='utf8')
a = exporter.index('  for n in #[')
b = exporter.index('] do', a)
exporter = exporter[:a]+'  for n in #['+', '.join('`BanditRL.OnlineAdaptiveOSD.'+n for n in headers)+exporter[b:]
exporter = exporter.replace('Actual same-run cumulative parent proof VALUE. Selected direct constants only, not a full graph or proof necessity; source specializations and combined package gates remain pending.',
    'Four complete source-convex/canonical endpoint proof VALUEs. Selected direct constants only; no full graph/necessity or package/chapter/benchmark acceptance.')
write(RUN/'ExportSpecializationValuesV1.lean', exporter)
capture('specialization-value-export-v1', 'lake', 'env', 'lean', '--run', RUN/'ExportSpecializationValuesV1.lean',
    RUN/'specialization-values-native-v1.json')
data = load(RUN/'specialization-values-native-v1.json')
expected = {
    'source_eq4_4':['BanditRL.OnlineAdaptiveOSD.regret_bound'],
    'source_theorem4_14':['BanditRL.OnlineAdaptiveOSD.regret_bound', 'Real.sqrt_mul'],
    'canonical_eq4_4':['BanditRL.OnlineAdaptiveOSD.source_eq4_4', 'BanditRL.OnlineAdaptiveOSD.canonical_feedback'],
    'canonical_theorem4_14':['BanditRL.OnlineAdaptiveOSD.source_theorem4_14', 'BanditRL.OnlineAdaptiveOSD.canonical_feedback']}
assert len(data['rows']) == 4
for row in data['rows']:
    name = row['declaration'].rsplit('.', 1)[1]
    assert row['has_value'] and set(expected[name]).issubset(row['VALUE_constants'])
write(RUN/'specialization-direct-parent-checks-v1.json', dict(expected_direct_VALUE_parents=expected,
    actual_VALUE_sha256=sha(RUN/'specialization-values-native-v1.json'), all_expected_found=True,
    boundary='Selected direct compiled parents, not full graph/necessity. Four declarations correspond to two performance displays plus canonical adapters, not four independent printed source results.'))
capture('specialization-compiled-trial-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'compiled',
    '--attempt-id', 'specialization-bodies-v1', '--harness', 'hierarchical', '--progress-class', 'compiled-leaf',
    '--obligations-before', '4', '--obligations-after', '4',
    '--verifier-evidence', RUN/'specialization-canonical_theorem4_14-focused-build-v1.json',
    '--verifier-evidence', RUN/'specialization-public-probe-v1.json',
    '--verifier-evidence', RUN/'specialization-values-native-v1.json',
    '--notes', 'Four sequential actual focused successes, full public/standard axioms/frozen hconvex fences and selected compiled parents. Distinct BODY review, required benchmark/algorithm canary and all package gates remain pending.')
print('Four full source/canonical endpoints public/axiom/fence/direct compiled parent checks passed.', flush=True)
