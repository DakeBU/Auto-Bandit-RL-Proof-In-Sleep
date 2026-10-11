from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash
public = ROOT/'BanditRLProof/OnlineAdaptiveBenchmark.lean'
headers = load(CONTRACT/'benchmark-stabilized-v1.json')['exact_headers']
probe = (CONTRACT/'benchmark-context-draft-v1.lean.txt').read_text(encoding='utf8')
for name, row in headers.items():
    version = 'v2' if name == 'benchmark_isGLB' else 'v1'
    assert load(RUN/('benchmark-'+name+'-focused-build-'+version+'.json'))['actual_exit'] == 0
    assert sha(row['path']) == row['raw_sha256']
    assert statement_hash(lean_declaration_header(public, name)) == row['normalized_statement_hash']
    probe += '\n'+Path(row['path']).read_text(encoding='utf8').replace('theorem '+name, 'example', 1)
    args = 'D S hD hS' if name != 'source_theorem4_14_infimum' else 'V D hD loss x₁ p hx₁ T hconvex hloss hlegal hdiam u hu'
    probe += '  exact BanditRL.OnlineAdaptiveBenchmark.'+name+' '+args+'\n'
    probe += '#check BanditRL.OnlineAdaptiveBenchmark.'+name+'\n#print axioms BanditRL.OnlineAdaptiveBenchmark.'+name+'\n'
probe += '\nend BanditRL.OnlineAdaptiveBenchmark\n'
write(RUN/'BenchmarkPublicProbeV1.lean', probe)
code, out = capture('benchmark-public-probe-v1', 'lake', 'env', 'lean', RUN/'BenchmarkPublicProbeV1.lean')
print(out, flush=True)
assert 'sorryAx' not in out
assert out.count('depends on axioms: [propext, Classical.choice, Quot.sound]') == 5
for name in headers:
    capture('benchmark-'+name+'-fence-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
        'statement-fence', '--declaration', name, '--file', public,
        '--output', RUN/('benchmark-'+name+'-fence-native-v1.json'))
    capture('benchmark-'+name+'-safe-verify-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
        'safe-verify', '--fence', RUN/('benchmark-'+name+'-fence-native-v1.json'), '--lean-file', public)
capture('benchmark-named-declarations-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'list-lean-decls', 'OnlineAdaptiveBenchmark', '--statement')
exporter = (RUN/'ExportParentValueV1.lean').read_text(encoding='utf8')
exporter = exporter.replace('BanditRLProof.OnlineAdaptiveOSD', 'BanditRLProof.OnlineAdaptiveBenchmark')
a = exporter.index('  for n in #[')
b = exporter.index('] do', a)
exporter = exporter[:a]+'  for n in #['+', '.join('`BanditRL.OnlineAdaptiveBenchmark.'+n for n in headers)+exporter[b:]
exporter = exporter.replace('Actual same-run cumulative parent proof VALUE. Selected direct constants only, not a full graph or proof necessity; source specializations and combined package gates remain pending.',
    'Five full benchmark/attainment/source-conjunction actual proof VALUEs. Selected direct constants only; not a full graph, necessity, literal printed-minimum certification, or package/chapter acceptance.')
write(RUN/'ExportBenchmarkValuesV1.lean', exporter)
capture('benchmark-value-export-v1', 'lake', 'env', 'lean', '--run', RUN/'ExportBenchmarkValuesV1.lean',
    RUN/'benchmark-values-native-v1.json')
data = load(RUN/'benchmark-values-native-v1.json')
expected = {
    'benchmark_isGLB':['BanditRL.OnlineOptimalStep.lower_bound', 'BanditRL.OnlineOptimalStep.distance_energy_argmin'],
    'source_benchmark_value':['BanditRL.OnlineAdaptiveBenchmark.benchmark_isGLB', 'IsGLB.csInf_eq', 'Real.sqrt_mul'],
    'benchmark_attained_iff':['BanditRL.OnlineOptimalStep.zero_distance_decreases', 'BanditRL.OnlineOptimalStep.zero_energy_decreases', 'BanditRL.OnlineOptimalStep.lower_bound', 'BanditRL.OnlineOptimalStep.distance_energy_argmin'],
    'benchmark_positive_minimum':['BanditRL.OnlineOptimalStep.distance_energy_argmin', 'BanditRL.OnlineOptimalStep.optimal_unique'],
    'source_theorem4_14_infimum':['BanditRL.OnlineAdaptiveOSD.source_theorem4_14', 'BanditRL.OnlineAdaptiveOSD.energy_nonneg', 'BanditRL.OnlineAdaptiveBenchmark.source_benchmark_value']}
assert len(data['rows']) == 5
for row in data['rows']:
    name = row['declaration'].rsplit('.', 1)[1]
    assert row['has_value'] and set(expected[name]).issubset(row['VALUE_constants']), name
write(RUN/'benchmark-direct-parent-checks-v1.json', dict(expected_direct_VALUE_parents=expected,
    actual_VALUE_sha256=sha(RUN/'benchmark-values-native-v1.json'), all_expected_found=True,
    boundary='Selected direct compiled parents, not full graph or necessity. Full conjunction/unique-minimum statements were publicly applied. Distinct BODY review/package gates pending.'))
capture('benchmark-compiled-trial-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'compiled',
    '--attempt-id', 'benchmark-bodies-v2', '--harness', 'hierarchical', '--progress-class', 'compiled-leaf',
    '--obligations-before', '5', '--obligations-after', '5',
    '--verifier-evidence', RUN/'benchmark-source_theorem4_14_infimum-focused-build-v1.json',
    '--verifier-evidence', RUN/'benchmark-public-probe-v1.json',
    '--verifier-evidence', RUN/'benchmark-values-native-v1.json',
    '--notes', 'Five actual sequential focused successes; first failure retained with local BODY-only ring repair. Full public/axiom/fence/direct VALUE checks. Distinct BODY review, algorithm canary and all package gates pending.')
print('Five complete public statements/standard axioms/unchanged fences/direct compiled parents verified.', flush=True)
