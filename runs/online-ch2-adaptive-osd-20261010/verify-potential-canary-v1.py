from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash
canary = ROOT/'Tests/OnlineAdaptivePotentialCanary.lean'
frozen = load(RUN/'potential-canary-body-input-v2.json')['header_hashes']
names = ['leading_zero_and_stall', 'signed_zero_and_free_terminal']
probe = 'import Tests.OnlineAdaptivePotentialCanary\nopen Finset Tests.OnlineAdaptivePotentialCanary\n\n'
for i, name in enumerate(names, 1):
    assert statement_hash(lean_declaration_header(canary, name)) == frozen[name]
    header = (CONTRACT/('potential-canary-header-%d-draft-v1.lean.txt' % i)).read_text(encoding='utf8')
    probe += header.replace('theorem '+name, 'example', 1)
    probe += '  exact Tests.OnlineAdaptivePotentialCanary.'+name+'\n\n'
    probe += '#check Tests.OnlineAdaptivePotentialCanary.'+name+'\n'
    probe += '#print axioms Tests.OnlineAdaptivePotentialCanary.'+name+'\n\n'
write(RUN/'PotentialCanaryPublicProbeV1.lean', probe)
capture('potential-canary-public-probe-v1', 'lake', 'env', 'lean', RUN/'PotentialCanaryPublicProbeV1.lean')
for i, name in enumerate(names, 1):
    capture('potential-canary-fence-%d-v1' % i, sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
        'statement-fence', '--declaration', name, '--file', canary,
        '--output', RUN/('potential-canary-fence-%d-native-v1.json' % i))
    capture('potential-canary-safe-verify-%d-v1' % i, sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
        'safe-verify', '--fence', RUN/('potential-canary-fence-%d-native-v1.json' % i), '--lean-file', canary)
exporter = (ROOT/'runs/online-ch2-adaptive-energy-20261010/ExportCanaryConjunctValuesV1.lean').read_text(encoding='utf8')
start = exporter.index('  for n in #[')
end = exporter.index(' do\n', start)
exporter = exporter[:start]+'''  for n in #[`BanditRL.OnlineAdaptivePotential.weighted_potential_sum,
      `Tests.OnlineAdaptivePotentialCanary.leading_zero_and_stall,
      `Tests.OnlineAdaptivePotentialCanary.signed_zero_and_free_terminal]'''+exporter[end:]
start = exporter.index('  for (name,index) in #[')
end = exporter.index(' do\n', start)
exporter = exporter[:start]+'''  for (name,index) in #[
      (`Tests.OnlineAdaptivePotentialCanary.leading_zero_and_stall,0),
      (`Tests.OnlineAdaptivePotentialCanary.leading_zero_and_stall,3),
      (`Tests.OnlineAdaptivePotentialCanary.signed_zero_and_free_terminal,0),
      (`Tests.OnlineAdaptivePotentialCanary.signed_zero_and_free_terminal,1)]'''+exporter[end:]
exporter = exporter.replace('OnlineAdaptiveEnergy', 'OnlineAdaptivePotential')
exporter = exporter.replace('`BanditRL.OnlineAdaptivePotential.source_energy_term_bound',
    '`BanditRL.OnlineAdaptivePotential.weighted_potential_sum')
exporter = exporter.replace('Direct TYPE/VALUE constants in five selected full declarations and independently selected five inequality conjunction branches (including strictgap via prefixT3)',
    'Direct TYPE/VALUE constants in three selected full declarations and four independently selected inequality conjunction branches (including strictgap via C3)')
write(RUN/'ExportPotentialCanaryConjunctValuesV1.lean', exporter)
capture('potential-canary-value-export-v1', 'lake', 'env', 'lean', '--run',
    RUN/'ExportPotentialCanaryConjunctValuesV1.lean', RUN/'potential-canary-values-native-v1.json')
data = load(RUN/'potential-canary-values-native-v1.json')
assert len(data['nodes']) == 3 and len(data['selected_conjuncts']) == 4
assert all(r['required_present'] for r in data['selected_conjuncts'])
capture('potential-canary-compiled-trial-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'compiled',
    '--attempt-id', 'potential-canary-body-v2', '--harness', 'hierarchical', '--progress-class', 'compiled-leaf',
    '--obligations-before', '2', '--obligations-after', '2',
    '--verifier-evidence', RUN/'potential-canary-focused-build-v2.json',
    '--verifier-evidence', RUN/'potential-canary-values-native-v1.json',
    '--notes', 'Actual two full canaries compiled with four selected public-call branches; no accepted closure or parent algorithm claim.')
print('Two full canaries, standard axioms, unchanged headers and four selected compiled public-call branches verified.', flush=True)
