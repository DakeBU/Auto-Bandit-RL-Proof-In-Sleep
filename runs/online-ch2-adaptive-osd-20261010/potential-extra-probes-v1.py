from common import *
context = (CONTRACT/'potential-canary-context-draft-v1.lean.txt').read_text(encoding='utf8')
checks = []
for i, name in [(1, 'leading_zero_and_stall'), (2, 'signed_zero_and_free_terminal')]:
    text = (CONTRACT/('potential-canary-header-%d-draft-v1.lean.txt' % i)).read_text(encoding='utf8')
    assert text.startswith('theorem '+name+' :') and text.rstrip().endswith(':= by')
    checks.append('#check ('+text[len('theorem '+name+' :'):].rstrip()[:-len(':= by')]+')\n')
write(RUN/'PotentialCanaryTypeProbeV1.lean', context+'\n'+'\n'.join(checks)+'\nend Tests.OnlineAdaptivePotentialCanary\n')
capture('potential-canary-type-probe-v1', 'lake', 'env', 'lean', RUN/'PotentialCanaryTypeProbeV1.lean')
exporter = (ROOT/'runs/online-ch2-adaptive-energy-20261010/ExportEnergyValuesV1.lean').read_text(encoding='utf8')
start = exporter.index('  let selected :')
end = exporter.index('  let mut rows :', start)
exporter = exporter[:start]+'''  let selected : Array (Name × Name) := #[
    (`BanditRL.OnlineAdaptivePotential.weighted_potential_sum,
      `Finset.sum_range_by_parts)]
'''+exporter[end:]
exporter = exporter.replace('OnlineAdaptiveEnergy', 'OnlineAdaptivePotential')
exporter = exporter.replace('Direct compiled TYPE/VALUE constant presences for three proof terminals of one source family;',
    'Direct compiled TYPE/VALUE constant presences for the one frozen generic potential terminal;')
write(RUN/'ExportPotentialValuesV1.lean', exporter)
capture('potential-value-export-v1', 'lake', 'env', 'lean', '--run', RUN/'ExportPotentialValuesV1.lean',
    RUN/'potential-values-native-v1.json')
data = load(RUN/'potential-values-native-v1.json')
assert len(data['rows']) == 1 and data['rows'][0]['has_value']
assert 'Finset.sum_range_by_parts' in data['rows'][0]['VALUE_constants']
write(RUN/'potential-local-evidence-v1.json', dict(
    actual_focused_compiler_marker='Built BanditRLProof.OnlineAdaptivePotential; Build completed successfully',
    full_generic_application=True, frozen_statement_unchanged=True,
    standard_axioms=['propext', 'Classical.choice', 'Quot.sound'],
    direct_compiled_parent='Finset.sum_range_by_parts',
    source_proof_display_erratum=False, BODY_review='pending', canary_BODY='not created',
    parent_causal_OSD='required-draft', combined_gate='not run for current package', whole_Goal='active'))
print('Canary proposition types elaborate only; actual potential VALUE parent checked.', flush=True)
