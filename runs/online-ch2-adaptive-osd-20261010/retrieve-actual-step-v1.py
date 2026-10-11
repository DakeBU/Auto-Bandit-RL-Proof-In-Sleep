from common import *
capture('actual-step-memory-retrieval-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'search-memory', 'projected subgradient one_step support_gap zero feedback')
for i, query in enumerate(['OnlineSubgradientDescent.lemma_2_31', 'OnlineLinearization.support_gap',
    'OnlineSubgradientPolicy.one_step', 'OnlineAdaptiveOSD.energy_nonneg'], 1):
    capture('actual-step-declaration-retrieval-%d-v1' % i, sys.executable, '-B', '-X', 'utf8',
        RUN/'native-scoped.py', 'list-lean-decls', query, '--statement')
capture('actual-step-source-API-window-v1', 'rg', '-n', '-A', '28',
    'theorem lemma_2_31|theorem support_gap',
    ROOT/'BanditRLProof/OnlineSubgradientDescent.lean', ROOT/'BanditRLProof/OnlineLinearization.lean')
probe = '''import BanditRLProof.OnlineAdaptiveOSD
import BanditRLProof.OnlineLinearization
#check BanditRL.OnlineSubgradientDescent.lemma_2_31
#check BanditRL.OnlineLinearization.support_gap
#check BanditRL.OnlineGradientDescent.project_spec
#check BanditRL.OnlineAdaptiveOSD.output_succ
#check BanditRL.OnlineAdaptiveOSD.output_mem
#check BanditRL.OnlineAdaptiveOSD.energy_succ
#check BanditRL.OnlineAdaptiveOSD.energy_nonneg
#check BanditRL.OnlineAdaptiveOSD.eta_eq_energy
#check Real.sqrt_pos
#check Real.sqrt_le_sqrt
#check Finset.sum_le_sum
#check Finset.sum_nonneg
'''
write(RUN/'ActualStepAPIProbeV1.lean', probe)
code, out = capture('actual-step-API-probe-v1', 'lake', 'env', 'lean', RUN/'ActualStepAPIProbeV1.lean')
print(out, flush=True)
capture('actual-step-retrieval-record-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'retrieval-record', '--task', TASK, '--query', 'Same-run inclusive-energy projected support one-step with zero skip',
    '--candidate', 'BanditRL.OnlineSubgradientDescent.lemma_2_31',
    '--candidate', 'BanditRL.OnlineLinearization.support_gap',
    '--candidate', 'BanditRL.OnlineAdaptiveOSD.energy_nonneg',
    '--rejection', 'BanditRL.OnlineSubgradientPolicy.one_step=Exogenous step sequence and no zero-feedback skip; adapt shared geometric chain instead',
    '--compiled-scratch', RUN/'ActualStepAPIProbeV1.lean',
    '--provenance', 'Actual local declaration/memory/source windows and pinned compiler API TYPE probe; API availability only, not new theorem BODY/source acceptance',
    '--output', RUN/'actual-step-retrieval-native-RAW-v1.jsonl')
print('Actual pinned one-step API retrieval recorded before tactics.', flush=True)
