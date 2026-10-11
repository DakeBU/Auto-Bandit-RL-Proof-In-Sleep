from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash
public = ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean'
f = load(CONTRACT/'actual-step-stabilized-v1.json')
headers = f['exact_headers']
for name, row in headers.items():
    assert statement_hash(lean_declaration_header(public, name)) == row['normalized_statement_hash']
assert public.read_bytes() == (RUN/'actual-step-group-D-body-attempt-v2.lean.txt').read_bytes()
assert load(RUN/'actual-step-direct-parent-checks-v1.json')['all_expected_found']
assert load(RUN/'actual-step-group-D-focused-build-v2.json')['actual_exit'] == 0
parent = CONTRACT/'algorithm-regret_bound-header-draft-v1.lean.txt'
assert sha(parent) == '09461432a5218714d00b5de604eca269cd3c027c6f3a9a49e6176a2d1955a2c1'
raw = parent.read_text(encoding='utf8').rstrip()
statement = raw[len('theorem regret_bound '):-len(':= by')].strip()
probe = '''import BanditRLProof.OnlineAdaptiveOSD
noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace BanditRL.OnlineAdaptiveOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance : DecidableEq E := Classical.decEq E
#check BanditRL.OnlineAdaptivePotential.weighted_potential_sum
#check BanditRL.OnlineAdaptiveEnergy.norm_sq_sum_div_sqrt_prefix
#check BanditRL.OnlineAdaptiveOSD.one_step
#check BanditRL.OnlineAdaptiveOSD.energy_eq_sum
#check BanditRL.OnlineAdaptiveOSD.energy_step_mono
#check BanditRL.OnlineAdaptiveOSD.output_mem
#check BanditRL.OnlineAdaptiveOSD.regret_zero_diameter
'''
probe += '#check (∀ '+statement.replace(' :\n', ',\n', 1)+')\n'
probe += 'end BanditRL.OnlineAdaptiveOSD\n'
write(RUN/'ParentDependencyTypeProbeV1.lean', probe)
code, out = capture('parent-dependency-type-probe-v1', 'lake', 'env', 'lean', RUN/'ParentDependencyTypeProbeV1.lean')
print(out, flush=True)
write(CONTRACT/'parent-proving-window-request-v1.md', '''# Reopen the unchanged parent for actual proving

The frozen regret_bound header RAW09461432a5218714d00b5de604eca269cd3c027c6f3a9a49e6176a2d1955a2c1 and normalizedcbe0f23c66a8cfe9ac979b3d7c04b9b1486e0843eacd2dae250dc2d07ce92011 are unchanged since the reviewed original causal contract. Eight recursive definitions are also unchanged. No new target, weakened terminal or new assumptions are requested. Original full neutral reconstruction and source CONTRACT review remain explicitly staged evidence, not fresh source blindness.

Two separate decisions requested: (1) existing seven actual one-step dependency BODYs, including current lint-cleaned Dv2, are semantically correct with all frozen seven headers; (2) IF those BODYs are favorable and source/parent dependency audit is favorable, open only the exact ONE parent regret_bound BODY append in OnlineAdaptiveOSD.lean, preserving every current prefix byte except moving final namespace end. No extra helper/import/context/source-target/benchmark/source-wrapper/canary/root/reader/registry/global edits. Own evidence/lifecycle files may record actual proving/repair/candidate attempts. Any header change requires versioned contract/neutral review, never a BODY tactic repair.

Mathematical route and fixed constants: for D>0,T>0, let a_t=norm(X_t-u)^2 and w_t=sqrt(Q_(t+1))/(2alphaD). Actual energy_step_mono makes w nonnegative/nondecreasing, actual output_mem plus diameter bounds a_t<=D². Sum the actual one_step for the same selected trajectory. The locally compiled zero-weight weighted_potential_sum bounds the distance-change sum by (D²-a_T)*sqrt(Q_T)/(2alphaD), retaining the negative terminal. Existing OnlineAdaptiveEnergy.norm_sq_sum_div_sqrt_prefix, rewritten using actual energy_eq_sum, bounds the observed energy sum by 2sqrt(Q_T). Multiply by alphaD/2 and combine to coefficient (1/(2alpha)+alpha)D. No cancellation of sqrt(Q_T) is used, so all-zero/leading-zero energy remains valid. T0 uses the actual zero state and empty sum. D0 uses the proved feasible singleton/zero-real-regret adapter; total division in the unchanged parent then gives RHS0 even if selected vectors are nonzero. No desired regret/stability premise enters.

Parent supports actual-prefix legal feedback, not an assumed off-path OracleLaw, retains current-source properness/global supports and the explicitly reviewed support-sufficient generalization. Canonical/source-convex Eq4.4/Theorem4.14 specializations and the separate benchmark/canaries remain required future windows. Actual parent proof, generic public and axioms/fences/VALUE evidence, distinct BODY review and all full-package/publication gates remain separate. This transition does not accept a source theorem, package, chapter or Goal.
''')
write(RUN/'director-parent-window-v1.md', '''Review actual one-step BODYs separately, then authorize only the unchanged already-frozen all-T,D>=0 negative-terminal regret_bound. True frontier has lowered from actual causal state to actual one-step; finish same-run summation rather than introducing a consumer premise. Preserve zero-feedback/zero-energy/zero-diameter branches and exact source/support information boundary.
''')
write(RUN/'architect-parent-window-v1.md', '''All prerequisites locally compile: genuine causal state and feasible history, proper support finiteness/lawful canonical adapter, current zero/nonzero projection one_step, zero-diameter adapter, nonnegative weighted potential and same-run observed-energy bound. T0 and D0 handled before positive-D/T sum; use w=sqrt(inclusive energy)/(2alphaD), a=distance²,C=D², source energy sum2sqrt(total). ONE finite parent BODY window after favorable dependency BODY+CONTRACT verdict, no new declarations/imports. Parent terminal residual remains explicit; benchmark/source specialization later.
''')
files = [PDF, public, PUBLIC, ROOT/'Tests/OnlineAdaptivePotentialCanary.lean',
    ROOT/'BanditRLProof/OnlineAdaptiveEnergy.lean', ROOT/'BanditRLProof/OnlineSubgradientDescent.lean',
    ROOT/'BanditRLProof/OnlineSubgradientPolicy.lean']
files += [Path(row['path']) for row in headers.values()]
files += [CONTRACT/n for n in [
    'algorithm-definition-context-draft-v2.lean.txt', 'algorithm-regret_bound-header-draft-v1.lean.txt',
    'algorithm-fingerprints-draft-v1.json', 'algorithm-stabilized-v1.json',
    'algorithm-source-card-draft-v1.md', 'algorithm-assumption-delta-draft-v1.md',
    'algorithm-neutral-packet-v1.lean.txt', 'actual-step-stabilized-v1.json',
    'actual-step-fingerprints-draft-v1.json', 'actual-step-neutral-packet-v1.lean.txt',
    'actual-step-source-card-draft-v1.md', 'parent-proving-window-request-v1.md']]
files += [RUN/n for n in [
    'actual-step-CONTRACT-review-v1.md', 'actual-step-CONTRACT-review-v1.json',
    'actual-step-blind-decoder-v1.md', 'actual-step-blind-decoder-v1.json',
    'worker-actual-step-route-v1.md', 'prove-actual-step-v1.py', 'verify-actual-step-v1.py',
    'actual-step-dead-tactic-cleanup-v2.json', 'clean-actual-step-dead-tactic-v2.py',
    'actual-step-group-D-body-attempt-v2.lean.txt', 'actual-step-group-D-focused-build-v2.json',
    'ActualStepPublicProbeV1.lean', 'actual-step-public-probe-v1.json',
    'ExportActualStepValuesV1.lean', 'actual-step-value-export-v1.json',
    'actual-step-values-native-v1.json', 'actual-step-direct-parent-checks-v1.json',
    'actual-step-named-declarations-v1.json', 'actual-step-compiled-trial-v1.json',
    'bootstrap-BODY-review-v1.md', 'bootstrap-BODY-review-v1.json',
    'algorithm-blind-decoder-v1.md', 'algorithm-blind-decoder-v1.json',
    'algorithm-CONTRACT-review-v1.md', 'algorithm-CONTRACT-review-v1.json',
    'potential-BODY-and-canary-CONTRACT-review-v1.md', 'potential-BODY-and-canary-CONTRACT-review-v1.json',
    'potential-canary-BODY-minimum-review-v1.md', 'potential-canary-BODY-minimum-review-v1.json',
    'ParentDependencyTypeProbeV1.lean', 'parent-dependency-type-probe-v1.json',
    'director-parent-window-v1.md', 'architect-parent-window-v1.md']]
for letter in 'ABCD':
    files += [RUN/('actual-step-group-'+letter+n) for n in [
        '-body-attempt-v1.lean.txt', '-focused-build-v1.json', '-compiled-local-v1.json']]
for name in headers:
    files += [RUN/('actual-step-'+name+n) for n in ['-fence-native-v1.json', '-safe-verify-v1.json']]
assert all(p.is_file() for p in files)
write(RUN/'actual-step-BODY-parent-window-inputs-v1.json', dict(files=rows(files),
    scope='Separate actual seven dependency BODY verdict and unchanged one-parent proving transition; no parent BODY yet.'))
write(RUN/'actual-step-BODY-parent-window-packet-v1.md', '''# Separate step BODY and parent proving-window review

Independently RAW hash all fixed inputs before/after. First review actual seven BODYs against frozen complete headers/context, all four ordered source snapshots and focused receipts, full generic public applications/axioms/fences/compiled VALUE parents, and minimal Dv2 lint cleanup (v1 was compiler0 with one dead ring, not a proof failure). Verify prior A/B/C bytes unchanged and current source exactly Dv2. Inspect both scaled inequalities and all three conjunctive targets, current legal support/properness, skip with nonzero historical energy, D0 actual feasible points without loss finiteness/legality claims. This is seven dependency interfaces, not seven source results.

Separately inspect unchanged frozen parent, original full neutral reconstruction and reviewed source/assumption deltas, actual readiness of weighted potential/energy/current one-step, and the proposed full mathematical D0/T0/allzeroenergy route in parent-proving-window-request-v1. Only after favorable separate verdicts authorize appending ONE exact regret_bound BODY with current prefix preserved except moved namespace end. No additional headers/helpers/imports/context changes or benchmark/source-wrapper/canary/root/reader/registry/global edits. Parent not yet proved; no approval by merely counting proofs or exit0.

Create-only actual-step-BODY-parent-window-review-v1.md/.json UTF8singleLF in this RUN, two distinct verdicts (step_BODY and parent_contract_transition), blocking repairs or exact single-parent edit window, full RAW/index/report/source/current-production/header/context hashes, truthful source-view/history/actor disclosures and all remaining gates. No theorem tactics/new build/native acceptance requested. Parent BODY/public checks/review and actual algorithm canary, benchmark/source specializations/full combined/publication/FINAL/native/delivery remain required. Chapter and whole Goal open.
''')
print('Actual step BODY plus separate unchanged parent proving-window packet prepared.', flush=True)
