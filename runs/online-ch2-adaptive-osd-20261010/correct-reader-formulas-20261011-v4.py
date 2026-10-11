from common import *
import copy,json
reader=load(RUN/'reader-integration-proposal-20261011-v3.json')
old=copy.deepcopy(reader)
h=reader['highlights'][0]
extra_math=r'\begin{gathered}\delta_t=\ell_t(x_t)-\ell_t(u),\quad a_t=\|x_t-u\|^2,\\ \delta_t\le\frac{(a_t-a_{t+1})\sqrt{S_{t+1}}}{2\alpha D}+\frac{\alpha D}{2}\frac{\|g_t\|^2}{\sqrt{S_{t+1}}}\quad(D>0),\\ \sum_{t<T}\frac{\|g_t\|^2}{\sqrt{S_{t+1}}}\le2\sqrt{S_T}.\end{gathered}'
h['math']+=' '+extra_math
extra_proof=(' Quantitatively, writing a_t=||x_t-u||^2 and delta_t=ell_t(x_t)-ell_t(u), the D>0 one-step result is delta_t <= (a_t-a_(t+1))*sqrt(S_(t+1))/(2alphaD) + (alphaD/2)*||g_t||^2/sqrt(S_(t+1)). The shared energy theorem gives sum(t<T)||g_t||^2/sqrt(S_(t+1)) <= 2sqrt(S_T), so its scaled contribution is at most alphaD sqrt(S_T). If an inclusive energy is zero, nonnegativity forces the current support to be zero; the totalized 0/0 summand is zero and the actual algorithm skips. No positive-energy premise is added.')
h['proof_idea']+=extra_proof;h['intuition']+=extra_proof
h['lean_notes']+=(' Selected external Mathlib facts in the supporting proof chain: Finset.sum_range_by_parts, Finset.sum_range_sub and Finset.sum_range_sub\' for the signed potential calculation; Real.sqrt_le_sqrt for monotone energy weights. The shared adaptive-energy proof supplies the displayed quantitative energy inequality. These are supporting-chain facts, not an assertion that every named constant occurs directly in the final wrapper VALUE.')
reader['highlights'][1]['lean_notes']+=(' Selected external support in the underlying parameterized proof includes Finset.sum_range_by_parts and range telescoping, with Real.sqrt_le_sqrt for the cumulative-energy weights. The specialization itself applies the actual parameterized theorem and removes its nonnegative residual; this is a selected supporting-chain account, not a full dependency graph.')
reader['highlights'][2]['proof_idea']+=(' The positive-eta image is nonempty with eta=1. The benchmark GLB proof establishes both a lower bound and the greatest-lower-bound direction using the positive optimizer or arbitrarily small mixed-zero objective values; strict decrease alone is not used to prove the infimum. IsGLB.csInf_eq identifies the infimum and Real.sqrt_mul supplies the sqrt(2) factor under nonnegativity.')
reader['highlights'][2]['intuition']=reader['highlights'][2]['proof_idea']
reader['highlights'][2]['lean_notes']+=(' Selected external Mathlib facts: IsGLB.csInf_eq and Real.sqrt_mul; the positive-eta image has witness eta=1. Shared scalar lower-bound, positive gap/argmin and uniqueness facts come from BanditRL.OnlineOptimalStep.lower_bound, distance_energy_argmin and optimal_unique; zero_distance_decreases and zero_energy_decreases distinguish unattained mixed-zero boundaries. These are selected supporting-chain facts, not a necessity or full-graph certificate.')
assert reader['source_cards']==old['source_cards']
write(RUN/'reader-integration-proposal-20261011-v4.json',reader)
plan=load(RUN/'exact-integration-proposal-20261011-v3.json')
for row in plan['rows']:
    if row['path'].endswith('highlights.json'):
        obj=load(row['after_snapshot']);before=load(row['before_snapshot'])
        assert obj['highlights'][-3:]==old['highlights'];obj['highlights'][-3:]=reader['highlights']
        assert obj['highlights'][:-3]==before['highlights']
        ap=RUN/'integration-proposal-snapshots-20261011-v4'/Path(row['after_snapshot']).name
        write(ap,obj);row['after_snapshot']=ap.as_posix();row['after_sha256']=sha(ap)
manifest=load(RUN/'prospective-contribution-20261011-v3.json')
manifest['verification']['independent_review'] += ' New v4 reader proposal makes the quantitative one-step and cumulative-energy proof visible with explicit selected supporting Mathlib facts; exact publication proposal review pending.'
write(RUN/'prospective-contribution-20261011-v4.json',manifest)
plan.update(prospective_manifest=rows([RUN/'prospective-contribution-20261011-v4.json']),reader_proposal=rows([RUN/'reader-integration-proposal-20261011-v4.json']),supersedes=rows([RUN/'exact-integration-proposal-20261011-v3.json']),changes_from_v3='Only three NEW highlight objects: quantitative one-step/energy inequalities, zero-prefix explanation, selected external Mathlib/GLB/argmin facts. Source cards/old objects/pins/Lean unchanged; manifest notes this current proposal.')
write(RUN/'exact-integration-proposal-20261011-v4.json',plan)
sys.path.insert(0,str(ROOT))
from tools.check_contributor_contract import validate_contract
_,errors=validate_contract(RUN/'prospective-contribution-20261011-v4.json')
write(RUN/'prospective-contribution-schema-check-20261011-v4.json',dict(manifest=rows([RUN/'prospective-contribution-20261011-v4.json']),errors=errors))
assert not errors,errors
print('v4 plan SHA '+sha(RUN/'exact-integration-proposal-20261011-v4.json'))
