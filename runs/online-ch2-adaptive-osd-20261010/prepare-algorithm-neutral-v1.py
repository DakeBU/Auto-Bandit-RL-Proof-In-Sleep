from common import *
import re
context = (CONTRACT/'algorithm-definition-context-draft-v2.lean.txt').read_text(encoding='utf8')
headers = [(CONTRACT/('algorithm-'+name+'-header-draft-v1.lean.txt')).read_text(encoding='utf8')
    for name in ['state_succ', 'regret_bound']]
renamings = [('BanditRL.OnlineAdaptiveOSD', 'NeutralDynamics'), ('state', 'A'), ('history', 'H'),
    ('energy', 'Q'), ('output', 'X'), ('selected', 'G'), ('eta', 'R'),
    ('LegalFeedback', 'L'), ('regret', 'F'), ('state_succ', 'certificate_one'),
    ('regret_bound', 'certificate_two')]
text = context+'\n'+'\n'.join(h.replace(' := by', '') for h in headers)+'\nend BanditRL.OnlineAdaptiveOSD\n'
for old, new in renamings:
    text = re.sub(r'(?<![\w.])'+re.escape(old)+r'(?!\w)', new, text)
write(CONTRACT/'algorithm-neutral-packet-v1.lean.txt', text)
write(CONTRACT/'algorithm-neutral-renaming-v1.json', dict(renamings=renamings,
    packet_sha256=sha(CONTRACT/'algorithm-neutral-packet-v1.lean.txt'),
    shared_import_names_retained='Actual shared types and projection/support semantics required to interpret definitions; related history disclosed, not absolute anonymity.'))
write(CONTRACT/'algorithm-source-card-draft-v1.md', '''# Causal adaptive OSD source card, draft

Pinned Orabona arXiv:1912.13213v10 dated2026-06-21, PDF SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Printed39-40 / PDF51-52, Eq4.4 and Theorem4.14, as necessary Chapter2 forward adaptive-rate dependency. Original PDF52 pixels personally re-read by root in this algorithm drafting round; prior-render file bytes remain SHA7126457ef0e6aaaea40a4de08719efbd1723ef748e0e97f0443c50c7015f7edb. This is a source map, not full Chapter4 inventory or acceptance.

Theorem4.14 assumes a closed nonempty convex V subset R^d of diameter at most D, convex losses R^d ->(-infinity,+infinity] subdifferentiable on V, feasible x1, and OSD with eta_t=sqrt2 D/(2 sqrt(sum_(i<=t)||g_i||²)); do not update when g_t=0. For every u in V, sum_(t=1..T)(ell_t(x_t)-ell_t(u)) <= D sqrt(2 sum_(t=1..T)||g_t||²). The preceding Eq4.4 uses eta_t=D/sqrt(inclusive energy) and gives (3/2)D sqrt(total energy). Source real Euclidean norm and global subgradients, deterministic pathwise full-information losses, zero skip explicit. Source t1..T maps Lean0..T-1; source x_(T+1)=Lean outputT and energyT includes exactly T selected supports.

Proposed stronger parameterized endpoint on the SAME actual causal recurrence is in algorithm-regret_bound-header-draft-v1; alpha>0, D>=0, T arbitrary, coefficient 1/(2alpha)+alpha and negative terminal ||x_T-u||² sqrt(S_T)/(2alphaD). Eight definitions and shared projection/policy types appear in reviewed-for-proposal contextv2. hlegal uses actual supports at played points, SubdifferentiableOn ensures source proper/finite loss semantics; omission of explicit convexity in the support-sufficient generalization needs semantic review. The producer is actual Nat.rec, not a future-energy schedule existence claim.

Source final equality writes sqrt2 times a minimum over eta>0 of D²/(2eta)+eta S/2. That equality's attained-minimum reading needs separate review in minimum-infimum-repair-proposed-v1; no repair is approved or silently applied here. Zero g skip and zero diameter must not be deleted to rescue attainment. Original PDF unchanged. Separately, the alleged missing /2 on printed14 was rejected and withdrawn; no source erratum for that correct formula.
''')
write(CONTRACT/'minimum-infimum-repair-proposed-v1.md', '''# Separate proposed repair: attainment at degenerate benchmark coefficients

Pinned source is unchanged. Theorem4.14 printed40/PDF52 displays D sqrt(2S)=sqrt2 min_(eta>0)[D²/(2eta)+eta S/2], S=sum selected norm². Proposal only, not accepted: interpret the displayed optimum as infimum for all D,S>=0, retaining actual attained minimum when D,S>0, and distinguish the bothzero case.

Audit: D1,S0 gives B(eta)=1/(2eta)>0, B(2eta)<B(eta), tending toward0 with no positive minimizer. D0,S1 gives B(eta)=eta/2>0, B(eta/2)<B(eta), also infimum0 unattained. D=S0 gives constant0, attained at every eta>0. D,S>0 gives unique eta=D/sqrtS, valueD sqrtS. These are compatible source situations: constant losses on a nontrivial feasible domain have S0,D>0; a singleton feasible set can have legal nonzero ambient affine supports and D0,S>0. Source skips zero supports, not the entire boundary. Thus adding D>0,S>0 to the whole regret theorem would weaken its stated regimes and is not proposed.

Exact future Lean benchmark should reuse OnlineOptimalStep.upperBound with A=D²,B=S and existing lower_bound/positive argmin/zero decrease/zero_coefficients; prove IsGLB of positive-eta image for all D,S>=0, plus exact attainment classification and source factor sqrt2. This benchmark is algebra on actual energy S when linked, not an algorithm achieving every future-fixed optimum. It requires distinct repair review and exact header freeze before new production proof; no existing accepted contract or original source is changed by this proposal.
''')
capture('algorithm-prefix-API-retrieval-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'list-lean-decls', 'OnlineSubgradientPolicy.history_prefix', '--statement')
capture('algorithm-optimum-API-retrieval-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'list-lean-decls', 'OnlineOptimalStep', '--statement')
print('Two complete algorithm propositions plus exact definitions neutralized; source/minimum repair separately proposed.', flush=True)
