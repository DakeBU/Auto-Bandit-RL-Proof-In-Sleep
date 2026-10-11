from common import *
public = ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean'
bootstrap_review = RUN/'bootstrap-BODY-review-v1.json'
assert sha(public) == load(bootstrap_review)['production_sha256']
frontier = dict(
    package=TASK, state='open proving frontier; compiled semantic-reviewed dependencies, no package acceptance',
    branch=BRANCH, base=BASE, production_sha256=sha(public),
    required_parent=dict(name='BanditRL.OnlineAdaptiveOSD.regret_bound',
        raw_header_sha256=sha(CONTRACT/'algorithm-regret_bound-header-draft-v1.lean.txt'),
        BODY_present=False, closed=False),
    locally_closed_dependencies=[
        dict(family='nonnegative weighted potential', BODY='compiled and distinct reviewed',
            canary='full locally compiled and distinct reviewed', combined_gates='pending'),
        dict(family='actual joint causal state recurrence and strict-past state prefix',
            BODY='compiled and distinct reviewed', proof_count=2,
            review_sha256=sha(RUN/'causal-state-BODY-review-v1.json')),
        dict(family='same-run energy, full-history feasibility, finite losses and shared lawful-policy adapter',
            BODY='five sequential actual focused builds, full public/axiom/fence/VALUE checks, distinct reviewed',
            proof_count=10, source_result_count='not ten printed results', review_sha256=sha(bootstrap_review))],
    dependency_frontier=dict(stage='seven exact actual one-step dependency headers await CONTRACT review',
        source_neutral_decode='complete, three two-conjunct conclusions',
        BODY_present=False, fingerprints_sha256=sha(CONTRACT/'actual-step-fingerprints-draft-v1.json')),
    remaining_required=['actual zero/nonzero-step proofs', 'same-run all-T/nonnegative-D negative-terminal regret',
        'alpha1 Eq4.4 and alpha sqrt2/2 Theorem4.14 source-convex/canonical specializations',
        'separately reviewed infimum and attainment benchmark', 'nondegenerate actual algorithm canaries',
        'root/Tests/full harness/axioms/registry/reader/shadow/site/FINAL/native/delivery',
        'whole Chapter2 remaining source obligations; Chapters3-16 unenumerated; whole Goal active'],
    publication='No new commit/push/PR/merge/deployment in this package; old PR217 remains stacked dependency',
    preservation='Old accepted headers and baseline code/global SGB unchanged; .lake/Git stores/worktree preserved')
write(RUN/'causal-frontier-v2.json', frontier)
write(RUN/'memory-digest-v2.md', '''# Local staged digest v2

The causal algorithm is an actual single Nat.rec over finite history × observed energy. state_succ and strict-past state_prefix are compiled and separately BODY-reviewed under fixed common external V,alpha,D,x1,p; no exogenous eta equality premise. Ten bootstrap BODYs now compile in five dependency-ordered groups, with full generic applications, standard axiom lists, frozen fences and direct compiled parents separately verified and semantically reviewed. This lowers the required parent proof frontier to actual zero/nonzero one-step inequalities; the parent remains absent/unproved. Arbitrary p legality is distinct from proper/support finiteness, and the shared canonical selector law is used rather than duplicated.

Next seven exact one-step headers include THREE complete double conjunctions, not the two informally mentioned in root's decoder request. The exact neutral packet always contained all three; decoder detected/corrected the counting description, no contract mutation. D0 geometric helper needs feasibility but no loss/support regularity; it asserts totalized real equality and norm0, never finite EReal values. Leading/all-zero feedback must stay valid under total division and explicit skip. Existing source support_gap was actually retrieved, but the shared lemma_2_31's eta1 component suffices without importing a second linear-policy interface.

No current package combined root/Tests/harness/site gate or PR delivery yet. All prior source reading retraction/minimum repair remain separate. This is a run-local memory digest, not promoted certified global memory or a source/chapter completion claim.
''')
for folder in ['proof-obligations', 'conversion-windows', 'research-wiki/retrieval-index']:
    path = ROOT/folder/(TASK+'.md')
    before = path.read_bytes()
    write(RUN/('before-causal-frontier-v2-'+folder.replace('/','-')+'.md'), before)
    addition = '''

## Current causal dependency frontier v2

Latest authoritative snapshot: runs/online-ch2-adaptive-osd-20261010/causal-frontier-v2.json; older pending descriptions above are historical. The actual joint state recurrence and whole-state strict-past theorem, plus ten same-run energy/feasibility/finite-loss/lawful-policy bootstrap proofs, are locally compiled and distinct BODY-reviewed. Ten bootstrap interfaces are not ten printed results. Actual named declarations, full generic applications, standard axioms, fences and direct compiled VALUE parents are recorded separately in this RUN. The frozen negative-terminal parent regret_bound is still absent/unproved; its dependency frontier is now seven exact zero/nonzero step headers awaiting CONTRACT review. Parent source terminal and all degenerate cases remain required. Next proofs do not receive desired regret/stability as hypotheses. No new context/import/helper is authorized.

This is one open causal OSD package on the exact stacked PR217 base; full root/Tests/harness/registry/reader/site/native/delivery gates and actual algorithm canaries remain pending. Global SGB/frontier and old accepted contracts are unchanged. No new PR/merge/live claim. Whole Chapter2 remains partial and total Goal active.
'''
    path.write_bytes(before.rstrip(b'\n')+addition.encode('utf8'))
print('Actual causal frontier and local digest recorded; no accepted/Goal closure.', flush=True)
