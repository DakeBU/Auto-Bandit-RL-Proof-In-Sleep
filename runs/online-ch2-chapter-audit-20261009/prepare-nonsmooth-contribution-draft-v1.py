from common_nonsmooth_roots_v1 import *

fixed()
p=load(RUN/'nonsmooth-reader-proposal-v2.json')
names=[t['declaration'] for t in load(CONTRACT/'nonsmooth-targets-draft-v1.json')['targets']]
tests=[t['declaration'] for t in load(CONTRACT/'nonsmooth-canary-contracts-v2.json')['targets']]
g=load(RUN/'nonsmooth-compiled-graph-inspected-v1.json')
c=load(ROOT/'research-wiki/contribution-contracts/ONLINE-C1-CHAPTER-AUDIT-20261009.json')
c.update(id='ONLINE-CH2-NONSMOOTH-20261009',route='online-learning/chapter-2',frontier_cell=p['route'],
    target='Three actual source-derived convexity/differentiability producers for two required introductory nonsmooth families, plus five complementary public canaries. Operative source inventory v3 is accepted as source enumeration only. '+p['boundary'],
    affected_files=['BanditRLProof/OnlineNonsmoothExamples.lean','Tests/OnlineNonsmoothExamplesCanary.lean','BanditRLProof.lean','Tests.lean',
        'website/content/chapters.json','website/content/readings.json','website/content/highlights.json'],declarations=names)
c['source'].update(anchor='Section2.2 opening paragraph, printed16/PDF28: shifted absolute center10 and labelled hinge. Exact pointwise/global criteria are derived generalizations, not three numbered source theorems.',
    version='arXiv:1912.13213v10,2026-06-21; SHA '+PDF_SHA)
c['reuse_plan'].update(classification='adapt',decision='adapt_existing',
    searched_existing=['Actual534-public Online declaration retrieval plus current native headers/full module hashes; exact prior review join; actual pinned norm/abs, affine convex/max, full hinge support and singleton differentiability APIs. No duplicate per-Book foundations.'],
    reused_declarations=['convexOn_univ_norm','not_differentiableAt_abs_zero']+['BanditRL.OnlineConvex.'+n for n in
        ['affine_convex','convexExtended_coe_iff','example_2_27','theorem_2_22','sourceDifferentiableAt_regular']],
    new_shared_declarations=names,known_consumers=[names[2]]+tests,
    planned_consumers=['Required Chapter2 source audit of introductory nonsmooth examples'],
    decision_reason='Construct actual convexity, every-point kink iff and global zero-normal iff from existing complete support/derivative producers. The labelled global direction genuinely constructs a margin witness; no supplied support/stability conclusion or wrapper-only endpoint.')
c['semantic_roundtrip'].update(status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',source_reviewer='/root/source_reviewer',
    verdict='accepted-with-explicit-delta',remaining_semantic_delta='Distinct production CONTRACT/source qualification/BODY and five canary CONTRACT/BODY accepted at unchanged complete source hashes. Reader v1 rejected solely for absolute intuition; exact v2 fix under separate narrow review. Staged automated roles requested Astra/medium; no human/external/absolute-blind/runtime attestation. '+p['boundary'])
c['graph_contribution'].update(lean_graph='new-node',overview_graph='updated',functor_hypergraph='none-found-with-reason',
    functor_reason='Same-source static differentiability examples and an explicit scalar-normal substitution; no new cross-setting transport or certified categorical functor.',
    focus_targets=names,visual_review='Actual selected13nodes/1773coalesced TYPE_VALUE presences and13required direct VALUE pairs. Shared registry and actual current reader pixels remain future independent gates; no import-as-implication claim.')
c['progress_updates'].update(teaching_route='planned exact publication: one source-qualified card/three new notes and one module glob on existing singleton-differentiability route, preserving all old cards/IDs/links/formulas.',
    banditrlwiki='no-change-with-reason: static convex analysis examples do not change any Bandit setting or policy.',
    results_ledger='no-change-with-reason: finite package does not accept Chapter2; source inventory and OWN candidate milestones recorded separately with mandatory proof totalnull.',
    roadmap='no-change-with-reason: whole16GoalACTIVE; Chapter2 partial, Chapters3-16 unenumerated; all forward references required/open and global SGB unchanged.',
    website_surfaces=['website/content/chapters.json','website/content/readings.json','website/content/highlights.json'])
c['truth_boundary']=p['boundary']+' Source unrestricted hinge sentence is retained with a separately reviewed zero-normal qualification, not author endorsement. Arbitrary real labels, genuine ambient derivatives and zero dimension remain explicit.'
c['verification'].update(focused_checks=['Actual three production/five canary complete public VALUE witnesses; eight standard-only axiom records; eight unchanged native header/safe guards (safe-verify does not compile); actual13required compiled VALUE pairs. Failed compiler/receipt/schema/reader attempts separately retained.'],
    bandit_check='Current exact root/Test imports applied after distinct BODY approval; actual combined root/Tests build in progress. Full harness pending.',
    site_build='Pending fresh applicable complete Lean gate and local isolated output; no generated _site edit or deployment.',
    site_check='Pending all old shared registry IDs/URLs/source binding preservation plus exactly three new shared proof nodes and current reader pixels.',
    independent_review='Distinct staged automated source CONTRACT/BODY and canary CONTRACT/BODY reports are bound in current RUN. Reader correction, FINAL/native/delivery remain pending; no absolute-blind/human/external/runtime model attestation.',
    owned_test_files=['Tests/OnlineNonsmoothExamplesCanary.lean'],owned_test_root_files=['Tests.lean'])
write(RUN/'nonsmooth-contribution-manifest-draft-v1.json',c)
write(RUN/'nonsmooth-retrieval-index-draft-v1.md',
    '# ONLINE-CH2-NONSMOOTH-20261009\n\n'+p['boundary']+'\n\n'
    'Source/statement freeze: docs/contracts/online-ch2-chapter-audit-v1/nonsmooth-stabilized-v1.json; operative chapter source enumeration version3. '
    'Three exact actual public production bodies; five frozen-v2 complementary canary bodies; complete public VALUE kernels and standard-only axioms;13selected compiled nodes/1773coalesced TYPE_VALUE presences/13prespecified direct VALUE pairs. '
    'Actual BODY acceptances are distinct from full package/chapter acceptance. Reader v1 rejected for one incorrect absolute intuition, v2 repair review pending. '
    'Current root/Test appends use independent exact RAW-prefix approval. Root/Tests compilation in progress; full harness, shadow, contributor, shared registry/readers/site/pixels, FINAL/native/delivery pending. '
    'Whole Goal ACTIVE; no main/live, merge, deployment or worktree retirement.\n')
fixed()
print('Own contribution/retrieval drafts prepared; no unreviewed canonical reader or manifest mutation.')
