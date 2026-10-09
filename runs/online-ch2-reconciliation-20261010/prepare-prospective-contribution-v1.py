from ftl_canary_proof import *
canary_fixed()
proposal=load(RUN/'reader-proposal-v1.json')
names=[n['full_name'] for n in proposal['notes']]
tests=[r['declaration'] for r in load(CANARY/'frozen-headers-draft-v2.json')['rows']]
assert len(names)==13 and len(tests)==8
manifest=dict(schema_version='2.0',id=TASK,route='online-learning/chapter-2',frontier_cell='online-ogd',source_facing=True,
 source=dict(kind='book',title='Online Learning: A Modern Introduction Using Convex Optimization',
   version='arXiv:1912.13213v10 (2026-06-21), SHA '+PDF_SHA,
   anchor='Chapter2 printed11-12/PDF23-24 generic strict-past FTL definition and any feasible first action. Qualified provenance overlays on65overlapping Chapter2 containers, with all required forward mathematics retained.',
   url='https://arxiv.org/pdf/1912.13213v10'),
 target='Construct the actual generic finite-history classical partial FTL selector, exact success/failure and unique-point semantics, feasible initialization and restricted-prefix causality. Reconcile bounded source provenance without chapter completion. '+proposal['boundary'],
 affected_files=['BanditRLProof/OnlineFTLSelector.lean','BanditRLProof.lean','website/content/chapters.json',
   'website/content/readings.json','website/content/highlights.json','docs/contracts/online-book-v1/coverage.json'],
 declarations=names,
 reuse_plan=dict(classification='adapt',decision='new_shared',
   searched_existing=['Actual project source/CLI/header scans and pinned Mathlib declaration retrieval for scalar linear/square FTL, generic source leader comparison, finite sums, IsMinOn and classical minimizer selection; generic-ftl contract/source review evidence. No dependency or toolchain upgrade.'],
   reused_declarations=['Fin.sum_univ_eq_sum_range','Set.IsMinOn','isMinOn_iff','Classical.choose','Classical.choose_spec'],
   new_shared_declarations=names,known_consumers=tests+names[4:],
   planned_consumers=['Source-qualified Chapter2 FTL foundation and later Chapter7 performance contracts, preserving all required future dependencies.'],
   no_duplicate_wrapper=True,
   decision_reason='Existing scalar linear and square-loss strategies do not construct arbitrary-loss strict-past selection. One canonical four-definition/nine-proof interface supplies actual canaries and shared Book graph; no per-book project, arbitrary tie identity or duplicate regret theorem.'),
 reader_contract=dict(source_anchor_visible=True,natural_language_formula_proof=True,hidden_assumptions_visible=True,
   source_vs_lean_delta_visible=True,lean_folded=True,dependencies_visible=True,remaining_boundary_visible=True),
 semantic_roundtrip=dict(required=True,status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',
   source_reviewer='/root/source_reviewer',verdict='accepted-with-explicit-delta',
   remaining_semantic_delta='Distinct source-withheld nine complete generic statements/four-definition and eight complete concrete statements/seven-definition reconstruction, anti-anchored source CONTRACT, production BODY and canary BODY accepted. Requested Astra/medium and reused distinct staged actors, not human/external/absolute blindness or runtime model attestation. Option is an explicit partiality completion; arbitrary X generalizes Euclidean source; no unconditional attainment, executable/measurable optimizer or new regret bound. Recovery none at1 supplies no action and some0 at2 is a separate prefix query, not a valid full interaction after failure. All retained failures and original provenance flags preserved. Exact integration/combined/FINAL/native/delivery are separate gates. '+proposal['boundary']),
 graph_contribution=dict(lean_graph='integration-node',overview_graph='updated',functor_hypergraph='none-found-with-reason',
   functor_reason='Generic restricted-prefix selection is a shared optimization interface; no new certified cross-setting transport or functor is proved.',
   focus_targets=names,
   visual_review='24actual selected compiled values:13production,8publicTests,3privateTesthelpers;11separately selected conjunction branches. Shared registry must preserve all11041completeoldnodeobjects and add exactly13canonicalIDs to11054, excluding Test/generatedTest. Actual shared registry/site/pixels are later required gates. Counts are neither proof necessity, full transitive graph nor source obligation denominator.',
   edge_semantics='formal-solid; overlays-dashed'),
 progress_updates=dict(teaching_route='updated: online-ogd only, one module/goal/completion suffix, one source-qualified FTL card and13canonical declaration notes. Preserve all old links/notes and other Books.',
   banditrlwiki='no-change-with-reason: generic deterministic FTL foundation does not alter Bandit settings or policy guarantees.',
   results_ledger='no-change-with-reason: no completed chapter or global route milestone; this bounded foundation/reconciliation has its own scoped task ledger.',
   roadmap='updated: Chapter2 remains partial/null with8requiredforwardcontainersopen,6futuremathematicalclaimsrequired/open/unenumerated, explicit bounded provenance and current source-join candidate; Chapter1 and Chapters3-16 unchanged; globalSGB untouched.',
   website_surfaces=['website/content/chapters.json','website/content/readings.json','website/content/highlights.json']),
 truth_boundary=proposal['boundary'],
 verification=dict(focused_checks='Nine frozen production BODYs and eight complete canary BODYs genuinely compile.13production and8completepublicTest probes/standard axiom brackets;17nativeheaderfences and safe-verifies, actual24VALUEgraph and11selectedconjuncts. Frozen definitions/context and statements unchanged; failures retained.',
   bandit_check='Required combined root/Tests/full harness/contributor/shadow gates. Actual results recorded separately as generated in this run; not asserted passed at integration-plan freeze.',
   site_build='Required isolated local lean-verified build only after genuine combined Lean gate. Generated website/_site untouched. No deployed/live claim.',
   site_check='Required actual shared registry identity and complete old-object preservation, all new source-qualified readers/formulas/folded statements/proofs, browser/original pixels and separate FINAL.',
   independent_review='Production BODY/canary CONTRACT/bounded R2-R4 provenance review and separate eight-canary BODY review are accepted-with-explicit-delta; exact integration plan, FINAL/native/post-native/delivery are distinct later evidence.',
   owned_test_files=['Tests/OnlineFTLSelectorCanary.lean'],owned_test_root_files=['Tests.lean']),
 contributor=dict(name='Codex for Ji Cheng',role='Formalizer with distinct reused staged automated decoder and source reviewer'))
write(RUN/'prospective-contribution-v1.json',manifest)
canary_fixed()
print('Prospective scoped contribution prepared; not materialized.',flush=True)
