from common_nonsmooth_publication_v2 import *

fixed()
inventory=load(CONTRACT/'complete-source-reconciliation-draft-v3.json')
source=next(r for r in inventory['rows'] if r['source_id']=='additional:absolute-hinge-convex-nondifferentiable-introduction')
targets=load(CONTRACT/'nonsmooth-targets-draft-v1.json')['targets']
write(CONTRACT/'nonsmooth-source-to-public-binding-v1.json',dict(
    source_inventory='docs/contracts/online-ch2-chapter-audit-v1/complete-source-reconciliation-draft-v3.json',
    source_inventory_sha256=sha(CONTRACT/'complete-source-reconciliation-draft-v3.json'),
    source_container_id=source['source_id'],source_pages=source['source_pages'],
    source_families=2,derived_public_proofs=3,
    exact_current_declarations=[dict(name=t['declaration'],statement_hash=t['statement_hash'],
        full_production_scope_and_BODY_sha256=sha(PUBLIC)) for t in targets],
    exact_canary_contract_sha256=sha(CONTRACT/'nonsmooth-canary-contracts-v2.json'),
    exact_canary_module_sha256=sha(CANARY),
    phase='Finite exact terminals compiled and production/canary/source qualification/reader BODY scope reviewed; final integrated package acceptance and delivery pending',
    independent_source_contract_review_sha256=sha(RUN/'source-contract-repair-review-v1.json'),
    independent_production_BODY_review_sha256=sha(RUN/'nonsmooth-production-BODY-review-v1.json'),
    independent_canary_BODY_review_sha256=sha(RUN/'nonsmooth-canary-publication-review-v1.json'),
    independent_reader_repair_review_sha256=sha(RUN/'nonsmooth-reader-repair-review-v2.json'),
    actual_public_kernel_receipts=[sha(RUN/'nonsmooth-all-public-values-v1.json'),sha(RUN/'nonsmooth-canaries-public-values-v1.json')],
    frozen_source_inventory_v3_not_mutated=True,
    source_delta='Source center10 generalized to every real c. Hinge exact pointwise/global loci derived for arbitrary real labels; independently reviewed zero-normal qualification retained with pinned source sentence. No author-endorsed erratum or source alteration.',
    progress_measure='Three fixed terminal types actually closed from ready dependencies; two source families served. Counts of retrieved declarations, overlapping source containers and registry nodes are not chapter progress denominators.',
    chapter_mandatory_proof_total=None,chapter_complete=False,whole_Goal_status='ACTIVE',
    required_forward_dependencies_unchanged=True,main_live_updated=False))
fixed()
print('Frozen source paragraph joined to actual three unchanged public VALUES/two families without mutating inventory or claiming chapter completion.')
