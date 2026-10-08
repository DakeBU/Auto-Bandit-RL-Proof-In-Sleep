from common_v1 import *

baseline_fixed(mutable=['MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl'])
assert load(RUN / 'draft-typecheck-v2-exit.json')['actual_exit'] == 0
audit = []
expected_new = [t['name'] for t in load(ROOT / 'docs/contracts/online-completed-causal-v1/targets-v1.json')['targets']]
for name in ['bandit_paper_cards','bandit_scenario_cards','bandit_textbook_cards',
             'proof_weapon_cards','local_leaf_cards','local_lean_declarations']:
    p = ROOT / 'research-wiki/retrieval-index' / (name + '.json')
    old = load(RUN / 'baseline' / ('retrieval-' + name + '.raw'))
    current = load(p)
    old.pop('generated',None)
    current.pop('generated',None)
    added = []
    if name == 'local_lean_declarations':
        previous = old['declarations']
        now = current['declarations']
        keep = {r['full_name'] for r in previous}
        added = [r for r in now if r['full_name'] not in keep]
        assert [r for r in now if r['full_name'] in keep] == previous
        assert [r['full_name'] for r in added] == expected_new
        current['declarations'] = previous
    assert current == old, name
    audit.append(dict(path=p.as_posix(), before_sha256=sha(RUN / 'baseline' / ('retrieval-' + name + '.raw')),
        current_sha256=sha(p), only_generated_timestamp_and_exact_prior4_additions=True, actual_added=added))
write(RUN / 'draft-retrieval-scope-audit-v1.json', dict(rows=audit,
      exact_prior_completed4_scanner_entries_added=True, current_new_kernel_public_entries=0,
      scanner_not_compile_evidence=True, old_entries_order_preserved=True))
assert len(load(CONTRACT / 'chapter-one-source-ledger-draft-v1.json')['original16_source_objects']) == 16
assert load(CONTRACT / 'chapter-one-source-ledger-draft-v1.json')['required_proof_leaf_total'] is None
write(RUN / 'retrieval-route-v1.json', dict(
    reused_local_parents=[dict(name='BanditRL.OnlineLearning.independent_private_seed_pair',
       purpose='Regroup environment/past tape/current draw independence'),
       dict(name='BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess',
       purpose='Actual all-horizon generated feasible finite-history policy expected-fixed producer')],
    exact_mathlib_sources=raw_index([ROOT / '.lake/packages/mathlib/Mathlib' / rel for rel in [
       'Probability/Kernel/Representation.lean','Probability/Kernel/CondDistrib.lean',
       'Probability/Independence/InfinitePi.lean','Probability/Independence/Basic.lean',
       'Probability/Kernel/Composition/MeasureCompProd.lean','Data/Fin/Tuple/Basic.lean']]),
    exact_parent_raw=raw_index([ROOT / 'BanditRLProof/OnlineGuessingRandomizedIID.lean',
       ROOT / 'BanditRLProof/OnlineGuessingIIDBenchmark.lean']),
    cli_declared_sampler_absent_before_work=True,
    no_new_dependency_or_toolchain=True, general_product_map_helper='mathlib-candidate if new',
    decision='adapt_existing single-step kernel sampling and IID producer; new_route_local actual finite causal recursion and law compatibility',
    source_theorem_count_claim=0, current_kernel_proofs=0))
write(RUN / 'contract-mutable-scope-v1.json', dict(
    contract_version=2, immutable_context=(CONTRACT / 'context-v2.lean.txt').as_posix(),
    immutable_context_sha256=sha(CONTRACT / 'context-v2.lean.txt'),
    immutable_headers_sha256=sha(CONTRACT / 'targets-v1.lean.txt'),
    task_metadata_append_only=[directory+'/'+TASK+'.md' for directory in
       ['tasks','proof-obligations','conversion-windows','proof-blueprints']],
    own_journals_append_only=['runs/trials.jsonl','runs/lifecycle_sessions.jsonl'],
    own_run_and_contract_new_version_evidence=True,
    proving_scope=[PUBLIC.relative_to(ROOT).as_posix(), CANARY.relative_to(ROOT).as_posix()],
    root_reader_contribution_manifest_changes_require_separate_body_future_review=True,
    global_frontier_and_lifecycle_memory_immutable=True,
    current_new_body_count=0, terminal_hash_edit_requires_new_contract_review=True))
write(RUN / 'contract-reader-plan-v1.md',
      'After actual public bodies, separate BODY source review must approve exact reader/source-card/5-note proposal, actual parent edges and precise root/Test import additions before publication. Actual combined Lean/root/Tests/fullharness, selected proof VALUE audit/axioms, statement fences, own shadow, both contributor bases and clean local site required; MathJax errors including red commands and actual original pixels need distinct review. Same shared declaration registry; preserve all existing entries/IDs/URLs/book owners and original source16/null. No current Lean-verified claim for this draft package.\n')
files = [CONTRACT / p for p in ['source-card-v1.json','source-intent-v1.md','context-v1.lean.txt','context-v2.lean.txt',
         'targets-v1.lean.txt','targets-v1.json','targets-v2.json','dependency-dag-v1.json','semantic-signature-v1.json',
         'reader-requirements-v1.json','canary-plan-v1.md','chapter-one-source-ledger-draft-v1.json']]
files += [RUN / p for p in ['00_context.md','10_director-v1.md','11_architect-v1.md','12_worker-v1.md',
          'common_v1.py','prepare-draft-v1.py','repair-draft-context-v2.py','prepare-blind-packet-v1.py',
          'prepare-contract-review-v1.py','draft-typecheck-v1.lean','draft-typecheck-v1.log','draft-typecheck-v1-exit.json',
          'draft-typecheck-v2.lean','draft-typecheck-v2.log','draft-typecheck-v2-exit.json','draft-context-repair-v2.json',
          'draft-baseline-v1.json','draft-retrieval-scope-audit-v1.json','retrieval-route-v1.json','contract-mutable-scope-v1.json',
          'contract-reader-plan-v1.md','memory_digest.md','retrieval_index.md','neutral-context-and-statements-v1.lean.txt',
          'neutral-input-instructions-v1.md','neutral-renaming-bindings-v1.json',
          'blind-reconstruction-v1.md','blind-receipt-v1.json','source-pdf13-v1.png','source-pdf13-text-v1.txt',
          'source-pdf15-v1.png','source-pdf15-text-v1.txt']]
files += list((RUN / 'prior-delivery-and-retrieval').iterdir())
files += [RUN / (label + suffix) for label in ['draft-new-task-v2','draft-blueprint-v2','draft-lifecycle-v2',
          'draft-reference-index-v2','draft-search-kernel-v2','draft-search-sampler-v2','draft-search-actual-parent-v2']
          for suffix in ['.log','-exit.json']]
files += [ROOT / r['path'] for r in load(RUN / 'draft-baseline-v1.json')['rows']]
files += [ROOT / directory / (TASK+'.md') for directory in ['tasks','proof-obligations','conversion-windows','proof-blueprints']]
files += [ROOT / 'research-wiki/retrieval-index' / (name+'.json') for name in
          ['bandit_paper_cards','bandit_scenario_cards','bandit_textbook_cards','proof_weapon_cards','local_leaf_cards','local_lean_declarations']]
rows = raw_index(files)
write(RUN / 'source-contract-review-inputs-v1.json', dict(rows=rows, fixed_input_count=len(rows),
      phase='draft contextv2 five exact unchanged terminal headers; no public theorem bodies',
      contract_version=2, original16_source_objects=16, required_proof_leaf_total=None,
      chapter_complete=False, goal_complete=False))
write(RUN / 'source-contract-review-packet-v1.md',
      'Anti-anchored contract review: hash this fixed RAW index before/after; personally reread original source texts and view original cached PNG13/15 (copies, not fresh rendering), compare five proposed declarations+contextv2 against neutral reconstruction in seven slots. Seek mismatches: given behavioral kernels vs arbitrary protocols, existsONE f before ALLnu/horizons, actual finite recursion/no futuretarget/currenttargetindependence not supplied, observation law arbitrary for joint/cond and onlyIIDunit for source performance, globaltypedunit/actionsconsistent, expected FIXED benchmark outsideE, naturalT0, classical/noncomputable selection vs executable sampler, conditional law onlyAE on actual marginal. Core sampler is single-step mathlib reused into same infinite family; that alone does not close the terminal. All5 targets derived infrastructure/adapters, not5printedresults. Original16/null/allotherC1/C2/unenumeratedC3-16/appendices preserved. Current contextv1 compile failed1 only noncomputable measure abbreviations; contextv2 onlyannotations repaired and all5 exact headers unchanged; v2types0 is not a theorem proof.\n\n'
      'Inspect actual baseline, previous PR199 exact4db37 delivery/readonly head repair, scanner deltas only timestamps plus prior4public entries, local API types/pinnedsources/parent contracts/DAG/canary-plan/future reader plan. Do not certify future gates or all-protocol universal reduction. Assess contract-mutable-scope-v1.json and allow only exact frozen new module/context/header proof bodies/helpers, later canaries and own task/journal evidence; no root/readers until separate BODY review, no pins/globalSGB/globalmemory/paper edits. Return ONLY source-contract-review-v1.md and source-contract-receipt-v1.json with actual count/allRAWbeforeafter/reportSHA/verdict/blocking repairs/seven slots/precise permitted scope and retained source delta. Requested Astra/medium, reused distinct automated reviewer disclosed, no human/external/absolute blind/runtime attestation.\n')
print('Contract fixed RAW input count:',len(rows),'no public proof body; separate contract review required.',flush=True)
