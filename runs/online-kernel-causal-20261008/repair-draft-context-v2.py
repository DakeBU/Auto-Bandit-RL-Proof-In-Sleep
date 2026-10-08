from common_v1 import *

baseline_fixed()
assert load(RUN / 'draft-typecheck-v1-exit.json')['actual_exit'] == 1
old = (CONTRACT / 'context-v1.lean.txt').read_text(encoding='utf8')
new = old.replace('abbrev kernelUniformTapeLaw', 'noncomputable abbrev kernelUniformTapeLaw').replace(
    'abbrev kernelGameLaw', 'noncomputable abbrev kernelGameLaw')
assert new.count('noncomputable abbrev') == 2
assert new.replace('noncomputable abbrev', 'abbrev') == old
write(CONTRACT / 'context-v2.lean.txt', new)
targets = load(CONTRACT / 'targets-v1.json')
targets['version'] = 2
targets['exact_context_sha256'] = sha(CONTRACT / 'context-v2.lean.txt')
targets['headers_file'] = (CONTRACT / 'targets-v1.lean.txt').relative_to(ROOT).as_posix()
targets['original_statement_hashes_unchanged'] = True
write(CONTRACT / 'targets-v2.json', targets)
write(RUN / 'draft-context-repair-v2.json', dict(
    failed_context=(CONTRACT / 'context-v1.lean.txt').as_posix(),
    failed_context_sha256=sha(CONTRACT / 'context-v1.lean.txt'),
    failed_log_sha256=sha(RUN / 'draft-typecheck-v1.log'), failed_actual_exit=1,
    repair='Only noncomputable annotations for infinitePi and prod measure abbreviations; no algorithm or proposition edit.',
    repaired_context_sha256=sha(CONTRACT / 'context-v2.lean.txt'),
    exact_all_five_header_hashes_unchanged=True, original_files_retained=True,
    phase='draft; no stabilized/proving terminal exists yet', proof_progress=False))
prototype = new.rsplit('end BanditRL.OnlineLearning',1)[0]
prototype = prototype.replace('namespace BanditRL.OnlineLearning',
                              'set_option pp.notation false\nset_option pp.universes true\n\nnamespace BanditRL.OnlineLearning',1)
for target in targets['targets']:
    rest = target['header'].split(target['name'].split('.')[-1],1)[1].strip().replace(' :\n', ',\n', 1)
    prototype += '\n#check (∀ ' + rest + ')\n'
prototype += '\nend BanditRL.OnlineLearning\n'
write(RUN / 'draft-typecheck-v2.lean', prototype)
gate('draft-typecheck-v2', 'lake', 'env', 'lean', RUN / 'draft-typecheck-v2.lean')
for cmd in ['new-task','blueprint-refresh','lifecycle-event','search-memory','list-lean-decls']:
    native('draft-help-'+cmd+'-v2',cmd,'--help')
native('draft-new-task-v2', 'new-task', TASK, '--kind', 'causal-kernel-realization',
       '--title', 'One causal behavioral kernel process and exact IID expected-fixed excess',
       '--target-lean', PUBLIC.relative_to(ROOT).as_posix())
for directory in ['tasks','proof-obligations','conversion-windows']:
    p = ROOT / directory / (TASK + '.md')
    write(RUN / ('native-' + directory + '-template-v2.raw'), p.read_bytes())
    p.write_bytes(p.read_bytes() + ('\n\n## Draft5 derived kernel targets, contextv2\n\n' +
        (CONTRACT / 'source-intent-v1.md').read_text(encoding='utf8') +
        '\nExact5 headersv1 unchanged; contextv2 computational annotation repair retained. Targets-v2.json and DAG define all obligations. K1/K2 dependency-ready; other terminals await real proofs. No new public theorem body. Contract review required before stabilization.\n').encode('utf8'))
native('draft-blueprint-v2', 'blueprint-refresh', TASK)
native('draft-lifecycle-v2', 'lifecycle-event', '--session', TASK, '--event', 'draft', '--payload-json',
       json.dumps(dict(run_id=RUN.name, contract_version=2, source_sha256=PDF_SHA,
       target_statement_hashes=[r['statement_hash'] for r in targets['targets']], obligations=5, compiled=0,
       original_draft_typecheck_failed=1, repaired_context_typecheck=0, chapter_complete=False, goal_complete=False)))
for name in ['bandit_paper_cards','bandit_scenario_cards','bandit_textbook_cards',
             'proof_weapon_cards','local_leaf_cards','local_lean_declarations']:
    p = ROOT / 'research-wiki/retrieval-index' / (name + '.json')
    write(RUN / 'baseline' / ('retrieval-' + name + '.raw'), p.read_bytes())
native('draft-reference-index-v2', 'reference-index')
native('draft-search-kernel-v2', 'search-memory', 'kernel')
native('draft-search-sampler-v2', 'list-lean-decls', 'kernel_sampler', '--statement')
native('draft-search-actual-parent-v2', 'list-lean-decls', 'randomized_history_policy_expectedFixed_excess', '--statement')
write(RUN / 'memory_digest.md',
      'DRAFT unverified kernel package. Existing kernel single-step sampling/infinitePi and actual randomized_history_policy_expectedFixed_excess are local retrieved parents, no new kernel proofs. Drafttypev1 failed on two measure computations, exactv2 noncomputable annotations repaired context; all5 proposed terminal hashes unchanged, actualtypev2 Lean0. One coherent causal recursion, derived joint law and same-process terminal REQUIRED. Prior completed4 accepted/delivered PR1994db37; original16/null/remainingchapters preserved. Semantic contract review pending; no new verified lemma.\n')
write(RUN / 'retrieval_index.md',
      'Pinned local Representation/CondDistrib/InfinitePi/MeasureCompProd/Fin.Tuple APIs inspected and actual API/typeprobe logs retained. Source unknown-law population mean only analytical. Exact local randomized-history parent retrieved by statement. No Optlib/LML/upstream dependency or toolchain changes. General product-map helper may be mathlib-candidate; actual causal action recursion route-local. CLI scanner is declaration presence only, not proof compilation; all index deltas separately audited.\n')
print('Actual contextv2 DRAFT elaboration0; five header hashes unchanged, no public theorem body.', flush=True)
