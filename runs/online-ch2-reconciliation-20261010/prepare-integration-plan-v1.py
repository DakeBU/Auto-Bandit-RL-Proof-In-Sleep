from ftl_canary_proof import *
import copy, gzip

canary_fixed()
review_path = RUN / 'ftl-canary-BODY-review-v1.json'
review = load(review_path)
assert sha(review_path) == '47f8ec8b77a419c8bd39fc10fccee22a63bff8359d827e8d24c47999ff36d684'
assert review['verdict'] == 'accepted-with-explicit-delta' and review['canary_BODY_accepted']
assert not review['required_repairs']
assert sha(review['report']) == review['report_sha256']
assert sha(review['input_manifest']) == review['input_manifest_sha256']
for row in load(review['input_manifest'])['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
assert sha(MODULE) == review['production_sha256'] and sha(TEST) == review['Test_sha256']

prior = ROOT / 'tmp/online-ch2-unbounded-osd-site-v1/books/registry.json'
prior_receipt = ROOT / 'runs/online-ch2-unbounded-osd-20261010/registry-inspected-v1.json'
registry = load(prior)
assert sha(prior) == load(prior_receipt)['registry_sha256']
assert len(registry['nodes']) == 11041
names = ['BanditRL.OnlineFTLSelector.' + s for s in ['cumulative', 'minimizers', 'select', 'predict']]
names += [r['declaration'] for r in load(LEAF / 'frozen-headers-draft-v1.json')['rows']]
assert len(set(names)) == 13
assert not set('declaration:' + n for n in names).intersection(n['id'] for n in registry['nodes'])
write(RUN / 'registry-baseline-v1.json.gz', gzip.compress(prior.read_bytes(), mtime=0))
write(RUN / 'registry-baseline-binding-v1.json', dict(
    prior_source=prior.as_posix(), prior_complete_raw_sha256=sha(prior),
    compressed_snapshot_sha256=sha(RUN / 'registry-baseline-v1.json.gz'),
    prior_actual_registry_receipt=rows([prior_receipt]), source_commit=registry['source_commit'],
    total_shared_nodes=11041, expected_new_canonical_ids=['declaration:' + n for n in names],
    expected_new_theorems=9, expected_new_definitions=4, expected_total=11054,
    public_Test_and_generated_Test_excluded=True,
    scope='Preserved complete parent registry objects from its clean local site source99ee791, not a fresh site at later parent delivery HEAD2e06e21 or this uncommitted candidate.'))

source = ('Orabona, Online Learning: A Modern Introduction Using Convex Optimization, '
          'arXiv:1912.13213v10 (2026-06-21), Chapter2 printed11-12/PDF23-24. '
          'Pinned PDF SHA256 ' + PDF_SHA + '. ')
objects = ('An arbitrary type X, feasible subset V and real-valued losses represented on the ambient X. '
           'Only their restrictions to V determine this selector. Lean time0 is source round1; '
           'the prediction at time t uses exactly losses with indices s<t. ')
boundary = ('This is one generic strict-past FTL algorithm-definition foundation: four definitions and nine derived proof terminals, '
            'not thirteen printed results or a regret guarantee. The source argmin rule is completed as a classical partial Option selector. '
            'No unconditional attainment, executable/measurable optimizer, full valid run for arbitrary losses or new FTL performance bound is proved. '
            'The fixed choice is compared only when its entire minimizer set agrees; arbitrary tied choices are not identified. '
            'The old scalar linear and squared-loss FTL strategies remain source-qualified instances, with no proved definitional equality to this classical selector. '
            'In the recovery canary P1=none supplies no playable action; P2=some0 is a separate longer-prefix query, '
            'not a valid complete online interaction continuing after failure. '
            'The65overlapping source containers are not an independent theorem or proof-obligation denominator. '
            'All eight forward containers remain required/open at chapter level: prescient and OSD package bindings are reconciled as bounded candidates, '
            'while six future mathematical claims remain required/open and unenumerated. Ownership/navigation does not discharge them. '
            'Chapter2 remains partial with null proof total; Chapters3-16 unenumerated/null; whole Goal ACTIVE. '
            'Stacked on OPEN draft unmerged PR214 exact ' + BASE + '. No merge, deployment, main/live, CI or retirement claim.')
canaries = ('Eight complete public canaries prove the actual nonconstant trajectory3/4->1/4->1/2 with feasible prefix minima, '
            'current/future independence, outside-domain invariance, tied minima without naming the chosen endpoint, '
            'empty domain versus empty history and two distinct initials, affine nonattainment on the nonempty closed convex real line, '
            'and separately recomputed recovery from none to some0. Their24selected compiled values include13production,8publicTests and3privatehelpers. '
            'Eleven independently selected conjunction branches retain production VALUEs directly or through actual private helpers; '
            'this is neither a full transitive graph nor proof-necessity or occurrence analysis. ')
specs = [
    ('Finite cumulative loss', 'All finite history lengths including0, arbitrary X and real losses; no feasible-set or regularity premise.',
     r'C_L(x)=\sum_{i\in\mathrm{Fin}(n)}L_i(x).',
     'Sum the supplied finite tuple. The empty sum is zero. cumulative_prefix later identifies the exact natural-index strict prefix.'),
    ('The complete feasible minimizer set', 'All V, histories and points; V may be empty and the minimum need not be attained.',
     r'M_V(L)=\{p\in V:C_L(p)\le C_L(u)\ \forall u\in V\}.',
     'Include both membership and global minimum comparison on V. IsMinOn alone is not used as a replacement for feasibility.'),
    ('Conditional classical minimizer selection', 'All V and finite histories, with no nonemptiness or attainment premise.',
     r'S_V(L)=\begin{cases}\mathrm{some}(p),&M_V(L)\ne\varnothing,\ p\in M_V(L),\\\mathrm{none},&M_V(L)=\varnothing.\end{cases}',
     'Branch on nonemptiness of exactly the minimizer set and use Classical.choose only in the successful branch. No default minimizer is fabricated.'),
    ('FTL with the supplied feasible initial action', 'A supplied subtype initial:V, arbitrary loss stream and natural time. Feasibility of the initial excludes empty V.',
     r'P_0=\mathrm{some}(x_0),\qquad P_t=S_V((\ell_s)_{s<t})\quad(t>0).',
     'Use the given initial at zero; at positive time form Fin t from strict-past losses. Each query is recomputed from its prefix, not an absorbing Option recursion.'),
    ('The exact strict-past sum convention', 'All natural t including0, every stream and ambient point; no V premise.',
     r'C_{(\ell_s)_{s<t}}(x)=\sum_{s=0}^{t-1}\ell_s(x).',
     'Fin.sum_univ_eq_sum_range transports the same terms without shifting a round or dropping an endpoint.'),
    ('A successful selection is feasible and minimizes', 'All V, finite histories and p; assumes the actual equality S_V(L)=some p.',
     r'S_V(L)=\mathrm{some}(p)\Longrightarrow p\in V\ \wedge\ C_L(p)\le C_L(u)\ (u\in V).',
     'Unfold the actual nonempty branch, use choose_spec and identify p by Option.some injectivity. Tied minima do not give the converse for every named p.'),
    ('Failure means no feasible attained minimum', 'All V and finite histories, including empty domains/history; no compactness premise.',
     r'S_V(L)=\mathrm{none}\Longleftrightarrow\neg\exists p\in V,\ \forall u\in V,\ C_L(p)\le C_L(u).',
     'Split the same existence branch in both directions. none records nonattainment or empty domain, not timeout or a numerical approximation failure.'),
    ('Changing loss values outside V preserves selection', 'Histories of the same length with EqOn(L_i,L_i\u0027,V) for every coordinate; tied minima permitted.',
     r'L_i|_V=L_i^{\prime}|_V\ (\forall i)\Longrightarrow S_V(L)=S_V(L^{\prime}).',
     'Termwise restricted equality gives equal cumulative objectives on V, hence equal complete minimizer sets. Rewriting that set in the same classical choice proves actual Option equality.'),
    ('A unique feasible minimum determines the actual output', 'A supplied feasible p, its actual IsMinOn proof and uniqueness among feasible minimizers. These are explicit adapter premises.',
     r'p\in M_V(L),\quad M_V(L)\subseteq\{p\}\Longrightarrow S_V(L)=\mathrm{some}(p).',
     'The some case uses select_some_spec and uniqueness; the none case contradicts select_none_iff and the supplied minimum. The adapter does not establish unconditional attainment.'),
    ('Initialization preserves the chosen feasible first action', 'Arbitrary X,V, supplied initial:V and stream; no loss values inspected.',
     r'P_0=\mathrm{some}(x_0).',
     'Reduce the zero-time branch of predict. This is the source permission for any admissible initial action, not equality with the separate empty-history selector.'),
    ('Every successful prediction minimizes exactly its past', 'All natural t including0, feasible initial and actual equality P_t=some p.',
     r'P_t=\mathrm{some}(p)\Longrightarrow p\in V\ \wedge\ \sum_{s<t}\ell_s(p)\le\sum_{s<t}\ell_s(u)\ (u\in V).',
     'At zero identify the supplied feasible initial and the empty objective. At positive time use select_some_spec and cumulative_prefix on the same selected tuple.'),
    ('Prediction failure has an exact prefix meaning', 'All natural t including0 and a feasible supplied initial; no regularity or attainment hypothesis.',
     r'P_t=\mathrm{none}\Longleftrightarrow\neg\exists p\in V,\ \forall u\in V,\ \sum_{s<t}\ell_s(p)\le\sum_{s<t}\ell_s(u).',
     'At zero eliminate impossible some=none and exhibit the feasible initial as empty-sum minimizer. At positive time transport select_none_iff through cumulative_prefix.'),
    ('Strict-past feasible-domain causality', 'The SAME feasible initial and V; all s<t losses agree only on V. No equality of current/future or outside-V values.',
     r'\ell_s|_V=\ell_s^{\prime}|_V\ (s<t)\Longrightarrow P_t(\ell)=P_t(\ell^{\prime}).',
     'At zero both sides return the same supplied initial. At positive time instantiate select_congr for the Fin t tuple. The stream representation does not grant access to future losses; this equality certifies strict-prefix dependence.')]
assert len(specs) == len(names)
graph = {n['name']: n for n in load(RUN / 'ftl-canary-selected-value-graph-v1.json')['nodes']}
known = {n['id'][len('declaration:'):] for n in registry['nodes']} | set(names)
notes = []
for i, (name, (title, assumptions, formula, proof)) in enumerate(zip(names, specs)):
    parents = sorted(p for p in graph[name]['value_dependencies'] if p in known and p != name)
    notes.append(dict(full_name=name, title=title, chapter='online-ogd', featured=False, teaching_order=215+i,
        plain=objects+assumptions, math=formula, intuition=proof,
        why='Represent the generic strict-past FTL source definition with honest conditional attainment and initialization.',
        position=source+('Definition' if i<4 else 'Derived interface')+' of this one source family; not a separately numbered source theorem.',
        proof_idea=proof, lean_notes=objects+assumptions+proof+' '+canaries+boundary, dependencies=parents))
card = dict(label='Generic strict-past FTL: conditional minimizer and feasible initialization',
    pages='printed11-12 / PDF23-24', pdf_page=23, url='https://arxiv.org/pdf/1912.13213v10', math=specs[3][2],
    plain=objects+specs[3][1], fallback=objects+specs[3][1], relationship=source+boundary,
    contract=dict(model='One fixed classical partial selector of the full feasible strict-past minimizer set, with a supplied feasible first action.',
        assumptions='No convexity, closedness, compactness or attainment for this conditional foundation. Source Euclidean V is generalized to arbitrary X with ambient real losses restricted to V.',
        parameters='Lean t0=source round1; Fin t/range t losses0..t-1. Initial and tie-choice convention fixed in equality comparisons.',
        regret='No new performance bound. Partial selection, exact feasibility/minimum and restricted-prefix invariance only.',
        guarantee=canaries+boundary),
    local_status=dict(status='compiled', label='Generic conditional FTL foundation compiled; Chapter2 partial', boundary=boundary))
proposal = dict(route='online-ogd', notes=notes, card=card, boundary=boundary,
    new_module_glob='BanditRLProof/OnlineFTLSelector.lean',
    added_learning_goal='Construct the generic strict-past FTL partial minimizer rule with feasible initialization, exact failure semantics and restricted-domain prefix causality.',
    completion_extension=' Additive algorithm-definition foundation and qualified provenance reconciliation; no new regret bound or chapter acceptance. '+boundary)
write(RUN / 'reader-proposal-v1.json', proposal)

# Retain every historical row and mismatch flag; add a source-qualified overlay.
old_path = ROOT / 'docs/contracts/online-ch2-chapter-audit-v1/complete-source-reconciliation-draft-v3.json'
old = load(old_path)
assert len(old['rows']) == 65
additional = load(CONTRACT / 'additional-source-bindings-draft-v1.json')['rows']
source_join = dict(stage='qualified local-content reconciliation candidate; not chapter acceptance',
    chapter=2, source_sha256=PDF_SHA, inherited_source_inventory=rows([old_path]),
    source_audit_containers=65, independent_mandatory_obligation_total=None, proof_leaf_total=None,
    historical_inventory=old,
    source_qualified_overlays=[dict(source_id='additional:strict-past-FTL-definition',
        generic_primary_declarations=names,
        production=rows([MODULE]), frozen_definition_context=rows([LEAF/'definition-context-v1.lean.txt']),
        frozen_headers=rows([LEAF/'frozen-headers-draft-v1.json']),
        production_BODY_review=rows([RUN/'production-BODY-canary-CONTRACT-repair-review-v1.json']),
        canary_BODY_review=rows([review_path]),
        preserved_specialized_instances=next(r for r in old['rows'] if r['source_id']=='additional:strict-past-FTL-definition')['exact_current_primary_declarations'],
        instance_boundary='Source-qualified specialized linear/square strategies only; no definitional equality or arbitrary tie-choice policy identity to the new classical selector is proved.',
        source_container_acceptance='pending dedicated reconciliation/integration FINAL', chapter_accepted=False)] +
        [dict(source_id=k, explicit_bound_package=v,
              complete_prescient_producer_chain=(load(CONTRACT/'prescient-complete-chain-bindings-draft-v1.json') if k=='additional:prescient-lookahead-nonpositive-stability' else None),
              bounded_classification_review=rows([RUN/'production-BODY-canary-CONTRACT-repair-review-v1.json']),
              source_container_acceptance='pending dedicated reconciliation/integration FINAL',chapter_accepted=False)
         for k,v in additional.items()],
    appropriate_scope_selection=rows([CONTRACT/'appropriate-scope-receipt-selection-draft-v1.json']),
    earlier_module_deltas=rows([RUN/'staged-module-delta-resolution-v1.json',RUN/'staged-module-delta-supplement-v1.json']),
    omitted_complete_definitions=rows([CONTRACT/'omitted-definition-context-bindings-draft-v1.json']),
    narrow_native_signature_adapters=rows([CONTRACT/'domain-structure-signature-repair-v1.json',CONTRACT/'ancillary-signature-adapter-v1.json']),
    required_forward_obligations=load(CONTRACT/'required-forward-dependencies-draft-v1.json'),
    required_open_forward_containers=8, future_mathematical_claims_required_open_unenumerated=6,
    future_readonly_retrieval=rows([RUN/'forward-readonly-retrieval-v1.json']),
    classification_boundary=boundary, source_container_acceptance=False,
    chapter_complete=False, book_complete=False, whole_Goal='active')
join_path = CONTRACT / 'qualified-source-reconciliation-draft-v4.json'
write(join_path, source_join)

plans = []
def transition(rel, raw, delta):
    path = ROOT / rel
    stem = rel.replace('/', '--')
    before = RUN / ('integration-before-' + stem + '.raw')
    after = RUN / ('integration-after-' + stem + '.raw')
    write(before, path.read_bytes()); write(after, raw)
    plans.append(dict(path=path.as_posix(), before_snapshot=before.as_posix(), before_sha256=sha(path),
        after_snapshot=after.as_posix(), after_sha256=sha(after), delta=delta))

for rel, line in [('BanditRLProof.lean','import BanditRLProof.OnlineFTLSelector'),
                  ('Tests.lean','import Tests.OnlineFTLSelectorCanary')]:
    assert line.encode('utf8') not in (ROOT/rel).read_bytes()
    transition(rel, (ROOT/rel).read_bytes()+('\n'+line+'\n').encode('utf8'), 'Exact RAW prefix plus one import.')
for key in ['chapters','readings','highlights']:
    rel='website/content/'+key+'.json'; new=copy.deepcopy(load(ROOT/rel))
    if key=='chapters':
        row=next(r for r in new['chapters'] if r['slug']=='online-ogd')
        row['module_globs'].append(proposal['new_module_glob'])
        row['learning_goals'].append(proposal['added_learning_goal'])
        row['completion_definition']+=proposal['completion_extension']
    elif key=='readings':
        next(r for r in new['readings'] if r['slug']=='online-ogd')['source_theorems'].append(card)
    else:
        assert not any(r['full_name'] in names for r in new['highlights'])
        new['highlights'].extend(notes)
    transition(rel,(json.dumps(new,ensure_ascii=False,indent=2)+'\n').encode('utf8'),
        dict(chapters='Only online-ogd append module/goal/completion suffix.',
             readings='Only online-ogd append one FTL source-qualified card.',
             highlights='Append13canonical notes; every old note unchanged.')[key])
rel='docs/contracts/online-book-v1/coverage.json'; new=copy.deepcopy(load(ROOT/rel))
row=next(r for r in new['chapters'] if r['chapter']==2)
row.update(status='partial-with-generic-ftl-and-explicit-required-forward-obligations',
    accepted=False, mandatory_count=None,
    latest_package_evidence=review_path.relative_to(ROOT).as_posix(),
    versioned_source_join_candidate=join_path.relative_to(ROOT).as_posix(),
    required_open_forward_containers=8, required_future_mathematical_claims_open_unenumerated=6,
    main_stack_migration='Existing35scope source/BODY/FINAL selections,41comment-only row deltas plus one preplanned proof delta,7omitted definition contexts and31prescient producer declarations have bounded distinct classification/provenance review. Whole-chapter source-container FINAL, all required future mathematical dependencies and main integration remain open.',
    boundary=boundary)
transition(rel,(json.dumps(new,ensure_ascii=False,indent=2)+'\n').encode('utf8'),
    'Only Chapter2 current partial/evidence/source-join/required-open/provenance fields; all other chapters/top-level fields unchanged.')
write(CONTRACT/'exact-integration-plan-v1.json',dict(rows=plans,reader_proposal_sha256=sha(RUN/'reader-proposal-v1.json'),
    source_join_sha256=sha(join_path),allowed_old_mutations=6,all_other_baseline_paths_immutable=True,
    other_Books_preserved=True,old_links_fields_preserved=True,shared_registry_expected=11054,
    public_Tests_excluded=True,global_SGB_untouched=True,generated_site_not_edited=True,
    source_container_closed=False,chapter_complete=False,whole_goal='active'))
write(RUN/'integration-plan-prepared-v1.json',dict(plan=rows([CONTRACT/'exact-integration-plan-v1.json']),
    source_join=rows([join_path]),reader_proposal=rows([RUN/'reader-proposal-v1.json']),
    actual_old_mutations=0,roots_and_readers_still_unchanged=True,canary_BODY_review=rows([review_path]),
    combined_gates='pending',site='pending',native_acceptance='pending',FINAL='pending'))
canary_fixed()
print('Exact six-path plan,13reader notes,one source card and qualified65container overlay prepared; no old path changed.',flush=True)
