from common import *
import copy, gzip

review_path = RUN / 'canary-BODY-review-v1.json'
review = load(review_path)
assert review['verdict'] in ['accepted', 'accepted-with-explicit-delta']
assert not review['required_repairs']
assert sha(review['report']) == review['report_sha256']
assert sha(review['input_manifest']) == review['input_manifest_sha256']
for row in load(review['input_manifest'])['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
test = ROOT / 'Tests/OnlineAdaptiveEnergyCanary.lean'
assert sha(PUBLIC) == review['exact_production_source_sha256']
assert sha(test) == review['exact_canary_source_sha256']
names = ['BanditRL.OnlineAdaptiveEnergy.' + x for x in
         ['sum_div_sqrt_prefix', 'norm_sq_sum_div_sqrt_prefix', 'source_energy_term_bound']]
source = ('Orabona, Online Learning: A Modern Introduction Using Convex Optimization, '
          'arXiv:1912.13213v10 (2026-06-21), unnumbered energy display after Lemma4.13 '
          'and before Eq.(4.4), printed40/PDF52; SHA256 ' + PDF_SHA + '. ')
boundary = ('One source energy-display family is now a reusable prerequisite for the required '
            'Chapter2 adaptive-rate forward claim, represented by three production proofs and two '
            'full canaries, not three independent source results. Actual causal adaptive OSD, '
            'zero-feedback skipping, zero-radius/zero-energy regret, zero-weight potential, '
            'Eq.(4.4), Theorem4.14 and its minimum-versus-infimum edge remain required/open. '
            'All eight Chapter2 forward containers and six future mathematical claims remain '
            'required/open. Chapter2 partial/null; Chapters3-16 unenumerated/null; Chapter4 '
            'is not a competing main task. Whole Chapters1-16 Goal ACTIVE. Stacked on OPEN '
            'draft unmerged PR216 exact ' + BASE + '. No merge, deployment, main/live or retirement claim.')
objects = ('For every finite horizon T, normed additive commutative group E, feedback stream '
           'g from natural indices to E and nonnegative scalar D, the sum of squared feedback '
           'norms divided by the square root of their cumulative energy, multiplied by D/2, '
           'is at most D times the square root of total energy. An abstract nonnegative '
           'increment theorem and its squared-norm specialization supply the same bound.')
delta = ('Source t=1..T is Lean t=0..T-1; each denominator includes the current increment. '
         'The analytic theorem generalizes Euclidean squared norms to a normed additive '
         'commutative group. D is a nonnegative scalar here; interpreting it as domain diameter '
         'belongs to the future OSD consumer. Real division is totalized: zero cumulative energy '
         'forces the nonnegative current increment to be zero, so its summand is zero. '
         'This includes leading/interior zero feedback, empty horizon and D=0 without a '
         'positive-energy premise. It does not establish an algorithmic skip rule. '
         'The source invokes Lemma4.13 with a positive offset and a limit; our proof instead '
         'uses the existing square-root supporting line and handles zero prefixes algebraically. '
         'No continuity of inverse square root at zero is asserted. Lemma4.13 is source '
         'correspondence, not a direct Lean proof dependency.')
proof = ('Write S_t for the cumulative nonnegative energy through the current increment. '
         'If S_t is positive, the shared square-root supporting line gives '
         'a_t/sqrt(S_t) <= 2(sqrt(S_t)-sqrt(S_(t-1))). If S_t=0, nonnegativity forces '
         'both the increment and preceding sum to be zero, giving the same inequality. '
         'Inductively add these inequalities: adjacent square roots telescope and the '
         'initial sum is zero. Substitute a_t=norm(g_t)^2, then multiply by the '
         'nonnegative scalar D/2 and cancel the numerical factor2.')
canaries = ('Two full public canaries retain 8 and 3 conjuncts. Feedback [0,3,0,4] has '
            'total energy25 and normalized sum31/5, strictly below the D=2 bound10. '
            'Separate cases cover T=0, a nonempty all-zero stream and D=0 with nonzero '
            'energy. All five inequality conjuncts have actual connected public theorem '
            'calls, including the strict gap via the T=3 prefix. Compiled VALUE constant '
            'presence does not establish necessity or a complete transitive graph.')
parent = 'BanditRLProof.Tsallis.two_mul_sqrt_sub_sqrt_le_sub_div_sqrt'
source_math = (r'\frac{D}{2}\sum_{t=1}^{T}\frac{\|g_t\|_2^2}'
               r'{\sqrt{\sum_{i=1}^{t}\|g_i\|_2^2}}'
               r'\le D\sqrt{\sum_{t=1}^{T}\|g_t\|_2^2}.')
proof_math = (r'\begin{gathered}S_{-1}=0,\quad S_t=\sum_{i=0}^{t}a_i,\quad a_i\ge0,\\ '
              r'\frac{a_t}{\sqrt{S_t}}\le2(\sqrt{S_t}-\sqrt{S_{t-1}}),\\ '
              r'\sum_{t=0}^{T-1}\frac{a_t}{\sqrt{S_t}}\le2\sqrt{S_{T-1}},\\ '
              r'a_t=\|g_t\|^2,\quad '
              r'\frac D2\sum_{t=0}^{T-1}\frac{\|g_t\|^2}{\sqrt{S_t}}'
              r'\le D\sqrt{S_{T-1}}.\end{gathered}')
highlight = dict(full_name=names[2], title='Adaptive energy sums telescope across zero prefixes',
                 chapter='online-ogd', featured=False, teaching_order=301,
                 source_match='closest-source', plain=source+objects, math=proof_math,
                 intuition=proof, why='Supply the energy term needed by the required causal adaptive OSD proof.',
                 position=source+boundary, proof_idea=proof,
                 lean_notes=delta+' Actual direct shared chain: '+parent+' -> '+names[0]+' -> '+names[1]+' -> '+names[2]+'. '+canaries+' '+boundary,
                 dependencies=[names[1]])
card = dict(label='Required adaptive-rate prerequisite: cumulative energy display',
            pages='printed40 / PDF52', pdf_page=52, url='https://arxiv.org/pdf/1912.13213v10',
            math=source_math, plain=objects, fallback=objects, relationship=source+delta+' '+boundary,
            contract=dict(model='Deterministic finite nonnegative energy summation.',
                          assumptions='Finite horizon; normed additive commutative group; D>=0. No positive prefix energy or bounded-domain hypothesis.',
                          parameters='Current inclusive prefix denominator; source1..T corresponds to Lean0..T-1; totalized zero summands.',
                          regret='This analytic bound does not construct a causal algorithm or prove its regret.',
                          guarantee=canaries+' The adjacent teaching note supplies the displayed proof, folded exact Lean and actual parents.'),
            local_status=dict(status='compiled', label='Energy prerequisite compiled; causal OSD and Chapter2 open', boundary=boundary))
write(RUN/'reader-proposal-v1.json', dict(source=source, objects=objects, delta=delta,
      proof=proof, canaries=canaries, boundary=boundary, highlight=highlight, source_card=card))

prior_run = ROOT/'runs/online-ch2-adaptive-summation-20261010'
prior_build = load(prior_run/'site-build-v1.json')
args = prior_build['command']
out = Path(args[args.index('--output')+1])
if not out.is_absolute(): out = ROOT/out
registry_path = out/'books/registry.json'
reg = load(registry_path)
assert sha(registry_path) == load(prior_run/'registry-inspected-v1.json')['registry_sha256']
assert len(reg['nodes']) == 11055
assert not any(n['id'] in ['declaration:'+x for x in names] for n in reg['nodes'])
write(RUN/'registry-baseline-v1.json.gz', gzip.compress(registry_path.read_bytes(), mtime=0))
write(RUN/'registry-baseline-binding-v1.json', dict(prior=rows([registry_path,prior_run/'registry-inspected-v1.json']),
      snapshot_sha256=sha(RUN/'registry-baseline-v1.json.gz'), source_commit=reg['source_commit'],
      source_dirty=False, complete_old_nodes=11055, new_ids=['declaration:'+x for x in names],
      expected_total=11058, expected_source_cards=16,
      boundary='Historical actual clean source6c935087 local registry, not a new site at current evidence head873039.'))
old_allowed = ['BanditRLProof.lean','Tests.lean','website/content/chapters.json',
               'website/content/readings.json','website/content/highlights.json',
               'docs/contracts/online-book-v1/coverage.json']
planned=[]
for relative in old_allowed:
    path=ROOT/relative; before=path.read_bytes()
    if relative in ['BanditRLProof.lean','Tests.lean']:
        addition='import '+('BanditRLProof.OnlineAdaptiveEnergy' if relative=='BanditRLProof.lean' else 'Tests.OnlineAdaptiveEnergyCanary')+'\n'
        assert addition.encode() not in before and before.endswith(b'\n')
        after=before+addition.encode()
    else:
        obj=load(path); old=copy.deepcopy(obj)
        if relative.endswith('chapters.json'):
            item=next(x for x in obj['chapters'] if x['slug']=='online-ogd')
            item['module_globs'].append('BanditRLProof/OnlineAdaptiveEnergy.lean')
            item['learning_goals'].append('Telescope cumulative energy sums, retaining zero prefixes, empty horizons and zero external scaling.')
            item['completion_definition']+=' Additive adaptive energy prerequisite: '+boundary
            assert [x for x in obj['chapters'] if x['slug']!='online-ogd']==[x for x in old['chapters'] if x['slug']!='online-ogd']
        elif relative.endswith('readings.json'):
            item=next(x for x in obj['readings'] if x['slug']=='online-ogd')
            item['source_theorems'].append(card)
            assert [x for x in obj['readings'] if x['slug']!='online-ogd']==[x for x in old['readings'] if x['slug']!='online-ogd']
            assert item['source_theorems'][:-1]==next(x for x in old['readings'] if x['slug']=='online-ogd')['source_theorems']
        elif relative.endswith('highlights.json'):
            obj['highlights'].append(highlight)
            assert obj['highlights'][:-1]==old['highlights']
        else:
            item=next(x for x in obj['chapters'] if x['chapter']==2)
            assert not item['accepted'] and item['mandatory_count'] is None
            assert item['required_open_forward_containers']==8 and item['required_future_mathematical_claims_open_unenumerated']==6
            item['adaptive_energy_prerequisite']=dict(source='ORABONA-V10-ENERGY-P40',
                declarations=names, source_families=1, evidence='runs/'+RUN.name+'/canary-BODY-review-v1.json',
                scope='Compiled and source-reviewed energy calculation; causal OSD/regret/chapter remain open.')
            item['boundary']+=' '+boundary
            assert [x for x in obj['chapters'] if x['chapter']!=2]==[x for x in old['chapters'] if x['chapter']!=2]
        after=(json.dumps(obj,ensure_ascii=False,indent=2)+'\n').encode('utf8')
    key=relative.replace('/','__'); bp=RUN/'integration-snapshots'/('BEFORE-'+key); ap=RUN/'integration-snapshots'/('AFTER-'+key)
    write(bp,before); write(ap,after)
    planned.append(dict(path=path.as_posix(),before_snapshot=bp.as_posix(),before_sha256=sha(bp),after_snapshot=ap.as_posix(),after_sha256=sha(ap)))
write(CONTRACT/'shared-book-mapping-v1.json',dict(source_id='ORABONA-V10-ENERGY-P40',source_sha256=PDF_SHA,
      source_Chapter=4,source_pdf_page=52,canonical_declarations=names,source_families=1,
      canonical_module='BanditRLProof.OnlineAdaptiveEnergy',shared_registry_ids=['declaration:'+x for x in names],
      actual_direct_edges=[[parent,names[0]],[names[0],names[1]],[names[1],names[2]]],
      source_correspondence_only='Lemma4.13; not an actual direct proof edge',
      owning_reader_route='online-ogd',planned_consumer='Required Chapter2 causal adaptive OSD; no compiled consumer edge yet',
      other_Books='Same underlying shared project and declaration registry; no proof-tree clones',
      source_container_closed=False,chapter_complete=False,whole_Goal='active'))
manifest=copy.deepcopy(load(ROOT/'research-wiki/contribution-contracts/ONLINE-CH2-ADAPTIVE-SUMMATION-20261010.json'))
manifest.update(id=TASK,target=objects+' '+boundary,declarations=names,truth_boundary=boundary)
manifest['source'].update(anchor='Unnumbered cumulative-energy display after Lemma4.13 and before Eq.(4.4), printed40/PDF52.')
manifest['affected_files']=['BanditRLProof/OnlineAdaptiveEnergy.lean','BanditRLProof.lean','website/content/chapters.json','website/content/readings.json','website/content/highlights.json']
manifest['reuse_plan'].update(searched_existing=['Actual pinned native retrieval/list-lean-decls; unit-increment sqrt schedule is insufficient for arbitrary energy.'],
    reused_declarations=[parent],new_shared_declarations=names,
    known_consumers=['Tests.OnlineAdaptiveEnergyCanary.nonzero_energy_zero_prefix_canary','Tests.OnlineAdaptiveEnergyCanary.zero_boundaries_canary'],
    planned_consumers=['Required Chapter2 actual causal adaptive OSD; remains open.'],
    decision_reason='One canonical energy-display family, abstract scalar proof plus norm and scale adapters; actual shared Tsallis parent reused, no per-Book project/toolchain/dependency upgrade.')
manifest['semantic_roundtrip'].update(remaining_semantic_delta=delta+' Distinct reused automated decoder/source reviewer; related history disclosed. Exact CONTRACT/production BODY/canary CONTRACT/BODY reviews retained; integration/combined/site/FINAL/native/delivery pending. No external/human/absolute-blind/runtime attestation.')
manifest['graph_contribution'].update(focus_targets=names,
    functor_reason='An algebraic supporting-line reuse across Tsallis and energy summation is an actual theorem edge, not a separately certified equivalence functor.',
    visual_review='Pending actual new source card/teaching note/folded Lean/module original pixels and complete11055oldregistryobjects plus3production nodes=11058;16cards. Structural counts are not independent source-result/chapter totals.')
manifest['progress_updates'].update(teaching_route='Append one shared module, learning goal, bounded suffix, source-qualified card and teaching note; preserve all older Book objects and links.',
    banditrlwiki='no-change-with-reason: analytic prerequisite changes no Bandit policy or guarantee.',
    results_ledger='no-change-with-reason: bounded foundation growth does not complete a chapter/global route.',
    roadmap='updated: Chapter2 partial/null, all8forward and6futureclaims required/open; Chapter4 unenumerated/null; global SGB untouched.')
manifest['verification'].update(focused_checks=['Actual scalar and allthree focused production builds0; two FULL canary buildv2 0 after retained BODY API-orientation failurev1. Five full public applications/standard axiom audits, five native fences/safe-verifies, actual three-parent chain and five selected inequality public calls. Initial fence annotation failure retained. Frozen headers/context unchanged.'],
    bandit_check='Combined root/Tests/full harness and nonempty contributor/shadow gates required; pending.',
    site_build='Pending isolated clean-source build after applicable combined gate; generated website/_site untouched; no live claim.',
    site_check='Pending shared registry/actual original-pixel checks.',
    independent_review='Distinct source CONTRACT/production BODY/canary CONTRACT/BODY; integration/FINAL/native/delivery pending.',
    owned_test_files=['Tests/OnlineAdaptiveEnergyCanary.lean'],owned_test_root_files=['Tests.lean'])
write(RUN/'prospective-contribution-v1.json',manifest)
write(CONTRACT/'exact-integration-plan-v1.json',dict(rows=planned,old_allowed=old_allowed,
    new_manifest='research-wiki/contribution-contracts/'+TASK+'.json',
    prospective_manifest_sha256=sha(RUN/'prospective-contribution-v1.json'),
    mapping_sha256=sha(CONTRACT/'shared-book-mapping-v1.json'),
    production_sha256=sha(PUBLIC),Test_sha256=sha(test),
    scope='Exactly six old-file AFTER snapshots and one create-only manifest; proofs unchanged; pending distinct integration review.'))
print('Prepared exact integration proposal; no old tracked file changed.',flush=True)
