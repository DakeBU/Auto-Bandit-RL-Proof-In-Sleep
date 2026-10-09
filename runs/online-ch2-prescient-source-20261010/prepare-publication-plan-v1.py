from common import *
import copy,gzip
fixed()
evidence=load(RUN/'eight-public-values-inspected-v1.json')
assert evidence['eight_headers_unchanged'] and len(evidence['selected_numeric_tails'])==2
st=load(CONTRACT/'stabilized-v1.json'); names=[t['name'] for t in st['six_targets']]
graph={n['name']:n for n in load(RUN/'selected-value-graph-v1.json')['nodes']}
prior=ROOT/'tmp/online-ch2-prescient-cumulative-site-v2/books/registry.json'
receipt=ROOT/'runs/online-ch2-prescient-cumulative-20261009/registry-inspected-v2.json'
old=load(prior); old_receipt=load(receipt)
assert sha(prior)==old_receipt['actual_current_registry_sha256'] and len(old['nodes'])==11020
write(RUN/'registry-baseline-v1.json.gz',gzip.compress(prior.read_bytes(),mtime=0))
write(RUN/'registry-baseline-binding-v1.json',dict(prior_source=prior.as_posix(),prior_complete_raw_sha256=sha(prior),compressed_snapshot_sha256=sha(RUN/'registry-baseline-v1.json.gz'),prior_actual_registry_receipt=rows([receipt]),source_commit=old['source_commit'],identity=old['identity'],total_shared_nodes=11020,expected_new_canonical_ids=['declaration:'+n for n in names],expected_new_theorems=6,expected_new_definitions=0,expected_total=11026,public_Test_and_generated_Test_excluded=True,scope='Parent clean candidate site source712969cf; not a fresh build at later metadata head547137ea.'))
known={n['id'][len('declaration:'):] for n in old['nodes']}|set(names)
route='online-ogd'
boundary=('This package transports source loss hypotheses and actual valid argmin runs into the SAME current-loss Option recursion; it is not universal attainment or automatic interior preservation. '
 'Closedness and strict convexity do not imply an attained penalized minimum, as the existing exponential counterexample shows. '
 'The six proof terminals and two concrete canaries are bounded dependency progress, not six printed source results or a chapter denominator. '
 'All eight Chapter 2 forward containers remain required/open pending dedicated source reconciliation and chapter gates; Chapter 2 is partial with null complete proof denominator, Chapters 3-16 remain unenumerated/null, and the Chapters 1-16 Goal stays active. '
 'Prior package boundaries describe their historical scope; this additional package now derives properness and the source valid-run identity rather than assuming hseq. '
 'Stacked on OPEN draft unmerged PR #212 exact '+BASE+'. No merge, deployment, main/live, CI or retirement claim.')
source=('Orabona, Online Learning: A Modern Introduction Using Convex Optimization, arXiv:1912.13213v10 (2026-06-21), '
 'Chapter 2 required prescient forward observation printed14/PDF26; Definitions2.16/2.18 and subgradient conventions printed16-17/PDF28-29; Definition6.4 printed63/PDF75; Algorithm15.8/Theorem15.30 printed265-266/PDF277-278. Pinned PDF SHA256 '+PDF_SHA+'. ')
objects=('Write B(a;b)=psi(a)-psi(b)-Dpsi(b)[a-b], target first and derivative base second. '
 'For the source algorithm, Lean loss t is source loss_(t+1); current WHOLE loss arrives before selecting and paying x(t+1), whose base is x(t). '
 'The partial classical selector and recursion are canonical shared declarations, not executable or measurable optimizers. ')
source_assumptions=('Real finite-dimensional inner-product E; V nonempty, closed, convex and contained in X. '
 'The ambient real representative psi is strictly convex on X and differentiable on interior X; SourceClosed(coe psi + extendedIndicator X) encodes ambient closed sublevels of its restricted generator. '
 'The initial center and all updated states through T lie in interior X; the initial center need not belong to V or a loss domain. '
 'For each played loss, bottom is excluded globally, V lies in its effective domain, and global ambient supporting subgradients exist at every feasible point. '
 'Each given successor is feasible and actually minimizes the extended-real penalized objective. These are the algorithm update premises, not an assumed regret or hseq bound. '
 'Losses may be top outside V; finite feasible comparisons justify toReal without assuming global convexity of its zero-default extension. '
 'Literal source closedness premises are retained although the conditional argument does not use them to infer attainment. ')
canaries=('Public fixed and decreasing-step tests use the verified nonquadratic generator z^4/4+z^2/2, V=[-1,1], two distinct current losses and states1/2->0->1/2. '
 'They prove global no-bottom and finite-on-V facts, extract actual known minima from parent concrete proofs, and invoke the new source transports. '
 'The fixed numeric proof -9/8<=5/16 and decreasing comparator+1/2 proof -1/2<=-11/64 each retain their corresponding NEW source endpoint in the individually selected compiled proof value. '
 'The decreasing previous-state maxima are5/8 at comparator-1/2 and9/64 at+1/2; weighted movements29/64. No sharp terminal-corrected bound is substituted for a printed endpoint. ')
specs=[
 ('Finite feasible domain produces properness',
  'Arbitrary type E, no topology/norm/dimension. V is nonempty, f has no bottom anywhere, and V is included in effectiveDomain f={z:f(z)<top}. Top outside V remains allowed. ',
  r'V\ne\varnothing,\quad f(z)\ne-\infty\ (\forall z),\quad V\subseteq\operatorname{dom}f\quad\Longrightarrow\quad f\text{ proper}.',
  'Choose z in V. Domain inclusion gives f(z)<top, while global no-bottom excludes the other infinity. EReal.coe_toReal supplies the finite real witness required by the canonical SourceProper definition. This is a producer, with both source regret wrappers as actual consumers.'),
 ('Strict convexity of the actual penalized objective',
  'Real inner-product E, no completeness/dimension assumption. V is convex and contained in X, psi is strictly convex on X, f is SourceProper with global supports at every feasible point, eta>0, and the center x is arbitrary. The total fderiv at x is linear even without differentiability; this algebra does not license source Bregman semantics at a bad base. ',
  r'F(z)=\operatorname{toReal}(f(z))+\eta^{-1}B_\psi(z;x),\qquad F\text{ strictly convex on }V.',
  'Reuse finitePart_convex_of_subdifferentiable on V. Strict convexity of psi supplies a strict convex-combination inequality; the frozen derivative term is affine and cancels. Multiply by the positive inverse eta and add the convex finite-loss inequality. No coercivity or attained minimum is concluded.'),
 ('The selector returns the supplied unique minimizer',
  'Complete real inner-product E; the same strict-objective assumptions, positive eta and a supplied feasible point p with an ACTUAL extended-real IsMinOn premise. IsMinOn alone does not include membership, so p in V is explicit. No generator differentiability or center membership is needed for this static identity. ',
  r'p\in V,\quad p\in\arg\min_{z\in V}\{f(z)+\eta^{-1}B_\psi(z;x)\}\quad\Longrightarrow\quad\operatorname{advance}(V,\psi,\eta,f,x)=\operatorname{some}(p).',
  'Global supports and properness certify all feasible loss values finite. Transport BOTH the supplied and actually selected extended-real minima through proximal_finitePart_minimizer_iff. penalized_strictConvex and StrictConvexOn.eq_of_isMinOn identify them, then unfold the SAME advance definition. This is conditional uniqueness, not general existence.'),
 ('Valid source updates identify the actual recursion',
  'Complete real inner-product E, convex V subset X, strictly convex psi on X. A supplied trajectory starts at x0 and each played successor is a feasible actual penalized minimizer about its preceding point. Played steps are positive and losses proper with global supports on V. T=0 is allowed; no hseq input, interior assumption or existence of a future-aware algorithm is used here. ',
  r'x(0)=x_0,\quad x(t+1)\in\arg\min_{z\in V}\{\ell_t(z)+\eta_t^{-1}B_\psi(z;x(t))\}\quad\Longrightarrow\quad\forall t\le T,\ I_t=\operatorname{some}(x(t)).',
  'Induct on t. The zero case is the canonical initial state. At a successor, rewrite the previous actual Option state by induction, simplify bind(some), and apply advance_eq_some_of_minimizer to that round\u0027s current loss and supplied minimum. This fixes algorithm identity rather than assuming unrelated successful outputs.'),
 ('The source fixed-step regret bound',
  source_assumptions+'Constant eta>0; every natural horizon T including0. Every comparator u lies in V, but need not be interior. The printed bound keeps negative movements; it has no additional terminal term. ',
  r'\sum_{t=0}^{T-1}(\ell_t(x(t+1))-\ell_t(u))\le\frac{B_\psi(u;x_0)}{\eta}-\frac1\eta\sum_{t=0}^{T-1}B_\psi(x(t+1);x(t)).',
  'sourceProper_of_domain converts the source codomain/domain assumptions to properness for every played loss. iterate_eq_of_source_updates identifies this actual argmin run with the canonical recursion. Reuse iterate_fixed_regret from that SAME run; its upstream one-step proof is derived from actual minima. The mandatory printed fixed statement is proved even though the source leaves its proof as an exercise. T=0 yields an inequality via nonnegative initial divergence, not an equality.'),
 ('The source decreasing-step finite-maximum bound',
  source_assumptions+'Here T>0, eta(t)>0 for t<T and eta(t+1)<=eta(t) only for t+1<T. The finite maximum ranges over PREVIOUS states x(0)..x(T-1); the final denominator is the last played eta(T-1). No bounded V premise or terminal x(T) inside the maximum is added. ',
  r'\sum_{t=0}^{T-1}(\ell_t(x(t+1))-\ell_t(u))\le\frac{\max_{0\le t<T}B_\psi(u;x(t))}{\eta(T-1)}-\sum_{t=0}^{T-1}\frac{B_\psi(x(t+1);x(t))}{\eta(t)}.',
  'Derive properness from the source loss assumptions and identify the eta-dependent supplied argmin run with the actual recursion. Apply iterate_variable_regret, whose certified weighted telescope uses exactly the previous-state finite maximum. Negative weighted movements remain. This is the printed endpoint, distinct from the stronger parent that also subtracts terminal divergence.')]
notes=[]
for i,(row,spec) in enumerate(zip(st['six_targets'],specs)):
    title,assumptions,formula,proof=spec
    parents=sorted(p for p in graph[row['name']]['value_dependencies'] if p in known and p!=row['name'])
    notes.append(dict(full_name=row['name'],title=title,chapter=route,featured=False,teaching_order=192+i,plain=objects+assumptions,math=formula,intuition=proof,why='Close the exact source-loss or actual valid-run transport edge in the required Chapter2 prescient dependency.',position=source+('Derived Definition2.18 source-domain adapter, not a separately numbered theorem.' if i==0 else 'Derived source-run transport interface, not a separately numbered source result.' if i<4 else 'Faithful printed Theorem15.30 valid-run conclusion, with explicit source-to-recursion hypothesis transport.'),proof_idea=proof,lean_notes=objects+assumptions+proof+' '+canaries+boundary,dependencies=parents))
card=dict(label='Chapter 2 prescient dependency: source hypotheses and the actual valid run',pages='printed14,16-17,63,265-266 / PDF26,28-29,75,277-278',pdf_page=277,url='https://arxiv.org/pdf/1912.13213v10',math=specs[-1][2],plain=objects+source_assumptions+'Fixed T>=0 with constant positive eta; only variable endpoint T>0 with nonincreasing positive played steps. ',fallback=source_assumptions,relationship=source+boundary,contract=dict(model='Same current-known-whole-loss canonical Option recursion, identified from actual valid source argmin updates by uniqueness.',assumptions=source_assumptions,parameters='Lean t=source round t+1; state0=x0. Fixed T>=0/constant eta>0; variable T>0/positive nonincreasing played eta, max over0..T-1, last denominator eta(T-1).',regret='Both printed fixed/variable bounds preserve negative movements. Sharp terminal-corrected parents remain distinct.',guarantee=canaries+boundary),local_status=dict(status='compiled',label='Source valid-run transports compiled; chapter/container reconciliation pending',boundary=boundary))
proposal=dict(route=route,notes=notes,card=card,boundary=boundary,new_module_glob='BanditRLProof/OnlinePrescientBregmanSource.lean',added_learning_goal='Derive properness and uniqueness from source hypotheses, identify the actual source argmin run, and obtain both printed signed prescient regret bounds.',completion_extension=' Additive source valid-run progress: six fixed transport proofs, not universal attainment or chapter acceptance. '+boundary)
write(RUN/'reader-proposal-v1.json',proposal)
plans=[]
for rel,line in [('BanditRLProof.lean','import BanditRLProof.OnlinePrescientBregmanSource'),('Tests.lean','import Tests.OnlinePrescientBregmanSourceCanary')]:
    p=ROOT/rel;raw=p.read_bytes();assert line.encode() not in raw
    before=RUN/('publication-before-'+p.name);after=RUN/('publication-after-'+p.name)
    write(before,raw);write(after,raw+('\n'+line+'\n').encode('utf8'))
    plans.append(dict(path=p.as_posix(),before_snapshot=before.as_posix(),before_sha256=sha(p),after_snapshot=after.as_posix(),after_sha256=sha(after),delta='Exact raw prefix plus single new import.'))
for key in ['chapters','readings','highlights']:
    p=ROOT/('website/content/'+key+'.json');new=copy.deepcopy(load(p))
    before=RUN/('publication-before-'+key+'.json');after=RUN/('publication-after-'+key+'.json')
    write(before,p.read_bytes())
    if key=='chapters':
        row=next(r for r in new['chapters'] if r['slug']==route)
        row['module_globs'].append(proposal['new_module_glob']);row['learning_goals'].append(proposal['added_learning_goal']);row['completion_definition']+=proposal['completion_extension']
    elif key=='readings':next(r for r in new['readings'] if r['slug']==route)['source_theorems'].append(card)
    else:
        assert not any(r['full_name'] in names for r in new['highlights'])
        new['highlights'].extend(notes)
    write(after,new)
    plans.append(dict(path=p.as_posix(),before_snapshot=before.as_posix(),before_sha256=sha(p),after_snapshot=after.as_posix(),after_sha256=sha(after),delta={'chapters':'Only online-ogd append module/goal/completion suffix.','readings':'Only online-ogd append one source-qualified card.','highlights':'Append six canonical production notes; every old note unchanged.'}[key]))
write(CONTRACT/'exact-publication-plan-v1.json',dict(rows=plans,reader_proposal_sha256=sha(RUN/'reader-proposal-v1.json'),allowed_old_mutations=5,all_other_baseline_paths_immutable=True,other_Books_preserved=True,old_links_fields_preserved=True,shared_registry_expected=11026,public_Tests_excluded=True,global_SGB_untouched=True,generated_site_not_edited=True,source_container_closed=False,chapter_complete=False,whole_goal='active'))
write(RUN/'publication-plan-review-inputs-v1.json',dict(rows=rows([CONTRACT/'exact-publication-plan-v1.json',RUN/'reader-proposal-v1.json',RUN/'registry-baseline-binding-v1.json',RUN/'registry-baseline-v1.json.gz',RUN/'eight-public-values-inspected-v1.json',PUBLIC,ROOT/'Tests/OnlinePrescientBregmanSourceCanary.lean']+[Path(r[k]) for r in plans for k in ['before_snapshot','after_snapshot']])))
write(RUN/'publication-plan-request-v1.md','''# Separate exact publication plan review

Inspect six new per-target notes and one source-qualified card, all five exact before/after transitions, and immutable complete parent shared-registry baseline. Source-facing helper scopes differ: arbitrary E properness, inner-product strict helper, complete algorithm helpers, finite-dimensional source wrappers. Do not transfer common source assumptions to generic helpers or variable monotonicity to unrelated T0 interfaces. Printed variable numeric fixture is +1/2 comparator -1/2<=-11/64. Old card/boundary paragraphs remain historical; current source-run transport explicitly derives properness/hseq, without claiming universal attainment or any of eight container/chapter closure. Reject ambiguous source/Lean assumption or terminal/maximum/movement prose.

No baseline root/reader mutation yet. Approve exactly five old paths plus own contribution manifest/evidence later, six new production canonical IDs, preserving every complete old registry object, other Books/links/frozen data/globalSGB. Only after actual combined root/Tests/full harness may local site builder receive lean-verified. Source contract/BODY/site/FINAL/native/delivery separate. This prospective plan does not authorize merge/deploy or assert website/live updates. New script is only preparation/snapshots; no materialization helper exists yet. Review exact row bytes and logic, with a separate create-only publication-plan-review-v1.md/json and approved_plan_sha256/approved_rows. Bind input manifestSHA and record requiredrepairs. Requested Astra/medium, reused staged actor history, no human/external/runtimeattestation.
''')
fixed()
print('Six notes/one card/five exact old-path transitions prepared, old sources unchanged.')
