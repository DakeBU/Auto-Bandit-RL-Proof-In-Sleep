from common import *
import copy, gzip
fixed()
st=load(CONTRACT/'stabilized-v1.json')
assert sha(PUBLIC)==load(RUN/'all-five-public-inspected-v1.json')['module_sha256']
route='online-ogd'
boundary=('Five derived same-run cumulative interfaces are additive progress for a REQUIRED Chapter 2 prescient forward dependency. '
    'Successful actual Option outputs and all reached states in interior X are explicit conditional hypotheses; source closedness and strict convexity are not asserted to guarantee a valid run. '
    'The source X/interior generator representation, finite-on-V/no-bottom source loss transport into proper/global-support premises, and a full source valid-run wrapper remain REQUIRED/OPEN. '
    'This does not complete Algorithm 15.8, Theorem 15.30, Chapters 6 or 15, or Chapter 2. All eight Chapter 2 forward containers remain open; Chapter 2 is partial with null complete proof denominator, Chapters 3-16 unenumerated/null, and the whole Chapters 1-16 Goal ACTIVE. '
    'Historical package boundary paragraphs describe their respective scopes; these five new interfaces add sharp fixed/variable cumulative bounds under their explicitly stated actual-run assumptions. '
    'Stacked on OPEN draft unmerged PR #211 exact '+BASE+'. No merge, deployment, main, live or CI acceptance claim.')
source=('Orabona, Online Learning: A Modern Introduction Using Convex Optimization, arXiv:1912.13213v10 (2026-06-21), '
    'Chapter 2 prescient observation printed14/PDF26; source properness/global subgradients printed16-17/PDF28-29; '
    'Definition6.4 printed63/PDF75; Algorithm15.8 and Theorem15.30 printed265-266/PDF277-278. Pinned PDF SHA256 '+PDF_SHA+'. ')
objects=('Use the canonical ordered Bregman expression B(a;b)=psi(a)-psi(b)-Dpsi(b)[a-b], with target first and derivative base second. '
    'Source spaces are finite Euclidean and the generator is defined on X; the reusable Lean interfaces use a complete real inner-product space and an ambient representative, differentiable on interior X. '
    'Every actual state through T lies in interior X. This licenses the actual derivatives, not boundary values of a default total fderiv. ')
assumptions=('V is convex; each played extended-real loss is SourceProper and has a global ambient supporting subgradient at every feasible point. '
    'These supports compare every ambient y and certify finite compared loss values; no infinity subtraction is used. Steps before T are strictly positive. '
    'The same canonical iterate returns some(x(t)) for every t<=T; this is a posthoc mathematical success hypothesis, not an input to the algorithm. '
    'The whole current loss is read before its paid successor prediction. Source loss_(t+1) is Lean loss t, source x0 is Lean x0, and source eta_T is Lean eta(T-1). '
    'No comparator, desired regret inequality, future oracle, executable optimizer, measurable selection or universal attainment is assumed as an algorithm. ')
normalization=('Fixed steps allow T=0: empty sums and the derived identity x(0)=x0 give the zero-horizon endpoint. '
    'Variable steps require T>0 and nonincrease only between played rounds; the finite maximum is exactly over states0,...,T-1 and never includes x(T). '
    'No bounded domain or nonnegative arbitrary M is added to sharp interfaces. Printed corollaries additionally assume V subset X and strict convexity on X, and derive terminal B>=0 before dropping its negative term. '
    'Negative movement terms remain in both printed corollaries. ')
canaries=('Two complete public Test conjunctions exercise the five interfaces. On V=[-1,1] and psi(z)=z^4/4+z^2/2, '
    'restricted absolute then affine -5z/8 at fixed step1 select the actual states1/2 ->0 ->1/2. Ordered movements are11/64 and9/64; at u=-1/2 the terminal divergence is5/8, and sharp/printed numerical bounds are -9/8<=-5/16 and -9/8<=5/16. '
    'A genuinely decreasing schedule1,1/2 uses the different second loss -5z/4 and proves its actual unique penalized minimum, again giving1/2 ->0 ->1/2. '
    'Weighted movements equal29/64; the previous-state maximum is5/8 for u=-1/2 and9/64 for u=1/2, while the latter initial divergence is0. '
    'Sharp and printed numeric instances are -7/4<=-29/64 and -1/2<=-11/64. Thus the maximum cannot be silently replaced by the initial value. '
    'These are concrete finite diagnostics, not additional numbered source results or canonical Book nodes. ')
ps='BanditRL.OnlinePrescientBregman.'
specs=[
 ('iterate_divergence_sum','Sum the comparisons from the very same actual updates',
  r'\begin{gathered}L_T(u)=\sum_{t=0}^{T-1}(\ell_t(x_{t+1})-\ell_t(u)),\\ L_T(u)\le\sum_{t=0}^{T-1}\frac{B(u;x_t)-B(u;x_{t+1})}{\eta_t}-\sum_{t=0}^{T-1}\frac{B(x_{t+1};x_t)}{\eta_t}.\end{gathered}',
  'For each t<T, extract the two actual consecutive successful states and obtain both ambient derivatives from their interior membership. Apply the actual iterate_one_step producer, divide by the positive current step, and sum. This proves the desired inequality from actual minima; it does not assume the single-step regret bound.'),
 ('iterate_fixed_sharp','Telescope constant steps while retaining both negative residuals',
  r'L_T(u)\le\frac{B(u;x_0)}{\eta}-\frac{B(u;x_T)}{\eta}-\frac1\eta\sum_{t=0}^{T-1}B(x_{t+1};x_t),\quad\eta>0.',
  'Apply the actual same-run divergence sum with a constant positive schedule. Option.some injectivity at state0 identifies x(0) with the initial x0. Pull the common denominator outside the sum and telescope consecutive potentials. Keep the negative terminal divergence and the entire negative movement sum; convexity of the generator is not needed for this signed algebraic result.'),
 ('iterate_variable_sharp','Bound the weighted telescope and keep its final negative term',
  r'\begin{gathered}T>0,\quad B(u;x_t)\le M\ (0\le t<T),\quad0<\eta_{t+1}\le\eta_t,\\ L_T(u)\le\frac{M}{\eta_{T-1}}-\frac{B(u;x_T)}{\eta_{T-1}}-\sum_{t=0}^{T-1}\frac{B(x_{t+1};x_t)}{\eta_t}.\end{gathered}',
  'Apply the same actual divergence sum. Reuse the canonical weighted_potential_sum with potential a=2B and cap C=2M; cancel the nonzero constant2. The nonincreasing positive steps make the intervening reciprocal differences nonnegative, so only previous potentials need the cap M. M is arbitrary real; no bounded-domain or generator convexity premise is required for this signed inequality. The final state remains an explicit negative residual.'),
 ('iterate_fixed_regret','Derive the printed fixed-step form by terminal nonnegativity',
  r'L_T(u)\le\frac{B(u;x_0)}{\eta}-\frac1\eta\sum_{t=0}^{T-1}B(x_{t+1};x_t),\quad\eta>0.',
  'Start with iterate_fixed_sharp. From V subset X, comparator u belongs to X; the terminal actual state is in interior X and has its actual derivative. Strict convexity supplies convexity, and the canonical divergence_nonneg theorem gives B(u;x(T))>=0. Divide by positive eta and drop only the negative terminal term. The negative movement sum is preserved. This corresponds to the fixed-step main-text result whose source proof is left as an exercise, under the explicit conditional run/hypothesis delta.'),
 ('iterate_variable_regret','Use the exact previous-state maximum in the printed variable form',
  r'L_T(u)\le\frac{\max_{0\le t<T}B(u;x_t)}{\eta_{T-1}}-\sum_{t=0}^{T-1}\frac{B(x_{t+1};x_t)}{\eta_t},\quad T>0.',
  'The finite range0,...,T-1 is nonempty because T>0. Finset.le_sup\u0027 bounds every previous divergence by that actual maximum; use it as M in iterate_variable_sharp. The same source-domain, strict-convexity and actual-terminal-derivative argument proves terminal nonnegativity. Drop only its negative term divided by the positive last played step; retain all weighted movements. This is a fixed-horizon deterministic statement, without an empty-maximum convention or future round eta(T).')]
assert [ps+x[0] for x in specs]==[t['declaration'] for t in st['targets']]
prior=ROOT/'tmp/online-ch2-prescient-causal-site-v3/books/registry.json'
receipt=ROOT/'runs/online-ch2-prescient-causal-20261009/registry-inspected-v3.json'
old=load(prior)
assert sha(prior)==load(receipt)['actual_current_registry_sha256'] and len(old['nodes'])==11015 and old['lean_verified']
assert old['source_commit']=='f6a0ab4a2c2494afcd5f582bb744efffea9451bc'
write(RUN/'registry-baseline-v1.json.gz',gzip.compress(prior.read_bytes(),mtime=0))
names={r['id'][len('declaration:'):] for r in old['nodes']}
names.update(ps+x[0] for x in specs)
write(RUN/'registry-baseline-binding-v1.json',dict(prior_source=prior.as_posix(),prior_complete_raw_sha256=sha(prior),compressed_snapshot_sha256=sha(RUN/'registry-baseline-v1.json.gz'),prior_actual_registry_receipt_sha256=sha(receipt),source_commit=old['source_commit'],total_shared_nodes=11015,identity=old['identity'],expected_new_canonical_ids=['declaration:'+ps+x[0] for x in specs],expected_new_definitions=0,expected_new_theorems=5,expected_total=11020,all_public_Test_and_generated_Test_nodes_excluded=True,main_live_updated=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
graph={n['name']:n for n in load(RUN/'all-five-value-graph-v1.json')}
notes=[]
for i,(short,title,formula,proof) in enumerate(specs):
    n=ps+short
    parents=sorted(p for p in graph[n]['value_dependencies'] if p in names and p!=n)
    notes.append(dict(full_name=n,title=title,chapter=route,featured=False,teaching_order=187+i,
        plain=objects+assumptions+normalization,math=formula,intuition=proof,
        why='Close a conditional same-run cumulative proof edge in the required Chapter 2 prescient dependency.',
        position=source+'Derived interface, not a separately numbered source result.',proof_idea=proof,
        lean_notes=objects+assumptions+normalization+proof+' '+canaries+boundary,dependencies=parents))
card=dict(label='Chapter 2 prescient dependency: same-run cumulative sharp and printed bounds',pages='printed14,16-17,63,265-266 / PDF26,28-29,75,277-278',pdf_page=277,url='https://arxiv.org/pdf/1912.13213v10',math=specs[-1][2],plain=objects+assumptions+normalization,fallback=assumptions+normalization,relationship=source+boundary,
    contract=dict(model='Same actual current-known-loss Option recursion; successful/interior run explicitly assumed.',assumptions=objects+assumptions+normalization,parameters='Lean t=source round t+1; x0 is actual initial state; eta(T-1) is the last played step. Fixed T>=0; variable T>0.',regret='Same actual successor-loss finite-part sum with sharp negative terminal/movement terms; printed forms drop terminal only after nonnegativity.',guarantee=canaries+boundary),
    local_status=dict(status='compiled',label='Conditional cumulative interfaces compiled; full source run remains open',boundary=boundary))
proposal=dict(route=route,notes=notes,card=card,boundary=boundary,new_module_glob='BanditRLProof/OnlinePrescientBregmanRegret.lean',added_learning_goal='Derive sharp fixed and decreasing-step cumulative regret from the same actual prescient updates, with correct previous-state maximum and negative movement terms.',completion_extension=' Additive conditional cumulative progress: five derived same-run interfaces; full source transport and valid-run wrapper remain open. '+boundary)
write(RUN/'reader-proposal-v1.json',proposal)
plans=[]
for rel,line in [('BanditRLProof.lean','import BanditRLProof.OnlinePrescientBregmanRegret'),('Tests.lean','import Tests.OnlinePrescientBregmanRegretCanary')]:
    p=ROOT/rel; raw=p.read_bytes(); assert line.encode() not in raw
    before=RUN/('publication-before-'+Path(rel).name); after=RUN/('publication-after-'+Path(rel).name)
    write(before,raw); write(after,raw+('\n'+line+'\n').encode('utf8'))
    plans.append(dict(path=p.as_posix(),before_snapshot=before.as_posix(),before_sha256=sha(p),after_snapshot=after.as_posix(),after_sha256=sha(after),delta='Raw prefix preserved plus one import.'))
for key in ['chapters','readings','highlights']:
    p=ROOT/('website/content/'+key+'.json'); new=copy.deepcopy(load(p))
    before=RUN/('publication-before-'+key+'.json'); after=RUN/('publication-after-'+key+'.json')
    write(before,p.read_bytes())
    if key=='chapters':
        row=next(r for r in new['chapters'] if r['slug']==route)
        row['module_globs'].append(proposal['new_module_glob']); row['learning_goals'].append(proposal['added_learning_goal']); row['completion_definition']+=proposal['completion_extension']
    elif key=='readings': next(r for r in new['readings'] if r['slug']==route)['source_theorems'].append(card)
    else:
        assert not any(r['full_name'] in {n['full_name'] for n in notes} for r in new['highlights'])
        new['highlights'].extend(notes)
    write(after,new)
    plans.append(dict(path=p.as_posix(),before_snapshot=before.as_posix(),before_sha256=sha(p),after_snapshot=after.as_posix(),after_sha256=sha(after),delta={'chapters':'Only online-ogd append module/goal/completion suffix.','readings':'Only online-ogd append one source-qualified card.','highlights':'Append five canonical production notes; preserve all old notes.'}[key]))
write(CONTRACT/'exact-publication-plan-v1.json',dict(rows=plans,reader_proposal_sha256=sha(RUN/'reader-proposal-v1.json'),allowed_old_mutations=5,all_other_baseline_paths_immutable=True,other_Books_preserved=True,old_links_and_fields_preserved=True,shared_registry_not_per_Book=True,global_SGB_untouched=True,generated_site_not_edited=True,source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
write(RUN/'publication-director-v1.md','Prospective exact five-path materialization only; no existing root/Test/reader mutation yet. Five derived production proofs, not five printed results. Actual VALUE parents come from the inspected compiler graph and known canonical registry IDs; imports/source overlays are not implication edges. Preserve every old field/link/other Book. Full applicable combined Lean gate must precede lean-verified site build. Shared baseline11015 + five canonical production IDs =11020; public/generated Tests excluded. Functor none-found-with-reason: same-setting signed-potential telescope reuses canonical weighted potential, without a new proved cross-setting map. '+boundary+' '+canaries)
fixed()
print('Five source-qualified notes and exact five-path prospective plan prepared; no baseline mutation.')
