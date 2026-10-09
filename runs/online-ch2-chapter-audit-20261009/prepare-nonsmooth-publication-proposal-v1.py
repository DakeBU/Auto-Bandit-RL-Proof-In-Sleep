from lower_common_v1 import *

reviewed(); headers(3)
assert load(RUN/'nonsmooth-canaries-candidate-v1.json')['full_root_Tests_harness_reader_registry_site_PENDING']
test=ROOT/'Tests/OnlineNonsmoothExamplesCanary.lean'
plans=[]
for filename,line in [('BanditRLProof.lean','import BanditRLProof.OnlineNonsmoothExamples'),
                      ('Tests.lean','import Tests.OnlineNonsmoothExamplesCanary')]:
    p=ROOT/filename; raw=p.read_bytes(); assert line.encode() not in raw
    snap=RUN/(filename.replace('.lean','')+'-prefix-before-nonsmooth-v1.lean')
    write(snap,raw)
    append='\n'+line+'\n'
    plans.append(dict(path=p.as_posix(),snapshot=snap.as_posix(),baseline_sha256=sha(p),
        append_exact_utf8=append,permitted_result_sha256=hashlib.sha256(raw+append.encode()).hexdigest()))
write(CONTRACT/'nonsmooth-exact-import-plan-v1.json',dict(rows=plans,old_raw_prefix_must_remain_identical=True))
route='online-subgradient-differentiability'
boundary='Three actual new public proofs serve TWO introductory source families at printed16/PDF28; five complementary public canaries include nondegenerate scalar and plane cases, plus zero-normal and dimension-zero boundaries. This is a bounded nonsmooth example package and accepted source inventory, not Chapter2 acceptance. All required Chapter2 numbered/unnumbered branches, prescient and future-chapter references and appendices remain required; proof-leaf total unknown(null). Chapter1 already delivered in OPEN draft PR203; this branch is stacked on its exact unmerged head '+BASE+'. Whole Chapters1-16 Goal ACTIVE; no main/live, merge or deployment claim.'
qualification='Pinned source opening Section2.2 says the hinge loss is not differentiable. Retain that sentence and distinguish ordinary pointwise ambient differentiation from global differentiation: for nonzero effective normal it fails on the margin hyperplane and is smooth off it; zero effective normal gives the constant1 loss. This is a separately reviewed mathematical qualification, not a modified pinned source or author-endorsed erratum.'
assumptions='Ordinary real ambient Frechet differentiation. Every real c, label y and feature z; finite-dimensional real inner-product E includes Euclidean spaces and dimension0. No nonzero label/normal, positive dimension, boundedness, closedness, properness/support/derivative oracle is assumed. Shift c generalizes the printed center10; effective normal a generalizes the labelled form without restricting labels to plus/minus1.'
proofs=[
    'The loss is the real norm composed with the affine translation w↦w-c, hence convex. Away from c, w-c is nonzero, so abs is differentiable there. If a derivative existed at c, composition with t↦t+c at0 would differentiate abs at0, a contradiction.',
    'The affine margin and constant0 are convex, so their maximum is convex. At inner(a,x)=1 the complete support segment contains0 and -a; a singleton derivative would force a=0, contradicting that margin. Off the hyperplane the actual support is a singleton. The complete source differentiability theorem produces a genuine local real germ, and its finite-hinge representative gives the actual derivative.',
    'Substitute a=y smul z using inner(y smul z,x)=y inner(z,x). If a is nonzero, x=inner(a,a) inverse smul a has margin1 because inner(a,a) is nonzero, so a global derivative is impossible. If a=0 all margins vanish and the function is constantly1. This proves the exact global iff for the same function, including zero and negative labels.'
]
maths=[r'f_c(x)=|x-c|,\quad f_c\text{ convex},\quad Df_c(x)\text{ exists}\iff x\ne c.',
       r'h_a(x)=\max(1-\langle a,x\rangle,0),\quad Dh_a(x)\text{ exists}\iff\langle a,x\rangle\ne1.',
       r'h_{y,z}(x)=\max(1-y\langle z,x\rangle,0),\quad h_{y,z}\text{ differentiable everywhere}\iff y\,z=0.']
titles=['Shifted absolute: exact kink and smooth complement','Hinge: exact ambient margin hyperplane','Labelled hinge: the effective-normal global criterion']
graph=load(RUN/'nonsmooth-compiled-selected-graph-v1.json'); nodes={n['name']:n for n in graph['nodes']}
notes=[]
for i,t in enumerate(reviewed()['targets']):
    parents=[n for n in nodes[t['declaration']]['value_dependencies'] if n.startswith('BanditRL.OnlineConvex.')]
    notes.append(dict(full_name=t['declaration'],title=titles[i],chapter=route,featured=False,teaching_order=150+i,
        plain=proofs[i],math=maths[i],intuition='The kink concerns the ambient function at a margin point; zero effective normal removes the kink.',
        why='Close the two required introductory nonsmooth source families with exact pointwise and global criteria.',
        position='Orabona arXiv:1912.13213v10, 2026-06-21; Section2.2 opening paragraph, printed16/PDF28; SHA '+PDF_SHA+'.',
        proof_idea=proofs[i],lean_notes=assumptions+' '+qualification+' '+boundary,dependencies=parents))
card=dict(label='Section2.2 opening examples: shifted absolute and labelled hinge',pages='printed16 / PDF28',
    pdf_page=28,url='https://arxiv.org/pdf/1912.13213v10',math=maths[0]+'\qquad '+maths[1]+'\qquad '+maths[2],
    plain=qualification+' '+assumptions+' '+' '.join(proofs),fallback=qualification+' '+' '.join(proofs),
    relationship='Three derived exact criteria for two introductory source families, reusing the full singleton-support and hinge-support producers in this same Lean project. '+qualification,
    contract=dict(model='Deterministic static finite-dimensional real convex analysis, without an algorithm or feedback protocol.',
        assumptions=assumptions,parameters='Every c and every point; every effective normal a; every real label y and feature z. Pointwise iff and global iff are separate conclusions.',
        regret='No regret, policy, measurable selection, stochastic or complexity guarantee is asserted by these three examples.',
        guarantee='All three losses are globally convex; the exact kink sets are {c} and {x:inner(a,x)=1}; labelled hinge is globally differentiable exactly when y smul z=0. '+qualification),
    local_status=dict(status='compiled',label='Exact example bodies compiled; package integration pending',boundary=boundary))
write(RUN/'nonsmooth-reader-proposal-v1.json',dict(route=route,card=card,notes=notes,boundary=boundary,
    new_module_glob='BanditRLProof/OnlineNonsmoothExamples.lean',
    added_learning_goal='Separate an actual ambient kink, off-margin differentiability, tangential differentiation at the same point and zero effective normal.',
    completion_extension='Additive current extension: three derived exact convexity/differentiability proof declarations for TWO introductory families, with five complementary canaries; their package and Chapter2 acceptance remain separate. '+boundary,
    no_old_card_note_ID_link_or_formula_removal=True,not_yet_integrated=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
mutable=['BanditRLProof.lean','Tests.lean','website/content/chapters.json','website/content/readings.json','website/content/highlights.json']
for p in mutable[2:]: write(RUN/('publication-before-'+Path(p).name), (ROOT/p).read_bytes())
write(CONTRACT/'nonsmooth-future-publication-scope-v1.json',dict(
    permitted_new_paths=['BanditRLProof/OnlineNonsmoothExamples.lean','Tests/OnlineNonsmoothExamplesCanary.lean',
        'research-wiki/contribution-contracts/ONLINE-CH2-NONSMOOTH-20261009.json','research-wiki/retrieval-index/ONLINE-CH2-NONSMOOTH-20261009.md'],
    mutable_old_paths=mutable,exact_import_plan_sha256=sha(CONTRACT/'nonsmooth-exact-import-plan-v1.json'),
    reader_proposal_sha256=sha(RUN/'nonsmooth-reader-proposal-v1.json'),
    rules='Roots only exact raw prefix append. Chapters only target route module glob/one goal/additive completion extension; all previous fields and source boundary preserved. Readings only append one source-qualified card to same route; highlights only append three named notes. Every other parsed subtree/value, old Lean/Test/root prefix, pins, global SGB and shared stores immutable. OWN run/contract/task lifecycle evidence allowed; no coverage Chapter2 acceptance yet.',
    chapter_complete=False,whole_Goal_status='ACTIVE'))
paths=[test,PRODUCTION,CONTRACT/'nonsmooth-canary-contracts-v1.json',CONTRACT/'nonsmooth-canary-contracts-v2.json',
    CONTRACT/'nonsmooth-canary-operative-version-v2.json',CONTRACT/'nonsmooth-exact-import-plan-v1.json',CONTRACT/'nonsmooth-future-publication-scope-v1.json',
    RUN/'nonsmooth-reader-proposal-v1.json',RUN/'nonsmooth-canary-blind-reconstruction-v2.md',RUN/'nonsmooth-canary-blind-receipt-v2.json',
    RUN/'nonsmooth-canaries-candidate-v1.json',RUN/'nonsmooth-canaries-public-values-v1.lean',RUN/'nonsmooth-canaries-public-values-v1.json',
    RUN/'nonsmooth-canaries-focused-build-v1.json',RUN/'nonsmooth-canaries-focused-build-v2.json',RUN/'nonsmooth-canaries-failure-classification-v1.json',
    RUN/'nonsmooth-compiled-selected-graph-v1.json',RUN/'nonsmooth-compiled-graph-inspected-v1.json',RUN/'nonsmooth-graph-required-value-pairs-v1.json',
    RUN/'nonsmooth-production-BODY-review-v1.md',RUN/'nonsmooth-production-BODY-review-v1.json']
paths += [Path(p['snapshot']) for p in plans]
paths += [RUN/('publication-before-'+Path(p).name) for p in mutable[2:]]
paths += [ROOT/'Tests/OnlineGradientDescentSourceCanary.lean']
paths += [ROOT/p for p in mutable]
paths += [RUN/'nonsmooth-canary-blind-packet-v2.md',RUN/'nonsmooth-canary-blind-input-v2.json',
    RUN/'nonsmooth-graph-receipt-collision-failure-v1.json',RUN/'nonsmooth-compiled-selected-graph-command-v2.json',
    RUN/'nonsmooth-compiled-selected-graph-data-v2.json',CONTRACT/'nonsmooth-targets-draft-v1.json']
paths += list((RUN/'nonsmooth-native-fences-v1').glob('*.json'))
paths += [RUN/('nonsmooth-safe-%02d-v1.json'%i) for i in range(1,9)]
write(RUN/'nonsmooth-canary-publication-review-input-v1.json',dict(files=rows(paths),
    scope='Five exact canary contracts and actual BODYs, explicit v1->v2 same-point delta and precise future publication/root append scope; not Chapter2 final acceptance.',
    requested_review='Compare v2 neutral reconstruction with every full canary body/type, nondegenerate examples and genuine zero branches; actual kernel/axioms/direct VALUE pairs. Separately judge future reader qualification and exact bounded mutations before any canonical integration.',
    production_BODY_already_accepted_sha256=sha(RUN/'nonsmooth-production-BODY-review-v1.json'),
    publication_not_yet_mutated=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
reviewed();headers(3)
print('Canary BODY and precise publication/root append review input ready; canonical files untouched.')
