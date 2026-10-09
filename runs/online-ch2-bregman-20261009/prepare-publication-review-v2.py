from common import *
import copy
fixed()
c=load(RUN/'complete-candidate-inspected-v1.json')
assert c['both_selected_numeric_tails_retain_public_helper'] and sha(PUBLIC)==c['production_sha256']
p=ROOT/'Tests/OnlineBregmanProximalCanary.lean'
assert sha(p)==c['test_sha256']
old=load(RUN/'reader-proposal-v1.json');new=copy.deepcopy(old)
before='Two proposed exact public Test families use ψ(z)=z^4/4+z^2/2 with abs loss, center1/2 and actual minimum0; and ψ(z)=z^2/2 on[0,1] with center-1 outsideV and actual minimum0. Their minimum/strictness and final numeric VALUE use remain separate pending Test gates at this proposal stage. They are illustrative instances, not new printed results.'
after='Two compiled public Test families prove actual strict convexity, polynomial derivatives and minimizing conditions: ψ(z)=z^4/4+z^2/2 with nonsmooth abs loss, center1/2 and minimum0; and ψ(z)=z^2/2 on[0,1] with center-1 outsideV and boundary minimum0. The ordered nonquadratic divergences are9/64 and11/64. Each universal comparison and separately selected final numerical proof branch retains actual public proximal_one_step VALUE; final bounds -1/2<=-5/16 and -1/2<=1/2 use equality transport of that comparison. Divergence formulas also use actual public gradient conversion. Nonnegative has a full generic public VALUE witness, with no claimed concrete Test VALUE use. These are illustrative instances, not new printed results, an existence theorem or a causal algorithm.'
apis={
 'divergence':'Actual Mathlib fderiv produces the canonical continuous dual map.',
 'divergence_self':'Actual continuous-linear-map zero evaluation and scalar cancellation.',
 'three_point_identity':'Actual Mathlib ContinuousLinearMap.sub_apply, map_sub and scalar ring algebra.',
 'divergence_nonneg':'Actual Mathlib ConvexOn.comp_affineMap, ConvexOn.le_slope_of_hasDerivAt and HasFDerivAt.comp_hasDerivAt on the feasible affine segment.',
 'proximal_one_step':'Actual BanditRL.OnlineProximal.convex_minimizer_comparison and own three_point_identity are compiled VALUE parents. Actual Mathlib HasFDerivAt.comp/sub/sub_const/const_smul and positive scalar multiplication differentiate the exact penalty.',
 'divergence_eq_gradient':'Actual Mathlib DifferentiableAt.hasGradientAt and HasGradientAt.fderiv_apply recover the gradient pairing.'
}
for note in new['notes']:
    assert before in note['lean_notes']
    note['lean_notes']=note['lean_notes'].replace(before,after)+' '+apis[note['full_name'].rsplit('.',1)[1]]
write(RUN/'reader-proposal-v2.json',new)
plan=copy.deepcopy(load(CONTRACT/'exact-publication-plan-v1.json'))
for n in ['readings','highlights']:
    row=next(r for r in plan['rows'] if r['path'].endswith('/'+n+'.json'))
    material=load(row['after_snapshot'])
    if n=='highlights':
        byname={x['full_name']:x for x in new['notes']}
        material['highlights']=[byname.get(x['full_name'],x) for x in material['highlights']]
    else:
        card=next(r for r in material['readings'] if r['slug']==new['route'])['source_theorems'][-1]
        card['plain']+=' '+after
        card['contract']['guarantee']+=' '+after
        new['card']=copy.deepcopy(card)
    dest=RUN/('publication-after-'+n+'-v2.json');write(dest,material)
    row['after_snapshot']=dest.as_posix();row['after_sha256']=sha(dest)
    row['delta']+='; final concrete compiled Test narrative and actual local/Mathlib parent explanation'
# Bind the exact final card material separately; v2 notes and final card remain explicit.
write(RUN/'reader-final-card-v2.json',new['card'])
plan['reader_proposal_sha256']=sha(RUN/'reader-proposal-v2.json')
plan['final_card_sha256']=sha(RUN/'reader-final-card-v2.json')
plan['previous_plan_sha256']=sha(CONTRACT/'exact-publication-plan-v1.json')
write(CONTRACT/'exact-publication-plan-v2.json',plan)
write(RUN/'canary-BODY-publication-review-packet-v2.md','Review actual final two Test BODYs, all complete conjunctions AND separately selected final numeric proof expressions, full VALUE/four standard axiom outputs/native fences, selected8node graph and8actual VALUE parent pairs. Two failed canary implementation versions retained: imports/id, then real inner simp-index instance; read-only APIprobe actual0 justified typed equality repairv3. Production immutable at prior BODYaccepted SHA; no target/context weakening. Exact raw/native canary hashes distinguished in reviewed stabilized contract. Concrete nonnegative use was only planned; no such actual Test VALUE claim, generic witness actual0. Separately assess exact future5oldfile transitions in exact-publication-plan-v2.json; v1 future bytes never applied. Preserve all other baseline, old nodes/formulas/IDs/links and otherBooks. Six exact public notes and1sourcequalified card with source-vs-Lean deltas/fullsourceOPEN. Proposed imports only2; no canonical mutation yet. Approve materialization only after review. Combined root/Tests/fullharness/sharedregistry/site/DOM/pixels/FINAL/native/delivery remain separate pending. Do not infer chapter/source/Goal completion.')
excluded={'lifecycle-state.json','lifecycle-sessions.jsonl','own-artifact-journal.md','trials.jsonl'}
paths=[PUBLIC,p]+[x for x in RUN.iterdir() if x.is_file() and x.name not in excluded]+list(CONTRACT.glob('*'))
write(RUN/'canary-BODY-publication-review-inputs-v2.json',dict(rows=rows(paths),allowed_new_outputs=['canary-BODY-publication-review-v2.md','canary-BODY-publication-review-v2.json'],no_existing_input_changes=True))
fixed()
print('Actual canary BODY, individually selected numeric tails and exact5path reader/import plan ready for distinct review.')
