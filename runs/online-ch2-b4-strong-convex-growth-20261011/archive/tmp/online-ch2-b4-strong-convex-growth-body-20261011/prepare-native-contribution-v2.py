from pathlib import Path
import hashlib, json, importlib.util

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent / 'native-contribution-candidate-v2.json'
NAME = 'BanditRL.OnlineConvex.stronglyConvex_minimum_growth'
RUN = 'runs/online-ch2-b4-strong-convex-growth-20261011'
draft = ROOT / 'tmp/online-ch2-b4-next-strong-convex-freeze-20261011/application/native-contribution-manifest-draft-v1.json'
m = json.loads(draft.read_text(encoding='utf-8'))
boundary = ('One locally compiled, independently mathematical/semantic-reviewed conditional B4 dependency; supplied attained minimum only. '
    'No existence or uniqueness theorem, actual cumulative FTRL/BTRL minimizer, stability producer, or corrected whole7.47/15.31 guarantee. '
    'Seven Chapter2 forward containers and six future claims, B1-B7 and full B4 remain OPEN; Chapter2 partial, accepted=false, complete proof denominator=null. '
    'Chapters1-16 Goal ACTIVE. Combined gates, reader pixels, Exposition and final bounded acceptance require separate actual receipts. Unmerged/unpublished; no main/live update.')
m['target'] = ('Conditional quadratic growth for SourceProper EReal f on literal convex V subset effectiveDomain f in a real normed space, lambda>=0, '
    'all feasible strong-convex segment inequalities with coefficient lambda/2, supplied p in V with IsMinOn f V p, every q in V. '
    'Conclusion (f p).toReal+(lambda/2)*norm(q-p)^2 <= (f q).toReal, with finite endpoint bridges proved internally. ' + boundary)
r=m['reuse_plan']
r['reused_declarations'] = ['BanditRL.OnlineConvex.SourceProper','BanditRL.OnlineConvex.effectiveDomain',
    'EReal.coe_toReal','EReal.coe_le_coe_iff._simp_1','mul_nonneg','norm_sub_rev']
r['known_consumers'] = ['BanditRL.Tests.OnlineStrongConvexMinimumCanary.square_two_exact_growth',
    'BanditRL.Tests.OnlineStrongConvexMinimumCanary.interval_zero_extended_domain']
r['decision_reason'] = ('One route-local analytic B4 component, installed in the existing shared library and root. No duplicate wrapper/helper. '
    'Two concrete public consumers exercise positive sharp coefficient and zero coefficient with genuine extended domain; they do not establish two independent algorithmic applications. '
    'Selected dependencies above are actual TYPE/VALUE occurrences, not necessity or transitive dependency claims.')
m['reader_contract']={k:True for k in m['reader_contract']}
s=m['semantic_roundtrip']; s['status']='accepted'; s['verdict']='accepted-with-explicit-delta'
s['source_reviewer'] += '; production BODY mathematical/semantic review: '+RUN+'/archive/tmp/online-ch2-b4-strong-convex-growth-body-review-20261011/candidate-body-review-v1.json SHA256 fb4ae375df5851672eb0f3d4bcadbb50956ce8205608c3efe35800812882d6a7'
s['remaining_semantic_delta'] = ('General real normed ambient explicitly generalizes the source finite-dimensional setting. Derived consequence of Definition4.1, not an invented numbered theorem or Chapter4 closure. '
    'hp/hmin/hq are CONDITIONAL_TARGET. Proof uses a direct interior segment contradiction; finite EReal endpoint conversions proved without silently totalizing infinity. '
    'No attainment/uniqueness or algorithm performance claim. Exact sealed header ded5adebef211f810552abbc4eced856dd9fff59f268989e9c1ff5a4ecd3d590; lifecycle fingerprint 4b4f2471e1d85ac984e1171e838809cdf8e3203a1a11816689a31ab4adba85ad.')
g=m['graph_contribution']; g['lean_graph']='new-node'; g['functor_reason']='No independently formalized categorical transport; ambient generalization is an explicit statement delta.'
g['visual_review']='Reader content V3 proposes exactly one card, one lesson/route append and one module glob; inherited full objects and multiplicities preserved. Actual source-bound DOM/pixel review remains required.'
p=m['progress_updates']; p['teaching_route']='updated: one conditional B4 dependency card, source-bound lesson and existing online-ogd module ownership. No new Book/project.'
p['results_ledger']='updated: production focused actual0; two public canary candidates focused/import actual0, independently reviewed before installation. Whole parent/container remains open; fresh combined/final evidence is separate.'
p['website_surfaces']=['website/content/chapters.json','website/content/readings.json','website/content/highlights.json']
m['truth_boundary']=boundary
v=m['verification']; v['focused_checks']=[
    RUN+'/archive/tmp/online-ch2-b4-strong-convex-growth-body-20261011/production-module-focused-v1.json',
    RUN+'/archive/tmp/online-ch2-b4-strong-convex-growth-body-20261011/imported-production-comparison-v1.json SHA256 4c381b3b41761559e18bbd5adeedc93e982e2322f2e9267518f3c66c3a86d0c3',
    RUN+'/archive/tmp/online-ch2-b4-strong-convex-growth-canary-20261011/canary-compiled-candidate-report-v1.json SHA256 f271ef71090fdb432214d2cd87b5c30e0ea9062a8c996407826d8be443cacccf',
    'Production RAW55b37c648437e231f1b967cdc9cfa4102ce1bea6efde3ed81b23884604f89317; exact imported TYPE85/VALUE383 equal candidate; only propext, Classical.choice, Quot.sound. '
    'Both public canary VALUEs genuinely apply the production endpoint as the first conjunct proof; redundant9<=9 is not a third consumer.']
v['bandit_check']='Required next on a clean committed candidate: combined library root, Tests and full harness; focused results do not imply this gate.'
v['site_build']='Required after successful same-source full Lean gate: plain preflight and Lean-verified build to isolated output with exact RAW inputs and HEAD binding.'
v['site_check']='Required official site check, full-object/registry preservation and independent original-pixel reader QA. No site/live acceptance asserted here.'
v['independent_review']='Frozen header/blind/source and production BODY reviews retained. Public canary BODY and reader content application eligibility must precede canonical installation. Combined gates and final bounded acceptance remain separate.'
m['contributor']['role']='Conditional analytic proof author and separate neutral/source/BODY/canary reviewers attributed in immutable evidence.'
l=m['learning_contract']; l['failure_class']='NONE'
l['salvage']={'required':True,'status':'completed','reason':
    'Current mathematical construction compiled first try. Retained historical API/environment probe repair (unknown liftIO; wrapper GBK print after actual0), two canary simp/unfold implementation failures, and parent archive/staging preparation repairs; no source refutation or target deletion. No failed result relabeled as success.',
    'promoted_fragments':[NAME]+r['known_consumers'],'discarded_fragments':[]}
l['parallelism']['direction_fingerprints']=['conditional-growth-segment:55b37c648437e231f1b967cdc9cfa4102ce1bea6efde3ed81b23884604f89317']
l['parallelism']['expected_information_gain']='One mathematical construction route; distinct reviewers and concrete consumer author are role separation, not competing proof routes or a scheduler experiment.'
l['cross_route_blind_spot_audit']['canonical_route']='Direct interior segment contradiction with finite EReal endpoint bridge.'
l['cross_route_blind_spot_audit']['selection_reason']='One verified construction; literal source topology retained separately without claiming all dependencies closed.'
b=l['reader_backpressure']; b['exposition_evidence']='Reviewed full reader content append candidates; actual DOM/pixels and Exposition Seal remain required. Zero reader-debt budget is not measured acceptance.'
b['source_expansion_nodes']=['D41','D218','FINITE-FEASIBLE-VALUES','CONDITIONAL-ATTAINED-MINIMUM','OPEN-ACTUAL-CUMULATIVE-PRODUCER','OPEN-CORRECTED-WHOLE-BOUND']
b['lean_expansion_nodes']=[NAME]; b['assumptions_preserved']=True; b['boundary_preserved']=True
with OUT.open('x',encoding='utf-8',newline='\n') as f: json.dump(m,f,ensure_ascii=False,indent=2); f.write('\n')
spec=importlib.util.spec_from_file_location('contract_check',ROOT/'tools/check_contributor_contract.py')
check=importlib.util.module_from_spec(spec); spec.loader.exec_module(check)
_,errors=check.validate_contract(OUT)
print(json.dumps({'path':OUT.relative_to(ROOT).as_posix(),'sha256':hashlib.sha256(OUT.read_bytes()).hexdigest(),'pure_validator_errors':errors,'installed':False},indent=2))
assert not errors
