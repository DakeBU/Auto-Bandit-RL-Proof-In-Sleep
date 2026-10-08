from common_integrated_v2 import *
fixed_integrated()
prior=Path('runs/online-square-minimum-20261008')
s=(prior/'verify-registry-v1.py').read_text(encoding='utf8')
s=s.replace('common_integrated_v1','common_integrated_v2').replace('tmp/online-square-minimum-site-v1','tmp/online-iid-benchmark-site-v2')
s=s.replace('registry-base-snapshot-v1','registry-base-snapshot-v2').replace('full-fence-bindings-v1','full-fence-bindings-v2').replace('actual-public-canary-headers-v1','actual-public-canary-headers-v2')
s=s.replace('10913','__TOTAL__').replace('10906','10913').replace('__TOTAL__','10923')
s=s.replace('len(production) == 7','len(production) == 10').replace("== 11 and len(reading['teaching_route'])", "== 12 and len(reading['teaching_route'])")
s=s.replace('len(notes) == 6','len(notes) == 8').replace('len(headers) == 6','len(headers) == 8').replace('production[:6]','production[:8]')
start=s.index('for phrase in [')
end=s.index('module_path =',start)
phrases=['not eight printed theorems','Generally infinite','BEFORE','a.s.','only on legal unit tuples','consumer only',
    'starts at1/2','distribution-known oracle','T>0','asymptotic-success equivalence','randomization/general filtration',
    'five older main-relative','unknown(null)','totalGoalACTIVE','not main/live','Safe-verify itself does not compile','future-aware']
s=s[:start]+'for phrase in '+repr(phrases)+':\n    assert phrase in text, phrase\n'+s[end:]
s=s.replace('meanPredict_bestRegret_refined','meanPredict_expectedFixed_excess').replace("'registry-v1.json'","'registry-v2.json'")
s=s.replace('new_registry_nodes=7','new_registry_nodes=10').replace('new_public_proofs=6','new_public_proofs=8').replace('new_public_definitions=1','new_public_definitions=2')
s=s.replace('source_cards=11','source_cards=12').replace('new_proof_notes=6','new_proof_notes=8').replace('six_actual_headers_present','eight_actual_headers_present')
s=s.replace('named_canaries=20','named_canaries=28').replace('expected_fixed_benchmark_remains_required=True','deterministic_expected_fixed_core_closed=True, randomized_and_asymptotic_source_coverage_required=True')
s=s.replace('7new shared production nodes; six exact','10new shared production nodes; eight exact')
write(RUN/'verify-registry-v2.py',s)
s=(prior/'capture-reader-v1.cjs').read_text(encoding='utf8')
start=s.index(" const names=")
end=s.index(' const nodes=',start)
names=['expectedFixedMinimum','expectedFixedMinimum_eq_variance','history_policy_expectedFixed_excess','meanPredict_expectedFixed_excess']
proofs=[r['name'].rsplit('.',1)[1] for r in load(CONTRACT/'targets-v2.json')['rows']]
s=s[:start]+' const names='+json.dumps(names)+'; const proofNames='+json.dumps(proofs)+';\n'+s[end:]
s=s.replace('length===14','length===15').replace("10,'square-minimum-source-card-v1.png',1,11", "11,'iid-benchmark-source-card-v2.png',1,12")
s=s.replace('reader-first-viewport-v1','reader-first-viewport-v2').replace('public-note-${i+1}-v1','public-note-${i+1}-v2').replace('module-new-declaration-${i+1}-v1','module-new-declaration-${i+1}-v2')
s=s.replace('formula-render-v1','formula-render-v2').replace('actualSourceGuideMathContainers:14','actualSourceGuideMathContainers:15').replace('newPublicNoteMathContainers:6','newPublicNoteMathContainers:8')
s=s.replace('actual-current-square-minimum-panels-and-catalog-captured','actual-current-expected-fixed-causal-IID-panels-and-catalog-captured')
write(RUN/'capture-reader-v2.cjs',s)
s=(prior/'capture-reader-v1.py').read_text(encoding='utf8').replace('common_integrated_v1','common_integrated_v2')
s=s.replace('online-square-minimum','online-iid-benchmark').replace('-site-v1','-site-v2').replace('registry-v1','registry-v2')
s=s.replace('capture-reader-v1.cjs','capture-reader-v2.cjs').replace('formula-render-v1','formula-render-v2').replace('len(r[\'panels\']) == 7','len(r[\'panels\']) == 9')
s=s.replace("len(r['images']) == 12","len(r['images']) == 14").replace('Actual12current','Actual14current')
s=s.replace('source_route_rendered_formulas=14','source_route_rendered_formulas=15').replace('new_proof_note_formulas=6','new_proof_note_formulas=8')
write(RUN/'capture-reader-v2.py',s)
write(RUN/'site-tool-preparation-v2.json',dict(template_paths=[(prior/p).as_posix() for p in ['verify-registry-v1.py','capture-reader-v1.py','capture-reader-v1.cjs']],
    retained_exact_old_registry_nodes=10913,expected_new_production_nodes=10,expected_new_proof_notes=8,
    expected_source_cards=12,expected_current_images=14,actual_site_not_yet_built=True,package_accepted=False,chapter_complete=False,goal_complete=False))
print('Current source-specific registry and actual pixel tools prepared; clean applicable site gate pending.')
