from common_integrated_v2 import *

fixed_integrated()
prior=Path('runs/online-iid-benchmark-20261008')
s=(prior/'capture-reader-v9.cjs').read_text(encoding='utf8')
start=s.index(' const names=');end=s.index(' const nodes=',start)
names=['privateSeedPastInformation','private_seed_past_independent',
    'predictable_private_seed_expectedFixed_excess','randomized_history_policy_expectedFixed_excess']
proofs=[r['name'].rsplit('.',1)[1] for r in load(CONTRACT/'targets-v2.json')['rows']]
s=s[:start]+' const names='+json.dumps(names)+'; const proofNames='+json.dumps(proofs)+';\n'+s[end:]
for before,after in [('length===15','length===16'),
        ("11,'iid-benchmark-source-card-v9.png',1,12","12,'private-seed-source-card-v2.png',1,13"),
        ('reader-first-viewport-v9','reader-first-viewport-v2'),('public-note-${i+1}-v9','public-note-${i+1}-v2'),
        ('module-new-declaration-${i+1}-v9','module-new-declaration-${i+1}-v2'),
        ('formula-render-v9','formula-render-v2'),('actualSourceGuideMathContainers:15','actualSourceGuideMathContainers:16'),
        ('newPublicNoteMathContainers:8','newPublicNoteMathContainers:7'),
        ('actual-current-expected-fixed-causal-IID-panels-and-catalog-captured','actual-current-private-seed-subordinate-information-IID-panels-and-catalog-captured')]:
    assert before in s,before
    s=s.replace(before,after)
write(RUN/'capture-reader-v2.cjs',s)
s=(prior/'capture-reader-v9.py').read_text(encoding='utf8')
for before,after in [('online-iid-benchmark','online-randomized-iid'),('-site-v9','-site-v2'),
        ('registry-v9','registry-v2'),('capture-reader-v9.cjs','capture-reader-v2.cjs'),
        ('formula-render-v9','formula-render-v2'),("len(r['panels']) == 9","len(r['panels']) == 8"),
        ("len(r['images']) == 14","len(r['images']) == 13"),('Actual14current','Actual13current'),
        ('source_route_rendered_formulas=15','source_route_rendered_formulas=16'),
        ('new_proof_note_formulas=8','new_proof_note_formulas=7')]:
    assert before in s,before
    s=s.replace(before,after)
write(RUN/'capture-reader-v2.py',s)
write(RUN/'site-capture-tool-preparation-v2.json',dict(
    template_paths=[(prior/p).as_posix() for p in ['capture-reader-v9.py','capture-reader-v9.cjs']],
    exact_template_sha256={p:sha(prior/p) for p in ['capture-reader-v9.py','capture-reader-v9.cjs']},
    expected_old_shared_nodes=10923,expected_new_public_nodes=8,expected_source_cards=13,
    expected_new_proof_notes=7,expected_current_images=13,
    actual_new_site_not_built=True,package_accepted=False,chapter_complete=False,goal_complete=False))
print('Own private-seed source/card/catalogue capture tools prepared; no site or pixel gate passed yet.')
