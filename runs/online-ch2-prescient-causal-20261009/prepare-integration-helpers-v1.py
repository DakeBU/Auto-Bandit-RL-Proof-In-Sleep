from publication_guard_v1 import *
fixed()
prior = ROOT / 'runs/online-ch2-extended-proximal-20261009'
s = (prior / 'prepare-stage-v1.py').read_text(encoding='utf8')
s = s.replace('exact-publication-plan-v3.json', 'exact-publication-plan-v2.json')
s = s.replace('legacy_eight_wording_fields_explicit=True', 'all_old_fields_preserved=True')
write(RUN / 'prepare-stage-v1.py', s)
s = (prior / 'commit-and-build-site-v1.py').read_text(encoding='utf8')
s = s.replace('Prove extended-loss proximal bridges on the feasible domain', 'Prove current-loss partial Bregman recursion and transition bounds')
assert 'Prove extended-loss' not in s
write(RUN / 'commit-and-build-site-v1.py', s)
s = (prior / 'verify-registry-v1.py').read_text(encoding='utf8')
s = s.replace('11002', 'OLD_COUNT').replace('11005', 'NEW_COUNT')
s = s.replace('OLD_COUNT', '11005').replace('NEW_COUNT', '11015')
s = s.replace('len(expected) == 3', 'len(expected) == 10')
s = s.replace('OnlineBregmanExtendedCanary.', 'OnlinePrescientBregmanCanary.')
s = s.replace("len(reading['source_theorems']) == 9", "len(reading['source_theorems']) == 10")
s = s.replace('new_production_nodes=3, new_production_theorems=3, new_production_definitions=0',
              'new_production_nodes=10, new_production_theorems=8, new_production_definitions=2')
s = s.replace('source_cards=9', 'source_cards=10')
s = s.replace('exactly3 new canonical shared production theorems.', 'exactly10 new shared production nodes(8proofs/2defs).')
write(RUN / 'verify-registry-v1.py', s)
d = load(CONTRACT / 'stabilized-v1.json')
targets = d['targets'] + [dict(declaration=x['declaration']) for x in d['definitions']]
write(RUN / 'browser-production-nodes-v1.json', dict(targets=targets,
    current_production_count=10, source_card_count=10, source_math_containers=13,
    expected_original_images=22, no_Test_catalogue=True,
    transport='Actual local file URI; no new HTTP service or live claim.'))
s = (ROOT / 'runs/online-ch2-bregman-20261009/capture-bregman-reader-v1.cjs').read_text(encoding='utf8')
s = s.replace("if(nodes.length!==6||nodes.some(n=>!n))throw Error('Missing six new public nodes');",
    "if(nodes.length!==10||nodes.some(n=>!n))throw Error('Missing ten new public nodes');")
s = s.replace('bregman-source-card-v1.png', 'prescient-source-card-v1.png')
s = s.replace('actual-bregman-proximal-foundation-captured', 'actual-prescient-partial-recursion-captured')
write(RUN / 'capture-prescient-reader-v1.cjs', s)
s = (prior / 'run-file-browser-capture-v1.py').read_text(encoding='utf8')
s = s.replace('BanditRL.OnlineBregman.proximal_one_step_extended', 'BanditRL.OnlinePrescientBregman.iterate_one_step')
s = s.replace('online-ch2-extended-proximal-browser-v1', 'online-ch2-prescient-causal-browser-v1')
s = s.replace('capture-extended-reader-v1.cjs', 'capture-prescient-reader-v1.cjs')
s = s.replace("'9', '12'", "'10', '13'")
s = s.replace("len(b['images']) == 15 and len(b['panels']) == 11 and len(b['modulePanels']) == 3",
    "len(b['images']) == 22 and len(b['panels']) == 11 and len(b['modulePanels']) == 10")
s = s.replace("b['actualSourceGuideMathContainers'] == 12", "b['actualSourceGuideMathContainers'] == 13")
s = s.replace('fifteen originals', 'twenty-two originals')
write(RUN / 'run-file-browser-capture-v1.py', s)
fixed()
print('Prepared exact OWN staging, clean source/site, complete registry and22-original file-browser helpers.')
