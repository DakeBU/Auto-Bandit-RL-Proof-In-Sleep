from publication_guard_v1 import *
fixed()
assert load(RUN / 'full-harness-inspected-v1.json')['actual_check_passed']
d = load(CONTRACT / 'stabilized-v1.json')
old = load(ROOT / 'docs/contracts/online-ch2-bregman-v1/stabilized-v1.json')
legacy = [dict(declaration=old['definition']['declaration'])] + old['targets']
write(RUN / 'browser-production-nodes-v1.json', dict(targets=d['targets'], legacy_targets=legacy,
    current_production_count=3, explicitly_corrected_legacy_note_count=6, source_card_count=9,
    source_math_containers=12, expected_original_images=15, no_Test_catalogue=True,
    transport='Actual local file URI; no new HTTP service or live claim.'))
s = (ROOT / 'runs/online-ch2-bregman-20261009/capture-bregman-reader-v1.cjs').read_text(encoding='utf8')
s = s.replace(" const targets=JSON.parse(fs.readFileSync(targetsFile,'utf8')).targets.map(t=>({name:t.declaration}));",
    " const packet=JSON.parse(fs.readFileSync(targetsFile,'utf8'));\n const targets=packet.targets.map(t=>({name:t.declaration}));\n const legacy=packet.legacy_targets.map(t=>registry.nodes.find(n=>n.id==='declaration:'+t.declaration));\n if(legacy.length!==6||legacy.some(n=>!n))throw Error('Missing six legacy note nodes');")
s = s.replace("if(nodes.length!==6||nodes.some(n=>!n))throw Error('Missing six new public nodes');",
    "if(nodes.length!==3||nodes.some(n=>!n))throw Error('Missing three new public nodes');")
a = "  const specs=[['article.source-theorem-card',Number(sourceCards)-1,'bregman-source-card-v1.png',Number(sourceCards)],...nodes.map((n,i)=>['#'+n.url.split('#')[1]+'-teaching',0,`public-note-${i+1}-v1.png`,1])];"
b = "  const specs=[['article.source-theorem-card',Number(sourceCards)-1,'extended-source-card-v1.png',Number(sourceCards)],['article.source-theorem-card',Number(sourceCards)-2,'legacy-bregman-source-card-v1.png',Number(sourceCards)],...nodes.map((n,i)=>['#'+n.url.split('#')[1]+'-teaching',0,`public-note-${i+1}-v1.png`,1]),...legacy.map((n,i)=>['#'+n.url.split('#')[1]+'-teaching',0,`legacy-note-${i+1}-v1.png`,1])];"
assert s.count(a) == 1
s = s.replace(a, b)
s = s.replace('actual-bregman-proximal-foundation-captured', 'actual-extended-proximal-and-legacy-wording-captured')
write(RUN / 'capture-extended-reader-v1.cjs', s)
fixed()
print('Prepared exact fifteen-original desktop browser capture, including all six corrected legacy notes and legacy card.')
