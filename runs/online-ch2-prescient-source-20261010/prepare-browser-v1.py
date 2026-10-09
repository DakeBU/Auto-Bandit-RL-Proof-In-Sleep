from publication_guard_v1 import *
fixed()
parent=ROOT/'runs/online-ch2-prescient-cumulative-20261009/capture-prescient-cumulative-reader-v2.cjs'
s=parent.read_text(encoding='utf8').replace('nodes.length!==5','nodes.length!==6').replace('Missing five new public nodes','Missing six new public nodes')
s=s.replace('t.declaration','t.name').replace('v2','v1').replace('prescient-cumulative-source-card','prescient-source-transport-card').replace('actual-prescient-cumulative-captured','actual-prescient-source-transport-captured')
old="   const prose=await panel.innerText();if(!prose.includes('The shared iterate_divergence_sum interface allows every natural horizon T')||!prose.includes('Only iterate_variable_sharp and iterate_variable_regret require T>0'))throw Error('Repaired interface-scope prose missing');"
assert s.count(old)==1
s=s.replace(old,"   const prose=await panel.innerText();if(!prose.includes('All eight Chapter 2 forward containers remain required/open')||!prose.includes('not universal attainment'))throw Error('Bounded source-run boundary missing');")
old="   if(file==='public-note-3-v1.png'){const mml=await panel.locator('mjx-assistive-mml').textContent();if(!mml.includes('T')||!mml.includes('η')||!mml.includes('<'))throw Error('Variable horizon/step assumptions missing from actual MathML');}"
assert s.count(old)==1
s=s.replace(old,"   if(file==='public-note-6-v1.png'){const mml=await panel.locator('mjx-assistive-mml').textContent();if(!mml.includes('max')||!mml.includes('T')||!mml.includes('η'))throw Error('Variable previous-state maximum/step formula missing from actual MathML');}")
write(RUN/'capture-prescient-source-reader-v1.cjs',s)
write(RUN/'browser-production-nodes-v1.json',dict(targets=load(CONTRACT/'stabilized-v1.json')['six_targets'],current_production_count=6,source_card_count=12,source_math_containers=15,expected_original_images=14,no_Test_catalogue=True,transport='Actual local file URI; no HTTP service or live claim.'))
print('Browser helper prepared, not executed.')
