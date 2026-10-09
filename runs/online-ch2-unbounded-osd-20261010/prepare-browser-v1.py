from publication_guard_v2 import *
fixed()
parent=ROOT/'runs/online-ch2-prescient-source-20261010/capture-prescient-source-reader-v1.cjs'
s=parent.read_text(encoding='utf8')
s=s.replace('nodes.length!==6','nodes.length!==15').replace('Missing six new public nodes','Missing fifteen new public nodes')
s=s.replace('prescient-source-transport-card','unbounded-osd-source-card').replace('actual-prescient-source-transport-captured','actual-unbounded-osd-source-captured')
old="!prose.includes('All eight Chapter 2 forward containers remain required/open')||!prose.includes('not universal attainment')"
new="!prose.includes('All eight Chapter2 forward containers remain required/open')||!prose.includes('not a lower bound against all learners')"
assert s.count(old)==1
s=s.replace(old,new).replace('Bounded source-run boundary missing','Bounded unbounded-OSD dependency boundary missing')
a=s.index("   if(file==='public-note-6-v1.png')");b=s.index('\n   panels.push',a)
s=s[:a]+"   if(file==='public-note-15-v1.png'){const mml=await panel.locator('mjx-assistive-mml').textContent();if(!mml.includes('T')||!mml.includes('α')||!mml.includes('∃'))throw Error('Source existential/exponent/horizon formula missing from actual MathML');}"+s[b:]
write(RUN/'capture-unbounded-osd-reader-v1.cjs',s)
names=[r['full_name'] for r in load(RUN/'reader-proposal-v1.json')['notes']]
write(RUN/'browser-production-nodes-v1.json',dict(targets=[dict(name=n) for n in names],current_production_count=15,source_card_count=13,source_math_containers=16,expected_original_images=32,no_Test_catalogue=True,transport='Actual local file URI; no HTTP service or live claim.'))
print('Prospective actual localfile browser helper ready; not executed.',flush=True)
