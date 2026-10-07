"""Root visual rejection of clipped third card; content-label-only repair."""
from common_v4 import *
fixed(True,True);passed('source-site-gates-v5-01')
b=load(RUN/'formula-render-v1-browser.json');assert b['cards'][2]['box']['width']>b['cards'][0]['box']['width']+250
write(RUN/'visual-rejection-v1.json',dict(actor='/root',actual_view_image=True,renderer_command_exit_zero=True,decision='repair',finding='Third actual card has width1357px versus first two1057px and screenshot visibly clips its right side within the source disclosure',images=[dict(path=(RUN/('source-card-%02d-v1.png'%i)).as_posix(),sha256=sha(RUN/('source-card-%02d-v1.png'%i))) for i in [1,2,3]],not_accepted_visual_evidence=True,no_compilation_failure_inferred=True))
p=Path('website/content/readings.json');write(RUN/'snapshots/readings-before-visual-badge-repair-v2.txt',p.read_bytes())
d=load(p);x=next(a for a in d['readings'] if a['slug']==ROUTE);old=load(p);label=x['source_theorems'][2]['local_status']['label'];assert label=='New global-convex / full closed-segment terminal compiled'
x['source_theorems'][2]['local_status']['label']='Full segment terminal compiled'
oldx=next(a for a in old['readings'] if a['slug']==ROUTE);oldx['source_theorems'][2]['local_status']['label']=x['source_theorems'][2]['local_status']['label'];assert d==old
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
write(RUN/'visual-badge-reader-repair-v2.json',dict(previous_visual_decision='visual-rejection-v1.json',repair='Shorten only third-card status badge; full global-convex/every-closed-segment ambient conclusion stays in adjacent formula/explanation',original_label=label,new_label=x['source_theorems'][2]['local_status']['label'],all_other_reader_fields_unchanged=True,source_math_headers_bodies_unchanged=True,CSS_generator_schema_unchanged=True,old_images_preserved=True))
mapping=[('browser-v1.py','browser-v2.py'),('render-source-card-v1.cjs','render-source-card-v2.cjs'),('render-source-card-v1.py','render-source-card-v2.py')]
for src,dst in mapping:
 t=(RUN/src).read_text(encoding='utf-8')
 for a,z in [('browser-v1','browser-v2'),('reader-v1','reader-v2'),('formula-render-v1','formula-render-v2'),('render-source-card-v1','render-source-card-v2'),('playwright-v1','playwright-v2'),("+'-v1.png'","+'-v2.png'"),("-%02d-v1.png","-%02d-v2.png"),("registry-v1.json","registry-v2.json")]:t=t.replace(a,z)
 if dst.endswith('.cjs'):
  needle="const infos=[];";assert needle in t;t=t.replace(needle,"const infos=[];\n  for(let i=0;i<3;i++){const g=await cards.nth(i).evaluate(el=>{const p=el.closest('details'),r=el.getBoundingClientRect(),q=p.getBoundingClientRect();return {width:r.width,parentWidth:q.width,right:r.right,parentRight:q.right,scrollWidth:el.scrollWidth,clientWidth:el.clientWidth};});if(g.right>g.parentRight+1||g.width>g.parentWidth+1||g.scrollWidth>g.clientWidth+1)throw Error('Actual source-card geometry overflow: '+JSON.stringify(g));}")
 write(RUN/dst,t)
 if dst.endswith('.py'):compile(t,str(RUN/dst),'exec')
t=(RUN/'verify-registry-v2.py').read_text(encoding='utf-8').replace("RUN/'registry-v1.json'","RUN/'registry-v2.json'")
write(RUN/'verify-registry-v3.py',t)
t=(RUN/'bind-integrated-gates-v4.py').read_text(encoding='utf-8')
for a,z in [('contributor-exact-v4-01','contributor-exact-v5-01'),('scoped-diff-v3-01','scoped-diff-v4-01'),('site-build-v3-01','site-build-v4-01'),('site-check-v2-01','site-check-v3-01'),('registry-v2-01','registry-v3-01'),('browser-v1','browser-v2'),('formula-render-v1','formula-render-v2'),('source-card-%02d-v1.png','source-card-%02d-v2.png'),('registry-v1.json','registry-v2.json')]:t=t.replace(a,z)
t=t.replace("dest=RUN/'reader-first-viewport-v1.png'","dest=RUN/'reader-first-viewport-v2.png'")
t=t.replace("harness_index_only_repair=load(RUN/'harness-tracked-source-repair-v2.json')","harness_index_only_repair=load(RUN/'harness-tracked-source-repair-v2.json'),actual_visual_repair=load(RUN/'visual-badge-reader-repair-v2.json'),earlier_visual_rejection_preserved=load(RUN/'visual-rejection-v1.json')")
write(RUN/'bind-integrated-gates-v5.py',t);compile(t,str(RUN/'bind-integrated-gates-v5.py'),'exec')
t=(RUN/'prepare-delivery-v1.py').read_text(encoding='utf-8').replace('registry-v1.json','registry-v2.json').replace('formula-render-v1.json','formula-render-v2.json').replace('same frozen definition/header bytes, no source/math/test/schema weakening','same frozen definition/header bytes, no source/math/test/schema weakening')
write(RUN/'prepare-delivery-v2.py',t);compile(t,str(RUN/'prepare-delivery-v2.py'),'exec')
t=(RUN/'prepare-pr-payload-v2.py').read_text(encoding='utf-8').replace('registry-v1.json','registry-v2.json').replace('and all three source-card PNGs','and all three current source-card-v2 PNGs, with original clipped third-card-v1 preserved as an actual visual rejection')
write(RUN/'prepare-pr-payload-v3.py',t);compile(t,str(RUN/'prepare-pr-payload-v3.py'),'exec')
fixed(True,True);print('Label-only visual repair prepared; original actual clipped images preserved. Actual geometry/new pixels pending.')
