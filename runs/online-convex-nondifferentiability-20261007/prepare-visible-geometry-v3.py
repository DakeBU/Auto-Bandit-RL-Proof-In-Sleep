"""Before first rerender, make geometry checks apply after each disclosure is open."""
from common_v4 import *
p=RUN/'render-source-card-v2.cjs';t=p.read_text(encoding='utf-8')
start=t.index('  for(let i=0;i<3;i++){const g=');end=t.index('\n',start)
old=t[start:end];t=t[:start]+t[end+1:]
needle='   await card.screenshot';assert needle in t
check="   const g=await card.evaluate(el=>{const p=el.closest('details'),r=el.getBoundingClientRect(),q=p.getBoundingClientRect();return {width:r.width,height:r.height,parentWidth:q.width,right:r.right,parentRight:q.right,scrollWidth:el.scrollWidth,clientWidth:el.clientWidth};});if(g.height<=0||g.right>g.parentRight+1||g.width>g.parentWidth+1||g.scrollWidth>g.clientWidth+1)throw Error('Visible source-card geometry overflow: '+JSON.stringify(g));\n"
t=t.replace(needle,check+needle);write(RUN/'render-source-card-v3.cjs',t)
t=(RUN/'render-source-card-v2.py').read_text(encoding='utf-8').replace('render-source-card-v2.cjs','render-source-card-v3.cjs');write(RUN/'render-source-card-v3.py',t);compile(t,str(RUN/'render-source-card-v3.py'),'exec')
t=(RUN/'source-site-gates-v6.py').read_text(encoding='utf-8').replace("RUN/'render-source-card-v2.py'","RUN/'render-source-card-v3.py'");write(RUN/'source-site-gates-v7.py',t);compile(t,str(RUN/'source-site-gates-v7.py'),'exec')
write(RUN/'visible-geometry-pre-use-v3.json',dict(executed_renderer_v2_failure=False,unused_original=p.as_posix(),effective=(RUN/'render-source-card-v3.cjs').as_posix(),reason='Each actual geometry assertion must run after its disclosure opens; closed hidden cards can have zero rectangles',actual_visible_height_required=True,source_or_math_changed=False))
print('Visible-after-open geometry assertions prepared before first new renderer use.')
