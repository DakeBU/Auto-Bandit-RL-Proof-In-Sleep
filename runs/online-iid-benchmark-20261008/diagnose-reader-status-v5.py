from common_integrated_v2 import *
fixed_integrated()
assert load(RUN/'current-reader-capture-v4-exit.json')['exit_code']==1
source=(RUN/'diagnose-reader-overflow-v3.py').read_text(encoding='utf8')
source=source.replace('current-reader-capture-v2','current-reader-capture-v4').replace('capture-reader-v2','capture-reader-v4')
source=source.replace('-v3','-v5').replace('formula-render-v2','formula-render-v4').replace('-viewport-v2','-viewport-v4')
# Add exact computed styles for the status pill and source heading, alongside original overflow geometry.
source=source.replace("geometry:{width:el.getBoundingClientRect().width,scrollWidth:el.scrollWidth,clientWidth:el.clientWidth},overflowChildren:",
    "geometry:{width:el.getBoundingClientRect().width,left:el.getBoundingClientRect().left,right:el.getBoundingClientRect().right,scrollWidth:el.scrollWidth,clientWidth:el.clientWidth},statusLayout:Array.from(el.querySelectorAll('.source-route-status,.source-route-status > *, .source-theorem-heading > *')).map(x=>({cls:x.className,width:x.getBoundingClientRect().width,minWidth:getComputedStyle(x).minWidth,whiteSpace:getComputedStyle(x).whiteSpace,text:x.textContent})),overflowChildren:")
write(RUN/'diagnose-reader-status-helper-v5.py',source)
exec(compile(source,'original-overflow-diagnostic-resume-v5','exec'))
