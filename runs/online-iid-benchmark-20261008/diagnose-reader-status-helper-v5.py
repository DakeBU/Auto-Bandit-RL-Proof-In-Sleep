from common_integrated_v2 import *
fixed_integrated()
assert load(RUN/'current-reader-capture-v4-exit.json')['exit_code']==1
old=(RUN/'capture-reader-v4.cjs').read_text(encoding='utf8')
needle="throw Error('Horizontal overflow '+file)"
assert old.count(needle)==1
diagnostic="{const evidence=await panel.evaluate(el=>({geometry:{width:el.getBoundingClientRect().width,left:el.getBoundingClientRect().left,right:el.getBoundingClientRect().right,scrollWidth:el.scrollWidth,clientWidth:el.clientWidth},statusLayout:Array.from(el.querySelectorAll('.source-route-status,.source-route-status > *, .source-theorem-heading > *')).map(x=>({cls:x.className,width:x.getBoundingClientRect().width,minWidth:getComputedStyle(x).minWidth,whiteSpace:getComputedStyle(x).whiteSpace,text:x.textContent})),overflowChildren:Array.from(el.querySelectorAll('*')).filter(x=>x.clientWidth>0&&x.scrollWidth>x.clientWidth+1).map(x=>({tag:x.tagName,cls:x.className,clientWidth:x.clientWidth,scrollWidth:x.scrollWidth,text:x.textContent.slice(0,350)}))}));fs.writeFileSync(path.join(run,'overflow-diagnostic-v5.json'),JSON.stringify(evidence,null,2)+'\\n');fs.writeFileSync(path.join(run,'overflow-diagnostic-v5-dom.html'),await page.content(),'utf8');await panel.screenshot({path:path.join(run,'overflow-diagnostic-v5.png')});throw Error('Actual overflow diagnostic retained '+file)}"
new=old.replace(needle,diagnostic).replace('reader-first-viewport-v4','reader-first-viewport-diagnostic-v5')
write(RUN/'capture-overflow-diagnostic-v5.cjs',new)
oldpy=(RUN/'capture-reader-v4.py').read_text(encoding='utf8')
newpy=oldpy[:oldpy.index('assert [sha(page)')]
newpy=newpy.replace('capture-reader-v4.cjs','capture-overflow-diagnostic-v5.cjs').replace('formula-render-v4-server','overflow-diagnostic-v5-server').replace('formula-render-v4-node','overflow-diagnostic-v5-node')
write(RUN/'capture-overflow-diagnostic-v5.py',newpy)
command=[sys.executable,'-B','-X','utf8',str(RUN/'capture-overflow-diagnostic-v5.py')]
with (RUN/'overflow-diagnostic-helper-v5.log').open('wb') as f: child=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT)
write(RUN/'overflow-diagnostic-helper-v5-exit.json',dict(command=command,actual_exit_code=child.returncode,
    log_sha256=sha(RUN/'overflow-diagnostic-helper-v5.log'),purpose='Capture actual failure geometry/DOM/pixels; expected rejection, not a passing visual gate.',
    public_unchanged_sha256=sha(PUBLIC),reader_not_modified=True,package_accepted=False,chapter_complete=False,goal_complete=False))
assert child.returncode==1 and (RUN/'overflow-diagnostic-v5.json').exists()
print('Actual original overflow geometry/DOM/PNG captured; failure retained, not gate acceptance.')
