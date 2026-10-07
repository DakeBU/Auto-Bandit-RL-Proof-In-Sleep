const fs=require('fs'),path=require('path');
const {chromium}=require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async()=>{
 const url=process.argv[2],run=process.argv[3],profile=process.argv[4];
 const context=await chromium.launchPersistentContext(profile,{executablePath:'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe',headless:true,viewport:{width:1440,height:1800},args:['--disable-gpu','--disable-sync','--disable-background-networking','--no-first-run']});
 try{
  const page=await context.newPage();await page.goto(url,{waitUntil:'networkidle',timeout:45000});await page.waitForFunction(()=>document.querySelectorAll('#source-guide mjx-container').length===10,null,{timeout:45000});
  const step=page.locator('#proof-bridge .proof-bridge-step').nth(3);const nodes=await step.evaluate(el=>Array.from(el.querySelectorAll('*')).filter(x=>x.scrollWidth>x.clientWidth+1).map(x=>({tag:x.tagName,class:x.className,scrollWidth:x.scrollWidth,clientWidth:x.clientWidth,overflowX:getComputedStyle(x).overflowX})));fs.writeFileSync(path.join(run,'formula-scroll-diagnostics-v4.json'),JSON.stringify(nodes,null,2));
  const candidates=await step.evaluate(el=>Array.from(el.querySelectorAll('*')).filter(x=>x.scrollWidth>x.clientWidth+1&&['auto','scroll'].includes(getComputedStyle(x).overflowX)).map(x=>({tag:x.tagName,class:x.className})));if(candidates.length!==1)throw Error('Expected one actual horizontal scroller: '+JSON.stringify(candidates));
  await page.evaluate(el=>window.scrollTo(0,window.scrollY+el.getBoundingClientRect().top-180),await step.elementHandle());const before=await step.evaluate(el=>{const x=Array.from(el.querySelectorAll('*')).find(x=>x.scrollWidth>x.clientWidth+1&&['auto','scroll'].includes(getComputedStyle(x).overflowX));return {left:x.scrollLeft,width:x.clientWidth,scrollWidth:x.scrollWidth};});
  await step.screenshot({path:path.join(run,'proof-bridge-step4-left-v4.png')});
  const after=await step.evaluate(el=>{const x=Array.from(el.querySelectorAll('*')).find(x=>x.scrollWidth>x.clientWidth+1&&['auto','scroll'].includes(getComputedStyle(x).overflowX));x.scrollLeft=x.scrollWidth-x.clientWidth;return {left:x.scrollLeft,width:x.clientWidth,scrollWidth:x.scrollWidth,MathJaxErrors:el.querySelectorAll('mjx-merror').length};});if(after.left<=0||after.left!==after.scrollWidth-after.width||after.MathJaxErrors!==0)throw Error('Actual right scroll/error verification failed');await page.waitForTimeout(100);await step.screenshot({path:path.join(run,'proof-bridge-step4-right-v4.png')});
  fs.writeFileSync(path.join(run,'formula-scroll-v4-browser.json'),JSON.stringify({before,after,actualScrollOnly:true,noDOMCSSOrGeneratedFileEdit:true,formula:await step.locator('mjx-container').evaluate(x=>x.outerHTML)},null,2)+'\n');
 }finally{await context.close();}
})().catch(e=>{console.error(e);process.exitCode=1;});
