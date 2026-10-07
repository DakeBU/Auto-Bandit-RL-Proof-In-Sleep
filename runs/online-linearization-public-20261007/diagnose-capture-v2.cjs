const fs=require('fs'),path=require('path');
const {chromium}=require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async()=>{
 const url=process.argv[2],run=process.argv[3],profile=process.argv[4];const errors=[],failed=[];
 const context=await chromium.launchPersistentContext(profile,{executablePath:'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe',headless:true,viewport:{width:1440,height:1800},args:['--disable-gpu','--disable-sync','--disable-background-networking','--no-first-run']});
 try{
  const page=await context.newPage();page.on('pageerror',e=>errors.push(String(e)));page.on('requestfailed',r=>failed.push({url:r.url(),reason:r.failure()}));
  await page.goto(url,{waitUntil:'networkidle',timeout:45000});await page.waitForTimeout(8000);
  const diagnostics=await page.evaluate(()=>({ready:document.readyState,MathJax:!!window.MathJax,globalMath:document.querySelectorAll('mjx-container').length,sourceMath:document.querySelectorAll('#source-guide mjx-container').length,sourceInputs:Array.from(document.querySelectorAll('#source-guide .math-tex')).map(x=>x.textContent),panelCounts:['article.source-theorem-card','#algorithm','#proof-bridge','#worked-example'].map(selector=>({selector,math:document.querySelector(selector)?.querySelectorAll('mjx-container').length,inputs:document.querySelector(selector)?.querySelectorAll('.math-tex').length}))}));
  fs.writeFileSync(path.join(run,'capture-diagnostics-v2.json'),JSON.stringify({...diagnostics,errors,failed},null,2)+'\n');fs.writeFileSync(path.join(run,'capture-diagnostics-v2-dom.html'),await page.content());
 }finally{await context.close();}
})().catch(e=>{console.error(e);process.exitCode=1;});
