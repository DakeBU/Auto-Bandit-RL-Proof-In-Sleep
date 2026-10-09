const fs=require('fs'),path=require('path');
const {chromium}=require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async()=>{
 const [url,run,profile]=process.argv.slice(2),errors=[],failed=[];
 const context=await chromium.launchPersistentContext(profile,{executablePath:'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe',headless:true,viewport:{width:1440,height:1800},args:['--disable-gpu','--disable-sync','--disable-background-networking','--no-first-run']});
 try{
  const page=await context.newPage();page.on('pageerror',e=>errors.push(String(e)));page.on('requestfailed',r=>failed.push({url:r.url(),failure:r.failure()}));
  await page.goto(url,{waitUntil:'networkidle',timeout:45000});
  await page.waitForTimeout(1500);
  await page.evaluate(()=>document.querySelectorAll('#source-guide details').forEach(e=>e.open=true));
  const diagnostics=await page.evaluate(()=>({
   sourceGuideExists:!!document.querySelector('#source-guide'),sourceCards:document.querySelectorAll('article.source-theorem-card').length,
   sourceMathContainers:document.querySelectorAll('#source-guide mjx-container').length,
   sourceMathTex:document.querySelectorAll('#source-guide .math-tex').length,
   sourceMathDetails:Array.from(document.querySelectorAll('#source-guide .math-tex')).map(e=>({text:e.textContent,containers:e.querySelectorAll('mjx-container').length,parentClientWidth:e.parentElement.clientWidth,parentScrollWidth:e.parentElement.scrollWidth,parentOverflowX:getComputedStyle(e.parentElement).overflowX,renderedWidth:e.querySelector('mjx-container')?.getBoundingClientRect().width||0})),
   mathJaxVersion:window.MathJax?.version||null,mathJaxStartup:!!window.MathJax?.startup,
   mathErrors:document.querySelectorAll('mjx-merror,[data-mjx-error]').length,
   scripts:Array.from(document.scripts).map(e=>e.src).filter(Boolean)}));
  fs.writeFileSync(path.join(run,'nonsmooth-browser-diagnostic-v2.json'),JSON.stringify({diagnostics,errors,failed,url},null,2)+'\n',{encoding:'utf8',flag:'wx'});
  fs.writeFileSync(path.join(run,'nonsmooth-browser-diagnostic-v2.html'),await page.content(),{encoding:'utf8',flag:'wx'});
  console.log(JSON.stringify({diagnostics,errors,failed}));
 }finally{await context.close();}
})().catch(e=>{console.error(e);process.exitCode=1;});
