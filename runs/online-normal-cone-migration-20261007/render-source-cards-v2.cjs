const fs = require('fs');
const path = require('path');
const {chromium}=require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async()=>{
 const url=process.argv[2], run=process.argv[3], profile=process.argv[4];
 const context=await chromium.launchPersistentContext(profile,{executablePath:'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe',headless:true,viewport:{width:1440,height:1800},args:['--disable-gpu','--disable-sync','--disable-background-networking','--no-first-run']});
 try {
  const page=await context.newPage();await page.goto(url,{waitUntil:'networkidle',timeout:45000});
  await page.waitForFunction(()=>document.querySelectorAll('.source-theorem-card mjx-container').length>=3,{timeout:45000});
  const disclosures=page.locator('details.source-theorem-disclosure');if(await disclosures.count()!==3)throw Error('Expected THREE source cards');
  const cards=[];
  for(let i=0;i<3;i++){
   const detail=disclosures.nth(i);await detail.locator('summary').click();
   const card=detail.locator('article.source-theorem-card');
   if(!await detail.evaluate(el=>el.open))throw Error('Disclosure not actually open');
   await card.screenshot({path:path.join(run,`source-card-${String(i+1).padStart(2,'0')}-v2.png`),timeout:45000});
   const info=await card.evaluate(el=>({heading:el.querySelector('h3').textContent,mathContainers:el.querySelectorAll('mjx-container').length,box:{width:el.getBoundingClientRect().width,height:el.getBoundingClientRect().height},renderedMath:Array.from(el.querySelectorAll('mjx-container')).map(x=>x.outerHTML)}));
   if(info.mathContainers!==1)throw Error('Expected one actual MathJax statement per source card');cards.push(info);
  }
  fs.writeFileSync(path.join(run,'formula-render-v2-dom.html'),await page.content(),'utf8');
  fs.writeFileSync(path.join(run,'formula-render-v2-browser.json'),JSON.stringify({status:'actual-three-disclosures-open-and-rendered',cards,userAgent:await page.evaluate(()=>navigator.userAgent),url,profilePreserved:profile,generatedSiteUnmodified:true},null,2)+'\n','utf8');
 }finally{await context.close();}
})().catch(e=>{console.error(e);process.exitCode=1;});
