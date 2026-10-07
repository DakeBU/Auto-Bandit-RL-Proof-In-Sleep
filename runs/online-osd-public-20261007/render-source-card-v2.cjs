const fs=require('fs'),path=require('path');
const {chromium}=require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async()=>{
 const url=process.argv[2],run=process.argv[3],profile=process.argv[4];
 const context=await chromium.launchPersistentContext(profile,{executablePath:'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe',headless:true,viewport:{width:1440,height:1800},args:['--disable-gpu','--disable-sync','--disable-background-networking','--no-first-run']});
 try{
  const page=await context.newPage();await page.goto(url,{waitUntil:'networkidle',timeout:45000});
  await page.waitForFunction(()=>document.querySelectorAll('.source-theorem-card mjx-container').length>=6,null,{timeout:45000});
  const cards=page.locator('article.source-theorem-card');if(await cards.count()!==6)throw Error('Expected exactly SIX source definition/theorem/example cards');
  const infos=[];
  for(let i=0;i<6;i++){
   const card=cards.nth(i),detail=card.locator("xpath=ancestor::details[contains(@class,'source-theorem-disclosure')][1]");
   let disclosure='none';if(await detail.count()){if(!await detail.evaluate(el=>el.open))await detail.locator('summary').click();if(!await detail.evaluate(el=>el.open))throw Error('Source disclosure not actually open');disclosure='actually-open';}
   const g=await card.evaluate(el=>{const p=el.closest('details'),r=el.getBoundingClientRect(),q=p.getBoundingClientRect();return {width:r.width,height:r.height,parentWidth:q.width,right:r.right,parentRight:q.right,scrollWidth:el.scrollWidth,clientWidth:el.clientWidth,viewportWidth:window.innerWidth,left:r.left};});if(g.height<=0||g.left<0||g.right>g.viewportWidth+1||g.right>g.parentRight+1||g.width>g.parentWidth+1||g.scrollWidth>g.clientWidth+1)throw Error('Visible source-card geometry overflow: '+JSON.stringify(g));
   await card.screenshot({path:path.join(run,'source-card-'+String(i+1).padStart(2,'0')+'-v2.png'),timeout:45000});
   const info=await card.evaluate(el=>({heading:el.querySelector('h3').textContent,mathContainers:el.querySelectorAll('mjx-container').length,mathErrors:el.querySelectorAll('mjx-merror').length,box:{width:el.getBoundingClientRect().width,height:el.getBoundingClientRect().height},renderedMath:Array.from(el.querySelectorAll('mjx-container')).map(x=>x.outerHTML)}));
   if(info.mathContainers!==1||info.mathErrors!==0)throw Error('Expected one actual MathJax source formula per card, with no rendering errors');
   infos.push({...info,disclosure});
  }
  fs.writeFileSync(path.join(run,'formula-render-v2-dom.html'),await page.content(),'utf8');
  fs.writeFileSync(path.join(run,'formula-render-v2-browser.json'),JSON.stringify({status:'actual-six-source-cards-visible-and-rendered',cards:infos,userAgent:await page.evaluate(()=>navigator.userAgent),url,profilePreserved:profile,generatedSiteUnmodified:true},null,2)+'\n','utf8');
 }finally{await context.close();}
})().catch(e=>{console.error(e);process.exitCode=1;});
