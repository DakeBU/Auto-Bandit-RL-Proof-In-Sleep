const fs=require('fs'),path=require('path');
const {chromium}=require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async()=>{
 const [url,run,profile]=process.argv.slice(2);
 const context=await chromium.launchPersistentContext(profile,{executablePath:'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe',headless:true,viewport:{width:1440,height:2400},args:['--disable-gpu','--disable-sync','--disable-background-networking','--no-first-run']});
 try{
  const page=await context.newPage();await page.goto(url,{waitUntil:'networkidle',timeout:45000});
  const panel=page.locator('article.source-theorem-card').last();
  const ds=panel.locator('xpath=ancestor::details');
  for(let i=0;i<await ds.count();i++){const d=ds.nth(i);if(!await d.evaluate(el=>el.open))await d.locator(':scope > summary').click();}
  await panel.scrollIntoViewIfNeeded();
  const geometry=await panel.evaluate(el=>({width:el.clientWidth,scrollWidth:el.scrollWidth,box:el.getBoundingClientRect().toJSON(),overflow:Array.from(el.querySelectorAll('*')).filter(x=>x.clientWidth>0&&x.scrollWidth>x.clientWidth+1).map(x=>({tag:x.tagName,cls:x.className,clientWidth:x.clientWidth,scrollWidth:x.scrollWidth,text:x.textContent.slice(0,100),overflowX:getComputedStyle(x).overflowX,whiteSpace:getComputedStyle(x).whiteSpace}))}));
  await panel.screenshot({path:path.join(run,'overflow-source-card-diagnostic-v3.png')});
  fs.writeFileSync(path.join(run,'overflow-source-card-diagnostic-v3-dom.html'),await page.content());
  fs.writeFileSync(path.join(run,'overflow-source-card-diagnostic-v3.json'),JSON.stringify({diagnosticOnly:true,renderingPassClaim:false,geometry},null,2)+'\n');
  console.log(JSON.stringify(geometry));
 }finally{await context.close();}
})().catch(e=>{console.error(e);process.exitCode=1;});
