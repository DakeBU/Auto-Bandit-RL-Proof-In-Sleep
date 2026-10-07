const fs=require('fs'),path=require('path');
const {chromium}=require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async()=>{
 const url=process.argv[2],run=process.argv[3],profile=process.argv[4];
 const context=await chromium.launchPersistentContext(profile,{executablePath:'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe',headless:true,viewport:{width:1440,height:1800},args:['--disable-gpu','--disable-sync','--disable-background-networking','--no-first-run']});
 try{
  const page=await context.newPage();await page.goto(url,{waitUntil:'networkidle',timeout:45000});await page.waitForFunction(()=>document.querySelectorAll('#source-guide mjx-container').length===13,null,{timeout:45000});
  await page.screenshot({path:path.join(run,'reader-first-viewport-v1.png')});
  const specs=[['article.source-theorem-card','source-card-01-v1.png',1],['#algorithm','algorithm-v1.png',4],['#proof-bridge','proof-bridge-v1.png',4],['#worked-example','worked-example-v1.png',4]];const panels=[];
  for(const [selector,file,expected] of specs){
   const panel=page.locator(selector);if(await panel.count()!==1)throw Error('Expected exactly one '+selector);
   const detail=panel.locator("xpath=ancestor::details[contains(@class,'source-theorem-disclosure')][1]");
   if(await detail.count()&&!await detail.evaluate(el=>el.open)){await detail.locator('summary').click();if(!await detail.evaluate(el=>el.open))throw Error('Disclosure not actually open');}
   const height=await panel.evaluate(el=>Math.ceil(el.getBoundingClientRect().height));await page.setViewportSize({width:1440,height:Math.max(1800,height+350)});await page.evaluate(el=>window.scrollTo(0,window.scrollY+el.getBoundingClientRect().top-180),await panel.elementHandle());await page.waitForTimeout(100);
   const box=await panel.boundingBox();if(!box||box.y<140||box.y+box.height>Math.max(1800,height+350)-30)throw Error('Panel hidden by sticky header or bottom-clipped '+selector);
   const geometry=await panel.evaluate(el=>({width:el.getBoundingClientRect().width,height:el.getBoundingClientRect().height,left:el.getBoundingClientRect().left,right:el.getBoundingClientRect().right,scrollWidth:el.scrollWidth,clientWidth:el.clientWidth,viewportWidth:window.innerWidth}));if(geometry.left<0||geometry.right>geometry.viewportWidth+1||geometry.scrollWidth>geometry.clientWidth+1)throw Error('Horizontal geometry overflow '+selector);
   await panel.screenshot({path:path.join(run,file),timeout:45000});const info=await panel.evaluate(el=>({heading:el.querySelector('h3,h4').textContent,mathContainers:el.querySelectorAll('mjx-container').length,mathErrors:el.querySelectorAll('mjx-merror').length,renderedMath:Array.from(el.querySelectorAll('mjx-container')).map(x=>x.outerHTML)}));
   if(info.mathContainers!==expected||info.mathErrors!==0)throw Error('Wrong rendered formula count/errors '+selector);panels.push({...info,selector,file,geometry,actualViewport:await page.viewportSize(),safeBelowStickyNavigation:true});
  }
  fs.writeFileSync(path.join(run,'formula-render-v1-dom.html'),await page.content(),'utf8');fs.writeFileSync(path.join(run,'formula-render-v1-browser.json'),JSON.stringify({status:'actual-one-source-card-and-full-algorithm-bridge-example-rendered',panels,actualThirteenRouteFormulas:true,userAgent:await page.evaluate(()=>navigator.userAgent),url,profilePreserved:profile,generatedSiteFilesUnmodified:true},null,2)+'\n','utf8');
 }finally{await context.close();}
})().catch(e=>{console.error(e);process.exitCode=1;});
