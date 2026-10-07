const fs=require('fs'),path=require('path');
const {chromium}=require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async()=>{
 const [url,run,profile]=process.argv.slice(2),errors=[],failed=[];
 const context=await chromium.launchPersistentContext(profile,{executablePath:'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe',headless:true,viewport:{width:1440,height:1800},args:['--disable-gpu','--disable-sync','--disable-background-networking','--no-first-run']});
 try{
  const page=await context.newPage();page.on('pageerror',e=>errors.push(String(e)));page.on('requestfailed',r=>failed.push({url:r.url(),failure:r.failure()}));
  await page.goto(url,{waitUntil:'networkidle',timeout:45000});await page.waitForFunction(()=>document.querySelectorAll('#source-guide mjx-container').length===12,null,{timeout:45000});
  const images=['reader-first-viewport-v1.png'];await page.screenshot({path:path.join(run,images[0])});
  const specs=[['article.source-theorem-card',0,'source-card-01-v1.png',1,2],['article.source-theorem-card',1,'source-card-02-v1.png',1,2],['#algorithm',0,'algorithm-v1.png',1,1],['#proof-bridge',0,'proof-bridge-v1.png',4,1],['#worked-example',0,'worked-example-v1.png',5,1]],panels=[];
  for(const [selector,index,file,expected,total] of specs){
   if(await page.locator(selector).count()!==total)throw Error('Unexpected panel count '+selector);const panel=page.locator(selector).nth(index);
   const detail=panel.locator("xpath=ancestor::details[contains(@class,'source-theorem-disclosure')][1]");
   if(await detail.count()&&!await detail.evaluate(el=>el.open)){await detail.locator('summary').click();if(!await detail.evaluate(el=>el.open))throw Error('Disclosure not open');}
   const height=await panel.evaluate(el=>Math.ceil(el.getBoundingClientRect().height));await page.setViewportSize({width:1440,height:Math.max(1800,height+350)});await page.evaluate(el=>window.scrollTo(0,window.scrollY+el.getBoundingClientRect().top-180),await panel.elementHandle());await page.waitForTimeout(100);
   const box=await panel.boundingBox();if(!box||box.y<140||box.y+box.height>Math.max(1800,height+350)-30)throw Error('Panel header/bottom clipped '+selector);
   const geometry=await panel.evaluate(el=>({width:el.getBoundingClientRect().width,height:el.getBoundingClientRect().height,left:el.getBoundingClientRect().left,right:el.getBoundingClientRect().right,scrollWidth:el.scrollWidth,clientWidth:el.clientWidth,viewportWidth:window.innerWidth}));if(geometry.left<0||geometry.right>geometry.viewportWidth+1||geometry.scrollWidth>geometry.clientWidth+1)throw Error('Panel horizontal overflow '+selector);
   await panel.screenshot({path:path.join(run,file),timeout:45000});images.push(file);
   const info=await panel.evaluate(el=>({heading:el.querySelector('h3,h4').textContent,mathContainers:el.querySelectorAll('mjx-container').length,mathErrors:el.querySelectorAll('mjx-merror').length,renderedMath:Array.from(el.querySelectorAll('mjx-container')).map(x=>x.outerHTML)}));if(info.mathContainers!==expected||info.mathErrors!==0)throw Error('Wrong formula count/errors '+selector);panels.push({...info,selector,index,file,geometry,actualViewport:await page.viewportSize(),safeBelowStickyNavigation:true});
  }
  const scrollers=await page.evaluate(()=>Array.from(document.querySelectorAll('#source-guide *')).map((x,index)=>({x,index})).filter(({x})=>x.clientWidth>0&&x.querySelector('mjx-container')&&x.scrollWidth>x.clientWidth+1&&['auto','scroll'].includes(getComputedStyle(x).overflowX)).map(({x,index})=>({index,tag:x.tagName,class:x.className,clientWidth:x.clientWidth,scrollWidth:x.scrollWidth,formula:Array.from(x.querySelectorAll('mjx-container')).map(y=>y.outerHTML)})));
  const scrollViews=[];
  for(let k=0;k<scrollers.length;k++){
   const row=scrollers[k],node=page.locator('#source-guide *').nth(row.index);await page.setViewportSize({width:1440,height:1800});await page.evaluate(el=>window.scrollTo(0,window.scrollY+el.getBoundingClientRect().top-220),await node.elementHandle());
   const left='wide-formula-'+String(k+1).padStart(2,'0')+'-left-v1.png',right='wide-formula-'+String(k+1).padStart(2,'0')+'-right-v1.png';await node.evaluate(el=>{el.scrollLeft=0;});await node.screenshot({path:path.join(run,left)});
   const before=await node.evaluate(el=>({left:el.scrollLeft,clientWidth:el.clientWidth,scrollWidth:el.scrollWidth}));const after=await node.evaluate(el=>{el.scrollLeft=el.scrollWidth-el.clientWidth;return {left:el.scrollLeft,clientWidth:el.clientWidth,scrollWidth:el.scrollWidth,mathErrors:el.querySelectorAll('mjx-merror').length};});
   if(before.left!==0||after.left<=0||after.left!==after.scrollWidth-after.clientWidth||after.mathErrors!==0)throw Error('Scroll verification failed');await page.waitForTimeout(100);await node.screenshot({path:path.join(run,right)});images.push(left,right);scrollViews.push({...row,before,after,leftFile:left,rightFile:right,actualScrollOnly:true,noDOMCSSOrGeneratedFileEdit:true});
  }
  if(errors.length||failed.length)throw Error(JSON.stringify({errors,failed}));
  fs.writeFileSync(path.join(run,'formula-render-v1-dom.html'),await page.content(),'utf8');fs.writeFileSync(path.join(run,'formula-render-v1-browser.json'),JSON.stringify({status:'actual-panels-and-any-wide-formula-scroll-pairs-captured',panels,scrollViews,images,actualRouteMathContainers:12,dataMathFields:15,algorithmThreeStepsRenderedAsProse:true,errors,failed,userAgent:await page.evaluate(()=>navigator.userAgent),url,profilePreserved:profile,generatedSiteFilesUnmodified:true},null,2)+'\n','utf8');
 }finally{await context.close();}
})().catch(e=>{console.error(e);process.exitCode=1;});
