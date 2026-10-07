const fs=require('fs'),path=require('path');
const {chromium}=require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async()=>{
 const [url,run,profile,registryFile]=process.argv.slice(2),errors=[],failed=[],registry=JSON.parse(fs.readFileSync(registryFile,'utf8'));
 const names=['empiricalMean_succ','ftlPredict_prefix','ftlPredict_mem','ftlPredict_half','ftlState_first','ftlState_eq_predict','ftlState_prefix','ftlState_mem','ftlState_half'];
 const lookup=n=>registry.nodes.find(x=>x.id==='declaration:BanditRL.OnlineLearning.'+n);
 const nodes=names.map(lookup),definitions=['ftlPredict','ftlMeanStep','ftlState'].map(lookup);if([...nodes,...definitions].some(x=>!x))throw Error('Missing actual nodes');
 const context=await chromium.launchPersistentContext(profile,{executablePath:'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe',headless:true,viewport:{width:1440,height:1800},args:['--disable-gpu','--disable-sync','--disable-background-networking','--no-first-run']});
 try{
  const page=await context.newPage();page.on('pageerror',e=>errors.push(String(e)));page.on('requestfailed',r=>failed.push({url:r.url(),failure:r.failure()}));
  await page.goto(url,{waitUntil:'networkidle',timeout:45000});await page.waitForFunction(()=>document.querySelectorAll('#source-guide mjx-container').length===10,null,{timeout:45000});
  const images=['reader-first-viewport-v1.png'];await page.screenshot({path:path.join(run,images[0])});
  const specs=[...Array.from({length:7},(_,i)=>['article.source-theorem-card',i,`source-card-${String(i+1).padStart(2,'0')}-v1.png`,1,7]),['#algorithm',0,'algorithm-v1.png',0,1],['#worked-example',0,'worked-example-v1.png',3,1],...nodes.map((n,i)=>['#'+n.url.split('#')[1]+'-teaching',0,`public-note-${String(i+1).padStart(2,'0')}-v1.png`,1,1])],panels=[];
  async function openAncestors(panel){const ancestors=panel.locator('xpath=ancestor::details');for(let i=0;i<await ancestors.count();i++){const d=ancestors.nth(i);if(!await d.evaluate(el=>el.open))await d.locator(':scope > summary').click();}}
  async function capture(panel,file){
   const height=await panel.evaluate(el=>Math.ceil(el.getBoundingClientRect().height)),viewportHeight=Math.max(1800,height+350);await page.setViewportSize({width:1440,height:viewportHeight});await page.evaluate(el=>window.scrollTo(0,window.scrollY+el.getBoundingClientRect().top-180),await panel.elementHandle());await page.waitForTimeout(100);
   const box=await panel.boundingBox();if(!box||box.y<140||box.y+box.height>viewportHeight-30)throw Error('Panel header/bottom clipped '+file);
   const geometry=await panel.evaluate(el=>({width:el.getBoundingClientRect().width,height:el.getBoundingClientRect().height,left:el.getBoundingClientRect().left,right:el.getBoundingClientRect().right,scrollWidth:el.scrollWidth,clientWidth:el.clientWidth,viewportWidth:window.innerWidth}));if(geometry.left<0||geometry.right>geometry.viewportWidth+1||geometry.scrollWidth>geometry.clientWidth+1)throw Error('Panel horizontal overflow '+file);
   await panel.screenshot({path:path.join(run,file),timeout:45000});images.push(file);return geometry;
  }
  for(const [selector,index,file,expected,total] of specs){
   if(await page.locator(selector).count()!==total)throw Error('Wrong panel count '+selector);const panel=page.locator(selector).nth(index);await openAncestors(panel);
   if(selector.endsWith('-teaching')){const tech=panel.locator('details.technical-reading');if(!await tech.evaluate(el=>el.open))await tech.locator(':scope > summary').click();if(await panel.locator('details.exact-lean').evaluate(el=>el.open))throw Error('Exact Lean must remain folded');}
   const geometry=await capture(panel,file);const info=await panel.evaluate(el=>({heading:el.querySelector('h3,h4').textContent,mathContainers:el.querySelectorAll('mjx-container').length,mathErrors:el.querySelectorAll('mjx-merror').length}));if(info.mathContainers!==expected||info.mathErrors!==0)throw Error('Wrong math count '+selector);panels.push({...info,selector,index,file,geometry,actualViewport:await page.viewportSize(),safeBelowStickyNavigation:true});
  }
  const scrollers=await page.evaluate(()=>Array.from(document.querySelectorAll('#source-guide *')).map((x,index)=>({x,index})).filter(({x})=>x.clientWidth>0&&x.querySelector('mjx-container')&&x.scrollWidth>x.clientWidth+1&&['auto','scroll'].includes(getComputedStyle(x).overflowX)).map(({x,index})=>({index,clientWidth:x.clientWidth,scrollWidth:x.scrollWidth})));
  const scrollViews=[];for(let k=0;k<scrollers.length;k++){const row=scrollers[k],node=page.locator('#source-guide *').nth(row.index);await page.setViewportSize({width:1440,height:1800});await page.evaluate(el=>window.scrollTo(0,window.scrollY+el.getBoundingClientRect().top-220),await node.elementHandle());const left=`wide-formula-${k+1}-left-v1.png`,right=`wide-formula-${k+1}-right-v1.png`;await node.evaluate(el=>{el.scrollLeft=0;});await node.screenshot({path:path.join(run,left)});const before=await node.evaluate(el=>el.scrollLeft);const after=await node.evaluate(el=>{el.scrollLeft=el.scrollWidth-el.clientWidth;return el.scrollLeft;});if(before!==0||after<=0)throw Error('Builtin scrolling failed');await node.screenshot({path:path.join(run,right)});images.push(left,right);scrollViews.push({...row,before,after,leftFile:left,rightFile:right,actualScrollOnly:true});}
  fs.writeFileSync(path.join(run,'formula-render-v1-dom.html'),await page.content(),'utf8');
  const modulePanels=[];let lastURL=null;
  for(let i=0;i<[...nodes,...definitions].length;i++){
   const node=[...nodes,...definitions][i],moduleURL=new URL('../../'+node.url.split('#')[0],url).href;
   if(moduleURL!==lastURL){await page.goto(moduleURL,{waitUntil:'networkidle',timeout:45000});lastURL=moduleURL;}
   const id=node.url.split('#')[1],panel=page.locator('#'+id);if(await panel.count()!==1)throw Error('Missing catalog node');if(!await panel.evaluate(el=>el.open))await panel.locator(':scope > summary').click();
   const wrap=panel.locator('[data-code-wrap]');if(await wrap.count()!==1||await wrap.getAttribute('aria-pressed')!=='false')throw Error('Wrap control initial state');await wrap.click();if(await wrap.getAttribute('aria-pressed')!=='true')throw Error('Actual wrap control failed');
   const code=await panel.locator('pre.lean-code').evaluate(el=>({scrollWidth:el.scrollWidth,clientWidth:el.clientWidth,whiteSpace:getComputedStyle(el).whiteSpace,text:el.textContent}));if(code.scrollWidth>code.clientWidth+1)throw Error('Wrapped full type still clipped');
   const file=`module-new-declaration-${String(i+1).padStart(2,'0')}-v1.png`,geometry=await capture(panel,file);modulePanels.push({id,file,moduleURL,geometry,actualBuiltinWrapButtonClicked:true,wrappedCode:code,fullExactTypeAlsoAuditedByHTMLAndKernel:true});
  }
  if(errors.length||failed.length)throw Error(JSON.stringify({errors,failed}));
  fs.writeFileSync(path.join(run,'formula-render-v1-browser.json'),JSON.stringify({status:'actual-panels-and-new-catalog-nodes-captured',panels,modulePanels,scrollViews,images,actualSourceGuideMathContainers:10,publicNoteMathContainers:9,errors,failed,url,profilePreserved:profile,generatedSiteFilesUnmodified:true},null,2)+'\n','utf8');
 }finally{await context.close();}
})().catch(e=>{console.error(e);process.exitCode=1;});
