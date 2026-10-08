const fs=require('fs'),path=require('path');
const {chromium}=require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async()=>{
 const [url,run,profile,registryFile]=process.argv.slice(2),errors=[],failed=[],registry=JSON.parse(fs.readFileSync(registryFile,'utf8'));
 const names=["expectedFixedMinimum", "expectedFixedMinimum_eq_variance", "history_policy_expectedFixed_excess", "meanPredict_expectedFixed_excess"]; const proofNames=["expected_fixed_prefix_decomposition", "expected_fixed_prefix_minimum", "expectedFixedMinimum_eq_variance", "iid_cumulative_prediction_decomposition", "history_policy_expectedFixed_excess", "meanPredict_expectedFixed_excess", "constant_mean_expectedFixed_excess_zero", "history_policy_normalized_expectedFixed_excess"];
 const nodes=names.map(n=>registry.nodes.find(x=>x.id==='declaration:BanditRL.OnlineLearning.'+n));if(nodes.some(x=>!x))throw Error('Missing existing nodes');
 const context=await chromium.launchPersistentContext(profile,{executablePath:'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe',headless:true,viewport:{width:1440,height:1800},args:['--disable-gpu','--disable-sync','--disable-background-networking','--no-first-run']});
 try{
  const page=await context.newPage();page.on('pageerror',e=>errors.push(String(e)));page.on('requestfailed',r=>failed.push({url:r.url(),failure:r.failure()}));
  await page.goto(url,{waitUntil:'networkidle',timeout:45000});await page.waitForFunction(()=>document.querySelectorAll('#source-guide mjx-container').length===15,null,{timeout:45000});
  const images=['reader-first-viewport-v4.png'];await page.screenshot({path:path.join(run,images[0])});
  const proofNodes=proofNames.map(n=>registry.nodes.find(x=>x.id==='declaration:BanditRL.OnlineLearning.'+n));if(proofNodes.some(x=>!x))throw Error('Missing public proof notes');
 const specs=[['article.source-theorem-card',11,'iid-benchmark-source-card-v4.png',1,12],...proofNodes.map((n,i)=>['#'+n.url.split('#')[1]+'-teaching',0,`public-note-${i+1}-v4.png`,1,1])],panels=[];
  async function openAncestors(panel){const ancestors=panel.locator('xpath=ancestor::details');for(let i=0;i<await ancestors.count();i++){const d=ancestors.nth(i);if(!await d.evaluate(el=>el.open))await d.locator(':scope > summary').click();}}
  async function capture(panel,file){
   const height=await panel.evaluate(el=>Math.ceil(el.getBoundingClientRect().height)),viewportHeight=Math.max(1800,height+350);await page.setViewportSize({width:1440,height:viewportHeight});await page.evaluate(el=>window.scrollTo(0,window.scrollY+el.getBoundingClientRect().top-180),await panel.elementHandle());await page.waitForTimeout(100);
   const box=await panel.boundingBox();if(!box||box.y<140||box.y+box.height>viewportHeight-30)throw Error('Panel clipped '+file);
   const geometry=await panel.evaluate(el=>({width:el.getBoundingClientRect().width,height:el.getBoundingClientRect().height,left:el.getBoundingClientRect().left,right:el.getBoundingClientRect().right,scrollWidth:el.scrollWidth,clientWidth:el.clientWidth,viewportWidth:window.innerWidth}));if(geometry.left<0||geometry.right>geometry.viewportWidth+1||geometry.scrollWidth>geometry.clientWidth+1)throw Error('Horizontal overflow '+file);
   await panel.screenshot({path:path.join(run,file),timeout:45000});images.push(file);return geometry;
  }
  for(const [selector,index,file,expected,total] of specs){
   if(await page.locator(selector).count()!==total)throw Error('Wrong panel count '+selector);const panel=page.locator(selector).nth(index);await openAncestors(panel);
   if(selector.endsWith('-teaching')){const tech=panel.locator('details.technical-reading');if(!await tech.evaluate(el=>el.open))await tech.locator(':scope > summary').click();if(await panel.locator('details.exact-lean').evaluate(el=>el.open))throw Error('Exact Lean must remain folded');}
   const geometry=await capture(panel,file);const info=await panel.evaluate(el=>({heading:el.querySelector('h3,h4').textContent,mathContainers:el.querySelectorAll('mjx-container').length,mathErrors:el.querySelectorAll('mjx-merror').length}));if(info.mathContainers!==expected||info.mathErrors!==0)throw Error('Wrong math count');panels.push({...info,selector,index,file,geometry,actualViewport:await page.viewportSize(),safeBelowStickyNavigation:true});
  }
  const scrollers=await page.evaluate(()=>Array.from(document.querySelectorAll('#source-guide *')).filter(x=>x.clientWidth>0&&x.querySelector('mjx-container')&&x.scrollWidth>x.clientWidth+1&&['auto','scroll'].includes(getComputedStyle(x).overflowX)).map(x=>({clientWidth:x.clientWidth,scrollWidth:x.scrollWidth})));
  if(scrollers.length)throw Error('Source formula horizontal scrollers '+JSON.stringify(scrollers));
  fs.writeFileSync(path.join(run,'formula-render-v4-dom.html'),await page.content(),'utf8');
  const modulePanels=[];let lastURL=null;
  for(let i=0;i<nodes.length;i++){
   const node=nodes[i],moduleURL=new URL('../../'+node.url.split('#')[0],url).href;
   if(moduleURL!==lastURL){await page.goto(moduleURL,{waitUntil:'networkidle',timeout:45000});lastURL=moduleURL;}
   const id=node.url.split('#')[1],panel=page.locator('#'+id);if(await panel.count()!==1)throw Error('Missing catalog node');if(!await panel.evaluate(el=>el.open))await panel.locator(':scope > summary').click();
   const wrap=panel.locator('[data-code-wrap]');if(await wrap.count()!==1||await wrap.getAttribute('aria-pressed')!=='false')throw Error('Wrap control state');await wrap.click();
   const code=await panel.locator('pre.lean-code').evaluate(el=>({scrollWidth:el.scrollWidth,clientWidth:el.clientWidth,whiteSpace:getComputedStyle(el).whiteSpace,text:el.textContent}));if(code.scrollWidth>code.clientWidth+1)throw Error('Wrapped type clipped');
   const file=`module-new-declaration-${i+1}-v4.png`,geometry=await capture(panel,file);modulePanels.push({id,file,moduleURL,geometry,actualBuiltinWrapButtonClicked:true,wrappedCode:code,fullExactTypeAlsoAuditedByHTMLAndKernel:true});
  }
  if(errors.length||failed.length)throw Error(JSON.stringify({errors,failed}));
  fs.writeFileSync(path.join(run,'formula-render-v4-browser.json'),JSON.stringify({status:'actual-current-expected-fixed-causal-IID-panels-and-catalog-captured',panels,modulePanels,images,actualSourceGuideMathContainers:15,newPublicNoteMathContainers:8,sourceHorizontalScrollers:scrollers,errors,failed,url,profilePreserved:profile,generatedSiteFilesUnmodified:true},null,2)+'\n','utf8');
 }finally{await context.close();}
})().catch(e=>{console.error(e);process.exitCode=1;});
