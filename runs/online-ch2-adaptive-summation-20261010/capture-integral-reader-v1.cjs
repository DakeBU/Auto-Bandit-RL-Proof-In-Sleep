const fs=require('fs'),path=require('path');
const {chromium}=require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async()=>{
 const [url,run,profile,registryFile]=process.argv.slice(2);
 const registry=JSON.parse(fs.readFileSync(registryFile,'utf8'));
 const node=registry.nodes.find(n=>n.id==='declaration:BanditRL.OnlineAdaptiveSummation.lemma_4_13');
 if(!node)throw Error('Missing canonical integral-comparison theorem');
 const names=['reader-first-viewport-v1.png','integral-source-card-v1.png','integral-teaching-note-v1.png','integral-module-declaration-v1.png','formula-render-v1-dom.html','formula-render-v1-browser.json'];
 for(const name of names)if(fs.existsSync(path.join(run,name)))throw Error('Create-only artifact already exists '+name);
 if(fs.existsSync(profile))throw Error('Create-only isolated profile already exists');
 const errors=[],failed=[],images=[],panels=[];
 const context=await chromium.launchPersistentContext(profile,{executablePath:'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe',headless:true,viewport:{width:1440,height:1800},args:['--disable-gpu','--disable-sync','--disable-background-networking','--no-first-run']});
 try{
  const page=await context.newPage();page.on('pageerror',e=>errors.push(String(e)));page.on('requestfailed',r=>failed.push({url:r.url(),failure:r.failure()}));
  await page.goto(url,{waitUntil:'networkidle',timeout:45000});
  await page.waitForFunction(()=>document.querySelectorAll('#source-guide mjx-container').length===18,{timeout:45000});
  if(await page.locator('article.source-theorem-card').count()!==15)throw Error('Fifteen source cards required');
  await page.screenshot({path:path.join(run,names[0])});images.push(names[0]);
  async function openAncestors(panel){const ds=panel.locator('xpath=ancestor::details');for(let i=0;i<await ds.count();i++){const d=ds.nth(i);if(!await d.evaluate(el=>el.open))await d.locator(':scope > summary').click();}}
  async function capture(panel,file){
   const height=await panel.evaluate(el=>Math.ceil(el.getBoundingClientRect().height));
   await page.setViewportSize({width:1440,height:Math.max(1800,height+350)});
   await page.evaluate(el=>window.scrollTo(0,window.scrollY+el.getBoundingClientRect().top-180),await panel.elementHandle());await page.waitForTimeout(75);
   const box=await panel.boundingBox();if(!box||box.y<140||box.y+box.height>page.viewportSize().height-30)throw Error('Clipped panel '+file);
   const geometry=await panel.evaluate(el=>({left:el.getBoundingClientRect().left,right:el.getBoundingClientRect().right,height:el.getBoundingClientRect().height,scrollWidth:el.scrollWidth,clientWidth:el.clientWidth,viewportWidth:window.innerWidth}));
   if(geometry.left<0||geometry.right>geometry.viewportWidth+1||geometry.scrollWidth>geometry.clientWidth+1)throw Error('Horizontal overflow '+file);
   await panel.screenshot({path:path.join(run,file),timeout:45000});images.push(file);return geometry;
  }
  for(const [selector,index,file] of [['article.source-theorem-card',14,names[1]],['#'+node.url.split('#')[1]+'-teaching',0,names[2]]]){
   const panel=page.locator(selector).nth(index);await openAncestors(panel);
   if(selector.endsWith('-teaching')){const tech=panel.locator('details.technical-reading');if(!await tech.evaluate(el=>el.open))await tech.locator(':scope > summary').click();if(await panel.locator('details.exact-lean').evaluate(el=>el.open))throw Error('Exact Lean must remain folded');}
   const geometry=await capture(panel,file),math=await panel.evaluate(el=>({mathContainers:el.querySelectorAll('mjx-container').length,mathErrors:el.querySelectorAll('mjx-merror,[mathcolor="red"],[data-mjx-error]').length}));
   if(math.mathContainers!==1||math.mathErrors!==0)throw Error('Actual math rendering failed '+file);
   const prose=await panel.innerText();
   for(const text of ['Lemma4.13','All eight Chapter2 forward containers','Whole Chapters1-16 Goal ACTIVE','minimum-versus-infimum','nonnegative half-line'])if(!prose.includes(text))throw Error('Source/boundary missing '+text);
   if(file===names[1]){const mml=await panel.locator('mjx-assistive-mml').textContent();if(!mml.includes('∑')||!mml.includes('∫')||!mml.includes('0'))throw Error('Actual source sum/integral/offset MathML missing');}
   panels.push({selector,index,file,geometry,...math,actualViewport:page.viewportSize(),belowStickyNavigation:true});
  }
  const scrollers=await page.evaluate(()=>Array.from(document.querySelectorAll('#source-guide *')).filter(x=>x.clientWidth>0&&x.querySelector('mjx-container')&&x.scrollWidth>x.clientWidth+1&&['auto','scroll'].includes(getComputedStyle(x).overflowX)).map(x=>({clientWidth:x.clientWidth,scrollWidth:x.scrollWidth})));
  if(scrollers.length)throw Error('Source math horizontal scrollers');
  fs.writeFileSync(path.join(run,names[4]),await page.content(),{encoding:'utf8',flag:'wx'});
  const moduleURL=new URL('../../'+node.url.split('#')[0],url).href;
  await page.goto(moduleURL,{waitUntil:'networkidle',timeout:45000});
  const id=node.url.split('#')[1],panel=page.locator('#'+id);if(await panel.count()!==1)throw Error('Missing catalog node');
  if(!await panel.evaluate(el=>el.open))await panel.locator(':scope > summary').click();
  const wrap=panel.locator('[data-code-wrap]');if(await wrap.count()!==1||await wrap.getAttribute('aria-pressed')!=='false')throw Error('Builtin wrap control absent');await wrap.click();
  if(await wrap.getAttribute('aria-pressed')!=='true')throw Error('Builtin wrap did not activate');
  const code=await panel.locator('pre.lean-code').evaluate(el=>({scrollWidth:el.scrollWidth,clientWidth:el.clientWidth,text:el.textContent,whiteSpace:getComputedStyle(el).whiteSpace}));
  if(code.scrollWidth>code.clientWidth+1||!code.text.includes('lemma_4_13')||!code.text.includes('sum_integral_adjacent_intervals'))throw Error('Wrapped full declaration/proof absent or clipped');
  const geometry=await capture(panel,names[3]);
  if(errors.length||failed.length)throw Error(JSON.stringify({errors,failed}));
  fs.writeFileSync(path.join(run,names[5]),JSON.stringify({status:'actual-integral-prerequisite-captured',panels,modulePanels:[{id,file:names[3],moduleURL,geometry,wrappedCode:code,actualBuiltinWrapButtonClicked:true}],images,actualSourceGuideMathContainers:18,sourceCards:15,sourceHorizontalScrollers:scrollers,errors,failed,url,profilePreserved:profile,scope:'Actual local fileURI desktop rendering only; original pixels require personal root/reviewer inspection. No HTTP/live/mobile claim.'},null,2)+'\n',{encoding:'utf8',flag:'wx'});
 }finally{await context.close();}
})().catch(e=>{console.error(e);process.exitCode=1;});
