const fs=require('fs'),path=require('path');
const {chromium}=require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async()=>{
 const [url,run,profile,registryFile,targetsFile,sourceCards,sourceMath]=process.argv.slice(2);
 const registry=JSON.parse(fs.readFileSync(registryFile,'utf8'));
 const targets=JSON.parse(fs.readFileSync(targetsFile,'utf8')).targets.map(t=>({name:t.declaration}));
 const nodes=targets.map(t=>registry.nodes.find(n=>n.id==='declaration:'+t.name));
 if(nodes.length!==10||nodes.some(n=>!n))throw Error('Missing ten new public nodes');
 const errors=[],failed=[],images=[],panels=[],modulePanels=[];
 const context=await chromium.launchPersistentContext(profile,{executablePath:'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe',headless:true,viewport:{width:1440,height:1800},args:['--disable-gpu','--disable-sync','--disable-background-networking','--no-first-run']});
 try{
  const page=await context.newPage();page.on('pageerror',e=>errors.push(String(e)));page.on('requestfailed',r=>failed.push({url:r.url(),failure:r.failure()}));
  await page.goto(url,{waitUntil:'networkidle',timeout:45000});
  await page.waitForFunction(n=>document.querySelectorAll('#source-guide mjx-container').length===n,Number(sourceMath),{timeout:45000});
  await page.screenshot({path:path.join(run,'reader-first-viewport-v2.png')});images.push('reader-first-viewport-v2.png');
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
  const specs=[['article.source-theorem-card',Number(sourceCards)-1,'prescient-source-card-v2.png',Number(sourceCards)],...nodes.map((n,i)=>['#'+n.url.split('#')[1]+'-teaching',0,`public-note-${i+1}-v2.png`,1])];
  for(const [selector,index,file,count] of specs){
   if(await page.locator(selector).count()!==count)throw Error('Wrong panel count '+selector);
   const panel=page.locator(selector).nth(index);await openAncestors(panel);
   if(selector.endsWith('-teaching')){const tech=panel.locator('details.technical-reading');if(!await tech.evaluate(el=>el.open))await tech.locator(':scope > summary').click();if(await panel.locator('details.exact-lean').evaluate(el=>el.open))throw Error('Exact Lean must remain folded');}
   const geometry=await capture(panel,file),math=await panel.evaluate(el=>({mathContainers:el.querySelectorAll('mjx-container').length,mathErrors:el.querySelectorAll('mjx-merror, [mathcolor="red"], [data-mjx-error]').length}));
   if(math.mathContainers!==1||math.mathErrors!==0)throw Error('Math rendering count/error '+file);
   if(file==='public-note-7-v2.png'){const mml=await panel.locator('mjx-assistive-mml').textContent();if(!mml.includes('\u2200')||!mml.includes('argmin')||!mml.includes('\u2203'))throw Error('Completion premise missing from actual MathML');}
   panels.push({selector,index,file,geometry,...math,actualViewport:page.viewportSize(),belowStickyNavigation:true});
  }
  const scrollers=await page.evaluate(()=>Array.from(document.querySelectorAll('#source-guide *')).filter(x=>x.clientWidth>0&&x.querySelector('mjx-container')&&x.scrollWidth>x.clientWidth+1&&['auto','scroll'].includes(getComputedStyle(x).overflowX)).map(x=>({clientWidth:x.clientWidth,scrollWidth:x.scrollWidth})));
  if(scrollers.length)throw Error('Source math horizontal scrollers');
  fs.writeFileSync(path.join(run,'formula-render-v1-dom.html'),await page.content(),{encoding:'utf8',flag:'wx'});
  let lastURL=null;
  for(let i=0;i<nodes.length;i++){
   const node=nodes[i],moduleURL=new URL('../../'+node.url.split('#')[0],url).href;
   if(moduleURL!==lastURL){await page.goto(moduleURL,{waitUntil:'networkidle',timeout:45000});lastURL=moduleURL;}
   const id=node.url.split('#')[1],panel=page.locator('#'+id);if(await panel.count()!==1)throw Error('Missing catalogue node');
   if(!await panel.evaluate(el=>el.open))await panel.locator(':scope > summary').click();
   const wrap=panel.locator('[data-code-wrap]');if(await wrap.count()!==1||await wrap.getAttribute('aria-pressed')!=='false')throw Error('Builtin wrap control');await wrap.click();
   const code=await panel.locator('pre.lean-code').evaluate(el=>({scrollWidth:el.scrollWidth,clientWidth:el.clientWidth,text:el.textContent,whiteSpace:getComputedStyle(el).whiteSpace}));
   if(code.scrollWidth>code.clientWidth+1)throw Error('Wrapped type clipped');
   const file=`module-declaration-${i+1}-v2.png`,geometry=await capture(panel,file);
   modulePanels.push({id,file,moduleURL,geometry,wrappedCode:code,actualBuiltinWrapButtonClicked:true});
  }
  if(errors.length||failed.length)throw Error(JSON.stringify({errors,failed}));
  fs.writeFileSync(path.join(run,'formula-render-v1-browser.json'),JSON.stringify({status:'actual-prescient-partial-recursion-captured',panels,modulePanels,images,actualSourceGuideMathContainers:Number(sourceMath),sourceHorizontalScrollers:scrollers,errors,failed,url,profilePreserved:profile,generatedSiteFilesUnmodified:true},null,2)+'\n',{encoding:'utf8',flag:'wx'});
 }finally{await context.close();}
})().catch(e=>{console.error(e);process.exitCode=1;});
