const fs=require('fs'),path=require('path');
const {chromium}=require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async()=>{
 const [url,run,profile]=process.argv.slice(2),errors=[],failed=[];
 const context=await chromium.launchPersistentContext(profile,{executablePath:'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe',headless:true,viewport:{width:1440,height:1800},args:['--disable-gpu','--disable-sync','--disable-background-networking','--no-first-run']});
 try{
  const page=await context.newPage();page.on('pageerror',e=>errors.push(String(e)));page.on('requestfailed',r=>failed.push({url:r.url(),failure:r.failure()}));
  await page.goto(url,{waitUntil:'networkidle',timeout:45000});await page.waitForFunction(()=>document.querySelectorAll('#source-guide mjx-container').length===12,null,{timeout:45000});
  const node=page.locator('#algorithm pre');if(await node.count()!==1)throw Error('Expected single pseudocode pre');
  const geometry=await node.evaluate(el=>({clientWidth:el.clientWidth,scrollWidth:el.scrollWidth,overflowX:getComputedStyle(el).overflowX,lines:el.textContent}));
  if(geometry.scrollWidth<=geometry.clientWidth+1||!['auto','scroll'].includes(geometry.overflowX))throw Error('Expected actual builtin code overflow');
  await page.evaluate(el=>window.scrollTo(0,window.scrollY+el.getBoundingClientRect().top-220),await node.elementHandle());
  const files=['algorithm-code-left-v1.png','algorithm-code-right-v1.png'];await node.evaluate(el=>{el.scrollLeft=0;});await node.screenshot({path:path.join(run,files[0])});
  const before=await node.evaluate(el=>el.scrollLeft);const after=await node.evaluate(el=>{el.scrollLeft=el.scrollWidth-el.clientWidth;return {scrollLeft:el.scrollLeft,clientWidth:el.clientWidth,scrollWidth:el.scrollWidth};});
  if(before!==0||after.scrollLeft<=0||after.scrollLeft!==after.scrollWidth-after.clientWidth)throw Error('Actual code scroll not realized');
  await page.waitForTimeout(100);await node.screenshot({path:path.join(run,files[1])});
  if(errors.length||failed.length)throw Error(JSON.stringify({errors,failed}));
  fs.writeFileSync(path.join(run,'algorithm-scroll-v1-browser.json'),JSON.stringify({status:'actual-builtin-code-left-right-scroll-pair',selector:'#algorithm pre',url,geometry,before,after,files,errors,failed,noDOMCSSOrGeneratedFileEdit:true,actualScrollOnly:true},null,2)+'\n');
 }finally{await context.close();}
})().catch(e=>{console.error(e);process.exitCode=1;});
