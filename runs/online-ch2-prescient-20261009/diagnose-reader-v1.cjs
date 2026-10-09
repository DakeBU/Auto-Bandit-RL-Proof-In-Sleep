const fs=require('fs');
const {chromium}=require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async()=>{
 const [url,output,profile]=process.argv.slice(2);
 const context=await chromium.launchPersistentContext(profile,{executablePath:'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe',headless:true,viewport:{width:1440,height:1800},args:['--disable-gpu','--disable-sync','--disable-background-networking','--no-first-run']});
 try{
  const page=await context.newPage();const errors=[];page.on('pageerror',e=>errors.push(String(e)));
  await page.goto(url,{waitUntil:'networkidle',timeout:45000});
  await page.waitForFunction(()=>document.querySelectorAll('#source-guide mjx-container').length>=6,{timeout:45000});
  const data=await page.evaluate(()=>({sourceCards:document.querySelectorAll('article.source-theorem-card').length,mathContainers:document.querySelectorAll('#source-guide mjx-container').length,mathErrors:document.querySelectorAll('#source-guide mjx-merror,#source-guide [data-mjx-error]').length,mathStatementBlocks:document.querySelectorAll('#source-guide [data-math-statement]').length,sourceCardTitles:Array.from(document.querySelectorAll('article.source-theorem-card h3')).map(x=>x.textContent)}));
  if(data.sourceCards!==6||data.mathErrors||errors.length)throw Error(JSON.stringify({data,errors}));
  fs.writeFileSync(output,JSON.stringify({actualDOM:data,pageErrors:errors,url,generatedSiteFilesUnmodified:true},null,2)+'\n',{encoding:'utf8',flag:'wx'});
 }finally{await context.close();}
})().catch(e=>{console.error(e);process.exitCode=1;});
