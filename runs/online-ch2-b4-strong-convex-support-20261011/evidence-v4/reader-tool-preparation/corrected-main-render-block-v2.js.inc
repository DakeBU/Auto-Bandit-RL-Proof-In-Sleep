    // Exact current source-driven cases; no old-object or rendering exemption.
    const mainRenderBytes=fs.readFileSync(path.join(root,inputSpec.corrected_main_render_inputs.path));
    if(hash(mainRenderBytes)!==inputSpec.corrected_main_render_inputs.sha256)throw Error('Corrected-main input SHA');
    const mainRender=JSON.parse(mainRenderBytes);
    for(const [p,sha] of Object.entries(mainRender.source_RAW))if(hash(fs.readFileSync(path.join(root,p)))!==sha)throw Error('Corrected-main source RAW '+p);
    report.correctedMain={inputSHA256:hash(mainRenderBytes),chapters:[],lessons:[],sourceCards:[],proofDisclosures:[],missionPanels:[]};
    const safeCase=s=>s.replace(/[^A-Za-z0-9_-]/g,'-');
    async function exactOne(selector,label){const x=page.locator(selector);if(await x.count()!==1)throw Error('Unique '+label+' '+selector);return x;}
    async function openRecordedAncestors(panel,label){
      const initial=await panel.evaluate(e=>{const a=[];for(let p=e.parentElement;p;p=p.parentElement)if(p.tagName==='DETAILS')a.push({summary:p.querySelector(':scope > summary')?.textContent,open:p.open});return a;});
      const ancestors=panel.locator('xpath=ancestor::details');
      for(let i=0;i<await ancestors.count();i++){const a=ancestors.nth(i);if(!(await a.evaluate(e=>e.open)))await a.locator(':scope > summary').click();}
      return {label,initial};
    }
    async function readyMath(panel,label,required){
      if(required)await panel.locator('mjx-container').first().waitFor({state:'visible',timeout:60000});
      const value=await data(panel);if(value.mathErrors||(required&&!value.mathContainers))throw Error('MathJax render '+label);return value;
    }
    async function strictPanelShots(panel,label){
      for(const width of [1440,390]){
        await page.setViewportSize({width,height:1800});
        await panel.scrollIntoViewIfNeeded();
        const bad=await panel.evaluate(el=>{
          const p=el.getBoundingClientRect();
          return [...el.querySelectorAll('h1,h2,h3,h4,p,dt,dd,pre,summary,a,mjx-container,.source-route-status,.source-theorem-heading')].flatMap(e=>{
            const q=e.getBoundingClientRect(),c=getComputedStyle(e);if(!q.width||!q.height||c.display==='none'||c.visibility==='hidden')return [];
            const ownOverflow=e.clientWidth>0&&e.scrollWidth>e.clientWidth+1;
            const ancestors=[];for(let a=e.parentElement;a&&a!==el.parentElement;a=a.parentElement){const b=a.getBoundingClientRect(),s=getComputedStyle(a);if(['hidden','clip'].includes(s.overflowX)&&(q.left<b.left-1||q.right>b.right+1))ancestors.push({tag:a.tagName,class:a.className,overflowX:s.overflowX,left:b.left,right:b.right});}
            return q.left<p.left-1||q.right>p.right+1||ownOverflow||ancestors.length?[{tag:e.tagName,class:e.className,text:e.textContent.slice(0,180),left:q.left,right:q.right,scrollWidth:e.scrollWidth,clientWidth:e.clientWidth,clippingAncestors:ancestors}]:[];
          });
        });
        if(bad.length){write('strict-clipping-'+label+'-'+width+'.json',JSON.stringify(bad,null,2));await page.screenshot({path:path.join(output,'strict-clipping-'+label+'-'+width+'.png'),fullPage:false});throw Error('Visible descendant clipping '+label+' '+width);}
      }
      return await screenshot(panel,label);
    }
    async function exactCard(label){
      const all=page.locator('article.source-theorem-card');const labels=await all.locator('h3').allTextContents();
      const indexes=labels.flatMap((x,i)=>norm(x)===norm(label)?[i]:[]);if(indexes.length!==1)throw Error('Unique exact current source label '+label);return all.nth(indexes[0]);
    }
    async function offeredLeanProofs(panel,sourceText,label){
      const all=panel.locator('details'),found=[];
      for(let i=0;i<await all.count();i++){
        const detail=all.nth(i),summary=norm(await detail.locator(':scope > summary').textContent());
        if(!/(?:exact|full|complete)\s+Lean\s+proof|Lean proof body/i.test(summary))continue;
        const initialOpen=await detail.evaluate(e=>e.open);if(initialOpen)throw Error('Lean proof initially unfolded '+label);
        await detail.locator(':scope > summary').click();const code=detail.locator('pre');if(await code.count()!==1)throw Error('Unique exposed Lean proof '+label);
        const text=norm(await code.textContent());if(!text||!norm(sourceText).includes(text))throw Error('Exposed Lean proof differs from pinned source '+label);
        found.push({summary,initialOpen,opened:await detail.evaluate(e=>e.open),normalizedText:text,screenshots:await strictPanelShots(detail,label+'-proof-'+i)});
      }
      report.correctedMain.proofDisclosures.push({label,offered:found.length,details:found,absenceBoundary:found.length?null:'No exact/full Lean proof disclosure offered by this panel; whole source RAW and exact commit/line links checked separately.'});
    }
    async function exactLesson(entry){
      const lesson=entry.highlight,decl=entry.declaration,name=lesson.full_name,stem='main-'+safeCase(name);
      const matches=registry.nodes.filter(n=>n.id==='declaration:'+name);if(matches.length!==1||matches[0].status!=='compiled'||matches[0].url.split('#')[1]!==decl.anchor)throw Error('Registry exact compiled identity '+name);
      const chapterURL=new URL('/chapters/'+lesson.chapter+'/',url).href;
      await exactHTTP(chapterURL);await page.goto(chapterURL,{waitUntil:'networkidle',timeout:60000});
      const panel=await exactOne('[id="'+decl.anchor+'-teaching"]',name);
      const ancestorState=await openRecordedAncestors(panel,name);
      const exact=panel.locator('details.exact-lean'),technical=panel.locator('details.technical-reading');
      if(await exact.count()!==1||await technical.count()!==1)throw Error('Unique lesson disclosures '+name);
      const initial={exactOpen:await exact.evaluate(e=>e.open),technicalOpen:await technical.evaluate(e=>e.open)};
      if(initial.exactOpen||initial.technicalOpen)throw Error('Initial folded lesson state changed '+name);
      const normalizedStatement=norm(decl.statement),foldedText=norm(await exact.locator('pre').textContent());
      if(foldedText!==normalizedStatement)throw Error('Folded full source header '+name);
      const foldedShots=await strictPanelShots(panel,stem+'-folded');
      await technical.locator(':scope > summary').click();
      const value=await readyMath(panel,name,Boolean(lesson.math));
      requireWords(value.text,[name,lesson.plain,lesson.intuition,lesson.why,lesson.position,lesson.proof_idea,lesson.lean_notes,...lesson.dependencies],name);
      const sourceURL=`https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/${expectedHead}/${decl.file}#L${decl.line}`;
      if(!value.links.some(x=>x.href===sourceURL))throw Error('Lesson pinned source line '+name);
      await exact.locator(':scope > summary').click();if(!(await exact.evaluate(e=>e.open))||norm(await exact.locator('pre').innerText())!==normalizedStatement)throw Error('Actual unfolded exact header '+name);
      const sourceText=fs.readFileSync(path.join(root,decl.file),'utf8');
      await offeredLeanProofs(panel,sourceText,stem+'-lesson');
      const openShots=await strictPanelShots(panel,stem+'-unfolded');write(stem+'-lesson-dom.html',await page.content());
      const moduleURL=new URL('../../'+matches[0].url.split('#')[0],url).href;
      await exactHTTP(moduleURL);await page.goto(moduleURL,{waitUntil:'networkidle',timeout:60000});
      const catalog=await exactOne('[id="'+decl.anchor+'"]',name+' catalog');await openRecordedAncestors(catalog,name+' catalog');
      const catalogInitialOpen=await catalog.evaluate(e=>e.open);if(catalogInitialOpen)throw Error('Catalog declaration initially unfolded '+name);
      await catalog.locator(':scope > summary').click();await verifyWrapControl(catalog,normalizedStatement,name);
      if(!(await catalog.locator('.source-links a').evaluateAll(xs=>xs.map(x=>x.href))).includes(sourceURL))throw Error('Catalog pinned complete source link '+name);
      await offeredLeanProofs(catalog,sourceText,stem+'-catalog');const catalogShots=await strictPanelShots(catalog,stem+'-catalog');write(stem+'-catalog-dom.html',await page.content());
      report.correctedMain.lessons.push({name,chapter:lesson.chapter,ancestorState,initial,catalogInitialOpen,statement:normalizedStatement,sourceURL,sourceSHA256:hash(Buffer.from(sourceText)),foldedShots,openShots,catalogShots});
    }
    for(const chapter of mainRender.chapters){
      const chapterURL=new URL('/chapters/'+chapter.slug+'/',url).href;
      await exactHTTP(chapterURL);await page.goto(chapterURL,{waitUntil:'networkidle',timeout:60000});
      const reading=chapter.reading,cards=[...(reading.source_theorem?[reading.source_theorem]:[]),...(reading.source_theorems||[])];
      if(await page.locator('article.source-theorem-card').count()!==cards.length)throw Error('Exact current source card count '+chapter.slug);
      for(let i=0;i<cards.length;i++){
        const expected=cards[i],panel=await exactCard(expected.label),label='main-'+chapter.slug+'-source-'+i;
        const ancestors=await openRecordedAncestors(panel,label);const value=await readyMath(panel,label,Boolean(expected.math));
        requireWords(value.text,[expected.label,expected.plain,expected.relationship,...Object.values(expected.contract||{}),...(expected.local_status?[expected.local_status.label,expected.local_status.boundary]:[])],label);
        const expectedPDF=expected.pdf_page?expected.url.split('#')[0]+'#page='+expected.pdf_page:expected.url;if(!value.links.some(x=>x.href===expectedPDF))throw Error('Exact source PDF anchor '+label);
        report.correctedMain.sourceCards.push({chapter:chapter.slug,label:expected.label,ancestors,...value,screenshots:await strictPanelShots(panel,label)});
      }
      for(const [field,selector,words] of [
        ['notation','#notation',reading.notation.flatMap(x=>[x.term,x.meaning])],
        ['algorithm','#algorithm',[reading.algorithm.title,reading.algorithm.kind,...reading.algorithm.steps.flatMap(x=>[x.title,x.detail])]]
      ]){const panel=await exactOne(selector,chapter.slug+' '+field);await openRecordedAncestors(panel,field);const value=await data(panel);requireWords(value.text,words,chapter.slug+' '+field);report.panels.push({kind:'corrected-main-'+field,chapter:chapter.slug,...value,screenshot:await strictPanelShots(panel,'main-'+chapter.slug+'-'+field)});}
      for(const [field,selector] of [['proof_bridge','#proof-bridge'],['worked_example','#worked-example']]){
        const expected=reading[field];if(!expected)continue;const panel=await exactOne(selector,chapter.slug+' '+field);await openRecordedAncestors(panel,field);
        const value=await readyMath(panel,chapter.slug+' '+field,expected.steps.some(x=>Boolean(x.math)));
        requireWords(value.text,[expected.title,expected.summary||expected.intro,expected.boundary,...(expected.takeaway?[expected.takeaway]:[]),...expected.steps.flatMap(x=>[x.title,x.detail])].filter(Boolean),chapter.slug+' '+field);
        report.panels.push({kind:'corrected-main-'+field,chapter:chapter.slug,...value,screenshot:await strictPanelShots(panel,'main-'+chapter.slug+'-'+field)});
      }
      write('main-'+chapter.slug+'-source-dom.html',await page.content());
      report.correctedMain.chapters.push({slug:chapter.slug,sourceCards:cards.length,lessons:chapter.lessons.length});
      for(const entry of chapter.lessons)await exactLesson(entry);
    }
    for(const entry of mainRender.supplemental_lessons)await exactLesson(entry);
    // Previously inspected local generated selector families; exact current mission strings.
    const missionCases=[
      {path:'/',selector:'#overview',name:'home-overview',words:['BanditRLlib','Understand why a learning guarantee holds—and where it breaks.','Read the proof ideas, follow their Lean evidence, and explore how they connect across bandits, reinforcement learning and online learning.']},
      {path:'/',selector:'#math-2-0',name:'home-math-mission',words:['Our original aims meet Terence Tao’s Math 2.0','A living network → understandable mathematics → new ideas.','Source-linked research maps and a reusable Lean library are the foundations. Clear explanations and interactive teaching are the human value. Proof-method transfer, ablation and verified theorem neighborhoods are the research agenda.']},
      {path:'/math-2-0/',selector:'#mission',name:'math2-mission',words:[mainRender.math2.title,mainRender.math2.mission,'Our original goals of connected knowledge, checked proofs and clearer teaching predate and resonate with this report.','These are examples in Tao’s talk, not an official nine-goal program or an endorsement.']}
    ];
    for(const item of missionCases){
      const target=new URL(item.path,url).href;await exactHTTP(target);await page.goto(target,{waitUntil:'networkidle',timeout:60000});
      const panel=await exactOne(item.selector,item.name);const value=await data(panel);requireWords(value.text,item.words,item.name);
      if(item.path==='/math-2-0/'&&!value.links.some(x=>x.href===mainRender.math2.source.url))throw Error('Tao source link');
      report.correctedMain.missionPanels.push({name:item.name,...value,screenshots:await strictPanelShots(panel,item.name)});write(item.name+'-dom.html',await page.content());
    }
    await page.goto(new URL('/math-2-0/',url).href,{waitUntil:'networkidle',timeout:60000});
    if(await page.locator('article.math-direction').count()!==9)throw Error('Exactly nine current Math2 examples');
    for(const direction of mainRender.math2.directions){const panel=await exactOne('#direction-'+direction.number,'Math2 example');const value=await data(panel);requireWords(value.text,[direction.title,direction.role,direction.foundation,direction.next],'Math2 example '+direction.number);for(const evidence of direction.evidence){const expected=evidence.source?`https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/${expectedHead}/${evidence.source}`:new URL('/'+evidence.path,url).href;if(!value.links.some(x=>x.href===expected&&norm(x.text)===norm(evidence.title)))throw Error('Math2 exact evidence link '+direction.number+' '+evidence.title);}report.correctedMain.missionPanels.push({name:'math2-example-'+direction.number,...value,screenshots:await strictPanelShots(panel,'math2-example-'+direction.number)});}
    write('math2-directions-dom.html',await page.content());
    for(const [p,sha] of Object.entries(mainRender.source_RAW))if(hash(fs.readFileSync(path.join(root,p)))!==sha)throw Error('Corrected-main source changed during capture '+p);
    if(hash(fs.readFileSync(path.join(root,inputSpec.corrected_main_render_inputs.path)))!==hash(mainRenderBytes))throw Error('Corrected-main payload changed');
    report.correctedMain.allRequiredCasesCaptured=true;
