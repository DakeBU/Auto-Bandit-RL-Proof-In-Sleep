const fs = require('fs'), path = require('path'), crypto = require('crypto');
const { chromium } = require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
const hash = b => crypto.createHash('sha256').update(b).digest('hex');
const norm = s => s.replace(/[\u200b\u00ad]/g, '').replace(/\s+/g, ' ').trim();
const inside = (p, base) => { const rel = path.relative(base, p); return rel && !rel.startsWith('..') && !path.isAbsolute(rel); };
(async () => {
  const [url, outputArg, profileArg, registryArg, rootArg, siteArg, gateArg, gateSHA, expectedHead] = process.argv.slice(2);
  if (process.argv.slice(2).length !== 9) throw Error('Expected URL OUTPUT PROFILE REGISTRY ROOT SITE COMBINED_GATE_RECEIPT GATE_SHA256 HEAD');
  const root = fs.realpathSync(rootArg), base = path.join(root, 'tmp', 'online-main-reconciliation-mobile-status-fix-20261011');
  const output = path.resolve(outputArg), profile = path.resolve(profileArg), registryFile = fs.realpathSync(registryArg);
  const expectedSite = fs.realpathSync(siteArg);
  const gitState = () => { const run = (...args) => require('child_process').execFileSync('git',args,{cwd:root,encoding:'utf8'}).trim(); return {HEAD:run('rev-parse','HEAD'),branch:run('branch','--show-current'),status:run('status','--porcelain')}; };
  const currentGitBefore = gitState();
  if(currentGitBefore.HEAD !== expectedHead || currentGitBefore.status !== '') throw Error('Current clean candidate Git state required');
  if (!inside(expectedSite, path.join(root,'tmp'))) throw Error('Site must be isolated under root/tmp');
  const gateBytes = fs.readFileSync(gateArg), gate = JSON.parse(gateBytes);
  if (!/^[a-f0-9]{40}$/.test(expectedHead) || hash(gateBytes) !== gateSHA || gate.actual_exit !== 0 || !gate.capture_integrity_ok || !gate.complete_source_path_set_and_RAW_unchanged || gate.pre_git.HEAD !== expectedHead || gate.post_git.HEAD !== expectedHead || gate.pre_git.status_porcelain_v1_z_hex !== '' || gate.post_git.status_porcelain_v1_z_hex !== '' || !gate.argv.some(x => /(?:^|[\\/])bandit\.py$/.test(x)) || !gate.argv.includes('check')) throw Error('Successful clean exact-head full harness receipt required');
  if(currentGitBefore.branch!==gate.pre_git.branch || gate.post_git.branch!==gate.pre_git.branch) throw Error('Gate/current branch mismatch');
  const siteManifestFile = path.join(expectedSite,'site-manifest.json'), siteManifestBytes = fs.readFileSync(siteManifestFile), siteManifest = JSON.parse(siteManifestBytes);
  if(siteManifest.source_commit !== expectedHead || siteManifest.source_dirty !== false || siteManifest.lean_verified !== true) throw Error('Site HEAD/clean binding mismatch');
  if (!inside(output, base) || !inside(profile, base) || output === profile || inside(output, profile) || inside(profile, output)) throw Error('Output/profile must be distinct children of own ignored QA namespace');
  if (!inside(registryFile, expectedSite)) throw Error('Registry must belong to the specified isolated site output');
  if (fs.existsSync(output) || fs.existsSync(profile)) throw Error('Create-only output/profile already exists');
  const u = new URL(url);
  if (u.protocol !== 'http:' || !['127.0.0.1', 'localhost'].includes(u.hostname) || u.pathname !== '/chapters/online-ogd/') throw Error('Only local chapter HTTP URL allowed');
  const registryBytes = fs.readFileSync(registryFile), registry = JSON.parse(registryBytes);
  if (registry.source_commit !== expectedHead || registry.lean_verified !== true || registryFile !== fs.realpathSync(path.join(expectedSite,'books','registry.json'))) throw Error('Registry/site/HEAD mismatch');
  const sourceRel = 'BanditRLProof/OnlineCumulativePotential.lean', sourceBytes = fs.readFileSync(path.join(root, sourceRel)), source = sourceBytes.toString('utf8');
  const frozen = fs.readFileSync(path.join(root, 'docs/contracts/online-ch2-b4-finite-identity-v1/neutral-frozen-header-v1.txt'));
  if (hash(frozen) !== '92e0dcfac53595e35b68bfd8083c09640d06da809355ab02ec4eb4b007b0bd67') throw Error('Frozen production headers changed');
  if (hash(sourceBytes) !== '61c811c0b1f941ec22ac41f64e555a0e4d4d8dc32b8145ea53808dbdc0fc17da') throw Error('Reviewed core changed');
  const startToken='theorem finite_regret_identity';
  const frozenText=frozen.toString('utf8'), frozenStart=frozenText.indexOf(startToken);
  const frozenEnd=frozenText.indexOf('\nend BanditRL.OnlineCumulativePotential',frozenStart);
  const sourceStart=source.indexOf(startToken), sourceEnd=source.indexOf(' := by',sourceStart);
  if(frozenStart<0 || frozenEnd<0 || sourceStart<0 || sourceEnd<0) throw Error('Complete signature boundaries missing');
  const expectedHeader=norm(frozenText.slice(frozenStart,frozenEnd));
  if(norm(source.slice(sourceStart,sourceEnd)) !== expectedHeader) throw Error('Reviewed source and frozen exact header differ');
  const sourceRoot = fs.readFileSync(path.join(root, 'BanditRLProof.lean'), 'utf8');
  if (!/^import BanditRLProof\.OnlineCumulativePotential\s*$/m.test(sourceRoot)) throw Error('Shared production root import missing');
  const highlights = JSON.parse(fs.readFileSync(path.join(root, 'website/content/highlights.json'), 'utf8')).highlights;
  const specs = ['BanditRL.OnlineCumulativePotential.finite_regret_identity'].map(fullName => {
    const nodes = registry.nodes.filter(n => n.id === 'declaration:' + fullName);
    if (nodes.length !== 1) throw Error('Canonical registry uniqueness failure ' + fullName);
    const lesson = highlights.filter(x => x.full_name === fullName);
    if (lesson.length !== 1) throw Error('Lesson uniqueness failure ' + fullName);
    const name = fullName.split('.').pop(), line = source.split('\n').findIndex(x => x.startsWith('theorem ' + name + ' ')) + 1;
    if (!line) throw Error('Actual source declaration missing ' + fullName);
    if (!nodes[0].url.includes('#')) throw Error('Registry URL lacks anchor');
    const contexts = [...source.slice(0, source.indexOf('theorem ' + name + ' ')).matchAll(/^variable .*?(?=\n\n)/gms)];
    return { fullName, name, node: nodes[0], lesson: lesson[0], line, ambientContext: source.slice(0, source.indexOf('theorem ' + name + ' ')) };
  });
  fs.mkdirSync(output, { recursive: true });
  const report = { startedUTC: new Date().toISOString(), argv: process.argv.slice(2), url, sourceCommit: registry.source_commit,
    currentGitBefore, readerHelperSHA256:hash(fs.readFileSync(__filename)), expectedNormalizedHeaderSHA256:hash(Buffer.from(expectedHeader)), expectedHead, gateSHA256: hash(gateBytes), siteDirectory: expectedSite, siteManifestSHA256: hash(siteManifestBytes), rawHTTPBindings: [], registrySHA256: hash(registryBytes), sourceSHA256: hash(sourceBytes), frozenHeadersSHA256: hash(frozen), rootImportVerified: true,
    canonicalBindings: specs.map(s => ({ fullName: s.fullName, node: s.node, actualSourceLine: s.line })), panels: [], modules: [], images: [],
    pageErrors: [], failedRequests: [], dependencyLinkReview: [], scope: 'SIMULATED CSS-INJECTION PREVIEW ONLY, not source-HEAD acceptance. Isolated local Edge DOM/render capture only. Human pixel/source FINAL review remains separate; desktop1440/mobile390 captures; no live/native or human pixel acceptance.' };
  const write = (name, bytes) => fs.writeFileSync(path.join(output, name), bytes, { flag: 'wx' });
  let context;
  const mathjaxStartup='https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js';
  const mathjaxFontPrefix='https://cdn.jsdelivr.net/npm/mathjax@3/es5/output/chtml/fonts/woff-v2/';
  const chapterHTML=fs.readFileSync(path.join(expectedSite,'chapters/online-ogd/index.html'),'utf8');
  const declaredScripts=[...chapterHTML.matchAll(/<script\b[^>]*\bsrc=["']([^"']+)["']/gi)].map(x=>x[1]);
  if(!declaredScripts.includes(mathjaxStartup))throw Error('Expected MathJax startup is not declared by actual generated chapter HTML');
  report.externalHTTPBindings=[];
  report.externalResourceBoundary='MathJax @3 is a mutable CDN selector, not a frozen package version. Exact downloaded bytes/headers/URL/time are captured separately from generated-site bytes.';
  function allowedMathjax(target) {
    const x=new URL(target);
    if(x.protocol!=='https:'||x.origin!=='https://cdn.jsdelivr.net'||x.search||x.hash||x.username||x.password)return false;
    return x.href===mathjaxStartup||(x.href.startsWith(mathjaxFontPrefix)&&/^MathJax_[A-Za-z0-9_-]+\.woff$/.test(x.href.slice(mathjaxFontPrefix.length)));
  }
  async function externalMathjaxHTTP(target,resourceType) {
    const isStartup=target===mathjaxStartup;
    if((isStartup&&resourceType!=='script')||(!isStartup&&resourceType!=='font'))throw Error('MathJax resource type rejected '+resourceType+' '+target);
    if(!allowedMathjax(target))throw Error('External resource outside declared MathJax package '+target);
    const row={requestedURL:target,retrievedUTC:new Date().toISOString(),redirects:[],source:'external CDN; not generated site',resourceType,mutableVersionSelector:'@3',versionFrozen:false};
    const index=report.externalHTTPBindings.length+1;report.externalHTTPBindings.push(row);
    async function get(address,depth) {
      if(depth>5||!allowedMathjax(address)||(isStartup?(address!==mathjaxStartup):(address===mathjaxStartup)))throw Error('MathJax redirect rejected '+address);
      return await new Promise((resolve,reject)=>{
        const req=require('https').get(address,{headers:{'Accept-Encoding':'identity','Cache-Control':'no-cache'}},res=>{
          const headers={...res.headers},status=res.statusCode;
          if([301,302,303,307,308].includes(status)){
            const location=res.headers.location;res.resume();if(!location)return reject(Error('Redirect without Location'));
            const next=new URL(location,address).href;row.redirects.push({url:address,status,headers,location:next});get(next,depth+1).then(resolve,reject);return;
          }
          if(status!==200||(headers['content-encoding']&&headers['content-encoding']!=='identity')){res.resume();reject(Error('MathJax unexpected status/encoding '+status));return;}
          const chunks=[];res.on('data',b=>chunks.push(b));res.on('error',reject);res.on('end',()=>resolve({bytes:Buffer.concat(chunks),headers,status,url:address}));
        });req.setTimeout(60000,()=>req.destroy(Error('MathJax HTTPS timeout')));req.on('error',reject);
      });
    }
    try {
      const response=await get(target,0),contentType=response.headers['content-type'];
      if(typeof contentType!=='string'||!contentType.trim())throw Error('MathJax MIME missing');
      const mediaType=contentType.split(';')[0].trim().toLowerCase();
      if(!(isStartup?['application/javascript','text/javascript']:['font/woff','application/font-woff','application/x-font-woff']).includes(mediaType))throw Error('MathJax resource MIME rejected '+contentType);
      const file='external-http-'+index+'.raw';write(file,response.bytes);
      Object.assign(row,{resolvedURL:response.url,status:response.status,headers:response.headers,contentType,file,bytes:response.bytes.length,sha256:hash(response.bytes),resolvedVersionHeader:response.headers['x-jsd-version']??null,resolvedVersionTypeHeader:response.headers['x-jsd-version-type']??null,completedUTC:new Date().toISOString()});
      return {bytes:response.bytes,contentType};
    } catch(e){row.error=String(e);throw e;}
  }
  async function exactHTTP(target) {
    const parsed = new URL(target);
    if(parsed.origin !== u.origin) throw Error('Nonlocal raw HTTP');
    let rel = decodeURIComponent(parsed.pathname).replace(/^\/+/, '');
    if(rel.endsWith('/')) rel += 'index.html';
    const file = fs.realpathSync(path.join(expectedSite,rel));
    if(!inside(file,expectedSite)) throw Error('HTTP target escapes site');
    const local = fs.readFileSync(file);
    const remote = await new Promise((resolve,reject) => {
      require('http').get(target,{headers:{'Accept-Encoding':'identity','Cache-Control':'no-cache'}},res=>{
        if(res.statusCode!==200 || (res.headers['content-encoding'] && res.headers['content-encoding']!=='identity')) {res.resume();reject(Error('Unexpected raw HTTP status/encoding'));return;}
        const chunks=[];res.on('data',b=>chunks.push(b));res.on('end',()=>resolve(Buffer.concat(chunks)));res.on('error',reject);
      }).on('error',reject);
    });
    if(!remote.equals(local)) throw Error('HTTP body differs from generated file: '+rel);
    const record={url:target,file,sha256:hash(local),bytes:local.length,rawExactBeforeDOM:true};
    report.rawHTTPBindings.push(record);write('http-'+report.rawHTTPBindings.length+'.raw',remote);return local;
  }
  try {
    await exactHTTP(new URL('/books/registry.json',url).href);
    await exactHTTP(new URL('/site-manifest.json',url).href);
    await exactHTTP(url);
    for(const spec of specs) await exactHTTP(new URL('../../'+spec.node.url.split('#')[0],url).href);
    context = await chromium.launchPersistentContext(profile, { executablePath: 'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe', headless: true,
      serviceWorkers:'block', viewport: { width: 1440, height: 1800 }, args: ['--disable-gpu', '--disable-sync', '--disable-background-networking', '--no-first-run'] });
    await context.addInitScript(css => document.addEventListener('DOMContentLoaded',()=>{const el=document.createElement('style');el.dataset.simulatedCandidate='true';el.textContent=css;document.head.appendChild(el);}), ".source-route-status { flex-wrap: wrap; }\n.source-route-status > span,\n.source-route-summary-meta {\n  min-width: 0;\n  max-width: 100%;\n}\n\n.source-route-status > .status,\n.source-route-summary-meta > .status {\n  max-width: 100%;\n  white-space: normal;\n  overflow-wrap: anywhere;\n}\n\n");
    await context.route('**/*',async route=>{
      const type=route.request().resourceType(), target=new URL(route.request().url());
      if(target.origin!==u.origin) {
        try {const response=await externalMathjaxHTTP(target.href,type);await route.fulfill({status:200,contentType:response.contentType,body:response.bytes});}
        catch(e){report.pageErrors.push(String(e));await route.abort();}
        return;
      }
      try {
        const extension=path.extname(target.pathname).toLowerCase();
        const mime={'.html':'text/html; charset=utf-8','.css':'text/css; charset=utf-8','.js':'application/javascript; charset=utf-8','.mjs':'application/javascript; charset=utf-8','.json':'application/json; charset=utf-8','.woff':'font/woff','.woff2':'font/woff2','.ttf':'font/ttf','.otf':'font/otf','.svg':'image/svg+xml','.png':'image/png','.jpg':'image/jpeg','.jpeg':'image/jpeg','.gif':'image/gif','.webp':'image/webp','.avif':'image/avif','.ico':'image/x-icon','.txt':'text/plain; charset=utf-8','.wasm':'application/wasm'};
        const contentType=target.pathname.endsWith('/')?'text/html; charset=utf-8':mime[extension];
        if(!contentType)throw Error('Unsupported local resource MIME '+target.href+' type='+type);
        const bytes=await exactHTTP(target.href);report.rawHTTPBindings.at(-1).resourceType=type;
        await route.fulfill({status:200,contentType,body:bytes});
      }
      catch(e) { report.pageErrors.push(String(e));await route.abort(); }
    });
    const page = await context.newPage();
    page.on('pageerror', e => report.pageErrors.push(String(e)));
    page.on('requestfailed', req => report.failedRequests.push({ url: req.url(), failure: req.failure() }));
    await page.goto(url, { waitUntil: 'networkidle', timeout: 60000 });
    await page.waitForFunction(() => [...document.querySelectorAll('article.source-theorem-card')].some(el => el.textContent.includes('Corrected terminal accounting: the finite-real regret identity') && el.querySelector('mjx-container')), null, { timeout: 60000 });
    report.simulatedCSSPreview=true;
    report.allSourceCardGeometry=[];
    for(const width of [1440,390]) {
      await page.setViewportSize({width,height:1800});
      await page.locator('details.source-theorem-disclosure').evaluateAll(xs=>xs.forEach(e=>e.open=true));
      await page.waitForTimeout(200);
      const rows=await page.locator('article.source-theorem-card').evaluateAll(xs=>xs.map(e=>{const q=e.getBoundingClientRect();const parts=[...e.querySelectorAll('.source-theorem-heading,.source-theorem-heading a,.source-route-status,.source-route-status>.status')].map(p=>{const b=p.getBoundingClientRect();return {class:p.className,left:b.left,right:b.right,scrollWidth:p.scrollWidth,clientWidth:p.clientWidth};});return {title:e.querySelector('h3')?.innerText,left:q.left,right:q.right,scrollWidth:e.scrollWidth,clientWidth:e.clientWidth,parts};}));
      report.allSourceCardGeometry.push({width,rows});
      const bad=rows.filter(x=>x.left<0||x.right>width+1||x.scrollWidth>x.clientWidth+1||x.parts.some(p=>p.left<x.left-1||p.right>x.right+1||p.scrollWidth>p.clientWidth+1));
      if(bad.length)throw Error('SIMULATED preview other source-card overflow '+JSON.stringify(bad));
    }
    async function openAncestors(panel) {
      await panel.evaluate(el => { for (let p = el.parentElement; p; p = p.parentElement) if (p.tagName === 'DETAILS') p.open = true; });
    }
    async function screenshot(panel, name) {
      await openAncestors(panel);
      const shots=[];
      for(const width of [1440,390]) {
      report.screenshotAttempts ||= []; const attempt={name,width,phase:'viewport-started'};report.screenshotAttempts.push(attempt);report.activeScreenshotAttempt=attempt;
      await page.setViewportSize({width,height:1800});
      await page.waitForTimeout(100);
      const height = await panel.evaluate(el => Math.ceil(el.getBoundingClientRect().height));
      attempt.initialHeight=height;attempt.phase='measured';
      if (height > 26000) throw Error('Panel exceeds bounded screenshot height; split capture requires explicit successor script');
      await page.setViewportSize({ width, height: Math.max(1800, height + 400) });
      await panel.evaluate(el => window.scrollTo(0, window.scrollY + el.getBoundingClientRect().top - 180));
      const geometry = await panel.evaluate(el => { const q = el.getBoundingClientRect(); return { left:q.left,right:q.right,top:q.top,bottom:q.bottom,height:q.height,scrollWidth:el.scrollWidth,clientWidth:el.clientWidth,viewportWidth:innerWidth,viewportHeight:innerHeight }; });
      attempt.geometry=geometry;
      attempt.ancestors=await panel.evaluate(el=>{const out=[];for(let e=el;e;e=e.parentElement){const r=e.getBoundingClientRect(),c=getComputedStyle(e);out.push({tag:e.tagName,id:e.id,class:e.className,left:r.left,right:r.right,width:r.width,scrollWidth:e.scrollWidth,clientWidth:e.clientWidth,display:c.display,minWidth:c.minWidth,maxWidth:c.maxWidth,gridTemplateColumns:c.gridTemplateColumns,overflowX:c.overflowX});}return out;});
      attempt.descendants=await panel.evaluate(el=>{const p=el.getBoundingClientRect();return [...el.querySelectorAll('*')].map(e=>{const r=e.getBoundingClientRect(),c=getComputedStyle(e);return {tag:e.tagName,id:e.id,class:e.className?.baseVal??e.className,text:e.textContent?.slice(0,160),left:r.left,right:r.right,width:r.width,scrollWidth:e.scrollWidth,clientWidth:e.clientWidth,overflowX:c.overflowX,whiteSpace:c.whiteSpace,minWidth:c.minWidth};}).filter(x=>x.right>p.right+1||x.left<p.left-1||x.scrollWidth>x.clientWidth+1).slice(0,60);});
      if (geometry.left < 0 || geometry.right > geometry.viewportWidth + 1 || geometry.scrollWidth > geometry.clientWidth + 1 || geometry.top < 0 || geometry.bottom > geometry.viewportHeight) {
        attempt.phase='rejected-clipping';write('diagnostic-'+name+'-'+width+'-dom.html',await page.content());
        const diagnostic='diagnostic-'+name+'-'+width+'.png';await page.screenshot({path:path.join(output,diagnostic),fullPage:false});attempt.diagnosticPNG={file:diagnostic,sha256:hash(fs.readFileSync(path.join(output,diagnostic)))};
        throw Error('Clipped panel '+name+' width='+width+' geometry='+JSON.stringify(geometry));
      }
      attempt.phase='geometry-passed';
      const file = name + '-'+width+'.png'; await panel.screenshot({ path: path.join(output, file), timeout: 60000 });
      const item = { file, sha256: hash(fs.readFileSync(path.join(output, file))), geometry }; report.images.push(item); shots.push(item); } return shots;
    }
    async function data(panel) { return await panel.evaluate(el => ({ text:el.innerText, mathContainers:el.querySelectorAll('mjx-container').length,
      mathErrors:el.querySelectorAll('mjx-merror,[data-mjx-error]').length, links:[...el.querySelectorAll('a')].map(a => ({text:a.textContent,href:a.href})),
      formulas:[...el.querySelectorAll('mjx-container')].map(x => x.textContent) })); }
    function requireWords(text, words, kind) { for (const word of words) if (!norm(text).includes(word)) throw Error(kind + ' missing visible contract: ' + word); }
    const cards = page.locator('article.source-theorem-card').filter({ hasText: 'Corrected terminal accounting: the finite-real regret identity' });
    if (await cards.count() !== 1) throw Error('Expected exactly one coherent source card');
    await openAncestors(cards); const card = await data(cards);
    if (!card.mathContainers || card.mathErrors || !card.links.some(x => x.href === 'https://arxiv.org/pdf/1912.13213v10#page=142')) throw Error('Coherent card formula/pinned PDF failure');
    requireWords(card.text, ['arbitrary','real','T>0','terminal','gap','EReal','open'], 'source card');
    report.panels.push({ kind:'coherent-source-card', ...card, screenshot:await screenshot(cards,'source-card-v1') });
    for (const spec of specs) {
      const anchor = spec.node.url.split('#')[1], panel = page.locator('[id="' + anchor + '-teaching"]');
      if (await panel.count() !== 1) throw Error('Missing exact lesson ' + spec.fullName);
      await openAncestors(panel); await panel.locator('details.technical-reading').evaluate(el => { el.open = true; });
      if (await panel.locator('details.exact-lean').evaluate(el => el.open)) throw Error('Exact Lean must initially remain folded');
      const item = await data(panel);
      requireWords(item.text,[spec.fullName,spec.lesson.plain,spec.lesson.proof_idea],'lesson');
      if (!item.mathContainers || item.mathErrors) throw Error('Lesson formula rendering failure');
      requireWords(item.text,['T>0','G includes the current loss','terminal','gap','Nat.recAux','Finset.sum_range_succ','EReal','open'],spec.name);
      const exact = norm(await panel.locator('details.exact-lean pre').textContent());
      if (exact !== expectedHeader) throw Error('Folded complete header differs from frozen signature');
      const deps = spec.lesson.dependencies.map(name => { requireWords(item.text,[name],'dependency'); const node = registry.nodes.find(n => n.id === 'declaration:' + name);
        return {name,renderedLinks:item.links.filter(a => norm(a.text).includes(name)),registryURL:node ? node.url : null}; });
      report.dependencyLinkReview.push({fullName:spec.fullName,dependencies:deps,unlinkedNames:deps.filter(x => !x.renderedLinks.length).map(x => x.name),boundary:'Current renderer emits teaching dependency names as code; absence of inline hyperlinks is explicitly recorded, not asserted as passed link QA.'});
      report.panels.push({kind:'teaching',fullName:spec.fullName,...item,foldedExactStatement:exact,screenshot:await screenshot(panel,'lesson-'+spec.name+'-v1')});
    }
    const boundary = page.locator('#completion-contract');
    if (await boundary.count() !== 1) throw Error('Chapter completion contract absent');
    await boundary.locator('details').evaluate(el => { el.open = true; });
    const boundaryData = await data(boundary); requireWords(boundaryData.text,['partial','null','ACTIVE'],'chapter boundary');
    report.panels.push({kind:'chapter-boundary',...boundaryData,screenshot:await screenshot(boundary,'chapter-boundary-v1')});
    write('chapter-dom-v1.html',await page.content());
    for (const spec of specs) {
      const moduleURL = new URL('../../'+spec.node.url.split('#')[0],url).href;
      if (new URL(moduleURL).origin !== u.origin) throw Error('Nonlocal module destination');
      await page.goto(moduleURL,{waitUntil:'networkidle',timeout:60000});
      const panel = page.locator('[id="'+spec.node.url.split('#')[1]+'"]');
      if (await panel.count() !== 1) throw Error('Module declaration missing');
      await panel.evaluate(el=>{el.open=true;}); await openAncestors(panel);
      const wrap=panel.locator('[data-code-wrap]'); if(await wrap.getAttribute('aria-pressed')!=='false') throw Error('Unexpected wrap initial state'); await wrap.click();
      const code=await panel.locator('pre.lean-code').evaluate(el=>({text:el.textContent,scrollWidth:el.scrollWidth,clientWidth:el.clientWidth}));
      if(norm(code.text)!==expectedHeader||code.scrollWidth>code.clientWidth+1)throw Error('Catalog complete header absent/changed/clipped');
      const links=await panel.locator('.source-links a').evaluateAll(xs=>xs.map(x=>x.href));
      const expected=`https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/${registry.source_commit}/${sourceRel}#L${spec.line}`;
      if(!links.includes(expected))throw Error('Incorrect pinned source file/line '+spec.fullName);
      report.modules.push({fullName:spec.fullName,moduleURL,code,sourceLink:expected,contextViaPinnedWholeSource:true,
        sourceAmbientContext:spec.ambientContext,screenshot:await screenshot(panel,'catalog-'+spec.name+'-v1')});
      write('catalog-'+spec.name+'-dom-v1.html',await page.content());
    }
    // Added main theorem: full source signature, displayed proof, and exact pinned link.
    const uniqueName='BanditRL.OnlineGradientDescent.project_existsUnique';
    const uniqueNode=registry.nodes.filter(n=>n.id==='declaration:'+uniqueName);
    const uniqueLesson=highlights.filter(n=>n.full_name===uniqueName);
    if(uniqueNode.length!==1||uniqueLesson.length!==1)throw Error('Unique projection node/lesson missing or duplicated');
    const uniqueRel='BanditRLProof/OnlineGradientDescent.lean', uniqueBytes=fs.readFileSync(path.join(root,uniqueRel));
    const uniqueSource=uniqueBytes.toString('utf8'), token='theorem project_existsUnique';
    const us=uniqueSource.indexOf(token), ue=uniqueSource.indexOf(' := by',us);
    if(us<0||ue<us)throw Error('Unique projection source boundaries');
    const uniqueHeader=norm(uniqueSource.slice(us,ue));
    const uniqueLine=uniqueSource.slice(0,us).split('\n').length;
    const uniqueAnchor=uniqueNode[0].url.split('#')[1];
    await page.goto(url,{waitUntil:'networkidle',timeout:60000});
    const uniquePanel=page.locator('[id="'+uniqueAnchor+'-teaching"]');
    if(await uniquePanel.count()!==1)throw Error('Unique projection lesson missing');
    await openAncestors(uniquePanel);await uniquePanel.locator('details.technical-reading').evaluate(e=>e.open=true);
    if(await uniquePanel.locator('details.exact-lean').evaluate(e=>e.open))throw Error('Unique exact Lean not initially folded');
    await page.waitForFunction(()=>!!window.MathJax?.startup?.document?.math,null,{timeout:60000});
    const ud=await data(uniquePanel);
    requireWords(ud.text,[uniqueLesson[0].plain,uniqueLesson[0].proof_idea,'complete','closed','convex'],'unique projection lesson');
    if(!ud.mathContainers||ud.mathErrors||norm(await uniquePanel.locator('details.exact-lean pre').textContent())!==uniqueHeader)throw Error('Unique displayed math/header');
    report.panels.push({kind:'unique-projection-lesson',...ud,screenshot:await screenshot(uniquePanel,'unique-projection-lesson')});
    const projectionCard=page.locator('article.source-theorem-card').filter({hasText:'Proposition 2.11: projection decreases distance'});
    if(await projectionCard.count()!==1)throw Error('Projection source card absent');
    await openAncestors(projectionCard);const pd=await data(projectionCard);
    if(!pd.mathContainers||pd.mathErrors)throw Error('Projection source formula');
    report.panels.push({kind:'projection-source-bridge',...pd,screenshot:await screenshot(projectionCard,'projection-source-bridge')});
    await page.goto(new URL('../../'+uniqueNode[0].url.split('#')[0],url).href,{waitUntil:'networkidle',timeout:60000});
    const up=page.locator('[id="'+uniqueAnchor+'"]');await up.evaluate(e=>e.open=true);
    const uw=up.locator('[data-code-wrap]');if(await uw.getAttribute('aria-pressed')==='false')await uw.click();
    if(norm(await up.locator('pre.lean-code').textContent())!==uniqueHeader)throw Error('Unique catalog exact signature');
    const expectedUnique=`https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/${expectedHead}/${uniqueRel}#L${uniqueLine}`;
    if(!(await up.locator('.source-links a').evaluateAll(xs=>xs.map(x=>x.href))).includes(expectedUnique))throw Error('Unique pinned whole-proof source link');
    report.modules.push({fullName:uniqueName,sourceSHA256:hash(uniqueBytes),sourceAmbientContext:uniqueSource.slice(0,us),sourceLink:expectedUnique,screenshot:await screenshot(up,'unique-projection-catalog')});
    const books=JSON.parse(fs.readFileSync(path.join(root,'website/content/books.json'))).books;
    const chapters=JSON.parse(fs.readFileSync(path.join(root,'website/content/chapters.json'))).chapters;
    const owners=new Map();for(const b of books)if(b.status==='source-mapped')for(const ref of b.chapter_refs)if(ref.startsWith('teaching:')&&chapters.some(c=>'teaching:'+c.slug===ref)&&!owners.has(ref))owners.set(ref,b.id);
    for(const bookId of ['bandit','online-learning']) {
      await page.goto(new URL('/books/'+bookId+'/',url).href,{waitUntil:'networkidle',timeout:60000});
      const group=page.locator('[data-nav-group="'+bookId+'-book"]');if(await group.count()!==1)throw Error('Book ownership navigation missing');
      await group.evaluate(e=>e.open=true);
      const links=await group.locator('a.book-nav-link').evaluateAll(xs=>xs.map(x=>new URL(x.href).pathname));
      const expected=[...owners].filter(([ref,id])=>id===bookId).map(([ref])=>'/chapters/'+ref.slice(9)+'/index.html').sort();
      const normalized=links.map(x=>x.endsWith('/')?x+'index.html':x).sort();
      if(JSON.stringify(expected)!==JSON.stringify(normalized))throw Error('Book-owned navigation mismatches '+bookId);
      const main=page.locator('#main-content');
      if(await main.count()!==1)throw Error('Book main content missing');
      report.panels.push({kind:'book-main-content',bookId,screenshot:await screenshot(main,'book-'+bookId+'-content')});
      for(const width of [1440,390]) {
        const contentAttempt={name:'book-'+bookId+'-visible-content',width,phase:'viewport-started'};
        report.screenshotAttempts.push(contentAttempt);report.activeScreenshotAttempt=contentAttempt;
        await page.setViewportSize({width,height:1800});
        // Preserve the original whole-page assertion, then inspect visible content
        // under clipping ancestors. Vertical page scrolling is not horizontal clipping.
        if(await page.evaluate(()=>document.documentElement.scrollWidth>innerWidth+1))throw Error('Book page horizontal overflow');
        contentAttempt.elements=await main.evaluate(main=>[...main.querySelectorAll('article,section,li,a,h1,h2,h3,p')].filter(e=>e.checkVisibility({checkVisibilityCSS:true})&&e.getBoundingClientRect().width>0).map(e=>{
          const q=e.getBoundingClientRect(),c=getComputedStyle(e),ancestors=[];let scrollContainer=null;
          for(let a=e.parentElement;a;a=a.parentElement){const b=a.getBoundingClientRect(),cs=getComputedStyle(a);ancestors.push({tag:a.tagName,id:a.id,class:a.className,left:b.left,right:b.right,overflowX:cs.overflowX,clientWidth:a.clientWidth,scrollWidth:a.scrollWidth});if(!scrollContainer&&['auto','scroll'].includes(cs.overflowX)&&a.scrollWidth>a.clientWidth+1)scrollContainer=a;}
          const issues=[];
          // Content inside a genuine horizontal scroller is reachable by scrolling;
          // its outer scroller box must itself fit every clipping ancestor/viewport.
          const box=scrollContainer?scrollContainer.getBoundingClientRect():q;
          if(box.left<0||box.right>innerWidth+1)issues.push('viewport horizontal clipping');
          let start=scrollContainer?scrollContainer.parentElement:e.parentElement;
          for(let a=start;a;a=a.parentElement){const b=a.getBoundingClientRect(),cs=getComputedStyle(a);if(['hidden','clip','auto','scroll'].includes(cs.overflowX)&&(box.left<b.left-1||box.right>b.right+1))issues.push('ancestor horizontal clipping '+a.tagName+'#'+a.id);}
          if(!['auto','scroll'].includes(c.overflowX)&&['hidden','clip'].includes(c.overflowX)&&e.scrollWidth>e.clientWidth+1)issues.push('own concealed horizontal content');
          return {tag:e.tagName,class:e.className,text:e.innerText.slice(0,120),left:q.left,right:q.right,scrollWidth:e.scrollWidth,clientWidth:e.clientWidth,overflowX:c.overflowX,legalHorizontalScroller:scrollContainer?{tag:scrollContainer.tagName,class:scrollContainer.className,scrollWidth:scrollContainer.scrollWidth,clientWidth:scrollContainer.clientWidth}:null,ancestors,issues};
        }));
        if(!contentAttempt.elements.some(x=>x.tag==='ARTICLE'))throw Error('Book article geometry coverage empty');
        const routeSelector=bookId==='bandit'?'a.book-chapter-card, a.spine-chapter-card':'.shared-route li';
        const actualRoutes=await main.locator(routeSelector).count();
        const measuredRoutes=contentAttempt.elements.filter(x=>bookId==='bandit'?x.tag==='A'&&/(?:^|\s)(?:book-chapter-card|spine-chapter-card)(?:\s|$)/.test(x.class):x.tag==='LI'&&x.ancestors.some(a=>/(?:^|\s)shared-route(?:\s|$)/.test(a.class))).length;
        contentAttempt.routeCoverage={selector:routeSelector,actual:actualRoutes,measured:measuredRoutes};
        if(!actualRoutes||measuredRoutes!==actualRoutes)throw Error('Actual Book route/card geometry coverage incomplete');
        const clipped=contentAttempt.elements.filter(x=>x.issues.length);if(clipped.length)throw Error('Clipped Book cards/routes/content '+JSON.stringify(clipped));
        contentAttempt.phase='geometry-passed';
        const attempt={name:'book-'+bookId+'-navigation',width,phase:'viewport-started',links:[]};
        report.screenshotAttempts.push(attempt);report.activeScreenshotAttempt=attempt;
        await page.setViewportSize({width,height:1800});
        const toggle=page.locator('.sidebar-toggle');
        if(await toggle.isVisible() && await toggle.getAttribute('aria-expanded')!=='true')await toggle.click();
        await group.evaluate(e=>e.open=true);
        // A scrollable sidebar is legal. Every owned link is scrolled into view and
        // checked against both viewport and sidebar; hidden unrelated nav groups are excluded.
        const sidebar=page.locator('#site-sidebar');
        for(const link of await group.locator('a.book-nav-link').all()) {
          await link.scrollIntoViewIfNeeded();
          const geometry=await link.evaluate(e=>{const q=e.getBoundingClientRect(),s=document.querySelector('#site-sidebar').getBoundingClientRect();return {text:e.innerText,left:q.left,right:q.right,top:q.top,bottom:q.bottom,scrollWidth:e.scrollWidth,clientWidth:e.clientWidth,sidebarLeft:s.left,sidebarRight:s.right,viewportWidth:innerWidth,viewportHeight:innerHeight};});
          attempt.links.push(geometry);
          if(geometry.left<Math.max(0,geometry.sidebarLeft)-1||geometry.right>Math.min(geometry.viewportWidth,geometry.sidebarRight)+1||geometry.scrollWidth>geometry.clientWidth+1||geometry.top<0||geometry.bottom>geometry.viewportHeight)throw Error('Clipped visible Book navigation link '+JSON.stringify(geometry));
        }
        attempt.geometry=await sidebar.evaluate(e=>{const q=e.getBoundingClientRect();return {left:q.left,right:q.right,top:q.top,bottom:q.bottom,viewportWidth:innerWidth,viewportHeight:innerHeight};});
        const g=attempt.geometry;if(g.left<0||g.right>g.viewportWidth+1||g.top<0||g.bottom>g.viewportHeight+1)throw Error('Book sidebar viewport clipping');
        attempt.phase='geometry-passed';
        const file='book-'+bookId+'-navigation-'+width+'.png';await page.screenshot({path:path.join(output,file),fullPage:false});
        report.images.push({file,sha256:hash(fs.readFileSync(path.join(output,file))),geometry:attempt.geometry});
        if(await toggle.isVisible() && await toggle.getAttribute('aria-expanded')==='true')await page.locator('.sidebar-close').click();
      }
      report.panels.push({kind:'book-owned-navigation',bookId,actual:normalized,expected});write('book-'+bookId+'-dom.html',await page.content());
    }
    if(hash(fs.readFileSync(path.join(root,uniqueRel)))!==hash(uniqueBytes))throw Error('Unique source changed during capture');
    if(report.pageErrors.length||report.failedRequests.length)throw Error('Browser console/network failures');
    if(hash(fs.readFileSync(registryFile))!==report.registrySHA256||hash(fs.readFileSync(path.join(root,sourceRel)))!==report.sourceSHA256)throw Error('Inputs changed during capture');
    for(const row of report.rawHTTPBindings) if(hash(fs.readFileSync(row.file))!==row.sha256) throw Error('Generated HTTP input changed');
    for(const row of report.externalHTTPBindings) if(!row.file||hash(fs.readFileSync(path.join(output,row.file)))!==row.sha256||fs.statSync(path.join(output,row.file)).size!==row.bytes)throw Error('Captured external CDN bytes changed/incomplete');
    if(hash(fs.readFileSync(gateArg))!==gateSHA) throw Error('Gate receipt changed');
    report.currentGitAfter=gitState();
    if(JSON.stringify(report.currentGitAfter)!==JSON.stringify(currentGitBefore) || report.currentGitAfter.HEAD!==expectedHead || report.currentGitAfter.status!=='') throw Error('Current Git changed during reader capture');
    if(hash(fs.readFileSync(__filename))!==report.readerHelperSHA256) throw Error('Reader helper changed during capture');
    report.finishedUTC=new Date().toISOString();report.profilePreserved=profile;
    report.verdict='Capture complete; personal pixel review and dependency-link presentation adjudication remain separate.';
    write('reconciliation-render-v1.json',JSON.stringify(report,null,2)+'\n');
  } catch(e) { report.error=String(e);report.currentGitAfterFailure=gitState();
    if(context){try{const p=context.pages().at(-1);if(p){report.failureViewport=p.viewportSize();write('failure-dom.html',await p.content());await p.screenshot({path:path.join(output,'failure-viewport.png'),fullPage:false});report.failurePNG={file:'failure-viewport.png',sha256:hash(fs.readFileSync(path.join(output,'failure-viewport.png')))};}}catch(diagnosticError){report.diagnosticCaptureError=String(diagnosticError);}}
report.failedUTC=new Date().toISOString();write('reconciliation-render-failure-v1.json',JSON.stringify(report,null,2)+'\n');throw e; }
  finally { if(context)await context.close(); }
})().catch(e=>{console.error(e);process.exitCode=1;});
