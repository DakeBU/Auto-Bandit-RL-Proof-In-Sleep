const fs = require('fs'), path = require('path'), crypto = require('crypto');
const { chromium } = require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
const hash = b => crypto.createHash('sha256').update(b).digest('hex');
const norm = s => s.replace(/[\u200b\u00ad]/g, '').replace(/\s+/g, ' ').trim();
const inside = (p, base) => { const rel = path.relative(base, p); return rel && !rel.startsWith('..') && !path.isAbsolute(rel); };
(async () => {
  const [url, outputArg, profileArg, registryArg, rootArg, siteArg, gateArg, gateSHA, expectedHead, specArg, specSHA] = process.argv.slice(2);
  if (process.argv.slice(2).length !== 11) throw Error('Expected URL OUTPUT PROFILE REGISTRY ROOT SITE COMBINED_GATE_RECEIPT GATE_SHA256 HEAD SPEC SPEC_SHA256');
  const root = fs.realpathSync(rootArg), base = path.join(root, 'tmp', 'online-support-reader-tool-preparation-20261012');
  const output = path.resolve(outputArg), profile = path.resolve(profileArg), registryFile = fs.realpathSync(registryArg);
  const expectedSite = fs.realpathSync(siteArg);
  const gitState = () => { const run = (...args) => require('child_process').execFileSync('git',['-c','core.longpaths=true',...args],{cwd:root,encoding:'utf8'}).trim(); return {HEAD:run('rev-parse','HEAD'),branch:run('branch','--show-current'),status:run('status','--porcelain')}; };
  const currentGitBefore = gitState();
  const specBytes=fs.readFileSync(specArg),inputSpec=JSON.parse(specBytes);
  if(hash(specBytes)!==specSHA||inputSpec.ready_for_execution!==true||inputSpec.head!==expectedHead||inputSpec.branch!==currentGitBefore.branch)throw Error('Executable pinned support spec required');
  if(hash(fs.readFileSync(__filename))!==inputSpec.browser_helper_sha256)throw Error('Reader helper SHA binding');
  for(const [p,sha] of Object.entries(inputSpec.bindings))if(hash(fs.readFileSync(path.join(root,p)))!==sha)throw Error('Input RAW changed '+p);
  for(const role of ['full_harness','site_build_verified','site_check']){
    const b=inputSpec.evidence_required[role];if(!b||hash(fs.readFileSync(b.path))!==b.sha256)throw Error('Missing gate binding '+role);
    const g=JSON.parse(fs.readFileSync(b.path));if(g.actual_exit!==0||g.capture_integrity_ok!==true||g.complete_source_path_set_and_RAW_unchanged!==true||g.pre_git.HEAD!==expectedHead||g.post_git.HEAD!==expectedHead||g.pre_git.status_porcelain_v1_z_hex!==''||g.post_git.status_porcelain_v1_z_hex!=='')throw Error('Unsuccessful exact-head gate '+role);
  }
  if(path.resolve(inputSpec.evidence_required.full_harness.path)!==path.resolve(gateArg)||inputSpec.evidence_required.full_harness.sha256!==gateSHA||path.resolve(inputSpec.evidence_required.isolated_site)!==expectedSite)throw Error('Exact same harness/site bindings required');
  for(const role of ['site_build_verified','site_check']){const g=JSON.parse(fs.readFileSync(inputSpec.evidence_required[role].path));const at=g.argv.indexOf('--output');if(at<0||path.resolve(root,g.argv[at+1])!==expectedSite)throw Error('Gate output path mismatch '+role);}
  const fallback=inputSpec.evidence_required.browser_unavailable_observation;
  if(!fallback||hash(fs.readFileSync(fallback.path))!==fallback.sha256)throw Error('Documented actual browser capability observation required for isolated fallback');
  const structural=inputSpec.evidence_required.structural_result;
  if(!structural||hash(fs.readFileSync(structural.path))!==structural.sha256)throw Error('Pinned passed structural check required');
  const sr=JSON.parse(fs.readFileSync(structural.path));if(sr.actual_exit!==0||sr.pre_git.HEAD!==expectedHead||sr.post_git.HEAD!==expectedHead)throw Error('Structural receipt mismatch');

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
    pageErrors: [], failedRequests: [], dependencyLinkReview: [], scope: 'Isolated local Edge DOM/render capture only. Human pixel/source FINAL review remains separate; desktop1440/mobile390 captures; no live/native or human pixel acceptance.' };
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
    if(!rel||rel.endsWith('/')) rel += 'index.html';
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

    const bookNav=await page.locator('[data-nav-group="books"] > .nav-group-links > a').evaluateAll(xs=>xs.map(x=>new URL(x.href).pathname).filter(x=>/\/books\/[^/]+\/(?:index.html)?$/.test(x)).sort());
    const expectedBookNav=['bandit','reinforcement-learning','online-learning','conformal-prediction'].map(x=>'/books/'+x+'/index.html').sort();
    if(JSON.stringify(bookNav.map(x=>x.endsWith('/')?x+'index.html':x))!==JSON.stringify(expectedBookNav))throw Error('Four Book navigation links must remain exact');
    report.fourBookNavigation=bookNav;
    // Actual final QA: no injected CSS. Every current source card is measured.
    report.allSourceCardGeometry=[];
    for(const width of [1440,390]) {
      await page.setViewportSize({width,height:1800});
      await page.locator('details.source-theorem-disclosure').evaluateAll(xs=>xs.forEach(e=>e.open=true));
      await page.waitForTimeout(200);
      const rows=await page.locator('article.source-theorem-card').evaluateAll(xs=>xs.map(e=>{const q=e.getBoundingClientRect();const parts=[...e.querySelectorAll('.source-theorem-heading,.source-theorem-heading a,.source-route-status,.source-route-status>.status')].map(p=>{const b=p.getBoundingClientRect();return {class:p.className,left:b.left,right:b.right,scrollWidth:p.scrollWidth,clientWidth:p.clientWidth};});return {title:e.querySelector('h3')?.innerText,left:q.left,right:q.right,scrollWidth:e.scrollWidth,clientWidth:e.clientWidth,parts};}));
      report.allSourceCardGeometry.push({width,rows});
      if(rows.length!==25)throw Error('Expected preserved24 plus one reviewed support source card');
      const bad=rows.filter(x=>x.left<0||x.right>width+1||x.scrollWidth>x.clientWidth+1||x.parts.some(p=>p.left<x.left-1||p.right>x.right+1||p.scrollWidth>p.clientWidth+1));
      if(bad.length)throw Error('Actual source-card geometry overflow '+JSON.stringify(bad));
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
    async function verifyWrapControl(panel, expectedStatement, label) {
      const button=panel.locator('[data-code-wrap]'),block=panel.locator('pre.lean-code');
      if(await button.count()!==1||await block.count()!==1)throw Error('Wrap control/block uniqueness '+label);
      async function snapshot(phase) {
        const value=await block.evaluate(e=>({text:e.textContent,whiteSpace:getComputedStyle(e).whiteSpace,classes:e.className}));
        const aria=await button.getAttribute('aria-pressed');
        if(!['pre','pre-wrap','break-spaces'].includes(value.whiteSpace))throw Error('Unexpected Lean whitespace mode '+label+' '+value.whiteSpace);
        const wrapped=value.whiteSpace!=='pre';
        if(aria!==String(wrapped))throw Error('Wrap aria/computed inconsistency '+label+' '+phase);
        if(norm(value.text)!==expectedStatement)throw Error('Wrap changed complete header '+label+' '+phase);
        return {phase,aria,wrapped,...value};
      }
      const initial=await snapshot('initial-responsive'),states=[initial];
      await button.click();const first=await snapshot('first-toggle');states.push(first);
      if(first.wrapped===initial.wrapped||first.text!==initial.text)throw Error('First wrap toggle failed/content changed '+label);
      await button.click();const second=await snapshot('second-toggle');states.push(second);
      if(second.wrapped!==initial.wrapped||second.text!==initial.text)throw Error('Reverse wrap toggle failed/content changed '+label);
      if(!second.wrapped){await button.click();states.push(await snapshot('restore-wrapped'));}
      const final=states.at(-1);if(!final.wrapped||final.text!==initial.text)throw Error('Final wrapped state/content mismatch '+label);
      report.wrapControlChecks ||= [];report.wrapControlChecks.push({label,states});
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
    const boundaryData = await data(boundary);
    requireWords(boundaryData.text,['partial','null','seven required forward containers','six future mathematical claims remain open','not completion of all Chapter 2'],'chapter boundary');
    if(!/\bGoal remains active\b/i.test(norm(boundaryData.text)))throw Error('Chapter boundary must explicitly retain Goal remains active');
    report.chapterBoundarySemanticCheck={partial:true,denominatorNull:true,requiredForwardContainers:7,futureClaimsOpen:6,goalActive:true,wholeChapterIncomplete:true};
    report.panels.push({kind:'chapter-boundary',...boundaryData,screenshot:await screenshot(boundary,'chapter-boundary-v1')});
    write('chapter-dom-v1.html',await page.content());
    for (const spec of specs) {
      const moduleURL = new URL('../../'+spec.node.url.split('#')[0],url).href;
      if (new URL(moduleURL).origin !== u.origin) throw Error('Nonlocal module destination');
      await page.goto(moduleURL,{waitUntil:'networkidle',timeout:60000});
      const panel = page.locator('[id="'+spec.node.url.split('#')[1]+'"]');
      if (await panel.count() !== 1) throw Error('Module declaration missing');
      await panel.evaluate(el=>{el.open=true;}); await openAncestors(panel);
      await verifyWrapControl(panel,expectedHeader,spec.fullName);
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
    await verifyWrapControl(up,uniqueHeader,uniqueName);
    if(norm(await up.locator('pre.lean-code').textContent())!==uniqueHeader)throw Error('Unique catalog exact signature');
    const expectedUnique=`https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/${expectedHead}/${uniqueRel}#L${uniqueLine}`;
    if(!(await up.locator('.source-links a').evaluateAll(xs=>xs.map(x=>x.href))).includes(expectedUnique))throw Error('Unique pinned whole-proof source link');
    report.modules.push({fullName:uniqueName,sourceSHA256:hash(uniqueBytes),sourceAmbientContext:uniqueSource.slice(0,us),sourceLink:expectedUnique,screenshot:await screenshot(up,'unique-projection-catalog')});
    // New conditional strong-convex growth leaf; existing B4/OGD checks above retained.
    const growthName='BanditRL.OnlineConvex.stronglyConvex_minimum_growth';
    const growthRel='BanditRLProof/OnlineStrongConvexMinimum.lean';
    const growthBytes=fs.readFileSync(path.join(root,growthRel)),growthSource=growthBytes.toString('utf8');
    if(hash(growthBytes)!=='55b37c648437e231f1b967cdc9cfa4102ce1bea6efde3ed81b23884604f89317')throw Error('Reviewed growth production bytes changed');
    const growthFrozen=fs.readFileSync(path.join(root,'docs/contracts/online-ch2-b4-strong-convex-growth-v1/neutral-frozen-header-v1.txt'));
    if(hash(growthFrozen)!=='ded5adebef211f810552abbc4eced856dd9fff59f268989e9c1ff5a4ecd3d590')throw Error('Frozen growth declaration changed');
    if(!/^import BanditRLProof\.OnlineStrongConvexMinimum\s*$/m.test(sourceRoot))throw Error('Growth shared-root import absent');
    const growthToken='theorem stronglyConvex_minimum_growth',gs=growthSource.indexOf(growthToken),gf=growthFrozen.toString('utf8'),gfs=gf.indexOf(growthToken),gfe=gf.indexOf('\nend BanditRL.OnlineConvex',gfs);
    const bodyMarker=gs<0?null:/\s*:=\s*by/.exec(growthSource.slice(gs));
    if(gs<0||gfs<0||gfe<0||!bodyMarker)throw Error('Growth full header boundaries missing');
    const growthHeader=norm(gf.slice(gfs,gfe));
    if(norm(growthSource.slice(gs,gs+bodyMarker.index))!==growthHeader)throw Error('Growth actual/frozen complete header mismatch');
    const growthLine=growthSource.slice(0,gs).split('\n').length;
    const growthNodes=registry.nodes.filter(x=>x.id==='declaration:'+growthName),growthLessons=highlights.filter(x=>x.full_name===growthName);
    if(growthNodes.length!==1||growthLessons.length!==1||growthNodes[0].status!=='compiled')throw Error('Growth unique compiled node/lesson missing');
    const growthNode=growthNodes[0],growthLesson=growthLessons[0],growthAnchor=growthNode.url.split('#')[1];
    if(!growthAnchor)throw Error('Growth declaration anchor missing');
    const expectedGrowth=`https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/${expectedHead}/${growthRel}#L${growthLine}`;
    await page.goto(url,{waitUntil:'networkidle',timeout:60000});
    const growthCard=page.locator('article.source-theorem-card').filter({hasText:'Derived B4 dependency: quadratic growth at a supplied minimum'});
    if(await growthCard.count()!==1)throw Error('Growth coherent source card missing/duplicated');
    await openAncestors(growthCard);
    await growthCard.locator('mjx-container').first().waitFor({state:'visible',timeout:60000});
    const gc=await data(growthCard);
    if(!gc.mathContainers||gc.mathErrors||!gc.links.some(x=>x.href==='https://arxiv.org/pdf/1912.13213v10#page=46'))throw Error('Growth source/formula/PDF binding');
    requireWords(gc.text,['SourceProper','effectiveDomain','lambda/2','0<a<1','finite','Supply p','B1-B7','7.47/15.31','open'],'growth source contract');
    report.panels.push({kind:'growth-source-card',...gc,screenshot:await screenshot(growthCard,'growth-source-card')});
    const growthPanel=page.locator('[id="'+growthAnchor+'-teaching"]');
    if(await growthPanel.count()!==1)throw Error('Growth lesson missing/duplicated');
    await openAncestors(growthPanel);await growthPanel.locator('details.technical-reading').evaluate(e=>e.open=true);
    if(await growthPanel.locator('details.exact-lean').evaluate(e=>e.open))throw Error('Growth exact header must initially remain folded');
    const gd=await data(growthPanel);
    requireWords(gd.text,[growthName,growthLesson.plain,growthLesson.proof_idea,'lambda/2','finite','conditional','existence or uniqueness','B1-B7','7.47/15.31','open'],'growth teaching');
    if(!gd.mathContainers||gd.mathErrors||norm(await growthPanel.locator('details.exact-lean pre').textContent())!==growthHeader)throw Error('Growth lesson formula/full-header mismatch');
    for(const dependency of growthLesson.dependencies)requireWords(gd.text,[dependency],'growth dependency');
    if(!gd.links.some(x=>x.href===expectedGrowth))throw Error('Growth lesson full-proof source link missing/wrong');
    report.panels.push({kind:'growth-teaching',...gd,foldedExactHeader:growthHeader,screenshot:await screenshot(growthPanel,'growth-lesson')});
    write('growth-chapter-dom.html',await page.content());
    await page.goto(new URL('../../'+growthNode.url.split('#')[0],url).href,{waitUntil:'networkidle',timeout:60000});
    const growthCatalog=page.locator('[id="'+growthAnchor+'"]');
    if(await growthCatalog.count()!==1)throw Error('Growth catalog declaration missing');
    await growthCatalog.evaluate(e=>e.open=true);await openAncestors(growthCatalog);
    await verifyWrapControl(growthCatalog,growthHeader,growthName);
    const growthCode=await growthCatalog.locator('pre.lean-code').evaluate(e=>({text:e.textContent,scrollWidth:e.scrollWidth,clientWidth:e.clientWidth}));
    if(norm(growthCode.text)!==growthHeader||growthCode.scrollWidth>growthCode.clientWidth+1)throw Error('Growth catalog exact header clipping/mismatch');
    if(!(await growthCatalog.locator('.source-links a').evaluateAll(xs=>xs.map(x=>x.href))).includes(expectedGrowth))throw Error('Growth catalog pinned complete-proof link wrong');
    report.modules.push({fullName:growthName,sourceSHA256:hash(growthBytes),frozenHeaderSHA256:hash(growthFrozen),sourceLink:expectedGrowth,code:growthCode,screenshot:await screenshot(growthCatalog,'growth-catalog')});
    write('growth-catalog-dom.html',await page.content());
    {
    // New conditional strong-convex support leaf; existing B4/OGD checks above retained.
    const supportName='BanditRL.OnlineConvex.stronglyConvex_support_growth';
    const supportRel='BanditRLProof/OnlineStrongConvexSupport.lean';
    const supportBytes=fs.readFileSync(path.join(root,supportRel)),supportSource=supportBytes.toString('utf8');
    if(hash(supportBytes)!=='f3a475b58661a4efefdb33b9715852a08008940bd437e1cb3ad64862b772d1e5')throw Error('Reviewed support production bytes changed');
    const supportFrozen=fs.readFileSync(path.join(root,'docs/contracts/online-ch2-b4-strong-convex-support-v1/neutral-frozen-header-v1.txt'));
    if(hash(supportFrozen)!=='23e26732b827730a343a1dd758a19a39d4f8d4af06941330f9636272d3114d57')throw Error('Frozen support declaration changed');
    if(!/^import BanditRLProof\.OnlineStrongConvexSupport\s*$/m.test(sourceRoot))throw Error('Support shared-root import absent');
    const supportToken='theorem stronglyConvex_support_growth',gs=supportSource.indexOf(supportToken),gf=supportFrozen.toString('utf8'),gfs=gf.indexOf(supportToken),gfe=gf.indexOf('\nend BanditRL.OnlineConvex',gfs);
    const bodyMarker=gs<0?null:/\s*:=\s*by/.exec(supportSource.slice(gs));
    if(gs<0||gfs<0||gfe<0||!bodyMarker)throw Error('Support full header boundaries missing');
    const supportHeader=norm(gf.slice(gfs,gfe));
    if(norm(supportSource.slice(gs,gs+bodyMarker.index))!==supportHeader)throw Error('Support actual/frozen complete header mismatch');
    const supportLine=supportSource.slice(0,gs).split('\n').length;
    const supportNodes=registry.nodes.filter(x=>x.id==='declaration:'+supportName),supportLessons=highlights.filter(x=>x.full_name===supportName);
    if(supportNodes.length!==1||supportLessons.length!==1||supportNodes[0].status!=='compiled')throw Error('Support unique compiled node/lesson missing');
    const supportNode=supportNodes[0],supportLesson=supportLessons[0],supportAnchor=supportNode.url.split('#')[1];
    if(!supportAnchor)throw Error('Support declaration anchor missing');
    await exactHTTP(new URL('../../'+supportNode.url.split('#')[0],url).href);
    const expectedSupport=`https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/${expectedHead}/${supportRel}#L${supportLine}`;
    await page.goto(url,{waitUntil:'networkidle',timeout:60000});
    const supportCard=page.locator('article.source-theorem-card').filter({hasText:'Lemma4.2 forward dependency: quadratic lower bound at a supplied support'});
    if(await supportCard.count()!==1)throw Error('Support coherent source card missing/duplicated');
    await openAncestors(supportCard);
    await supportCard.locator('mjx-container').first().waitFor({state:'visible',timeout:60000});
    const gc=await data(supportCard);
    if(!gc.mathContainers||gc.mathErrors||!gc.links.some(x=>x.href==='https://arxiv.org/pdf/1912.13213v10#page=46'))throw Error('Support source/formula/PDF binding');
    requireWords(gc.text,['SourceProper','effectiveDomain','lambda/2','0<a<1','finite','Supply p','B1-B7','7.47/15.31','OPEN'],'support source contract');
    report.panels.push({kind:'support-source-card',...gc,screenshot:await screenshot(supportCard,'support-source-card')});
    const supportPanel=page.locator('[id="'+supportAnchor+'-teaching"]');
    if(await supportPanel.count()!==1)throw Error('Support lesson missing/duplicated');
    await openAncestors(supportPanel);await supportPanel.locator('details.technical-reading').evaluate(e=>e.open=true);
    if(await supportPanel.locator('details.exact-lean').evaluate(e=>e.open))throw Error('Support exact header must initially remain folded');
    const gd=await data(supportPanel);
    requireWords(gd.text,[supportName,supportLesson.plain,supportLesson.proof_idea,'lambda/2','finite','B1-B7','7.47/15.31'],'support teaching');
    if(!gd.mathContainers||gd.mathErrors||norm(await supportPanel.locator('details.exact-lean pre').textContent())!==supportHeader)throw Error('Support lesson formula/full-header mismatch');
    for(const dependency of supportLesson.dependencies)requireWords(gd.text,[dependency],'support dependency');
    if(!gd.links.some(x=>x.href===expectedSupport))throw Error('Support lesson full-proof source link missing/wrong');
    report.panels.push({kind:'support-teaching',...gd,foldedExactHeader:supportHeader,screenshot:await screenshot(supportPanel,'support-lesson')});
    write('support-chapter-dom.html',await page.content());
    await page.goto(new URL('../../'+supportNode.url.split('#')[0],url).href,{waitUntil:'networkidle',timeout:60000});
    const supportCatalog=page.locator('[id="'+supportAnchor+'"]');
    if(await supportCatalog.count()!==1)throw Error('Support catalog declaration missing');
    await supportCatalog.evaluate(e=>e.open=true);await openAncestors(supportCatalog);
    await verifyWrapControl(supportCatalog,supportHeader,supportName);
    const supportCode=await supportCatalog.locator('pre.lean-code').evaluate(e=>({text:e.textContent,scrollWidth:e.scrollWidth,clientWidth:e.clientWidth}));
    if(norm(supportCode.text)!==supportHeader||supportCode.scrollWidth>supportCode.clientWidth+1)throw Error('Support catalog exact header clipping/mismatch');
    if(!(await supportCatalog.locator('.source-links a').evaluateAll(xs=>xs.map(x=>x.href))).includes(expectedSupport))throw Error('Support catalog pinned complete-proof link wrong');
    report.modules.push({fullName:supportName,sourceSHA256:hash(supportBytes),frozenHeaderSHA256:hash(supportFrozen),sourceLink:expectedSupport,code:supportCode,screenshot:await screenshot(supportCatalog,'support-catalog')});
    write('support-catalog-dom.html',await page.content());
    }
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
      const retained=mainRender.retained_parent_bindings.find(x=>x.consumer===name);
      if(retained){
        if(!lesson.dependencies.includes(retained.parent))throw Error('Retained real parent dependency '+name);
        const call=fs.readFileSync(path.join(root,retained.consumer_source),'utf8').split(/\r?\n/)[retained.actual_call_line-1];
        if(!call.includes(':= affine_support_of_domain_interior '))throw Error('Actual unchanged parent application '+name);
        const parentNodes=registry.nodes.filter(x=>x.id==='declaration:'+retained.parent),parentLessons=highlights.filter(x=>x.full_name===retained.parent);
        if(parentNodes.length!==1||parentLessons.length!==1||parentLessons[0].chapter!=='online-minorant')throw Error('One retained canonical parent '+name);
        const parentNode=parentNodes[0],parentURL=new URL('/chapters/online-minorant/',url).href;
        await exactHTTP(parentURL);await page.goto(parentURL,{waitUntil:'networkidle',timeout:60000});
        const parentPanel=await exactOne('[id="'+parentNode.url.split('#')[1]+'-teaching"]','retained parent lesson');await openRecordedAncestors(parentPanel,name+' shared parent');
        const actualLink=parentPanel.locator('.source-links a').filter({hasText:'Open in the declaration catalog'});
        if(await actualLink.count()!==1)throw Error('Actual canonical parent catalog link '+name);
        const href=await actualLink.evaluate(e=>e.href),expectedHref=new URL('/'+parentNode.url,url).href;
        if(href!==expectedHref)throw Error('Canonical parent link target '+name);
        const parentLessonShots=await strictPanelShots(parentPanel,stem+'-retained-parent-lesson');
        await exactHTTP(href.split('#')[0]);await actualLink.click();await page.waitForURL(expectedHref,{timeout:60000});
        const parentCatalog=await exactOne('[id="'+parentNode.url.split('#')[1]+'"]','clicked canonical parent');await openRecordedAncestors(parentCatalog,name+' clicked parent');
        const openedByNavigation=await parentCatalog.evaluate(e=>e.open);if(!openedByNavigation)await parentCatalog.locator(':scope > summary').click();
        const parentEntry=mainRender.chapters.flatMap(x=>x.lessons).find(x=>x.highlight.full_name===retained.parent);if(!parentEntry)throw Error('Reviewed parent source entry absent');
        await verifyWrapControl(parentCatalog,norm(parentEntry.declaration.statement),retained.parent);
        const parentCatalogShots=await strictPanelShots(parentCatalog,stem+'-retained-parent-catalog');write(stem+'-retained-parent-dom.html',await page.content());
        report.correctedMain.retainedParentChecks ||= [];
        report.correctedMain.retainedParentChecks.push({consumer:name,parent:retained.parent,actualSourceCall:{file:retained.consumer_source,line:retained.actual_call_line,text:call},consumerDependencyVisible:true,consumerInlineParentLinks:value.links.filter(x=>norm(x.text).includes(retained.parent)),inlineLinkBoundary:'Current renderer lists dependency names as code; these are not falsely described as clickable inline links. The real canonical parent lesson-to-catalog link is clicked and its target captured.',clickedCanonicalParentLink:href,openedByNavigation,parentLessonShots,parentCatalogShots});
      }

    }
    for(const chapter of mainRender.chapters){
      const chapterURL=new URL('/chapters/'+chapter.slug+'/',url).href;
      await exactHTTP(chapterURL);await page.goto(chapterURL,{waitUntil:'networkidle',timeout:60000});
      const orientation=await exactOne('#orientation',chapter.slug+' orientation');const orientValue=await data(orientation);requireWords(orientValue.text,[chapter.chapter.audience,...chapter.chapter.learning_goals],chapter.slug+' orientation');report.panels.push({kind:'corrected-main-orientation',chapter:chapter.slug,...orientValue,screenshot:await strictPanelShots(orientation,'main-'+chapter.slug+'-orientation')});
      if(chapter.chapter.completion_definition){const completion=await exactOne('#completion-contract',chapter.slug+' completion');const disclosure=completion.locator('details.maintainer-contract');if(await disclosure.count()!==1)throw Error('Unique maintainer disclosure '+chapter.slug);const initialOpen=await disclosure.evaluate(e=>e.open);if(initialOpen)throw Error('Completion initially unfolded '+chapter.slug);await disclosure.locator(':scope > summary').click();const cv=await data(completion);requireWords(cv.text,[chapter.chapter.completion_definition,...chapter.chapter.completion_blockers],chapter.slug+' exact completion');report.panels.push({kind:'corrected-main-completion',chapter:chapter.slug,initialOpen,...cv,screenshot:await strictPanelShots(completion,'main-'+chapter.slug+'-completion')});}
      const visibleNames=await page.locator('#teaching-notes > article.theorem-panel .declaration-name code').allTextContents();const expectedVisible=chapter.reading.teaching_route.filter(n=>highlights.find(x=>x.full_name===n)?.source_match!=='extension');if(JSON.stringify(visibleNames.map(norm))!==JSON.stringify(expectedVisible))throw Error('Exact current visible teaching-route order '+chapter.slug);
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
    if(report.correctedMain.retainedParentChecks?.length!==2)throw Error('Both retained real-parent cases required');
    report.correctedMain.allRequiredCasesCaptured=true;

    if(hash(fs.readFileSync(path.join(root,growthRel)))!==hash(growthBytes)||hash(fs.readFileSync(path.join(root,'docs/contracts/online-ch2-b4-strong-convex-growth-v1/neutral-frozen-header-v1.txt')))!==hash(growthFrozen))throw Error('Growth source/header changed during capture');
    if(hash(fs.readFileSync(path.join(root,uniqueRel)))!==hash(uniqueBytes))throw Error('Unique source changed during capture');
    if(report.pageErrors.length||report.failedRequests.length)throw Error('Browser console/network failures');
    if(hash(fs.readFileSync(registryFile))!==report.registrySHA256||hash(fs.readFileSync(path.join(root,sourceRel)))!==report.sourceSHA256)throw Error('Inputs changed during capture');
    for(const row of report.rawHTTPBindings) if(hash(fs.readFileSync(row.file))!==row.sha256) throw Error('Generated HTTP input changed');
    for(const row of report.externalHTTPBindings) if(!row.file||hash(fs.readFileSync(path.join(output,row.file)))!==row.sha256||fs.statSync(path.join(output,row.file)).size!==row.bytes)throw Error('Captured external CDN bytes changed/incomplete');
    if(hash(fs.readFileSync(gateArg))!==gateSHA) throw Error('Gate receipt changed');
    report.currentGitAfter=gitState();
    if(JSON.stringify(report.currentGitAfter)!==JSON.stringify(currentGitBefore) || report.currentGitAfter.HEAD!==expectedHead || report.currentGitAfter.status!=='') throw Error('Current Git changed during reader capture');
    if(hash(fs.readFileSync(__filename))!==report.readerHelperSHA256) throw Error('Reader helper changed during capture');
    for(const [p,sha] of Object.entries(inputSpec.bindings))if(hash(fs.readFileSync(path.join(root,p)))!==sha)throw Error('Input changed during capture '+p);
    if(hash(fs.readFileSync(specArg))!==specSHA)throw Error('Spec changed during capture');
    report.inputSpecSHA256=specSHA;
    report.finishedUTC=new Date().toISOString();report.profilePreserved=profile;
    report.verdict='All programmed support/corrected-main/home/Math2 DOM and real screenshot cases complete; independent personal pixel/source adjudication remains separate.';
    write('reconciliation-render-v1.json',JSON.stringify(report,null,2)+'\n');
  } catch(e) { report.error=String(e);report.currentGitAfterFailure=gitState();
    if(context){try{const p=context.pages().at(-1);if(p){report.failureViewport=p.viewportSize();write('failure-dom.html',await p.content());await p.screenshot({path:path.join(output,'failure-viewport.png'),fullPage:false});report.failurePNG={file:'failure-viewport.png',sha256:hash(fs.readFileSync(path.join(output,'failure-viewport.png')))};}}catch(diagnosticError){report.diagnosticCaptureError=String(diagnosticError);}}
report.failedUTC=new Date().toISOString();write('reconciliation-render-failure-v1.json',JSON.stringify(report,null,2)+'\n');throw e; }
  finally { if(context)await context.close(); }
})().catch(e=>{console.error(e);process.exitCode=1;});
