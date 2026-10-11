const fs = require('fs'), path = require('path'), crypto = require('crypto');
const { chromium } = require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
const hash = b => crypto.createHash('sha256').update(b).digest('hex');
const norm = s => s.replace(/[\u200b\u00ad]/g, '').replace(/\s+/g, ' ').trim();
const inside = (p, base) => { const rel = path.relative(base, p); return rel && !rel.startsWith('..') && !path.isAbsolute(rel); };
(async () => {
  const [url, outputArg, profileArg, registryArg, rootArg, siteArg, gateArg, gateSHA, expectedHead] = process.argv.slice(2);
  if (process.argv.slice(2).length !== 9) throw Error('Expected URL OUTPUT PROFILE REGISTRY ROOT SITE COMBINED_GATE_RECEIPT GATE_SHA256 HEAD');
  const root = fs.realpathSync(rootArg), base = path.join(root, 'tmp', 'online-ch2-b4-finite-identity-reader-qa-20261011');
  const output = path.resolve(outputArg), profile = path.resolve(profileArg), registryFile = fs.realpathSync(registryArg);
  const expectedSite = fs.realpathSync(siteArg);
  if (!inside(expectedSite, path.join(root,'tmp'))) throw Error('Site must be isolated under root/tmp');
  const gateBytes = fs.readFileSync(gateArg), gate = JSON.parse(gateBytes);
  if (!/^[a-f0-9]{40}$/.test(expectedHead) || hash(gateBytes) !== gateSHA || gate.actual_exit !== 0 || !gate.capture_integrity_ok || !gate.complete_source_path_set_and_RAW_unchanged || gate.pre_git.HEAD !== expectedHead || gate.post_git.HEAD !== expectedHead || gate.pre_git.status_porcelain_v1_z_hex !== '' || gate.post_git.status_porcelain_v1_z_hex !== '' || !gate.argv.some(x => /(?:^|[\\/])bandit\.py$/.test(x)) || !gate.argv.includes('check')) throw Error('Successful clean exact-head full harness receipt required');
  const siteManifestFile = path.join(expectedSite,'site-manifest.json'), siteManifestBytes = fs.readFileSync(siteManifestFile), siteManifest = JSON.parse(siteManifestBytes);
  if(siteManifest.source_commit !== expectedHead || siteManifest.source_dirty !== false) throw Error('Site HEAD/clean binding mismatch');
  if (!inside(output, base) || !inside(profile, base) || output === profile || inside(output, profile) || inside(profile, output)) throw Error('Output/profile must be distinct children of own ignored QA namespace');
  if (!inside(registryFile, expectedSite)) throw Error('Registry must belong to the specified isolated site output');
  if (fs.existsSync(output) || fs.existsSync(profile)) throw Error('Create-only output/profile already exists');
  const u = new URL(url);
  if (u.protocol !== 'http:' || !['127.0.0.1', 'localhost'].includes(u.hostname) || u.pathname !== '/chapters/online-ogd/') throw Error('Only local chapter HTTP URL allowed');
  const registryBytes = fs.readFileSync(registryFile), registry = JSON.parse(registryBytes);
  if (registry.source_commit !== expectedHead || registryFile !== fs.realpathSync(path.join(expectedSite,'books','registry.json'))) throw Error('Registry/site/HEAD mismatch');
  const sourceRel = 'BanditRLProof/OnlineCumulativePotential.lean', sourceBytes = fs.readFileSync(path.join(root, sourceRel)), source = sourceBytes.toString('utf8');
  const frozen = fs.readFileSync(path.join(root, 'docs/contracts/online-ch2-b4-finite-identity-v1/neutral-frozen-header-v1.txt'));
  if (hash(frozen) !== '92e0dcfac53595e35b68bfd8083c09640d06da809355ab02ec4eb4b007b0bd67') throw Error('Frozen production headers changed');
  if (hash(sourceBytes) !== '61c811c0b1f941ec22ac41f64e555a0e4d4d8dc32b8145ea53808dbdc0fc17da') throw Error('Reviewed core changed');
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
    expectedHead, gateSHA256: hash(gateBytes), siteDirectory: expectedSite, siteManifestSHA256: hash(siteManifestBytes), rawHTTPBindings: [], registrySHA256: hash(registryBytes), sourceSHA256: hash(sourceBytes), frozenHeadersSHA256: hash(frozen), rootImportVerified: true,
    canonicalBindings: specs.map(s => ({ fullName: s.fullName, node: s.node, actualSourceLine: s.line })), panels: [], modules: [], images: [],
    pageErrors: [], failedRequests: [], dependencyLinkReview: [], scope: 'Isolated local Edge DOM/render capture only. Human pixel/source FINAL review remains separate; no live/mobile/native acceptance.' };
  const write = (name, bytes) => fs.writeFileSync(path.join(output, name), bytes, { flag: 'wx' });
  let context;
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
      viewport: { width: 1440, height: 1800 }, args: ['--disable-gpu', '--disable-sync', '--disable-background-networking', '--no-first-run'] });
    await context.route('**/*',async route=>{
      if(route.request().resourceType() !== 'document') return route.continue();
      try { const bytes=await exactHTTP(route.request().url()); await route.fulfill({status:200,contentType:'text/html; charset=utf-8',body:bytes}); }
      catch(e) { report.pageErrors.push(String(e));await route.abort(); }
    });
    const page = await context.newPage();
    page.on('pageerror', e => report.pageErrors.push(String(e)));
    page.on('requestfailed', req => report.failedRequests.push({ url: req.url(), failure: req.failure() }));
    await page.goto(url, { waitUntil: 'networkidle', timeout: 60000 });
    await page.waitForFunction(() => [...document.querySelectorAll('article.source-theorem-card')].some(el => el.textContent.includes('Corrected terminal accounting: the finite-real regret identity') && el.querySelector('mjx-container')), null, { timeout: 60000 });
    async function openAncestors(panel) {
      await panel.evaluate(el => { for (let p = el.parentElement; p; p = p.parentElement) if (p.tagName === 'DETAILS') p.open = true; });
    }
    async function screenshot(panel, name) {
      await openAncestors(panel);
      const height = await panel.evaluate(el => Math.ceil(el.getBoundingClientRect().height));
      if (height > 26000) throw Error('Panel exceeds bounded screenshot height; split capture requires explicit successor script');
      await page.setViewportSize({ width: 1440, height: Math.max(1800, height + 400) });
      await panel.evaluate(el => window.scrollTo(0, window.scrollY + el.getBoundingClientRect().top - 180));
      const geometry = await panel.evaluate(el => { const q = el.getBoundingClientRect(); return { left:q.left,right:q.right,top:q.top,bottom:q.bottom,height:q.height,scrollWidth:el.scrollWidth,clientWidth:el.clientWidth,viewportWidth:innerWidth,viewportHeight:innerHeight }; });
      if (geometry.left < 0 || geometry.right > geometry.viewportWidth + 1 || geometry.scrollWidth > geometry.clientWidth + 1 || geometry.top < 0 || geometry.bottom > geometry.viewportHeight) throw Error('Clipped panel ' + name);
      const file = name + '.png'; await panel.screenshot({ path: path.join(output, file), timeout: 60000 });
      const item = { file, sha256: hash(fs.readFileSync(path.join(output, file))), geometry }; report.images.push(item); return item;
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
      if (!exact.includes(spec.name)) throw Error('Wrong folded exact theorem');
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
      if(!code.text.includes(spec.name)||code.scrollWidth>code.clientWidth+1)throw Error('Exact code absent/clipped');
      const links=await panel.locator('.source-links a').evaluateAll(xs=>xs.map(x=>x.href));
      const expected=`https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/${registry.source_commit}/${sourceRel}#L${spec.line}`;
      if(!links.includes(expected))throw Error('Incorrect pinned source file/line '+spec.fullName);
      report.modules.push({fullName:spec.fullName,moduleURL,code,sourceLink:expected,contextViaPinnedWholeSource:true,
        sourceAmbientContext:spec.ambientContext,screenshot:await screenshot(panel,'catalog-'+spec.name+'-v1')});
      write('catalog-'+spec.name+'-dom-v1.html',await page.content());
    }
    if(report.pageErrors.length||report.failedRequests.length)throw Error('Browser console/network failures');
    if(hash(fs.readFileSync(registryFile))!==report.registrySHA256||hash(fs.readFileSync(path.join(root,sourceRel)))!==report.sourceSHA256)throw Error('Inputs changed during capture');
    for(const row of report.rawHTTPBindings) if(hash(fs.readFileSync(row.file))!==row.sha256) throw Error('Generated HTTP input changed');
    if(hash(fs.readFileSync(gateArg))!==gateSHA) throw Error('Gate receipt changed');
    report.finishedUTC=new Date().toISOString();report.profilePreserved=profile;
    report.verdict='Capture complete; personal pixel review and dependency-link presentation adjudication remain separate.';
    write('finite-identity-render-v1.json',JSON.stringify(report,null,2)+'\n');
  } catch(e) { report.error=String(e);report.failedUTC=new Date().toISOString();write('finite-identity-render-failure-v1.json',JSON.stringify(report,null,2)+'\n');throw e; }
  finally { if(context)await context.close(); }
})().catch(e=>{console.error(e);process.exitCode=1;});
