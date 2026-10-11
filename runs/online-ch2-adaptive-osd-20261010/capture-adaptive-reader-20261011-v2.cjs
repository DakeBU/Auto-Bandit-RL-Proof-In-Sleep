const fs = require('fs'), path = require('path');
const { chromium } = require('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async () => {
  const [url, run, profile, registryFile, root] = process.argv.slice(2);
  const registry = JSON.parse(fs.readFileSync(registryFile, 'utf8'));
  const specs = [
    ['OnlineAdaptivePotential', 'weighted_potential_sum'],
    ['OnlineAdaptiveOSD', 'regret_bound'],
    ['OnlineAdaptiveOSD', 'source_eq4_4'],
    ['OnlineAdaptiveBenchmark', 'source_theorem4_14_infimum']
  ].map(([module, name]) => {
    const node = registry.nodes.find(n => n.id === `declaration:BanditRL.${module}.${name}`);
    if (!node) throw Error('Missing canonical node ' + name);
    const lines = fs.readFileSync(path.join(root, 'BanditRLProof', module + '.lean'), 'utf8').split('\n');
    const line = lines.findIndex(x => new RegExp(`^theorem ${name}\\b`).test(x)) + 1;
    if (!line) throw Error('Missing actual declaration line ' + name);
    return { module, name, node, line };
  });
  const reportName = 'adaptive-render-20261011-v2.json';
  if (fs.existsSync(profile) || fs.existsSync(path.join(run, reportName))) throw Error('Create-only output exists');
  const errors = [], failed = [], panels = [], modules = [], images = [];
  const context = await chromium.launchPersistentContext(profile, {
    executablePath: 'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe',
    headless: true, viewport: { width: 1440, height: 1800 },
    args: ['--disable-gpu', '--disable-sync', '--disable-background-networking', '--no-first-run']
  });
  try {
    const page = await context.newPage();
    page.on('pageerror', e => errors.push(String(e)));
    page.on('requestfailed', r => failed.push({ url: r.url(), failure: r.failure() }));
    await page.goto(url, { waitUntil: 'networkidle', timeout: 45000 });
    await page.waitForFunction(() => {
      const cards = [...document.querySelectorAll('article.source-theorem-card')];
      return cards.length === 19 && cards.slice(16).every(c => c.querySelector('mjx-container'));
    }, { timeout: 45000 });
    async function shot(panel, name) {
      const file = `adaptive-${name}-20261011-v2.png`;
      if (fs.existsSync(path.join(run, file))) throw Error('Create-only screenshot exists');
      const h = await panel.evaluate(el => Math.ceil(el.getBoundingClientRect().height));
      await page.setViewportSize({ width: 1440, height: Math.max(1800, h + 350) });
      await panel.evaluate(el => window.scrollTo(0, window.scrollY + el.getBoundingClientRect().top - 180));
      const geometry = await panel.evaluate(el => ({
        left: el.getBoundingClientRect().left, right: el.getBoundingClientRect().right,
        height: el.getBoundingClientRect().height, top: el.getBoundingClientRect().top,
        bottom: el.getBoundingClientRect().bottom, scrollWidth: el.scrollWidth,
        clientWidth: el.clientWidth, viewportWidth: innerWidth, viewportHeight: innerHeight
      }));
      if (geometry.left < 0 || geometry.right > geometry.viewportWidth + 1 ||
          geometry.scrollWidth > geometry.clientWidth + 1 || geometry.top < 140 ||
          geometry.bottom > geometry.viewportHeight - 30) throw Error('Clipped panel ' + name);
      await panel.screenshot({ path: path.join(run, file), timeout: 45000 });
      images.push(file);
      return { file, geometry };
    }
    for (let i = 16; i < 19; i++) {
      const panel = page.locator('article.source-theorem-card').nth(i);
      const data = await panel.evaluate(el => ({ text: el.innerText,
        mathContainers: el.querySelectorAll('mjx-container').length,
        mathErrors: el.querySelectorAll('mjx-merror,[data-mjx-error]').length,
        sourceLinks: [...el.querySelectorAll('a')].map(a => a.href) }));
      if (data.mathContainers !== 1 || data.mathErrors || !data.sourceLinks.some(x => x === 'https://arxiv.org/pdf/1912.13213v10#page=52')) throw Error('Card math/source failure ' + JSON.stringify(data));
      if (i === 18 && (!data.text.includes('infimum') || !data.text.includes('unattained'))) throw Error('Missing explicit benchmark repair');
      panels.push({ kind: 'source-card', index: i, ...data, ...await shot(panel, 'source-card-' + i) });
    }
    for (const spec of specs.slice(1)) {
      const panel = page.locator('#' + spec.node.url.split('#')[1] + '-teaching');
      const ancestors = panel.locator('xpath=ancestor::details');
      for (let i = 0; i < await ancestors.count(); i++) {
        const d = ancestors.nth(i);
        if (!await d.evaluate(el => el.open)) await d.locator(':scope > summary').click();
      }
      const technical = panel.locator('details.technical-reading');
      if (!await technical.evaluate(el => el.open)) await technical.locator(':scope > summary').click();
      if (await panel.locator('details.exact-lean').evaluate(el => el.open)) throw Error('Lean must remain folded');
      const data = await panel.evaluate(el => ({ text: el.innerText,
        mathContainers: el.querySelectorAll('mjx-container').length,
        mathErrors: el.querySelectorAll('mjx-merror,[data-mjx-error]').length }));
      if (!data.mathContainers || data.mathErrors) throw Error('Teaching math failure');
      panels.push({ kind: 'teaching-proof', name: spec.name, ...data, ...await shot(panel, 'teaching-' + spec.name) });
    }
    const scrollers = await page.evaluate(() => [...document.querySelectorAll('#source-guide *')]
      .filter(x => x.clientWidth && x.querySelector('mjx-container') && x.scrollWidth > x.clientWidth + 1 &&
        ['auto', 'scroll'].includes(getComputedStyle(x).overflowX)).map(x => ({ clientWidth: x.clientWidth, scrollWidth: x.scrollWidth })));
    if (scrollers.length) throw Error('Source math horizontal scrolling');
    fs.writeFileSync(path.join(run, 'adaptive-reader-dom-20261011-v2.html'), await page.content(), { flag: 'wx' });
    for (const spec of specs) {
      const moduleURL = new URL('../../' + spec.node.url.split('#')[0], url).href;
      await page.goto(moduleURL, { waitUntil: 'networkidle', timeout: 45000 });
      const panel = page.locator('#' + spec.node.url.split('#')[1]);
      if (await panel.count() !== 1) throw Error('Missing module declaration');
      if (!await panel.evaluate(el => el.open)) await panel.locator(':scope > summary').click();
      const wrap = panel.locator('[data-code-wrap]');
      if (await wrap.getAttribute('aria-pressed') !== 'false') throw Error('Wrap control initial state');
      await wrap.click();
      const code = await panel.locator('pre.lean-code').evaluate(el => ({
        text: el.textContent, scrollWidth: el.scrollWidth, clientWidth: el.clientWidth,
        whiteSpace: getComputedStyle(el).whiteSpace
      }));
      if (await wrap.getAttribute('aria-pressed') !== 'true' || code.scrollWidth > code.clientWidth + 1 ||
          !code.text.includes(spec.name)) throw Error('Exact statement overflow/missing');
      const sourceLink = await panel.locator('.source-links a').first().getAttribute('href');
      const source = new URL(sourceLink);
      if (source.hostname !== 'github.com' || source.pathname !==
          `/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/${registry.source_commit}/BanditRLProof/${spec.module}.lean` ||
          source.hash !== '#L' + spec.line) throw Error('Incorrect pinned source link');
      modules.push({ name: spec.name, moduleURL, code, sourceLink,
        actualBuiltinWrapButtonClicked: true, proofBODYViaSourceLink: true,
        ...await shot(panel, 'module-' + spec.name) });
    }
    if (errors.length || failed.length) throw Error(JSON.stringify({ errors, failed }));
    fs.writeFileSync(path.join(run, reportName), JSON.stringify({
      url, siteSourceCommit: registry.source_commit, sourceCards: 19, panels, modules,
      images, errors, failed, sourceHorizontalScrollers: scrollers, profilePreserved: profile,
      scope: 'Actual isolated local file-URI desktop rendering; source-link targets checked separately after push; original pixels require personal inspection. No live/mobile claim.'
    }, null, 2) + '\n', { flag: 'wx' });
  } finally { await context.close(); }
})().catch(e => { console.error(e); process.exitCode = 1; });
