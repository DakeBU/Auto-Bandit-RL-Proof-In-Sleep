"""Build the frozen, anonymous BanditRLlib reading site (standard library only).

This entry point always removes project authorship UI and original repository
navigation. Library development belongs on main, not on this review snapshot.
"""
from pathlib import Path
import argparse
import hashlib
import gzip
import html
import json
import posixpath
import re
import sys
import build_core as site

ROOT = Path(__file__).resolve().parents[2]
PAGE_WRITER = site.write_page
LAYOUT = site.layout
OUTPUT = ROOT / 'docs'

def safe_source(file):
    path = ROOT / file
    return (not Path(file).is_absolute() and '..' not in Path(file).parts
            and path.is_file() and '.git' not in Path(file).parts
            and 'docs' not in Path(file).parts)

def source_target(file, fragment=''):
    return 'source/' + file + '.html' + fragment if safe_source(file) else 'source-access/index.html'

def rewrite_urls(text, page):
    def source(match):
        file, fragment = match.group(1), match.group(2) or ''
        return site.href_from(page, source_target(file, fragment))
    text = re.sub(r'review:repository/blob/[^/]+/([^\s"<>?#]+)(#[A-Za-z0-9_-]+)?', source, text)
    text = re.sub(r'review:repository[^\s"<>\')]*', site.href_from(page, 'source-access/index.html'), text)
    text = re.sub(r'review:site/([^\s"<>\')]*)', lambda m: site.href_from(page, m[1] or 'index.html'), text)
    return text.replace('review:site', site.href_from(page, 'index.html'))

def anonymous_page(output, page, content):
    if page == 'proof-graph-laboratory/index.html':
        content = re.sub(r'<section id="execution-boundary">.*?</section>',
            '<section id="execution-boundary"><h2>Snapshot boundary</h2><p>This page preserves previously reported prototype observations, not a new experiment on the current library. Operational benchmark runners are not included here. The included declaration dependency exporter can be run after building Lean; the static site cannot run proofs, ZDDs, or MIP solvers.</p></section>', content, flags=re.S)
    content = re.sub(r'https://Anonymous\.github\.io/[^\s"<>]+', 'review:repository', content)
    content = re.sub(r'<section id="(?:contributors|how-to-contribute)"[^>]*>.*?</section>', '', content, flags=re.S)
    content = re.sub(r'<a\b[^>]*href="[^"]*(?:contributors/index.html|#contributors|#how-to-contribute)"[^>]*>.*?</a>', '', content, flags=re.S)
    content = re.sub(r'<(?:meta[^>]*property="og:url"|link[^>]*rel="canonical")[^>]*>', '', content)
    content = content.replace('<meta charset="utf-8">', '<meta charset="utf-8"><meta name="referrer" content="no-referrer"><meta name="robots" content="noindex,nofollow">')
    content = content.replace('GitHub repository', 'Review source').replace('Autoformalization in public', 'Anonymous review snapshot')
    content = content.replace('Contribute a Lemma', 'Review scope').replace('03 · Contributor', '03 · Reviewer')
    content = content.replace('Contribute one lemma', 'Inspect the review scope').replace('Follow the contribution contract', 'Read the snapshot boundaries')
    content = content.replace('and contribute one reviewable lemma at a time.', 'and inspect the scope of the frozen review snapshot.')
    content = content.replace('Local experimental workspace', 'Static review edition')
    content = content.replace('href="graph.json"', 'href="graph.json.gz"').replace('download the full graph artifact', 'download the full graph artifact (gzip)')
    content = content.replace('community/index.html#machine-contract', 'community/index.html')
    # These legacy published cross-links predate the current map's anchors.
    content = re.sub(r'(implementation-map/index.html)#(?:delayed-sapo-d10-d12-gap-ordering-audit|neurips-2025-delayed-bobw-central-endpoints|neurips-2025-succinct-lower-bound-geometry-audit|neurips-2025-stochastic-gradient-bandit-mechanism-audit|neurips-2025-sgb-phase-transition-followon|target-drift-v2-controlled-evaluation)', r'\1', content)
    content = content.replace('Lean gate passed before this site build; local proof declarations are shown as compiled.',
                            'Frozen Lean sources match the successful CI build; compiled labels are limited to these declarations.')
    # The frozen release is an appendix, not a contribution or online service.
    content = content.replace('python3 tools/bandit.py check', 'lake build &amp;&amp; lake build Tests')
    content = content.replace('py -3 tools/bandit.py check', 'lake build &amp;&amp; lake build Tests')
    content = content.replace('Generated from current sources at', 'Frozen review snapshot generated at')
    content = re.sub(r'\b[a-f0-9]{40}\b', 'review-snapshot', content)
    PAGE_WRITER(output, page, rewrite_urls(content, page))

def simple_page(page, title, body):
    def build(output, *args):
        verified, generated_at = args[-2:]
        site.write_page(output, page, LAYOUT(page, title,
            '<section class="hero"><p class="eyebrow">Anonymous review snapshot</p><h1>' + title + '</h1>' + body + '</section>',
            [], 'installation' if page.startswith('installation') else '', verified, generated_at))
    return build

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-verified', action='store_true', help='retain compiled labels only for the unchanged CI-verified Lean snapshot')
    parser.add_argument('--output', type=Path, default=OUTPUT)
    args = parser.parse_args()
    if args.lean_verified:
        record = json.loads((ROOT / 'snapshot-integrity.json').read_text(encoding='utf-8'))
        for file, digest in record['lean_files'].items():
            if hashlib.sha256((ROOT / file).read_bytes().replace(b'\r\n', b'\n')).hexdigest() != digest:
                raise SystemExit('Lean input differs from the verified frozen snapshot: ' + file)
        actual = {p.relative_to(ROOT).as_posix() for base in ['BanditRLProof', 'Tests'] for p in (ROOT / base).rglob('*.lean')}
        if not actual.issubset(record['lean_files']):
            raise SystemExit('Unverified new Lean source in frozen snapshot')
    site.write_page = anonymous_page
    site.git_source_state = lambda: ('snapshot', False)
    site.build_contributors = lambda *args: None
    site.build_public_repository_readme = lambda *args: None
    site.render_current_snapshot = lambda page, modules, declarations, chapters, results, verified: (
        '<section id="current-snapshot"><h2>Frozen review evidence</h2><p>'
        + str(len(modules)) + ' modules and ' + str(len(declarations))
        + ' declarations are indexed from the unchanged Lean snapshot. '
        + 'The teaching pages distinguish compiled, partial, planned, and blocked results. '
        + 'A compiled chapter status is limited to its stated scope, not the entire textbook.</p></section>')
    site.build_installation = simple_page('installation/index.html', 'Reproduce the frozen library', '''
<p>Download the anonymous repository archive and extract it. Install <a href="https://lean-lang.org/install/">Lean through Elan</a>. The checked-in toolchain and dependency manifest pin Lean and Mathlib.</p>
<pre class="command-block" tabindex="0"><code>lake exe cache get
lake build
lake build Tests
python3 website/scripts/build_site.py --lean-verified
python3 website/scripts/check_site.py
python3 -m http.server 8000 --directory docs</code></pre>
<p>The build flag checks the frozen Lean file inventory before retaining compiled labels; it does not run Lean itself. Run the two Lean build targets above to independently check the proofs. This release includes the complete Lean library and tests, the reading-site generator, and the declaration dependency exporter. Operational harness logs and author records are not included.</p>
<p>Future library development remains on the non-anonymous main branch. This review branch is frozen and must not be merged back into main.</p>''')
    site.build_community = simple_page('community/index.html', 'Review scope', '<p>This is a read-only review snapshot. Project authorship and contributor records are omitted. Please send review feedback through the submission system, not through a public repository issue.</p>')
    site.build_workflow = simple_page('workflow/index.html', 'ABRL development method', '''<p>ABRL organizes agent-assisted construction around an explicit mathematical target. Human authors review the intended statement; agents retrieve library results, construct intermediate proofs, and diagnose failures; Lean checks the resulting terms. Only accepted, checked results enter the reusable library.</p><ol><li>Fix the algorithm, assumptions, objective, and quantifiers.</li><li>Decompose the argument into typed intermediate results and retrieve existing lemmas.</li><li>Construct and check candidate proofs while preserving the target.</li><li>Review whether the checked statement establishes the intended theorem.</li><li>Integrate accepted results and update their dependencies and reading pages.</li></ol><p>The hierarchical harness is the current default; parallel master–worker exploration is experimental. No matched comparison establishes a winning harness. Operational execution logs are excluded from this anonymous library snapshot.</p>''')
    site.build_attribution = simple_page('attribution/index.html', 'Sources and licenses', '''<p>Lean 4 and Mathlib provide the formal foundation. Their upstream licenses apply to dependencies; no external library source is vendored in this snapshot. Original artifact code uses the <a href="../LICENSE">MIT license</a>. See <a href="../NOTICE.md">third-party notices</a>.</p><p>The reading-site organization was inspired by <a href="https://github.com/shosonoda/lean-ridgelet">Sho Sonoda’s Lean-Ridgelet repository</a>, its <a href="https://shosonoda.github.io/lean-ridgelet/blueprint/html-multi/overview/">Blueprint website</a>, and <a href="https://statsmllib.github.io/">StatsMLlib</a>. No code or template was copied from these sites; no participation, endorsement, or maintenance by their authors is implied.</p><p>Textbook and paper citations remain on the relevant mathematical pages. These bibliographic authors are not project contributors.</p>''')
    site.build_research_ide = simple_page('ide/index.html', 'Static review edition', '<p>This snapshot provides exact Lean declarations, teaching chapters, and dependency navigation. It does not provide an online Lean compiler or a lemma-submission service. Run Lean locally using the Installation page.</p>')
    site.build_source_access = simple_page('source-access/index.html', 'Review source', '<p>Exact Lean source is bundled in this anonymous release. Use the source link on each declaration to inspect its file and line. Download the anonymous repository for local compilation. Historical issue links, development logs, and author-identifying services are deliberately excluded.</p><p><a href="../installation/index.html">Build instructions</a> · <a href="../source/index.html">Browse bundled source</a></p>')
    sys.argv = [sys.argv[0], '--output', str(args.output)] + (['--lean-verified'] if args.lean_verified else [])
    site.main()
    output = args.output.resolve()
    # Keep all generated data local, including source URLs used by graph cards.
    for path in output.rglob('*'):
        if path.is_file() and path.suffix in {'.json', '.js', '.md', '.mmd', '.svg'}:
            content = path.read_text(encoding='utf-8')
            content = rewrite_urls(content, 'lean-graph/index.html' if path.suffix == '.json' else path.relative_to(output).as_posix())
            path.write_text(content, encoding='utf-8', newline='\n')
    manifest_path = output / 'site-manifest.json'
    manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
    manifest.pop('source_commit', None)
    manifest['anonymous_review'] = True
    manifest['development_branch'] = 'main (not this frozen review branch)'
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8')
    # The anonymous host limits individual files to 8 MB. The UI already uses
    # small independent shards; compress only the optional complete download.
    full_graph = output / 'lean-graph/graph.json'
    packed = gzip.compress(full_graph.read_bytes(), mtime=0)
    if len(packed) >= 8_000_000:
        raise SystemExit('Full graph download exceeds anonymous host file limit')
    full_graph.with_suffix('.json.gz').write_bytes(packed)
    full_graph.unlink()
    source_files = [p for p in ROOT.rglob('*') if p.is_file() and not any(
        part in {'.git', '.lake', '__pycache__', 'docs', '_site'} for part in p.relative_to(ROOT).parts)
        and p.suffix in {'.lean', '.json', '.py', '.md', '.mmd'}]
    listing = []
    for path in sorted(source_files):
        rel = path.relative_to(ROOT).as_posix()
        text = path.read_text(encoding='utf-8')
        page = 'source/' + rel + '.html'
        code = '\n'.join('<span id="L%d">%d %s</span>' % (i, i, html.escape(line))
                         for i, line in enumerate(text.splitlines(), 1))
        site.write_page(output, page, LAYOUT(page, rel, '<h1>' + html.escape(rel) + '</h1><pre class="lean-code" tabindex="0"><code>' + code + '</code></pre>', [], '', args.lean_verified, manifest['generated_at']))
        listing.append('<li><a href="' + html.escape(rel) + '.html">' + html.escape(rel) + '</a></li>')
    site.write_page(output, 'source/index.html', LAYOUT('source/index.html', 'Bundled source', '<h1>Bundled source</h1><ul>' + ''.join(listing) + '</ul>', [], '', args.lean_verified, manifest['generated_at']))
    print('Anonymous website generated; project authors and contributor UI omitted.')

if __name__ == '__main__':
    main()
