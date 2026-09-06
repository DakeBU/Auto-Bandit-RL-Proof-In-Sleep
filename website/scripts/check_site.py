"""Check anonymous website links, declaration anchors, statuses and metadata."""
from pathlib import Path
from html.parser import HTMLParser
from urllib.parse import urlsplit, unquote
import json
import re
from functools import lru_cache

ROOT = Path(__file__).resolve().parents[2]
SITE = ROOT / 'docs'

@lru_cache(maxsize=None)
def resolve_target(parent, path):
    target = (parent / unquote(path)).resolve()
    return target / 'index.html' if target.is_dir() else target

class Page(HTMLParser):
    def __init__(self, text):
        super().__init__()
        self.ids, self.links = set(), []
        self.feed(text)
    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if 'id' in attrs:
            self.ids.add(attrs['id'])
        for key in ('href', 'src'):
            if attrs.get(key):
                self.links.append(attrs[key])

def main():
    manifest = json.loads((SITE / 'site-manifest.json').read_text(encoding='utf-8'))
    assert manifest['anonymous_review']
    assert manifest['author_count'] == manifest['contributor_count'] == 0
    assert 'source_commit' not in manifest
    assert not (SITE / 'contributors/index.html').exists()
    pages, errors = {}, []
    for path in SITE.rglob('*.html'):
        text = path.read_text(encoding='utf-8')
        pages[path.resolve()] = Page(text)
        if re.search(r'class="contributor-card|href="[^"]*contributors/index.html', text):
            errors.append(f'Authorship UI: {path.relative_to(SITE)}')
        if 'name="referrer" content="no-referrer"' not in text:
            errors.append(f'Missing referrer policy: {path.relative_to(SITE)}')
    checked = 0
    for path, page in pages.items():
        for link in page.links:
            url = urlsplit(link)
            if url.scheme in {'http', 'https', 'mailto', 'data'} or url.netloc:
                continue
            if url.scheme:
                errors.append(f'Unresolved URL: {path.relative_to(SITE)}: {link}')
                continue
            target = resolve_target(path.parent, url.path) if url.path else path
            if not target.is_file() or not target.is_relative_to(SITE.resolve()):
                errors.append(f'Missing local link: {path.relative_to(SITE)}: {link}')
            elif url.fragment and target in pages and unquote(url.fragment) not in pages[target].ids:
                errors.append(f'Missing anchor: {path.relative_to(SITE)}: {link}')
            checked += 1
    search = json.loads((SITE / 'search-index.json').read_text(encoding='utf-8'))
    assert len(search) == manifest['declaration_count']
    assert manifest['placeholder_count'] == 0
    if errors:
        print('\n'.join(errors[:40]))
        raise SystemExit(f'{len(errors)} failures')
    print(f'PASS: {len(pages)} HTML pages; {checked} local links/anchors; {len(search)} declarations; no authorship UI.')

if __name__ == '__main__':
    main()
