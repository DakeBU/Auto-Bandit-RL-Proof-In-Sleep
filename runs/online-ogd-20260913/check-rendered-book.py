import json,hashlib
from pathlib import Path
root=Path('website/_site')
s=(root/'chapters/online-ogd/index.html').read_text(encoding='utf8')
b=s.split('<nav class="book-breadcrumb"',1)[1].split('</nav>',1)[0]
assert 'Online Learning Book' in b and 'Bandit Book' not in b
book=(root/'books/online-learning/index.html').read_text(encoding='utf8')
assert 'Source-mapped reading view' in book
assert 'whole-book completion' in book
bandit=(root/'books/bandit/index.html').read_text(encoding='utf8')
section=bandit.split('<section id="teaching-routes">',1)[1].split('</section>',1)[0]
assert 'chapters/online-ogd/' not in section
assert section.count('class="book-chapter-card"')==10
registry=json.loads((root/'books/registry.json').read_text(encoding='utf8'))
nodes=[n for n in registry['nodes'] if n['id'].startswith('declaration:BanditRL.OnlineGradientDescent.')]
assert len(nodes)==16
assert all(n['books']==['online-learning'] and n['status']=='compiled' for n in nodes)
manifest=json.loads((root/'site-manifest.json').read_text(encoding='utf8'))
assert manifest['lean_verified'] and manifest['placeholder_count']==0
result={'ok':True,'ogd_nodes':len(nodes),'membership':'online-learning','breadcrumb':'Online Learning Book','bandit_teaching_cards':10,'source_commit':manifest['source_commit'],'source_dirty':manifest['source_dirty'],'lean_verified':True,'checks':'canonical registry identities, rendered breadcrumb, scoped book status, no foreign Bandit Book membership'}
Path('runs/online-ogd-20260913/book-render-check.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
print(result)
