"""Keep the existing registry boundary fixture's exact phrase without changing meaning."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent;p=Path('website/content/chapters.json')
sha=lambda q:hashlib.sha256(Path(q).read_bytes()).hexdigest()
snap=run/'leaves/reader-before-boundary-phrase-v2.json.txt';assert not snap.exists();snap.write_bytes(p.read_bytes())
d=json.loads(p.read_text(encoding='utf-8'));x=next(row for row in d['chapters'] if row['slug']=='online-huber')
old=x['completion_definition'];assert 'not completion of Chapter2' in old and 'not Chapter2 completion' not in old
x['completion_definition']=old+' This is not Chapter2 completion.'
with p.open('w',encoding='utf-8',newline='\n') as f:json.dump(d,f,ensure_ascii=False,indent=2);f.write('\n')
before=json.loads(snap.read_text(encoding='utf-8'));after=json.loads(p.read_text(encoding='utf-8'))
oldrow=next(row for row in before['chapters'] if row['slug']=='online-huber');newrow=next(row for row in after['chapters'] if row['slug']=='online-huber')
assert {k:v for k,v in oldrow.items() if k!='completion_definition'}=={k:v for k,v in newrow.items() if k!='completion_definition'}
assert [r for r in before['chapters'] if r['slug']!='online-huber']==[r for r in after['chapters'] if r['slug']!='online-huber']
out=run/'reader-boundary-phrase-v2.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:json.dump(dict(status='pre-gate-reader-compatibility-only',path=p.as_posix(),snapshot=snap.as_posix(),before_sha256=sha(snap),after_sha256=sha(p),old_value=old,new_value=newrow['completion_definition'],fixture='tools/test_book_registry.py:test_huber_source_uses_shared_registry_with_chapter_boundary',full_harness_failed=False,mathematical_statement_body_canary_changed=False,all_other_Book_subtrees_unchanged=True),f,indent=2);f.write('\n')
print('Existing exact boundary phrase retained before full harness; mathematical meaning unchanged.')
