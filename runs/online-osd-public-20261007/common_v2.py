"""Effective complete raw-header metadata adapter; never compare distinct hash domains."""
from common_v1 import *
def fixed(integrated=False):
 f=load(RUN/'draft-freeze-v2.json');allowed=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json'] if integrated else []
 for p,h in f['fixed_files'].items():
  if p not in allowed:assert sha(p)==h,p
 sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
 text=PUBLIC.read_text(encoding='utf-8')
 for n,h in f['raw_headers'].items():
  m=re.search(r'(?m)^theorem '+re.escape(n)+r'\b[\s\S]*?(?= := by)',text);assert m,n
  raw=m.group(0).strip();native=lean_declaration_header(PUBLIC,n)
  assert hashlib.sha256(raw.encode()).hexdigest()==h,('complete raw',n)
  assert ' '.join(raw.split())==native,n
  assert hashlib.sha256(native.encode()).hexdigest()==f['native_headers'][n],('native',n)
 return f
