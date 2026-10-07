"""Check raw exact headers AND native normalized fingerprints separately."""
from common_v1 import *
def fixed(integrated=False,body=False):
 f=__import__('common_v1').fixed(integrated,False)
 if body:
  sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
  text=PUBLIC.read_text(encoding='utf-8')
  native=load(CONTRACT/'native-statement-fingerprints-v1.json')
  for n,h in f['headers'].items():
   m=re.search(r'(?m)^theorem '+re.escape(n)+r'\b[\s\S]*?(?= :=)',text);assert m,n
   assert hashlib.sha256(m.group(0).strip().encode()).hexdigest()==h,('raw header',n)
   assert hashlib.sha256(lean_declaration_header(PUBLIC,n).encode()).hexdigest()==native[n],('native normalized',n)
 return f
