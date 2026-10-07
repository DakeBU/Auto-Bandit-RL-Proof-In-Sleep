"""Pre-use distinction: frozen raw headers vs native whitespace-normalized fingerprints."""
from common_v2 import *
def fixed(integrated=False,body=False):
 f=__import__('common_v2').fixed(integrated,False)
 if body:
  sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
  expected=load(CONTRACT/'native-statement-fingerprints-v1.json')
  for n,h in expected.items():assert hashlib.sha256(lean_declaration_header(PUBLIC,n).encode()).hexdigest()==h,n
 return f
