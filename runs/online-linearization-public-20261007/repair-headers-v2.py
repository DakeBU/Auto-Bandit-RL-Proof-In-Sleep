"""Repair a draft extractor; no change to any actual terminal or Lean body."""
from common_v1 import *
fixed();old=fixed();t=PUBLIC.read_text(encoding='utf-8')
headers={m.group(1):m.group(0).strip() for m in re.finditer(r'(?m)^theorem (\w+)\b[\s\S]*?(?=\s+:=\s+by\b)',t)}
assert len(headers)==18 and set(headers)==set(old['native_headers'])
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
nativehash={n:hashlib.sha256(lean_declaration_header(PUBLIC,n).encode()).hexdigest() for n in headers};assert nativehash==old['native_headers']
rawhash={n:hashlib.sha256(h.encode()).hexdigest() for n,h in headers.items()}
for n,h in headers.items():assert ' :\n' in h or ' :' in h;assert h.endswith(lean_declaration_header(PUBLIC,n).split(' : ')[-1]) or h.count(':')>=2
write(CONTRACT/'headers-v2.json',headers);write(CONTRACT/'raw-statement-fingerprints-v2.json',rawhash);write(CONTRACT/'native-statement-fingerprints-v2.json',nativehash)
v2=dict(old);v2.update(contract_version=2,raw_headers=rawhash,native_headers=nativehash,actual_Lean_targets_unchanged=True,extractor_repair='Body delimiter := by, not nested E := E; original v1 truncated draft metadata retained')
write(RUN/'draft-freeze-v2.json',v2)
manifest=load(CONTRACT/'contract-manifest-v1.json');manifest.update(contract_version=2,raw_headers=rawhash,native_headers=nativehash,headers_file='headers-v2.json',previous_draft_metadata_only_repair=True,Lean_statement_change=False)
write(CONTRACT/'contract-manifest-v2.json',manifest)
write(CONTRACT/'contract-v2.md',(CONTRACT/'contract-v1.md').read_text(encoding='utf-8')+'\nVersion2 draft metadata repair: the initial raw extractor stopped at named implicit argument E := E. Original v1 truncated raw headers and failed retrieval attempt are retained. Current headers-v2 contain ALL18 complete actual multiline headers, checked against unchanged native full hashes and unchanged full module. No actual statement, hypothesis, algorithm, source or theorem body changed; not a new mathematical target or proof weakening. The v2 metadata is the current review terminal.\n')
write(RUN/'draft-extractor-repair-v2.json',dict(stage='draft-repair',failure='prepare-neutral-retrieval-v1.py ValueError(outputHistory_last) after successful declaration searches; no neutral kernel invocation yet',root_cause='Regex stopped at nested named argument E := E instead of body',old_raw_metadata_retained=True,version=2,actual_native_hashes_unchanged=True,actual_public_canary_unchanged=True,new_proofs=0,chapter_complete=False,goal_complete=False))
common=(RUN/'common_v1.py').read_text(encoding='utf-8').replace('draft-freeze-v1.json','draft-freeze-v2.json').replace('headers-v1.json','headers-v2.json')
write(RUN/'common_v2.py',common)
prepare=(RUN/'prepare-neutral-retrieval-v1.py').read_text(encoding='utf-8').replace('from common_v1 import *','from common_v2 import *').replace('-v1','-v2')
write(RUN/'prepare-neutral-retrieval-v2.py',prepare)
native('draft-v2-event','lifecycle-event','--session',TASK,'--event','draft','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=2,extractor_metadata_repair=True,actual_Lean_statements_unchanged=True,new_proofs=0,chapter_complete=False,goal_complete=False)))
print('Version2 repaired complete draft headers; same18 full native hashes and all source/proof bytes unchanged.')
