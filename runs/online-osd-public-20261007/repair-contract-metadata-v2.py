"""Preserve malformed raw-header draft; freeze complete unchanged actual targets."""
from common_v1 import *
f=load(RUN/'draft-freeze-v1.json');assert load(RUN/'prepare-contract-v1-01-exit.json')['exit_code']!=0
for p,h in f['fixed_files'].items():assert sha(p)==h,p
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
text=PUBLIC.read_text(encoding='utf-8');headers={};native={}
for n in f['raw_headers']:
 m=re.search(r'(?m)^theorem '+re.escape(n)+r'\b[\s\S]*?(?= := by)',text);assert m,n
 h=m.group(0).strip();actual=lean_declaration_header(PUBLIC,n)
 assert ' '.join(h.split())==actual,n
 assert len(h)>len(load(CONTRACT/'headers.json')[n]),n
 headers[n]=h;native[n]=hashlib.sha256(actual.encode()).hexdigest();assert native[n]==f['native_headers'][n],n
raw={n:hashlib.sha256(t.encode()).hexdigest() for n,t in headers.items()}
write(CONTRACT/'headers-v2.json',headers);write(CONTRACT/'raw-statement-fingerprints-v2.json',raw)
write(RUN/'draft-freeze-v2.json',dict(**{k:v for k,v in f.items() if k!='raw_headers'},raw_headers=raw,raw_metadata_version=2,prior_draft=(RUN/'draft-freeze-v1.json').as_posix(),prior_draft_sha256=sha(RUN/'draft-freeze-v1.json'),actual_mathematical_targets_unchanged=True))
write(CONTRACT/'contract-manifest-overlay-v2.json',dict(prior=(CONTRACT/'contract-manifest-v1.json').as_posix(),prior_sha256=sha(CONTRACT/'contract-manifest-v1.json'),mathematical_contract_version=1,raw_metadata_version=2,headers='headers-v2.json',raw_fingerprints='raw-statement-fingerprints-v2.json',native_fingerprints='native-statement-fingerprints-v1.json',actual_context='actual-context-v1.txt',unchanged_public_module_sha256=sha(PUBLIC),separate_metadata_repair_review_required=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
write(RUN/'metadata-repairs-v2.json',dict(status='actual defects detected before semantic review',M1=dict(kind='raw header extractor defect',defect='Naive lookahead stopped at binder E := E, truncating all15 raw headers.',repair='Version2 extracts through actual := by and independently requires whitespace-normalized equality to pinned native top-level parser.',all15_actual_native_fingerprints_unchanged=True,actual_PUBLIC_and_CANARY_unchanged=True,original_draft_headers_raw_fingerprints_and_scripts_preserved=True,mathematical_target_change=False,separate_source_repair_verdict_required=True),M2=dict(kind='source image rendering runtime failure',actual_failed_command='prepare-contract-v1-01',actual_exception='Default Python lacks pypdfium2',repair='Use configured bundled Python already confirmed to contain pypdfium2/PIL/pypdf; no install or Lean toolchain/dependency change.',bundled_Python='C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe',rendering_pending=True),compiled=False,source_package_accepted=False))
print('All15 complete raw headers now independently equal native full types; actual source/definitions/targets/native hashes unchanged; originals retained, separate review pending.')
