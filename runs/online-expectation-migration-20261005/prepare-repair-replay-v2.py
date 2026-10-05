"""Version replay gates; preserve failed logs and the pre-repair preparation."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
freeze=load(run/'draft-freeze-v1.json');module=Path('BanditRLProof/OnlineExpectation.lean')
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(module.read_text(encoding='utf-8'))==tokens((run/'original-OnlineExpectation.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(module,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
assert load(run/'reader-registry-tests-v2-01-exit.json')['exit_code']==0
changes=[('verify-history-bindings-v2.py','verify-history-bindings-v3.py', [('history-binding-audit-v1.json','history-binding-audit-v2.json')]),
 ('check-scoped-diff-v2.py','check-scoped-diff-v3.py',[("'/original-' in p)","'/original-' in p or '/leaves/reader-before-boundary-repair-' in p)")]),
 ('prepare-final-reader-v1.py','prepare-final-reader-v2.py',[
  ('full-harness-v1-01','full-harness-v2-01'),('scoped-diff-v2-01','scoped-diff-v3-01'),('history-bindings-v2-01','history-bindings-v3-01'),
  ('history-binding-audit-v1.json','history-binding-audit-v2.json'),
  ('integrated-gates-overlay-v1.json','integrated-gates-overlay-v2.json'),('final-reader-packet-v1.md','final-reader-packet-v2.md'),('final-reader-inputs-v1.json','final-reader-inputs-v2.json'),
  ('no currentmathrepair or targetweakening','Reader fullharness v1failed only existing explicit parent-noncompletion wording test; preservedfailedlog/pre-repairrawJSON, same-boundary sentence repair, isolatedregistrytests and completev2replay. No mathrepair/testedit/targetweakening'),
  ("'candidate-frontier-shadow-v1']","'candidate-frontier-shadow-v1','reader-registry-tests-v2-01']")])]
rows=[]
for before,after,replacements in changes:
 src=run/before;out=run/after;assert not out.exists()
 text=src.read_text(encoding='utf-8')
 for a,b in replacements:assert a in text,(before,a);text=text.replace(a,b)
 with out.open('w',encoding='utf-8',newline='\n') as handle:handle.write(text)
 rows.append(dict(original=src.as_posix(),original_sha256=sha(src),versioned=out.as_posix(),versioned_sha256=sha(out)))
out=run/'repair-replay-preparation-v2.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as handle:
 json.dump(dict(status='reader-tests-passed-fullreplay-pending',rows=rows,all_headers_definition_proof_tokens_canary_unchanged=True,isolated_reader_tests='reader-registry-tests-v2-01',math_gates_need_no_repeat_after_reader_wording_only=True,full_harness_replay_required=True,failed_v1_preserved=True,tests_unchanged=True),handle,indent=2);handle.write('\n')
print('Reader test replay passed; versioned final/historical/scoped replay prepared, all mathematics unchanged.')
