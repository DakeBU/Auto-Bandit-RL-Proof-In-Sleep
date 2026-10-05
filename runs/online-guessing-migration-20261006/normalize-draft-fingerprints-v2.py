"""Preserve v1 and use the native normalized fingerprint for planned headers."""
from pathlib import Path
import hashlib,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import normalize_statement
run=Path(__file__).parent;contract=Path('docs/contracts/online-guessing-migration-v1')
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x):
 assert not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
headers=load(contract/'headers.json');changed=[]
for n,row in headers.items():
 if not row['state'].startswith('planned'):continue
 original=row['statement'];normalized=normalize_statement(original)
 changed.append(dict(name=n,old_raw_header_hash=row['statement_hash'],normalized_native_header_hash=hashlib.sha256(normalized.encode()).hexdigest(),only_whitespace_changed=True))
 row['statement']=normalized;row['statement_hash']=changed[-1]['normalized_native_header_hash']
write(contract/'headers-native-v2.json',headers)
freeze=load(run/'draft-freeze-v1.json')
freeze['fingerprint_version']='v2-native-normalized-planned-headers-only'
freeze['headers']={n:r['statement_hash'] for n,r in headers.items()}
freeze['planned_new_headers']={n:r['statement_hash'] for n,r in headers.items() if r['state'].startswith('planned')}
write(run/'draft-freeze-v2.json',freeze)
write(run/'fingerprint-correction-v2.json',dict(status='draft-metadata-correction-before-source-stabilization',rows=changed,reason='Native lean_declaration_header returns normalize_statement; v1 planned three headers were multiline raw text rather than canonical native normalized text. Exact binder/assumption/conclusion/algorithm tokens unchanged; raw v1 preserved. No new body existed and no mathematical target weakened. Restricted blind packet is unchanged because its statements have exactly the same tokens.',prior_contract='headers.json',authoritative_contract='headers-native-v2.json',authoritative_freeze='draft-freeze-v2.json',mathematical_repair=False))
print('Preserved raw v1; three planned fingerprints now use native normalization, mathematical tokens unchanged.')
