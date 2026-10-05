"""Repair tactic syntax only; preserve the original failed typing attempt."""
from pathlib import Path
import hashlib,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent
old=run/'leaves/draft-statement-v1.lean'
new=run/'leaves/draft-statement-v2.lean'
assert not new.exists()
assert hashlib.sha256(old.read_bytes()).hexdigest()=='d22de51e9fccbd690170aecb94c12a2f2d2a504e9149489512616240e99bb2a5'
text=old.read_text(encoding='utf-8')
assert text.count(' := by\n\n')==2
with new.open('w',encoding='utf-8',newline='\n') as f:f.write(text.replace(' := by\n\n',' := by\n  skip\n\n'))
frozen=json.loads((run/'draft-freeze-v1.json').read_text(encoding='utf-8'))
for n,h in frozen['headers'].items():
    assert lean_declaration_header(old,n)==lean_declaration_header(new,n)
    assert hashlib.sha256(lean_declaration_header(new,n).encode()).hexdigest()==h
record={'kind':'private-probe-syntax-repair','original_file':old.as_posix(),'original_sha256':hashlib.sha256(old.read_bytes()).hexdigest(),
        'repaired_file':new.as_posix(),'repaired_sha256':hashlib.sha256(new.read_bytes()).hexdigest(),
        'original_failure':'Empty tactic blocks caused parser errors as well as two unproved goals; not clean header typing evidence.',
        'delta':'Insert skip in two private tactic bodies; both frozen headers and scoped context unchanged.',
        'headers':frozen['headers'],'original_preserved':True,'public_proofs_present':0,'compiled':False}
with (run/'private-probe-repair-v2.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(record,f,indent=2);f.write('\n')
print('Original preserved; identical headers; v2 remains intentionally unproved.')
