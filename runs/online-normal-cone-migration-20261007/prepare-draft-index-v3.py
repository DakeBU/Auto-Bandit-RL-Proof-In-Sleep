from pathlib import Path
import hashlib,json
run=Path(__file__).resolve().parent
s=(run/'freeze-draft-v2.py').read_text(encoding='utf-8').replace('historical-raw-supersession-v1.json','historical-raw-supersession-v2.json')
p=run/'freeze-draft-v3.py';assert not p.exists();p.write_bytes(s.encode())
meta=dict(before_first_use=True,path=p.as_posix(),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),failure='freeze-draft-v2-01 immutable-write guard rejected replacing existing v1 snapshot index after adding owning shared modules.',repair='New v2 snapshot index, original v1 preserved unchanged; all existing exact snapshot bytes must still match. No Lean/source target repair.',failed_log='freeze-draft-v2-01.log')
(run/'draft-preparer-before-use-v3.json').write_bytes((json.dumps(meta,indent=2)+'\n').encode())
