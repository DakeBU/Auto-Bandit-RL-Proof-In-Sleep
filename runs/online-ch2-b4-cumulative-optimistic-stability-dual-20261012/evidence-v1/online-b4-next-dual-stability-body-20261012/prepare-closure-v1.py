from pathlib import Path
import json, hashlib, ast
P = Path(__file__).resolve().parent
def bind(p):
    p = p.resolve(); h = hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda: f.read(1048576), b''): h.update(c)
    return dict(path=str(p), bytes=p.stat().st_size, sha256=h.hexdigest())
orig = json.loads((P/'header-origins-v1.json').read_text(encoding='utf-8'))
files = {}; rows = []
for row in orig:
    op = Path(row['olean']).resolve(); rel = Path(*row['module'].split('.')); s = op.as_posix()
    ir = None
    if row['module'] == 'CumulativeOptimisticStabilityCandidate':
        src = P.parent/'online-b4-next-stability-body-20261012/candidate-v1.lean'
    elif '/.lake/build/lib/lean/' in s:
        base = Path(s.split('/.lake/build/lib/lean/')[0]); src = base/rel.with_suffix('.lean'); ir = base/'.lake/build/ir'/rel
    else:
        base = Path(s.split('/lib/lean/')[0]); src = base/'src/lean'/rel.with_suffix('.lean')
        if row['module'].startswith('Lake.'): src = base/'src/lean/lake'/rel.with_suffix('.lean')
    assert src.is_file(), str(src)
    fs = [src, *op.parent.glob(op.stem+'.*')]
    if ir: fs += list(ir.parent.glob(ir.name+'.*'))
    for f in fs:
        if f.is_file(): files[str(f.resolve())] = f
    rows.append(dict(module=row['module'], source=str(src.resolve()), olean=str(op)))
manifest = dict(scope='Actual header-import closure source and all existing lib/IR companions; full inventory pinned before BODY and import. Initial header trial itself pins declared parents only.', origins=rows, inputs=[bind(p) for p in files.values()], origin_probe=bind(P/'HeaderElaboration-v2.lean'), origin_output=bind(P/'header-origins-v1.json'), header_receipt=bind(P/'header-v1/receipt.json'))
with (P/'closure-manifest-v1.json').open('x', encoding='utf-8') as f: json.dump(manifest,f,indent=2)
cap = (P/'capture-v1.py').read_text(encoding='utf-8').replace("pinfile=P/'capture-pins-v1.json'", "pinfile=P/'capture-pins-v2.json'")
ast.parse(cap)
with (P/'capture-v2.py').open('x', encoding='utf-8') as f: f.write(cap)
pins = json.loads((P/'capture-pins-v1.json').read_text(encoding='utf-8')); pins['closure_manifest_sha256'] = bind(P/'closure-manifest-v1.json')['sha256']; pins['capture'] = bind(P/'capture-v2.py')
with (P/'capture-pins-v2.json').open('x', encoding='utf-8') as f: json.dump(pins,f,indent=2)
print(json.dumps(dict(pins=bind(P/'capture-pins-v2.json'), closure=bind(P/'closure-manifest-v1.json'), modules=len(rows), files=len(files))))
