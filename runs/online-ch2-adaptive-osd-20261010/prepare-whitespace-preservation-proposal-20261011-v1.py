from common import *
import re, collections
source=RUN/'preflight-staged-RAW-20261011-v1.json'
a=load(source); files=collections.defaultdict(list)
for line in a['whitespace_lines']:
    m=re.fullmatch(r'(.*?):(\d+): (trailing whitespace\.|new blank line at EOF\.)',line)
    if m: files[m[1]].append((int(m[2]),m[3]))
counts=collections.Counter(); records=[]; additions=[]; ordinary=[]
for rel, diagnostics in sorted(files.items()):
    p=ROOT/rel; raw=p.read_bytes(); lines=raw.splitlines(keepends=True); kinds=collections.Counter(); details=[]
    for n,typ in diagnostics:
        ln=lines[n-1]; body=ln[:-2] if ln.endswith(b'\r\n') else ln[:-1] if ln.endswith(b'\n') else ln
        kind='blank-at-eof' if typ.startswith('new') else 'CR-only' if ln.endswith(b'\r\n') and not body.endswith((b' ',b'\t')) else 'ordinary-trailing'
        kinds[kind]+=1; counts[kind]+=1
        details.append(dict(line=n,kind=kind,line_bytes_hex=ln.hex()))
        if kind=='ordinary-trailing':ordinary.append(dict(path=rel,line=n))
    base=RUN if p.is_relative_to(RUN) else CONTRACT
    assert p.is_relative_to(base)
    local=p.relative_to(base).as_posix(); assert not any(c in local for c in ' \t*?[]"\\')
    options=[]
    if kinds['CR-only']: options.append('cr-at-eol')
    if kinds['blank-at-eof']:
        assert local in ['frontier-proposal-snapshots-20261011-v1/BEFORE-conversion-windows.md','frontier-proposal-snapshots-20261011-v1/BEFORE-proof-obligations.md','frontier-proposal-snapshots-20261011-v1/BEFORE-research-wiki-retrieval-index.md']
        options.append('-blank-at-eof')
    if options: additions.append((base,local+' whitespace='+','.join(options)+'\n'))
    records.append(dict(path=rel,sha256=sha(p),bytes=len(raw),crlf=raw.count(b'\r\n'),lf=raw.count(b'\n'),categories=dict(kinds),diagnostics=details))
snap=RUN/'whitespace-proposal-snapshots-20261011-v1'; changes=[]
for base in [RUN,CONTRACT]:
    p=base/'.gitattributes'; before=p.read_bytes(); suffix=''.join(v for b,v in additions if b==base).encode()
    if not suffix:continue
    assert before.endswith(b'\n')
    name='RUN' if base==RUN else 'CONTRACT'
    bp=snap/(name+'-BEFORE.gitattributes'); ap=snap/(name+'-AFTER.gitattributes')
    write(bp,before);write(ap,before+suffix)
    changes.append(dict(path=p.relative_to(ROOT).as_posix(),before_sha256=sha(bp),after_sha256=sha(ap),before_snapshot=bp.relative_to(ROOT).as_posix(),after_snapshot=ap.relative_to(ROOT).as_posix(),mode='exact-prefix-append'))
assert len(ordinary)==7 and len({x['path'] for x in ordinary})==1
p=ROOT/ordinary[0]['path']; raw=p.read_bytes(); lines=raw.splitlines(keepends=True)
for x in ordinary:
    i=x['line']-1; assert lines[i].endswith(b' \n'); lines[i]=lines[i][:-2]+b'\n'
successor=snap/'PROPOSED-SUCCESSOR-forward-precise-source-candidates-20261011-v1.md';write(successor,b''.join(lines))
plan=dict(schema=1,mode='proposal-only-no-application',input=dict(path=source.relative_to(ROOT).as_posix(),sha256=sha(source)),diagnostic_file_count=len(files),diagnostic_counts=dict(counts),files=records,attribute_changes=changes,ordinary_trailing_errors_retained=ordinary,ordinary_successor_proposal=dict(original=p.relative_to(ROOT).as_posix(),before_sha256=sha(p),snapshot=successor.relative_to(ROOT).as_posix(),after_sha256=sha(successor),justification='Removes exactly seven single trailing ASCII spaces after Depends on prose. No source claim, proof, dependency, line count or newline convention changes. Original stays immutable; successor alone does not clear original diagnostics.'),expected_remaining_errors=7,acceptance='NOT clean: seven ordinary errors intentionally remain visible; no blanket whitespace suppression',original_evidence_rewritten=False)
write(RUN/'whitespace-preservation-proposal-20261011-v1.json',plan)
print(json.dumps(dict(files=len(files),counts=dict(counts),attributes=len(changes),ordinary_errors_retained=len(ordinary))))
