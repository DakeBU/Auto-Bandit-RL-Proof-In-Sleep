from lower_common_v1 import *
import copy

reviewed();headers(3)
p=load(RUN/'nonsmooth-reader-proposal-v2.json')
route=p['route']; output=[]
for plan in load(CONTRACT/'nonsmooth-exact-import-plan-v1.json')['rows']:
    target=Path(plan['path']); before=Path(plan['snapshot']).read_bytes()
    assert target.read_bytes()==before and sha(target)==plan['baseline_sha256']
    raw=before+plan['append_exact_utf8'].encode('utf8')
    assert hashlib.sha256(raw).hexdigest()==plan['permitted_result_sha256']
    after=RUN/('publication-after-'+target.name)
    write(after,raw)
    output.append(dict(path=target.as_posix(),before_sha256=sha(target),after_snapshot=after.as_posix(),after_sha256=sha(after),operation='exact original RAW prefix plus one planned import'))
for filename,key in [('readings.json','readings'),('highlights.json','highlights'),('chapters.json','chapters')]:
    target=ROOT/'website/content'/filename
    snapshot=RUN/('publication-before-'+filename)
    assert target.read_bytes()==snapshot.read_bytes()
    old=load(snapshot);d=copy.deepcopy(old)
    if filename=='readings.json':
        r=next(r for r in d[key] if r['slug']==route)
        assert p['card']['label'] not in [c['label'] for c in r['source_theorems']]
        r['source_theorems'].append(p['card'])
        check=copy.deepcopy(d);next(r for r in check[key] if r['slug']==route)['source_theorems'].pop();assert check==old
    elif filename=='highlights.json':
        assert not set(n['full_name'] for n in p['notes']) & set(n['full_name'] for n in d[key])
        d[key].extend(p['notes']);assert d[key][:-3]==old[key]
    else:
        r=next(r for r in d[key] if r['slug']==route)
        assert p['new_module_glob'] not in r['module_globs']
        r['module_globs'].append(p['new_module_glob'])
        r['learning_goals'].append(p['added_learning_goal'])
        r['completion_definition']+=' '+p['completion_extension']
        check=copy.deepcopy(d);q=next(r for r in check[key] if r['slug']==route)
        q['module_globs'].pop();q['learning_goals'].pop()
        q['completion_definition']=q['completion_definition'][:-len(' '+p['completion_extension'])]
        assert check==old
    after=RUN/('publication-after-'+filename)
    write(after,d)
    output.append(dict(path=target.as_posix(),before_sha256=sha(target),before_snapshot=snapshot.as_posix(),
        after_snapshot=after.as_posix(),after_sha256=sha(after),operation='only exact future-scope AST additions; every previous parsed value/source formula/card/note/link retained'))
write(CONTRACT/'nonsmooth-materialized-future-bytes-v1.json',dict(
    rows=output,reader_proposal_v2_sha256=sha(RUN/'nonsmooth-reader-proposal-v2.json'),
    future_scope_v2_sha256=sha(CONTRACT/'nonsmooth-future-publication-scope-v2.json'),
    canonical_files_modified=False,review_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
reviewed();headers(3)
print('Exact five future byte results materialized under OWN RUN only; canonical roots/readers still unchanged.')
