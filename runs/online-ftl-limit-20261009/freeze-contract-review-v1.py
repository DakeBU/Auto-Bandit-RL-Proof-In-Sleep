from common_v1 import *
fixed()
b=load(RUN/'blind-receipt-v1.json')
assert b['inputs_unchanged'] and not b['blocking_ambiguities']
assert b['report_sha256']==sha(RUN/'blind-reconstruction-v1.md')
for row in load(RUN/'blind-inputs-v1.json')['rows']:
    assert sha(row['path'])==row['sha256']
write(RUN/'root-source-pixel-review-v1.json',dict(actor='/root',
    actually_viewed=[dict(page=page,path=(RUN/('source-pdf%d-v1.png'%page)).as_posix(),
        sha256=sha(RUN/('source-pdf%d-v1.png'%page)),detail='original',fresh_render=True) for page in [14,16,18]],
    findings='Ordinary limit <=0 on printed2, actual strict-past initialhalf algorithm and4log bound on printed4, sublinear best-regret prose onprinted6. Derived F1-5 explicitly separate from printed claims; no unconditional ordinary fixedcomparator convergence claim.'))
paths=list(CONTRACT.iterdir())+[RUN/p for p in ['00_context.md','10_director-v1.md','11_architect-v1.md','12_worker-v1.md',
    'memory_digest.md','retrieval_index.md','neutral-context-and-statements-v1.lean.txt','blind-packet-v1.md','blind-inputs-v1.json',
    'blind-reconstruction-v1.md','blind-receipt-v1.json','source-contract-review-packet-v1.md','contract-mutable-scope-v1.json',
    'draft-typecheck-v1.lean','draft-typecheck-v1.log','draft-typecheck-v1-exit.json','api-probe-v1.lean','api-probe-v1.log','api-probe-v1-exit.json',
    'baseline-v1.json','root-source-pixel-review-v1.json','roundtrip-render-repair-v1.json']]
paths += [RUN/('source-pdf%d%s'%(page,suffix)) for page in [14,16,18] for suffix in ['-v1.png','-text-v1.txt']]
paths += [ROOT/r['path'] for r in load(RUN/'baseline-v1.json')['rows'] if 'OnlineLearning' in r['path'] or 'OnlineSquareMinimum' in r['path'] or 'OnlineNoRegretSemantics' in r['path']]
paths += [ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows']]
write(RUN/'source-contract-review-inputs-v1.json',dict(rows=rows(paths)))
print('Bound RAW inputs for distinct anti-anchored contract review:',len(set(paths)),flush=True)
