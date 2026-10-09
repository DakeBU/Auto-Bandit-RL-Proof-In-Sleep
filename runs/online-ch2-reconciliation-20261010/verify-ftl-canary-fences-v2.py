from ftl_canary_proof import *
canary_fixed();results=[]
for i,row in enumerate(load(CANARY/'frozen-headers-draft-v2.json')['rows'],1):
    fence=RUN/'fences'/('canary-%s-v1.json'%i)
    if fence.exists():
        assert i==1 and load(RUN/'ftl-canary-fence-1-v1.json')['actual_exit']==0
    else:
        capture('ftl-canary-fence-%s-v1'%i,sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',row['declaration'],'--file',TEST,'--output',fence)
    f=load(fence);assert f['statement_hash']==row['normalized_header_sha256']
    _,out=capture('ftl-canary-safe-verify-%s-v1'%i,sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','safe-verify','--fence',fence,'--lean-file',TEST)
    decoded=json.loads(out);assert decoded['ok'],decoded
    results.append(dict(declaration=row['declaration'],frozen_header_sha256=row['normalized_header_sha256'],fence=rows([fence]),verification=rows([RUN/('ftl-canary-safe-verify-%s-v1.json'%i)])))
write(RUN/'ftl-eight-canary-fences-inspected-v1.json',dict(rows=results,semantic_BOUNDARY='Native header fences and forbidden-token checks only; no compilation, full definition-context or theorem BODY review. Complete context and compiler values have separate receipts.',Test=rows([TEST]),chapter_complete=False))
canary_fixed()
