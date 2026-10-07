from common_v1 import *
fixed();assert load(RUN/'full-type-identities-v1-exit.json')['exit_code']==1
s=(RUN/'prepare-neutral-v1.py').read_text(encoding='utf-8')
s=s.replace("gate('actual-API-retrieval-v1'","gate('actual-API-retrieval-v2'")
s=s.replace("context=old[:old.index('#check')]","context=old[:old.index('#check')];context=context.replace('namespace NeutralUnits','namespace NeutralUnits\\nuniverse u').replace('Type*','Type u')")
s=s.replace("commonbind='{E : Type*}","commonbind='{E : Type u}")
s=s.replace("args=tail[:index].strip();prop=tail[index+1:].strip()","args=tail[:index].strip().replace('Type*','Type u');prop=tail[index+1:].strip().replace('Type*','Type u')")
for a,b in [('neutral-closed-props-v1','neutral-closed-props-v2'),('full-type-identities-v1','full-type-identities-v2')]:s=s.replace(a,b)
s=s.replace("'\\nopen BanditRL.OnlineConvex","'\\nuniverse u\\nopen BanditRL.OnlineConvex")
s=s.replace("x['neutral']+' = ('+prop","x['neutral']+('.{u}' if 'Type u' in prop else '')+' = ('+prop")
write(RUN/'prepare-neutral-v2.py',s)
write(RUN/'neutral-probe-repair-v2.json',dict(stage='draft type-certificate repair only',failure='Full proposition rfl v1 failed: two independently inferred universe parameters; neutral closed Props themselves compiled.',failed_log_sha256=sha(RUN/'full-type-identities-v1.log'),repair='Explicit common universe u on each quantified Type and corresponding neutral proposition constant.',source_target_changed=False,proofs_changed=False,contract_version=1,new_math=0,pass_pending=True))
gate('execute-neutral-v2',sys.executable,'-B','-X','utf8',RUN/'prepare-neutral-v2.py')
