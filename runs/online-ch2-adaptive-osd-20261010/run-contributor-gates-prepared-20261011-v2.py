from delivery_guard_20261011_v2 import *
a=arguments();fixed(a,require_index=True);binding=source_binding()
receipts=[]
for label,base in [('stack',CONFIG['base']),('main',CONFIG['origin_main_at_preparation'])]:
    changed=subprocess.check_output(['git','diff','--name-only',base],cwd=ROOT,encoding='utf8').splitlines()
    for name in ['OnlineAdaptivePotential','OnlineAdaptiveOSD','OnlineAdaptiveBenchmark']:
        assert 'BanditRLProof/'+name+'.lean' in changed,'Nonempty substantive diff required'
    code,out=capture('contributor-'+label+'-'+a.tag,sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base,required=False)
    assert code==0 and 'not applicable' not in out.lower(),out
    receipts.append(dict(base=base,receipt=rows([RUN/('contributor-'+label+'-'+a.tag+'.json')])[0]))
fixed(a,require_index=True);same_binding(binding)
write(RUN/('contributor-inspected-'+a.tag+'.json'),dict(checks=receipts,source_binding=binding,nonempty_substantive_diff=True,origin_main_is_pinned_historical_snapshot=True,boundary='No native/package/chapter or merge acceptance'))
