from common import *
fixed()
h=load(CONTRACT/'headers-draft-v1.json')
p=h['prefix']+h['definitions']
for row in h['targets']:
    bs,con=row['header'].split('theorem '+row['name'].rsplit('.',1)[1],1)[1].rsplit(' :\n',1)
    p+=row['context']
    p+=('#check fun '+bs.strip()+' =>\n  ('+con.strip()+' : Prop)\n') if bs.strip() else '#check ('+con.strip()+' : Prop)\n'
    p+='end BanditRL.OnlineUnboundedOSD\n'
write(RUN/'TargetTypesV2.lean',p)
write(RUN/'type-probe-repair-v2.json',dict(before_actual_exit=load(RUN/'draft-type-probe-v1.json')['actual_exit'],cause='A zero-binder Prop must be #check(expression), not #check fun =>expression. Draft probe generator syntax only.',all_headers_and_definitions_unchanged=True,headers_sha256=sha(CONTRACT/'headers-draft-v1.json'),definitions_sha256=sha(CONTRACT/'definitions-draft-v1.lean'),previous_probe_retained=True))
code,out=capture('draft-type-probe-v2','lake','env','lean',RUN/'TargetTypesV2.lean',required=False)
assert code==0
write(RUN/'draft-type-probe-inspected-v2.json',dict(actual_exit=code,target_types=11,proof_bodies=0,definitions=4,placeholder_or_axiom=False,scope='Eleven Prop types and complete prospective definitions only, not eleven compiled theorems. Unused hypothesis warnings are from lambda type probes, not weakened statements.'))
for f in ['retrieval-command-v2.json','RetrievalV2.lean']:
    src=ROOT/'tmp/online-ch2-unbounded-readonly-20261010-v1'/f
    dst=RUN/('prior-readonly-'+f)
    if not dst.exists():write(dst,src.read_bytes())
    else:assert sha(src)==sha(dst)
assert load(RUN/'prior-readonly-retrieval-command-v2.json')['actual_exit']==0
for sub in ['conversion-window','lifecycle-event','statement-fence']:
    capture('CLI-help-'+sub+'-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py',sub,'--help')
neutral=[]
def renamed(s):
    s=s.replace('BanditRL.OnlineUnboundedOSD','NeutralPacket')
    for old,new in [('powerSteps','schedule'),('switchSlope','signPattern'),('switchLoss','payoff'),('phi','coefficient')]:s=s.replace(old,new)
    for i,r in enumerate(h['targets']):s=s.replace(r['name'].rsplit('.',1)[1],'claim'+str(i+1))
    return s
for i,r in enumerate(h['targets']):neutral.append(dict(id='claim'+str(i+1),context=renamed(r['context']),header=renamed(r['header'])))
write(RUN/'neutral-packet-v1.json',dict(imports=h['prefix'],definitions=renamed(h['definitions']),targets=neutral,scope='Source withheld; exact mathematical types and complete definitions with neutralized owned names. Shared API meanings may be read, no paper/source-card/author/proof bodies. Existing related actor history disclosed.'))
write(RUN/'neutral-inputs-v1.json',dict(rows=rows([RUN/'neutral-packet-v1.json',RUN/'TargetTypesV2.lean']),source_contents_withheld=True,neutral_packet_only_for_decoding=True,related_history_disclosed=True))
fixed()
print('All eleven exact draft types elaborated; neutral packet ready; no theorem body lowered.')
