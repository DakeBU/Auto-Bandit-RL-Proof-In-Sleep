from common_v1 import *
fixed()
write(RUN/'full-neutral-repair-v2.json',dict(
    prior_exit=load(RUN/'full-neutral-types-v1-exit.json')['exit_code'],
    prior_log_sha256=sha(RUN/'full-neutral-types-v1.log'),
    cause='Header-to-closed-Prop generator split the first binder colon, rather than the declaration result colon.',
    correction='Locate the result colon outside balanced parentheses/brackets/braces. Preserve failed packet and all actual headers/bodies.',
    source_or_frozen_target_changed=False,invalid_packet_not_sent_to_decoder=True))
actual=load(RUN/'actual-public-canary-headers-v1.json')
original=(RUN/'full-neutral-packet-v1.lean').read_text(encoding='utf-8')
context=original[:original.index('def B001')]
replacement={'BanditRLProof.Exp3.FiniteActionDistribution':'P',
 'BanditRLProof.Exp3.finiteActionMeasure':'law','polyaNext':'f1','pathWeight':'f2',
 'binaryStream':'f3','binaryValues':'f4','causalPredict':'f5','pathRegret':'f6',
 'pathExpectation':'f7','prefixMeasure':'f8','pathLearnerLoss':'f9','pathBestLoss':'f10',
 'coinMeasure':'f11','seededPolicy':'f12','empiricalMean':'m','comparatorRegret':'r'}
def neutral(s):
    for a,b in sorted(replacement.items(),key=lambda x:-len(x[0])):s=s.replace(a,b)
    return s
def split_result(s):
    depth=0
    for i,ch in enumerate(s):
        if ch in '([{':depth+=1
        elif ch in ')]}':depth-=1
        elif ch==':' and depth==0:return s[:i].strip(),s[i+1:].strip()
    raise AssertionError(s)
packet=context;index=[]
for i,row in enumerate(actual,1):
    h=row['header'];local=row['name'].rsplit('.',1)[1]
    start='theorem '+local;assert h.startswith(start)
    binders,prop=split_result(h[len(start):])
    binders=neutral(binders).replace('Type*','Type u');prop=neutral(prop)
    ident='B'+str(i).zfill(3)
    packet+='def '+ident+' : Prop :=\n  '+(('∀ '+binders+', '+prop) if binders else prop)+'\n\n'
    index.append(dict(id=ident,name=row['name'],polymorphic='Type u' in binders))
packet+='end NeutralContext\n'
write(RUN/'full-neutral-packet-v2.lean',packet)
write(RUN/'full-neutral-map-v2.json',index)
gate('full-neutral-types-v2','lake','env','lean',RUN/'full-neutral-packet-v2.lean')
write(RUN/'full-neutral-input-v2.json',dict(path=(RUN/'full-neutral-packet-v2.lean').as_posix(),
    sha256=sha(RUN/'full-neutral-packet-v2.lean'),number_of_targets=64,
    definitions_context_only=True,proofs_absent=True,source_identity_not_supplied_in_packet=True,
    reused_actor_history_must_be_disclosed=True,actual_closed_types=True))
fixed()
print('All64 actual closed propositions typechecked; applicable neutral packet v2.')
