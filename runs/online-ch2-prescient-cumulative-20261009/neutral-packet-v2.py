from common import *
import re
data=load(RUN/'neutral-statement-packet-v1.json')
out={k:v for k,v in data.items() if k not in ['canonical_supporting_definitions','loss_support_definitions']}
defs=[]
for file,names in [('BanditRLProof/OnlinePrescientBregman.lean',['advance','iterate']),('BanditRLProof/OnlineBregmanProximal.lean',['divergence']),('BanditRLProof/OnlineClosedProper.lean',['SourceProper']),('BanditRLProof/OnlineSubgradientBasic.lean',['SourceSubdifferential'])]:
    s=(ROOT/file).read_text(encoding='utf8')
    for name in names:
        m=re.search(r'^def '+name+r'\b[\s\S]*?(?=\n\n|\Z)',s,re.M)
        assert m, (file,name)
        defs.append(dict(name=name,exact_definition=m.group(0)))
out['canonical_definitions']=defs
out['no_source_prose_or_proof_bodies']=True
write(RUN/'neutral-statement-packet-v2.json',out)
write(RUN/'neutral-packet-repair-v2.json',dict(reason='First unissued packet included complete supporting modules whose comments identify sources. It was not sent to decoder. Version2 contains exact definitions only and unchanged target/context.',prior_sha256=sha(RUN/'neutral-statement-packet-v1.json'),current_sha256=sha(RUN/'neutral-statement-packet-v2.json'),target_header_hashes_unchanged=[t['statement_sha256'] for t in out['targets']],prior_packet_was_sent=False))
print('Neutral definitions-only v2 issued; v1 retained unissued.')
