from common import *
fixed()
headers=load(CONTRACT/'headers-draft-v2.json')
defs=[
 ('BanditRLProof/OnlineConvexExtended.lean','def effectiveDomain','\n\n'),
 ('BanditRLProof/OnlineConvexExtended.lean','def extendedIndicator','\n\n'),
 ('BanditRLProof/OnlineClosedProper.lean','def SourceClosed','\n\n'),
 ('BanditRLProof/OnlineClosedProper.lean','def SourceProper','\n\n'),
 ('BanditRLProof/OnlineSubgradientBasic.lean','def SourceSubdifferential','\n\n'),
 ('BanditRLProof/OnlineBregmanProximal.lean','def divergence','\n\n'),
 ('BanditRLProof/OnlinePrescientBregman.lean','def advance','\n\n'),
 ('BanditRLProof/OnlinePrescientBregman.lean','def iterate','\n\n')]
packet='''# Neutral statement reconstruction packet

Reconstruct exactly the six statements below across seven semantic slots. Definitions, exact typed headers, and required scoped contexts only; no source attribution or theorem proof bodies. Imports supply canonical definitions. Do not seek source identities or prior review verdicts. Disclose related conversation history limits; this is source-withheld staged reconstruction, not absolute blindness. Requested actor effort medium.

## Canonical definitions (verbatim declarations, comments excluded)
'''
inputs=[]
for path,start,sep in defs:
    s=(ROOT/path).read_text(encoding='utf8')
    a=s.index(start);b=s.index(sep,a)
    definition=s[a:b]
    assert '/-' not in definition and '--' not in definition
    packet+='\n```lean\n'+definition+'\n```\n'
    inputs.append(dict(path=path,declaration_sha256=hashlib.sha256(definition.encode('utf8')).hexdigest()))
packet+='\n## Imports and exact scoped headers\n\n```lean\n'+headers['imports']+'```\n'
for target in headers['targets']:
    packet+='\n```lean\n'+target['context']+target['header']+'\nend\n```\n'
write(RUN/'neutral-packet-v1.md',packet)
write(RUN/'neutral-packet-inputs-v1.json',dict(packet=rows([RUN/'neutral-packet-v1.md']),definitions=inputs,headers=rows([CONTRACT/'headers-draft-v2.json']),source_identity_in_packet=False,proof_bodies_in_packet=False, limitation='Reused distinct actor has prior related context; source withheld for this packet only.'))
queries=[('proper','SourceProper'),('strict','StrictConvexOn'),('finite','finitePart_convex_of_subdifferentiable'),('minimum','proximal_finitePart_minimizer_iff'),('iterate','iterate_fixed_regret')]
for tag,q in queries:
    capture('retrieval-declarations-'+tag+'-v1',sys.executable,'-B','-X','utf8',ROOT/'tools/bandit.py','list-lean-decls',q,'--statement')
capture('retrieval-memory-proper-v1',sys.executable,'-B','-X','utf8',ROOT/'tools/bandit.py','search-memory','SourceProper')
capture('retrieval-source-API-v1','rg','-n','sourceProper_of_domain|SourceProper|finitePart_convex_of_subdifferentiable|proximal_finitePart_minimizer_iff|eq_of_isMinOn|theorem iterate_fixed_regret|theorem iterate_variable_regret','BanditRLProof/OnlineClosedProper.lean','BanditRLProof/OnlineBregmanExtended.lean','BanditRLProof/OnlinePrescientBregmanRegret.lean','.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean')
capture('retrieval-EReal-v1','rg','-n','theorem coe_toReal','\.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean',required=False)
write(RUN/'retrieval-audit-v1.md','''# Retrieval audit

Actual declaration-index queries and raw source search are separate evidence; index may be stale and no declaration card is compilation. Reuse finitePart_convex_of_subdifferentiable, proximal_finitePart_minimizer_iff, StrictConvexOn.eq_of_isMinOn, existing advance/iterate and cumulative fixed/variable statements. Missing properness producer is new shared with two endpoint consumers; algebraic strict objective/uniqueness/identity are new same-algorithm integration nodes. No external Optlib or new toolchain dependency. Before this helper, guessed OnlineExtendedProximal.lean and literal PowerShell wildcard searches failed read-only (file absent/OS123); correct file resolved via rg --files to OnlineBregmanExtended.lean. During contract context an old-package literal wildcard search again returned OS123, no code change or proof result. These are retrieval failures, not theorem obstructions.
''')
fixed()
