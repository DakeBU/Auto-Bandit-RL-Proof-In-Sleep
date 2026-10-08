from common_v1 import *
import re
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash
fixed()
context=(CONTRACT/'canary-context-v1.lean.txt').read_text(encoding='utf8')
text=(CONTRACT/'canary-targets-v1.lean.txt').read_text(encoding='utf8')
probe=context.replace('import BanditRLProof.OnlineFTLLimitSemantics',
    'import BanditRLProof.OnlineSquareMinimum\nimport BanditRLProof.OnlineNoRegretSemantics').rsplit('end Tests.OnlineFTLLimitSemantics',1)[0]
targets=[]
for i,chunk in enumerate(text.split('theorem ')[1:],1):
    header='theorem '+chunk.strip()
    name=re.search(r'theorem\s+(\w+)',header).group(1)
    targets.append(dict(id='C'+str(i),name='Tests.OnlineFTLLimitSemantics.'+name,header=header,statement_hash=statement_hash(header)))
    args,goal=header.split(name,1)[1].split(' :\n',1)
    probe+='\n#check ('+('∀ '+args.strip()+',\n' if args.strip() else '')+goal+')\n'
assert len(targets)==12
write(CONTRACT/'canary-targets-v1.json',dict(version=1,targets=targets,
    context_sha256=sha(CONTRACT/'canary-context-v1.lean.txt'),body_compiled=False,chapter_complete=False,goal_complete=False))
write(RUN/'canary-draft-typecheck-v1.lean',probe+'\nend Tests.OnlineFTLLimitSemantics\n')
gate('canary-draft-typecheck-v1','lake','env','lean',RUN/'canary-draft-typecheck-v1.lean')
neutral=(RUN/'neutral-context-and-statements-v1.lean.txt').read_text(encoding='utf8')
neutral=neutral.split('\ntheorem meanPredict_bestLoss_nonneg',1)[0]+'\nend BanditRL.OnlineLearning\n'
neutral+='\nopen BanditRL.OnlineLearning\nnamespace Tests.OnlineFTLLimitSemantics\n\n'
neutral+='def alternatingObservation (t : ℕ) : ℝ := if t % 2 = 0 then 0 else 1\n\n'+text+'\nend Tests.OnlineFTLLimitSemantics\n'
write(RUN/'neutral-canary-statements-v1.lean.txt',neutral)
write(RUN/'canary-blind-packet-v1.md','Read ONLY neutral-canary-statements-v1.lean.txt. Reconstruct12 exactstatements, all assumptions/quantifiers/indices/signs/constants/ordinarylimits, and explain what nondegenerate validation is expressed. '
    'NO source/otherfiles/priorverdict read; retainedpreviousdecoderhistory disclosed. No proof or compile/source acceptance verdict. Write ONLY canary-blind-reconstruction-v1.md and canary-blind-receipt-v1.json in ownRUN, two RAWinputbeforeafter and report_sha256, inputs_unchanged; requested GPT-6 Astra/medium unverified, reusedactor history. '
    'Avoid tautologically calling all5 main endpoints verified: the packet is onlycanarytargettypes, no bodies. Separate binaryprefix/convergenceproducer target and actualpublic instantiation goals.')
write(RUN/'canary-blind-inputs-v1.json',dict(rows=rows([RUN/'neutral-canary-statements-v1.lean.txt',RUN/'canary-blind-packet-v1.md'])))
write(RUN/'canary-source-review-packet-v1.md','Separate canary contract review. Audit exact12headers/context, neutralreconstruction and arithmetic on actualperiodicbinary sequence0,1,0,1,... . '
    'Source originalp2/p4/p6 supplies actualmeanPredict and signedmetric; these12 are tests, not12source results. Verify initialvalueshalf,0,half,third; bestR0=0,R1=quarter,R2=threequarters; fixedu0 limitnegativequarter, uhalf0. '
    'Binarycounts floorT/2 and empiricalmean→half mustbe proved fromsame stream; all5publicproducer statements mustbe actuallyinstantiated later, nooracle lower/upper/mean/regret premises. '
    'Report slots+nondegeneracy/type/boundary; allowedcanarybodyproof afterapproval, headersimmutable. Do notlabel compiled/bodyaccepted/source/chapterclosed. '
    'Write canary-contract-review-v1.md and canary-contract-receipt-v1.json here only, RAWallinputbeforeafter, report_sha256, inputs_unchanged/fixed_input_count, required_blocking_repairs, verdict accepted|rejected|accepted-with-explicit-delta. Otherpackageglobalfilesnotmutable.')
print('12 exact proposed canary types elaborated; no test proof.',flush=True)
