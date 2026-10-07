from common_v1 import *
fixed()
original=(RUN/'leaves/neutral-types-v1.lean').read_text(encoding='utf-8')
text=original.replace('import BanditRLProof.OnlineSubgradientPolicy','import BanditRLProof.OnlineSubgradientPolicy\nimport BanditRLProof.OnlineGuessingOGD')
for name in ['output','selected','LegalFeedback']:text=text.replace(':= BanditRL.OnlineSubgradientPolicy.'+name,' := BanditRL.OnlineSubgradientPolicy.'+name+' (E := ℝ)')
write(RUN/'leaves/neutral-types-v2.lean',text)
shared=Path('BanditRLProof/OnlineSubgradientPolicy.lean').read_text(encoding='utf-8').split('\ntheorem history_zero')[0]
shared=shared[shared.index('noncomputable section'):]
write(RUN/'blind-packet-v2.md','''Restricted source-blind packet. Read ONLY this packet. No source/proof/prior verdict/repo search. Requested GPT6Astra/medium, runtime attestation unavailable. Reconstruct Q01-Q04 individually in natural language and LaTeX and all seven semantic slots. Disclose inherited neutral-decoder context; do not infer source identity/acceptance. Write ONLY blind-reconstruction-v1.md/blind-receipt-v1.json beside this file; raw packet/report SHA256 and actor.task=/root/osd_blind. These are fully elaborated target proposition descriptions, NOT proofs.
W is the nonempty closed convex [0,1] real domain; project is actual nearest projection. b is finite real absolute loss embedded in EReal. EReal.toReal maps both infinities to zero, but b is finite everywhere. F/X/A/L are exact aliases of the following common context at real E. Global support membership means f(x)+g(z-x)<=f(z) for EVERY real z. A fixed exogenous policy has only the displayed finite explicit inputs; no promise about how exogenous parameters were chosen is implied. No probability or finite-query implementation is provided.
Shared mathematical context, no performance assumptions:
```lean
'''+shared+'\n```\nComplete typed targets:\n```lean\n'+text+'\n```\n')
write(RUN/'neutral-repair-v2.json',dict(original_failure='neutral-types-v1-01.log',changes=['Import the actual shared unitInterval-owning module; policy-only import does not expose it','Fix aliases X/A/L to E=real so typeclasses have no unresolved metavariable','Global support context quoted as complete scalar definition, not truncated subsequent theorem'],public_headers_changed=False,stage='draft',source_package_accepted=False,chapter_complete=False,goal_complete=False))
gate('neutral-types-v2-01','lake','env','lean',RUN/'leaves/neutral-types-v2.lean')
native('retrieval-record-v1-01','retrieval-record','--task',TASK,'--query','absolute loss actual finite-history played legal policy same-run horizon sqrtT','--candidate','BanditRL.OnlineGuessingSubgradient.loss_subgradient_bound','--candidate','BanditRL.OnlineSubgradientPolicy.regret_tuned','--compiled-scratch',str(RUN/'leaves/retrieval-probe-v1.lean'),'--provenance','Actual compiled public API types in pinned shared project; neutral elaboration failure preserved/repaired without public target change. No unchecked external repository or upgraded dependency','--output',str(RUN/'retrieval-v1.json'))
write(RUN/'snapshots/native-scaffold-task-v1.md',Path('tasks',TASK+'.md').read_bytes())
Path('tasks',TASK+'.md').write_bytes((CONTRACT/'contract-v1.md').read_bytes())
print('Four exact neutral targets elaborated; only metadata/import/type specialization repaired. No public proof body.')
