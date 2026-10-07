from common_v1 import *
fixed()
assert load(RUN/'neutral-closed-props-v1-exit.json')['exit_code']==1
old=RUN/'leaves/neutral-closed-props-v1.lean'
text=old.read_text(encoding='utf-8')
text=re.sub(r'(?m)^ (let .*)$',r'    \1',text)
write(RUN/'neutral-layout-repair-v2.json',dict(kind='neutral certificate layout only, before CONTRACT review',failed_probe=old.as_posix(),failed_probe_sha256=sha(old),original_exit_sha256=sha(RUN/'neutral-closed-props-v1-exit.json'),error='unexpected token def; expected term at N08 after N07 let-layout',cause='Stripping the proposition first line then indenting it one space made first let shallower than its unchanged four-space body.',repair='Indent only the first neutral let line four spaces to match the original frozen header layout.',all_public_and_planned_headers_unchanged=True,mathematical_target_version=1,original_failure_retained=True,acceptance=False))
write(RUN/'leaves/neutral-closed-props-v2.lean',text)
gate('neutral-closed-props-v2','lake','env','lean',RUN/'leaves/neutral-closed-props-v2.lean')
identity='import BanditRLProof.OnlineLearningFoundations\n'+text+'''
universe u
def propositionOf {P : Prop} (_ : P) : Prop := P
example : Neutral.N01.{u} = propositionOf (@BanditRL.OnlineLearning.lemma_1_2.{u}) := by rfl
'''
write(RUN/'leaves/exact-public-type-v2.lean',identity)
gate('exact-public-type-v2','lake','env','lean',RUN/'leaves/exact-public-type-v2.lean')
plan=load(CONTRACT/'planned-canary-headers-v1.json')
write(RUN/'neutral-map-v1.json',[dict(neutral='N%02d'%i,actual=PRE+'lemma_1_2' if i==1 else TEST+list(plan)[i-2],kind='existing source terminal' if i==1 else 'planned named validation test') for i in range(1,9)])
write(RUN/'blind-packet-v1.md','''# Source-blind closed propositions
Read ONLY this packet. Requested GPT-6 Astra/medium, no escalation/runtime attestation. Disclose reused actor prior history. Reconstruct EVERY N01-N08 in natural language and LaTeX, all seven slots: objects/spaces, quantifiers, assumptions, conclusion, constants/indices, operation/information, boundaries. Do not search source identities, original aliases, theorem bodies or previous verdicts. Report each definition's exact scope; a/b are explicit total functions. No theorem/proof acceptance verdict requested.
```lean
'''+text+'''
```
Write ONLY blind-decoder-v1.md and blind-decoder-receipt-v1.json in this RUN. Receipt actor.task=/root/osd_blind, input/report nested path and sha256_raw_bytes, proposition_ids N01-N08, semantic_slots_per_proposition7, prior_history_disclosure, requested_model GPT-6 Astra/requested_reasoning_effort medium/runtime_model_attested false. No source/proof/review edits.
''')
write(RUN/'neutral-type-bindings-v1.json',dict(status='Actual eight closedProps and existing public exact-type rfl compiled',public_source_sha256=sha(PUBLIC),packet_sha256=sha(RUN/'blind-packet-v1.md'),planned_canary_headers_sha256=sha(CONTRACT/'planned-canary-headers-v1.json'),canary_actual_type_identity_pending=True,source_review_pending=True,first_failed_probe_retained=True))
fixed();print('Actual eight neutral Props/public-type rfl passed; v1 layout failure retained; no target change.')
