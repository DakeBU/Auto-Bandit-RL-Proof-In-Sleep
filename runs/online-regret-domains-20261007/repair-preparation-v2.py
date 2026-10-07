from common_v1 import *
fixed()
old=load(CONTRACT/'existing-public-headers-v1.json');tests=load(CONTRACT/'planned-canary-headers-v1.json')
scratch=(RUN/'leaves/neutral-closed-props-v1.lean').read_text(encoding='utf-8')
identity=(RUN/'leaves/existing-public-type-identities-v1.lean').read_text(encoding='utf-8')
identity=identity.replace('def propositionOf','universe u\ndef propositionOf')
for i,n in enumerate(old,1):
 identity=identity.replace('Neutral.N%02d = propositionOf (@%s%s)'%(i,PRE,n),'Neutral.N%02d.{u} = propositionOf (@%s%s.{u})'%(i,PRE,n))
write(RUN/'leaves/existing-public-type-identities-v2.lean',identity)
gate('existing-public-type-identities-v2','lake','env','lean',RUN/'leaves/existing-public-type-identities-v2.lean')
write(RUN/'preparation-repair-v2.json',dict(original_failure='existing-public-type-identities-v1.log',reason='Independent implicit universe metavariables in polymorphic equality audit; both sides now explicitly share arbitrary universe u',original_failure_preserved=True,target_header_changed=False,neutral_closed_types_changed=False,proof_bodies_written=False,applicable_identity='leaves/existing-public-type-identities-v2.lean'))
blueprint=Path('proof-blueprints')/(TASK+'.md');raw=blueprint.read_bytes()
write(RUN/'snapshots/native-blueprint-full-v1.md.raw',raw)
blueprint.write_bytes(('''# Scoped proof blueprint: '''+TASK+'''

Owning contract: docs/contracts/online-regret-domains-v1/contract-v1.md.
Exact statements and typed context are in existing-public-headers-v1.json,
planned-canary-headers-v1.json and planned-test-definitions-v1.json there.
Single ready route: typed finite regret identity -> restriction/prefix/empty
sum -> concrete negative-loss game -> shared eventual-upper adapter.
Planned edges are initial-dependency-DAG-v1.json; required actual VALUE
pairs are proof-value-obligations-v1.json. Contract review pending.
Zero new production math; eight test propositions. Chapter/Goal incomplete.

Actual native blueprint-refresh succeeded but embeds the complete global
MANIFEST (12MB), including unrelated historic blueprints. Original exact
output is retained in this RUN snapshots/native-blueprint-full-v1.md.raw.
This scoped navigation replacement neither erases its evidence nor changes
any target. No repeated full-manifest expansion is used for this task.
''').encode())
write(RUN/'blueprint-scope-repair-v2.json',dict(native_exit=load(RUN/'blueprint-own-v1-exit.json'),original_raw_bytes=len(raw),original_sha256=hashlib.sha256(raw).hexdigest(),snapshot_sha256=sha(RUN/'snapshots/native-blueprint-full-v1.md.raw'),scoped_blueprint_sha256=sha(blueprint),mathematical_targets_unchanged=True))
headers=list(old.items())+list(tests.items())
write(RUN/'neutral-map-v1.json',[dict(neutral='N%02d'%i,actual=(PRE if i<=2 else TEST)+n,kind='existing public proof' if i<=2 else 'named validation target') for i,(n,h) in enumerate(headers,1)])
write(RUN/'blind-packet-v1.md','''# Exact neutral propositions
Read ONLY this packet. Requested GPT-6 Astra/medium/no escalation; no runtime attestation. Disclose prior actor history and do not lookup source identity, actual aliases, bodies or old verdicts. Reconstruct EVERY N01–N10 in natural language and LaTeX, seven slots each: objects/quantifiers/assumptions/conclusion/constants and indices/probability and information/boundary. Reconstruct context a–j, typed loss domain, embedding/restriction and numerical counter-boundaries. No source acceptance decision. Write ONLY blind-decoder-v1.md and blind-decoder-receipt-v1.json in this RUN, actor.task=/root/osd_blind; input/report nested path/sha256_raw_bytes, proposition_ids N01–N10, semantic_slots_per_proposition7, prior_history_disclosure, requested_model GPT-6 Astra/requested_reasoning_effort medium/runtime_model_attested false.
```lean
'''+scratch+'\n```\n')
write(RUN/'neutral-type-bindings-v1.json',dict(status='10 exact closed types and 2 existing public exact identities at shared arbitrary universe u compiled; no new test bodies yet',blind_packet_sha256=sha(RUN/'blind-packet-v1.md'),applicable_identity_audit='existing-public-type-identities-v2',planned_production_math=0,source_review_pending=True))
write(RUN/'source-pixel-review-v1.json',dict(actor='/root',actual_tool='view_image',path=(RUN/'source-pdf14-v1.png').as_posix(),sha256=sha(RUN/'source-pdf14-v1.png'),pdf_page=14,printed_page=2,observed='Original rendered PDF actually viewed: finite regret formula, displayed limit wording, Remark1.1 and W-superset-V footnote; no generic W theorem',independent_external_review=False))
fixed();print('Preparation repair complete; same10 neutral targets; applicable two polymorphic identities v2; no new theorem body written.')
