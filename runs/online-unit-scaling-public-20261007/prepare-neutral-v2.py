from common_v1 import *
fixed()
gate('actual-API-retrieval-v2','rg','-n','SourceProper|SourceSubdifferential|SubdifferentiableOn|theorem_2_28|def history|def project|def fullSpace|project_fullSpace|HasFDerivAt.comp|hasGradientAt_scaled|history_scaling','BanditRLProof/OnlineClosedProper.lean','BanditRLProof/OnlineSubgradientBasic.lean','BanditRLProof/OnlineAffineSubgradient.lean','BanditRLProof/OnlineSubgradientDescent.lean','BanditRLProof/OnlineSubgradientPolicy.lean','BanditRLProof/OnlineGradientDescent.lean','BanditRLProof/OnlineHuber.lean','.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean',PUBLIC)
old=Path('runs/online-unit-scaling-20261004/leaves/neutral-types-v1.lean').read_text(encoding='utf-8');context=old[:old.index('#check')];context=context.replace('namespace NeutralUnits','namespace NeutralUnits\nuniverse u').replace('Type*','Type u')
rename={'BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V':'B','BanditRL.OnlineOptimalStep.upperBound':'U','SourceProper':'Q','SourceSubdifferential':'S','SupportPolicy':'P','scaledLoss':'F','scaledEta':'e','scaledPolicy':'a','history':'H','output':'Z','selected':'G','LegalFeedback':'L','regret':'R','V':'K'}
def translated(s):
 for a,b in rename.items():s=re.sub(r'(?<![\w.])'+re.escape(a)+r'(?!\w)',lambda m:b,s)
 return s
defs=[];mapping=[];actualprops=[]
commonbind='{E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]'
for k,(n,h) in enumerate(load(CONTRACT/'headers-v1.json').items(),1):
 tail=h[len('theorem '+n):];depth=0;index=None
 for j,ch in enumerate(tail):
  if ch in '({[':depth+=1
  elif ch in ')}]':depth-=1
  elif ch==':' and depth==0:index=j;break
 assert index is not None and depth==0,n
 args=tail[:index].strip().replace('Type*','Type u');prop=tail[index+1:].strip().replace('Type*','Type u');q='N%02d'%k
 bind=commonbind+' '+args if 'E' in re.findall(r'\b\w+\b',args+' '+prop) else args
 neutral='∀ '+translated(bind)+',\n  '+translated(prop)
 defs.append('def '+q+' : Prop := '+neutral);mapping.append(dict(neutral=q,actual=PRE+n,raw_header_sha256=hashlib.sha256(h.encode()).hexdigest(),args=bind))
 actualprops.append('∀ '+bind+',\n '+prop)
scratch=context+'\n\n'.join(defs)+'\n'+'\n'.join('#check '+x['neutral'] for x in mapping)+'\nend NeutralUnits\n'
write(RUN/'leaves/neutral-closed-props-v2.lean',scratch);gate('neutral-closed-props-v2','lake','env','lean',RUN/'leaves/neutral-closed-props-v2.lean')
identities='import BanditRLProof.OnlineUnitScaling\n'+scratch+'\nuniverse u\nopen BanditRL.OnlineConvex BanditRL.OnlineSubgradientPolicy BanditRL.OnlineUnitScaling\n'
for x,prop in zip(mapping,actualprops):identities+='example : NeutralUnits.'+x['neutral']+('.{u}' if 'Type u' in prop else '')+' = ('+prop+') := by rfl\n'
write(RUN/'leaves/full-type-identities-v2.lean',identities);gate('full-type-identities-v2','lake','env','lean',RUN/'leaves/full-type-identities-v2.lean')
write(RUN/'neutral-map-v1.json',mapping)
write(RUN/'blind-packet-v1.md','''# Source-blind complete proposition reconstruction
Requested GPT-6 Astra/medium/no escalation; runtime not independently attested. Disclose reused neutral-decoder history. Read ONLY this packet. Reconstruct EACH CLOSED N01-N22 in natural language and LaTeX with all seven slots: objects/spaces; quantifiers; assumptions; conclusion; constants/indices; operation/information; boundaries. No source identity/alias search, old verdict or body acceptance. K is fixed whole space; J is its actual nearest-point choice; k in H/Z/G/L/R is a dummy uniform interface, all targets use K only. P is deterministic finite-past whole losses/played history/current whole loss. Q/S/B are fully defined; distinguish algebraic EReal.toReal sum R from finite-loss guarantees. Check positive c versus arbitrary real chainrule c; positive eta versus unrestricted algebraic recursion; same adapted policy vs independent policy; no unspecified stochastic laws. Dimensions use additive exponent notation, not an actual physical unit type system.

```lean
'''+scratch+'''```

Write ONLY blind-decoder-v1.md and blind-decoder-receipt-v1.json in this packet RUN. Receipt actor.task=/root/osd_blind; input/report nested path and sha256_raw_bytes; proposition_ids N01-N22; semantic_slots_per_proposition7; prior_history_disclosure; requested_model GPT-6 Astra,requested_reasoning_effort medium,runtime_model_attested false. No source/proof/review verdict or other edits.''')
write(RUN/'neutral-type-bindings-v1.json',dict(status='actual22closedProps-and-fulltype-rfl-passed',packet_sha256=sha(RUN/'blind-packet-v1.md'),mapping_sha256=sha(RUN/'neutral-map-v1.json'),source_public_sha256=sha(PUBLIC),new_proofs=0,new_definitions=0,source_review_pending=True,not_proof_body_or_fidelity_evidence=True))
fixed();print('Actual22closed neutralProps/fulltypeidentities rfl compiled; distinct decoder/source review pending.')
