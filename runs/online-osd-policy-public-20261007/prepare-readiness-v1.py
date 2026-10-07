"""Actual declaration/API retrieval and full neutral type/value checks before blind review."""
from common_v1 import *
fixed();passed('render-source-v1-01')
imgs=load(RUN/'source-image-bindings-v1.json');assert all(sha(r['path'])==r['sha256'] for r in imgs['images'])
write(RUN/'source-pixel-review-v1.json',dict(actor='/root',status='all four actual source PNGs viewed',images=imgs['images'],PDF_sha256=imgs['PDF_sha256'],observations=['Definition2.18/2.20 properness/global supports visible at printed16.','Printed19 full arbitrary-current Lemma2.31 and explicit gradient-to-subgradient regret transfer.','Printed20 Algorithm2.2 output/pay/support/project order, Example2.32 separately required.','Printed21 coarse fixed formula and dimensional analysis separately identified.'],limits='These source pages only; no book/chapter acceptance.'))
for cmd in ['lifecycle-event','trial-log','statement-fence','safe-verify','frontier-refresh','frontier-shadow','retrieval-record','reference-index','list-lean-decls']:
 native('help-'+cmd+'-v1-01',cmd,'--help')
headers=load(CONTRACT/'headers-v1.json')
api=['BanditRL.OnlineSubgradientDescent.lemma_2_31','BanditRL.OnlineSubgradientDescent.finite_loss','BanditRL.OnlineSubgradientDescent.currentSubgradient_mem','BanditRL.OnlineGradientDescent.project_spec','BanditRL.OnlineGradientDescent.weighted_potential_sum','Fin.snoc_last','Fin.snoc_castSucc','Nat.rec','EReal.coe_toReal','Metric.dist_le_diam_of_mem','Real.sq_sqrt']
write(RUN/'leaves/actual-public-types-v1.lean','import BanditRLProof.OnlineSubgradientPolicy\nset_option pp.universes true\n'+'\n'.join('#check @'+n for n in [PRE+n for n in headers]+api))
gate('actual-public-types-v1-01','lake','env','lean',RUN/'leaves/actual-public-types-v1.lean')
context=re.sub(r'/--?[\s\S]*?-/', '',(CONTRACT/'actual-context-v1.txt').read_text(encoding='utf-8')).replace('namespace BanditRL.OnlineSubgradientPolicy','namespace NeutralHistory')
assert 'Orabona' not in context and 'Algorithm' not in context
props=[];mapping=[]
for i,(name,header) in enumerate(headers.items(),1):
 tail=header[len('theorem '+name):].strip();depth=0;pos=None
 for j,c in enumerate(tail):
  if c in '([{':depth+=1
  elif c in ')]}':depth-=1
  elif c==':' and depth==0:pos=j;break
 assert pos is not None,name
 pn=f'P{i:02}';props.append('def '+pn+' [instFD : FiniteDimensional ℝ E] : Prop :=\n  ∀ '+tail[:pos].strip()+',\n    '+tail[pos+1:].strip())
 mapping.append(dict(neutral_name='NeutralHistory.'+pn,actual_name=PRE+name,raw_header_SHA256=load(CONTRACT/'raw-statement-fingerprints-v1.json')[name]))
borrowed=['#print BanditRL.OnlineGradientDescent.Domain','#check @BanditRL.OnlineGradientDescent.project_spec','#print BanditRL.OnlineConvex.SourceProper','#print BanditRL.OnlineConvex.SourceSubdifferential','#print BanditRL.OnlineSubgradientDescent.SubdifferentiableOn','#print BanditRL.OnlineSubgradientDescent.currentSubgradient','#print BanditRL.OnlineSubgradientDescent.step','#print BanditRL.OnlineSubgradientDescent.iterate','#print EReal.toReal','#print Metric.diam']
neutral=context+'\n'+'\n\n'.join(props)+'\n'+'\n'.join(borrowed)+'\n'+'\n'.join('#print P'+f'{i:02}' for i in range(1,22))+'\nend NeutralHistory\n'
write(RUN/'leaves/neutral-propositions-v1.lean',neutral)
gate('neutral-propositions-v1-01','lake','env','lean',RUN/'leaves/neutral-propositions-v1.lean')
depnames=['Domain','SupportPolicy','history','output','selected','OracleLaw','canonicalPolicy','LegalFeedback','regret']
meta='''
open Lean Meta Elab Command in
run_meta do
  let env ← getEnv
  let deps : Array (Name × Name) := #[
'''+',\n'.join('    (`NeutralHistory.'+n+', `'+PRE+n+')' for n in depnames)+''']
  let renameDeps (e : Expr) : Expr := e.replace fun x => match x with
    | .const n ls => match deps.find? (fun p => p.1 == n) with
      | some p => some (.const p.2 ls)
      | none => none
    | _ => none
  for (neutral, actual) in deps do
    let some ai := env.find? actual | throwError "missing actual {actual}"
    let some ni := env.find? neutral | throwError "missing neutral {neutral}"
    unless ← isDefEq ai.type (renameDeps ni.type) do
      throwError "DEPENDENCY TYPE MISMATCH {actual}: {ai.type}; {renameDeps ni.type}"
    let some av := ai.value? | throwError "missing actual value {actual}"
    let some nv := ni.value? | throwError "missing neutral value {neutral}"
    unless ← isDefEq av (renameDeps nv) do
      throwError "DEPENDENCY VALUE MISMATCH {actual}: {av}; {renameDeps nv}"
    logInfo m!"DEPENDENCY_TYPE_VALUE_MATCH {actual} = {neutral}"
  let rec closeLambdas : Expr → Expr
    | .lam n t b bi => .forallE n t (closeLambdas b) bi
    | e => e
  let pairs : Array (Name × Name) := #[
'''+',\n'.join('    (`'+r['actual_name']+', `'+r['neutral_name']+')' for r in mapping)+''']
  for (actual, neutral) in pairs do
    let some ai := env.find? actual | throwError "missing actual {actual}"
    let some ni := env.find? neutral | throwError "missing neutral {neutral}"
    let some nv := ni.value? | throwError "missing proposition description {neutral}"
    unless ← isDefEq ai.type (renameDeps (closeLambdas nv)) do
      throwError "FULL CONTEXT MISMATCH {actual}: {ai.type}; {renameDeps (closeLambdas nv)}"
    logInfo m!"FULL_CONTEXT_MATCH {actual} = {neutral}"
'''
write(RUN/'leaves/full-context-comparison-v1.lean','import Lean\nimport BanditRLProof.OnlineSubgradientPolicy\n'+neutral+'\n'+meta)
gate('full-context-comparison-v1-01','lake','env','lean',RUN/'leaves/full-context-comparison-v1.lean')
raw=(RUN/'full-context-comparison-v1-01.log').read_text(encoding='utf-8');assert raw.count('FULL_CONTEXT_MATCH ')==21 and raw.count('DEPENDENCY_TYPE_VALUE_MATCH ')==9
write(RUN/'neutral-to-actual-map-v1.json',dict(rows=mapping,method='Lean.Meta.isDefEq full closed types under nine explicitly type AND value-audited dependency renamings; not literal equality of independently named constants or theorem proofs',all21_exact_actual_types_preserved=True,dependency_names=depnames,evidence='full-context-comparison-v1-01.log',neutral_Props_are_descriptions_not_proofs=True))
import argparse
sys.path.insert(0,str(ROOT));from tools import bandit
idx=RUN/'retrieval-snapshot-v1';before=sha('MANIFEST.md');old={p.as_posix():sha(p) for p in Path('research-wiki/retrieval-index').glob('*.json')}
bandit.RETRIEVAL_INDEX_DIR=idx;bandit.MANIFEST=RUN/'reference-index-manifest-v1.md';assert bandit.cmd_reference_index(argparse.Namespace())==0
assert sha('MANIFEST.md')==before
for p,h in old.items():assert sha(p)==h,p
write(RUN/'reference-index-scope-v1.json',dict(actual_implementation='tools.bandit.cmd_reference_index with explicit task-owned output/MANIFEST adapter; CLI has no scoped output flag',canonical_indexes_and_MANIFEST_unchanged=True,rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in idx.glob('*.json')]))
for label,cmd,args in [('decl-policy-v1-01','list-lean-decls',['OnlineSubgradientPolicy','--statement']),('memory-policy-v1-01','search-memory',['finite-history support']),('mathlib-cards-v1-01','list-mathlib',[]),('weapons-v1-01','list-weapons',[])]:native(label,cmd,*args)
native('retrieval-record-v1-01','retrieval-record','--task',TASK,'--query','actual deterministic finite-history played-legal support recurrence and same-run sharp regret','--candidate',PRE+'history','--candidate',PRE+'one_step_chain','--candidate',PRE+'regret_fixed','--candidate',PRE+'regret_variable','--candidate',PRE+'regret_tuned','--compiled-scratch',RUN/'leaves/actual-public-types-v1.lean','--provenance','Actual existing21 public target types, nine neutral dependency compiled type/value checks, full21 closed target types under map and eleven pinned shared/mathlib API headers. No new proof/dependency upgrade.','--output',RUN/'native-retrieval-v1.json')
intro='''Restricted source-blind packet. Requested GPT6Astra/medium only. Read ONLY this packet, no repository/source/proof/prior-verdict search. Reconstruct P01-P21 individually in natural language/LaTeX and seven semantic slots. Disclose any prior neutral-decoder context; no source identity or source acceptance is provided. Write ONLY blind-reconstruction-v1.md / blind-receipt-v1.json adjacent, with raw packet/report SHA, actor.task=/root/osd_blind, requested settings and runtime_model_attested=false. These are fully elaborated proposition descriptions, NOT proofs of the targets. Mathematical definitions are context, not assumed performance bounds.

The finite-dimensional real inner-product space has a nonempty closed convex domain and actual nearest projection. Proper losses are nowhere bottom and finite somewhere; supports test ALL ambient comparisons. EReal.toReal maps BOTH infinities to zero, so finite-value production matters. The policy receives time, exactly Fin t past whole losses, Fin(t+1) actual outputs and current whole loss; recursion appends the actual projection. Played legality differs from the stronger OPTIONAL universal off-path law. Policy/initialization/schedules are prescribed exogenous parameters; strict-prefix comparison keeps p/x1 fixed and compares whole past loss functions/rates. No probability law, measurability, external-parameter independence, executable finite-query oracle or anytime assertion. Audit source-round1/Lean0 indexing, output T endpoint, same actual chosen supports and same tuned eta-dependent run, all residual signs/denominators/constant halves, fixed T0/unbounded versus variable T>0/actual bounded metric diameter, distance-versus-all-comparator tuning with positive D/G/T, and exact identity adapters for the current-only choice. Distinguish structural consequences from any literature attribution, which is not supplied.

```lean
'''
packet=intro+neutral+'\n```\nActual standalone elaboration and borrowed context (target proofs omitted):\n```text\n'+(RUN/'neutral-propositions-v1-01.log').read_text(encoding='utf-8')+'\n```\n'
assert 'Orabona' not in packet and '2.31' not in packet and 'arXiv' not in packet
write(RUN/'blind-packet-v1.md',packet)
write(RUN/'readiness-v1.json',dict(status='actual21 public types/eleven shared API types/nine dependency types AND values/21 full neutral target types under map and scoped retrieval passed',new_proofs=0,new_definitions=0,current_focused_body_compiled=False,source_package_accepted=False,chapter_complete=False,goal_complete=False))
event('draft',dict(actual_targets=21,neutral_type_and_value_comparison_passed=True,current_distinct_semantic_review_pending=True,new_proofs=0))
fixed();print('Current21 exact neutral targets and existing producer retrieval ready; distinct decoder/CONTRACT pending.')
