from pathlib import Path
import hashlib,json,re,subprocess,sys
r=Path('runs/online-linearization-20261004');d=Path('docs/contracts/online-linearization-v1');d.mkdir(parents=True,exist_ok=True)
def write(p,s):
 with Path(p).open('w',encoding='utf-8',newline='\n') as f:f.write(s)
def jwrite(p,o):write(p,json.dumps(o,ensure_ascii=False,indent=2)+'\n')
ctx=(r/'leaves/context-v1.lean.txt').read_text(encoding='utf-8');headers=json.loads((r/'leaves/headers-v1.json').read_text(encoding='utf-8'))
write(d/'context.lean.txt',ctx)
for n,h in headers.items():
 write(d/(n+'-header.txt'),h+'\n')
 cmd=[sys.executable,'tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineLinearization.'+n,'--file',str(r/'leaves/target-v1.lean.txt'),'--output',str(d/(n+'.json'))]
 # Native premise fragments copied from the frozen headers, not invented extra assumptions.
 for start in re.finditer(r'\((h\w+)\s*:',h):
  i=start.start();depth=0
  for k in range(i,len(h)):
   if h[k]=='(':depth+=1
   elif h[k]==')':
    depth-=1
    if depth==0:cmd+=['--source-assumption',h[i:k+1]];break
 subprocess.run([sys.executable,str(r/'run-command.py'),'fence-'+n]+cmd,check=True)
notes={
'00_context.md':'''# Context
Whole-book unbudgeted real Goal remains active. Package only: C2-linearization, Orabona v10 Section2.3 printed22/PDF34. Worktree research-online-book; new branch codex/research-online-linearization, stacked on unmerged OPENdraft PR149 exact410693c31d8e1343c6b023886304520c2a834a11. Canonical main clean6847b678a73db68dee5101d6f05c2453c1405afc. Shared Git/.lake retained, no toolchain change, no anonymous/private-paper edits. Main/live not updated. All writing commands run in this worktree.
Roles: formalizer/root GPT6 Astra/medium; distinct existing blind/source actors medium. These are automated actors, not independent human/external-model review. Single lower proof route. Native commands enforce selected fences/trials/checks, while staged role/source reviews remain explicit file/prompt conventions; no single-runtime full-flow claim. Existing global active_frontier SGB must remain unchanged. Historical package raw receipts stay immutable; future root/metadata changes will drift their current-path rows, not revoke historical exact-commit acceptance.
''',
'10_upper_director.md':'''# Director
Bounded terminal: a genuine causal linear learner reads only strict-past vectors; a chosen current support is appended after output. Convex comparator regret is bounded by the linear comparator regret of the SAME learner on its actually generated supports. Universal OLO guarantees transport to the same realized sequence. This is a theorem-edge; helpers alone cannot discharge C2-linearization. No projection/stepsize algorithm is imposed on arbitrary learner A. Deterministic pathwise full information, finite-dimensional real Euclidean space, proper extended-real losses subdifferentiable on the shared nonempty closed convex domain. No boundedness, independence, measurable random oracle, or executable-choice claim. Every formal/source numbered result remains required in coverage; wholeChapter/book incomplete.
''',
'20_middle_architect.md':'''# Architect
Freeze18 actual Prop headers and raw context definitions before theorem bodies. First ready finite leaves: outputHistory_last, history_zero/succ/castSucc; then history_selected, output_linear_run and outputHistory_played. Feasibility follows from universal finite-history learner law; no desired one-step regret input. Strict-past loss-prefix equality keeps A,p fixed externally. Current policy sees past whole functions, reconstructed finite outputs, and current whole loss, not future/comparator/horizon. Off-path OracleLaw optional adapter; central comparison needs only actual played legal supports. Canonical producer instantiates support selection.
DAG: history_succ->history_selected->output_linear_run; history_selected->outputHistory_played; outputHistory_last+feasible+oraclelaw->oracle_feedback->canonical_feedback; support_gap (existing lemma2.31 first conjunct with eta1)+linearLoss_gap+output_linear_run+finite sum->regret_comparison; regret_comparison+universalOLO->regret_transfer; canonical_feedback+regret_comparison->canonical_regret_comparison. The generic linear inner-gap identity and arbitrary learner interface do not require new dependencies. Shared module imports OSDPolicy and OnlineLearningRegret. Mathlib Fin.snoc and inner_sub_right reused. support_gap is a thin project wrapper, not duplicated projection theory. Retrieve existing project declaration API via native list-lean-decls and memory; theorem-cards and mathlib convex searches yield no causal producer. Typed signatures actually compiled before stabilization; exit0 alone not proof compilation.
Allowed edits after stabilization: body-only lower leaves/new publicmodule with identical context and18headers; new Tests/examples and evidence. Any statement/definition change requires version2 source/decoder review. No silent terminal weakening. Failures retained as raw compiler logs and repair notes.
''',
'source-card.md':'''# ONLINE-LINEARIZATION-ORABONA-V10-S2.3
Pinned PDF SHA256 cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17, 2026-06-21, Section2.3 printed22/PDF34. Raw source-pages includes context printed21-23 and read-ahead Chapter3; only Section2.3 is active.
Source: legal g_t in the global subdifferential of current loss at actual x_t implies loss gap <= inner(g_t,x_t-u). Sum over t, define tilde loss(x)=inner(g_t,x), then convex regret <= linear regret at SAME x_t. Any algorithm for linear losses can thus be used for OCO. Linear objective is difference of two sums for arbitrary vector sequence, all u in V. Reduction not always optimal (Example2.14); no minimax/universal optimality assertion.
Lean: A:t -> (Fin t ->E)->E is an externally prescribed deterministic causal learner; current output A t pastVectors precedes current loss read by support policy p. Actual vector history is Nat.rec/Fin.snoc; outputHistory reconstructs all earlier outputs from prefixes, proved equal to actual played outputs. Full sequence loss parameter is not queried in output until prior rounds; prefix theorem proves conditional strict-past nonanticipation with A,p fixed, not independence of how external A,p were constructed. LegalFeedback only played points; optional OracleLaw/canonical producer establish legal feedback under Feasible A and SubdifferentiableOn losses.
Shared Domain nonempty closed convex, finite-dimensional real inner product space models Rd. SourceProper rules out bottom and provides a finite ambient point; global supports plus properness yield finite losses at played point/comparator before toReal use. Main comparison permits an arbitrary ambient played x with legal support; it does not require off-path feasibility because support_gap already implies finite played values. Public feasible/canonical adapters give full OCO implementation on V. No bounded V requirement. Source round1=Lean0; T0 is algebraic extension. Comparator is evaluation-only; no input u/T to A or p. Universal OLO hB quantifies over all vector sequences and all feasible comparators at fixed T, then instantiated on generated supports; it is not an assumed desired actual one-step regret inequality. Fixed exogenous parameters, no randomized/adaptive-law probability or algorithm-existence-from-fullfuture claim.
Structural18-header components are library implementation consequences, not18 printed source theorems. Actual source endpoint is unnumbered Section2.3 performance/reduction. New chapter gate remains pending through semantic/Lean/fullharness/axiom/canary/site/reviewer acceptance. No main/live or wholechapter completion.
''',
'memory-digest-draft.md':'''# Draft digest
Source/statement API search and finite-history typed context are real evidence. new-task created conversion window; separate conversion-window command refused overwrite, raw rejection retained, then fill initial stub explicitly. Several guessed nonexistent paths/globs produced readonly retrieval errors; no source or toolchain change. Stop guessing paths, use rg actual file inventory. No bodies yet, no proof claim. Next freeze/review18 targets, then single dependency-ready structural route.
''',
'retrieval-index.md':'''# Retrieval index
Pinned source: source-binding.json/source-pages.txt/source-card.md. Existing API: retrieve-subgradient.log, retrieve-linearization.log, search-linearization.log; sourcegap chain OnlineSubgradientDescent.lemma_2_31; finite_loss/currentSubgradient_mem; OSDPolicy.OracleLaw/canonicalPolicy; OnlineLearning.comparatorRegret_eq_sum. Mathlib Fin.snoc_last/castSucc/lastCases, inner_sub_right, Finset.sum_le_sum. theorem-cards no matching causal reducer; no external Optlib dependency or upgrade. Type probe: draft-types-01.log/exit.json. Exact contracts docs/contracts/online-linearization-v1. Generic shared definitions reused, new module same registry.
'''}
for n,s in notes.items():write(r/n,s)
write('conversion-windows/ONLINE-LINEARIZATION-20261004.md',notes['source-card.md']+'\n'+notes['20_middle_architect.md'])
write('tasks/ONLINE-LINEARIZATION-20261004.md','# ONLINE-LINEARIZATION-20261004\nStatus: draft (typed target, proof not started).\nTarget file: BanditRLProof/OnlineLinearization.lean\nSource card: runs/online-linearization-20261004/source-card.md\nConversion window: conversion-windows/ONLINE-LINEARIZATION-20261004.md\n'+notes['10_upper_director.md']+'\n'+notes['20_middle_architect.md'])
# Source-blind packet: names neutralized, definitions only, no upstream theorem bodies.
imported='''structure Domain (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
 carrier : Set E
 nonempty : carrier.Nonempty
 closed : IsClosed carrier
 convex : Convex ℝ carrier
def Proper (f : E → EReal) : Prop := (∀ x, f x ≠ ⊥) ∧ ∃ x, ∃ r : ℝ, f x = (r : EReal)
def Supports (f : E → EReal) (x : E) : Set E := {g | ∀ y, f x + (inner ℝ g (y - x) : EReal) ≤ f y}
def Regular (V : Domain E) (f : E → EReal) : Prop := Proper f ∧ ∀ x ∈ V.carrier, (Supports f x).Nonempty
abbrev Support := (t : ℕ) → (Fin t → E → EReal) → (Fin (t + 1) → E) → (E → EReal) → E
def Law (V : Domain E) (p : Support) : Prop := ∀ t past h f, Regular V f → h (Fin.last t) ∈ V.carrier → p t past h f ∈ Supports f (h (Fin.last t))
def Choose (f : E → EReal) (x : E) : E := if h : (Supports f x).Nonempty then Classical.choose h else 0
def Default : Support := fun t _ h f => Choose f (h (Fin.last t))
def Comparator (loss : ℕ → E → ℝ) (prediction : ℕ → E) (u : E) (T : ℕ) : ℝ := (∑ t ∈ range T, loss t (prediction t)) - ∑ t ∈ range T, loss t u
'''
local=ctx[ctx.index('abbrev LinearPolicy'):]
local=local.replace('abbrev SupportPolicy := BanditRL.OnlineSubgradientPolicy.SupportPolicy (E := E)','abbrev SupportPolicy := Support')
mapping={'BanditRL.OnlineSubgradientDescent.SubdifferentiableOn':'Regular','BanditRL.OnlineSubgradientPolicy.OracleLaw':'Law','BanditRL.OnlineSubgradientPolicy.canonicalPolicy':'Default','BanditRL.OnlineLearning.comparatorRegret':'Comparator','SourceSubdifferential':'Supports','(E := E)':''}
for a,b in mapping.items():local=local.replace(a,b)
packet='Decode only this packet and all18 unproved headers. Do not read source identity/proofs/verdicts/otherfiles. For each statement reconstruct all seven semantic slots; distinguish actual and universal laws, finite-loss coercion, same trajectory, universal performance input and information order. No proof/source acceptance claim.\n\n```lean\nnoncomputable section\nopen Set Finset\nvariable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]\n'+imported+local+'\n'
for k,(n,h) in enumerate(headers.items(),1):
 for a,b in mapping.items():h=h.replace(a,b)
 packet+=h.replace('theorem '+n+' ','theorem F'+str(k).zfill(2)+' ',1)+'\n\n'
packet+='```\n';write(r/'blind-packet-v1.md',packet)
jwrite(r/'blind-neutral-name-map.json',{ 'F'+str(i+1).zfill(2):n for i,n in enumerate(headers)})
rows=[]
for p in [r/'source-binding.json',r/'source-pages.txt',r/'source-card.md',r/'blind-packet-v1.md',r/'leaves/target-v1.lean.txt',r/'leaves/context-v1.lean.txt',r/'leaves/types-v1.lean',r/'draft-types-01.log',r/'draft-types-01-exit.json']+sorted(d.glob('*')):
 rows.append({'path':p.as_posix(),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
jwrite(r/'contract-source-inputs-v1.json',{'rows':rows,'row_count':len(rows)})
jwrite(r/'draft-freeze.json',{'stage':'draft','context_sha256':hashlib.sha256(ctx.encode()).hexdigest(),'headers':{n:json.loads((d/(n+'.json')).read_text())['statement_hash'] for n in headers},'body_proof_started':False,'context_types_compiled':True,'raw_inputs':len(rows)})
jwrite(r/'proof-obligations.json',{'task':'ONLINE-LINEARIZATION-20261004','stage':'draft','required':[{'name':n,'state':'unproved','terminal':n in ['regret_comparison','regret_transfer','canonical_regret_comparison']} for n in headers],'chapter_complete':False,'book_complete':False})
write(r/'source-review-packet-v1.md','Distinct anti-anchored source reviewer: search for mismatch in all18 headers, actual context definitions and typed probe. Read/verify every rawrow in contract-source-inputs-v1.json plus blind-reconstruction-v1.md and blind-receipt-v1.json. Pinned source Section2.3 printed22/PDF34; source-pages/sourcecard. Seven slots pertarget, source-vs-library structural labels, genuine strict-past learner/current support recursion, finite EReal values, same learner/sequence, no future/comparator input; played versus off-pathlaw; universalOLO performance input is reduction contract, not asserted producer of that OLO guarantee. Return accepted/rejected/accepted-with-explicit-delta and immutable raw receipt. Draft contract only, no proof/public/canary/compilation acceptance. Do not edit frozen rows. Formalizer/root and separate blind/source automated actors medium, no human/externalreview claim.\n')
print('prepared',len(headers),'headers',len(rows),'rawrows')
