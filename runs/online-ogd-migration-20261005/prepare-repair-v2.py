"""Freeze a new source-premise repair; the rejected v1 inputs stay untouched."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent
contract=Path('docs/contracts/online-ogd-migration-v2')
contract.mkdir(parents=True,exist_ok=True)
def write(p,v):
    with Path(p).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(v,str):f.write(v+'\n')
        else:json.dump(v,f,indent=2);f.write('\n')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
rejected=json.loads((run/'source-contract-receipt-v1.json').read_text(encoding='utf-8'))
assert rejected['verdict']=='rejected'
for row in rejected['reviewed_files']:assert sha(row['path'])==row['sha256'],row['path']
assert sha(rejected['report'])==rejected['report_sha256']
context='''import BanditRLProof.OnlineGradientDescentVariable
import BanditRLProof.OnlineConvexFirstOrder
import Mathlib.Tactic

noncomputable section
open Set Finset
open scoped InnerProductSpace
namespace BanditRL.OnlineGradientDescentSource
open BanditRL.OnlineGradientDescent
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def FeasibleRegularLoss (V : Domain E) (f : E → ℝ) : Prop :=
  ConvexOn ℝ V.carrier f ∧ ∀ x ∈ V.carrier, DifferentiableAt ℝ f x

def SourceRegularLoss (V : Domain E) (f : E → ℝ) : Prop :=
  ∃ U : Set E, IsOpen U ∧ V.carrier ⊆ U ∧
    ConvexOn ℝ V.carrier f ∧ DifferentiableOn ℝ f U
'''
write(contract/'context.lean.txt',context+'\nend BanditRL.OnlineGradientDescentSource')
headers={
 'source_to_feasible':'theorem source_to_feasible (V : Domain E) (f : E → ℝ) (hf : SourceRegularLoss V f) : FeasibleRegularLoss V f',
 'regular_to_feasible':'theorem regular_to_feasible (V : Domain E) (f : E → ℝ) (hf : RegularLoss V f) : FeasibleRegularLoss V f',
 'linear_regular':'theorem linear_regular (V : Domain E) (g : E) : RegularLoss V (fun z => inner ℝ g z)',
 'gradient_linear':'theorem gradient_linear (g x : E) : gradient (fun z => inner ℝ g z) x = g',
}
old=json.loads(Path('docs/contracts/online-ogd-migration-v1/native-headers-v1.json').read_text())
for name in ['first_order','lemma_2_12','theorem_2_13_fixed','variable_one_step',
             'theorem_2_13_variable_bound','theorem_2_13_variable','equation_2_1_distance','equation_2_1']:
    headers[name]=old[name]['statement'].replace('RegularLoss','FeasibleRegularLoss')
assert len(headers)==12
for name,header in headers.items():write(contract/(name+'-header.txt'),header)
write(run/'leaves/targets-v2.lean.txt',context+'\n\n'.join(h+' := by\n' for h in headers.values())+
      '\nend BanditRL.OnlineGradientDescentSource')
def split_statement(h):
    rest=re.sub(r'^theorem\s+\w+\s*','',h);depth=0
    for i,ch in enumerate(rest):
        if ch in '([{':depth+=1
        elif ch in ')]}':depth-=1
        elif ch==':' and depth==0:return rest[:i].strip(),rest[i+1:].strip()
    raise AssertionError(h)
probe=context+'\n'
for i,(name,h) in enumerate(headers.items()):
    binders,result=split_statement(h)
    probe+='def Type'+str(i+1)+' : Prop := '+('∀ '+binders+', ' if binders else '')+result+'\n'
    probe+='#check @Type'+str(i+1)+'\n'
probe+='end BanditRL.OnlineGradientDescentSource\n'
write(run/'leaves/native-types-v2.lean',probe)
neutral=(run/'neutral-context.lean.txt').read_text(encoding='utf-8').rsplit('end NeutralMigration',1)[0]
neutral=neutral.replace('namespace NeutralMigration','namespace NeutralRepair')
definitions={'Domain':'Q0','project':'Q1','RegularLoss':'Q2','step':'Q3','iterate':'Q4','regret':'Q5',
             'iterateVariable':'Q6','regretVariable':'Q7','FeasibleRegularLoss':'Q8','SourceRegularLoss':'Q9'}
names={n:'M'+str(i+1).zfill(2) for i,n in enumerate(headers)}
replacements=dict(definitions,**names)
def change(t):
    for a,b in sorted(replacements.items(),key=lambda kv:-len(kv[0])):t=re.sub(r'\b'+re.escape(a)+r'\b',b,t)
    return t
newdefs=context.split('def FeasibleRegularLoss',1)[1]
neutral+='\ndef '+change('FeasibleRegularLoss'+newdefs)
neutralheaders={names[n]:change(h) for n,h in headers.items()}
neutralprobe=neutral+'\n'
for n,h in neutralheaders.items():
    b,t=split_statement(h)
    neutralprobe+='def '+n+'Type : Prop := '+('∀ '+b+', ' if b else '')+t+'\n#check @'+n+'Type\n'
neutralprobe+='end NeutralRepair\n'
write(run/'leaves/neutral-types-v2.lean',neutralprobe)
write(run/'blind-packet-v2.md',
      'Fresh restricted pass: read only this packet. Reconstruct twelve unproved headers M01-M12 in seven '
      'semantic slots, with all quantifiers, regularity, conclusion/constants/indexing/information order '
      'and excluded regimes. No source/provenance/name map/proofs/logs/reviews. No acceptance claim.\n\n'
      'Scoped context:\n```lean\n'+neutral+'\n```\n\nUnproved headers:\n```lean\n'+
      '\n\n'.join(neutralheaders.values())+'\nend NeutralRepair\n```')
write(run/'private-neutral-name-map-v2.json',dict(definitions=definitions,targets=names))
write(run/'draft-freeze-v2.json',dict(stage='draft-repair',context_sha256=sha(contract/'context.lean.txt'),
    headers={n:hashlib.sha256(h.encode()).hexdigest() for n,h in headers.items()},
    source_pdf_sha256='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17',
    old_source_review_raw_rows_unchanged=len(rejected['reviewed_files']),old_headers_unchanged=16,
    old_bodies_unchanged=True,new_public_module='BanditRLProof/OnlineGradientDescentSource.lean',
    definitions=2,new_proofs_started=False,
    uncompiled_target_file='Empty by markers only in .txt for actual native header extraction; no proof claim'))
write(contract/'source-intent.md',
    'Version2 repair after independent source audit rejection of the unrestricted source-to-old-RegularLoss '
    'implication. Same Orabona v10 Algorithm2.1/Prop2.11/Lemma2.12/Theorem2.13 bothbranches/Eq2.1, '
    'printed12-15/PDF24-27; supporting gradient printed11/PDF23. The chapter game declares losses V→R '
    '(printed8/PDF20); an ambient real extension carries the specified derivative. Values outside the '
    'differentiability neighborhood are totalized without needing convexity or differentiability there. '
    'Source convexity restricted to convex V and differentiability on an arbitrary open U containing V '
    'imply FeasibleRegularLoss; U is NOT required convex. The latter predicate is a genuine weaker '
    'interface: convexity on V plus ambient DifferentiableAt at every feasible point. source_to_feasible '
    'must prove this implication. regular_to_feasible preserves historical API compatibility, never the '
    'false reverse implication. Complete real Hilbert generalization specializes to finite Euclidean space. '
    'No compact/diameter assumption for fixed endpoint, and no gradient/support/regret desired-bound premise. '
    'Bounded decreasing branch keeps prescribed positive adjacent nonincrease schedule, T>=1 and final '
    'eta(T-1); exact Metric.diam needs boundedness. T0 fixed extension allowed; tuned D,G,T all positive, '
    'bounds refer to actual tuned trajectory, no future-gradient learner. Source losses/initialpoint '
    'and comparator ordering, BOTH one-step inequalities and negative residuals unchanged. '
    'Existing definitions/project/step/iterate/iterateVariable are reused; no duplicate public algorithm. '
    'Two affine helpers prove true linear regularity/gradient and permit reusing old lemma2.12 quadratic '
    'component without a duplicate projection theory. Twelve library refinements are not twelve printed '
    'source results. Old16 declarations/contracts remain historically valid but incomplete for broad '
    'source scope until this new adapter/producer chain passes all gates. A new reviewed comment/reader '
    'qualification may be applied later with exact raw old snapshot; no silent historical weakening.')
write(run/'20_middle_architect-v2.md',
    'Single lower repair route. Source open-neighborhood -> feasible-point regularity; old stronger '
    'RegularLoss -> new predicate separately. Reuse actual OnlineConvex.convex_gradient_lower_bound '
    'for first-order. Prove affine linear_regular via continuous dual linearity, and gradient_linear '
    'via its HasFDerivAt and Riesz dual. Instantiate old lemma2.12 on this genuine affine loss to '
    'reuse the purely quadratic projected-step producer; combine with new first-order, preserving both '
    'inequalities for the SAME original step. New fixed finite telescope and tuned bounds use actual '
    'old recurrence; variable accumulation reuses old weighted_potential_sum and source diameter. '
    'No old theorem body/header change; allowed later changes: new source module/Test/root imports, '
    'scoped reader correction and old comment qualification with supersession snapshots. Before proving, '
    'all12 native/neutral types, source/statement freeze, distinct fresh blind and source repair review '
    'must pass. First dependency-ready leaf is source_to_feasible, not an assumed support inequality.')
write(run/'proof-obligations-v2.json',dict(stage='draft-repair',
    required=[dict(name=n,state='unproved',statement_hash=hashlib.sha256(h.encode()).hexdigest()) for n,h in headers.items()],
    terminal=['lemma_2_12','theorem_2_13_fixed','theorem_2_13_variable','equation_2_1'],
    dependency_graph=dict(source_to_feasible=['DifferentiableOn.differentiableAt','IsOpen.mem_nhds'],
      regular_to_feasible=['ConvexOn.subset','DifferentiableOn.differentiableAt'],
      first_order=['OnlineConvex.convex_gradient_lower_bound'],
      linear_regular=['LinearMap.convexOn','ContinuousLinearMap.differentiable'],
      gradient_linear=['hasGradientAt_iff_hasFDerivAt','continuous dual derivative'],
      lemma_2_12=['first_order','linear_regular','gradient_linear','old lemma_2_12 quadratic component'],
      theorem_2_13_fixed=['new lemma_2_12','old iterate_mem','finite telescope'],
      variable_one_step=['new lemma_2_12','old iterateVariable_mem'],
      theorem_2_13_variable_bound=['variable_one_step','old weighted_potential_sum'],
      theorem_2_13_variable=['theorem_2_13_variable_bound','Metric.dist_le_diam_of_mem'],
      equation_2_1_distance=['theorem_2_13_fixed','actual gradient sum bounds'],
      equation_2_1=['equation_2_1_distance','a priori pairwise diameter']),
    old_v1_rejected=True,old_proof_bodies_true_under_written_predicate=True,
    chapter_complete=False,book_complete=False,goal_complete=False))
print(json.dumps(dict(status='new-v2-targets-frozen',target_count=12,old135_raw_rows_unchanged=True,
    new_proofs_started=False,first_ready_leaf='source_to_feasible')))
