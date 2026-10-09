from common_v1 import *
fixed()
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash
from tools.bandit import scan_lean_declarations
source=load(CONTRACT/'source-fingerprint-v1.json')
write(RUN/'root-source-pixel-review-v1.json',dict(actor='/root',personally_viewed_original_images=[dict(path=p['image_path'],sha256=p['image_sha256']) for p in source['source_pages']],image_count=16,
 actual_tool='view_image detail original',scope='All physical20-35 source pages; maintext ends before2.4 on34, exercises/history separate on34-35',
 findings='Source formulas, hypotheses, algorithm output/reveal/update order, negative terminal terms and numbered/unnumbered claims reread. Closure proofs left as exercises remain mandatory. Relative-interior footnote and 2D uncountable nonsmoothness are mandatory. Lookahead refers separately to prescient15.5.1; ordinary-gradient squares do not become negative under a causal unchanged OGD run.',
 source_sha256=PDF_SHA,chapter2_complete=False,whole_Goal_status='ACTIVE'))
prior_contract=ROOT/'docs/contracts/online-ogd-migration-v2'
names=['theorem_2_13_variable_bound','theorem_2_13_variable']
path=ROOT/'BanditRLProof/OnlineGradientDescentSource.lean';targets=[]
for name in names:
 old=load(prior_contract/(name+'.json'));header=lean_declaration_header(path,old['declaration'])
 assert header==old['statement'] and statement_hash(header)==old['statement_hash']
 targets.append(dict(name=old['declaration'],path=path.as_posix(),exact_header=header,statement_hash=statement_hash(header),file_sha256=sha(path),prior_contract=(prior_contract/(name+'.json')).as_posix(),prior_contract_sha256=sha(prior_contract/(name+'.json'))))
prior_names=['source-contract-receipt-v2.json','blind-receipt-v2.json','public-body-receipt-v2.json','final-reader-receipt-v2.json','accepted-decision-v2.json','pr-delivery-v2.json']
receipts=[]
for name in prior_names:
 p=ROOT/'runs/online-ogd-migration-20261005'/name;d=load(p)
 receipts.append(dict(path=p.as_posix(),sha256=sha(p),scope=d.get('scope',d.get('terminal_progress','Original actual delivery evidence; do not infer wholechapter acceptance')),verdict=d.get('verdict',d.get('stage'))))
prior_final=load(ROOT/'runs/online-ogd-migration-20261005/final-reader-receipt-v2.json')
bindings=[]
for item in prior_final['reviewed_files']:
 p=Path(item['path'])
 if not p.is_absolute():p=(ROOT/p).resolve()
 if p==path:
  assert sha(p)==item['sha256'];bindings.append(dict(path=p.as_posix(),current_sha256=sha(p),prior_final_sha256=item['sha256']))
assert bindings,'Current full source producer file must match actual prior FINAL, not headers only'
write(CONTRACT/'variable-ogd-prior-contract-reuse-v1.json',dict(phase='stabilized exact unchanged scoped prior contract/BODY/source review reuse; new chapter integration still draft',
 source_anchor='Theorem2.13 variable branch printed13/PDF25 and proof14/PDF26; Algorithm2.1 printed12/PDF24',source_sha256=PDF_SHA,
 targets=targets,prior_receipts=receipts,current_source_file_matches_prior_FINAL=bindings,
 semantic_signature=dict(objects='finite-dimensional real Euclidean source; existing complete real Hilbert generalization explicit',
 quantifiers='all positive finite T, fixed initial feasible x1, same eta/loss sequence, every feasible comparator u; no future-loss-selected algorithm',
 assumptions='nonempty closed convex V; bounded V for Metric.diam branch or explicit finite D all-pairs bound; positive nonincreasing finite-prefix eta; source regularity passed through actual ambient-source-to-feasible adapter',
 conclusion='same actual projected-gradient recurrence regret <= D^2/(2eta(T-1))+sum eta(t)||g(t)||^2/2 - ||x(T)-u||^2/(2eta(T-1))',
 constants='source rounds1..T correspondLean0..T-1, Leaniterate T is sourcex(T+1); nonzero terminal retained; zeroD allowed; positiveT excludes eta(-1) empty interpretation',
 information='current loss gradient used only after current output; strict-past prefix producer retained; deterministic pathwise guarantee',
 boundary='fixed-step remains unbounded-domain-capable; variable diameter bound not silently extended to unbounded V; actual current-run gradients; no wholeChapter2/Goal acceptance'),
 permitted_edits='OWN RUN scratch/readiness/fence/audit metadata only; no production/Test/root/source/pin/reader mutation',chapter2_complete=False,whole_Goal_status='ACTIVE'))
write(RUN/'20_architect-variable-reuse-v1.md','Select two exact unchanged public variable-step terminals as the first finite dependency-ready audit leaf. Their earlier distinct CONTRACT/BODY/FINAL/delivery and full current producer-file hash agree; no new semantic encoder/proof wrapper is needed merely to count a declaration. Reuse actual projection/feasibility/strict-prefix/first-order/source adapter/one-step/weighted potential/telescope. Record current whole-type/public-value and existing active-projection canary evidence by an actual new kernel readiness file; do not call this new mathematical progress or Chapter2 acceptance. Wider chapter contract remains draft until separate full-source audit. First lookahead source gap is separately pending classification; do not silently omit it.')
write(RUN/'30_lower-variable-readiness-v1.lean','''import Tests.OnlineGradientDescentSourceCanary

noncomputable section
open Set Finset BanditRL.OnlineGradientDescent
open BanditRL.OnlineGradientDescentSource
open scoped InnerProductSpace
namespace Chapter2CurrentReadiness
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

'''+ '\n\n'.join(t['exact_header'].replace('theorem '+t['name'].rsplit('.',1)[-1],'example',1)+' := by\n  exact '+t['name']+' '+(
 'V η loss x₁ hx₁ T hT hη hmono hloss D hdiam u hu' if t['name'].endswith('_bound') else 'V hV η loss x₁ hx₁ T hT hη hmono hloss u hu') for t in targets)+'''

-- Whole public values below are scratch witnesses, not new production declarations.
noncomputable def prefixValue := @BanditRL.OnlineGradientDescent.iterateVariable_prefix
noncomputable def feasibilityValue := @BanditRL.OnlineGradientDescent.iterateVariable_mem
noncomputable def sourceAdapterValue := @BanditRL.OnlineGradientDescentSource.source_to_feasible
noncomputable def concreteVariableValue := @Tests.OnlineGradientDescentSource.active_projection_variable
noncomputable def concreteNondegenerateValue := @Tests.OnlineGradientDescentVariable.nondegenerate

#check @BanditRL.OnlineGradientDescentSource.theorem_2_13_variable_bound
#check @BanditRL.OnlineGradientDescentSource.theorem_2_13_variable
#check @Tests.OnlineGradientDescentSource.active_projection_variable
#print axioms BanditRL.OnlineGradientDescentSource.theorem_2_13_variable_bound
#print axioms BanditRL.OnlineGradientDescentSource.theorem_2_13_variable
#print axioms prefixValue
#print axioms feasibilityValue
#print axioms sourceAdapterValue
#print axioms concreteVariableValue
#print axioms concreteNondegenerateValue
end Chapter2CurrentReadiness
''')
fixed();print('Exact prior variable contracts and full source BODY/FINAL binding verified; bounded current Lean readiness file prepared.')
