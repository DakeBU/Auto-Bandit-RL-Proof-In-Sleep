"""Apply only the barycenter reader corrections after distinct body review."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-BARYCENTER-MIGRATION-20261005'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x,existing=False):
 p=Path(p);assert p.exists() if existing else not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
r=load(run/'public-body-receipt-v1.json');freeze=load(run/'draft-freeze-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not r.get('mathematical_repairs',r.get('required_mathematical_repairs',[])) and sha(r['report'])==r['report_sha256']
reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
for row in load(run/'public-body-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256']
for p,h in reviewed.items():assert sha(p)==h,p
write(run/'body-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),report_sha256=r['report_sha256'],retained_proofs=3,retained_definitions=0,new_proofs=0,required_reader_corrections=r.get('required_reader_corrections',[])))
snap={row['path']:row for row in load(run/'historical-raw-supersession-v1.json')['rows']}
for p in ['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:assert sha(p)==snap[p]['raw_sha256']==sha(snap[p]['snapshot'])
p=Path('website/content/readings.json');d=load(p);x=next(row for row in d['readings'] if row['slug']=='online-barycenter')
x['primary']['sections']='Section2.1.1, necessary nonclosed-barycenter dependency of Theorem2.9; three retained library results, not three printed source results'
x['notation'][0]['meaning']='Actual mean membership in s itself under a probability law, finite-dimensional real normed Borel space, genuine Integrable X and AE membership. No closedness, full ambient interior, boundedness, finite support or measurable-set premise.'
x['notation'][1]['meaning']='The geometric helper produces a nonzero continuous real linear map with a(y)<=a(x) on s, at a closure point outside ambient interior. Non-strict support at level a(x); no strict separation, relative-interior or zero-level normalization.'
x['notation'][2]['meaning']='Only the barycenter body centers X-mean, constructs a proper-kernel representative equal almost everywhere, proves its integrability and integral0, then uses strict finite-rank descent and affine preimage convexity.'
x['algorithm']['steps'][0]['detail']='Pinned closed-convex integral theory puts the mean in closure s. This intermediate result cannot replace the terminal membership in the original nonclosed s.'
x['algorithm']['steps'][1]['detail']='A hypothetical missing mean yields a nonzero support functional: Hahn-Banach for nonempty ambient interior, or a proper affine-span annihilator otherwise. Integrability, linear integral commutation and probability mass1 prove equality of functional VALUES a(X)=a(mean X) almost everywhere, not that X or the map a is constant.'
x['algorithm']['steps'][2]['detail']='Construct the centered proper-kernel lift, prove integrability by subtype isometry and its actual mean0 by integral commutation. Affine preimage convexity and AE membership survive; strict kernel-rank descent allows strong induction to conclude membership in s itself. These properties are produced, not assumed.'
card=x['source_theorems'][0];card['label']='Theorem2.9: separately mapped parent Jensen endpoint'
card['relationship']='This page revalidates three retained library dependencies, not three printed results or Jensen itself. Historical theorem_2_9 compilation is retained; source Jensen, its affine-minorant negative-part producer and probability-loss canaries require separate distinct revalidation. This receipt accepts only the barycenter dependency.'
card['local_status']['label']='Barycenter dependency recompiled; historical Jensen parent awaits separate revalidation'
card['local_status']['boundary']='This package does not accept Orabona Theorem2.9, Chapter2 or the whole book. Three retained proofs, no definitions or new proof code/nodes.'
example=x['worked_example'];example['intro']='The verified law is half dirac1 plus half dirac3, of total mass1. The distinct support vectors (1,0) and (3,0) lie in the nonclosed lower-dimensional ray {(x,0):x>0}; its mean is (2,0).'
example['takeaway']='The public general theorem reaches the original nonclosed ray, with genuine integrability and probability normalization. Its proof does not impose finite support on arbitrary X.'
example['boundary']='This freshly replayed nonconstant probability canary tests only the barycenter dependency. Source Jensen and its probability infinite-loss/nonclosed-domain canaries remain separate revalidation obligations.'
assert len(x['notation'])==3 and len(x['teaching_route'])==3
write(p,d,True)
p=Path('website/content/highlights.json');d=load(p)
for x in d['highlights']:
 if x.get('chapter')!='online-barycenter':continue
 n=x['full_name'].rsplit('.',1)[-1]
 x['position']='Library dependency of Orabona v10 Theorem2.9, printedp11/PDF23; not an additional printed source result.'
 x['why']='Supplies the nonclosed-convex-set barycenter needed by the separately mapped Jensen parent. This package does not accept Jensen.'
 if n=='supporting_functional_ae_eq_mean':
  x['plain']='Under a probability law and genuine Integrable X, an AE upper bound a(X)<=a(mean X) forces equality of those functional values almost everywhere.'
  x['lean_notes']='Complete real normed E is enough; no finite-dimensional or Borel structure on E is supplied. The given continuous real linear a may be zero. Neither X nor the linear map is proved constant. The proof uses actual integrable composition/equal integrals and probability constant mass1; there is no kernel lift or transparency option in this helper.'
 elif n=='supporting_functional_at_closure':
  x['plain']='In finite dimension, a closure point outside ambient interior has nonzero non-strict linear support at level a(x), even when ambient interior is empty.'
  x['lean_notes']='A deterministic geometric result, with no probability or measurability context. No closedness, full dimension, relative-interior replacement, strict separation, normalization or a(x)=0 claim. Nonempty interior uses Hahn-Banach; empty interior uses the proper affine-span direction and its nonzero annihilator. No centered lift/transparency option occurs here.'
 else:
  assert n=='integral_mem_convex_finiteDimensional'
  x['plain']='An integrable finite-dimensional random vector lying in convex s almost everywhere under a probability law has its actual mean in s itself.'
  x['lean_notes']='Actual public type retains MeasurableSpace E/BorelSpace E on finite-dimensional real normed E. No closedness, boundedness, finite support, MeasurableSet s, separate pointwise membership or full-interior premise. Only this body uses the centered proper-kernel AE representative, proves integrability and mean0, and strictly descends finite rank. Its local transparency setting assists elaboration without changing kernel checking. No arbitrary infinite-dimensional nonclosed-set conclusion is claimed.'
 x['intuition']=x['plain']
write(p,d,True)
p=Path('website/content/chapters.json');d=load(p);x=next(row for row in d['chapters'] if row['slug']=='online-barycenter')
x['summary']='Under a probability law, genuine integrability and AE membership in a finite-dimensional convex set put the mean in that set itself, without closedness or full ambient interior.'
x['completion_definition']='Three retained library proofs: actual finite-dimensional convex-set barycenter and two supporting helpers, zero new proof code/nodes. This is not completion of Orabona Theorem2.9 or all Chapter 2.'
x['completion_blockers']=['The historical source Jensen proof, affine-minorant negative-part producer and probability-loss canaries require separate distinct revalidation; this dependency receipt does not accept that parent.', 'Chapter2 mandatory total remains incomplete/null; remaining main-text obligations and the Chapters1-16 Goal stay open.']
write(p,d,True)
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
 old=load(snap[p]['snapshot']);new=load(p)
 assert [row for row in old[k] if row.get(key)!='online-barycenter']==[row for row in new[k] if row.get(key)!='online-barycenter']
 for extra in set(old)-{k}:assert old[extra]==new[extra]
public=Path('BanditRLProof/OnlineConvexBarycenter.lean');tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(public.read_text(encoding='utf-8'))==tokens((run/'original-OnlineConvexBarycenter.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
paths=[public.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json'];names=['BanditRL.OnlineConvex.'+n for n in freeze['headers']]
c=load('research-wiki/contribution-contracts/online-expectation-migration-20261005.json')
c.update(id=task,frontier_cell='online-barycenter',target='Distinctly revalidate three retained nonclosed convex-barycenter/support proofs and qualify their existing reader, without changing proof code/headers or accepting parent Jensen.',affected_files=paths,declarations=names)
c['source']['anchor']='Theorem2.9 printed11/PDF23 necessary actual-set barycenter dependency; three library proofs are not printed source statements and parent is not accepted here.'
c['reuse_plan']=dict(classification='reuse',decision='reuse_existing',searched_existing=['Actual3public types/headers and pinned closed-convex integral, supporting separation, integral commutation/AE equality and finite-rank APIs; fresh compiled3node544directedge scopedgraph.'],reused_declarations=names,new_shared_declarations=[],known_consumers=['Tests.OnlineConvexBarycenter','BanditRLProof.OnlineJensen'],planned_consumers=['Separate source Jensen migration after affine-minorant and remaining dependency gates'],no_duplicate_wrapper=True,decision_reason='Three unchanged proof bodies/no production definitions/zero new code/nodes, one shared project.')
c['semantic_roundtrip'].update(status='accepted',verdict=r['verdict'],remaining_semantic_delta='Distinct automated source-contract/body review of necessary library dependencies. Actual helper class scopes, AE functional-value equality, ambient non-strict support and genuine nonclosed actual-set membership explicit. Final corrected reader/package review pending; no human/external/runtime attestation.')
c['graph_contribution'].update(lean_graph='reuse-only',focus_targets=names,functor_reason='Retained nonclosed convex-barycenter dependency; no cross-setting functor claim.',visual_review='Fresh compiled3node544directedge scopedgraph, not full/canary export; corrected reader/registry/site pending.')
c['progress_updates'].update(teaching_route='updated: same online-barycenter route/3highlights/3links; each helper scope and actual-set/probability/integrability/AE/parent boundaries qualified.',website_surfaces=paths[1:])
c['truth_boundary']='Three retained library proofs/no production definitions/zero new code/nodes. Complete normed AE-value helper, finite-dimensional measure-free ambient support helper, finite-dimensional Borel-context probability/integrable/AE actual-set barycenter distinct. Genuine kernel-lift integrability/zero mean/rank descent produced; no closedness/closure-only/fullinterior or consumer shortcut. Nonconstant nonclosed lower-dimensional probability canary. Source Theorem2.9/affine minorant/Chapter2/wholeGoal/main/live not accepted or updated by this package.'
c['verification'].update(focused_checks=['Fresh public module/full byte-exact probability canary/14named standard3-or-none axioms including law_probability/3native guards; all3headers/proof tokens/canary bytes fixed.'],bandit_check='Fresh combined root/Tests/full harness pending recorded integration.',site_build='Clean lean-verified build only after fresh applicable combined gate.',site_check='Same3canonicalnodes/10806oldIDsURLs/source-qualified reader checks pending.')
write('research-wiki/contribution-contracts/online-barycenter-migration-20261005.json',c)
write(run/'reader-integration-v1.json',dict(status='integrated-package-pending',affected_files=paths,selected_route='online-barycenter',required_reader_corrections_addressed=True,all_other_Book_subtrees_unchanged=True,all_headers_proof_tokens_canary_preserved=True,retained_proofs=3,retained_definitions=0,new_proofs=0,new_registry_nodes=0,parent_accepted=False,chapter_complete=False,goal_complete=False))
with Path('MANIFEST.md').open('a',encoding='utf-8',newline='\n') as f:f.write('\n- Nonclosed convex-barycenter migration 20261005: three retained proofs/no production definitions/zero new code/nodes; complete-normed AE equality, finite-dimensional ambient support and probability/integrable/AE actual-set barycenter scopes qualified. Distinct contract/body reviewed; final reader/integration/PR pending. See runs/online-barycenter-migration-20261005.\n')
print('Five barycenter reader corrections integrated; other Books/3headers/proof tokens/canary preserved.')
