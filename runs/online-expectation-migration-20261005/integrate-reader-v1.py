"""Correct only the expectation reader after the distinct body verdict."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-EXPECTATION-MIGRATION-20261005'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x,existing=False):
 p=Path(p);assert p.exists() if existing else not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as handle:
  if isinstance(x,str):handle.write(x.rstrip('\n')+'\n')
  else:json.dump(x,handle,ensure_ascii=False,indent=2);handle.write('\n')
r=load(run/'public-body-receipt-v1.json');freeze=load(run/'draft-freeze-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not r.get('mathematical_repairs',r.get('required_mathematical_repairs',[])) and sha(r['report'])==r['report_sha256']
reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
for row in load(run/'public-body-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256']
for p,h in reviewed.items():assert sha(p)==h,p
write(run/'body-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),report_sha256=r['report_sha256'],retained_proofs=7,retained_definitions=3,new_proofs=0,required_reader_corrections=r.get('required_reader_corrections',[])))
snap={row['path']:row for row in load(run/'historical-raw-supersession-v1.json')['rows']}
for p in ['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:assert sha(p)==snap[p]['raw_sha256']==sha(snap[p]['snapshot'])
p=Path('website/content/readings.json');d=load(p);x=next(row for row in d['readings'] if row['slug']=='online-expectation')
x['primary']['sections']='Section2.1.1, necessary representation dependency of Theorem2.9; seven library helpers and three definitions, not printed source results'
x['notation'][0]['meaning']='Total ENNReal lower integral of f.toENNReal on arbitrary measure/sample space; no function measurability, integrability, probability or normalization premise in the definition.'
x['notation'][1]['meaning']='Total ENNReal lower integral of (-f).toENNReal, the magnitude of the negative part. A separate Jensen producer must prove this finite under source assumptions.'
x['notation'][2]['meaning']='Unnormalized EReal difference of the two parts. Legitimate signed-integral interpretation needs appropriate measurability and at least one finite part. Both infinite gives formal bottom here, not a valid signed expectation.'
x['algorithm']['steps'][0]['detail']='Both parts are total nonnegative extended lower integrals, even without a supplied measurability premise; this does not certify classical measurable expectation semantics.'
x['algorithm']['steps'][1]['detail']='Actual Bochner Integrable real f includes a.e. strong measurability and finite norm integral, proving both parts finite and exact embedded-real compatibility. This does not extend to a nonintegrable default-zero Bochner integral. Jensen must separately produce finite negative part via an affine minorant; loss integrability is not a source premise.'
x['algorithm']['steps'][2]['detail']='A.e. nonnegativity alone gives the formal negative-zero reduction without extra measurable/integrable premises. The positive-infinite helper separately retains negative part != infinity, excluding both-infinite arithmetic.'
card=x['source_theorems'][0];card['label']='Theorem2.9: separately mapped parent Jensen endpoint'
card['relationship']='This page revalidates seven representation helpers and three definitions, not seven printed results or Jensen itself. The historical shared theorem_2_9 proof is retained and compiled; it and its affine-minorant/nonclosed-barycenter dependencies require separate distinct semantic revalidation. This foundation receipt does not accept that parent or its negative-part producer.'
card['local_status']['label']='Representation foundations recompiled; historical parent retained for separate revalidation'
card['local_status']['boundary']='Only seven retained library proofs and three unchanged definitions are reviewed here; source Theorem2.9, later dependencies, Chapter2 and the whole book are not accepted by this package.'
example=x['worked_example'];example['intro']='The identity integral over dirac(-1)+dirac(3) is 2 under a measure of mass TWO, not probability expectation1. Growing n+1 under infinite counting measure tests the positive-infinite signed-integral branch; neither law is a Jensen probability instance.'
example['steps'][0]['detail']='Both signed atoms contribute to the unnormalized integral2. There is no division by total mass2 in these definitions.'
example['steps'][2]['detail']='Counting measure has infinite mass and is not a probability law. The historical Source Jensen geometric probability canary is separate and requires its own distinct revalidation.'
example['boundary']='Only these nonprobability foundation canaries are freshly replayed in this package. The probability-law infinite-loss and nonclosed-domain parent canaries remain separate review obligations.'
assert len(x['notation'])==3 and len(x['teaching_route'])==4
write(p,d,True)
p=Path('website/content/highlights.json');d=load(p)
for x in d['highlights']:
 if x.get('chapter')!='online-expectation':continue
 n=x['full_name'].rsplit('.',1)[-1]
 x['position']='Library representation dependency of Orabona v10 Theorem2.9, printedp11/PDF23; not a printed foundation theorem.'
 x['why']='Supplies the separately mapped Jensen parent with finite or infinite signed-integral representation; this migration does not accept that parent.'
 if n=='positiveIntegral_coe_ne_top':
  x['plain']='Actual Bochner Integrable real f proves finite positive part under an arbitrary measure.'
  x['lean_notes']='Integrable includes a.e. strong measurability and finite norm integral; neither pointwise finite values nor a total default-zero integral suffices. The separate negative-part helper has the same premise. No probability/mass normalization is assumed.'
 elif n=='signedExpectation_coe_integrable':
  x['plain']='For actually integrable real f, the unnormalized signed representation equals the embedded real Bochner integral.'
  x['lean_notes']='Both part integrals are proved finite before EReal subtraction is identified with the real integral. No nonintegrable Bochner-zero extension. The mass-two identity canary gives integral2, not probability expectation1.'
 elif n=='signedExpectation_of_nonneg':
  x['plain']='A.e. nonnegative extended f has negative part0 and the total signed representation equals its positive lower integral.'
  x['lean_notes']='Formal identity requires only a.e. nonnegativity, with no extra measurable/integrable premise and positive infinity allowed. Appropriate measurability remains separate for classical signed-integral interpretation; a.e. is relative to arbitrary measure.'
 else:
  assert n=='signedExpectation_eq_top'
  x['plain']='Positive part infinity and the explicit finite-negative-part premise give signed value positive infinity.'
  x['lean_notes']='Both-infinite is excluded: pinned total top-top=bottom is not a legitimate signed expectation. Counting-measure n+1 is a nonconstant finite-valued infinite-integral canary, not a probability Jensen instance. Parent convexity/integrable-X must separately produce finite negative part.'
 x['intuition']=x['plain']
write(p,d,True)
p=Path('website/content/chapters.json');d=load(p);x=next(row for row in d['chapters'] if row['slug']=='online-expectation')
x['summary']='Arbitrary-measure signed-integral representation: actual integrable-real compatibility, a.e. nonnegative reduction and infinite-positive/finite-negative branch; total both-infinite arithmetic is not a valid expectation.'
x['completion_definition']='Seven retained library proofs and three unchanged definitions, zero new proof code/nodes. This package does not accept parent Jensen, its negative-part producer, Chapter2 or the whole book.'
x['completion_blockers']=['The historical full Jensen proof and its affine-minorant/nonclosed-barycenter dependencies need separate distinct revalidation; source loss-integrability cannot be added and probability-law canaries are separate.', 'Chapter2 mandatory total remains incomplete/null; all remaining main-text obligations and the whole Goal remain open.']
write(p,d,True)
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
 old=load(snap[p]['snapshot']);new=load(p)
 assert [row for row in old[k] if row.get(key)!='online-expectation']==[row for row in new[k] if row.get(key)!='online-expectation']
 for extra in set(old)-{k}:assert old[extra]==new[extra]
public=Path('BanditRLProof/OnlineExpectation.lean');tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(public.read_text(encoding='utf-8'))==tokens((run/'original-OnlineExpectation.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
paths=[public.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json'];names=['BanditRL.OnlineConvex.'+n for n in freeze['headers']]
c=load('research-wiki/contribution-contracts/online-optimality-migration-20261005.json')
c.update(id=task,frontier_cell='online-expectation',target='Distinctly revalidate seven retained representation helpers/three definitions and qualify their existing Book reader; no proof code/new nodes or Jensen acceptance.',affected_files=paths,declarations=names)
c['source']['anchor']='Theorem2.9 printed11/PDF23 necessary signed-integral representation dependency; helpers not printed source statements and parent not accepted here.'
c['reuse_plan']=dict(classification='reuse',decision='reuse_existing',searched_existing=['Actual10public declarations/native types, pinned Bochner/positive-negative/EReal APIs and fresh compiled shared-root10node317edge scopedgraph.'],reused_declarations=names,new_shared_declarations=[],known_consumers=['Tests.OnlineExpectationCanary','BanditRLProof.OnlineJensen'],planned_consumers=['Separate source Jensen migration after remaining dependency gates'],no_duplicate_wrapper=True,decision_reason='Seven unchanged proofs/three unchanged definitions/zero new proof code/nodes, one shared project.')
c['semantic_roundtrip'].update(status='accepted',verdict=r['verdict'],remaining_semantic_delta='Distinct source-contract/body review of representation dependencies under arbitrary measures; total arithmetic versus signed-integral interpretation/nonprobability canary/source parent boundary explicit. Final corrected reader/package review pending; no human/external/runtime attestation.')
c['graph_contribution'].update(lean_graph='reuse-only',focus_targets=names,functor_reason='Retained signed-integral foundations; no cross-setting functor claim.',visual_review='Fresh compiled10node317directedge scopedgraph; corrected reader/registry/site gates pending.')
c['progress_updates'].update(teaching_route='updated: same online-expectation route/4highlights/4links, arbitrary-measure/legitimate finite-part/actual Integrable/nonprobability/parent boundaries qualified.',website_surfaces=paths[1:])
c['truth_boundary']='Seven retained proofs/three retained definitions/zero new proof code/nodes. Arbitrary measure/no normalization; total lower integrals and EReal difference are not automatic measurable signed expectations. Actual Integrable real-f required for finite compatibility; a.e.nonnegative formal reduction and explicit finite-negative infinite-positive branch retained. Mass-two/counting canaries not probability Jensen instances. Parent source negative-part finiteness/Jensen/dependency distinct reviews remain required; Chapter2/allChapters1-16/main/live not complete or updated.'
c['verification'].update(focused_checks=['Fresh actual module/byte-exact fullcanary/18named standard3-or-none axioms/10native guards; all10headers/definition/proof tokens fixed.'],bandit_check='Fresh combined root/Tests/full harness pending recorded integration.',site_build='Clean lean-verified build only after fresh applicable combined gate.',site_check='Same10canonicalnodes/10806oldIDsURLs/source-qualified reader checks pending.')
write('research-wiki/contribution-contracts/online-expectation-migration-20261005.json',c)
write(run/'reader-integration-v1.json',dict(status='integrated-package-pending',affected_files=paths,selected_route='online-expectation',required_reader_corrections_addressed=True,all_other_Book_subtrees_unchanged=True,all_headers_definition_proof_tokens_canary_preserved=True,retained_proofs=7,retained_definitions=3,new_proofs=0,new_registry_nodes=0,parent_accepted=False,chapter_complete=False,goal_complete=False))
with Path('MANIFEST.md').open('a',encoding='utf-8',newline='\n') as handle:
 handle.write('\n- Expectation representation migration 20261005: seven retained proofs/three definitions, zero new proof code/nodes; arbitrary-measure/finite-part/actual Integrable/nonprobability canary and parent-Jensen boundaries qualified. Distinct contract/body reviewed; final reader/integration/PR gates pending. See runs/online-expectation-migration-20261005.\n')
print('Six expectation reader qualifications integrated; allotherBooks/10headers/fullcode/canary preserved.')
