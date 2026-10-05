"""Apply seven reader corrections after the distinct four-body verdict."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-MINORANT-MIGRATION-20261005'
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
write(run/'body-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),report_sha256=r['report_sha256'],retained_proofs=4,retained_definitions=0,new_proofs=0,required_reader_corrections=r.get('required_reader_corrections',[])))
snap={row['path']:row for row in load(run/'historical-raw-supersession-v1.json')['rows']}
for p in ['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:assert sha(p)==snap[p]['raw_sha256']==sha(snap[p]['snapshot'])
p=Path('website/content/readings.json');d=load(p);x=next(row for row in d['readings'] if row['slug']=='online-minorant')
x['primary']['sections']='Section2.1.1, necessary affine-support/minorant dependency of Theorem2.9; four retained library results, not four printed source results'
x['notation'][0]['meaning']='For the general terminal: global no-bottom and nonempty effective domain f<top, so domain points are genuinely finite. The finite-neighbourhood helper instead derives global no-bottom. All actual types use finite-dimensional real normed E, without supplied Borel, measurable, probability, inner-product or CompleteSpace classes; old Borel prose is historical stale evidence.'
x['notation'][1]['meaning']='A continuous real linear a plus real b lies below f at ALL ambient points, including top outside domain. The first two helpers additionally touch f at chosen x; the last two conclusions give only the global bound. a may be zero, without uniqueness, normalization, chosen boundary contact or quantitative norm bounds.'
x['notation'][2]['meaning']='The general producer generates intrinsic interior within the affine span, translates to its direction space and proves ambient interior there, then extends the actual linear functional and corrects the intercept. Ambient domain-interior assumptions remain in the two interior helpers; only domain nonempty is needed by the general terminal.'
x['algorithm']['steps'][0]['detail']='The finite-neighbourhood support helper needs actual eventually-everywhere finite values, not just finite at x. Epigraph boundary and nonzero separation produce a vertical coefficient proved negative before division, and derive global no-bottom. Fermat applies to auxiliary identity/linear functions, not loss differentiability. Domain-interior support produces that neighbourhood and touches f(x); the interior minorant helper directly drops contact from this support.'
x['algorithm']['steps'][1]['detail']='With no-bottom, convex real epigraph and nonempty domain only, generate intrinsic affine-span interior and restrict/translate f into its direction space. Actual ambient interior there permits the helper; no closedness, lsc, full ambient dimension, measurable loss or desired-minorant oracle is added.'
x['algorithm']['steps'][2]['detail']='Actually extend the restricted linear map to ambient finite-dimensional E, obtain continuity and adjust the intercept; prove the bound everywhere, with top outside domain handled explicitly. No particular boundary contact, nonzero output slope or quantitative bound is promised.'
assert len(x['notation'])==3 and len(x['teaching_route'])==2
card=x['source_theorems'][0];card['label']='Theorem2.9: separately mapped parent Jensen endpoint'
card['relationship']='This page revalidates four retained library dependencies, not four printed results or Jensen itself. The two teaching links are selected representatives, not the full public declaration set or exhaustive actual graph. Historical shared theorem_2_9 compilation remains separate; its finite-negative-part producer and source probability-loss canaries require distinct revalidation. No loss-integrability premise is added to that source parent.'
card['local_status']['label']='Affine-support/minorant dependency recompiled; historical Jensen parent awaits separate revalidation'
card['local_status']['boundary']='Only four retained library proofs, no production definitions or new proof code/nodes; this package does not accept source Jensen, Chapter2 or the whole book.'
example=x['worked_example'];example['intro']='The actual canary loss equals coordinate p.1 on the nonclosed lower-dimensional ray {(x,0):x>0}, and top outside. The base coordinate is finite everywhere in its upperAdd representation, so this example does not settle mixed-infinity conventions generally.'
example['takeaway']='The general public theorem handles this lower-dimensional nonclosed domain and gives an all-ambient affine inequality, without a chosen contact or nonzero-slope guarantee.'
example['boundary']='Six retained canary proofs and one definition verify formula, no-bottom, convexity, exact domain, global minorant and values1/3/top with nonclosed domain. This geometric dependency test is not a probability Jensen-loss test; parent and its probability canaries remain separate revalidation obligations.'
write(p,d,True)
p=Path('website/content/highlights.json');d=load(p)
for x in d['highlights']:
 if x.get('chapter')!='online-minorant':continue
 n=x['full_name'].rsplit('.',1)[-1]
 x['position']='Library dependency of Orabona v10 Theorem2.9, printedp11/PDF23; not an additional printed source result.'
 x['why']='Supplies a future integrable affine lower bound for the separately reviewed Jensen negative-part producer; this package does not accept that producer or Jensen.'
 if n=='affine_minorant_of_domain_interior':
  x['plain']='With no-bottom, convex real epigraph and an ambient domain-interior point, retain the global continuous affine bound from touching support.'
  x['proof_idea']='Directly obtain affine_support_of_domain_interior and discard its contact equality. The negative-vertical-coefficient producer is upstream in the finite-neighbourhood support helper.'
  x['lean_notes']='Finite-dimensional real normed E, no supplied Borel/measurable/probability/CompleteSpace/inner-product parameter. This helper still needs AMBIENT domain interior; it does not discharge the general terminal or claim relative interior suffices here. The output slope mayzero. Two curated teaching links represent four public results, not the exhaustive actual graph.'
  x['dependencies']=['BanditRL.OnlineConvex.affine_support_of_domain_interior']
 else:
  assert n=='convex_affine_minorant'
  x['plain']='No-bottom, convex real epigraph and merely nonempty effective domain yield a continuous real affine bound at every ambient point, including top outside.'
  x['proof_idea']='Generate intrinsic interior in the domain affine span, pull back to the translated direction space, prove its actual ambient interior, apply the helper, extend its linear functional and correct the intercept.'
  x['lean_notes']='No closedness, lsc, ambient-interior, full dimension, measurable loss or loss differentiability premise. Actual finite-dimensional real normed scope has no supplied Borel/probability/CompleteSpace/inner-product parameter; no arbitrary infinite-dimensional extension. Slopes mayzero; no uniqueness, normalization, chosen boundary contact or quantitative norm bound. The nonclosed lower-dimensional coordinate/topoutside canary tests only this geometric dependency.'
 x['intuition']=x['plain']
write(p,d,True)
p=Path('website/content/chapters.json');d=load(p);x=next(row for row in d['chapters'] if row['slug']=='online-minorant')
x['summary']='Four finite-dimensional affine-support/minorant library dependencies: finite-neighbourhood support derives no-bottom; general nonempty-domain minorant uses intrinsic affine-span interior without closedness or lsc.'
x['completion_definition']='Four retained proofs: two touching-support helpers and two global-minorant results, zero new proof code/nodes. The two teaching links are selected representatives. This is not completion of Orabona Theorem2.9 or Chapter2.'
x['completion_blockers']=['Historical source Jensen and its finite-negative-part producer/probability-loss canaries require separate distinct revalidation; loss integrability cannot be added to the source assumptions.', 'Chapter2 mandatory total remains incomplete/null; all remaining main-text obligations and the Chapters1-16 Goal remain open.']
write(p,d,True)
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
 old=load(snap[p]['snapshot']);new=load(p)
 assert [row for row in old[k] if row.get(key)!='online-minorant']==[row for row in new[k] if row.get(key)!='online-minorant']
 for extra in set(old)-{k}:assert old[extra]==new[extra]
public=Path('BanditRLProof/OnlineConvexMinorant.lean');tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(public.read_text(encoding='utf-8'))==tokens((run/'original-OnlineConvexMinorant.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
paths=[public.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json'];names=['BanditRL.OnlineConvex.'+n for n in freeze['headers']]
c=load('research-wiki/contribution-contracts/online-barycenter-migration-20261005.json')
c.update(id=task,frontier_cell='online-minorant',target='Distinctly revalidate four retained affine-support/minorant producer proofs and qualify their existing two-link reader, preserving all proof code/headers and leaving parent Jensen open.',affected_files=paths,declarations=names)
c['source']['anchor']='Theorem2.9 printed11/PDF23 necessary affine-support/minorant dependencies; four library proofs are not printed source results or parent acceptance.'
c['reuse_plan']=dict(classification='reuse',decision='reuse_existing',searched_existing=['Actual4types/headers and pinned intrinsic interior/local Fermat/linear extension/affine-isometry APIs; fresh compiled4node896directedge scopedgraph.'],reused_declarations=names,new_shared_declarations=[],known_consumers=['Tests.OnlineConvexMinorant','BanditRLProof.OnlineJensen'],planned_consumers=['Separate Jensen negative-part producer/source parent review'],no_duplicate_wrapper=True,decision_reason='Four unchanged proof bodies/no production definitions/zero new code/nodes, one shared project.')
c['semantic_roundtrip'].update(status='accepted',verdict=r['verdict'],remaining_semantic_delta='Distinct automated contract/body review of necessary library dependencies. Actual class scopes, finite-neighbourhood/no-bottom producer, touching versus minorant, ambient versus intrinsic interior, output slope and canary boundaries explicit. Final corrected reader/package pending; no human/external/runtime attestation.')
c['graph_contribution'].update(lean_graph='reuse-only',focus_targets=names,functor_reason='Retained finite-dimensional affine-support/minorant dependencies; no cross-setting functor claim.',visual_review='Actual scoped compiled4node896directedges, not full/canary export; two representative teaching links are not exhaustive actual graph. Corrected reader/registry/site pending.')
c['progress_updates'].update(teaching_route='updated: same online-minorant two representative links/highlights, four underlying public results; seven source/type/proof/canary/parent qualifications.',website_surfaces=paths[1:])
c['truth_boundary']='Four retained library proofs/no production definitions/newcode/nodes. FiniteD realnormed/no supplied Borel/probability/CompleteSpace parameters. Genuine finite-neighbourhood support produces nowhere-bottom/negative vertical coefficient using auxiliary derivatives; firsttwo touch, lasttwo only global bound and mayzero slope. General nonempty-domain producer generates intrinsic affine-span restriction/interior and actual extension/intercept correction without closedness/lsc/loss differentiability/desiredminorant oracle. Nonclosed lowerdimcoordinate/topoutside canary, not Jensenprobabilityloss test. Two links representative, all4 shared nodes retained. SourceJensennegativeproducer/parent/Chapter2/wholeGoal/main/live remain open or unchanged.'
c['verification'].update(focused_checks=['Fresh public module/full byte-exact nonclosedcanary/11named standard3-or-none axioms/4native guards; all4headers/proof tokens/canary bytes fixed.'],bandit_check='Fresh combined root/Tests/full harness pending recorded integration.',site_build='Clean lean-verified build only after fresh applicable combined gate.',site_check='Same4canonicalnodes/10806oldIDsURLs/source-qualified reader checks pending.')
write('research-wiki/contribution-contracts/online-minorant-migration-20261005.json',c)
write(run/'reader-integration-v1.json',dict(status='integrated-package-pending',affected_files=paths,selected_route='online-minorant',required_reader_corrections_addressed=True,all_other_Book_subtrees_unchanged=True,all_headers_proof_tokens_canary_preserved=True,retained_proofs=4,retained_definitions=0,new_proofs=0,new_registry_nodes=0,parent_accepted=False,chapter_complete=False,goal_complete=False))
with Path('MANIFEST.md').open('a',encoding='utf-8',newline='\n') as f:f.write('\n- Affine support/minorant migration 20261005: four retained proofs/no production definitions/newcode/nodes; actual finite-dimensional types, finite-neighbourhood no-bottom producer, contact/minorant and ambient/intrinsic distinctions qualified. Two representative links retain four shared public results. Distinct contract/body reviewed; final reader/integration/PR pending. See runs/online-minorant-migration-20261005.\n')
print('Seven minorant reader qualifications integrated; other Books/4headers/proof tokens/canary preserved.')
