"""Apply seven reviewed source/producer/expectation qualifications to the Jensen reader only."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-JENSEN-MIGRATION-20261005'
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
write(run/'body-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),report_sha256=r['report_sha256'],retained_proofs=2,retained_definitions=0,new_proofs=0,required_reader_corrections=r.get('required_reader_corrections',[])))
snap={row['path']:row for row in load(run/'historical-raw-supersession-v1.json')['rows']}
for p in ['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:assert sha(p)==snap[p]['raw_sha256']==sha(snap[p]['snapshot'])
p=Path('website/content/readings.json');d=load(p);x=next(row for row in d['readings'] if row['slug']=='online-jensen')
x['primary']['sections']='Section2.1.1, one printed Theorem2.9 and its necessary finite-negative-part library producer'
x['notation'][0]['meaning']='Total positive-minus-negative EReal expression outside admissible inputs. Here the actual producer proves finite negative part, so both-infinite ambiguity is excluded and positive-infinite loss expectation is legitimate. No finite expected loss or use of toReal at infinity as a finite loss is promised.'
x['notation'][1]['meaning']='Source E[X] exists means ordinary finite Lebesgue coordinate expectations. In finite-dimensional Euclidean space these correspond to genuine Bochner Integrable X via integrable_pi_iff/integrable_piLp_iff; principal-value means and total nonintegrable-zero fallback are excluded. The convex loss need not be integrable.'
x['notation'][2]['meaning']='With global no-bottom, f<top means finite values; X belongs almost surely, not necessarily everywhere. Domain need not be closed, measurable as a set or full-dimensional. Actual finite-dimensional real normed E retains MeasurableSpace/BorelSpace; no supplied CompleteSpace/inner-product parameter or infinite-dimensional claim. Probability mass1, separate Measurable f, Measurable X and Integrable X remain explicit.'
x['algorithm']['steps'][0]['detail']='Probability and AE domain membership supply a nonempty-domain witness. The actual global affine minorant gives a(X)+b, genuinely integrable because X is integrable. Pointwise domination bounds the negative loss part by this real affine negative part, whose integral is proved finite. Negative-part finiteness is produced, not assumed.'
x['algorithm']['steps'][1]['detail']='An infinite positive integral with the produced finite negative integral makes the signed expectation legitimately positive infinity. This branch supplies f(mean)≤top; it does not separately promise mean-domain membership or a finite expected loss.'
x['algorithm']['steps'][2]['detail']='If the positive integral is finite, measurability and AE finite embedding produce Y=toReal(f(X)). Actual finite positive/negative parts make their maxima integrable, hence their difference Y integrable. The genuinely integrable pair (X,Y) lies AE in the original convex real epigraph; its mean stays in that potentially nonclosed epigraph. Pair-integral and AE signed real-integral compatibility yield the exact source inequality.'
assert len(x['notation'])==3 and len(x['teaching_route'])==2
card=x['source_theorems'][0]
card['relationship']='One printed Theorem2.9 plus its necessary negative-part library producer, not two printed results. Source finite-mean wording is explicitly interpreted as ordinary finite Lebesgue coordinate expectations, corresponding to genuine Bochner Integrable X in finite-dimensional Euclidean spaces. Actual finite-dimensional real normed measurable/Borel generality includes those source instances. No loss-integrability, closedness, lsc, full-dimensional-domain or finite-support-law assumption is added. Historical compilation and this distinct contract/body review remain separate from the final recorded package decision.'
card['contract']['model']='Finite-dimensional real normed measurable/Borel vectors, including source Euclidean spaces, under an arbitrary probability law of mass1.'
card['contract']['assumptions']='Global no-bottom measurable convex extended loss; separate measurable X, genuinely Integrable X and AE below-top domain membership. No loss-integrability or closed/full-dimensional-domain premise.'
card['contract']['parameters']='Arbitrary probability space and finite dimension, including dimension0; no supplied CompleteSpace/inner-product parameter, no infinite-dimensional source claim.'
card['local_status']['label']='Source Jensen and produced finite negative part, freshly recompiled'
card['local_status']['boundary']='Exactly one source theorem and one necessary producer. Frozen producer measurability premises stay in its signature even where its body does not use them. Final package evidence is recorded separately; Chapter2 mandatory total remains null/incomplete and the whole book Goal active.'
example=x['worked_example']
example['steps'][0]['detail']='The normalized geometric probability masses sum to one; the actual anonymous IsProbabilityMeasure instance is retrieved and included in the named audit.'
example['takeaway']='Genuinely integrable input and finite loss at every sample do not force finite expected loss; the source terminal permits legitimate positive infinity after producing finite negative part.'
example['boundary']='The whole unchanged canary has13proofs/3definitions/2probability instances. Separate normalized halfdirac1+halfdirac3 proves mean2/square expectation5 and a nonconstant finite source instance; separate lower-dimensional nonclosed coordinate/top-outside loss uses a genuine probability law, measurable loss and AE domain membership. Counting-measure foundation examples are not these source probability tests. All20named audits include both actual anonymous probability instances.'
write(p,d,True)
p=Path('website/content/highlights.json');d=load(p)
for x in d['highlights']:
 if x.get('chapter')!='online-jensen':continue
 n=x['full_name'].rsplit('.',1)[-1]
 if n=='jensen_negativeIntegral_ne_top':
  x['plain']='Under the source probability/convex-loss/integrable-input hypotheses, produce a finite negative loss integral; do not assume loss integrability.'
  x['why']='Makes the possibly infinite signed loss expectation legitimate before the source Jensen terminal is used; this library prerequisite is not a second printed theorem.'
  x['position']='Necessary library producer for Orabona v10 Theorem2.9, printedp11/PDF23.'
  x['proof_idea']='Obtain a nonempty-domain witness from probability AE membership, invoke actual global affine minorant, prove its composition with X integrable, and pointwise dominate the negative loss part by that real affine negative part.'
  x['lean_notes']='Actual finite-dimensional real normed measurable/Borel E, probability mass1, global no-bottom/convexity, Measurable f/Measurable X/Integrable X/AE domain are retained; the first two measurability premises may be unused by this body but remain frozen. No supplied finite-negative-part, closedness, lsc, full-dimensional-domain, finite-support or loss-integrability premise. Source finite Lebesgue coordinate mean corresponds to genuine Integrable X, not principal value/nonintegrable default zero.'
 else:
  assert n=='theorem_2_9'
  x['plain']='For measurable convex loss and a genuinely integrable random vector with AE finite loss under a probability law, f(mean) is at most the possibly positive-infinite expected loss.'
  x['why']='Closes the one source Theorem2.9 endpoint after its actual finite-negative-part producer, without adding integrability of the loss.'
  x['position']='Orabona v10 Theorem2.9, printedp11/PDF23; finite-mean interpretation and normed-space generality explicitly reviewed.'
  x['proof_idea']='Invoke the actual negative-finite producer; infinite positive part yields legitimate signed top. Otherwise actual measurable AE-real Y and finite positive/negative parts produce Integrable Y, before the actual original nonclosed epigraph barycenter of (X,Y), pair integral and signed-real compatibility produce the source inequality.'
  x['lean_notes']='Finite-dimensional real normed measurable/Borel E, no supplied CompleteSpace/inner-product parameter or infinite-dimensional endpoint. Source E[X] exists means ordinary finite Lebesgue coordinate mean: no principal-value/total nonintegrable-zero fallback. No loss-integrability/closedness/lsc/full-dimension/finite-support premise, or assumed epigraph mean/Integrable Y oracle. The top branch gives le_top, no added finite mean-loss/domain promise; both-infinite total subtraction is unreachable. Two teaching links are not a full/canary graph export. Three actual probability canaries and20named audits include both anonymous probability instances.'
 x['intuition']=x['plain']
write(p,d,True)
p=Path('website/content/chapters.json');d=load(p);x=next(row for row in d['chapters'] if row['slug']=='online-jensen')
x['summary']='One source Jensen theorem and its produced finite-negative-part prerequisite: genuine finite-mean input, measurable convex extended loss, arbitrary probability law, and possibly infinite expected loss on a nonclosed domain.'
x['completion_definition']='One Orabona Theorem2.9 terminal and one necessary producer, with explicit finite Lebesgue mean interpretation; two retained proofs/zero new code/nodes. This is not completion of Chapter2 or the whole book.'
x['completion_blockers']=['Other mandatory Chapter2 main-text/necessary appendix obligations and historical source migrations still require matching/revalidation; some already have compiled code, so they are not uniformly unproved.', 'Chapter2 mandatory total remains incomplete/null; Chapters3-16 stay mandatory unenumerated and the persistent whole-book Goal active.']
write(p,d,True)
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
 old=load(snap[p]['snapshot']);new=load(p)
 assert [row for row in old[k] if row.get(key)!='online-jensen']==[row for row in new[k] if row.get(key)!='online-jensen']
 for extra in set(old)-{k}:assert old[extra]==new[extra]
public=Path('BanditRLProof/OnlineJensen.lean');tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(public.read_text(encoding='utf-8'))==tokens((run/'original-OnlineJensen.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
paths=[public.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json'];names=['BanditRL.OnlineConvex.'+n for n in freeze['headers']]
c=load('research-wiki/contribution-contracts/online-minorant-migration-20261005.json')
c.update(id=task,frontier_cell='online-jensen',target='Distinctly revalidate source Theorem2.9 and its actual finite-negative-part producer, then qualify the existing reader; exact two proof bodies/headers and whole probability canary fixed.',affected_files=paths,declarations=names)
c['source']['anchor']='Theorem2.9 printed11/PDF23 and necessary negative-part producer; one printed source result, finite Lebesgue mean interpretation explicitly reviewed.'
c['reuse_plan']=dict(classification='reuse',decision='reuse_existing',searched_existing=['Actual2public types/headers; pinned Pi/PiLp integrability equivalence, real finite-part integrability and global integral_pair APIs; existing real-valued closed-set mathlib Jensen requires different assumptions. Actual compiled scoped2node350directedge environment graph.'],reused_declarations=names,new_shared_declarations=[],known_consumers=['Tests.OnlineJensenInfinite','Tests.OnlineJensenFinite','Tests.OnlineJensenNonclosed'],planned_consumers=['Future Chapter3 online-to-batch source matching only after Chapter2 gate; no concurrent Chapter3 proof writing.'],no_duplicate_wrapper=True,decision_reason='Two unchanged proof bodies/no production definitions/new code/nodes; accepted shared minorant/barycenter/representation dependencies, one Lean graph.')
c['semantic_roundtrip'].update(status='accepted',verdict=r['verdict'],remaining_semantic_delta='Source finite Lebesgue mean interpretation and finiteD realnormed measurable/Borel generality explicit; distinct contract/body accepted, final corrected reader/package pending. No human/external/runtime attestation.')
c['graph_contribution'].update(lean_graph='reuse-only',focus_targets=names,functor_reason='Retained source Jensen expectation producer/epigraph argument; no certified cross-setting functor or graph-derived discovery claim.',visual_review='Actual scoped2nodes350directtype/valueedges, including definitions, not full/canary export; two shared public nodes/reader links. Registry/site pending.')
c['progress_updates'].update(teaching_route='updated: same online-jensen two links/highlights, one source result plus actual prerequisite; seven source-mean/type/producer/expectation/canary/completion qualifications.',website_surfaces=paths[1:])
c['truth_boundary']='Two retained proofs/no production definitions/new code/nodes. Source finite Lebesgue coordinate mean interpretation ↔ genuine finiteD Bochner Integrable, excludes principal-value/nonintegrable-zero fallback. Actual finiteD realnormed MeasurableSpace/Borel/probability1; no supplied CompleteSpace/innerproduct/infiniteD claim. Actual integrable affine negative-part producer; positive∞ permitted; finite parts produce actual Integrable Y/original nonclosed epigraph mean. No lossIntegrable/closed/lsc/full-dimensional/finite-support or desired-terminal oracle. Whole13proofs3defs2probinstance canary and20named v2 audits/2guards; v1 name-lookup failures preserved, no mathematical repair. Final package gate pending; Chapter2null/wholeGoal/main/live remain incomplete/unchanged.'
c['verification'].update(focused_checks=['Fresh retained module and byte-exact whole probability canary13proofs3defs2instances; actual20unique named v2 standard3-or-none axiom audit and2nativeguards. Failed v1 guessed instance audit preserved; actual names retrieved, no target/body/test repair.'],bandit_check='Fresh combined root/Tests/full harness pending recorded integration.',site_build='Clean lean-verified build only after fresh applicable combined Lean gate.',site_check='Same2canonicalnodes/10806oldIDsURLs/source-qualified reader checks pending.')
write('research-wiki/contribution-contracts/online-jensen-migration-20261005.json',c)
write(run/'reader-integration-v1.json',dict(status='integrated-package-pending',affected_files=paths,selected_route='online-jensen',required_reader_corrections_addressed=True,all_other_Book_subtrees_unchanged=True,all_headers_proof_tokens_canary_preserved=True,retained_proofs=2,retained_definitions=0,new_proofs=0,new_registry_nodes=0,source_terminal_accepted=False,chapter_complete=False,goal_complete=False))
with Path('MANIFEST.md').open('a',encoding='utf-8',newline='\n') as f:f.write('\n- Source Jensen migration20261005: one Theorem2.9 and its actual finite-negative-part producer, two retained proofs/zero new code/nodes; finite Lebesgue mean interpretation, finiteD measurable/Borel scope, true producer/finite-positive/infinite-positive branches and three probability canaries qualified. Distinct contract/body reviewed; final integration/reader/PR pending. See runs/online-jensen-migration-20261005.\n')
print('Seven Jensen reader corrections applied; other Books/two frozen bodies/whole canary preserved.')
