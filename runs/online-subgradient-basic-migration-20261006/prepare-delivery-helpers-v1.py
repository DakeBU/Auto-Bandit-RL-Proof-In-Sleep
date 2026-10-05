"""Prepare bounded subgradient acceptance and REST delivery helpers before use."""
from pathlib import Path
import ast,hashlib,json
run=Path(__file__).parent;src=Path('runs/online-closed-proper-migration-20261006');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
s=(src/'record-acceptance-v1.py').read_text(encoding='utf8')
for a,b in [('online-closed-proper','online-subgradient-basic'),('ONLINE-CLOSED-PROPER','ONLINE-SUBGRADIENT-BASIC'),('OnlineClosedProper','OnlineSubgradientBasic'),('CLOSED-PROPER-RETAINED','SUBGRADIENT-BASIC-RETAINED'),('sourceClosed_iff_lowerSemicontinuous','theorem_2_21'),('f989706461cb466bc290261f4845f113621e807d','283e359e2b85740ad557574d337d6f4a1d55fe8f'),("'lean:BanditRL.OnlineConvex.SourceClosed:compiled'","'lean:BanditRL.OnlineConvex.SourceSubdifferential:compiled'")]:s=s.replace(a,b)
nums={'retained_public_proofs':2,'retained_public_definitions':1,'retained_proofs':2,'retained_definitions':1,'public_canary_proofs':3,'named_axiom_audits':6,'native_guards':2,'source_numbered_anchors':2,'source_definitions':1,'source_numbered_indicator_examples':0,'remaining_chapter_legacy_migrations':8,'legacy_migrations_before':9,'legacy_remaining_before':9,'legacy_remaining_after':8,'compiled_scope_nodes':3,'compiled_scope_edges':320,'stacked_base_PR':166}
delta='Definition2.20 explicitly proper-source restriction; actual all-EReal support predicate is broader, faithful on proper specialization. Generic bottom/top all-vector degeneracy/domainincludesbottom/properfinite disclosed. Actual finite-witness point-domain theorem drops adjacent source convexity (stronger), exactly converts universalxg to domainsubset/outsideempty. T2.21 globallyREALf/ConvexV/forallx∈V existsg forallambienty global support; existence is printed hypothesis, not producedgeneralexistence/desiredconvexityinput. Actual weighted supportsincl0/1 and inner cancellation produceConvexOn. Arbitrary real-inner-product generalizes source finiteEuclidean; noCompleteFiniteD, Ezero nonempty/Vempty allowed. Two independentproofs/fullS shared/no mutual valueedges; sourceinterior+relativefootnote/T2.22/T2.23 REQUIRED separate.'
counts='Definition2.20, required adjacent outside-domain/dom-subdifferential inclusion group, Theorem2.21; printed16-17/PDF28-29.2numberedanchors+1required unnumberedgroup/2retainedproof1complete definition/0newmathcode,nodes.'
changes=[]
def put(n,v):
 lines=s.splitlines(keepends=True);a=sum(map(len,lines[:n.lineno-1]))+len(lines[n.lineno-1].encode()[:n.col_offset].decode());b=sum(map(len,lines[:n.end_lineno-1]))+len(lines[n.end_lineno-1].encode()[:n.end_col_offset].decode());changes.append((a,b,repr(v)))
for n in ast.walk(ast.parse(s)):
 if isinstance(n,ast.keyword) and n.arg in nums:put(n.value,nums[n.arg])
 elif isinstance(n,ast.Constant) and isinstance(n.value,str):
  v=n.value
  if v.startswith('Source Euclidean/stated Hausdorff'):put(n,delta)
  elif v.startswith('Orabona v10 four numbered'):put(n,counts)
  elif v.startswith('Definitions2.16/2.18') or v.startswith('Four numbered closed/proper anchors'):put(n,counts)
  elif v.startswith('ONLYOnlineSubgradientBasic;3retained'):put(n,'ONLYOnlineSubgradientBasic;2retainedproof1complete definition/0newproof gain,2numberedanchors+required adjacent domain group.')
  elif v.startswith('Seven CONTRACT/BODY'):put(n,'Eight CONTRACT/BODY corrections applied and distinctly rechecked.')
  elif v.startswith('Only four numbered anchors'):put(n,'Only Definition2.20/required adjacent domain observation/T2.21 accepted;2retainedproof1complete definition/0newmathcode,nodes. ')
  elif v.startswith(' Whole6canaryproofs'):put(n,' Whole3canaryproofs/6namedstandard3-or-none axes/no sorryAx/2guards,3nodes320directreferences notfull/canaryexport. Sequentialroot9089Tests9232/full466tests7existing skips/exactstackedcontribution/history/scopedCRLFawarewhitespace/cleanlocalsite3canonicalnodes10809oldIDsURLs0new/actualfirstviewportpassed. Eightreaderfixes distinctlyreviewed/no mathematics/testweakening. Legacy9->8ONLYOnlineSubgradientBasic;Chapter1migration/Chapter2mandatorytotalnull/incomplete/wholeGoalACTIVE/mainliveunchanged/PRpending/worktreeretained.')
  elif v.startswith('Accepted3actualheaders'):put(n,'Accepted2actualheaders/1complete support definition/current6@types/sourceblind/CONTRACT/BODY/FINAL/rawbindings/additiveoverlays. Actual finitewitness/domainconversion/ConvexOn/inner APIs,whole3canaries/6namedaxes/2guards/rootTestsfull/site3canonicalnodes10809IDsURLs/compiled3nodes320directreferences/no mutual2proofedges. Interior+relativeinteriorfootnote/T2.22/T2.23 required separately/Chapter1migration/wholeGoalACTIVE,noChapter3proofcompetition.')
  elif v.startswith('Same actualcompiled3proof2definition'):put(n,'Same actualcompiled2proof1complete definition bundle accepted after distinct source/reader/integrated gates;2numberedanchors+required adjacent domain group/0newproofgain, notChapter2/book/productivityexperiment.')
  elif v.startswith('Persistent Orabona Chapters1-16 Goal; only closed/proper'):put(n,'Persistent Orabona Chapters1-16 Goal; only subgradient-basic sourcepackage accepted,Chapter2/book incomplete')
  elif v=='Only closed/proper sourcepackage accepted; whole GoalACTIVE, stackedPRpending.':put(n,'Only subgradient-basic sourcepackage accepted; wholeGoalACTIVE,stackedPRpending.')
for a,b,v in sorted(changes,reverse=True):s=s[:a]+v+s[b:]
ast.parse(s);p=run/'record-acceptance-v1.py';assert not p.exists();p.write_bytes(s.encode())
t=(src/'create-pr-v1.py').read_text(encoding='utf8')
for a,b in [('base-PR165-fresh-v1','base-PR166-fresh-v1'),("repo+'/pulls/165'","repo+'/pulls/166'"),('f989706461cb466bc290261f4845f113621e807d','283e359e2b85740ad557574d337d6f4a1d55fe8f'),('codex/research-online-closed-proper-migration','codex/research-online-subgradient-basic-migration'),('codex%2Fresearch-online-closed-proper-migration','codex%2Fresearch-online-subgradient-basic-migration'),('codex/research-online-huber-migration','codex/research-online-closed-proper-migration')]:t=t.replace(a,b)
ast.parse(t);q=run/'create-pr-v1.py';assert not q.exists();q.write_bytes(t.encode())
o=run/'acceptance-REST-helpers-before-use-v1.json';assert not o.exists();o.write_bytes((json.dumps(dict(rows=[dict(path=x.as_posix(),sha256=sha(x)) for x in [p,q]],before_first_use=True,exact_base='283e359e2b85740ad557574d337d6f4a1d55fe8f'),indent=2)+'\n').encode())
print('Current scoped acceptance and exact REST PR helpers bound before use; no acceptance/push/API mutation.')
