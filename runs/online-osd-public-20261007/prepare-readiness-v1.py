"""Actual local retrieval and all exact propositions, before current source stabilization."""
from common_v2 import *
fixed();passed('render-source-images-v2-01')
images=load(RUN/'source-image-bindings-v2.json');assert all(sha(x['path'])==x['sha256'] for x in images['images'])
write(RUN/'source-pixel-review-v1.json',dict(status='actual root viewed all four source PNGs',actor='/root',PDF_sha256=images['PDF_sha256'],images=images['images'],observations=['Definition2.20 for proper functions and global ambient supporting inequality visible on printed16.','Full arbitrary-current Lemma2.31 and OGD-to-OSD transfer visible on printed19.','Algorithm2.2 prints current feasible prediction before current loss and support/update on printed20.','Separate coarse fixed OSD formula and unit argument visible on printed21; dimensional transport is not this package.'],limits='These actual pages only, no general Book acceptance.'))
context=(CONTRACT/'actual-context-v1.txt').read_text(encoding='utf-8')
neutral=re.sub(r'/--?[\s\S]*?-/', '',context).replace('namespace BanditRL.OnlineSubgradientDescent','namespace NeutralUpdate')
assert 'Definition2.20' not in neutral and 'Orabona' not in neutral
headers=load(CONTRACT/'headers-v2.json');propositions=[];mapping=[]
for index,(name,header) in enumerate(headers.items(),1):
 tail=header[len('theorem '+name):].strip();depth=0;position=None
 for i,c in enumerate(tail):
  if c in '([{':depth+=1
  elif c in ')]}':depth-=1
  elif c==':' and depth==0:position=i;break
 assert position is not None and depth==0,name
 parameters=tail[:position].strip();conclusion=tail[position+1:].strip();neutral_name=f'P{index:02}'
 propositions.append('def '+neutral_name+' : Prop :=\n  ∀ '+parameters+',\n    '+conclusion)
 mapping.append(dict(neutral_name=neutral_name,actual_name=PRE+name,actual_raw_header_SHA256=load(CONTRACT/'raw-statement-fingerprints-v2.json')[name]))
checks='\n'.join('#print '+r['neutral_name'] for r in mapping)
borrowed='\n'.join(['#print BanditRL.OnlineGradientDescent.Domain','#print BanditRL.OnlineConvex.SourceProper','#print BanditRL.OnlineConvex.SourceSubdifferential','#print BanditRL.OnlineConvex.effectiveDomain','#check @BanditRL.OnlineGradientDescent.project_spec','#check @BanditRL.OnlineGradientDescent.proposition_2_11'])
write(RUN/'leaves/neutral-propositions-v1.lean',neutral+'\n'+'\n\n'.join(propositions)+'\n'+borrowed+'\n'+checks+'\nend NeutralUpdate\n')
write(RUN/'neutral-to-actual-map-v1.json',dict(rows=mapping,neutral_target_definitions_are_Prop_descriptions_not_proofs=True,all15_exact_actual_types_preserved=True))
names=[PRE+n for n in headers]
api_names=['BanditRL.OnlineConvex.subgradient_point_finite','BanditRL.OnlineGradientDescent.project_spec','BanditRL.OnlineGradientDescent.proposition_2_11','BanditRL.OnlineGradientDescent.weighted_potential_sum','norm_sub_sq_real','EReal.coe_toReal','Metric.dist_le_diam_of_mem','Real.sq_sqrt']
write(RUN/'leaves/actual-public-types-v1.lean','import BanditRLProof.OnlineSubgradientDescent\n'+'\n'.join('#check @'+n for n in names+api_names))
write(RUN/'readiness-probes-before-use-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [RUN/'leaves/neutral-propositions-v1.lean',RUN/'leaves/actual-public-types-v1.lean']],new_proof_bodies=False))
gate('neutral-propositions-v1-01','lake','env','lean',RUN/'leaves/neutral-propositions-v1.lean')
gate('actual-public-types-v1-01','lake','env','lean',RUN/'leaves/actual-public-types-v1.lean')
sys.path.insert(0,str(ROOT));from tools import bandit
import argparse
index=RUN/'retrieval-snapshot-v1';assert not index.exists();before=sha('MANIFEST.md');indexes={p.as_posix():sha(p) for p in Path('research-wiki/retrieval-index').glob('*.json')}
bandit.RETRIEVAL_INDEX_DIR=index;bandit.MANIFEST=RUN/'reference-index-manifest-v1.md';assert bandit.cmd_reference_index(argparse.Namespace())==0
assert sha('MANIFEST.md')==before
for p,h in indexes.items():assert sha(p)==h,p
write(RUN/'reference-index-scope-v1.json',dict(status='passed',implementation='Actual tools.bandit.cmd_reference_index with explicit output/MANIFEST adapter; CLI lacks scoped output option.',canonical_indexes_and_MANIFEST_unchanged=True,same_Lean_Book_registry=True,rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in sorted(index.glob('*.json'))]))
for label,command,args in [('mathlib-cards-v1-01','list-mathlib',[]),('paper-cards-v1-01','list-papers',[]),('weapon-cards-v1-01','list-weapons',[]),('memory-OSD-v1-01','search-memory',['OSD']),('declarations-OSD-v1-01','list-lean-decls',['OnlineSubgradientDescent']),('declarations-OSD-statements-v1-01','list-lean-decls',['OnlineSubgradientDescent','--statement'])]:native(label,command,*args)
native('retrieval-record-v1-01','retrieval-record','--task',TASK,'--query','exact arbitrary-current global-support step and canonical projected subgradient recursion/fixed variable residuals','--candidate',PRE+'lemma_2_31','--candidate',PRE+'iterate_prefix','--candidate',PRE+'regret_fixed','--candidate',PRE+'regret_variable','--candidate',PRE+'regret_tuned','--compiled-scratch',RUN/'leaves/actual-public-types-v1.lean','--provenance','Actual public15 types and eight pinned shared/Mathlib API types; unchanged producer modules; Orabona v10 printed16/19/20/21. Reuse, no duplicate or external unchecked dependency.','--output',RUN/'native-retrieval-v1.json')
packet='''Restricted neutral packet. Requested GPT6Astra/medium. Read ONLY this packet: no source/repository search, proof bodies, literature identity or previous verdict. Reconstruct P01-P15 individually in natural language/LaTeX and seven semantic slots; all needed structural definitions, borrowed actual types and elaboration output follow. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json adjacent, with raw packet/report SHA256, actor/requested settings and no runtime attestation/source acceptance. These are actual fully elaborated proposition definitions, NOT proofs of the targets. Mathematical definitions of choice/recursion are context, not assumed performance inequalities.

The real inner-product space is finite dimensional. Borrowed Domain is nonempty closed convex, and project_spec states actual nearest-point membership/minimization. Properness means nowhere bottom and finite somewhere; global supports test EVERY ambient comparison. Actual loss finiteness must precede real differences. Current selector takes f,x only, canonical noncomputable choice from an actual nonempty support set or otherwise zero. Initial value and schedule externally prescribed. Whole-function strict-prefix equality has its literal quantifier scope; a future-dependent external initial value is not constrained by this packet. All claims concern one specified choice/recursion, not every legal support policy or an executable oracle. Fixed0 horizon, variablepositive horizon/last played schedule, bounded diameter and actual same-run support bound are distinct hypotheses. No probability/filtration/measurability/anytime assertion. Audit arbitrary current query versus feasible comparator, ambient global support versus interior support, EReal finiteness versus unconditional toReal, actual algorithm versus supplied single-step performance premise, and all sign/constants/residual/index boundaries.

```lean
'''
packet+=(RUN/'leaves/neutral-propositions-v1.lean').read_text(encoding='utf-8')+'\n```\nActual standalone elaboration (each P is a proposition description only):\n```text\n'+(RUN/'neutral-propositions-v1-01.log').read_text(encoding='utf-8')+'\n```\n'
assert 'Orabona' not in packet and '2.31' not in packet and 'accepted' not in packet
write(RUN/'blind-packet-v1.md',packet)
write(RUN/'readiness-v1.json',dict(status='actual neutral context/all15 proposition descriptions/public15 types/shared8 API types and scoped native retrieval passed',proof_compiled_current_focused=False,existing_bodies_preexist_current_review=True,new_proofs=0,new_definitions=0,reuse_decision='reuse_existing',effective_headers='headers-v2.json',raw_metadata_repair_separate_source_review_pending=True,renderer_repaired_without_install=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
event('draft',dict(effective_actual_headers=(CONTRACT/'headers-v2.json').as_posix(),raw_metadata_repair=(RUN/'metadata-repairs-v2.json').as_posix(),retained_proofs=15,new_proofs=0,existing_bodies_preexist_current_review=True))
fixed();print('All15 actual propositions/public types/eight sharedAPI types and current retrieval ready; new source-blind packet prepared, current source stabilization/body gates pending.')
