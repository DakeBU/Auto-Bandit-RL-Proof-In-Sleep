"""Audit actual theorem bodies, public canaries, kernels, frozen headers and value dependencies."""
from common_v2 import *
fixed(False,True);passed('public-canary-focused-v4-01')
r=load(RUN/'source-contract-receipt-v3.json');assert r['repair_verdict']['M1']['verdict']=='satisfied'
reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
rows=[]
for row in load(RUN/'source-contract-inputs-v3.json')['rows']:
 assert reviewed[row['path']]==row['sha256']==sha(row['path']),row['path'];rows.append(row)
write(RUN/'prior-contract-bindings-v1.json',dict(status='passed',rows=rows,original_context_failure_and_separate_M1_acceptance_preserved=True,immutable_journal_snapshots=True))
names=[PRE+n for n in load(CONTRACT/'headers.json')]
tests=re.findall(r'^theorem\s+(\w+)',CANARY.read_text(encoding='utf-8'),re.M);assert len(tests)==4
assert not re.findall(r'^(?:noncomputable\s+)?(?:def|abbrev)\s',CANARY.read_text(encoding='utf-8'),re.M)
targets=names+['ConvexUncountabilityProbe.'+n for n in tests];assert len(set(targets))==6
write(RUN/'public-named-declarations-v1.json',dict(production_proofs=names,production_definitions=[],canary_proofs=targets[2:],canary_definitions=[],canary_abbreviations=[],unique_named_type_checks=6,unique_named_kernel_checks=6,source_numbered_results=0,new_source_maintext_obligations=1))
write(RUN/'canary-plan-overlay-v2.json',dict(original_worker_plan='Three initial canary scenarios',current_canary_proofs=4,added_scenario='Every countable proposed exception set misses an actual ambient nonsmooth point, directly consuming the final public conjunction; finite endpoint pair/scalar-only substitution cannot certify this.',reason='Actual final producer instantiation and semantic exception-set interpretation, not implementation-mirroring regression tests.',frozen_public_headers_unchanged=True))
write(RUN/'leaves/actual-public-types-v1.lean','import Tests.OnlineConvexUncountabilityCanary\n'+'\n'.join('#check @'+n for n in targets)+'\n#print '+PRE+'coordinateAbsolute')
write(RUN/'leaves/public-all-axioms-v1.lean','import Tests.OnlineConvexUncountabilityCanary\n'+'\n'.join('#print axioms '+n for n in targets))
text=Path('runs/online-convex-nondifferentiability-20261007/leaves/export-public-dependencies-v1.lean').read_text(encoding='utf-8').replace('OnlineConvexNondifferentiabilityCanary','OnlineConvexUncountabilityCanary')
start=text.index('def targets : Array Name := #[');end=text.index(']\n',start)+1
text=text[:start]+'def targets : Array Name := #[\n '+',\n '.join('`'+n for n in targets)+']'+text[end:]
text=text.replace('selected actual convex nondifferentiability nodes','selected actual new uncountability proof nodes')
write(RUN/'leaves/export-public-dependencies-v1.lean',text)
write(RUN/'body-probes-before-first-use-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [RUN/'leaves/actual-public-types-v1.lean',RUN/'leaves/public-all-axioms-v1.lean',RUN/'leaves/export-public-dependencies-v1.lean']]))
gate('actual-public-types-v1-01','lake','env','lean',RUN/'leaves/actual-public-types-v1.lean')
gate('public-all-axioms-v1-01','lake','env','lean',RUN/'leaves/public-all-axioms-v1.lean')
gate('compiled-public-graph-v1-01','lake','env','lean','--run',RUN/'leaves/export-public-dependencies-v1.lean',RUN/'compiled-public-graph-v1.json')
for n,h in load(CONTRACT/'native-statement-fingerprints-v1.json').items():
 fence=RUN/('native-public-fences/'+n+'.json')
 native('public-fence-'+n+'-v1','statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',fence);assert load(fence)['statement_hash']==h
 native('public-safe-'+n+'-v1','safe-verify','--fence',fence,'--lean-file',PUBLIC,'--lean-file',CANARY)
raw=(RUN/'public-all-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
assert len(matches)==6 and {n for n,a in matches}==set(targets)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
g=load(RUN/'compiled-public-graph-v1.json');assert len(g['nodes'])==6 and all(n['has_value'] and n['kind']=='theorem' for n in g['nodes'])
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']}
first=PRE+'coordinate_segment_not_countable';final=PRE+'convex_uncountable_nondifferentiability'
required=[[first,'Cardinal.Real.Icc_countable_iff'],[first,'Set.Countable.preimage'],[first,'Set.Countable.mono'],[final,first],[final,PRE+'coordinate_absolute_convex'],[final,PRE+'convex_nondifferentiable_segment'],[final,'Set.Countable.mono'],['ConvexUncountabilityProbe.segment_nonsmooth_intersection_not_countable',first],['ConvexUncountabilityProbe.segment_nonsmooth_intersection_not_countable',PRE+'convex_nondifferentiable_segment'],['ConvexUncountabilityProbe.countable_exception_set_misses_nonsmooth_point',final]]
for p in required:assert tuple(p) in pairs,p
write(RUN/'compiled-dependencies-v1.json',dict(status='passed',nodes=6,proof_nodes=6,definition_nodes=0,direct_references=len(g['edges']),required_value_pairs=required,actual_producer_to_terminal_and_canary_pairs=True,full_registry_export=False))
m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/'public-canary-focused-v4-01.log').read_text(encoding='utf-8'));assert m
write(RUN/'public-actual-bindings-v1.json',dict(status='compiled',module_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),new_public_proofs=2,new_public_definitions=0,new_canary_proofs=4,canary_definitions=0,canary_abbreviations=0,named_type_checks=6,named_kernel_checks=6,axes=axes,native_guards=2,native_normalized_fingerprints=load(CONTRACT/'native-statement-fingerprints-v1.json'),raw_header_fingerprints=load(RUN/'draft-freeze-v1.json')['headers'],both_actual_raw_and_native_headers_verified=True,focused_jobs=int(m.group(1)),actual_source_terminal=final,source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('compiled-worker-trial-v3','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','UNCOUNTABLE-BODY-V3','--lean',PUBLIC,'--statement-hash',load(CONTRACT/'native-statement-fingerprints-v1.json')['convex_uncountable_nondifferentiability'],'--new-declaration',final,'--verifier-evidence',RUN/'public-actual-bindings-v1.json','--harness','hierarchical','--progress-class','compiled-leaf','--notes','Actual same-function source closed-segment/locus uncountability producers, zero definitions/two public proofs/four canaries/six standard-kernel/two guards and actual value graph. Body/combined/site/FINAL/native/PRpending; Chapter2/Goal not complete. Actual context/hash-adapter/focused failures retained, frozen targets unchanged.')
write(RUN/'proof-obligations-proving-v3.json',dict(stage='proving',terminal=dict(name=final,state='actual body compiled, distinct BODY review pending'),new_public_proofs=2,new_definitions=0,new_canary_proofs=4,required_other_maintext='Lemma2.31/OSD/linearization/Example2.32/unitanalysis/remainingChapter1/2 and necessaryappendices',source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed(False,True);print('Actual2publicproofs/0definitions/4canaryproofs/6standardkernel/2guards/6nodevaluegraph',len(g['edges']),'direct refs; BODY pending.')
