from common_v1 import *
fixed()
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash
targets=load(CONTRACT/'general-initialization-targets-stabilized-v3.json')['new_targets']
module=ROOT/'BanditRLProof/OnlineFTLInitializationRegret.lean'
assert len(targets)==4
for t in targets:assert statement_hash(lean_declaration_header(module,t['name']))==t['statement_hash']
write(RUN/'snapshots/general-init-four-body-candidate-v1.lean.raw',module.read_bytes())
code='import BanditRLProof.OnlineFTLInitializationRegret\n\nopen Filter BanditRL.OnlineLearning\n\n'
arguments=['initial y T hT','initial y T hT hi hy','initial y hi hy','initial y hi hy']
for t,args in zip(targets,arguments):
    code+='#check '+t['name']+'\n#print axioms '+t['name']+'\n'
    code+='example '+t['binders']+' :\n    '+t['conclusion']+' :=\n  '+t['name']+' '+args+'\n\n'
probe=RUN/'general-init-four-public-values-v1.lean'
write(probe,code)
gate('general-init-four-public-values-v1','lake','env','lean',probe)
log=(RUN/'general-init-four-public-values-v1.log').read_text('utf8')
assert log.count('depends on axioms:')+log.count('does not depend on any axioms')==4
assert 'sorryAx' not in log
for line in log.splitlines():
    if 'depends on axioms:' in line:
        used={x.strip() for x in line.split('depends on axioms:',1)[1].strip().strip('[]').split(',') if x.strip()}
        assert used <= {'propext','Classical.choice','Quot.sound'},line
old=(RUN/'export-readiness-graph-v1.lean').read_text('utf8')
old=old.replace('import BanditRLProof\n','import BanditRLProof\nimport BanditRLProof.OnlineFTLInitializationRegret\n',1)
old=old.replace('def targets : Array Name := #[','def targets : Array Name := #[\n'+','.join('`'+t['name'] for t in targets)+',')
old=old.replace('Lean.importModules #[{ module := `BanditRLProof }]','Lean.importModules #[{ module := `BanditRLProof }, { module := `BanditRLProof.OnlineFTLInitializationRegret }]')
old=old.replace('Fifty exact reused public Chapter1 proof targets plus selected support definitions.','Fifty unchanged reused Chapter1 public proof targets, four exact actual general-initial FTL bodies and selected support definitions.')
graph_script=RUN/'export-general-init-readiness-v1.lean'
write(graph_script,old)
graph_path=RUN/'compiled-general-init-readiness-graph-v1.json'
gate('export-general-init-readiness-v1','lake','env','lean','--run',graph_script,graph_path)
g=load(graph_path);names={n['name'] for n in g['nodes']}
assert len(names)==77 and all(n['has_value'] and n['module']!='unknown' for n in g['nodes'])
pairs=[('G002',targets[0]['name']),('G002','BanditRL.OnlineLearning.meanPredict_bestRegret_refined'),('G003',targets[0]['name']),('G003','BanditRL.OnlineLearning.meanPredict_bestRegret_bound'),('G003','BanditRL.OnlineLearning.comparatorRegret_le_squaredBestRegret'),('G003','BanditRL.OnlineLearning.noRegret_of_vanishing_bound'),('G004',targets[0]['name']),('G004','BanditRL.OnlineLearning.meanPredict_bestRegret_average_tendsto_zero'),('G004','tendsto_const_div_atTop_nhds_zero_nat')]
checks=[]
byid={t['id']:t for t in targets}
for id,parent in pairs:
    n=next(n for n in g['nodes'] if n['name']==byid[id]['name'])
    assert parent in n['value_dependencies'],(id,parent)
    checks.append(dict(public=n['name'],actual_direct_value_parent=parent))
for t in targets:
    fence=CONTRACT/('public-'+t['id']+'-fence-v1.json')
    gate('fence-'+t['id']+'-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','statement-fence','--declaration',t['name'],'--file',module,'--output',fence)
    assert load(fence)['statement_hash']==t['statement_hash']
    gate('safe-'+t['id']+'-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--fence',fence,'--lean-file',module)
fixed()
assert sha(module)==sha(RUN/'snapshots/general-init-four-body-candidate-v1.lean.raw')
write(RUN/'general-init-public-readiness-v1.json',dict(phase='candidate proof readiness only; distinct BODY and chapter gates pending',source_review_sha256=sha(RUN/'source-contract-receipt-v3.json'),source_review_correction_sha256=sha(RUN/'source-contract-receipt-correction-v4.json'),production_module_sha256=sha(module),exact_frozen_headers=4,actual_public_whole_type_value_witnesses=4,axiom_outputs=4,standard_only=True,focused_final='G004-focused-v2',selected_compiled_nodes=len(g['nodes']),coalesced_direct_TYPE_VALUE_edges=len(g['edges']),actual_required_value_pairs=checks,native_fence_and_safe_pairs=4,new_public_targets_compiled=4,new_required_source_objects_accepted=0,proof_total=None,chapter_complete=False,goal_complete=False))
print('Four frozen public proofs/whole-type witnesses/standard axioms/fences and9 direct VALUE pairs verified; BODY pending.',flush=True)
