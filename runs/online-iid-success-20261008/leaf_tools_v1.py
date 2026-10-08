from common_reviewed_v1 import *

def start_leaf(index, body, description):
    headers_fixed(index)
    rows=load(CONTRACT/'targets-v1.json')['targets']
    row=rows[index]
    native(row['id']+'-running-v1','trial-log','--task',TASK,'--role','lower',
        '--kind','attempt','--status','running','--run-id',RUN.name,'--lean',PUBLIC,
        '--attempt-id','SUCCESS-'+row['id']+'-V1','--harness','hierarchical',
        '--target-fingerprint',sha(CONTRACT/'targets-v1.json'),'--notes',description)
    prior=PUBLIC.read_text(encoding='utf8')
    write(RUN/'leaves'/('before-'+row['id']+'-v1.lean'),PUBLIC.read_bytes())
    assert prior.endswith('end BanditRL.OnlineLearning\n')
    PUBLIC.write_text(prior[:-len('end BanditRL.OnlineLearning\n')]+
        '/-- '+description+' -/\n'+row['header']+' := by\n'+body.rstrip()+'\n\n'+
        'end BanditRL.OnlineLearning\n',encoding='utf8',newline='\n')
    write(RUN/'leaves'/(row['id']+'-body-v1.lean'),PUBLIC.read_bytes())
    headers_fixed(index+1)
    return row

def finish_leaf(index, version, description):
    headers_fixed(index+1)
    rows=load(CONTRACT/'targets-v1.json')['targets']
    row=rows[index]
    label=row['id']+'-'+version
    native(label+'-fence','statement-fence','--declaration',row['name'],'--file',PUBLIC,
        '--output',RUN/(label+'-fence.json'))
    native(label+'-safe-verify','safe-verify','--fence',RUN/(label+'-fence.json'),'--lean-file',PUBLIC)
    write(RUN/(label+'-kernel.lean'),'import BanditRLProof.OnlineGuessingIIDSuccess\n#check '+row['name']+
        '\n#print axioms '+row['name']+'\n')
    gate(label+'-kernel','lake','env','lean',RUN/(label+'-kernel.lean'))
    native(label+'-compiled','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled',
        '--run-id',RUN.name,'--lean',PUBLIC,'--attempt-id','SUCCESS-'+row['id']+'-'+version.upper(),
        '--harness','hierarchical','--target-fingerprint',sha(CONTRACT/'targets-v1.json'),
        '--new-declaration',row['name'],'--verifier-evidence',RUN/(row['id']+'-focused-build-'+version+'-exit.json'),
        '--progress-class','compiled-leaf','--obligations-before',str(4-index),
        '--obligations-after',str(3-index),'--notes',description)
    write(RUN/('30_worker-'+row['id']+'-'+version+'.md'),description+
        '\nActual body focused build/kernel, headerfence/safe scans separately pass. '
        'Exact terminal unchanged; BODY/source acceptance and combined gates still pending. Goal active.')
    write(RUN/('leaf-progress-'+row['id']+'-'+version+'.json'),dict(total_bounded_terminals=4,
        compiled=[r['name'] for r in rows[:index+1]],remaining=[r['name'] for r in rows[index+1:]],
        public_sha256=sha(PUBLIC),package_accepted=False,chapter_complete=False,goal_complete=False))
