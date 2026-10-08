from leaf_tools_v1 import *

def start_leaf(index, body, description):
    headers_fixed(index)
    row=load(CONTRACT/'targets-v1.json')['targets'][index]
    native(row['id']+'-running-v1','trial-log','--task',TASK,'--role','lower',
        '--kind','attempt','--status','running','--run-id',RUN.name,'--lean',PUBLIC,
        '--attempt-id','SUCCESS-'+row['id']+'-V1','--harness','hierarchical',
        '--target-fingerprint',sha(CONTRACT/'targets-v1.json'),'--notes',description)
    prior=PUBLIC.read_text(encoding='utf8')
    write(RUN/'leaves'/('before-'+row['id']+'-v1.lean'),PUBLIC.read_bytes())
    assert prior.endswith('end BanditRL.OnlineLearning\n')
    PUBLIC.write_bytes((prior[:-len('end BanditRL.OnlineLearning\n')]+
        '/-- '+description+' -/\n'+row['header']+' := by\n'+body.rstrip()+'\n\n'+
        'end BanditRL.OnlineLearning\n').encode('utf8'))
    write(RUN/'leaves'/(row['id']+'-body-v1.lean'),PUBLIC.read_bytes())
    headers_fixed(index+1)
    return row
