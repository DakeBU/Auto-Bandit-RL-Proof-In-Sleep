from common import *
import ast
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash
review=load(RUN/'benchmark-BODY-canary-CONTRACT-review-v1.json')
window=review['approved_conditional_edit_window']
public=Path(window['path'])
headers=load(CONTRACT/'algorithm-canary-stabilized-v1.json')['exact_headers']
failed=RUN/'algorithm-canary-trace_canary-body-attempt-v2.lean.txt'
assert public.read_bytes()==failed.read_bytes()
assert load(RUN/'algorithm-canary-trace_canary-focused-build-v2.json')['actual_exit']==1
tree=ast.parse((RUN/'prove-algorithm-canary-v1.py').read_text(encoding='utf8'))
bodies=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign)
    and any(isinstance(t,ast.Name) and t.id=='bodies' for t in n.targets))
old='    norm_num only [feedback]\n'
assert bodies['trace_canary'].count(old)==2
bodies['trace_canary']=bodies['trace_canary'].replace(old,'    norm_num [feedback]\n')
bodies['trace_canary']=bodies['trace_canary'].replace('project V (x 1 3 - r 1 3 * (-4)) = 4 / 5','project V (x 1 3 + r 1 3 * 4) = 4 / 5')
write(RUN/'algorithm-canary-normal-form-repair-v3.json',dict(
    classification='Local tactic normal form: simplification changed x - eta*(-4) into x + eta*4; change pattern must match this normal form.',
    failure_receipt_sha256=sha(RUN/'algorithm-canary-trace_canary-focused-build-v2.json'),
    failed_snapshot_sha256=sha(failed),edit='Retain v2 conditional fix; change only last projection change pattern to x + eta*4. No statement or mathematical target change.',
    frozen_headers_unchanged=True,context_unchanged=True,source_mathematics_unchanged=True))
prefix=(RUN/'algorithm-canary-feedback_energy-body-attempt-v1.lean.txt').read_bytes().rsplit(b'end AdaptiveProbe\n',1)[0]
end=b'end AdaptiveProbe\n'
completed=['loss_regular','feedback_energy']
order=[n for g in window['ordered_groups'] for n in g]
for name in order[2:]:
    version='v3' if name=='trace_canary' else 'v1'
    if name!='trace_canary':
        assert public.read_bytes()==prefix+end
        event('algorithm-canary-'+name+'-proving-event-v1','proving',dict(current_leaf=name,
            allowed_file=public.as_posix(),preceding_focused_successes=completed))
    addition=b'\n'+Path(headers[name]['path']).read_bytes()+bodies[name].encode('utf8')
    public.write_bytes(prefix+addition+end)
    assert statement_hash(lean_declaration_header(public,name))==headers[name]['normalized_statement_hash']
    write(RUN/('algorithm-canary-'+name+'-body-attempt-'+version+'.lean.txt'),public.read_bytes())
    label='algorithm-canary-'+name+'-focused-build-'+version
    code,out=capture(label,'lake','build','Tests.OnlineAdaptiveOSDCanary',required=False)
    print(out if code else '\n'.join(out.splitlines()[-6:]),flush=True)
    if code:
        capture('algorithm-canary-'+name+'-failed-trial-'+version,sys.executable,'-B','-X','utf8',RUN/'native-scoped.py',
            'trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','failed',
            '--attempt-id','algorithm-canary-'+name+'-body-'+version,'--harness','hierarchical',
            '--obligations-before','7','--obligations-after',str(7-len(completed)),
            '--verifier-evidence',RUN/(label+'.json'),
            '--notes','Actual focused failure and complete snapshot retained; stop downstream append, frozen target/context unchanged.')
        sys.exit(code)
    assert 'Build completed successfully' in out
    write(RUN/('algorithm-canary-'+name+'-compiled-local-'+version+'.json'),dict(
        production_sha256=sha(public),header=headers[name],focused_receipt_sha256=sha(RUN/(label+'.json')),
        boundary='Focused only; public/axiom/VALUE/BODY review/full package gates open.'))
    completed.append(name)
    prefix+=addition
print('All seven unchanged complete canary bodies focused-compiled.',flush=True)
