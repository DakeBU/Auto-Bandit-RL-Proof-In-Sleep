from common_reader_v8 import *
import base64
fixed()
stage=[RUN.relative_to(ROOT).as_posix(),CONTRACT.relative_to(ROOT).as_posix(),CONTRIBUTION.relative_to(ROOT).as_posix(),
    *[Path(r['path']).relative_to(ROOT).as_posix() for r in load(RUN/'reader-integration-bindings-v5.json')['rows']],
    *[d+'/'+TASK+'.md' for d in ['tasks','proof-obligations','conversion-windows']]]
gate('post-native-stage-v5','git','add','--',*stage)
exceptions=load(RUN/'post-native-RAW-exception-addendum-v5.json')['exact_RAW_exceptions']
command=['git','diff','--cached',BASE,'--check']
p=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
observed={s.split(':',1)[0] for s in p.stdout.decode('utf8').splitlines() if ': trailing whitespace.' in s or ': new blank line at EOF.' in s}
allowed={Path(r['path']).relative_to(ROOT).as_posix() for r in exceptions}
assert observed==allowed and p.returncode==2
for r in exceptions:assert sha(r['path'])==r['sha256']
write(RUN/'post-native-cumulative-full-diff-v5.json',dict(command=command,actual_exit=p.returncode,stdout_base64=base64.b64encode(p.stdout).decode('ascii'),exact_exceptions=exceptions,full_unexcluded_zero=False))
p=subprocess.run(command+['--','.',*[':(exclude)'+f for f in sorted(allowed)]],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
write(RUN/'post-native-cumulative-scoped-diff-v5.json',dict(actual_exit=p.returncode,stdout_base64=base64.b64encode(p.stdout).decode('ascii')))
assert p.returncode==0
pending=[]
for label,cmd in [('post-native-stage-final-v5',['git','add','--',*stage]),('post-native-commit-v5',['git','commit','-m','Record Chapter1 source reconciliation and native review evidence'])]:
    log=ROOT/'tmp'/(TASK+'-'+label+'.log');assert not log.exists();tick=time.monotonic()
    with log.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
    assert child.returncode==0
    pending.append((label,log,dict(command=cmd,actual_exit=child.returncode,seconds=time.monotonic()-tick,log_sha256=sha(log))))
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
fixed();assert not SITE.exists()
cmd=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',str(SITE)]
log=ROOT/'tmp'/(TASK+'-site-build-v4.log');assert not log.exists();tick=time.monotonic()
with log.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
for label,path,r in pending:write(RUN/(label+'.log'),path.read_bytes());write(RUN/(label+'-exit.json'),r)
write(RUN/'site-build-v4.log',log.read_bytes())
write(RUN/'site-build-v4-exit.json',dict(command=cmd,actual_exit=child.returncode,seconds=time.monotonic()-tick,
    source_commit=head,actual_clean_at_site_start=True,log_sha256=sha(RUN/'site-build-v4.log'),
    applicable_combined_gate_sha256=sha(RUN/'combined-gates-inspected-v1.json'),deployed=False))
assert child.returncode==0
gate('site-check-v4',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',SITE)
gate('registry-check-v4',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v4.py')
for label,base in [('post-native-contributor-stack-v4',BASE),('post-native-contributor-main-v4','origin/main')]:
    gate(label,sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base)
    text=(RUN/(label+'.log')).read_text('utf8');assert 'Contributor contract: N/A' not in text and PUBLIC.relative_to(ROOT).as_posix() in text
write(RUN/'post-native-contributor-gates-v4.json',dict(actual_head=head,both_nonempty_bases_cover_new_production=True,
    actual_SITE4_source_commit=head,code_pins_unchanged=True,chapter_complete=False,goal_complete=False))
fixed()
print('Post-native status-only clean SITE4/registry/two nonempty contributor gates passed; capture/current pixels/post-native delivery review next.')
