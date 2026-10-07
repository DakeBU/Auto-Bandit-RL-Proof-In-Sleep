from common_accepted_v1 import *
accepted_fixed()
cmd=['git','rev-parse','origin/'+BASE_BRANCH]
observed=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
assert observed.returncode==128
write(RUN/'unfetched-stacked-ref-v4.log',observed.stdout)
write(RUN/'unfetched-stacked-ref-v4-exit.json',dict(command=cmd,exit_code=observed.returncode,log_sha256=sha(RUN/'unfetched-stacked-ref-v4.log'),reason='Fresh fetch succeeds but remote.origin.fetch intentionally tracks main only; this names no local origin stacked ref.',repair='Read the actual remote stacked branch with git ls-remote and corroborate with GitHub REST; preserve fetch configuration and prior helper.'))
fetchspec=subprocess.check_output(['git','config','--get-all','remote.origin.fetch'],encoding='utf8').strip()
actualremote=subprocess.check_output(['git','ls-remote','origin','refs/heads/'+BASE_BRANCH],encoding='utf8').split()[0]
assert actualremote==BASE
write(RUN/'stacked-remote-ref-repair-v5.json',dict(fetchspec=fetchspec,actual_remote_head=actualremote,expected=BASE,read_only_remote_verification=True,source_or_review_changed=False,chapter_complete=False,goal_complete=False))
source=(RUN/'publish-reviewed-v4.py').read_text(encoding='utf8')
prefix=source[:source.index("native('publication-PR-prose-repair-event-v4'")]
tail=source[source.index("basepr=json.loads"):]
tail=tail.replace("assert subprocess.check_output(['git','rev-parse','origin/'+BASE_BRANCH],encoding='utf8').strip()==BASE","assert subprocess.check_output(['git','ls-remote','origin','refs/heads/'+BASE_BRANCH],encoding='utf8').split()[0]==BASE")
prefix=prefix[:prefix.index("write(RUN/'publication-repair-accepted-v4.json'")]
exec(compile(prefix+'\n'+tail,'publish-reviewed-v4-tail-with-v5-remote-check','exec'))
