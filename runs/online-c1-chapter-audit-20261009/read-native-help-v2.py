from common_v1 import *
fixed()
write(RUN/'native-help-lookup-failure-v1.md','''A read-only PowerShell help batch reported outer exit1. Actual top-level help listed the available native commands. Five guessed names lifecycle-record, add-task, proof-frontier, record-trial and retrieval-index were rejected by argparse; the memory-record help succeeded. No task/lifecycle/memory/retrieval mutation occurred. V2 uses actual listed new-task, trial-log, lifecycle-event, frontier-* and retrieval-record names and persists individual actual help exit/log receipts. These lookup failures are not Lean or chapter failures and cannot be called passed.''')
for command in ['new-task','conversion-window','trial-log','agent-note','agent-brief','lifecycle-event','frontier-dispatch','frontier-refresh','frontier-shadow','memory-record','retrieval-record','statement-fence','safe-verify','check']:
    gate('help-native-'+command+'-v2',sys.executable,'-B','-X','utf8','tools/bandit.py',command,'--help')
fixed()
