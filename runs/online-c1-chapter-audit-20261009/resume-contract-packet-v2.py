from common_v1 import *
fixed()
write(RUN/'contract-packet-failure-v1.md','''prepare-contract-review-v1.py actually exited1 at its final input-file assertion, after writing the questions, proposed future scope, prior-dependency index and source-review packet. The typed-domain canary path was guessed incorrectly as Tests/OnlineRegretDomainsCanary.lean; rg located actual Tests/OnlineLearningRegretDomainsCanary.lean. All actual mathematical source/header/body bytes remain unchanged. V2 resumes only input-index creation using existing exact packet/draft files and correct actual path; no overwritten records or claimed chapter acceptance.''')
s=(RUN/'prepare-contract-review-v1.py').read_text(encoding='utf-8-sig')
code='from common_v1 import *\nfixed()\nprior=[Path(r["path"]) for r in load(RUN/"prior-dependency-decisions-v1.json")["rows"]]\n'+s[s.index('paths=list'):]
code=code.replace("Tests/OnlineRegretDomainsCanary.lean","Tests/OnlineLearningRegretDomainsCanary.lean")
write(RUN/'prepare-contract-review-v2.py',code)
fixed()
