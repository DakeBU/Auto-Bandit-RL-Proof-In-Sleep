from common_v1 import *
sys.path.insert(0,str(ROOT))
from tools import bandit
assert Path.cwd()==ROOT
# Same native CLI/schema; only the append-only attempt journal is owned by this run.
bandit.TRIAL_LOG=RUN/'trials.jsonl'
raise SystemExit(bandit.main())
