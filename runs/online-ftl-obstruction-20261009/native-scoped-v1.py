from common_v1 import *
sys.path.insert(0,str(ROOT))
from tools import bandit
assert Path.cwd()==ROOT
bandit.TRIAL_LOG=RUN/'trials.jsonl'
raise SystemExit(bandit.main())
