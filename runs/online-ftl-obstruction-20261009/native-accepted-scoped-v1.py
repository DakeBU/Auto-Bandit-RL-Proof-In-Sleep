from common_v1 import *
sys.path.insert(0,str(ROOT))
from tools import bandit
assert Path.cwd()==ROOT
# Preserve the original BODY/FINAL-bound six actual attempts including retained D4 failure byte-for-byte.
bandit.TRIAL_LOG=RUN/'accepted-scoped-trials-v1.jsonl'
raise SystemExit(bandit.main())
