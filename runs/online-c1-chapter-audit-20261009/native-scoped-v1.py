from common_v1 import *
sys.path.insert(0,str(ROOT))
from tools import bandit
assert Path.cwd()==ROOT
bandit.TRIAL_LOG=RUN/'trials.jsonl'
bandit.MANIFEST=RUN/'own-artifact-journal.md'
_original_store=bandit.lifecycle.SessionStore
class OwnSessionStore(_original_store):
    def __init__(self,root,session_id):
        super().__init__(root,session_id)
        self.events_path=RUN/'lifecycle-sessions.jsonl'
        self.state_path=RUN/'lifecycle-state.json'
bandit.lifecycle.SessionStore=OwnSessionStore
raise SystemExit(bandit.main())
