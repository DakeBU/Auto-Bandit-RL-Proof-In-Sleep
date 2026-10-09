from common import *
sys.path.insert(0,str(ROOT))
from tools import bandit
assert Path.cwd()==ROOT and sys.argv[1:]==['reference-index']
bandit.RETRIEVAL_INDEX_DIR=RUN/'reference-index-v1'
bandit.MANIFEST=RUN/'own-artifact-journal.md'
raise SystemExit(bandit.main())
