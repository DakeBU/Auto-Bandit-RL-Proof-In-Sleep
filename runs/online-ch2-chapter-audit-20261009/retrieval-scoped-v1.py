from common_v1 import *
sys.path.insert(0,str(ROOT))
from tools import bandit
assert Path.cwd()==ROOT
assert sys.argv[1] in ['reference-index','list-mathlib','list-papers','list-weapons','search-memory','list-lean-decls']
bandit.RETRIEVAL_INDEX_DIR=RUN/'retrieval-index-v1'
bandit.MANIFEST=RUN/'own-retrieval-journal-v1.md'
raise SystemExit(bandit.main())
