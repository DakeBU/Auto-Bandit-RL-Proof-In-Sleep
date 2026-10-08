from common_v1 import *
sys.path.insert(0,str(ROOT/'tools'))
import bandit
# Actual project CLI implementation/scanner; redirect only generated retrieval outputs.
# ROOT, source paths, public declaration scanner and schema remain unchanged.
bandit.RETRIEVAL_INDEX_DIR=RUN/'native-reference-index'
raise SystemExit(bandit.main(['reference-index']))
