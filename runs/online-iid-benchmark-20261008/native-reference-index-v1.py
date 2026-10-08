from common_v1 import *
sys.path.insert(0,str(ROOT/'tools'))
import bandit
bandit.RETRIEVAL_INDEX_DIR=RUN/'native-reference-index'
raise SystemExit(bandit.main(['reference-index']))
