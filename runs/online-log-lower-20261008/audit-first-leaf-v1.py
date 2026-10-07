from common_v1 import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import normalize_statement, lean_declaration_header
fixed()
header=load(CONTRACT/'planned-public-headers-v1.json')['probability_mem']
assert lean_declaration_header(PUBLIC,'probability_mem') == normalize_statement(header)
write(RUN/'leaves/probability-canaries-v1.lean', '''import BanditRLProof.OnlineGuessingLogLower
open BanditRL.OnlineLearning.GuessingLower Set
example : polyaNext [] = (1 : ℝ) / 2 := by norm_num [polyaNext]
example : polyaNext [true] = (2 : ℝ) / 3 := by norm_num [polyaNext]
example : polyaNext [false] = (1 : ℝ) / 3 := by norm_num [polyaNext]
example (h : List Bool) : 0 < polyaNext h ∧ polyaNext h < 1 := probability_mem h
#check BanditRL.OnlineLearning.GuessingLower.probability_mem
#print axioms BanditRL.OnlineLearning.GuessingLower.probability_mem
''')
gate('probability-canaries-v1','lake','env','lean',RUN/'leaves/probability-canaries-v1.lean')
log=(RUN/'probability-canaries-v1.log').read_text(encoding='utf-8')
assert 'sorryAx' not in log
match=re.search(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
assert match and match[1]==PRE+'probability_mem'
axioms=re.sub(r'\s+','',match[2]).split(',')
assert set(axioms) <= {'propext','Classical.choice','Quot.sound'}
fence=RUN/'leaf-fences-v1/probability_mem.json'
native('probability-fence-v1','statement-fence','--declaration',PRE+'probability_mem',
       '--file',PUBLIC,'--source-assumption',header,'--output',fence)
native('probability-safe-v1','safe-verify','--fence',fence,'--lean-file',PUBLIC)
write(RUN/'probability-leaf-bindings-v1.json',dict(
    named_public_proof=PRE+'probability_mem',public_sha256=sha(PUBLIC),
    actual_header=lean_declaration_header(PUBLIC,'probability_mem'),
    frozen_exact_header_sha256=hashlib.sha256(header.encode()).hexdigest(),
    axioms=axioms,canaries=['empty=1/2','true=2/3','false=1/3','universal strict probability'],
    build_exit=load(RUN/'first-probability-build-v1-exit.json')['exit_code'],
    fence_sha256=sha(fence),safe_verify_exit=load(RUN/'probability-safe-v1-exit.json')['exit_code'],
    progress='compiled-leaf; actual probability producer closed',
    remaining_frozen_targets=15,source_claim_accepted=False,BODY_review='pending',
    chapter_complete=False,goal_complete=False))
native('probability-worker-trial-v1','trial-log','--task',TASK,'--role','lower',
       '--kind','build','--status','compiled','--run-id',RUN.name,'--lean',PUBLIC,
       '--verifier-evidence',RUN/'probability-leaf-bindings-v1.json',
       '--harness','hierarchical','--progress-class','compiled-leaf',
       '--new-declaration',PRE+'probability_mem','--notes',
       'One actual frozen proof, three numerical nondegenerate probability canaries, named kernel axioms and native statement fence/safe verifier. Normalization, moments, actual regret bridge and randomized lower terminal remain required; no source package/chapter/Goal acceptance.')
fixed()
print('First actual producer leaf verified; remaining law/lower chain still required.')
