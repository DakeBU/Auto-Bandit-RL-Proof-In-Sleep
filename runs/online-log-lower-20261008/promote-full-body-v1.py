from common_v1 import *
fixed()
assert load(RUN/'seeded-attempt-v3-exit.json')['exit_code']==0
assert PUBLIC.read_bytes()==(RUN/'snapshots/public-deterministic-v1.lean.raw').read_bytes()
source=(RUN/'leaves/seeded-v3.lean').read_text(encoding='utf-8')
source=source.replace('simp [List.count_cons, polyaNext, hl]','simp [polyaNext, hl]')
source=source.replace('simp [binaryStream, List.reverse_cons, List.getElem?_append_right]',
    'simp [binaryStream, List.reverse_cons]')
old='''    rw [heads_succ, ih]
    push_cast
    have hd : (T : ℝ) + 2 ≠ 0 := by positivity
    field_simp <;> ring'''
new=old.replace('field_simp <;> ring','field_simp')
assert source.count(old)==1
source=source.replace(old,new)
source=re.sub(r'(?m)^(\s*)field_simp <;> ring$',r'\1field_simp\n\1ring',source)
doc='''/-!
Constructive derived support for Orabona v10 Chapter 1, printed p4/PDF p16:
logarithmic dependence of guessing regret is unavoidable. The source explicitly
does not prove minimax optimality there; H(T+1)/6 and log(T+2)/6 are derived here,
not source-printed or sharp constants. Loss is squared error without a half factor.
The terminal chooses one fixed binary path outside the independent seed integral.
It applies at positive horizons to measurable, pointwise [0,1]-valued history policies.
All law masses, moments, same-path causal loss and comparator minimum are produced.
-/

'''
marker='noncomputable section\n'
assert source.count(marker)==1
source=source.replace(marker,doc+marker)
PUBLIC.write_bytes(source.encode('utf-8'))
write(RUN/'snapshots/public-full-body-v1.lean.raw',PUBLIC.read_bytes())
gate('public-full-body-build-v1','lake','build','BanditRLProof.OnlineGuessingLogLower')
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,normalize_statement
headers=load(CONTRACT/'planned-public-headers-v1.json')
for n,h in headers.items():assert lean_declaration_header(PUBLIC,n)==normalize_statement(h),n
write(RUN/'full-proof-frontier-v1.json',dict(
    frozen_targets=list(headers),compiled_frozen_target_count=16,
    actual_positive_horizon_fixed_witness_producer=True,
    seed_integrability_produced_from_measurable_bounded_outputs=True,
    exact_frozen_headers_unchanged=True,public_sha256=sha(PUBLIC),
    BODY_semantic_review='pending',public_canary_kernel_root_Tests_full_harness_site_FINAL='pending',
    source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed()
print('Sixteen frozen public proof bodies compiled; acceptance gates remain pending.')
