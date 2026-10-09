from common import *
fixed()
assert load(RUN / 'canary-API-v1.json')['actual_exit'] == 1
s = (RUN / 'canary-API-v1.lean').read_text(encoding='utf8')
s = s.replace('#check Real.strictConvexOn_exp', '#check strictConvexOn_exp')
s = s.replace('#check HasDerivAt.fderiv', '#check HasDerivAt.hasFDerivAt\n#check HasFDerivAt.fderiv\n#check fderiv_eq_deriv_mul')
write(RUN / 'canary-API-v2.lean', s)
write(RUN / 'canary-API-repair-v2.json', dict(original_actual_exit=1,
    diagnosis='Pinned strictConvexOn_exp lives at global namespace; HasDerivAt has hasFDerivAt, then HasFDerivAt.fderiv, not a direct fderiv projection.',
    typed_source_lookup_only=True, no_new_proof_compiled=True, statement_change=False))
_, out = capture('canary-API-v2', 'lake', 'env', 'lean', RUN / 'canary-API-v2.lean')
print(out[:3600], flush=True)
fixed()
