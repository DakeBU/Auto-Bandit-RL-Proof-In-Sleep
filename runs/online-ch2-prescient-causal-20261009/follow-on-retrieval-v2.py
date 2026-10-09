from publication_guard_v4 import *
fixed()
old = ROOT/'tmp/online-ch2-prescient-cumulative-API-v1.lean'
new = ROOT/'tmp/online-ch2-prescient-cumulative-API-v2.lean'
s = old.read_text(encoding='utf8')
assert s.count('Finset.range_nonempty') == 1
write(new, s.replace('Finset.range_nonempty', 'Finset.nonempty_range_iff'))
code,out = capture('follow-on-actual-API-retrieval-v2','lake','env','lean',new,required=False)
write(RUN/'follow-on-API-inspected-v2.json',dict(actual_exit=code, prior_exit=load(RUN/'follow-on-actual-API-retrieval-v1.json')['actual_exit'],
    prior_failure='Unknown Finset.range_nonempty; seven preceding exact types printed but overall probe not compiled.',
    actual_source_retrieval='.lake/packages/mathlib/Mathlib/Data/Finset/Range.lean:102 nonempty_range_iff, alias lives in Aesop namespace.',
    exact_only_probe_change='Finset.range_nonempty -> Finset.nonempty_range_iff',
    actual_probe_source_sha256=sha(new), no_theorem_or_proof_body=True, no_new_contract_frozen=True,
    current_FINAL_inputs_unchanged=True, whole_Goal_status='ACTIVE'))
fixed()
print('Follow-on versioned exact declaration retrieval exit',code)
print(out[-1300:])
