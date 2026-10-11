from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash
review_path = RUN/'algorithm-CONTRACT-review-v1.json'
review = load(review_path)
assert sha(review_path) == 'f038710a22e785da0ff5ce0d995239e749a33ec0cf735c5af01a190026ea44be'
assert not review['required_repairs']
for r in review['raw_input_checks']:
    assert sha(r['path']) == r['expected_sha256'] == r['before_sha256'] == r['after_sha256']
assert sha(review['report']) == review['report_sha256']
assert sha(review['input_manifest']) == review['input_manifest_sha256']
context = Path(review['definition_context'])
assert sha(context) == review['definition_context_sha256']
headers = review['approved_headers']
for r in headers.values():
    assert sha(r['path']) == r['raw_sha256']
public = Path(review['allowed_conditional_proof_window']['path'])
write(CONTRACT/'algorithm-stabilized-v1.json', dict(
    review_sha256=sha(review_path), definition_context_sha256=sha(context), headers=headers,
    allowed_window=review['allowed_conditional_proof_window'],
    parent_BODY='not authorized; mandatory frozen terminal', whole_Goal='active'))
write(RUN/'worker-causal-state-route-v1.md', '''Actual shared policy/projection API and exact typed definitions reviewed. First leaf state_succ is definitional reduction of the single Nat.rec joint history/energy update; use rfl, no changed hypothesis. Only after successful actual focused build lower state_prefix: structural induction, equality of earlier state and complete finite past-loss tuple, current loss equality at consumed index, rewrite exact compiled state_succ and unfold only observers. This proves the whole pair with common fixed external parameters/p; no exogenous eta equality or future loss access. One lower route, all three header/context hashes frozen; parent regret proof not started. Actual failures must preserve output/snapshot and header.
''')
event('algorithm-stabilized-event-v1', 'stabilized', dict(current_leaf='state_succ',
    review_sha256=sha(review_path), context_sha256=sha(context), headers=headers,
    parent_terminal='regret_bound frozen, BODY not authorized'))
event('state-succ-proving-event-v1', 'proving', dict(current_leaf='state_succ',
    statement_hash=headers['state_succ']['normalized_statement_hash'], allowed_file=public.as_posix()))
end = b'\nend BanditRL.OnlineAdaptiveOSD\n'
first = context.read_bytes()+b'\n'+Path(headers['state_succ']['path']).read_bytes()+b'  rfl\n'
write(public, first+end)
assert statement_hash(lean_declaration_header(public, 'state_succ')) == headers['state_succ']['normalized_statement_hash']
write(RUN/'state-succ-body-attempt-v1.lean.txt', public.read_bytes())
code, out = capture('state-succ-focused-build-v1', 'lake', 'build', 'BanditRLProof.OnlineAdaptiveOSD', required=False)
print(out, flush=True)
if code != 0:
    sys.exit(code)
write(RUN/'state-succ-compiled-local-v1.json', dict(
    production_sha256=sha(public), header_hash=headers['state_succ']['normalized_statement_hash'],
    actual_build_receipt_sha256=sha(RUN/'state-succ-focused-build-v1.json'),
    boundary='Actual recurrence BODY only; no parent performance, semantic BODY acceptance or full combined gate.'))
assert public.read_bytes() == first+end
event('state-prefix-proving-event-v1', 'proving', dict(current_leaf='state_prefix',
    statement_hash=headers['state_prefix']['normalized_statement_hash'],
    dependency_focused_receipt=sha(RUN/'state-succ-focused-build-v1.json')))
body = '''  induction t with
  | zero => rfl
  | succ t ih =>
    have hs := ih (fun s hs => hloss s (Nat.lt_succ_of_lt hs))
    have hpast : (fun i : Fin t => loss i.val) = fun i : Fin t => loss' i.val := by
      funext i
      exact hloss i.val (Nat.lt_succ_of_lt i.isLt)
    rw [state_succ, state_succ]
    simp only [history, output, selected, eta, energy, hs, hpast,
      hloss t (Nat.lt_succ_self t)]
'''
second = first+b'\n'+Path(headers['state_prefix']['path']).read_bytes()+body.encode('utf8')+end
public.write_bytes(second)
assert public.read_bytes().startswith(first)
for name in ['state_succ', 'state_prefix']:
    assert statement_hash(lean_declaration_header(public, name)) == headers[name]['normalized_statement_hash']
write(RUN/'state-prefix-body-attempt-v1.lean.txt', public.read_bytes())
code, out = capture('state-prefix-focused-build-v1', 'lake', 'build', 'BanditRLProof.OnlineAdaptiveOSD', required=False)
print(out, flush=True)
sys.exit(code)
