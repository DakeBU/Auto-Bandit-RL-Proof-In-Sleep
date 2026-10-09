from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
d = load(CONTRACT / 'stabilized-v1.json')
assert load(RUN / 'advance-inspected-v3.json')['production_sha256'] == sha(PUBLIC)
assert load(RUN / 'advance-inspected-v3.json')['compiled']
before = PUBLIC.read_bytes()
write(RUN / 'before-recursion-selection-v1.lean', before)
selected = d['targets'][3:7]
event('recursion-selected-native-v1', 'proving', dict(
    selected_leaves=[dict(declaration=t['declaration'], statement_hash=t['statement_hash']) for t in selected],
    dependency_ready='Exact current-only definitions and both advance specs focused/public/fence audited.',
    source_container_closed=False, chapter_complete=False, goal_complete=False))
capture('recursion-running-trial-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'running', '--attempt-id', 'PC003-prefix-and-definedness-v1', '--run-id', RUN.name, '--lean', PUBLIC.relative_to(ROOT).as_posix(), '--statement-hash', selected[0]['statement_hash'], '--obligations-before', '4', '--obligations-after', '4', '--notes', 'Four dependency-ready frozen recursion proofs. Prefix equality, true previous-state extraction, absorbing none, completion conditional on actual local attainment. No universal attainment or source performance closure.')
bodies = [
''' := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [iterate]
      rw [ih (fun s hs => h\u03b7 s (Nat.lt_succ_of_lt hs))
        (fun s hs => hloss s (Nat.lt_succ_of_lt hs)),
        h\u03b7 t (Nat.lt_succ_self t), hloss t (Nat.lt_succ_self t)]
''',
''' := by
  change (iterate V \u03c8 \u03b7 loss x0 t).bind (advance V \u03c8 (\u03b7 t) (loss t)) = some p at h
  obtain \u27e8x, hx, hstep\u27e9 := Option.bind_eq_some_iff.mp h
  exact \u27e8x, hx, advance_some_spec V \u03c8 (\u03b7 t) (loss t) x p hstep\u27e9
''',
''' := by
  induction k with
  | zero => simpa only [Nat.add_zero] using h
  | succ k ih =>
      change (iterate V \u03c8 \u03b7 loss x0 (t + k)).bind
        (advance V \u03c8 (\u03b7 (t + k)) (loss (t + k))) = none
      rw [ih]
      rfl
''',
''' := by
  induction T with
  | zero => exact \u27e8x0, rfl\u27e9
  | succ T ih =>
      obtain \u27e8x, hx\u27e9 := ih (fun t ht y hy => hatt t (Nat.lt_succ_of_lt ht) y hy)
      have ha := hatt T (Nat.lt_succ_self T) x hx
      have hn : advance V \u03c8 (\u03b7 T) (loss T) x \u2260 none := by
        intro hnone
        exact (advance_none_iff V \u03c8 (\u03b7 T) (loss T) x).mp hnone ha
      cases hs : advance V \u03c8 (\u03b7 T) (loss T) x with
      | none => exact (hn hs).elim
      | some p =>
          refine \u27e8p, ?_\u27e9
          change (iterate V \u03c8 \u03b7 loss x0 T).bind
            (advance V \u03c8 (\u03b7 T) (loss T)) = some p
          rw [hx]
          exact hs
''']
s = before.decode('utf8')
end = 'end BanditRL.OnlinePrescientBregman\n'
assert s.endswith(end)
prefix = s[:-len(end)]
s = prefix + '\n'.join(t['exact_proposed_header'] + body for t, body in zip(selected, bodies)) + '\n' + end
PUBLIC.write_bytes(s.encode('utf8'))
assert PUBLIC.read_bytes().startswith(prefix.encode('utf8'))
for t in d['targets'][:7]:
    assert statement_hash(lean_declaration_header(PUBLIC, t['declaration'])) == t['statement_hash']
for x in d['definitions']:
    assert x['exact_definition'] in s
write(RUN / 'recursion-attempt-v1.lean', PUBLIC.read_bytes())
rc, out = capture('focused-recursion-v1', 'lake', 'build', 'BanditRLProof.OnlinePrescientBregman', required=False)
print(out[-3500:], flush=True)
jobs = re.findall(r'Build completed successfully \((\d+) jobs\)', out)
write(RUN / 'recursion-attempt-result-v1.json', dict(actual_exit=rc,
    production_sha256=sha(PUBLIC), compiled=rc == 0 and bool(jobs),
    actual_cached_inclusive_build_jobs=jobs, selected_proofs=4,
    total_materialized_proofs=7, materialized_definitions=2, other_proofs_pending=1,
    frozen_hashes_unchanged=True, previous_proofs_unchanged=True,
    source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
