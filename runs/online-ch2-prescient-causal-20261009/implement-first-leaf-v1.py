from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
d = load(CONTRACT / 'stabilized-v1.json')
t = d['targets'][0]
assert t['declaration'] == 'BanditRL.OnlineBregman.divergence_extension_eq'
prefix = 'import BanditRLProof.OnlineBregmanExtended\nimport Mathlib.Analysis.Calculus.FDeriv.Congr\nimport Mathlib.Data.Option.Basic\n\nnoncomputable section\nopen Set\n\nnamespace BanditRL.OnlineBregman\nvariable {E : Type*} [NormedAddCommGroup E] [NormedSpace \u211d E]\n\n'
body = ''' := by
  have he : Filter.EventuallyEq \u03c8 \u03c6 (nhds b) :=
    (mem_interior_iff_mem_nhds.mp hb).mono fun z hz => hEq hz
  have hd : fderiv \u211d \u03c8 b = fderiv \u211d \u03c6 b := he.fderiv_eq
  simp only [divergence, hEq ha, hEq (interior_subset hb), hd]
'''
write(PUBLIC, prefix + t['exact_proposed_header'] + body + '\nend BanditRL.OnlineBregman\n')
assert statement_hash(lean_declaration_header(PUBLIC, t['declaration'])) == t['statement_hash']
write(RUN / 'first-leaf-attempt-v1.lean', PUBLIC.read_bytes())
rc, out = capture('focused-first-leaf-v1', 'lake', 'build', 'BanditRLProof.OnlinePrescientBregman', required=False)
print(out[-4500:], flush=True)
jobs = re.findall(r'Build completed successfully \((\d+) jobs\)', out)
write(RUN / 'first-leaf-attempt-result-v1.json', dict(actual_exit=rc, production_sha256=sha(PUBLIC), compiled=rc == 0 and bool(jobs), actual_cached_inclusive_build_jobs=jobs, selected_proofs=1, other_frozen_proofs_pending=7, definitions_not_yet_materialized=2, statement_hash_unchanged=True, source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
