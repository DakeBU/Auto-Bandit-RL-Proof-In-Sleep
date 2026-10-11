from common import *
sys.path.insert(0, str(ROOT))
from tools import abrl_lifecycle as lifecycle

capture('new-task-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'new-task', TASK, '--kind', 'theorem', '--title',
    'Causal adaptive OSD with explicit zero-feedback handling',
    '--target-lean', 'BanditRLProof/OnlineAdaptiveOSD.lean')
for label, command, query, extra in [
    ('weighted-memory-v1', 'search-memory', 'weighted potential', []),
    ('weighted-declarations-v1', 'list-lean-decls', 'weighted_potential_sum', ['--statement']),
    ('subgradient-policy-declarations-v1', 'list-lean-decls', 'OnlineSubgradientPolicy', ['--statement']),
    ('energy-declarations-v1', 'list-lean-decls', 'OnlineAdaptiveEnergy', ['--statement'])]:
    capture(label, sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py', command, query, *extra)
capture('mathlib-card-retrieval-v1', 'rg', '-n', 'MLIB-FINSET-SUMS|summation|telescop',
    'research-wiki/mathlib/theorem-cards.md')
context = ('import Mathlib.Algebra.BigOperators.Module\nimport Mathlib.Tactic\n\n'
    'noncomputable section\nopen Finset\n\nnamespace BanditRL.OnlineAdaptivePotential\n')
header = ('theorem weighted_potential_sum (a w : ℕ → ℝ) (C : ℝ) (T : ℕ) (hT : 0 < T)\n'
    '    (hw : ∀ t < T, 0 ≤ w t)\n'
    '    (hmono : ∀ t, t + 1 < T → w t ≤ w (t + 1))\n'
    '    (hbound : ∀ t < T, a t ≤ C) :\n'
    '    (∑ t ∈ range T, (a t - a (t + 1)) * w t) ≤\n'
    '      C * w (T - 1) - a T * w (T - 1) := by\n')
write(CONTRACT/'potential-definition-context-v1.lean.txt', context)
write(CONTRACT/'potential-header-draft-v1.lean.txt', header)
statement = lifecycle.lean_declaration_header(CONTRACT/'potential-header-draft-v1.lean.txt', 'weighted_potential_sum')
write(CONTRACT/'potential-fingerprint-draft-v1.json', dict(
    declaration='BanditRL.OnlineAdaptivePotential.weighted_potential_sum', statement=statement,
    statement_hash=lifecycle.statement_hash(statement), context_sha256=sha(CONTRACT/'potential-definition-context-v1.lean.txt'),
    header_sha256=sha(CONTRACT/'potential-header-draft-v1.lean.txt'), phase='draft; no BODY or compiled public theorem'))
write(CONTRACT/'source-card-v1.md', '# Pinned source and current preparatory leaf\n\n'
    'Orabona, Online Learning: A Modern Introduction Using Convex Optimization, arXiv:1912.13213v10 '
    '(2026-06-21), SHA256 '+PDF_SHA+'. Current source reread: printed13-14/PDF25-26, '
    'Theorem2.13 and its variable-step summation; printed39-40/PDF51-52, Eq4.3 zero-feedback skipping, '
    'Eq4.4 and Theorem4.14. Root viewed the four original page images.\n\n'
    'The current leaf is a preparatory algebraic extension of the weighted-distance calculation, '
    'not a verbatim new numbered source theorem and not actual OSD. It substitutes general nonnegative '
    'nondecreasing weights w_t for 1/(2eta_t), so zero weights are legal. Potentials are arbitrary real '
    'numbers bounded above by C at played indices; no lower bound or terminal bound is needed. '
    'The source consumer later uses a_t=norm(x_t-u)^2 and w_t=sqrt(inclusive energy)/(2alpha D) for D>0. '
    'Source t=1..T is Lean t=0..T-1; terminal a_T is source squared distance at x_(T+1), '
    'last weight is w_(T-1). T>0 is explicit; empty-horizon OSD is a separate zero-sum branch.\n\n'
    'Proof-display issue for independent review: printed14/PDF26 second equality displays '
    '(1/eta_(t+1)-1/eta_t)*norm(x_(t+1)-u)^2 without factor1/2, while the preceding divided '
    'potential and following D^2/2 line require that factor. The frozen Theorem2.13 terminal is valid; '
    'our preparatory statement uses w=1/(2eta), retaining the factor and negative terminal exactly. '
    'This is a separately recorded proof-display correction, not an author endorsement or change to the pinned PDF.\n\n'
    'Future Theorem4.14 min-versus-infimum degeneracy requires its own source-repair review; '
    'not resolved by this potential leaf. No future losses or desired regret/stability bound are supplied '
    'as premises of a claimed algorithm.\n')
write(CONTRACT/'potential-contract-draft-v1.md', '# Potential leaf contract v1\n\n'
    'Model: finite real sequences on natural indices. Quantifiers: all a,w,C,T with T>0; '
    'played weights nonnegative, adjacent weights nondecreasing before T, a_t<=C for t<T. '
    'Conclusion: weighted potential decrement sum<=C*w_(T-1)-a_T*w_(T-1). '
    'T, last-weight indexing and negative terminal are frozen in the header/fingerprint. '
    'Zero and stalled weights, signed potentials and unrestricted terminal a_T are allowed. '
    'There is no probability, oracle, loss regularity, comparator, future information or regret premise.\n\n'
    'Reuse decision: adapt Mathlib Finset.sum_range_by_parts plus existing telescoping sums. '
    'The existing OnlineGradientDescent.weighted_potential_sum requires every eta>0 and therefore '
    'cannot handle a leading zero-energy prefix directly. Do not copy its induction as a second foundational '
    'summation theory. This generic algebraic extension is mathlib-candidate; a single shared module is planned. '
    'Source correspondence, not a direct Lean dependency: Theorem2.13 proof. '
    'Finite leaf edit window AFTER favorable contract review: create only OnlineAdaptivePotential.lean '
    'with this exact context/header and proof BODY. No root, Test, reader, old contract, toolchain or dependency edit. '
    'No algorithm definition or performance endpoint is stabilized by this contract.\n\n'
    'Roles: root director/architect/formalizer; reused distinct osd_blind reconstructs a neutral header '
    'without source; reused distinct source_reviewer compares source/intent/Lean/decoder before proving. '
    'Related role history is disclosed; no human/external/absolute-blind/runtime attestation. '
    'Later BODY/canary/combined/reader/registry/axiom/native/delivery gates remain separate and required.\n')
write(CONTRACT/'algorithm-terminal-draft-v1.md', '# Required parent, still draft\n\n'
    'Construct actual finite-history Nat.rec state (past outputs, cumulative selected support energy). '
    'Current action precedes current loss. A fixed history-dependent policy sees finite past losses/outputs '
    'and current whole loss; selected support is legal at the actual output. After feedback update energy, '
    'choose eta_t=alpha D/sqrt(new energy), and if selected support=0 append the unchanged output; '
    'otherwise append the shared projection. No comparator, horizon or future feedback enters the update. '
    'Prove exact recurrences, feasibility, strict-prefix dependence, energy=sum actual support norms squared, '
    'oracle-law sufficient adapter and actual played-point support/finite-loss/one-step bounds.\n\n'
    'On this SAME generated trajectory, for D>0,alpha>0 and an actual diameter upper bound, retain terminal: '
    'regret_T(u)<= (1/(2alpha)+alpha) D sqrt(S_T) '
    '-norm(x_(T+1)-u)^2 sqrt(S_T)/(2alpha D). '
    'Leading/interior zeros require zero-weight potential and support-derived nonpositive skipped loss gap. '
    'Handle T=0, total energy0 and D=0 explicitly; no positive-energy or positive-D premise may silently '
    'replace the source endpoints. Specialize alpha=1 to Eq4.4 and alpha=sqrt2/2 to Theorem4.14 bound. '
    'Preserve the separate required min-versus-infimum correction and assumptions. Exact Lean algorithm '
    'definitions and endpoint headers will be reviewed/frozen before their proof bodies. '
    'This draft is not a stabilized or accepted algorithm.\n\n'
    'Chapter2 all8forward containers/all6futureclaims remain required/open, proof total null. '
    'Ch3-16 unenumerated/null; no competing Chapter4 main task. WholeGoalACTIVE. '
    'Stacked on OPEN unmerged draft PR217 exact'+BASE+'; main/live unchanged.\n')
write(CONTRACT/'DAG-draft-v1.json', dict(nodes=[
    dict(id='Mathlib.Finset.sum_range_by_parts', status='API-read-and-typed', dependencies=[]),
    dict(id='potential', status='draft', dependencies=['Mathlib.Finset.sum_range_by_parts']),
    dict(id='causal-history-energy-zero-skip', status='required-draft', dependencies=['shared projection','SupportPolicy']),
    dict(id='same-trajectory-one-step', status='required-draft', dependencies=['causal-history-energy-zero-skip','lemma_2_31']),
    dict(id='same-trajectory-adaptive-regret', status='required-draft', dependencies=['potential','same-trajectory-one-step','OnlineAdaptiveEnergy.source_energy_term_bound']),
    dict(id='Eq4.4-and-Theorem4.14-bound', status='required-draft', dependencies=['same-trajectory-adaptive-regret']),
    dict(id='source-min-infimum-repair', status='required-separate-review', dependencies=[])],
    source_claim_denominator=None, chapter_complete=False, whole_Goal='active'))
write(RUN/'00_context.md', '# Causal adaptive OSD continuation\n\n'
    'Canonical E:/ABRL/research; isolated existing checkout E:/ABRL/worktrees/research-online-book. '
    'Branch '+BRANCH+'; exact stacked base '+BASE+' from delivered OPEN draft/unmerged PR217. '
    'Previous package closed ONE energy-display family, not algorithm/Chapter2. '
    'Actual initial tracked diff empty; relevant RAW + exact Git tree baseline retained, '
    'no claim of a new complete35392RAW scan. Shared .lake/Git stores/Book graph retained. '
    'Same persistent Chapters1-16 Goal ACTIVE; requested Astra/medium without runtime attestation.\n')
write(RUN/'director-potential-draft-v1.md', 'Select only the dependency-ready weighted potential leaf. '
    'The parent is actual causal adaptive OSD, not an eta-schedule existence consumer. '
    'Keep source/algorithm/chapters required; no package/chapter closure from this leaf.\n')
write(RUN/'architect-potential-draft-v1.md', 'Use Mathlib summation by parts with g_i=a_i-a_(i+1), '
    'then telescope prefixes. Bound increment-weight terms using a_i<=C and nonnegative adjacent weight differences. '
    'The residual first-weight factor is nonpositive because a0<=C and w0>=0. Retain terminal a_T with last weight. '
    'One lower route; no tactics before exact header/source review.\n')
neutral = header.replace('weighted_potential_sum', 'certificate').replace('hbound', 'hB').replace('hmono', 'hM')
for old, new in [('a', 'A'), ('w', 'W'), ('C', 'B'), ('T', 'n')]:
    import re
    neutral = re.sub(r'\b'+old+r'\b', new, neutral)
write(RUN/'neutral-potential-packet-v1.lean.txt', 'import Mathlib\nopen Finset\n\n'+neutral)
write(CONTRACT/'neutral-renaming-v1.json', dict(bijection=dict(a='A', w='W', C='B', T='n'),
    declaration='certificate', source_withheld=True, related_history_disclosed=True,
    complete_context='Mathlib; Finset; no ambient variables or custom definitions'))
documents = [ROOT/x/(TASK+'.md') for x in ['tasks','conversion-windows','proof-obligations','research-wiki/retrieval-index']]
originals = []
for path in documents:
    raw = path.read_bytes()
    originals.append(dict(path=path.as_posix(), sha256=sha(path), RAW_base64=base64.b64encode(raw).decode('ascii')))
    path.write_bytes(raw.replace(b'\r\n', b'\n')+(
        '\n## Current exact draft contract\n\nSee docs/contracts/online-ch2-adaptive-osd-v1/: '
        'only potential header v1 is submitted for stabilization; parent algorithm remains required draft. '
        'Stock scaffold examples are inactive. No permission to weaken a frozen terminal, add assumptions, '
        'edit old sources/readers/pins/globalSGB or claim chapter closure. WholeGoalACTIVE.\n').encode('utf8'))
write(RUN/'new-native-doc-byte-protocol-v1.json', dict(originals=originals, after=rows(documents),
    rule='Only fresh OWN scaffold docs: CRLF to LF before initial contract fingerprint, then explicit draft suffix; historical RAW retained.'))
write(RUN/'.gitattributes', '* -text\nown-artifact-journal.md whitespace=cr-at-eol\nlifecycle-state.json whitespace=cr-at-eol\nlifecycle-sessions.jsonl whitespace=cr-at-eol\n')
write(CONTRACT/'.gitattributes', '* -text\n')
event('potential-draft-event-v1', 'draft', dict(current_leaf='weighted_potential_sum',
    source_sha256=PDF_SHA, statement_hash=lifecycle.statement_hash(statement),
    parent_algorithm_status='required-draft', source_proof_display_delta='half-factor requires independent review',
    whole_Goal='active', chapter_complete=False))
print('Exact preparatory draft written; no Lean theorem BODY or algorithm declaration created.', flush=True)
