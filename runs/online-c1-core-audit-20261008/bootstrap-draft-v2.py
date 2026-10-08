from common_v1 import *
import re

assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()==BASE
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,normalize_statement,statement_hash
CONTRACT.mkdir(parents=True,exist_ok=False)
old_inventory=load('runs/online-iid-success-20261008/five-old-modules-read-only-inventory-v1.json')
inventory={x['path']:x for x in old_inventory['modules']}
rows=[]
for p in MODULES:
    assert sha(p)==inventory[p.as_posix()]['sha256']
    write(RUN/'snapshots'/p.name,p.read_bytes())
    for decl in inventory[p.as_posix()]['declarations']:
        name=PRE+decl['name'];header=lean_declaration_header(p,name)
        rows.append(dict(id='A'+str(len(rows)+1).zfill(3),name=name,path=p.as_posix(),header=header,
            statement_hash=statement_hash(header),original_file_sha256=sha(p),source_indexed_line=decl['line']))
assert len(rows)==12
source_map={
 'lemma_1_2':('Lemma1.2',3,15,'Exact hindsight-prefix minimizers supplied; arbitrary loss/action space; T0 empty extension. No arbitrary argmin existence producer is asserted.'),
 'expected_square_decomposition':('C1-IID-MEAN derived identity',1,13,'Probability and L2; arbitrary real fixed comparator. Generalizes bounded guessing squared-loss motivation; not separately numbered.'),
 'independent_prediction_square':('C1-IID-LOWER derived identity',1,13,'Consumes current prediction/target independence and both L2. Generic variance decomposition only, not itself causal independence producer.'),
 'meanPredict_independent':('C1-GAME/C1-IID-LOWER actual learner',1,13,'Derives independence for real initial-half strict-past meanPredict from joint independence. No same-law or bound assumption needed.'),
 'meanPredict_measurable':('C1-GAME actual learner regularity',1,13,'Derived measurability from measurable targets; not printed theorem.'),
 'meanPredict_memLp':('C1-GAME/IID regularity',1,13,'Legacy pointwise every-omega unit support is stronger than a.s. source support. New accepted AE producers remain separate; audit does not waive this API limitation.'),
 'iid_meanPredict_excess':('Eq1.1 actual learner derived identity',1,13,'One infinite process, joint independence/same-law/measurability and pointwise unit support; zero-based rounds and T0 extension. Does not assert success rate.'),
 'iid_meanPredict_excess_nonneg':('C1-IID-LOWER actual learner',1,13,'Same legacy pointwise support; derived nonnegativity for this actual learner, not arbitrary stochastic kernel.'),
 'source_mean_optimal':('C1-IID-MEAN',1,13,'Pointwise unit support; population mean feasible and optimal over all real constants. Mean is analysis oracle, not unknown-law algorithm input.'),
 'history_policy_independent':('C1-GAME/C1-IID-LOWER causal producer',1,13,'Actual measurable strict finite-history deterministic policy; derives independence from joint target independence. No support/L2 assumption.'),
 'history_policy_loss_ge_variance':('C1-IID-LOWER deterministic policy bound',1,13,'Legacy pointwise target support and global all-history policy bound stronger than a.s. targets/legal-cube feasibility. Current-round variance, no identical-law hypothesis. Restricted deterministic policy, not full strategy-class closure.'),
 'normalized_excess':('Eq1.1/1.2 arithmetic adapter',1,13,'Positive horizon and arbitrary real total/variance parameter. Exact scalar identity only, no asymptotic result.')}
for row in rows:
    anchor,page,pdf,delta=source_map[row['name'].split('.')[-1]]
    row.update(source_anchor=anchor,printed_page=page,pdf_page=pdf,semantic_delta=delta,
        kind='existing-public-proof audit; no new theorem',proof_body_edit_allowed=False)
write(CONTRACT/'targets-v1.json',dict(version=1,phase='draft',targets=rows,existing_proofs=12,new_proofs=0,
    chapter_complete=False,goal_complete=False))
write(CONTRACT/'source-fingerprint-v1.json',dict(url='https://arxiv.org/pdf/1912.13213v10',version='v10,2026-06-21',sha256=PDF_SHA,
    printed_pages=[1,2,3,4],pdf_pages=[13,14,15,16],source_title='Online Learning: A Modern Introduction Using Convex Optimization'))
imports='import Mathlib.Probability.Moments.Variance\nimport Mathlib.Probability.IdentDistrib\nimport Mathlib.Tactic\n\nnoncomputable section\nopen MeasureTheory ProbabilityTheory\nuniverse u\n'
defs='def D01 (y : ℕ → ℝ) (T : ℕ) : ℝ := (∑ i ∈ Finset.range T, y i) / (T : ℝ)\ndef D02 (y : ℕ → ℝ) (t : ℕ) : ℝ := if t = 0 then 1/2 else D01 y t\n'
neutral=imports+'\nnamespace NeutralCoreAudit\n'+defs+'\n'
for row in rows:
    h=row['header'];short=row['name'].split('.')[-1]
    h=h.replace('theorem '+short,'def Q'+row['id'][1:],1).replace('Type*','Type u')
    h=h.replace('meanPredict','D02')
    # Top-level colon is located by balanced binder delimiters, not the final nested colon.
    depth=0;colon=None
    for i,ch in enumerate(h):
        if ch in '({[': depth+=1
        elif ch in ')}]': depth-=1
        elif ch==':' and depth==0: colon=i;break
    assert colon is not None
    neutral+=h[:colon]+' : Prop :=\n  '+h[colon+1:].strip()+'\n\n'
neutral+='end NeutralCoreAudit\n'
write(CONTRACT/'neutral-context-v1.lean',neutral)
write(CONTRACT/'public-context-v1.lean','\n\n'.join(x['header'] for x in rows))
write(CONTRACT/'contract-v1.md','''# C1 core source audit v1 — frozen draft

Audit twelve existing public proofs in five unreviewed main-relative source modules. No proof body/header change or duplicate production wrapper is permitted. The sole future production change is a reviewed module-level comment spelling out exact source/delta boundaries; all existing theorem tokens remain byte-identical. The new test module must instantiate actual public proof values on nondegenerate models. Independently reconstruct all twelve signatures, then review source intent, quantifier order, hidden hypotheses, metrics, constants/index/T0, information and permitted evidence.

One actual source-numbered Lemma1.2 plus eleven derived generic/causal/regularity/arithmetic APIs, not twelve printed results. Legacy pointwise support and global off-cube policy bound remain explicit API limitations; the later accepted AE/legal-cube producers remain separate. No arbitrary supplied independent predictor is a full causal algorithm. No learner uses population mean or future observations. This is a source-correction/integration audit, new mathematical proofs=0, not new progress by declaration count.

Source is exact Orabona v10 hash and printed1–4/PDF13–16, with chapter-one original sixteen objects and null proof-leaf total preserved. Full universal-kernel/completed-information/AE-factorization source coverage, fullC1/C2, unenumeratedC3–16 and necessary appendices remain required. Whole Goal stays ACTIVE. PR196 exact6b387a39 OPENdraft/unmerged is the stacked base; main6847 unchanged, no merge/deploy/live/retirement. Reused staged automated decoder/source reviewer, requested Astra/medium, no absolute-blind/human/external/runtime attestation.
''')
write(CONTRACT/'conversion-window-v1.md','''Allowed: own contract/RUN/task metadata, exact reviewed comments in five owned old modules, one canary and Tests import, one source card/12 exact API notes/own boundary in existing C1 route, own schema2 manifest, own native records and scoped frontier. Forbidden: theorem/body weakening, other old code/readers/contracts, shared pins, global SGB frontier, anonymous/private materials, generated website/_site, canonical main or other worktrees. Scope is twelve reused declarations/five required source audits, not full source strategy coverage. Freeze full signatures and comment delta before implementation. Failed attempts/raw logs preserved.
''')
write(CONTRACT/'initial-DAG-v1.json',dict(nodes=[dict(id=x['id'],declaration=x['name'],status='existing-body-unreviewed',
    intended_dependencies=('source:Lemma1.2' if x['name'].endswith('lemma_1_2') else x['source_anchor'])) for x in rows],
    graph_kind='intent DAG only; actual compiler TYPE/VALUE graph audit required',source_audits_before=5,source_audits_after=None,
    new_mathematical_proofs=0,globalSGB_unchanged=True))
write(CONTRACT/'proof-obligations-draft-v1.json',dict(existing_proof_targets=[x['id'] for x in rows],
    dependency_ready='Existing bodies present; actual fresh compile/types/values and independent source review required',
    required_gates=['source/neutral/full-signature review','nondegenerate public proof-value canaries','frozen header/body tokens',
        'focused/root/Tests/full harness','axioms/compiler VALUE deps','stacked and origin/main contributor checks','shared registry/site/DOM/pixels','FINAL/native review/draft delivery'],
    source_audits_before=5,source_audits_after=None,new_proofs=0,chapter_complete=False,goal_complete=False))
old=load('docs/contracts/online-iid-success-v1/chapter-one-source-ledger-accepted-v2.json')
assert len(old['maintext_items'])==16 and old['required_proof_leaf_total'] is None
write(CONTRACT/'chapter-one-source-ledger-draft-v1.json',dict(original16_source_objects=old['maintext_items'],required_proof_leaf_total=None,
    prior_accepted_ledger='docs/contracts/online-iid-success-v1/chapter-one-source-ledger-accepted-v2.json',
    prior_ledger_sha256=sha('docs/contracts/online-iid-success-v1/chapter-one-source-ledger-accepted-v2.json'),
    own_five_core_audits='draft/unreviewed',chapter_complete=False,goal_complete=False))
fixed_files={p.as_posix():sha(p) for p in MODULES+[Path('lean-toolchain'),Path('lakefile.lean'),Path('lake-manifest.json'),Path('runs/active_frontier.json')]}
write(RUN/'draft-baseline-v1.json',dict(base_head=BASE,base_PR=196,branch=BRANCH,fixed_files=fixed_files,canonical_main='6847b678a73db68dee5101d6f05c2453c1405afc',
    sharedGit='E:/ABRL/research/.git',all_other_worktrees_preserved=True,globalSGB_unchanged=True))
write(RUN/'00_context.md','Persistent whole Orabona Chapters1–16 Goal active/no budget. New bounded five-core source audit on PR196 exact6b387a39, not main. Twelve existing proof headers/bodies frozen; no new proof count. Legacy pointwise/global policy hypotheses must be disclosed, not silently weakened. Distinct staged roles requested Astra/medium. No full strategy-class, chapter/Goal/main/live closure. Same underlying Lean/Lake/registry and isolated existing online-book worktree.')
write(RUN/'10_upper_director.md','Select dependency-ready audit of twelve existing core bodies and five missing main-relative contributor contracts. First contract/semantic freeze, then actual public nondegenerate canaries and comment-only source corrections. Do not fabricate covering manifests or waive universal-model coverage. Reuse existing bodies and accepted later producer packages; source1.2 exact hmin/hmem supplied, sourceIID/API-limit deltas explicit. No multi-route proof experiment.')
write(RUN/'20_middle_architect.md','Single reuse/audit route. Existing five-module DAG: Foundations feeds FTL; Stochastic variance identities feed Information and IID; Information derives real meanPredict independence; IID actual mean nonnegative excess and benchmark; History derives strict-tuple policy independence and positive normalization. Actual compiled graph will distinguish supplied-independent consumer from causal producer. Typed source-neutral definitions D01/D02 and all twelve headers frozen before canaries. Nondegenerate coin/clipped stream, nontrivial leader switch and outside-unit generic scalar tests; no wrappers for new proof-count progress.')
write(RUN/'31_lower_initial.md','Lower initial status: existing proof bodies read, no edit, no fresh compile claimed. Five old source audits are required because remote push contributor failed them. Draft neutral signatures/API/source retrieval next; stable terminal types remain exact throughout canary and comment-only work.')
fixed()
native('new-task-v1','new-task',TASK,'--kind','source-core-audit','--title','C1 five core source audits, twelve existing proof values','--target-lean','BanditRLProof/OnlineLearningFoundations.lean')
native('lifecycle-draft-v1','lifecycle-event','--session',TASK,'--event','draft','--payload-json',json.dumps(dict(run_id=RUN.name,
    contract_version=1,existing_proof_targets=12,new_proofs=0,source_audits=5,chapter_complete=False,goal_complete=False)))
native('blueprint-refresh-v1','blueprint-refresh',TASK)
blueprint=Path('proof-blueprints')/(TASK+'.md');raw=blueprint.read_bytes();archive=RUN/'native-blueprint-generated-v1.txt.gz'
write(archive,gzip.compress(raw,mtime=0));assert gzip.decompress(archive.read_bytes())==raw
write(RUN/'native-blueprint-archive-v1.json',dict(actual_command='python tools/bandit.py blueprint-refresh '+TASK,
    generated_raw_sha256=hashlib.sha256(raw).hexdigest(),archive=archive.as_posix(),archive_sha256=sha(archive),
    raw_bytes=len(raw),compressed_bytes=archive.stat().st_size,roundtrip_bytes_exact=True,
    explanation='Native CLI embeds all existing roadmap/declarations. Preserve exact generated bytes once, compressed; current own blueprint below is the bounded explicit audit route, not a fabricated command outcome.'))
blueprint.write_bytes(('''# Bounded C1 core audit blueprint

Actual blueprint-refresh generated the complete project snapshot. Exact unmodified generated bytes are preserved in runs/online-c1-core-audit-20261008/native-blueprint-generated-v1.txt.gz, with actual exit and decompress/raw SHA evidence. This current task route is a bounded replacement summary written before contract freeze; archive history is retained.

Twelve existing public statements in five modules, dependency DAG and full hypotheses are in docs/contracts/online-c1-core-audit-v1/targets-v1.json and initial-DAG-v1.json. No new theorem/proof-body edits. CONTRACT -> actual proof-value canaries/focused+kernel+compiler graph -> candidate -> combined/full harness+stacked/main contributor+shared site -> separate FINAL/native audits -> scoped draft delivery. Existing script/template placeholders are historical scaffolding, not operative subGaussian assumptions. This route uses real probability/L2, exact hindsight minimizers and strict finite-history measurability with the legacy pointwise/global-bound API deltas. Five source audits remain pending. Original16 objects/null proof total, full source strategy model, C1/C2/C3–16/appendices/Goal remain required.
''').encode('utf8'))
fixed()
print('Actual bounded DRAFT created: twelve existing signatures, five required source audits, native blueprint raw archive roundtrip exact; no semantic/compile acceptance.')
