from common_v1 import *
fixed()
headers=[
('guessing_prefix_minimum', '''theorem guessing_prefix_minimum (y : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1) :
    empiricalMean y T ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        (∑ t ∈ Finset.range T, (empiricalMean y T - y t)^2) ≤
          ∑ t ∈ Finset.range T, (u - y t)^2''',[]),
('squaredLoss_minimum_eq', '''theorem squaredLoss_minimum_eq (y : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1) :
    sInf ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - y t)^2) ''
      Set.Icc (0 : ℝ) 1) =
        ∑ t ∈ Finset.range T, (empiricalMean y T - y t)^2''',['guessing_prefix_minimum']),
('squaredBestRegret_eq_comparatorRegret', '''theorem squaredBestRegret_eq_comparatorRegret (y prediction : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1) :
    squaredBestRegret y prediction T =
      comparatorRegret (fun t x => (x - y t)^2) prediction (empiricalMean y T) T''',['squaredLoss_minimum_eq']),
('comparatorRegret_le_squaredBestRegret', '''theorem comparatorRegret_le_squaredBestRegret (y prediction : ℕ → ℝ) (T : ℕ)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    comparatorRegret (fun t x => (x - y t)^2) prediction u T ≤
      squaredBestRegret y prediction T''',['guessing_prefix_minimum','squaredBestRegret_eq_comparatorRegret']),
('meanPredict_bestRegret_bound', '''theorem meanPredict_bestRegret_bound (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1) :
    squaredBestRegret y (meanPredict y) T ≤ 4 + 4 * Real.log T''',['squaredBestRegret_eq_comparatorRegret','theorem_1_3']),
('meanPredict_bestRegret_refined', '''theorem meanPredict_bestRegret_refined (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1) :
    squaredBestRegret y (meanPredict y) T ≤
      (1 : ℝ) / 4 + ∑ t ∈ Finset.range (T - 1), 4 / ((t : ℝ) + 2)''',['squaredBestRegret_eq_comparatorRegret','meanPredict_regret_refined'])]
definition='''noncomputable def squaredBestRegret (y prediction : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, (prediction t - y t)^2) -
    sInf ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - y t)^2) ''
      Set.Icc (0 : ℝ) 1)
'''
imports='import BanditRLProof.OnlineLearningFTL\nimport BanditRLProof.OnlineLearningRegret\nimport Mathlib.Order.ConditionallyCompleteLattice.Basic\n'
context=imports+'\nnamespace BanditRL.OnlineLearning\n'+definition+'\nend BanditRL.OnlineLearning\n'
write(CONTRACT/'public-context-v1.lean',context)
rows=[dict(id='M'+str(i).zfill(3),name='BanditRL.OnlineLearning.'+n,header=h,header_sha256=hashlib.sha256(h.encode('utf8')).hexdigest(),dependencies=d,
    source_class='derived literal-minimum producer/representation' if i<=4 else 'literal-minimum adapter of existing actual FTL guarantee') for i,(n,h,d) in enumerate(headers,1)]
write(CONTRACT/'targets-v1.json',dict(version=1,rows=rows,new_public_proofs=6,new_definitions=1,
    source_numbered_theorem_count_not_equal_to_new_declaration_count=True,chapter_complete=False,goal_complete=False))
write(CONTRACT/'initial-DAG-v1.json',dict(nodes=rows,import_ready=['empiricalMean_mem','empiricalMean_minimizes','theorem_1_3','meanPredict_regret_refined','IsLeast.csInf_eq'],
    first_finite_leaf='M001',actual_API_compilation_pending=True,globalSGB_not_changed=True))
types=[]
for i,(n,h,d) in enumerate(headers,1):
    params,conclusion=h[len('theorem '+n):].rsplit(' :\n',1)
    types.append('def Q'+str(i).zfill(3)+' : Prop := ∀'+params+',\n'+conclusion+'\n')
checks='\n#check IsLeast.csInf_eq\n#check csInf_le\n#check le_csInf\n#check BanditRL.OnlineLearning.empiricalMean_mem\n#check BanditRL.OnlineLearning.empiricalMean_minimizes\n#check BanditRL.OnlineLearning.theorem_1_3\n#check BanditRL.OnlineLearning.meanPredict_regret_refined\n#check BanditRL.OnlineLearning.lemma_1_2\n'
write(RUN/'draft-types-v1.lean',context+'\nopen BanditRL.OnlineLearning\nnamespace DraftMinimum\n'+'\n'.join(types)+'\nend DraftMinimum\n'+checks)
neutral_context='''import Mathlib
namespace NeutralMinimum
noncomputable def C0 (y : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, y t) / T
noncomputable def C1 (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then 1 / 2 else C0 y t
noncomputable def C2 (loss : ℕ → ℝ → ℝ) (prediction : ℕ → ℝ)
    (u : ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, loss t (prediction t)) -
    ∑ t ∈ Finset.range T, loss t u
noncomputable def C3 (y prediction : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, (prediction t - y t)^2) -
    sInf ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - y t)^2) ''
      Set.Icc (0 : ℝ) 1)
'''
neutral_types=[]
for type in types:
    for before,after in [('squaredBestRegret','C3'),('comparatorRegret','C2'),('empiricalMean','C0'),('meanPredict','C1')]:type=type.replace(before,after)
    neutral_types.append(type)
neutral=neutral_context+'\n'.join(neutral_types)+'\nend NeutralMinimum\n'
write(CONTRACT/'neutral-context-v1.lean',neutral)
write(RUN/'neutral-packet-v1.md','''Reconstruct only the four definitions C0-C3 and six closed propositions Q001-Q006 below, in natural language, LaTeX and seven semantic slots. No source identity, theorem proofs, desired verdict or prior acceptance is supplied. Explicitly distinguish finite-horizon minimum/infimum, feasibility, arbitrary supplied prediction versus the explicitly defined strict-prefix predictor, positive-horizon restrictions, signed comparisons, empty-prefix conventions and coefficient/indexing. Do not read other files or source identities. No proof/acceptance judgment; staged actor history is disclosed, no absolute-blind/runtime/human/external attestation.\n\n```lean\n'''+neutral+'```\n')
write(RUN/'neutral-inputs-v1.json',dict(rows=[dict(path=p.resolve().as_posix(),sha256=sha(p)) for p in [RUN/'neutral-packet-v1.md',CONTRACT/'neutral-context-v1.lean']],definition_count=4,terminal_count=6))
write(CONTRACT/'contract-v1.md','''# Version1 draft: actual squared hindsight minimum

Source Orabona1912.13213v10/2026-06-21 pinned PDF SHAcef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Printed2/PDF14 square-game best-fixed regret, printed3/PDF15 actual empirical-mean argmin, printed4/PDF16 Theorem1.3, printed5/PDF17 sharp initial1/4 and positive-round tail. ROOT directly read/viewed current copied cached source14-16 against the unchanged pinned PDF; caches are provenance-preserving copies, not a claimed fresh rerender. Page17 cache follows separate copy/read before stabilization.

Six exact frozen prospective headers in targets-v1; public-context-v1 contains one genuine literal minimum definition. No target body yet. At every finite T with y_t in[0,1] for t<T, produce mean feasibility/minimization. ForT0, empty sum/minimum are0 and defaultmean0 is feasible; this is an explicit library extension, not uniqueness/source1/T atzero. ForpositiveT use actual existing mean_minimizes/mem. Real sInf over nonempty image is proved attained with actual source mean, no totalized-inf or assumed minimizer certificate. Same losses, predictor, comparator and horizon in shared comparatorRegret. Generic provided prediction equality/order need not be feasible or causal and are representation generalizations, not algorithm existence. Actual endpoints use meanPredict (first1/2, later strict-prefix mean) and existing theorem1.3/refined bodies; arbitrary initialization not given sharpquarter guarantee. Source1..T=Lean0..T-1; refined source2..T=Lean t0..T-2 denominator t+2. Signed pathwise best regret may be negative; do not inherit expected-excess nonnegativity.

No IID/expectation/probability/min-expectation exchange theorem here. Printed1-2 expected fixed minimum and causal variance benchmark remain REQUIRED next, never inferred from this pathwise minimum. No generic argmin for arbitrary losses/carriers and no sublinear/ordinary-limit claim. Four derived representation/order results and two actual-guarantee adapters are not six printed book theorems or new regret-rate mathematics. Proposed meaningful terminal is literal minimum now produced, rather than assumed, and actual FTL guarantee expressed against it.

Distinct required decoder/reviewer before stabilization/proving; same requestedAstra-medium and history disclosed. Sourcecard/fingerprints/DAG/API checks/review receipts required. Future root/Tests/harness/axiom/canary/sharedregistry/reader/site/FINAL/native/PR gates separate. Only bounded square minimum hinge may close; full C1, IID benchmark, five main-relative source-module audits, Chapter2,3-16/appendices remain required. Original16C1items/proof-totalnull, GoalACTIVE, PR192 OPENdraft stack. No main/live/merge/deploy/retirement.
''')
write(CONTRACT/'source-card-v1.json',dict(source_url='https://arxiv.org/pdf/1912.13213v10',PDF_sha256=PDF_SHA,
    anchors=[dict(printed_page=p,pdf_page=p+12) for p in [2,3,4,5]],
    intent='Produce actual interval squared-loss hindsight minimum and same signed best regret, then apply actual strict-past mean guarantees.',
    proposed_delta=['T0 empty-prefix extension without uniqueness','arbitrary supplied real prediction identity/order is algebra only',
        'sInf value proven actually attained by produced empirical mean','six derived producer/representation/adapters, not six printed theorems'],
    required_remaining=['IID minimum of expected fixed loss/cumulative causal variance benchmark','five main-relative module audits','full Chapter1','Chapter2','Chapters3-16','necessary appendices'],
    source_package_accepted=False,chapter_complete=False,goal_complete=False))
for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']:
    p=Path(folder)/(TASK+'.md')
    p.write_bytes(p.read_bytes()+('\n\n## Draft exact square-minimum contract v1\n\n'+(CONTRACT/'contract-v1.md').read_text(encoding='utf8')+'\nFrozen prospective headers: '+sha(CONTRACT/'targets-v1.json')+'; no source/body acceptance yet.\n').encode('utf8'))
write(RUN/'native-reference-index-v1.py',"from common_v1 import *\nsys.path.insert(0,str(ROOT/'tools'))\nimport bandit\nbandit.RETRIEVAL_INDEX_DIR=RUN/'native-reference-index'\nraise SystemExit(bandit.main(['reference-index']))\n")
gate('actual-reference-index-v1',sys.executable,'-B','-X','utf8',RUN/'native-reference-index-v1.py')
for label,command in [('mathlib-cards','list-mathlib'),('paper-cards','list-papers'),('weapon-cards','list-weapons')]:native(label+'-v1',command)
for query in ['empiricalMean_minimizes','squaredBestRegret','csInf']:
    native('memory-'+query+'-v1','search-memory',query)
    native('declarations-'+query+'-v1','list-lean-decls',query,'--statement')
gate('actual-draft-types-and-API-v1','lake','env','lean',RUN/'draft-types-v1.lean')
gate('actual-neutral-types-v1','lake','env','lean',CONTRACT/'neutral-context-v1.lean')
fixed();print('Six draft Prop types/four neutral definitions actually compile; distinct reconstruction/source stabilization still pending.')
