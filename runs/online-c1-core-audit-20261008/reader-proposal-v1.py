from common_proving_v1 import *
contract_bindings_fixed()
rows=load(CONTRACT/'targets-v2.json')['targets']
boundary=('This current package audits exactly five old core modules and reuses twelve public proofs; it adds no production theorem. '
    'Five source audits remain candidates until separate BODY, combined Lean/harness, stacked and origin/main contributor, reader/site/FINAL and native gates pass. '
    'Earlier cards and gap entries record their earlier package/head boundaries; this current five-module audit is a separate scoped update and preserves historical Foundation revalidation. '
    'Original sixteen Chapter 1 source objects and unknown (null) proof total are preserved. Full universal stochastic-kernel/completed-information/AE-factorization coverage, '
    'remaining Chapter 1 and Chapter 2 obligations, unenumerated Chapters 3–16 and necessary appendices remain REQUIRED. '
    'The whole Goal remains ACTIVE. Stacked on OPEN draft unmerged PR196 exact6b387a39e401cb1b90003fca6e49d3bdd9ce7a9a; canonical main6847 and live site are unchanged.')
source=('Orabona v10, 2026-06-21: Lemma1.2 is printed p.4 / PDF p.16, while the IID squared-loss motivation and Eq(1.1)/(1.2) are printed p.1 / PDF p.13. '
    'The initial-half strict-past mean learner is printed pp.3–4 / PDF pp.15–16. Source rounds1..T map to Lean0..T−1. '
    'One numbered lemma and eleven generic/derived/regularity/arithmetic APIs are represented here; these are not twelve numbered source results.')
proof=('For EVERY positive prefix n≤T, assume a feasible leader w_n minimizing its prefix loss against EVERY u∈V. '
    'Induct on T: compare the previous prefix with the next feasible leader and then add the current summand. This proves the hindsight Be-the-Leader inequality; supplied minimizers do not define a causal learner. '
    'For squared loss, subtract the mean and expand; the centered cross term integrates to zero. For independent random P,Y, covariance vanishes, giving E(P−Y)^2=E(P−EY)^2+Var(Y). '
    'The actual x_0=1/2, x_t=t^{-1}Σ_{i<t}Y_i depends only on strict past. Joint target independence and measurable finite sums/division derive its independence from Y_t; measurability and bounds derive L2. '
    'Under identical laws, integrate the finite sum, substitute the one-round identity and cancel T·Var(Y_0). Every resulting mean-square term is nonnegative. '
    'The population mean is feasible and attains the variance benchmark over ALL real fixed comparators; it is an analysis witness, not a learner input. '
    'A measurable scalar policy π_t of the strict finite-history tuple is independent of the current target by disjoint-coordinate independence and composition. Its L2 square identity gives a current-round variance lower bound WITHOUT same-law. '
    'Finally divide the scalar residual by T only for T>0. This last equality is not a convergence theorem.')
legacy=('Exact old types remain unchanged. A006–A009 and A011 require Y_t(ω)∈[0,1] for EVERY t,ω. '
    'A011 also requires π_t(z)∈[0,1] for EVERY real history tuple z, including illegal tuples. '
    'These are stronger API limitations than AE target support and legal-cube feasibility. Later accepted AE/legal-cube producers remain separate; no silent substitution is allowed. '
    'A002/A003 use probability and L2 only, and A003 consumes given independence. A004/A010 actually derive independence. '
    'Expected fixed comparator minimization is outside expectation; no expected hindsight minimum swap. Normalization at T0 can differ by −variance.')
formula=r'\begin{aligned}w_n&\in V,\quad\sum_{t<n}\ell_t(w_n)\le\sum_{t<n}\ell_t(u)\quad(0<n\le T,\ u\in V),\\\sum_{t<T}\ell_t(w_{t+1})&\le\sum_{t<T}\ell_t(w_T),\\\mathbb E(P-Y)^2&=\mathbb E(P-\mathbb EY)^2+\operatorname{Var}(Y)\quad(P\perp Y),\\x_0&=\tfrac12,\quad x_t=t^{-1}\sum_{i<t}Y_i\ (t>0),\\\mathbb E\sum_{t<T}(x_t-Y_t)^2-Tv&=\sum_{t<T}\mathbb E(x_t-m)^2\ge0\quad(\mathrm{IID}),\\A_T/T-v&=(A_T-Tv)/T\quad(T>0).\end{aligned}'
card=dict(label='Five legacy core modules: exact assumptions and reused proofs',pages='printed1,3–4 / PDF13,15–16',
    pdf_page=16,url='https://arxiv.org/pdf/1912.13213v10',math=formula,plain=proof,fallback=proof,
    relationship=source,contract=dict(model='Arbitrary action/loss domain for Lemma1.2; probability/L2 identities and actual strict-past real predictions for the derived APIs.',
    assumptions=legacy,parameters='Source round1=Lean0; supplied prefix leader(t+1) is hindsight. One infinite process and one learner before all horizons. T0 empty sums do not extend positive normalization.',
    regret='Population mean minimizes expected squared loss among fixed real u; with IID the [0,1] expected-fixed prefix minimum is T·Var(Y0), not E[min hindsight loss].',
    guarantee=source+' '+proof+' '+boundary),local_status=dict(status='compiled',
    label='Twelve existing proofs and actual canaries compiled locally; five audit candidates',boundary=legacy+' '+boundary))
items=[
 ('The fixed squared-loss identity holds for every real comparator',r'\mathbb E(u-Y)^2=\operatorname{Var}(Y)+(u-\mathbb EY)^2.',
 'Expand the square around the expectation. Integrability of the square and the mean follows from L2; the centered first moment vanishes.',
 'Probability space, real Y with MemLp Y 2 and arbitrary u∈ℝ; no boundedness or independence assumption. Comparator u=2 has loss5/2 for the positive-variance fair target.',[]),
 ('Independent random predictions: the consumer identity',r'P\perp Y\ \Longrightarrow\ \mathbb E(P-Y)^2=\mathbb E(P-\mathbb EY)^2+\operatorname{Var}(Y).',
 'Apply the variance-of-difference formula to L2 P,Y. Given independence makes covariance zero; subtracting the target mean leaves its variance unchanged.',
 'Both real variables are L2 and their independence is a premise. This consumer does not establish that P is a causal algorithm; the separate mean/history producers do.',[]),
 ('The real sample-mean prediction is independent of the current target',r'x_0=\tfrac12,\quad x_t=t^{-1}\sum_{i<t}Y_i,\qquad x_t\perp Y_t.',
 'At zero the actual prediction is constant. Otherwise, joint independence separates the strict-past coordinate sum from the current target; measurable division preserves independence.',
 'One infinite measurable jointly independent target family on a probability space, every natural time t. No same-law or boundedness premise. The learner receives no population mean, law or horizon.', ['meanPredict']),
 ('Measurability of the actual sample-mean learner',r'x_t(\omega)=\begin{cases}\tfrac12&t=0,\\t^{-1}\sum_{i<t}Y_i(\omega)&t>0.\end{cases}',
 'The fixed initial branch is measurable. Each later branch is a finite sum of measurable targets divided by a fixed real scalar.',
 'Coordinate measurability only; no measure, probability, independence, same-law or support hypothesis. This is derived regularity, not a performance result.',['meanPredict']),
 ('Legacy pointwise support implies square integrability',r'(\forall i,\omega,\ Y_i(\omega)\in[0,1])\ \Longrightarrow\ x_t\in L^2.',
 'Feasibility of every actual finite mean and its initial half bounds x_t between0 and1 at every sample point. Measurability and this bound yield L2 on a probability space.',
 'The exact legacy hypothesis is ∀iω, not AE support. It is a stronger API limitation; no independence or identical-law assumption is needed.',['meanPredict_measurable','meanPredict_mem']),
 ('Legacy IID excess is nonnegative for this actual learner',r'0\le\mathbb E\sum_{t<T}(x_t-Y_t)^2-T\operatorname{Var}(Y_0).',
 'Rewrite with the actual learner finite excess identity and sum the nonnegative integrals of squared estimation errors.',
 'Same infinite measurable, jointly independent, identically distributed process with ∀iω unit support. T0 gives zero. Expected nonnegativity is not a pathwise claim or an asymptotic rate.',['iid_meanPredict_excess']),
 ('The population mean is feasible and attains the fixed benchmark',r'm=\mathbb EY\in[0,1],\quad\mathbb E(m-Y)^2=\operatorname{Var}(Y)\le\mathbb E(u-Y)^2\quad(\forall u\in\mathbb R).',
 'Integrate the pointwise unit bounds to get mean feasibility. Substitute u=m in the generic square identity for attainment; its nonnegative extra square proves optimality for every real constant.',
 'Measurable pointwise-unit real Y on a probability space; no IID premise for this single-variable statement. The population mean is law dependent and used only as an analysis comparator, never as the unknown-law learner input.',['expected_square_decomposition']),
 ('A genuine scalar history policy is independent of the current target',r'P_t=\pi_t(Y_{<t}),\qquad P_t\perp Y_t.',
 'Joint coordinate independence separates range t from the singleton{t}. Compose the strict-past tuple with the given measurable scalar policy and select the current singleton coordinate.',
 'Any measurable policy ((↑range t)→ℝ)→ℝ, with measurable jointly independent targets and probability. No L2, support, identical-law or global policy bound is required here. Deterministic history composition does not represent every stochastic kernel.',[]),
 ('Legacy history loss is at least the current-round variance',r'\operatorname{Var}(Y_t)\le\mathbb E\bigl(\pi_t(Y_{<t})-Y_t\bigr)^2.',
 'Measurability and the two global unit bounds derive L2 for prediction and current target. The actual history-independence producer feeds the square identity; discard only the nonnegative mean-error integral.',
 'Exact stronger API: ∀iω target support and ∀z policy output in[0,1], including illegal history tuples. NO same-law premise; the benchmark is Var(Yt), not Var(Y0) without common law. Full randomized/completed-information source coverage remains required.',['history_policy_independent','independent_prediction_square']),
 ('Positive-horizon normalization is scalar arithmetic',r'A/T-v=(A-Tv)/T\quad(T>0).',
 'Positive natural T has nonzero real coercion. Clear the denominator and use distributivity.',
 'Arbitrary real total A and variance parameter v, only T>0. It supplies no probability, algorithm, sign, convergence or rate. At T0 the left side is−v, the right side0, as the v=1/4 canary verifies.',[])
]
missing=[r for r in rows if r['name'].split('.')[-1] not in ['lemma_1_2','iid_meanPredict_excess']]
assert len(missing)==len(items)==10
notes=[]
for i,(r,item) in enumerate(zip(missing,items)):
    title,math,idea,context,parents=item
    notes.append(dict(full_name=r['name'],title=title,chapter='online-foundations',featured=False,
    teaching_order=95+i,plain=idea,math=math,intuition='Read the exact assumptions before applying the shared proof.',
    why='Publish the existing core proof with a source-qualified explanation and its actual API boundary.',
    position=source,proof_idea=idea,lean_notes=context+' '+boundary,
    dependencies=[PRE+p for p in parents]))
old=load('website/content/highlights.json')['highlights']
lemma=dict(next(x for x in old if x['full_name']==PRE+'lemma_1_2'))
lemma['lean_notes']=lemma['lean_notes'].replace('This package revalidates one existing source lemma',
    'The earlier foundation-only package historically revalidated one existing source lemma').replace(
    'Chapter 1 source reconciliation and integration into main remain open; all nine main-relative contributor gaps are retained in the audit.',
    'At that earlier package/head, nine main-relative contributor gaps were retained. The existing historical acceptance and seven tests remain preserved; this current package separately audits five old core modules. Chapter 1 source reconciliation and integration into main remain open.')+' '+boundary
iid=dict(next(x for x in old if x['full_name']==PRE+'iid_meanPredict_excess'))
iid['why']='The actual learner produces this finite expected IID identity; it is a derived explanation of Eq(1.1), not another numbered theorem.'
iid['proof_idea']='Derive L2 and actual strict-past prediction independence. Integrate the finite sum; apply the independent square identity at each time. Identical laws replace the current mean/variance by those ofY0, and cancel T·Var(Y0). Each residual square integral is nonnegative.'
iid['lean_notes']='Exact old premises: probability, ∀t measurable Yt, joint independence, ∀t IdentDistrib(Yt,Y0), and ∀tω Ytω∈[0,1] POINTWISE. Same infinite process and actual x0=1/2/strict-past mean throughout; no unknown-law/future/horizon input. The pointwise support is a stronger API limitation; later AE producers are separate. T0 is the empty-sum extension. This finite identity alone does not prove success or a convergence rate. The fixed mean benchmark is outside expectation; no expected hindsight minimum swap. '+boundary
write(RUN/'reader-proposal-v1.json',dict(card=card,notes=notes,replacements=[lemma,iid],boundary=boundary,
    exact_R1_R8=load(CONTRACT/'reader-requirements-v1.json'),old_other_notes_and_all_source_cards_preserved=True,
    no_duplicate_name=True,current_reader_files_unmodified=True,chapter_complete=False,goal_complete=False))
contract_bindings_fixed()
print('Prepared one source card, ten missing notes and exact two permitted note corrections; no current reader mutation or acceptance.')
