from common_reviewed_v1 import *
headers_fixed(4)
names=[r['name'] for r in load(CONTRACT/'targets-v1.json')['targets']]
model=('Fix one infinite process Y on a probability space. Every Y_t is measurable, has the law of Y_0, '
    'and belongs to [0,1] almost surely. Joint IID is required for the policy criterion and learner success, '
    'but not for the mean-predictor upper bound. All necessary square integrability is derived from a.s. support.')
seed_model=('For the policy criterion, S is a measurable private tape independent of the WHOLE target process. '
    'Each pi_t is jointly measurable and feasible for EVERY seed on legal strict-past unit histories. '
    'The actual prediction is P_t=pi_t(S,Y_<t). One process and one policy are fixed before all horizons. '
    'The criterion characterizes success; it does not assert every policy converges.')
metric=('A_T=E[sum_{t<T}(P_t-Y_t)^2], m=E[Y_0], v=Var(Y_0), '
    'B_T=min_{u in[0,1]} E[sum_{t<T}(u-Y_t)^2]=T v. The population mean is a feasible minimizer. '
    'The comparator is fixed before expectation; B_T is not E[min_u sum loss]. E_T=A_T-B_T.')
boundary=('Only this bounded explicit private-tape model is covered by the policy result. Universal stochastic-kernel, '
    'completed-information and AE-factorization source coverage remains required. Five old main-relative module '
    'audits remain required; the remote push contributor check still fails on those contracts. '
    'Original sixteen Chapter1 source objects and unknown(null) proof-leaf total are retained. '
    'Chapter1/2 remain open, Chapters3–16 are unenumerated, necessary appendices are required and the total Goal is ACTIVE. '
    'This work is stacked on OPEN draft unmerged PR195 exact372c9a6c138c50d7a5e08e91351238f231565219. '
    'Canonical main6847 is unchanged; no merge, deployment or live update. No high-probability, almost-sure, '
    'minimax or full strategy-class guarantee is asserted.')
index=('Source rounds1..T correspond to Lean0..T-1. The actual learner predicts1/2 initially and then the '
    'empirical mean of exactly the strictly earlier observations. It receives no population mean, law or horizon. '
    'Normalized expressions are defined atT0, but their arithmetic equality is used only eventually forT>0. '
    'Ordinary expected zero convergence and magnitude little-o are distinct from adversarial eventual-upper-epsilon NoRegret.')
proof=('For positive T, (A_T-Tv)/T=A_T/T-v. The standard little-o quotient criterion therefore gives '
    'sublinear centered excess iff the average excess tends to zero. The existing causal private-seed producer gives '
    'E_T=sum E[(P_t-m)^2]>=0, so this is also equivalent to vanishing Cesaro mean squared deviation. '
    'For the actual mean learner, source Theorem1.3 bounds loss minus the empirical hindsight minimum pathwise. '
    'That empirical minimum is at most the loss of the fixed population comparator m. Integrate this inequality '
    'using derived L2, and use expected fixed loss at m=Tv to obtain E_T<=4+4lnT even without independence. '
    'With joint IID the causal lower bound also gives E_T>=0. Sandwich E_T/T between0 and(4+4lnT)/T, '
    'whose limit is zero. Apply the same normalization adapter to obtain little-o.')
formula=r'\begin{aligned}A_T&=\mathbb E[\sum_{t<T}(P_t-Y_t)^2],\quad v=\operatorname{Var}(Y_0),\\\mathcal E_T&=A_T-\min_{u\in[0,1]}\mathbb E[\sum_{t<T}(u-Y_t)^2]=A_T-Tv,\\\mathcal E_T=o(T)&\iff A_T/T-v\longrightarrow0\iff\frac1T\sum_{t<T}\mathbb E[(P_t-\mathbb E Y_0)^2]\longrightarrow0,\\x_0&=\tfrac12,\quad x_t=\frac1t\sum_{i<t}Y_i\ (t>0),\\0\le\mathcal E_T(x)&\le4+4\ln T\ (T\ge1,\ \text{IID}),\quad\mathcal E_T(x)/T\longrightarrow0.\end{aligned}'
card=dict(label='Stochastic success and the actual sample-mean learner',pages='printed1–2,4 / PDF13–14,16',
    pdf_page=13,url='https://arxiv.org/pdf/1912.13213v10',math=formula,plain=proof,fallback=proof,
    relationship='Equations(1.1)/(1.2) motivate success. S001 is a generic arithmetic adapter; S003/S004 are derived stochastic applications of Theorem1.3, not newly numbered source results.',
    contract=dict(model=model,assumptions=model+' '+seed_model,parameters=index,
        regret=metric,guarantee=proof+' '+boundary),
    local_status=dict(status='compiled',label='Four fixed proof terminals compiled locally',
        boundary='Focused bodies and nondegenerate canaries compiled; distinct CONTRACT passed. BODY/combined/reader/FINAL/native/delivery gates remain separate. '+boundary))
notes_data=[
    ('A centered total is sublinear exactly when its average excess vanishes',
     r'A_T-Tc=o(T)\iff A_T/T-c\longrightarrow0.',
     'Use the Mathlib little-o quotient criterion and the existing normalization identity eventually for positive horizons.',
     'Generic signed real total and c: no sign, monotonicity, convergence assumption, A_0=0 or c=0. AtT0 the average-minus-c and divided residual may differ. This adapter proves an equivalence, not a learner guarantee.',
     ['normalized_excess']),
    ('A private-seed policy succeeds exactly when its average mean-square error vanishes',
     r'\mathcal E_T=o(T)\iff A_T/T-v\longrightarrow0\iff T^{-1}\sum_{t<T}\mathbb E[(P_t-m)^2]\longrightarrow0.',
     'The actual causal policy produces nonnegative excess and its finite sum-of-squares identity. Normalize that identity and apply the centered-total adapter.',
     model+' '+seed_model+' '+metric+' This does not assert arbitrary policies are successful. The actual persistent private-bit canary has excessT/4 and is not successful.',
     ['centered_total_sublinear_iff_average','randomized_history_policy_expectedFixed_excess']),
    ('Integrate the sample-mean regret bound without an independence assumption',
     r'\mathcal E_T(x)\le4+4\ln T\quad(T\ge1).',
     'The pathwise empirical minimum is at most fixed population-mean loss. Compare before integration, derive square integrability, then use expected fixed loss at the mean=Tv.',
     model+' NO joint independence is assumed here. '+metric+' '+index+' This is a derived Theorem1.3 application; no nonnegative conclusion follows without IID. The repeated-target canary has two-round excess−1/4.',
     ['theorem_1_3','empiricalMean_minimizes','expected_fixed_prefix_decomposition','expectedFixedMinimum_eq_variance']),
    ('The real unknown-law sample-mean learner is stochastically successful',
     r'0\le\mathcal E_T(x)/T\le(4+4\ln T)/T\longrightarrow0,\qquad\mathcal E_T(x)=o(T).',
     'Combine the actual IID causal nonnegative lower bound with the integrated upper. The logarithmic ratio vanishes; a squeeze gives the ordinary zero limit, and the same generic adapter gives little-o.',
     model+' Joint IID is required for this lower-bound sandwich. '+index+' No convergence hypothesis is supplied. The fair infinite IID canary has positive variance1/4 and actual two-round excess1/4 while its same unknown-law learner tends to the benchmark.',
     ['meanPredict_expectedFixed_excess','meanPredict_expectedFixed_upper','centered_total_sublinear_iff_average'])]
notes=[]
for i,(title,math,idea,context,parents) in enumerate(notes_data):
    notes.append(dict(full_name=names[i],title=title,chapter='online-foundations',featured=False,
        teaching_order=85+i,plain=idea,math=math,intuition='Normalize the actual fixed-comparator expected excess.',
        why='Connect the source success definition to a real learner, with all information and integration hypotheses explicit.',
        position='One of four adapters/derived application proofs extending the preceding source cards; full Chapter1 remains open.',
        proof_idea=idea,lean_notes=context+' Remaining required program obligations are stated in the source card above.',
        dependencies=[PRE+n for n in parents]))
write(RUN/'reader-proposal-v1.json',dict(card=card,notes=notes,boundary=boundary,
    no_current_production_reader_edit=True,reader_requirements=load(RUN/'stabilized-contract-v1.json')['reader_requirements']))
headers_fixed(4)
