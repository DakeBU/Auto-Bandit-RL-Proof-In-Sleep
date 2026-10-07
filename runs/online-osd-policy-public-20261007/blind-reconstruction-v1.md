# Source-blind finite-history policy reconstruction

Actor: `/root/osd_blind`. Requested model/effort: GPT-6 Astra / medium. Runtime model attested: false.

Decoder-history disclosure: this same decoder previously read and reconstructed the two neutral fifteen-proposition interfaces in `online-osd-public-20261007` (v1 and v2). Therefore this is not a first-exposure or history-free decoder. For this reconstruction, the only file read was the present `online-osd-policy-public-20261007/blind-packet-v1.md`. No repository search, source text, target proofs, actual-name maps, or prior reviewer verdicts were inspected. Prior neutral exposure is disclosed rather than represented as source-intent knowledge. The present twenty-one statements are decoded from this packet.

## Common meaning and notation

Every P01-P21 retains the printed binders `{E : Type*}`, `[NormedAddCommGroup E]`, `[InnerProductSpace R E]`, and `[instFD : FiniteDimensional R E]`. Write V for the carrier of a nonempty closed convex domain. Its actual projection Pi_V(z) is in V and minimizes distance from z over V.

For an extended-real function f, properness is exactly nowhere minus infinity on the entire ambient E and finite at at least one ambient point. The support set is
\[
\partial f(x)=\{g:\forall y\in E,\ f(x)+\operatorname{embed}(\langle g,y-x\rangle)\le f(y)\}.
\]
The universal comparison is ambient, not restricted to V, its interior, or a finite-valued subset. Write S_V(f) for properness and existence of at least one such support at every feasible point. Properness alone does not imply finiteness everywhere. Properness plus a support at x does imply finiteness at x, because a finite ambient witness rules out a supported positive-infinite value. The ordinary real losses in the inequalities require that finite-value meaning: EReal.toReal sends BOTH infinities to zero and preserves finite reals. Define f(x)^r=(f(x)).toReal; it is not an unconditional faithful conversion at infinity.

A policy has exactly the type
\[
p:(t:\mathbb N)\to(\operatorname{Fin}t\to(E\to\overline{\mathbb R}))\to(\operatorname{Fin}(t+1)\to E)\to(E\to\overline{\mathbb R})\to E.
\]
Its explicit inputs are time, exactly t past whole loss functions, exactly t+1 output points including the current output, and the current whole loss. Finite history length does not mean finite-query access to each function or executable evaluation. The type does not include future losses or the entire schedule as direct arguments. However policy p, initial a, and schedule are externally prescribed parameters; nothing prevents their external construction from encoding other information. No external-parameter independence, probability law, filtration, measurability, or executable oracle claim is supplied.

For one actual run with inputs (V,eta,f,a,p), let H_t:Fin(t+1)->E be its constructed history, x_t=H_t(t), and
\[
F_{<t}(i)=f_{i.\mathrm{val}},\qquad g_t=p(t,F_{<t},H_t,f_t),\qquad
H_0=(a),\qquad H_{t+1}=H_t\mathbin{\mathrm{snoc}}\Pi_V(x_t-\eta_tg_t).
\]
Thus x_t is formed before using f_t for the next update; p uses the actual constructed H_t, not a separately supplied sequence. Snoc keeps earlier outputs and appends the actual projected successor. The argument named x1 in Lean is a=x_0. In a one-based round convention, Lean t=0 is round 1, f_t corresponds to round t+1, and x_T is the output after T updates (the round T+1 point), not the last point charged in T-round regret.

Played legality is
\[
L_T(V,\eta,f,a,p):\quad\forall t<T,\quad g_t\in\partial f_t(x_t),
\]
only on this actual run and prefix. In contrast the stronger optional off-path law is
\[
O_V(p):\quad\forall t,F,h,f,\quad S_V(f)\land h(t)\in V\ \Longrightarrow\ p(t,F,h,f)\in\partial f(h(t)).
\]
Here F and h can be arbitrary typed histories, not necessarily actual or mutually consistent; only the last point of h must be feasible. Past losses need not satisfy regularity and older h entries need not be feasible. The law is conditional on current regularity and last-point feasibility. It is not bundled into the policy type. P09 uses it as a sufficient route to played legality; the performance statements instead take actual played legality directly, except the single-round versions that take one actual membership premise.

Define the real-valued regret
\[
R_T(u)=\sum_{t=0}^{T-1}\bigl(f_t(x_t)^r-f_t(u)^r\bigr).
\]
All selected vectors, histories, outputs, and regrets within a statement are from the same specified recursion and schedule. Each section uses seven slots: (1) objects/binders; (2) quantifier/information scope; (3) hypotheses; (4) operation; (5) conclusion in words and mathematics; (6) constants/indices; (7) limits and degeneracies. These organizational labels introduce no new hypotheses.

## P01

1. **Objects/binders:** Common finite-dimensional binders; arbitrary V,eta,f,a,p.
2. **Scope:** Universal over all run inputs, including arbitrary initial point and arbitrary policy.
3. **Hypotheses:** None beyond the common domain/space structure.
4. **Operation:** Construct the base history H_0 by the given recursion.
5. **Conclusion:** The initial history is the constant one-entry function: \(H_0=(i\mapsto a)\).
6. **Constants/indices:** Domain of H_0 is Fin(1), not an empty history. No loss has been played.
7. **Limits:** No initial feasibility, positive rate, regular loss, or legal policy assumption. This is a structural equality, not a performance guarantee.

## P02

1. **Objects/binders:** Common binders; arbitrary V,eta,f,a,p and natural t.
2. **Scope:** At every natural t of the actual run, for arbitrary policy.
3. **Hypotheses:** No regularity, feasibility, sign, or legality premises.
4. **Operation:** Use actual H_t to select g_t from its finite past and current f_t, then project x_t-eta_t g_t.
5. **Conclusion:** The history successor appends precisely that projection: \(H_{t+1}=\operatorname{snoc}(H_t,\Pi_V(x_t-\eta_tg_t))\).
6. **Constants/indices:** Fin(t+1) grows to Fin(t+2); prior entries remain and the new entry is at t+1. Current update uses rate eta_t and loss f_t.
7. **Limits:** Even an illegal vector or negative rate is permitted in this structural description. The appended vector is not an independently assumed next iterate.

## P03

1. **Objects/binders:** Common binders; arbitrary V,eta,f,a,p.
2. **Scope:** Every run, at time zero.
3. **Hypotheses:** No feasibility or loss/policy assumptions.
4. **Operation:** Take the last entry of the base history.
5. **Conclusion:** The first output equals the external initial value: \(x_0=a\).
6. **Constants/indices:** Lean output 0 equals the argument called x1; no off-by-one update occurs before it.
7. **Limits:** This does not imply a is feasible or independent of future information.

## P04

1. **Objects/binders:** Common binders; arbitrary V,eta,f,a,p,t.
2. **Scope:** Universal current time for the same actual run.
3. **Hypotheses:** No sign, legality, or feasible-initial-point premise.
4. **Operation:** Read the last entry after the actual snoc update.
5. **Conclusion:** The output obeys the projected update exactly: \(x_{t+1}=\Pi_V(x_t-\eta_tg_t)\).
6. **Constants/indices:** Uses actual g_t selected at x_t; the successor is t+1.
7. **Limits:** A recursion identity does not assert that g_t is a support or that losses are finite.

## P05

1. **Objects/binders:** Common binders; V,eta,f,a,p,t and i:Fin(t+1).
2. **Scope:** After fixing a feasible initial value, all times and every entry in the actual history.
3. **Hypotheses:** a in V; no other feasibility, regularity, sign, or legality conditions.
4. **Operation:** Construct H_t by the actual projection recursion and select arbitrary entry i.
5. **Conclusion:** Every recorded output is feasible: \(\forall t,\forall i\in\operatorname{Fin}(t+1),\ H_t(i)\in V\).
6. **Constants/indices:** Includes the initial entry i=0 and latest entry i=t.
7. **Limits:** Applies even to illegal policies or zero/negative schedules. Feasibility alone does not establish support legality or finite loss.

## P06

1. **Objects/binders:** Common binders; V,eta,f,a,p,t.
2. **Scope:** Any natural time in a run with fixed feasible initial value.
3. **Hypotheses:** a in V only beyond structural assumptions.
4. **Operation:** Take the last point x_t of actual H_t.
5. **Conclusion:** The played/current output stays feasible: \(x_t\in V\).
6. **Constants/indices:** Holds at t=0 as well as after every update.
7. **Limits:** No positivity, legal feedback, or current-loss regularity is inferred or required.

## P07

1. **Objects/binders:** Common binders; V, two schedules eta,eta', two loss sequences f,f', common a,p, and t.
2. **Scope:** The two runs keep the very same domain, initial point, and policy. Agreement is over every s<t, not at or after t.
3. **Hypotheses:** \(\forall s<t,\eta_s=\eta'_s\) and \(\forall s<t,f_s=f'_s\) as WHOLE ambient functions. No feasibility or legality premise.
4. **Operation:** Construct both actual histories with their own agreed prefixes and common p.
5. **Conclusion:** The full history functions agree: \(H_t(V,\eta,f,a,p)=H_t(V,\eta',f',a,p)\).
6. **Constants/indices:** Equality covers all t+1 recorded points. At t=0 prefix conditions are vacuous and both histories are (a).
7. **Limits:** Does not follow merely from equal observed scalar losses; does not compare different policies; does not constrain future-dependent external selection of p,a,eta. It is strict-prefix invariance, not a stochastic adaptedness theorem.

## P08

1. **Objects/binders:** Common binders; V,eta,eta',f,f',same a,p,t.
2. **Scope:** Same-policy, same-initial-point comparison with strict past-function/rate agreement.
3. **Hypotheses:** \(\forall s<t,\eta_s=\eta'_s\) and \(\forall s<t,f_s=f'_s\); no other regularity or feasibility requirements.
4. **Operation:** Take the last entries of the two actual time-t histories.
5. **Conclusion:** Current outputs agree: \(x_t(V,\eta,f,a,p)=x_t(V,\eta',f',a,p)\).
6. **Constants/indices:** Current f_t need not agree, so no selected-vector equality at t is stated. At t=0 both outputs equal a.
7. **Limits:** It does not make future-dependent external parameters independent of the future, or provide equal outputs for different policies or merely matching scalar observations.

## P09

1. **Objects/binders:** Common binders; V,eta,f,a,p and natural horizon T.
2. **Scope:** After feasible initialization, assume the universal off-path law, then regularity of every played loss; conclude legality for this actual run.
3. **Hypotheses:** a in V, O_V(p), and S_V(f_t) for each t<T. No positive rate requirement.
4. **Operation:** Feed p the actual finite loss prefix, actual H_t, and current f_t.
5. **Conclusion:** Played legality holds: \(L_T(V,\eta,f,a,p)\), i.e. \(\forall t<T,g_t\in\partial f_t(x_t)\).
6. **Constants/indices:** Natural T may be zero; legality then has no instances. Only losses at t<T need regularity.
7. **Limits:** Universal off-path law is sufficient here and stronger than played legality; it is not a necessary extra premise of every later performance statement. No legality beyond the prefix follows without more assumptions.

## P10

1. **Objects/binders:** Common binders; V,eta,f,a,p,t and feasible comparator u.
2. **Scope:** Arbitrary policy/run with feasible initialization and current regular loss, then every feasible u.
3. **Hypotheses:** a in V, S_V(f_t), u in V. Neither played legality nor O_V(p) is required.
4. **Operation:** Evaluate the current loss at actual output x_t and comparator u, convert toReal, and embed back.
5. **Conclusion:** Both values are finite: \(f_t(x_t)=\operatorname{embed}(f_t(x_t)^r)\) and \(f_t(u)=\operatorname{embed}(f_t(u)^r)\).
6. **Constants/indices:** Exact equalities for the same current loss; no rate condition and no horizon.
7. **Limits:** Existence of supports at feasible points suffices for finiteness even if this policy chooses an illegal vector. Since both infinities map to zero, the conclusion cannot be replaced by unconditional toReal faithfulness.

## P11

1. **Objects/binders:** Common binders; arbitrary V,eta,f,a,p,t and feasible u.
2. **Scope:** Fix any actual run and current t, then current positivity, regularity, actual selected support membership, and feasible u. Crucially there is NO a in V or x_t in V premise.
3. **Hypotheses:** eta_t>0, S_V(f_t), g_t in partial f_t(x_t), and u in V. Properness plus the actual support gives finiteness at the possibly infeasible x_t; regularity on V gives comparator finiteness.
4. **Operation:** Use actual g_t and actual projected x_{t+1}. No supplied loss-progress inequality is assumed.
5. **Conclusion:** The conjunction forming this chain holds:
   \[
   \eta_t(f_t(x_t)^r-f_t(u)^r)\le\eta_t\langle g_t,x_t-u\rangle
   \le\frac{\|x_t-u\|^2}{2}-\frac{\|x_{t+1}-u\|^2}{2}+\frac{\eta_t^2}{2}\|g_t\|^2.
   \]
6. **Constants/indices:** Half squared potentials, negative successor term, and squared eta_t/2 support penalty; t and t+1 are distinct.
7. **Limits:** Current rate zero excluded. No global off-path law, earlier legality, feasible initialization, diameter, or uniform gradient bound. At t=0 an infeasible a is permitted if its selected vector meets the support premise.

## P12

1. **Objects/binders:** Common binders; arbitrary V,eta,f,a,p,t,u.
2. **Scope:** Same arbitrary-initial-point current-round scope as P11; only comparator feasibility is required.
3. **Hypotheses:** eta_t>0, S_V(f_t), actual g_t in partial f_t(x_t), u in V. No a in V premise.
4. **Operation:** The actual same-run projection successor and actual selected vector.
5. **Conclusion:** The current real loss difference is bounded by potential decrease and a norm penalty:
   \[
   f_t(x_t)^r-f_t(u)^r\le\frac{\|x_t-u\|^2-\|x_{t+1}-u\|^2}{2\eta_t}+\frac{\eta_t}{2}\|g_t\|^2.
   \]
6. **Constants/indices:** Divide the whole squared-distance difference by 2 eta_t; support penalty eta_t/2, not eta_t squared/2.
7. **Limits:** Zero rate excluded; support premise supplies finiteness for an arbitrary current query. No full-prefix legality, off-path law, or cumulative performance assumption is added.

## P13

1. **Objects/binders:** Common binders; V,positive real eta,losses,a,p,natural T,u.
2. **Scope:** Fixed scalar eta, then run inputs, feasible initialization,T, prefix regularity and same-run legality, then feasible comparator.
3. **Hypotheses:** eta>0, a,u in V, S_V(f_t) for t<T, and L_T for the CONSTANT eta run. V may be unbounded; O_V(p) is not required.
4. **Operation:** Actual policy recursion with eta_s=eta for every s; all g_t and x_T in the conclusion use this run.
5. **Conclusion:**
   \[
   R_T(u)\le\frac{\|a-u\|^2}{2\eta}+\frac{\eta}{2}\sum_{t=0}^{T-1}\|g_t\|^2-\frac{\|x_T-u\|^2}{2\eta}.
   \]
6. **Constants/indices:** Negative terminal residual retained. T losses at 0,...,T-1 and output endpoint T. Exact half coefficients.
7. **Limits:** T=0 allowed: empty regret/sum and cancellation of initial/terminal distances. Eta=0 excluded. No global norm/diameter assumption or supplied per-step performance premise.

## P14

1. **Objects/binders:** Common binders; V,positive scalar eta,losses,a,p,natural T,u.
2. **Scope:** Same constant-schedule ordering as P13, for every feasible comparator after played legality.
3. **Hypotheses:** eta>0, a,u in V, prefix S_V(f_t), and L_T of the same constant run; no off-path law or bounded domain requirement.
4. **Operation:** Actual constant-step policy run and its selected vectors.
5. **Conclusion:**
   \[
   R_T(u)\le\frac{\|a-u\|^2}{2\eta}+\frac{\eta}{2}\sum_{t=0}^{T-1}\|g_t\|^2.
   \]
6. **Constants/indices:** No terminal residual in this conclusion. Coefficients remain 1/(2 eta) and eta/2.
7. **Limits:** T=0 allowed, giving 0<=||a-u||^2/(2 eta). No square-root rate is asserted without tuning and same-run norm control.

## P15

1. **Objects/binders:** Common binders; V,variable eta,losses,a,p,positive T,real D,u.
2. **Scope:** Run inputs and feasible initialization, positive horizon, played-prefix rate/regularity/legality conditions, then D with all-pairs diameter bound, then feasible u.
3. **Hypotheses:** a,u in V; T>0; eta_t>0 for t<T; eta_{t+1}<=eta_t whenever t+1<T; S_V(f_t) for t<T; L_T of this run; ||x-y||<=D for all x,y in V.
4. **Operation:** Actual variable-schedule policy recursion; each norm refers to its own selected vector on this run.
5. **Conclusion:**
   \[
   R_T(u)\le\frac{D^2}{2\eta_{T-1}}+\sum_{t=0}^{T-1}\frac{\eta_t}{2}\|g_t\|^2-\frac{\|x_T-u\|^2}{2\eta_{T-1}}.
   \]
6. **Constants/indices:** Last PLAYED rate eta_{T-1}, not eta_T, occurs in both outer denominators; each summand has its own eta_t/2. Negative endpoint residual.
7. **Limits:** T=0 excluded; T=1 has vacuous monotonicity. No explicit D>0 is required; domain nonemptiness and diameter premise imply D>=0, with D=0 allowed. No rate conditions after the played prefix or universal off-path law.

## P16

1. **Objects/binders:** Common binders; V,variable schedule,losses,a,p,positive T,u.
2. **Scope:** After run, feasibility, horizon, prefix rate/regularity/legality premises, require bounded V and then feasible u.
3. **Hypotheses:** a,u in V; T>0; all played rates positive and nonincreasing across adjacent played indices; all played losses S_V; L_T; Bornology.IsBounded(V).
4. **Operation:** Actual variable-step policy run; use d=Metric.diam(V) rather than an arbitrary D upper bound.
5. **Conclusion:**
   \[
   R_T(u)\le\frac{d^2}{2\eta_{T-1}}+\sum_{t=0}^{T-1}\frac{\eta_t}{2}\|g_t\|^2-\frac{\|x_T-u\|^2}{2\eta_{T-1}}.
   \]
6. **Constants/indices:** Metric.diam is the real conversion of extended diameter; both endpoint terms use the last played eta_{T-1}. Terminal term remains negative.
7. **Limits:** Boundedness is essential to the claimed finite-diameter meaning and is not dropped because Metric.diam has type real. Singleton diameter zero allowed. Positive T required; T=1 monotonicity vacuous; no off-path law required.

## P17

1. **Objects/binders:** Common binders; V,losses,a,p,positive natural T,positive real D,G,u.
2. **Scope:** After fixed run inputs and feasible a, positive T,D,G and prefix regularity, require legality for the tuned run, then feasible comparator with initial-distance bound, then same-run norm bound.
3. **Hypotheses:** a,u in V; T,D,G>0; S_V(f_t) for t<T; L_T for eta_star=D/(G sqrt(T)); ||a-u||<=D; ||g_t||<=G for all t<T on THAT eta_star run.
4. **Operation:** Set constant eta_star, construct the actual policy history under it, and use that run in legality, norm bounds, and regret. Policy can depend on actual output history, so the selected vectors can change with eta_star.
5. **Conclusion:** Comparator-specific tuned regret satisfies
   \[
   R_T(u;\eta_\star,p)\le DG\sqrt T,\qquad\eta_\star=\frac{D}{G\sqrt T}.
   \]
6. **Constants/indices:** Leading constant 1; T coerced to real inside sqrt; norm/legality for t<T. No terminal residual in the displayed bound.
7. **Limits:** T=0,D=0,G=0 excluded. D bounds only this initial distance, not necessarily domain diameter. Actual norms or distance may be zero with positive upper bounds. No transfer from another eta-dependent run, all-points norm bound, off-path law, or anytime claim.

## P18

1. **Objects/binders:** Common binders; V,losses,a,p,positive T,D,G.
2. **Scope:** Fix those inputs and prefix regularity/legality, all-pairs diameter and same-run norm bounds; THEN quantify over every u in V with one common run and constants.
3. **Hypotheses:** a in V; T,D,G>0; S_V(f_t) for t<T; L_T on eta_star=D/(G sqrt(T)); ||x-y||<=D for all feasible x,y; ||g_t||<=G on the same tuned run for t<T.
4. **Operation:** Actual tuned history-policy recursion independent of comparator u, with same selected vectors in all assumptions and conclusions.
5. **Conclusion:** Uniform feasible-comparator bound:
   \[
   \forall u\in V,\quad R_T(u;\eta_\star,p)\le DG\sqrt T.
   \]
6. **Constants/indices:** Exact constant 1, fixed positive horizon, played indices 0,...,T-1. D is a common diameter upper bound, not necessarily exact Metric.diam.
7. **Limits:** Strict positivity remains when actual diameter/norms are zero. No minimizer existence, infimum attainment, all off-path legality, external parameter independence, or anytime rate is asserted.

## P19

1. **Objects/binders:** Common binders, including the explicit finite-dimensional instance even if unused; any V.
2. **Scope:** OracleLaw universally quantifies over time, arbitrary past whole functions, arbitrary typed h, and current f, including off-path histories.
3. **Hypotheses:** Within that conditional law, S_V(f) and last point h(t) in V. No regularity/feasibility requirement on older entries and no history consistency premise.
4. **Operation:** Define canonical policy p_c(t,F,h,f)=c(f,h(t)), with c choosing a global support if nonempty and zero otherwise. It ignores F and all older h entries.
5. **Conclusion:** Canonical policy satisfies the off-path law:
   \[
   O_V(p_c),\quad\text{equivalently }S_V(f)\land h(t)\in V\Rightarrow c(f,h(t))\in\partial f(h(t)).
   \]
6. **Constants/indices:** Last entry is Fin.last t at index t in a length t+1 history; no numerical regret constant or horizon.
7. **Limits:** The guarantee remains conditional, not legality for arbitrary nonregular f/infeasible query. Classical choice and zero fallback are exact; no executable or minimum-norm choice is implied.

## P20

1. **Objects/binders:** Common binders; arbitrary V,eta,f,a,t, with policy fixed to p_c.
2. **Scope:** All schedules, losses, initial points, and times, without initial feasibility or regularity.
3. **Hypotheses:** None beyond common structural types.
4. **Operation:** Compare canonical-policy history output with the packet's borrowed current-only recursion y_0=a, y_{t+1}=Pi_V(y_t-eta_t c(f_t,y_t)). Both use the same actual c and projection, including fallback.
5. **Conclusion:** Exact identity of outputs: \(x_t(V,\eta,f,a,p_c)=y_t(V,\eta,f,a)\).
6. **Constants/indices:** Same t on both sides; t=0 yields a=a. Equality rather than approximation or equality of bounds.
7. **Limits:** This adapter covers only the precise canonical policy, not arbitrary policies choosing other legal supports. No proof of target performance or literature attribution is supplied by this equality description.

## P21

1. **Objects/binders:** Common binders; arbitrary V,eta,f,a,t, policy fixed to p_c.
2. **Scope:** All run inputs and times; no feasibility, positivity, support-existence, or OracleLaw premises.
3. **Hypotheses:** None beyond structural context.
4. **Operation:** Select from the canonical history run and compare with c evaluated at the borrowed current-only iterate y_t using the same f_t.
5. **Conclusion:** Exact selected-vector identity:
   \[
   g_t(V,\eta,f,a,p_c)=c(f_t,y_t(V,\eta,f,a)).
   \]
6. **Constants/indices:** Both sides use current loss t and current point t, not successor t+1. Equality is exact, including the zero fallback when a support set is empty.
7. **Limits:** Identity alone does not certify support membership at irregular functions or infeasible queries. It does not equate arbitrary legal policies with the canonical choice or claim source fidelity.

## Evidence boundary

The packet supplies proposition definitions, borrowed mathematical context, and context elaboration, not target theorem proofs. A `Prop` description elaborating successfully is not proof of the proposition. This report reconstructs the exact described interfaces, hypotheses, and conclusions only. It makes no source-intent review, source acceptance, proof validation, integrated library gate, chapter-completion, or Goal-completion claim.
