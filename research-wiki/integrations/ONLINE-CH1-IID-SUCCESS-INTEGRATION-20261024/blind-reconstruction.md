# Source-blind decoding of Q1–Q4

## Exposure record and boundary

The sole mathematical input consulted was
maintenance-evidence/batch25-statement-seal-v1/neutral-statements.txt.
Its SHA256 was independently checked as
8cb9101fddd4626e3f1652cf06f48a0f4d362a89052e92668f6130d5279e393e.

No surrounding file, original source, theorem body, PR, card, manifest, seal file, or prior review was read. General workspace instructions and the decoder task were visible before reading the packet. No source identity, intended source theorem, attribution, or prior verdict was supplied to this decoder. Standard Lean/Mathlib semantics were used from knowledge. No upstream lookup was needed. This report reconstructs the signatures, does not prove them, and makes no source-fidelity claim. It remains source-blind at delivery and is ready for the parent to seal by its file hashes.

## Common notation and the four literal definitions

For a real sequence \(y:\mathbb N\to\mathbb R\), define
\[
 \bar y_n=\frac{\sum_{t=0}^{n-1}y_t}{n},\qquad
 p_t(y)=\begin{cases}\frac12,&t=0,\\
 \bar y_t,&t>0.
 \end{cases}
\]
Natural denominators are coerced into the reals. An empty sum is zero and real division by zero in Lean is zero. Thus \(\bar y_0=0\), while the explicit branch gives \(p_0(y)=1/2\). For \(t>0\), the prediction averages exactly observations \(0,\ldots,t-1\).

Write \(\mathbb E_\mu f=\int_\Omega f(\omega)\,d\mu(\omega)\). For real-valued observation and prediction sequences \(Y_t,P_t\), let
\[
 A_T(P,Y)=\mathbb E_\mu\!\left[\sum_{t=0}^{T-1}
                (P_t-Y_t)^2\right],
\]
\[
 B_T(Y)=\inf_{u\in[0,1]}
      \mathbb E_\mu\!\left[\sum_{t=0}^{T-1}(u-Y_t)^2\right],
 \qquad R_T(P,Y)=A_T(P,Y)-B_T(Y).
\]
These are respectively the loss term, expectedFixedMinimum, and expectedFixedRegret. The literal comparator is a real sInf of the image of [0,1], so the displayed infimum, rather than an asserted minimum operator, is the direct translation.

The optimization is outside the expectation: choose one deterministic scalar \(u\), use it at every time within the horizon and on every outcome, take its expected cumulative loss, and then take the infimum over \(u\). It is not the expected pathwise best scalar, not a scalar adapted to the seed or trajectory, and not a time-varying comparator. The optimization is separately defined for each \(T\), so the definition itself does not require a common optimizer across horizons.

In isolation the definitions quantify over an arbitrary measure and arbitrary functions and contain no integrability assumptions. Lean's real Bochner integral and real sInf are total operations, not automatically extended-real optimization. Under the probability, measurability and boundedness assumptions in Q2–Q4, all displayed losses have the ordinary finite expectation interpretation. For their concrete or bounded generic predictions, at \(T=0\) the cumulative losses and \(B_0\) are zero, hence \(R_0=0\).

For Q2 and Q4, let
\[
 m=\mathbb E_\mu Y_0,\qquad
 \sigma^2=\operatorname{Var}_\mu(Y_0)
          =\mathbb E_\mu[(Y_0-m)^2].
\]
The bounded measurable probability setting makes this the usual finite variance. The notation \(r_T=o(T)\) means that for every real \(\varepsilon>0\), eventually in natural \(T\),
\[
 |r_T|\leq\varepsilon |T|.
\]
It is a two-sided magnitude condition. All limits below are deterministic limits along natural horizons \(T\to\infty\); they are not almost-sure or in-probability convergence claims for realized losses.

## Q1

**Universal parameters.** Every function \(a:\mathbb N\to\mathbb R\) and every real scalar \(c\), without positivity, stochastic, regularity, or boundedness assumptions.

**Reconstruction.**
\[
 \bigl(a_T-Tc=o(T)\bigr)
 \quad\Longleftrightarrow\quad
 \lim_{T\to\infty}\left(\frac{a_T}{T}-c\right)=0.
\]
The total function and the constant are fixed before considering the horizon limit. The equivalence translates sublinear centered total into convergence of normalized total to \(c\). It does not assert that either condition holds for an arbitrary \(a,c\), nor provide a rate. The value at \(T=0\) is admitted in each sequence but is irrelevant to atTop. At zero the right sequence equals \(-c\), using real division by zero, regardless of \(a_0\).

**Binder ledger.**

- total: universally quantified data, type \(\mathbb N\to\mathbb R\).
- c: universally quantified data, type \(\mathbb R\).
- Each T in the two little-o lambda expressions and the Tendsto lambda is a locally bound natural horizon, not a separate hypothesis or existential witness.
- The eventual thresholds and positive accuracy parameters are implicit in standard little-o/Tendsto semantics. There is no explicit hypothesis binder in Q1.

## Q2

**Universal setting and assumptions.** For every outcome type \(\Omega\), seed type Seed, measurable-space structures on both, probability measure \(\mu\) on \(\Omega\), and observation sequence \(Y:\mathbb N\to(\Omega\to\mathbb R)\):

1. Every \(Y_t\) is measurable.
2. Every \(Y_t\) has the same distribution as \(Y_0\), both taken under \(\mu\).
3. For each \(t\), \(Y_t\in[0,1]\) almost surely under \(\mu\).
4. The family \(Y_t\), indexed by all natural times, is mutually independent under \(\mu\), in the finite-subfamily sense of iIndepFun. This is stronger than pairwise independence.

Also quantify over every measurable seed \(S:\Omega\to\mathrm{Seed}\) that is independent of the entire random sequence \(\omega\mapsto(t\mapsto Y_t(\omega))\) under \(\mu\), and every policy family
\[
 \pi_t:\mathrm{Seed}\times(\{0,\ldots,t-1\}\to\mathbb R)
                      \to\mathbb R.
\]
Each \(\pi_t\) is measurable for the standard product/function measurable structures. For every \(t\), every seed value \(s\), and every history \(z\) whose coordinates lie in [0,1], require \(\pi_t(s,z)\in[0,1]\).

Define, locally rather than by a further universal choice,
\[
 P_t(\omega)=\pi_t\!\left(S(\omega),
             (Y_i(\omega))_{i\in\{0,\ldots,t-1\}}\right).
\]
The input history is all strictly earlier observations. It contains neither the current observation nor future observations. A single seed random variable can encode policy randomness for all times. Its law is not specified, and no uniform-seed assumption or fresh independent draw each round is asserted. Independence is between the seed and the whole observation process. At \(t=0\) the history type is empty, and the prediction may depend on \(S\); it is not forced to equal \(1/2\). The bounded-history condition applies for all seed values, not merely almost all realized seeds or histories.

**Reconstruction.** For every such setting and policy, all three clauses hold:
\[
 \forall T\in\mathbb N,\qquad 0\leq R_T(P,Y),
\]
\[
 R_T(P,Y)=o(T)
 \quad\Longleftrightarrow\quad
 \lim_{T\to\infty}\left(\frac{A_T(P,Y)}{T}-\sigma^2\right)=0,
\]
\[
 \lim_{T\to\infty}\left(\frac{A_T(P,Y)}{T}-\sigma^2\right)=0
 \quad\Longleftrightarrow\quad
 \lim_{T\to\infty}\frac1T\sum_{t=0}^{T-1}
       \mathbb E_\mu[(P_t-m)^2]=0.
\]

The first clause is a finite-horizon statement including zero. The other two are equivalences of asymptotic properties. They do not assert that this arbitrary policy has sublinear regret or satisfies either limit. Their conjunction characterizes when these properties hold. The final condition is convergence to zero of the Cesaro mean of expected squared prediction errors relative to the deterministic population mean. It does not assert individual-time \(L^2\) convergence of \(P_t\), almost-sure convergence, or a convergence rate. Expectation in this clause includes all randomness carried by \(\Omega\), including the seed.

At \(T=0\), regret is zero, the normalized-loss-minus-variance sequence is \(-\sigma^2\), and the normalized sum of mean-square errors is zero. None of these initial values changes either limit. The signatures do not separately state a finite-horizon identity equating those normalized quantities.

**Binder ledger.**

- Ω: implicit universally quantified type in universe u.
- Seed: implicit universally quantified type in universe v.
- MeasurableSpace Ω and MeasurableSpace Seed: typeclass structure binders, with no additional topological assumptions.
- μ: universally quantified measure data.
- IsProbabilityMeasure μ: typeclass hypothesis asserting total mass one.
- Y: universally quantified observation data.
- hY: proof hypothesis; its internal ∀ t ranges over all natural times.
- hlaw: proof hypothesis; its internal ∀ t ranges over all natural times; both IdentDistrib measures are μ.
- hb: proof hypothesis; internal ∀ t is followed by an almost-everywhere outcome binder ω under μ. It is not an everywhere bound. Countability of natural times also permits a common conull event, but that reformulation is not the literal binder order.
- hind: proof hypothesis of mutual independence of the observation family.
- S: universally quantified seed function data.
- hS: proof hypothesis of seed measurability.
- hseed: proof hypothesis of seed/process independence. In its lambda, ω is an outcome and t is a natural coordinate of the entire process.
- policy: universally quantified dependent function data; its dependent binder t is natural and fixes the history subtype \(i:\uparrow(\mathrm{Finset.range}\ t)\).
- hp: proof hypothesis; internal ∀ t states measurability of the policy at each time.
- hpb: proof hypothesis; internal ∀ t s z ranges over a natural time, every Seed value, and every real history of that time's finite index type. Its premise ∀ i quantifies every history index. The arrow is implication from coordinatewise bounded history to bounded policy output.
- prediction: local let definition in the conclusion, not an assumption, proof witness, or existentially quantified predictor. Its lambda binders t and ω are time and outcome; the history lambda binder i is a subtype index coerced to its underlying natural number in Y i ω.
- ∀ T in the first conjunct: universal conclusion over every natural horizon.
- T in all other lambda expressions: locally bound natural horizon of a deterministic sequence.
- t in every finite sum: bound natural summation index with range \(0\leq t<T\).
- ω in every integral: bound outcome integrated under μ. The inner ∫ ω, Y 0 ω ∂μ in the final clause uses a fresh local binder and produces the constant m; it does not share the outer outcome variable.

## Q3

**Universal setting and assumptions.** For every measurable outcome type \(\Omega\), probability measure \(\mu\), and sequence of measurable real random variables \(Y_t\) with identical marginal distributions to \(Y_0\) and \(Y_t\in[0,1]\) almost surely for each time, and for every natural horizon \(T>0\), use the specific predictor
\[
 P_0=\frac12,\qquad
 P_t=\frac1t\sum_{i=0}^{t-1}Y_i\quad(t>0).
\]

**Reconstruction.**
\[
 R_T(P,Y)\leq 4+4\ln T,\qquad T\in\mathbb N,\ T>0.
\]
Here log is the natural real logarithm and \(T\) is coerced to a real. This is an exact finite-horizon upper bound with constant term 4 and logarithmic coefficient 4. No observation independence assumption, seed, general policy quantifier, or other stochastic-feedback condition appears. Temporal dependence is allowed. The predictor uses the full strict past through the displayed empirical average.

Q3 does not assert a lower bound on expectedFixedRegret. With dependence, a history-based predictor need not have nonnegative regret relative to the best deterministic fixed expected-loss comparator. Consequently this one-sided upper bound alone is not an absolute-value sublinear-regret claim, nor a conclusion that \(R_T/T\to0\). Q3 does not include \(T=0\) in its conclusion. The literal prediction and regret definitions are still defined at zero, with \(R_0=0\). The strictly positive restriction is part of the theorem even though Lean also totalizes log at zero.

**Binder ledger.**

- Ω: implicit universally quantified type in universe u.
- MeasurableSpace Ω: typeclass structure binder.
- μ: universally quantified measure data.
- IsProbabilityMeasure μ: typeclass probability hypothesis.
- Y: universally quantified observation sequence.
- hY: proof hypothesis \(\forall t\in\mathbb N\), measurability.
- hlaw: proof hypothesis \(\forall t\in\mathbb N\), identical distribution with Y 0 under μ.
- hb: proof hypothesis with internal natural t and μ-almost-everywhere outcome ω binders.
- T: universally quantified natural horizon data.
- hT: proof hypothesis \(0<T\).
- t and ω in the supplied prediction lambda: local time and outcome binders.
- i in the inner lambda supplied to meanPredict: a natural sequence index, so meanPredict receives the complete sample-path sequence as an argument; its literal definition only uses the strict past.
- There is no hind binder, independent seed, policy measurability/boundedness binder, or universal conclusion over generic predictions.

## Q4

**Universal setting and assumptions.** For every measurable outcome type \(\Omega\), probability measure \(\mu\), and measurable, identically distributed, almost-surely [0,1]-valued observation sequence \(Y_t\), additionally assume mutual independence of the whole natural-indexed family. Use the same specific empirical-mean predictor as Q3.

**Reconstruction.**
\[
 \lim_{T\to\infty}\frac{R_T(P,Y)}{T}=0
 \quad\text{and}\quad R_T(P,Y)=o(T).
\]
Both assertions hold unconditionally once these hypotheses are supplied. The conjunction is not an implication or merely a characterization of when convergence occurs. Although the two asymptotic formulations are equivalent for real sequences over eventually positive natural horizons, the signature explicitly asserts both.

There is no finite-horizon restriction \(0<T\), because the conclusion concerns sequences indexed by every natural T and their atTop behavior. The zero term uses \(R_0/0=0\) and has no effect on convergence. No convergence rate, realized/sample-path regret limit, distribution-free guarantee for dependent observations, or generic-policy guarantee is included in Q4.

**Binder ledger.**

- Ω: implicit universally quantified type in universe u.
- MeasurableSpace Ω: typeclass structure binder.
- μ: universally quantified measure data.
- IsProbabilityMeasure μ: typeclass probability hypothesis.
- Y: universally quantified observation sequence.
- hY: proof hypothesis with internal universal natural t.
- hlaw: proof hypothesis with internal universal natural t.
- hb: proof hypothesis with internal universal natural t and μ-almost-everywhere outcome ω.
- hind: proof hypothesis of mutual independence of Y under μ.
- T in each conclusion lambda: local natural horizon binder. There is no top-level T or hT binder.
- t, ω and i inside each concrete prediction expression: respectively local natural prediction time, outcome, and natural sample-path sequence index.
- The conjunction binds no witness and introduces no existential quantifier.

## Binder ledger for the literal definitions

- empiricalMean: y is real-sequence data, n is a natural horizon; t is the finite-sum index in range n.
- meanPredict: y is real-sequence data, t is a natural prediction time. The equality test t=0 selects the initialization branch; it is not an assumed hypothesis.
- expectedFixedMinimum: Ω is an implicit type, MeasurableSpace Ω is a structure, μ is a measure, Y an observation sequence, T a natural horizon. u is a real lambda binder whose image is restricted to [0,1]. ω is an integral binder and t a finite-sum binder.
- expectedFixedRegret: Ω and its measurable-space structure are implicit/instance binders; μ is a measure, Y and prediction are real-valued process data, T a natural horizon. ω is an integral binder and t a finite-sum binder. There is no independence or probability hypothesis inside either of these definitions.
- Universe levels u,v are type-universe parameters, not mathematical random variables.

## Unresolved questions and limits of this reconstruction

No blocking semantic ambiguity or missing essential upstream definition was found under standard Lean/Mathlib interpretations of IdentDistrib, iIndepFun, IndepFun, variance, atTop, little-o, integral and real sInf.

No theorem body or proof was inspected, so derivability, compilation, hidden proof dependencies and implementation fidelity are unassessed. No source document or intended theorem was available, so source matching, attribution, completeness against a source, and whether any source requires different feedback, independence, quantifier order, or constants are intentionally unresolved. These are comparison tasks for a later stage, not claims made by this decoder.



---
Public location projection of private evidence batch25-blind-decoding-v1/decoding.md. Original SHA256: `3c52fd24758db2fc8349c229b41a6b1f5e0d56ac5713fab7a01be843473be213`. Physical paths alone are logicalized; original stage wording and limits remain unchanged. Later bounded status is recorded in review-binding.json.
