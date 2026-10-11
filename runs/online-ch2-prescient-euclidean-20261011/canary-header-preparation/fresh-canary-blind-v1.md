# Fresh blind reconstruction v1

## Scope and exposure

This is a statement reconstruction from exactly four neutral text files. Source faithfulness and proof validity are outside scope. No paper, prospectus, source bodies, reviews, memory, repository files, or additional directories were opened. No imports were resolved, compilation run, or proofs attempted. The task message and inherited conversation instructions were visible; these included workspace governance and a memory summary, but no memory file was accessed or used. Thus this is not a claim of an empty-context process. Requested model label: GPT-6 Astra / medium; engine attestation is unavailable and not claimed.

Inputs read and SHA-256 verified (all match supplied hashes):

- neutral-complete-canary-headers-v1.txt: 06b896bedf5883f7aea542035a8c8f99de48c79bc9d9972ca57a82226fc0e6df
- neutral-imported-definitions-v1.txt: dff55f4b3262afa2869e8dce05cf27bde92b8ef94945f31c7a198a0c8f39c9a1
- neutral-standard-definitions-v1.txt: a5bf043f78dca8dc95e501b13ee41c9bfef17638ba2ecd2145edb833c5a0e06e
- neutral-additional-definitions-v1.txt: f014b39f9c575879b0e4e892b5c2580bd25fc343d6adb6e807c6c591c34a27c8

The only filesystem content read was these four files. Report writes are create-only in their directory. Input hashes are identity checks, not evidence of compilation or mathematical truth.

## Shared complete context and definitions

The headers import BanditRLProof.OnlinePrescientEuclidean, Tests.OnlineSubgradientBasicCanary, and Mathlib.Tactic; open Set, Finset, BanditRL.OnlineConvex, BanditRL.OnlineBregman, and BanditRL.OnlinePrescientBregman; use a noncomputable section and autoImplicit=false; and declare both theorems in PrescientEuclideanProbe. Import contents were not read beyond the supplied extracts.

Neither theorem has external parameters or hypotheses. Each is a closed proposition with four local let-bindings, followed by a conjunction. Properness, convexity, minimization, and run equality are conclusions asserted by the statements, not assumed premises.

For both statements, V=[0,2] is a subset of the real line. For every natural time t, loss_t(z)=z^2/2 as a finite real embedded in EReal when z belongs to V; otherwise loss_t(z)=top. All times share this loss. The interval is bounded but is not a finite set. Its loss values are finite on V and top off V; none is bottom under this explicit definition. Effective domain means {z | loss_t(z)<top}; this definition by itself does not exclude bottom, whereas SourceProper does.

SourceProper(f) means (for every real z, f(z) is not bottom) AND there exist a real z and real r with f(z)=the EReal embedding of r. IsConvexExtended(f) means that its real epigraph {(z,r) | f(z)<=embed(r)} is convex over the reals. No separate closedness or lower-semicontinuity predicate for the loss is asserted.

The subdifferential supplied here is global: g belongs to SourceSubdifferential(f,z) exactly when, for every real y, f(z)+embed(g*(y-z))<=f(y). Consequently the asserted membership z in SourceSubdifferential(loss_t,z) uses g=z; it does not assert that this subdifferential is a singleton.

IsMinOn(F,V,p) means F(p)<=F(z) for every z in V. It does not alone assert p in V; the headers and advance explicitly supply membership separately.

The run uses psi(z)=|z|^2/2. The supplied divergence is D_psi(a,b)=psi(a)-psi(b)-[fderiv_R psi b](a-b). For this differentiable quadratic this is the usual squared-distance half; this identifies the expression's semantics and is not a checked Lean derivation. advance(V,psi,eta,f,a) returns some chosen p when there exists p in V minimizing f(z)+embed(eta^{-1}*D_psi(z,a)) over V, and returns none if no such p exists. Selection is Classical.choose, with no tie-breaking rule in the supplied definition. iterate starts at some x0 at time zero; at time t+1 it binds the previous option through advance with eta_t and loss_t. A none propagates. The numeral 2 in iterate V psi eta loss 2 t is the initial point x0=2, NOT a horizon argument. The asserted range t<=2 is the separate run restriction.

## Statement 1: variable_quadratic_actual_run

Local bindings in addition to the common V and loss:

- eta_t=1 for t=0 and eta_t=1/2 for every t>=1.
- x_t=2 for t=0, x_t=1 for t=1, and x_t=2/3 for every t>=2.

The complete conjunction asserts all of the following:

1. V is convex over the reals, nonempty, and closed.
2. For every natural t, loss_t is SourceProper and IsConvexExtended, and effectiveDomain(loss_t)=V.
3. For every natural t and every real z in V, z belongs to SourceSubdifferential(loss_t,z), with the global inequality explained above.
4. loss_0(3)=top.
5. toReal(loss_0(0))+toReal(loss_0(2)) is unequal to 2*toReal(loss_0(1)). This is a specific midpoint non-affinity witness, not a quantified strict-convexity assertion.
6. For every natural t, eta_t>0; for every natural t, eta_(t+1)<=eta_t.
7. eta_0=1 and eta_1=1/2.
8. x_0=2, x_1=1, x_2=2/3.
9. For every natural t<2 (exactly t=0,1), x_(t+1) belongs to V AND minimizes loss_t(z)+embed(|z-x_t|^2/(2*eta_t)) over z in V. Equivalently the value at x_(t+1) is <= the value at every z in V.
10. For every natural t<=2 (exactly t=0,1,2), iterate(V,psi,eta,loss,2,t)=some(x_t), using the actual option-valued, choice-defined run.
11. The real sum over t=0,1 of [toReal(loss_t(x_(t+1)))-toReal(loss_t(0))] equals 13/18.
12. The real sum over t=0,1 of [toReal(loss_t(x_t))-toReal(loss_t(0))] equals 5/2.
13. |x_1-x_0|^2/(2*eta_0)=1/2.
14. |x_2-x_1|^2/(2*eta_1)=1/9.
15. The sum over t=0,1 of |x_(t+1)-x_t|^2/(2*eta_t) equals 11/18.
16. For every real u in V, the sum over t=0,1 of [toReal(loss_t(x_(t+1)))-toReal(loss_t(u))] is at most
    max{|u-x_0|^2/2, |u-x_1|^2/2}/eta_1 minus the sum over t=0,1 of |x_(t+1)-x_t|^2/(2*eta_t).
    The maximum is exactly Finset.sup' over range 2, with the supplied nonempty witness; it ranges over x_0 and x_1, excluding x_2. In concrete coordinates the right side is max{(u-2)^2/2,(u-1)^2/2}/(1/2)-11/18.
17. As an additional explicit real-number proposition, 13/18<=61/18. The header states this as a separate conjunct; it does not syntactically label it a specialization, though its numbers match the displayed comparator bound at u=0.

## Statement 2: fixed_quadratic_actual_run

Local bindings in addition to the common V and loss:

- eta_t=1 for every natural t.
- x_t=2 for t=0, x_t=1 for t=1, and x_t=1/2 for every t>=2.

The complete conjunction asserts all of the following:

1. V is convex over the reals, nonempty, and closed.
2. For every natural t, loss_t is SourceProper and IsConvexExtended, and effectiveDomain(loss_t)=V.
3. For every natural t and every real z in V, z belongs to SourceSubdifferential(loss_t,z), with the global inequality explained above.
4. loss_0(3)=top.
5. toReal(loss_0(0))+toReal(loss_0(2)) is unequal to 2*toReal(loss_0(1)).
6. For every natural t, eta_t>0; for every natural t, eta_(t+1)<=eta_t.
7. eta_0=1 and eta_1=1.
8. x_0=2, x_1=1, x_2=1/2.
9. For every natural t<2, x_(t+1) belongs to V AND minimizes loss_t(z)+embed(|z-x_t|^2/(2*eta_t)) over z in V.
10. For every natural t<=2, iterate(V,psi,eta,loss,2,t)=some(x_t).
11. The real sum over t=0,1 of [toReal(loss_t(x_(t+1)))-toReal(loss_t(0))] equals 5/8.
12. The real sum over t=0,1 of [toReal(loss_t(x_t))-toReal(loss_t(0))] equals 5/2.
13. |x_1-x_0|^2/(2*eta_0)=1/2.
14. |x_2-x_1|^2/(2*eta_1)=1/8.
15. The sum over t=0,1 of |x_(t+1)-x_t|^2/(2*eta_t) equals 5/8.
16. For every real u in V, the sum over t=0,1 of [toReal(loss_t(x_(t+1)))-toReal(loss_t(u))] is at most
    |u-2|^2/(2*1) minus [the sum over t=0,1 of |x_(t+1)-x_t|^2]/(2*1).
    This is the initial-point expression, with the common denominator outside the second sum exactly as in the header. In concrete coordinates the right side is (u-2)^2/2-5/8.
17. As an additional explicit real-number proposition, 5/8<=11/8. It is a separate conjunct; its numbers match the displayed comparator bound at u=0.

## Indexing, scoring, and limits

Both sums and minimization assertions concern two rounds, indexed 0 and 1. The main bounded score uses the updated point x_(t+1) on loss_t; the separate 5/2 diagnostic uses the old point x_t. The comparator is the same real u for both rounds and is universally quantified over V, while the displayed numerical scores use comparator zero. All scoring and movement arithmetic is real-valued after the explicit toReal calls. Because the scored points and comparator lie in V, their losses are finite; the top-valued witness at z=3 is not scored. No claim about toReal(top) as an infinite real is needed or made.

The sequences eta and x are defined for every natural t, and loss properties and rate monotonicity are asserted for all natural t. Nevertheless update optimality stops at t<2 and run equality stops at t<=2. The constant tail used to define x does not assert that the actual run stays constant or agrees with that tail after time 2. No statement concerns arbitrary horizon, arbitrary losses, arbitrary starting points, randomness, expectation, or probabilistic qualification.

The run assertion is stronger than merely naming two minimizers: it identifies the choice-defined iteration at all three stated times. The headers do not supply uniqueness as a premise or conclusion. Whether equality to the selected minimizer follows, and whether all other conjuncts are provable, cannot be certified by this blind reconstruction.

## Ambiguities and blockers

No missing premise or unresolved mathematical symbol blocks a semantic reconstruction from the supplied extracts and ordinary Lean notation. Definitions for standard infrastructure such as EReal.toReal, fderiv, Finset.sup', and Option.bind were not opened; standard mathematical readings are used, without import or elaboration verification. The gradient definitions in the standard extract are not used by either displayed header. No additional conditions may be imported from the theorem names or filenames.

The source text, proof bodies, Lean elaboration/build results, and source-review evidence are absent by design. Accordingly this report gives no source-faithfulness verdict, proof-validity verdict, compilation claim, or intended-source claim. The two complete claims are concrete closed conjunctions, not general algorithmic theorems.