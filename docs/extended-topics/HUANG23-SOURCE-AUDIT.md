# Huang v3 C.2/C.4/C.5: original proof audit and constant-preserving repairs

Date: 2026-09-20. Status: independent mathematical and source reviews accepted with explicit contract deltas. No Lean implementation.
Pinned source https://arxiv.org/pdf/2306.06836v3 , SHA256
84ea805fae998deeea63273932b207ac5edd0c10616c2f1ba1f260aec4ff527f.
Inspected full C.5–C.7 proofs, printed pp21–25, and corresponding statements;
rendered pp22 and24 to verify the two issues below. Earlier work inspected
C.11/C.12 and stated I.1. This is not a full audit of the paper's RL theorem.

## Published supplement comparison (2026-09-20)

The earlier download obstruction is resolved. The [official NeurIPS landing
page](https://proceedings.neurips.cc/paper/2023/hash/b11393733b1ea5890100302ab8a0f74c-Abstract.html)
links the Supplemental ZIP. An HTTP request redirects to HTTPS and returns
HTTP200; a second download reproduces the same archive bytes. The ZIP passes
CRC checks. Only `full.pdf` was extracted; bundled code was not executed.

- ZIP SHA256: `4fa7ed0857cc07339ea8884a5bdc64d8039bc68513f043648bc45cb72dee087c`.
- Published `full.pdf` SHA256: `af3f298ba5489c2931c00f41b42b76bb16b389d2217787d5c25d3060180784ef`.
- Both PDFs contain 54 pages. With the same `pdftotext -layout`, page text is
  exactly equal except pages1,11,13; all appendix pages14–54 agree.
- Text differences concern the arXiv stamp/layout and Los Angeles spelling on
  page1, funding acknowledgments on page11, and reference39 publication metadata
  on page13. These do not change the audited score statement or its assumptions.
- Direct 100dpi raster comparison of pages17,21–25 gives identical PPM bytes.
  Visual inspection of published pages22 and24 confirms that the prefix
  calibration implication and random-factor extraction below are present.
- Independent all-page raster comparison additionally checks appendix pages14–54;
  its evidence and verdict are bound in the version receipt. Text equality alone
  does not imply pixel equality: the reviewer found an additional visual change
  on page2, outside this appendix audit.

The version comparison is recorded in
`runs/extended-topics-20260919/huang-official-version-audit.json`;
`compare_huang_versions.py` reproduces pinned-byte and exact page-text checks.
The earlier v3 receipt remains an immutable historical audit. This comparison
extends the existing C.2/C.4/C.5 finite-horizon repair's source applicability to
the matching published appendix; it does not certify the whole paper, all-time
wording, regression/RL chain, or a Lean implementation. The two PDF files are
not byte-identical, and no claim of whole-document identity is made.

## Explicit finite-horizon reconstruction

Let T,d>=1, lambda,R,b,tau0>0, p in (1,2],
a=(2-p)/(2p), delta in (0,1), and before/after filtration G_(s-1),G_s.
Let predictable normalized features x_s in R^d satisfy ||x_s||<=R, and let
adapted noise z_s satisfy E[z_s|G_(s-1)]=0 and
E[|z_s|^p|G_(s-1)]<=b^p. Define
 H0=lambda I, H_s=H_(s-1)+x_s x_s^T,
 w_s^2=x_s^T H_(s-1)^(-1)x_s, v_s=w_s^2/(1+w_s^2),
 kappa=d*log(1+T*R^2/(lambda*d)),
 tau_s=tau0*sqrt(1+w_s^2)/w_s*s^a,
 d_s=sum_(r<=s) h_tau_r(z_r) x_r, d0=0,
 ell_n=log(2n^2/delta), D_n=(sqrt(2kappa)*b)^p*(log(3n))^((2-p)/2),
 c_n=D_n/tau0^p,
 alpha_n=4*tau0*n^a*(c_n+ell_n).
Here h_tau is clipping to [-tau,tau]. Initially assume x_s!=0 so tau_s is
finite positive. A zero-feature extension is described at the end.
The actual Gram gives sum_(s<=n)v_s<=kappa<=2kappa for n<=T, by rank-one
determinants and trace/AM-GM. Thus this budget is produced, not a probability
conclusion assumed as input. In the source x_s=phi_s/sigma_s, with the usual
predictable scales bounded below, R=L/sigma_min.

The target is, with probability >=1-2delta simultaneously for n<=T,
 ||d_n||_(H_n^(-1))<=alpha_n.
Adding the regularization gradient at ||theta_star||<=B gives the source
C.2 bound sqrt(lambda)*B+alpha_n. The displayed finite-prefix alpha equals
the source's expression after p=1+epsilon. No tau0 lower bound is needed for
this unsimplified alpha; the horizon tuning is used only for its later
compact simplification. All logarithmic/norm conventions are explicit.

## C.4: random predictable MGF factors need compensation

For a fixed terminal n, let A_j mean all score bounds hold for prefixes1..j,
and A0=true. Define for s<=n
 M_s=(s/n)^a /sqrt(1+w_s^2)
     * d_(s-1)^T H_(s-1)^(-1)x_s *1_(A_(s-1))
       /(alpha_n*w_s).
The deterministic alpha_n is nondecreasing in n. Cauchy–Schwarz on A_(s-1)
gives |M_s|<=1; M_s is predictable. This equals the source's normalization,
since max_(r<=n)alpha_r=alpha_n. The stopped cross sum is exactly
 2*tau0*n^a*alpha_n * sum_(s<=n) M_s*h_1(z_s/tau_s).

For any real u and p in (1,2],
 exp(h_1(u))<=1+u+|u|^p and exp(-h_1(u))<=1-u+|u|^p.
One direct proof: for |u|<=1, Taylor bounds give exp(u)<=1+u+u^2 for
u>=0, and exp(u)<=1+u+u^2/2 for u<=0; |u|^p>=u^2. For u>=1 use
exp(1)<3<=1+u+u^p and exp(-1)<1<=1-u+u^p; exchange signs for u<=-1.
Convex interpolation between exponent0 and exponent with sign(M_s) then
gives exp(M_s*h_1(u))<=1+M_s*u+|M_s|*|u|^p.
Conditional centering and moments imply
 E[exp(M_s*h_1(z_s/tau_s))|G_(s-1)]<=1+r_s<=exp(r_s),
where r_s=b^p/tau_s^p is nonnegative predictable and generally RANDOM.

The source p24 takes (1+r_n) outside an unconditional expectation, then
iterates to a product of such factors. Predictability alone does not justify
that displayed extraction. This is a written-proof gap, not a refutation
of C.4's conclusion.

Repair: set Z_j=exp(sum_(s<=j)[M_s*h_1(z_s/tau_s)-r_s]) for j<=n.
Conditioning gives E[Z_j|G_(j-1)]<=Z_(j-1), Z0=1. These nonnegative variables
are integrable: their exponent is at most j because |M_s*h_1|<=1 and r_s>=0.
Hence E[Z_n]<=1. Holder, the produced leverage budget and harmonic sum give
 sum_(s<=n)r_s
 =(b/tau0)^p sum v_s^(p/2)*s^(-(2-p)/2)
 <=(b/tau0)^p*(2kappa)^(p/2)*(log(3n))^((2-p)/2)=c_n.
At p=2 the same inequality is direct. Consequently
 E exp(sum M_s*h_1(z_s/tau_s))<=exp(c_n).
Markov at level exp(c_n+ell_n) bounds the upper-tail probability by
delta/(2n^2). A finite union over n<=T costs <=delta, since
sum_(n>=1)1/(2n^2)<=1 (also follows by the elementary integral bound).
Thus, on one event of probability >=1-delta, every stopped cross sum obeys
 cross_n<=2*tau0*n^a*alpha_n*(c_n+ell_n)=alpha_n^2/2.
The terminal-dependent predictable M_s are constructed separately for each
n, which is valid before this finite union. No independence is asserted.

## C.5: square-term proof and the reciprocal-probability typo

The source weighted square term Q_n=sum h_tau_s(z_s)^2*v_s satisfies
 Q_n<=tau0^2*n^(2a)*sum X_s, X_s=h_1(z_s/tau_s)^2 in [0,1].
Conditional p-moments, the same Holder calculation and actual budget give
sum E[X_s|G_(s-1)]<=c_n. Center Y_s=X_s-E[X_s|G_(s-1)]: |Y_s|<=1<=2,
and sum E[Y_s^2|G_(s-1)]<=sum E[X_s^2|G_(s-1)]<=c_n.
Because b,kappa,tau0>0, c_n>0 is an admissible deterministic variance bound
for I.1. Use the source's conservative increment bound2, fixed-prefix failure
delta/(2n^2), and union over n<=T. With probability >=1-delta, simultaneously,
 Q_n<=tau0^2*n^(2a)*[c_n+sqrt(2c_n*ell_n)+(4/3)ell_n]
     <=tau0^2*n^(2a)*(sqrt(c_n)+sqrt(2ell_n))^2.
The final comparison simply enlarges the cross and linear terms. This is
exactly the C.5 displayed endpoint. The prose above C.17 writes
'1-2t^2/delta'; it must be '1-delta/(2t^2)' for the invocation and union used.
This typo does not require changing the final failure budget once corrected.

## C.2: the prefix calibration implication is false, but unnecessary

Source p22 infers a prefix square-root bound from a tau0 lower bound tuned
to T. At p=2 and the allowed equality tau0=sqrt(2kappa)*b/sqrt(ell_T), for
any n<T, that asserted inequality reduces to
 sqrt(2kappa)*b <= sqrt(2kappa)*b*sqrt(ell_n/ell_T), which is false.
This refutes the displayed deterministic implication, not C.2 itself.

A direct replacement suffices. Put u=c_n+ell_n. Cauchy–Schwarz gives
(sqrt(c_n)+sqrt(2ell_n))^2<=3u. Since ell_n>log2>=1/2, u>=1/2 and
3u<=8u^2. Therefore the C.5 bound is <=alpha_n^2/2 without the false
prefix calibration step and without changing alpha_n.

The exact rank-one inverse recurrence gives
 ||d_n||_(H_n^(-1))^2 <= sum_(s<=n)
   2*h_tau_s(z_s)*d_(s-1)^T H_(s-1)^(-1)x_s/(1+w_s^2) + Q_n,
after discarding a nonpositive square. On the intersection of the C.4/C.5
events (probability >=1-2delta), suppose a first violating prefix n exists.
All A_(s-1) for s<=n are true, so the actual cross sum at that prefix equals
the stopped sum. Both contributions are <=alpha_n^2/2, contradicting
||d_n||>alpha_n. Thus all prefixes satisfy the target. This is the missing
explicit first-violation justification, not unrestricted removal of indicators.

## Compact source tuning, endpoints and scope

If tau0=(sqrt(2kappa)*b)*(log(3T))^a/ell_T^(1/p), then c_T=ell_T.
For n<=T, c_n<=c_T and ell_n<=ell_T. Hence
 alpha_n<=8*tau0*n^a*ell_T
 =8*n^a*sqrt(2kappa)*b*(log(3T))^a*ell_T^((p-1)/p).
This recovers the compact noise-vector bound used by the later papers on the
explicit finite horizon. It does not turn the vector bound into an arbitrary
time-varying scalar projection bound; that required the separate direct
scalar proof in the Tani recovery.

If b=0, use a separately chosen tau0>0: conditional p-moment zero forces
all z_s=0 almost surely, so d_n=0 for all finite prefixes. Do not substitute
tau0=0 or variance0 into I.1. For x_s=0, one may set a positive finite tau_s,
define M_s=r_s=X_s=0 in these auxiliary arguments, and note its actual score
and Gram contribution is zero. This extends the algorithm's undefined quotient
explicitly; it is not a literal source convention. Conditional moment and
predictability assumptions must hold for the chosen filtration.

The original main paper's broader regression curvature, perturbation, linear
bandit and RL results are not all certified by this score audit. The bounds
here preserve C.4/C.5/C.2 constants on an explicit finite horizon while
repairing their displayed argument; no unrestricted all-time assertion,
whole-document identity, new Lean theorem, or topic completion follows. The
published appendix correspondence is separately established above.


## Source scope delta

Lemma C.2 on printed p17 writes forall t>=1 even though its calibration and
leverage budget use a fixed horizon T. This reconstruction only claims
1<=n<=T. The unrestricted printed wording is not certified.

## Integration boundary

This is a source-audit and mathematical-repair checkpoint for the heavy-tail
route. No production Lean declaration, registry node, teaching route, result
badge, contributor credit or graph edge changes. The Lean Graph and Overview
Graph remain unchanged because this repair has no compiled declaration.
Functor Hypergraph: none-found-with-reason for this checkpoint; a compensated
exponential is a proof mechanism, not a certified cross-setting bridge here.
The all-ten ledger remains active with zero completed topics. The existing
BCL source-policy endpoint remains the primary frozen formalization target.
No new Lean or site gate, main merge, deployment or controlled evaluation is
claimed by this document. The published appendix correspondence is covered by
the new version receipt; the broader regression/RL results remain outside
accepted scope.

Evidence receipt: `runs/extended-topics-20260919/huang-v3-dependency-audit.json`.
The receipt binds the unchanged private derivation and both independent reviews.
