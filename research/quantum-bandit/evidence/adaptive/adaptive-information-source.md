# Private original contract: adaptive reset transcript information

Status before implementation: source/statement frozen, not proved. Original
elementary derivation, not attributed to an external paper and no novelty claim.
Inputs remain the frozen local Lean 4.29.1 / Mathlib versions in intake.md.
Owner: BanditRLlib private research adapter; no public registry or upload.

Reuse search: BanditRLProof/LowerBounds/CommonDensityOverlap.lean has measure
affinity/testing but no finite kernel Hellinger chain identity. Mathlib's finite
sums/Real.sqrt and PMF supply the classical algebra. QuantumComputinglib's
BasisHellinger and ResetBlockProcess supply actual normalized output masses and
bounded same-arm words. Searches of the pinned external source snapshots found
no directly compatible adaptive reset theorem; no external import or copy is used.

Source objects: finite outcomes iota, finite arms K (possibly zero if a policy
exists), integer D >= 0, one supplied normalized fresh pure input psi; two actual
unitary oracle families E,F. A single deterministic policy is shared by both
environments and depends only on the prior classical outcome list. Its Plan
contains an arm, chronological word of known unitaries / forward / inverse calls,
and proved syntactic query cap q <= D. No quantum state crosses a block boundary.
For n blocks a finite transcript is a nested pair: Trace(0)=Unit;
Trace(n+1)=Trace(n) x iota, ordered prior history then new outcome. The list view
recursively appends the last outcome. No alternative measurement is introduced.

Let k_E(h,j) be the existing actual computational-basis probability of evaluating
policy(h).word at E(policy(h).arm) on psi. Normalization and nonnegativity MUST be
derived from existing word unitarity, not supplied as new root premises.
The literal transcript density is p_E(0,())=1 and
p_E(n+1,(h,j))=p_E(n,h) k_E(list(h),j). This is the finite density representation
of the reset process, with an explicit PMF/list-law bridge required before claiming
an assertion about the previously defined historyLaw.

H^2(p,q)=sum_x(sqrt(p_x)-sqrt(q_x))^2, without a factor 1/2.
For arbitrary nonnegative parent densities and normalized nonnegative kernels:
H^2(p k, q l) = H^2(p,q) + sum_h sqrt(p_h q_h) H^2(k_h,l_h).
This auxiliary identity need not assume normalized parent densities.

If ||E_i-F_i||op <= eta_i, existing per-word mathematics produces
H^2(k_E(h),k_F(h)) <= D q(h) eta_arm(h)^2.
Define literal weighted trace cost C(n+1,(h,j))=C(n,h)+q(h) eta_arm(h)^2,
and C(0,())=0. It charges both forward/inverse calls, only for the arm used.
Let EC_E(n)=sum_h p_E(n,h) C(n,h), and similarly EC_F.
The intended root is H^2(p_E(n),p_F(n)) <= D/2 (EC_E(n)+EC_F(n)).
No conditional information bound, normalization, unbiasedness, independence of
estimation errors, or adaptive information chain is assumed in this root.

Proof route from the source (to be independently reconstructed): expand the joint
finite sum and square roots, use kernel normalization to obtain the exact chain
identity; use 2 sqrt(p q) <= p+q; prove the actual trace-density/expected-cost
recurrences; induct on n with the produced per-word bound. For uniform eta,
a pathwise real query horizon T bounds C by T eta^2 and yields H^2 <= D T eta^2.
Arm-local weighted costs are retained so one differing arm can support a future
K-arm testing reduction. Such a reduction is NOT proved by this contract.

Boundary: fixed finite number of computational-basis reset blocks; known unitaries
and psi are mathematical model inputs, not free synthesis/loading claims. Empty
words are allowed. Randomized policies, arbitrary POVMs, random stopping,
finite-bit runtime, algorithmic estimation, regret/PAC guarantees and minimax
lower bounds remain separate leaves. A later stopping adapter may encode halted
steps with zero-query words, but is not asserted here. No public graph changes.
