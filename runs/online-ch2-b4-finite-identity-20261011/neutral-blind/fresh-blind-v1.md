# Neutral HEADER blind decode

Actor: `/root/b4_finite_identity_blind`.

The sole file read was `E:/ABRL/worktrees/research-online-book/tmp/online-ch2-b4-finite-identity-proposal-20261011/neutral-proposed-header-v1.txt`. One raw-byte read supplied both the SHA256 computation and UTF8 display. Its raw SHA256 is `92e0dcfac53595e35b68bfd8083c09640d06da809355ab02ec4eb4b007b0bd67`, matching the assignment. No other files were read, including memory files, source PDFs, proofs, proposals, and historical reviews.

The assignment requested GPT-6 Astra / medium. Actual runtime model and effort cannot be independently attested here. Generic inherited system/developer context, skill catalog, workspace instructions, environment metadata, and memory-summary context were already exposed. The assignment also exposed the expected hash, filenames, role, and decoding checklist. This review does not claim completely zero background.

## Decoded statement

`BanditRL.OnlineCumulativePotential.finite_regret_identity` quantifies over an arbitrary universe-polymorphic type `E`, arbitrary functions `psi loss : Nat -> E -> Real`, arbitrary sequence `x : Nat -> E`, arbitrary points `u z : E`, and `T : Nat` with `0 < T`. `E` is implicit; the other theorem binders are explicit. No structure or decidable equality on `E` is needed. Supplied points make an actual instance inhabited without requiring an `Inhabited E` instance.

The local lets define, rather than independently quantify over:

- `y(t) = z` exactly when `t = T`, and `y(t) = x(t)` otherwise. Indices after T are unchanged.
- `G(t,v) = psi(t,v) + sum_{i=0}^{t} loss(i,v)`. The sum includes loss at time t, because `range (t+1)` is `0,...,t`.

For positive T, the identity can be written as follows. Every sum with an empty index interval is zero.

```text
sum_{t=0}^{T-1} [loss(t,x(t)) - loss(t,u)]
  = psi(T-1,u) - psi(0,x(0))
    + sum_{t=0}^{T-2} [G(t,x(t)) - G(t,x(t+1))]
    + G(T-1,x(T-1)) - G(T-1,z)
    + sum_{t=0}^{T-2} [psi(t,x(t+1)) - psi(t+1,x(t+1))]
    + G(T-1,z) - G(T-1,u).
```

The original first right-side sum has exactly T terms. It compares adjacent trajectory points under the same `G t`; the displayed expansion isolates its final term. The original second right-side sum has exactly T-1 terms, ending at `t=T-2`. It compares adjacent potential times at the same point `x(t+1)`. Its final point is `x(T-1)`, never z. The endpoint correction uses `G(T-1,.)`, so no term involving `loss(T,.)` appears anywhere.

The endpoint z is completely arbitrary. Its negative occurrence in the final first-sum term cancels its explicit positive occurrence. Both sides are therefore independent of z. In particular, the header does not require `z=x(T)` or an optimizer. The original value `x(T)` and later x coordinates are unused after unfolding under positivity. The statement is an exact equality of real numbers, with no constants, learning rates, inequalities, or asymptotic notation.

## Positivity and degenerate cases

Natural subtraction is truncated, so `0-1=0`. Positivity ensures that `T-1` is the intended final time and `y(0)=x(0)`.

At T=1, the temporal-potential sum is empty. The right side becomes

```text
psi(0,u)-psi(0,x(0))
  + G(0,x(0))-G(0,z) + G(0,z)-G(0,u)
  = loss(0,x(0))-loss(0,u).
```

If the positivity hypothesis were removed, T=0 would make both finite sums and the left side zero, while `y(0)=z`. The right side would become `loss(0,z)-loss(0,u)`. Thus the unrestricted zero-horizon statement is false: take E=Real, z=1, u=0, psi identically zero, and `loss(t,v)=v` to obtain `0=1`.

The choices `z=x(T)`, `z=u`, and `z=x(T-1)` are all permitted. The second makes the explicit endpoint correction zero; the third makes the final first-sum term zero. Constant sequences, singleton E, zero psi, zero loss, negative values, and coincident points are allowed. Empty E supplies no actual instance of u/z/x; no extra inhabitance condition has been omitted.

## Missing assumptions and interpretation risks

There is no minimization rule, recurrence, optimality assumption, zero initial potential, convexity, smoothness, continuity, measurability, integrability, boundedness, monotonicity, positivity of losses, or probability model. In particular the header supplies no guarantee that the term with arbitrary z is small or has a particular sign.

No unresolved index/type ambiguity was found under standard Lean semantics. The main potential misreadings are exclusive versus inclusive loss history in G, erroneously adding a temporal-psi term at `t=T-1`, using endpoint time T, treating the splice as replacing all future positions, or admitting horizon zero without a new condition. This is a semantic decode, not kernel verification or a judgment of source-faithfulness.

No proof BODY was constructed or compiled. No source search or Git inspection occurred. The assignment designated the output directory ignored; that status was not independently checked because the read scope allowed only the input header. Outputs are create-only, UTF8 without BOM, with LF newlines, in the designated temporary directory.
