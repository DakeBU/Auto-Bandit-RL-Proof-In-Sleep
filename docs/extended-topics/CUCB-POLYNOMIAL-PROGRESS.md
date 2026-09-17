# CUCB polynomial-bound construction progress

2026-09-18. Repaired Theorem1 remains compiled. Neither mandatory Theorem2 branch is yet claimed complete. These declarations construct the actual cutoff bound and scalar ingredients needed for its exact distribution-independent endpoint.

`FiniteGapCutoff.sum_le_cutoff_integral` proves a finite layer-cake cutoff envelope with baseline a*card and excess integral. It does not add the min-gap threshold term again. It handles gaps below the cutoff by filtering the actual finite list, proves tail-filter equality on the integration interval, and retains the exact b-a boundary term.

`CUCBGapCutoff` proves each actual under-charge count is bounded by its actual counter, and their total across arms is at most H. Applying the cutoff envelope to actual charge times and integrating yields

    R(H) <= H*a + sum_i integral_a^Delta_max ell_H(x,p_i) dx
      + (1+(2+I{p_*<1})pi^2/6)m*Delta_max,

for a in the positive source gap domain. The baseline is paid once per actual round. A separate large-cutoff theorem covers Delta_max<=a, including the zero-gap situation, without an invalid reversed/empty-domain integral.

`CUCBPolynomialThreshold` derives inverseAt(d)=(d/gamma)^(1/omega) from the actual modulus assumption, its square/reciprocal identities, and both exact threshold formulas. For the probabilistic source branch it also proves the uniform actual-arm envelope

    ell_H(d,p_i) <= (12 log H/p_*)*gamma^(2/omega)*d^(-2/omega)
                   +24 log H/p_i.

This covers mixed deterministic and probabilistic arms; no assumption that every p_i<1 is added. The deterministic branch has its separate exact coefficient6 formula. The inverse lemmas need only omega>0; the final source theorem additionally requires omega<=1.

`PowerTailIntegral` proves the exact finite power-tail integral bound for q>1 and positive endpoints, the balancing identity K*((K/N)^(1/q))^(-q)=N, and the resulting objective coefficient q/(q-1). These scalar identities do not themselves constitute Theorem2. The source instantiation must use q=2/omega, derive all positivity conditions, choose the cutoff, handle H=1 and cutoff>=Delta_max, integrate/sum the actual threshold envelopes and rewrite into the exact frozen gamma/log/H exponents and coefficients. Both full terminals remain open, as do concrete noisy canaries, independent source/repair acceptance, shared mappings and all-topic ICLR evidence. No experiment, merge or deployment is implied.
