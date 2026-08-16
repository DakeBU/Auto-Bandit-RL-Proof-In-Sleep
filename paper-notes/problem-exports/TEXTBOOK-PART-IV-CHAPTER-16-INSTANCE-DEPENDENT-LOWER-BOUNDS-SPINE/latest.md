# Proof Export: Chapter 16 consistency and `d_inf` dependency slice

Task id: `TEXTBOOK-PART-IV-CHAPTER-16-INSTANCE-DEPENDENT-LOWER-BOUNDS-SPINE`

Status: synchronized partial proof export. The declarations below compile;
Theorem 16.2, Lemma 16.3, and Theorem 16.4 do not.

## Compiled Lean declarations

- `BanditRLProof.LowerBounds.IsConsistentRegret`
- `BanditRLProof.LowerBounds.IsConsistentPolicyOver`
- `BanditRLProof.LowerBounds.IsConsistentRegret.add`
- `BanditRLProof.LowerBounds.IsConsistentRegret.eventually_add_le_rpow`
- `BanditRLProof.LowerBounds.IsConsistentRegret.eventually_log_add_div_log_le`
- `BanditRLProof.LowerBounds.divergenceInfimum`
- `BanditRLProof.LowerBounds.divergenceInfimum_le`
- `BanditRLProof.LowerBounds.parametricDivergenceInfimum`
- `BanditRLProof.LowerBounds.parametricDivergenceInfimum_le`
- `BanditRLProof.LowerBounds.unitGaussianDivergenceInfimum`
- `BanditRLProof.LowerBounds.unitGaussianDivergenceInfimum_le_perturbed`

## Natural-language proof map

The scalar consistency predicate says that for every real `p>0`, the
normalized sequence `R_n/n^p` converges to zero. Adding two such limits proves
that the regret sum for the original and alternative environments is also
consistent. Hence its normalization is eventually below one, which gives
`R_n+R_n' <= n^p`. If the sum is eventually positive, monotonicity of the real
logarithm and `log(n^p)=p log n` show that
`log(R_n+R_n')/log n <= p` eventually. This is exactly the analytic inequality
used by the source before taking its limsup.

The distribution-class `d_inf` is defined as an `ENNReal` infimum of
`D(P||P')` over class members with mean strictly greater than `muStar`. Thus
every admissible confusing alternative gives an upper bound on `d_inf`, with
the KL direction visible in the theorem type. A parameterized form applies the
same construction to a family of laws. For unit-variance Gaussians, the
alternative mean `muStar+epsilon`, with `epsilon>0`, is strictly admissible;
the compiled Chapter 15 Gaussian KL identity yields cost
`(muStar-mu+epsilon)^2/2`.

## Exact boundary

The Gaussian candidate theorem is not yet the exact Gaussian `d_inf` equality:
its infimum lower bound and epsilon-to-zero step remain open. More importantly,
the bandit terminals require the same-policy adaptive-history divergence
decomposition of Lemma 15.1. The conditional kernel-KL integral and canonical
possibly randomized policy history law are still absent. No source terminal is
exported as proved.
