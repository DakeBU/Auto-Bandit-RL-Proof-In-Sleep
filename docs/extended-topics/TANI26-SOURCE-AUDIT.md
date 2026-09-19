# Tani and Futami UAI 2026: local proof audit

Source: Robust and Computationally Efficient Linear Contextual Bandits under
Adversarial Corruption and Heavy-Tailed Noise, PMLR337:6645-6676.
PDF SHA256: d94bd094a16744dd9bd0dfee302a2ff4be58c2540fe3027767f938f53530686e.
Independent source reviewer A read the full supplied model/algorithm and relevant
proof appendices B-D, including rendered checks of pp6667,6670,6672.
External Wang2025/Huang2023 dependencies are only partially audited below; no
complete transitive proof certification, code reproduction or Lean acceptance
is asserted.

The model has conditional mean-zero (1+epsilon)-moment noise, epsilon in (0,1],
known moment scales, known horizon and a supplied corruption budget or valid
upper bound. Infinite variance is permitted when epsilon<1. The procedure is
Huber/projected OMD with a leverage-dependent scale, not BCL scalar hard
truncation. The endpoint is high-probability conditional-mean pseudo-regret.
Unknown-budget corollaries require available valid upper bounds; epsilon remains
an input. Constant update cost is only in horizon, not dimension or arm oracle.

Unresolved written-proof obligations:
- Eq49 drops predictable confidence indicators from an absolute signed sum;
  this need not increase that sum. Preserve the stopped process throughout.
- Eq50->51 does not justify changing vector features to adaptive scalar
  estimation-error projections while retaining the original clipping schedule.
- p6670 substitutes beta_t for beta_(t-1) to assert a leverage floor; the
  initial beta0 can fail to supply that floor. A separate initialization proof
  or explicit algorithm change is required.
- Eq62 omits a factor alpha in w_t^(-2). Correcting this fixed factor can
  preserve the asymptotic rate but changes the displayed constant.
- Huber kink, zero-action, zero-corruption, optimization attainment and finite
  horizon conventions need explicit treatment.

These findings concern the supplied proof; they do not establish a false final
theorem. The source is a distinct future conditional-noise contextual extension,
not a replacement proof of BCL's original scalar algorithm/regret coefficient.
Detailed derivations and the initialization parameter check are recorded in
private review-20260919/tani26-full-audit.md, hashed in the run receipt.

## External-dependency checkpoint: quarter-threshold transfer

Pinned [Huang arXiv v3](https://arxiv.org/pdf/2306.06836v3), dated March 2024,
SHA256 84ea805fae998deeea63273932b207ac5edd0c10616c2f1ba1f260aec4ff527f.
Its identity with the NeurIPS2023 supplement remains unverified.
The appendix C.12/I.1 route, with explicit predictable scales and leverage
budget, yields a finite-horizon threshold-count coefficient
`r^(1+epsilon) + sqrt(2*r^(1+epsilon)) + 2/3` at threshold `tau/r`.
For r=4 and epsilon<=1, the direct bound is at most `67/3`;
the displayed substitution does not establish Tani Eq43's smaller `65/3`.
Independent mathematical review accepted this bounded derivation and explicit
limitation. It is not a counterexample to Eq43 or a repaired final regret proof.
Actual leverage production and downstream constants remain open.

The [official Wang2025 source](https://proceedings.mlr.press/v267/wang25et.html)
is pinned with SHA256
0e0f6f0941884f0b9da758a405e51b9564b04dc46b6d5009cae9810f0f4093e2.
Initial inspection verified Lemma7's deterministic determinant/trace algebra.
Its Eq30–31 also removes stopped indicators and invokes a scalar conversion;
these steps do not supply the missing justification identified above.
Full OMD and concentration dependency acceptance remains pending.

Evidence: `runs/extended-topics-20260919/tani-external-dependency-audit.json`.
This checkpoint adds no Lean declaration or fresh build result.
