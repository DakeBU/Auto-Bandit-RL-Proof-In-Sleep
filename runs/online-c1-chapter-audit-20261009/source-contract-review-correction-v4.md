# Bounded v4 correction of reviewer v3 narrative

**Correction accepted.** The v3 report contains a false numerical example and a false generalization about the legal initialized FTL process. Both are explicitly withdrawn here; the immutable v3 files are not edited. The four frozen G001–G004 target types, the contract stabilization verdict and its exact future scope remain unchanged. This correction does not accept any newly written proof or add a theorem/permission.

Actor `/root/source_reviewer` is the same reused distinct automated reviewer with disclosed staged history. GPT-6 Astra / medium remains the requested setting, without runtime, human/external or absolute-blind attestation.

## Exact arithmetic correction

Take initial=0, y0=0, y1=1, T=2. The actual `ftlPredict` definition gives p0=0 and p1=empiricalMean(y,1)=0. Thus played loss is0+1=1. The attained feasible fixed mean is1/2, with loss1/4+1/4=1/2. True-best regret is **+1/2**, not -1/2. Independent exact rational arithmetic confirms these values. The half-initialized run has played loss5/4 and regret3/4. G001's signed first-loss correction is-1/4, so3/4-1/4=1/2, consistent with the unchanged target.

This was the reviewer's own error, not a source, Lean, target, body or decoder error. Specifically superseded are the negative-example sentence in the v3 report's mathematical discussion and the G004 statement “General-initial finite regret need not be nonnegative”, also present at receipt JSON pointer `/target_verdicts/3/independent_source_judgment`. Replace the latter with: “G004 follows by a fixed finite first-loss correction divided by T; this proof route does not require invoking a separate nonnegativity theorem. For the actual FTL predictor on unit-valued scored prefixes, true-best regret is nonnegative by the prefix-minimum induction.”

## Why the contrary nonnegativity exclusion is wrong

The actual `meanPredict_bestLoss_nonneg` proof uses prefix minimization, not a special first-half inequality. Let C_n(u)=sum_{t<n}(u-y_t)^2 and A_n be cumulative played loss of the actual initialized FTL. At n=0, A0=C0=0 for any initial value. Inductively A_n>=C_n(empiricalMean_n). For n>0, p_n=empiricalMean_n; for n=0 both prefix sums are empty irrespective of p0. Hence

A_(n+1) >= C_n(p_n)+(p_n-y_n)^2 = C_(n+1)(p_n) >= C_(n+1)(empiricalMean_(n+1)).

The last inequality is the existing global real `empiricalMean_minimizes`. For a unit-valued scored prefix, the actual `squaredLoss_minimum_eq` identifies this mean loss with the feasible interval minimum, including T0. Therefore true-best regret of the actual initialized FTL is nonnegative in the G002–G004 source setting. This is a source/definition-level mathematical explanation, not a new compiled general-initial Lean theorem or a newly required public target. The initial value need not be half for this reasoning.

Keep the hypotheses of the interval identification visible. G001 alone allows arbitrary real observations and should not inherit unit-prefix minimum identification without justification. This review does not assert interval-best nonnegativity on arbitrary outside-interval streams. Likewise signed regret for arbitrary supplied prediction traces is a different object. Neither is a counterexample to nonnegativity of the actual legal FTL process here.

The first-loss **correction** can genuinely be negative, as-1/4 in this example. Accordingly the v3 G001 seven-slot statement that the correction need not be nonnegative remains correct; it must not be confused with the total true-best regret. G003 still asserts only upper NoRegret; G004 still asserts ordinary zero only for normalized true-best regret, not every fixed comparator. The original dyadic fixed-comparator obstruction remains untouched.

## Scope and evidence

Twelve precise files were independently RAW-hashed before and after: immutable v3 report/receipt, exact targets/context, current FTL/mean/best-regret definitions and the actual half nonnegativity proof, plus unchanged scope/reader requirements. All ten scientific/scope files match their prior v3 RAW bindings; both old review hashes match the requested originals. No original196 index is rewritten or claimed currently unchanged after separately authorized proving activity.

Only this correction report and receipt are created. No newly authored module/proof was inspected or accepted here; parent-reported G001/G002 compilation and running G003 work are not this review's evidence. No additional public target, expanded proof permission, native action, chapter/Goal acceptance or publication is authorized. Existing R1–R10 and future gate obligations remain exactly unchanged. This is a correction to review metadata and reasoning, not a new mathematics stage or fresh combined-gate claim.
