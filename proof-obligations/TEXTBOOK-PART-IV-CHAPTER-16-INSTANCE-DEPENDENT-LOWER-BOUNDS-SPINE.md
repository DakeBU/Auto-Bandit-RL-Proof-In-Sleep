# Proof Obligations: Textbook Part IV Chapter 16 instance-dependent lower bounds

Task id: `TEXTBOOK-PART-IV-CHAPTER-16-INSTANCE-DEPENDENT-LOWER-BOUNDS-SPINE`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`

Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `CH16-SOURCE-FENCE` | exact Definition 16.1 / Theorem 16.2 / Lemma 16.3 / Theorem 16.4 | official source | evidence artifacts | textbook cards | freeze all quantifiers, directions, constants, pages | three editions distinct | source evidence | repository artifacts | source review | mapped |
| `CH16-CONSISTENCY` | every `nu in E`, every real `p>0`, `R_n/n^p -> 0` | filters/rpow | `Tendsto` | `MLIB-ASYMPTOTICS` | direct definition | nonnegativity remains caller fact | project-local | `IsConsistentRegret`; `IsConsistentPolicyOver` | focused Lean | compiled |
| `CH16-CONSISTENCY-SUM` | consistency of `R+R'` | previous node | `Tendsto.add` | `MLIB-ASYMPTOTICS` | add normalized limits | same exponent | project-local | `IsConsistentRegret.add` | focused Lean | compiled |
| `CH16-POWER` | eventually `R+R'<=n^p` | consistency sum | `eventually_lt_const`, real rpow | `MLIB-ASYMPTOTICS` | bound ratio by one and clear denominator | `p>0`, eventually `n>0` | project-local | `IsConsistentRegret.eventually_add_le_rpow` | focused Lean | compiled |
| `CH16-LOG` | eventually `log(R+R')/log n<=p` | power leaf | `Real.log_le_log`, `Real.log_rpow` | `MLIB-REAL-LOG-SQRT` | monotone log and positive division | positive sum; eventually `n>1` | project-local | `IsConsistentRegret.eventually_log_add_div_log_le` | focused Lean | compiled |
| `CH16-DINF` | extended-real distribution-class infimum | Chapter 14 KL | complete-lattice `sInf` | Mathlib source | literal source set comprehension | measurable reward; explicit mean map | project-local | `divergenceInfimum`; `divergenceInfimum_le` | focused Lean | compiled |
| `CH16-PARAMETRIC-DINF` | family-indexed infimum/candidate | previous node | `sInf_le` | Mathlib source | insert any strictly better parameter | strict mean inequality | project-local | `parametricDivergenceInfimum`; `parametricDivergenceInfimum_le` | focused Lean | compiled |
| `CH16-GAUSSIAN-PERTURB` | cost at `muStar+epsilon` | Chapter 15 Gaussian KL | `klDiv_gaussianReal_one` | local compiled card | insert alternative and normalize square | `epsilon>0`; direction fixed | project-local | `unitGaussianDivergenceInfimum_le_perturbed` | focused Lean | compiled |
| `CH16-GAUSSIAN-DINF` | exact `gap^2/2` infimum | preceding candidate | limit/infimum/order APIs | `MLIB-ASYMPTOTICS` | prove lower bound, then squeeze epsilon to zero | `mu<muStar`; ENNReal branches | Mathlib candidate | none | focused Lean | partial |
| `CH16-HISTORY` | original-law expected-pull information inequality | Ch15 Lemma 15.1 | stochastic policy/history | KL chain-rule route | change one arm | same policy; first-law expectation | connected blocker | none | focused Lean | blocked |
| `CH16-THM-16-2` | exact Eq. (16.2) | history, log, dInf | liminf filters | source card | epsilon alternative then liminf | zero/finite/infinite `d_inf` | source terminal | reserved | focused Lean | blocked |
| `CH16-LEMMA-16-3` | exact Eq. (16.4) | history KL, BH | Ch14/15 | source card | event `T_i(n)>n/2` | positive log terms; finite positive KL branch | source terminal | reserved | focused Lean | blocked |
| `CH16-THM-16-4` | exact Eq. (16.5) | Lemma 16.3, Gaussian KL, regret decomposition | local Gaussian and sums | source card | shift by `Delta_i(1+epsilon)` and sum positive parts | `N` nonempty, `C>0`, `0<p<1`, `0<epsilon<=1` | source terminal | reserved | focused Lean | blocked |
| `CH16-CANARY` | root-import typed applications and axiom reports | compiled slice | `BanditRLProof` root | local declarations | instantiate nontrivial Gaussian candidate | no placeholders | project-local | `Tests/TextbookPartIVChapter16Canary.lean` | Tests | pending |
| `CH16-SITE-REVIEW` | synchronized evidence/site and independent audit | all above | build/check/browser | repository | compare informal and Lean statements | no terminal promotion | repository | evidence artifacts | full/remote | pending |

## Failure classification

The current source-terminal failure is a `connected blocker`: Chapter 15's
conditional kernel-KL integral and stochastic-policy history law are absent.
The exact Gaussian `d_inf` equality and final liminf manipulation are separate
`local Lean lemma gap` obligations. No theorem target is weakened in response.

## Reviewer notes

- Compare the informal and Lean consistency quantifier order exactly.
- Check `P_i -> P_i'` KL direction and original-law pull expectation.
- Check the strict alternative mean and event `T_i(n)>n/2`.
- Check empty/zero/infinite `d_inf` and real-division branches.
- Check that Eq. (16.5)'s positive part covers the entire per-gap quotient.
- Check one common stochastic policy and unit Gaussian variance.
- Do not promote source or route cards to compiled evidence.
