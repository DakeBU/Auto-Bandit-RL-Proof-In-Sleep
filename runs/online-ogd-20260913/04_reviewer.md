# Semantic reviewer decision

Reviewer phase: same GPT-6 Astra model, separate phase after implementation;
not independent external review. Reviewed source PDF printed pp.12-15 against
frozen v1 headers, actual current proof bodies and public-root canary.

Verdict: semantic acceptance of the scoped mathematical package. Full local
harness also passed (full-gate-exit.txt=0; 422 tests, 7 skipped). Source-map
validation and reviewable PR delivery are recorded separately before Goal closure.

| Requirement | Review result and direct evidence |
|---|---|
| Algorithm identity | project is chosen from mathlib's actual minimizer existence, not supplied as an oracle certificate; step evaluates gradient of current loss; iterate uses genuine Nat recursion |
| Projection feasibility and uniqueness | project_spec and project_eq_of_variational prove membership/minimality and the unique variational representative; canary actually uses the public characterization |
| Proposition 2.11 | arbitrary z and feasible u; proof uses variational inequality and norm expansion, not a assumed contraction |
| Convex differentiability | RegularLoss supplies convexity and differentiability on an open neighborhood; first_order constructs affine line, differentiates it and applies ConvexOn.le_slope_of_hasDerivAt |
| Lemma 2.12 | conclusion retains BOTH loss/inner-product and inner-product/potential inequalities; no one-step certificate is a premise |
| Fixed-step Theorem 2.13 | same actual iterate in losses, gradients and terminal; eta>0; no diameter premise; negative terminal term explicitly retained |
| Eq. (2.1) | positive D,G and T>0; hgrad is about the specified tuned trajectory; uniform diameter bound supplies each u after fixing that trajectory |
| Indices and information | zero-based t maps source t+1; current point is independent of loss t and later by iterate_prefix; fixed terminal valid at T=0 |
| Source dimensionality | generalized from finite-dimensional Euclidean space to real Hilbert spaces, with the required finite-dimensional instance checked through EuclideanSpace R (Fin 3) |
| Evidence authority | no arbitrary algorithm exists premise, presumed stability/regret inequality, numerical approximation or future-gradient-dependent tuning |
| Nondegeneracy | V=[0,1], gradients -2 and 1/2, first projection clips 2 to 1, terminal point 1/2, regret 1/2, terminal square 1/4 |
| Foundation audit | all printed OGD theorems and canary depend only on propext, Classical.choice, Quot.sound; no custom assumption or unfinished proof constant |
| Freeze integrity | original headers and definition/typeclass prefix remain unchanged; corrected native fence metadata is compared with original captures by check_online_ogd_contract.py |
| Dependency evidence | compiled-dependencies.json is a scoped excerpt of the actual root environment export, with six explicit source-chain proof-value occurrence checks; it is not a kernel execution trace |
| Shared Book identity | Online Learning Book references teaching:online-ogd; all nodes retain declaration:BanditRL.OnlineGradientDescent.* identity in the single canonical registry; old Book references remain |

The fixed-step source explicitly allows an unbounded domain (printed p.14).
Using a positive upper bound on diameter rather than requiring an attained exact
supremum preserves the source corollary and makes its hypotheses directly usable.
Separate loss neighborhoods cause no semantic gap for a finite prefix; a finite
intersection contains V and is open. Exact-real noncomputability of projection
is stated; no executable numerical solver or online Lean service is claimed.

Rejected expansions: entire Chapter 2; Theorem 2.13 varying steps; general OMD;
Tsallis dual guarantees; automatic acceptance by command exit; main/live updates.
The maintained SGB frontier is not altered by accepting this independent package.
