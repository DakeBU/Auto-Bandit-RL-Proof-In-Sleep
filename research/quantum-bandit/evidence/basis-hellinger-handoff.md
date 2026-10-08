# Computational-basis Hellinger lower-leaf handoff

Objective / frontier: the pre-proof `BasisHellingerSeal.md` at quantum HEAD
`305952f4291d7be530c76f51f7e98d77faf1cf45`, Lean 4.29.1. Reused substantive-worker
protocol already read for the query-word objective; read the new seal before code.

Mathematical delta / exact verified statements: in namespace
`QuantumBlockEncoding.BasisHellinger`, for finite complex Euclidean vectors,
`basisProbability x j = ‖x j‖²` and
`hellingerSq p r = ∑ j, (sqrt(p j)-sqrt(r j))²` (NO factor 1/2).

- `basisProbability_nonneg`: each actual basis probability is nonnegative.
- `sum_basisProbability`: `∑ j, basisProbability x j = ‖x‖²`.
- `basisProbability_normalized`: normalized x gives probability mass exactly 1.
- `sqrt_basisProbability`, `hellingerSq_basis_formula`: actual H² is exactly
  `∑ j, (‖x j‖-‖y j‖)²`.
- `hellingerSq_basis_le`: this H² is at most `‖x-y‖²`, without normalization premises.
- `wordOutput w U ψ = Matrix.toEuclideanCLM (QuantumQueryWord.eval w U) ψ`.
- `wordOutput_norm`, `wordOutput_probability_normalized`: word output normalization
  is proved from actual instruction/oracle unitarity and normalized input ψ.
- `wordOutput_distance_le`: for unitary U,V, normalized ψ and `‖U-V‖op ≤ η`, actual
  output distance is at most `q*η`, with `q = QuantumQueryWord.queryCount w`.
- `word_hellingerSq_le`: actual output basis distributions satisfy `H² ≤ q²*η²`.
- `bounded_word_hellingerSq_le`: if actual `q ≤ D`, then `H² ≤ D*q*η²`; the proof
  explicitly establishes `q²*η² ≤ D*q*η²` by nonnegative multiplication.

Source / Lean expansion: coordinate squared norms → PiLp L2 norm identity →
genuine distribution normalization; coordinate reverse triangle → sum of squared
distances; chronological word unitary certificate → normalized output; existing
query-word operator telescoping → derived state distance → H² bound → budget
refinement. Every node in the scoped seal is discharged. Canary assembles both
distributions' nonnegativity/normalization and both bounds from ONLY source inputs.

Binder/definition audit: finite index and DecidableEq only where matrix/query
semantics need it (TYPING); unitary U,V, normalized ψ, same literal word/known
gates, operator distance and optional q≤D are SOURCE. No EXCESS assumptions of
output unitarity, state distance, probability normality, reverse triangle, η≥0 or
quadratic cost. η≥0 is derived from operator distance. Definitions are literal.
No additional nonempty-dimension assumption. QueryCount still charges BOTH oracle
directions via its prior exact forward+inverse count theorem.

Files changed only:

- `QuantumBlockEncoding/BasisHellinger.lean` SHA256
  `7C53AE6D5A845829A2F1E41191D17973215CC1D76D5C1389A64C47EEF43D64A5`.
- `ABEISTests/BasisHellingerCanary.lean` SHA256
  `0A9A54D9C252E2474834221FE945C87839C0EE7282A650FD6AAB006B836A6DFD`.
- This handoff. No roots/global metadata/other authors' modules or original D-drive
  repositories modified, no push.

Exact validation commands in `C:\qb261009\quantum`:

1. `lake env lean -o .lake\build\lib\lean\QuantumBlockEncoding\BasisHellinger.olean QuantumBlockEncoding\BasisHellinger.lean`:
   initial attempt IMPLEMENTATION_FAILED exit1: final budget tactic's multiline
   argument syntax failed at line122; other analytic/query lemmas accepted, with
   unused-section-variable warnings. Replaced budget tactic by literal monotone
   multiplications, minimized unused binders. Final retry PASS exit0, no warnings.
2. `lake build QuantumBlockEncoding.BasisHellinger ABEISTests.BasisHellingerCanary`:
   PASS exit0, 3401 jobs; module 40s, canary 42s. The four `#check` types match the
   sealed contract. All five `#print axioms` reports show only
   `[propext, Classical.choice, Quot.sound]`, with no sorryAx or new axioms.
3. Text scan found no sorry/admit/axiom declarations in owned files. Canary audits
   five root theorem axioms and exports four exact theorem types via `#check`.

Failure / salvage: NONE for final focused module compilation; no mathematical
route rejected; all scoped fragments retained and verified, no transient residue.
Reuse audit: local BornStability supplies unitary norm-map semantics; local
QuantumQueryWord supplies actual chronological fixed-oracle telescoping and query
cost. Mathlib PiLp L2 norm identity, reverse norm triangle and real square root are
reused directly. No competing external state/probability API introduced.

Direction fingerprint: `computational-basis / literal-probabilities /
reverse-triangle-L2 / derived-query-output / q²-to-Dq`.
Expected information gain: genuine dimension-independent per-block Hellinger
ingredient for a future lower bound, independently of estimator closure. Parent
explicitly admitted the worker; one route, no multi-route comparator needed.
Relevant process memory: QBE-PM-VERIFIER-SEMANTIC-LEVEL; no finite simulation promoted.

Purification/Exposition Seal: PROVED_LOCAL after focused gates; independent
round-trip/source review and publication/aggregate/site gates belong to integration
owner. This does not certify an arbitrary POVM, tensor-register dilation, reset
protocol, adaptive chain, stopping argument, hypothesis test or minimax/regret
lower bound. Those and the two-arm parameter-to-unitary-distance producer remain
explicit missing leaves. Recommended next independent node: derive a concrete
two-arm oracle-distance bound in the same access model, or prove the classical
history Hellinger chain using genuinely produced reset-block laws. No lower-bound
closure is claimed here.
