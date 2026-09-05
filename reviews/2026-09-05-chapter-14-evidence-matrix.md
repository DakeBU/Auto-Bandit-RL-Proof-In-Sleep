# Chapter 14 current evidence matrix

Scope: required body author pp.186-191, ending before Notes. Names below are
under BanditRLProof.LowerBounds; module paths are in BanditRLProof/LowerBounds/.
Canaries are Tests/TextbookPartIVChapter14<Suffix>Canary.lean. Historical
accepted/task/site status does not independently certify the expanded body.

| Body content | Source module | Exact terminal or interface | Canary suffix | Full gate |
| --- | --- | --- | --- | --- |
| prefix-code model and entropy units | InformationTheory | BinaryPrefixCode; expectedCodeLength; discreteEntropyBaseTwo_eq_div_log_two | (empty) | existing spine + subsequent gates |
| Eq.14.1/14.2 global Huffman optimum | HuffmanConstruction | huffmanCode_optimal; huffmanCode_entropy_sandwich | HuffmanConstruction | dff13cb |
| arithmetic expected-rate convergence | ArithmeticBlockCoding | arithmeticBlockCode_rate_tendsto_entropy | ArithmeticBlock | 2a31a01 |
| universal source-code converse | BlockEntropy | sourceBlock_code_family_limit_ge_entropy | Block | d256f27 and subsequent gates |
| finite KL / Eq.14.4 | FiniteDiscreteKL | relativeEntropy_finite_sum_log; relativeEntropy_finite_eq_top_iff | (empty) | 40c56ca and subsequent gates |
| Eq.14.5 / RN equivalence | FinitePartitionKLRecovery | finitePartitionRelativeEntropy_eq_relativeEntropy | Recovery | 40c56ca |
| Eq.14.6 common density | CommonDensityKL | relativeEntropy_commonDensity_eq_if | CommonDensity | 78846b8 |
| Theorem14.2 / Eq.14.7 | InformationTheory | bretagnolleHuber | (empty) | existing spine + subsequent gates |
| Eq.14.8 source Jensen step | AffinityKL | bretagnolleHuberScale_le_half_commonDensityAffinity_sq | Affinity | b8325c2 |
| Eq.14.9 Le Cam bound | CommonDensityOverlap | half_commonDensityAffinity_sq_le_overlap | Overlap | b8325c2 |
| Gaussian KL and testing constants | GaussianTesting | klDiv_gaussianReal_same_variance; gaussian_testing_max_error_three_twentieths | Gaussian | 1e8af14 |
| non-metric counterexamples | RelativeEntropyNonMetric | bernoulliRelativeEntropy_asymmetry; relativeEntropy_triangle_counterexample | NonMetric | d325147 running |
| cross entropy and zero-mass limit | CrossEntropy | relativeEntropy_finite_crossEntropy; entropyTerm_tendsto_zero_right | CrossEntropy | d325147 running |
| ceiling-log fixed-length construction | FixedLengthCoding | exists_ceilingLogPrefixCode | FixedCode | d325147 running |
| precise uniform-law qualification | UniformCoding | fixedLength_uniformPowerTwo_optimal; uniform_three_fixedLength_not_optimal | UniformCode | pending after d325147 |
| common domination and finite-KL iff | CommonDomination | exists_commonSigmaFiniteDominatingMeasure; relativeEntropy_finite_lt_top_iff_ac | Domination | pending after d325147 |

Intermediate construction canaries remain in the aggregate: CodingBound,
Shannon, PrefixConstruction, Exchange, Sibling, Pruning, Greedy, HuffmanStep,
HuffmanAlphabet, ArithmeticIntervals, Dyadic, ArithmeticPrefix, ArithmeticZero,
Partition and Filtration. Optional arbitrary-sub-sigma DPI remains in the
main Chapter14 canary; Chapter15 history KL is not a Chapter14 theorem.

## Source/model qualifications to preserve in every export

1. Nonempty codewords imply a one-bit singleton convention; the naive empty
   singleton word is not represented as an allowed local code.
2. Uniform constant-length optimality holds at power-of-two cardinalities;
   the broad arbitrary-N reading is refuted by the compiled ternary example.
3. Arithmetic coding is a classical exact-real interval-address construction
   with a constant support/escape overhead, not an executable implementation.
   Rate is expected bits per symbol for finite IID blocks, with zero masses.
4. Cross-entropy differences are unrounded information quantities. Infinite
   support mismatch is handled in ENNReal, not totalized real-log arithmetic.
5. Finite KL iff AC is finite-alphabet-only; Gaussian variance is positive;
   main BH is unconditional with exp(-infinity)=0 and KL direction P to Q.

## Non-proof gates still required

Final aggregate including UniformCoding/CommonDomination; current full-body
source declaration/canary audit; synchronized conversion/obligation status;
Markdown/LaTeX build and visual QA; site content/build/browser verification;
any required remote publication evidence. The LaTeX fragment now compiles
with the temporary article wrapper, but this alone is not visual QA.
Whole chapter remains partial while these checks are pending.

Export build check: the synchronized LaTeX fragment compiled with installed
TeX Live 2025 using tmp/ch14-export-check.tex. Three overfull identifier lines
were repaired using discretionary breaks; the final log has no overfull boxes
or LaTeX errors and produces a three-page PDF. Log:
tmp/ch14-export-build/ch14-export-check.log. Visual page review remains pending;
temporary wrapper/build outputs are not committed source artifacts.
