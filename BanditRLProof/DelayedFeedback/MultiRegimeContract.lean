namespace BanditRLProof

namespace DelayedFeedback

universe uAlgorithm uInitialization uTuning uInformation uComparator
  uStochasticEnvironment uAdversarialEnvironment

/-- A source-facing interface for a theorem that evaluates one algorithmic
object in two environment regimes.  Both endpoint predicates receive the same
algorithm, initialization, tuning, information structure, and comparator.

This structure is only a target contract.  Constructing its data does not
prove either endpoint, identify Delayed SAPO, or establish best-of-both-worlds
regret. -/
structure SameAlgorithmMultiRegimeContract
    (Algorithm : Type uAlgorithm)
    (Initialization : Type uInitialization)
    (Tuning : Type uTuning)
    (Information : Type uInformation)
    (Comparator : Type uComparator)
    (StochasticEnvironment : Type uStochasticEnvironment)
    (AdversarialEnvironment : Type uAdversarialEnvironment) where
  algorithm : Algorithm
  initialization : Initialization
  tuning : Tuning
  information : Information
  comparator : Comparator
  stochasticEndpoint :
    Algorithm → Initialization → Tuning → Information → Comparator →
      StochasticEnvironment → Prop
  adversarialEndpoint :
    Algorithm → Initialization → Tuning → Information → Comparator →
      AdversarialEnvironment → Prop

namespace SameAlgorithmMultiRegimeContract

/-- The stochastic endpoint instantiated with the contract's shared identity
fields. -/
def stochasticClaim
    {Algorithm : Type uAlgorithm}
    {Initialization : Type uInitialization}
    {Tuning : Type uTuning}
    {Information : Type uInformation}
    {Comparator : Type uComparator}
    {StochasticEnvironment : Type uStochasticEnvironment}
    {AdversarialEnvironment : Type uAdversarialEnvironment}
    (contract : SameAlgorithmMultiRegimeContract Algorithm Initialization
      Tuning Information Comparator StochasticEnvironment
      AdversarialEnvironment)
    (environment : StochasticEnvironment) : Prop :=
  contract.stochasticEndpoint contract.algorithm contract.initialization
    contract.tuning contract.information contract.comparator environment

/-- The adversarial endpoint instantiated with exactly the same shared
algorithm, initialization, tuning, information, and comparator fields. -/
def adversarialClaim
    {Algorithm : Type uAlgorithm}
    {Initialization : Type uInitialization}
    {Tuning : Type uTuning}
    {Information : Type uInformation}
    {Comparator : Type uComparator}
    {StochasticEnvironment : Type uStochasticEnvironment}
    {AdversarialEnvironment : Type uAdversarialEnvironment}
    (contract : SameAlgorithmMultiRegimeContract Algorithm Initialization
      Tuning Information Comparator StochasticEnvironment
      AdversarialEnvironment)
    (environment : AdversarialEnvironment) : Prop :=
  contract.adversarialEndpoint contract.algorithm contract.initialization
    contract.tuning contract.information contract.comparator environment

theorem stochasticClaim_iff_shared_fields
    {Algorithm : Type uAlgorithm}
    {Initialization : Type uInitialization}
    {Tuning : Type uTuning}
    {Information : Type uInformation}
    {Comparator : Type uComparator}
    {StochasticEnvironment : Type uStochasticEnvironment}
    {AdversarialEnvironment : Type uAdversarialEnvironment}
    (contract : SameAlgorithmMultiRegimeContract Algorithm Initialization
      Tuning Information Comparator StochasticEnvironment
      AdversarialEnvironment)
    (environment : StochasticEnvironment) :
    stochasticClaim contract environment ↔
      contract.stochasticEndpoint contract.algorithm contract.initialization
        contract.tuning contract.information contract.comparator environment := by
  rfl

theorem adversarialClaim_iff_shared_fields
    {Algorithm : Type uAlgorithm}
    {Initialization : Type uInitialization}
    {Tuning : Type uTuning}
    {Information : Type uInformation}
    {Comparator : Type uComparator}
    {StochasticEnvironment : Type uStochasticEnvironment}
    {AdversarialEnvironment : Type uAdversarialEnvironment}
    (contract : SameAlgorithmMultiRegimeContract Algorithm Initialization
      Tuning Information Comparator StochasticEnvironment
      AdversarialEnvironment)
    (environment : AdversarialEnvironment) :
    adversarialClaim contract environment ↔
      contract.adversarialEndpoint contract.algorithm contract.initialization
        contract.tuning contract.information contract.comparator environment := by
  rfl

end SameAlgorithmMultiRegimeContract

end DelayedFeedback

end BanditRLProof
