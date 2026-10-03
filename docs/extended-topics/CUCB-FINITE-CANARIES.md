# CUCB concrete noisy model witnesses

2026-09-18. These are concrete instances of the full frozen SourceModel and original actual-trajectory regret. They supplement the symbolic dependency audit. The combinatorial topic remains incomplete pending independent semantic acceptance, shared mappings and all-topic evidence.

## Primitive model

CUCBFiniteExample uses the existing Thompson.uniformActionMeasure on Fin4 x Bool x Fin4 x Bool: 64 equally likely atoms. Separate coordinates produce Bernoulli means 1/4, 1/2, 3/4 and an independent fair trigger coin. Each marginal is the actual pushforward law, not a supplied concentration premise. The finite probabilities, observed marginal compatibility, reward integrability and nonnegativity are proved directly. noisy_each_arm proves the probability of outcome one is strictly between zero and one for every arm.

The two feasible actions select {0,1} and {1,2}; selected_size proves both have two arms and the model proves the sets distinct. Every selected arm is observed. The other arm is observed when the extra coin is true. Actual per-arm minimum trigger probabilities are (1/2,1,1/2), with global minimum 1/2. Reward is the product of the selected outcomes. Actual expected rewards are 1/8 and 3/8.

## Full models and terminal instances

CUCBFiniteSourceExample proves the nonlinear input score v0*v1 or v1*v2 is nonnegative, monotone and 2-Lipschitz in the source sup-coordinate condition, with modulus f(u)=2u (gamma=2, omega=1). Its measurable deterministic oracle maximizes the current input score; ties choose the first action. All SourceModel fields are proved, including inverse range and oracle success. No performance, count, confidence or tail premise is added.

The source instance has alpha=beta=1, maximum positive gap 1/4. first_action_law proves the actual first action is almost surely the inferior action; regret_one_positive proves original actual-trajectory R(1)=1/4. Thus the principal learning witness is not only a nonpositive approximation-regret case.

refined_regret instantiates full Theorem1. probabilistic_regret instantiates Theorem2 for all integer H>=1 and simplifies the exact source bound to:

    R(H) <= 4*(72*log H)^(1/2)*H^(1/2)
      +(1+pi^2/2)*3/4+30*log H.

randomizedSource uses an actual uniform two-action oracle with alpha=1, beta=1/2. Its source success condition is proved by the presence of a maximizing action; randomized_action_mass proves each action has probability 1/2 at every input. randomized_probabilistic_regret instantiates the same full performance theorem with the original signed alpha*beta benchmark. This supplementary oracle intentionally ignores its input and is not presented as a learning improvement; the input-dependent primary model above supplies the learning witness.

noBadSource sets alpha=1/3 while retaining the exact maximizing oracle and noisy environment. The worse true reward equals alpha times the optimum; no_bad_regret proves R(H)<=0 for every H, including zero, through the general empty-bad-family terminal theorem.

CUCBFiniteDeterministicExample keeps the same noisy samples, action sets, rewards, marginal laws and maximizing oracle, replacing only the observation mask by full observation. Its feedback compatibility and SourceModel are proved. full_globalMinTrigger=1 and deterministic_regret instantiates the other Theorem2 branch for H>=1:

    R(H) <= 4*(18*log H)^(1/2)*H^(1/2)+(1+pi^2/3)*3/4.

## Validation and limits

All three modules are imported by the shared public root. Tests/CUCBFiniteModelCanary checks the concrete witnesses and prints dependencies of the model structures and terminal results. Focused compilation passed with only propext, Classical.choice and Quot.sound. The joint gate and local site receipt are recorded separately after execution.

The finite canary has bounded rewards; it does not add a bounded realized-reward hypothesis to the general SourceModel or performance theorems. Source/repair independent review, exact shared source/topic/declaration mappings and all-ten ICLR controlled evidence remain required. Compilation is not independent source acceptance or a controlled experiment. No merge or deployment is claimed.
