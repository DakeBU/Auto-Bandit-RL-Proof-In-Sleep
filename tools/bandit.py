#!/usr/bin/env python3
"""Local workflow helper for Auto-Bandit-RL-Proof-In-Sleep.

The helper is deliberately plain-file and dependency-free.  It is the stable
command surface for agents; it is not itself an AI agent.
"""

from __future__ import annotations

import argparse
import csv
import datetime as _dt
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
STATE_DIR = ROOT / ".abrl"
STATE_FILE = STATE_DIR / "state.json"
MANIFEST = ROOT / "MANIFEST.md"
TRIAL_LOG = ROOT / "runs" / "trials.jsonl"
TRIAL_SUMMARY = ROOT / "runs" / "trials_summary.csv"
BLUEPRINT_DIR = ROOT / "proof-blueprints"
RETRIEVAL_INDEX_DIR = ROOT / "research-wiki" / "retrieval-index"
PROBLEM_EXPORT_DIR = ROOT / "paper-notes" / "problem-exports"
AGENT_PROFILE_DIR = ROOT / "agent-profiles"

AGENT_ROLES = ("upper", "middle", "lower", "reviewer")
TRIAL_KINDS = ("plan", "attempt", "build", "review", "proposal", "compression", "handoff", "export")
TRIAL_STATUSES = ("queued", "running", "blocked", "failed", "compiled", "accepted", "rejected")

WORK_DIRS = [
    "tasks",
    "task-inbox",
    "conversion-windows",
    "paper-notes",
    "paper-notes/problem-exports",
    "agent-briefs",
    "proof-attempts",
    "proof-blueprints",
    "proof-obligations",
    "verifier-feedback",
    "candidate-populations",
    "open-problem-proposals",
    "reviews",
    "reports",
    "runs",
    "runs/logs",
    "runs/context-packs",
    "runs/pro-prompts",
    "run-presets",
    "agent-profiles",
    "research-wiki/papers",
    "research-wiki/ideas",
    "research-wiki/claims",
    "research-wiki/cited-results",
    "research-wiki/proof-techniques",
    "research-wiki/proof-weapons",
    "research-wiki/open-problems",
    "research-wiki/retrieval-index",
    "research-wiki/lml",
    "research-wiki/mathlib",
    "research-wiki/mathlib-candidates",
    "research-wiki/textbooks",
    "research-wiki/scenarios",
    "research-wiki/theory-tree",
    "templates",
]

LML_SEED_COMMIT = "19dc3ab132c2a7539f5944503d1114eac4c5bb74"
LML_SEED_DATE = "2026-06-24"

LML_CARDS = [
    {
        "id": "LML-BANDIT-REGRET-GAP",
        "source": "LeanMachineLearning/LML",
        "declaration": "Bandits.regret_eq_sum_gap",
        "module": "LeanMachineLearning.Online.Bandit.Regret",
        "role": "Regret decomposition into a sum of action gaps.",
        "status": "theorem-card",
    },
    {
        "id": "LML-BANDIT-REGRET-PULLCOUNT",
        "source": "LeanMachineLearning/LML",
        "declaration": "Bandits.regret_eq_sum_pullCount_mul_gap",
        "module": "LeanMachineLearning.Online.Bandit.Regret",
        "role": "Regret decomposition through arm pull counts.",
        "status": "theorem-card",
    },
    {
        "id": "LML-ETC-REGRET",
        "source": "LeanMachineLearning/LML",
        "declaration": "Bandits.ETC.regret_le",
        "module": "LeanMachineLearning.Online.Bandit.Algorithms.ETC",
        "role": "Explore-Then-Commit expected regret bound.",
        "status": "theorem-card",
    },
    {
        "id": "LML-UCB-REGRET",
        "source": "LeanMachineLearning/LML",
        "declaration": "Bandits.UCB.regret_le",
        "module": "LeanMachineLearning.Online.Bandit.Algorithms.UCB",
        "role": "UCB logarithmic pull-count regret route.",
        "status": "theorem-card",
    },
    {
        "id": "LML-TS-POSTERIOR-ACTION",
        "source": "LeanMachineLearning/LML",
        "declaration": "Bandits.TS.hasCondDistrib_action",
        "module": "LeanMachineLearning.Online.Bandit.Algorithms.TS",
        "role": "Thompson sampling action distribution equals posterior best-action distribution.",
        "status": "theorem-card",
    },
    {
        "id": "LML-TS-BAYES-REGRET",
        "source": "LeanMachineLearning/LML",
        "declaration": "Bandits.integral_regret_le",
        "module": "LeanMachineLearning.Online.Bandit.Algorithms.Regret.BayesRegretTS",
        "role": "Bayesian regret upper bound for Thompson sampling.",
        "status": "theorem-card",
    },
]

MATHLIB_CARDS = [
    {
        "id": "MLIB-FINSET-SUMS",
        "source": "Mathlib",
        "module": "Mathlib.Data.Finset.Basic; Mathlib.Algebra.BigOperators.Fin",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html",
        "query_terms": ["Finset.sum", "Finset.range", "sum_filter", "sum_congr", "card_filter"],
        "role": "Finite sums, indicator partitions, pull-count decompositions, and arm/time reindexing.",
        "status": "import-candidate",
    },
    {
        "id": "MLIB-FINTYPE-FIN",
        "source": "Mathlib",
        "module": "Mathlib.Data.Fintype.Basic; Mathlib.Data.Fin.Basic",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Basic.html",
        "query_terms": ["Fintype.card", "Fin", "Finite", "Nonempty", "Fin.cast"],
        "role": "Finite action spaces, nonempty arm sets, finite policies, and index coercions.",
        "status": "import-candidate",
    },
    {
        "id": "MLIB-ORDER-ALGEBRA",
        "source": "Mathlib",
        "module": "Mathlib.Algebra.Order.Field.Basic; Mathlib.Data.Real.Basic",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Field/Basic.html",
        "query_terms": ["linarith", "nlinarith", "div_le_iff", "mul_le_mul", "Nat.cast_pos"],
        "role": "Gap nonnegativity, confidence-width algebra, positivity, and denominator side conditions.",
        "status": "import-candidate",
    },
    {
        "id": "MLIB-REAL-LOG-SQRT",
        "source": "Mathlib",
        "module": "Mathlib.Analysis.SpecialFunctions.Log.Basic; Mathlib.Data.Real.Sqrt",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Log/Basic.html",
        "query_terms": ["Real.log", "Real.sqrt", "sq_sqrt", "log_nonneg", "sqrt_le_sqrt"],
        "role": "UCB radii, logarithmic regret simplification, and square-root confidence bounds.",
        "status": "import-candidate",
    },
    {
        "id": "MLIB-EXP-LOG-INEQUALITIES",
        "source": "Mathlib",
        "module": "Mathlib.Analysis.SpecialFunctions.Log.Basic",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Log/Basic.html",
        "query_terms": ["Real.exp", "Real.log", "exp_le_exp", "log_le_iff_le_exp", "rpow"],
        "role": "Exponential-weight potentials, Chernoff routes, KL-UCB algebra, and learning-rate optimization.",
        "status": "import-candidate",
    },
    {
        "id": "MLIB-MEASURE-INTEGRAL",
        "source": "Mathlib",
        "module": "Mathlib.MeasureTheory.Integral.Bochner.Basic",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/Basic.html",
        "query_terms": ["Integrable", "lintegral", "integral", "AEStronglyMeasurable", "AEMeasurable"],
        "role": "Expected regret, Bayesian regret, integrability contracts, and expectation linearity routes.",
        "status": "import-candidate",
    },
    {
        "id": "MLIB-PROBABILITY-INDEPENDENCE",
        "source": "Mathlib",
        "module": "Mathlib.Probability.Independence.Basic",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html",
        "query_terms": ["IndepFun", "iIndepFun", "IndepSet", "IdentDistrib", "iid"],
        "role": "IID rewards, product event decompositions, Hoeffding-style assumptions, and theorem contracts.",
        "status": "import-candidate",
    },
    {
        "id": "MLIB-CONDITIONAL-EXPECTATION",
        "source": "Mathlib",
        "module": "Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.html",
        "query_terms": ["condexp", "filtration", "adapted", "martingale", "stoppingTime"],
        "role": "Adaptive rewards, Thompson posterior identities, martingale concentration, and RL filtrations.",
        "status": "import-candidate",
    },
    {
        "id": "MLIB-MARTINGALE-STOCHASTIC",
        "source": "Mathlib",
        "module": "Mathlib.Probability.Martingale.Basic; Mathlib.Probability.Notation",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/Basic.html",
        "query_terms": ["Martingale", "Submartingale", "Supermartingale", "filtration", "stoppingTime"],
        "role": "Self-normalized processes, optional-stopping surfaces, delayed feedback, and finite-horizon RL regret.",
        "status": "import-candidate",
    },
    {
        "id": "MLIB-PROBABILITY-KERNEL",
        "source": "Mathlib",
        "module": "Mathlib.Probability.Kernel.Basic",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Basic.html",
        "query_terms": ["Kernel", "MarkovKernel", "bind", "comp", "prod"],
        "role": "Reward kernels, posterior kernels, finite-horizon MDP surfaces, and policy-induced laws.",
        "status": "import-candidate",
    },
    {
        "id": "MLIB-ASYMPTOTICS",
        "source": "Mathlib",
        "module": "Mathlib.Analysis.Asymptotics.Asymptotics",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Asymptotics/Asymptotics.html",
        "query_terms": ["Asymptotics.IsBigO", "IsTheta", "Eventually", "Filter.atTop"],
        "role": "Asymptotic optimality, logarithmic regret, minimax rates, and exported theorem statements.",
        "status": "import-candidate",
    },
    {
        "id": "MLIB-CONVEX-LINALG",
        "source": "Mathlib",
        "module": "Mathlib.Analysis.Convex.Basic; Mathlib.LinearAlgebra.Matrix",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/Basic.html",
        "query_terms": ["Convex", "Matrix", "inner", "norm", "IsBounded", "projection"],
        "role": "Linear bandits, confidence ellipsoids, least-squares design, and convex action sets.",
        "status": "import-candidate",
    },
    {
        "id": "MLIB-METRIC-TOPOLOGY",
        "source": "Mathlib",
        "module": "Mathlib.Topology.MetricSpace.Basic",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Basic.html",
        "query_terms": ["Metric.ball", "Metric.closedBall", "LipschitzWith", "TotallyBounded", "diam"],
        "role": "Lipschitz/continuum bandits, covering arguments, nearest-neighbor policies, and metric action spaces.",
        "status": "import-candidate",
    },
    {
        "id": "MLIB-PROBABILITY-SUBGAUSSIAN",
        "source": "Mathlib",
        "module": "Mathlib.Probability.Moments.SubGaussian",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/SubGaussian.html",
        "query_terms": [
            "measure_sum_ge_le_of_iIndepFun",
            "hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero",
            "measure_sum_ge_le_of_HasCondSubgaussianMGF",
            "HasSubgaussianMGF",
        ],
        "role": "Hoeffding-style tails, Azuma-Hoeffding routes, sub-Gaussian reward sums, and UCB/ETC concentration leaves.",
        "status": "import-candidate",
    },
    {
        "id": "MLIB-PROBABILITY-MGF",
        "source": "Mathlib",
        "module": "Mathlib.Probability.Moments.Basic; Mathlib.Probability.Moments.Tilted",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/Basic.html",
        "query_terms": ["mgf", "cgf", "IndepFun.mgf_add", "IndepFun.cgf_add", "tilted"],
        "role": "Moment-generating and cumulant-generating function algebra for Chernoff, exponential weights, and concentration routes.",
        "status": "import-candidate",
    },
    {
        "id": "MLIB-PROBABILITY-VARIANCE",
        "source": "Mathlib",
        "module": "Mathlib.Probability.Moments.Variance",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/Variance.html",
        "query_terms": ["variance", "chebyshev", "IndepFun.variance_add", "MemLp"],
        "role": "Variance bookkeeping, Chebyshev-style tails, robust/heavy-tailed baselines, and second-moment contracts.",
        "status": "import-candidate",
    },
    {
        "id": "MLIB-REAL-RPOW-TSALLIS",
        "source": "Mathlib",
        "module": "Mathlib.Analysis.SpecialFunctions.Pow.Real; Mathlib.Analysis.SpecialFunctions.Pow.NNReal",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Real.html",
        "query_terms": ["Real.rpow", "NNReal.rpow", "rpow", "rpow_le_rpow", "rpow_pos_of_pos"],
        "role": "Tsallis entropy regularizers, power potentials, FTRL/OMD penalty algebra, and nonnegative-probability weights.",
        "status": "import-candidate",
    },
]

BANDIT_TEXTBOOK_CARDS = [
    {
        "id": "TXT-BUBECK-CESABIANCHI-2012",
        "title": "Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems",
        "authors": "Sébastien Bubeck; Nicolò Cesa-Bianchi",
        "source": "https://arxiv.org/abs/1204.5721",
        "branches": ["iid finite-arm", "adversarial finite-arm", "contextual bandits", "lower bounds"],
        "proof_roots": ["regret decomposition", "UCB", "EXP3", "minimax lower bounds"],
        "memory_status": "survey-card",
    },
    {
        "id": "TXT-LATTIMORE-SZEPESVARI-2020",
        "title": "Bandit Algorithms",
        "authors": "Tor Lattimore; Csaba Szepesvári",
        "source": "https://tor-lattimore.com/downloads/book/book.pdf",
        "branches": [
            "probability and concentration",
            "finite stochastic arms",
            "adversarial finite arms",
            "lower bounds",
            "contextual and linear bandits",
            "adversarial linear bandits",
        ],
        "proof_roots": ["ETC", "UCB", "MOSS", "KL-UCB", "EXP3", "linear UCB", "least-squares confidence"],
        "memory_status": "textbook-card",
    },
    {
        "id": "TXT-SLIVKINS-2019-2024",
        "title": "Introduction to Multi-Armed Bandits",
        "authors": "Aleksandrs Slivkins",
        "source": "https://arxiv.org/abs/1904.07272",
        "branches": [
            "IID rewards",
            "Bayesian priors",
            "Lipschitz rewards",
            "adversarial rewards",
            "contextual bandits",
            "bandits with knapsacks",
            "bandits and agents",
        ],
        "proof_roots": ["Bayesian regret", "similarity/metric bandits", "BwK", "incentive-compatible exploration"],
        "memory_status": "textbook-card",
    },
]

BANDIT_PAPER_CARDS = [
    {
        "id": "PPR-AUER-CBF-2002-UCB1",
        "title": "Finite-time Analysis of the Multiarmed Bandit Problem",
        "authors": "Peter Auer; Nicolò Cesa-Bianchi; Paul Fischer",
        "source": "https://doi.org/10.1023/A:1013689704352",
        "scenarios": ["SCN-STOCHASTIC-FINITE"],
        "proof_roots": ["UCB1", "finite-time logarithmic regret", "gap-dependent regret"],
        "lean_leaf_families": ["pull-count threshold", "good event split", "tail summability"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-AUER-CFS-2002-EXP3",
        "title": "The Nonstochastic Multiarmed Bandit Problem",
        "authors": "Peter Auer; Nicolò Cesa-Bianchi; Yoav Freund; Robert E. Schapire",
        "source": "https://doi.org/10.1137/S0097539701398375",
        "scenarios": ["SCN-ADVERSARIAL-FINITE"],
        "proof_roots": ["EXP3", "exponential weights", "importance-weighted loss"],
        "lean_leaf_families": ["potential inequality", "unbiased estimator", "learning-rate optimization"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-ZIMMERT-SELDIN-2018-TSALLIS-INF",
        "title": "Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits",
        "authors": "Julian Zimmert; Yevgeny Seldin",
        "source": "https://arxiv.org/abs/1807.07623",
        "scenarios": ["SCN-BOBW-ADAPTIVE", "SCN-ADVERSARIAL-FINITE", "SCN-STOCHASTIC-FINITE"],
        "proof_roots": ["Tsallis-INF", "Tsallis entropy regularizer", "best-of-both-worlds regret"],
        "lean_leaf_families": ["FTRL optimality", "Tsallis potential algebra", "importance-weighted loss", "self-bounding regret"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-MASOUDIAN-SELDIN-2021-TSALLIS-INF",
        "title": "Improved Analysis of the Tsallis-INF Algorithm in Stochastically Constrained Adversarial Bandits and Stochastic Bandits with Adversarial Corruptions",
        "authors": "Saeed Masoudian; Yevgeny Seldin",
        "source": "https://arxiv.org/abs/2103.12487",
        "scenarios": ["SCN-BOBW-ADAPTIVE", "SCN-ADVERSARIAL-FINITE", "SCN-STOCHASTIC-FINITE"],
        "proof_roots": ["Tsallis-INF analysis", "stochastic/adversarial interpolation", "gap-dependent bounds"],
        "lean_leaf_families": ["stability term", "penalty term", "self-bounding conversion", "power-weight algebra"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-KATO-ITO-2024-LC-TSALLIS-INF",
        "title": "LC-Tsallis-INF: Generalized Best-of-Both-Worlds Linear Contextual Bandits",
        "authors": "Masahiro Kato; Shinji Ito",
        "source": "https://arxiv.org/abs/2403.03219",
        "scenarios": ["SCN-BOBW-ADAPTIVE", "SCN-LINEAR-GLM", "SCN-CONTEXTUAL"],
        "proof_roots": ["Linear contextual Tsallis-INF", "hybrid stochastic/adversarial regret", "high-probability bounds"],
        "lean_leaf_families": ["linear loss estimates", "Tsallis regularization", "confidence-plus-FTRL bridge"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-ADAPTIVE-LR-FTRL-2024",
        "title": "A Simple and Adaptive Learning Rate for FTRL in Online Learning with Minimax Regret of Theta(T^(2/3)) and its Application to Best-of-Both-Worlds",
        "authors": "Taira Tsuchiya; Shinji Ito",
        "source": "https://arxiv.org/abs/2405.20028",
        "scenarios": ["SCN-BOBW-ADAPTIVE", "SCN-ADVERSARIAL-FINITE"],
        "proof_roots": ["adaptive learning rates", "FTRL stability", "best-of-both-worlds"],
        "lean_leaf_families": ["learning-rate schedule", "stability/penalty split", "self-bounding conversion"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-GARIVIER-CAPPE-2011-KLUCB",
        "title": "The KL-UCB Algorithm for Bounded Stochastic Bandits and Beyond",
        "authors": "Aurélien Garivier; Olivier Cappé",
        "source": "https://arxiv.org/abs/1102.2490",
        "scenarios": ["SCN-STOCHASTIC-FINITE"],
        "proof_roots": ["KL-UCB", "bounded stochastic bandits", "Bernoulli KL routes"],
        "lean_leaf_families": ["KL monotonicity", "confidence inversion", "bounded reward event"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-AGRAWAL-GOYAL-2011-TS",
        "title": "Analysis of Thompson Sampling for the Multi-armed Bandit Problem",
        "authors": "Shipra Agrawal; Navin Goyal",
        "source": "https://arxiv.org/abs/1111.1797",
        "scenarios": ["SCN-STOCHASTIC-FINITE", "SCN-BAYESIAN-POSTERIOR"],
        "proof_roots": ["Thompson sampling", "posterior samples", "Bayesian regret"],
        "lean_leaf_families": ["posterior action identity", "Beta-Bernoulli update", "probability matching"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-ABBASI-YADKORI-2011-SELF-NORMALIZED",
        "title": "Online Least Squares Estimation with Self-Normalized Processes: An Application to Bandit Problems",
        "authors": "Yasin Abbasi-Yadkori; Dávid Pál; Csaba Szepesvári",
        "source": "https://arxiv.org/abs/1102.2670",
        "scenarios": ["SCN-LINEAR-GLM"],
        "proof_roots": ["self-normalized concentration", "linear least squares", "OFUL confidence"],
        "lean_leaf_families": ["Gram matrix monotonicity", "elliptical potential", "martingale vector bound"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB",
        "title": "A Contextual-Bandit Approach to Personalized News Article Recommendation",
        "authors": "Lihong Li; Wei Chu; John Langford; Robert E. Schapire",
        "source": "https://doi.org/10.1145/1772690.1772758",
        "scenarios": ["SCN-CONTEXTUAL", "SCN-LINEAR-GLM", "SCN-LLM-REC-SYS"],
        "proof_roots": ["LinUCB", "offline evaluation", "contextual reward model"],
        "lean_leaf_families": ["feature-vector reward", "argmax policy", "context-history interface"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-AZAR-OSBAND-MUNOS-2017-UCBVI",
        "title": "Minimax Regret Bounds for Reinforcement Learning",
        "authors": "Mohammad Gheshlaghi Azar; Ian Osband; Rémi Munos",
        "source": "https://arxiv.org/abs/1703.05449",
        "scenarios": ["SCN-RL-MDP"],
        "proof_roots": ["UCB-VI", "finite-horizon MDP regret", "Bellman optimism"],
        "lean_leaf_families": ["finite kernels", "Bellman recursion", "episode regret telescope"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-BADANIDIYURU-KLEINBERG-SLIVKINS-2013-BWK",
        "title": "Bandits with Knapsacks",
        "authors": "Ashwinkumar Badanidiyuru; Robert Kleinberg; Aleksandrs Slivkins",
        "source": "https://arxiv.org/abs/1305.2545",
        "scenarios": ["SCN-RESOURCE-CONSTRAINED"],
        "proof_roots": ["bandits with knapsacks", "primal-dual resource allocation", "budgeted regret"],
        "lean_leaf_families": ["resource consumption trace", "budget stopping time", "Lagrangian comparison"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-IJCAI-2018-DUELING-SURVEY",
        "title": "Advancements in Dueling Bandits",
        "authors": "Yanan Sui; Masrour Zoghi; Katja Hofmann; Yisong Yue",
        "source": "https://doi.org/10.24963/ijcai.2018/776",
        "scenarios": ["SCN-DUELING-PREFERENCE"],
        "proof_roots": ["dueling bandits", "preference matrices", "Condorcet/Borda regret"],
        "lean_leaf_families": ["pairwise action relation", "preference probability", "winner notion"],
        "memory_status": "survey-card",
    },
    {
        "id": "PPR-AAAI-2020-SAFE-LINEAR-STOCHASTIC",
        "title": "Safe Linear Stochastic Bandits",
        "authors": "Kia Khezeli; Eilyan Bitar",
        "source": "https://doi.org/10.1609/aaai.v34i06.6581",
        "scenarios": ["SCN-CONSTRAINTS"],
        "proof_roots": ["safe linear bandits", "constraint confidence", "safe action set"],
        "lean_leaf_families": ["baseline feasibility", "safe-set monotonicity", "constraint regret"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-AAAI-2016-DP-MAB",
        "title": "Algorithms for Differentially Private Multi-Armed Bandits",
        "authors": "Aristide Tossou; Christos Dimitrakakis",
        "source": "https://doi.org/10.1609/aaai.v30i1.10212",
        "scenarios": ["SCN-CONSTRAINTS"],
        "proof_roots": ["differential privacy", "private UCB", "privacy-regret tradeoff"],
        "lean_leaf_families": ["noise distribution contract", "privacy composition", "private confidence radius"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-FAT-2018-MERITOCRATIC-FAIRNESS",
        "title": "Meritocratic Fairness for Infinite and Contextual Bandits",
        "authors": "Matthew Joseph; Michael Kearns; Jamie Morgenstern; Seth Neel; Aaron Roth",
        "source": "https://doi.org/10.1145/3278721.3278764",
        "scenarios": ["SCN-CONSTRAINTS", "SCN-CONTEXTUAL"],
        "proof_roots": ["fair contextual bandits", "meritocratic fairness", "infinite arms"],
        "lean_leaf_families": ["fairness invariant", "action dominance relation", "contextual policy constraint"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-AAAI-2021-FEDERATED-MAB",
        "title": "Federated Multi-Armed Bandits",
        "authors": "Chengshuai Shi; Cong Shen",
        "source": "https://doi.org/10.1609/aaai.v35i11.17156",
        "scenarios": ["SCN-FEDERATED-DISTRIBUTED"],
        "proof_roots": ["federated MAB", "client aggregation", "communication-efficient regret"],
        "lean_leaf_families": ["client-indexed traces", "aggregation invariant", "communication round count"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-FEDERATED-NEURAL-BANDITS-2022",
        "title": "Federated Neural Bandits",
        "authors": "Federated neural bandit authors",
        "source": "https://arxiv.org/abs/2205.14309",
        "scenarios": ["SCN-FEDERATED-DISTRIBUTED", "SCN-LLM-REC-SYS"],
        "proof_roots": ["federated neural bandits", "nonlinear contextual bandits", "distributed representation learning"],
        "lean_leaf_families": ["client embedding contract", "nonlinear confidence surrogate", "federated update trace"],
        "memory_status": "paper-card",
    },
]

BANDIT_SCENARIO_CARDS = [
    {
        "id": "SCN-STOCHASTIC-FINITE",
        "name": "finite stochastic bandits",
        "core_algorithms": ["ETC", "UCB", "MOSS", "KL-UCB", "Thompson sampling"],
        "leaf_families": ["pull-count algebra", "gap decomposition", "sub-Gaussian tails", "Bernoulli KL"],
        "mathlib_needs": ["MLIB-FINSET-SUMS", "MLIB-ORDER-ALGEBRA", "MLIB-PROBABILITY-INDEPENDENCE"],
        "source_cards": [
            "TXT-BUBECK-CESABIANCHI-2012",
            "TXT-LATTIMORE-SZEPESVARI-2020",
            "PPR-AUER-CBF-2002-UCB1",
            "PPR-GARIVIER-CAPPE-2011-KLUCB",
            "PPR-AGRAWAL-GOYAL-2011-TS",
        ],
        "status": "seeded",
    },
    {
        "id": "SCN-BAYESIAN-POSTERIOR",
        "name": "Bayesian and posterior-sampling bandits",
        "core_algorithms": ["Thompson sampling", "Bayes-UCB", "posterior sampling with priors"],
        "leaf_families": ["posterior kernels", "Bayesian regret", "probability matching", "prior/posterior update contracts"],
        "mathlib_needs": ["MLIB-PROBABILITY-KERNEL", "MLIB-CONDITIONAL-EXPECTATION", "MLIB-MEASURE-INTEGRAL"],
        "source_cards": ["TXT-SLIVKINS-2019-2024", "PPR-AGRAWAL-GOYAL-2011-TS"],
        "status": "planned",
    },
    {
        "id": "SCN-ADVERSARIAL-FINITE",
        "name": "adversarial finite-arm bandits",
        "core_algorithms": ["EXP3", "EXP3-IX", "FTRL/OMD variants"],
        "leaf_families": ["importance-weighted estimators", "exponential weights", "potential inequalities"],
        "mathlib_needs": ["MLIB-FINSET-SUMS", "MLIB-EXP-LOG-INEQUALITIES", "MLIB-ORDER-ALGEBRA"],
        "source_cards": ["TXT-BUBECK-CESABIANCHI-2012", "TXT-LATTIMORE-SZEPESVARI-2020", "PPR-AUER-CFS-2002-EXP3"],
        "status": "planned",
    },
    {
        "id": "SCN-BOBW-ADAPTIVE",
        "name": "best-of-both-worlds and adaptive adversarial bandits",
        "core_algorithms": ["Tsallis-INF", "LC-Tsallis-INF", "adaptive-learning-rate FTRL", "self-bounding FTRL"],
        "leaf_families": ["Tsallis entropy regularization", "self-bounding regret conversion", "stability/penalty split", "adaptive learning-rate schedule"],
        "mathlib_needs": ["MLIB-FINSET-SUMS", "MLIB-REAL-RPOW-TSALLIS", "MLIB-CONVEX-LINALG", "MLIB-EXP-LOG-INEQUALITIES"],
        "source_cards": [
            "PPR-ZIMMERT-SELDIN-2018-TSALLIS-INF",
            "PPR-MASOUDIAN-SELDIN-2021-TSALLIS-INF",
            "PPR-KATO-ITO-2024-LC-TSALLIS-INF",
            "PPR-ADAPTIVE-LR-FTRL-2024",
        ],
        "status": "planned",
    },
    {
        "id": "SCN-CONTEXTUAL",
        "name": "contextual bandits",
        "core_algorithms": ["EXP4", "LinUCB", "Thompson contextual variants"],
        "leaf_families": ["policy classes", "expert advice", "context measurability", "regret against policies"],
        "mathlib_needs": ["MLIB-MEASURE-INTEGRAL", "MLIB-PROBABILITY-KERNEL", "MLIB-FINSET-SUMS"],
        "source_cards": ["TXT-LATTIMORE-SZEPESVARI-2020", "PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB", "PPR-FAT-2018-MERITOCRATIC-FAIRNESS"],
        "status": "planned",
    },
    {
        "id": "SCN-LINEAR-GLM",
        "name": "linear and generalized-linear bandits",
        "core_algorithms": ["LinUCB", "OFUL", "linear Thompson sampling", "GLM-UCB"],
        "leaf_families": ["least squares", "self-normalized martingales", "ellipsoid confidence", "determinant algebra"],
        "mathlib_needs": ["MLIB-CONVEX-LINALG", "MLIB-MARTINGALE-STOCHASTIC", "MLIB-REAL-LOG-SQRT"],
        "source_cards": ["TXT-LATTIMORE-SZEPESVARI-2020", "PPR-ABBASI-YADKORI-2011-SELF-NORMALIZED", "PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB"],
        "status": "planned",
    },
    {
        "id": "SCN-LIPSCHITZ-METRIC",
        "name": "Lipschitz, continuum, and metric bandits",
        "core_algorithms": ["zooming", "hierarchical optimistic optimization", "nearest-neighbor UCB"],
        "leaf_families": ["metric balls", "covering numbers", "Lipschitz reward contracts", "near-optimality dimension"],
        "mathlib_needs": ["MLIB-METRIC-TOPOLOGY", "MLIB-FINSET-SUMS", "MLIB-ASYMPTOTICS"],
        "source_cards": ["TXT-SLIVKINS-2019-2024"],
        "status": "planned",
    },
    {
        "id": "SCN-PURE-EXPLORATION",
        "name": "pure exploration and best-arm identification",
        "core_algorithms": ["successive elimination", "LUCB", "Track-and-Stop"],
        "leaf_families": ["stopping rules", "fixed-confidence events", "sample complexity", "change-of-measure"],
        "mathlib_needs": ["MLIB-CONDITIONAL-EXPECTATION", "MLIB-MEASURE-INTEGRAL", "MLIB-ASYMPTOTICS"],
        "source_cards": ["TXT-LATTIMORE-SZEPESVARI-2020", "TXT-SLIVKINS-2019-2024"],
        "status": "planned",
    },
    {
        "id": "SCN-COMBINATORIAL",
        "name": "combinatorial and semi-bandit feedback",
        "core_algorithms": ["Combinatorial UCB", "semi-bandit Thompson", "matroid/knapsack variants"],
        "leaf_families": ["set-valued actions", "component rewards", "oracle contracts", "semi-bandit decomposition"],
        "mathlib_needs": ["MLIB-FINSET-SUMS", "MLIB-CONVEX-LINALG", "MLIB-ORDER-ALGEBRA"],
        "source_cards": ["TXT-LATTIMORE-SZEPESVARI-2020"],
        "status": "planned",
    },
    {
        "id": "SCN-RESOURCE-CONSTRAINED",
        "name": "resource-constrained bandits and bandits with knapsacks",
        "core_algorithms": ["BwK", "primal-dual UCB", "budgeted Thompson sampling"],
        "leaf_families": ["resource-consumption traces", "budget stopping times", "primal-dual comparison", "constraint regret"],
        "mathlib_needs": ["MLIB-FINSET-SUMS", "MLIB-ORDER-ALGEBRA", "MLIB-MEASURE-INTEGRAL"],
        "source_cards": ["TXT-SLIVKINS-2019-2024", "PPR-BADANIDIYURU-KLEINBERG-SLIVKINS-2013-BWK"],
        "status": "planned",
    },
    {
        "id": "SCN-DUELING-PREFERENCE",
        "name": "dueling, preference, and ranking bandits",
        "core_algorithms": ["RUCB variants", "Borda/Condorcet algorithms", "preference-based elimination"],
        "leaf_families": ["pairwise preference matrices", "winner notions", "comparison regret", "partial-monitoring bridge"],
        "mathlib_needs": ["MLIB-FINSET-SUMS", "MLIB-ORDER-ALGEBRA", "MLIB-PROBABILITY-INDEPENDENCE"],
        "source_cards": ["PPR-IJCAI-2018-DUELING-SURVEY"],
        "status": "planned",
    },
    {
        "id": "SCN-NONSTATIONARY",
        "name": "nonstationary, rotting, and drifting bandits",
        "core_algorithms": ["sliding-window UCB", "discounted UCB", "change-point UCB"],
        "leaf_families": ["dynamic regret", "variation budgets", "windowed concentration", "change detection"],
        "mathlib_needs": ["MLIB-FINSET-SUMS", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-ASYMPTOTICS"],
        "source_cards": ["TXT-SLIVKINS-2019-2024"],
        "status": "planned",
    },
    {
        "id": "SCN-HEAVY-TAILED-ROBUST",
        "name": "heavy-tailed, corrupted, and robust bandits",
        "core_algorithms": ["median-of-means UCB", "trimmed-mean UCB", "corruption-robust contextual bandits"],
        "leaf_families": ["robust mean estimator", "moment assumptions", "truncation event", "corruption budget"],
        "mathlib_needs": ["MLIB-MEASURE-INTEGRAL", "MLIB-ORDER-ALGEBRA", "MLIB-ASYMPTOTICS"],
        "source_cards": ["TXT-LATTIMORE-SZEPESVARI-2020"],
        "status": "watchlist",
    },
    {
        "id": "SCN-DELAYED-BATCHED",
        "name": "delayed-feedback, batched, and asynchronous bandits",
        "core_algorithms": ["delayed EXP3", "batched UCB", "asynchronous Thompson sampling"],
        "leaf_families": ["delay queues", "pending feedback", "batch regret", "asynchronous filtration"],
        "mathlib_needs": ["MLIB-FINSET-SUMS", "MLIB-MARTINGALE-STOCHASTIC", "MLIB-CONDITIONAL-EXPECTATION"],
        "source_cards": ["TXT-BUBECK-CESABIANCHI-2012"],
        "status": "planned",
    },
    {
        "id": "SCN-CONSTRAINTS",
        "name": "safe, conservative, fair, private, and constrained bandits",
        "core_algorithms": ["conservative UCB", "safe-UCB", "fair contextual bandits", "private UCB"],
        "leaf_families": ["baseline regret", "constraint budgets", "privacy noise", "fairness invariants"],
        "mathlib_needs": ["MLIB-MEASURE-INTEGRAL", "MLIB-ORDER-ALGEBRA", "MLIB-PROBABILITY-INDEPENDENCE"],
        "source_cards": [
            "PPR-AAAI-2020-SAFE-LINEAR-STOCHASTIC",
            "PPR-AAAI-2016-DP-MAB",
            "PPR-FAT-2018-MERITOCRATIC-FAIRNESS",
        ],
        "status": "planned",
    },
    {
        "id": "SCN-FEDERATED-DISTRIBUTED",
        "name": "federated and distributed bandits",
        "core_algorithms": ["Fed-UCB", "personalized federated bandits", "Byzantine-robust UCB"],
        "leaf_families": ["client aggregation", "heterogeneity", "communication rounds", "robust mean estimates"],
        "mathlib_needs": ["MLIB-FINSET-SUMS", "MLIB-MEASURE-INTEGRAL", "MLIB-PROBABILITY-INDEPENDENCE"],
        "source_cards": ["PPR-AAAI-2021-FEDERATED-MAB", "PPR-FEDERATED-NEURAL-BANDITS-2022"],
        "status": "planned",
    },
    {
        "id": "SCN-RL-MDP",
        "name": "finite-horizon RL and MDP regret",
        "core_algorithms": ["UCB-VI", "posterior sampling RL", "optimism under uncertainty", "Bellman backups"],
        "leaf_families": ["finite kernels", "policies", "Bellman recursion", "occupancy measures", "episode regret"],
        "mathlib_needs": ["MLIB-PROBABILITY-KERNEL", "MLIB-CONDITIONAL-EXPECTATION", "MLIB-MEASURE-INTEGRAL"],
        "source_cards": ["TXT-SLIVKINS-2019-2024", "PPR-AZAR-OSBAND-MUNOS-2017-UCBVI"],
        "status": "planned",
    },
    {
        "id": "SCN-LLM-REC-SYS",
        "name": "LLM, recommender, and neural bandits",
        "core_algorithms": ["neural contextual bandits", "bandit prompt optimization", "LLM-assisted priors"],
        "leaf_families": ["offline-to-online priors", "context embeddings", "model-selection regret", "adaptive response generation"],
        "mathlib_needs": ["MLIB-MEASURE-INTEGRAL", "MLIB-PROBABILITY-KERNEL", "MLIB-CONVEX-LINALG"],
        "source_cards": ["PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB", "PPR-FEDERATED-NEURAL-BANDITS-2022"],
        "status": "watchlist",
    },
]

PROOF_WEAPON_CARDS = [
    {
        "id": "WEAPON-UCB-OPTIMISM",
        "name": "optimism under uncertainty",
        "kind": "proof-inspiration",
        "upper_planning_use": "Generate candidate routes for index-based stochastic bandit and finite-horizon RL regret proofs.",
        "lower_agent_rule": "Do not cite optimism as a theorem; instantiate local index definitions, confidence events, and compiled pull-count/regret leaves.",
        "source_cards": ["PPR-AUER-CBF-2002-UCB1", "PPR-AZAR-OSBAND-MUNOS-2017-UCBVI", "TXT-LATTIMORE-SZEPESVARI-2020"],
        "direct_reuse_cards": ["LML-UCB-REGRET", "MLIB-REAL-LOG-SQRT", "MLIB-PROBABILITY-SUBGAUSSIAN", "LOCAL-LEAF-FINITE-BOOKKEEPING"],
        "blocked_leaves": ["confidence event API", "positive pull count before index use", "tail summability"],
    },
    {
        "id": "WEAPON-TAIL-INEQUALITIES",
        "name": "sub-Gaussian, Hoeffding, Chernoff, and variance tails",
        "kind": "proof-inspiration",
        "upper_planning_use": "Select the weakest tail route matching reward assumptions: bounded, sub-Gaussian, conditional sub-Gaussian, or finite-variance.",
        "lower_agent_rule": "Use Mathlib/LML declarations or task-local cited results; do not reprove a tail inequality inside an algorithm file.",
        "source_cards": ["TXT-LATTIMORE-SZEPESVARI-2020", "TXT-BUBECK-CESABIANCHI-2012"],
        "direct_reuse_cards": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-PROBABILITY-MGF", "MLIB-PROBABILITY-VARIANCE", "MLIB-PROBABILITY-INDEPENDENCE"],
        "blocked_leaves": ["measurability/integrability contract", "independence or filtration contract", "tail-event union bound"],
    },
    {
        "id": "WEAPON-TSALLIS-INF-FTRL",
        "name": "Tsallis entropy FTRL and best-of-both-worlds bandits",
        "kind": "proof-inspiration",
        "upper_planning_use": "Propose routes for stochastic/adversarial interpolation, self-bounding regret, and adaptive learning-rate FTRL tasks.",
        "lower_agent_rule": "Do not treat the weapon as a reusable theorem; first formalize Tsallis regularizer, simplex constraints, FTRL optimality, and stability/penalty leaves.",
        "source_cards": [
            "PPR-ZIMMERT-SELDIN-2018-TSALLIS-INF",
            "PPR-MASOUDIAN-SELDIN-2021-TSALLIS-INF",
            "PPR-KATO-ITO-2024-LC-TSALLIS-INF",
            "PPR-ADAPTIVE-LR-FTRL-2024",
        ],
        "direct_reuse_cards": ["MLIB-REAL-RPOW-TSALLIS", "MLIB-CONVEX-LINALG", "MLIB-FINSET-SUMS", "MLIB-EXP-LOG-INEQUALITIES"],
        "blocked_leaves": ["simplex probability vector API", "Tsallis entropy algebra", "FTRL one-step optimality", "stability/penalty decomposition"],
    },
    {
        "id": "WEAPON-EXP3-POTENTIAL",
        "name": "exponential weights potential",
        "kind": "proof-inspiration",
        "upper_planning_use": "Plan adversarial finite-arm regret proofs using importance-weighted losses and potential telescoping.",
        "lower_agent_rule": "Use exact exponential/log inequalities from Mathlib and expose estimator unbiasedness as separate leaves.",
        "source_cards": ["PPR-AUER-CFS-2002-EXP3", "TXT-BUBECK-CESABIANCHI-2012"],
        "direct_reuse_cards": ["MLIB-EXP-LOG-INEQUALITIES", "MLIB-FINSET-SUMS", "MLIB-MEASURE-INTEGRAL"],
        "blocked_leaves": ["importance-weighted estimator API", "potential telescope", "learning-rate algebra"],
    },
    {
        "id": "WEAPON-SELF-NORMALIZED-OFUL",
        "name": "self-normalized concentration for OFUL/LinUCB",
        "kind": "proof-inspiration",
        "upper_planning_use": "Route linear/GLM bandit proofs through Gram matrix monotonicity, confidence ellipsoids, and elliptical potential.",
        "lower_agent_rule": "Separate linear algebra leaves from stochastic-process leaves; do not hide determinant or norm side conditions.",
        "source_cards": ["PPR-ABBASI-YADKORI-2011-SELF-NORMALIZED", "PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB"],
        "direct_reuse_cards": ["MLIB-CONVEX-LINALG", "MLIB-MARTINGALE-STOCHASTIC", "MLIB-REAL-LOG-SQRT"],
        "blocked_leaves": ["Gram matrix API", "elliptical potential", "martingale self-normalized tail"],
    },
    {
        "id": "WEAPON-POSTERIOR-SAMPLING",
        "name": "posterior sampling and probability matching",
        "kind": "proof-inspiration",
        "upper_planning_use": "Plan Thompson-sampling and Bayesian regret proofs around posterior action identities and Bayes-risk decompositions.",
        "lower_agent_rule": "Use LML posterior theorem cards when available; otherwise formalize kernels and conditional distributions before regret algebra.",
        "source_cards": ["PPR-AGRAWAL-GOYAL-2011-TS", "TXT-SLIVKINS-2019-2024"],
        "direct_reuse_cards": ["LML-TS-POSTERIOR-ACTION", "LML-TS-BAYES-REGRET", "MLIB-PROBABILITY-KERNEL", "MLIB-CONDITIONAL-EXPECTATION"],
        "blocked_leaves": ["posterior kernel", "conditional distribution identity", "Bayesian regret integrability"],
    },
    {
        "id": "WEAPON-KL-CHANGE-OF-MEASURE",
        "name": "KL change-of-measure and information lower bounds",
        "kind": "proof-inspiration",
        "upper_planning_use": "Generate lower-bound and KL-UCB confidence-inversion routes for Bernoulli or bounded reward models.",
        "lower_agent_rule": "Record KL definitions, convexity, and absolute-continuity assumptions explicitly before any theorem reuse.",
        "source_cards": ["PPR-GARIVIER-CAPPE-2011-KLUCB", "TXT-LATTIMORE-SZEPESVARI-2020"],
        "direct_reuse_cards": ["MLIB-EXP-LOG-INEQUALITIES", "MLIB-MEASURE-INTEGRAL", "MLIB-ORDER-ALGEBRA"],
        "blocked_leaves": ["Bernoulli KL API", "change-of-measure lemma", "confidence-set inversion"],
    },
    {
        "id": "WEAPON-PRIMAL-DUAL-BWK",
        "name": "primal-dual resource accounting for bandits with knapsacks",
        "kind": "proof-inspiration",
        "upper_planning_use": "Plan resource-constrained bandit proofs through budget traces, stopping times, and Lagrangian comparisons.",
        "lower_agent_rule": "Expose budget feasibility and stopping-time assumptions as reusable contracts before final regret proof work.",
        "source_cards": ["PPR-BADANIDIYURU-KLEINBERG-SLIVKINS-2013-BWK", "TXT-SLIVKINS-2019-2024"],
        "direct_reuse_cards": ["MLIB-FINSET-SUMS", "MLIB-ORDER-ALGEBRA", "MLIB-MEASURE-INTEGRAL"],
        "blocked_leaves": ["resource consumption trace", "budget stopping time", "dual feasibility"],
    },
]

LOCAL_LEAF_CARDS = [
    {
        "id": "LOCAL-LEAF-FINITE-BOOKKEEPING",
        "module": "BanditRLProof.LeafLemmas",
        "status": "leanCompiled",
        "declarations": [
            "pullCount_one",
            "pullCount_succ_of_eq",
            "pullCount_succ_of_ne",
            "pullCount_le_succ",
            "pullCount_succ_le_succ",
            "pullCount_mono",
            "pullCount_le_time",
            "pullCount_add_le",
            "pullCount_le_add",
            "pullCount_eq_zero_of_forall_ne",
            "pullCount_eq_time_of_forall_eq",
            "pullCount_pos_of_eq_before",
            "pullCount_const_self",
            "pullCount_const_of_ne",
            "pullCount_add_eq_of_forall_ne_between",
            "pullCount_add_eq_add_of_forall_eq_between",
            "sumRewards_succ_of_eq",
            "sumRewards_succ_of_ne",
            "sumRewards_eq_zero_of_forall_ne",
            "sumRewards_const_of_ne",
            "sumRewards_add_eq_of_forall_ne_between",
            "FiniteBanditModel.bestMean_eq_mean_bestArm",
            "FiniteBanditModel.gap_of_ne_bestArm",
            "pseudoRegret_one",
            "pseudoRegret_succ_of_bestArm",
            "pseudoRegret_succ_of_gap_zero",
            "pseudoRegret_eq_zero_of_forall_bestArm",
            "pseudoRegret_eq_zero_of_forall_gap_zero",
            "pseudoRegret_const_bestArm",
            "pseudoRegret_const_of_gap_zero",
            "pseudoRegret_add_eq_of_forall_bestArm_between",
            "pseudoRegret_add_eq_of_forall_gap_zero_between",
        ],
        "role": "Compiled dependency-light bridge leaves for pull counts, segment counts, reward sums, gaps, and pseudo-regret.",
        "mathlib_routes": ["MLIB-FINSET-SUMS", "MLIB-FINTYPE-FIN", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-ALGORITHM-WRAPPERS",
        "module": "BanditRLProof.Algorithms.ETC; BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "ETC.exploreArm_eq_of_mod_eq",
            "UCB.score_eq_empiricalMean",
        ],
        "role": "Compiled dependency-light wrapper leaves for current ETC and UCB surfaces.",
        "mathlib_routes": ["MLIB-FINTYPE-FIN", "MLIB-ORDER-ALGEBRA"],
    },
]


def now_iso() -> str:
    return _dt.datetime.now(_dt.timezone.utc).replace(microsecond=0).isoformat()


def stamp() -> str:
    return _dt.datetime.now().strftime("%Y%m%d-%H%M%S")


def rel(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    print(f"wrote {rel(path)}")


def write_new(path: Path, text: str) -> None:
    if path.exists():
        raise SystemExit(f"refusing to overwrite existing file: {rel(path)}")
    write_text(path, text)


def write_if_missing(path: Path, text: str) -> bool:
    if path.exists():
        return False
    write_text(path, text)
    return True


def append_line(path: Path, line: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(line + "\n")


def append_jsonl(path: Path, record: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(record, sort_keys=True, ensure_ascii=False) + "\n")


def load_jsonl(path: Path) -> list[dict]:
    if not path.exists():
        return []
    rows: list[dict] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        rows.append(json.loads(line))
    return rows


def compact_lean_statement(lines: list[str], start_index: int, max_lines: int = 8) -> str:
    """Return a compact declaration header for search/display."""
    parts: list[str] = []
    for raw in lines[start_index:start_index + max_lines]:
        stripped = raw.strip()
        if not stripped:
            continue
        parts.append(re.sub(r"\s+", " ", stripped))
        if ":=" in stripped or stripped == "where" or stripped.endswith(" where"):
            break
    statement = " ".join(parts)
    if " := " in statement:
        statement = statement.split(" := ", 1)[0]
    return statement[:700]


def scan_lean_declarations(include_tests: bool = False) -> list[dict[str, str | int]]:
    """Create a compact local declaration index from Lean source files."""
    roots = [ROOT / "BanditRLProof"]
    if include_tests:
        roots.append(ROOT / "Tests")
    decls: list[dict[str, str | int]] = []
    decl_re = re.compile(
        r"^\s*(?:@\[[^\]]+\]\s*)*(?:noncomputable\s+)?(?:partial\s+)?"
        r"(abbrev|def|theorem|structure|inductive)\s+([A-Za-z0-9_'.]+)"
    )
    namespace_re = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.]+)")
    end_re = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_.]+))?\s*$")
    for root in roots:
        if not root.exists():
            continue
        for path in sorted(root.rglob("*.lean")):
            namespace_stack: list[str] = []
            lines = path.read_text(encoding="utf-8").splitlines()
            for lineno, line in enumerate(lines, start=1):
                ns_match = namespace_re.match(line)
                if ns_match:
                    namespace_stack.extend(ns_match.group(1).split("."))
                    continue
                end_match = end_re.match(line)
                if end_match:
                    name = end_match.group(1)
                    if name and namespace_stack:
                        parts = name.split(".")
                        if namespace_stack[-len(parts):] == parts:
                            del namespace_stack[-len(parts):]
                    elif not name and namespace_stack:
                        namespace_stack.pop()
                    continue
                decl_match = decl_re.match(line)
                if not decl_match:
                    continue
                kind, name = decl_match.groups()
                full_name = name if "." in name else ".".join(namespace_stack + [name])
                decls.append({
                    "kind": kind,
                    "name": name,
                    "full_name": full_name,
                    "file": rel(path),
                    "line": lineno,
                    "statement": compact_lean_statement(lines, lineno - 1),
                })
    return decls


def run(cmd: list[str]) -> int:
    print("$ " + " ".join(shlex.quote(part) for part in cmd))
    return subprocess.run(cmd, cwd=ROOT).returncode


def run_capture(cmd: list[str]) -> tuple[int, str]:
    completed = subprocess.run(
        cmd,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    return completed.returncode, completed.stdout


def task_file(task_id: str) -> Path:
    return ROOT / "tasks" / f"{task_id}.md"


def task_exists(task_id: str) -> bool:
    return task_file(task_id).exists()


def add_manifest(command: str, path: Path, kind: str, note: str) -> None:
    if not MANIFEST.exists():
        write_text(MANIFEST, "# Manifest\n\nAppend-only artifact ledger.\n")
    append_line(MANIFEST, f"- `{now_iso()}` `{command}` `{kind}` `{rel(path)}` - {note}")


def latest_run_dir() -> Path | None:
    runs = [p for p in (ROOT / "runs").glob("*") if p.is_dir()]
    if not runs:
        return None
    return sorted(runs, key=lambda p: p.name)[-1]


def resolve_run_id(value: str) -> Path:
    if value in {"", "latest"}:
        found = latest_run_dir()
        if found is None:
            raise SystemExit("no run directories exist")
        return found
    path = ROOT / "runs" / value
    if not path.exists():
        raise SystemExit(f"run directory not found: {rel(path)}")
    return path


def read_optional(path: Path, limit: int = 8000) -> str:
    if not path.exists():
        return ""
    text = path.read_text(encoding="utf-8")
    return text[-limit:]


def prompt_header(task_id: str, cycle: int, role: str) -> str:
    return f"""# ABRL Harness Prompt

Task id: `{task_id}`
Cycle: `{cycle}`
Role: `{role}`
Harness: `hierarchical`

Acceptance rule: a mathematical result is accepted only after the relevant Lean
declaration compiles under `lake build && lake build Tests`, or after the
obligation is explicitly recorded as blocked with a cited result and next leaf.

Mathlib-ready leaf rule:

- Decompose aggressively.  A lower Lean target should be a small lemma that
  fits in one agent context window.
- Specify more than the theorem.  Record local APIs, imports, statement shape,
  and intended proof route before tactic work.
- Treat persistent failure as mathematical signal.  Recheck the statement,
  missing assumptions, and possible counterexamples before continuing.
- Promote hidden regularity to reusable contracts: integrability, continuity,
  nonemptiness, measurability, boundedness, and finiteness are named lemmas or
  cited obligations.
- Do not frequently change proof strategy.  Repair the current route unless
  reviewer/middle records a reason to pivot.
- Design leaf lemmas as future Mathlib contributions whenever they are general
  enough; ABRL-specific wrappers should be thin.
- Before creating a new general lemma, search `python3 tools/bandit.py
  search-memory <term>`, `python3 tools/bandit.py list-lean-decls <term>`,
  and the Mathlib retrieval cards for existing APIs.

"""


def task_template(task_id: str, kind: str, title: str, target_lean: str) -> str:
    return f"""# {title}

Task id: `{task_id}`
Kind: `{kind}`
Status: `planned`
Harness: `hierarchical`

## Goal

State the bandit/RL theorem, definition, or literature-port target.

## Source

- Paper or repository:
- Theorem/lemma/section:
- Existing Lean declaration:
- Textbook/source card:
- Scenario card:

## Lean Target

```lean
-- target declaration names here
```

Target file: `{target_lean}`

## Proof Obligations

- [ ] Natural-language statement is mapped to Lean symbols.
- [ ] Required model assumptions are explicit.
- [ ] Probability, measurability, concentration, and stopping-time contracts are recorded.
- [ ] Reusable theorem cards are identified before proof search.
- [ ] Each active leaf has local APIs, intended proof route, and regularity contracts.
- [ ] General leaves are classified as `mathlib-candidate`, `project-local`, or `theorem-card-only`.
- [ ] `lake build && lake build Tests` passes.

## Mathlib-Ready Leaf Contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| root | TBD | TBD | TBD | project-local |

## Retrieval Cards

- LML cards:
- Mathlib cards:
- Textbook cards:
- Scenario cards:

## Trial Logging

```bash
python3 tools/bandit.py trial-log --task {task_id} --role lower --kind attempt --status running --notes "..."
python3 tools/bandit.py trial-summary
```
"""


def conversion_window_template(task_id: str, title: str) -> str:
    return f"""# Conversion Window: {title}

Task id: `{task_id}`

Source card:
Scenario card:

## Natural-Language Statement

Write the theorem, proof fragment, or paper equation in precise prose.

## Lean Mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| `A_t` | action at time `t` | | action process | unmapped |

## Assumption Ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| finite action set | typed | task packet | no |
| sub-Gaussian rewards | obligation | cited result | yes |

## Local API And Proof Route

| Leaf | Existing APIs/imports | Mathlib/LML cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| root | TBD | TBD | theorem-card route plus local wrappers | pivot only after reviewer records a mathematical reason |

## Proof-DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Human proof map | Retrieval cards | Regularity contracts | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| root | target theorem | TBD | upper | | this file | TBD | TBD | project-local | `lake build && lake build Tests` | planned |

## Gaps

- [ ] Missing definition:
- [ ] Missing lemma:
- [ ] Missing regularity contract:
- [ ] Mathlib candidate to upstream:
- [ ] Missing cited-result entry:
"""


def proof_obligations_template(task_id: str, title: str) -> str:
    return f"""# Proof Obligations: {title}

Task id: `{task_id}`

Source card:
Scenario card:

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `{task_id}-ROOT` | root theorem or definition | conversion window | TBD | TBD | TBD | TBD | project-local | upper | TBD | `lake build && lake build Tests` | planned |

## Failure Classification

Use exactly one:

- source translation gap;
- local Lean lemma gap;
- theorem-card dependency;
- external cited result;
- semantic interface gap;
- missing regularity contract;
- likely false statement or counterexample;
- invalid route;
- stale dynamic leaf;
- connected blocker.

## Reviewer Notes

- Keep failed attempts in `proof-attempts/{task_id}/`.
- Do not promote simulator checks, prose sketches, or theorem cards to certified memory.
- If an LML theorem is used, cite the upstream declaration and record whether it is imported, ported, or only a theorem card.
- Do not frequently change proof strategy; record the mathematical reason before pivoting.
- Mark general leaf lemmas as Mathlib candidates when they should become reusable upstream infrastructure.
"""


def make_prompt_deck(run_dir: Path, task_id: str, cycle: int, lower_count: int) -> list[Path]:
    task_text = read_optional(task_file(task_id), 12000)
    conversion_text = read_optional(ROOT / "conversion-windows" / f"{task_id}.md", 12000)
    obligations_text = read_optional(ROOT / "proof-obligations" / f"{task_id}.md", 12000)
    memory_text = read_optional(RETRIEVAL_INDEX_DIR / f"{task_id}.json", 12000)
    completion_text = read_optional(ROOT / "docs" / "completion_gap_audit.md", 14000)
    adaptive_text = read_optional(ROOT / "docs" / "adaptive_harness_design.md", 14000)
    foundation_leaf_text = read_optional(ROOT / "research-wiki" / "theory-tree" / "mathlib-foundation-leaf-map.md", 16000)
    mathlib_text = read_optional(RETRIEVAL_INDEX_DIR / "mathlib_bandit_cards.json", 10000)
    textbook_text = read_optional(RETRIEVAL_INDEX_DIR / "bandit_textbook_cards.json", 8000)
    paper_text = read_optional(RETRIEVAL_INDEX_DIR / "bandit_paper_cards.json", 10000)
    scenario_text = read_optional(RETRIEVAL_INDEX_DIR / "bandit_scenario_cards.json", 10000)
    weapon_text = read_optional(RETRIEVAL_INDEX_DIR / "proof_weapon_cards.json", 10000)
    local_leaf_text = read_optional(RETRIEVAL_INDEX_DIR / "local_leaf_cards.json", 6000)
    local_decl_text = read_optional(RETRIEVAL_INDEX_DIR / "local_lean_declarations.json", 10000)
    context = f"""# Context

Task file exists: `{task_exists(task_id)}`
Lean gate: `lake build && lake build Tests`

## Task

{task_text or "_No task file found._"}

## Conversion Window

{conversion_text or "_No conversion window found._"}

## Proof Obligations

{obligations_text or "_No proof obligation ledger found._"}

## Completion Gap Audit

{completion_text or "_No completion gap audit found._"}

## Adaptive Harness Design

{adaptive_text or "_No adaptive harness design found._"}

## Mathlib Foundation Leaf Map

{foundation_leaf_text or "_No foundation leaf map found._"}

## Retrieval Memory

```json
{memory_text or "{}"}
```

## Mathlib Retrieval Cards

```json
{mathlib_text or "{}"}
```

## Bandit Textbook Cards

```json
{textbook_text or "{}"}
```

## Bandit Paper Cards

```json
{paper_text or "{}"}
```

## Bandit Scenario Cards

```json
{scenario_text or "{}"}
```

## Proof Weapon Cards

These cards are upper-layer route inspiration only.  They are not Lean proof
certificates.

```json
{weapon_text or "{}"}
```

## Local Compiled Leaf Cards

```json
{local_leaf_text or "{}"}
```

## Local Lean Declaration Index

```json
{local_decl_text or "{}"}
```
"""
    write_text(run_dir / "00_context.md", context)
    write_text(run_dir / "dialogue.md", f"# Dialogue\n\nRun: `{run_dir.name}`\nTask: `{task_id}`\n")
    write_text(run_dir / "todo.md", "- [ ] Upper selects proof frontier.\n- [ ] Middle updates conversion window and memory.\n- [ ] Lower attempts one leaf.\n- [ ] Reviewer runs gate and records status.\n")

    prompts: list[Path] = []
    upper = prompt_header(task_id, cycle, "upper") + """You are the theorem director.

Produce:
1. the exact theorem frontier for this cycle;
2. the theorem cards or cited results that may be used;
3. one or two active proof-DAG leaves with local APIs, intended route,
   regularity contracts, and Mathlib status;
4. any rejected routes or persistent-failure signals that must be written to
   memory.

Use proof weapons only as route inspiration.  Ground the selected route in
Mathlib/LML/local declarations or explicit proof obligations before assigning
lower work.

Do not ask lower agents to prove a theorem whose assumptions or source mapping
are not in the conversion window.
"""
    write_text(run_dir / "10_upper_director.md", upper)
    prompts.append(run_dir / "10_upper_director.md")

    middle = prompt_header(task_id, cycle, "middle") + """You are the formalization and memory manager.

Synchronize task, conversion window, proof obligations, theorem-card memory,
and Lean declarations.  Produce lower-agent packets with exact file scope,
target declaration, dependencies, local APIs/imports, intended proof route,
regularity contracts, Mathlib status, and gate.

For each new leaf, decide whether the next worker should be Lean-direct,
retrieval-first, or natural-language-prover-assisted.  Natural-language proof
is useful only when it sharpens the Lean statement, assumptions, or route.
"""
    write_text(run_dir / "20_middle_formalizer.md", middle)
    prompts.append(run_dir / "20_middle_formalizer.md")

    for i in range(1, lower_count + 1):
        lower_kind = ["proof architect", "Lean worker", "retrieval/search worker"][(i - 1) % 3]
        body = prompt_header(task_id, cycle, f"lower-{i}") + f"""You are a lower {lower_kind}.

Work on exactly one assigned leaf.  If the leaf is under-specified, write the
missing assumption or source mapping into the appropriate memory file instead
of changing the theorem.  Do not frequently change the proof route; persistent
failure is a signal to audit the statement or hypotheses.  If you edit Lean,
run `lake build && lake build Tests`.  General measure, probability, order,
finite-sum, concentration, or convexity leaves should be written as
Mathlib-ready lemmas unless they are truly ABRL-specific wrappers.
"""
        path = run_dir / f"3{i}_lower_{i}.md"
        write_text(path, body)
        prompts.append(path)

    reviewer = prompt_header(task_id, cycle, "reviewer") + """You are the reviewer/build gate.

Check target fidelity, hidden assumptions, stale leaves, and Lean status.  Run
or request `python3 tools/bandit.py check`.  Record whether new work is:
compiled, blocked, rejected, stale, or only theorem-card memory.
Verify that Mathlib-candidate leaves are small, general, and recorded in
`research-wiki/mathlib-candidates/` when appropriate.
"""
    write_text(run_dir / "40_reviewer.md", reviewer)
    prompts.append(run_dir / "40_reviewer.md")

    write_text(run_dir / "90_handoff.md", "# Handoff\n\nPending cycle closeout.\n")
    return prompts


def format_agent_command(template: str, prompt: Path, run_dir: Path, task_id: str, cycle: int) -> str:
    return template.format(
        root=shlex.quote(str(ROOT)),
        prompt=shlex.quote(str(prompt)),
        run=shlex.quote(str(run_dir)),
        task=shlex.quote(task_id),
        cycle=str(cycle),
    )


def execute_prompt(template: str, prompt: Path, run_dir: Path, task_id: str, cycle: int) -> int:
    command = format_agent_command(template, prompt, run_dir, task_id, cycle)
    print("$ " + command)
    start = time.perf_counter()
    completed = subprocess.run(command, shell=True, cwd=ROOT)
    elapsed = time.perf_counter() - start
    append_jsonl(TRIAL_LOG, {
        "time": now_iso(),
        "task": task_id,
        "role": "agent",
        "kind": "attempt",
        "status": "compiled" if completed.returncode == 0 else "failed",
        "notes": f"executed {rel(prompt)} in {elapsed:.1f}s",
        "run_id": run_dir.name,
        "prompt": rel(prompt),
        "exit_code": completed.returncode,
    })
    return completed.returncode


def resolve_agent_profile_path(value: str) -> Path:
    path = Path(value)
    if path.exists():
        return path
    named = AGENT_PROFILE_DIR / value
    if named.exists():
        return named
    if not value.endswith(".json"):
        named_json = AGENT_PROFILE_DIR / f"{value}.json"
        if named_json.exists():
            return named_json
    raise SystemExit(f"agent profile not found: {value}")


def load_agent_profile(value: str) -> dict[str, str]:
    if not value:
        return {}
    path = resolve_agent_profile_path(value)
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise SystemExit(f"agent profile must be a JSON object: {rel(path)}")
    profile: dict[str, str] = {}
    for key, command in data.items():
        if not isinstance(key, str) or not isinstance(command, str):
            raise SystemExit(f"agent profile entries must be string keys and values: {rel(path)}")
        profile[key] = command
    return profile


def role_for_prompt(prompt: Path) -> str:
    name = prompt.name
    if name.startswith("10_"):
        return "upper"
    if name.startswith("20_"):
        return "middle"
    if name.startswith("3"):
        return "lower"
    if name.startswith("40_"):
        return "reviewer"
    return "agent"


def command_for_prompt(prompt: Path, fallback: str, profile: dict[str, str]) -> str:
    role = role_for_prompt(prompt)
    if role in profile:
        return profile[role]
    if "default" in profile:
        return profile["default"]
    if fallback:
        return fallback
    raise SystemExit(f"no agent command for {rel(prompt)}; role={role}")


def cmd_init(_args: argparse.Namespace) -> int:
    for name in WORK_DIRS:
        (ROOT / name).mkdir(parents=True, exist_ok=True)
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    write_if_missing(STATE_FILE, json.dumps({"created": now_iso(), "harness": "hierarchical"}, indent=2) + "\n")
    write_if_missing(MANIFEST, "# Manifest\n\nAppend-only artifact ledger.\n")
    for name in WORK_DIRS:
        write_if_missing(ROOT / name / "README.md", f"# {name}\n\nManaged by `tools/bandit.py`.\n")
    write_if_missing(AGENT_PROFILE_DIR / "local-echo.example.json", json.dumps({
        "upper": "sed -n '1,220p' {prompt}",
        "middle": "sed -n '1,220p' {prompt}",
        "lower": "sed -n '1,220p' {prompt}",
        "reviewer": "sed -n '1,220p' {prompt}",
    }, indent=2) + "\n")
    add_manifest("bandit.py init", STATE_FILE, "state", "initialized work directories")
    return 0


def cmd_new_task(args: argparse.Namespace) -> int:
    path = task_file(args.id)
    write_new(path, task_template(args.id, args.kind, args.title, args.target_lean))
    write_if_missing(ROOT / "conversion-windows" / f"{args.id}.md", conversion_window_template(args.id, args.title))
    write_if_missing(ROOT / "proof-obligations" / f"{args.id}.md", proof_obligations_template(args.id, args.title))
    add_manifest("bandit.py new-task", path, "task", args.title)
    return 0


def cmd_conversion_window(args: argparse.Namespace) -> int:
    path = ROOT / "conversion-windows" / f"{args.id}.md"
    write_new(path, conversion_window_template(args.id, args.title))
    add_manifest("bandit.py conversion-window", path, "conversion-window", args.title)
    return 0


def cmd_agent_brief(args: argparse.Namespace) -> int:
    task_text = read_optional(task_file(args.id), 12000)
    text = f"""# Agent Brief: {args.id}

Role: `{args.role}`

## Task Context

{task_text or "_No task file found._"}

## Instructions

- Work within the hierarchical harness.
- Keep theorem cards separate from compiled Lean certificates.
- Log attempts with `python3 tools/bandit.py trial-log`.
"""
    path = ROOT / "agent-briefs" / f"{args.id}-{args.role}.md"
    write_new(path, text)
    add_manifest("bandit.py agent-brief", path, "agent-brief", args.role)
    return 0


def cmd_trial_log(args: argparse.Namespace) -> int:
    if args.role not in AGENT_ROLES:
        raise SystemExit(f"--role must be one of {AGENT_ROLES}")
    if args.kind not in TRIAL_KINDS:
        raise SystemExit(f"--kind must be one of {TRIAL_KINDS}")
    if args.status not in TRIAL_STATUSES:
        raise SystemExit(f"--status must be one of {TRIAL_STATUSES}")
    record = {
        "time": now_iso(),
        "task": args.task,
        "role": args.role,
        "kind": args.kind,
        "status": args.status,
        "notes": args.notes,
        "lean": args.lean,
        "source": args.source,
        "run_id": args.run_id,
    }
    append_jsonl(TRIAL_LOG, record)
    print(json.dumps(record, indent=2, ensure_ascii=False))
    return 0


def cmd_trial_summary(_args: argparse.Namespace) -> int:
    rows = load_jsonl(TRIAL_LOG)
    fields = ["time", "task", "role", "kind", "status", "lean", "source", "run_id", "notes"]
    TRIAL_SUMMARY.parent.mkdir(parents=True, exist_ok=True)
    with TRIAL_SUMMARY.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow({field: row.get(field, "") for field in fields})
    print(f"wrote {rel(TRIAL_SUMMARY)} with {len(rows)} rows")
    return 0


def cmd_agent_note(args: argparse.Namespace) -> int:
    run_dir = resolve_run_id(args.run_id)
    message = args.message
    if args.file:
        message = read_text(Path(args.file))
    if not message:
        raise SystemExit("agent-note requires --message or --file")
    append_line(run_dir / "dialogue.md", f"\n## {args.role} - {now_iso()}\n\n{message}\n")
    print(f"appended note to {rel(run_dir / 'dialogue.md')}")
    return 0


def write_reference_indexes() -> list[Path]:
    paths: list[Path] = []
    path = RETRIEVAL_INDEX_DIR / "lml_bandit_cards.json"
    write_text(path, json.dumps({
        "source": "https://github.com/LeanMachineLearning/LML",
        "seed_commit": LML_SEED_COMMIT,
        "seed_date": LML_SEED_DATE,
        "cards": LML_CARDS,
    }, indent=2) + "\n")
    paths.append(path)
    path = RETRIEVAL_INDEX_DIR / "mathlib_bandit_cards.json"
    write_text(path, json.dumps({
        "source": "https://github.com/leanprover-community/mathlib4",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/",
        "cards": MATHLIB_CARDS,
    }, indent=2) + "\n")
    paths.append(path)
    path = RETRIEVAL_INDEX_DIR / "bandit_textbook_cards.json"
    write_text(path, json.dumps({
        "generated": now_iso(),
        "cards": BANDIT_TEXTBOOK_CARDS,
    }, indent=2) + "\n")
    paths.append(path)
    path = RETRIEVAL_INDEX_DIR / "bandit_paper_cards.json"
    write_text(path, json.dumps({
        "generated": now_iso(),
        "cards": BANDIT_PAPER_CARDS,
    }, indent=2) + "\n")
    paths.append(path)
    path = RETRIEVAL_INDEX_DIR / "bandit_scenario_cards.json"
    write_text(path, json.dumps({
        "generated": now_iso(),
        "cards": BANDIT_SCENARIO_CARDS,
    }, indent=2) + "\n")
    paths.append(path)
    path = RETRIEVAL_INDEX_DIR / "proof_weapon_cards.json"
    write_text(path, json.dumps({
        "generated": now_iso(),
        "cards": PROOF_WEAPON_CARDS,
    }, indent=2) + "\n")
    paths.append(path)
    path = RETRIEVAL_INDEX_DIR / "local_leaf_cards.json"
    write_text(path, json.dumps({
        "generated": now_iso(),
        "cards": LOCAL_LEAF_CARDS,
    }, indent=2) + "\n")
    paths.append(path)
    path = RETRIEVAL_INDEX_DIR / "local_lean_declarations.json"
    write_text(path, json.dumps({
        "generated": now_iso(),
        "declarations": scan_lean_declarations(),
    }, indent=2) + "\n")
    paths.append(path)
    return paths


def cmd_reference_index(_args: argparse.Namespace) -> int:
    paths = write_reference_indexes()
    for path in paths:
        add_manifest("bandit.py reference-index", path, "retrieval-index", f"refreshed {path.name}")
    return 0


def cmd_list_literature(_args: argparse.Namespace) -> int:
    for card in LML_CARDS:
        print(f"lml: {card['id']}: {card['declaration']} ({card['module']})")
    for card in BANDIT_TEXTBOOK_CARDS:
        print(f"textbook: {card['id']}: {card['title']}")
    for card in BANDIT_PAPER_CARDS:
        print(f"paper: {card['id']}: {card['title']}")
    return 0


def cmd_list_papers(_args: argparse.Namespace) -> int:
    for card in BANDIT_PAPER_CARDS:
        scenarios = ", ".join(card["scenarios"])
        print(f"{card['id']}: {card['title']} :: {scenarios}")
    return 0


def cmd_list_mathlib(_args: argparse.Namespace) -> int:
    for card in MATHLIB_CARDS:
        terms = ", ".join(card["query_terms"][:4])
        print(f"{card['id']}: {card['module']} :: {terms}")
    return 0


def cmd_list_scenarios(_args: argparse.Namespace) -> int:
    for card in BANDIT_SCENARIO_CARDS:
        algos = ", ".join(card["core_algorithms"][:4])
        print(f"{card['id']}: {card['name']} [{card['status']}] :: {algos}")
    return 0


def cmd_list_weapons(_args: argparse.Namespace) -> int:
    for card in PROOF_WEAPON_CARDS:
        reuse = ", ".join(card["direct_reuse_cards"][:4])
        print(f"{card['id']}: {card['name']} :: inspiration-only :: {reuse}")
    return 0


def cmd_list_lean_decls(args: argparse.Namespace) -> int:
    decls = scan_lean_declarations(include_tests=args.include_tests)
    query = args.query.lower()
    for decl in decls:
        blob = json.dumps(decl, sort_keys=True).lower()
        if query and query not in blob:
            continue
        print(f"{decl['full_name']} [{decl['kind']}] {decl['file']}:{decl['line']}")
        if args.statement and decl.get("statement"):
            print(f"  {decl['statement']}")
    return 0


def cmd_search_memory(args: argparse.Namespace) -> int:
    haystacks = {
        "lml": LML_CARDS,
        "mathlib": MATHLIB_CARDS,
        "textbook": BANDIT_TEXTBOOK_CARDS,
        "paper": BANDIT_PAPER_CARDS,
        "scenario": BANDIT_SCENARIO_CARDS,
        "weapon": PROOF_WEAPON_CARDS,
        "local": LOCAL_LEAF_CARDS,
        "lean": scan_lean_declarations(),
    }
    needle = args.query.lower()
    hits: list[tuple[str, dict]] = []
    for group, cards in haystacks.items():
        for card in cards:
            blob = json.dumps(card, sort_keys=True).lower()
            if needle in blob:
                hits.append((group, card))
    for group, card in hits:
        if group == "lean":
            print(f"lean: {card['full_name']} [{card['kind']}] {card['file']}:{card['line']}")
            if card.get("statement"):
                print(f"  {card['statement']}")
            continue
        name = card.get("id", "")
        module = card.get("module") or card.get("title") or card.get("name") or card.get("declaration", "")
        print(f"{group}: {name}: {module}")
    if not hits:
        print("no hits")
    return 0


def cmd_blueprint_refresh(args: argparse.Namespace) -> int:
    if not task_exists(args.id):
        raise SystemExit(f"task file not found: {rel(task_file(args.id))}")
    task_text = read_optional(task_file(args.id), 14000)
    conversion_text = read_optional(ROOT / "conversion-windows" / f"{args.id}.md", 14000)
    obligations_text = read_optional(ROOT / "proof-obligations" / f"{args.id}.md", 14000)
    completion_text = read_optional(ROOT / "docs" / "completion_gap_audit.md", 18000)
    adaptive_text = read_optional(ROOT / "docs" / "adaptive_harness_design.md", 18000)
    foundation_leaf_text = read_optional(ROOT / "research-wiki" / "theory-tree" / "mathlib-foundation-leaf-map.md", 22000)
    trials = [row for row in load_jsonl(TRIAL_LOG) if row.get("task") == args.id][-20:]
    text = f"""# Proof Blueprint: {args.id}

Generated: `{now_iso()}`

## Source Task

{task_text}

## Conversion Window Snapshot

{conversion_text or "_No conversion window found._"}

## Obligation Snapshot

{obligations_text or "_No proof obligation ledger found._"}

## Completion Gap Audit

{completion_text or "_No completion gap audit found._"}

## Adaptive Harness Design

{adaptive_text or "_No adaptive harness design found._"}

## Mathlib Foundation Leaf Map

{foundation_leaf_text or "_No foundation leaf map found._"}

## Relevant LML Theorem Cards

```json
{json.dumps(LML_CARDS, indent=2)}
```

## Relevant Mathlib Retrieval Cards

```json
{json.dumps(MATHLIB_CARDS, indent=2)}
```

## Bandit Textbook Cards

```json
{json.dumps(BANDIT_TEXTBOOK_CARDS, indent=2)}
```

## Bandit Paper Cards

```json
{json.dumps(BANDIT_PAPER_CARDS, indent=2)}
```

## Bandit Scenario Cards

```json
{json.dumps(BANDIT_SCENARIO_CARDS, indent=2)}
```

## Proof Weapon Cards

These cards are planning inspiration only.  They do not certify any theorem.

```json
{json.dumps(PROOF_WEAPON_CARDS, indent=2)}
```

## Local Compiled Leaf Cards

```json
{json.dumps(LOCAL_LEAF_CARDS, indent=2)}
```

## Local Lean Declaration Index

```json
{json.dumps(scan_lean_declarations(), indent=2)}
```

## Recent Trials

```json
{json.dumps(trials, indent=2, ensure_ascii=False)}
```

## Reviewer Gate

```bash
python3 tools/bandit.py check
```
"""
    path = BLUEPRINT_DIR / f"{args.id}.md"
    write_text(path, text)
    add_manifest("bandit.py blueprint-refresh", path, "proof-blueprint", args.id)
    return 0


def cmd_memory_refresh(args: argparse.Namespace) -> int:
    trials = [row for row in load_jsonl(TRIAL_LOG) if row.get("task") == args.id][-50:]
    index = {
        "task": args.id,
        "generated": now_iso(),
        "harness": "hierarchical",
        "lml_seed_commit": LML_SEED_COMMIT,
        "lml_seed_date": LML_SEED_DATE,
        "lml_cards": LML_CARDS,
        "mathlib_cards": MATHLIB_CARDS,
        "textbook_cards": BANDIT_TEXTBOOK_CARDS,
        "paper_cards": BANDIT_PAPER_CARDS,
        "scenario_cards": BANDIT_SCENARIO_CARDS,
        "proof_weapon_cards": PROOF_WEAPON_CARDS,
        "local_leaf_cards": LOCAL_LEAF_CARDS,
        "local_lean_declarations": scan_lean_declarations(),
        "recent_trials": trials,
        "open_memory_files": [
            f"research-wiki/lml/{args.id}.md",
            "research-wiki/mathlib/theorem-cards.md",
            "research-wiki/textbooks/bandit-classics.md",
            "research-wiki/papers/bandit-frontier-cards.md",
            "research-wiki/scenarios/bandit-scenario-atlas.md",
            "research-wiki/proof-weapons/bandit-proof-weapons.md",
            "research-wiki/theory-tree/bandit-theory-tree.md",
            "research-wiki/theory-tree/mathlib-foundation-leaf-map.md",
            "research-wiki/mathlib-candidates/",
            "research-wiki/mathlib-candidates/finite-bookkeeping-leaves.md",
            "docs/completion_gap_audit.md",
            "docs/adaptive_harness_design.md",
            "docs/proof_export.md",
            "research-wiki/retrieval-index/local_lean_declarations.json",
            f"proof-attempts/{args.id}/",
            f"proof-obligations/{args.id}.md",
            f"conversion-windows/{args.id}.md",
        ],
    }
    path = RETRIEVAL_INDEX_DIR / f"{args.id}.json"
    write_text(path, json.dumps(index, indent=2, ensure_ascii=False) + "\n")
    if args.run_id:
        run_dir = resolve_run_id(args.run_id)
        digest = f"""# Memory Digest

Task: `{args.id}`
Generated: `{now_iso()}`

Recent trials: `{len(trials)}`
Retrieval index: `{rel(path)}`

Next agents should read the task, conversion window, proof obligations, and
LML/Mathlib/textbook/scenario theorem-card indexes before editing Lean.
"""
        write_text(run_dir / "memory_digest.md", digest)
    add_manifest("bandit.py memory-refresh", path, "retrieval-index", args.id)
    return 0


def cmd_export_proof(args: argparse.Namespace) -> int:
    out_dir = PROBLEM_EXPORT_DIR / args.id
    tex = f"""% Auto-generated proof export skeleton for {args.id}
\\section{{{args.title}}}

\\paragraph{{Status.}}
This note is a synchronized natural-language export for task \\texttt{{{args.id}}}.
Only Lean declarations that pass \\texttt{{lake build \\&\\& lake build Tests}} should be
stated as proved.

\\paragraph{{Lean declarations.}}
Add theorem names here.

\\paragraph{{Proof map.}}
Translate the compiled Lean proof into paper-readable mathematics here.
"""
    md = f"""# Proof Export: {args.title}

Task id: `{args.id}`

Status: synchronized skeleton.

## Lean Declarations

- TBD

## Natural-Language Proof

Write the paper-readable proof after Lean closure.
"""
    write_text(out_dir / "latest.tex", tex)
    write_text(out_dir / "latest.md", md)
    add_manifest("bandit.py export-proof", out_dir / "latest.tex", "proof-export", args.id)
    return 0


def cmd_run_cycle(args: argparse.Namespace) -> int:
    run_dir = ROOT / "runs" / f"{stamp()}-{args.id}-cycle{args.cycle:02d}"
    run_dir.mkdir(parents=True, exist_ok=False)
    prompts = make_prompt_deck(run_dir, args.id, args.cycle, args.lower_count)
    append_jsonl(TRIAL_LOG, {
        "time": now_iso(),
        "task": args.id,
        "role": "upper",
        "kind": "plan",
        "status": "queued",
        "notes": f"created hierarchical prompt deck with {args.lower_count} lower prompts",
        "run_id": run_dir.name,
    })
    if args.execute:
        profile = load_agent_profile(args.agent_profile)
        if not args.agent_cmd and not profile:
            raise SystemExit("--execute requires --agent-cmd or --agent-profile")
        code = 0
        for prompt in prompts:
            command = command_for_prompt(prompt, args.agent_cmd, profile)
            code = execute_prompt(command, prompt, run_dir, args.id, args.cycle)
            if code != 0 and args.stop_on_error:
                break
        return code
    print(f"created run deck: {rel(run_dir)}")
    return 0


def cmd_sleep_run(args: argparse.Namespace) -> int:
    code = 0
    for cycle in range(1, args.cycles + 1):
        ns = argparse.Namespace(
            id=args.id,
            cycle=cycle,
            lower_count=args.lower_count,
            execute=args.execute,
            agent_cmd=args.agent_cmd,
            agent_profile=args.agent_profile,
            stop_on_error=args.stop_on_error,
        )
        code = cmd_run_cycle(ns)
        if code != 0 and args.stop_on_error:
            return code
        if args.check_each_cycle:
            code = cmd_check(argparse.Namespace())
            if code != 0 and args.stop_on_error:
                return code
        cmd_memory_refresh(argparse.Namespace(id=args.id, run_id="latest"))
    return code


def cmd_check(_args: argparse.Namespace) -> int:
    code = run(["lake", "build"])
    if code != 0:
        return code
    code = run(["lake", "build", "Tests"])
    if code != 0:
        return code
    pattern = r"\b(sorry|admit|axiom|postulate)\b"
    if shutil.which("rg"):
        code, out = run_capture(["rg", "-n", pattern, "BanditRLProof", "Tests"])
        if code == 0:
            print(out)
            print("forbidden placeholder scan failed")
            return 1
        if code not in (0, 1):
            print(out)
            return code
    else:
        for root in ["BanditRLProof", "Tests"]:
            for path in (ROOT / root).rglob("*.lean"):
                text = path.read_text(encoding="utf-8")
                if re.search(pattern, text):
                    print(f"forbidden placeholder in {rel(path)}")
                    return 1
    print("check passed")
    return 0


def cmd_next_task(_args: argparse.Namespace) -> int:
    tasks = sorted((ROOT / "tasks").glob("*.md"))
    if not tasks:
        print("no tasks")
        return 0
    for path in tasks:
        text = path.read_text(encoding="utf-8", errors="ignore")
        status = "unknown"
        match = re.search(r"Status:\s*`([^`]+)`", text)
        if match:
            status = match.group(1)
        print(f"{path.stem}: {status} ({rel(path)})")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="ABRL local harness helper")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("init", help="initialize work directories")
    p.set_defaults(func=cmd_init)

    p = sub.add_parser("new-task", help="create task, conversion window, and proof ledger")
    p.add_argument("id")
    p.add_argument("--kind", default="theoremFormalization")
    p.add_argument("--title", required=True)
    p.add_argument("--target-lean", default="BanditRLProof/OpenProblems.lean")
    p.set_defaults(func=cmd_new_task)

    p = sub.add_parser("conversion-window", help="create a conversion window")
    p.add_argument("id")
    p.add_argument("--title", required=True)
    p.set_defaults(func=cmd_conversion_window)

    p = sub.add_parser("agent-brief", help="create an agent brief")
    p.add_argument("id")
    p.add_argument("--role", choices=AGENT_ROLES, default="lower")
    p.set_defaults(func=cmd_agent_brief)

    p = sub.add_parser("trial-log", help="append a trial record")
    p.add_argument("--task", required=True)
    p.add_argument("--role", required=True)
    p.add_argument("--kind", required=True)
    p.add_argument("--status", required=True)
    p.add_argument("--notes", default="")
    p.add_argument("--lean", default="")
    p.add_argument("--source", default="")
    p.add_argument("--run-id", default="")
    p.set_defaults(func=cmd_trial_log)

    p = sub.add_parser("trial-summary", help="rewrite trial summary CSV")
    p.set_defaults(func=cmd_trial_summary)

    p = sub.add_parser("agent-note", help="append a role note to run dialogue")
    p.add_argument("run_id")
    p.add_argument("--role", choices=AGENT_ROLES, default="middle")
    p.add_argument("--message", default="")
    p.add_argument("--file", default="")
    p.set_defaults(func=cmd_agent_note)

    p = sub.add_parser("reference-index", help="refresh LML, Mathlib, textbook, paper, scenario, weapon, and local Lean indexes")
    p.set_defaults(func=cmd_reference_index)

    p = sub.add_parser("list-literature", help="list built-in theorem cards")
    p.set_defaults(func=cmd_list_literature)

    p = sub.add_parser("list-papers", help="list bandit paper and survey cards")
    p.set_defaults(func=cmd_list_papers)

    p = sub.add_parser("list-mathlib", help="list Mathlib retrieval cards")
    p.set_defaults(func=cmd_list_mathlib)

    p = sub.add_parser("list-scenarios", help="list bandit scenario cards")
    p.set_defaults(func=cmd_list_scenarios)

    p = sub.add_parser("list-weapons", help="list proof weapon inspiration cards")
    p.set_defaults(func=cmd_list_weapons)

    p = sub.add_parser("list-lean-decls", help="list local Lean declarations")
    p.add_argument("query", nargs="?", default="")
    p.add_argument("--include-tests", action="store_true")
    p.add_argument("--statement", action="store_true", help="print compact declaration statements")
    p.set_defaults(func=cmd_list_lean_decls)

    p = sub.add_parser("search-memory", help="search theorem, Mathlib, textbook, paper, scenario, weapon, local leaf, and Lean declaration cards")
    p.add_argument("query")
    p.set_defaults(func=cmd_search_memory)

    p = sub.add_parser("blueprint-refresh", help="refresh proof blueprint snapshot")
    p.add_argument("id")
    p.set_defaults(func=cmd_blueprint_refresh)

    p = sub.add_parser("memory-refresh", help="refresh retrieval memory")
    p.add_argument("id")
    p.add_argument("--run-id", default="")
    p.set_defaults(func=cmd_memory_refresh)

    p = sub.add_parser("export-proof", help="create Markdown and LaTeX proof export skeletons")
    p.add_argument("id")
    p.add_argument("--title", required=True)
    p.set_defaults(func=cmd_export_proof)

    p = sub.add_parser("run-cycle", help="create or execute one hierarchical prompt deck")
    p.add_argument("id")
    p.add_argument("--cycle", type=int, default=1)
    p.add_argument("--lower-count", type=int, default=3)
    p.add_argument("--execute", action="store_true")
    p.add_argument("--agent-cmd", default="")
    p.add_argument("--agent-profile", default="")
    p.add_argument("--stop-on-error", action="store_true")
    p.set_defaults(func=cmd_run_cycle)

    p = sub.add_parser("sleep-run", help="create or execute repeated hierarchical cycles")
    p.add_argument("id")
    p.add_argument("--cycles", type=int, default=1)
    p.add_argument("--lower-count", type=int, default=3)
    p.add_argument("--execute", action="store_true")
    p.add_argument("--agent-cmd", default="")
    p.add_argument("--agent-profile", default="")
    p.add_argument("--check-each-cycle", action="store_true")
    p.add_argument("--stop-on-error", action="store_true")
    p.set_defaults(func=cmd_sleep_run)

    p = sub.add_parser("check", help="run Lean build gate and placeholder scan")
    p.set_defaults(func=cmd_check)

    p = sub.add_parser("next-task", help="list known tasks")
    p.set_defaults(func=cmd_next_task)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
