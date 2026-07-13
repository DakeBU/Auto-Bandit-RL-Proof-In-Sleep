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


if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")

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
LEAN_ROUTE_ROADMAP = ROOT / "research-wiki" / "theory-tree" / "lean-route-roadmap.json"
DEFAULT_EXTENDED_PRO_PROMPT = (
    ROOT
    / "reports"
    / "extended_pro_after_oracle_wrong_event_coord_meas_candidate_prompt_2026-06-30.md"
)
DEFAULT_EXTENDED_PRO_PENDING = (
    ROOT
    / "reports"
    / "extended_pro_after_oracle_wrong_event_coord_meas_pending_2026-06-30.md"
)
DEFAULT_EXTENDED_PRO_RESPONSE_TEMPLATE = (
    ROOT
    / "reports"
    / "extended_pro_after_oracle_wrong_event_coord_meas_response_template_2026-06-30.md"
)
DEFAULT_EXTENDED_PRO_HANDOFF = (
    ROOT
    / "reports"
    / "extended_pro_after_oracle_wrong_event_coord_meas_manual_handoff_2026-06-30.md"
)
DEFAULT_EXTENDED_PRO_RESPONSE_STEM = "extended_pro_after_oracle_wrong_event_coord_meas"
DEFAULT_EXTENDED_PRO_BOUNDARY = "ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES"
DEFAULT_EXTENDED_PRO_REVIEW_TITLE = "After Oracle Wrong-Event Coordinate Measurability"
DEFAULT_REVIEW_PROMPT = (
    ROOT
    / "reports"
    / "local_dual_review_after_oracle_wrong_event_coord_meas_prompt_2026-06-30.md"
)
DEFAULT_REVIEW_PENDING = (
    ROOT
    / "reports"
    / "local_dual_review_after_oracle_wrong_event_coord_meas_pending_2026-06-30.md"
)
DEFAULT_REVIEW_RESPONSE_TEMPLATE = (
    ROOT
    / "reports"
    / "local_dual_review_after_oracle_wrong_event_coord_meas_response_template_2026-06-30.md"
)
DEFAULT_REVIEW_HANDOFF = (
    ROOT
    / "reports"
    / "local_dual_review_after_oracle_wrong_event_coord_meas_handoff_2026-06-30.md"
)
DEFAULT_REVIEW_RESPONSE_STEM = "local_dual_review_after_oracle_wrong_event_coord_meas"
DEFAULT_REVIEW_BOUNDARY = "ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES"
DEFAULT_REVIEW_TITLE = "After Oracle Wrong-Event Coordinate Measurability"
DEFAULT_REVIEW_MODEL = "Local dual-agent review"


def default_extended_pro_response_output() -> Path:
    today = _dt.datetime.now().strftime("%Y-%m-%d")
    return (
        ROOT
        / "reports"
        / f"{DEFAULT_EXTENDED_PRO_RESPONSE_STEM}_{today}.md"
    )


def default_review_response_output() -> Path:
    today = _dt.datetime.now().strftime("%Y-%m-%d")
    return (
        ROOT
        / "reports"
        / f"{DEFAULT_REVIEW_RESPONSE_STEM}_{today}.md"
    )

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
        "module": "Mathlib.Data.Finset.Basic; Mathlib.Data.Finset.Card; Mathlib.Algebra.BigOperators.Group.Finset.Basic; Mathlib.Algebra.Field.Rat",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html",
        "query_terms": [
            "Finset.sum",
            "Finset.range",
            "Finset.card",
            "Finset.sum_range_succ",
            "Finset.range_add_one",
            "Finset.filter_insert",
            "sum_filter",
            "sum_congr",
            "card_filter",
        ],
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
        "module": "Mathlib.MeasureTheory.MeasurableSpace.Basic; Mathlib.MeasureTheory.Integral.Bochner.Basic",
        "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Basic.html",
        "query_terms": [
            "Measurable",
            "MeasurableSet",
            "MeasurableSingletonClass",
            "MeasurableSet.singleton",
            "Measurable.indicator",
            "Integrable",
            "lintegral",
            "integral",
            "AEStronglyMeasurable",
            "AEMeasurable",
        ],
        "role": "Measurable-space canaries, expected regret, Bayesian regret, integrability contracts, and expectation linearity routes.",
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
        "id": "PPR-KUROKI-RUMI-TSUCHIYA-VITALE-CESABIANCHI-2023-BOBW-LCB",
        "title": "Best-of-Both-Worlds Algorithms for Linear Contextual Bandits",
        "authors": "Yuko Kuroki; Alberto Rumi; Taira Tsuchiya; Fabio Vitale; Nicolò Cesa-Bianchi",
        "source": "https://arxiv.org/abs/2312.15433",
        "scenarios": ["SCN-BOBW-ADAPTIVE", "SCN-CONTEXTUAL", "SCN-LINEAR-GLM"],
        "proof_roots": ["best-of-both-worlds linear contextual bandits", "FTRL", "stochastic/adversarial interpolation"],
        "lean_leaf_families": ["context distribution contract", "linear loss estimator", "FTRL stability", "polylog stochastic regret route"],
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
    {
        "id": "PPR-EMNLP-2024-LLM-PRIOR-BANDITS",
        "title": "Jump Starting Bandits with LLM-Generated Prior Knowledge",
        "authors": "Contextual bandit and LLM-generated prior knowledge authors",
        "source": "https://arxiv.org/abs/2406.19317",
        "scenarios": ["SCN-LLM-REC-SYS", "SCN-CONTEXTUAL"],
        "proof_roots": ["LLM-generated priors", "contextual bandits", "offline-to-online warm start"],
        "lean_leaf_families": ["prior-quality contract", "logged-data positivity", "contextual regret warm-start comparison"],
        "memory_status": "paper-card",
    },
    {
        "id": "PPR-BOUNEFFOUF-FERAUD-2025-MAB-LLM",
        "title": "Multi-Armed Bandits Meet Large Language Models",
        "authors": "Djallel Bouneffouf; Raphael Feraud",
        "source": "https://arxiv.org/abs/2505.13355",
        "scenarios": ["SCN-LLM-REC-SYS", "SCN-CONTEXTUAL"],
        "proof_roots": ["bandit-enhanced LLM systems", "LLM-enhanced bandit frameworks", "adaptive model/prompt selection"],
        "lean_leaf_families": ["model-selection action space", "prompt-policy context contract", "human-feedback/logged-feedback bridge"],
        "memory_status": "survey-card",
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
            "PPR-KUROKI-RUMI-TSUCHIYA-VITALE-CESABIANCHI-2023-BOBW-LCB",
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
        "source_cards": [
            "PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB",
            "PPR-FEDERATED-NEURAL-BANDITS-2022",
            "PPR-EMNLP-2024-LLM-PRIOR-BANDITS",
            "PPR-BOUNEFFOUF-FERAUD-2025-MAB-LLM",
        ],
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
            "pullCount_eq_of_forall_lt",
            "pullCount_const_self",
            "pullCount_const_of_ne",
            "pullCount_add_eq_of_forall_ne_between",
            "pullCount_add_eq_add_of_forall_eq_between",
            "pullCount_eq_list_filter_length",
            "sumRewards_succ_of_eq",
            "sumRewards_succ_of_ne",
            "sumRewards_eq_zero_of_forall_ne",
            "sumRewards_const_of_ne",
            "sumRewards_add_eq_of_forall_ne_between",
            "sumRewards_eq_list_range_foldl",
            "sumRewards_eq_list_range_filter_foldl",
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
            "pseudoRegret_eq_list_range_foldl",
        ],
        "role": "Compiled dependency-light bridge leaves for pull counts, prefix congruence, segment counts, reward sums, gaps, and pseudo-regret.",
        "mathlib_routes": ["MLIB-FINSET-SUMS", "MLIB-FINTYPE-FIN", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-FINITE-BANDIT-MODEL-INVARIANTS",
        "leaf_ids": [
            "FINITE-BANDIT-GAP-BESTARM",
            "FINITE-BANDIT-BESTARM-DOMINATES",
            "FINITE-BANDIT-GAP-NONNEG",
            "FINITE-BANDIT-MAXGAP",
            "FINITE-BANDIT-GAP-LE-MAXGAP",
            "FINITE-BANDIT-MAXGAP-NONNEG",
        ],
        "module": "BanditRLProof.Core; BanditRLProof.FiniteBanditModelInvariants",
        "status": "leanCompiled",
        "declarations": [
            "FiniteBanditModel.gap_bestArm",
            "FiniteBanditModel.mean_le_bestArm_mean",
            "FiniteBanditModel.gap_nonneg",
            "FiniteBanditModel.maxGap",
            "FiniteBanditModel.gap_le_maxGap",
            "FiniteBanditModel.maxGap_nonneg",
        ],
        "role": "Compiled zero best-arm gap, best-arm dominance, model-gap nonnegativity, and finite max-gap invariants for the local FiniteBanditModel selector.",
        "mathlib_routes": ["MLIB-FINTYPE-FIN", "MLIB-FINSET-SUMS", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-ALGORITHM-WRAPPERS",
        "leaf_ids": [
            "ETC-EXPLOREARM-EQ-IFF-MOD",
            "ETC-EXPLOREARM-ADD-K",
        ],
        "module": "BanditRLProof.Algorithms.ETC; BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "ETC.exploreArm_eq_of_mod_eq",
            "ETC.exploreArm_eq_iff_mod_eq_val",
            "ETC.exploreArm_add_K",
            "UCB.score_eq_empiricalMean",
        ],
        "role": "Compiled dependency-light wrapper leaves for current ETC and UCB surfaces, including ETC modular round-robin helpers.",
        "mathlib_routes": ["MLIB-FINTYPE-FIN", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-UCB-CONFIDENCE-ALGEBRA",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.confidenceScore",
            "UCB.meanGap",
            "UCB.meanGap_le_two_radius_of_confidenceScore_max",
            "UCB.not_two_radius_lt_meanGap_of_confidenceScore_max",
        ],
        "role": "Compiled deterministic UCB confidence-radius algebra: defines the Real-valued confidence score `empiricalMean + radius` and mean gap against a designated best arm, proves that best-arm upper confidence, chosen-arm lower confidence, and score maximality imply `gap <= 2 * chosenRadius`, and exposes the strict-gap contradiction consumer. This is the good-event algebra input for future suboptimal-pull/count bounds; it does not prove the log/sqrt radius formula, concentration tail producer, expected pull-count bound, or final UCB regret theorem.",
        "mathlib_routes": ["MLIB-ORDER-ALGEBRA", "LOCAL-LEAF-TAIL-SUMMABILITY-UCB"],
    },
    {
        "id": "LOCAL-LEAF-UCB-CONFIDENCE-EVENT-CONSUMER",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.upperConfidenceBad",
            "UCB.lowerConfidenceBad",
            "UCB.confidenceBadEvent",
            "UCB.not_upperConfidenceBad_of_not_confidenceBadEvent",
            "UCB.not_lowerConfidenceBad_of_not_confidenceBadEvent",
            "UCB.meanGap_le_two_radius_of_not_confidenceBadEvent",
        ],
        "role": "Compiled UCB confidence-event consumer: defines random empirical-mean upper/lower confidence failure sets and their finite-arm union bad event, proves that outside this bad event each arm has the needed upper/lower confidence facts, and combines that event complement with UCB score maximality to get `gap <= 2 * chosenRadius`. Event measurability is provided by a separate local wrapper; concrete empirical-mean measurability, tail bounds, log/sqrt radius formulas, pull-count bounds, and final regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-CONFIDENCE-ALGEBRA", "LOCAL-LEAF-TAIL-SUMMABILITY-UCB", "LOCAL-LEAF-TAIL-UNION-FINITE"],
    },
    {
        "id": "LOCAL-LEAF-UCB-CONFIDENCE-EVENT-UNION-BOUND",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
            "TAIL-SUMMABILITY-UCB",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.measure_confidenceBadEvent_le_sum_upper_lower",
        ],
        "role": "Compiled finite-arm union-bound consumer for UCB confidence events: the measure of the union of upper/lower confidence failures is bounded by the finite sum of each arm's upper and lower failure measures. This is an outer-measure wrapper and connects the confidence event API to future per-arm tail bounds; event measurability is provided by a separate local wrapper, while concentration tails, log/sqrt radius formulas, pull-count bounds, and final regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-CONFIDENCE-EVENT-CONSUMER", "LOCAL-LEAF-TAIL-UNION-FINITE", "LOCAL-LEAF-TAIL-SUMMABILITY-UCB"],
    },
    {
        "id": "LOCAL-LEAF-UCB-CONFIDENCE-EVENT-MEASURABILITY",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.measurableSet_upperConfidenceBad",
            "UCB.measurableSet_lowerConfidenceBad",
            "UCB.measurableSet_confidenceBadEvent",
        ],
        "role": "Compiled UCB confidence-event measurability wrapper: per-arm empirical-mean measurability gives measurable upper/lower confidence failure events and the finite-arm confidence bad event. This connects the event consumer/union-bound layer to probability-facing APIs; concrete empirical-mean measurability, tail bounds, log/sqrt radius formulas, pull-count bounds, and final UCB regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-CONFIDENCE-EVENT-CONSUMER", "LOCAL-LEAF-UCB-CONFIDENCE-EVENT-UNION-BOUND", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-UCB-FINITE-HORIZON-CONFIDENCE-EVENT",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
            "TAIL-SUMMABILITY-UCB",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.confidenceBadEventAt",
            "UCB.measurableSet_confidenceBadEventAt",
            "UCB.finiteHorizonConfidenceBadEvent",
            "UCB.measure_finiteHorizonConfidenceBadEvent_le_sum_upper_lower",
        ],
        "role": "Compiled finite-horizon UCB confidence-event bridge: packages the time-indexed confidence bad event, proves its single-time measurability from per-arm empirical-mean measurability, and bounds the finite-horizon bad-event measure by the double finite sum over times, arms, and upper/lower confidence failures. This assembles existing single-time UCB event wrappers across t < T; concrete empirical-mean construction, concentration tails, log/sqrt radius formulas, pull-count bounds, and final UCB regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-CONFIDENCE-EVENT-MEASURABILITY", "LOCAL-LEAF-UCB-CONFIDENCE-EVENT-UNION-BOUND", "LOCAL-LEAF-TAIL-SUMMABILITY-UCB", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-UCB-FINITE-HORIZON-GOOD-EVENT-CONSUMER",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.not_confidenceBadEventAt_of_not_finiteHorizonConfidenceBadEvent",
            "UCB.meanGap_le_two_radius_of_not_finiteHorizonConfidenceBadEvent",
            "UCB.mem_finiteHorizonConfidenceBadEvent_of_two_radius_lt_meanGap_of_score_max",
            "UCB.scoreMaxEvent_subset_finiteHorizonConfidenceBadEvent_of_two_radius_lt_meanGap",
        ],
        "role": "Compiled finite-horizon UCB good-event consumer: outside `finiteHorizonConfidenceBadEvent`, every `t < T` single-time confidence bad event is absent, and score maximality at that time yields `meanGap <= 2 * radius t chosen`; contrapositively, a score-max event for a large-gap arm is included in the finite-horizon bad event. This connects the confidence event to the deterministic gap-radius consumer used by later pull-count proofs; concrete selected-arm trace, empirical-mean construction, pull-count bounds, and final UCB regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-FINITE-HORIZON-CONFIDENCE-EVENT", "LOCAL-LEAF-UCB-CONFIDENCE-EVENT-CONSUMER", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-UCB-FINITE-HORIZON-CONFIDENCE-TAIL-CONSUMER",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
            "TAIL-SUMMABILITY-UCB",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.measure_finiteHorizonConfidenceBadEvent_le_tail_sum",
        ],
        "role": "Compiled finite-horizon UCB confidence-event tail-budget consumer: if every time/arm upper and lower confidence failure has an ENNReal tail bound, then the finite-horizon confidence bad event is bounded by the double finite sum of those upper/lower tail budgets. This assembles abstract tail assumptions only; concrete empirical-mean construction, concentration tail production, log/sqrt radius formulas, pull-count bounds, and final UCB regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-FINITE-HORIZON-CONFIDENCE-EVENT", "LOCAL-LEAF-TAIL-SUMMABILITY-UCB", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-UCB-ABS-DEVIATION-TAIL-ADAPTER",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
            "TAIL-SUMMABILITY-UCB",
            "BRL-OP-CONCENTRATION-001",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.upperConfidenceBad_subset_absDeviation",
            "UCB.lowerConfidenceBad_subset_absDeviation",
            "UCB.measure_upperConfidenceBad_le_absDeviation",
            "UCB.measure_lowerConfidenceBad_le_absDeviation",
            "UCB.measure_finiteHorizonConfidenceBadEvent_le_absDeviation_tail_sum",
        ],
        "role": "Compiled UCB absolute-deviation tail adapter: upper and lower confidence failures are subsets of the absolute empirical-mean deviation event `radius <= |empiricalMean - trueMean|`; measure monotonicity exposes upper/lower failure bounds from absolute-deviation bounds, and the finite-horizon confidence bad event is bounded by the double sum of a shared absolute-deviation tail budget. This aligns the UCB event layer with Chebyshev/sub-Gaussian concentration event shapes; concrete empirical-mean construction, concentration tail production, log/sqrt radius formulas, pull-count bounds, and final UCB regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-FINITE-HORIZON-CONFIDENCE-TAIL-CONSUMER", "TAIL-VARIANCE-ROBUST", "TAIL-SUBGAUSS-SUM", "TAIL-COND-SUBGAUSS"],
    },
    {
        "id": "LOCAL-LEAF-UCB-CHEBYSHEV-ABS-DEVIATION-TAIL",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
            "TAIL-SUMMABILITY-UCB",
            "TAIL-VARIANCE-ROBUST",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.chebyshevAbsDeviationTail",
            "UCB.measure_absDeviation_le_chebyshev_tail",
            "UCB.measure_finiteHorizonConfidenceBadEvent_le_chebyshev_tail_sum",
        ],
        "role": "Compiled UCB Chebyshev absolute-deviation tail producer: under finite measure, `MemLp` second-moment evidence, positive radius, and empirical-mean expectation identified with `trueMean`, the UCB absolute-deviation event is bounded by the Mathlib variance/Chebyshev budget, and the finite-horizon confidence bad event is bounded by the corresponding double finite sum. This is a finite-variance concentration route only; empirical-mean construction, variance-rate simplification, sub-Gaussian/log-sqrt UCB radius formulas, pull-count bounds, and final UCB regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-ABS-DEVIATION-TAIL-ADAPTER", "LOCAL-LEAF-CONCENTRATION-VARIANCE", "MLIB-PROBABILITY-VARIANCE"],
    },
    {
        "id": "LOCAL-LEAF-UCB-SUBGAUSSIAN-ABS-DEVIATION-TAIL",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
            "TAIL-SUMMABILITY-UCB",
            "TAIL-SUBGAUSS-SUM",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.subGaussianAbsDeviationTail",
            "UCB.measure_absDeviation_le_subGaussian_tail",
            "UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_tail_sum",
        ],
        "role": "Compiled UCB sub-Gaussian absolute-deviation tail producer: if the centered empirical-mean error `empiricalMean t arm - trueMean arm` has a Mathlib `HasSubgaussianMGF` proxy and the radius is nonnegative, then the UCB absolute-deviation event has the standard two-sided exponential tail, and the finite-horizon confidence bad event is bounded by the corresponding double finite sum. This is still an abstract centered empirical-mean tail route; empirical-mean construction, proxy/radius simplification to the textbook log/sqrt form, pull-count bounds, and final UCB regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-ABS-DEVIATION-TAIL-ADAPTER", "LOCAL-LEAF-CONCENTRATION-SUBGAUSSIAN", "TAIL-SUBGAUSS-SUM", "TAIL-COND-SUBGAUSS"],
    },
    {
        "id": "LOCAL-LEAF-UCB-SUBGAUSSIAN-ONE-SIDED-TAIL",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
            "TAIL-SUMMABILITY-UCB",
            "TAIL-SUBGAUSS-SUM",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.subGaussianOneSidedDeviationTail",
            "UCB.measure_upperConfidenceBad_le_subGaussian_tail",
            "UCB.measure_lowerConfidenceBad_le_subGaussian_tail",
            "UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_oneSided_tail_sum",
        ],
        "role": "Compiled sharper UCB one-sided sub-Gaussian tail producer: if the centered empirical-mean error `empiricalMean t arm - trueMean arm` has a Mathlib `HasSubgaussianMGF` proxy and the radius is nonnegative, then each upper/lower confidence failure is bounded by the one-sided exponential tail, and the finite-horizon confidence bad event is bounded by the corresponding upper-plus-lower finite sum. This avoids routing one-sided confidence failures through a two-sided absolute-deviation budget, but still leaves empirical-mean construction, proxy/radius simplification to the textbook log/sqrt form, pull-count bounds, and final UCB regret separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-FINITE-HORIZON-CONFIDENCE-TAIL-CONSUMER", "LOCAL-LEAF-CONCENTRATION-SUBGAUSSIAN", "TAIL-SUBGAUSS-SUM", "TAIL-COND-SUBGAUSS"],
    },
    {
        "id": "LOCAL-LEAF-UCB-SUBGAUSSIAN-RADIUS-BUDGET",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
            "TAIL-SUMMABILITY-UCB",
            "TAIL-SUBGAUSS-SUM",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.subGaussianOneSidedDeviationTail_le_exp_neg_budget",
            "UCB.measure_upperConfidenceBad_le_subGaussian_exp_neg_budget",
            "UCB.measure_lowerConfidenceBad_le_subGaussian_exp_neg_budget",
            "UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_exp_neg_budget_sum",
        ],
        "role": "Compiled UCB one-sided sub-Gaussian radius-budget simplification: if `0 < proxy` and `2 * proxy * budget <= radius^2`, the canonical one-sided tail is bounded by `exp(-budget)`, and the upper/lower confidence-failure plus finite-horizon bad-event wrappers consume that budget directly. This is the algebraic handoff toward textbook log/sqrt radii; empirical-mean construction, the actual sqrt/log radius instantiation, pull-count bounds, and final UCB regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-SUBGAUSSIAN-ONE-SIDED-TAIL", "Mathlib.Analysis.SpecialFunctions.Exp", "Mathlib.Data.ENNReal.Real"],
    },
    {
        "id": "LOCAL-LEAF-UCB-SUBGAUSSIAN-SQRT-BUDGET-RADIUS",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
            "TAIL-SUMMABILITY-UCB",
            "TAIL-SUBGAUSS-SUM",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.subGaussianBudgetRadius",
            "UCB.subGaussianBudgetRadius_nonneg",
            "UCB.subGaussianBudgetRadius_sq_domination",
            "UCB.subGaussianOneSidedDeviationTail_budgetRadius_le_exp_neg_budget",
            "UCB.measure_upperConfidenceBad_le_subGaussian_budgetRadius",
            "UCB.measure_lowerConfidenceBad_le_subGaussian_budgetRadius",
            "UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_budgetRadius_sum",
        ],
        "role": "Compiled concrete UCB square-root budget radius leaf: defines `subGaussianBudgetRadius proxy budget t arm = sqrt (2 * proxy * budget)`, proves nonnegativity and the radius-square domination using Mathlib `Real.sq_sqrt'`, then specializes the one-sided sub-Gaussian upper/lower confidence-failure and finite-horizon bad-event bounds to `exp(-budget)` tails. The logarithmic schedule and textbook delta-scale surfaces are compiled separately; empirical-mean construction, pull-count bounds, and final UCB regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-SUBGAUSSIAN-RADIUS-BUDGET", "Mathlib.Data.Real.Sqrt", "Mathlib.Analysis.SpecialFunctions.Exp"],
    },
    {
        "id": "LOCAL-LEAF-UCB-SUBGAUSSIAN-LOG-BUDGET-RADIUS",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
            "TAIL-SUMMABILITY-UCB",
            "TAIL-SUBGAUSS-SUM",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.exp_neg_log_eq_inv",
            "UCB.subGaussianLogBudgetRadius",
            "UCB.subGaussianLogBudgetRadius_apply",
            "UCB.subGaussianLogBudgetRadius_nonneg",
            "UCB.subGaussianLogBudgetRadius_sq_domination",
            "UCB.subGaussianOneSidedDeviationTail_logBudgetRadius_le_inv_scale",
            "UCB.measure_upperConfidenceBad_le_subGaussian_logBudgetRadius",
            "UCB.measure_lowerConfidenceBad_le_subGaussian_logBudgetRadius",
            "UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_logBudgetRadius_inv_scale_sum",
        ],
        "role": "Compiled schedule-agnostic UCB logarithmic budget radius leaf: defines `subGaussianLogBudgetRadius proxy scale = sqrt (2 * proxy * log scale)`, proves nonnegativity and radius-square domination via the square-root budget leaf, simplifies `exp(-log scale)` to `scale⁻¹` under `0 < scale`, and specializes one-sided sub-Gaussian upper/lower confidence-failure plus finite-horizon bad-event bounds to inverse-scale tails. Constant-scale double-sum folding and textbook delta-scale allocation are compiled separately; empirical-mean construction, pull-count bounds, and final UCB regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-SUBGAUSSIAN-SQRT-BUDGET-RADIUS", "Mathlib.Analysis.SpecialFunctions.Log.Basic", "Mathlib.Data.Real.Sqrt"],
    },
    {
        "id": "LOCAL-LEAF-UCB-SUBGAUSSIAN-CONSTANT-LOG-BUDGET-RADIUS",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
            "TAIL-SUMMABILITY-UCB",
            "TAIL-SUBGAUSS-SUM",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.subGaussianConstantLogBudgetRadius",
            "UCB.subGaussianConstantLogBudgetRadius_apply",
            "UCB.subGaussianConstantLogBudgetRadius_nonneg",
            "UCB.subGaussianConstantLogBudgetRadius_sq_domination",
            "UCB.constant_invScale_double_sum",
            "UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_constantLogBudgetRadius_card",
        ],
        "role": "Compiled constant-scale UCB logarithmic budget radius leaf: defines `subGaussianConstantLogBudgetRadius proxy scale = sqrt (2 * proxy * log scale)`, reuses the schedule-agnostic log-budget radius regularity, and folds the finite-horizon inverse-scale double sum into `T` and `Fintype.card Arm` nsmul. The textbook finite-horizon delta scale is compiled separately as `LOCAL-LEAF-UCB-SUBGAUSSIAN-TEXTBOOK-DELTA-RADIUS`; empirical-mean construction, pull-count bounds, and final UCB regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-SUBGAUSSIAN-LOG-BUDGET-RADIUS", "MLIB-FINSET-SUMS", "MLIB-FINTYPE-FIN"],
    },
    {
        "id": "LOCAL-LEAF-UCB-SUBGAUSSIAN-TEXTBOOK-DELTA-RADIUS",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
            "TAIL-SUMMABILITY-UCB",
            "TAIL-SUBGAUSS-SUM",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.constant_invScale_double_sum_le_of_real",
            "UCB.textbookDeltaScale",
            "UCB.textbookDeltaScale_pos",
            "UCB.textbookDeltaScale_total_inv_budget_eq_delta",
            "UCB.constant_invScale_double_sum_textbookDeltaScale_le_delta",
            "UCB.subGaussianTextbookDeltaRadius",
            "UCB.subGaussianTextbookDeltaRadius_apply",
            "UCB.measure_finiteHorizonConfidenceBadEvent_le_subGaussian_textbookDeltaRadius_delta",
            "UCB.measure_scoreMaxEvent_le_subGaussian_textbookDeltaRadius_delta_of_gap",
        ],
        "role": "Compiled textbook finite-horizon UCB delta-scale leaf: defines `textbookDeltaScale T delta = 2 * T * |Arm| / delta`, proves positivity under `0 < T`, nonempty finite arms, and `0 < delta`, proves the folded two-sided inverse-scale tail budget equals `delta` at the real level and is bounded by `ENNReal.ofReal delta`, defines the corresponding `subGaussianTextbookDeltaRadius`, proves the finite-horizon confidence bad event is bounded by `delta` under centered empirical-mean sub-Gaussian hypotheses, and bounds large-gap score-max events by the same `delta` budget. Concrete empirical-mean construction, pull-count bounds, and final UCB regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-SUBGAUSSIAN-CONSTANT-LOG-BUDGET-RADIUS", "Mathlib.Tactic.Ring", "MLIB-FINSET-SUMS", "MLIB-FINTYPE-FIN"],
    },
    {
        "id": "LOCAL-LEAF-UCB-SELECTED-LARGE-GAP-DELTA",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
            "TAIL-SUMMABILITY-UCB",
            "TAIL-SUBGAUSS-SUM",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.selectedEvent_subset_scoreMaxEvent_of_action_score_max",
            "UCB.measure_selectedLargeGapEvent_le_subGaussian_textbookDeltaRadius_delta",
            "UCB.selectedEventOn_subset_finiteHorizonConfidenceBadEvent_of_action_score_max",
            "UCB.measure_selectedLargeGapEventOn_le_subGaussian_textbookDeltaRadius_delta",
        ],
        "role": "Compiled selected-action UCB delta bridge: if a selected action certifies score maximality against the best arm, then the selected-action event is contained in the score-max event, and large-gap selected-arm events inherit the textbook `delta` probability budget under the existing centered empirical-mean sub-Gaussian hypotheses. The finite-time-set variant shows that selecting the same large-gap arm at any time from an explicit `Finset Nat` is still covered by the same finite-horizon confidence bad event and therefore the same `delta` budget. Concrete UCB argmax/tie-breaking policy, empirical-mean construction, pull-count summation, and final regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-SUBGAUSSIAN-TEXTBOOK-DELTA-RADIUS", "MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-UCB-CONCRETE-SCORE-ARGMAX-ACTION",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
            "TAIL-SUMMABILITY-UCB",
            "TAIL-SUBGAUSS-SUM",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.scoreArgmax",
            "UCB.scoreArgmax_spec",
            "UCB.confidenceScoreArgmaxAction",
            "UCB.confidenceScoreArgmaxAction_score_max",
            "UCB.confidenceScoreArgmaxAction_score_max_of_selected",
            "UCB.measure_confidenceScoreArgmax_selectedLargeGapEvent_le_subGaussian_textbookDeltaRadius_delta",
            "UCB.measure_confidenceScoreArgmax_selectedLargeGapEventOn_le_subGaussian_textbookDeltaRadius_delta",
        ],
        "role": "Compiled concrete finite-arm UCB score-argmax action leaf: scans `List.finRange K` over Real scores, proves the selected score dominates every `Fin K` arm, packages a confidence-score argmax action, discharges the selected-action score-maximality contract, and specializes the single-time and finite-time-set large-gap textbook `delta` bounds without an external `hscore_of_selected` hypothesis. Concrete empirical-mean construction, action-trace recursion from histories, pull-count summation, and final regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-SELECTED-LARGE-GAP-DELTA", "MLIB-FINTYPE-FIN", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-UCB-CONCRETE-SCORE-ARGMAX-COUNT-BUDGET",
        "leaf_ids": [
            "UCB-GOOD-EVENT-GAP-CONSUMER",
            "TAIL-SUMMABILITY-UCB",
            "EXP-FINSET-INDICATOR-PULL",
        ],
        "module": "BanditRLProof.Algorithms.UCB",
        "status": "leanCompiled",
        "declarations": [
            "UCB.sum_measure_confidenceScoreArgmax_selectedLargeGapEventOn_le_card_mul_delta",
            "UCB.lintegral_confidenceScoreArgmax_selectedLargeGapCountOn_le_card_mul_delta",
            "UCB.lintegral_confidenceScoreArgmax_pullCount_le_horizon_mul_delta",
            "UCB.lintegral_confidenceScoreArgmax_pullCount_le_free_or_delta_sum",
            "UCB.lintegral_confidenceScoreArgmax_pullCount_le_freeBudget_add_horizon_delta",
            "UCB.freeTimes_indicator_sum_le_card",
            "UCB.selectedSmallPullCount_sum_eq_min_pullCount",
            "UCB.selectedSmallPullCount_sum_le_threshold",
            "UCB.selectedSmallPullCount_indicator_sum_le_threshold",
            "UCB.lintegral_selectedSmallPullCount_indicator_sum_le_threshold",
            "UCB.selectedPullCount_sum_eq_pullCount",
            "UCB.selectedPullCount_indicator_sum_eq_natCast_pullCount",
            "UCB.selectedPullCount_indicator_sum_eq_selectedSmall_add_selectedLargePullCount",
            "UCB.natCast_pullCount_le_threshold_add_selectedLargePullCount_indicator_sum",
            "UCB.measurableSet_selectedLargePullCount",
            "UCB.lintegral_selectedLargePullCount_indicator_sum_eq_sum_measure",
            "UCB.measure_confidenceScoreArgmax_selectedLargePullCountEvent_le_subGaussian_textbookDeltaRadius_delta",
            "UCB.sum_measure_confidenceScoreArgmax_selectedLargePullCountEvent_le_horizon_mul_delta",
            "UCB.lintegral_confidenceScoreArgmax_selectedLargePullCount_indicator_sum_le_horizon_mul_delta",
            "UCB.lintegral_confidenceScoreArgmax_pullCount_le_threshold_add_horizon_delta_of_selectedLargePullCount",
            "UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusRecursiveSampleCount_add_horizon_delta",
            "UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta",
            "UCB.lintegral_historyAction_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta",
            "UCB.lintegral_generatedActionTrace_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta",
            "UCB.identityActionPolicy",
            "UCB.confidenceScoreArgmaxGeneratedState",
            "UCB.confidenceScoreArgmaxGeneratedTrace",
            "UCB.lintegral_confidenceScoreArgmaxGeneratedTrace_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta",
            "UCB.lintegral_confidenceScoreArgmax_pullCount_le_freeCard_add_horizon_delta",
            "UCB.subGaussianTextbookDeltaRadiusChargedTimes",
            "UCB.subGaussianTextbookDeltaRadiusFreeTimes",
            "UCB.mem_subGaussianTextbookDeltaRadiusChargedTimes_iff",
            "UCB.mem_subGaussianTextbookDeltaRadiusFreeTimes_iff",
            "UCB.subGaussianTextbookDeltaRadiusChargedTimes_of_not_free",
            "UCB.subGaussianTextbookDeltaRadiusChargedTimes_gap_large",
            "UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusFreeCard_add_horizon_delta",
            "UCB.subGaussianTextbookDeltaRadiusFreeTimes_card_le_threshold",
            "UCB.subGaussianTextbookDeltaRadiusFreeTimes_card_le_threshold_ennreal",
            "UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusThreshold_add_horizon_delta",
            "UCB.subGaussianTextbookDeltaRadius_large_gap_of_lt_half_meanGap",
            "UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusHalfGapThreshold_add_horizon_delta",
            "UCB.subGaussianTextbookDeltaRadius_lt_half_meanGap_of_sq_lt",
            "UCB.subGaussianTextbookDeltaRadius_lt_half_meanGap_of_eight_mul_lt_sq",
            "UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusEightProxyLogThreshold_add_horizon_delta",
            "UCB.subGaussianTextbookDeltaRadius_lt_half_meanGap_of_proxy_lt_gap_sq_div",
            "UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusProxyThreshold_add_horizon_delta",
            "UCB.subGaussianTextbookDeltaRadius_lt_half_meanGap_of_proxy_le_variance_div_count",
            "UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusSampleCountThreshold_add_horizon_delta",
            "UCB.subGaussianTextbookDeltaRadius_count_large_of_threshold_lt_bound",
            "UCB.lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusSampleCountLowerBound_add_horizon_delta",
        ],
        "role": "Compiled count-facing UCB score-argmax bridge: sums the single-time concrete large-gap selected-arm probability bounds over an explicit finite time set, lifts the result through the existing finite-sum selected-action indicator lower-integral API, yielding a selected-time count budget `|times| * delta`, specializes `times = Finset.range T` through the existing recursive `pullCount` lower-integral identity to bound the selected arm's horizon pull count by `T * delta` when the large-gap condition holds throughout the horizon, exposes a threshold/suffix-shaped pull-count split charging explicit `freeTimes` by `1` and all other large-gap times by `delta`, consumes an abstract free-time budget to produce `freeBudget + T * delta`, discharges that budget with `freeTimes.card` through a generic free-time indicator cardinality wrapper, adds a pathwise selected-small-pull-count budget proving selected occurrences with prior `pullCount < B` sum to `min (pullCount T) B` and hence at most `B`, lifts that selected-small budget to a probability-facing lower-integral bound under an arbitrary probability measure, splits selected pulls into selected-small and selected-large-count indicators, exposes the pointwise ENNReal budget `pullCount <= B + selectedLargeCount`, proves selected-large-count event measurability under an explicit `OpensMeasurableSpace Nat` contract, bounds selected-large-count finite sums by `T * delta` from a pointwise large-count-to-large-gap source, integrates this into a concrete score-argmax `B + T * delta` pull-count wrapper, adds a recursive sample-count adapter from `proxy <= varianceProxy / pullCount` plus the real threshold certificate into that wrapper, adds a source-count wrapper that lets later empirical-mean leaves supply a history-derived `sampleCount` aligned with recursive `pullCount` on selected-large events, adds a history-action wrapper that transfers the same budget to an externally generated trace agreeing with score argmax throughout the horizon, adds a generated-policy trace wrapper that discharges score-argmax measurability from `Policy.generatedActionTrace` state measurability plus pointwise equality, and adds an identity-policy concrete score-argmax generated-trace wrapper that discharges the generated-trace equality contract definitionally. It also instantiates the split with concrete textbook-radius large-gap/free-time Finsets, adds a threshold consumer yielding `B + T * delta` once all horizon times `t >= B` satisfy the large-gap radius condition, exposes the standard half-gap threshold adapter, exposes square/eight-proxy-log threshold consumers, adds a proxy-small threshold consumer under positive log scale, adds a sample-count threshold consumer from `proxy <= varianceProxy / count`, and adds a lower-bound-on-count consumer using a global threshold `B`. Empirical-mean construction, history-recursive UCB action trace, concrete proxy/count source from empirical rewards, and final regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-UCB-CONCRETE-SCORE-ARGMAX-ACTION", "LOCAL-LEAF-EXPECTATION-SUMS", "LOCAL-LEAF-EXPECTATION-PULLCOUNT", "EXP-FINSET-INDICATOR-PULL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-UCB-NATIVE-REAL-HISTORY-INDEX",
        "leaf_ids": [
            "UCB-NATIVE-REAL-HISTORY-INDEX",
            "UCB-INDEX",
        ],
        "module": "BanditRLProof.Algorithms.UCBRealHistoryIndex",
        "status": "leanCompiled",
        "declarations": [
            "UCB.realEmpiricalMean",
            "UCB.realWidth",
            "UCB.realIndex",
            "UCB.realHistoryWidth",
            "UCB.realHistoryIndex",
            "UCB.realIndexAction",
            "UCB.realHistoryIndexAction",
            "UCB.measurable_realEmpiricalMean",
            "UCB.measurable_realWidth",
            "UCB.measurable_realIndex",
            "UCB.realIndexAction_spec",
            "UCB.measurable_realIndexAction",
            "UCB.realHistoryEmpiricalMean_finitePairHistoryOfTrace",
            "UCB.realHistoryWidth_finitePairHistoryOfTrace",
            "UCB.realHistoryIndex_finitePairHistoryOfTrace",
            "UCB.realHistoryIndexAction_finitePairHistoryOfTrace",
        ],
        "role": "Compiled native Real UCB history-index leaf aligned with the pinned LML score. The Lean-facing definitions use realEmpiricalMean = sumRewards / pullCount and the realized path-dependent width realWidth = sqrt (2*c*log(n+1)/pullCount), rather than the older deterministic-in-omega proxy surface. Inclusive finite-pair-history width/index/least-encoded action definitions use the matching n+2 convention and are proved equal to the trace quantities at n+1. The selector reuses the compiled least-Encodable.encode Nat.find semantics and supplies both score maximality and measurability. Local APIs/imports are UCB confidence algebra, ETCRealHistoryScore/ETCRealArgmaxTie, History.finitePairHistoryOfTrace, measurable_sumRewards, measurable_natCast_pullCount, Mathlib Real.log/Real.sqrt and measurable division. Regularity is positive K for the selector, canonical measurable Fin K for measurability, and timewise measurable action/reward coordinates; there is no measure, reward law, MGF, independence, filtration, or positivity-of-count premise in this leaf. Retrieval evidence is pinned LML ucbWidth'/ucbWidth, empMean'/empMean, measurableArgmax, nextArm, and the UCB regret proof at commit 19dc3ab132c2a7539f5944503d1114eac4c5bb74, plus MLIB-REAL-LOG-SQRT, MLIB-FINSET-SUMS, and the compiled local history-score/measurability APIs. Failure policy: concrete empirical-mean, random-width, history/trace score mapping, least-encoded maximization, and measurability are closed. Fixed-count peeling and abstract stream-law transport now compile separately; the next faithful blocker is constructing that source for the actual generated UCB sequence and proving its canonical stationary arm-stream law, followed by one-sided tails and expected pull-count assembly. Do not feed this random width into the older deterministic proxy theorem by strengthening or falsifying its type.",
        "mathlib_routes": [
            "MLIB-REAL-LOG-SQRT",
            "MLIB-FINSET-SUMS",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-MEASURABLE-LOCAL-QUANTITIES",
            "LOCAL-LEAF-MEASURABLE-PULLCOUNT-CAST",
            "LOCAL-LEAF-ETC-NATIVE-REAL-HISTORY-SCORE-SOURCE-EXACT-REGRET",
            "LML-UCB-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-UCB-FIXED-COUNT-PEELING-LAW",
        "leaf_ids": [
            "UCB-FIXED-COUNT-PEELING-LAW",
            "UCB-PEELING-LAW",
        ],
        "module": "BanditRLProof.Algorithms.UCBFixedCountPeeling",
        "status": "leanCompiled",
        "declarations": [
            "UCB.ArmRewardStream",
            "UCB.armPrefixSum",
            "UCB.measurable_armPrefixSum",
            "UCB.FixedArmPrefixSource",
            "UCB.FixedArmPrefixSource.measurable_armStream",
            "UCB.FixedArmPrefixSource.measurable_armPrefixSum",
            "UCB.measure_pullCount_prod_sumRewards_mem_le_of_fixedArmPrefixSource",
            "UCB.measure_pullCount_prod_sumRewards_mem_le_of_fixedArmPrefixSource_identDistrib",
        ],
        "role": "Compiled source-faithful fixed-count peeling and law-transport leaf for the pinned LML UCB route. FixedArmPrefixSource exposes a measurable latent table Nat -> Fin K -> Real and the pathwise identity sumRewards(action,reward,arm,n) = armPrefixSum arm (pullCount action arm n) armStream. The first theorem covers the adaptive (pullCount,sumRewards) event by the finite union over k <= n and applies the Mathlib-backed outer-measure finite-union bound. The second uses one IdentDistrib law for the complete latent stream and measurable composition with armPrefixSum to transport every fixed-count event to a canonical stream measure. Local imports/APIs are UCBRealHistoryIndex, ProbabilityUnionBound.measure_biUnion_finset_le, pullCount_le_time, Finset.range/filter/sum, measurable_pi_apply, Finset.measurable_sum, and ProbabilityTheory.IdentDistrib.measure_mem_eq/comp. Regularity is measurable source and canonical spaces, coordinate measurability recorded by the source, measurable event s, and DecidablePred for the projected count filter; neither theorem requires a probability measure, independence, an MGF, filtration, or count positivity. Retrieval evidence is pinned LML SumRewards.prob_pullCount_prod_sumRewards_mem_le and identDistrib_sum_range_snd at commit 19dc3ab132c2a7539f5944503d1114eac4c5bb74, plus MLIB-PROBABILITY-INDEPENDENCE, MLIB-MEASURE-INTEGRAL, MLIB-FINSET-SUMS, and the compiled local union-bound/count wrappers. Failure policy: generic adaptive-count peeling and abstract complete-stream law transport are closed. Do not claim the UCB tail or regret theorem until the actual generated UCB process supplies FixedArmPrefixSource and the canonical stationary/product arm-stream IdentDistrib law; alternatively record and prove a conditional-MGF substitute with equivalent adaptive-sum strength.",
        "mathlib_routes": [
            "LML-UCB-REGRET",
            "MLIB-PROBABILITY-INDEPENDENCE",
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-FINSET-SUMS",
            "LOCAL-LEAF-PROBABILITY-UNION-BOUND",
            "LOCAL-LEAF-UCB-NATIVE-REAL-HISTORY-INDEX",
        ],
    },
    {
        "id": "LOCAL-LEAF-IID-REWARD-FAMILY",
        "leaf_ids": [
            "IID-REWARD-FAMILY",
        ],
        "module": "BanditRLProof.IndependenceFoundation",
        "status": "leanCompiled",
        "declarations": [
            "IndependenceFoundation.iIndepFun_infinitePi_coord",
            "IndependenceFoundation.iIndepFun_rewardTrace_infinitePi",
        ],
        "role": "Compiled Mathlib-backed infinite-product independence wrappers: coordinate transforms under an infinite product measure form an independent family, with a reward-trace specialization for time-indexed reward coordinates.",
        "mathlib_routes": ["MLIB-PROBABILITY-INDEPENDENCE", "Mathlib.Probability.Independence.InfinitePi"],
    },
    {
        "id": "LOCAL-LEAF-ETC-TRACE",
        "leaf_ids": [
            "ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE",
            "ETC-ACTION-WITH-COMMIT-COMMIT-PHASE",
            "ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE",
        ],
        "module": "BanditRLProof.Algorithms.ETCTrace",
        "status": "leanCompiled",
        "declarations": [
            "ETC.actionWithCommit",
            "ETC.actionWithCommit_eq_exploreArm_of_lt",
            "ETC.actionWithCommit_eq_commitArm_of_ge",
            "ETC.actionWithCommit_eq_bestArm_of_commitArm_eq_bestArm_of_explorationPulls_mul_K_le",
        ],
        "role": "Compiled project-local ETC phase-switching trace boundary: a commit-arm-parametric trace agrees with round-robin exploration during the configured exploration prefix, with the commit arm after that horizon, and with the selected best arm after that horizon when the commit arm is the selected best arm.",
        "mathlib_routes": ["MLIB-FINTYPE-FIN"],
    },
    {
        "id": "LOCAL-LEAF-ETC-TRACE-COUNT",
        "leaf_ids": [
            "ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT",
            "ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT",
            "ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT",
            "ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT",
            "ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT",
            "ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT",
        ],
        "module": "BanditRLProof.Algorithms.ETCTraceCountLemmas",
        "status": "leanCompiled",
        "declarations": [
            "ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le",
            "ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq",
            "ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge",
            "ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq",
            "ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_of_ne",
            "ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_commitArm",
        ],
        "role": "Compiled project-local ETC trace/count transfer and update layer: actionWithCommit matches exploreArm on exploration prefixes, yields the configured exploration-horizon count, has a one-step post-commit recurrence, has a closed-form post-exploration suffix count, and exposes commit-arm plus non-commit-arm suffix corollaries.",
        "mathlib_routes": ["MLIB-FINTYPE-FIN"],
    },
    {
        "id": "LOCAL-LEAF-ETC-EMPIRICAL-MEAN",
        "leaf_ids": [
            "ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION",
            "ETC-EMP-MEAN-COMPARISON-AS-FINITE-SUM",
            "ETC-EMPMEAN-EVENT-SUBSET-SUMREWARDS-TAIL-EVENT",
        ],
        "module": "BanditRLProof.Algorithms.ETCEmpiricalMean",
        "status": "leanCompiled",
        "declarations": [
            "ETC.empMeanAtExploration",
            "ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls",
            "ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos",
            "ETC.empMeanAtExploration_ge_best_event_subset_sumRewards_tail_event_of_imp",
        ],
        "role": "Compiled fixed-commit ETC empirical-mean API: denominator rewrite, positive-denominator comparison to fixed-horizon sumRewards, and event-shape adapter into an abstract real finite-sum tail event.",
        "mathlib_routes": ["MLIB-FINSET-SUMS", "MLIB-ORDER-ALGEBRA", "MLIB-PROBABILITY-SUBGAUSSIAN"],
    },
    {
        "id": "LOCAL-LEAF-ETC-SUMREWARDS-DIFF",
        "leaf_ids": [
            "ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET",
        ],
        "module": "BanditRLProof.Algorithms.ETCSumRewardsDiff",
        "status": "leanCompiled",
        "declarations": [
            "ETC.centeredPairwiseRewardDiff",
            "ETC.centeredPairwiseGapThreshold",
            "ETC.selectedSubMean_sum_eq_sumRewards_sub_pullCount_mul",
            "ETC.meanSubSelected_sum_eq_pullCount_mul_sub_sumRewards",
            "ETC.sumRewards_le_imp_centered_pairwise_sum_ge",
            "ETC.empMeanAtExploration_ge_best_event_subset_centered_pairwise_sum_event",
        ],
        "role": "Compiled deterministic centered pairwise reward-difference Finset bridge: fixed-horizon sumRewards comparison implies the concrete centered Real finite-sum tail event at the ETC exploration horizon.",
        "mathlib_routes": ["MLIB-FINSET-SUMS", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-TAIL-UNION-FINITE",
        "leaf_ids": [
            "TAIL-UNION-FINITE",
        ],
        "module": "BanditRLProof.ProbabilityUnionBound",
        "status": "leanCompiled",
        "declarations": [
            "ProbabilityUnionBound.measure_biUnion_finset_le",
            "ProbabilityUnionBound.measure_iUnion_fintype_le_sum",
        ],
        "role": "Compiled Mathlib-backed finite-union probability/outer-measure wrapper: the measure of a finite union is bounded by the finite sum of event measures, both for an explicit Finset and for a Fintype/univ specialization. No event measurability or probability-measure assumption is required.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-TAIL-SUMMABILITY-UCB",
        "leaf_ids": [
            "TAIL-SUMMABILITY-UCB",
        ],
        "module": "BanditRLProof.UCBSummability",
        "status": "leanCompiled",
        "declarations": [
            "UCBSummability.finiteHorizonBadEvent",
            "UCBSummability.measure_finiteHorizonBadEvent_le_sum",
            "UCBSummability.measure_finiteHorizonBadEvent_le_tail_sum",
        ],
        "role": "Compiled abstract finite-horizon UCB bad-event summability wrapper: the union over finite arms and t < T is bounded by the double finite sum of event measures, and by any per-arm/per-time ENNReal tail budget. This consumes per-event concentration bounds; it does not prove the UCB log/sqrt tail producer or final regret theorem.",
        "mathlib_routes": ["LOCAL-LEAF-TAIL-UNION-FINITE", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-EXP3-POTENTIAL",
        "leaf_ids": [
            "EXP3-POTENTIAL",
        ],
        "module": "BanditRLProof.Exp3Potential",
        "status": "leanCompiled",
        "declarations": [
            "Exp3Potential.potential",
            "Exp3Potential.updatedWeight",
            "Exp3Potential.updatedPotential",
            "Exp3Potential.updatedPotential_eq_sum",
            "Exp3Potential.updatedWeight_nonneg_of_nonneg",
            "Exp3Potential.updatedPotential_nonneg_of_nonneg",
            "Exp3Potential.updatedPotential_sub_potential_eq_sum_weight_mul_exp_sub_one",
            "Exp3Potential.sum_range_forward_difference",
            "Exp3Potential.potentialProcess",
            "Exp3Potential.potentialProcess_telescope_sum_range",
        ],
        "role": "Compiled deterministic finite-action EXP3 potential surface: defines finite-sum potentials, exponential-weight updates, updated-potential unfolding, nonnegativity preservation, one-step potential-increment algebra, and finite-horizon telescoping. This does not prove importance-weighted estimator unbiasedness, exp/log inequalities, learning-rate optimization, or an EXP3 regret theorem.",
        "mathlib_routes": ["MLIB-EXP-LOG-INEQUALITIES", "MLIB-FINSET-SUMS", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-FTRL-ONE-STEP",
        "leaf_ids": [
            "FTRL-ONE-STEP",
        ],
        "module": "BanditRLProof.FTRLOneStep",
        "status": "leanCompiled",
        "declarations": [
            "FTRL.linearLoss",
            "FTRL.finiteSimplex",
            "FTRL.regularizedObjective",
            "FTRL.IsRegularizedMinimizer",
            "FTRL.linearLoss_sub_le_regularizer_sub_div_of_isRegularizedMinimizer",
            "FTRL.linearLoss_sub_le_regularizer_sub_div_of_simplex_minimizer",
        ],
        "role": "Compiled deterministic finite-action FTRL one-step wrapper: finite-sum linear loss, finite-simplex predicate, regularized objective, explicit minimizer certificate, and the positive-learning-rate inequality `linearLoss p - linearLoss q <= (R q - R p) / eta` for any feasible comparator. This consumes minimizer/feasibility certificates and does not prove convexity, minimizer existence, Tsallis regularizer facts, stability/penalty decomposition, or regret.",
        "mathlib_routes": ["MLIB-CONVEX-LINALG", "MLIB-FINSET-SUMS", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-TSALLIS-REGULARIZER",
        "leaf_ids": [
            "TSALLIS-REGULARIZER",
        ],
        "module": "BanditRLProof.TsallisRegularizer",
        "status": "leanCompiled",
        "declarations": [
            "Tsallis.powerSum",
            "Tsallis.entropy",
            "Tsallis.negEntropyRegularizer",
            "Tsallis.one_sub_exponent_ne_zero",
            "Tsallis.powerSum_nonneg_of_finiteSimplex",
            "Tsallis.negEntropyRegularizer_wellDefined_on_finiteSimplex",
        ],
        "role": "Compiled deterministic finite-simplex Tsallis regularizer surface: defines the finite Real.rpow power sum, Tsallis entropy, negative-entropy regularizer, proves the denominator `1 - alpha` is nonzero from `alpha != 1`, proves the power sum is nonnegative on the compiled finite simplex, and packages those well-definedness facts. This does not prove convexity, rpow stability/penalty bounds, self-bounding conversion, learning-rate optimization, or regret.",
        "mathlib_routes": ["MLIB-REAL-RPOW-TSALLIS", "LOCAL-LEAF-FTRL-ONE-STEP", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-GRAM-PSD",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.rankOneGram",
            "OFUL.quadraticForm",
            "OFUL.featureGram",
            "OFUL.rankOneGram_quadraticForm_eq_sq",
            "OFUL.rankOneGram_quadraticForm_nonneg",
            "OFUL.featureGram_quadraticForm_eq_sum_sq",
            "OFUL.featureGram_quadraticForm_nonneg",
        ],
        "role": "Compiled deterministic finite-dimensional OFUL/LinUCB Gram-matrix surface: defines rank-one feature Gram matrices, finite-history feature Gram matrices, an explicit quadratic form, proves the rank-one form is a squared projection, proves the finite-history form is a sum of squared projections, and exposes nonnegativity wrappers. This is a PSD foundation only; it does not prove a determinant lemma, log-determinant telescope, self-normalized martingale bound, confidence ellipsoid, or OFUL regret theorem.",
        "mathlib_routes": ["MLIB-CONVEX-LINALG", "MLIB-FINSET-SUMS", "Mathlib.Data.Matrix.Basic"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-RANKONE-DET-UPDATE",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.rankOneGram_eq_replicateCol_mul_replicateRow",
            "OFUL.det_one_add_rankOneGram",
            "OFUL.det_rankOne_update_factor_eq_one_add_dotProduct_inv_mulVec",
            "OFUL.det_add_rankOneGram",
        ],
        "role": "Compiled Mathlib Schur-complement determinant-update wrapper for OFUL/LinUCB: bridges the local rank-one Gram matrix to Mathlib's replicateCol/replicateRow shape, proves `det (1 + x x^T) = 1 + x^T x`, and packages the invertible-base rank-one update `det (A + x x^T) = det A * (1 + x^T A^{-1} x)` under Mathlib's `IsUnit A.det` side condition. This does not prove positive definiteness/invertibility of regularized Gram matrices, log-determinant telescoping, determinant growth inequalities, self-normalized martingale concentration, confidence ellipsoids, or OFUL regret.",
        "mathlib_routes": ["Mathlib.LinearAlgebra.Matrix.SchurComplement", "LOCAL-LEAF-OFUL-GRAM-PSD", "MLIB-CONVEX-LINALG"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-REGULARIZED-GRAM-BASE",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.det_scalar_identity",
            "OFUL.det_scalar_identity_ne_zero",
            "OFUL.isUnit_det_scalar_identity",
            "OFUL.det_scalar_add_rankOneGram",
            "OFUL.regularizedFeatureGram",
            "OFUL.regularizedFeatureGram_eq_scalar_add_featureGram",
        ],
        "role": "Compiled regularized-Gram base wrapper for OFUL/LinUCB: defines `lambda I + sum_t x_t x_t^T`, proves `det (lambda I) = lambda^d`, packages nonzero scalar regularization as Mathlib's `IsUnit det` side condition, and specializes the rank-one determinant update from the scalar base. This does not prove positive definiteness/invertibility of arbitrary regularized Grams, log-determinant telescoping, determinant-growth inequalities, self-normalized martingale concentration, confidence ellipsoids, or OFUL regret.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-RANKONE-DET-UPDATE", "LOCAL-LEAF-OFUL-GRAM-PSD", "Mathlib.LinearAlgebra.Matrix.SchurComplement", "MLIB-CONVEX-LINALG"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-REGULARIZED-GRAM-QFORM",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.quadraticForm_add",
            "OFUL.quadraticForm_scalar_identity",
            "OFUL.regularizedFeatureGram_quadraticForm_eq_sum_sq",
            "OFUL.regularizedFeatureGram_quadraticForm_nonneg",
        ],
        "role": "Compiled regularized-Gram quadratic-form wrapper for OFUL/LinUCB: proves quadratic forms distribute over matrix addition, unfolds the scalar regularization term as `lambda * sum_i y_i^2`, unfolds the regularized Gram quadratic form as scalar regularization plus finite-history squared projections, and proves PSD under `0 <= lambda`. This does not prove strict positive definiteness, determinant positivity, invertibility of arbitrary regularized Grams, log-determinant telescoping, determinant-growth inequalities, self-normalized martingale concentration, confidence ellipsoids, or OFUL regret.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-REGULARIZED-GRAM-BASE", "LOCAL-LEAF-OFUL-GRAM-PSD", "MLIB-CONVEX-LINALG", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-REGULARIZED-GRAM-POS-QFORM",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.sum_sq_pos_of_exists_ne_zero",
            "OFUL.regularizedFeatureGram_quadraticForm_pos_of_pos_lambda",
        ],
        "role": "Compiled strict-positive regularized-Gram quadratic-form wrapper for OFUL/LinUCB: proves a finite coordinate square sum is positive for nonzero vectors and therefore `quadraticForm (lambda I + sum_t x_t x_t^T) y > 0` under `0 < lambda` and `y != 0`. This is a positive-definiteness route lemma; it does not prove determinant positivity, matrix inverse existence for arbitrary regularized Grams, log-determinant telescoping, determinant-growth inequalities, self-normalized martingale concentration, confidence ellipsoids, or OFUL regret.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-REGULARIZED-GRAM-QFORM", "LOCAL-LEAF-OFUL-REGULARIZED-GRAM-BASE", "MLIB-CONVEX-LINALG", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-REGULARIZED-GRAM-DET-POS",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.dotProduct_mulVec_eq_quadraticForm",
            "OFUL.exists_coord_ne_zero_of_ne_zero",
            "OFUL.featureGram_isHermitian",
            "OFUL.regularizedFeatureGram_isHermitian",
            "OFUL.regularizedFeatureGram_posDef",
            "OFUL.regularizedFeatureGram_det_pos",
            "OFUL.regularizedFeatureGram_det_ne_zero",
            "OFUL.isUnit_det_regularizedFeatureGram",
        ],
        "role": "Compiled Mathlib PosDef/determinant bridge for OFUL/LinUCB regularized Grams: connects the local quadratic-form proof to Mathlib's `Matrix.PosDef`, proves Hermitian wrappers, proves positive determinant and nonzero determinant under `0 < lambda`, and packages the `IsUnit det` side condition for arbitrary finite-history regularized Gram matrices. This does not prove log-determinant telescoping, determinant-growth inequalities, self-normalized martingale concentration, confidence ellipsoids, or OFUL regret.",
        "mathlib_routes": ["Mathlib.Analysis.Matrix.PosDef", "LOCAL-LEAF-OFUL-REGULARIZED-GRAM-POS-QFORM", "LOCAL-LEAF-OFUL-REGULARIZED-GRAM-QFORM", "MLIB-CONVEX-LINALG"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-REGULARIZED-GRAM-DET-UPDATE",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.det_regularizedFeatureGram_add_rankOneGram",
        ],
        "role": "Compiled one-step determinant recursion for OFUL/LinUCB regularized Grams: specializes the rank-one determinant lemma to an arbitrary finite-history regularized Gram and discharges the determinant-unit side condition from positive regularization. This is the direct algebraic input for log-det telescoping; it does not prove the telescope, determinant-growth inequalities, self-normalized martingale concentration, confidence ellipsoids, or OFUL regret.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-REGULARIZED-GRAM-DET-POS", "LOCAL-LEAF-OFUL-RANKONE-DET-UPDATE", "Mathlib.LinearAlgebra.Matrix.SchurComplement"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-LOG-DET-UPDATE",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.rankOneGram_isHermitian",
            "OFUL.rankOneGram_posSemidef",
            "OFUL.regularizedFeatureGram_add_rankOneGram_posDef",
            "OFUL.det_regularizedFeatureGram_add_rankOneGram_pos",
            "OFUL.regularizedFeatureGram_rankOne_update_factor_pos",
            "OFUL.log_det_regularizedFeatureGram_add_rankOneGram",
            "OFUL.log_det_regularizedFeatureGram_add_rankOneGram_sub",
        ],
        "role": "Compiled logarithmic one-step determinant-update wrapper for OFUL/LinUCB: proves rank-one Grams are Mathlib-positive semidefinite, the rank-one update of a positive regularized Gram remains PosDef with positive determinant, the determinant-update scalar factor is positive, and `log det(V + x x^T) - log det(V) = log(1 + x^T V^{-1} x)`. This is the local log-det increment input; it does not prove finite-horizon log-det telescoping, determinant-growth inequalities, self-normalized martingale concentration, confidence ellipsoids, or OFUL regret.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-REGULARIZED-GRAM-DET-UPDATE", "LOCAL-LEAF-OFUL-REGULARIZED-GRAM-DET-POS", "Mathlib.Analysis.SpecialFunctions.Log.Basic"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-LOG-DET-TELESCOPE",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.sum_range_forward_difference",
            "OFUL.sum_range_log_update_factor_eq_log_det_ratio",
        ],
        "role": "Compiled abstract finite-horizon log-det telescope wrapper for OFUL/LinUCB: packages `sum_t (Phi_{t+1} - Phi_t) = Phi_T - Phi_0` and the corresponding sum of one-step log-update factors into a final log-determinant ratio. This is not yet instantiated with a concrete growing OFUL history process and does not prove determinant-growth inequalities, self-normalized martingale concentration, confidence ellipsoids, or OFUL regret.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-LOG-DET-UPDATE", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-PREFIX-LOG-DET-TELESCOPE",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.prefixFeatureGram",
            "OFUL.regularizedPrefixFeatureGram",
            "OFUL.prefixFeatureGram_succ",
            "OFUL.regularizedPrefixFeatureGram_succ",
            "OFUL.prefixFeatureGram_isHermitian",
            "OFUL.regularizedPrefixFeatureGram_isHermitian",
            "OFUL.prefixFeatureGram_quadraticForm_eq_sum_sq",
            "OFUL.regularizedPrefixFeatureGram_quadraticForm_eq_sum_sq",
            "OFUL.prefixFeatureGram_quadraticForm_nonneg",
            "OFUL.regularizedPrefixFeatureGram_quadraticForm_nonneg",
            "OFUL.regularizedPrefixFeatureGram_quadraticForm_pos_of_pos_lambda",
            "OFUL.regularizedPrefixFeatureGram_posDef",
            "OFUL.regularizedPrefixFeatureGram_det_pos",
            "OFUL.regularizedPrefixFeatureGram_det_ne_zero",
            "OFUL.isUnit_det_regularizedPrefixFeatureGram",
            "OFUL.det_regularizedPrefixFeatureGram_add_rankOneGram",
            "OFUL.regularizedPrefixFeatureGram_add_rankOneGram_posDef",
            "OFUL.det_regularizedPrefixFeatureGram_add_rankOneGram_pos",
            "OFUL.regularizedPrefixFeatureGram_rankOne_update_factor_pos",
            "OFUL.log_det_regularizedPrefixFeatureGram_add_rankOneGram",
            "OFUL.log_det_regularizedPrefixFeatureGram_add_rankOneGram_sub",
            "OFUL.det_regularizedPrefixFeatureGram_succ",
            "OFUL.log_det_regularizedPrefixFeatureGram_succ_sub",
            "OFUL.sum_range_log_regularizedPrefixFeatureGram_update_factor_eq_log_det_ratio",
        ],
        "role": "Compiled concrete Nat-prefix growing-history log-det telescope for OFUL/LinUCB: defines prefix Grams `sum_{t<T} x_t x_t^T`, proves successor rank-one updates, Hermitian/quadratic-form/PSD/PosDef and determinant side conditions under `0 < lambda`, proves one-step determinant/log-det recursions for `T -> T+1`, and instantiates the abstract finite-horizon log-det telescope to the prefix determinant sequence. This does not prove determinant-growth upper bounds such as elliptical-potential min/log inequalities, self-normalized martingale concentration, confidence ellipsoids, or OFUL regret.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-LOG-DET-TELESCOPE", "LOCAL-LEAF-OFUL-LOG-DET-UPDATE", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-PREFIX-LOG-DET-BASE",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.prefixFeatureGram_zero",
            "OFUL.regularizedPrefixFeatureGram_zero",
            "OFUL.det_regularizedPrefixFeatureGram_zero",
            "OFUL.sum_range_log_regularizedPrefixFeatureGram_update_factor_eq_log_det_sub_base",
        ],
        "role": "Compiled scalar-base endpoint wrapper for the concrete Nat-prefix OFUL/LinUCB log-det telescope: proves the zero-horizon prefix Gram is zero, the zero-horizon regularized prefix Gram is `lambda I`, its determinant is `lambda^d`, and rewrites the prefix log-det telescope endpoint as `log det(V_T) - log(lambda^d)`. This still does not prove determinant-growth upper bounds, elliptical-potential min/log inequalities, self-normalized martingale concentration, confidence ellipsoids, or OFUL regret.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-PREFIX-LOG-DET-TELESCOPE", "LOCAL-LEAF-OFUL-REGULARIZED-GRAM-BASE"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-DETERMINANT-GROWTH-CONSUMER",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.div_one_add_self_le_log_one_add",
            "OFUL.self_le_two_log_one_add_of_le_one",
            "OFUL.one_le_two_log_two",
            "OFUL.min_one_le_two_log_one_add",
            "OFUL.sum_range_min_one_le_two_sum_log_one_add",
            "OFUL.sum_range_min_prefix_update_le_two_log_det_sub_base",
        ],
        "role": "Compiled first determinant-growth consumer for OFUL/LinUCB: proves the scalar inequality `min 1 z <= 2 log(1+z)` for `0 <= z`, lifts it to finite sums, and combines it with the concrete Nat-prefix log-det telescope to bound the sum of clipped inverse-quadratic update scalars by `2 * (log det(V_T) - log(lambda^d))`. It keeps nonnegativity of each inverse-quadratic scalar as an explicit regularity contract and does not yet prove that contract from `PosDef` inverse APIs, determinant upper bounds, self-normalized martingale concentration, confidence ellipsoids, or OFUL regret.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-PREFIX-LOG-DET-BASE", "Mathlib.Analysis.SpecialFunctions.Log.Basic", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-CLIPPED-SUM-LOG-UPPER",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.sum_range_min_one_le_two_of_sum_log_one_add_le",
        ],
        "role": "Compiled clipped finite-sum log-upper handoff for OFUL/LinUCB: under explicit `0 <= u_t` and an abstract certificate `sum_t log(1+u_t) <= B`, the clipped update sum `sum_t min(1,u_t)` is bounded by `2 * B`. This keeps scalar clipped-sum bookkeeping separate from determinant telescopes, PosDef discharge, determinant upper bounds, self-normalized martingale concentration, confidence ellipsoids, and OFUL regret.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-DETERMINANT-GROWTH-CONSUMER", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-UNCLIPPED-SMALL-UPDATE-SUM-LOG",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.sum_range_le_two_sum_log_one_add_of_le_one",
        ],
        "role": "Compiled finite-sum small-update log bridge for OFUL/LinUCB: under explicit `0 <= u_t` and `u_t <= 1`, the raw update sum is bounded by `2 * sum_t log(1+u_t)`. This is the unclipped counterpart of the scalar min/log finite-sum bridge; determinant telescope, PosDef discharge, determinant upper bounds, self-normalized martingale concentration, confidence ellipsoids, and OFUL regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-DETERMINANT-GROWTH-CONSUMER", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-UNCLIPPED-SMALL-UPDATE-SUM-LOG-UPPER",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.sum_range_le_two_of_sum_log_one_add_le_of_le_one",
        ],
        "role": "Compiled finite-sum small-update log-upper handoff for OFUL/LinUCB: under explicit `0 <= u_t`, `u_t <= 1`, and an abstract certificate `sum_t log(1+u_t) <= B`, the raw update sum is bounded by `2 * B`. This keeps scalar finite-sum bookkeeping separate from determinant telescopes, PosDef discharge, determinant upper bounds, self-normalized martingale concentration, confidence ellipsoids, and OFUL regret.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-UNCLIPPED-SMALL-UPDATE-SUM-LOG", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-UNCLIPPED-SMALL-UPDATE-LOG-DET-EXPLICIT-NONNEG",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.sum_range_prefix_update_le_two_log_det_sub_base",
        ],
        "role": "Compiled explicit-regularity small-update log-det endpoint consumer for OFUL/LinUCB: under explicit `0 <= u_t` and `u_t <= 1` contracts, the raw inverse-quadratic update sum is bounded by `2 * (log det(V_T)-log(lambda^d))`. This is the unclipped counterpart of the first determinant-growth consumer; PosDef discharge, determinant upper bounds, self-normalized martingale concentration, confidence ellipsoids, and OFUL regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-DETERMINANT-GROWTH-CONSUMER", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-INVERSE-QUADRATIC-NONNEG-CONSUMER",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.regularizedPrefixFeatureGram_inv_posDef",
            "OFUL.regularizedPrefixFeatureGram_inv_quadratic_nonneg",
            "OFUL.sum_range_min_prefix_update_le_two_log_det_sub_base_of_pos_lambda",
        ],
        "role": "Compiled PosDef-inverse consumer for the OFUL/LinUCB determinant-growth route: uses Mathlib `Matrix.PosDef.inv` and `PosSemidef.dotProduct_mulVec_nonneg` to prove `0 <= x^T V_t^{-1} x` for Nat-prefix regularized Grams under `0 < lambda`, then removes the explicit inverse-quadratic nonnegativity contract from the clipped min/log determinant-growth bound. It does not prove determinant upper bounds, dimension/radius simplifications, self-normalized martingale concentration, confidence ellipsoids, or OFUL regret.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-DETERMINANT-GROWTH-CONSUMER", "LOCAL-LEAF-OFUL-PREFIX-LOG-DET-BASE", "Mathlib.Analysis.Matrix.PosDef"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-UNCLIPPED-SMALL-UPDATE-LOG-DET-SUB-BASE",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.sum_range_prefix_update_le_two_log_det_sub_base_of_update_le_one",
        ],
        "role": "Compiled small-update log-det telescope endpoint consumer for OFUL/LinUCB: under `0 < lambda` and `u_t <= 1`, the raw inverse-quadratic update sum is bounded by `2 * (log det(V_T)-log(lambda^d))`. This removes clipping only under the explicit small-update contract; determinant upper bounds, self-normalized martingale concentration, confidence ellipsoids, and OFUL regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-INVERSE-QUADRATIC-NONNEG-CONSUMER", "LOCAL-LEAF-OFUL-PREFIX-LOG-DET-BASE", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-LOG-DET-UPPER-CONSUMER",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.sum_range_min_prefix_update_le_two_log_det_upper",
        ],
        "role": "Compiled terminal log-determinant upper-bound consumer for OFUL/LinUCB: if a later route supplies `log det(V_T) - log(lambda^d) <= B`, the local clipped elliptical-potential sum is bounded by `2 * B`. This is the handoff surface for determinant upper bounds; it does not prove the concrete trace/AM-GM determinant upper bound, dimension/radius simplification, self-normalized martingale concentration, confidence ellipsoids, or OFUL regret.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-INVERSE-QUADRATIC-NONNEG-CONSUMER", "LOCAL-LEAF-OFUL-DETERMINANT-GROWTH-CONSUMER", "MLIB-CONVEX-LINALG"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-UNCLIPPED-SMALL-UPDATE-LOG-DET-UPPER",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.sum_range_prefix_update_le_two_log_det_upper_of_update_le_one",
        ],
        "role": "Compiled small-update terminal log-determinant upper-bound consumer for OFUL/LinUCB: if `log det(V_T)-log(lambda^d) <= B` and every inverse-quadratic update scalar satisfies `u_t <= 1`, the raw unclipped update sum is bounded by `2 * B`. This is a deterministic handoff only; determinant upper bounds, self-normalized martingale concentration, confidence ellipsoids, and OFUL regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-LOG-DET-UPPER-CONSUMER", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-DET-MUL-EXP-UPPER-CONSUMER",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.log_det_regularizedPrefixFeatureGram_sub_base_le_of_det_le_mul_exp",
            "OFUL.sum_range_min_prefix_update_le_two_det_mul_exp_upper",
        ],
        "role": "Compiled multiplicative determinant-upper consumer for OFUL/LinUCB: turns a future bound `det(V_T) <= lambda^d * exp(B)` into `log det(V_T)-log(lambda^d) <= B` using Mathlib `Real.log_le_log`, `Real.log_mul`, and `Real.log_exp`, then yields the clipped elliptical-potential sum bound `<= 2 * B`. It does not prove the concrete determinant upper bound itself, trace/AM-GM dimension-radius simplification, self-normalized martingale concentration, confidence ellipsoids, or OFUL regret.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-LOG-DET-UPPER-CONSUMER", "Mathlib.Analysis.SpecialFunctions.Log.Basic", "Mathlib.Analysis.Matrix.PosDef"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-UNCLIPPED-SMALL-UPDATE-DET-MUL-EXP-UPPER",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.sum_range_prefix_update_le_two_det_mul_exp_upper_of_update_le_one",
        ],
        "role": "Compiled small-update multiplicative determinant-upper consumer for OFUL/LinUCB: if `det(V_T) <= lambda^d * exp(B)` and every inverse-quadratic update scalar satisfies `u_t <= 1`, the raw unclipped update sum is bounded by `2 * B`. This is a deterministic handoff only; concrete determinant bounds, self-normalized martingale concentration, confidence ellipsoids, and OFUL regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-UNCLIPPED-SMALL-UPDATE-LOG-DET-UPPER", "LOCAL-LEAF-OFUL-DET-MUL-EXP-UPPER-CONSUMER", "Mathlib.Analysis.SpecialFunctions.Log.Basic"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-PREFIX-TRACE-BOUND",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.trace_rankOneGram",
            "OFUL.trace_scalar_identity",
            "OFUL.trace_prefixFeatureGram",
            "OFUL.trace_regularizedPrefixFeatureGram",
            "OFUL.trace_regularizedPrefixFeatureGram_le",
        ],
        "role": "Compiled trace/radius input layer for the OFUL/LinUCB determinant-upper route: proves rank-one, scalar, prefix, and regularized-prefix trace expansions, and bounds `trace(V_T)` by `d * lambda + T * L2` under a pointwise squared-feature-norm ceiling. This is the trace side of the future trace/AM-GM determinant upper bound; it does not prove the AM-GM product-of-eigenvalues inequality, the concrete multiplicative determinant bound, self-normalized martingale concentration, confidence ellipsoids, or OFUL regret.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-DET-MUL-EXP-UPPER-CONSUMER", "Mathlib.LinearAlgebra.Matrix.Trace", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-TRACE-AVERAGE-DET-CONSUMER",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.det_regularizedPrefixFeatureGram_le_pow_trace_bound_average",
        ],
        "role": "Compiled trace-average determinant-upper consumer for OFUL/LinUCB: if a future AM-GM/eigenvalue route supplies `det(V_T) <= (trace(V_T)/d)^d`, the local trace/radius bound converts it to `det(V_T) <= ((d*lambda + T*L2)/d)^d` under a pointwise squared-feature-norm ceiling and an explicit average nonnegativity side condition. The AM-GM and scalar-exp simplifications are handled by later local leaves; self-normalized martingale concentration, confidence ellipsoids, and OFUL regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-PREFIX-TRACE-BOUND", "Mathlib.Analysis.MeanInequalities", "Mathlib.Analysis.Matrix.PosDef"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-AMGM-DET-TRACE-BOUND",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.finset_prod_le_pow_sum_div_card_of_nonneg",
            "OFUL.prod_univ_le_pow_sum_div_card_of_nonneg",
            "OFUL.det_posSemidef_le_pow_trace_div_card",
            "OFUL.det_regularizedPrefixFeatureGram_le_pow_trace_div_card",
            "OFUL.det_regularizedPrefixFeatureGram_le_pow_trace_bound_average_of_pos_lambda",
        ],
        "role": "Compiled Mathlib-backed AM-GM determinant trace bound for OFUL/LinUCB: wraps `Real.geom_mean_le_arith_mean` into a finite nonnegative product bound, applies it to positive-semidefinite eigenvalues using Mathlib `det_eq_prod_eigenvalues` and `trace_eq_sum_eigenvalues`, proves `det(V_T) <= (trace(V_T)/d)^d` for regularized Nat-prefix Grams under `0 < lambda`, and combines this with the local trace/radius bound to get `det(V_T) <= ((d*lambda + T*L2)/d)^d`. It assumes a nonempty feature type; scalar-exp simplification is handled by a later local leaf, while self-normalized martingale concentration, confidence ellipsoids, and OFUL regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-TRACE-AVERAGE-DET-CONSUMER", "LOCAL-LEAF-OFUL-PREFIX-TRACE-BOUND", "Mathlib.Analysis.MeanInequalities", "Mathlib.Analysis.Matrix.PosDef"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-TRACE-AVERAGE-EXP-CONSUMER",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.det_regularizedPrefixFeatureGram_le_mul_exp_of_trace_average_bound",
            "OFUL.sum_range_min_prefix_update_le_two_of_trace_average_bound",
        ],
        "role": "Compiled final multiplicative handoff consumer for OFUL/LinUCB determinant growth: once a scalar simplification proves `((d*lambda + T*L2)/d)^d <= lambda^d * exp(B)`, the local AM-GM/trace/radius route yields `det(V_T) <= lambda^d * exp(B)` and therefore the clipped elliptical-potential sum bound `<= 2 * B`. The concrete scalar-exp simplification is now tracked by `LOCAL-LEAF-OFUL-SCALAR-TRACE-AVERAGE-EXP-BOUND`; self-normalized martingale concentration, confidence ellipsoids, and OFUL regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-AMGM-DET-TRACE-BOUND", "LOCAL-LEAF-OFUL-DET-MUL-EXP-UPPER-CONSUMER", "Mathlib.Analysis.SpecialFunctions.Exp"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-SCALAR-TRACE-AVERAGE-EXP-BOUND",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.trace_average_pow_le_lambda_pow_mul_exp_dim_scaled",
            "OFUL.det_regularizedPrefixFeatureGram_le_mul_exp_trace_average_dim_scaled",
            "OFUL.sum_range_min_prefix_update_le_two_trace_average_dim_scaled",
        ],
        "role": "Compiled scalar exponential simplification and concrete OFUL/LinUCB consumers: under `0 < lambda`, `0 <= L2`, nonempty feature type, and pointwise squared-norm ceiling, proves `((d*lambda + T*L2)/d)^d <= lambda^d * exp(d * (T*L2/(d*lambda)))`, then derives the determinant bound and clipped elliptical-potential sum bound with that explicit exponent. Dimension cancellation is handled by a later local leaf; self-normalized martingale concentration, confidence ellipsoids, and OFUL regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-AMGM-DET-TRACE-BOUND", "LOCAL-LEAF-OFUL-TRACE-AVERAGE-EXP-CONSUMER", "Mathlib.Analysis.SpecialFunctions.Exp", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-SCALAR-TRACE-AVERAGE-EXP-CANCEL",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.trace_average_exp_exponent_dim_cancel",
            "OFUL.trace_average_pow_le_lambda_pow_mul_exp",
            "OFUL.det_regularizedPrefixFeatureGram_le_mul_exp_trace_average",
            "OFUL.sum_range_min_prefix_update_le_two_trace_average",
        ],
        "role": "Compiled dimension-cancelled scalar exponential OFUL/LinUCB consumers: proves `d * (T*L2/(d*lambda)) = T*L2/lambda`, upgrades the trace-average scalar inequality to `((d*lambda + T*L2)/d)^d <= lambda^d * exp(T*L2/lambda)`, and derives determinant plus clipped elliptical-potential bounds with the standard exponent. Self-normalized martingale concentration, confidence ellipsoids, and OFUL regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-SCALAR-TRACE-AVERAGE-EXP-BOUND", "LOCAL-LEAF-OFUL-TRACE-AVERAGE-EXP-CONSUMER", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-SCALAR-TRACE-AVERAGE-EXP-LOG",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.trace_average_pow_le_lambda_pow_mul_exp_log",
            "OFUL.det_regularizedPrefixFeatureGram_le_mul_exp_trace_average_log",
            "OFUL.sum_range_min_prefix_update_le_two_trace_average_log",
        ],
        "role": "Compiled standard logarithmic OFUL/LinUCB trace-average endpoint: under `0 < lambda`, `0 <= L2`, nonempty feature type, and pointwise squared-norm ceiling, proves `((d*lambda + T*L2)/d)^d <= lambda^d * exp(d * log(1 + T*L2/(d*lambda)))`, then derives the determinant bound and clipped elliptical-potential sum bound `<= 2 * d * log(1 + T*L2/(d*lambda))`. This keeps the textbook logarithmic determinant-growth shape instead of linearizing to `T*L2/lambda`; self-normalized martingale concentration, confidence ellipsoids, and OFUL regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-AMGM-DET-TRACE-BOUND", "LOCAL-LEAF-OFUL-TRACE-AVERAGE-EXP-CONSUMER", "Mathlib.Analysis.SpecialFunctions.Log.Basic", "Mathlib.Analysis.SpecialFunctions.Exp"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-UNCLIPPED-SMALL-UPDATE-GENERIC",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.sum_range_prefix_update_le_two_of_trace_average_bound_of_update_le_one",
        ],
        "role": "Compiled generic small-update OFUL/LinUCB elliptical-potential consumer: any scalar trace-average certificate `((d*lambda + T*L2)/d)^d <= lambda^d * exp(B)` now yields a raw, unclipped inverse-quadratic update-sum bound `<= 2 * B` when each update scalar is at most one. This is a deterministic handoff for later least-squares/confidence routes; self-normalized martingale concentration, confidence ellipsoids, and OFUL regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-TRACE-AVERAGE-EXP-CONSUMER", "LOCAL-LEAF-OFUL-INVERSE-QUADRATIC-NONNEG-CONSUMER", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-UNCLIPPED-SMALL-UPDATE-DIM-SCALED",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.sum_range_prefix_update_le_two_trace_average_dim_scaled_of_update_le_one",
        ],
        "role": "Compiled dimension-scaled small-update OFUL/LinUCB elliptical-potential consumer: under `0 < lambda`, `0 <= L2`, pointwise squared-norm ceiling, and `u_t <= 1`, the raw inverse-quadratic update sum is bounded by `2 * (d * (T*L2/(d*lambda)))`. This preserves the pre-cancellation scalar endpoint for later algebraic routes; self-normalized martingale concentration, confidence ellipsoids, and OFUL regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-UNCLIPPED-SMALL-UPDATE-GENERIC", "LOCAL-LEAF-OFUL-SCALAR-TRACE-AVERAGE-EXP-BOUND", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-UNCLIPPED-SMALL-UPDATE-LINEAR",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.sum_range_prefix_update_le_two_trace_average_of_update_le_one",
        ],
        "role": "Compiled dimension-cancelled small-update OFUL/LinUCB elliptical-potential consumer: under `0 < lambda`, `0 <= L2`, pointwise squared-norm ceiling, and `u_t <= 1`, the raw inverse-quadratic update sum is bounded by `2 * (T*L2/lambda)`. This is a deterministic coarse endpoint for later least-squares/confidence routes; self-normalized martingale concentration, confidence ellipsoids, and OFUL regret remain separate.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-UNCLIPPED-SMALL-UPDATE-GENERIC", "LOCAL-LEAF-OFUL-SCALAR-TRACE-AVERAGE-EXP-CANCEL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-OFUL-UNCLIPPED-SMALL-UPDATE-LOG",
        "leaf_ids": [
            "OFUL-ELLIPTICAL-POTENTIAL",
        ],
        "module": "BanditRLProof.OFULEllipticalPotential",
        "status": "leanCompiled",
        "declarations": [
            "OFUL.sum_range_prefix_update_le_two_trace_average_log_of_update_le_one",
        ],
        "role": "Compiled small-update OFUL/LinUCB elliptical-potential consumer: if every inverse-quadratic update scalar is at most one, the existing clipped logarithmic trace-average endpoint applies to the raw, unclipped update sum. This is a deterministic handoff for later confidence/least-squares routes; it still does not prove self-normalized martingale concentration, confidence ellipsoids, or OFUL regret.",
        "mathlib_routes": ["LOCAL-LEAF-OFUL-SCALAR-TRACE-AVERAGE-EXP-LOG", "LOCAL-LEAF-OFUL-INVERSE-QUADRATIC-NONNEG-CONSUMER", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-CONCENTRATION-SUBGAUSSIAN",
        "leaf_ids": [
            "TAIL-HOEFFDING-BOUNDED",
            "TAIL-SUBGAUSS-SUM",
            "TAIL-SUBGAUSS-DIFF-SUM-IMPORT",
            "TAIL-COND-SUBGAUSS",
        ],
        "module": "BanditRLProof.ConcentrationSubGaussian",
        "status": "leanCompiled",
        "declarations": [
            "Concentration.intervalVarianceProxy",
            "Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq",
            "Concentration.subGaussian_sum_tail_of_iIndepFun",
            "Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun",
            "Concentration.condSubGaussian_sum_tail_of_stronglyAdapted",
            "Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted",
        ],
        "role": "Compiled Mathlib-backed sub-Gaussian concentration wrappers: bounded-variable Hoeffding MGF source with interval variance proxy, independent finite-sum tail, ENNReal boundary adapter, strongly adapted conditional sub-Gaussian finite-prefix tail, and its ENNReal boundary adapter.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-CONDITIONAL-EXPECTATION", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-CONCENTRATION-VARIANCE",
        "leaf_ids": [
            "TAIL-VARIANCE-ROBUST",
        ],
        "module": "BanditRLProof.ConcentrationVariance",
        "status": "leanCompiled",
        "declarations": [
            "Concentration.variance_chebyshev_tail",
            "Concentration.evariance_chebyshev_tail",
            "Concentration.variance_sum_of_pairwise_indep",
        ],
        "role": "Compiled Mathlib-backed finite-variance concentration wrappers: real-variance Chebyshev tail, extended-real evariance Chebyshev tail, and finite-sum variance additivity for pairwise independent summands. This is not a robust mean estimator or a final bandit regret theorem.",
        "mathlib_routes": ["MLIB-PROBABILITY-VARIANCE", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-ETC-PAIRWISE-CENTERED-SUBGAUSS-TAIL",
        "leaf_ids": [
            "ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF",
        ],
        "module": "BanditRLProof.Algorithms.ETCPairwiseCenteredSubGaussianTail",
        "status": "leanCompiled",
        "declarations": [
            "ETC.pairwiseEmpMeanTailContract_of_centered_subGaussian_event_bounds",
        ],
        "role": "Compiled concrete producer specialization from centered pairwise reward-difference sub-Gaussian witnesses over the ETC exploration horizon to PairwiseEmpMeanTailContract; independence and sub-Gaussian witnesses remain explicit hypotheses.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-DIFF-SUBGAUSS-WITNESS-CONTRACT",
        "leaf_ids": [
            "ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT",
        ],
        "module": "BanditRLProof.Algorithms.ETCCenteredDiffSubGaussianWitnesses",
        "status": "leanCompiled",
        "declarations": [
            "ETC.CenteredDiffSubGaussianWitnesses",
            "ETC.pairwiseEmpMeanTailContract_of_centeredDiffSubGaussianWitnesses",
        ],
        "role": "Compiled witness contract surface for concrete centered reward-difference sub-Gaussian ETC tail work: packages variance proxies, independence, HasSubgaussianMGF, and tail domination, then produces PairwiseEmpMeanTailContract through the centered-diff producer.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-DIFF-COND-SUBGAUSS-WITNESS-CONTRACT",
        "leaf_ids": [
            "ETC-CENTERED-DIFF-COND-SUBGAUSSIAN-WITNESS-CONTRACT",
        ],
        "module": "BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses",
        "status": "leanCompiled",
        "declarations": [
            "ETC.CenteredDiffCondSubGaussianWitnesses",
            "ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses",
        ],
        "role": "Compiled conditional reward-law contract surface for the ETC centered reward-difference route: packages per-arm filtrations, strong adaptedness, HasSubgaussianMGF at index 0, later HasCondSubgaussianMGF witnesses, and tail domination, then produces PairwiseEmpMeanTailContract through the conditional sub-Gaussian wrapper. This supports COND-EXPECT-REWARD; bounded/source assembly for the fixed actionWithCommit reward-level package is now compiled, while full policy predictability remains open.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-CONDITIONAL-EXPECTATION", "MLIB-MARTINGALE-STOCHASTIC", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-DIFF-STRONGLY-ADAPTED-HISTORY",
        "leaf_ids": [
            "ETC-CENTERED-DIFF-STRONGLY-ADAPTED-HISTORY",
        ],
        "module": "BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses",
        "status": "leanCompiled",
        "declarations": [
            "History.historyFiltrationSucc",
            "History.historyFiltrationSucc_apply",
            "ETC.measurable_centeredPairwiseRewardDiff_historyFiltrationSucc",
            "ETC.stronglyAdapted_centeredPairwiseRewardDiff_historyFiltrationSucc",
        ],
        "role": "Compiled adaptedness-field derivation for the ETC conditional centered-diff route: shifts the generated history filtration by one step and proves fixed-commit centered pairwise reward differences are strongly adapted under reward-coordinate measurability. Concrete conditional MGF witnesses remain open.",
        "mathlib_routes": ["MLIB-CONDITIONAL-EXPECTATION", "MLIB-MARTINGALE-STOCHASTIC", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-DIFF-COND-MGF-ZERO-MISS",
        "leaf_ids": [
            "ETC-CENTERED-DIFF-COND-MGF-ZERO-MISS",
        ],
        "module": "BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses",
        "status": "leanCompiled",
        "declarations": [
            "ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_action_miss",
            "ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_miss",
            "ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_miss",
        ],
        "role": "Compiled zero-summand MGF source for the ETC conditional centered-diff route: when fixed-commit actionWithCommit at a time pulls neither the comparison arm nor the best arm, the centered pairwise reward-difference is definitionally zero and has zero-variance unconditional and conditional sub-Gaussian MGF, including the shifted generated-history specialization. Sampled reward-law MGF witnesses remain open.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-CONDITIONAL-EXPECTATION", "MLIB-MARTINGALE-STOCHASTIC"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-DIFF-COND-MGF-SAMPLED-TRANSFER",
        "leaf_ids": [
            "ETC-CENTERED-DIFF-COND-MGF-SAMPLED-TRANSFER",
        ],
        "module": "BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses",
        "status": "leanCompiled",
        "declarations": [
            "ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_arm",
            "ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_bestArm",
            "ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_arm",
            "ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_bestArm",
        ],
        "role": "Compiled sampled-arm conditional MGF transfer for the ETC centered-diff route: when actionWithCommit pulls the comparison arm, a conditional MGF witness for reward minus that arm mean transfers to centeredPairwiseRewardDiff; when it pulls bestArm, an explicit negative-centered best-arm conditional MGF witness transfers. This still assumes sampled centered-reward MGF witnesses.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-CONDITIONAL-EXPECTATION", "MLIB-MARTINGALE-STOCHASTIC"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-REWARD-COND-SUBGAUSS-WITNESS-CONTRACT",
        "leaf_ids": [
            "ETC-CENTERED-REWARD-COND-SUBGAUSSIAN-WITNESS-CONTRACT",
        ],
        "module": "BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses",
        "status": "leanCompiled",
        "declarations": [
            "ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_centeredReward",
            "ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_centeredReward",
            "ETC.CenteredRewardCondSubGaussianWitnesses",
            "ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses",
        ],
        "role": "Compiled reward-level conditional sub-Gaussian witness contract for the ETC centered-diff route: packages sampled centered-reward conditional MGF witnesses, the zeroth unconditional witness, reward-coordinate measurability, and tail domination, then constructs CenteredDiffCondSubGaussianWitnesses. Independence plus unconditional centered-reward sub-Gaussianity supplies the fixed-action conditional MGF bridge, and BoundedRewardTraceSource now assembles the fixed actionWithCommit reward-level package.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-CONDITIONAL-EXPECTATION", "MLIB-MARTINGALE-STOCHASTIC"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-REWARD-COND-MGF-INDEP-SOURCE",
        "leaf_ids": [
            "ETC-CENTERED-REWARD-COND-MGF-INDEP-SOURCE",
        ],
        "module": "BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses",
        "status": "leanCompiled",
        "declarations": [
            "ETC.hasCondSubgaussianMGF_of_indep_comap",
            "ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_iIndepFun_reward",
        ],
        "role": "Compiled independence-based conditional MGF source for the ETC centered-reward route: Mathlib's condExpKernel/of_rat route turns unconditional HasSubgaussianMGF plus independence from a sub-sigma-algebra into HasCondSubgaussianMGF, then specializes reward-coordinate iIndepFun to fixed actionWithCommit History.historyFiltrationSucc. Concrete kernel-law construction of the unconditional centered-reward sub-Gaussian witnesses and full policy predictability remain open.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-CONDITIONAL-EXPECTATION", "MLIB-PROBABILITY-INDEPENDENCE"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-REWARD-COND-MEAN-ZERO-INDEP-SOURCE",
        "leaf_ids": [
            "ETC-CENTERED-REWARD-COND-MEAN-ZERO-INDEP-SOURCE",
        ],
        "module": "BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses",
        "status": "leanCompiled",
        "declarations": [
            "ETC.centeredReward_condExp_eq_zero_of_indep",
            "ETC.centeredReward_condExp_historyFiltrationSucc_eq_zero_of_indep",
            "ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_indep",
            "ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_iIndepFun_reward",
        ],
        "role": "Compiled conditional mean-zero source for the ETC centered reward route: wraps Mathlib condExp_indep_eq to show a centered reward has zero conditional expectation against an arbitrary sub-sigma-algebra, specializes it to History.historyFiltrationSucc, adds the succ-indexed shape used by Mathlib's conditional tail API, and combines reward-coordinate iIndepFun plus the full fixed-action history independence bridge with an explicit zero-integral side condition. Concrete reward-law conditional MGF remains open; the exact-mean zero-integral source is a separate compiled leaf.",
        "mathlib_routes": ["MLIB-CONDITIONAL-EXPECTATION", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-REWARD-COND-MEAN-ZERO-BOUNDED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ETC-CENTERED-REWARD-COND-MEAN-ZERO-BOUNDED-SOURCE",
        ],
        "module": "BanditRLProof.Algorithms.ETCBoundedRewardSource",
        "status": "leanCompiled",
        "declarations": [
            "ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_boundedRewardTraceSource",
        ],
        "role": "Compiled bounded-source conditional mean-zero wrapper for the ETC centered reward route: BoundedRewardTraceSource supplies reward-coordinate iIndepFun and the action-matched zero-integral identity, an explicit action equality rewrites the mean to the sampled arm, and the existing succ-indexed History.historyFiltrationSucc conditional mean-zero source discharges the conditional expectation. This is fixed to deterministic actionWithCommit; arbitrary policy predictability and condExpKernel trajectory identification remain open.",
        "mathlib_routes": ["MLIB-CONDITIONAL-EXPECTATION", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL", "LOCAL-LEAF-ETC-CENTERED-REWARD-COND-MEAN-ZERO-INDEP-SOURCE", "LOCAL-LEAF-ETC-CENTERED-REWARD-ZERO-INTEGRAL-SOURCE"],
    },
    {
        "id": "LOCAL-LEAF-MART-DIFF-PREFIX-WITNESS",
        "leaf_ids": [
            "MART-DIFF-REWARD",
        ],
        "module": "BanditRLProof.MartingaleDifference",
        "status": "leanCompiled",
        "declarations": [
            "MartingaleDiff.SuccMartingaleDifference",
            "MartingaleDiff.SuccMartingaleDifference.toPrefix",
            "MartingaleDiff.SuccMartingaleDifference.stronglyAdapted'",
            "MartingaleDiff.SuccMartingaleDifference.integrable'",
            "MartingaleDiff.SuccMartingaleDifference.condExp_succ_ae_eq_zero",
            "MartingaleDiff.SuccMartingaleDifferencePrefix",
            "MartingaleDiff.SuccMartingaleDifferencePrefix.stronglyAdapted'",
            "MartingaleDiff.SuccMartingaleDifferencePrefix.integrable_of_lt",
            "MartingaleDiff.SuccMartingaleDifferencePrefix.condExp_succ_ae_eq_zero",
            "MartingaleDiff.centeredRewardProcess",
            "MartingaleDiff.succMartingaleDifference_centeredRewardProcess_of_condExp",
            "MartingaleDiff.succMartingaleDifferencePrefix_centeredRewardProcess_of_condExp",
            "MartingaleDiff.partialSumsSucc",
            "MartingaleDiff.martingale_partialSumsSucc_of_succMartingaleDifference",
            "MartingaleDiff.martingale_partialSumsSucc_centeredRewardProcess_of_condExp",
        ],
        "role": "Compiled martingale-difference witness surface for MART-DIFF-REWARD: records global and finite-prefix StronglyAdapted increments, integrability, and succ-indexed conditional mean-zero facts; names centeredRewardProcess as reward minus baseline; builds global/prefix martingale-difference witnesses for centered rewards from those contracts; defines partialSumsSucc starting from Y 1; and proves via Mathlib martingale_of_condExp_sub_eq_zero_nat that global succ-indexed centered-reward differences yield a Mathlib Martingale partial-sum process. This is not optional stopping, condExpKernel reward-law identification, arbitrary adaptive policy predictability, or final adaptive regret.",
        "mathlib_routes": ["MLIB-MARTINGALE-STOCHASTIC", "MLIB-CONDITIONAL-EXPECTATION", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-REWARD-MART-DIFF-BOUNDED-SOURCE",
        "leaf_ids": [
            "MART-DIFF-REWARD",
            "COND-EXPECT-REWARD",
        ],
        "module": "BanditRLProof.Algorithms.ETCBoundedRewardSource",
        "status": "leanCompiled",
        "declarations": [
            "ETC.measurable_centeredReward_actionWithCommit_historyFiltrationSucc",
            "ETC.stronglyAdapted_centeredReward_actionWithCommit_historyFiltrationSucc",
            "ETC.centeredReward_actionWithCommit_integrable_of_boundedRewardTraceSource",
            "ETC.centeredReward_actionWithCommit_succMartingaleDifferencePrefix_of_boundedRewardTraceSource",
        ],
        "role": "Compiled fixed-action ETC centered-reward martingale-difference prefix source: for deterministic actionWithCommit and a BoundedRewardTraceSource, action-matched centered rewards are strongly adapted to History.historyFiltrationSucc, integrable on any prefix inside the exploration horizon, and have succ-indexed conditional expectation zero. This remains finite-prefix and fixed-policy; arbitrary adaptive policy predictability, condExpKernel law identification, and final martingale/regret theorems remain open.",
        "mathlib_routes": ["LOCAL-LEAF-MART-DIFF-PREFIX-WITNESS", "LOCAL-LEAF-ETC-CENTERED-REWARD-COND-MEAN-ZERO-BOUNDED-SOURCE", "LOCAL-LEAF-ETC-CENTERED-REWARD-BOUNDED-INTEGRABLE-SOURCE", "FILTRATION-HISTORY", "MLIB-MARTINGALE-STOCHASTIC"],
    },
    {
        "id": "LOCAL-LEAF-STOPPING-TIME-BUDGET",
        "leaf_ids": [
            "STOPPING-TIME-BUDGET",
        ],
        "module": "BanditRLProof.BudgetStoppingTime",
        "status": "leanCompiled",
        "declarations": [
            "Budget.budgetExhaustionTime",
            "Budget.isStoppingTime_budgetExhaustionTime_of_adapted",
            "Budget.measurableSet_budgetExhaustionTime_le_of_adapted",
        ],
        "role": "Compiled Mathlib-backed budget stopping-time wrapper: the first time an adapted Nat-valued accumulated-resource process reaches a budget is a stopping time, with the horizon event measurable at each filtration level. This is not a BwK model, optional-stopping theorem, or resource-constrained regret result.",
        "mathlib_routes": ["MLIB-MARTINGALE-STOCHASTIC", "MLIB-CONDITIONAL-EXPECTATION", "Mathlib.Probability.Process.HittingTime"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-REWARD-PAST-IINDEP-SOURCE",
        "leaf_ids": [
            "ETC-CENTERED-REWARD-PAST-IINDEP-SOURCE",
        ],
        "module": "BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses",
        "status": "leanCompiled",
        "declarations": [
            "ETC.indep_centeredReward_succ_pastReward_iSup_of_iIndepFun_reward",
            "ETC.indep_centeredReward_succ_pastReward_iSup_infinitePi",
        ],
        "role": "Compiled product-law/history subleaf for the ETC conditional mean-zero route: reward-coordinate iIndepFun implies the centered reward at time i+1 is independent of the reward-only past coordinate sigma-algebra generated by j <= i, with an infinitePi specialization. The deterministic action generators are handled by the full-history independence leaf.",
        "mathlib_routes": ["MLIB-PROBABILITY-INDEPENDENCE", "FILTRATION-HISTORY"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-REWARD-HISTORY-IINDEP-SOURCE",
        "leaf_ids": [
            "ETC-CENTERED-REWARD-HISTORY-IINDEP-SOURCE",
        ],
        "module": "BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses",
        "status": "leanCompiled",
        "declarations": [
            "ETC.historyFiltrationSucc_actionWithCommit_le_pastReward_iSup",
            "ETC.indep_centeredReward_succ_historyFiltrationSucc_of_iIndepFun_reward",
            "ETC.indep_centeredReward_succ_historyFiltrationSucc_infinitePi",
        ],
        "role": "Compiled full-history product-law subleaf for the ETC conditional mean-zero route: for fixed actionWithCommit, deterministic action singleton generators are univ/empty, so History.historyFiltrationSucc is included in the reward-only past sigma-algebra; reward-coordinate iIndepFun then gives centered reward independence from the full shifted history, with an infinitePi specialization.",
        "mathlib_routes": ["MLIB-PROBABILITY-INDEPENDENCE", "FILTRATION-HISTORY"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-REWARD-ZERO-INTEGRAL-SOURCE",
        "leaf_ids": [
            "ETC-CENTERED-REWARD-ZERO-INTEGRAL-SOURCE",
        ],
        "module": "BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian",
        "status": "leanCompiled",
        "declarations": [
            "ETC.centeredReward_integral_eq_zero_of_integral_eq_mean",
            "ETC.centeredReward_integral_eq_zero_of_mem_Icc_integral_eq_mean",
            "ETC.centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean",
        ],
        "role": "Compiled zero-integral source for the ETC centered reward route: an exact raw-reward mean identity plus raw integrability gives integral(reward - mean) = 0; bounded Icc facts can now supply raw integrability; and the BoundedRewardTraceSource action-matched fields instantiate that fact over the ETC exploration horizon. Concrete reward-law conditional MGF remains separate.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-REWARD-COND-WITNESS-BOUNDED-SOURCE",
        "leaf_ids": [
            "ETC-CENTERED-REWARD-COND-WITNESS-BOUNDED-SOURCE",
        ],
        "module": "BanditRLProof.Algorithms.ETCBoundedRewardSource",
        "status": "leanCompiled",
        "declarations": [
            "ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_boundedRewardTraceSource",
            "ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource",
            "ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian",
            "ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_boundedRewardTraceSource_condSubGaussian",
        ],
        "role": "Compiled bounded/source assembly of the fixed actionWithCommit reward-level conditional witness package plus its pairwise-tail-contract and argmax-probability consumers: BoundedRewardTraceSource gives the zeroth unconditional centered-reward sub-Gaussian witness and, via reward-coordinate independence plus the fixed-history conditional MGF bridge, the later sampled conditional MGF witnesses for CenteredRewardCondSubGaussianWitnesses. Timewise reward measurability, positive exploration horizon, and tail domination remain explicit contracts.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-CONDITIONAL-EXPECTATION", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-REWARD-COND-CANONICAL-TAIL-BOUNDED-SOURCE",
        "leaf_ids": [
            "ETC-CENTERED-REWARD-COND-CANONICAL-TAIL-BOUNDED-SOURCE",
        ],
        "module": "BanditRLProof.Algorithms.ETCBoundedRewardSource",
        "status": "leanCompiled",
        "declarations": [
            "ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource_canonicalTail",
            "ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian_canonicalTail",
            "ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource_condSubGaussian",
        ],
        "role": "Compiled canonical-tail normalization for the fixed actionWithCommit bounded-source conditional route: chooses ETC.centeredDiffSubGaussianTail with the bounded centered-reward variance proxy, discharges the previous explicit tail-domination hypothesis definitionally, and exposes no-htail witness-package, pairwise-tail-contract, and argmax-probability wrappers.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-CONDITIONAL-EXPECTATION", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-REWARD-BOUNDED-INTEGRABLE-SOURCE",
        "leaf_ids": [
            "INT-REWARD-BOUNDED",
            "ETC-CENTERED-REWARD-BOUNDED-INTEGRABLE-SOURCE",
        ],
        "module": "BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian",
        "status": "leanCompiled",
        "declarations": [
            "ETC.centeredReward_integrable_of_mem_Icc",
            "ETC.centeredReward_integrable_of_boundedRewardTraceSource",
        ],
        "role": "Compiled bounded-to-integrable source for the ETC centered reward route: Mathlib Integrable.of_mem_Icc turns a.e. measurability plus an a.s. interval bound into raw reward integrability, and BoundedRewardTraceSource supplies those fields over the fixed-commit ETC exploration horizon.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-DIFF-SUBGAUSS-CANONICAL-TAIL",
        "leaf_ids": [
            "ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL",
        ],
        "module": "BanditRLProof.Algorithms.ETCCenteredDiffCanonicalTail",
        "status": "leanCompiled",
        "declarations": [
            "ETC.centeredDiffSubGaussianTail",
            "ETC.centeredDiffSubGaussianWitnesses_of_indep_subG",
            "ETC.pairwiseEmpMeanTailContract_of_centeredDiff_indep_subG",
        ],
        "role": "Compiled canonical exponential tail helper for the centered-diff independent sub-Gaussian route: turns explicit independence and HasSubgaussianMGF witnesses into CenteredDiffSubGaussianWitnesses and PairwiseEmpMeanTailContract with no separate tail-domination hypothesis.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-ETC-WRONG-COMMIT-CANONICAL-SUBGAUSS",
        "leaf_ids": [
            "ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND",
        ],
        "module": "BanditRLProof.Algorithms.ETCWrongCommitCanonicalTail",
        "status": "leanCompiled",
        "declarations": [
            "ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail",
        ],
        "role": "Compiled concrete argmax-oracle wrong-commit probability bound using the canonical centered-diff independent sub-Gaussian tail budget; reward-law independence and HasSubgaussianMGF witnesses remain explicit.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS",
        "leaf_ids": [
            "ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS",
        ],
        "module": "BanditRLProof.Algorithms.ETCCenteredDiffRewardIndependence",
        "status": "leanCompiled",
        "declarations": [
            "ETC.iIndepFun_centeredPairwiseRewardDiff_of_iIndepFun_reward",
        ],
        "role": "Compiled deterministic independence transfer: time-coordinate independence of the reward trace implies independence of the centered pairwise reward-difference summands via measurable transforms.",
        "mathlib_routes": ["MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS",
        "leaf_ids": [
            "ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS",
        ],
        "module": "BanditRLProof.Algorithms.ETCCenteredDiffRewardSubGaussian",
        "status": "leanCompiled",
        "declarations": [
            "ETC.centeredPairwiseRewardDiffVarianceProxy",
            "ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_centeredReward",
        ],
        "role": "Compiled deterministic sub-Gaussian transfer: per-time centered reward sub-Gaussian witnesses imply centered pairwise reward-difference sub-Gaussian witnesses with an action-case variance proxy.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSS",
        "leaf_ids": [
            "ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSSIAN-BOUND",
        ],
        "module": "BanditRLProof.Algorithms.ETCCenteredDiffRewardSubGaussian",
        "status": "leanCompiled",
        "declarations": [
            "ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_centeredReward_subG",
        ],
        "role": "Compiled concrete argmax-oracle wrong-commit probability bound from trace-level reward-coordinate independence plus per-time centered reward sub-Gaussian witnesses.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-REWARD-BOUNDED-SUBGAUSS-SOURCE",
        "leaf_ids": [
            "ETC-CENTERED-REWARD-BOUNDED-SUBGAUSSIAN-SOURCE",
        ],
        "module": "BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian",
        "status": "leanCompiled",
        "declarations": [
            "ETC.centeredRewardBoundVarianceProxy",
            "ETC.centeredReward_hasSubgaussianMGF_of_mem_Icc_integral_eq_mean",
        ],
        "role": "Compiled ETC-shaped bounded reward source: almost-sure interval bounds plus exact mean identity imply per-time centered reward HasSubgaussianMGF by reusing the generic Concentration bounded-centered Hoeffding wrapper.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSS",
        "leaf_ids": [
            "ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSSIAN-BOUND",
        ],
        "module": "BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian",
        "status": "leanCompiled",
        "declarations": [
            "ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_bounded_centered",
        ],
        "role": "Compiled strong all-arm argmax-oracle wrong-commit probability bound from trace-level reward-coordinate independence, almost-sure reward bounds, and exact mean identities for every arm/time coordinate.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-ETC-WRONG-COMMIT-ACTION-MATCHED-REWARD-SUBGAUSS",
        "leaf_ids": [
            "ETC-WRONG-COMMIT-ACTION-MATCHED-REWARD-SUBGAUSSIAN-BOUND",
        ],
        "module": "BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian",
        "status": "leanCompiled",
        "declarations": [
            "ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_centeredReward_subG",
        ],
        "role": "Compiled concrete argmax-oracle wrong-commit probability bound from trace-level reward-coordinate independence plus centered reward sub-Gaussian witnesses only for the arm actually pulled at each time.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-ETC-WRONG-COMMIT-ACTION-MATCHED-BOUNDED-REWARD",
        "leaf_ids": [
            "ETC-WRONG-COMMIT-ACTION-MATCHED-BOUNDED-REWARD-BOUND",
        ],
        "module": "BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian",
        "status": "leanCompiled",
        "declarations": [
            "ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_bounded_centered",
        ],
        "role": "Compiled practical fixed-commit ETC wrong-commit probability bound from trace-level reward-coordinate independence, action-matched a.e. bounds, and action-matched exact mean identities.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-ETC-BOUNDED-REWARD-TRACE-SOURCE-CONTRACT",
        "leaf_ids": [
            "ETC-BOUNDED-REWARD-TRACE-SOURCE-CONTRACT",
        ],
        "module": "BanditRLProof.Algorithms.ETCBoundedRewardSource",
        "status": "leanCompiled",
        "declarations": [
            "ETC.BoundedRewardTraceSource",
            "ETC.centeredReward_hasSubgaussianMGF_of_boundedRewardTraceSource",
            "ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource",
        ],
        "role": "Compiled action-matched source-contract surface for the bounded-reward ETC route: packages trace-level reward-coordinate independence, a.e. measurability, a.s. interval bounds, exact mean identities for the arm actually pulled at each time, and consumes them for centered reward sub-Gaussian and wrong-commit bounds.",
        "mathlib_routes": ["MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-ETC-INFINITEPI-BOUNDED-REWARD-SOURCE",
        "leaf_ids": [
            "ETC-BOUNDED-REWARD-INFINITEPI-SOURCE",
            "ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE",
        ],
        "module": "BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource",
        "status": "leanCompiled",
        "declarations": [
            "ETC.boundedRewardTraceSource_infinitePi_actionWithCommit",
            "ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean",
        ],
        "role": "Compiled concrete fixed-commit product-coordinate source: infinitePi reward-coordinate laws with action-matched bounds and means instantiate BoundedRewardTraceSource and the argmax-oracle wrong-commit probability bound.",
        "mathlib_routes": ["MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL", "MLIB-PROBABILITY-SUBGAUSSIAN"],
    },
    {
        "id": "LOCAL-LEAF-ETC-CENTERED-REWARD-COND-CANONICAL-TAIL-INFINITEPI-SOURCE",
        "leaf_ids": [
            "ETC-CENTERED-REWARD-COND-CANONICAL-TAIL-INFINITEPI-SOURCE",
        ],
        "module": "BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource",
        "status": "leanCompiled",
        "declarations": [
            "ETC.centeredRewardCondSubGaussianWitnesses_of_infinitePi_bounded_actionMean_canonicalTail",
            "ETC.pairwiseEmpMeanTailContract_of_infinitePi_bounded_actionMean_condSubGaussian_canonicalTail",
            "ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean_condSubGaussian",
        ],
        "role": "Compiled concrete infinitePi specialization of the fixed actionWithCommit bounded-source conditional canonical-tail route: product-coordinate action-matched bounds and means instantiate the reward-level conditional witness package, pairwise-tail contract, and argmax wrong-commit probability wrapper with no explicit htail.",
        "mathlib_routes": ["MLIB-PROBABILITY-INDEPENDENCE", "MLIB-MEASURE-INTEGRAL", "MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-CONDITIONAL-EXPECTATION"],
    },
    {
        "id": "LOCAL-LEAF-ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE",
        "leaf_ids": [
            "ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE",
        ],
        "module": "BanditRLProof.Algorithms.ETCWrongCommitRegretAssembly",
        "status": "leanCompiled",
        "declarations": [
            "ETC.pseudoRegret_actionWithCommit_choice_le_sum_gap_mul_explorationPulls_add_suffix_badGap",
        ],
        "role": "Compiled pointwise deterministic bridge from an Omega-indexed ETC commit selector to an exploration budget plus a suffix bad-gap penalty charged only on the wrong-commit branch.",
        "mathlib_routes": ["MLIB-FINSET-SUMS", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY",
        "leaf_ids": [
            "ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY",
        ],
        "module": "BanditRLProof.Algorithms.ETCExpectedRegretAssembly",
        "status": "leanCompiled",
        "declarations": [
            "ETC.lintegral_ofReal_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob",
        ],
        "role": "Compiled ENNReal.ofReal lower-integral bridge from an Omega-indexed ETC commit selector to exploration budget plus suffix bad-gap budget times an abstract wrong-commit probability upper bound.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-ETC-WRONG-COMMIT-BOCHNER-REGRET-ASSEMBLY",
        "leaf_ids": [
            "ETC-WRONG-COMMIT-BOCHNER-REGRET-ASSEMBLY",
        ],
        "module": "BanditRLProof.Algorithms.ETCExpectedRegretAssembly",
        "status": "leanCompiled",
        "declarations": [
            "ETC.integral_real_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob",
        ],
        "role": "Compiled project-local Bochner/Real expected-regret assembly for ETC wrong commits: an Omega-indexed commit selector, pointwise non-best gap bound, measurable wrong-commit event, Real probability upper bound via mu.real, nonnegative suffix bad-gap bound, and integrability of the Real pseudo-regret random variable imply an ordinary MeasureTheory.integral bound by exploration budget plus suffix penalty times pWrong. This converts the existing pointwise wrong-commit assembly into a Real expected-regret surface; it does not instantiate the concrete argmax/infinitePi probability source, prove integrability, or produce the final adaptive ETC theorem.",
        "mathlib_routes": [
            "Mathlib.MeasureTheory.Integral.Bochner.Set",
            "LOCAL-LEAF-ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE",
            "LOCAL-LEAF-ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY",
            "MLIB-MEASURE-INTEGRAL",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-ACTIONWITHCOMMIT-PSEUDOREGRET-INTEGRABILITY",
        "leaf_ids": [
            "ETC-ACTIONWITHCOMMIT-PSEUDOREGRET-INTEGRABILITY",
        ],
        "module": "BanditRLProof.Algorithms.ETCExpectedRegretAssembly",
        "status": "leanCompiled",
        "declarations": [
            "ETC.integrable_real_pseudoRegret_actionWithCommit_choice_of_measurable_commit",
        ],
        "role": "Compiled project-local Bochner regularity helper: for a finite-valued measurable ETC commit selector and any finite measure, the Real-cast finite-horizon pseudoRegret of actionWithCommit is Integrable. The proof uses Mathlib measurable_of_countable, Integrable.of_bound, and a finite Finset sum bound over all commit arms. This discharges the abstract Bochner wrapper's integrability side condition for measurable finite-arm selectors; it does not prove commit measurability or any probability/concentration bound.",
        "mathlib_routes": [
            "Mathlib.MeasureTheory.Integral.Bochner.Set",
            "LOCAL-LEAF-ETC-WRONG-COMMIT-BOCHNER-REGRET-ASSEMBLY",
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-FINSET-SUMS",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-WRONG-COMMIT-INFINITEPI-REAL-PROBABILITY-BOUND",
        "leaf_ids": [
            "ETC-WRONG-COMMIT-INFINITEPI-REAL-PROBABILITY-BOUND",
        ],
        "module": "BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly",
        "status": "leanCompiled",
        "declarations": [
            "ETC.fixedProductWrongCommitTailBudgetReal",
            "ETC.real_measure_fixedProductArgmaxCommit_ne_bestArm_le_fixedProductWrongCommitTailBudgetReal_of_infinitePi_bounded_actionMean",
        ],
        "role": "Compiled project-local Real wrong-commit probability bridge for the fixed-product argmax/infinitePi route. It converts the existing finite ENNReal fixed-product wrong-commit tail budget to a Measure.real bound via ENNReal.toReal_mono, exposing the probability supplier used by Bochner expected-regret wrappers as a standalone reusable surface. It remains fixed-product/fixed-exploration and proves no integrability, regret assembly, adaptive policy law, or final ETC theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-PROBABILITY-INDEPENDENCE",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "LOCAL-LEAF-ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-WRONG-COMMIT-INFINITEPI-BOCHNER-REGRET-ASSEMBLY",
        "leaf_ids": [
            "ETC-WRONG-COMMIT-INFINITEPI-BOCHNER-REGRET-ASSEMBLY",
        ],
        "module": "BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly",
        "status": "leanCompiled",
        "declarations": [
            "ETC.fixedProductWrongCommitTailBudget",
            "ETC.fixedProductWrongCommitTailBudgetReal",
            "ETC.fixedProductBadGapIntegralRegretBoundReal",
            "ETC.integral_real_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean",
            "ETC.integral_real_pseudoRegret_fixedProductArgmaxAction_le_fixedProductBadGapIntegralRegretBoundReal_of_infinitePi_bounded_actionMean",
        ],
        "role": "Compiled concrete fixed-product Bochner/Real expected-regret assembly for the finite argmax ETC commit oracle under an infinitePi bounded-reward source. It reuses the fixed-product Measure.real wrong-commit probability bridge, discharges integrability via the finite-valued measurable commit selector helper, and concludes an ordinary MeasureTheory.integral bound against a named bad-gap Real RHS. It now also exposes the same bad-gap endpoint with the named fixedProductArgmaxAction/fixedProductArgmaxCommit API used by the sum-gap and max-gap adapters. It remains fixed-product/fixed-exploration and keeps the explicit badGapBound contract; sum-gap Real, max-gap Real, adaptive policy laws, and the final ETC theorem remain separate.",
        "mathlib_routes": [
            "LOCAL-LEAF-ETC-WRONG-COMMIT-BOCHNER-REGRET-ASSEMBLY",
            "LOCAL-LEAF-ETC-ACTIONWITHCOMMIT-PSEUDOREGRET-INTEGRABILITY",
            "LOCAL-LEAF-ETC-WRONG-COMMIT-INFINITEPI-REAL-PROBABILITY-BOUND",
            "LOCAL-LEAF-ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE",
            "ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES",
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-PROBABILITY-INDEPENDENCE",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-WRONG-COMMIT-INFINITEPI-BOCHNER-SUMGAP-ADAPTER",
        "leaf_ids": [
            "ETC-WRONG-COMMIT-INFINITEPI-BOCHNER-SUMGAP-ADAPTER",
        ],
        "module": "BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly",
        "status": "leanCompiled",
        "declarations": [
            "ETC.fixedProductSumGapIntegralRegretBoundReal",
            "ETC.integral_real_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_sumGap_prob_of_infinitePi_bounded_actionMean",
            "ETC.integral_real_pseudoRegret_fixedProductArgmaxAction_le_fixedProductSumGapIntegralRegretBoundReal_of_infinitePi_bounded_actionMean",
        ],
        "role": "Compiled conservative sum-gap specialization of the concrete fixed-product Bochner/Real ETC expected-regret assembly. It removes the explicit badGapBound and hbadGap contracts by using the finite sum of all model gaps, FiniteBanditModel.gap_nonneg, and Finset.single_le_sum, exposes a named Real sum-gap RHS, and provides the polished fixedProductArgmaxAction wrapper. It remains fixed-product/fixed-exploration and does not prove adaptive policy laws or the final ETC theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-ETC-WRONG-COMMIT-INFINITEPI-BOCHNER-REGRET-ASSEMBLY",
            "LOCAL-LEAF-FINITE-BANDIT-MODEL-INVARIANTS",
            "LOCAL-LEAF-ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY",
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-FINSET-SUMS",
            "MLIB-ORDER-ALGEBRA",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-WRONG-COMMIT-INFINITEPI-BOCHNER-MAXGAP-ADAPTER",
        "leaf_ids": [
            "ETC-WRONG-COMMIT-INFINITEPI-BOCHNER-MAXGAP-ADAPTER",
        ],
        "module": "BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly",
        "status": "leanCompiled",
        "declarations": [
            "ETC.fixedProductMaxGapIntegralRegretBoundReal",
            "ETC.integral_real_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_maxGap_prob_of_infinitePi_bounded_actionMean",
            "ETC.integral_real_pseudoRegret_fixedProductArgmaxAction_le_fixedProductMaxGapIntegralRegretBoundReal_of_infinitePi_bounded_actionMean",
        ],
        "role": "Compiled max-gap specialization of the concrete fixed-product Bochner/Real ETC expected-regret assembly. It removes the explicit badGapBound and hbadGap contracts by using FiniteBanditModel.gap_le_maxGap and maxGap_nonneg, exposes a named Real max-gap RHS, and provides the polished fixedProductArgmaxAction wrapper. It remains fixed-product/fixed-exploration and does not prove adaptive policy laws or the final ETC theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-ETC-WRONG-COMMIT-INFINITEPI-BOCHNER-REGRET-ASSEMBLY",
            "LOCAL-LEAF-FINITE-BANDIT-MODEL-INVARIANTS",
            "LOCAL-LEAF-ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER",
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-FINSET-SUMS",
            "MLIB-ORDER-ALGEBRA",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-CANONICAL-EXPLORATION-INFINITEPI-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-CANONICAL-EXPLORATION-INFINITEPI-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly",
        "status": "leanCompiled",
        "declarations": [
            "ETC.explorationArgmaxCommit",
            "ETC.explorationArgmaxAction",
            "ETC.explorationMaxGapIntegralRegretBoundReal",
            "ETC.integral_real_pseudoRegret_explorationArgmaxAction_le_explorationMaxGapIntegralRegretBoundReal_of_infinitePi_bounded_exploreMean",
        ],
        "role": "Compiled canonical fixed-product Bochner/Real ETC endpoint whose public coordinate bounds and means are indexed directly by the round-robin exploration action ETC.exploreArm. It removes the semantically irrelevant baseCommitArm from the public source contract by fixing model.bestArm only internally and rewriting the existing fixed-product theorem through actionWithCommit_eq_exploreArm_of_lt. Contracts are probability coordinate laws, fixed spec/model, suffix r, lo/hi bounds indexed by exploration actions, positive exploration pulls, and exploration-coordinate mean identities. This is a theorem-level fixed-product/fixed-exploration expected-regret bound, not Bandits.ETC.regret_le, an adaptive environment law, or a conditional reward-law theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-ETC-WRONG-COMMIT-INFINITEPI-BOCHNER-MAXGAP-ADAPTER",
            "LOCAL-LEAF-ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE",
            "LOCAL-LEAF-ETC-ACTIONWITHCOMMIT-PSEUDOREGRET-INTEGRABILITY",
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-PROBABILITY-INDEPENDENCE",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-FINSET-SUMS",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-EMPMEAN-EXPLORATION-PREFIX-CONGRUENCE",
        "leaf_ids": [
            "ETC-EMPMEAN-EXPLORATION-PREFIX-CONGRUENCE",
        ],
        "module": "BanditRLProof.Algorithms.ETCEmpiricalMean",
        "status": "leanCompiled",
        "declarations": [
            "ETC.empMeanAtExploration_eq_of_eq_on_prefix",
        ],
        "role": "Compiled project-local finite-prefix congruence for ETC exploration empirical means. If two reward traces agree at every time strictly below spec.explorationPulls * K, then every ETC.empMeanAtExploration coordinate agrees. This is the deterministic bridge required to reconstruct a post-exploration commit score from a finite reward history. It does not construct a history-derived policy, prove action-trace alignment, introduce a probability law, or prove a conditional reward-law theorem.",
        "mathlib_routes": [
            "ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION",
            "LOCAL-LEAF-MATHLIB-FINSET-WRAPPERS",
            "MLIB-FINSET-SUMS",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-EMPMEAN-FINITE-HISTORY-RECONSTRUCTION",
        "leaf_ids": [
            "ETC-EMPMEAN-FINITE-HISTORY-RECONSTRUCTION",
        ],
        "module": "BanditRLProof.HistoryFiltration; BanditRLProof.Algorithms.ETCEmpiricalMean",
        "status": "leanCompiled",
        "declarations": [
            "History.completeRewardTrace",
            "History.completeRewardTrace_finiteRewardHistoryOfTrace_apply_of_le",
            "ETC.empMeanAtExploration_completeRewardTrace_eq_of_explorationHorizon_le",
        ],
        "role": "Compiled project-local finite reward-history reconstruction bridge for adaptive ETC. A finite reward history is completed with a default value outside its observed prefix; when the generated action at time t + 1 has a history through t and spec.explorationPulls * K <= t + 1, every fixed-commit ETC exploration empirical mean computed from that completed trace equals the ambient-trace score. It does not define the finite-history ETC policy, prove generated action-trace equality, establish measurability of that policy, or transport an adaptive reward law.",
        "mathlib_routes": [
            "LOCAL-LEAF-ETC-EMPMEAN-EXPLORATION-PREFIX-CONGRUENCE",
            "LOCAL-LEAF-MATHLIB-FINSET-WRAPPERS",
            "MLIB-FINSET-SUMS",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-GENERATED-HISTORY-POLICY-ACTION-ALIGNMENT",
        "leaf_ids": [
            "ETC-GENERATED-HISTORY-POLICY-ACTION-ALIGNMENT",
        ],
        "module": "BanditRLProof.Algorithms.ETCGeneratedHistoryPolicy",
        "status": "leanCompiled",
        "declarations": [
            "ETC.explorationArgmaxHistoryState",
            "ETC.measurable_explorationArgmaxHistoryState",
            "ETC.explorationArgmaxHistoryPolicy",
            "ETC.explorationArgmaxGeneratedAction",
            "ETC.explorationArgmaxGeneratedAction_eq_explorationArgmaxAction",
        ],
        "role": "Compiled project-local adaptive ETC action-alignment surface. It defines a measurable policy whose shifted t + 1 action explores while t + 1 is in the exploration prefix and otherwise chooses the empirical-mean argmax from a zero-completed finite reward history. Under 0 < spec.explorationPulls, its generated action generator over identity reward traces is exactly ETC.explorationArgmaxAction. The proof combines full-trace empirical-mean measurability, the finite-score-vector argmax measurability wrapper, and finite-history score reconstruction. It does not construct an adaptive reward kernel/law, prove conditional expectation or concentration, or prove Bandits.ETC.regret_le.",
        "mathlib_routes": [
            "LOCAL-LEAF-ETC-EMPMEAN-FINITE-HISTORY-RECONSTRUCTION",
            "LOCAL-LEAF-POLICY-MEASURABILITY",
            "LOCAL-LEAF-ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES",
            "MLIB-FINSET-SUMS",
            "MLIB-MEASURE-INTEGRAL",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-PARTIALTRAJ-LAW",
        "leaf_ids": [
            "ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-PARTIALTRAJ-LAW",
        ],
        "module": "BanditRLProof.Algorithms.ETCGeneratedHistoryPolicy",
        "status": "leanCompiled",
        "declarations": [
            "ETC.explorationArgmaxGeneratedActionPartialTrajectoryPairLawSource_trajMeasure",
        ],
        "role": "Compiled canonical action-dependent probability-law source for ETC. Given an initial probability measure, a Markov reward kernel, and measurable history context, it instantiates the generic RewardKernel.historyStepKernelFamily trajMeasure construction at the measurable finite-history ETC policy and packages the full generated finite-pair partialTraj condExpKernel law. Together with the compiled generated-action equality, this is a genuine kernel-trajectory law for the canonical ETC action trace. It does not identify that trajectory measure with the fixed product-coordinate source, construct an arbitrary adaptive environment law, prove conditional mean-zero/concentration under a finite bandit model, or prove Bandits.ETC.regret_le.",
        "mathlib_routes": [
            "LOCAL-LEAF-ETC-GENERATED-HISTORY-POLICY-ACTION-ALIGNMENT",
            "LOCAL-LEAF-POLICY-MEASURABILITY",
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-CONDITIONAL-EXPECTATION",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-COND-MGF-MODEL-MEAN",
        "leaf_ids": [
            "ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-COND-MGF-MODEL-MEAN",
        ],
        "module": "BanditRLProof.Algorithms.ETCGeneratedHistoryPolicy",
        "status": "leanCompiled",
        "declarations": [
            "ETC.explorationArgmaxHistory_centeredReward_succ_hasCondSubgaussianMGF_trajMeasure",
        ],
        "role": "Compiled canonical trajectory conditional-MGF specialization for ETC. A CenteredRewardKernelLaw whose context-independent mean is the finite-bandit model mean supplies Mathlib HasCondSubgaussianMGF for the successor reward centered at the arm selected by the finite-history ETC policy. The remaining explicit regularity field is a selected finite-history variance ceiling. This is a kernel-trajectory concentration foundation; it does not construct the kernel law from a finite-bandit model, identify the canonical trajectory with the product-coordinate source, derive a variance ceiling, or prove a final regret bound.",
        "mathlib_routes": [
            "LOCAL-LEAF-ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-PARTIALTRAJ-LAW",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-PROBABILITY-KERNEL",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-LAWS-MARKOV-REWARD-KERNEL",
        "leaf_ids": [
            "ETC-FINITE-ARM-LAWS-MARKOV-REWARD-KERNEL",
        ],
        "module": "BanditRLProof.RewardKernel",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.contextIndependentOfActionLaws",
            "RewardKernel.selectedMeasure_contextIndependentOfActionLaws",
        ],
        "role": "Compiled finite-arm reward-law to Markov-kernel bridge. For a countable action space with measurable singletons and an action-indexed family of probability measures, it builds a context-independent MarkovRewardKernel by Kernel.ofFunOfCountable followed by comap Prod.snd, and proves that selectedMeasure is definitionally the original action law. Fin K instantiates the action regularity directly. It does not construct centered means, boundedness, variance proxies, conditional MGF witnesses, trajectory transport, or regret.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "ProbabilityTheory.Kernel.ofFunOfCountable",
            "ProbabilityTheory.Kernel.comap",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-CENTERED-KERNEL-COND-MGF",
        "leaf_ids": [
            "ETC-FINITE-ARM-BOUNDED-CENTERED-KERNEL-COND-MGF",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ETC.finiteArmBoundedCenteredRewardKernelLaw",
            "ETC.explorationArgmaxHistory_centeredReward_succ_hasCondSubgaussianMGF_of_boundedArmLaws",
        ],
        "role": "Compiled finite-bandit model-law bridge for the canonical generated-history ETC trajectory. Per-arm probability laws with a common a.s. interval bound, Rat-to-Real a.e. measurability, and exact integrals equal to model.mean construct the context-independent CenteredRewardKernelLaw with the common Hoeffding variance proxy. The direct consumer supplies successor-reward HasCondSubgaussianMGF. The downstream full-sum leaf now aligns the initial law and combines these witnesses; this leaf itself does not identify the canonical trajectory with a target environment or prove a wrong-commit/regret theorem.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-MEASURE-INTEGRAL",
            "MeasureTheory.Integrable.of_mem_Icc",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-PAIRWISE-TAIL-CONTRACT",
        "leaf_ids": [
            "ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-PAIRWISE-TAIL-CONTRACT",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ETC.finiteArmCenteredRewardKernelLaw_of_hasSubgaussianMGF",
            "ETC.explorationArgmaxHistory_centeredReward_succ_hasCondSubgaussianMGF_of_armLaws",
            "ETC.explorationArgmaxHistory_centeredRewardCondSubGaussianWitnesses_of_armLaws",
            "ETC.explorationArgmaxHistory_pairwiseEmpMeanTailContract_of_armLaws",
        ],
        "role": "Compiled direct-MGF concentration route for canonical generated-history ETC. Per-arm Rat probability laws, exact integrals equal to model.mean, and a common caller-supplied HasSubgaussianMGF proxy construct the context-independent CenteredRewardKernelLaw without bounded support. The successor theorem transfers the selected arm MGF through the canonical historyStepKernelFamily. The witness constructor maps the initial arm law to coordinate zero, transports successor conditional MGFs across equality of the generated-history and fixed actionWithCommit filtrations during exploration, and feeds the existing centered-pairwise adapter. The endpoint is the exact PairwiseEmpMeanTailContract for exploration empirical means, with the masked one-sided fixed-horizon process and no arm union. Regularity is per-arm probability, exact Rat-to-Real model means, common sigma2, direct centered arm MGFs, measurable history context, and positive exploration pulls. Retrieval evidence is Mathlib HasSubgaussianMGF.integrable/of_map, the local centered kernel law consumer, trajMeasure_map_eval_zero, measurable-space MGF transport, and the centered-diff witness adapter. Failure policy: this leaf itself is only the concentration contract; its external condDistrib, native Real exact-regret, selected feedback-law, and least-encoded action consumers now compile downstream. The downstream source-shaped history-score bridge now compiles; faithful local field compatibility now compiles; only actual cross-toolchain LML symbol import remains.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "ProbabilityTheory.HasSubgaussianMGF.integrable",
            "ProbabilityTheory.HasSubgaussianMGF.of_map",
            "ProbabilityTheory.HasCondSubgaussianMGF.of_measurableSpace_eq",
            "RewardKernel.trajMeasure_map_eval_zero",
            "ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-CANONICAL-PER-ARM-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-CANONICAL-PER-ARM-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ETC.explorationArgmaxHistory_prob_commit_eq_arm_le_pairwiseTail_of_armLaws",
            "ETC.canonicalSubGaussianArmPairwiseTailReal",
            "ETC.canonicalSubGaussianArmPerArmIntegralRegretBoundReal",
            "ETC.real_measure_explorationArgmaxCommit_eq_arm_le_canonicalSubGaussianArmPairwiseTailReal",
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal",
        ],
        "role": "Compiled canonical generated-history ETC expected-regret theorem from direct common-sub-Gaussian finite-arm laws. The direct-MGF PairwiseEmpMeanTailContract bounds each concrete non-best explorationArgmaxCommit fiber by its matching masked one-sided pairwise tail with no arm union. ENNReal.toReal_mono converts each finite exponential tail to a named Real budget. The generic measurable-commit Bochner assembly is then bounded termwise by Finset.sum_le_sum and mul_le_mul_of_nonneg_left; gap_bestArm removes the unconstrained best-arm summand. The endpoint preserves the per-arm suffix sum and assumes no bounded support, max-gap collapse, coordinate independence, or full trajectory law. Regularity is per-arm Rat probability laws, exact integrals equal to model.mean, one common sigma2 : NNReal, direct centered HasSubgaussianMGF witnesses, measurable history context, positive exploration pulls, and finite suffix r. Retrieval evidence is the compiled direct-MGF pairwise contract, concrete argmax-fiber consumer, ENNReal.toReal_mono, measurable finite commit selector, and generic per-arm Bochner assembly. Failure policy: this canonical Rat leaf remains non-final, but downstream leaves now compile native Real exact concentration/count/regret, finite-prefix and selected feedback-law transport, least-encoded tie semantics, and three-piece action assembly. The downstream source-shaped history-score bridge now compiles; faithful local field compatibility now compiles; only actual cross-toolchain LML symbol import remains; do not report this leaf as Bandits.ETC.regret_le.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-FINSET-SUMS",
            "ENNReal.toReal_mono",
            "Finset.sum_le_sum",
            "mul_le_mul_of_nonneg_left",
            "ETC.prob_argmaxCommitOracle_eq_arm_le_pairwise_tail_of_contract",
            "ETC.integral_real_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_sum_gap_mul_commit_prob",
            "LOCAL-LEAF-ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-PAIRWISE-TAIL-CONTRACT",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_explorationPrefix_map_eq",
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_initial_map_eq_condDistrib",
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_initial_map_eq_explorationArm_condDistrib",
        ],
        "role": "Compiled external-process transport of the direct common-sub-Gaussian canonical per-arm ETC Bochner bound. Equality of exploration-prefix pushforwards first transports the canonical theorem because generated ETC regret depends only on the first spec.explorationPulls*K rewards. RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib then derives that prefix equality from the time-zero marginal and successor condDistrib laws. The practical scheduled-arm specialization fixes Context := Unit and rewrites each canonical exploration step kernel to armLaw (ETC.exploreArm spec (i+1)) using ETC.explorationArgmaxHistory_stepKernel_apply_eq_exploreArmLaw_of_lt. Regularity is an arbitrary external probability measure, a coordinate-measurable Rat reward trace, per-arm probability laws whose Bochner integrals equal model.mean, one common sigma2 : NNReal with direct centered HasSubgaussianMGF witnesses, positive exploration pulls, a finite suffix r, the scheduled arm-zero marginal, and scheduled-arm successor condDistrib identities only through exploration. No bounded support, suffix or full trajectory law, coordinate independence, arm union, caller-visible local kernel/state/context, or individual commit-fiber transport is assumed. Retrieval evidence is the canonical direct-MGF per-arm theorem, finite-prefix uniqueness, Measure.map_map, Measure.integral_map, and the exploration-step-kernel reduction. Failure policy: this Rat law surface remains non-final, but its action-history, native Real exact prefix/source-law, selected feedback-law, and least-encoded action consumers now compile. The downstream source-shaped history-score bridge now compiles; faithful local field compatibility now compiles; only actual cross-toolchain LML symbol import remains.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-MEASURE-INTEGRAL",
            "MeasureTheory.Measure.map_map",
            "MeasureTheory.integral_map",
            "RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib",
            "ETC.explorationArgmaxHistory_stepKernel_apply_eq_exploreArmLaw_of_lt",
            "LOCAL-LEAF-ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-CANONICAL-PER-ARM-BOCHNER-REGRET",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_actionRewardHistory_explorationArm_condDistrib",
        ],
        "role": "Compiled LML-shaped full action/reward-history constant-law transport for the direct common-sub-Gaussian per-arm ETC Bochner conclusion. A constant conditional law for reward zero given action zero yields the scheduled arm-zero marginal through RewardKernel.map_eq_of_condDistrib_ae_eq_const. For each exploration successor, RewardKernel.condDistrib_ae_eq_const_of_comp projects the constant scheduled-arm law conditioned on the complete finite action/reward pair history and next action through History.pairHistoryRewardProjection to the reward-only prefix; the compiled external scheduled-arm direct-MGF theorem then returns the same gap-weighted armwise RHS. Regularity is an arbitrary external probability measure, timewise measurable action and Rat reward traces, per-arm probability laws with exact model means, one common sigma2 : NNReal and direct centered HasSubgaussianMGF witnesses, positive exploration pulls, finite suffix r, the initial constant conditional law, and constant scheduled-arm successor conditional laws only through exploration. No bounded support, arm union, injectivity of the history projection, algorithm action-generation law, suffix/full trajectory law, coordinate independence, or caller-visible local trajectory kernel is assumed. Retrieval evidence is the generic constant-law marginal/coarsening APIs, finite pair-history measurability and reward projection, and the external scheduled-arm direct-MGF endpoint. Failure policy: the action-dependent Rat adapter, native Real exact prefix/conditional-law theorem, selected feedback-law adapter, and least-encoded action assembly now compile. The downstream source-shaped history-score bridge now compiles; faithful local field compatibility now compiles; only actual cross-toolchain LML symbol import remains.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-MEASURE-INTEGRAL",
            "RewardKernel.map_eq_of_condDistrib_ae_eq_const",
            "RewardKernel.condDistrib_ae_eq_const_of_comp",
            "History.measurable_finitePairHistoryOfTrace",
            "History.measurable_pairHistoryRewardProjection",
            "LOCAL-LEAF-ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-ACTION-DEPENDENT-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-ACTION-DEPENDENT-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_actionDependent_actionRewardHistory_condDistrib",
        ],
        "role": "Compiled dependency-light action-dependent selected-kernel transport for the direct common-sub-Gaussian per-arm ETC Bochner conclusion. The external process supplies a.e. identities making action zero and each exploration successor action equal to the deterministic round-robin arm, plus raw action-indexed conditional reward kernels: Kernel.ofFunOfCountable armLaw initially and contextIndependentOfActionLaws on each complete pair-history/next-action condition. RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected pushes the selector equalities to the conditioning pushforwards and converts the selected kernels to constant scheduled-arm laws; the compiled full-history direct-MGF theorem then returns the unchanged gap-weighted armwise RHS. Regularity is an arbitrary external probability measure, timewise measurable action and Rat reward traces, per-arm probability laws with exact model means, one common sigma2 : NNReal and direct centered HasSubgaussianMGF witnesses, positive exploration pulls, finite suffix r, scheduled-action a.e. identities, and raw selected-kernel condDistrib laws only through exploration. No bounded support, arm union, suffix/full trajectory law, coordinate independence, direct LML dependency, or caller-visible local trajectory kernel is assumed. Retrieval evidence is the generic selector-to-constant-law API, Mathlib ae_map_iff/measurable equality machinery, Kernel.ofFunOfCountable, contextIndependentOfActionLaws, and the full-history direct-MGF consumer. Failure policy: this dependency-light Rat law route is closed, and downstream native Real concentration, exact counts/regret, finite-prefix and selected feedback-law transport, least-encoded tie semantics, and action assembly now compile. The downstream source-shaped history-score bridge now compiles; exact LML alignment only lacks actual measurableArgmax/IsAlgEnvSeq symbol-and-field instantiation.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-MEASURE-INTEGRAL",
            "Filter.EventuallyEq",
            "MeasureTheory.ae_map_iff",
            "ProbabilityTheory.Kernel.ofFunOfCountable",
            "RewardKernel.contextIndependentOfActionLaws",
            "RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected",
            "LOCAL-LEAF-ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-CENTERED-FULL-SUM-TAIL",
        "leaf_ids": [
            "ETC-FINITE-ARM-BOUNDED-CENTERED-FULL-SUM-TAIL",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.trajMeasure_map_eval_zero",
            "ETC.explorationArgmaxHistory_centeredRewardProcess_sum_tail_ennreal_of_boundedArmLaws",
        ],
        "role": "Compiled one-sided finite-horizon Azuma-Hoeffding tail for the full canonical ETC centered reward sum at times 0 through n - 1. The trajectory initial law is the law of ETC.exploreArm spec 0; a general trajMeasure zeroth-coordinate marginal lemma transfers the bounded arm MGF to time zero, while the generated-history centered kernel law supplies successor conditional MGF witnesses. The process is strongly adapted to History.historyFiltrationSucc and uses the common interval variance proxy at every time. This total selected-reward sum is not itself a pairwise empirical-mean tail; the downstream canonical bounded-arm pairwise wrong-commit leaf now supplies that endpoint. Environment transport and regret remain separate.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-MARTINGALE-STOCHASTIC",
            "MLIB-PROBABILITY-KERNEL",
            "ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT",
        "leaf_ids": [
            "ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ProbabilityTheory.HasCondSubgaussianMGF.of_measurableSpace_eq",
            "History.historyFiltrationSucc_eq_of_action_eq_on_prefix",
            "ETC.explorationArgmaxGeneratedAction_eq_actionWithCommit_of_lt",
            "ETC.explorationArgmaxHistory_centeredRewardCondSubGaussianWitnesses_of_boundedArmLaws",
            "ETC.explorationArgmaxHistory_pairwiseEmpMeanTailContract_of_boundedArmLaws",
            "ETC.explorationArgmaxHistory_prob_wrongCommit_le_pairwiseTailSum_of_boundedArmLaws",
        ],
        "role": "Compiled canonical generated-history ETC pairwise wrong-commit route from common-bounded finite-arm laws with exact model means. Generated actions equal every fixed-commit round-robin trace through the exploration prefix; the corresponding finite-pair history filtrations agree, and a general measurable-space equality adapter transports HasCondSubgaussianMGF. The resulting reward-level witnesses feed the existing centered-diff conditional tail contract and finite non-best-arm union, yielding the actual explorationArgmaxCommit wrong-commit probability under the canonical trajMeasure. This is one-sided at the fixed exploration horizon and union-bounded. The downstream canonical Bochner leaf now converts and consumes this budget; external environment-law transport remains separate.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-MARTINGALE-STOCHASTIC",
            "LOCAL-LEAF-ETC-CENTERED-REWARD-COND-SUBGAUSS-WITNESS-CONTRACT",
            "LOCAL-LEAF-HISTORY-FILTRATION-FINITEPAIR-COMAP",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-PER-ARM-COMMIT-PROB-BOCHNER-ASSEMBLY",
        "leaf_ids": [
            "ETC-PER-ARM-COMMIT-PROB-BOCHNER-ASSEMBLY",
        ],
        "module": "BanditRLProof.Algorithms.ETCExpectedRegretAssembly",
        "status": "leanCompiled",
        "declarations": [
            "ETC.integral_real_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_sum_gap_mul_commit_prob",
        ],
        "role": "Compiled generic Bochner/Real ETC assembly that preserves the suffix charge arm by arm. For a measurable finite commit selector, the expected pseudo-regret is bounded by the round-robin exploration budget plus the finite sum of r * gap(a) times the Real probability of {commit = a}. The proof uses the deterministic phase-split gap bound, finite-valued pseudo-regret integrability, a measurable indicator decomposition of gap(commit), the project Mathlib-backed Bochner finite-sum wrapper, and integral_indicator/setIntegral_const. Regularity is only a probability measure and measurable commit selector; no wrong-event union, concentration, reward law, independence, or filtration is assumed. Failure policy: this leaf supplies the exact per-arm assembly shape but not the armwise commit-probability/tail bounds, Real/common-sub-Gaussian model port, or upstream measurableArgmax semantics; keep those as separate leaves and do not collapse this result back to maxGap times a union probability.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-FINSET-SUMS",
            "LOCAL-LEAF-EXP-FINITE-SUM",
            "LOCAL-LEAF-ETC-ACTIONWITHCOMMIT-PSEUDOREGRET-INTEGRABILITY",
            "ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND",
            "MeasureTheory.integral_indicator",
            "MeasureTheory.setIntegral_const",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-COMMIT-ARM-PAIRWISE-TAIL",
        "leaf_ids": [
            "ETC-FINITE-ARM-BOUNDED-COMMIT-ARM-PAIRWISE-TAIL",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ETC.argmaxCommitOracle_eq_arm_subset_empMean_ge_bestArm",
            "ETC.prob_argmaxCommitOracle_eq_arm_le_pairwise_tail",
            "ETC.prob_argmaxCommitOracle_eq_arm_le_pairwise_tail_of_contract",
            "ETC.explorationArgmaxHistory_prob_commit_eq_arm_le_pairwiseTail_of_boundedArmLaws",
        ],
        "role": "Compiled arm-specific concrete ETC commit-event probability route. The deterministic finite Rat argmax fiber {choose = a} is contained in the single comparison event empMean(a) >= empMean(bestArm); measure monotonicity consumes an arbitrary tail for that event; PairwiseEmpMeanTailContract supplies the non-best arm entry; and common-bounded exact-mean finite-arm laws instantiate the result under the canonical generated-history trajMeasure. The concentration source is the existing masked centered pairwise reward-difference process adapted to the fixed actionWithCommit history filtration; generated-history conditional MGF witnesses are transported to that filtration through exploration-prefix measurable-space equality. The event is one-sided at the fixed exploration horizon and no union over arms is taken. Regularity is positive exploration pulls, per-arm probability laws, common a.s. bounds, exact model means, and measurable context. Its finite Real conversion and termwise Bochner substitution are compiled downstream. Failure policy: do not reintroduce maxGap times a wrong-event union, claim external-law transport for these individual fibers, or overstate Real/common-sub-Gaussian and measurableArgmax alignment.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-CONDITIONAL-EXPECTATION",
            "MeasureTheory.measure_mono",
            "LOCAL-LEAF-ETC-PAIRWISE-TAIL-CONTRACT",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-CANONICAL-PER-ARM-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-FINITE-ARM-BOUNDED-CANONICAL-PER-ARM-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ETC.canonicalBoundedArmPairwiseTailReal",
            "ETC.canonicalBoundedArmPerArmIntegralRegretBoundReal",
            "ETC.real_measure_explorationArgmaxCommit_eq_arm_le_canonicalBoundedArmPairwiseTailReal",
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmPerArmIntegralRegretBoundReal",
        ],
        "role": "Compiled canonical bounded-Rat generated-history ETC Bochner theorem with the suffix preserved as the finite sum of each arm gap times that arm's own centered pairwise tail. ENNReal.toReal_mono converts each finite exponential tail; the generic per-arm commit-probability Bochner assembly exposes the finite sum; Finset.sum_le_sum and nonnegative gap coefficients substitute each non-best arm bound termwise; and gap_bestArm makes the unconstrained best-arm term vanish. The concentration source remains the masked centered pairwise reward-difference process adapted to the fixed actionWithCommit history filtration after exploration-prefix conditional-MGF transport, with a common interval proxy and a one-sided fixed exploration horizon; no arm union is taken. Regularity is positive exploration pulls, per-arm probability laws, common a.s. bounds, exact model means, measurable context, and finite suffix r. Retrieval evidence is the compiled armwise ENNReal tail, ENNReal.toReal_mono, the generic per-arm Bochner assembly, Finset.sum_le_sum, mul_le_mul_of_nonneg_left, gap_nonneg, and gap_bestArm. Its complete dependency-light external conditional-law adapter chain is compiled downstream. Failure policy: direct LML integration, arbitrary Real/common-sub-Gaussian rewards, and upstream measurableArgmax tie alignment remain separate.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-FINSET-SUMS",
            "ENNReal.toReal_mono",
            "Finset.sum_le_sum",
            "LOCAL-LEAF-ETC-PER-ARM-COMMIT-PROB-BOCHNER-ASSEMBLY",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-COMMIT-ARM-PAIRWISE-TAIL",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-CANONICAL-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-FINITE-ARM-BOUNDED-CANONICAL-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ETC.canonicalBoundedArmWrongCommitTailBudget",
            "ETC.canonicalBoundedArmWrongCommitTailBudgetReal",
            "ETC.canonicalBoundedArmMaxGapIntegralRegretBoundReal",
            "ETC.real_measure_explorationArgmaxCommit_ne_bestArm_le_canonicalBoundedArmWrongCommitTailBudgetReal",
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal",
        ],
        "role": "Compiled Bochner/Real expected pseudo-regret endpoint for the generated finite-history ETC action under the canonical context-independent bounded finite-arm reward-kernel trajMeasure. The finite centered pairwise wrong-commit ENNReal sum is named and converted with ENNReal.toReal_mono; coordinatewise empirical-mean measurability gives a measurable finite argmax commit and wrong event; the existing finite-valued pseudo-regret integrability theorem and generic exploration-plus-max-gap consumer finish the bound. The theorem is action-dependent and uses no coordinate independence. Downstream leaves transport this integral first from an equal exploration-prefix law and then from an explicit initial marginal plus successor conditional laws; matching the exact upstream LML statement remains separate.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-FINSET-SUMS",
            "MLIB-ORDER-ALGEBRA",
            "LOCAL-LEAF-ETC-ACTIONWITHCOMMIT-PSEUDOREGRET-INTEGRABILITY",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-PREFIX-LAW-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-FINITE-ARM-BOUNDED-EXTERNAL-PREFIX-LAW-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ETC.explorationArgmaxPrefixRegretReal",
            "ETC.measurable_explorationArgmaxPrefixRegretReal",
            "ETC.explorationArgmaxPrefixRegretReal_finiteRewardHistoryOfTrace",
            "ETC.explorationArgmaxPrefixRegretReal_finiteRewardHistoryOfTrace_generated",
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_explorationPrefix_map_eq",
        ],
        "role": "Compiled finite-horizon external-law transport for the bounded generated ETC Bochner theorem. The pseudo-regret integrand is factored through the measurable reward prefix Finset.Iic (explorationPulls * K - 1); Measure.integral_map then transports the canonical bound to any external RewardTrace Rat probability law whose exploration-prefix pushforward equals the canonical trajMeasure prefix law. The contract intentionally does not require equality of full infinite trajectory laws or any suffix reward law. The downstream external-condDistrib leaf now derives this prefix identity from an initial marginal and successor conditional laws. This leaf remains a bounded Rat/max-gap-union specialization, not the exact Real/sub-Gaussian/per-arm Bandits.ETC.regret_le theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-FINSET-SUMS",
            "MeasureTheory.integral_map",
            "History.measurable_finiteRewardHistoryOfTrace",
            "LOCAL-LEAF-ETC-EMPMEAN-FINITE-HISTORY-RECONSTRUCTION",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-CANONICAL-BOCHNER-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-PREFIX-LAW-PER-ARM-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-FINITE-ARM-BOUNDED-EXTERNAL-PREFIX-LAW-PER-ARM-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_eq_of_explorationPrefix_map_eq",
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_explorationPrefix_map_eq",
        ],
        "role": "Compiled external-law transport for the canonical bounded-Rat per-arm ETC Bochner theorem. The reusable equality factors generated ETC pseudo-regret through finiteRewardHistoryOfTrace at explorationPulls*K-1, uses measurable_explorationArgmaxPrefixRegretReal and Measure.integral_map, and proves that equal exploration-prefix pushforwards give equal regret integrals. The consumer then transports the canonical gap-weighted sum of arm-specific Real pairwise tails to any external RewardTrace Rat probability law with that prefix identity. It requires positive exploration pulls, per-arm probability laws, common a.s. bounds, exact model means, measurable context, finite suffix r, and prefix-pushforward equality; it requires neither full trajectory equality, suffix reward laws, coordinate independence, nor individual commit-fiber transport. The underlying concentration route remains the one-sided fixed-horizon masked centered pairwise process on the fixed actionWithCommit filtration after exploration-prefix MGF transport, with a common interval proxy and no arm union. Retrieval evidence is the compiled finite-prefix regret factorization, History.measurable_finiteRewardHistoryOfTrace, Measure.integral_map, and the canonical per-arm Bochner endpoint. Its initial-marginal/successor-condDistrib, scheduled exploration-arm, full action/reward-history, and action-dependent selected-kernel consumers are compiled downstream. Failure policy: direct LML integration, Real/common-sub-Gaussian support, and upstream measurableArgmax alignment remain separate.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-PROBABILITY-KERNEL",
            "MeasureTheory.integral_map",
            "History.measurable_finiteRewardHistoryOfTrace",
            "LOCAL-LEAF-ETC-EMPMEAN-FINITE-HISTORY-RECONSTRUCTION",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-CANONICAL-PER-ARM-BOCHNER-REGRET",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-BOCHNER-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_initial_map_eq_condDistrib",
        ],
        "role": "Compiled external-process per-arm ETC expected-regret theorem from an initial selected-arm marginal and successor conditional reward laws through the exploration prefix. Coordinatewise reward measurability makes the full reward trace measurable and its map a probability law. RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib uses hzero and hcond for i < explorationPulls*K-1 to identify the mapped reward prefix with the canonical trajMeasure prefix; the compiled per-arm prefix-law theorem supplies the gap-weighted armwise Real tail budget; and Measure.integral_map pulls the bound back from Measure.map reward mu to Omega. Regularity is an external probability measure, coordinate-measurable Rat reward trace, positive exploration pulls, per-arm probability laws, common a.s. interval, exact model means, measurable context, finite suffix r, the time-zero marginal, and successor condDistrib identities only before the last exploration reward. The inherited concentration process is the one-sided fixed-horizon masked centered pairwise difference on the fixed actionWithCommit filtration after exploration-prefix MGF transport, with a common interval proxy and no arm union. No suffix law, full trajectory equality, coordinate independence, or individual fiber transport is assumed. Retrieval evidence is the generic finite-prefix uniqueness theorem, Measure.map_map, Measure.integral_map, and the external prefix-law per-arm endpoint. The scheduled-arm, full action/reward-history, and action-dependent selected-kernel per-arm adapters are compiled downstream. Failure policy: direct LML integration, Real/common-sub-Gaussian support, and measurableArgmax alignment remain separate.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-MEASURE-INTEGRAL",
            "RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib",
            "MeasureTheory.Measure.map_map",
            "MeasureTheory.integral_map",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-PREFIX-LAW-PER-ARM-BOCHNER-REGRET",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-BOCHNER-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-FINITE-ARM-BOUNDED-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_initial_map_eq_explorationArm_condDistrib",
        ],
        "role": "Compiled practical scheduled exploration-arm conditional-law adapter for the canonical bounded-Rat per-arm ETC Bochner conclusion. An external probability space supplies a coordinate-measurable reward trace, the initial law armLaw (exploreArm spec 0), and condDistrib of reward i+1 given its reward prefix equal to armLaw (exploreArm spec (i+1)) for i < explorationPulls*K-1. The proof fixes Context := Unit, rewrites the local historyStepKernelFamily to the scheduled arm law with explorationArgmaxHistory_stepKernel_apply_eq_exploreArmLaw_of_lt, and consumes the compiled per-arm initial-map/successor-condDistrib theorem. Regularity is positive exploration pulls, probability arm laws, a common a.s. interval, exact model means, and finite suffix r. The inherited concentration route is the one-sided fixed-horizon masked centered pairwise process on the fixed actionWithCommit filtration after exploration-prefix MGF transport, with a common interval proxy and no arm union. Callers expose no context, local state, policy, reward kernel, trajMeasure, suffix law, full trajectory equality, or coordinate independence. Retrieval evidence is the compiled deterministic exploration step-kernel reduction and external per-arm conditional-law consumer. The full action/reward-history and action-dependent selected-kernel per-arm adapters are compiled downstream. Failure policy: direct LML integration, Real/common-sub-Gaussian support, and measurableArgmax alignment remain separate.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-MEASURE-INTEGRAL",
            "ETC.explorationArgmaxHistory_stepKernel_apply_eq_exploreArmLaw_of_lt",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-BOCHNER-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib",
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_initial_map_eq_condDistrib",
        ],
        "role": "Compiled external-process constructor and consumer for the bounded generated ETC Bochner theorem. A generic induction identifies every finite reward-prefix pushforward with the corresponding Ionescu-Tulcea trajMeasure prefix from the zeroth marginal and condDistrib of reward i+1 given the prefix through i; it uses condDistrib_ae_eq_iff_measure_eq_compProd and map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure. The ETC specialization needs those laws only for i < explorationPulls*K-1, derives the exploration-prefix equality, consumes the external-prefix theorem, and pulls the integral back from Measure.map reward mu to the original probability space. Regularity is coordinate measurability, finite/probability measures, StandardBorel and Nonempty reward target, positive exploration pulls, bounded Rat arm laws with exact means, and measurable context. No suffix law, full trajectory equality, or coordinate independence is assumed. The downstream exploration-arm condDistrib leaf now removes historyStepKernelFamily from the caller contract. Exact LML alignment still requires Real/common-sub-Gaussian rewards, argmax alignment, and per-arm gap-weighted bounds.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-MEASURE-INTEGRAL",
            "ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd",
            "ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure",
            "RewardKernel.trajMeasure_map_eval_zero",
            "MeasureTheory.Measure.map_map",
            "MeasureTheory.integral_map",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-PREFIX-LAW-BOCHNER-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-FINITE-ARM-BOUNDED-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ETC.explorationArgmaxHistory_stepKernel_apply_eq_exploreArmLaw_of_lt",
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_initial_map_eq_explorationArm_condDistrib",
        ],
        "role": "Compiled practical stationary exploration-arm conditional-law adapter and bounded generated ETC Bochner endpoint. Before the exploration horizon, unfolding explorationArgmaxHistoryPolicy, historyStepKernelFamily, and contextIndependentOfActionLaws shows that the canonical step kernel is exactly armLaw (exploreArm spec (i+1)). Therefore an external coordinate-measurable RewardTrace Rat process on any probability space inherits the canonical bounded regret theorem from the initial law armLaw (exploreArm spec 0) and condDistrib of reward i+1 given the reward prefix equal to armLaw (exploreArm spec (i+1)) for i < explorationPulls*K-1. The public endpoint fixes the irrelevant context to Unit, so callers mention no context, reconstructed state, policy kernel, reward kernel, or trajMeasure. No suffix law, full trajectory equality, or independence is assumed. The downstream action/reward-history leaf now coarsens an LML-shaped constant feedback law to this reward-prefix contract. Exact LML alignment still requires a small action-dependent-to-constant kernel adapter plus Real/common-sub-Gaussian, argmax, and per-arm RHS work.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-MEASURE-INTEGRAL",
            "RewardKernel.historyStepKernelFamily_apply",
            "RewardKernel.selectedMeasure_contextIndependentOfActionLaws",
            "ETC.explorationArgmaxHistoryPolicy",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-BOCHNER-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.condDistrib_ae_eq_const_of_comp",
            "RewardKernel.map_eq_of_condDistrib_ae_eq_const",
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_actionRewardHistory_explorationArm_condDistrib",
        ],
        "role": "Compiled LML-shaped full-history feedback-law transport and bounded ETC Bochner endpoint. The generic condDistrib coarsening theorem proves that a constant conditional target law given a fine variable remains constant after any measurable projection; its joint-law proof uses condDistrib_ae_eq_iff_measure_eq_compProd, compProd_const, map_prod_map, and needs no injectivity. A second generic theorem obtains the target marginal from a constant conditional law by the snd projection. The ETC consumer applies these to the initial reward conditioned on action zero and to reward i+1 conditioned on (finite action/reward pair history through i, action i+1), projecting to the reward-only prefix before consuming the scheduled exploration-arm theorem. Contracts are an external probability space, timewise measurable action/reward traces, constant scheduled-arm conditional laws only through exploration, positive exploration pulls, and bounded exact-mean Rat arm laws. No algorithm action-law proof, suffix feedback law, full trajectory equality, or independence is assumed. Downstream action-dependent and per-arm leaves close the dependency-light exact-seed-shaped law adapters. Direct LML import and exact Real/common-sub-Gaussian/argmax alignment remain separate.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-MEASURE-INTEGRAL",
            "ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd",
            "MeasureTheory.Measure.compProd_const",
            "MeasureTheory.Measure.map_prod_map",
            "MeasureTheory.Measure.snd_map_prodMk",
            "MeasureTheory.Measure.snd_prod",
            "History.measurable_finitePairHistoryOfTrace",
            "History.measurable_pairHistoryRewardProjection",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-BOCHNER-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_actionRewardHistory_explorationArm_condDistrib",
        ],
        "role": "Compiled LML-shaped full action/reward-history constant-law transport for the canonical bounded-Rat per-arm ETC Bochner conclusion. The initial reward has the scheduled arm-zero law conditionally on action zero. For i < explorationPulls*K-1, reward i+1 has the scheduled arm law conditionally on the complete finite action/reward pair history and next action. RewardKernel.map_eq_of_condDistrib_ae_eq_const extracts the time-zero marginal; RewardKernel.condDistrib_ae_eq_const_of_comp projects each constant fine conditional law through History.pairHistoryRewardProjection to the reward-only prefix; the compiled scheduled-arm per-arm theorem then returns the gap-weighted armwise RHS. Regularity is an arbitrary external probability space, timewise measurable action and Rat reward traces, positive exploration pulls, per-arm probability laws, a common a.s. interval, exact model means, and finite suffix r. The inherited concentration process remains the one-sided fixed-horizon masked centered pairwise difference on the fixed actionWithCommit filtration after exploration-prefix MGF transport, with a common interval proxy and no arm union. No injectivity of the projection, algorithm action-law proof, suffix feedback law, full trajectory equality, coordinate independence, or caller-visible local kernel is assumed. Retrieval evidence is the compiled generic constant-law coarsening/marginal APIs, finite pair-history measurability/projection, and scheduled-arm per-arm endpoint. The action-dependent selected-kernel per-arm adapter is compiled downstream. Failure policy: do not claim direct LML import, Real/common-sub-Gaussian support, or measurableArgmax alignment yet.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-MEASURE-INTEGRAL",
            "RewardKernel.condDistrib_ae_eq_const_of_comp",
            "RewardKernel.map_eq_of_condDistrib_ae_eq_const",
            "History.measurable_finitePairHistoryOfTrace",
            "History.measurable_pairHistoryRewardProjection",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-DEPENDENT-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-DEPENDENT-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected",
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_actionDependent_actionRewardHistory_condDistrib",
        ],
        "role": "Compiled dependency-light exact-seed-shaped action-dependent feedback-law adapter and bounded ETC endpoint. The generic selector theorem pushes selected(fine omega)=selectedValue a.e. from mu to mu.map fine using ae_map_iff and measurable equality, then rewrites any pointwise action-selected kernel to the constant selected law. The ETC specialization applies it to action zero with selected=id and Kernel.ofFunOfCountable armLaw, and to complete (action,reward)-history/next-action conditions with selected=Prod.snd and the context-independent action-law kernel. Together with a.e. exploration action identities, these raw action-dependent condDistrib laws feed the full-history constant-law consumer and the external bounded regret theorem. Contracts are an external probability space, measurable action/reward traces, action zero and successor exploration actions a.e. equal to scheduled arms, raw action-selected feedback conditional laws through exploration, positive exploration pulls, and bounded exact-mean Rat arm laws. No suffix law, full trajectory equality, or independence is assumed. The per-arm counterpart is compiled downstream. Failure policy: this is not a direct IsAlgEnvSeq import because ABRL does not depend on the newer LML toolchain; a future import wrapper only needs to translate HasCondDistrib fields and ETC.arm_of_lt into these raw hypotheses. Exact theorem alignment still requires Real/common-sub-Gaussian rewards and measurableArgmax semantics.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "Filter.EventuallyEq",
            "MeasureTheory.ae_map_iff",
            "measurableSet_eq_fun",
            "ProbabilityTheory.Kernel.ofFunOfCountable",
            "RewardKernel.contextIndependentOfActionLaws",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-DEPENDENT-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
        "leaf_ids": [
            "ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-DEPENDENT-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCFiniteArmRewardLaw",
        "status": "leanCompiled",
        "declarations": [
            "ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_actionDependent_actionRewardHistory_condDistrib",
        ],
        "role": "Compiled dependency-light exact-seed-shaped action-dependent feedback-law adapter for the canonical bounded-Rat per-arm ETC Bochner conclusion. The external process supplies a.e. identities making action zero and each exploration successor action equal to the deterministic round-robin arm, plus raw action-selected conditional reward kernels: Kernel.ofFunOfCountable armLaw at time zero and contextIndependentOfActionLaws on each complete pair-history/next-action condition. RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected pushes the selector equalities to the condition pushforwards and converts those kernels to constant scheduled-arm laws; the compiled full-history per-arm consumer then returns the gap-weighted armwise RHS. Regularity is an arbitrary external probability space, timewise measurable action and Rat reward traces, positive exploration pulls, per-arm probability laws, common a.s. bounds, exact model means, finite suffix r, scheduled-action a.e. identities, and raw selected-kernel condDistrib laws only through exploration. The inherited concentration process is the one-sided fixed-horizon masked centered pairwise reward difference on the fixed actionWithCommit filtration after exploration-prefix MGF transport, with a common interval proxy and no arm union. No suffix law, full trajectory equality, coordinate independence, direct LML dependency, or caller-visible local trajectory kernel is assumed. Retrieval evidence is the compiled generic selector-to-constant-law theorem, Mathlib ae_map_iff/measurable equality, Kernel.ofFunOfCountable, contextIndependentOfActionLaws, and full-history per-arm consumer. Failure policy: the dependency-light per-arm law route is now closed. A direct newer-toolchain IsAlgEnvSeq wrapper is optional integration work; exact LML theorem alignment still requires Real/common-sub-Gaussian rewards and measurableArgmax tie semantics, and must not be claimed from this Rat/bounded theorem.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "Filter.EventuallyEq",
            "MeasureTheory.ae_map_iff",
            "measurableSet_eq_fun",
            "ProbabilityTheory.Kernel.ofFunOfCountable",
            "RewardKernel.contextIndependentOfActionLaws",
            "RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET",
            "LOCAL-LEAF-ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-DEPENDENT-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY",
        "leaf_ids": [
            "ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY",
        ],
        "module": "BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly",
        "status": "leanCompiled",
        "declarations": [
            "ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean",
        ],
        "role": "Compiled concrete ENNReal.ofReal lower-integral ETC regret assembly for the finite argmax commit oracle under an infinite product bounded-reward source, consuming the compiled infinitePi wrong-commit probability bound.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-ETC-FIXED-PRODUCT-BADGAP-LINTEGRAL-REGRET-WRAPPER",
        "leaf_ids": [
            "ETC-FIXED-PRODUCT-BADGAP-LINTEGRAL-REGRET-WRAPPER",
        ],
        "module": "BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly",
        "status": "leanCompiled",
        "declarations": [
            "ETC.fixedProductBadGapLintegralRegretBound",
            "ETC.lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductBadGapLintegralRegretBound_of_infinitePi_bounded_actionMean",
        ],
        "role": "Compiled polished fixed product-coordinate bad-gap lower-integral ETC regret wrapper with named fixedProductArgmaxAction endpoint and named ENNReal.ofReal RHS budget. It packages the explicit badGapBound suffix contract behind fixedProductWrongCommitTailBudget, while remaining fixed-product/fixed-exploration and not a Bochner/Rat-valued expected-regret or adaptive theorem.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-ORDER-ALGEBRA", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY",
        "leaf_ids": [
            "ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY",
        ],
        "module": "BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly",
        "status": "leanCompiled",
        "declarations": [
            "ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_sumGap_prob_of_infinitePi_bounded_actionMean",
        ],
        "role": "Compiled conservative suffix adapter for the concrete argmax/infinitePi ENNReal.ofReal lower-integral ETC regret assembly, using the total finite sum of model gaps as the non-best bad-gap bound.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-ORDER-ALGEBRA", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-ETC-FIXED-PRODUCT-SUMGAP-LINTEGRAL-REGRET-WRAPPER",
        "leaf_ids": [
            "ETC-FIXED-PRODUCT-SUMGAP-LINTEGRAL-REGRET-WRAPPER",
        ],
        "module": "BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly",
        "status": "leanCompiled",
        "declarations": [
            "ETC.fixedProductSumGapLintegralRegretBound",
            "ETC.lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductSumGapLintegralRegretBound_of_infinitePi_bounded_actionMean",
        ],
        "role": "Compiled polished fixed product-coordinate conservative sum-gap lower-integral ETC regret wrapper with named fixedProductArgmaxAction endpoint and named ENNReal.ofReal RHS budget. It removes the explicit badGapBound contract through the finite sum of model gaps, while remaining fixed-product/fixed-exploration and not a Bochner/Rat-valued expected-regret or adaptive theorem.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-ORDER-ALGEBRA", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-ETC-WRONG-COMMIT-INFINITEPI-MAXGAP-LINTEGRAL-REGRET-ASSEMBLY",
        "leaf_ids": [
            "ETC-WRONG-COMMIT-INFINITEPI-MAXGAP-LINTEGRAL-REGRET-ASSEMBLY",
        ],
        "module": "BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly",
        "status": "leanCompiled",
        "declarations": [
            "ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_maxGap_prob_of_infinitePi_bounded_actionMean",
        ],
        "role": "Compiled sharper suffix adapter for the concrete argmax/infinitePi ENNReal.ofReal lower-integral ETC regret assembly, using FiniteBanditModel.maxGap as the non-best bad-gap bound.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-ORDER-ALGEBRA", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER",
        "leaf_ids": [
            "ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER",
        ],
        "module": "BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly",
        "status": "leanCompiled",
        "declarations": [
            "ETC.fixedProductArgmaxCommit",
            "ETC.fixedProductArgmaxAction",
            "ETC.fixedProductMaxGapLintegralRegretBound",
            "ETC.lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductMaxGapLintegralRegretBound_of_infinitePi_bounded_actionMean",
        ],
        "role": "Compiled polished fixed product-coordinate max-gap lower-integral ETC regret wrapper with named argmax action and named RHS budget.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-PROBABILITY-INDEPENDENCE", "MLIB-PROBABILITY-SUBGAUSSIAN", "MLIB-ORDER-ALGEBRA", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-ETC-COUNT-LEMMAS",
        "leaf_ids": [
            "ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT",
            "ETC-ROUND-ROBIN-ADD-K-COUNT",
            "ETC-ROUND-ROBIN-MUL-K-COUNT",
            "ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT",
        ],
        "module": "BanditRLProof.Algorithms.ETCCountLemmas",
        "status": "leanCompiled",
        "declarations": [
            "ETC.pullCount_exploreArm_K_eq_one",
            "ETC.pullCount_exploreArm_add_K_eq_add_one",
            "ETC.pullCount_exploreArm_mul_K_eq",
            "ETC.pullCount_exploreArm_explorationPulls_mul_K_eq",
        ],
        "role": "Compiled project-local deterministic ETC count scaffolds: first-cycle counts, full-cycle extension recurrence, m-cycle counts, and the configured exploration-horizon count adapter.",
        "mathlib_routes": ["MLIB-FINSET-SUMS", "MLIB-FINTYPE-FIN"],
    },
    {
        "id": "LOCAL-LEAF-ETC-REGRET-LEMMAS",
        "leaf_ids": [
            "ETC-EXPLORATION-REGRET-BOUND",
            "ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND",
            "ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT-BUDGET-REGRET",
            "ETC-ACTION-WITH-COMMIT-COARSE-SUFFIX-REGRET-BOUND",
            "ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET",
            "ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET",
            "ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND",
            "ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND",
        ],
        "module": "BanditRLProof.Algorithms.ETCRegretLemmas",
        "status": "leanCompiled",
        "declarations": [
            "ETC.pseudoRegret_exploreArm_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls",
            "ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls",
            "ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_suffix_count_budget",
            "ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix",
            "ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap",
            "ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_of_commitArm_eq_bestArm",
            "ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_of_commitArm_eq_bestArm",
            "ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix_gap",
        ],
        "role": "Compiled project-local deterministic ETC regret scaffolds bounding the pure round-robin exploration prefix, fixed-commit trace exploration horizon, unsimplified post-exploration fixed-commit suffix count budget, coarse uniform post-exploration suffix budget, exact fixed-commit post-horizon phase-split regret, best-arm commit no-extra-suffix regret and suffix regret bound, and the phase-split exploration-plus-suffix-gap bound.",
        "mathlib_routes": ["MLIB-FINSET-SUMS", "MLIB-FINTYPE-FIN", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-MATHLIB-FINSET-WRAPPERS",
        "module": "BanditRLProof.MathlibWrappers",
        "status": "leanCompiled",
        "declarations": [
            "pullCount_eq_finset_filter_card",
            "sumRewards_eq_finset_filter_sum",
            "pseudoRegret_eq_finset_sum",
        ],
        "role": "Compiled Mathlib-backed wrappers connecting recursive pull counts, selected reward sums, and pseudo-regret to Finset.range cardinality/sums.",
        "mathlib_routes": ["MLIB-FINSET-SUMS", "MLIB-FINTYPE-FIN", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-REGRET-DECOMPOSITION",
        "module": "BanditRLProof.RegretDecomposition",
        "status": "leanCompiled",
        "declarations": [
            "pseudoRegret_eq_finset_sum_gap_mul_pullCount",
        ],
        "role": "Compiled deterministic regret decomposition from time-indexed pseudo-regret to arm-indexed gap times pull-count sum.",
        "mathlib_routes": ["MLIB-FINSET-SUMS", "MLIB-FINTYPE-FIN", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-REGRET-COUNT-BOUNDS",
        "leaf_ids": [
            "REGRET-COUNT-BOUND",
            "REGRET-NAT-COUNT-BOUND",
            "REGRET-UNIFORM-NAT-COUNT-BOUND",
        ],
        "module": "BanditRLProof.RegretCountBounds",
        "status": "leanCompiled",
        "declarations": [
            "pseudoRegret_le_finset_sum_gap_mul_count_bound",
            "pseudoRegret_le_finset_sum_gap_mul_nat_count_bound",
            "pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound",
        ],
        "role": "Compiled deterministic scaffolds converting Rat-valued, Nat-valued, and uniform Nat pull-count bounds into gap-weighted pseudo-regret bounds.",
        "mathlib_routes": ["MLIB-FINSET-SUMS", "MLIB-FINTYPE-FIN", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-PULLCOUNT-DECOMPOSITION",
        "module": "BanditRLProof.PullCountDecomposition",
        "status": "leanCompiled",
        "declarations": [
            "finset_sum_pullCount_eq_time",
        ],
        "role": "Compiled deterministic count partition identity: finite action pull counts sum to the time horizon.",
        "mathlib_routes": ["MLIB-FINSET-SUMS", "MLIB-FINTYPE-FIN"],
    },
    {
        "id": "LOCAL-LEAF-MEASURE-FOUNDATION",
        "module": "BanditRLProof.MeasureFoundation",
        "status": "leanCompiled",
        "declarations": [
            "measurableSet_actionTrace_eval_eq",
            "measurable_actionTrace_eval_eq_indicator_const",
            "measurable_actionTrace_eval_eq_indicator_reward",
        ],
        "role": "Compiled measurable action-event, pull-indicator, and selected-reward indicator canaries for action and reward traces.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
        "leaf_ids": [
            "MEAS-HISTORY",
        ],
        "module": "BanditRLProof.HistoryFiltration",
        "status": "leanCompiled",
        "declarations": [
            "History.FiniteActionHistory",
            "History.FiniteRewardHistory",
            "History.FiniteHistory",
            "History.FinitePairHistory",
            "History.finiteActionHistoryOfTrace",
            "History.finiteRewardHistoryOfTrace",
            "History.finiteHistoryOfTrace",
            "History.finitePairHistoryOfTrace",
            "History.finiteActionHistoryOfTrace_apply",
            "History.finiteRewardHistoryOfTrace_apply",
            "History.finiteHistoryOfTrace_fst",
            "History.finiteHistoryOfTrace_snd",
            "History.finitePairHistoryOfTrace_apply",
            "History.pairHistoryRewardProjection",
            "History.pairHistoryRewardProjection_apply",
            "History.pairHistoryRewardProjection_finitePairHistoryOfTrace",
            "History.measurable_finiteActionHistory_eval",
            "History.measurable_finiteRewardHistory_eval",
            "History.measurable_finiteHistory_action_eval",
            "History.measurable_finiteHistory_reward_eval",
            "History.measurable_pairHistoryRewardProjection",
            "History.measurable_finitePairHistoryOfTrace",
            "History.measurable_finiteActionHistoryOfTrace",
            "History.measurable_finiteRewardHistoryOfTrace",
            "History.measurable_finiteHistoryOfTrace",
        ],
        "role": "Compiled finite-history product measurability surface: finite action histories, finite reward histories, paired product histories and pair-coordinate histories over Finset.Iic prefixes, measurable coordinate projections, reward projection from pair-coordinate histories, and measurable restriction maps from timewise measurable action/reward traces.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-PROBABILITY-KERNEL"],
    },
    {
        "id": "LOCAL-LEAF-HISTORY-FILTRATION",
        "leaf_ids": [
            "FILTRATION-HISTORY",
        ],
        "module": "BanditRLProof.HistoryFiltration",
        "status": "leanCompiled",
        "declarations": [
            "History.historyGenerators",
            "History.historyGenerators_mono",
            "History.historyMeasurableSpace",
            "History.historyMeasurableSpace_mono",
            "History.historyMeasurableSpace_le",
            "History.historyFiltration",
            "History.historyFiltration_apply",
            "History.measurableSet_action_mem_historyFiltration",
            "History.measurableSet_reward_mem_historyFiltration",
        ],
        "role": "Compiled history-filtration canary: past action/reward singleton events generate monotone history sigma-algebras and a Mathlib filtration, with past action and reward singleton events measurable in the current history.",
        "mathlib_routes": ["MLIB-CONDITIONAL-EXPECTATION", "MLIB-MARTINGALE-STOCHASTIC", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-HISTORY-FILTRATION-FINITEPAIR-COMAP",
        "leaf_ids": [
            "HISTORY-FILTRATION-FINITEPAIR-COMAP",
        ],
        "module": "BanditRLProof.HistoryFiltration",
        "status": "leanCompiled",
        "declarations": [
            "History.measurable_finitePairHistoryOfTrace_mem_historyFiltration_of_lt",
            "History.historyFiltration_succ_eq_comap_finitePairHistoryOfTrace",
            "History.historyFiltrationSucc_eq_comap_finitePairHistoryOfTrace",
        ],
        "role": "Compiled discrete/countable history-filtration bridge: finite pair histories are measurable at later generated-history filtration levels, History.historyFiltration ... (n + 1) is exactly the comap of History.finitePairHistoryOfTrace ... n, and the shifted History.historyFiltrationSucc ... n has the same comap form. This aligns the hand-rolled history filtration with Mathlib finite-prefix conditional-distribution surfaces; it does not prove any reward-law, condExpKernel, partialTraj, or trajectory transport identity.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
            "LOCAL-LEAF-HISTORY-FILTRATION",
            "LOCAL-LEAF-HISTORY-ADAPTED-COORDINATES",
        ],
    },
    {
        "id": "LOCAL-LEAF-HISTORY-ADAPTED-COORDINATES",
        "leaf_ids": [
            "ADAPTED-ACTION",
        ],
        "module": "BanditRLProof.HistoryFiltration",
        "status": "leanCompiled",
        "declarations": [
            "History.measurable_action_mem_historyFiltration_of_lt",
            "History.measurable_reward_mem_historyFiltration_of_lt",
        ],
        "role": "Compiled countable/discrete adapted-coordinate canary: past action and reward coordinates are measurable with respect to the generated history filtration. This is not a full policy-predictability or conditional reward-law theorem.",
        "mathlib_routes": ["MLIB-CONDITIONAL-EXPECTATION", "MLIB-MARTINGALE-STOCHASTIC", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-POLICY-MEASURABILITY",
        "leaf_ids": [
            "MEAS-POLICY",
        ],
        "module": "BanditRLProof.PolicyMeasurability",
        "status": "leanCompiled",
        "declarations": [
            "Policy.MeasurablePolicy",
            "Policy.measurable_action_of_measurable_state",
            "Policy.measurable_action_mem_filtration_of_measurable_state",
            "Policy.measurable_action_mem_historyFiltration_of_measurable_state",
        ],
        "role": "Compiled policy measurability/predictability surface: a measurable policy applied to a measurable history/context state yields a measurable action, including arbitrary-filtration and generated-history-filtration specializations. This does not construct kernels, trajectory laws, reward laws, or final adaptive regret.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-CONDITIONAL-EXPECTATION"],
    },
    {
        "id": "LOCAL-LEAF-POLICY-GENERATED-ACTION-TRACE-MEASURABILITY",
        "leaf_ids": [
            "POLICY-GENERATED-ACTION-TRACE-MEASURABILITY",
        ],
        "module": "BanditRLProof.PolicyMeasurability",
        "status": "leanCompiled",
        "declarations": [
            "Policy.generatedActionTrace",
            "Policy.measurable_generatedActionTrace_eval_of_measurable_state",
            "Policy.measurable_generatedActionTrace_eval_mem_filtration_of_measurable_state",
            "Policy.measurable_generatedActionTrace_eval_mem_historyFiltration_of_measurable_state",
            "Policy.generatedActionTraceSucc",
            "Policy.generatedActionTraceSucc_zero",
            "Policy.generatedActionTraceSucc_succ",
            "Policy.generatedActionTraceSucc_succ_eq",
            "Policy.measurable_generatedActionTraceSucc_eval_of_measurable_state",
            "Policy.measurable_generatedActionTraceSucc_succ_mem_filtration_of_measurable_state",
        ],
        "role": "Compiled policy-generated action trace measurability surface: applying a measurable policy to a time-indexed measurable state process yields an action trace whose coordinates are measurable in the ambient, arbitrary-filtration, and generated-history-filtration senses; the shifted time-indexed trace has coordinate t+1 selected by policy t, exposes the pointwise equality, and is predictable from F_t when the state is F_t-measurable. This is a KERNEL-POLICY-BIND precursor, not a kernel bind, reward law, or trajectory-law construction.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-CONDITIONAL-EXPECTATION"],
    },
    {
        "id": "LOCAL-LEAF-REWARD-KERNEL-CONTRACT",
        "leaf_ids": [
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.RewardKernel",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.MarkovRewardKernel",
            "RewardKernel.ofKernel",
            "RewardKernel.measurable_kernel",
            "RewardKernel.measurable_apply_of_measurable_index",
            "RewardKernel.measurable_eventProbability_of_measurable_index",
            "RewardKernel.isProbabilityMeasure_apply",
            "RewardKernel.apply_univ",
            "RewardKernel.const",
            "RewardKernel.deterministic",
            "RewardKernel.selectedMeasure",
            "RewardKernel.isProbabilityMeasure_selectedMeasure",
            "RewardKernel.selectedMeasure_univ",
            "RewardKernel.measurable_selectedMeasure_of_measurable",
            "RewardKernel.measurable_selectedEventProbability_of_measurable",
            "RewardKernel.measurable_selectedMeasure_of_policy_state",
            "RewardKernel.measurable_selectedEventProbability_of_policy_state",
        ],
        "role": "Compiled reward-kernel contract surface: wraps Mathlib's Markov kernel API as an arm/context-indexed reward law, exposes selected-measure probability and event-probability measurability, and connects measurable policy/state actions to context/action reward-kernel lookup. This is a KERNEL-POLICY-BIND precursor, not kernel bind, trajectory-law, or conditional reward-law construction.",
        "mathlib_routes": ["MLIB-PROBABILITY-KERNEL", "MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-POSTERIOR-KERNEL-CONTRACT",
        "leaf_ids": [
            "POSTERIOR-KERNEL",
        ],
        "module": "BanditRLProof.PosteriorKernel",
        "status": "leanCompiled",
        "declarations": [
            "PosteriorKernel.MarkovPosteriorKernel",
            "PosteriorKernel.ofKernel",
            "PosteriorKernel.ofMeasureSelector",
            "PosteriorKernel.ofMeasureSelector_apply",
            "PosteriorKernel.ofCountableHistorySelector",
            "PosteriorKernel.ofCountableHistorySelector_apply",
            "PosteriorKernel.measurable_kernel",
            "PosteriorKernel.measurable_apply_of_measurable_history",
            "PosteriorKernel.measurable_eventProbability_of_measurable_history",
            "PosteriorKernel.isProbabilityMeasure_apply",
            "PosteriorKernel.apply_univ",
            "PosteriorKernel.BayesianPosteriorSurface",
            "PosteriorKernel.BayesianPosteriorSurface.posterior_isProbabilityMeasure_apply",
        ],
        "role": "Compiled posterior-kernel contract surface: wraps Mathlib's Markov kernel API as a posterior distribution over environments indexed by histories, builds kernels from measurable posterior-measure selectors or countable/discrete history selectors, exposes selected posterior probability and event-probability measurability, and records a prior/likelihood/posterior surface. This is not a Bayes-rule proof, regular conditional distribution existence theorem, Thompson probability-matching identity, or Bayesian regret theorem.",
        "mathlib_routes": ["MLIB-PROBABILITY-KERNEL", "MLIB-CONDITIONAL-EXPECTATION"],
    },
    {
        "id": "LOCAL-LEAF-TS-POSTERIOR-ACTION-IDENTITY-LEDGER",
        "leaf_ids": [
            "TS-PROB-MATCH",
            "POSTERIOR-KERNEL",
        ],
        "module": "BanditRLProof.Algorithms.Thompson",
        "status": "leanCompiled",
        "declarations": [
            "Thompson.PosteriorActionIdentityLedger",
            "Thompson.PosteriorActionIdentityLedger.actionKernel_apply_eq_posteriorBest_map",
            "Thompson.PosteriorActionIdentityLedger.actionKernel_apply_singleton_eq_posteriorBest_preimage",
        ],
        "role": "Compiled Thompson posterior-action identity ledger: packages a posterior kernel over environments, a Thompson action kernel, a measurable environment-to-best-action map, and the event-level probability-matching equality saying the action kernel equals the posterior pushforward by bestAction. It exposes event-level and singleton action-probability consumers. This is not a Bayes-rule proof, posterior sampler construction, LML import, or Bayesian regret theorem.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-POSTERIOR-KERNEL-CONTRACT",
            "LML-TS-POSTERIOR-ACTION",
        ],
    },
    {
        "id": "LOCAL-LEAF-TS-POSTERIOR-BEST-ACTION-MEASURABILITY",
        "leaf_ids": [
            "TS-PROB-MATCH",
            "POSTERIOR-KERNEL",
        ],
        "module": "BanditRLProof.Algorithms.Thompson",
        "status": "leanCompiled",
        "declarations": [
            "Thompson.bestAction_measurable_of_countable_env",
            "Thompson.PosteriorActionIdentityLedger.ofCountableEnv",
        ],
        "role": "Compiled Thompson posterior best-action regularity leaf: on a countable singleton-measurable environment space, any environment-to-action bestAction selector is measurable, and the posterior-action identity ledger can be built without separately supplying that measurability field. This discharges the finite/countable posterior best-action measurability side condition for the local probability-matching ledger, while still assuming the event-level posterior action law and not proving Bayes' rule, constructing the posterior sampler, importing LML, or proving Bayesian regret.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "Mathlib.MeasureTheory.MeasurableSpace.Constructions",
            "LOCAL-LEAF-POSTERIOR-KERNEL-CONTRACT",
            "LOCAL-LEAF-TS-POSTERIOR-ACTION-IDENTITY-LEDGER",
            "LML-TS-POSTERIOR-ACTION",
        ],
    },
    {
        "id": "LOCAL-LEAF-POLICY-REWARD-ONE-STEP-KERNEL-COMPOSITION",
        "leaf_ids": [
            "POLICY-REWARD-ONE-STEP-KERNEL-COMPOSITION",
        ],
        "module": "BanditRLProof.RewardKernel",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.policyContextStateIndex",
            "RewardKernel.measurable_policyContextStateIndex",
            "RewardKernel.composePolicy",
            "RewardKernel.composePolicy_kernel_apply",
            "RewardKernel.isMarkovKernel_composePolicy",
            "RewardKernel.measurable_composePolicy_eventProbability",
        ],
        "role": "Compiled one-step policy/reward kernel composition surface: a measurable policy maps context/state pairs to context/action reward-kernel indices, and the resulting context/state-indexed reward law is again a Mathlib Markov kernel with measurable event probabilities. This is a KERNEL-POLICY-BIND precursor, not finite-horizon trajectory-law or Ionescu-Tulcea assembly.",
        "mathlib_routes": ["MLIB-PROBABILITY-KERNEL", "LOCAL-LEAF-POLICY-MEASURABILITY", "LOCAL-LEAF-REWARD-KERNEL-CONTRACT"],
    },
    {
        "id": "LOCAL-LEAF-POLICY-REWARD-IIC-HISTORY-PARTIAL-TRAJECTORY",
        "leaf_ids": [
            "POLICY-REWARD-IIC-HISTORY-PARTIAL-TRAJECTORY",
        ],
        "module": "BanditRLProof.RewardKernel",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.historyStepRewardKernel",
            "RewardKernel.historyStepKernelFamily",
            "RewardKernel.historyStepKernelFamily_apply",
            "RewardKernel.isMarkovKernel_historyStepKernelFamily",
            "RewardKernel.measurable_historyStepKernelFamily_eventProbability",
            "RewardKernel.partialTrajectoryKernel",
            "RewardKernel.isMarkovKernel_partialTrajectoryKernel",
            "RewardKernel.measurable_partialTrajectoryKernel_eventProbability",
            "RewardKernel.partialTrajectoryKernel_succ_next_map",
            "RewardKernel.partialTrajectoryKernel_succ_next_map_apply",
        ],
        "role": "Compiled finite-prefix reward-history trajectory surface: time-indexed measurable context/state extractors plus measurable policies and a context/action reward kernel produce Mathlib Ionescu-Tulcea-compatible step kernels over Finset.Iic reward histories, Mathlib partialTraj assembles finite-prefix Markov trajectory kernels with measurable event probabilities, and the one-step partialTraj next-coordinate marginal is exposed as the configured history-step reward kernel. This is a KERNEL-POLICY-BIND precursor, not a full bandit action/reward trajectory law, conditional reward-law transfer, or final adaptive theorem.",
        "mathlib_routes": ["MLIB-PROBABILITY-KERNEL", "LOCAL-LEAF-POLICY-REWARD-ONE-STEP-KERNEL-COMPOSITION", "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj"],
    },
    {
        "id": "LOCAL-LEAF-POLICY-REWARD-ACTION-REWARD-PARTIAL-TRAJECTORY",
        "leaf_ids": [
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.RewardKernel",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.policyActionOfContextState",
            "RewardKernel.measurable_policyActionOfContextState",
            "RewardKernel.policyActionKernel",
            "RewardKernel.policyActionKernel_apply",
            "RewardKernel.isMarkovKernel_policyActionKernel",
            "RewardKernel.composePolicyActionReward",
            "RewardKernel.composePolicyActionReward_kernel",
            "RewardKernel.isMarkovKernel_composePolicyActionReward",
            "RewardKernel.measurable_composePolicyActionReward_eventProbability",
            "RewardKernel.composePolicyActionReward_reward_event",
            "RewardKernel.composePolicyActionReward_kernel_apply_eq_map_prod_mk",
            "RewardKernel.actionRewardHistoryStepKernel",
            "RewardKernel.actionRewardHistoryStepKernelFamily",
            "RewardKernel.actionRewardHistoryStepKernelFamily_apply",
            "RewardKernel.isMarkovKernel_actionRewardHistoryStepKernelFamily",
            "RewardKernel.measurable_actionRewardHistoryStepKernelFamily_eventProbability",
            "RewardKernel.actionRewardHistoryStepKernelFamily_reward_event",
            "RewardKernel.actionRewardHistoryStepKernelFamily_apply_eq_map_prod_mk",
            "RewardKernel.actionRewardPartialTrajectoryKernel",
            "RewardKernel.isMarkovKernel_actionRewardPartialTrajectoryKernel",
            "RewardKernel.measurable_actionRewardPartialTrajectoryKernel_eventProbability",
            "RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map",
            "RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map_apply",
            "RewardKernel.actionRewardPartialTrajectoryKernel_succ_extend_map_apply",
        ],
        "role": "Compiled finite-prefix action/reward trajectory surface for KERNEL-POLICY-BIND: a measurable policy gives a deterministic action kernel, product with the selected reward kernel gives a one-step (Action x Reward) Markov kernel, the full one-step/history-step action/reward laws are exposed as fixed-policy-action pushforwards of selected reward laws, the reward marginal of the one-step and history-step action/reward kernels is the selected reward law, Mathlib partialTraj assembles finite-prefix action/reward pair trajectory kernels with measurable event probabilities, the one-step partialTraj next-coordinate marginal is exposed as the configured action/reward history-step kernel, and the one-step full-prefix kernel is exposed as the history-step kernel pushed through History.extendPairHistorySucc. CondExpKernel identification, Bayes-rule posterior identification, and final adaptive theorems remain separate leaves.",
        "mathlib_routes": ["MLIB-PROBABILITY-KERNEL", "LOCAL-LEAF-POLICY-REWARD-ONE-STEP-KERNEL-COMPOSITION", "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY", "Mathlib.Probability.Kernel.Composition.Prod", "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj"],
    },
    {
        "id": "LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-NEXT-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
            "POLICY-REWARD-IIC-HISTORY-PARTIAL-TRAJECTORY",
        ],
        "module": "BanditRLProof.RewardKernel",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.partialTrajectoryKernel_succ_next_map",
            "RewardKernel.partialTrajectoryKernel_succ_next_map_apply",
            "RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map",
            "RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map_apply",
        ],
        "role": "Compiled Mathlib-backed partialTraj one-step next-coordinate marginal wrappers: for both reward-history and action/reward pair trajectories, mapping the one-step extension kernel from n to n+1 along the coordinate n+1 recovers the configured history-step kernel. This names the local trajectory-kernel side of the future generated-history condExpKernel pair-law identity, but it does not construct that condExpKernel identity.",
        "mathlib_routes": [
            "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj",
            "LOCAL-LEAF-POLICY-REWARD-IIC-HISTORY-PARTIAL-TRAJECTORY",
            "LOCAL-LEAF-POLICY-REWARD-ACTION-REWARD-PARTIAL-TRAJECTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-EXTEND-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
            "MEAS-HISTORY",
        ],
        "module": "BanditRLProof.RewardKernel",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.actionRewardPartialTrajectoryKernel_succ_extend_map_apply",
        ],
        "role": "Compiled Mathlib-backed partialTraj one-step full-extension wrapper: for finite action/reward pair trajectories, the n-to-n+1 partialTraj measure at a frozen prefix is exactly the history-step (Action x Reward) kernel pushed through History.extendPairHistorySucc. This supplies the trajectory-kernel side of the extension-map COND-EXPECT-REWARD route, but it does not prove the generated-history condExpKernel/partialTraj law.",
        "mathlib_routes": [
            "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-HISTORY-SUCC-EXTEND-HOOKUP",
            "LOCAL-LEAF-POLICY-REWARD-ACTION-REWARD-PARTIAL-TRAJECTORY",
            "LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-NEXT-MAP",
        ],
    },
    {
        "id": "LOCAL-LEAF-POLICY-REWARD-TRAJMEASURE-CONDDISTRIB-HISTORYSTEP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.RewardKernel",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.instIsMarkovKernel_actionRewardHistoryStepKernelFamily",
            "RewardKernel.actionRewardHistoryStepKernelFamily_condDistrib_trajMeasure",
        ],
        "role": "Compiled Mathlib-backed canonical trajectory-measure conditional law: for the action/reward history-step kernel family, Mathlib trajMeasure has regular conditional distribution of the next pair given the finite prefix equal a.e. to RewardKernel.actionRewardHistoryStepKernelFamily. This is the canonical Ionescu-Tulcea source side of the COND-EXPECT-REWARD law-identification route; it does not identify an arbitrary ambient condExpKernel over Omega, transport History.historyFiltrationSucc, or prove the final adaptive theorem.",
        "mathlib_routes": [
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
            "Mathlib.Probability.Kernel.CondDistrib",
            "LOCAL-LEAF-POLICY-REWARD-ACTION-REWARD-PARTIAL-TRAJECTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-POLICY-REWARD-TRAJMEASURE-REWARD-CONDDISTRIB",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.RewardKernel",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.actionRewardHistoryStepKernelFamily_reward_condDistrib_trajMeasure",
        ],
        "role": "Compiled Mathlib-backed canonical reward-marginal trajectory conditional law: for the action/reward history-step kernel family, condDistrib of the next reward coordinate given the finite pair prefix is a.e. the Prod.snd pushforward of RewardKernel.actionRewardHistoryStepKernelFamily. It is obtained from Mathlib condDistrib_comp plus the local next-pair trajMeasure law; it still does not identify an arbitrary ambient condExpKernel over Omega, transport History.historyFiltrationSucc, or prove the final adaptive theorem.",
        "mathlib_routes": [
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
            "Mathlib.Probability.Kernel.CondDistrib",
            "LOCAL-LEAF-POLICY-REWARD-TRAJMEASURE-CONDDISTRIB-HISTORYSTEP",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
        ],
    },
    {
        "id": "LOCAL-LEAF-POLICY-REWARD-TRAJMEASURE-ACTION-CONDDISTRIB",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.RewardKernel",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.actionRewardHistoryStepKernelFamily_action_condDistrib_trajMeasure",
        ],
        "role": "Compiled Mathlib-backed canonical action-marginal trajectory conditional law: for the action/reward history-step kernel family, condDistrib of the next action coordinate given the finite pair prefix is a.e. the Prod.fst pushforward of RewardKernel.actionRewardHistoryStepKernelFamily. It is obtained from Mathlib condDistrib_comp plus the local next-pair trajMeasure law; it still does not identify an arbitrary ambient condExpKernel over Omega, transport History.historyFiltrationSucc, or prove the final adaptive theorem.",
        "mathlib_routes": [
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
            "Mathlib.Probability.Kernel.CondDistrib",
            "LOCAL-LEAF-POLICY-REWARD-TRAJMEASURE-CONDDISTRIB-HISTORYSTEP",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
        ],
    },
    {
        "id": "LOCAL-LEAF-POLICY-REWARD-TRAJMEASURE-SELECTED-ACTION-CONDDISTRIB",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.RewardKernel",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.actionRewardHistoryStepKernelFamily_selectedAction_condDistrib_trajMeasure",
        ],
        "role": "Compiled Mathlib-backed canonical selected-action trajectory conditional law: for the action/reward history-step kernel family, condDistrib of the next action coordinate given the finite pair prefix is a.e. the Dirac law at the policy-selected action determined by the frozen prefix. It rewrites the canonical action-marginal law through RewardKernel.actionRewardHistoryStepKernelFamily_action_map; it still does not identify an arbitrary ambient condExpKernel over Omega, transport History.historyFiltrationSucc, or prove the final adaptive theorem.",
        "mathlib_routes": [
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
            "Mathlib.Probability.Kernel.CondDistrib",
            "LOCAL-LEAF-POLICY-REWARD-TRAJMEASURE-ACTION-CONDDISTRIB",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
        ],
    },
    {
        "id": "LOCAL-LEAF-POLICY-REWARD-TRAJMEASURE-SELECTED-REWARD-CONDDISTRIB",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.RewardKernel",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.actionRewardHistoryStepKernelFamily_selectedMeasure_condDistrib_trajMeasure",
        ],
        "role": "Compiled Mathlib-backed canonical selected-reward trajectory conditional law: for the action/reward history-step kernel family, condDistrib of the next reward coordinate given the finite pair prefix is a.e. the selected context/action reward measure determined by the frozen prefix and policy action. It rewrites the canonical reward-marginal law through RewardKernel.actionRewardHistoryStepKernelFamily_reward_map; it still does not identify an arbitrary ambient condExpKernel over Omega, transport History.historyFiltrationSucc, or prove the final adaptive theorem.",
        "mathlib_routes": [
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
            "Mathlib.Probability.Kernel.CondDistrib",
            "LOCAL-LEAF-POLICY-REWARD-TRAJMEASURE-REWARD-CONDDISTRIB",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
        ],
    },
    {
        "id": "LOCAL-LEAF-KERNEL-CENTERED-REWARD-LAW-TRANSFER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.RewardKernel",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.CenteredRewardKernelLaw",
            "RewardKernel.composePolicyActionReward_reward_event",
            "RewardKernel.composePolicy_centeredReward_integrable",
            "RewardKernel.composePolicy_centeredReward_integral_eq_zero",
            "RewardKernel.composePolicy_centeredReward_hasSubgaussianMGF",
            "RewardKernel.historyStepKernelFamily_centeredReward_integrable",
            "RewardKernel.historyStepKernelFamily_centeredReward_integral_eq_zero",
            "RewardKernel.historyStepKernelFamily_centeredReward_hasSubgaussianMGF",
            "RewardKernel.actionRewardHistoryStepKernelFamily_reward_event",
        ],
        "role": "Compiled kernel-level centered-reward law transfer surface for COND-EXPECT-REWARD: a pointwise selected reward-law contract packages centered integrability, zero integral, and HasSubgaussianMGF for each context/action reward law; policy-composed and finite reward-history step kernels inherit those facts; the action/reward product step kernels expose the selected reward law as their reward marginal. This is not a condExpKernel identification for partialTraj or a final adaptive theorem.",
        "mathlib_routes": ["MLIB-PROBABILITY-KERNEL", "MLIB-PROBABILITY-SUBGAUSSIAN", "Mathlib.Probability.Kernel.Composition.Prod"],
    },
    {
        "id": "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.RewardKernel",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.composePolicyActionReward_reward_map",
            "RewardKernel.actionRewardHistoryStepKernelFamily_reward_map",
            "RewardKernel.composePolicyActionReward_action_map",
            "RewardKernel.actionRewardHistoryStepKernelFamily_action_map",
        ],
        "role": "Compiled measure-level action/reward marginal map-law transfer surface for COND-EXPECT-REWARD: the one-step action/reward product kernel and the finite-history action/reward step kernel both push forward along Prod.snd to the selected context/action reward measure, and along Prod.fst to the Dirac law at the policy-selected action. This upgrades the earlier event-level reward marginal wrappers to Measure.map equalities and exposes the deterministic action side of the product kernel, matching the shape consumed by condExpKernel map-law consumers, but it still does not prove partialTraj/history-to-condExpKernel identification, frozen-past conditions, arbitrary adaptive policy predictability, or final adaptive ETC/UCB theorems.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "LOCAL-LEAF-KERNEL-CENTERED-REWARD-LAW-TRANSFER",
            "Mathlib.Probability.Kernel.Composition.Prod",
            "Mathlib.MeasureTheory.Measure.Map",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-CONDEXPKERNEL-ZERO",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_integral_eq_zero",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_condExpKernel_integral_eq_zero",
        ],
        "role": "Compiled narrow condExpKernel-to-condExp bridge for COND-EXPECT-REWARD: if the conditional-expectation kernel integral of a centered reward is zero trim-a.e., then the ordinary conditional expectation is zero, with a succ-indexed centered-reward specialization. This consumes, but does not construct, the partialTraj/history-to-condExpKernel reward-law identification; arbitrary policy predictability and final adaptive ETC/UCB theorems remain open.",
        "mathlib_routes": ["MLIB-CONDITIONAL-EXPECTATION", "MLIB-PROBABILITY-KERNEL", "Mathlib.Probability.Independence.Conditional"],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-CONDDISTRIB-TO-CONDEXPKERNEL-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_countable",
            "ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_countable_trim",
        ],
        "role": "Compiled Mathlib-backed bridge from a regular conditional distribution law to a conditional-expectation-kernel pushforward law on countable targets: if condDistrib X Y mu is a.e. a kernel k over the conditioning variable, then condExpKernel mu (comap Y) pushed forward by X is a.e. k (Y omega). The trim companion proves the same equality under mu.trim hY.comap_le by showing singleton event-probability functions are conditioning-measurable and applying ae_eq_trim_of_measurable before singleton measure ext. It consumes a condDistrib identification and does not construct a trajectory law or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.Probability.Kernel.Condexp",
            "Mathlib.Probability.Kernel.CondDistrib",
            "Mathlib.MeasureTheory.Measure.Dirac",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-PAIR-CONDEXPKERNEL-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_condExpKernel_map_trajMeasure",
        ],
        "role": "Compiled canonical next-pair trajMeasure condExpKernel map law: for the Mathlib trajectory measure generated by RewardKernel.actionRewardHistoryStepKernelFamily, condExpKernel conditioned on the finite pair prefix and pushed forward by the next (Action, Reward) coordinate is a.e. the configured history-step kernel at that prefix. This is still canonical trajMeasure only; arbitrary ambient Omega/History.historyFiltrationSucc transport remains open.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-CONDDISTRIB-TO-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-POLICY-REWARD-TRAJMEASURE-CONDDISTRIB-HISTORYSTEP",
            "Mathlib.Probability.Kernel.Condexp",
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-ACTION-CONDEXPKERNEL-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_action_condExpKernel_map_trajMeasure",
        ],
        "role": "Compiled canonical next-action trajMeasure condExpKernel map law: for the Mathlib trajectory measure generated by RewardKernel.actionRewardHistoryStepKernelFamily, condExpKernel conditioned on the finite pair prefix and pushed forward by the next action coordinate is a.e. the Dirac law at the policy-selected action. It is the Prod.fst projection of the canonical next-pair law through RewardKernel.actionRewardHistoryStepKernelFamily_action_map; arbitrary ambient Omega/History.historyFiltrationSucc transport remains open.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-PAIR-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "Mathlib.Probability.Kernel.Condexp",
            "Mathlib.MeasureTheory.Measure.Map",
            "Mathlib.MeasureTheory.Measure.Dirac",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-ACTION-MARGINAL-CONDEXPKERNEL-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_actionMarginal_condExpKernel_map_trajMeasure",
        ],
        "role": "Compiled direct action-marginal canonical trajMeasure condExpKernel map law: applying the countable-target condDistrib-to-condExpKernel bridge to the next action coordinate and the canonical action condDistrib law yields the Prod.fst marginal of RewardKernel.actionRewardHistoryStepKernelFamily. This is the action-side analogue of the reward-marginal canonical condExpKernel law and only requires Countable Action; arbitrary ambient Omega/History.historyFiltrationSucc transport remains open.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-CONDDISTRIB-TO-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-POLICY-REWARD-TRAJMEASURE-ACTION-CONDDISTRIB",
            "Mathlib.Probability.Kernel.Condexp",
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-ACTION-CONDEXPKERNEL-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_selectedAction_condExpKernel_map_trajMeasure",
        ],
        "role": "Compiled direct selected-action canonical trajMeasure condExpKernel map law: applying the countable-target condDistrib-to-condExpKernel bridge to the next action coordinate and the canonical action condDistrib law yields the Dirac law at the policy-selected action. This route only requires the target Action to be countable, rather than the whole (Action, Reward) pair; arbitrary ambient Omega/History.historyFiltrationSucc transport remains open.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-ACTION-MARGINAL-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-CONDDISTRIB-TO-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-POLICY-REWARD-TRAJMEASURE-ACTION-CONDDISTRIB",
            "LOCAL-LEAF-POLICY-REWARD-TRAJMEASURE-SELECTED-ACTION-CONDDISTRIB",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "Mathlib.Probability.Kernel.Condexp",
            "Mathlib.MeasureTheory.Measure.Dirac",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-ACTION-CONDEXPKERNEL-AE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.eventuallyEq_const_of_map_eq_dirac",
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_selectedAction_condExpKernel_ae_trajMeasure",
        ],
        "role": "Compiled canonical selected-action condExpKernel a.e. law: a reusable Dirac-pushforward helper turns Measure.map X mu = dirac x into X =ᵐ[mu] const x, and the canonical trajMeasure selected-action condExpKernel map law is converted into the conditional a.e. next-action equality required by the next-pair split-law builder. This supplies the action side on canonical Ionescu-Tulcea trajectories; arbitrary ambient Omega/History.historyFiltrationSucc transport remains open.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-ACTION-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER",
            "Mathlib.MeasureTheory.Measure.Map",
            "Mathlib.MeasureTheory.Measure.Dirac",
            "Mathlib.Probability.Kernel.Condexp",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-EXTEND-CONDEXPKERNEL-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_condExpKernel_map_trajMeasure",
        ],
        "role": "Compiled canonical extension-map trajMeasure condExpKernel law: for the Mathlib trajectory measure generated by RewardKernel.actionRewardHistoryStepKernelFamily, the canonical next-pair condExpKernel map law pushed through History.extendPairHistorySucc yields the one-step RewardKernel.actionRewardPartialTrajectoryKernel extension-map surface at the frozen finite prefix. This aligns the canonical source with existing extension-map consumers but still does not transport an arbitrary ambient Omega/History.historyFiltrationSucc process.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-PAIR-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-EXTEND-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
            "Mathlib.Probability.Kernel.Condexp",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-PREFIX-CONDEXPKERNEL-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_prefix_condExpKernel_map_trajMeasure",
        ],
        "role": "Compiled canonical full-prefix trajMeasure condExpKernel law: the canonical extension-map law plus condExpKernel frozen-prefix evidence rewrites the pushforward to Preorder.frestrictLe (n + 1), yielding the one-step RewardKernel.actionRewardPartialTrajectoryKernel surface on the full finite prefix. This is still canonical trajMeasure only; arbitrary ambient Omega/History.historyFiltrationSucc transport remains open.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-EXTEND-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CONDEXPKERNEL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
            "Mathlib.Probability.Kernel.Condexp",
            "Mathlib.MeasureTheory.Measure.Trim",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-FINITEPAIRHISTORY-CONDEXPKERNEL-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_finitePairHistoryOfTrace_condExpKernel_map_trajMeasure",
        ],
        "role": "Compiled canonical trajMeasure notation-alignment wrapper: the canonical full-prefix condExpKernel law is restated using History.finitePairHistoryOfTrace for the old and successor pair prefixes, matching the project theorem-card shape. This is still canonical trajMeasure only; arbitrary ambient Omega/History.historyFiltrationSucc transport remains open.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-PREFIX-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-EXTEND-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
            "Mathlib.Probability.Kernel.Condexp",
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-SELECTED-REWARD-CONDEXPKERNEL-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.instIsMarkovKernel_historyStepKernelFamily",
            "ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure",
        ],
        "role": "Compiled reward-only canonical trajectory-law source: the existing Markov proof for RewardKernel.historyStepKernelFamily is exposed as an instance, then Mathlib Kernel.condDistrib_trajMeasure plus the local countable-target condDistrib-to-condExpKernel bridge show that the next reward coordinate under the reward-only trajMeasure has conditional pushforward equal to the selected context/action reward measure at the finite reward prefix. Generated finite-pair alignment and trim-a.e. source construction are compiled downstream; arbitrary ambient Omega transport remains open.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-CONDDISTRIB-TO-CONDEXPKERNEL-MAP",
            "RewardKernel.historyStepKernelFamily",
            "RewardKernel.isMarkovKernel_historyStepKernelFamily",
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
            "Mathlib.Probability.Kernel.Condexp",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-GENERATED-FINITEPAIR-CONDITIONING",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "FILTRATION-HISTORY",
            "KERNEL-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.comap_finitePairHistoryOfTrace_generatedActionFromRewardHistory_eq_comap_finiteRewardHistoryOfTrace",
            "ConditionalExpectationReward.historyFiltrationSucc_generatedActionFromRewardHistory_eq_comap_finiteRewardHistoryOfTrace",
            "ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure_generatedActionFromRewardHistory_finitePairHistoryOfTrace",
        ],
        "role": "Compiled generated-conditioning alignment and canonical-law theorem surface: finite pair prefixes formed from generatedActionFromRewardHistory generate exactly the same comap measurable space as finite reward prefixes; History.historyFiltrationSucc therefore has the reward-prefix comap form; and the reward-only canonical trajMeasure selected-reward condExpKernel.map law is restated on the generated finite-pair conditioning surface. The proof uses coordinate measurability and History.pairHistoryRewardProjection, not a source assumption. Its trim-a.e. strengthening and canonical selected-source constructor are compiled in the downstream trim-selected-source leaf.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-PROBABILITY-KERNEL",
            "LOCAL-LEAF-HISTORY-FILTRATION-FINITEPAIR-COMAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-SELECTED-REWARD-CONDEXPKERNEL-MAP",
            "History.measurable_pairHistoryRewardProjection",
            "History.pairHistoryRewardProjection_finitePairHistoryOfTrace",
            "Mathlib.MeasureTheory.Measure.Trim",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-TRIM-SELECTED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "FILTRATION-HISTORY",
            "KERNEL-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_countable_trim",
            "ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure_trim",
            "ConditionalExpectationReward.historyStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure_generatedActionFromRewardHistory_finitePairHistoryOfTrace_trim",
            "ConditionalExpectationReward.historyStepKernelFamily_generatedActionSelectedRewardFinitePairHistoryLawSource_trajMeasure",
        ],
        "role": "Compiled trim-aware canonical selected-source route: measurable singleton event probabilities strengthen the countable-target condDistrib-to-condExpKernel map equality to ae (mu.trim hY.comap_le); the reward-only historyStepKernelFamily trajMeasure specialization is transported through the generated finite-pair/reward-prefix comap equality; and the resulting law constructs GeneratedActionSelectedRewardFinitePairHistoryLawSource without a selected-reward source assumption. The canonical full generated partialTraj source and theorem-shaped law are compiled downstream. The route requires a probability initial Rat law, measurable context/state extractors, and countable/singleton action regularity at the source boundary; arbitrary ambient Omega transport and final adaptive bandit theorems remain open.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-PROBABILITY-KERNEL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-CONDDISTRIB-TO-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-GENERATED-FINITEPAIR-CONDITIONING",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-FROM-COMAP-LAW",
            "Mathlib.MeasureTheory.Measure.Trim",
            "MeasureTheory.ae_eq_trim_of_measurable",
            "ProbabilityTheory.condDistrib_apply_ae_eq_condExpKernel_map",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-GENERATED-PARTIALTRAJ-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "FILTRATION-HISTORY",
            "KERNEL-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.historyStepKernelFamily_generatedActionPartialTrajectoryPairLawSource_trajMeasure",
            "ConditionalExpectationReward.historyStepKernelFamily_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_trajMeasure",
        ],
        "role": "Compiled theorem-level canonical endpoint for the reward-only trajectory route: the trim-aware canonical selected-reward source is converted through the deterministic generated-action split into GeneratedActionPartialTrajectoryPairLawSource, and the successor finite pair-prefix pushforward of condExpKernel is proved equal to RewardKernel.actionRewardPartialTrajectoryKernel on the canonical historyStepKernelFamily trajMeasure. No ambient selected-reward, random-pair, or partialTraj source assumption remains. The canonical conditional mean-zero consumer is compiled downstream. This is not the arbitrary-ambient COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD and does not provide ambient integrability, variance, or final adaptive regret contracts.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-TRIM-SELECTED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-SELECTED-REWARD-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-PROJECTION",
            "LOCAL-LEAF-POLICY-REWARD-IIC-HISTORY-PARTIAL-TRAJECTORY",
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
            "Mathlib.Probability.Kernel.Condexp",
            "Mathlib.MeasureTheory.Measure.Trim",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-MEAN-ZERO",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "FILTRATION-HISTORY",
            "KERNEL-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.historyStepKernelFamily_centeredReward_succ_condExp_eq_zero_trajMeasure",
        ],
        "role": "Compiled canonical conditional-mean theorem: on the reward-only historyStepKernelFamily trajMeasure, the successor reward centered by the policy-selected kernel mean has conditional expectation zero under the generated finite-pair history. The canonical full partialTraj law discharges all conditional-law identification; the theorem keeps ambient Integrable centeredReward as the exact remaining regularity contract and deliberately avoids the unusable requirement that every trace in Nat -> Rat satisfy pointwise raw bounds. The canonical conditional-MGF consumer is compiled downstream; ambient integrability production, arbitrary ambient transport, and final adaptive theorems remain open.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-GENERATED-PARTIALTRAJ-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-CONSUMER",
            "LOCAL-LEAF-KERNEL-CENTERED-REWARD-LAW-TRANSFER",
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.Probability.Kernel.Condexp",
            "Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-CONDEXPKERNEL-COND-MGF-INTEGRATED-TRANSFER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-REWARD",
            "TAIL-COND-SUBGAUSS",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.hasCondSubgaussianMGF_of_condExpKernel_map_eq",
            "ConditionalExpectationReward.hasCondSubgaussianMGF_of_condExpKernel_map_eq_historyStepKernel_centeredReward",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_historyStepKernelFamily_condExpKernel_map_eq",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_historyStepKernelFamily_condExpKernel_map_eq_historyFiltrationSucc",
        ],
        "role": "Compiled integrated conditional-MGF transfer: a trim-a.e. condExpKernel pushforward law into target measures with a common HasSubgaussianMGF proxy now yields Mathlib HasCondSubgaussianMGF without an ambient h_integrable_exp hypothesis. Measure.integrable_comp_iff combines target-wise exponential integrability with the uniform MGF bound; StronglyMeasurable.integral_kernel and Integrable.of_bound establish integrability of the inner norm integral over the finite trim measure. The strengthening propagates through the history-step, coordinate-measurable, generated-history, canonical trajMeasure, centered/bounded/definitional source, and practical raw-range source consumers. Centered-reward measurability, the conditional reward-coordinate law, and deterministic variance domination remain explicit; arbitrary ambient law construction, martingale tails, and final bandit theorems remain open.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.Probability.Moments.SubGaussian",
            "MeasureTheory.Measure.integrable_comp_iff",
            "MeasureTheory.StronglyMeasurable.integral_kernel",
            "MeasureTheory.Integrable.of_bound",
            "ProbabilityTheory.HasSubgaussianMGF.id_map_iff",
            "ProbabilityTheory.Kernel.HasSubgaussianMGF.of_rat",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "FILTRATION-HISTORY",
            "KERNEL-REWARD",
            "KERNEL-POLICY-BIND",
            "TAIL-COND-SUBGAUSS",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.historyStepKernelFamily_centeredReward_succ_hasCondSubgaussianMGF_trajMeasure",
        ],
        "role": "Compiled canonical conditional-sub-Gaussian theorem: on the reward-only historyStepKernelFamily trajMeasure, the successor centered reward satisfies HasCondSubgaussianMGF under generated finite-pair history. The canonical full partialTraj law supplies the conditional reward law; measurable mean plus context/state/policy measurability supplies centered measurability; a deterministic ceiling over finite reward histories supplies trim-a.e. variance domination; and the integrated target-law transfer derives all-real ambient exponential integrability from the selected kernel MGF laws. No ambient h_integrable_exp or law-source hypothesis remains. A canonical finite-sum tail theorem is compiled downstream; arbitrary ambient transport, empirical-mean/confidence specialization, and final bandit theorems remain open.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-GENERATED-PARTIALTRAJ-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-MEAN-ZERO",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-COND-MGF-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-CONDEXPKERNEL-COND-MGF-INTEGRATED-TRANSFER",
            "LOCAL-LEAF-KERNEL-CENTERED-REWARD-LAW-TRANSFER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.Probability.Moments.SubGaussian",
            "Mathlib.Probability.Kernel.Condexp",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-SUM-TAIL",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "FILTRATION-HISTORY",
            "KERNEL-REWARD",
            "KERNEL-POLICY-BIND",
            "TAIL-COND-SUBGAUSS",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionFromRewardHistory_centeredRewardSuccProcess_stronglyAdapted",
            "ConditionalExpectationReward.historyStepKernelFamily_centeredRewardSuccProcess_sum_tail_ennreal_trajMeasure",
        ],
        "role": "Compiled canonical concentration endpoint for the reward-only trajectory route: the zero-initialized process Y 0 = 0 and Y (i+1) = reward(i+1) minus the policy-selected finite-history mean is StronglyAdapted to generated History.historyFiltrationSucc; the canonical conditional-MGF theorem supplies every successor witness with proxy varianceCeiling i; and Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted yields an ENNReal Azuma-Hoeffding bound for the Finset.range n sum. The zero initial term aligns Mathlib's unconditional h0 contract, so the random sum covers centered rewards 1 through n-1. Contracts are a probability initial Rat law, measurable context/state/mean surfaces, countable/singleton actions, CenteredRewardKernelLaw, deterministic finite-history variance ceilings, and eps >= 0. No independence, ambient source, or ambient exponential-integrability premise remains; empirical-mean specialization, confidence-event inversion, and final bandit/RL theorems remain open.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-CONDEXPKERNEL-COND-MGF-INTEGRATED-TRANSFER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-COND-MGF-CONSUMER",
            "LOCAL-LEAF-HISTORY-FILTRATION",
            "LOCAL-LEAF-CONCENTRATION-SUBGAUSSIAN",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-CONDITIONAL-EXPECTATION",
            "ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF",
            "MeasureTheory.StronglyAdapted",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-AVERAGE-TAIL",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "FILTRATION-HISTORY",
            "KERNEL-REWARD",
            "KERNEL-POLICY-BIND",
            "TAIL-COND-SUBGAUSS",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.historyStepKernelFamily_centeredRewardSuccProcess_average_tail_ennreal_trajMeasure",
        ],
        "role": "Compiled project-local empirical-average specialization of the canonical reward-only centered sum tail: for m > 0, the Finset.range (m + 1) sum retains the deterministic zero slot and therefore contains exactly successor rewards 1 through m. The wrapper rewrites eps <= sum / m to m * eps <= sum using Mathlib le_div_iff₀ and invokes the compiled canonical ENNReal Azuma-Hoeffding tail with threshold m * eps. Contracts are the canonical probability initial Rat law, measurable context/state/mean surfaces, countable/singleton actions, CenteredRewardKernelLaw, deterministic selected finite-history variance ceilings, m > 0, and eps >= 0. It is an aggregate trajectory-average tail, not an arm-wise empirical-mean, confidence-radius, or UCB/ETC regret theorem. The COND-EXPECT-REWARD conversion-window and proof-obligation files named by the retrieval index are absent from this worktree; do not infer their routes from this wrapper.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-SUM-TAIL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-COND-MGF",
            "LOCAL-LEAF-CONCENTRATION-SUBGAUSSIAN",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-FINSET-SUMS",
            "MLIB-ORDER-ALGEBRA",
            "le_div_iff₀",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-REWARD-CONDEXPKERNEL-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_reward_condExpKernel_map_trajMeasure",
        ],
        "role": "Compiled canonical trajMeasure specialization of the condDistrib-to-condExpKernel bridge: for the Mathlib trajectory measure generated by RewardKernel.actionRewardHistoryStepKernelFamily, condExpKernel conditioned on the finite pair prefix and pushed forward by the next reward coordinate is a.e. the reward marginal of the configured history-step kernel. This is still a canonical trajMeasure result, not an arbitrary ambient Omega/History.historyFiltrationSucc transport theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-CONDDISTRIB-TO-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-POLICY-REWARD-TRAJMEASURE-REWARD-CONDDISTRIB",
            "Mathlib.Probability.Kernel.Condexp",
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-CONDEXPKERNEL-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_selectedMeasure_condExpKernel_map_trajMeasure",
        ],
        "role": "Compiled selected-reward form of the canonical trajMeasure condExpKernel map law: for the Mathlib trajectory measure generated by RewardKernel.actionRewardHistoryStepKernelFamily, condExpKernel conditioned on the finite pair prefix and pushed forward by the next reward coordinate is a.e. the selected context/action reward measure at that prefix. This is still canonical trajMeasure only; arbitrary ambient Omega/History.historyFiltrationSucc transport remains open.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-REWARD-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-POLICY-REWARD-TRAJMEASURE-SELECTED-REWARD-CONDDISTRIB",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "Mathlib.Probability.Kernel.Condexp",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-FINITEPAIRHISTORY-CONDEXPKERNEL-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_selectedMeasure_finitePairHistoryOfTrace_condExpKernel_map_trajMeasure",
        ],
        "role": "Compiled notation-alignment wrapper for the selected-reward canonical trajMeasure law: the next-reward condExpKernel pushforward is stated with History.finitePairHistoryOfTrace as the conditioning finite-pair prefix and returns the selected context/action reward measure at that prefix. This is still canonical trajMeasure only; arbitrary ambient Omega/History.historyFiltrationSucc transport remains open.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-FINITEPAIRHISTORY-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-POLICY-REWARD-TRAJMEASURE-SELECTED-REWARD-CONDDISTRIB",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "Mathlib.Probability.Kernel.Condexp",
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-REWARDHISTORY-CONDEXPKERNEL-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_selectedMeasure_rewardHistoryOfTrace_condExpKernel_map_trajMeasure",
        ],
        "role": "Compiled canonical reward-history projection wrapper: the selected-reward finite-pair-history trajMeasure law is specialized to pairContext/pairState obtained by History.pairHistoryRewardProjection, so the RHS is stated with History.finiteRewardHistoryOfTrace. This is still canonical trajMeasure only; arbitrary ambient Omega/History.historyFiltrationSucc transport remains open.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-FINITEPAIRHISTORY-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-LAW-SOURCE-CONTRACT",
            "History.pairHistoryRewardProjection_finitePairHistoryOfTrace",
            "Mathlib.Probability.Kernel.Condexp",
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-LAW-SOURCE-CONTRACT",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.GeneratedActionSelectedRewardFinitePairHistoryLawSource",
            "ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_finitePairHistory_reward_map_eq_selected_policy",
            "ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_selectedRewardFinitePairHistoryLawSource",
        ],
        "role": "Compiled ambient source-contract leaf for the remaining generated selected-reward law: it packages the generated History.historyFiltrationSucc next-reward condExpKernel map law stated at History.finitePairHistoryOfTrace, rewrites the finite-pair prefix to the reward-history shape consumed by existing constructors, and converts the source into GeneratedActionPartialTrajectoryPairLawSource. It consumes the ambient selected-reward law and does not prove the theorem-card trajectory transport.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-REWARDHISTORY-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-FINITEPAIRHISTORY-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-SELECTED-REWARD-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-CONTRACT",
            "Mathlib.Probability.Kernel.Condexp",
            "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-FROM-COMAP-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_comap_reward_map_eq_selected_policy",
            "ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_comap_trim_reward_map_eq_selected_policy",
            "ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_comap_reward_map_eq_selected_policy",
            "ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_comap_trim_reward_map_eq_selected_policy",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_comap_reward_map_eq_selected_policy",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_comap_trim_reward_map_eq_selected_policy",
        ],
        "role": "Compiled source-constructor and theorem-wrapper leaf: a selected-reward next-reward condExpKernel.map law stated with the conditioning sigma-algebra as the comap of History.finitePairHistoryOfTrace now constructs GeneratedActionSelectedRewardFinitePairHistoryLawSource, constructs the full GeneratedActionPartialTrajectoryPairLawSource, and directly exposes the theorem-card-shaped full finite-pair partialTraj/condExpKernel law. It uses the local History.historyFiltrationSucc_eq_comap_finitePairHistoryOfTrace bridge and supports both the original generated-history trim filter and a Mathlib-facing comap-trim filter entry at the selected source, partialTraj source, and theorem-wrapper layers; it consumes rather than proves the selected-reward law or theorem-card trajectory transport.",
        "mathlib_routes": [
            "LOCAL-LEAF-HISTORY-FILTRATION-FINITEPAIR-COMAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-LAW-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-CONDDISTRIB-TO-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-FINITEPAIRHISTORY-CONDEXPKERNEL-MAP",
            "Mathlib.Probability.Kernel.Condexp",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-PARTIALTRAJ-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_selectedRewardFinitePairHistoryLawSource",
        ],
        "role": "Compiled source-projection leaf: a GeneratedActionSelectedRewardFinitePairHistoryLawSource now directly exposes the theorem-card-shaped generated-history full finite-pair partialTraj/condExpKernel law for generatedActionFromRewardHistory. It consumes the selected-reward finite-pair-history law field; it does not prove that field from a global trajectory/disintegration argument or upgrade the theorem-card row.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-LAW-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-PROJECTION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-SELECTED-REWARD-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
            "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_definitionalActualRewardMapSource",
        ],
        "role": "Compiled source-conversion leaf: a GeneratedActionDefinitionalActualRewardMapSource now constructs the generated selected-reward finite-pair-history source by unfolding generatedActionFromRewardHistory and projecting finite pair histories to reward histories. It reuses the actual-action reward-coordinate law field; it does not prove that field from ambient disintegration or trajectory transport.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-LAW-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-PARTIALTRAJ-LAW",
            "History.pairHistoryRewardProjection_finitePairHistoryOfTrace",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PRACTICAL-RAW-RANGE-SOURCE-TO-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_uniformVarianceBoundedSource",
            "ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_historyVarianceBoundedSource",
        ],
        "role": "Compiled source-conversion route: the practical definitional raw-range/measurable-mean-range generated random next-pair package, plus its uniform-variance and selected-history-variance wrappers, now projects directly to GeneratedActionSelectedRewardFinitePairHistoryLawSource. The proof lowers through GeneratedActionPartialTrajectoryPairLawSource and the selected finite-pair-history projection, so downstream selected-source mean-zero and conditional-MGF consumers no longer require callers to manually build the selected-reward source from the practical package. It still consumes the packaged random next-pair law and does not prove ambient trajectory transport.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-PROJECTION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PRACTICAL-SOURCE-VIA-SELECTED-FINITEPAIRHISTORY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_via_selectedRewardFinitePairHistoryLawSource",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource_of_varianceCeiling_le",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_via_selectedRewardFinitePairHistoryLawSource_of_varianceCeiling_le",
        ],
        "role": "Compiled route-specific theorem surface: the practical definitional raw-range/measurable-mean-range generated random next-pair package now reaches ordinary succ-indexed conditional mean-zero, and its uniform-variance or selected-history-variance wrappers reach succ-indexed HasCondSubgaussianMGF witnesses, by first projecting to GeneratedActionSelectedRewardFinitePairHistoryLawSource and then using the selected-source consumers. This records the selected finite-pair-history route end-to-end while still consuming the packaged random next-pair law and variance/proxy contracts.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PRACTICAL-RAW-RANGE-SOURCE-TO-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-MEAN-ZERO",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER",
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-MEAN-ZERO",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeBounded",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_comap_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeBounded",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled direct mean-zero consumer for the generated selected-reward finite-pair-history route: the source contract is converted into GeneratedActionPartialTrajectoryPairLawSource and then consumed with raw/mean range regularity to yield ordinary succ-indexed conditional mean-zero, and the same result is now exposed directly from the finite-pair comap selected-reward law with either the generated-history trim filter or the direct comap-trim filter. It still consumes, rather than proves, the ambient selected-reward law.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-FROM-COMAP-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-PARTIALTRAJ-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-LAW-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-MEAN-ZERO",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-MEAN-ZERO",
            "MLIB-CONDITIONAL-EXPECTATION",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_selectedRewardFinitePairHistoryLawSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled direct conditional-MGF consumers for the generated selected-reward finite-pair-history source: the source contract is converted into GeneratedActionPartialTrajectoryPairLawSource and then consumed with raw/mean range regularity plus either a global variance ceiling, a coarser global proxy, selected-history variance ceilings, or a coarser selected-history proxy. It still consumes, rather than proves, the ambient selected-reward law and the variance/proxy contracts.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-MEAN-ZERO",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-LAW-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-HISTORY-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-PAIR-CONDEXPKERNEL-MAP-SPLIT",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.pair_map_eq_map_prod_mk_of_action_ae_eq_const_reward_map_eq",
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_condExpKernel_map_trajMeasure_of_selectedAction_ae_selectedMeasure",
        ],
        "role": "Compiled canonical split-route next-pair law: a generic measure helper combines a conditional a.e. deterministic action side with a selected-reward pushforward law to identify the pair pushforward as Measure.map (Prod.mk selectedAction) selectedReward, and the canonical trajMeasure selected-action a.e. law plus selected-reward condExpKernel map law then recover RewardKernel.actionRewardHistoryStepKernelFamily. This validates the split route on canonical Ionescu-Tulcea trajectories using separate Countable Action and Countable Reward assumptions, while arbitrary ambient Omega/History.historyFiltrationSucc transport remains open.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-ACTION-CONDEXPKERNEL-AE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "Mathlib.MeasureTheory.Measure.Map",
            "Mathlib.Probability.Kernel.Condexp",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-CONSUMER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_integral_eq_historyStepKernel_centeredReward",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_integral_eq",
        ],
        "role": "Compiled project-local consumer for COND-EXPECT-REWARD: under explicit trim-a.e. law/integral-identification hypotheses connecting the conditional-expectation kernel centered-reward integral to the corresponding RewardKernel.historyStepKernelFamily centered-reward integral, the history-step zero-integral theorem supplies the condExpKernel-zero side condition and the existing condExpKernel-to-condExp bridge yields ordinary conditional mean-zero. This assumes, but does not construct, the partialTraj/history-to-condExpKernel reward-law identification; arbitrary policy predictability, conditional sub-Gaussian witnesses, and final adaptive ETC/UCB theorems remain open.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-PROBABILITY-KERNEL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-CONDEXPKERNEL-ZERO",
            "LOCAL-LEAF-KERNEL-CENTERED-REWARD-LAW-TRANSFER",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-MAP-CONSUMER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_map_eq_historyStepKernel_centeredReward",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable_rawRangeMeasurableMeanRangeBounded",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_historyFiltrationSucc_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local map-law consumer for COND-EXPECT-REWARD: under an explicit trim-a.e. reward-coordinate pushforward equality from condExpKernel to RewardKernel.historyStepKernelFamily plus a frozen-past a.e. equality for the centered target variable, Mathlib integral_map converts the map-level law identification into the earlier integral-equality consumer and ordinary conditional mean-zero. Coordinate-measurable and generated-history raw-reward/selected-mean range wrappers now derive centered-reward integrability automatically before consuming that reward-coordinate map law. This is closer to the future trajectory-law route but still assumes, rather than proves, partialTraj/history-to-condExpKernel identification, arbitrary policy predictability, source-level conditional sub-Gaussian witness assembly, and final adaptive ETC/UCB theorems.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-PROBABILITY-KERNEL",
            "Mathlib.MeasureTheory.Integral.Bochner.Basic",
            "LOCAL-LEAF-COND-EXPECT-REWARD-CONDEXPKERNEL-ZERO",
            "LOCAL-LEAF-KERNEL-CENTERED-REWARD-LAW-TRANSFER",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-COND-MGF-CONSUMER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.hasSubgaussianMGF_mono_varianceProxy",
            "ConditionalExpectationReward.hasCondSubgaussianMGF_of_condExpKernel_map_eq",
            "ConditionalExpectationReward.hasCondSubgaussianMGF_of_condExpKernel_map_eq_historyStepKernel_centeredReward",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_historyStepKernelFamily_condExpKernel_map_eq",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_historyStepKernelFamily_condExpKernel_map_eq_historyFiltrationSucc",
        ],
        "role": "Compiled project-local conditional-MGF consumer for COND-EXPECT-REWARD: a generic condExpKernel pushforward-map equality plus target HasSubgaussianMGF witnesses gives Mathlib HasCondSubgaussianMGF, the history-step specialization feeds RewardKernel.historyStepKernelFamily_centeredReward_hasSubgaussianMGF through a frozen-past centered-variable equality plus an explicit deterministic variance-proxy upper bound, and succ-indexed coordinate-measurable/generated-history-filtration wrappers discharge that frozen-past side condition. The integrated transfer now derives ambient exponential integrability from target-wise integrability and the common MGF bound. Ambient centered-reward measurability, reward-coordinate map law, and variance bound remain explicit; this does not construct the ambient partialTraj/history-to-condExpKernel law, arbitrary adaptive policy predictability, or final adaptive tail/regret theorem.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-PROBABILITY-KERNEL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-MAP-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-CONDEXPKERNEL-COND-MGF-INTEGRATED-TRANSFER",
            "LOCAL-LEAF-KERNEL-CENTERED-REWARD-LAW-TRANSFER",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CENTERED",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_frozenPast_ae_of_history_frozen",
        ],
        "role": "Compiled project-local frozen-history bridge for COND-EXPECT-REWARD: if the finite reward history is already frozen under the conditional-expectation kernel, then the history-selected context/action mean inside the succ-indexed centered reward is frozen under the same kernel. This supplies the deterministic part of the map-law consumer's h_kernel_X_eq side condition, but it still assumes rather than proves the history frozen-past property, partialTraj/history-to-condExpKernel identification, arbitrary adaptive policy predictability, and final adaptive ETC/UCB theorems.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-MAP-CONSUMER",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CONDEXPKERNEL",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "FILTRATION-HISTORY",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.condExpKernel_event_real_eq_indicator_of_measurableSet",
            "ConditionalExpectationReward.condExpKernel_ae_eq_const_of_countable_measurable",
            "ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_of_measurable",
        ],
        "role": "Compiled project-local frozen-past support for COND-EXPECT-REWARD: an mcond-measurable event has conditional-kernel real mass equal to its indicator trim-a.e.; countable-valued mcond-measurable variables are therefore a.e. constant under condExpKernel; and finite reward histories measurable at filtration level F i are frozen under condExpKernel mu (F i). This discharges the history frozen-past side condition once finite-history measurability is supplied, but it still does not prove partialTraj/history-to-condExpKernel reward-law identification, arbitrary adaptive policy predictability, or final adaptive ETC/UCB theorems.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Typeclasses.Probability",
            "LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CENTERED",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-FINITE-HISTORY-MEAS-HOOKUP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "FILTRATION-HISTORY",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_of_coordinate_measurable",
            "ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_historyFiltrationSucc",
        ],
        "role": "Compiled project-local finite-history measurability hookup for COND-EXPECT-REWARD: coordinate measurability at F i yields measurability of History.finiteRewardHistoryOfTrace and therefore the condExpKernel frozen-past property; the generated History.historyFiltrationSucc specialization supplies those coordinate hypotheses from the local history filtration. This closes the concrete finite-history measurability side of the frozen-past route, but still does not prove partialTraj/history-to-condExpKernel reward-law identification, arbitrary adaptive policy predictability, or final adaptive ETC/UCB theorems.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CONDEXPKERNEL",
            "LOCAL-LEAF-HISTORY-FILTRATION",
            "LOCAL-LEAF-HISTORY-ADAPTED-COORDINATES",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-HISTORY-FROZEN-HOOKUP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "FILTRATION-HISTORY",
            "MEAS-HISTORY",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_of_measurable",
            "ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_of_coordinate_measurable",
            "ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_historyFiltrationSucc",
        ],
        "role": "Compiled project-local pair-history frozen-past hookup for COND-EXPECT-REWARD: under a countable action space, finite action/reward pair prefixes measurable at F i are frozen under condExpKernel mu (F i), and the generated History.historyFiltrationSucc specialization supplies those action/reward coordinate measurability hypotheses. This strengthens the frozen-past support from reward-only prefixes to full pair prefixes for the future partialTraj/condExpKernel pair-law identification; it still does not prove that law.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CONDEXPKERNEL",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
            "LOCAL-LEAF-HISTORY-FILTRATION",
            "LOCAL-LEAF-HISTORY-ADAPTED-COORDINATES",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-HISTORY-SUCC-EXTEND-HOOKUP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "FILTRATION-HISTORY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "History.extendPairHistorySucc",
            "History.extendPairHistorySucc_apply_of_le",
            "History.extendPairHistorySucc_apply_succ",
            "History.finitePairHistoryOfTrace_succ",
            "History.measurable_extendPairHistorySucc",
            "ConditionalExpectationReward.finitePairHistory_succ_ae_eq_extend_of_pairHistory_frozen",
            "ConditionalExpectationReward.finitePairHistory_succ_condExpKernel_ae_eq_extend_historyFiltrationSucc",
        ],
        "role": "Compiled project-local successor-extension hookup for the COND-EXPECT-REWARD pair-law route: History names the deterministic extension of a finite action/reward pair prefix by a next pair, proves the trace prefix at i+1 decomposes through that extension, and proves the extension map is measurable; ConditionalExpectationReward then shows that under a frozen pair-prefix hypothesis, and concretely under generated History.historyFiltrationSucc condExpKernel, the random extended finite pair trace is a.e. this frozen-prefix extension by the random next pair. This is a structural predecessor to the full partialTraj/condExpKernel joint law, not the law itself.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-HISTORY-FROZEN-HOOKUP",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
            "LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-NEXT-MAP",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-MAP-CONSUMER-FROZEN-HOOKUP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "FILTRATION-HISTORY",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_historyFiltrationSucc",
        ],
        "role": "Compiled project-local map-law consumer hookup for COND-EXPECT-REWARD: the succ-indexed history-step map-law conditional mean-zero consumer no longer needs a separately supplied frozen-past h_kernel_X_eq when the finite reward prefix is coordinate-measurable at F i, with a generated History.historyFiltrationSucc specialization. The remaining structural input is still the reward-coordinate pushforward identity from condExpKernel to RewardKernel.historyStepKernelFamily; this does not prove partialTraj/history-to-condExpKernel reward-law identification, arbitrary adaptive policy predictability, or final adaptive ETC/UCB theorems.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-MAP-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-FINITE-HISTORY-MEAS-HOOKUP",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-CONSUMER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_of_coordinate_measurable",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_of_coordinate_measurable_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local pair-law consumer for COND-EXPECT-REWARD: a condExpKernel next-step (Action x Reward) pushforward identity against RewardKernel.actionRewardHistoryStepKernelFamily, plus compatibility between pair-history context/state and reward-history context/state, implies the reward-coordinate map-law consumer needed for ordinary conditional mean-zero. A source-free raw-reward/selected-mean range wrapper now derives centered-reward integrability automatically before consuming this direct pair-map law. This packages the Prod.snd marginalization step through RewardKernel.actionRewardHistoryStepKernelFamily_reward_map; it still assumes, rather than proves, the condExpKernel action/reward pair-law identification from partialTraj.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-MAP-CONSUMER-FROZEN-HOOKUP",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "LOCAL-LEAF-POLICY-REWARD-ACTION-REWARD-PARTIAL-TRAJECTORY",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-HISTORYFILTRATION-HOOKUP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local generated-history specialization of the pair-law consumer for COND-EXPECT-REWARD: under History.historyFiltrationSucc, timewise action/reward measurability supplies next-coordinate measurability and History.measurable_reward_mem_historyFiltration_of_lt supplies the finite reward-prefix measurability required by the pair-map consumer. A source-free raw-reward/selected-mean range wrapper now derives centered-reward integrability automatically before consuming the same generated-history next-pair law. The remaining structural input is still the condExpKernel action/reward pair-law pushforward identity into RewardKernel.actionRewardHistoryStepKernelFamily.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-CONSUMER",
            "LOCAL-LEAF-HISTORY-FILTRATION",
            "LOCAL-LEAF-HISTORY-ADAPTED-COORDINATES",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-HISTORYTRACE-PROJECTION-HOOKUP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local trace-history projection specialization for the generated-history pair-law consumer: pairHistory is now the concrete finite prefix fun j => (action omega j, reward omega j), while pairContext and pairState are reward-projection wrappers around the original reward-history context/state. A source-free raw-reward/selected-mean range wrapper now derives centered-reward integrability automatically for this concrete trace-pair route. This removes explicit pair-history compatibility hypotheses and leaves the generated-history condExpKernel pushforward identity for the concrete next action/reward pair as the remaining structural input.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-HISTORYFILTRATION-HOOKUP",
            "LOCAL-LEAF-POLICY-REWARD-ACTION-REWARD-PARTIAL-TRAJECTORY",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-PROJECTION-MEAS-HOOKUP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "History.pairHistoryRewardProjection",
            "History.measurable_pairHistoryRewardProjection",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected_of_context_state_measurable",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected_of_context_state_measurable_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local projection-measurability hookup for the generated-history concrete pair-law consumer: History now exposes the measurable reward projection from finite action/reward pair histories, and ConditionalExpectationReward uses it to derive reward-projection pairContext/pairState measurability from the original reward-history context/state measurability. A source-free raw-reward/selected-mean range wrapper now derives centered-reward integrability automatically for this projection-measurable route. The remaining structural input is still the concrete generated-history condExpKernel action/reward pair-law pushforward equality.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-HISTORYTRACE-PROJECTION-HOOKUP",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-FINITEPAIRTRACE-HOOKUP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "History.FinitePairHistory",
            "History.finitePairHistoryOfTrace",
            "History.finitePairHistoryOfTrace_apply",
            "History.pairHistoryRewardProjection_finitePairHistoryOfTrace",
            "History.measurable_finitePairHistoryOfTrace",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local named finite pair-trace hookup for the generated-history concrete pair-law consumer: History now exposes the Finset.Iic-indexed action/reward pair-coordinate trace prefix and its measurability/projection equality, and ConditionalExpectationReward states the remaining condExpKernel pair-law hypothesis using History.finitePairHistoryOfTrace. A source-free raw-reward/selected-mean range wrapper now derives centered-reward integrability automatically before consuming that direct history-step next-pair law. This aligns the consumer with RewardKernel.actionRewardPartialTrajectoryKernel's pair-coordinate prefix shape; the actual condExpKernel pair-law identity remains open.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-PROJECTION-MEAS-HOOKUP",
            "LOCAL-LEAF-POLICY-REWARD-ACTION-REWARD-PARTIAL-TRAJECTORY",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
            "MEAS-HISTORY",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local consumer that turns an explicit generated-history condExpKernel law for the extended finite action/reward pair trace into the existing next-pair map-law consumer via RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map_apply. The projection theorem is exposed as a reusable law adapter, the centered-reward consumer aligns COND-EXPECT-REWARD with the Mathlib partialTraj finite-prefix surface, and a raw-reward/selected-mean range wrapper now derives centered-reward integrability automatically before consuming the full finite-pair partialTraj law. This still assumes the actual condExpKernel/partialTraj law.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-NEXT-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-FINITEPAIRTRACE-HOOKUP",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-TRAJECTORY-PARTIALTRAJ-PAIR-LAW-SOURCE-CONTRACT",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.GeneratedActionPartialTrajectoryPairLawSource",
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalMapSource_of_partialTrajectoryPairLawSource",
        ],
        "role": "Compiled project-local source-contract leaf for the remaining generated-history partialTraj/condExpKernel pair-law gap: it packages the exact full finite-pair trace law over generatedActionFromRewardHistory as a reusable source, then feeds that source into the existing definitional generated random-pair map source constructor. This does not prove the law from arbitrary mu/action/reward, does not transport canonical trajMeasure to ambient Omega, and does not upgrade COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD from theorem-card-only.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
            "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj",
            "Mathlib.Probability.Kernel.Disintegration.StandardBorel",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-PROJECTION",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_partialTrajectoryPairLawSource",
            "ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_partialTrajectoryPairLawSource",
            "ConditionalExpectationReward.generatedActionSelectedRewardFinitePairHistoryLawSource_of_partialTrajectoryPairLawSource",
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_partialTrajectoryPairLawSource",
        ],
        "role": "Compiled project-local source-projection leaf: a GeneratedActionPartialTrajectoryPairLawSource directly exposes the theorem-card-shaped generated-history full finite-pair partialTraj/condExpKernel law as a named theorem and now also projects to the weaker definitional actual reward-map, selected-reward finite-pair-history, and explicit generated-action actual reward-map source interfaces. It consumes the source field; it does not construct the law from arbitrary mu/action/reward, transport canonical trajMeasure to ambient Omega, or upgrade COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD from theorem-card-only.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj",
            "Mathlib.Probability.Kernel.Disintegration.StandardBorel",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-TRAJECTORY-PARTIALTRAJ-PAIR-LAW-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-EXTEND-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_partialTrajectoryKernel_extend_map_eq",
        ],
        "role": "Compiled project-local source-constructor leaf: the narrower frozen-prefix extension-map partialTraj/condExpKernel law now constructs a GeneratedActionPartialTrajectoryPairLawSource by reusing the existing extension-to-full-trace adapter. It reduces the future source-building obligation to the extension-map law but does not prove that law, transport canonical trajMeasure to ambient Omega, or upgrade COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD from theorem-card-only.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj",
            "Mathlib.Probability.Kernel.Disintegration.StandardBorel",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-PROJECTION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-TRAJECTORY-PARTIALTRAJ-PAIR-LAW-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
            "LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-EXTEND-MAP",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-HISTORYSTEP-PAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq",
        ],
        "role": "Compiled project-local source-constructor leaf: a generated-history next-pair condExpKernel law identified with RewardKernel.actionRewardHistoryStepKernelFamily now constructs a GeneratedActionPartialTrajectoryPairLawSource via the existing next-pair-to-extension-map and extension-to-full-source adapters. It reduces the future source-building obligation to the canonical next-pair law but does not prove that law, transport canonical trajMeasure to ambient Omega, or upgrade COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD from theorem-card-only.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
            "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj",
            "Mathlib.Probability.Kernel.Disintegration.StandardBorel",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-EXTEND-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-PROJECTION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-FROM-PAIRMAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-PAIR-CONDEXPKERNEL-MAP",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-SPLIT-NEXTPAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_action_ae_eq_policy_reward_map_eq",
        ],
        "role": "Compiled project-local source-constructor leaf: split generated-history next-pair laws, namely the action conditional a.e. equality and the policy-selected reward-coordinate condExpKernel map law, now construct a GeneratedActionPartialTrajectoryPairLawSource via the local split-law builder and the existing history-step-pair source constructor. It reduces the future source-building obligation to the two split laws but does not prove those laws, transport canonical trajMeasure to ambient Omega, or upgrade COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD from theorem-card-only.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
            "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj",
            "Mathlib.Probability.Kernel.Disintegration.StandardBorel",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-ACTION-CONDEXPKERNEL-AE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-PAIR-CONDEXPKERNEL-MAP-SPLIT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-SELECTED-REWARD-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_reward_map_eq_selected_policy",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_reward_map_eq_selected_policy",
        ],
        "role": "Compiled project-local source-constructor/theorem-wrapper leaf: for generatedActionFromRewardHistory, the generated-trace action-freezing theorem supplies the action side of the split next-pair route, so a policy-selected reward-coordinate condExpKernel map law alone constructs a GeneratedActionPartialTrajectoryPairLawSource and now directly exposes the theorem-card-shaped full finite-pair partialTraj/condExpKernel law. It reduces the future source-building obligation to the selected reward law but does not prove that law, transport canonical trajMeasure to ambient Omega, or upgrade COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD from theorem-card-only.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.Probability.Kernel.IonescuTulcea.Traj",
            "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj",
            "Mathlib.Probability.Kernel.Disintegration.StandardBorel",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-SPLIT-NEXTPAIR-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-CONDEXPKERNEL-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-REWARD-MAP-TO-DEFINITIONAL-RANDOM-PAIR-MAP-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-DEFINITIONAL-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_randomPairDefinitionalMapSource",
        ],
        "role": "Compiled project-local source-conversion leaf: a GeneratedActionRandomPairDefinitionalMapSource now constructs a GeneratedActionPartialTrajectoryPairLawSource by projecting the source to the policy-selected reward-coordinate law and reusing the selected-reward source constructor. It connects the existing definitional random-pair source surface to the partialTraj source route but does not prove the random-pair source law, transport canonical trajMeasure to ambient Omega, or upgrade COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD from theorem-card-only.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj",
            "Mathlib.Probability.Kernel.Disintegration.StandardBorel",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-SELECTED-REWARD-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-RANDOM-PAIR-MAP-SOURCE-TO-SELECTED-POLICY-REWARD-MAP",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_partialTrajectoryPairLawSource",
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_comap_reward_map_eq_selected_policy",
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_comap_trim_reward_map_eq_selected_policy",
        ],
        "role": "Compiled project-local source/comap source-conversion leaf: a GeneratedActionPartialTrajectoryPairLawSource, or the finite-pair comap selected-reward law that constructs that source, plus measurable mean, centered reward-kernel law, raw reward range bounds, and deterministic mean range bounds now builds the practical GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource. The selected-reward law can be supplied at either the generated-history trim surface or the direct comap-trim surface. It consumes the packaged full finite-pair partialTraj/condExpKernel law or the selected-reward comap law; it does not prove either law, transport canonical trajMeasure to ambient Omega, add variance ceilings, or upgrade COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD from theorem-card-only.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-FROM-COMAP-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-DEFINITIONAL-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-SELECTED-REWARD-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-SPLIT-NEXTPAIR-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-EXTEND-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-PROJECTION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-TRAJECTORY-PARTIALTRAJ-PAIR-LAW-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_partialTrajectoryPairLawSource",
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_comap_reward_map_eq_selected_policy",
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_comap_trim_reward_map_eq_selected_policy",
        ],
        "role": "Compiled project-local source/comap source-conversion leaf: a GeneratedActionPartialTrajectoryPairLawSource, or the finite-pair comap selected-reward law that constructs that source, plus measurable mean, centered reward-kernel law, raw reward range bounds, deterministic mean range bounds, and a global variance ceiling now builds the packaged uniform-variance practical source. The selected-reward law can be supplied at either the generated-history trim surface or the direct comap-trim surface. It consumes the packaged full finite-pair partialTraj/condExpKernel law or the selected-reward comap law; it does not prove either law, transport canonical trajMeasure to ambient Omega, construct a history-indexed ceiling, or upgrade COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD from theorem-card-only.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-FROM-COMAP-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-TRAJECTORY-PARTIALTRAJ-PAIR-LAW-SOURCE-CONTRACT",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-MEAN-ZERO",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_partialTrajectoryPairLawSource_definitionalRawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local source-consumer leaf: a GeneratedActionPartialTrajectoryPairLawSource plus raw/mean range regularity now directly yields ordinary succ-indexed conditional mean-zero for the generated reward-history action trace. It consumes the packaged full finite-pair partialTraj/condExpKernel law; it does not prove that law, transport canonical trajMeasure to ambient Omega, derive variance ceilings, or upgrade COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD from theorem-card-only.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-CONDEXPKERNEL-ZERO",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-TRAJECTORY-PARTIALTRAJ-PAIR-LAW-SOURCE-CONTRACT",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_partialTrajectoryPairLawSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded",
        ],
        "role": "Compiled project-local source/comap consumer leaf: a GeneratedActionPartialTrajectoryPairLawSource plus raw/mean range regularity and a global variance ceiling directly yields the succ-indexed HasCondSubgaussianMGF witness for the generated reward-history action trace; the same witness is now exposed directly from the finite-pair comap selected-reward law by first constructing the partialTraj source, with both the generated-history trim filter and the direct comap-trim filter accepted as entry surfaces. It consumes the packaged or comap-supplied full finite-pair partialTraj/condExpKernel law route; it does not prove that law, transport canonical trajMeasure to ambient Omega, derive variance ceilings, or upgrade COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD from theorem-card-only.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-FROM-COMAP-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-TRAJECTORY-PARTIALTRAJ-PAIR-LAW-SOURCE-CONTRACT",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_partialTrajectoryPairLawSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local source/comap consumer route: a GeneratedActionPartialTrajectoryPairLawSource plus raw/mean range regularity, a global variance ceiling, and a deterministic domination hceiling : varianceCeiling <= c now directly yields the succ-indexed HasCondSubgaussianMGF witness at the coarser proxy c for the generated reward-history action trace; the same coarser-proxy witness is now exposed directly from the finite-pair comap selected-reward law by first constructing the partialTraj source, with both the generated-history trim filter and the direct comap-trim filter accepted as entry surfaces. It consumes the packaged or comap-supplied full finite-pair partialTraj/condExpKernel law route; it does not prove that law, transport canonical trajMeasure to ambient Omega, derive variance ceilings, prove proxy domination, or upgrade COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD from theorem-card-only.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-FROM-COMAP-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-TRAJECTORY-PARTIALTRAJ-PAIR-LAW-SOURCE-CONTRACT",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-HISTORY-VARIANCE-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_partialTrajectoryPairLawSource",
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_comap_reward_map_eq_selected_policy",
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_comap_trim_reward_map_eq_selected_policy",
        ],
        "role": "Compiled project-local source/comap source-conversion leaf: a GeneratedActionPartialTrajectoryPairLawSource, or the finite-pair comap selected-reward law that constructs that source, plus measurable mean, centered reward-kernel law, raw reward range bounds, deterministic mean range bounds, and selected-history variance ceilings now builds the packaged history-variance practical source. The selected-reward law can be supplied at either the generated-history trim surface or the direct comap-trim surface. It consumes the packaged full finite-pair partialTraj/condExpKernel law or the selected-reward comap law; it does not prove either law, transport canonical trajMeasure to ambient Omega, derive the selected-history ceiling, or upgrade COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD from theorem-card-only.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-FROM-COMAP-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-TRAJECTORY-PARTIALTRAJ-PAIR-LAW-SOURCE-CONTRACT",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-HISTORY-VARIANCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_partialTrajectoryPairLawSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded",
        ],
        "role": "Compiled project-local source/comap consumer leaf: a GeneratedActionPartialTrajectoryPairLawSource plus raw/mean range regularity and selected-history variance ceilings now directly yields the succ-indexed HasCondSubgaussianMGF witness at proxy varianceCeiling i for the generated reward-history action trace; the same witness is now exposed directly from the finite-pair comap selected-reward law by first constructing the partialTraj source, with both the generated-history trim filter and the direct comap-trim filter accepted as entry surfaces. It consumes the packaged or comap-supplied full finite-pair partialTraj/condExpKernel law route; it does not prove that law, transport canonical trajMeasure to ambient Omega, derive selected-history ceilings, or upgrade COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD from theorem-card-only.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-FROM-COMAP-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-TRAJECTORY-PARTIALTRAJ-PAIR-LAW-SOURCE-CONTRACT",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_partialTrajectoryPairLawSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_comap_trim_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local source/comap consumer leaf: a GeneratedActionPartialTrajectoryPairLawSource plus raw/mean range regularity, selected-history variance ceilings, and a deterministic domination hceiling : varianceCeiling i <= c now directly yields the succ-indexed HasCondSubgaussianMGF witness at the coarser proxy c for the generated reward-history action trace; the same coarser-proxy witness is now exposed directly from the finite-pair comap selected-reward law by first constructing the partialTraj source, with both the generated-history trim filter and the direct comap-trim filter accepted as entry surfaces. It consumes the packaged or comap-supplied full finite-pair partialTraj/condExpKernel law route; it does not prove that law, transport canonical trajMeasure to ambient Omega, derive selected-history ceilings, prove proxy domination, or upgrade COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD from theorem-card-only.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-FROM-COMAP-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-TRAJECTORY-PARTIALTRAJ-PAIR-LAW-SOURCE-CONTRACT",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-REWARD-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
            "MEAS-HISTORY",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace",
            "ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local reward-coordinate adapter for the COND-EXPECT-REWARD partialTraj route: a full finite-pair trace condExpKernel/partialTraj law is first projected to the next (Action x Reward) law, then mapped through Prod.snd and RewardKernel.actionRewardHistoryStepKernelFamily_reward_map to recover the selected reward measure. A generated-action wrapper supplies the successor action equality from Policy.generatedActionTraceSucc and rewrites the policy-selected action to the actual next action. A raw-reward/selected-mean range consumer now uses this reward-map adapter to obtain succ-indexed conditional mean-zero directly from the same full finite-pair trace law without separately passing integrability. This still assumes the full finite-pair trace condExpKernel/partialTraj law and does not construct the ambient trajectory identification or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.finitePairHistory_succ_condExpKernel_map_eq_extend_historyFiltrationSucc",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_of_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local extension-map consumer for the COND-EXPECT-REWARD partialTraj route: the generated History.historyFiltrationSucc condExpKernel successor decomposition is upgraded from an a.e. equality to a Measure.map equality by Mathlib Measure.map_congr, a reusable adapter turns an extension-map partialTraj law into the full finite-pair-trace partialTraj law, and the centered-reward consumer can assume only that condExpKernel pushed through the deterministic frozen-prefix extension map agrees with the one-step action/reward partialTraj kernel. A raw-reward/selected-mean range wrapper now derives centered-reward integrability automatically before consuming that narrower extension-map law. This narrows the remaining trajectory-law assumption from the whole i+1 finite pair trace to the extension of a frozen old pair prefix by the random next pair; it still does not prove the actual condExpKernel/partialTraj law.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-HISTORY-SUCC-EXTEND-HOOKUP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
            "LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-NEXT-MAP",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-REWARD-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace",
            "ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local reward-coordinate adapter and raw-range mean-zero consumer for the extension-map partialTraj route: the deterministic frozen-prefix extension-map law is first lifted to the full finite-pair trace law by the existing successor-decomposition adapter, then the finite-pair trace reward-map adapter projects through the next pair and Prod.snd to recover the actual-action selected reward law. A generated-action wrapper supplies the successor action equality from Policy.generatedActionTraceSucc, and the raw-reward/selected-mean range wrapper derives integrability before consuming the selected-reward law to obtain succ-indexed conditional mean-zero. This still assumes the extension-map condExpKernel/partialTraj law and does not construct the ambient trajectory identification or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-REWARD-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-HISTORYSTEP-REWARD-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
            "MEAS-HISTORY",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardHistoryStepKernelFamily_pair_map_eq",
            "ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace",
            "ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local reward-coordinate adapter and generated-action raw-range mean-zero surface for the next-pair history-step route: an explicit conditional next (Action x Reward) pushforward law into RewardKernel.actionRewardHistoryStepKernelFamily is projected through Prod.snd and RewardKernel.actionRewardHistoryStepKernelFamily_reward_map to recover the actual-action selected reward law. The finite-pair-history specialization aligns pairContext/pairState with reward-history context/state by History.pairHistoryRewardProjection, the generated-action wrapper derives the successor action equality from Policy.generatedActionTraceSucc, and the raw-reward/selected-mean range wrapper records the common generated-action calling convention for succ-indexed conditional mean-zero. This still assumes the next-pair condExpKernel law and does not construct the ambient trajectory identification or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-FROM-PAIRMAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-FROM-PAIRMAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
            "MEAS-HISTORY",
            "FILTRATION-HISTORY",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace",
        ],
        "role": "Compiled project-local law builder for the COND-EXPECT-REWARD partialTraj route: a conditional next-pair pushforward identity into RewardKernel.actionRewardHistoryStepKernelFamily is pushed through History.extendPairHistorySucc, and RewardKernel.actionRewardPartialTrajectoryKernel_succ_extend_map_apply identifies the target with the one-step action/reward partialTraj kernel. This connects the pair-map law shape to the extension-map law shape, but still assumes the actual generated-history next-pair condExpKernel law.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-FINITEPAIRTRACE-HOOKUP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
            "LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-EXTEND-MAP",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
            "ADAPTED-ACTION",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "RewardKernel.composePolicyActionReward_kernel_apply_eq_map_prod_mk",
            "RewardKernel.actionRewardHistoryStepKernelFamily_apply_eq_map_prod_mk",
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_action_ae_eq_policy_reward_map_eq",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_action_ae_eq_policy_reward_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local split-law builder and raw-range mean-zero consumer for the COND-EXPECT-REWARD next-pair route: if the next action is a.e. the policy-selected action under the conditional kernel and the next reward pushforward is the selected reward measure, then the full next (Action x Reward) pushforward law is RewardKernel.actionRewardHistoryStepKernelFamily; the raw-reward/selected-mean range wrapper then feeds that canonical pair law into the finite-pair mean-zero consumer. This decomposes the remaining pair-law obligation into a predictable-action/frozen-action side and a reward-law side; it does not prove either side.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-POLICY-REWARD-ACTION-REWARD-PARTIAL-TRAJECTORY",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-FROM-PAIRMAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-FINITEPAIRTRACE-HOOKUP",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-PRODUCT-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
            "ADAPTED-ACTION",
            "KERNEL-REWARD",
            "MEAS-HISTORY",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.condExpKernel_pair_map_eq_map_prod_mk_of_action_ae_reward_map_eq",
            "ConditionalExpectationReward.random_pair_condExpKernel_map_eq_actual_action_of_generatedActionTraceSucc_reward_map_eq_actual_action",
        ],
        "role": "Compiled project-local ambient split-product law for the COND-EXPECT-REWARD random next-pair route: a conditional action a.e. equality plus a reward-coordinate selected-measure law directly produce the fully random next-pair product pushforward Measure.map (Prod.mk selectedAction) selectedReward. The generated History.historyFiltrationSucc specialization obtains the action side from Policy.generatedActionTraceSucc and turns an actual-action reward map law into the random next-pair product law consumed by downstream adapters. It still assumes the reward-coordinate selected-measure law and does not identify ambient trajectory laws with condExpKernel.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-RANDOM-PAIR-HISTORYSTEP-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "KERNEL-POLICY-BIND",
            "ADAPTED-ACTION",
            "KERNEL-REWARD",
            "MEAS-HISTORY",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action",
        ],
        "role": "Compiled project-local law-shape adapter for the COND-EXPECT-REWARD next-pair route: a generated-action random next-pair source law stated as a conditional pushforward of (action y (i+1), reward y (i+1)) into Measure.map (Prod.mk actualAction) selectedMeasure is rewritten into the canonical RewardKernel.actionRewardHistoryStepKernelFamily pair law over the concrete finite pair trace. This preserves the random-pair law as an explicit assumption but removes manual Prod.mk/selectedMeasure rewrites for downstream pair-law consumers.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
            "LOCAL-LEAF-POLICY-REWARD-ACTION-REWARD-PARTIAL-TRAJECTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-POLICY-HOOKUP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_of_measurable_of_policy_eq",
        ],
        "role": "Compiled action-freezing hookup for the COND-EXPECT-REWARD next-pair route: a countable next action measurable at F i is frozen by condExpKernel, and a trim-a.e. equality to the policy-selected action turns that frozen action into the conditional a.e. action equality consumed by the next-pair split-law builder. This does not prove arbitrary policy predictability or the reward-coordinate selected-measure law.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CONDEXPKERNEL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER",
            "LOCAL-LEAF-POLICY-GENERATED-ACTION-TRACE-MEASURABILITY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-HISTORY-HOOKUP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-HISTORY",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_of_pairHistory_measurable_of_action_eq",
            "ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_action_eq",
        ],
        "role": "Compiled generated-history action-freezing hookup for the COND-EXPECT-REWARD next-pair route: if a finite pair history is F_i-measurable, pairState is measurable, and the next action is pointwise the policy-selected action from that pair history, then the conditional action a.e. equality consumed by the split-law builder follows; the History.historyFiltrationSucc/finitePairHistoryOfTrace specialization discharges the pair-history measurability side from local history APIs. This still assumes the pointwise policy-generation equality and does not prove the reward-coordinate selected-measure law.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-POLICY-HOOKUP",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
            "LOCAL-LEAF-POLICY-MEASURABILITY",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "POLICY-GENERATED-ACTION-TRACE-MEASURABILITY",
            "KERNEL-POLICY-BIND",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "Policy.generatedActionTraceSucc",
            "Policy.generatedActionTraceSucc_succ_eq",
            "Policy.measurable_generatedActionTraceSucc_succ_mem_filtration_of_measurable_state",
            "ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc",
        ],
        "role": "Compiled policy-generated trace source for the COND-EXPECT-REWARD next-pair action side: a shifted time-indexed generated action trace has action coordinate i+1 selected by policy i from the finite pair-history state, so an action-trace equality to that generated trace supplies the pointwise policy-generation equality consumed by the generated-history action-freezing hookup. This still does not prove the reward-coordinate selected-measure law or the full condExpKernel/partialTraj identification.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-HISTORY-HOOKUP",
            "LOCAL-LEAF-POLICY-GENERATED-ACTION-TRACE-MEASURABILITY",
            "LOCAL-LEAF-POLICY-MEASURABILITY",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalExpectationReward",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_pair_map_eq",
            "ConditionalExpectationReward.pair_condExpKernel_map_eq_frozen_actual_action_of_generatedActionTraceSucc_random_pair_map_eq",
            "ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_policy_of_action_eq",
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action",
            "ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_reward_map_eq_actual_action",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_reward_map_eq_actual_action",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_pair_map_eq_actual_action",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_reward_map_eq_actual_action",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_reward_map_eq_actual_action_rawRangeMeasurableMeanRangeBounded",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_reward_map_eq_selected_policy_rawRangeMeasurableMeanRangeBounded",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_pair_map_eq_actual_action_rawRangeMeasurableMeanRangeBounded",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_pair_map_eq_actual_action",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_random_pair_map_eq_actual_action",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_random_pair_map_eq_actual_action_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled generated-action plus policy-selected/actual/random-pair reward-law hookup for the COND-EXPECT-REWARD route: if the conditional law is stated as an actual-action pair-product law, Prod.snd marginalization gives the actual-action reward-coordinate law and a reusable adapter exposes the resulting full finite-pair-trace partialTraj law; if it is stated for the fully random next pair, the generated action trace first freezes the action coordinate with Measure.map_congr and a second reusable adapter exposes the same full-trace law. The route then rewrites the selected action to the policy action, combines it with the split-law builder to produce the full next-pair condExpKernel law, pushes that through the extension-map partialTraj builder, and provides succ-indexed conditional mean-zero consumers under integrability; it now also exposes generatedActionFromRewardHistory actual-action reward-coordinate laws as a GeneratedActionPartialTrajectoryPairLawSource and as a theorem-card-shaped full finite-pair partialTraj/condExpKernel law without an explicit action trace or generated-trace equality parameter. It also consumes explicit generated-action equality plus policy-selected reward-coordinate, actual-action reward-coordinate, actual-action pair-product, or fully random next-pair law and raw/mean range regularity directly into mean-zero without first packaging a source or passing a separate integrability hypothesis. This still assumes the pair/reward law source and does not prove the full ambient trajectory-to-condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-FROM-PAIRMAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.GeneratedActionActualRewardMapSource",
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_partialTrajectoryKernel_map_eq",
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_partialTrajectoryKernel_extend_map_eq",
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionActualRewardMapSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionActualRewardMapSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionActualRewardMapSource_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled generated-policy actual reward-coordinate map source contract for the COND-EXPECT-REWARD route: it packages shifted generated-action equality plus the per-step conditional law of only the next reward coordinate under the actual next action, can now also build that source directly from full finite-pair partialTraj, frozen-prefix extension-map partialTraj, or canonical history-step next-pair law hypotheses, then reuses the existing actual reward-map route to expose full finite-pair-trace partialTraj law and succ-indexed conditional mean-zero under integrability; it also directly consumes the same source plus raw reward and selected-mean range regularity into succ-indexed conditional mean-zero without a separate integrability hypothesis. This is weaker than the random next-pair source and still assumes the actual reward-coordinate or ambient trajectory-to-condExpKernel/partialTraj/history-step law, raw/mean range regularity or integrability, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionActualRewardMapSource",
        ],
        "role": "Compiled actual reward-coordinate source-level canonical pair-law consumer for the COND-EXPECT-REWARD route: GeneratedActionActualRewardMapSource now directly yields the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law over History.finitePairHistoryOfTrace by lifting reward-history context/state through History.pairHistoryRewardProjection and reusing the generated-action actual reward-map hookup. This still assumes the actual reward-coordinate law source and ambient trajectory-to-condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_generatedActionActualRewardMapSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a GeneratedActionActualRewardMapSource plus reward-history state measurability is upgraded into the stronger GeneratedActionRandomPairMapSource by rewriting reward histories through History.pairHistoryRewardProjection and consuming the ambient split-product condExpKernel law. This still assumes the actual-action reward-coordinate source and ambient trajectory-to-condExpKernel identification; it does not construct the reward law itself.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-PRODUCT-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource",
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_definitionalActualRewardMapSource",
            "ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_reward_map_eq_selected_policy",
            "ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_partialTrajectoryKernel_map_eq",
            "ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_partialTrajectoryKernel_extend_map_eq",
            "ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionDefinitionalActualRewardMapSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled definitional generated-action actual reward-coordinate map source contract for the COND-EXPECT-REWARD route: it removes the explicit action trace and timewise action-measurability inputs from the actual reward-map source by using generatedActionFromRewardHistory plus measurable reward-history state extractors, can package a policy-selected reward-coordinate law, full finite-pair partialTraj law, frozen-prefix extension-map partialTraj law, or canonical history-step next-pair law into the actual generated-successor reward-map source, then converts to the existing actual reward-map source to expose full finite-pair-trace partialTraj law and succ-indexed conditional mean-zero under integrability; it now also directly consumes the definitional actual reward-map source plus raw reward and selected-mean range regularity into succ-indexed conditional mean-zero without a separate integrability hypothesis. This still assumes the reward-coordinate or ambient trajectory-to-condExpKernel/partialTraj/history-step law, raw/mean range regularity or integrability, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-REWARD-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-REWARD-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-HISTORYSTEP-REWARD-MAP",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
            "LOCAL-LEAF-POLICY-MEASURABILITY",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-MEAN-ZERO",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionDefinitionalActualRewardMapSource",
        ],
        "role": "Compiled project-local conditional mean-zero consumer leaf for the COND-EXPECT-REWARD route: a packaged definitional generated-action actual reward-coordinate source, centered reward-kernel law, and explicit centered-reward integrability yield the succ-indexed ordinary conditional expectation zero statement over the generated-action history filtration. The proof derives action measurability from the source's state measurability, lowers through the explicit actual reward-map source, and reuses the existing generated-action actual reward-map mean-zero consumer. It still assumes the packaged actual-action reward-coordinate law, centered-reward integrability, and ambient trajectory-to-condExpKernel identification; it adds no raw/mean range regularity, variance ceiling, MGF witness, or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource",
        ],
        "role": "Compiled definitional actual reward-coordinate source-level canonical pair-law consumer for the COND-EXPECT-REWARD route: GeneratedActionDefinitionalActualRewardMapSource now yields the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law over generatedActionFromRewardHistory, deriving action measurability from reward-history state measurability and reusing the explicit actual-source pair-law wrapper. This still assumes the definitional actual reward-coordinate law source and ambient trajectory-to-condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
            "LOCAL-LEAF-POLICY-MEASURABILITY",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-PARTIALTRAJ-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource",
        ],
        "role": "Compiled definitional actual reward-coordinate source-level partialTraj consumer for the COND-EXPECT-REWARD route: GeneratedActionDefinitionalActualRewardMapSource now yields the full finite-pair-trace actionRewardPartialTrajectoryKernel law over generatedActionFromRewardHistory, deriving action measurability from reward-history state measurability and reusing the explicit actual-source partialTraj wrapper. This still assumes the definitional actual reward-coordinate law source and ambient trajectory-to-condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
            "LOCAL-LEAF-POLICY-MEASURABILITY",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-DEFINITIONAL-RANDOM-PAIR-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalMapSource_of_generatedActionDefinitionalActualRewardMapSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a definitional actual-action reward-coordinate map source plus context measurability now builds the stronger definitional generated random-pair map source by first deriving the full finite-pair partialTraj law and then reusing the existing definitional random-pair source constructor. It still assumes the definitional actual reward-coordinate source and ambient trajectory-to-condExpKernel identification; it does not construct the source, regularity, conditional MGF, adaptive, or final regret theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-PARTIALTRAJ-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
            "LOCAL-LEAF-POLICY-MEASURABILITY",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-GENERATED-RANDOM-PAIR-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_generatedActionDefinitionalActualRewardMapSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a definitional actual-action reward-coordinate source now directly produces the explicit generated-action random-pair map source over generatedActionFromRewardHistory by lowering to the explicit actual reward-map source and applying the ambient split-product source upgrade. This does not require context measurability, but still assumes the definitional actual reward-coordinate law and ambient trajectory-to-condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.GeneratedActionRandomPairMapSource",
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq",
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_actionRewardPartialTrajectoryKernel_map_eq",
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairMapSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairMapSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairMapSource_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled generated-policy random next-pair law source contract for the COND-EXPECT-REWARD route: it packages shifted generated-action equality plus the per-step random next-pair condExpKernel map law as a reusable structure, can now also build that source directly from canonical history-step next-pair, full finite-pair partialTraj, or frozen-prefix extension-map partialTraj law hypotheses, then consumes the existing generated-action/random-pair route to expose full finite-pair-trace partialTraj law and succ-indexed conditional mean-zero. The mean-zero consumer is available both under a direct integrability hypothesis and from raw reward plus selected-mean range regularity. This is a contract surface; it still does not construct the pair/reward law source, ambient trajectory-to-condExpKernel identification, or a final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-MEAN-ZERO",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairMapSource",
        ],
        "role": "Compiled project-local conditional mean-zero consumer leaf for the COND-EXPECT-REWARD route: a packaged generated-policy random next-pair map source, centered reward-kernel law, and explicit centered-reward integrability yield the succ-indexed ordinary conditional expectation zero statement over the supplied generated action/reward history filtration. The proof unpacks source.action_generated and the per-step random-pair map law, then reuses the compiled generated-action random-pair route. It still assumes the packaged random next-pair law, centered-reward integrability, and ambient trajectory-to-condExpKernel identification; it adds no raw/mean range regularity, variance ceiling, MGF witness, or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-RAW-RANGE-MEASURABLE-MEAN-RANGE-MEAN-ZERO",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairMapSource_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local raw-range conditional mean-zero consumer leaf for the COND-EXPECT-REWARD route: a packaged generated-policy random next-pair map source, centered reward-kernel law, deterministic raw reward range bounds, deterministic selected-mean range bounds, and timewise reward measurability yield the succ-indexed ordinary conditional expectation zero statement without a separate centered-reward integrability hypothesis. The proof unpacks source.action_generated and the per-step random-pair map law, then reuses the compiled generated-action random-pair raw/mean range wrapper. It still assumes the packaged random next-pair law, raw/mean range regularity, and ambient trajectory-to-condExpKernel identification; it adds no variance ceiling, MGF witness, adaptive law identification, or final regret theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-MEAN-ZERO",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "MEAS-HISTORY",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairMapSource",
        ],
        "role": "Compiled project-local source consumer for the COND-EXPECT-REWARD route: the packaged GeneratedActionRandomPairMapSource now directly yields the canonical RewardKernel.actionRewardHistoryStepKernelFamily next-pair law over History.finitePairHistoryOfTrace, with reward-history context/state lifted through History.pairHistoryRewardProjection. This removes repeated unpacking of action_generated and random_pair_map_eq_actual_action before downstream pair-law consumers, but still assumes the random next-pair law source and does not identify the ambient trajectory law with condExpKernel.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-RANDOM-PAIR-HISTORYSTEP-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairMapSource",
            "ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalMapSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a generated-policy random next-pair map source is converted into the weaker actual-action reward-coordinate map source by freezing the generated action coordinate under the conditional kernel and marginalizing through Prod.snd. The definitional variant derives action measurability from the random-pair definitional source. This still assumes the random next-pair law, state measurability for action freezing, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairCenteredSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a generated-policy centered random next-pair source now directly exposes its packaged GeneratedActionRandomPairMapSource through a stable named projection. The centered reward-kernel law and per-step centered-reward integrability fields remain available for stronger centered consumers, but are not needed by this weaker map-source interface. It still assumes the random next-pair law, centered-source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairCenteredSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a generated-policy centered random next-pair source is weakened into the actual-action reward-coordinate map source by projecting its packaged random-pair map source and state-measurability field into the existing random-pair-to-actual source conversion. This exposes the weaker reward-coordinate interface to downstream consumers while keeping the centered law and integrability fields available in the stronger source. It still assumes the random next-pair law, centered-source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairBoundedCenteredSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a bounded generated-policy centered random next-pair source now directly exposes its packaged GeneratedActionRandomPairMapSource through a stable named projection. The a.e. centered-reward measurability and interval-bound evidence remain available for integrability consumers, but are not needed by this weaker map-source interface. It still assumes the random next-pair law, bounded-centered source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairBoundedCenteredSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a bounded generated-policy centered random next-pair source is weakened into the actual-action reward-coordinate map source by projecting its packaged random-pair map source and state-measurability field into the existing random-pair-to-actual source conversion. Its a.e. measurability and interval-bound evidence remains available for integrability consumers but is not needed by this weaker reward-coordinate interface. It still assumes the random next-pair law, bounded-centered source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionFromRewardHistory",
            "ConditionalExpectationReward.generatedActionFromRewardHistory_measurable",
            "ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource",
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalMapSource_of_actionRewardPartialTrajectoryKernel_map_eq",
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalMapSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq",
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalMapSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq",
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_definitionalMapSource",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalMapSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalMapSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalMapSource_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled definitional generated-action map source contract for the COND-EXPECT-REWARD route: it removes the explicit action-trace equality field from GeneratedActionRandomPairMapSource by defining the action trace as the shifted policy-generated trace over finite reward histories, derives timewise action measurability from measurable reward-history state extractors and reward traces, converts to the existing random-pair map source, exposes adapters from full finite-pair, frozen-prefix extension-map partialTraj, and canonical history-step next-pair law hypotheses into that source contract, and exposes full finite-pair-trace partialTraj law plus succ-indexed conditional mean-zero consumers. The mean-zero consumer is available both under a direct integrability hypothesis and from raw reward plus selected-mean range regularity. This still assumes the ambient trajectory-to-condExpKernel law shape as an input and does not construct it or prove a final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-REWARD-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
            "LOCAL-LEAF-POLICY-MEASURABILITY",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-RANDOM-PAIR-MAP-SOURCE-TO-SELECTED-POLICY-REWARD-MAP",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_policy_of_generatedActionRandomPairDefinitionalMapSource",
        ],
        "role": "Compiled project-local source-projection leaf for the COND-EXPECT-REWARD route: a definitional generated random-pair map source now exposes the policy-selected reward-coordinate condExpKernel selected-measure law by lowering through the definitional actual-action reward-map source and unfolding generatedActionFromRewardHistory. It still assumes the definitional random next-pair source and ambient trajectory-to-condExpKernel identification; it does not construct the source or prove final mean-zero, MGF, adaptive, or regret theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-MAP-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-REWARD-MAP-TO-DEFINITIONAL-RANDOM-PAIR-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalMapSource_of_reward_map_eq_selected_policy",
        ],
        "role": "Compiled project-local source-constructor leaf for the COND-EXPECT-REWARD route: a policy-selected reward-coordinate selected-measure law plus context/state measurability now builds the bare GeneratedActionRandomPairDefinitionalMapSource. The proof rewrites the policy-selected law to the generated successor action, lifts it through the frozen-prefix extension-map partialTraj route, and reuses the existing definitional random-pair map source constructor. It still assumes the policy-selected reward-coordinate condExpKernel law and ambient trajectory-to-condExpKernel identification; it adds no raw range, mean range, variance ceiling, MGF witness, or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-REWARD-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-DEFINITIONAL-MAP-SOURCE-RAW-RANGE-MEAN-ZERO",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_reward_map_eq_selected_policy_definitionalMapSource_rawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local mean-zero consumer for the COND-EXPECT-REWARD route: a policy-selected reward-coordinate selected-measure law first builds the bare GeneratedActionRandomPairDefinitionalMapSource, then the source-level raw/mean range consumer yields succ-indexed conditional mean-zero. It still assumes the policy-selected reward-coordinate condExpKernel law, raw reward and selected-mean range regularity, centered reward-kernel law, and ambient trajectory-to-condExpKernel identification; it adds no variance ceiling, MGF witness, or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-REWARD-MAP-TO-DEFINITIONAL-RANDOM-PAIR-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-REWARD-MAP",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-DEFINITIONAL-MAP-SOURCE-UNIFORM-VARIANCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "TAIL-COND-SUBGAUSS",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalMapSource_rawRangeMeasurableMeanRangeUniformVarianceBounded",
        ],
        "role": "Compiled project-local conditional MGF consumer for the COND-EXPECT-REWARD route: a policy-selected reward-coordinate selected-measure law first builds the bare GeneratedActionRandomPairDefinitionalMapSource, then raw/mean range regularity and a global variance ceiling wrap it into the practical uniform-variance source and yield succ-indexed HasCondSubgaussianMGF. It still assumes the policy-selected reward-coordinate condExpKernel law, raw reward and selected-mean range regularity, centered reward-kernel law, a model-side variance ceiling, and ambient trajectory-to-condExpKernel identification; it does not prove the trajectory law or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-REWARD-MAP-TO-DEFINITIONAL-RANDOM-PAIR-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-DEFINITIONAL-MAP-SOURCE-RAW-RANGE-MEAN-ZERO",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-DEFINITIONAL-MAP-SOURCE-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "TAIL-COND-SUBGAUSS",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalMapSource_rawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local coarser-proxy conditional MGF consumer for the COND-EXPECT-REWARD route: a policy-selected reward-coordinate selected-measure law first builds the bare GeneratedActionRandomPairDefinitionalMapSource, then raw/mean range regularity and a global variance ceiling wrap it into the practical uniform-variance source and yield succ-indexed HasCondSubgaussianMGF at any deterministic proxy c satisfying varianceCeiling <= c. It still assumes the policy-selected reward-coordinate condExpKernel law, raw reward and selected-mean range regularity, centered reward-kernel law, a model-side variance ceiling, and ambient trajectory-to-condExpKernel identification; it does not prove the trajectory law or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-REWARD-MAP-TO-DEFINITIONAL-RANDOM-PAIR-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-DEFINITIONAL-MAP-SOURCE-UNIFORM-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-DEFINITIONAL-MAP-SOURCE-HISTORY-VARIANCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "TAIL-COND-SUBGAUSS",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalMapSource_rawRangeMeasurableMeanRangeHistoryVarianceBounded",
        ],
        "role": "Compiled project-local conditional MGF consumer for the COND-EXPECT-REWARD route: a policy-selected reward-coordinate selected-measure law first builds the bare GeneratedActionRandomPairDefinitionalMapSource, then raw/mean range regularity and time-indexed selected-history variance ceilings wrap it into the practical history-variance source and yield succ-indexed HasCondSubgaussianMGF at varianceCeiling i. It still assumes the policy-selected reward-coordinate condExpKernel law, raw reward and selected-mean range regularity, centered reward-kernel law, selected-history variance ceilings, and ambient trajectory-to-condExpKernel identification; it does not prove the trajectory law or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-REWARD-MAP-TO-DEFINITIONAL-RANDOM-PAIR-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-DEFINITIONAL-MAP-SOURCE-RAW-RANGE-MEAN-ZERO",
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-DEFINITIONAL-MAP-SOURCE-UNIFORM-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-HISTORY-VARIANCE-CONSUMER",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-DEFINITIONAL-MAP-SOURCE-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "TAIL-COND-SUBGAUSS",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalMapSource_rawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local coarser-proxy conditional MGF consumer for the COND-EXPECT-REWARD route: a policy-selected reward-coordinate selected-measure law first builds the bare GeneratedActionRandomPairDefinitionalMapSource, then raw/mean range regularity and time-indexed selected-history variance ceilings wrap it into the practical history-variance source and yield succ-indexed HasCondSubgaussianMGF at any deterministic proxy c satisfying varianceCeiling i <= c. It still assumes the policy-selected reward-coordinate condExpKernel law, raw reward and selected-mean range regularity, centered reward-kernel law, selected-history variance ceilings, and ambient trajectory-to-condExpKernel identification; it does not prove the trajectory law or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-REWARD-MAP-TO-DEFINITIONAL-RANDOM-PAIR-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-DEFINITIONAL-MAP-SOURCE-HISTORY-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalMapSource",
        ],
        "role": "Compiled project-local definitional source consumer for the COND-EXPECT-REWARD route: the definitional generated random-pair source over generatedActionFromRewardHistory now directly yields the canonical RewardKernel.actionRewardHistoryStepKernelFamily next-pair law over History.finitePairHistoryOfTrace. This removes explicit action-trace and haction inputs before the canonical pair-law surface, while still assuming the definitional random next-pair law source and ambient trajectory-to-condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-RANDOM-PAIR-HISTORYSTEP-LAW",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairCenteredSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairCenteredSource",
        ],
        "role": "Compiled generated-policy centered source contract for the COND-EXPECT-REWARD route: it packages context/state measurability, the centered reward-kernel law, the generated random next-pair map source, and per-step ambient centered-reward integrability, then consumes the existing source route to expose full finite-pair-trace partialTraj law and succ-indexed conditional mean-zero without a separate h_integrable argument. This still assumes the random pair law source, integrability fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "LOCAL-LEAF-POLICY-MEASURABILITY",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairCenteredSource",
        ],
        "role": "Compiled project-local centered-source canonical pair-law consumer for the COND-EXPECT-REWARD route: a GeneratedActionRandomPairCenteredSource now directly exposes the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law by projecting its packaged GeneratedActionRandomPairMapSource and context/state measurability fields. This keeps the centered law and integrability fields available for later consumers but does not use them to construct the random next-pair law or the ambient condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-COND-MGF-CONSUMER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairCenteredSource",
        ],
        "role": "Compiled project-local centered-source conditional MGF consumer for COND-EXPECT-REWARD: a GeneratedActionRandomPairCenteredSource feeds its generated-action equality, canonical next-pair map law, centered kernel law, and context/state measurability into the history-filtration conditional-MGF route, yielding Mathlib HasCondSubgaussianMGF for the centered successor reward. Ambient centered-reward measurability and deterministic variance-proxy domination remain explicit; exponential integrability is derived by the integrated target-law transfer. The theorem still assumes the random next-pair law source and ambient trajectory-to-condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-COND-MGF-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-COND-MGF-CONSUMER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "MEAS-REWARD",
            "INT-REWARD-BOUNDED",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairBoundedCenteredSource",
        ],
        "role": "Compiled project-local bounded-centered-source conditional MGF consumer for COND-EXPECT-REWARD: a GeneratedActionRandomPairBoundedCenteredSource lowers through the bounded-to-centered source adapter and reuses the centered-source Mathlib HasCondSubgaussianMGF route for the centered successor reward. Ambient centered-reward measurability and deterministic variance-proxy domination remain explicit, while exponential integrability is derived by the integrated target-law transfer; bounded exponential-integrability helpers remain available independently.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-COND-MGF-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-EXP-INTEGRABILITY",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.integrable_exp_mul_of_mem_Icc",
            "ConditionalExpectationReward.centeredReward_succ_integrable_exp_of_generatedActionRandomPairBoundedCenteredSource",
        ],
        "role": "Compiled project-local bounded-centered-source exponential integrability leaf for COND-EXPECT-REWARD: any a.e.-measurable real variable with an a.e. interval bound now has integrable exponential tilts on a finite measure space, and GeneratedActionRandomPairBoundedCenteredSource applies that helper to centered successor rewards. This discharges the exponential-integrability side condition from bounded interval evidence while still leaving centered reward measurability and variance-proxy domination as separate MGF contracts.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "Mathlib.Analysis.SpecialFunctions.Exp",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairBoundedCenteredSource",
        ],
        "role": "Compiled project-local bounded-centered-source canonical pair-law consumer for the COND-EXPECT-REWARD route: a GeneratedActionRandomPairBoundedCenteredSource now directly exposes the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law by lowering through the integrability-based centered source. This preserves the bounded/a.e. regularity route while still assuming the random next-pair law source and ambient condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-CONTRACT",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource",
            "ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_definitionalCenteredSource",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalCenteredSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalCenteredSource",
        ],
        "role": "Compiled definitional generated-policy centered source contract for the COND-EXPECT-REWARD route: it removes explicit action-trace and haction inputs from the centered source layer by using generatedActionFromRewardHistory plus GeneratedActionRandomPairDefinitionalMapSource, converts into the existing GeneratedActionRandomPairCenteredSource, and exposes full finite-pair-trace partialTraj law plus succ-indexed conditional mean-zero consumers. This still assumes the definitional random next-pair law, centered reward integrability fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-COND-MGF-CONSUMER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalCenteredSource",
        ],
        "role": "Compiled project-local definitional centered-source conditional MGF consumer for COND-EXPECT-REWARD: a GeneratedActionRandomPairDefinitionalCenteredSource fixes the action trace to generatedActionFromRewardHistory, lowers to the explicit centered source, and reuses the Mathlib HasCondSubgaussianMGF route for the centered successor reward. This removes explicit action/haction and ambient exponential-integrability inputs at the centered MGF layer; centered-reward measurability and variance-proxy domination remain explicit.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-COND-MGF-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalCenteredSource",
        ],
        "role": "Compiled project-local definitional centered-source canonical pair-law consumer for the COND-EXPECT-REWARD route: a GeneratedActionRandomPairDefinitionalCenteredSource now directly exposes the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law over generatedActionFromRewardHistory by converting through the explicit centered source. This removes explicit action/haction inputs at the centered-source layer while still assuming the definitional random next-pair law source and ambient condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-INTEGRABILITY",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairDefinitionalCenteredSource",
        ],
        "role": "Compiled project-local integrability projection for the COND-EXPECT-REWARD route: a definitional centered generated random-pair source now exposes its packaged per-step ambient centered-reward integrability as a named theorem. It is a direct field projection, useful for consumers that need integrability without unpacking the source structure. It still assumes the definitional centered source fields, including integrability itself, rather than deriving bounds or laws.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairDefinitionalCenteredSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a definitional centered generated random-pair source is weakened into the explicit generated random-pair map source whose action trace is generatedActionFromRewardHistory by projecting its packaged definitional map source. The centered reward-kernel law and integrability fields remain available for stronger consumers but are not needed by this weaker map-source interface. It still assumes the definitional random next-pair law, centered source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalCenteredSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a definitional centered generated random-pair source is weakened into the definitional generated actual-action reward-coordinate source by projecting its packaged definitional random-pair map source into the existing definitional random-pair-to-actual source conversion. The centered reward-kernel law and integrability fields remain available for stronger centered-source consumers but are not needed by this weaker reward-coordinate interface. It still assumes the definitional random next-pair law, centered source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairDefinitionalCenteredSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a definitional centered generated random-pair source is weakened into the explicit generated actual-action reward-coordinate source whose action trace is generatedActionFromRewardHistory. It first projects into the definitional actual-map source and then reuses the definitional-to-explicit actual reward-map conversion. It still assumes the definitional random next-pair law, centered source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource",
            "ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairBoundedCenteredSource",
            "ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_boundedCenteredSource",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairBoundedCenteredSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairBoundedCenteredSource",
        ],
        "role": "Compiled bounded generated-policy centered source contract for the COND-EXPECT-REWARD route: it replaces the centered source's direct per-step ambient integrability field with a.e. measurability plus per-step a.e. interval bounds, derives integrability through Mathlib Integrable.of_mem_Icc, converts into GeneratedActionRandomPairCenteredSource, and exposes the same full finite-pair-trace partialTraj law and succ-indexed conditional mean-zero consumers. This still assumes the random pair law source, a.e. centered-bound evidence, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-MEAN-BOUNDED-SOURCE-CONTRACT",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawMeanBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawMeanBoundedSource",
            "ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_rawMeanBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawMeanBoundedSource",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawMeanBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawMeanBoundedSource",
        ],
        "role": "Compiled raw-reward/selected-mean bounded generated-policy source contract for the COND-EXPECT-REWARD route: it replaces direct centered a.e. measurability and centered interval bounds with separate raw reward and selected mean a.e. measurability plus interval bounds, derives centered measurability via AEMeasurable.sub and centered bounds by interval subtraction, converts into GeneratedActionRandomPairBoundedCenteredSource, and exposes integrability, full finite-pair-trace partialTraj law, and succ-indexed conditional mean-zero consumers. This still assumes the random pair law source, raw/mean bound evidence, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawMeanBoundedSource",
        ],
        "role": "Compiled project-local raw-reward/selected-mean bounded canonical pair-law consumer for the COND-EXPECT-REWARD route: a GeneratedActionRandomPairRawMeanBoundedSource now directly exposes the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law by lowering through the bounded-centered source. This preserves the raw/mean bounded regularity route while still assuming the random next-pair law source and ambient condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawMeanBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a raw-reward/selected-mean bounded generated-policy random next-pair source now directly exposes its packaged GeneratedActionRandomPairMapSource through a stable named projection. The raw reward and selected mean a.e. measurability/bound fields remain available for stronger centered-bound and integrability consumers, but are not needed by this weaker map-source interface. It still assumes the random next-pair law, raw/mean bounded source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-MEAN-BOUNDED-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawMeanBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a raw-reward/selected-mean bounded generated-policy random next-pair source is weakened into the actual-action reward-coordinate map source by projecting its packaged random-pair map source and state-measurability field into the existing random-pair-to-actual source conversion. Its raw reward and selected mean a.e. measurability/bound fields remain available for centered-bound and integrability consumers but are not needed by this weaker reward-coordinate interface. It still assumes the random next-pair law, raw/mean bounded source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEAN-BOUNDED-SOURCE-CONTRACT",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource",
            "ConditionalExpectationReward.rawReward_succ_aemeasurable_of_measurable_reward",
            "ConditionalExpectationReward.generatedActionRandomPairRawMeanBoundedSource_of_rawBoundMeanBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeanBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeanBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeanBoundedSource",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeanBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeanBoundedSource",
        ],
        "role": "Compiled raw-reward-bound/selected-mean bounded generated-policy source contract for the COND-EXPECT-REWARD route: it removes the raw reward a.e. measurability field from the raw/mean bounded source by deriving Rat-to-Real raw reward a.e. measurability from the existing timewise reward trace measurability, then reuses the raw/mean bounded source to expose centered a.e. measurability, centered bounds, integrability, full finite-pair-trace partialTraj law, and succ-indexed conditional mean-zero. This still assumes the random pair law source, raw reward bounds, selected mean measurability/bounds, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "MEAS-REWARD",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeanBoundedSource",
        ],
        "role": "Compiled project-local raw-reward-bound/selected-mean bounded canonical pair-law consumer for the COND-EXPECT-REWARD route: a GeneratedActionRandomPairRawBoundMeanBoundedSource now directly exposes the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law by lowering through the raw/mean bounded source and then the bounded-centered route. This preserves the raw reward measurability-from-hreward layer while still assuming the random next-pair law source and ambient condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawBoundMeanBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a raw-reward-bound/selected-mean bounded generated-policy random next-pair source now directly exposes its packaged GeneratedActionRandomPairMapSource through a stable named projection. The raw reward interval bounds and selected mean a.e. measurability/bound fields remain available for stronger centered-bound and integrability consumers, but are not needed by this weaker map-source interface. It still assumes the random next-pair law, raw-bound/mean-bounded source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEAN-BOUNDED-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeanBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a raw-reward-bound/selected-mean bounded generated-policy random next-pair source is weakened into the actual-action reward-coordinate map source by projecting its packaged random-pair map source and state-measurability field into the existing random-pair-to-actual source conversion. Its raw reward bounds and selected mean a.e. measurability/bound fields remain available for centered-bound and integrability consumers but are not needed by this weaker reward-coordinate interface. It still assumes the random next-pair law, raw-bound/mean-bounded source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-CONTRACT",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource",
            "ConditionalExpectationReward.selectedMean_succ_aemeasurable_of_measurable_mean",
            "ConditionalExpectationReward.generatedActionRandomPairRawBoundMeanBoundedSource_of_rawBoundMeasurableMeanBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource",
        ],
        "role": "Compiled raw-reward-bound/measurable-selected-mean generated-policy source contract for the COND-EXPECT-REWARD route: it removes the selected-mean a.e. measurability field from the raw-bound/mean-bounded source by deriving Rat-to-Real selected-mean a.e. measurability from a measurable mean surface composed with finite reward histories, context/state extractors, and the measurable policy action, then reuses the raw-bound/mean-bounded source to expose centered a.e. measurability, centered bounds, integrability, full finite-pair-trace partialTraj law, and succ-indexed conditional mean-zero. This still assumes the random pair law source, raw reward bounds, selected mean bounds, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "MEAS-REWARD",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-MEAN-ZERO",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource",
        ],
        "role": "Compiled project-local source-level raw-bound/measurable-selected-mean conditional mean-zero consumer leaf for the COND-EXPECT-REWARD route: a GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource packages the generated random-pair law source, centered reward-kernel law, raw reward interval bounds, selected-mean interval bounds, and mean measurability, then yields the succ-indexed ordinary conditional expectation zero statement. The proof lowers the source to the raw-bound/mean-bounded layer and reuses that compiled conditional mean-zero consumer. It still assumes the packaged random next-pair law, source regularity fields, and ambient trajectory-to-condExpKernel identification; it adds no variance ceiling, conditional MGF witness, adaptive law identification, or final regret theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawBoundMeasurableMeanBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a raw-reward-bound/measurable-selected-mean generated-policy random next-pair source now directly exposes its packaged GeneratedActionRandomPairMapSource through a stable named projection. The measurable mean surface, raw reward interval bounds, and selected mean bound fields remain available for stronger centered-bound and integrability consumers, but are not needed by this weaker map-source interface. It still assumes the random next-pair law, raw-bound/measurable-mean source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource",
        ],
        "role": "Compiled project-local raw-reward-bound/measurable-selected-mean canonical pair-law consumer for the COND-EXPECT-REWARD route: a GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource now directly exposes the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law by lowering through the raw-bound/mean-bounded source and then the raw/mean bounded route. This preserves the measurable selected-mean surface layer while still assuming the random next-pair law source and ambient condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeasurableMeanBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a raw-reward-bound/measurable-selected-mean generated-policy random next-pair source is weakened into the actual-action reward-coordinate map source by projecting its packaged random-pair map source and state-measurability field into the existing random-pair-to-actual source conversion. Its measurable mean surface, raw reward bounds, and selected mean bound fields remain available for centered-bound and integrability consumers but are not needed by this weaker reward-coordinate interface. It still assumes the random next-pair law, raw-bound/measurable-mean source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.selectedMean_succ_bound_of_mean_range_bound",
            "ConditionalExpectationReward.generatedActionRandomPairRawBoundMeasurableMeanBoundedSource_of_rawBoundMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled raw-reward-bound/measurable-mean-range generated-policy source contract for the COND-EXPECT-REWARD route: it removes the selected-mean a.e. bound field from the raw-bound/measurable-mean source by deriving selected-mean interval evidence from a deterministic pointwise range bound on the mean surface, then reuses the measurable-mean source to expose centered a.e. measurability, centered bounds, integrability, full finite-pair-trace partialTraj law, and succ-indexed conditional mean-zero. This still assumes the random pair law source, raw reward bounds, mean measurability, deterministic mean range bounds, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "MEAS-REWARD",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-MEAN-ZERO",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local source-level raw-bound/measurable-mean-range conditional mean-zero consumer leaf for the COND-EXPECT-REWARD route: a GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource packages the generated random-pair law source, centered reward-kernel law, raw reward interval bounds, mean measurability, and deterministic selected-mean range bounds, then yields the succ-indexed ordinary conditional expectation zero statement. The proof lowers the source to the raw-bound/measurable-mean bounded layer and reuses that compiled conditional mean-zero consumer. It still assumes the packaged random next-pair law, source regularity fields, and ambient trajectory-to-condExpKernel identification; it adds no variance ceiling, conditional MGF witness, adaptive law identification, or final regret theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawBoundMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a raw-reward-bound/measurable-mean-range bounded generated-policy random next-pair source now directly exposes its packaged GeneratedActionRandomPairMapSource through a stable named projection. The measurable mean surface, raw reward interval bounds, and deterministic mean range bounds remain available for stronger centered-bound and integrability consumers, but are not needed by this weaker map-source interface. It still assumes the random next-pair law, raw-bound/measurable-mean-range source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local raw-reward-bound/measurable-mean-range canonical pair-law consumer for the COND-EXPECT-REWARD route: a GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource now directly exposes the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law by lowering through the raw-bound/measurable-mean source and then the raw-bound/mean-bounded route. This preserves the deterministic selected-mean range-bound layer while still assuming the random next-pair law source and ambient condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a raw-reward-bound/measurable-mean-range bounded generated-policy random next-pair source is weakened into the actual-action reward-coordinate map source by projecting its packaged random-pair map source and state-measurability field into the existing random-pair-to-actual source conversion. Its measurable mean surface, raw reward bounds, and deterministic mean range bound fields remain available for centered-bound and integrability consumers but are not needed by this weaker reward-coordinate interface. It still assumes the random next-pair law, raw-bound/measurable-mean-range source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.rawReward_succ_bound_of_reward_range_bound",
            "ConditionalExpectationReward.centeredReward_succ_integrable_of_rawRangeMeasurableMeanRangeBounded",
            "ConditionalExpectationReward.generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource_of_rawRangeMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled raw-reward-range/measurable-mean-range generated-policy source contract for the COND-EXPECT-REWARD route: it removes the raw-reward a.e. bound field from the raw-bound/measurable-mean-range source by deriving raw reward interval evidence from a deterministic pointwise range bound on the reward trace, exposes a source-free regularity helper turning raw reward and selected-mean range evidence into centered-reward integrability, then reuses the raw-bound/measurable-mean-range source to expose centered a.e. measurability, centered bounds, integrability, full finite-pair-trace partialTraj law, and succ-indexed conditional mean-zero. This still assumes the random pair law source, mean measurability, deterministic raw reward and mean range bounds, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "MEAS-REWARD",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-MEAN-ZERO",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local source-level raw-range conditional mean-zero consumer leaf for the COND-EXPECT-REWARD route: a GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource packages the generated random-pair law source, centered reward-kernel law, mean measurability, deterministic raw reward range bounds, and deterministic selected-mean range bounds, then yields the succ-indexed ordinary conditional expectation zero statement. The proof lowers the source to the raw-bound/measurable-mean-range layer and reuses that compiled conditional mean-zero consumer. It still assumes the packaged random next-pair law, source regularity fields, and ambient trajectory-to-condExpKernel identification; it adds no variance ceiling, conditional MGF witness, adaptive law identification, or final regret theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairRawRangeMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local source-projection leaf for the COND-EXPECT-REWARD route: the explicit top raw-reward-range/measurable-mean-range bounded generated random-pair source now directly exposes its packaged GeneratedActionRandomPairMapSource by a stable named wrapper. This is the explicit-action counterpart of the definitional raw-range map-source projection; it still assumes the packaged random next-pair law and all top-layer source regularity fields.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local raw-reward-range/measurable-mean-range canonical pair-law consumer for the COND-EXPECT-REWARD route: a GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource now directly exposes the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law by lowering through the raw-bound/measurable-mean-range source and then the measurable-mean route. This preserves the deterministic raw reward and selected-mean range-bound layer while still assuming the random next-pair law source and ambient condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawRangeMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a raw-reward-range/measurable-mean-range bounded generated-policy random next-pair source is weakened into the actual-action reward-coordinate map source by projecting its packaged random-pair map source and state-measurability field into the existing random-pair-to-actual source conversion. Its deterministic raw reward and mean range fields remain available for centered-bound and integrability consumers but are not needed by this weaker reward-coordinate interface. It still assumes the random next-pair law, raw-range/measurable-mean-range source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_actionRewardPartialTrajectoryKernel_map_eq",
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq",
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq",
            "ConditionalExpectationReward.generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeBounded",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeBounded",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeBounded",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeBounded",
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled definitional generated-action raw-range/measurable-mean-range source contract for the COND-EXPECT-REWARD route: it removes the explicit action trace and timewise action-measurability inputs from the practical raw-range source by using generatedActionFromRewardHistory plus GeneratedActionRandomPairDefinitionalMapSource; it now also builds that practical top-layer source directly from full finite-pair, frozen-prefix extension-map partialTraj, and canonical history-step next-pair law hypotheses plus raw/mean range regularity, converts to the existing raw-range source to expose integrability and full finite-pair-trace partialTraj law, directly consumes the full finite-pair `partialTraj` law plus regularity into succ-indexed conditional mean-zero, directly consumes the frozen-prefix extension-map law plus regularity into the same mean-zero fact, directly consumes the canonical history-step next-pair law plus regularity into the same mean-zero fact, and directly consumes generated-action policy-selected or actual-action reward-coordinate selected-measure laws plus regularity into mean-zero. This still assumes the reward-coordinate/next-pair/ambient trajectory-to-condExpKernel law shape as an input and does not construct sub-Gaussian witnesses or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "MEAS-REWARD",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-RAW-RANGE-MEASURABLE-MEAN-RANGE-MEAN-ZERO",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local conditional mean-zero consumer leaf for the COND-EXPECT-REWARD route: an actual-action reward-coordinate selected-measure law over generatedActionFromRewardHistory plus context/state measurability, mean measurability, centered kernel law, and deterministic raw reward and selected-mean range bounds yields the succ-indexed ordinary conditional expectation zero statement for the centered selected reward. The proof derives the generated action trace and frozen-prefix extension-map law, then reuses the compiled extension-map raw-range/measurable-mean-range mean-zero consumer. It still assumes the actual-action reward-coordinate condExpKernel law, raw/mean range regularity, and ambient trajectory-to-condExpKernel identification; it adds no variance ceiling, MGF witness, or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-REWARD-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-REWARD-MAP-RAW-RANGE-MEASURABLE-MEAN-RANGE-MEAN-ZERO",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local conditional mean-zero consumer leaf for the COND-EXPECT-REWARD route: a policy-selected reward-coordinate selected-measure law over generatedActionFromRewardHistory plus context/state measurability, mean measurability, centered kernel law, and deterministic raw reward and selected-mean range bounds yields the succ-indexed ordinary conditional expectation zero statement for the centered selected reward. The proof uses generatedActionFromRewardHistory measurability and the definitional equality to Policy.generatedActionTraceSucc, then reuses the selected-policy raw-range/measurable-mean-range generated-action consumer. It still assumes the policy-selected reward-coordinate condExpKernel law, raw/mean range regularity, and ambient trajectory-to-condExpKernel identification; it adds no variance ceiling, MGF witness, or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-REWARD-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-RAW-RANGE-MEASURABLE-MEAN-RANGE-MEAN-ZERO",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_generatedActionDefinitionalActualRewardMapSource",
        ],
        "role": "Compiled project-local source-constructor leaf for the COND-EXPECT-REWARD route: a packaged definitional actual-action reward-coordinate source plus context measurability, mean measurability, centered kernel law, and deterministic raw reward and selected-mean range bounds builds the base definitional raw-range/measurable-mean-range generated random-pair source. The proof reuses the compiled definitional actual-source to definitional random-pair map-source bridge and then copies the regularity fields into the practical raw-range source. It still assumes the packaged actual-action reward-coordinate law, raw/mean range regularity, and ambient trajectory-to-condExpKernel identification; it adds no variance ceiling, MGF witness, or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-DEFINITIONAL-RANDOM-PAIR-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-RAW-RANGE-MEASURABLE-MEAN-RANGE-MEAN-ZERO",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeBounded",
        ],
        "role": "Compiled project-local conditional mean-zero consumer leaf for the COND-EXPECT-REWARD route: a packaged definitional actual-action reward-coordinate source plus context measurability, mean measurability, centered kernel law, and deterministic raw reward and selected-mean range bounds yields the succ-indexed ordinary conditional expectation zero statement for the centered selected reward over generatedActionFromRewardHistory. The proof reuses the direct reward-coordinate selected-measure raw-range/measurable-mean-range consumer while taking state measurability and reward-coordinate law evidence from the packaged source. It still assumes the packaged actual-action reward-coordinate law, raw/mean range regularity, and ambient trajectory-to-condExpKernel identification; it adds no variance ceiling, MGF witness, or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-UNIFORM-VARIANCE-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_generatedActionDefinitionalActualRewardMapSource",
        ],
        "role": "Compiled project-local source-constructor leaf for the COND-EXPECT-REWARD conditional MGF route: a packaged definitional actual-action reward-coordinate source plus context/mean/kernel/raw-range/mean-range regularity and a global varianceProxy ceiling builds the packaged definitional raw-range/measurable-mean-range uniform-variance source. The proof reuses the packaged actual-source to raw-range source constructor and then stores the global variance bound for downstream MGF consumers. It still assumes the packaged actual-action reward-coordinate law, raw/mean range regularity, a model-side variance ceiling, and ambient trajectory-to-condExpKernel identification; it does not prove an MGF witness or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-UNIFORM-VARIANCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded",
        ],
        "role": "Compiled project-local conditional MGF consumer leaf for the COND-EXPECT-REWARD route: a packaged definitional actual-action reward-coordinate source plus context/mean/kernel/raw-range/mean-range regularity and a global varianceProxy ceiling directly yields the succ-indexed HasCondSubgaussianMGF witness with proxy varianceCeiling. The proof builds the packaged definitional raw-range/measurable-mean-range uniform-variance source and reuses its source-level MGF consumer. It still assumes the packaged actual-action reward-coordinate law, raw/mean range regularity, a model-side variance ceiling, and ambient trajectory-to-condExpKernel identification; it does not prove the reward law or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local coarser-proxy conditional MGF consumer leaf for the COND-EXPECT-REWARD route: a packaged definitional actual-action reward-coordinate source plus context/mean/kernel/raw-range/mean-range regularity, a global varianceProxy ceiling, and varianceCeiling <= c directly yields the succ-indexed HasCondSubgaussianMGF witness with proxy c. The proof builds the packaged definitional raw-range/measurable-mean-range uniform-variance source and reuses the source-level larger-proxy MGF consumer. It still assumes the packaged actual-action reward-coordinate law, raw/mean range regularity, a model-side variance ceiling, the coarser-proxy domination, and ambient trajectory-to-condExpKernel identification; it does not prove the reward law or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-UNIFORM-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-HISTORY-VARIANCE-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_generatedActionDefinitionalActualRewardMapSource",
        ],
        "role": "Compiled project-local source-constructor leaf for the COND-EXPECT-REWARD conditional MGF route: a packaged definitional actual-action reward-coordinate source plus context/mean/kernel/raw-range/mean-range regularity and time-indexed selected-history variance ceilings builds the packaged definitional raw-range/measurable-mean-range history-variance source. The proof reuses the packaged actual-source to raw-range source constructor and then stores the selected-history bound for downstream MGF consumers. It still assumes the packaged actual-action reward-coordinate law, raw/mean range regularity, selected-history variance ceilings, and ambient trajectory-to-condExpKernel identification; it does not prove an MGF witness or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-HISTORY-VARIANCE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-HISTORY-VARIANCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded",
        ],
        "role": "Compiled project-local conditional MGF consumer leaf for the COND-EXPECT-REWARD route: a packaged definitional actual-action reward-coordinate source plus context/mean/kernel/raw-range/mean-range regularity and time-indexed selected-history variance ceilings directly yields the succ-indexed HasCondSubgaussianMGF witness with proxy varianceCeiling i. The proof builds the packaged definitional raw-range/measurable-mean-range history-variance source and reuses its source-level MGF consumer. It still assumes the packaged actual-action reward-coordinate law, raw/mean range regularity, selected-history variance ceilings, and ambient trajectory-to-condExpKernel identification; it does not prove the reward law or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-HISTORY-VARIANCE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local coarser-proxy conditional MGF consumer leaf for the COND-EXPECT-REWARD route: a packaged definitional actual-action reward-coordinate source plus context/mean/kernel/raw-range/mean-range regularity, time-indexed selected-history variance ceilings, and varianceCeiling i <= c directly yields the succ-indexed HasCondSubgaussianMGF witness with proxy c. The proof builds the packaged definitional raw-range/measurable-mean-range history-variance source and reuses the source-level larger-proxy MGF consumer. It still assumes the packaged actual-action reward-coordinate law, raw/mean range regularity, selected-history variance ceilings, the coarser-proxy domination, and ambient trajectory-to-condExpKernel identification; it does not prove the reward law or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "LOCAL-LEAF-COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-HISTORY-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_reward_map_eq_actual_action",
        ],
        "role": "Compiled project-local source-constructor leaf for the COND-EXPECT-REWARD route: an actual-action reward-coordinate selected-measure law plus raw reward range, selected-mean range, centered kernel law, and context/state/mean measurability now directly builds the base definitional raw-range/measurable-mean-range generated random-pair source. The proof lifts the reward-coordinate law to the frozen-prefix extension-map partialTraj law and reuses the existing base source constructor. It still assumes the actual-action reward-coordinate condExpKernel law and ambient trajectory-to-condExpKernel identification; it adds no variance ceiling, MGF witness, or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-REWARD-MAP",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-REWARD-MAP-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_reward_map_eq_selected_policy",
        ],
        "role": "Compiled project-local source-constructor leaf for the COND-EXPECT-REWARD route: a policy-selected reward-coordinate selected-measure law plus raw reward range, selected-mean range, centered kernel law, and context/state/mean measurability now directly builds the base definitional raw-range/measurable-mean-range generated random-pair source. The proof rewrites the policy-selected action to generatedActionFromRewardHistory's successor action and reuses the actual-action base source constructor. It still assumes the policy-selected reward-coordinate condExpKernel law and ambient trajectory-to-condExpKernel identification; it adds no variance ceiling, MGF witness, or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_map_eq",
        ],
        "role": "Compiled project-local practical source constructor for the COND-EXPECT-REWARD conditional MGF route: a full finite-pair-trace partialTraj law, raw reward range, selected-mean range, centered kernel law, and global varianceProxy ceiling now directly build the packaged definitional raw-range/measurable-mean-range uniform-variance source. It still assumes the full partialTraj/condExpKernel law and a model-side variance ceiling; it does not construct the trajectory law, derive the ceiling from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for the COND-EXPECT-REWARD route: a full finite-pair-trace partialTraj law, raw reward range, selected-mean range, centered kernel law, and a global varianceProxy ceiling now directly yield the succ-indexed HasCondSubgaussianMGF witness with proxy varianceCeiling. It still assumes the full partialTraj/condExpKernel law and a model-side global variance ceiling; it does not construct the trajectory law, derive the ceiling from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for coarser downstream proxies from the full finite-pair partialTraj law plus a global variance surface: the existing full finite-pair partialTraj law plus raw/mean range regularity and a global varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling <= c. The proof constructs the packaged full-trace uniform-variance source and reuses the packaged uniform-source larger-proxy consumer; it still assumes the full finite-pair partialTraj/condExpKernel law and does not construct the ambient trajectory law or final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-COND-MGF",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_map_eq",
        ],
        "role": "Compiled project-local practical source constructor for the COND-EXPECT-REWARD conditional MGF route: a full finite-pair-trace partialTraj law, raw reward range, selected-mean range, centered kernel law, and a time-indexed selected-history varianceProxy ceiling now directly build the packaged definitional raw-range/measurable-mean-range history-variance source. It still assumes the full partialTraj/condExpKernel law and a model-side selected-history variance ceiling; it does not construct the trajectory law, derive the ceiling from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-HISTORY-VARIANCE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for the COND-EXPECT-REWARD route: a full finite-pair-trace partialTraj law, raw reward range, selected-mean range, centered kernel law, and a time-indexed selected-history varianceProxy ceiling now directly yield the succ-indexed HasCondSubgaussianMGF witness with proxy varianceCeiling i. It still assumes the full partialTraj/condExpKernel law and a model-side selected-history variance ceiling; it does not construct the trajectory law, derive the ceiling from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for coarser downstream proxies from the full finite-pair partialTraj law plus selected-history variance surface: the existing full finite-pair partialTraj law plus raw/mean range regularity and a time-indexed selected-history varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling i <= c. The proof constructs the packaged full-trace history-variance source and reuses the packaged history-source larger-proxy consumer; it still assumes the full finite-pair partialTraj/condExpKernel law and does not construct the ambient trajectory law or final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-COND-MGF",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq",
        ],
        "role": "Compiled project-local practical source constructor for the COND-EXPECT-REWARD conditional MGF route: a frozen-prefix extension-map partialTraj law, raw reward range, selected-mean range, centered kernel law, and global varianceProxy ceiling now directly build the packaged definitional raw-range/measurable-mean-range uniform-variance source. It still assumes the extension-map partialTraj/condExpKernel law and a model-side variance ceiling; it does not construct the trajectory law, derive the ceiling from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for the COND-EXPECT-REWARD route: a frozen-prefix extension-map partialTraj law, raw reward range, selected-mean range, centered kernel law, and a global varianceProxy ceiling now directly yield the succ-indexed HasCondSubgaussianMGF witness with proxy varianceCeiling. It still assumes the extension-map partialTraj/condExpKernel law and a model-side global variance ceiling; it does not construct the trajectory law, derive the ceiling from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for coarser downstream proxies from the frozen-prefix extension-map partialTraj law plus a global variance surface: the existing extension-map law plus raw/mean range regularity and a global varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling <= c. The proof constructs the packaged extension-map uniform-variance source and reuses the packaged uniform-source larger-proxy consumer; it still assumes the extension-map partialTraj/condExpKernel law and does not construct the ambient trajectory law or final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-COND-MGF",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-UNIFORM-VARIANCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for the COND-EXPECT-REWARD route: an actual-action reward-coordinate selected-measure law, raw reward range, selected-mean range, centered kernel law, and a global varianceProxy ceiling now directly yield the succ-indexed HasCondSubgaussianMGF witness with proxy varianceCeiling. It reuses the generated-action reward-map-to-extension-map adapter and the frozen-prefix extension-map uniform-variance MGF consumer. It still assumes the reward-coordinate condExpKernel law and a model-side global variance ceiling; it does not construct the reward-coordinate law, derive the ceiling from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-REWARD-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for coarser downstream proxies from the actual-action reward-coordinate selected-measure law surface: the existing actual-action law plus raw/mean range regularity and a global varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling <= c. The proof constructs the packaged uniform-variance source and reuses the packaged uniform-source larger-proxy consumer; it still assumes the reward-coordinate condExpKernel law and does not construct the ambient trajectory law or final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-UNIFORM-VARIANCE-COND-MGF",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-UNIFORM-VARIANCE-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_reward_map_eq_actual_action",
        ],
        "role": "Compiled project-local practical source constructor for the COND-EXPECT-REWARD route: an actual-action reward-coordinate selected-measure law, raw reward range, selected-mean range, centered kernel law, and a global varianceProxy ceiling now build the packaged definitional raw-range/measurable-mean-range uniform-variance source. It reuses the generated-action reward-map-to-extension-map adapter and the frozen-prefix extension-map uniform-variance source constructor. It still assumes the reward-coordinate condExpKernel law and a model-side global variance ceiling; it does not construct the reward-coordinate law, derive the ceiling from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-UNIFORM-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-REWARD-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-HISTORY-VARIANCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for the COND-EXPECT-REWARD route: an actual-action reward-coordinate selected-measure law, raw reward range, selected-mean range, centered kernel law, and selected finite-history varianceProxy ceilings now directly yield the succ-indexed HasCondSubgaussianMGF witness with proxy varianceCeiling i. It reuses the generated-action reward-map-to-extension-map adapter and the frozen-prefix extension-map history-variance MGF consumer. It still assumes the reward-coordinate condExpKernel law and model-side selected-history variance ceilings; it does not construct the reward-coordinate law, derive the ceilings from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-HISTORY-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-UNIFORM-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-REWARD-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-HISTORY-VARIANCE-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_reward_map_eq_actual_action",
        ],
        "role": "Compiled project-local practical source constructor for the COND-EXPECT-REWARD route: an actual-action reward-coordinate selected-measure law, raw reward range, selected-mean range, centered kernel law, and selected finite-history varianceProxy ceilings now build the packaged definitional raw-range/measurable-mean-range history-variance source. It reuses the generated-action reward-map-to-extension-map adapter and the frozen-prefix extension-map history-variance source constructor. It still assumes the reward-coordinate condExpKernel law and model-side selected-history variance ceilings; it does not construct the reward-coordinate law, derive the ceilings from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-HISTORY-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-REWARD-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for coarser downstream proxies from the actual-action reward-coordinate selected-measure law plus selected-history variance surface: the existing actual-action law plus raw/mean range regularity and a time-indexed selected-history varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling i <= c. The proof constructs the packaged actual-action history-variance source and reuses the packaged history-source larger-proxy consumer; it still assumes the reward-coordinate condExpKernel law and does not construct the ambient trajectory law or final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-HISTORY-VARIANCE-COND-MGF",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-UNIFORM-VARIANCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for the COND-EXPECT-REWARD route: a policy-selected reward-coordinate selected-measure law, raw reward range, selected-mean range, centered kernel law, and a global varianceProxy ceiling now directly yield the succ-indexed HasCondSubgaussianMGF witness with proxy varianceCeiling. It rewrites the policy-facing law to the generated successor action and reuses the actual-action reward-map uniform-variance MGF consumer. It still assumes the policy-selected reward-coordinate condExpKernel law and a model-side global variance ceiling; it does not construct the reward-coordinate law, derive the ceiling from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-UNIFORM-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-UNIFORM-VARIANCE-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_reward_map_eq_selected_policy",
        ],
        "role": "Compiled project-local practical source constructor for the COND-EXPECT-REWARD route: a policy-selected reward-coordinate selected-measure law, raw reward range, selected-mean range, centered kernel law, and a global varianceProxy ceiling now build the packaged definitional raw-range/measurable-mean-range uniform-variance source. It rewrites the policy-facing law to the generated successor action and reuses the actual-action reward-map uniform-variance source constructor. It still assumes the policy-selected reward-coordinate condExpKernel law and a model-side global variance ceiling; it does not construct the reward-coordinate law, derive the ceiling from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-UNIFORM-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for coarser downstream proxies from the policy-selected reward-coordinate selected-measure law surface: the existing policy-selected law plus raw/mean range regularity and a global varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling <= c. The proof constructs the packaged policy-selected uniform-variance source and reuses the packaged uniform-source larger-proxy consumer; it still assumes the reward-coordinate condExpKernel law and does not construct the ambient trajectory law or final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-UNIFORM-VARIANCE-COND-MGF",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-HISTORY-VARIANCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for the COND-EXPECT-REWARD route: a policy-selected reward-coordinate selected-measure law, raw reward range, selected-mean range, centered kernel law, and selected finite-history varianceProxy ceilings now directly yield the succ-indexed HasCondSubgaussianMGF witness with proxy varianceCeiling i. It rewrites the policy-facing law to the generated successor action and reuses the actual-action reward-map history-variance MGF consumer. It still assumes the policy-selected reward-coordinate condExpKernel law and model-side selected-history variance ceilings; it does not construct the reward-coordinate law, derive the ceilings from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-HISTORY-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-UNIFORM-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-HISTORY-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-HISTORY-VARIANCE-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_reward_map_eq_selected_policy",
        ],
        "role": "Compiled project-local practical source constructor for the COND-EXPECT-REWARD route: a policy-selected reward-coordinate selected-measure law, raw reward range, selected-mean range, centered kernel law, and selected finite-history varianceProxy ceilings now build the packaged definitional raw-range/measurable-mean-range history-variance source. It rewrites the policy-facing law to the generated successor action and reuses the actual-action reward-map history-variance source constructor. It still assumes the policy-selected reward-coordinate condExpKernel law and model-side selected-history variance ceilings; it does not construct the reward-coordinate law, derive the ceilings from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-HISTORY-VARIANCE-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for coarser downstream proxies from the policy-selected reward-coordinate selected-measure law plus selected-history variance surface: the existing policy-selected law plus raw/mean range regularity and a time-indexed selected-history varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling i <= c. The proof constructs the packaged policy-selected history-variance source and reuses the packaged history-source larger-proxy consumer; it still assumes the reward-coordinate condExpKernel law and does not construct the ambient trajectory law or final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-SELECTED-POLICY-HISTORY-VARIANCE-COND-MGF",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-HISTORY-VARIANCE-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq",
        ],
        "role": "Compiled project-local practical source constructor for the COND-EXPECT-REWARD conditional MGF route: a frozen-prefix extension-map partialTraj law, raw reward range, selected-mean range, centered kernel law, and a time-indexed selected-history varianceProxy ceiling now directly build the packaged definitional raw-range/measurable-mean-range history-variance source. It still assumes the extension-map partialTraj/condExpKernel law and a model-side selected-history variance ceiling; it does not construct the trajectory law, derive the ceiling from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-HISTORY-VARIANCE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-HISTORY-VARIANCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for the COND-EXPECT-REWARD route: a frozen-prefix extension-map partialTraj law, raw reward range, selected-mean range, centered kernel law, and a time-indexed selected-history varianceProxy ceiling now directly yield the succ-indexed HasCondSubgaussianMGF witness with proxy varianceCeiling i. It still assumes the extension-map partialTraj/condExpKernel law and a model-side selected-history variance ceiling; it does not construct the trajectory law, derive the ceiling from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for coarser downstream proxies from the frozen-prefix extension-map partialTraj law plus selected-history variance surface: the existing extension-map law plus raw/mean range regularity and a time-indexed selected-history varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling i <= c. The proof constructs the packaged extension-map history-variance source and reuses the packaged history-source larger-proxy consumer; it still assumes the extension-map partialTraj/condExpKernel law and does not construct the ambient trajectory law or final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-HISTORY-VARIANCE-COND-MGF",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-UNIFORM-VARIANCE-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq",
        ],
        "role": "Compiled project-local practical source constructor for the COND-EXPECT-REWARD conditional MGF route: a canonical history-step next-pair law, raw reward range, selected-mean range, centered kernel law, and global varianceProxy ceiling now directly build the packaged definitional raw-range/measurable-mean-range uniform-variance source. It still assumes the history-step pair-map condExpKernel law and a model-side variance ceiling; it does not construct the next-pair law, derive the ceiling from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-HISTORYSTEP-REWARD-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-UNIFORM-VARIANCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for the COND-EXPECT-REWARD route: a canonical history-step next-pair law, raw reward range, selected-mean range, centered kernel law, and a global varianceProxy ceiling now directly yield the succ-indexed HasCondSubgaussianMGF witness with proxy varianceCeiling. It still assumes the history-step pair-map condExpKernel law and a model-side global variance ceiling; it does not construct the next-pair law, derive the ceiling from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-HISTORYSTEP-REWARD-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for coarser downstream proxies from the canonical history-step next-pair law plus a global variance surface: the existing history-step pair-map law plus raw/mean range regularity and a global varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling <= c. The proof constructs the packaged history-step uniform-variance source and reuses the packaged uniform-source larger-proxy consumer; it still assumes the history-step pair-map condExpKernel law and does not construct the ambient trajectory law or final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-UNIFORM-VARIANCE-COND-MGF",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-HISTORY-VARIANCE-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq",
        ],
        "role": "Compiled project-local practical source constructor for the COND-EXPECT-REWARD conditional MGF route: a canonical history-step next-pair law, raw reward range, selected-mean range, centered kernel law, and a time-indexed selected-history varianceProxy ceiling now directly build the packaged definitional raw-range/measurable-mean-range history-variance source. It still assumes the history-step pair-map condExpKernel law and a model-side selected-history variance ceiling; it does not construct the next-pair law, derive the ceiling from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-UNIFORM-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-HISTORYSTEP-REWARD-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-HISTORY-VARIANCE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-HISTORY-VARIANCE-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for the COND-EXPECT-REWARD route: a canonical history-step next-pair law, raw reward range, selected-mean range, centered kernel law, and a time-indexed selected-history varianceProxy ceiling now directly yield the succ-indexed HasCondSubgaussianMGF witness with proxy varianceCeiling i. It still assumes the history-step pair-map condExpKernel law and a model-side selected-history variance ceiling; it does not construct the next-pair law, derive the ceiling from ranges, or prove a final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-HISTORYSTEP-REWARD-MAP",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for coarser downstream proxies from the canonical history-step next-pair law plus selected-history variance surface: the existing history-step pair-map law plus raw/mean range regularity and a time-indexed selected-history varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling i <= c. The proof constructs the packaged history-step history-variance source and reuses the packaged history-source larger-proxy consumer; it still assumes the history-step pair-map condExpKernel law and does not construct the ambient trajectory law or final adaptive theorem.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-HISTORY-VARIANCE-COND-MGF",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local definitional raw-reward-range/measurable-mean-range canonical pair-law consumer for the COND-EXPECT-REWARD route: a GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource now directly exposes the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law over generatedActionFromRewardHistory by lowering through the explicit raw-range source. This preserves the practical implicit-action surface while still assuming the definitional random next-pair law source and ambient condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a definitional raw-reward-range/measurable-mean-range bounded generated-policy random next-pair source is weakened directly into the explicit generated random-pair map source whose action trace is generatedActionFromRewardHistory, by projecting its packaged definitional map source through the existing definitional-to-explicit random-pair map conversion. Its centered-law, raw reward range, and mean range fields remain for stronger consumers but are not needed by this weaker map-source interface. It still assumes the definitional random next-pair law, raw-range/measurable-mean-range source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-PARTIALTRAJ-PAIR-LAW-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a practical definitional raw-reward-range/measurable-mean-range bounded generated-policy random next-pair source now weakens directly into GeneratedActionPartialTrajectoryPairLawSource by projecting its packaged definitional map source and context measurability. Its centered-law, raw reward range, mean range, and variance-proxy fields remain available for stronger consumers but are not needed by this weaker partialTraj source interface. It still assumes the packaged definitional random next-pair law and does not prove the ambient partialTraj/condExpKernel trajectory identification or final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-DEFINITIONAL-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-CENTERED-REGULARITY",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_measurable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local regularity leaf for the COND-EXPECT-REWARD route: the practical definitional raw-reward-range/measurable-mean-range generated-policy random next-pair source now exposes centered successor reward a.e. measurability, full measurability, and the centered interval bound directly. Full measurability is derived from timewise reward measurability, finite reward-history context/state measurability, policy measurability, and the measurable mean surface; the interval bound still lowers through the explicit raw-range source conversion. It still assumes the definitional random next-pair law, mean measurability, deterministic raw reward and mean range bounds, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "MEAS-REWARD",
            "MEAS-POLICY",
            "MEAS-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-BOUNDED-CENTERED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: the practical definitional raw-reward-range/measurable-mean-range generated-policy random next-pair source now yields the bounded centered source over generatedActionFromRewardHistory directly. It packages the existing definitional-to-explicit random-pair map projection together with the centered successor reward a.e. measurability and interval bounds, making the bounded-centered integrability and downstream conditional reward-law consumers addressable through one source contract. It still assumes the definitional random next-pair law, mean measurability, deterministic raw reward and mean range bounds, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-CENTERED-REGULARITY",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "MEAS-REWARD",
            "MEAS-POLICY",
            "MEAS-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-CENTERED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: the practical definitional raw-reward-range/measurable-mean-range generated-policy random next-pair source now yields the integrability-based centered source over generatedActionFromRewardHistory directly. It lowers through the bounded-centered source wrapper and then reuses the existing bounded-centered-to-centered conversion, making all existing centered-source consumers available from the practical top-level source contract. It still assumes the definitional random next-pair law, mean measurability, deterministic raw reward and mean range bounds, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-BOUNDED-CENTERED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "MEAS-REWARD",
            "MEAS-POLICY",
            "MEAS-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: the practical definitional raw-reward-range/measurable-mean-range generated-policy random next-pair source now yields the definitional integrability-based centered source directly, preserving generatedActionFromRewardHistory as the implicit action surface. It packages the existing definitional map source, centered kernel law, context measurability, and bounded-derived integrability into GeneratedActionRandomPairDefinitionalCenteredSource, making the newer definitional centered-source consumers available from the practical top-level source contract. It still assumes the definitional random next-pair law, mean measurability, deterministic raw reward and mean range bounds, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-CENTERED-REGULARITY",
            "MEAS-REWARD",
            "MEAS-POLICY",
            "MEAS-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-CONSUMER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local practical definitional raw-reward-range/measurable-mean-range conditional MGF consumer for COND-EXPECT-REWARD: the top generated-action source lowers through its definitional centered-source conversion and reuses the Mathlib HasCondSubgaussianMGF route over generatedActionFromRewardHistory. Ambient centered-reward measurability and variance-proxy domination remain explicit; the integrated target-law transfer removes the ambient exponential-integrability input.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-COND-MGF-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-CENTERED-REGULARITY",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-EXP-INTEGRABILITY",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_integrable_exp_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local practical definitional raw-reward-range/measurable-mean-range exponential integrability leaf for COND-EXPECT-REWARD: the top generatedActionFromRewardHistory source lowers to the bounded-centered source and derives integrability of exp(t * centeredReward_succ) for every real t from deterministic raw reward and selected-mean range evidence. It still assumes the definitional random next-pair law source, mean measurability, range bounds, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.Analysis.SpecialFunctions.Exp",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-EXP-INTEGRABILITY",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-BOUNDED-CENTERED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-CENTERED-REGULARITY",
            "MEAS-REWARD",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-BOUNDED-EXP-CONSUMER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_centered_meas",
        ],
        "role": "Compiled project-local practical conditional MGF consumer from a supplied centered-measurability witness: the definitional raw-reward-range/measurable-mean-range source feeds the existing Mathlib HasCondSubgaussianMGF route, and the integrated target-law transfer derives exponential integrability directly from the selected laws. Centered reward measurability and variance-proxy domination remain explicit; the legacy bounded-exp theorem name is retained for compatibility.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-EXP-INTEGRABILITY",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-CENTERED-REGULARITY",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-SOURCE-REGULARITY-CONSUMER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_variance_le",
        ],
        "role": "Compiled project-local practical conditional MGF consumer with source-derived regularity: the definitional raw-reward-range/measurable-mean-range source derives centered-reward measurability from its fields, while the integrated target-law transfer derives exponential integrability. The only remaining analytic MGF side condition at this surface is deterministic variance-proxy domination; the theorem still assumes the definitional random next-pair law source and ambient trajectory-to-condExpKernel identification.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-BOUNDED-EXP-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-EXP-INTEGRABILITY",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-CENTERED-REGULARITY",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_uniform_variance_le",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource",
        ],
        "role": "Compiled project-local practical conditional MGF consumer with a deterministic variance-proxy ceiling: the definitional raw-reward-range/measurable-mean-range source now reduces the trimmed-a.e. selected-history variance domination condition to a pointwise model-side bound forall context action, varianceProxy context action <= c. A packaged uniform-variance source wrapper carries the base practical source plus the ceiling and directly yields HasCondSubgaussianMGF with proxy varianceCeiling. It still assumes the definitional random next-pair law source, ambient trajectory-to-condExpKernel identification, and an explicit uniform variance ceiling; raw/mean range bounds alone do not imply an arbitrary varianceProxy ceiling.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-SOURCE-REGULARITY-CONSUMER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-HISTORY-VARIANCE-CONSUMER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_history_variance_le",
        ],
        "role": "Compiled project-local practical conditional MGF consumer with a selected finite-history variance-proxy ceiling: the definitional raw-reward-range/measurable-mean-range source now reduces the trimmed-a.e. selected-history variance domination condition to a pointwise bound over histories of shape forall history : ((j : Finset.Iic i) -> Rat), varianceProxy (context i history) ((policy i).action (state i history)) <= c. This is weaker than a global context/action ceiling and still leaves the finite-history/model-side variance ceiling explicit.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-SOURCE-REGULARITY-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_uniformVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-projection leaf for the COND-EXPECT-REWARD route: a practical definitional raw-range/measurable-mean-range uniform-variance source now directly exposes its packaged base raw-range/measurable-mean-range bounded source. This lets downstream non-variance consumers reuse the generated random-pair law and raw/mean range regularity without unpacking the uniform variance wrapper. It still assumes the packaged source fields, global variance ceiling, random next-pair law, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_uniformVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a practical uniform-variance raw-range/measurable-mean-range source now directly yields the explicit generated random-pair map source over generatedActionFromRewardHistory. It reuses the packaged base raw-range/measurable-mean-range bounded source and the existing definitional raw-range-to-random-pair-map projection, so full next-pair law and partialTraj consumers no longer need to unpack the uniform-variance wrapper. It still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-PARTIALTRAJ-PAIR-LAW-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_uniformVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a practical uniform-variance raw-range/measurable-mean-range source now lowers through its packaged base source into GeneratedActionPartialTrajectoryPairLawSource over generatedActionFromRewardHistory. This hides the uniform variance wrapper for full finite-pair partialTraj-source consumers while preserving the packaged random next-pair law assumption. It still assumes the raw/mean range regularity, global variance ceiling, packaged definitional random-pair law, ambient partialTraj/condExpKernel trajectory identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj",
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-PARTIALTRAJ-PAIR-LAW-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-DEFINITIONAL-MAP-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_uniformVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-consumer leaf for the COND-EXPECT-REWARD route: a practical uniform-variance raw-range/measurable-mean-range source now directly yields the canonical RewardKernel.actionRewardHistoryStepKernelFamily next-pair law over generatedActionFromRewardHistory and History.finitePairHistoryOfTrace. It first exposes the generated random-pair map source and then reuses the generic random-pair-source history-step consumer, so downstream history-step consumers no longer need to manually unpack the uniform-variance wrapper. It still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_uniformVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a practical uniform-variance raw-range/measurable-mean-range source now directly yields the weaker definitional generated actual-action reward-coordinate source over generatedActionFromRewardHistory. It first forgets the uniform-variance wrapper to its packaged base raw-range/measurable-mean-range bounded source, then projects that source through the existing definitional actual reward-map conversion. It still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_uniformVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a practical uniform-variance raw-range/measurable-mean-range source now directly yields the explicit generated actual-action reward-map source over generatedActionFromRewardHistory. It reuses the packaged base raw-range/measurable-mean-range bounded source and the existing actual reward-map projection, so reward-coordinate consumers no longer need to unpack the uniform-variance wrapper. It still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_uniformVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a practical uniform-variance raw-range/measurable-mean-range source now directly yields the definitional centered-source interface over generatedActionFromRewardHistory. It reuses the packaged base raw-range/measurable-mean-range bounded source and the existing bounded-to-definitional-centered conversion, making centered-source consumers available without manually unpacking the uniform-variance wrapper. It still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-BOUNDED-CENTERED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_uniformVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a practical uniform-variance raw-range/measurable-mean-range source now directly yields the bounded centered-source interface over generatedActionFromRewardHistory, preserving deterministic centered reward bounds for bounded-integrability and tail consumers. It reuses the packaged base raw-range/measurable-mean-range bounded source and the existing bounded-centered conversion, so bounded-centered consumers no longer need to manually unpack the uniform-variance wrapper. It still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-BOUNDED-CENTERED-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-CENTERED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_uniformVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a practical uniform-variance raw-range/measurable-mean-range source now directly yields the integrability-based centered-source interface over generatedActionFromRewardHistory. It lowers through the already packaged bounded centered-source projection, so centered-source consumers no longer need to unpack the uniform-variance wrapper or manually derive integrability from centered bounds. It still assumes the packaged random next-pair law, raw/mean range regularity, global variance ceiling, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-BOUNDED-CENTERED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-CENTERED-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_historyVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-projection leaf for the COND-EXPECT-REWARD route: a practical definitional raw-range/measurable-mean-range selected-history-variance source now directly exposes its packaged base raw-range/measurable-mean-range bounded source. This lets downstream non-variance consumers reuse the generated random-pair law and raw/mean range regularity without unpacking the history variance wrapper. It still assumes the packaged source fields, selected-history variance ceilings, random next-pair law, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairMapSource_of_historyVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a practical selected-history-variance raw-range/measurable-mean-range source now directly yields the explicit generated random-pair map source over generatedActionFromRewardHistory. It reuses the packaged base raw-range/measurable-mean-range bounded source and the existing definitional raw-range-to-random-pair-map projection, so full next-pair law and partialTraj consumers no longer need to unpack the history-variance wrapper. It still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-PARTIALTRAJ-PAIR-LAW-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionPartialTrajectoryPairLawSource_of_historyVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a practical selected-history-variance raw-range/measurable-mean-range source now lowers through its packaged base source into GeneratedActionPartialTrajectoryPairLawSource over generatedActionFromRewardHistory. This hides the history-variance wrapper for full finite-pair partialTraj-source consumers while preserving the packaged random next-pair law assumption. It still assumes the raw/mean range regularity, selected-history variance ceilings, packaged definitional random-pair law, ambient partialTraj/condExpKernel trajectory identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-PARTIALTRAJ-PAIR-LAW-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-DEFINITIONAL-MAP-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_historyVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-consumer leaf for the COND-EXPECT-REWARD route: a practical selected-history-variance raw-range/measurable-mean-range source now directly yields the canonical RewardKernel.actionRewardHistoryStepKernelFamily next-pair law over generatedActionFromRewardHistory and History.finitePairHistoryOfTrace. It first exposes the generated random-pair map source and then reuses the generic random-pair-source history-step consumer, so downstream history-step consumers no longer need to manually unpack the history-variance wrapper. It still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-TO-HISTORYSTEP-PAIR-LAW",
            "LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_historyVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a practical selected-history-variance raw-range/measurable-mean-range source now directly yields the weaker definitional generated actual-action reward-coordinate source over generatedActionFromRewardHistory. It first forgets the history-variance wrapper to its packaged base raw-range/measurable-mean-range bounded source, then projects that source through the existing definitional actual reward-map conversion. It still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_historyVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a practical selected-history-variance raw-range/measurable-mean-range source now directly yields the explicit generated actual-action reward-map source over generatedActionFromRewardHistory. It reuses the packaged base raw-range/measurable-mean-range bounded source and the existing actual reward-map projection, so reward-coordinate consumers no longer need to unpack the history-variance wrapper. It still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-BOUNDED-CENTERED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_historyVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a practical selected-history-variance raw-range/measurable-mean-range source now directly yields the bounded centered-source interface over generatedActionFromRewardHistory, preserving deterministic centered reward bounds for bounded-integrability and tail consumers. It reuses the packaged base raw-range/measurable-mean-range bounded source and the existing bounded-centered conversion, so bounded-centered consumers no longer need to manually unpack the history-variance wrapper. It still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-BOUNDED-CENTERED-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-CENTERED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_historyVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a practical selected-history-variance raw-range/measurable-mean-range source now directly yields the integrability-based centered-source interface over generatedActionFromRewardHistory. It lowers through the already packaged bounded centered-source projection, so centered-source consumers no longer need to unpack the history-variance wrapper or manually derive integrability from centered bounds. It still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-BOUNDED-CENTERED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-CENTERED-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_historyVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a practical selected-history-variance raw-range/measurable-mean-range source now directly yields the definitional centered-source interface over generatedActionFromRewardHistory. It reuses the packaged base raw-range/measurable-mean-range bounded source and the existing bounded-to-definitional-centered conversion, making centered-source consumers available without manually unpacking the history-variance wrapper. It still assumes the packaged random next-pair law, raw/mean range regularity, selected-history variance ceilings, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-HISTORY-VARIANCE-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_uniformVarianceBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the practical conditional MGF route: a packaged uniform variance-proxy source now yields the time-indexed selected-history variance source with constant ceiling fun _ => varianceCeiling. This lets consumers stated against the weaker history-variance interface reuse a stronger global context/action variance ceiling while still assuming the same definitional random next-pair law source and ambient trajectory-to-condExpKernel identification.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-VIA-HISTORY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_via_historyVarianceSource",
        ],
        "role": "Compiled project-local convenience consumer for the practical conditional MGF route: a packaged uniform variance-proxy source is first converted to the selected-history variance source with constant ceiling and then consumed through the history-variance conditional MGF interface. This gives the same `HasCondSubgaussianMGF` proxy as the direct uniform consumer while keeping downstream callers standardized on the weaker history-variance source API; it still assumes the definitional random next-pair law source and ambient trajectory-to-condExpKernel identification.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for coarser downstream proxies from a packaged uniform-variance source: if the global varianceCeiling is bounded by c, the generated centered successor reward has HasCondSubgaussianMGF with proxy c. The proof converts the uniform source to the constant selected-history variance source and reuses the history-variance larger-proxy consumer; it still assumes the definitional random next-pair law source and ambient trajectory-to-condExpKernel identification.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-HISTORY-VARIANCE-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource",
            "ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_uniformVarianceBoundedSource",
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource",
        ],
        "role": "Compiled project-local practical source wrapper and consumer for time-indexed selected-history variance ceilings: a definitional raw-reward-range/measurable-mean-range source can be packaged with varianceCeiling : Nat -> NNReal and forall i history, varianceProxy (context i history) ((policy i).action (state i history)) <= varianceCeiling i, yielding HasCondSubgaussianMGF at time i with proxy varianceCeiling i. A uniform-variance source now converts into this history-variance source with constant ceiling fun _ => varianceCeiling. It keeps the history-level variance contract explicit while avoiding per-call trimmed-a.e. variance hypotheses.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-CONDITIONAL-EXPECTATION",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-HISTORY-VARIANCE-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-HISTORY-VARIANCE-SOURCE",
            "FILTRATION-HISTORY",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_varianceCeiling_le",
        ],
        "role": "Compiled project-local practical conditional MGF consumer for coarser downstream proxies: a packaged selected-history variance source with proxy varianceCeiling i can be consumed at any deterministic proxy c satisfying varianceCeiling i <= c. The proof lowers to the base raw-range/measurable-mean-range source and composes the source's selected-history variance bound with the supplied ceiling inequality; it does not construct the definitional random next-pair law or ambient trajectory-to-condExpKernel identification.",
        "mathlib_routes": [
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-HISTORY-VARIANCE-CONSUMER",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a definitional raw-reward-range/measurable-mean-range bounded generated-policy random next-pair source is weakened into the definitional generated actual-action reward-coordinate source by projecting its packaged definitional random-pair map source into the existing definitional random-pair-to-actual source conversion. Its deterministic raw reward and mean range fields remain available for centered-bound and integrability consumers but are not needed by this weaker reward-coordinate interface. It still assumes the definitional random next-pair law, raw-range/measurable-mean-range source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE",
        "leaf_ids": [
            "COND-EXPECT-REWARD",
            "ADAPTED-ACTION",
            "MEAS-POLICY",
            "MEAS-HISTORY",
            "KERNEL-POLICY-BIND",
            "KERNEL-REWARD",
            "INT-REWARD-BOUNDED",
            "MEAS-REWARD",
        ],
        "module": "BanditRLProof.ConditionalRewardLawSource",
        "status": "leanCompiled",
        "declarations": [
            "ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource",
        ],
        "role": "Compiled project-local source-conversion leaf for the COND-EXPECT-REWARD route: a definitional raw-reward-range/measurable-mean-range bounded generated-policy random next-pair source is weakened into the explicit generated actual-action reward-coordinate source whose action trace is generatedActionFromRewardHistory, by first projecting to the definitional actual-map source and then reusing the definitional-to-explicit actual reward-map source conversion. Its deterministic raw reward and mean range fields remain available for centered-bound and integrability consumers but are not needed by this weaker reward-coordinate interface. It still assumes the definitional random next-pair law, raw-range/measurable-mean-range source regularity fields, ambient trajectory-to-condExpKernel identification, and final adaptive theorem.",
        "mathlib_routes": [
            "MLIB-CONDITIONAL-EXPECTATION",
            "MLIB-MEASURE-INTEGRAL",
            "Mathlib.MeasureTheory.Measure.Map",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT",
            "LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE",
            "LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT",
        ],
    },
    {
        "id": "LOCAL-LEAF-MEASURABLE-SUMS",
        "module": "BanditRLProof.MeasurableSums",
        "status": "leanCompiled",
        "declarations": [
            "measurable_finset_sum_indicator_reward",
        ],
        "role": "Compiled finite-sum measurability bridge for selected-reward indicator contributions.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-MEASURABLE-LOCAL-QUANTITIES",
        "module": "BanditRLProof.MeasurableLocalQuantities",
        "status": "leanCompiled",
        "declarations": [
            "measurable_sumRewards",
        ],
        "role": "Compiled measurability bridge from selected-reward finite sums to the local recursive sumRewards quantity.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-MEASURABLE-REGRET",
        "module": "BanditRLProof.MeasurableRegret",
        "status": "leanCompiled",
        "declarations": [
            "measurable_pseudoRegret",
        ],
        "role": "Compiled pseudo-regret random-variable measurability bridge before expectation or probability measures.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-MEASURABLE-PULLCOUNT",
        "module": "BanditRLProof.MeasurablePullCount",
        "status": "leanCompiled",
        "declarations": [
            "measurable_pullCount",
        ],
        "role": "Compiled pull-count random-variable measurability bridge before expected pull-count identities.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-MEASURABLE-PULLCOUNT-CAST",
        "module": "BanditRLProof.MeasurablePullCountCast",
        "status": "leanCompiled",
        "declarations": [
            "measurable_natCast_pullCount",
        ],
        "role": "Compiled scalar-casted pull-count measurability bridge before expected pull-count identities.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-EXPECTATION-FOUNDATION",
        "module": "BanditRLProof.ExpectationFoundation",
        "status": "leanCompiled",
        "declarations": [
            "lintegral_actionTrace_eval_eq_indicator_one",
        ],
        "role": "Compiled ENNReal lower-integral identity for action-equality pull-event indicators.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL"],
    },
    {
        "id": "LOCAL-LEAF-INTEGRABILITY-SUMS",
        "leaf_ids": [
            "INT-FINITE-SUM",
        ],
        "module": "BanditRLProof.IntegrabilitySums",
        "status": "leanCompiled",
        "declarations": [
            "IntegrabilitySums.integrable_finset_sum",
            "IntegrabilitySums.integrable_univ_sum",
        ],
        "role": "Compiled Mathlib-backed finite-sum integrability wrapper: an explicit Finset sum of integrable terms is integrable, with a Fintype/Finset.univ specialization for finite-arm proof shapes. This is not Bochner expectation linearity.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-EXPECTATION-BOCHNER-SUMS",
        "leaf_ids": [
            "EXP-FINITE-SUM",
        ],
        "module": "BanditRLProof.ExpectationBochnerSums",
        "status": "leanCompiled",
        "declarations": [
            "ExpectationBochnerSums.integral_finset_sum",
            "ExpectationBochnerSums.integral_univ_sum",
        ],
        "role": "Compiled Mathlib-backed Bochner finite-sum expectation wrapper: under per-term integrability, the integral of an explicit Finset sum equals the finite sum of integrals, with a Fintype/Finset.univ specialization for finite-arm proof shapes. This is not the expected-regret pull-count theorem.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS", "LOCAL-LEAF-INTEGRABILITY-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-EXPECTATION-REGRET-PULLCOUNT",
        "leaf_ids": [
            "EXP-REGRET-PULLCOUNT",
        ],
        "module": "BanditRLProof.ExpectationRegretPullCount",
        "status": "leanCompiled",
        "declarations": [
            "integrable_real_pseudoRegret_of_integrable_pullCount",
            "integral_real_pseudoRegret_eq_sum_gap_mul_integral_pullCount",
        ],
        "role": "Compiled Bochner/Real expected-regret pull-count decomposition: under Real-cast pull-count integrability for each finite arm, the integral of Real-cast pseudoRegret equals the finite sum of each Real-cast gap times the integral of that arm's Real-cast pullCount. This is not a Rat-valued expectation theorem, ENNReal lower-integral surrogate, concentration result, or final algorithm theorem.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS", "LOCAL-LEAF-REGRET-DECOMPOSITION", "LOCAL-LEAF-EXPECTATION-BOCHNER-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-REAL-MEAN-REGRET-PULLCOUNT",
        "leaf_ids": [
            "REAL-MEAN-REGRET-PULLCOUNT",
        ],
        "module": "BanditRLProof.RealMeanRegretPullCount",
        "status": "leanCompiled",
        "declarations": [
            "realMeanGap",
            "realMeanRegret",
            "realMeanRegret_eq_finset_sum_gap",
            "realMeanRegret_eq_sum_gap_mul_pullCount",
            "integrable_realMeanRegret_of_integrable_pullCount",
            "integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount",
        ],
        "role": "Compiled Real finite-arm mean-regret and expected pull-count decomposition aligned with the scalar bookkeeping semantics of the exact LML bandit regret route. realMeanGap uses supremum finite-arm mean minus the selected arm mean, realMeanRegret uses n times that supremum minus the finite selected-mean sum, and the deterministic theorem rewrites it as a gap-weighted pull-count sum. The Bochner theorem exchanges the finite arm sum and integral under explicit Real-cast pull-count integrability. Local APIs/imports are ActionTrace/pullCount, pullCount_eq_finset_filter_card, Finset.sum_fiberwise', IntegrabilitySums.integrable_univ_sum, and ExpectationBochnerSums.integral_univ_sum. Regularity is only a measurable sample space, an arbitrary measure, a Real arm-mean function, and per-arm pull-count integrability; no probability, reward kernel, policy, environment law, sub-Gaussian assumption, or argmax tie contract is used. Retrieval evidence is the exact LML seed definitions of gap/regret and regret_eq_sum_pullCount_mul_gap, MLIB-FINSET-SUMS, MLIB-MEASURE-INTEGRAL, and the compiled local finite-sum/pull-count wrappers; the LML card remains target evidence rather than an imported proof. Failure policy: its stationary Real kernel identity-integral specialization now compiles downstream. Do not coerce this theorem back through FiniteBanditModel Rat means, weaken the exact Real target, or report Bandits.ETC.regret_le as ported before the Real ETC expected-count/concentration producer, constants, and measurableArgmax semantics align.",
        "mathlib_routes": [
            "MLIB-FINSET-SUMS",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-MATHLIB-FINSET-WRAPPERS",
            "LOCAL-LEAF-INTEGRABILITY-SUMS",
            "LOCAL-LEAF-EXPECTATION-BOCHNER-SUMS",
            "LML-BANDIT-REGRET-PULLCOUNT",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-REAL-KERNEL-REGRET-PULLCOUNT",
        "leaf_ids": [
            "REAL-KERNEL-REGRET-PULLCOUNT",
        ],
        "module": "BanditRLProof.RealKernelRegretPullCount",
        "status": "leanCompiled",
        "declarations": [
            "realKernelMean",
            "realKernelGap",
            "realKernelRegret",
            "realKernelGap_nonneg",
            "realKernelRegret_eq_finset_sum_gap",
            "realKernelRegret_eq_sum_gap_mul_pullCount",
            "integrable_realKernelRegret_of_integrable_pullCount",
            "integral_realKernelRegret_eq_sum_gap_mul_integral_pullCount",
        ],
        "role": "Compiled stationary Real arm-kernel specialization of the LML-aligned scalar regret bookkeeping route. realKernelMean nu a is the Bochner identity integral under nu a, realKernelGap is supremum kernel mean minus arm mean, and realKernelRegret specializes realMeanRegret to those means. The leaf proves kernel-gap nonnegativity for nonempty Fin K, deterministic time-gap and arm-pull-count decompositions, integrability from per-arm pull-count integrability, and the final Bochner equality sum_a realKernelGap nu a * integral pullCount. Local APIs/imports are Mathlib.Probability.Kernel.Integral and LOCAL-LEAF-REAL-MEAN-REGRET-PULLCOUNT. The proof route is definitional specialization followed by the compiled Real mean-regret theorems; gap nonnegativity uses le_ciSup. Regularity is a Mathlib Kernel (Fin K) Real, an arbitrary measure on the action sample space, and per-arm Real-cast pull-count integrability; only gap nonnegativity requires Nonempty (Fin K). No Markov/probability kernel instance, identity integrability, algorithm/environment law, reward-process law, sub-Gaussian witness, independence, or argmax semantics is assumed. Retrieval evidence is the exact LML seed identity-integral gap/regret definitions, Mathlib Kernel.Integral, the prior Real mean leaf, and LML-BANDIT-REGRET-PULLCOUNT; LML remains card-only. Failure policy: kernel scalar bookkeeping is closed and the downstream Real ETC count-to-commit-probability expected-count endpoint now compiles. Next prove the exact Real exponential commit-fiber probability bound from empirical rewards with measurableArgmax semantics; do not add another Rat transport wrapper or claim Bandits.ETC.regret_le before that producer compiles.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-FINSET-SUMS",
            "LOCAL-LEAF-REAL-MEAN-REGRET-PULLCOUNT",
            "LML-BANDIT-REGRET-PULLCOUNT",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-REAL-EXPECTED-PULLCOUNT",
        "leaf_ids": [
            "REAL-ETC-EXPECTED-PULLCOUNT",
        ],
        "module": "BanditRLProof.Algorithms.ETCExpectedPullCount",
        "status": "leanCompiled",
        "declarations": [
            "ETC.integrable_real_pullCount_actionWithCommit_choice_of_measurable_commit",
            "ETC.integral_real_pullCount_actionWithCommit_choice_eq_exploration_add_suffix_mul_commit_prob",
            "ETC.integral_real_pullCount_actionWithCommit_choice_eq_exploration_add_remaining_mul_commit_prob",
            "ETC.integral_real_pullCount_actionWithCommit_choice_le_exploration_add_remaining_mul_of_commit_prob_le",
        ],
        "role": "Compiled Real/Bochner ETC per-arm expected-pull-count endpoint aligned with the exact LML horizon arithmetic. The leaf proves arbitrary-horizon Real-cast pull-count integrability for a measurable finite-arm commit selector, integrates the deterministic actionWithCommit count formula exactly as explorationPulls + suffix * mu.real {commit = a}, rewrites it under K * explorationPulls <= n to the LML-shaped n - K * explorationPulls suffix, and consumes any Real commit-fiber probability bound to obtain the corresponding expected-count inequality. Local APIs/imports are Mathlib Bochner set integrals and probability-measure typeclasses, LOCAL-LEAF-ETC-TRACE-COUNT, measurable_natCast_pullCount, pullCount_le_time, integral_indicator, setIntegral_const, and Measure.real. The proof route is finite-valued action measurability, deterministic pull-count boundedness, the compiled suffix count identity, indicator integration, horizon subtraction normalization, and nonnegative multiplication of the supplied probability bound. Regularity is a measurable sample space, a probability measure for exact expectation formulas, a measurable commit : Omega -> Fin K, and K * explorationPulls <= n for the LML horizon form; arbitrary-horizon integrability only needs a finite measure. No reward kernel, empirical mean, independence, sub-Gaussian MGF, concentration constant, optimal-arm premise, or argmax/tie rule is assumed. Retrieval evidence is the exact LML ETC.pullCount_of_ge and expectation_pullCount_le proof route, MLIB-MEASURE-INTEGRAL, LOCAL-LEAF-ETC-TRACE-COUNT, LOCAL-LEAF-MEASURABLE-PULLCOUNT-CAST, and LOCAL-LEAF-REAL-KERNEL-REGRET-PULLCOUNT; the LML theorem remains card-only. Failure policy: counting, integrability, and commit-fiber integration are closed. The next leaf must prove mu.real {commit = a} <= exp (-(m : Real) * realKernelGap nu a ^ 2 / (4 * sigma2)) from a concrete Real empirical-reward law and measurable argmax semantics; do not hide that concentration statement inside this consumer or claim the final ETC regret theorem before it compiles.",
        "mathlib_routes": [
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-ETC-TRACE-COUNT",
            "LOCAL-LEAF-MEASURABLE-PULLCOUNT-CAST",
            "LOCAL-LEAF-REAL-KERNEL-REGRET-PULLCOUNT",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-EXACT-COMMON-SUBGAUSSIAN-PER-ARM-EXPECTED-PULLCOUNT",
        "leaf_ids": [
            "ETC-EXACT-COMMON-SUBGAUSSIAN-PER-ARM-EXPECTED-PULLCOUNT",
        ],
        "module": "BanditRLProof.Algorithms.ETCExactSubGaussianTail",
        "status": "leanCompiled",
        "declarations": [
            "ETC.sum_centeredPairwiseRewardDiffVarianceProxy_const_eq_two_mul",
            "ETC.centeredPairwiseGapThreshold_eq_explorationPulls_mul_gap",
            "ETC.canonicalSubGaussianArmPairwiseTailReal_eq_exp_neg_explorationPulls_mul_gap_sq_div_four_mul",
            "ETC.real_measure_explorationArgmaxCommit_eq_arm_le_exp_neg_explorationPulls_mul_gap_sq_div_four_mul_of_armLaws",
            "ETC.integral_real_pullCount_explorationArgmaxAction_le_exploration_add_remaining_mul_exp_of_armLaws",
        ],
        "role": "Compiled exact-common-proxy ETC concentration and expected-pull-count leaf on the current canonical generated-history Rat arm-law model, with centered reward differences and all tail arithmetic in Real. The leaf proves that the masked pairwise variance-proxy sum is exactly 2 * explorationPulls * sigma2, rewrites the centered pairwise threshold as explorationPulls * gap for a non-best arm, normalizes the canonical tail to exp (-(explorationPulls : Real) * gap^2 / (4 * sigma2)), bounds the concrete explorationArgmaxCommit fiber, and feeds that bound to the Real/Bochner expected-count consumer to obtain explorationPulls + (n - K * explorationPulls) times the exact exponential. Local APIs/imports are ETCFiniteArmRewardLaw's canonical direct-MGF commit-fiber theorem, ETCExpectedPullCount's probability consumer, the masked pairwise variance proxy, exact exploration pull counts, Finset.filter cardinality, NNReal/Real coercions, Mathlib FieldSimp, and Ring. The proof route is indicator partition of the pairwise proxy, exact pull-count cardinalities, non-best gap-threshold rewriting, a separate sigma2 = 0 branch for total division, exact Real algebra, commit-fiber concentration, then Bochner expected-count composition. The concentration dependency internally constructs the context-independent canonical reward kernel, derives successor conditional MGFs from the arm-law MGFs, and transports them to historyFiltrationSucc through exploration-prefix measurable-space equality; this is not an assumption-free result for arbitrary adaptive kernels. Regularity is positive explorationPulls, K * explorationPulls <= n, a non-best arm, per-arm Rat probability laws with exact model means after casting to Real, centered Real HasSubgaussianMGF witnesses at one common NNReal sigma2, and a measurable generated-history context. The random variables are the existing masked centered pairwise reward differences; the result is a one-sided fixed-horizon, single-arm fiber bound with no arm union. Retrieval evidence is the exact LML ETC.expectation_pullCount_le constant, the compiled canonical direct-MGF Rat arm-law chain, MLIB measure/concentration APIs, and LOCAL-LEAF-ETC-REAL-EXPECTED-PULLCOUNT; LML remains theorem-card evidence only. Failure policy: exact common-proxy constants and the canonical Rat-arm-law per-arm expected-count endpoint are closed, and downstream native Real law/source, exact finite-sum regret, least-encoded tie semantics, and action assembly now compile. The downstream source-shaped history-score bridge now compiles; the direct port only lacks actual LML measurableArgmax/IsAlgEnvSeq symbol-and-field instantiation; do not claim this supporting leaf alone as Bandits.ETC.regret_le.",
        "mathlib_routes": [
            "MLIB-FINSET-SUMS",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-CANONICAL-PER-ARM-BOCHNER-REGRET",
            "LOCAL-LEAF-ETC-REAL-EXPECTED-PULLCOUNT",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-RAT-ARM-LAW-REAL-KERNEL-EXACT-REGRET",
        "leaf_ids": [
            "ETC-RAT-ARM-LAW-REAL-KERNEL-EXACT-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCRatArmLawRealKernel",
        "status": "leanCompiled",
        "declarations": [
            "ETC.ratArmLawRealKernel",
            "ETC.ratArmLawRealKernel_apply",
            "ETC.isMarkovKernel_ratArmLawRealKernel",
            "ETC.realKernelMean_ratArmLawRealKernel_eq_integral_cast",
            "ETC.realKernelMean_ratArmLawRealKernel_eq_modelMean",
            "ETC.ciSup_modelMean_cast_eq_bestArm",
            "ETC.realKernelGap_ratArmLawRealKernel_eq_modelGap",
            "ETC.integral_realKernelRegret_explorationArgmaxAction_le_exact_sum_of_armLaws",
        ],
        "role": "Compiled kernel-gap and finite-arm regret assembly for the exact canonical ETC route. The leaf pushes each existing Rat arm law forward along the cast to Real using Kernel.ofFunOfCountable, proves the resulting kernel is Markov under per-arm probability laws, identifies its identity-integral mean with the original cast integral and exact model mean, proves the finite iSup of cast means is attained at model.bestArm, and identifies realKernelGap exactly with the Real cast of model.gap. It then applies the Real kernel regret pull-count decomposition, discharges every pull-count integrability premise from measurable explorationArgmaxCommit, removes the best-arm summand, inserts the exact non-best per-arm count bounds, and obtains the full finite sum of gap * (m + (n-K*m) * exp (-m*gap^2/(4*sigma2))). Local APIs/imports are Measure.map, Measure.isProbabilityMeasure_map, integral_map, Kernel.ofFunOfCountable, ciSup_le/le_ciSup, FiniteBanditModel.mean_le_bestArm_mean/gap_nonneg/gap_bestArm, RealKernelRegretPullCount, and ETCExactSubGaussianTail. Regularity is positive exploration pulls, K*m <= n, per-arm Rat probability laws with exact Real-cast means and centered common-proxy HasSubgaussianMGF witnesses, and measurable canonical history context. The Real kernel is specifically the cast pushforward of those Rat laws and the probability space remains the canonical generated Rat reward trajectory; this is not arbitrary native Real reward-law or IsAlgEnvSeq transport. Retrieval evidence is exact LML Bandits.ETC.regret_le finite-sum shape, MLIB-PROBABILITY-KERNEL, MLIB-MEASURE-INTEGRAL, MLIB-FINSET-SUMS, LOCAL-LEAF-REAL-KERNEL-REGRET-PULLCOUNT, and LOCAL-LEAF-ETC-EXACT-COMMON-SUBGAUSSIAN-PER-ARM-EXPECTED-PULLCOUNT. Failure policy: canonical kernel mean/gap identification and finite-arm exact regret assembly are closed. Downstream native Real law/source transport, selected feedback laws, least-encoded tie semantics, and action assembly now compile; source-shaped history-score mapping now compiles; faithful local field compatibility now compiles; only actual cross-toolchain LML symbol import remains. Do not call this supporting theorem the final LML theorem or infer native Real reward support from the pushforward construction.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-FINSET-SUMS",
            "LOCAL-LEAF-REAL-KERNEL-REGRET-PULLCOUNT",
            "LOCAL-LEAF-ETC-EXACT-COMMON-SUBGAUSSIAN-PER-ARM-EXPECTED-PULLCOUNT",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-NATIVE-REAL-EMPIRICAL-MEAN-ARGMAX-COUNT",
        "leaf_ids": [
            "ETC-NATIVE-REAL-EMPIRICAL-MEAN-ARGMAX-COUNT",
        ],
        "module": "BanditRLProof.Algorithms.ETCRealEmpiricalMean",
        "status": "leanCompiled",
        "declarations": [
            "ETC.realEmpMeanAtExploration",
            "ETC.realEmpMeanAtExploration_eq_sumRewards_div_explorationPulls",
            "ETC.measurable_realEmpMeanAtExploration",
            "ETC.realArgmaxCommit",
            "ETC.realArgmaxCommit_spec",
            "ETC.realArgmaxCommit_const",
            "ETC.measurable_realArgmaxCommit_of_forall_measurable",
            "ETC.realExplorationArgmaxCommit",
            "ETC.realExplorationArgmaxAction",
            "ETC.measurable_realExplorationArgmaxCommit",
            "ETC.integral_real_pullCount_realExplorationArgmaxAction_eq_exploration_add_remaining_mul_commit_prob",
            "ETC.integral_real_pullCount_realExplorationArgmaxAction_le_exploration_add_remaining_mul_of_commit_prob_le",
        ],
        "role": "Compiled native Real reward-trace empirical-mean, finite argmax, measurability, and expected-count consumer for the exact ETC route. The leaf defines exploration means directly in Real, rewrites the denominator using exact round-robin counts, scans List.finRange K with a deterministic keep-the-old-arm-on-ties fold, proves every score is dominated by the selected score, and proves the selector measurable without assuming the uncountable Real score-vector space is countable. Its key measurability route expresses the score at a measurable finite-valued selected arm as a finite indicator sum, then inducts over the fold using measurable strict-comparison events and measurable ite. The reward-dependent commit/action feeds the existing Bochner count identity and abstract commit-fiber probability consumer exactly. Local APIs/imports are Mathlib.MeasureTheory.Group.Arithmetic, measurable_sumRewards, Finset.measurable_sum, measurableSet_eq_fun, measurableSet_lt, Measurable.ite, List.finRange/foldl, ETCTraceCountLemmas, and ETCExpectedPullCount. Regularity is a measurable sample space, timewise measurable Real reward coordinates, positive K from ETC.Spec, a probability measure for the count identities, and K*explorationPulls <= n; no reward kernel, conditional law, independence, MGF, sub-Gaussian tail, best arm, or IsAlgEnvSeq premise is used. The baseCommitArm only completes the deterministic action trace used to read exploration rewards; exploration scores are determined before commit. Retrieval evidence is the exact LML ETC empiricalMean/measurableArgmax/action route, MLIB-FINSET-SUMS, MLIB-MEASURE-INTEGRAL, LOCAL-LEAF-MEASURABLE-LOCAL-QUANTITIES, LOCAL-LEAF-ETC-TRACE-COUNT, and LOCAL-LEAF-ETC-REAL-EXPECTED-PULLCOUNT; LML remains theorem-card evidence only. Failure policy: native Real empirical means, deterministic tie behavior, commit measurability, and count consumption are closed. Downstream native Real laws, concentration, exact regret, selected feedback laws, and least-encoded action assembly now compile. The downstream source-shaped history-score bridge now compiles; the direct port only lacks actual LML measurableArgmax/IsAlgEnvSeq symbol-and-field instantiation; do not claim this supporting leaf as final Bandits.ETC.regret_le.",
        "mathlib_routes": [
            "MLIB-FINSET-SUMS",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-MEASURABLE-LOCAL-QUANTITIES",
            "LOCAL-LEAF-ETC-TRACE-COUNT",
            "LOCAL-LEAF-ETC-REAL-EXPECTED-PULLCOUNT",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-NATIVE-REAL-INFINITEPI-EXACT-REGRET",
        "leaf_ids": [
            "ETC-NATIVE-REAL-INFINITEPI-EXACT-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCRealInfinitePiTail",
        "status": "leanCompiled",
        "declarations": [
            "ETC.realKernelBestArm",
            "ETC.realKernelMean_le_realKernelBestArm",
            "ETC.ciSup_realKernelMean_eq_realKernelBestArm",
            "ETC.realKernelGap_eq_realKernelBestArm_sub",
            "ETC.realCenteredPairwiseRewardDiff",
            "ETC.realCenteredPairwiseGapThreshold",
            "ETC.realCenteredPairwiseRewardDiffVarianceProxy",
            "ETC.realExplorationArgmaxCommit_eq_arm_event_subset_centeredPairwise_sum_event",
            "ETC.iIndepFun_realCenteredPairwiseRewardDiff_of_iIndepFun_reward",
            "ETC.realCenteredPairwiseRewardDiff_hasSubgaussianMGF_of_centeredReward",
            "ETC.sum_realCenteredPairwiseRewardDiffVarianceProxy_const_eq_two_mul",
            "ETC.real_measure_realExplorationArgmaxCommit_eq_arm_le_exp_of_infinitePi_kernel",
            "ETC.integral_real_pullCount_realExplorationArgmaxAction_le_exp_of_infinitePi_kernel",
            "ETC.integral_realKernelRegret_realExplorationArgmaxAction_le_exact_sum_of_infinitePi_kernel",
        ],
        "role": "Compiled native Real canonical-product ETC concentration, expected-count, and exact finite-sum kernel-regret leaf. The Lean-facing endpoint assumes a Markov kernel nu on Fin K to Real and per-arm centered HasSubgaussianMGF witnesses with common NNReal proxy sigma2, chooses a finite maximizer of realKernelMean, and works under Measure.infinitePi (fun t => nu (ETC.exploreArm spec t)). It proves best-arm attainment and exact kernel-gap rewriting, native Real pairwise centered finite-sum algebra, independence under measurable coordinate transforms, sub-Gaussian sign/case transport, the exact proxy sum 2*m*sigma2, the single-arm commit-fiber bound exp (-m*gap^2/(4*sigma2)), the matching expected pull-count inequality, and the full sum of gap * (m + (n-K*m)*exp (...)). Local APIs/imports are ETCRealEmpiricalMean, IndependenceFoundation.iIndepFun_rewardTrace_infinitePi, Measure.infinitePi_map_eval, HasSubgaussianMGF.of_map/neg/congr, Concentration.subGaussian_sum_tail_of_iIndepFun, exact ETC pull counts, measureReal_mono, FieldSimp/Ring, and integral_realKernelRegret_eq_sum_gap_mul_integral_pullCount. The proof route is finite best-arm selection, empirical-comparison event inclusion, product-coordinate law transport, one-sided independent sub-Gaussian concentration, exact exponent normalization including sigma2=0, expected-count consumption, then termwise finite-sum regret assembly. Regularity is spec.hK, positive exploration pulls, K*m <= n, IsMarkovKernel nu, and one common centered MGF proxy for every arm. The result is canonical independent exploration-coordinate law only: it does not itself identify an arbitrary external algorithm/environment trajectory law. Retrieval evidence is exact upstream LML Bandits.ETC.regret_le and its expectation_pullCount_le route, MLIB-PROBABILITY-INDEPENDENCE, MLIB-PROBABILITY-SUBGAUSSIAN, MLIB-PROBABILITY-KERNEL, MLIB-MEASURE-INTEGRAL, MLIB-FINSET-SUMS, LOCAL-LEAF-IID-REWARD-FAMILY, LOCAL-LEAF-REAL-KERNEL-REGRET-PULLCOUNT, and LOCAL-LEAF-ETC-NATIVE-REAL-EMPIRICAL-MEAN-ARGMAX-COUNT; LML remains theorem-card/source evidence, not a local dependency. Failure policy: native Real canonical-product concentration, exact count, and finite-sum regret are closed. Downstream prefix/source-law transport, selected feedback laws, least-encoded tie semantics, and action assembly now compile. Source-shaped history-score mapping now compiles; faithful local field compatibility now compiles; only actual cross-toolchain LML symbol import remains; do not add StandardBorel Omega, weaken the exponent, or call this supporting theorem Bandits.ETC.regret_le.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-INDEPENDENCE",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-FINSET-SUMS",
            "LOCAL-LEAF-IID-REWARD-FAMILY",
            "LOCAL-LEAF-REAL-KERNEL-REGRET-PULLCOUNT",
            "LOCAL-LEAF-ETC-NATIVE-REAL-EMPIRICAL-MEAN-ARGMAX-COUNT",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-NATIVE-REAL-PREFIX-LAW-EXTERNAL-EXACT-REGRET",
        "leaf_ids": [
            "ETC-NATIVE-REAL-PREFIX-LAW-EXTERNAL-EXACT-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCRealPrefixLawTransport",
        "status": "leanCompiled",
        "declarations": [
            "ETC.realExplorationRewardPrefix",
            "ETC.realRewardTraceOfExplorationPrefix",
            "ETC.measurable_realExplorationRewardPrefix",
            "ETC.measurable_realRewardTraceOfExplorationPrefix",
            "ETC.realEmpMeanAtExploration_eq_of_eq_on_exploration",
            "ETC.realExplorationArgmaxCommit_eq_of_eq_on_exploration",
            "ETC.realExplorationArgmaxAction_realRewardTraceOf_prefix_eq",
            "ETC.measurable_realKernelRegret_of_forall_measurable_action",
            "ETC.realKernelRegretOfExplorationPrefix",
            "ETC.measurable_realKernelRegretOfExplorationPrefix",
            "ETC.realKernelRegret_realExplorationArgmaxAction_eq_prefixFunctional",
            "ETC.realKernelRegret_eq_of_action_eq_on_lt",
            "ETC.real_trajMeasure_const_eq_infinitePi",
            "ETC.realExplorationPrefixOfFiniteRewardHistory",
            "ETC.integral_realKernelRegret_realExplorationArgmaxAction_le_exact_sum_of_prefixLaw_eq_infinitePi",
            "ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_prefixLaw_eq_infinitePi",
            "ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_initial_map_eq_condDistrib",
        ],
        "role": "Compiled external-process transport for the native Real exact ETC theorem route. The strongest Lean-facing endpoint takes an arbitrary probability space with Real reward coordinates and an external finite-arm action process, assumes the scheduled exploration-arm zeroth reward marginal, successor condDistrib laws given finite reward history through m*K-1, and almost-sure equality of the external action with the local native Real ETC action only for t<n, and concludes the full exact finite sum for expected realKernelRegret. Supporting declarations factor empirical means, commit, action, and regret through Fin (m*K) reward prefixes; prove prefix extraction, zero extension, and the prefix regret functional measurable; transport integrals from equality of finite-prefix pushforwards; identify the constant-kernel Ionescu-Tulcea trajMeasure with Measure.infinitePi using measurePreserving_piUnique and IsProjectiveLimit.unique; and convert inclusive Finset.Iic histories to Fin prefixes. Local APIs/imports are ETCRealInfinitePiTail, RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib from ETCFiniteArmRewardLaw, History.finiteRewardHistoryOfTrace, Measure.map_map/integral_map, Kernel.trajMeasure/const, Measure.infinitePiNat/infinitePi projective limits, measurable Pi maps, and realKernelRegret_eq_finset_sum_gap. The proof route is deterministic prefix factorization, measurable integral transport, canonical-product regret insertion, finite-horizon action congruence, then generic initial-plus-successor conditional-law uniqueness. Regularity is a measurable external sample space with a probability measure, timewise measurable Real rewards, a Markov arm kernel, positive exploration pulls, K*m<=n, common centered HasSubgaussianMGF proxy, exact zeroth scheduled-arm marginal, successor scheduled-arm condDistrib laws through exploration, and horizon-restricted action equality a.e. No StandardBorelSpace Omega, external action measurability, full reward-trace law equality, or infinite-horizon action equality is required. Retrieval evidence is exact upstream LML IsAlgEnvSeq field shape and Bandits.ETC.regret_le proof route, MLIB-PROBABILITY-KERNEL, MLIB-MEASURE-INTEGRAL, MLIB-PROBABILITY-SUBGAUSSIAN, Mathlib finite-dimensional/projective-limit APIs, LOCAL-LEAF-ETC-NATIVE-REAL-INFINITEPI-EXACT-REGRET, and the compiled generic reward-prefix uniqueness theorem; LML remains source/card evidence rather than a local dependency. Failure policy: native Real prefix factorization and scheduled conditional-law transport are closed. Downstream leaves now map selected feedback laws and close least-encoded tie/action assembly; faithful local field compatibility now compiles; only actual cross-toolchain LML symbol import remains. Do not reopen concentration, require a full trajectory-law equality, strengthen to infinite action equality, or call this theorem Bandits.ETC.regret_le.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "MLIB-PROBABILITY-INDEPENDENCE",
            "LOCAL-LEAF-ETC-NATIVE-REAL-INFINITEPI-EXACT-REGRET",
            "LOCAL-LEAF-IID-REWARD-FAMILY",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-NATIVE-REAL-ACTION-DEPENDENT-SOURCE-EXACT-REGRET",
        "leaf_ids": [
            "ETC-NATIVE-REAL-ACTION-DEPENDENT-SOURCE-EXACT-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCRealSourceAdapter",
        "status": "leanCompiled",
        "declarations": [
            "ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_actionDependent_actionRewardHistory_condDistrib",
        ],
        "role": "Compiled native Real exact ETC adapter from upstream-shaped action-selected feedback laws. The Lean-facing theorem accepts an arbitrary probability space, measurable external action and Real reward coordinates, a Markov arm kernel with one common centered HasSubgaussianMGF proxy, positive exploration pulls, K*m<=n, round-robin exploration action equalities a.e., the initial reward condDistrib given action zero with Kernel.ofFunOfCountable (fun arm => nu arm), each successor reward condDistrib given the complete finite action/reward pair history and next action with RewardKernel.contextIndependentOfActionLaws, and horizon-restricted equality of the external action with the local native Real ETC action. It concludes the exact LML-shaped finite sum for expected realKernelRegret. Local APIs/imports are ETCRealPrefixLawTransport, RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected, RewardKernel.map_eq_of_condDistrib_ae_eq_const, RewardKernel.condDistrib_ae_eq_const_of_comp, History.finitePairHistoryOfTrace, History.pairHistoryRewardProjection, and contextIndependentOfActionLaws. The proof converts selected kernels to scheduled constant laws, extracts the zeroth marginal, coarsens full pair-history conditioning to reward-only prefixes, and invokes the compiled native Real conditional-law exact theorem. Regularity adds no StandardBorelSpace Omega, full trajectory law, independence, or infinite-horizon action equality. Retrieval evidence is the pinned LML seed 19dc3ab132c2a7539f5944503d1114eac4c5bb74, exact IsAlgEnvSeq feedback fields, stationaryEnv, ETC.arm_of_lt, MLIB-PROBABILITY-KERNEL, MLIB-MEASURE-INTEGRAL, and the prior native Real prefix-law leaf; LML remains source/card evidence rather than a local import. Failure policy: mathematical mapping of upstream feedback fields to hzero and hcond is closed. Downstream least-encoded action and finite-history score leaves close tie semantics, action assembly, and source-shaped empMean' mapping. Only an actual LML measurableArgmax/IsAlgEnvSeq symbol-and-field adapter remains; do not add stronger law assumptions or report Bandits.ETC.regret_le as locally imported.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-MEASURE-INTEGRAL",
            "MLIB-PROBABILITY-SUBGAUSSIAN",
            "LOCAL-LEAF-ETC-NATIVE-REAL-PREFIX-LAW-EXTERNAL-EXACT-REGRET",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-NATIVE-REAL-LEAST-ENCODED-ACTION-EXACT-REGRET",
        "leaf_ids": [
            "ETC-NATIVE-REAL-LEAST-ENCODED-ACTION-EXACT-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCRealArgmaxTie",
        "status": "leanCompiled",
        "declarations": [
            "ETC.realArgmaxCommit_argmax_finRange",
            "ETC.realArgmaxCommit_encode_le_of_score_le",
            "ETC.RealEncodedArgmaxCandidate",
            "ETC.realLeastEncodedArgmaxIndex",
            "ETC.realLeastEncodedArgmax",
            "ETC.realLeastEncodedArgmax_eq_realArgmaxCommit",
            "ETC.eventually_realExplorationArgmaxAction_eq_of_roundRobin_leastEncodedCommit_persist",
            "ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_actionDependent_actionRewardHistory_condDistrib_of_leastEncodedCommit_persist",
        ],
        "role": "Compiled native Real ETC least-encoded tie and action-behavior adapter. The Mathlib-facing layer proves the existing strict-improvement fold over List.finRange is List.argmax, uses List.index_of_argmax and List.idxOf_finRange to show it is the least Encodable.encode maximizer, ports the pinned LML Nat.find candidate construction as realLeastEncodedArgmax, and proves the two selectors equal. The action layer combines upstream-shaped round-robin exploration through K*m-1, least-encoded commit at K*m, and post-commit persistence into almost-sure equality with realExplorationArgmaxAction at every time. The strongest endpoint consumes those three action fields together with the action-selected initial/full-pair-history reward condDistrib laws and returns the exact LML-shaped native Real finite regret sum, without a caller-supplied horizon action equality. Local APIs/imports are Mathlib.Data.List.MinMax, List.argmax/index_of_argmax/idxOf_finRange, Nat.find_spec/find_min', Encodable.encode_injective, ETCRealEmpiricalMean, ETCTrace, and ETCRealSourceAdapter. Regularity is an arbitrary measurable probability space, measurable action/reward coordinates, a Markov Real kernel, one common centered HasSubgaussianMGF proxy, positive exploration pulls, K*m<=n, round-robin exploration action laws, least-encoded local exploration-score commit, persistence, and upstream-shaped selected feedback laws. No StandardBorelSpace Omega, full trajectory law, independence, preassembled horizon action equality, or infinite-horizon equality assumption is added. Retrieval evidence is pinned LML commit 19dc3ab132c2a7539f5944503d1114eac4c5bb74, measurableArgmax's Nat.find least-encode definition, ETC.arm_of_lt/arm_mul/arm_of_ge, Mathlib List.MinMax, and the compiled source adapter; LML remains card-only. Failure policy: local tie semantics and three-piece action assembly are closed, and the downstream history-score leaf now maps source-shaped empMean' scores to the local vector. Faithful local field compatibility now compiles; only actual cross-toolchain LML symbol import remains; do not reopen concentration, add stronger law assumptions, or report Bandits.ETC.regret_le as imported.",
        "mathlib_routes": [
            "MLIB-FINSET-SUMS",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-ETC-NATIVE-REAL-ACTION-DEPENDENT-SOURCE-EXACT-REGRET",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-NATIVE-REAL-HISTORY-SCORE-SOURCE-EXACT-REGRET",
        "leaf_ids": [
            "ETC-NATIVE-REAL-HISTORY-SCORE-SOURCE-EXACT-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCRealHistoryScore",
        "status": "leanCompiled",
        "declarations": [
            "ETC.realHistoryPullCount",
            "ETC.realHistorySumRewards",
            "ETC.realHistoryEmpMean",
            "ETC.realHistoryPullCount_finitePairHistoryOfTrace",
            "ETC.realHistorySumRewards_finitePairHistoryOfTrace",
            "ETC.realHistoryEmpMean_finitePairHistoryOfTrace",
            "ETC.realHistoryEmpMean_exploration_eq_realEmpMeanAtExploration",
            "ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_actionDependent_actionRewardHistory_condDistrib_of_historyLeastEncodedCommit_persist",
        ],
        "role": "Compiled source-shaped finite-history score and exact-regret adapter for native Real ETC. The Lean-facing layer mirrors the pinned LML pullCount', sumRewards', and empMean' mathematics on History.FinitePairHistory, proves the inclusive Iic n count/sum/mean equal the exclusive trace quantities at n+1, and identifies the K*m-1 history score vector with realEmpMeanAtExploration whenever exploration actions are round robin. The strongest theorem accepts the commit action already stated with the finite-pair-history score, combines all finite exploration action equalities into one ae event, rewrites that history score pointwise, and invokes the least-encoded action/source exact-regret endpoint. Local APIs/imports are ETCRealArgmaxTie, History.finitePairHistoryOfTrace, pullCount_eq_finset_filter_card, sumRewards_eq_finset_filter_sum, Finset.sum_coe_sort, Finset.Iic/range arithmetic, ae_all_iff, and the prior least-encoded source theorem. Regularity is an arbitrary measurable probability space, measurable action and Real reward coordinates, Markov Real arm kernel, common centered HasSubgaussianMGF proxy, positive exploration pulls, K*m<=n, round-robin exploration action laws, source-shaped history least-encoded commit, persistence, and selected initial/full-history feedback laws. It adds no StandardBorelSpace Omega, full trajectory law, independence, caller-supplied local-score equality, preassembled horizon action equality, or infinite-horizon equality. Retrieval evidence is pinned LML commit 19dc3ab132c2a7539f5944503d1114eac4c5bb74, Learning.history, pullCount'/sumRewards'/empMean', ETC.arm_mul, measurableArgmax Nat.find semantics, Mathlib Finset finite sums, and the compiled least-encoded action leaf; LML remains source/card evidence rather than a local import. Failure policy: source-shaped history empirical-mean mapping is closed, and the downstream local field-compatibility theorem now compiles. Only a true cross-toolchain import adapter to the actual LML symbols remains; do not claim Bandits.ETC.regret_le itself is imported.",
        "mathlib_routes": [
            "MLIB-FINSET-SUMS",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-ETC-NATIVE-REAL-LEAST-ENCODED-ACTION-EXACT-REGRET",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-ETC-NATIVE-REAL-LML-FIELD-COMPAT-EXACT-REGRET",
        "leaf_ids": [
            "ETC-NATIVE-REAL-LML-FIELD-COMPAT-EXACT-REGRET",
        ],
        "module": "BanditRLProof.Algorithms.ETCRealLMLCompat",
        "status": "leanCompiled",
        "declarations": [
            "ETC.RealStationaryETCSequence",
            "ETC.regret_le_of_realStationaryETCSequence",
        ],
        "role": "Compiled local LML-field compatibility theorem for the exact native Real ETC route. RealStationaryETCSequence bundles the exact consequences consumed from the pinned source: measurable actions and feedback, round-robin arm_of_lt behavior, history-score least-encoded arm_mul behavior, arm_of_ge persistence, and initial/successor stationary feedback condDistrib laws. regret_le_of_realStationaryETCSequence projects those fields into the compiled history-score endpoint and returns the exact LML-shaped finite-arm sum. Local APIs/imports are ETCRealHistoryScore, Mathlib Measure/Kernel conditional distributions, finite pair histories, realLeastEncodedArgmax, contextIndependentOfActionLaws, and the prior exact-regret theorem. Regularity is IsProbabilityMeasure mu, IsMarkovKernel nu, common centered HasSubgaussianMGF proxy, positive exploration pulls, and K*m<=n; the structure itself records the same measurability, action, and feedback-law consequences used by the theorem. No StandardBorelSpace Omega, full trajectory law, independence, extra local-score premise, or preassembled action equality is added. Retrieval evidence is pinned LML IsAlgEnvSeq fields, stationaryEnv feedback formulas, ETC.arm_of_lt/arm_mul/arm_of_ge, Bandits.ETC.regret_le at commit 19dc3ab132c2a7539f5944503d1114eac4c5bb74, and ABRL toolchain evidence: Lean/mathlib v4.29.1 versus LML v4.32.0-rc1 with mathlib 9ca31d8b72cf8c317e49c301bfdbfbe91fc49136. Failure policy: the full mathematical theorem is locally compiled under the faithful field bundle. The only direct-import boundary is cross-toolchain symbol identity; do not report the upstream LML declaration as imported, and do not upgrade the entire repository as part of this narrow leaf.",
        "mathlib_routes": [
            "MLIB-PROBABILITY-KERNEL",
            "MLIB-MEASURE-INTEGRAL",
            "LOCAL-LEAF-ETC-NATIVE-REAL-HISTORY-SCORE-SOURCE-EXACT-REGRET",
            "LML-ETC-REGRET",
        ],
    },
    {
        "id": "LOCAL-LEAF-EXPECTATION-SUMS",
        "module": "BanditRLProof.ExpectationSums",
        "status": "leanCompiled",
        "declarations": [
            "lintegral_finset_sum_actionTrace_eval_eq_indicator_one",
        ],
        "role": "Compiled ENNReal lower-integral finite-sum bridge for action-equality pull-event indicators.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-EXPECTATION-PULLCOUNT",
        "module": "BanditRLProof.ExpectationPullCount",
        "status": "leanCompiled",
        "declarations": [
            "lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq",
        ],
        "role": "Compiled ENNReal lower-integral identity for scalar-casted pull counts.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-EXPECTATION-WEIGHTED-PULLCOUNT",
        "module": "BanditRLProof.ExpectationWeightedPullCount",
        "status": "leanCompiled",
        "declarations": [
            "lintegral_finset_sum_gap_mul_natCast_pullCount_eq",
        ],
        "role": "Compiled ENNReal lower-integral weighted pull-count bridge before Bochner expectation or algorithm-specific regret.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-EXPECTATION-PULLCOUNT-BOUNDS",
        "module": "BanditRLProof.ExpectationPullCountBounds",
        "status": "leanCompiled",
        "declarations": [
            "lintegral_natCast_pullCount_le_time",
        ],
        "role": "Compiled ENNReal/probability pull-count budget bound under a probability measure.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-EXPECTATION-WEIGHTED-PULLCOUNT-BOUNDS",
        "module": "BanditRLProof.ExpectationWeightedPullCountBounds",
        "status": "leanCompiled",
        "declarations": [
            "lintegral_finset_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time",
        ],
        "role": "Compiled ENNReal/probability weighted pull-count budget bound under a probability measure.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS"],
    },
    {
        "id": "LOCAL-LEAF-EXPECTATION-FINITE-BANDIT-BOUNDS",
        "module": "BanditRLProof.ExpectationFiniteBanditBounds",
        "status": "leanCompiled",
        "declarations": [
            "lintegral_univ_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time",
        ],
        "role": "Compiled Fin K / Finset.univ specialization of the ENNReal/probability weighted pull-count budget bound.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS", "MLIB-FINTYPE-FIN"],
    },
    {
        "id": "LOCAL-LEAF-EXPECTATION-FINITE-BANDIT-MODEL-BOUNDS",
        "module": "BanditRLProof.ExpectationFiniteBanditModelBounds",
        "status": "leanCompiled",
        "declarations": [
            "lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time",
        ],
        "role": "Compiled ENNReal.ofReal surrogate bound for FiniteBanditModel Rat gaps over finite-arm weighted pull counts.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS", "MLIB-FINTYPE-FIN", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-EXPECTATION-PSEUDOREGRET-OFREAL-BOUNDS",
        "module": "BanditRLProof.ExpectationPseudoRegretOfRealBounds",
        "status": "leanCompiled",
        "declarations": [
            "lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg",
        ],
        "role": "Compiled ENNReal.ofReal lower-integral pseudo-regret bound under explicit model-gap nonnegativity.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS", "MLIB-FINTYPE-FIN", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-EXPECTATION-PSEUDOREGRET-RAT-BOUNDS",
        "leaf_ids": [
            "EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG",
            "EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP",
        ],
        "module": "BanditRLProof.ExpectationPseudoRegretRatBounds",
        "status": "leanCompiled",
        "declarations": [
            "lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg",
            "lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time",
        ],
        "role": "Compiled Rat-level and model-derived gap nonnegativity adapters for the ENNReal.ofReal lower-integral pseudo-regret bound.",
        "mathlib_routes": ["MLIB-MEASURE-INTEGRAL", "MLIB-FINSET-SUMS", "MLIB-FINTYPE-FIN", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-SCALAR-ENNREAL",
        "module": "BanditRLProof.ScalarENNReal",
        "status": "leanCompiled",
        "declarations": [
            "ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg",
        ],
        "role": "Compiled scalar faithfulness leaf moving ENNReal.ofReal through nonnegative finite weighted Nat-count sums.",
        "mathlib_routes": ["MLIB-FINSET-SUMS", "MLIB-ORDER-ALGEBRA"],
    },
    {
        "id": "LOCAL-LEAF-SCALAR-PSEUDOREGRET",
        "module": "BanditRLProof.ScalarPseudoRegret",
        "status": "leanCompiled",
        "declarations": [
            "ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg",
        ],
        "role": "Compiled scalar/model faithfulness bridge from Rat-valued pseudoRegret to the ENNReal.ofReal weighted pull-count expression under explicit gap nonnegativity.",
        "mathlib_routes": ["MLIB-FINSET-SUMS", "MLIB-ORDER-ALGEBRA"],
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
    print("$ " + " ".join(shlex.quote(part) for part in cmd), flush=True)
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


def read_snapshot(path: Path, limit: int) -> str:
    """Read a bounded head/tail snapshot without cutting partial lines."""
    if not path.exists():
        return ""
    text = path.read_text(encoding="utf-8")
    if len(text) <= limit:
        return text
    half = max(1, limit // 2)
    head = text[:half]
    tail = text[-half:]
    if "\n" in head:
        head = head[:head.rfind("\n")]
    if "\n" in tail:
        tail = tail[tail.find("\n") + 1:]
    omitted = len(text) - len(head) - len(tail)
    marker = f"<!-- {omitted} characters omitted from the middle of this snapshot. -->"
    return f"{head.rstrip()}\n\n{marker}\n\n{tail.lstrip()}"


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
    roadmap = load_lean_route_roadmap() if LEAN_ROUTE_ROADMAP.exists() else {}
    haystacks = {
        "lml": LML_CARDS,
        "mathlib": MATHLIB_CARDS,
        "textbook": BANDIT_TEXTBOOK_CARDS,
        "paper": BANDIT_PAPER_CARDS,
        "scenario": BANDIT_SCENARIO_CARDS,
        "weapon": PROOF_WEAPON_CARDS,
        "local": LOCAL_LEAF_CARDS,
        "spine": roadmap.get("shared_spines", []),
        "route": roadmap.get("routes", []),
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


def load_lean_route_roadmap() -> dict:
    if not LEAN_ROUTE_ROADMAP.exists():
        raise SystemExit(f"route roadmap not found: {rel(LEAN_ROUTE_ROADMAP)}")
    return json.loads(read_text(LEAN_ROUTE_ROADMAP))


def roadmap_routes() -> list[dict]:
    roadmap = load_lean_route_roadmap()
    return list(roadmap.get("routes", []))


def find_route(route_id: str) -> dict:
    route_id_norm = route_id.lower()
    for route in roadmap_routes():
        if route.get("id", "").lower() == route_id_norm:
            return route
    available = ", ".join(route.get("id", "") for route in roadmap_routes())
    raise SystemExit(f"unknown route id: {route_id}\navailable routes: {available}")


def cmd_list_routes(args: argparse.Namespace) -> int:
    routes = roadmap_routes()
    for route in routes:
        if args.priority and route.get("priority") != args.priority:
            continue
        scenarios = ", ".join(route.get("scenario_cards", []))
        print(f"{route.get('id')}: {route.get('title')} [{route.get('priority')}] :: {scenarios}")
    return 0


def cmd_route_plan(args: argparse.Namespace) -> int:
    route = find_route(args.id)
    if args.json:
        print(json.dumps(route, indent=2, ensure_ascii=False))
        return 0
    print(f"# {route['id']}: {route['title']}")
    print(f"priority: {route.get('priority', '')}")
    print()
    print("scenario cards:")
    for item in route.get("scenario_cards", []):
        print(f"- {item}")
    print()
    print("source cards:")
    for item in route.get("source_cards", []):
        print(f"- {item}")
    print()
    print("proof weapons, inspiration only:")
    for item in route.get("proof_weapons", []):
        print(f"- {item}")
    print()
    print("compiled local core:")
    for item in route.get("compiled_local_core", []):
        print(f"- {item}")
    print()
    print("next Mathlib-ready leaves:")
    for item in route.get("next_mathlib_ready_leaves", []):
        print(f"- {item}")
    print()
    print("layered route:")
    for layer in route.get("layers", []):
        print(f"- {layer.get('name')}:")
        for node in layer.get("nodes", []):
            print(f"  - {node}")
    print()
    print(f"reviewer gate: {route.get('reviewer_gate', '')}")
    if args.with_commands:
        print()
        print("useful commands:")
        print(f"- python3 tools/bandit.py search-memory {shlex.quote(route['id'])}")
        print(f"- python3 tools/bandit.py route-plan {shlex.quote(route['id'])} --json")
        print("- python3 tools/bandit.py list-lean-decls --statement")
        print("- python3 tools/bandit.py unfinished")
        print("- python3 tools/bandit.py check")
    return 0


def cmd_screen_plan(args: argparse.Namespace) -> int:
    route = find_route(args.route) if args.route else None
    task = args.task
    lower_count = args.lower_count
    cycles = args.cycles
    profile = args.agent_profile
    print("# ABRL screen/codex run plan")
    print()
    if route:
        print(f"route: {route['id']} - {route['title']}")
        print(f"reviewer gate: {route.get('reviewer_gate', '')}")
        print()
    print("preflight:")
    print("python3 tools/bandit.py check")
    print("python3 tools/bandit.py unfinished")
    if route:
        print(f"python3 tools/bandit.py route-plan {shlex.quote(route['id'])} --with-commands")
    print()
    print("screen command:")
    print(f"screen -S abrl-{task}")
    print()
    print("inside screen:")
    print(f"python3 tools/bandit.py blueprint-refresh {shlex.quote(task)}")
    print(f"python3 tools/bandit.py memory-refresh {shlex.quote(task)}")
    print(
        "python3 tools/bandit.py sleep-run "
        f"{shlex.quote(task)} --cycles {cycles} --lower-count {lower_count} "
        "--execute "
        f"--agent-profile {shlex.quote(profile)} "
        "--check-each-cycle --stop-on-error"
    )
    print(f"python3 tools/bandit.py memory-refresh {shlex.quote(task)} --run-id latest")
    print(f"python3 tools/bandit.py blueprint-refresh {shlex.quote(task)}")
    print("python3 tools/bandit.py check")
    print()
    print("reviewer checklist:")
    for item in load_lean_route_roadmap().get("screen_loop", {}).get("reviewer_must_check", []):
        print(f"- {item}")
    print()
    print("lower-agent rule: do not start from the whole route; middle must issue one exact Lean leaf packet.")
    return 0


def cmd_render_roadmap_assets(_args: argparse.Namespace) -> int:
    return run(["python3", "tools/render_lean_tree_assets.py"])


def cmd_blueprint_refresh(args: argparse.Namespace) -> int:
    if not task_exists(args.id):
        raise SystemExit(f"task file not found: {rel(task_file(args.id))}")
    task_text = read_snapshot(task_file(args.id), 14000)
    conversion_text = read_snapshot(ROOT / "conversion-windows" / f"{args.id}.md", 14000)
    obligations_text = read_snapshot(ROOT / "proof-obligations" / f"{args.id}.md", 14000)
    completion_text = read_snapshot(ROOT / "docs" / "completion_gap_audit.md", 18000)
    adaptive_text = read_snapshot(ROOT / "docs" / "adaptive_harness_design.md", 18000)
    foundation_leaf_text = read_snapshot(ROOT / "research-wiki" / "theory-tree" / "mathlib-foundation-leaf-map.md", 22000)
    route_roadmap_text = read_optional(LEAN_ROUTE_ROADMAP, 10_000_000)
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

## Structured Lean Route Roadmap

```json
{route_roadmap_text or "{}"}
```

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
        "lean_route_roadmap": load_lean_route_roadmap() if LEAN_ROUTE_ROADMAP.exists() else {},
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
            "research-wiki/theory-tree/lean-route-roadmap.json",
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
    if getattr(args, "require_review_response", False) or getattr(args, "require_review_direction", False):
        code = cmd_review_status(argparse.Namespace(
            prompt=str(DEFAULT_REVIEW_PROMPT.relative_to(ROOT)),
            pending=str(DEFAULT_REVIEW_PENDING.relative_to(ROOT)),
            response_stem=DEFAULT_REVIEW_RESPONSE_STEM,
            boundary=DEFAULT_REVIEW_BOUNDARY,
            require_response=True,
            json=False,
        ))
        if code != 0:
            return code
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
            require_review_response=args.require_review_response,
            require_review_direction=getattr(args, "require_review_direction", False),
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


UNFINISHED_STATUSES = {"missing-leaf", "import-route", "theorem-card", "weapon-only", "gate-pending"}


def parse_markdown_table(path: Path) -> list[dict[str, str]]:
    """Parse simple pipe tables used by ABRL ledgers."""
    if not path.exists():
        return []
    rows: list[list[str]] = []
    for raw in read_text(path).splitlines():
        stripped = raw.strip()
        if not stripped.startswith("|") or not stripped.endswith("|"):
            continue
        cells = [cell.strip() for cell in stripped.strip("|").split("|")]
        if not cells or all(set(cell) <= {"-", ":"} for cell in cells):
            continue
        rows.append(cells)
    if len(rows) < 2:
        return []
    header = rows[0]
    parsed: list[dict[str, str]] = []
    for cells in rows[1:]:
        if len(cells) != len(header):
            continue
        parsed.append(dict(zip(header, cells)))
    return parsed


def clean_cell(value: str) -> str:
    return value.replace("`", "").strip()


def cmd_unfinished(args: argparse.Namespace) -> int:
    leaf_path = ROOT / "research-wiki" / "theory-tree" / "mathlib-foundation-leaf-map.md"
    backlog_path = ROOT / "research-wiki" / "open-problems" / "bandit-proof-backlog.md"

    statuses = set(args.status or UNFINISHED_STATUSES)
    leaf_rows = []
    for row in parse_markdown_table(leaf_path):
        status = clean_cell(row.get("Current status", ""))
        if status in statuses:
            leaf_rows.append(row)

    backlog_rows = parse_markdown_table(backlog_path)

    print(f"unfinished leaf rows from {rel(leaf_path)}")
    if not leaf_rows:
        print("  no matching rows")
    for row in leaf_rows:
        leaf_id = clean_cell(row.get("Leaf id", ""))
        status = clean_cell(row.get("Current status", ""))
        statement = row.get("Intended statement shape", "").strip()
        retrieval = row.get("Retrieval cards", "").strip()
        contract = row.get("Regularity contract", "").strip()
        print(f"- {leaf_id} [{status}] {statement}")
        if retrieval:
            print(f"  retrieval: {retrieval}")
        if contract:
            print(f"  contract: {contract}")

    print()
    print(f"open proof backlog from {rel(backlog_path)}")
    if not backlog_rows:
        print("  no backlog rows")
    for row in backlog_rows:
        problem_id = clean_cell(row.get("Problem id", ""))
        status = clean_cell(row.get("Current status", ""))
        target = row.get("Target", "").strip()
        next_leaf = row.get("Next leaf", "").strip()
        print(f"- {problem_id} [{status}] {target}")
        if next_leaf:
            print(f"  next leaf: {next_leaf}")

    print()
    print("current recommendation")
    print("- PULLCOUNT-LIST-RANGE, SUMREWARDS-LIST-RANGE, and PSEUDOREGRET-LIST-RANGE are the dependency-light finite-prefix bridges.")
    print("- PULLCOUNT-FINSET, SUMREWARDS-FINSET, and PSEUDOREGRET-FINSET are compiled Mathlib wrappers.")
    print("- REGRET-PULLCOUNT is compiled locally as a deterministic consumer leaf.")
    print("- PULLCOUNT-SUM-TIME is compiled locally as a deterministic finite-action count partition leaf.")
    print("- MEAS-FIN-ACTION is compiled locally as a measurable action-event canary.")
    print("- MEAS-PULL-INDICATOR is compiled locally as a measurable pull-event indicator canary.")
    print("- MEAS-REWARD is compiled locally as a selected-reward indicator measurability canary.")
    print("- MEAS-HISTORY is compiled locally as a finite action/reward history product-measurability surface over Finset.Iic prefixes.")
    print("- FILTRATION-HISTORY is compiled locally as a history-filtration canary generated by past action/reward singleton events.")
    print("- HISTORY-FILTRATION-FINITEPAIR-COMAP is compiled locally as a discrete/countable bridge: finite pair histories are measurable at later generated-history filtration levels, History.historyFiltration ... (n + 1) is exactly the comap of History.finitePairHistoryOfTrace ... n, and the shifted History.historyFiltrationSucc ... n has the same comap form; this aligns the filtration sigma-algebra with Mathlib finite-prefix conditional-law surfaces but does not prove reward-law or trajectory-law transport.")
    print("- ADAPTED-ACTION is compiled locally as a countable/discrete past-coordinate measurability canary against History.historyFiltration; full policy predictability remains out of scope.")
    print("- IID-REWARD-FAMILY is compiled locally as Mathlib-backed infinite-product coordinate independence wrappers, including a reward-trace specialization.")
    print("- MEAS-POLICY is compiled locally as a measurable policy/state composition surface with arbitrary-filtration and generated-history-filtration specializations.")
    print("- POLICY-GENERATED-ACTION-TRACE-MEASURABILITY is compiled locally as a policy-generated action trace coordinate-measurability surface, including a shifted time-indexed generated trace whose i+1 coordinate is selected by policy i and is predictable from F_i when the state is F_i-measurable.")
    print("- KERNEL-REWARD is compiled locally as a Mathlib Markov-kernel reward-law contract surface with context/action selected-measure measurability wrappers.")
    print("- POSTERIOR-KERNEL is compiled locally as a Mathlib Markov-kernel posterior contract surface over histories and environments; Bayes-rule identification and Thompson probability matching remain separate.")
    print("- TS-POSTERIOR-ACTION-IDENTITY-LEDGER is compiled locally as a Thompson probability-matching contract surface: a posterior kernel, Thompson action kernel, measurable bestAction map, and event-level action-law equality yield event and singleton posterior best-action probability consumers; Bayes-rule identification, posterior sampler construction, and Bayesian regret remain separate.")
    print("- TS-POSTERIOR-BEST-ACTION-MEASURABILITY is compiled locally as a Thompson regularity leaf: for countable singleton-measurable environment spaces, any bestAction selector is measurable, and the posterior-action identity ledger can be built without a separate bestAction measurability proof; the event-level posterior action law remains assumed.")
    print("- POLICY-REWARD-ONE-STEP-KERNEL-COMPOSITION is compiled locally as a one-step context/state Markov reward kernel obtained from a measurable policy and context/action reward kernel.")
    print("- POLICY-REWARD-IIC-HISTORY-PARTIAL-TRAJECTORY is compiled locally as a Mathlib partialTraj finite-prefix reward-history kernel surface from time-indexed policies and measurable context/state extractors.")
    print("- KERNEL-POLICY-BIND is compiled locally as a Mathlib partialTraj finite-prefix action/reward pair trajectory-kernel surface from deterministic policy action kernels and selected reward kernels, with selected-reward marginal wrappers for one-step and history-step action/reward kernels and a one-step frozen-prefix extension map wrapper.")
    print("- POLICY-REWARD-PARTIALTRAJ-SUCC-NEXT-MAP is compiled locally as the Mathlib partialTraj one-step next-coordinate marginal wrapper for reward-history and action/reward pair trajectories; condExpKernel trajectory-law identification remains open.")
    print("- POLICY-REWARD-PARTIALTRAJ-SUCC-EXTEND-MAP is compiled locally as the Mathlib partialTraj one-step full-extension wrapper: the n-to-n+1 action/reward trajectory measure is the history-step pair kernel pushed through History.extendPairHistorySucc.")
    print("- POLICY-REWARD-TRAJMEASURE-CONDDISTRIB is compiled locally as the canonical Mathlib trajMeasure conditional-distribution law: for the action/reward history-step kernel family, condDistrib of the next pair given the finite prefix is a.e. RewardKernel.actionRewardHistoryStepKernelFamily; the next action coordinate law is its Prod.fst marginal and the selected policy-action Dirac law is compiled; the next reward coordinate law is its Prod.snd marginal and the selected context/action reward-measure form is compiled; ambient Omega/condExpKernel and History.historyFiltrationSucc transport remain open.")
    print("- KERNEL-CENTERED-REWARD-LAW-TRANSFER is compiled locally as a kernel-level selected reward law transfer surface: policy-composed and finite reward-history step kernels inherit centered integrability, zero integral, and sub-Gaussian MGF witnesses from pointwise context/action reward laws; condExpKernel identification remains open.")
    print("- KERNEL-REWARD-MAP-LAW-TRANSFER is compiled locally as measure-level action/reward marginal map equalities for one-step and history-step action/reward kernels: Prod.snd recovers the selected reward law and Prod.fst recovers the Dirac law at the policy-selected action; condExpKernel trajectory-law identification remains open.")
    print("- COND-EXPECT-REWARD-CONDEXPKERNEL-ZERO is compiled locally as a narrow condExpKernel-to-condExp zero bridge for centered rewards; it does not construct the trajectory-law condExpKernel identification.")
    print("- COND-EXPECT-REWARD-CONDDISTRIB-TO-CONDEXPKERNEL-MAP is compiled locally as a countable-target Mathlib bridge from condDistrib laws to condExpKernel pushforward map laws; its trim companion uses conditioning-measurable singleton probabilities plus ae_eq_trim_of_measurable, and it still consumes a condDistrib identification rather than constructing a trajectory law.")
    print("- COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-SELECTED-REWARD-CONDEXPKERNEL-MAP is compiled locally as a reward-only canonical trajectory-law source: RewardKernel.historyStepKernelFamily is registered as Markov and Mathlib condDistrib_trajMeasure is bridged to a selected-reward condExpKernel.map law at the finite reward prefix; generated finite-pair alignment and trim-selected-source construction are compiled downstream, while arbitrary ambient Omega transport remains open.")
    print("- COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-GENERATED-FINITEPAIR-CONDITIONING is compiled locally: generatedActionFromRewardHistory finite pair prefixes and finite reward prefixes induce the same comap measurable space, History.historyFiltrationSucc reduces to that reward-prefix comap, and the canonical reward-only selected-reward law is exposed on the generated finite-pair conditioning surface; its sound trim strengthening is compiled in the downstream canonical selected-source leaf.")
    print("- COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-TRIM-SELECTED-SOURCE is compiled locally: the countable-target condDistrib bridge is strengthened to the conditioning trim through measurable singleton probability functions, specialized to the reward-only historyStepKernelFamily trajMeasure, transported to the generated finite-pair comap, and used to construct GeneratedActionSelectedRewardFinitePairHistoryLawSource without a selected-reward source assumption; the canonical full partialTraj endpoint is compiled downstream, while arbitrary ambient Omega transport remains open.")
    print("- COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-GENERATED-PARTIALTRAJ-LAW is compiled locally as the theorem-level canonical endpoint: the canonical selected source is converted through deterministic generated actions into GeneratedActionPartialTrajectoryPairLawSource, and the successor finite pair-prefix condExpKernel pushforward is proved equal to RewardKernel.actionRewardPartialTrajectoryKernel without ambient law assumptions; its conditional mean-zero consumer is compiled downstream, while arbitrary ambient transport remains open.")
    print("- COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-MEAN-ZERO is compiled locally: the canonical full partialTraj law plus CenteredRewardKernelLaw and explicit ambient centered-reward integrability prove successor conditional expectation zero under generated finite-pair history; pointwise raw bounds on every Nat-to-Rat trace are intentionally not required, and the canonical conditional-MGF consumer is compiled downstream.")
    print("- COND-EXPECT-REWARD-CONDEXPKERNEL-COND-MGF-INTEGRATED-TRANSFER is compiled locally: target-wise HasSubgaussianMGF laws with a common proxy now derive ambient exponential integrability through Measure.integrable_comp_iff and yield HasCondSubgaussianMGF without h_integrable_exp; centered measurability, conditional reward-law identification, and variance domination remain explicit.")
    print("- COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-COND-MGF is compiled locally: the canonical full partialTraj law, measurable mean, a deterministic finite-history variance ceiling, and the integrated target-law transfer yield HasCondSubgaussianMGF for the successor centered reward under generated finite-pair history with no ambient law-source or h_integrable_exp hypothesis; the canonical finite-sum tail is compiled downstream.")
    print("- COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-SUM-TAIL is compiled locally: a zero-initialized successor centered-reward process is StronglyAdapted to generated history, canonical conditional-MGF witnesses feed the Mathlib conditional sum-tail wrapper, and an ENNReal Azuma-Hoeffding bound holds for the Finset.range n sum covering rewards 1 through n-1; empirical-mean/confidence specialization, arbitrary ambient transport, and final bandit theorems remain open.")
    print("- COND-EXPECT-REWARD-REWARDONLY-TRAJMEASURE-CENTERED-AVERAGE-TAIL is compiled locally: for m > 0, the canonical Finset.range (m + 1) centered sum tail is rewritten through le_div_iff₀ into an ENNReal tail for its aggregate successor-reward average at threshold eps; this is not an arm-wise empirical-mean or UCB/ETC confidence theorem. The retrieval index still names absent COND-EXPECT-REWARD conversion-window and proof-obligation files, which must be restored before treating their route metadata as evidence.")
    print("- COND-EXPECT-REWARD-TRAJMEASURE-PAIR-CONDEXPKERNEL-MAP is compiled locally as the canonical trajMeasure next-pair specialization: conditioning on the finite pair prefix and pushing condExpKernel forward by the next action/reward coordinate recovers RewardKernel.actionRewardHistoryStepKernelFamily; ambient Omega/History.historyFiltrationSucc transport remains open.")
    print("- COND-EXPECT-REWARD-TRAJMEASURE-ACTION-CONDEXPKERNEL-MAP is compiled locally as the canonical trajMeasure next-action specialization: projecting the canonical next-pair condExpKernel map law through Prod.fst recovers the Dirac law at the policy-selected action; ambient Omega/History.historyFiltrationSucc transport remains open.")
    print("- COND-EXPECT-REWARD-TRAJMEASURE-ACTION-MARGINAL-CONDEXPKERNEL-MAP is compiled locally as the direct countable-Action canonical action-marginal law: applying the condDistrib-to-condExpKernel bridge to the next action coordinate and the canonical action condDistrib law recovers the Prod.fst marginal of RewardKernel.actionRewardHistoryStepKernelFamily; ambient Omega/History.historyFiltrationSucc transport remains open.")
    print("- COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-ACTION-CONDEXPKERNEL-MAP is compiled locally as the direct countable-Action trajMeasure next-action specialization: applying the condDistrib-to-condExpKernel bridge to the next action coordinate and the canonical action condDistrib law recovers the policy-selected Dirac law without requiring Countable (Action x Reward); ambient Omega/History.historyFiltrationSucc transport remains open.")
    print("- COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-ACTION-CONDEXPKERNEL-AE is compiled locally as the canonical selected-action conditional a.e. law: a Dirac pushforward equality for the next-action condExpKernel map now yields the Filter.EventuallyEq action side consumed by the split-law builder; ambient Omega/History.historyFiltrationSucc transport remains open.")
    print("- COND-EXPECT-REWARD-TRAJMEASURE-EXTEND-CONDEXPKERNEL-MAP is compiled locally as the canonical extension-map specialization: the canonical next-pair condExpKernel map law pushed through History.extendPairHistorySucc recovers the one-step RewardKernel.actionRewardPartialTrajectoryKernel surface; ambient Omega/History.historyFiltrationSucc transport remains open.")
    print("- COND-EXPECT-REWARD-TRAJMEASURE-PREFIX-CONDEXPKERNEL-MAP is compiled locally as the canonical full-prefix specialization: the extension-map law plus condExpKernel frozen-prefix evidence rewrites the pushforward to Preorder.frestrictLe (n + 1), recovering RewardKernel.actionRewardPartialTrajectoryKernel on the full finite prefix; ambient Omega/History.historyFiltrationSucc transport remains open.")
    print("- COND-EXPECT-REWARD-TRAJMEASURE-FINITEPAIRHISTORY-CONDEXPKERNEL-MAP is compiled locally as the project-notation canonical wrapper: the same trajMeasure full-prefix law is stated with History.finitePairHistoryOfTrace for the old and successor pair prefixes, matching the theorem-card shape while still not transporting to an arbitrary ambient Omega process.")
    print("- COND-EXPECT-REWARD-TRAJMEASURE-REWARD-CONDEXPKERNEL-MAP is compiled locally as the canonical trajMeasure specialization: conditioning on the finite pair prefix and pushing condExpKernel forward by the next reward coordinate recovers the history-step reward marginal; ambient Omega/History.historyFiltrationSucc transport remains open.")
    print("- COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-CONDEXPKERNEL-MAP is compiled locally as the selected-reward form of the canonical trajMeasure condExpKernel map law; ambient Omega/History.historyFiltrationSucc transport remains open.")
    print("- COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-FINITEPAIRHISTORY-CONDEXPKERNEL-MAP is compiled locally as the project-notation selected-reward canonical wrapper: the same selected context/action reward-measure law is stated with History.finitePairHistoryOfTrace as the finite pair prefix; ambient Omega/History.historyFiltrationSucc transport remains open.")
    print("- COND-EXPECT-REWARD-TRAJMEASURE-SELECTED-REWARD-REWARDHISTORY-CONDEXPKERNEL-MAP is compiled locally as the reward-history projection of the canonical selected-reward trajMeasure law: pairContext/pairState are built from History.pairHistoryRewardProjection, so the RHS is stated with History.finiteRewardHistoryOfTrace; ambient transport remains open.")
    print("- COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-LAW-SOURCE-CONTRACT is compiled locally as an ambient source contract and adapter: it packages the generated History.historyFiltrationSucc selected-reward law stated at History.finitePairHistoryOfTrace and converts it into GeneratedActionPartialTrajectoryPairLawSource; it still consumes, rather than proves, the reward-law transport.")
    print("- COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-FROM-COMAP-LAW is compiled locally as a source constructor and theorem wrapper: a selected-reward condExpKernel.map law stated with conditioning sigma-algebra as the comap of History.finitePairHistoryOfTrace now builds both the generated selected-reward finite-pair-history source and the full generated finite-pair partialTraj source, and directly exposes the theorem-card-shaped full finite-pair partialTraj/condExpKernel law through the local History.historyFiltrationSucc comap bridge; the selected-source, partialTraj-source, and theorem-wrapper layers now accept both generated-history-trim and comap-trim law surfaces, but still consume the selected-reward law and do not prove ambient trajectory transport.")
    print("- COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-PARTIALTRAJ-LAW is compiled locally as a source-projection theorem: a GeneratedActionSelectedRewardFinitePairHistoryLawSource now directly exposes the generated-history full finite-pair partialTraj/condExpKernel law for generatedActionFromRewardHistory; it still consumes, rather than proves, the selected-reward law field.")
    print("- COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE is compiled locally as a source conversion: a GeneratedActionDefinitionalActualRewardMapSource now yields the generated selected-reward finite-pair-history source by unfolding generatedActionFromRewardHistory and projecting pair histories to reward histories; it still consumes the actual-action reward-coordinate law.")
    print("- COND-EXPECT-REWARD-PRACTICAL-RAW-RANGE-SOURCE-TO-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE is compiled locally as a source-conversion route: the practical definitional raw-range/measurable-mean-range generated random next-pair package, including its uniform-variance and selected-history-variance wrappers, now directly yields the generated selected-reward finite-pair-history source by lowering through the full finite-pair partialTraj source projection; it still consumes the packaged random next-pair law and does not prove ambient trajectory transport.")
    print("- COND-EXPECT-REWARD-PRACTICAL-SOURCE-VIA-SELECTED-FINITEPAIRHISTORY-COND-MGF is compiled locally as a route-specific theorem surface: the practical raw-range source now reaches conditional mean-zero, and its uniform-variance/history-variance wrappers reach conditional MGF witnesses, by first projecting through the generated selected-reward finite-pair-history source and then using selected-source consumers; it still consumes the packaged random next-pair law and variance/proxy contracts.")
    print("- COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-MEAN-ZERO is compiled locally as a direct consumer: the generated selected-reward finite-pair-history source plus raw/mean range regularity yields ordinary succ-indexed conditional mean-zero, and the finite-pair comap selected-reward law can now be consumed directly into the same mean-zero surface with either the generated-history trim filter or the direct comap-trim filter; it still consumes, rather than proves, the selected-reward law.")
    print("- COND-EXPECT-REWARD-GENERATED-SELECTED-REWARD-FINITEPAIRHISTORY-SOURCE-COND-MGF is compiled locally as a direct concentration consumer: the generated selected-reward finite-pair-history source plus raw/mean range regularity now yields succ-indexed conditional sub-Gaussian MGF witnesses under either a global variance ceiling, a coarser global proxy, selected-history variance ceilings, or a coarser selected-history proxy; it still consumes the selected-reward law and variance/proxy contracts.")
    print("- COND-EXPECT-REWARD-TRAJMEASURE-PAIR-CONDEXPKERNEL-MAP-SPLIT is compiled locally as the canonical split-route next-pair law: selected-action conditional a.e. equality plus selected-reward condExpKernel map law recover the full history-step pair law under separate Countable Action and Countable Reward assumptions; ambient Omega/History.historyFiltrationSucc transport remains open.")
    print("- COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-CONSUMER is compiled locally as an explicit law/integral-equality consumer from history-step centered-reward zero integral to ordinary conditional mean-zero; it still assumes the trajectory-law condExpKernel identification.")
    print("- COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-MAP-CONSUMER is compiled locally as a reward-coordinate pushforward-map consumer plus frozen-past condition for ordinary conditional mean-zero; it now also has coordinate-measurable and generated-history raw/mean range wrappers that derive centered-reward integrability automatically; it still assumes, rather than proves, the trajectory-law condExpKernel identification.")
    print("- COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-COND-MGF-CONSUMER is compiled locally as the conditional sub-Gaussian analogue: a condExpKernel pushforward map law plus centered measurability and a deterministic variance-proxy upper bound yield Mathlib HasCondSubgaussianMGF; target-wise MGF laws derive exponential integrability, and coordinate-measurable/generated-history wrappers discharge the frozen-past equality, while ambient law construction remains open.")
    print("- COND-EXPECT-REWARD-FROZEN-HISTORY-CENTERED is compiled locally as a deterministic bridge from a frozen finite-history hypothesis to the centered-target a.e. equality required by the map-law consumer; it still assumes the history frozen-past proof itself.")
    print("- COND-EXPECT-REWARD-FROZEN-HISTORY-CONDEXPKERNEL is compiled locally as the conditional-kernel frozen-past route from mcond-measurable events to countable-valued variables and finite reward histories; it is fed by the finite-history measurability hookup and still assumes the trajectory-law reward identification.")
    print("- COND-EXPECT-REWARD-FINITE-HISTORY-MEAS-HOOKUP is compiled locally as the concrete finite reward-history measurability hookup: coordinate measurability at F i and the generated History.historyFiltrationSucc specialization now supply the frozen-past hypothesis; condExpKernel trajectory-law reward identification remains open.")
    print("- COND-EXPECT-REWARD-PAIR-HISTORY-FROZEN-HOOKUP is compiled locally as the finite action/reward pair-history frozen-past hookup under [Countable Action], with a generated History.historyFiltrationSucc specialization; the actual partialTraj/condExpKernel pair-law identification remains open.")
    print("- COND-EXPECT-REWARD-PAIR-HISTORY-SUCC-EXTEND-HOOKUP is compiled locally as the successor-extension bridge: the i+1 pair trace decomposes into a frozen pair prefix plus the random next pair under generated condExpKernel; the full partialTraj/condExpKernel joint law remains open.")
    print("- COND-EXPECT-REWARD-MAP-CONSUMER-FROZEN-HOOKUP is compiled locally as the map-law consumer with frozen-past discharged from coordinate measurability or generated History.historyFiltrationSucc; the reward-coordinate condExpKernel-to-historyStepKernelFamily pushforward identity remains open.")
    print("- COND-EXPECT-REWARD-PAIR-MAP-CONSUMER is compiled locally as the next action/reward pair-law consumer: a condExpKernel pushforward identity to RewardKernel.actionRewardHistoryStepKernelFamily now marginalizes through Prod.snd into the reward-coordinate map-law consumer, with a raw/mean range wrapper deriving centered-reward integrability automatically; the actual partialTraj-to-condExpKernel pair-law identification remains open.")
    print("- COND-EXPECT-REWARD-PAIR-MAP-HISTORYFILTRATION-HOOKUP is compiled locally as the generated History.historyFiltrationSucc specialization of the pair-law consumer; next-coordinate and prefix measurability are supplied by local history-filtration APIs, and a raw-reward/selected-mean range wrapper now derives centered-reward integrability automatically; the actual condExpKernel pair-law identity remains open.")
    print("- COND-EXPECT-REWARD-PAIR-MAP-HISTORYTRACE-PROJECTION-HOOKUP is compiled locally as the concrete finite trace-pair history and reward-projection context/state specialization of the generated-history pair-law consumer, with a raw-reward/selected-mean range wrapper deriving centered-reward integrability automatically; the actual condExpKernel pair-law identity remains open.")
    print("- COND-EXPECT-REWARD-PAIR-MAP-PROJECTION-MEAS-HOOKUP is compiled locally as the measurable reward-projection hookup for pair histories, deriving projected pairContext/pairState measurability from reward-history context/state measurability and now deriving centered-reward integrability from raw-reward/selected-mean range bounds; the actual condExpKernel pair-law identity remains open.")
    print("- COND-EXPECT-REWARD-PAIR-MAP-FINITEPAIRTRACE-HOOKUP is compiled locally as the named History.finitePairHistoryOfTrace specialization of the generated-history pair-law consumer; the actual condExpKernel pair-law identity remains open.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER is compiled locally as the partialTraj finite-pair-trace consumer: an explicit generated-history condExpKernel law for the extended pair trace projects through the partialTraj next-coordinate marginal into a reusable next-pair map-law adapter, then into the centered-reward consumer; a raw-reward/selected-mean range wrapper now derives centered-reward integrability automatically before consuming the same full finite-pair partialTraj law; the actual condExpKernel/partialTraj law remains open.")
    print("- COND-EXPECT-REWARD-GENERATED-TRAJECTORY-PARTIALTRAJ-PAIR-LAW-SOURCE-CONTRACT is compiled locally as a source-contract leaf: it packages the exact generatedActionFromRewardHistory full finite-pair partialTraj/condExpKernel law as an explicit source and feeds that source into the definitional generated random-pair map source constructor; it does not prove the law or upgrade the theorem-card row.")
    print("- COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-PROJECTION is compiled locally as a source-projection leaf: a GeneratedActionPartialTrajectoryPairLawSource exposes its full finite-pair partialTraj/condExpKernel law field as a named theorem matching the theorem-card law shape and now also lowers to the definitional actual reward-map, selected-reward finite-pair-history, and explicit generated-action actual reward-map source interfaces; it does not prove the law or upgrade the theorem-card row.")
    print("- COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-EXTEND-MAP is compiled locally as a source-constructor leaf: the narrower frozen-prefix extension-map partialTraj/condExpKernel law constructs the full GeneratedActionPartialTrajectoryPairLawSource through the existing extension-to-full-trace adapter; it still does not prove the extension-map law or upgrade the theorem-card row.")
    print("- COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-HISTORYSTEP-PAIR-LAW is compiled locally as a source-constructor leaf: a generated-history next-pair condExpKernel law identified with RewardKernel.actionRewardHistoryStepKernelFamily constructs the full GeneratedActionPartialTrajectoryPairLawSource via the next-pair-to-extension-map and extension-to-full-source adapters; it still does not prove the next-pair law or upgrade the theorem-card row.")
    print("- COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-SPLIT-NEXTPAIR-LAW is compiled locally as a source-constructor leaf: generated-history action conditional a.e. equality plus the policy-selected reward-coordinate condExpKernel map law construct the full GeneratedActionPartialTrajectoryPairLawSource through the split next-pair law builder and existing source adapters; it still does not prove either split law or upgrade the theorem-card row.")
    print("- COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-SELECTED-REWARD-LAW is compiled locally as a source-constructor/theorem-wrapper leaf: for generatedActionFromRewardHistory, the generated-trace action side is discharged automatically, so the policy-selected reward-coordinate condExpKernel map law alone constructs the full GeneratedActionPartialTrajectoryPairLawSource and directly exposes the full finite-pair partialTraj/condExpKernel law; it still does not prove the reward law or upgrade the theorem-card row.")
    print("- COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-FROM-DEFINITIONAL-MAP-SOURCE is compiled locally as a source-conversion leaf: a GeneratedActionRandomPairDefinitionalMapSource projects to the policy-selected reward-coordinate law and then constructs the full GeneratedActionPartialTrajectoryPairLawSource; it still consumes, rather than proves, the definitional random-pair source law.")
    print("- COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE is compiled locally as a source/comap source-conversion leaf: a GeneratedActionPartialTrajectoryPairLawSource plus measurable mean, centered reward-kernel law, raw reward range bounds, and deterministic mean range bounds builds the practical definitional raw-range/measurable-mean-range bounded source, and the finite-pair comap selected-reward law can now build that source directly by constructing the partialTraj source internally with either the generated-history trim filter or the direct comap-trim filter; it still consumes, rather than proves, the full finite-pair partialTraj/condExpKernel law route or selected-reward comap law.")
    print("- COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-SOURCE is compiled locally as a source/comap source-conversion leaf: the same GeneratedActionPartialTrajectoryPairLawSource plus raw/mean range regularity and a global variance ceiling builds the packaged uniform-variance practical source, and the finite-pair comap selected-reward law can now build that packaged source directly by constructing the partialTraj source internally with either the generated-history trim filter or the direct comap-trim filter; it still consumes, rather than proves, the full finite-pair partialTraj/condExpKernel law route, selected-reward comap law, or global variance ceiling.")
    print("- COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-MEAN-ZERO is compiled locally as a source-consumer leaf: the same GeneratedActionPartialTrajectoryPairLawSource plus raw/mean range regularity directly yields ordinary succ-indexed conditional mean-zero; it still consumes, rather than proves, the full finite-pair partialTraj/condExpKernel law.")
    print("- COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-COND-MGF is compiled locally as a source/comap consumer leaf: the same GeneratedActionPartialTrajectoryPairLawSource plus raw/mean range regularity and a global variance ceiling directly yields the succ-indexed conditional sub-Gaussian MGF witness, and the finite-pair comap selected-reward law can now be consumed directly into that witness by constructing the partialTraj source internally; it still consumes, rather than proves, the full finite-pair partialTraj/condExpKernel law route.")
    print("- COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF is compiled locally as a source/comap theorem route: the same GeneratedActionPartialTrajectoryPairLawSource plus raw/mean range regularity, a global variance ceiling, and varianceCeiling <= c directly yields the succ-indexed conditional sub-Gaussian MGF witness at coarser proxy c, and the finite-pair comap selected-reward law can now be consumed with either the generated-history trim filter or direct comap-trim filter by constructing the partialTraj source internally; it still consumes, rather than proves, the full finite-pair partialTraj/condExpKernel law route or proxy domination.")
    print("- COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-HISTORY-VARIANCE-SOURCE is compiled locally as a source/comap source-conversion leaf: the same GeneratedActionPartialTrajectoryPairLawSource plus raw/mean range regularity and selected-history variance ceilings builds the packaged history-variance practical source, and the finite-pair comap selected-reward law can now build that packaged source directly by constructing the partialTraj source internally with either the generated-history trim filter or the direct comap-trim filter; it still consumes, rather than proves, the full finite-pair partialTraj/condExpKernel law route, selected-reward comap law, or selected-history ceilings.")
    print("- COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-HISTORY-VARIANCE-COND-MGF is compiled locally as a source/comap consumer leaf: the same GeneratedActionPartialTrajectoryPairLawSource plus raw/mean range regularity and selected-history variance ceilings directly yields the succ-indexed conditional sub-Gaussian MGF witness at proxy varianceCeiling i, and the finite-pair comap selected-reward law can now be consumed with either the generated-history trim filter or direct comap-trim filter by constructing the partialTraj source internally; it still consumes, rather than proves, the full finite-pair partialTraj/condExpKernel law route.")
    print("- COND-EXPECT-REWARD-GENERATED-PARTIALTRAJ-PAIR-LAW-SOURCE-TO-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF is compiled locally as a source/comap consumer leaf: the same GeneratedActionPartialTrajectoryPairLawSource plus raw/mean range regularity, selected-history variance ceilings, and varianceCeiling i <= c directly yields the succ-indexed conditional sub-Gaussian MGF witness at coarser proxy c, and the finite-pair comap selected-reward law can now be consumed with either the generated-history trim filter or direct comap-trim filter by constructing the partialTraj source internally; it still consumes, rather than proves, the full finite-pair partialTraj/condExpKernel law route or proxy domination.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-CONDEXPKERNEL-PAIR-LAW-CARD is theorem-card-only: the exact missing law is the generated-history condExpKernel pushforward of History.finitePairHistoryOfTrace at i+1 equals RewardKernel.actionRewardPartialTrajectoryKernel at the frozen i-prefix; prove this from an explicit trajectory-law/disintegration source before adding more consumers.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER is compiled locally as the extension-map partialTraj consumer: Measure.map_congr turns the generated successor decomposition into a pushforward identity, a reusable adapter lifts an extension-map law back to the full finite-pair-trace partialTraj law, and a raw-reward/selected-mean range wrapper derives centered-reward integrability automatically before consuming the narrower extension-map law; the actual condExpKernel/partialTraj law remains open.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-FROM-PAIRMAP is compiled locally as the law builder from a next-pair condExpKernel pushforward identity to the extension-map partialTraj identity; the next-pair law itself remains open.")
    print("- COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER is compiled locally as the split-law builder and raw-range mean-zero consumer: conditional action a.e. equality plus reward-coordinate map law produce the full next-pair condExpKernel law, and raw-reward/selected-mean range evidence then yields succ-indexed conditional mean-zero through the finite-pair consumer; predictability and reward-law sources remain open.")
    print("- COND-EXPECT-REWARD-NEXTPAIR-SPLIT-PRODUCT-LAW is compiled locally as the ambient split-product law: conditional action a.e. equality plus reward-coordinate selected-measure law directly produce the fully random next-pair product pushforward, with a generated History.historyFiltrationSucc specialization from Policy.generatedActionTraceSucc plus an actual-action reward map law; the reward-coordinate law and ambient trajectory identification remain open.")
    print("- COND-EXPECT-REWARD-NEXTPAIR-RANDOM-PAIR-HISTORYSTEP-LAW is compiled locally as the law-shape adapter from a generated-action random next-pair source law stated with Measure.map (Prod.mk actualAction) selectedMeasure into the canonical RewardKernel.actionRewardHistoryStepKernelFamily pair law; the random-pair law itself remains assumed.")
    print("- COND-EXPECT-REWARD-ACTION-FREEZE-POLICY-HOOKUP is compiled locally as the action-freezing side of the split-law builder: countable F_i-measurable next actions plus trim-a.e. policy equality produce the conditional action a.e. equality; policy predictability and reward-law sources remain open.")
    print("- COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-HISTORY-HOOKUP is compiled locally as the generated-history action side of the split-law builder: visible finite pair histories, measurable pairState, and pointwise policy-generation equality produce the conditional action a.e. equality; reward-law sources remain open.")
    print("- COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE is compiled locally as the shifted generated-trace source for that action side: equality to the generated trace supplies the pointwise policy-generation equality; reward-law sources remain open.")
    print("- COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP is compiled locally as the generated-action plus policy-selected/actual/random-pair reward-law hookup: an actual-action pair-product law marginalizes to the actual-action reward-coordinate map law, while a fully random next-pair law first freezes the action coordinate via Measure.map_congr; both pair-law shapes expose reusable full finite-pair-trace partialTraj law adapters, and generatedActionFromRewardHistory actual-action reward-coordinate laws now directly construct a GeneratedActionPartialTrajectoryPairLawSource and expose the theorem-card-shaped full finite-pair partialTraj/condExpKernel law without an explicit action trace or generated-trace equality parameter; the direct generated-action policy-selected reward-coordinate, actual-action reward-coordinate, actual-action pair-product, and fully random next-pair law routes also consume raw/mean range regularity without a separate integrability hypothesis; the pair/reward-law source and ambient trajectory-to-condExpKernel identification remain open.")
    print("- MEAS-SELECTED-REWARD-FINITE-SUM is compiled locally as a finite-sum measurability bridge.")
    print("- MEAS-SUMREWARDS is compiled locally as a measurability bridge for the recursive sumRewards quantity.")
    print("- MEAS-REGRET is compiled locally as pseudoRegret random-variable measurability.")
    print("- MEAS-PULLCOUNT is compiled locally as pullCount random-variable measurability.")
    print("- MEAS-PULLCOUNT-CAST is compiled locally as scalar-casted pullCount measurability.")
    print("- INT-FINITE-SUM is compiled locally as Mathlib-backed finite-sum integrability wrappers for explicit Finset and Fintype term families.")
    print("- EXP-FINITE-SUM is compiled locally as Mathlib-backed Bochner finite-sum expectation wrappers for explicit Finset and Fintype term families.")
    print("- EXP-REGRET-PULLCOUNT is compiled locally as a Bochner/Real expected-regret decomposition from pseudoRegret to a finite sum of gap-weighted expected pull counts under explicit pull-count integrability.")
    print("- REAL-MEAN-REGRET-PULLCOUNT is compiled locally as an LML-aligned Real mean-regret finite-sum, pull-count, integrability, and Bochner expectation decomposition under explicit per-arm pull-count integrability. Its stationary Real kernel identity-integral specialization now compiles downstream.")
    print("- REAL-KERNEL-REGRET-PULLCOUNT is compiled locally as the stationary Real arm-kernel identity-integral specialization, including nonnegative kernel gaps and deterministic/Bochner gap-weighted pull-count decompositions. Kernel scalar bookkeeping is closed and the downstream Real ETC count/integration endpoint now compiles.")
    print("- REAL-ETC-EXPECTED-PULLCOUNT is compiled locally as the LML-shaped Real/Bochner per-arm count-to-commit-probability endpoint: measurable actionWithCommit pull counts are integrable, their expectation is exactly explorationPulls + (n - K * explorationPulls) * mu.real {commit = a}, and any commit-fiber probability bound yields the matching expected-count inequality.")
    print("- ETC-EXACT-COMMON-SUBGAUSSIAN-PER-ARM-EXPECTED-PULLCOUNT is compiled locally on the canonical generated-history Rat arm-law model: the pairwise proxy sum is exactly 2 * explorationPulls * sigma2, the threshold is explorationPulls * gap for a non-best arm, the commit fiber is bounded by exp (-(explorationPulls : Real) * gap^2 / (4 * sigma2)), and the matching Real/Bochner expected pull-count bound follows. Downstream native Real law/source, least-encoded action, and source-shaped history-score assembly now compile; faithful local field compatibility now compiles; only actual cross-toolchain LML symbol import remains.")
    print("- ETC-RAT-ARM-LAW-REAL-KERNEL-EXACT-REGRET is compiled locally: Rat arm laws are pushed forward to a Markov Real kernel, its identity-integral means and iSup gaps are identified exactly with cast model means/gaps, and the canonical per-arm exact count bounds assemble into the full LML-shaped finite sum for Real kernel regret. Downstream native Real product, prefix, source-law, least-encoded action, and history-score endpoints now compile; faithful local field compatibility now compiles; only actual cross-toolchain LML symbol import remains.")
    print("- ETC-NATIVE-REAL-EMPIRICAL-MEAN-ARGMAX-COUNT is compiled locally: Real reward traces now have exploration empirical means, a deterministic finite Real argmax with explicit tie behavior, a direct measurability proof that does not countabilize Real score vectors, and exact/upper expected pull-count consumers. Downstream reward-law, concentration, least-encoded tie, action, and finite-history score assembly now compile; faithful local field compatibility now compiles; only actual cross-toolchain LML symbol import remains.")
    print("- EXP-INDICATOR-PULL is compiled locally as an ENNReal lower-integral indicator/event-measure canary.")
    print("- EXP-FINSET-INDICATOR-PULL is compiled locally as an ENNReal lower-integral finite-sum bridge.")
    print("- EXP-PULLCOUNT-LINTEGRAL is compiled locally as an ENNReal lower-integral pullCount identity.")
    print("- EXP-WEIGHTED-PULLCOUNT-LINTEGRAL is compiled locally as an ENNReal lower-integral weighted pullCount bridge.")
    print("- EXP-PULLCOUNT-LE-TIME is compiled locally as an ENNReal/probability pull-count budget bound.")
    print("- EXP-WEIGHTED-PULLCOUNT-LE-TIME is compiled locally as an ENNReal/probability weighted pull-count budget bound.")
    print("- EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN is compiled locally as a Fin K / Finset.univ specialization.")
    print("- EXP-MODEL-GAP-OFREAL-BOUND is compiled locally as an ENNReal.ofReal surrogate model-gap bound.")
    print("- OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS is compiled locally as a scalar ENNReal.ofReal faithfulness leaf.")
    print("- OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS is compiled locally as a pointwise scalar/model pseudo-regret faithfulness bridge under explicit gap nonnegativity.")
    print("- EXP-OFREAL-PSEUDOREGRET-BOUND is compiled locally as an ENNReal.ofReal lower-integral pseudo-regret bound under explicit gap nonnegativity.")
    print("- EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG is compiled locally as a Rat-level gap nonnegativity contract adapter for that lower-integral bound.")
    print("- FINITE-BANDIT-GAP-BESTARM is compiled locally as the zero-gap invariant for FiniteBanditModel.bestArm.")
    print("- FINITE-BANDIT-BESTARM-DOMINATES is compiled locally as a best-arm dominance invariant for FiniteBanditModel.bestArm.")
    print("- FINITE-BANDIT-GAP-NONNEG is compiled locally as model-derived Rat gap nonnegativity.")
    print("- FINITE-BANDIT-MAXGAP, FINITE-BANDIT-GAP-LE-MAXGAP, and FINITE-BANDIT-MAXGAP-NONNEG are compiled locally as finite max-gap invariants.")
    print("- EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP is compiled locally as a no-explicit-hgap ENNReal.ofReal lower-integral pseudo-regret bound.")
    print("- REGRET-COUNT-BOUND is compiled locally as a deterministic count-bound-to-regret scaffold.")
    print("- REGRET-NAT-COUNT-BOUND is compiled locally as a deterministic Nat-count-to-regret adapter.")
    print("- REGRET-UNIFORM-NAT-COUNT-BOUND is compiled locally as a deterministic uniform Nat-count-to-regret adapter.")
    print("- ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT is compiled locally as the first deterministic ETC round-robin count scaffold.")
    print("- ETC-EXPLOREARM-EQ-IFF-MOD is compiled locally as a modular characterization of the ETC round-robin selector.")
    print("- ETC-ROUND-ROBIN-ADD-K-COUNT is compiled locally as the full-cycle extension recurrence for ETC pull counts.")
    print("- ETC-ROUND-ROBIN-MUL-K-COUNT is compiled locally as the m-full-cycle ETC pull-count theorem.")
    print("- ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT is compiled locally as the configured exploration-horizon ETC count adapter.")
    print("- ETC-EXPLORATION-REGRET-BOUND is compiled locally as the deterministic exploration-only ETC pseudo-regret scaffold.")
    print("- ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE is compiled locally as the fixed-commit ETC trace boundary on the exploration prefix.")
    print("- ETC-ACTION-WITH-COMMIT-COMMIT-PHASE is compiled locally as the fixed-commit ETC trace boundary after the exploration horizon.")
    print("- ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE is compiled locally as the best-arm specialization of the fixed-commit ETC commit phase.")
    print("- ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT is compiled locally as the exploration-prefix pull-count transfer from actionWithCommit to exploreArm.")
    print("- ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT is compiled locally as the configured exploration-horizon pull count for actionWithCommit.")
    print("- ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND is compiled locally as the deterministic actionWithCommit exploration-horizon pseudo-regret scaffold.")
    print("- ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT is compiled locally as the one-step post-commit pull-count recurrence for actionWithCommit.")
    print("- ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT is compiled locally as the closed-form post-exploration suffix pull-count theorem for actionWithCommit.")
    print("- ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT is compiled locally as the non-commit-arm post-exploration pull-count stability corollary for actionWithCommit.")
    print("- ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT is compiled locally as the commit-arm post-exploration pull-count corollary for actionWithCommit.")
    print("- ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT-BUDGET-REGRET is compiled locally as the reviewer-approved unsimplified post-exploration fixed-commit count-budget regret scaffold.")
    print("- ETC-ACTION-WITH-COMMIT-COARSE-SUFFIX-REGRET-BOUND is compiled locally as the reviewer-approved coarse uniform post-exploration fixed-commit suffix regret scaffold.")
    print("- ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET is compiled locally as the reviewer-approved fixed-commit post-horizon phase-split pseudo-regret equality.")
    print("- ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET is compiled locally as the reviewer-approved optimal-commit no-extra-suffix-regret equality.")
    print("- ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND is compiled locally as the reviewer-approved optimal-commit suffix regret bound.")
    print("- ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND is compiled locally as the reviewer-approved phase-split exploration-plus-suffix-gap regret bound.")
    print("- ETC-MEAS-COMMITARM-NE-BESTARM is compiled locally as the first wrong-commit event measurability canary.")
    print("- ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY is compiled locally as the oracle-selected wrong-commit event measurability wrapper.")
    print("- ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-BRIDGE is compiled locally as the Mathlib-backed countable score-vector oracle-choice measurability wrapper.")
    print("- ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE is compiled locally as the Mathlib Pi-space coordinate-to-vector empirical-mean measurability wrapper.")
    print("- ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES is compiled locally as the coordinatewise empirical-mean-to-oracle-choice measurability composition wrapper.")
    print("- ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES is compiled locally as the coordinatewise empirical-mean-to-oracle-wrong-event measurability composition wrapper.")
    print("- ETC-WRONG-COMMIT-SUBSET-WRONG-MEAN-EVENT is compiled locally as the pure wrong-commit set-inclusion event-reduction leaf.")
    print("- ETC-PROB-WRONG-COMMIT-LE-WRONG-MEAN-EVENTS-OF-SUBSET is compiled locally as the arbitrary-measure monotonicity wrapper for that event reduction.")
    print("- ETC-MEAS-EMPMEAN-GE-EMPMEAN is compiled locally as the pairwise empirical-mean comparison-event measurability canary.")
    print("- ETC-MEAS-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM is compiled locally as the finite existential wrong-mean event measurability wrapper.")
    print("- ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM is compiled locally as the finite-union probability upper-bound wrapper for wrong-mean events.")
    print("- ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS is compiled locally as the final elementary event-probability assembly wrapper.")
    print("- ETC-PROB-WRONG-COMMIT-LE-SUM-PAIRWISE-TAIL is compiled locally as the abstract non-best pairwise-tail consumer wrapper.")
    print("- ETC-PROB-WRONG-COMMIT-LE-SUM-NONBEST-PAIRWISE-TAIL is compiled locally as the if-zeroed non-best pairwise-tail consumer wrapper.")
    print("- ETC-PROB-WRONG-COMMIT-LE-FILTERED-SUM-PAIRWISE-TAIL is compiled locally as the filtered-sum pairwise-tail consumer wrapper.")
    print("- ETC-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS is compiled locally as the Nat denominator-positivity leaf for actionWithCommit exploration counts.")
    print("- ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS is compiled locally as the Rat denominator-positivity adapter for actionWithCommit exploration counts.")
    print("- ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-NE-ZERO is compiled locally as the Rat nonzero-denominator adapter for actionWithCommit exploration counts.")
    print("- ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION is compiled locally as the deterministic empirical-mean definition and denominator rewrite at the fixed-commit ETC exploration horizon.")
    print("- ETC-EMPMEAN-EXPLORATION-PREFIX-CONGRUENCE is compiled locally as the finite reward-prefix congruence bridge for ETC empirical means; it supports later history-derived commit-score reconstruction but does not prove generated-policy alignment or an adaptive reward law.")
    print("- ETC-EMPMEAN-FINITE-HISTORY-RECONSTRUCTION is compiled locally as the completed finite-reward-history bridge for a generated action at time t + 1 once the exploration horizon is contained in that history; finite-history policy construction, action equality, measurability, and adaptive reward laws remain open.")
    print("- ETC-GENERATED-HISTORY-POLICY-ACTION-ALIGNMENT is compiled locally as the measurable finite-history ETC policy and exact generated action-trace equality with the canonical explorationArgmaxAction under positive exploration pulls; adaptive reward-law transport and the LML theorem remain open.")
    print("- ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-PARTIALTRAJ-LAW is compiled locally as the canonical Markov-kernel trajMeasure full partialTraj law for that finite-history ETC policy; arbitrary-environment and fixed-product law identification remain open.")
    print("- ETC-GENERATED-HISTORY-POLICY-TRAJMEASURE-COND-MGF-MODEL-MEAN is compiled locally as the abstract model-mean conditional sub-Gaussian MGF foundation for the canonical ETC kernel trajectory; the bounded finite-arm route now constructs its centered-law and variance inputs, while source transport remains open.")
    print("- ETC-FINITE-ARM-LAWS-MARKOV-REWARD-KERNEL is compiled locally: action-indexed probability laws produce a context-independent MarkovRewardKernel with selectedMeasure equal to the original arm law; the common-bounded finite-arm centered-law specialization is also compiled.")
    print("- ETC-FINITE-ARM-BOUNDED-CENTERED-KERNEL-COND-MGF is compiled locally: common-bounded arm laws with exact model means construct the centered kernel law and canonical successor conditional MGF; the downstream full-sum tail now closes initial-law alignment and conditional summation.")
    print("- ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-PAIRWISE-TAIL-CONTRACT is compiled locally: direct per-arm centered HasSubgaussianMGF witnesses with one common proxy and exact Rat model means construct the canonical centered kernel law, initial/successor fixed-filtration witnesses, and pairwise empirical-mean tail contract without bounded support or an arm union. Its dependency-light, native Real source-law, least-encoded action, and history-score consumers now compile downstream; faithful local field compatibility now compiles; only actual cross-toolchain LML symbol import remains.")
    print("- ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-CANONICAL-PER-ARM-BOCHNER-REGRET is compiled locally: each concrete non-best commit fiber is bounded by its direct-MGF pairwise tail, converted to Real, and substituted termwise into the gap-weighted Bochner assembly. External/native Real exact, least-encoded action, and history-score consumers now compile downstream; faithful local field compatibility now compiles; only actual cross-toolchain LML symbol import remains.")
    print("- ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-PER-ARM-BOCHNER-REGRET is compiled locally: finite exploration-prefix equality and scheduled-arm condDistrib transport yield the direct-MGF per-arm bound on arbitrary external processes. Full-history/action-dependent, native Real source-law, least-encoded action, and history-score consumers now compile; faithful local field compatibility now compiles; only actual cross-toolchain LML symbol import remains.")
    print("- ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET is compiled locally: LML-shaped constant reward laws conditioned on action zero and on each complete finite action/reward history plus next action are marginalized/coarsened to the scheduled reward-prefix laws, preserving the direct-MGF gap-weighted per-arm RHS without bounded support or an arm union. Its action-dependent selected-kernel consumer now compiles downstream, closing dependency-light Rat law transport.")
    print("- ETC-FINITE-ARM-COMMON-SUBGAUSSIAN-EXTERNAL-ACTION-DEPENDENT-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET is compiled locally: raw action-indexed feedback kernels plus a.e. scheduled exploration actions are converted to constant full-history arm laws and consumed by the direct-MGF per-arm theorem. Downstream native Real exact source-law, least-encoded action, and history-score transport now compile; faithful local field compatibility now compiles; only actual cross-toolchain LML symbol import remains.")
    print("- ETC-FINITE-ARM-BOUNDED-CENTERED-FULL-SUM-TAIL is compiled locally: the canonical ETC trajectory has a one-sided Azuma-Hoeffding bound for the actual centered rewards at every time in Finset.range n, including time zero; the downstream pairwise wrong-commit route is now compiled.")
    print("- ETC-FINITE-ARM-BOUNDED-PAIRWISE-WRONG-COMMIT is compiled locally: common-bounded finite-arm laws with exact model means yield the canonical explorationArgmaxCommit pairwise empirical-mean tail contract and finite-union wrong-commit probability under trajMeasure; the downstream canonical Bochner and external prefix-law consumers are now compiled.")
    print("- ETC-FINITE-ARM-BOUNDED-CANONICAL-BOCHNER-REGRET is compiled locally: the generated finite-history ETC action has a named Real expected pseudo-regret bound under the canonical bounded-arm trajMeasure, using measurable commit/wrong-event, ENNReal-to-Real tail conversion, and finite-valued integrability; the downstream exploration-prefix law transport is now compiled.")
    print("- ETC-FINITE-ARM-BOUNDED-EXTERNAL-PREFIX-LAW-BOCHNER-REGRET is compiled locally: generated ETC pseudo-regret factors measurably through the m*K exploration rewards, so equality of the external and canonical exploration-prefix pushforwards transports the Bochner bound without full trajectory-law equality or suffix-law assumptions. The same factorization now transports the canonical per-arm endpoint downstream.")
    print("- ETC-FINITE-ARM-BOUNDED-EXTERNAL-PREFIX-LAW-PER-ARM-BOCHNER-REGRET is compiled locally: equal exploration-prefix pushforwards imply equal generated ETC regret integrals, and the canonical gap-weighted armwise tail budget therefore holds under the external law without full trajectory, suffix, or individual fiber transport. Its initial-marginal plus successor-condDistrib consumer now compiles downstream.")
    print("- ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-PER-ARM-BOCHNER-REGRET is compiled locally: coordinate-measurable external rewards with the canonical time-zero marginal and successor condDistrib laws through m*K-1 inherit the armwise gap-weighted tail bound. Its scheduled exploration-arm adapter now compiles downstream.")
    print("- ETC-FINITE-ARM-BOUNDED-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-PER-ARM-BOCHNER-REGRET is compiled locally: the initial scheduled arm law and stationary scheduled-arm condDistrib laws through m*K-1 imply the gap-weighted per-arm ETC Bochner bound, with Context fixed to Unit and no caller-visible local kernel or arm union. Its full action/reward-history constant-law adapter now compiles downstream.")
    print("- ETC-FINITE-ARM-BOUNDED-EXTERNAL-CONDDISTRIB-BOCHNER-REGRET is compiled locally: a generic finite-prefix uniqueness induction converts the zeroth reward marginal and condDistrib laws for reward i+1 given the prefix through i into the canonical trajMeasure prefix law; the ETC consumer needs these laws only before m*K-1 and transports the bounded Bochner regret integral back to the original sample space. The downstream exploration-arm law leaf now removes historyStepKernelFamily from the caller contract.")
    print("- ETC-FINITE-ARM-BOUNDED-EXTERNAL-EXPLORATION-ARM-CONDDISTRIB-BOCHNER-REGRET is compiled locally: during exploration the generated-history step kernel reduces exactly to armLaw (exploreArm spec (i+1)), so an arbitrary external process inherits the bounded Bochner regret theorem from the initial explore-arm law and the stationary scheduled-arm condDistrib laws through m*K-1. The downstream full action/reward-history leaf now supplies these reward-prefix laws from LML-shaped constant feedback laws.")
    print("- ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET is compiled locally: constant full-history feedback laws coarsen to reward-prefix laws and the initial marginal; the downstream action-dependent leaf now constructs those constants from selector a.e. equality.")
    print("- ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET is compiled locally: LML-shaped constant feedback laws conditioned on action zero and on each complete pair-history/next-action condition coarsen to the scheduled-arm reward-prefix contract and yield the gap-weighted per-arm ETC bound. Its action-dependent selected-kernel adapter now compiles downstream.")
    print("- ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-DEPENDENT-ACTION-REWARD-HISTORY-CONDDISTRIB-BOCHNER-REGRET is compiled locally: action zero and exploration next-action a.e. identities turn raw action-selected feedback kernels into constant scheduled-arm laws, then the full-history consumer yields the external bounded ETC max-gap theorem. Its per-arm counterpart now compiles downstream.")
    print("- ETC-FINITE-ARM-BOUNDED-EXTERNAL-ACTION-DEPENDENT-ACTION-REWARD-HISTORY-CONDDISTRIB-PER-ARM-BOCHNER-REGRET is compiled locally: the same raw action-selected feedback laws and a.e. scheduled exploration actions now yield the gap-weighted per-arm ETC bound with no arm union. This closes the dependency-light per-arm law transport; direct LML HasCondDistrib integration, Real/common-sub-Gaussian rewards, and measurableArgmax semantics remain separate.")
    print("- ETC-EMP-MEAN-COMPARISON-AS-FINITE-SUM is compiled locally as the positive-denominator bridge from fixed-commit ETC empirical-mean comparison to fixed-horizon reward-sum comparison.")
    print("- ETC-EMPMEAN-EVENT-SUBSET-SUMREWARDS-TAIL-EVENT is compiled locally as the event-shape adapter from fixed-commit ETC empirical-mean comparison to an abstract fixed-horizon sumRewards tail event.")
    print("- ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET is compiled locally as the concrete centered reward-difference Finset bridge from fixed-horizon sumRewards comparison to the ETC pairwise tail event.")
    print("- ETC-MEASURABLE-SUMREWARDS-ACTION-WITH-COMMIT-EXPLORATION is compiled locally as the numerator-measurability bridge for fixed-commit ETC empirical means under stochastic reward traces.")
    print("- ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION-OF-DIV-CONST is compiled locally as the full fixed-commit ETC empirical-mean measurability wrapper under an explicit Rat division-by-constant measurability contract.")
    print("- RAT-MEASURABLE-DIV-CONST-OF-MEASURABLE-SINGLETON is compiled locally as a Rat division-by-constant measurability wrapper under [MeasurableSingletonClass Rat].")
    print("- ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION is compiled locally as the no-hdiv_const fixed-commit ETC empirical-mean measurability theorem consuming the Rat wrapper.")
    print("- ETC-MEASURABLE-EMPMEAN-AT-EXPLORATION-COORDINATES is compiled locally as the coordinate-shaped fixed-commit ETC empirical-mean measurability wrapper.")
    print("- ETC-COMMIT-ORACLE-ARGMAX-CONSUMER is compiled locally as the deterministic abstract commit-oracle argmax consumer for the wrong-commit event reduction.")
    print("- ETC-COMMIT-ORACLE-CONCRETE-ARGMAX is compiled locally as the finite Rat argmax-backed commit oracle, maximality certificate, and concrete wrong-event set-inclusion wrapper.")
    print("- ETC-COMMIT-ORACLE-PROB-WRAPPER is compiled locally as the oracle-specialized abstract pairwise-tail probability consumer.")
    print("- ETC-COMMIT-ORACLE-FILTERED-SUM-PAIRWISE-TAIL is compiled locally as the oracle-specialized filtered-sum pairwise-tail probability consumer.")
    print("- ETC-COMMIT-ORACLE-NONBEST-PAIRWISE-TAIL is compiled locally as the oracle-specialized if-zeroed nonbest pairwise-tail probability consumer.")
    print("- ETC-COMMIT-ORACLE-CONCRETE-FILTERED-SUM-PAIRWISE-TAIL is compiled locally as the concrete argmax-oracle filtered-sum pairwise-tail consumer wrapper.")
    print("- ETC-PAIRWISE-TAIL-CONTRACT-SURFACE is compiled locally as the abstract fixed-commit ETC empirical-mean pairwise-tail contract and consumer wrapper.")
    print("- UCB-CONFIDENCE-ALGEBRA is compiled locally as the deterministic good-event/index-maximality consumer: best-arm upper confidence, chosen-arm lower confidence, and UCB score maximality imply `gap <= 2 * chosenRadius`, with a strict-gap contradiction wrapper; log/sqrt radius formulas, tail producers, expected pull-count bounds, and final UCB regret remain separate.")
    print("- UCB-CONFIDENCE-EVENT-CONSUMER is compiled locally as the finite-arm good-event complement consumer: outside the union of upper/lower confidence failures, score maximality implies `gap <= 2 * chosenRadius`; event measurability is provided by a separate local wrapper, while tail bounds, log/sqrt radius formulas, pull-count bounds, and final UCB regret remain separate.")
    print("- UCB-CONFIDENCE-EVENT-UNION-BOUND is compiled locally as the finite-arm outer-measure union-bound consumer for upper/lower confidence failures; event measurability is provided by a separate local wrapper, while concrete concentration tails, log/sqrt radius formulas, pull-count bounds, and final UCB regret remain separate.")
    print("- UCB-CONFIDENCE-EVENT-MEASURABILITY is compiled locally as the measurable-set wrapper for upper/lower confidence failures and the finite-arm bad event under per-arm empirical-mean measurability; concrete empirical-mean measurability, tail bounds, log/sqrt radius formulas, pull-count bounds, and final UCB regret remain separate.")
    print("- UCB-FINITE-HORIZON-CONFIDENCE-EVENT is compiled locally as the time-indexed confidence-bad-event bridge and finite-horizon union-bound assembler over t < T, arms, and upper/lower failures; concrete empirical-mean construction, concentration tails, log/sqrt radius formulas, pull-count bounds, and final UCB regret remain separate.")
    print("- UCB-FINITE-HORIZON-GOOD-EVENT-CONSUMER is compiled locally as the finite-horizon good-event bridge: outside the finite-horizon confidence bad event, every `t < T` single-time bad event is absent, score maximality yields `gap <= 2 * radius t chosen`, and the score-max event for a large-gap arm is included in the finite-horizon bad event; selected-arm trace, pull-count bounds, and final UCB regret remain separate.")
    print("- UCB-FINITE-HORIZON-CONFIDENCE-TAIL-CONSUMER is compiled locally as the finite-horizon confidence-bad-event tail-budget consumer over t < T, arms, and upper/lower failure tails; concrete empirical-mean construction, concentration tail production, log/sqrt radius formulas, pull-count bounds, and final UCB regret remain separate.")
    print("- UCB-ABS-DEVIATION-TAIL-ADAPTER is compiled locally as the adapter from upper/lower confidence failures to absolute empirical-mean deviation events and a finite-horizon shared absolute-deviation tail budget; concrete empirical-mean construction, concentration tail production, log/sqrt radius formulas, pull-count bounds, and final UCB regret remain separate.")
    print("- UCB-CHEBYSHEV-ABS-DEVIATION-TAIL is compiled locally as a finite-variance Chebyshev producer for UCB absolute-deviation tails and finite-horizon confidence bad-event budgets; empirical-mean construction, variance-rate simplification, sub-Gaussian/log-sqrt radius formulas, pull-count bounds, and final UCB regret remain separate.")
    print("- UCB-SUBGAUSSIAN-ABS-DEVIATION-TAIL is compiled locally as an abstract centered empirical-mean sub-Gaussian producer for two-sided UCB absolute-deviation tails and finite-horizon confidence bad-event budgets; empirical-mean construction, proxy/radius simplification to textbook log/sqrt form, pull-count bounds, and final UCB regret remain separate.")
    print("- UCB-SUBGAUSSIAN-ONE-SIDED-TAIL is compiled locally as a sharper centered empirical-mean sub-Gaussian producer for one-sided upper/lower UCB confidence failures and finite-horizon confidence bad-event budgets; empirical-mean construction, proxy/radius simplification to textbook log/sqrt form, pull-count bounds, and final UCB regret remain separate.")
    print("- UCB-SUBGAUSSIAN-RADIUS-BUDGET is compiled locally as the one-sided radius-budget simplification: `0 < proxy` and `2 * proxy * budget <= radius^2` yield upper/lower and finite-horizon confidence bad-event bounds with `exp(-budget)` tails; empirical-mean construction, concrete sqrt/log radius instantiation, pull-count bounds, and final UCB regret remain separate.")
    print("- UCB-SUBGAUSSIAN-SQRT-BUDGET-RADIUS is compiled locally as the concrete square-root budget radius leaf: `sqrt (2 * proxy * budget)` is nonnegative, satisfies the radius-square domination contract, and yields upper/lower and finite-horizon confidence bad-event bounds with `exp(-budget)` tails; the logarithmic schedule and textbook delta-scale surfaces are compiled separately, while empirical-mean construction, pull-count bounds, and final UCB regret remain separate.")
    print("- UCB-SUBGAUSSIAN-LOG-BUDGET-RADIUS is compiled locally as the schedule-agnostic logarithmic budget radius leaf: `sqrt (2 * proxy * log scale)` is nonnegative, satisfies the radius-square domination contract, and yields upper/lower and finite-horizon confidence bad-event bounds with `scale^-1` tails under `0 < scale`; constant-scale double-sum folding is compiled separately as UCB-SUBGAUSSIAN-CONSTANT-LOG-BUDGET-RADIUS, while textbook scale choices, empirical-mean construction, pull-count bounds, and final UCB regret remain separate.")
    print("- UCB-SUBGAUSSIAN-CONSTANT-LOG-BUDGET-RADIUS is compiled locally as the constant-scale logarithmic budget radius leaf: `sqrt (2 * proxy * log scale)` yields finite-horizon confidence bad-event bounds with the inverse-scale double sum folded into `T` and `Fintype.card Arm` nsmul; textbook finite-horizon delta scale is compiled separately as UCB-SUBGAUSSIAN-TEXTBOOK-DELTA-RADIUS, while empirical-mean construction, pull-count bounds, and final UCB regret remain separate.")
    print("- UCB-SUBGAUSSIAN-TEXTBOOK-DELTA-RADIUS is compiled locally as the textbook finite-horizon delta-scale leaf: `scale = 2 * T * |Arm| / delta` is positive under `0 < T`, nonempty finite arms, and `0 < delta`, the folded two-sided inverse-scale tail budget is bounded by `ENNReal.ofReal delta`, the finite-horizon confidence bad event is bounded by `delta`, and large-gap score-max events inherit that same delta budget under centered empirical-mean sub-Gaussian hypotheses; empirical-mean construction, pull-count bounds, and final UCB regret remain separate.")
    print("- UCB-SELECTED-LARGE-GAP-DELTA is compiled locally as the selected-action bridge: a selected action with a score-maximality certificate is contained in the score-max event, and finite-time-set large-gap selected-arm events are covered by the same finite-horizon bad event, so they inherit the textbook `delta` budget; concrete UCB argmax/tie-breaking policy, empirical-mean construction, pull-count summation, and final regret remain separate.")
    print("- UCB-CONCRETE-SCORE-ARGMAX-ACTION is compiled locally as a concrete finite-arm Real score argmax action for UCB confidence scores; it discharges selected-action score maximality and specializes the single-time and finite-time-set large-gap textbook `delta` bounds without an external score certificate; empirical-mean construction, recursive history action trace, pull-count summation, and final regret remain separate.")
    print("- UCB-CONCRETE-SCORE-ARGMAX-COUNT-BUDGET is compiled locally as the earlier deterministic-proxy count-facing bridge through selected-event sums, lower integrals, threshold splits, and B + T * delta consumers. The native random-width route now has separate history-index and fixed-count-peeling leaves; it still needs an actual generated-process arm-stream source/law, one-sided tails, expected pulls, and final regret rather than pretending the deterministic proxy is the realized pull-count width.")
    print("- UCB-NATIVE-REAL-HISTORY-INDEX is compiled locally: real empirical means are sumRewards/pullCount, the confidence width is the realized path-dependent sqrt(2*c*log(n+1)/pullCount), inclusive finite-pair-history scores and least-encoded actions agree exactly with trace scores at n+1, and the selector is measurable and score-maximal. Fixed-count peeling now compiles separately; source instantiation, one-sided tails, expected pull counts, and final UCB regret remain downstream.")
    print("- UCB-FIXED-COUNT-PEELING-LAW is compiled locally: FixedArmPrefixSource records the pathwise selected-reward-prefix identity, the adaptive (pullCount,sumRewards) event is peeled over k <= n by the finite outer-measure union bound, and one complete-stream IdentDistrib law transports every fixed-count event to a canonical stream. The precise next blocker is constructing this source and canonical stationary/product stream law for the actual generated UCB sequence (or proving an equivalent conditional-MGF substitute), before one-sided index tails, expected pulls, and final regret.")
    print("- TAIL-UNION-FINITE is compiled locally as generic finite-union outer-measure wrappers for explicit Finset and Fintype event families.")
    print("- TAIL-SUMMABILITY-UCB is compiled locally as an abstract finite-horizon UCB bad-event summability wrapper over finite arms and t < T; the native Real empirical mean/random width/index and generic fixed-count peeling/law transport now compile, while actual generated-process arm-stream source instantiation, source-faithful one-sided tails, expected pull-count bounds, and final regret remain separate.")
    print("- EXP3-POTENTIAL is compiled locally as a deterministic finite-action exponential-weights potential surface with updated-potential unfolding, nonnegativity, one-step increment algebra, and finite-horizon telescope; estimator/log/regret leaves remain separate.")
    print("- FTRL-ONE-STEP is compiled locally as a deterministic finite-action regularized-objective minimizer wrapper yielding the one-step linear-loss inequality under eta > 0; convexity, minimizer existence, Tsallis regularizer, stability/penalty, and regret remain separate.")
    print("- TSALLIS-REGULARIZER is compiled locally as a finite-simplex Real.rpow power-sum/entropy/negative-entropy regularizer surface with denominator and nonnegative-power-sum well-definedness facts; convexity, stability/penalty, self-bounding, learning-rate, and regret remain separate.")
    print("- OFUL-GRAM-PSD is compiled locally as a finite-dimensional Gram quadratic-form wrapper: rank-one forms are squared projections and finite-history forms are sums of squared projections; determinant growth, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-RANKONE-DET-UPDATE is compiled locally as a Mathlib Schur-complement wrapper for rank-one feature determinant updates; regularized Gram invertibility, log-det telescoping, determinant-growth inequalities, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-REGULARIZED-GRAM-BASE is compiled locally as the scalar regularization base for OFUL Gram recursions: `det (lambda I) = lambda^d`, nonzero determinant/IsUnit, named regularized Gram, and the first scalar-base rank-one determinant update; arbitrary regularized Gram invertibility, log-det telescoping, determinant-growth inequalities, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-REGULARIZED-GRAM-QFORM is compiled locally as the regularized-Gram quadratic-form expansion and PSD wrapper: scalar term plus finite-history squared projections under `0 <= lambda`; strict positive definiteness, determinant positivity, arbitrary regularized Gram invertibility, log-det telescoping, determinant-growth inequalities, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-REGULARIZED-GRAM-POS-QFORM is compiled locally as the strict-positive regularized-Gram quadratic-form wrapper under `0 < lambda` and nonzero vector input; determinant positivity, arbitrary regularized Gram invertibility, log-det telescoping, determinant-growth inequalities, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-REGULARIZED-GRAM-DET-POS is compiled locally as the Mathlib PosDef/determinant bridge for arbitrary finite-history regularized Grams under `0 < lambda`: Hermitian wrappers, PosDef, positive/nonzero determinant, and `IsUnit det`; log-det telescoping, determinant-growth inequalities, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-REGULARIZED-GRAM-DET-UPDATE is compiled locally as the arbitrary finite-history regularized-Gram rank-one determinant recursion with the `IsUnit det` side condition discharged from positive regularization; log-det telescoping, determinant-growth inequalities, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-LOG-DET-UPDATE is compiled locally as the logarithmic one-step determinant-update wrapper: rank-one PSD, updated determinant positivity, positive update factor, and `log det(V + x x^T) - log det(V) = log(1 + x^T V^{-1} x)`; finite-horizon log-det telescoping, determinant-growth inequalities, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-LOG-DET-TELESCOPE is compiled locally as an abstract finite-horizon log-det telescope over one-step log-update factors; concrete Nat-prefix instantiation is tracked separately, and determinant-growth inequalities, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-PREFIX-LOG-DET-TELESCOPE is compiled locally as a concrete Nat-prefix growing-history regularized-Gram sequence with successor rank-one updates, determinant/log-det recursions, and a finite-horizon log-det telescope; determinant-growth inequalities, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-PREFIX-LOG-DET-BASE is compiled locally as the scalar-base endpoint wrapper for the concrete Nat-prefix log-det telescope: `V_0 = lambda I`, `det V_0 = lambda^d`, and the telescope endpoint rewrites to `log det(V_T) - log(lambda^d)`; determinant-growth inequalities, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-DETERMINANT-GROWTH-CONSUMER is compiled locally as the first min/log determinant-growth consumer: `sum_t min(1,u_t) <= 2 * (log det(V_T) - log(lambda^d))` for Nat-prefix update scalars under explicit `0 <= u_t`; determinant upper bounds, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-CLIPPED-SUM-LOG-UPPER is compiled locally as the clipped finite-sum log-upper handoff: under explicit `0 <= u_t` and `sum_t log(1+u_t) <= B`, the clipped update sum is bounded by `2 * B`; determinant telescope, PosDef discharge, determinant upper bounds, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-UNCLIPPED-SMALL-UPDATE-SUM-LOG is compiled locally as the finite-sum small-update log bridge: under explicit `0 <= u_t` and `u_t <= 1`, the raw update sum is bounded by `2 * sum_t log(1+u_t)`; determinant telescope, PosDef discharge, determinant upper bounds, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-UNCLIPPED-SMALL-UPDATE-SUM-LOG-UPPER is compiled locally as the finite-sum small-update log-upper handoff: under explicit `0 <= u_t`, `u_t <= 1`, and `sum_t log(1+u_t) <= B`, the raw update sum is bounded by `2 * B`; determinant telescope, PosDef discharge, determinant upper bounds, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-UNCLIPPED-SMALL-UPDATE-LOG-DET-EXPLICIT-NONNEG is compiled locally as the explicit-regularity small-update log-det endpoint handoff: under explicit `0 <= u_t` and `u_t <= 1`, the raw inverse-quadratic update sum is bounded by `2 * (log det(V_T)-log(lambda^d))`; PosDef discharge, determinant upper bounds, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-INVERSE-QUADRATIC-NONNEG-CONSUMER is compiled locally as the PosDef-inverse consumer that proves `0 <= x_t^T V_t^{-1} x_t` for regularized Nat-prefix Grams and removes the explicit nonnegativity contract from the min/log determinant-growth bound; determinant upper bounds, dimension/radius simplifications, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-UNCLIPPED-SMALL-UPDATE-LOG-DET-SUB-BASE is compiled locally as the small-update log-det endpoint handoff: under `u_t <= 1`, the raw inverse-quadratic update sum is bounded by `2 * (log det(V_T)-log(lambda^d))`; determinant upper bounds, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-LOG-DET-UPPER-CONSUMER is compiled locally as the terminal upper-bound handoff: any future proof of `log det(V_T)-log(lambda^d) <= B` immediately yields the clipped elliptical-potential bound `sum_t min(1,u_t) <= 2 * B`; concrete determinant upper bounds, dimension/radius simplifications, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-UNCLIPPED-SMALL-UPDATE-LOG-DET-UPPER is compiled locally as the small-update terminal upper-bound handoff: any future proof of `log det(V_T)-log(lambda^d) <= B` plus `u_t <= 1` yields the raw inverse-quadratic update-sum bound `sum_t u_t <= 2 * B`; determinant upper bounds, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-DET-MUL-EXP-UPPER-CONSUMER is compiled locally as the multiplicative determinant-upper handoff: any future proof of `det(V_T) <= lambda^d * exp(B)` yields both `log det(V_T)-log(lambda^d) <= B` and `sum_t min(1,u_t) <= 2 * B`; concrete trace/AM-GM determinant bounds, dimension/radius simplifications, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-UNCLIPPED-SMALL-UPDATE-DET-MUL-EXP-UPPER is compiled locally as the small-update multiplicative determinant-upper handoff: any future proof of `det(V_T) <= lambda^d * exp(B)` plus `u_t <= 1` yields the raw inverse-quadratic update-sum bound `sum_t u_t <= 2 * B`; concrete determinant bounds, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-PREFIX-TRACE-BOUND is compiled locally as the trace/radius input for determinant upper bounds: `trace(V_T) = d * lambda + sum_t ||x_t||^2` and `trace(V_T) <= d * lambda + T * L2` under a pointwise squared-norm ceiling; AM-GM determinant upper bounds, self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-TRACE-AVERAGE-DET-CONSUMER is compiled locally as the trace-average determinant handoff: a future AM-GM proof of `det(V_T) <= (trace(V_T)/d)^d` plus the local trace/radius bound yields `det(V_T) <= ((d*lambda + T*L2)/d)^d`; AM-GM and scalar-exp simplification are handled by later local leaves, while self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-AMGM-DET-TRACE-BOUND is compiled locally as the Mathlib-backed AM-GM/eigenvalue determinant trace bound: nonempty-feature regularized prefix Grams satisfy `det(V_T) <= (trace(V_T)/d)^d`, hence `det(V_T) <= ((d*lambda + T*L2)/d)^d` under a pointwise squared-norm ceiling; scalar-exp simplification is handled by a later local leaf, while self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-TRACE-AVERAGE-EXP-CONSUMER is compiled locally as the final multiplicative handoff consumer: any scalar proof of `((d*lambda + T*L2)/d)^d <= lambda^d * exp(B)` now yields `det(V_T) <= lambda^d * exp(B)` and the clipped elliptical-potential bound `sum_t min(1,u_t) <= 2 * B`; concrete scalar-exp simplification is tracked by OFUL-SCALAR-TRACE-AVERAGE-EXP-BOUND, while self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-SCALAR-TRACE-AVERAGE-EXP-BOUND is compiled locally as the scalar exponential simplification plus concrete determinant/clipped-sum consumers: under `0 < lambda`, `0 <= L2`, and a pointwise squared-norm ceiling, the AM-GM trace-average route yields `det(V_T) <= lambda^d * exp(d * (T*L2/(d*lambda)))` and `sum_t min(1,u_t) <= 2 * (d * (T*L2/(d*lambda)))`; dimension cancellation is handled by OFUL-SCALAR-TRACE-AVERAGE-EXP-CANCEL, while self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-SCALAR-TRACE-AVERAGE-EXP-CANCEL is compiled locally as the dimension-cancelled scalar exponential consumer: `d * (T*L2/(d*lambda)) = T*L2/lambda`, so the AM-GM trace-average route now yields `det(V_T) <= lambda^d * exp(T*L2/lambda)` and `sum_t min(1,u_t) <= 2 * (T*L2/lambda)`; self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-SCALAR-TRACE-AVERAGE-EXP-LOG is compiled locally as the standard logarithmic scalar endpoint: the AM-GM trace-average route now yields `det(V_T) <= lambda^d * exp(d * log(1 + T*L2/(d*lambda)))` and `sum_t min(1,u_t) <= 2 * d * log(1 + T*L2/(d*lambda))`; self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-UNCLIPPED-SMALL-UPDATE-GENERIC is compiled locally as the generic small-update elliptical-potential consumer: under `u_t <= 1`, any trace-average scalar certificate with exponent `B` yields the raw inverse-quadratic update-sum bound `<= 2 * B`; self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-UNCLIPPED-SMALL-UPDATE-DIM-SCALED is compiled locally as the dimension-scaled small-update elliptical-potential consumer: under `u_t <= 1`, the raw inverse-quadratic update sum is bounded by `2 * (d * (T*L2/(d*lambda)))`; self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-UNCLIPPED-SMALL-UPDATE-LINEAR is compiled locally as the dimension-cancelled small-update elliptical-potential consumer: under `u_t <= 1`, the raw inverse-quadratic update sum is bounded by `2 * (T*L2/lambda)`; self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- OFUL-UNCLIPPED-SMALL-UPDATE-LOG is compiled locally as the small-update logarithmic elliptical-potential consumer: under `u_t <= 1`, the raw inverse-quadratic update sum inherits the standard clipped logarithmic trace-average bound; self-normalized tails, confidence ellipsoids, and final OFUL regret remain separate.")
    print("- TAIL-HOEFFDING-BOUNDED is compiled locally as the generic bounded-centered Hoeffding MGF wrapper with an interval variance proxy.")
    print("- TAIL-SUBGAUSS-SUM is compiled locally as the Mathlib-backed independent sub-Gaussian finite-sum tail wrapper.")
    print("- TAIL-SUBGAUSS-DIFF-SUM-IMPORT is compiled locally as the ENNReal-valued independent sub-Gaussian finite-sum tail boundary wrapper.")
    print("- TAIL-COND-SUBGAUSS is compiled locally as the Mathlib-backed strongly adapted conditional sub-Gaussian finite-prefix tail wrapper plus ENNReal boundary adapter.")
    print("- TAIL-VARIANCE-ROBUST is compiled locally as Mathlib-backed Chebyshev/evariance tail wrappers plus a pairwise-independent finite-sum variance wrapper; robust mean estimators remain out of scope.")
    print("- ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS is compiled locally as the producer surface from abstract sub-Gaussian finite-sum witnesses to PairwiseEmpMeanTailContract.")
    print("- ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF is compiled locally as the producer specialization for concrete centered reward-difference summands; independence and sub-Gaussian witnesses remain explicit.")
    print("- ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT is compiled locally as the exact witness package consumed by the centered-diff producer.")
    print("- ETC-CENTERED-DIFF-COND-SUBGAUSSIAN-WITNESS-CONTRACT is compiled locally as the conditional witness package consumed by the centered-diff conditional route; fixed actionWithCommit bounded/source assembly is compiled, while full policy predictability remains open.")
    print("- ETC-CENTERED-DIFF-STRONGLY-ADAPTED-HISTORY is compiled locally as the shifted generated-history StronglyAdapted field for fixed-commit ETC centered reward differences; conditional MGF witness assembly is handled by separate source leaves.")
    print("- ETC-CENTERED-DIFF-COND-MGF-ZERO-MISS is compiled locally as a zero-summand conditional MGF source for times where actionWithCommit pulls neither the comparison arm nor the best arm; sampled-arm witnesses are handled separately.")
    print("- ETC-CENTERED-DIFF-COND-MGF-SAMPLED-TRANSFER is compiled locally as the deterministic transfer from sampled centered-reward conditional MGF witnesses to centered pairwise differences; the independence-based centered-reward MGF source supplies the fixed-action bridge from unconditional witnesses.")
    print("- ETC-CENTERED-REWARD-COND-SUBGAUSSIAN-WITNESS-CONTRACT is compiled locally as the reward-level conditional MGF source contract and constructor for CenteredDiffCondSubGaussianWitnesses.")
    print("- ETC-CENTERED-REWARD-COND-MGF-INDEP-SOURCE is compiled locally as the Mathlib condExpKernel/of_rat wrapper plus fixed-action History.historyFiltrationSucc specialization turning unconditional centered-reward sub-Gaussianity and reward-coordinate independence into conditional MGF witnesses.")
    print("- ETC-CENTERED-REWARD-COND-MEAN-ZERO-INDEP-SOURCE is compiled locally as the Mathlib condExp_indep_eq wrapper, History.historyFiltrationSucc specialization, succ-indexed conditional mean-zero shape, and iIndepFun-plus-full-history conditional mean-zero wrapper for centered rewards.")
    print("- ETC-CENTERED-REWARD-COND-MEAN-ZERO-BOUNDED-SOURCE is compiled locally as the BoundedRewardTraceSource wrapper that supplies the fixed actionWithCommit succ-indexed conditional mean-zero witness.")
    print("- MART-DIFF-REWARD is compiled locally as centered-reward martingale-difference contracts, builders from adapted/integrable/conditional-mean-zero hypotheses, a Mathlib partial-sum Martingale wrapper, and a fixed actionWithCommit bounded-source centered-reward instance.")
    print("- STOPPING-TIME-BUDGET is compiled locally as the Mathlib hittingAfter wrapper showing an adapted Nat-valued accumulated-resource process has a budget-exhaustion stopping time.")
    print("- ETC-CENTERED-REWARD-PAST-IINDEP-SOURCE is compiled locally as the reward-coordinate iIndepFun to reward-only past sigma-algebra independence bridge, with an infinitePi specialization.")
    print("- ETC-CENTERED-REWARD-HISTORY-IINDEP-SOURCE is compiled locally as the deterministic action-history inclusion plus full History.historyFiltrationSucc independence bridge, with an infinitePi specialization.")
    print("- INT-REWARD-BOUNDED / ETC-CENTERED-REWARD-BOUNDED-INTEGRABLE-SOURCE is compiled locally as the Mathlib Integrable.of_mem_Icc wrapper from a.e. bounded rewards to raw reward integrability.")
    print("- ETC-CENTERED-REWARD-ZERO-INTEGRAL-SOURCE is compiled locally as the exact-mean plus integrability source for centeredReward integral zero, with bounded-Icc and BoundedRewardTraceSource action-matched wrappers.")
    print("- ETC-CENTERED-REWARD-COND-WITNESS-BOUNDED-SOURCE is compiled locally as the BoundedRewardTraceSource assembly of the fixed actionWithCommit CenteredRewardCondSubGaussianWitnesses package plus pairwise-tail-contract and argmax-probability consumers.")
    print("- ETC-CENTERED-REWARD-COND-CANONICAL-TAIL-BOUNDED-SOURCE is compiled locally as the canonical-tail no-htail version of the fixed actionWithCommit bounded-source conditional route.")
    print("- ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL is compiled locally as the canonical exponential tail helper, removing the separate tail-domination hypothesis for the independent sub-Gaussian route.")
    print("- ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND is compiled locally as the concrete argmax-oracle wrong-commit probability bound using the canonical centered-diff tail; reward-law witnesses remain explicit.")
    print("- ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS is compiled locally as the deterministic transfer from reward-trace time-coordinate iIndepFun to centered pairwise reward-difference iIndepFun.")
    print("- ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS is compiled locally as the deterministic transfer from per-time centered reward sub-Gaussian witnesses to centered pairwise reward-difference sub-Gaussian witnesses.")
    print("- ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSSIAN-BOUND is compiled locally as the concrete argmax-oracle wrong-commit bound under trace-level reward-coordinate independence and centered reward sub-Gaussian witnesses.")
    print("- ETC-CENTERED-REWARD-BOUNDED-SUBGAUSSIAN-SOURCE is compiled locally as the ETC-shaped consumer of the generic bounded-centered Hoeffding MGF wrapper.")
    print("- ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSSIAN-BOUND is compiled locally as the strong all-arm concrete argmax-oracle wrong-commit bound under trace-level reward-coordinate independence, bounded rewards, and exact mean identities.")
    print("- ETC-WRONG-COMMIT-ACTION-MATCHED-REWARD-SUBGAUSSIAN-BOUND is compiled locally as the action-matched centered reward sub-Gaussian wrong-commit bound.")
    print("- ETC-WRONG-COMMIT-ACTION-MATCHED-BOUNDED-REWARD-BOUND is compiled locally as the practical fixed-commit bounded reward wrong-commit bound with means/bounds keyed to the arm actually pulled at each time.")
    print("- ETC-BOUNDED-REWARD-TRACE-SOURCE-CONTRACT is compiled locally as the action-matched source-contract package and consumer wrapper for trace-level reward-coordinate independence, a.e. bounds, and exact mean identities.")
    print("- ETC-BOUNDED-REWARD-INFINITEPI-SOURCE and ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE are compiled locally as the concrete fixed-commit product-coordinate reward source and wrong-commit bound.")
    print("- ETC-WRONG-COMMIT-INFINITEPI-REAL-PROBABILITY-BOUND is compiled locally as the fixed-product argmax/infinitePi Measure.real wrong-commit probability bridge from the ENNReal tail budget.")
    print("- ETC-CENTERED-REWARD-COND-CANONICAL-TAIL-INFINITEPI-SOURCE is compiled locally as the infinitePi specialization of the fixed actionWithCommit bounded-source conditional canonical-tail route.")
    print("- ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE is compiled locally as the deterministic bridge from an Omega-indexed commit selector to exploration budget plus wrong-commit suffix penalty.")
    print("- ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY is compiled locally as the ENNReal.ofReal lower-integral bridge using an abstract wrong-commit probability bound.")
    print("- ETC-WRONG-COMMIT-BOCHNER-REGRET-ASSEMBLY is compiled locally as the Bochner/Real expected-regret bridge using an abstract Real wrong-commit probability bound and an explicit integrability contract.")
    print("- ETC-ACTIONWITHCOMMIT-PSEUDOREGRET-INTEGRABILITY is compiled locally as the finite-valued measurable commit selector integrability helper for Bochner expected-regret wrappers.")
    print("- ETC-PER-ARM-COMMIT-PROB-BOCHNER-ASSEMBLY is compiled locally as the measurable finite-commit Bochner assembly with suffix RHS sum_a r * gap(a) * P(commit=a); the canonical armwise Real substitution now compiles downstream, while external per-arm transport and the exact Real/common-sub-Gaussian LML endpoint remain separate.")
    print("- ETC-FINITE-ARM-BOUNDED-COMMIT-ARM-PAIRWISE-TAIL is compiled locally: for every non-best arm a, the canonical generated-history probability of explorationArgmaxCommit=a is bounded by that arm's one-sided centered pairwise ENNReal tail without a finite union; its Real conversion is compiled downstream.")
    print("- ETC-FINITE-ARM-BOUNDED-CANONICAL-PER-ARM-BOCHNER-REGRET is compiled locally: finite armwise ENNReal tails are converted to Real and substituted termwise into the generic Bochner assembly, with the best-arm term vanishing by gap_bestArm. Its exploration-prefix external-law transport now compiles downstream.")
    print("- ETC-WRONG-COMMIT-INFINITEPI-BOCHNER-REGRET-ASSEMBLY is compiled locally as the concrete fixed-product argmax/infinitePi Bochner expected-regret assembly with a named Real bad-gap RHS and polished fixedProductArgmaxAction wrapper.")
    print("- ETC-WRONG-COMMIT-INFINITEPI-BOCHNER-SUMGAP-ADAPTER is compiled locally as the fixed-product argmax/infinitePi Bochner conservative sum-gap specialization with a named Real sum-gap RHS.")
    print("- ETC-WRONG-COMMIT-INFINITEPI-BOCHNER-MAXGAP-ADAPTER is compiled locally as the fixed-product argmax/infinitePi Bochner max-gap specialization with a named Real max-gap RHS.")
    print("- ETC-CANONICAL-EXPLORATION-INFINITEPI-BOCHNER-REGRET is compiled locally as the canonical fixed-product Real ETC expected-regret endpoint: its public coordinate law contracts are indexed directly by round-robin ETC.exploreArm, while model.bestArm is only an internal seed for the existing fixed-product wrapper. It is not the adaptive or LML final ETC theorem.")
    print("- ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY is compiled locally as the concrete argmax/infinitePi ENNReal.ofReal lower-integral regret assembly.")
    print("- ETC-FIXED-PRODUCT-BADGAP-LINTEGRAL-REGRET-WRAPPER is compiled locally as the polished fixed product-coordinate bad-gap lower-integral ETC wrapper with a named ENNReal RHS.")
    print("- ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY is compiled locally as the conservative sum-gap suffix adapter for that concrete lower-integral assembly.")
    print("- ETC-FIXED-PRODUCT-SUMGAP-LINTEGRAL-REGRET-WRAPPER is compiled locally as the polished fixed product-coordinate conservative sum-gap lower-integral ETC wrapper with a named ENNReal RHS.")
    print("- ETC-WRONG-COMMIT-INFINITEPI-MAXGAP-LINTEGRAL-REGRET-ASSEMBLY is compiled locally as the sharper max-gap suffix adapter for that concrete lower-integral assembly.")
    print("- ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER is compiled locally as the polished fixed product-coordinate max-gap lower-integral ETC wrapper.")
    print("- COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT is compiled locally as the narrower source contract that packages only the actual next-action reward-coordinate conditional map law, now also builds that source from full finite-pair partialTraj, frozen-prefix extension-map partialTraj, or canonical history-step next-pair law hypotheses, then reuses the existing generated-action actual reward-map route for finite-pair-trace partialTraj law and conditional mean-zero; it still assumes the reward-coordinate or ambient trajectory-to-condExpKernel/partialTraj/history-step law.")
    print("- COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW is compiled locally as the actual reward-coordinate source-level canonical pair-law consumer: GeneratedActionActualRewardMapSource now directly yields the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law over History.finitePairHistoryOfTrace; it still assumes the actual reward-coordinate law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE is compiled locally as a source-conversion leaf: GeneratedActionActualRewardMapSource plus state measurability now upgrades to GeneratedActionRandomPairMapSource through the ambient split-product condExpKernel law; it still assumes the actual reward-coordinate law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT is compiled locally as the definitional generated-action variant of the actual reward-map source: it removes explicit action-trace/haction inputs by using generatedActionFromRewardHistory and measurable reward-history state extractors, can package a policy-selected reward-coordinate law, full finite-pair partialTraj law, frozen-prefix extension-map partialTraj law, or canonical history-step next-pair law into the actual generated-successor reward-map source, reuses the actual reward-map consumers, and now directly consumes the source plus raw/mean range regularity into succ-indexed conditional mean-zero without a separate integrability hypothesis; it still assumes the reward-coordinate or ambient trajectory-to-condExpKernel/partialTraj/history-step law.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-MEAN-ZERO is compiled locally as the standalone integrability-based source-level conditional mean-zero consumer: a packaged GeneratedActionDefinitionalActualRewardMapSource plus centered reward-kernel law and explicit centered-reward integrability yields succ-indexed ordinary conditional expectation zero over generatedActionFromRewardHistory; it still assumes the packaged reward-coordinate law and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW is compiled locally as the definitional actual reward-coordinate source-level canonical pair-law consumer: GeneratedActionDefinitionalActualRewardMapSource now yields the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law over generatedActionFromRewardHistory; it still assumes the definitional actual reward-coordinate law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-PARTIALTRAJ-LAW is compiled locally as the definitional actual reward-coordinate source-level full finite-pair-trace partialTraj consumer: GeneratedActionDefinitionalActualRewardMapSource now yields the actionRewardPartialTrajectoryKernel law over generatedActionFromRewardHistory; it still assumes the definitional actual reward-coordinate law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-DEFINITIONAL-RANDOM-PAIR-MAP-SOURCE is compiled locally as a source-conversion leaf: a definitional actual-action reward-coordinate map source plus context measurability now builds the stronger definitional generated random-pair map source through the full finite-pair partialTraj law and existing random-pair source constructor; it still assumes the definitional actual reward-coordinate source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-GENERATED-RANDOM-PAIR-MAP-SOURCE is compiled locally as a source-conversion leaf: a definitional actual-action reward-coordinate map source now directly builds the explicit generated-action random-pair map source over generatedActionFromRewardHistory through the actual-to-random source upgrade; it still assumes the definitional actual reward-coordinate source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT is compiled locally as a reusable generated-policy random next-pair law source package; it now also builds that source from canonical history-step next-pair, full finite-pair partialTraj, or frozen-prefix extension-map partialTraj law hypotheses before exposing finite-pair-trace partialTraj law and succ-indexed conditional mean-zero consumers; it still assumes the pair/reward law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-MEAN-ZERO is compiled locally as the standalone integrability-based source-level conditional mean-zero consumer: a packaged GeneratedActionRandomPairMapSource plus centered reward-kernel law and explicit centered-reward integrability yields succ-indexed ordinary conditional expectation zero over the supplied generated action/reward history filtration; it still assumes the packaged random next-pair law and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-RAW-RANGE-MEASURABLE-MEAN-RANGE-MEAN-ZERO is compiled locally as the source-level raw-range conditional mean-zero consumer: a packaged GeneratedActionRandomPairMapSource plus centered reward-kernel law, deterministic raw reward range bounds, deterministic selected-mean range bounds, and reward measurability yields succ-indexed ordinary conditional expectation zero without a separate integrability hypothesis; it still assumes the packaged random next-pair law and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-TO-HISTORYSTEP-PAIR-LAW is compiled locally as the source-level canonical pair-law consumer: GeneratedActionRandomPairMapSource now directly yields the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law over History.finitePairHistoryOfTrace; it still assumes the random next-pair law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE is compiled locally as a source-conversion leaf: a generated random next-pair source now produces the weaker actual-action reward-coordinate map source by action freezing and Prod.snd marginalization; it still assumes the random pair law and state measurability.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE is compiled locally as a source-conversion leaf: a centered generated random-pair source now directly exposes its packaged GeneratedActionRandomPairMapSource; it still assumes the random next-pair law and source regularity fields.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE is compiled locally as a source-conversion leaf: a centered generated random-pair source now projects its packaged map source and state measurability into the weaker actual-action reward-coordinate source; it still assumes the centered source fields and random pair law.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE is compiled locally as a source-conversion leaf: a bounded centered generated random-pair source now directly exposes its packaged GeneratedActionRandomPairMapSource; it still assumes the random next-pair law and bounded source regularity fields.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE is compiled locally as a source-conversion leaf: a bounded centered generated random-pair source now projects its packaged map source and state measurability into the weaker actual-action reward-coordinate source; it still assumes the bounded-centered source fields and random pair law.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT is compiled locally as the variant that defines the action trace as the shifted policy-generated trace over finite reward histories and derives its timewise measurability from measurable state extractors plus reward traces; it now also exposes source constructors from full finite-pair, frozen-prefix extension-map partialTraj, and canonical history-step next-pair law hypotheses, then reuses the generated random-pair map source consumers including the raw/mean range regularity mean-zero route; it still assumes the ambient trajectory-to-condExpKernel law shape and does not construct it.")
    print("- COND-EXPECT-REWARD-DEFINITIONAL-RANDOM-PAIR-MAP-SOURCE-TO-SELECTED-POLICY-REWARD-MAP is compiled locally as a source-projection leaf: a definitional generated random-pair map source now exposes the policy-selected reward-coordinate condExpKernel law by lowering through the definitional actual-action reward-map source and unfolding generatedActionFromRewardHistory; it still assumes the definitional random next-pair source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-SELECTED-POLICY-REWARD-MAP-TO-DEFINITIONAL-RANDOM-PAIR-MAP-SOURCE is compiled locally as a source-constructor leaf: a policy-selected reward-coordinate selected-measure law plus context/state measurability now builds the bare definitional random-pair map source by rewriting to the generated successor action and reusing the frozen-prefix extension-map route; it still assumes the reward-coordinate condExpKernel law and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-SELECTED-POLICY-DEFINITIONAL-MAP-SOURCE-RAW-RANGE-MEAN-ZERO is compiled locally as a mean-zero consumer: the policy-selected reward-coordinate selected-measure law first builds the bare definitional random-pair map source, then the raw/mean range source consumer yields succ-indexed conditional mean-zero; it still assumes the reward-coordinate law, raw/mean range regularity, centered kernel law, and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-SELECTED-POLICY-DEFINITIONAL-MAP-SOURCE-UNIFORM-VARIANCE-COND-MGF is compiled locally as a conditional MGF consumer: the policy-selected reward-coordinate selected-measure law first builds the bare definitional random-pair map source, then raw/mean range regularity plus a global variance ceiling yield succ-indexed HasCondSubgaussianMGF; it still assumes the reward-coordinate law, regularity, variance ceiling, and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-SELECTED-POLICY-DEFINITIONAL-MAP-SOURCE-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF is compiled locally as a coarser-proxy conditional MGF consumer: the policy-selected reward-coordinate selected-measure law first builds the bare definitional random-pair map source, then raw/mean range regularity plus a global variance ceiling yield succ-indexed HasCondSubgaussianMGF at any deterministic proxy c satisfying varianceCeiling <= c; it still assumes the reward-coordinate law, regularity, variance ceiling, and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-SELECTED-POLICY-DEFINITIONAL-MAP-SOURCE-HISTORY-VARIANCE-COND-MGF is compiled locally as a conditional MGF consumer: the policy-selected reward-coordinate selected-measure law first builds the bare definitional random-pair map source, then raw/mean range regularity plus time-indexed selected-history variance ceilings yield succ-indexed HasCondSubgaussianMGF at varianceCeiling i; it still assumes the reward-coordinate law, regularity, selected-history variance ceilings, and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-SELECTED-POLICY-DEFINITIONAL-MAP-SOURCE-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF is compiled locally as a coarser-proxy conditional MGF consumer: the policy-selected reward-coordinate selected-measure law first builds the bare definitional random-pair map source, then raw/mean range regularity plus time-indexed selected-history variance ceilings yield succ-indexed HasCondSubgaussianMGF at any deterministic proxy c satisfying varianceCeiling i <= c; it still assumes the reward-coordinate law, regularity, selected-history variance ceilings, and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW is compiled locally as the definitional source-level canonical pair-law consumer: GeneratedActionRandomPairDefinitionalMapSource now directly yields the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law over generatedActionFromRewardHistory; it still assumes the definitional random next-pair law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT is compiled locally as a centered regularity/source package over the generated random-pair source, including context/state measurability, kernel centered law, and per-step ambient integrability; it still assumes those source/integrability fields rather than deriving them.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW is compiled locally as the centered-source canonical pair-law consumer: GeneratedActionRandomPairCenteredSource now directly yields the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law while preserving centered law and integrability fields for later consumers; it still assumes the random next-pair law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-COND-MGF-CONSUMER is compiled locally as the centered-source conditional MGF consumer: GeneratedActionRandomPairCenteredSource yields Mathlib HasCondSubgaussianMGF under explicit centered measurability and variance-proxy domination; exponential integrability is derived from selected target laws, while the random next-pair law source remains assumed.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-COND-MGF-CONSUMER is compiled locally as the bounded-centered-source conditional MGF consumer: GeneratedActionRandomPairBoundedCenteredSource lowers through the bounded-to-centered adapter and reuses the integrated centered-source route; centered measurability and variance-proxy domination remain explicit.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-EXP-INTEGRABILITY is compiled locally as a bounded-source exponential-integrability leaf: a.e. interval bounds on centered rewards now imply integrability of exp(t * centeredReward) for every real t on finite measure spaces.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW is compiled locally as the bounded-centered-source canonical pair-law consumer: GeneratedActionRandomPairBoundedCenteredSource now directly yields the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law by lowering through the integrability-based centered source; it still assumes the random next-pair law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-CONTRACT is compiled locally as the definitional generated-action centered source: it removes explicit action-trace/haction inputs from the centered source layer using generatedActionFromRewardHistory plus the definitional map source, then reuses the centered-source finite-pair-trace and conditional mean-zero consumers; it still assumes the definitional random pair law and centered integrability fields.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-COND-MGF-CONSUMER is compiled locally as the definitional centered-source conditional MGF consumer: GeneratedActionRandomPairDefinitionalCenteredSource fixes the action trace to generatedActionFromRewardHistory and reuses the integrated Mathlib HasCondSubgaussianMGF route; centered measurability and variance-proxy domination remain explicit.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW is compiled locally as the definitional centered-source canonical pair-law consumer: GeneratedActionRandomPairDefinitionalCenteredSource now directly yields the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law over generatedActionFromRewardHistory; it still assumes the definitional random next-pair law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-INTEGRABILITY is compiled locally as a direct integrability projection: a definitional centered generated random-pair source exposes its packaged per-step ambient centered-reward integrability as a named theorem; it still assumes the definitional centered source fields and does not derive bounds.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE is compiled locally as a source-conversion leaf: a definitional centered generated random-pair source now projects its packaged definitional map source into the explicit generated random-pair map source using generatedActionFromRewardHistory; it still assumes the definitional centered source fields and random pair law.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE is compiled locally as a source-conversion leaf: a definitional centered generated random-pair source now projects its packaged definitional map source into the weaker definitional actual-action reward-coordinate source; it still assumes the definitional centered source fields and random pair law.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE is compiled locally as a source-conversion leaf: a definitional centered generated random-pair source now projects through the definitional actual-map source into the explicit generated actual-action reward-coordinate source using generatedActionFromRewardHistory; it still assumes the definitional centered source fields and random pair law.")
    print("- COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT is compiled locally as the bounded/a.e.-measurable variant that derives the centered-source integrability field via Mathlib Integrable.of_mem_Icc, then exposes the same finite-pair-trace and conditional mean-zero consumers; it still assumes the random pair law source, a.e. bound evidence, and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-GENERATED-RAW-MEAN-BOUNDED-SOURCE-CONTRACT is compiled locally as the raw-reward/selected-mean bounded variant that derives centered a.e. measurability and centered interval bounds before reusing the bounded-centered source consumers; it still assumes the random pair law source, raw/mean bound evidence, and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW is compiled locally as the raw-reward/selected-mean bounded canonical pair-law consumer: GeneratedActionRandomPairRawMeanBoundedSource now directly yields the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law by lowering through the bounded-centered source; it still assumes the random next-pair law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE is compiled locally as a source-conversion leaf: a raw-reward/selected-mean bounded generated random-pair source now directly exposes its packaged GeneratedActionRandomPairMapSource; it still assumes the random next-pair law and source regularity fields.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE is compiled locally as a source-conversion leaf: a raw-reward/selected-mean bounded generated random-pair source now projects its packaged map source and state measurability into the weaker actual-action reward-coordinate source; it still assumes the raw/mean bounded source fields and random pair law.")
    print("- COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEAN-BOUNDED-SOURCE-CONTRACT is compiled locally as the variant that derives raw reward Rat-to-Real a.e. measurability from hreward, then reuses the raw/mean bounded source consumers; it still assumes the random pair law source, raw reward bounds, selected mean measurability/bounds, and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW is compiled locally as the raw-reward-bound/selected-mean bounded canonical pair-law consumer: GeneratedActionRandomPairRawBoundMeanBoundedSource now directly yields the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law by lowering through the raw/mean bounded source; it still assumes the random next-pair law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE is compiled locally as a source-conversion leaf: a raw-reward-bound/selected-mean bounded generated random-pair source now directly exposes its packaged GeneratedActionRandomPairMapSource; it still assumes the random next-pair law and source regularity fields.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE is compiled locally as a source-conversion leaf: a raw-reward-bound/selected-mean bounded generated random-pair source now projects its packaged map source and state measurability into the weaker actual-action reward-coordinate source; it still assumes the raw-bound/mean-bounded source fields and random pair law.")
    print("- COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-CONTRACT is compiled locally as the variant that derives selected mean Rat-to-Real a.e. measurability from a measurable mean surface composed with finite reward histories, context/state extractors, and the measurable policy action, then reuses the raw-bound/mean-bounded source consumers; it still assumes the random pair law source, raw reward bounds, selected mean bounds, and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-MEAN-ZERO is compiled locally as the source-level raw-bound/measurable-selected-mean conditional mean-zero consumer: a GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource lowers to the raw-bound/mean-bounded layer and yields succ-indexed ordinary conditional expectation zero; it still assumes the packaged random next-pair law, source regularity fields, and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE is compiled locally as a source-conversion leaf: a raw-reward-bound/measurable-selected-mean generated random-pair source now directly exposes its packaged GeneratedActionRandomPairMapSource; it still assumes the random next-pair law and source regularity fields.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW is compiled locally as the raw-reward-bound/measurable-selected-mean canonical pair-law consumer: GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource now directly yields the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law by lowering through the raw-bound/mean-bounded source; it still assumes the random next-pair law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE is compiled locally as a source-conversion leaf: a raw-reward-bound/measurable-selected-mean generated random-pair source now projects its packaged map source and state measurability into the weaker actual-action reward-coordinate source; it still assumes the raw-bound/measurable-mean source fields and random pair law.")
    print("- COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT is compiled locally as the variant that derives selected mean a.e. interval bounds from deterministic pointwise mean range bounds, then reuses the raw-bound/measurable-mean source consumers; it still assumes the random pair law source, raw reward bounds, mean measurability, deterministic mean range bounds, and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-MEAN-ZERO is compiled locally as the source-level raw-bound/measurable-mean-range conditional mean-zero consumer: a GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource lowers to the raw-bound/measurable-mean bounded layer and yields succ-indexed ordinary conditional expectation zero; it still assumes the packaged random next-pair law, source regularity fields, and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE is compiled locally as a source-conversion leaf: a raw-reward-bound/measurable-mean-range bounded generated random-pair source now directly exposes its packaged GeneratedActionRandomPairMapSource; it still assumes the random next-pair law and source regularity fields.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW is compiled locally as the raw-reward-bound/measurable-mean-range canonical pair-law consumer: GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource now directly yields the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law by lowering through the raw-bound/measurable-mean source; it still assumes the random next-pair law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE is compiled locally as a source-conversion leaf: a raw-reward-bound/measurable-mean-range bounded generated random-pair source now projects its packaged map source and state measurability into the weaker actual-action reward-coordinate source; it still assumes the raw-bound/measurable-mean-range source fields and random pair law.")
    print("- COND-EXPECT-REWARD-GENERATED-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT is compiled locally as the variant that derives raw reward a.e. interval bounds from deterministic pointwise reward range bounds and exposes a source-free centered-reward integrability helper, then reuses the raw-bound/measurable-mean-range source consumers; it still assumes the random pair law source, mean measurability, deterministic raw reward and mean range bounds, and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-GENERATED-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-MEAN-ZERO is compiled locally as the source-level raw-range conditional mean-zero consumer: a GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource lowers to the raw-bound/measurable-mean-range layer and yields succ-indexed ordinary conditional expectation zero; it still assumes the packaged random next-pair law, source regularity fields, and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE is compiled locally as a source-projection leaf: the explicit top raw-range/measurable-mean-range source now directly exposes its packaged GeneratedActionRandomPairMapSource through a named wrapper; it still assumes the packaged random next-pair law and top-layer regularity fields.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW is compiled locally as the raw-reward-range/measurable-mean-range canonical pair-law consumer: GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource now directly yields the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law by lowering through the raw-bound/measurable-mean-range source; it still assumes the random next-pair law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE is compiled locally as a source-conversion leaf: a raw-reward-range/measurable-mean-range bounded generated random-pair source now projects its packaged map source and state measurability into the weaker actual-action reward-coordinate source; it still assumes the raw-range/measurable-mean-range source fields and random pair law.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT is compiled locally as the practical definitional generated-action source: it removes explicit action-trace/haction inputs from the raw-range/measurable-mean-range layer by using generatedActionFromRewardHistory and the definitional random-pair map source; it now also constructs that top-layer source from full finite-pair, frozen-prefix extension-map partialTraj, and canonical history-step next-pair law hypotheses plus raw/mean range regularity, directly consumes the full finite-pair partialTraj law plus regularity into succ-indexed conditional mean-zero, directly consumes the frozen-prefix extension-map law plus regularity into that mean-zero fact, directly consumes the canonical history-step next-pair law plus regularity into that mean-zero fact, and directly consumes generated-action policy-selected or actual-action reward-coordinate selected-measure laws plus regularity into mean-zero; it still assumes the reward-coordinate/next-pair/ambient trajectory-to-condExpKernel law shape and does not construct it.")
    print("- COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-RAW-RANGE-MEASURABLE-MEAN-RANGE-MEAN-ZERO is compiled locally as a conditional mean-zero consumer leaf: an actual-action reward-coordinate selected-measure law over generatedActionFromRewardHistory plus raw/mean range regularity now yields the succ-indexed conditional expectation zero statement for the centered selected reward; it still assumes the actual-action reward-coordinate condExpKernel law and does not add variance ceilings, MGF witnesses, or final adaptive theorem.")
    print("- COND-EXPECT-REWARD-SELECTED-POLICY-REWARD-MAP-RAW-RANGE-MEASURABLE-MEAN-RANGE-MEAN-ZERO is compiled locally as a conditional mean-zero consumer leaf: a policy-selected reward-coordinate selected-measure law plus raw/mean range regularity now yields the succ-indexed conditional expectation zero statement for the centered selected reward over generatedActionFromRewardHistory; it still assumes the policy-selected reward-coordinate condExpKernel law and does not add variance ceilings, MGF witnesses, or final adaptive theorem.")
    print("- COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE is compiled locally as a source-constructor leaf: a packaged definitional actual-action reward-coordinate source plus context/mean/kernel/raw-range/mean-range regularity now builds the base definitional raw-range/measurable-mean-range generated random-pair source by reusing the definitional actual-source to definitional random-pair map-source bridge; it still assumes the packaged reward-coordinate law and does not add variance ceilings, MGF witnesses, or final adaptive theorem.")
    print("- COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-RAW-RANGE-MEASURABLE-MEAN-RANGE-MEAN-ZERO is compiled locally as a conditional mean-zero consumer leaf: a packaged definitional actual-action reward-coordinate source plus raw/mean range regularity now yields the succ-indexed conditional expectation zero statement for the centered selected reward over generatedActionFromRewardHistory; it still assumes the packaged reward-coordinate law and does not add variance ceilings, MGF witnesses, or final adaptive theorem.")
    print("- COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-UNIFORM-VARIANCE-SOURCE is compiled locally as a source-constructor leaf: a packaged definitional actual-action reward-coordinate source plus raw/mean range regularity and a global varianceProxy ceiling now builds the packaged definitional raw-range/measurable-mean-range uniform-variance source for downstream MGF consumers; it still assumes the packaged reward-coordinate law and does not itself prove the MGF witness or final adaptive theorem.")
    print("- COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-UNIFORM-VARIANCE-COND-MGF is compiled locally as a conditional MGF consumer leaf: a packaged definitional actual-action reward-coordinate source plus raw/mean range regularity and a global varianceProxy ceiling now yields the succ-indexed HasCondSubgaussianMGF witness with proxy varianceCeiling; it still assumes the packaged reward-coordinate law and does not prove the final adaptive theorem.")
    print("- COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF is compiled locally as a coarser-proxy conditional MGF consumer leaf: a packaged definitional actual-action reward-coordinate source plus raw/mean range regularity and a global varianceProxy ceiling can now be consumed at any deterministic proxy c satisfying varianceCeiling <= c; it still assumes the packaged reward-coordinate law and does not prove the final adaptive theorem.")
    print("- COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-HISTORY-VARIANCE-SOURCE is compiled locally as a source-constructor leaf: a packaged definitional actual-action reward-coordinate source plus raw/mean range regularity and time-indexed selected-history variance ceilings now builds the packaged definitional raw-range/measurable-mean-range history-variance source for downstream MGF consumers; it still assumes the packaged reward-coordinate law and does not itself prove the MGF witness or final adaptive theorem.")
    print("- COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-HISTORY-VARIANCE-COND-MGF is compiled locally as a conditional MGF consumer leaf: a packaged definitional actual-action reward-coordinate source plus raw/mean range regularity and time-indexed selected-history variance ceilings now yields the succ-indexed HasCondSubgaussianMGF witness with proxy varianceCeiling i; it still assumes the packaged reward-coordinate law and does not prove the final adaptive theorem.")
    print("- COND-EXPECT-REWARD-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF is compiled locally as a coarser-proxy conditional MGF consumer leaf: a packaged definitional actual-action reward-coordinate source plus raw/mean range regularity and time-indexed selected-history variance ceilings can now be consumed at any deterministic proxy c satisfying varianceCeiling i <= c; it still assumes the packaged reward-coordinate law and does not prove the final adaptive theorem.")
    print("- COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE is compiled locally as a source-constructor leaf: an actual-action reward-coordinate selected-measure law plus raw/mean range regularity now builds the base definitional raw-range/measurable-mean-range generated random-pair source without adding variance or MGF assumptions; it still assumes the actual-action reward-coordinate condExpKernel law and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-SELECTED-POLICY-REWARD-MAP-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE is compiled locally as a source-constructor leaf: a policy-selected reward-coordinate selected-measure law plus raw/mean range regularity now builds the base definitional raw-range/measurable-mean-range generated random-pair source by rewriting to the generated successor action; it still assumes the policy-selected reward-coordinate condExpKernel law and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-SOURCE is compiled locally as the full finite-pair partialTraj-law constructor for the packaged definitional raw-range/measurable-mean-range uniform-variance source.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-COND-MGF is compiled locally as the full finite-pair partialTraj-law conditional MGF consumer for the practical definitional raw-range/measurable-mean-range uniform-variance route.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF is compiled locally as a coarser-proxy consumer: the full finite-pair partialTraj law plus a global varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling <= c.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-SOURCE is compiled locally as the full finite-pair partialTraj-law constructor for the packaged definitional raw-range/measurable-mean-range history-variance source.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-COND-MGF is compiled locally as the full finite-pair partialTraj-law conditional MGF consumer for the practical definitional raw-range/measurable-mean-range history-variance route.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF is compiled locally as a coarser-proxy consumer: the full finite-pair partialTraj law plus a selected-history varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling i <= c.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-SOURCE is compiled locally as the frozen-prefix extension-map partialTraj-law constructor for the packaged definitional raw-range/measurable-mean-range uniform-variance source.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-COND-MGF is compiled locally as the frozen-prefix extension-map partialTraj-law conditional MGF consumer for the practical definitional raw-range/measurable-mean-range uniform-variance route.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF is compiled locally as a coarser-proxy consumer: the frozen-prefix extension-map partialTraj law plus a global varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling <= c.")
    print("- COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-UNIFORM-VARIANCE-COND-MGF is compiled locally as the actual-action reward-coordinate selected-measure law conditional MGF consumer for the practical definitional raw-range/measurable-mean-range uniform-variance route.")
    print("- COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF is compiled locally as a coarser-proxy consumer: the actual-action reward-coordinate selected-measure law plus a global varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling <= c.")
    print("- COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-UNIFORM-VARIANCE-SOURCE is compiled locally as the actual-action reward-coordinate selected-measure law source constructor for the practical definitional raw-range/measurable-mean-range uniform-variance route.")
    print("- COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-HISTORY-VARIANCE-COND-MGF is compiled locally as the actual-action reward-coordinate selected-measure law conditional MGF consumer for the practical definitional raw-range/measurable-mean-range history-variance route.")
    print("- COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-HISTORY-VARIANCE-SOURCE is compiled locally as the actual-action reward-coordinate selected-measure law source constructor for the practical definitional raw-range/measurable-mean-range history-variance route.")
    print("- COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF is compiled locally as a coarser-proxy consumer: the actual-action reward-coordinate selected-measure law plus a selected-history varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling i <= c.")
    print("- COND-EXPECT-REWARD-SELECTED-POLICY-UNIFORM-VARIANCE-COND-MGF is compiled locally as the policy-selected reward-coordinate selected-measure law conditional MGF consumer for the practical definitional raw-range/measurable-mean-range uniform-variance route.")
    print("- COND-EXPECT-REWARD-SELECTED-POLICY-UNIFORM-VARIANCE-SOURCE is compiled locally as the policy-selected reward-coordinate selected-measure law source constructor for the practical definitional raw-range/measurable-mean-range uniform-variance route.")
    print("- COND-EXPECT-REWARD-SELECTED-POLICY-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF is compiled locally as a coarser-proxy consumer: the policy-selected reward-coordinate selected-measure law plus a global varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling <= c.")
    print("- COND-EXPECT-REWARD-SELECTED-POLICY-HISTORY-VARIANCE-COND-MGF is compiled locally as the policy-selected reward-coordinate selected-measure law conditional MGF consumer for the practical definitional raw-range/measurable-mean-range history-variance route.")
    print("- COND-EXPECT-REWARD-SELECTED-POLICY-HISTORY-VARIANCE-SOURCE is compiled locally as the policy-selected reward-coordinate selected-measure law source constructor for the practical definitional raw-range/measurable-mean-range history-variance route.")
    print("- COND-EXPECT-REWARD-SELECTED-POLICY-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF is compiled locally as a coarser-proxy consumer: the policy-selected reward-coordinate selected-measure law plus a selected-history varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling i <= c.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-HISTORY-VARIANCE-SOURCE is compiled locally as the frozen-prefix extension-map partialTraj-law constructor for the packaged definitional raw-range/measurable-mean-range history-variance source.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-HISTORY-VARIANCE-COND-MGF is compiled locally as the frozen-prefix extension-map partialTraj-law conditional MGF consumer for the practical definitional raw-range/measurable-mean-range history-variance route.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF is compiled locally as a coarser-proxy consumer: the frozen-prefix extension-map partialTraj law plus a selected-history varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling i <= c.")
    print("- COND-EXPECT-REWARD-HISTORYSTEP-UNIFORM-VARIANCE-SOURCE is compiled locally as the canonical history-step next-pair law constructor for the packaged definitional raw-range/measurable-mean-range uniform-variance source.")
    print("- COND-EXPECT-REWARD-HISTORYSTEP-UNIFORM-VARIANCE-COND-MGF is compiled locally as the canonical history-step next-pair law conditional MGF consumer for the practical definitional raw-range/measurable-mean-range uniform-variance route.")
    print("- COND-EXPECT-REWARD-HISTORYSTEP-UNIFORM-VARIANCE-LARGER-PROXY-COND-MGF is compiled locally as a coarser-proxy consumer: the canonical history-step next-pair law plus a global varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling <= c.")
    print("- COND-EXPECT-REWARD-HISTORYSTEP-HISTORY-VARIANCE-SOURCE is compiled locally as the canonical history-step next-pair law constructor for the packaged definitional raw-range/measurable-mean-range history-variance source.")
    print("- COND-EXPECT-REWARD-HISTORYSTEP-HISTORY-VARIANCE-COND-MGF is compiled locally as the canonical history-step next-pair law conditional MGF consumer for the practical definitional raw-range/measurable-mean-range history-variance route.")
    print("- COND-EXPECT-REWARD-HISTORYSTEP-HISTORY-VARIANCE-LARGER-PROXY-COND-MGF is compiled locally as a coarser-proxy consumer: the canonical history-step next-pair law plus a selected-history varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling i <= c.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW is compiled locally as the definitional raw-reward-range/measurable-mean-range canonical pair-law consumer: GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource now directly yields the RewardKernel.actionRewardHistoryStepKernelFamily next-pair law over generatedActionFromRewardHistory by lowering through the explicit raw-range source; it still assumes the definitional random next-pair law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE is compiled locally as a source-conversion leaf: a definitional raw-reward-range/measurable-mean-range bounded generated random-pair source now projects its packaged definitional map source into the explicit generated random-pair map source using generatedActionFromRewardHistory; it still assumes the definitional raw-range/measurable-mean-range source fields and random pair law.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-PARTIALTRAJ-PAIR-LAW-SOURCE is compiled locally as a source-conversion leaf: a definitional raw-reward-range/measurable-mean-range bounded generated random-pair source now projects its packaged definitional map source and context measurability into GeneratedActionPartialTrajectoryPairLawSource; it still assumes the packaged definitional random-pair law and does not prove the ambient partialTraj/condExpKernel trajectory identification.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-CENTERED-REGULARITY is compiled locally as a regularity leaf: a definitional raw-reward-range/measurable-mean-range bounded generated random-pair source now exposes centered successor reward a.e. measurability, full measurability, and the centered interval bound directly; it still assumes the definitional raw-range/measurable-mean-range source fields and random pair law.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-BOUNDED-CENTERED-SOURCE is compiled locally as a source-conversion leaf: a definitional raw-reward-range/measurable-mean-range bounded generated random-pair source now packages its explicit generated random-pair map source plus centered a.e. measurability and bounds into the bounded centered source over generatedActionFromRewardHistory; it still assumes the definitional raw-range/measurable-mean-range source fields and random pair law.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-CENTERED-SOURCE is compiled locally as a source-conversion leaf: a definitional raw-reward-range/measurable-mean-range bounded generated random-pair source now lowers through the bounded-centered source into the integrability-based centered source over generatedActionFromRewardHistory; it still assumes the definitional raw-range/measurable-mean-range source fields and random pair law.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE is compiled locally as a source-conversion leaf: a definitional raw-reward-range/measurable-mean-range bounded generated random-pair source now packages its definitional map source, centered law, context measurability, and bounded-derived integrability into the definitional centered source; it still assumes the definitional raw-range/measurable-mean-range source fields and random pair law.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-CONSUMER is compiled locally as a practical top-level conditional MGF consumer: the definitional raw-range/measurable-mean-range source lowers through the definitional centered source and reuses the integrated Mathlib HasCondSubgaussianMGF route; centered measurability and variance-proxy domination remain explicit.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-EXP-INTEGRABILITY is compiled locally as the practical top-level exponential-integrability consumer: deterministic raw reward and selected-mean range evidence now derives exp(t * centeredReward) integrability for every real t over generatedActionFromRewardHistory.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-BOUNDED-EXP-CONSUMER remains compiled as a compatibility wrapper: centered measurability and variance-proxy domination remain explicit, while the integrated target-law route now derives h_integrable_exp without using the bounded-exp helper.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-SOURCE-REGULARITY-CONSUMER is compiled locally as the practical conditional MGF wrapper that derives centered-reward measurability from source regularity; integrated target laws derive exponential integrability, so only variance-proxy domination remains explicit.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-UNIFORM-VARIANCE-CONSUMER is compiled locally as the practical conditional MGF wrapper that reduces the remaining trimmed-a.e. variance-domination side condition to a model-side uniform varianceProxy ceiling, with a packaged uniform-variance source wrapper.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-COND-MGF-HISTORY-VARIANCE-CONSUMER is compiled locally as the practical conditional MGF wrapper that reduces the trimmed-a.e. variance-domination side condition to a selected finite-history varianceProxy ceiling, weaker than the global context/action ceiling.")
    print("- COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE is compiled locally as a source-projection leaf: a practical uniform-variance source now directly exposes its packaged raw-range/measurable-mean-range bounded base source; it still assumes the packaged random-pair law, raw/mean range regularity, and global variance ceiling.")
    print("- COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE is compiled locally as a source-conversion leaf: a practical uniform-variance source now lowers through its packaged base source into the explicit generated random-pair map source over generatedActionFromRewardHistory.")
    print("- COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-PARTIALTRAJ-PAIR-LAW-SOURCE is compiled locally as a source-conversion leaf: a practical uniform-variance source now lowers through its packaged raw-range base source into GeneratedActionPartialTrajectoryPairLawSource; it still assumes the packaged random-pair law and does not prove the ambient partialTraj/condExpKernel trajectory identification.")
    print("- COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-HISTORYSTEP-PAIR-LAW is compiled locally as a source-consumer leaf: a practical uniform-variance source now lowers through its generated random-pair map source into the canonical RewardKernel.actionRewardHistoryStepKernelFamily next-pair law over generatedActionFromRewardHistory.")
    print("- COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE is compiled locally as a source-conversion leaf: a practical uniform-variance source now lowers through its packaged base source into the weaker definitional generated actual-action reward-coordinate source over generatedActionFromRewardHistory.")
    print("- COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE is compiled locally as a source-conversion leaf: a practical uniform-variance source now lowers through its packaged base source into the explicit generated actual-action reward-map source over generatedActionFromRewardHistory.")
    print("- COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE is compiled locally as a source-conversion leaf: a practical uniform-variance source now lowers through its packaged base source into the definitional centered-source interface over generatedActionFromRewardHistory.")
    print("- COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-BOUNDED-CENTERED-SOURCE is compiled locally as a source-conversion leaf: a practical uniform-variance source now lowers through its packaged base source into the bounded centered-source interface over generatedActionFromRewardHistory.")
    print("- COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-CENTERED-SOURCE is compiled locally as a source-conversion leaf: a practical uniform-variance source now lowers through its bounded centered-source projection into the integrability-based centered-source interface over generatedActionFromRewardHistory.")
    print("- COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RAW-RANGE-BOUNDED-SOURCE is compiled locally as a source-projection leaf: a practical selected-history-variance source now directly exposes its packaged raw-range/measurable-mean-range bounded base source; it still assumes the packaged random-pair law, raw/mean range regularity, and selected-history variance ceilings.")
    print("- COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE is compiled locally as a source-conversion leaf: a practical selected-history-variance source now lowers through its packaged base source into the explicit generated random-pair map source over generatedActionFromRewardHistory.")
    print("- COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-PARTIALTRAJ-PAIR-LAW-SOURCE is compiled locally as a source-conversion leaf: a practical selected-history-variance source now lowers through its packaged raw-range base source into GeneratedActionPartialTrajectoryPairLawSource; it still assumes the packaged random-pair law and does not prove the ambient partialTraj/condExpKernel trajectory identification.")
    print("- COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-HISTORYSTEP-PAIR-LAW is compiled locally as a source-consumer leaf: a practical selected-history-variance source now lowers through its generated random-pair map source into the canonical RewardKernel.actionRewardHistoryStepKernelFamily next-pair law over generatedActionFromRewardHistory.")
    print("- COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE is compiled locally as a source-conversion leaf: a practical selected-history-variance source now lowers through its packaged base source into the weaker definitional generated actual-action reward-coordinate source over generatedActionFromRewardHistory.")
    print("- COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE is compiled locally as a source-conversion leaf: a practical selected-history-variance source now lowers through its packaged base source into the explicit generated actual-action reward-map source over generatedActionFromRewardHistory.")
    print("- COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-BOUNDED-CENTERED-SOURCE is compiled locally as a source-conversion leaf: a practical selected-history-variance source now lowers through its packaged base source into the bounded centered-source interface over generatedActionFromRewardHistory.")
    print("- COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-CENTERED-SOURCE is compiled locally as a source-conversion leaf: a practical selected-history-variance source now lowers through its bounded centered-source projection into the integrability-based centered-source interface over generatedActionFromRewardHistory.")
    print("- COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE is compiled locally as a source-conversion leaf: a practical selected-history-variance source now lowers through its packaged base source into the definitional centered-source interface over generatedActionFromRewardHistory.")
    print("- COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-HISTORY-VARIANCE-SOURCE is compiled locally as a source-conversion leaf: a packaged uniform variance ceiling yields the time-indexed selected-history variance source with constant ceiling fun _ => varianceCeiling.")
    print("- COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-VIA-HISTORY-COND-MGF is compiled locally as a convenience consumer: a packaged uniform variance source is converted to the selected-history variance source and then consumed through the history-variance conditional MGF interface; it still assumes the definitional random next-pair law source and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF is compiled locally as a coarser-proxy consumer: a packaged uniform variance source with global varianceCeiling can be consumed at any deterministic proxy c satisfying varianceCeiling <= c.")
    print("- COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-HISTORY-VARIANCE-SOURCE-COND-MGF-CONSUMER is compiled locally as the time-indexed selected-history variance source wrapper and conditional MGF consumer, yielding proxy varianceCeiling i without per-call trimmed-a.e. variance hypotheses and accepting uniform sources through the constant-ceiling source conversion.")
    print("- COND-EXPECT-REWARD-HISTORY-VARIANCE-SOURCE-LARGER-PROXY-COND-MGF is compiled locally as a coarser-proxy consumer: a packaged selected-history variance source with proxy varianceCeiling i can be consumed at any deterministic proxy c satisfying varianceCeiling i <= c.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE is compiled locally as a source-conversion leaf: a definitional raw-reward-range/measurable-mean-range bounded generated random-pair source now projects its packaged definitional map source into the weaker definitional actual-action reward-coordinate source; it still assumes the definitional raw-range/measurable-mean-range source fields and random pair law.")
    print("- COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE is compiled locally as a source-conversion leaf: a definitional raw-reward-range/measurable-mean-range bounded generated random-pair source now projects through the definitional actual-map source into the explicit generated actual-action reward-coordinate source using generatedActionFromRewardHistory; it still assumes the definitional raw-range/measurable-mean-range source fields and random pair law.")
    print("- COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-REWARD-MAP is compiled locally as the extension-map reward-coordinate adapter and raw-range mean-zero consumer: it lifts the frozen-prefix extension-map partialTraj law to the full finite-pair trace law, projects it to the actual-action selected reward law, and derives succ-indexed conditional mean-zero from raw-reward/selected-mean range bounds; it still assumes the extension-map law and ambient trajectory-to-condExpKernel identification.")
    print("- COND-EXPECT-REWARD-NEXTPAIR-HISTORYSTEP-REWARD-MAP is compiled locally as the direct history-step next-pair reward-coordinate adapter and generated-action raw-range mean-zero surface: it projects an explicit RewardKernel.actionRewardHistoryStepKernelFamily pair law through Prod.snd, rewrites the policy action to the actual successor action, and exposes a generated-action raw/mean range wrapper for succ-indexed conditional mean-zero; it still assumes the next-pair condExpKernel law and ambient trajectory-to-condExpKernel identification.")
    print("- Review responses recorded include the historical Extended Pro artifacts and the current local dual-agent review artifacts under reports/.")
    print("- ETC-WRONG-COMMIT-PROBABILITY-DESIGN is historical route evidence. Native Real exact concentration/count/regret, selected feedback-law transport, least-encoded tie semantics, three-piece action assembly, source-shaped history scores, and a faithful local LML-field theorem now compile; only true cross-toolchain import of the actual LML symbols remains.")
    print("- ETC-NATIVE-REAL-ACTION-DEPENDENT-SOURCE-EXACT-REGRET is compiled locally: upstream-shaped initial/full-history selected feedback laws map to the native Real exact theorem, and its least-encoded action-behavior consumer now compiles downstream.")
    print("- ETC-NATIVE-REAL-LEAST-ENCODED-ACTION-EXACT-REGRET is compiled locally: the Nat.find least-encoded selector equals the strict fold, and round-robin exploration, commit, and persistence generate the exact theorem's action equality. Its downstream history-score and faithful local field-compatibility consumers now compile; only actual cross-toolchain symbol import remains.")
    print("- ETC-NATIVE-REAL-HISTORY-SCORE-SOURCE-EXACT-REGRET is compiled locally: inclusive finite-pair-history pullCount'/sumRewards'/empMean' semantics are identified with the native Real exploration score, and a history-shaped least-encoded commit law directly yields the exact finite-sum regret theorem. Its downstream faithful local field-compatibility theorem now compiles; only actual cross-toolchain LML symbol import remains.")
    print("- ETC-NATIVE-REAL-LML-FIELD-COMPAT-EXACT-REGRET is compiled locally: RealStationaryETCSequence bundles the precise measurable action/reward, three ETC action phases, and stationary initial/successor feedback condDistrib laws, and regret_le_of_realStationaryETCSequence returns the exact LML-shaped finite sum. This is a local ported compatibility theorem, not an imported LML declaration; ABRL v4.29.1 and pinned LML v4.32.0-rc1 still require an explicit cross-toolchain dependency decision.")
    print("- Do not prove the generic constant-arm suffix lemma, simplify the RHS, or start broad Hoeffding/martingale/final ETC theorem work in the same batch.")
    print("- ETC-PAIRWISE-TAIL-IMPORT-ROUTE-CARD is historical route evidence. Downstream native Real product, exact finite-sum regret, selected feedback-law transport, least-encoded tie semantics, action assembly, history-score mapping, and faithful local field compatibility compile; only true cross-toolchain import of the actual LML symbols remains open.")
    print("- Do not mark theorem-card or weapon-only rows as local proofs.")
    return 0


def cmd_review_prompt(args: argparse.Namespace) -> int:
    path = Path(args.path)
    if not path.is_absolute():
        path = ROOT / path
    if not path.exists():
        print(f"review prompt not found: {rel(path)}")
        return 1
    print(path.read_text(encoding="utf-8", errors="replace"))
    return 0


def cmd_extended_pro_prompt(args: argparse.Namespace) -> int:
    return cmd_review_prompt(args)


def review_response_files(stem: str) -> list[Path]:
    reports = ROOT / "reports"
    if not reports.exists():
        return []
    files = []
    for path in sorted(reports.glob(f"{stem}*.md")):
        name = path.name
        if (
            "_prompt_" in name
            or "_candidate_prompt_" in name
            or "_pending_" in name
            or "_retry_pending_" in name
            or "_response_template_" in name
            or "_manual_handoff_" in name
            or "_handoff_" in name
            or name.endswith("_template.md")
        ):
            continue
        files.append(path)
    return files


def is_completed_review_response(path: Path) -> bool:
    text = path.read_text(encoding="utf-8", errors="replace")
    if "Paste the complete Extended Pro answer here." in text:
        return False
    if "Paste the complete local dual-agent answer here." in text:
        return False
    for marker in (
        "## Raw Extended Pro Response",
        "## Raw Local Dual-Agent Review",
        "## Combined Local Review",
    ):
        if marker in text:
            tail = text.split(marker, 1)[1].strip()
            return len(tail) >= 40
    return len(text.strip()) >= 400


def review_response_candidates(stem: str) -> list[Path]:
    return [
        path for path in review_response_files(stem)
        if is_completed_review_response(path)
    ]


def incomplete_review_response_candidates(stem: str) -> list[Path]:
    return [
        path for path in review_response_files(stem)
        if not is_completed_review_response(path)
    ]


def extended_pro_response_files(stem: str) -> list[Path]:
    return review_response_files(stem)


def is_completed_extended_pro_response(path: Path) -> bool:
    return is_completed_review_response(path)


def extended_pro_response_candidates(stem: str) -> list[Path]:
    return review_response_candidates(stem)


def incomplete_extended_pro_response_candidates(stem: str) -> list[Path]:
    return incomplete_review_response_candidates(stem)


def cmd_review_status(args: argparse.Namespace) -> int:
    prompt = Path(args.prompt)
    pending = Path(args.pending)
    if not prompt.is_absolute():
        prompt = ROOT / prompt
    if not pending.is_absolute():
        pending = ROOT / pending

    responses = review_response_candidates(args.response_stem)
    incomplete_responses = incomplete_review_response_candidates(args.response_stem)

    status = {
        "boundary": args.boundary,
        "prompt": rel(prompt),
        "prompt_present": prompt.exists(),
        "pending": rel(pending),
        "pending_present": pending.exists(),
        "responses": [rel(path) for path in responses],
        "incomplete_responses": [rel(path) for path in incomplete_responses],
        "response_received": bool(responses),
    }
    if args.json:
        print(json.dumps(status, indent=2))
        if args.require_response and not responses:
            return 2
        return 0

    print("Review direction status")
    print(f"- Boundary: {args.boundary}")
    print(f"- Prompt: {rel(prompt)} ({'present' if prompt.exists() else 'missing'})")
    print(f"- Pending/blocker: {rel(pending)} ({'present' if pending.exists() else 'missing'})")
    if responses:
        print("- Response: received")
        for path in responses:
            print(f"  - {rel(path)}")
        return 0

    print("- Response: missing")
    if incomplete_responses:
        print("- Incomplete response artifacts:")
        for path in incomplete_responses:
            print(f"  - {rel(path)}")
    print("- Status: pending local review direction; do not cross the recorded boundary.")
    if args.require_response:
        return 2
    return 0


def cmd_review_response_template(args: argparse.Namespace) -> int:
    path = Path(args.path)
    if not path.is_absolute():
        path = ROOT / path
    if not path.exists():
        print(f"review response template not found: {rel(path)}")
        return 1
    print(path.read_text(encoding="utf-8", errors="replace"))
    return 0


def cmd_extended_pro_response_template(args: argparse.Namespace) -> int:
    return cmd_review_response_template(args)


def cmd_review_handoff(args: argparse.Namespace) -> int:
    path = Path(args.path)
    if not path.is_absolute():
        path = ROOT / path
    if not path.exists():
        print(f"review handoff packet not found: {rel(path)}")
        return 1
    print(path.read_text(encoding="utf-8", errors="replace"))
    return 0


def cmd_extended_pro_handoff(args: argparse.Namespace) -> int:
    return cmd_review_handoff(args)


def cmd_review_record_response(args: argparse.Namespace) -> int:
    raw_path = Path(args.raw)
    output_path = Path(args.output)
    if not raw_path.is_absolute():
        raw_path = ROOT / raw_path
    if not output_path.is_absolute():
        output_path = ROOT / output_path
    if not raw_path.exists():
        print(f"raw review response not found: {rel(raw_path)}")
        return 1
    if output_path.exists() and not args.force:
        print(f"response output already exists: {rel(output_path)}")
        print("use --force to overwrite")
        return 1

    raw_response = raw_path.read_text(encoding="utf-8", errors="replace").strip()
    if len(raw_response) < 40:
        print("raw review response is too short to record as completed")
        return 1

    output_path.parent.mkdir(parents=True, exist_ok=True)
    prompt_path = Path(args.prompt_file)
    if not prompt_path.is_absolute():
        prompt_path = ROOT / prompt_path

    heading = getattr(args, "heading", "Local Dual-Agent Review Response")
    raw_heading = getattr(args, "raw_heading", "Raw Local Dual-Agent Review")
    body = f"""# {heading}: {args.title}

- Date: {args.date}
- Tool/model: {args.model}
- URL: {args.url}
- Prompt file: `{rel(prompt_path)}`
- Local gate before review: `python3 tools\\bandit.py check`
- Boundary:
  `{args.boundary}`
- Recorded from raw response:
  `{rel(raw_path)}`

## Reviewer Decision

- Chosen next leaf: {args.chosen_leaf}
- Classification: {args.classification}
- Status: {args.status}

## Exact Lean-Facing Statement

```lean
{args.statement}
```

## Imports And Local APIs

{args.imports}

## Intended Proof Route

{args.proof_route}

## Regularity Contracts

{args.contracts}

## Retrieval Evidence

{args.retrieval_evidence}

## Failure Policy

{args.failure_policy}

## {raw_heading}

{raw_response}
"""
    output_path.write_text(body, encoding="utf-8")
    print(f"recorded review response: {rel(output_path)}")
    return 0


def cmd_extended_pro_record_response(args: argparse.Namespace) -> int:
    args.heading = "Extended Pro Review Response"
    args.raw_heading = "Raw Extended Pro Response"
    return cmd_review_record_response(args)


def cmd_check(_args: argparse.Namespace) -> int:
    if not shutil.which("lake"):
        print("lake not found on PATH; install Lean/Lake or activate elan before running the ABRL gate")
        return 1
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
    code = run([sys.executable, "tools/test_bandit_cli.py"])
    if code != 0:
        return code
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

    p = sub.add_parser("search-memory", help="search theorem, Mathlib, textbook, paper, scenario, weapon, route, spine, local leaf, and Lean declaration cards")
    p.add_argument("query")
    p.set_defaults(func=cmd_search_memory)

    p = sub.add_parser("list-routes", help="list structured theorem-route roadmaps")
    p.add_argument("--priority", default="", help="optional priority filter such as active, active-next, planned, or watchlist")
    p.set_defaults(func=cmd_list_routes)

    p = sub.add_parser("route-plan", help="print one structured theorem-route plan")
    p.add_argument("id")
    p.add_argument("--json", action="store_true", help="print the raw route JSON")
    p.add_argument("--with-commands", action="store_true", help="include useful follow-up commands")
    p.set_defaults(func=cmd_route_plan)

    p = sub.add_parser("screen-plan", help="print a screen/codex execution plan for a task and optional route")
    p.add_argument("task")
    p.add_argument("--route", default="")
    p.add_argument("--cycles", type=int, default=2)
    p.add_argument("--lower-count", type=int, default=4)
    p.add_argument("--agent-profile", default="codex-parallel.example.json")
    p.set_defaults(func=cmd_screen_plan)

    p = sub.add_parser("render-roadmap-assets", help="render structured Lean route roadmap PNG diagrams")
    p.set_defaults(func=cmd_render_roadmap_assets)

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
    p.add_argument(
        "--require-review-response",
        action="store_true",
        help="deprecated alias for --require-review-direction",
    )
    p.add_argument(
        "--require-review-direction",
        action="store_true",
        help="stop before creating a run deck unless the current local review direction is recorded",
    )
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
    p.add_argument(
        "--require-review-response",
        action="store_true",
        help="deprecated alias for --require-review-direction",
    )
    p.add_argument(
        "--require-review-direction",
        action="store_true",
        help="stop before each cycle unless the current local review direction is recorded",
    )
    p.set_defaults(func=cmd_sleep_run)

    p = sub.add_parser("unfinished", help="list unfinished proof leaves and backlog rows")
    p.add_argument(
        "--status",
        action="append",
        choices=sorted(UNFINISHED_STATUSES),
        help="filter by one unfinished status; may be repeated",
    )
    p.set_defaults(func=cmd_unfinished)

    p = sub.add_parser("review-prompt", help="print the current local review prompt")
    p.add_argument(
        "--path",
        default=str(DEFAULT_REVIEW_PROMPT.relative_to(ROOT)),
        help="prompt file to print, relative to the repository root by default",
    )
    p.set_defaults(func=cmd_review_prompt)

    p = sub.add_parser("extended-pro-prompt", help="print a legacy Extended Pro review prompt")
    p.add_argument(
        "--path",
        default=str(DEFAULT_EXTENDED_PRO_PROMPT.relative_to(ROOT)),
        help="prompt file to print, relative to the repository root by default",
    )
    p.set_defaults(func=cmd_extended_pro_prompt)

    p = sub.add_parser("review-status", help="print the current review boundary status")
    p.add_argument(
        "--prompt",
        default=str(DEFAULT_REVIEW_PROMPT.relative_to(ROOT)),
        help="review prompt file, relative to the repository root by default",
    )
    p.add_argument(
        "--pending",
        default=str(DEFAULT_REVIEW_PENDING.relative_to(ROOT)),
        help="pending/blocker file, relative to the repository root by default",
    )
    p.add_argument(
        "--response-stem",
        default=DEFAULT_REVIEW_RESPONSE_STEM,
        help="reports/ filename stem used to detect a received review response",
    )
    p.add_argument(
        "--boundary",
        default=DEFAULT_REVIEW_BOUNDARY,
        help="human-readable boundary label",
    )
    p.add_argument(
        "--require-response",
        action="store_true",
        help="return nonzero when no review response has been recorded",
    )
    p.add_argument(
        "--json",
        action="store_true",
        help="print machine-readable review status JSON",
    )
    p.set_defaults(func=cmd_review_status)

    p = sub.add_parser("review-response-template", help="print the current local review response template")
    p.add_argument(
        "--path",
        default=str(DEFAULT_REVIEW_RESPONSE_TEMPLATE.relative_to(ROOT)),
        help="response template file to print, relative to the repository root by default",
    )
    p.set_defaults(func=cmd_review_response_template)

    p = sub.add_parser("extended-pro-response-template", help="print a legacy Extended Pro response template")
    p.add_argument(
        "--path",
        default=str(DEFAULT_EXTENDED_PRO_RESPONSE_TEMPLATE.relative_to(ROOT)),
        help="response template file to print, relative to the repository root by default",
    )
    p.set_defaults(func=cmd_extended_pro_response_template)

    p = sub.add_parser("review-handoff", help="print the current local review handoff packet")
    p.add_argument(
        "--path",
        default=str(DEFAULT_REVIEW_HANDOFF.relative_to(ROOT)),
        help="handoff packet file to print, relative to the repository root by default",
    )
    p.set_defaults(func=cmd_review_handoff)

    p = sub.add_parser("extended-pro-handoff", help="print a legacy manual Extended Pro handoff packet")
    p.add_argument(
        "--path",
        default=str(DEFAULT_EXTENDED_PRO_HANDOFF.relative_to(ROOT)),
        help="handoff packet file to print, relative to the repository root by default",
    )
    p.set_defaults(func=cmd_extended_pro_handoff)

    p = sub.add_parser("review-record-response", help="record a completed local review response artifact")
    p.add_argument("--raw", required=True, help="file containing the raw review response text")
    p.add_argument(
        "--output",
        default=str(default_review_response_output().relative_to(ROOT)),
        help="response artifact to write, relative to the repository root by default",
    )
    p.add_argument("--date", default=_dt.datetime.now().strftime("%Y-%m-%d"))
    p.add_argument("--model", default=DEFAULT_REVIEW_MODEL)
    p.add_argument("--url", default="")
    p.add_argument("--title", default=DEFAULT_REVIEW_TITLE)
    p.add_argument(
        "--prompt-file",
        default=str(DEFAULT_REVIEW_PROMPT.relative_to(ROOT)),
        help="prompt file associated with the response",
    )
    p.add_argument("--boundary", default=DEFAULT_REVIEW_BOUNDARY)
    p.add_argument("--chosen-leaf", default="TBD")
    p.add_argument("--classification", default="TBD")
    p.add_argument("--status", default="reviewer-approved")
    p.add_argument("--statement", default="-- TBD")
    p.add_argument("--imports", default="- TBD")
    p.add_argument("--proof-route", default="1. TBD")
    p.add_argument("--contracts", default="- TBD")
    p.add_argument("--retrieval-evidence", default="- TBD")
    p.add_argument("--failure-policy", default="- TBD")
    p.add_argument("--force", action="store_true", help="overwrite the output artifact if it already exists")
    p.set_defaults(func=cmd_review_record_response)

    p = sub.add_parser("extended-pro-record-response", help="record a completed legacy Extended Pro response artifact")
    p.add_argument("--raw", required=True, help="file containing the raw Extended Pro response text")
    p.add_argument(
        "--output",
        default=str(default_extended_pro_response_output().relative_to(ROOT)),
        help="response artifact to write, relative to the repository root by default",
    )
    p.add_argument("--date", default=_dt.datetime.now().strftime("%Y-%m-%d"))
    p.add_argument("--model", default="ChatGPT Extended Pro")
    p.add_argument("--url", default="")
    p.add_argument("--title", default=DEFAULT_EXTENDED_PRO_REVIEW_TITLE)
    p.add_argument(
        "--prompt-file",
        default=str(DEFAULT_EXTENDED_PRO_PROMPT.relative_to(ROOT)),
        help="prompt file associated with the response",
    )
    p.add_argument("--boundary", default=DEFAULT_EXTENDED_PRO_BOUNDARY)
    p.add_argument("--chosen-leaf", default="TBD")
    p.add_argument("--classification", default="TBD")
    p.add_argument("--status", default="reviewer-approved")
    p.add_argument("--statement", default="-- TBD")
    p.add_argument("--imports", default="- TBD")
    p.add_argument("--proof-route", default="1. TBD")
    p.add_argument("--contracts", default="- TBD")
    p.add_argument("--retrieval-evidence", default="- TBD")
    p.add_argument("--failure-policy", default="- TBD")
    p.add_argument("--force", action="store_true", help="overwrite the output artifact if it already exists")
    p.set_defaults(func=cmd_extended_pro_record_response)

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
