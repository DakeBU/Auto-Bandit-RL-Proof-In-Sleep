#!/usr/bin/env python3
"""Build a deterministic, positive-allowlist anonymous Lean/code supplement."""

import argparse
import hashlib
import json
import re
import subprocess
import sys
import zipfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
ARCHIVE_ROOT = "abrl-anonymous-artifact"
ARCHIVE_NAME = "ABRL-ICLR-2027-anonymous-lean-code.zip"
FIXED_ZIP_TIME = (2026, 1, 1, 0, 0, 0)
TEXT_PAYLOAD_SUFFIXES = {
    ".Containerfile", ".apparmor", ".json", ".lean", ".md", ".py", ".sh", ".toml",
    ".txt", ".yaml", ".yml",
}
TEXT_PAYLOAD_NAMES = {"LICENSE", "lean-toolchain"}

BLOCKED_BYTES = (
    b"dakebu",
    b"dake bu",
    b"ji cheng",
    b"bo xue",
    b"atsushi nitanda",
    b"hau-san wong",
    b"qingfu zhang",
    b"city university of hong kong",
    b"auto-bandit-rl-proof-in-sleep",
    b"git.overleaf.com",
    b"6a3f743d1f1f53f96990c557",
    b"d43bfeee56fb0c1c35cf5af9fc1a7fdc3e0c37b9",
    b"cb5d50be148c691cc595ed9fd2f535c42506fada",
)
WINDOWS_PATH = re.compile(
    br"(?i)(?<![a-z])[a-z]:[\\/](?:users[\\/][^\\/\s]+|home[\\/][^\\/\s]+|wt[\\/]|code[\\/])"
)
HOST_HOME = re.compile(br"(?i)/(?:home|users)/[^/\s]+/")
EMAIL = re.compile(br"(?i)\b[a-z0-9._%+-]+@[a-z0-9.-]+\.[a-z]{2,}\b")
PUBLIC_WORKSPACE_BASE_COMMIT = "d43bfeee56fb0c1c35cf5af9fc1a7fdc3e0c37b9"
PUBLIC_CANDIDATE_RUN_ID = "32137509103"
PUBLIC_CANDIDATE_RUN_URL = (
    "https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/"
    "actions/runs/32137509103"
)
PUBLIC_ISOLATION_CANDIDATE_RUN_ID = "32419343467"
PUBLIC_ISOLATION_CANDIDATE_RUN_URL = (
    "https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/"
    "actions/runs/32419343467"
)
PUBLIC_AGENT_LIFECYCLE_RUN_ID = "32436339541"
PUBLIC_AGENT_LIFECYCLE_RUN_URL = (
    "https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/"
    "actions/runs/32436339541"
)
PUBLIC_AGENT_IMAGE_RUN_ID = "32464814750"
PUBLIC_AGENT_IMAGE_RUN_URL = (
    "https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/"
    "actions/runs/32464814750"
)
PUBLIC_AGENT_OUTER_BOUNDARY_RUN_ID = "32735680163"
PUBLIC_AGENT_OUTER_BOUNDARY_RUN_URL = (
    "https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/"
    "actions/runs/32735680163"
)
SOURCE_PREFLIGHT_WORKFLOW = ".github/workflows/leanflow-source-preflight.yml"
PUBLIC_SOURCE_PREFLIGHT_REPOSITORY = "DakeBU/Auto-Bandit-RL-Proof-In-Sleep"
ANONYMOUS_SOURCE_PREFLIGHT_REPOSITORY = "anonymous/abrl-artifact"
PUBLIC_SOURCE_PREFLIGHT_REPOSITORY_NAME = "Auto-Bandit-RL-Proof-In-Sleep"
ANONYMOUS_SOURCE_PREFLIGHT_REPOSITORY_NAME = "abrl-artifact"
PUBLIC_SOURCE_PREFLIGHT_WORKFLOW_SHA256 = (
    "69cb85f9cb19135890f50bdf5e82fbc80740b0b779162f9abf178824c0961323"
)
SOURCE_PREFLIGHT_ANONYMIZED_FILES = {
    SOURCE_PREFLIGHT_WORKFLOW,
    "evaluation/target-drift-v2/README.md",
    "tools/validate_leanflow_source_preflight.py",
    "tools/test_leanflow_source_preflight.py",
}
PUBLIC_CANDIDATE_RECORD = (
    "evaluation/target-drift-v2/checker-image-candidate-32137509103.json"
)
PUBLIC_ISOLATION_CANDIDATE_RECORD = (
    "evaluation/target-drift-v2/checker-image-candidate-32419343467.json"
)
PUBLIC_AGENT_LIFECYCLE_RECORD = (
    "evaluation/target-drift-v2/agent-lifecycle-candidate-32436339541.json"
)
PUBLIC_AGENT_IMAGE_RECORD = (
    "evaluation/target-drift-v2/agent-image-candidate-32464814750.json"
)
PUBLIC_AGENT_OUTER_BOUNDARY_RECORD = (
    "evaluation/target-drift-v2/agent-outer-boundary-candidate-32735680163.json"
)
TARGET_DRIFT_V2_PROTOCOL = "evaluation/target-drift-v2/protocol.json"
EXTERNAL_COMPARATOR_PLAN = (
    "evaluation/target-drift-v2/external-comparator-plan.json"
)
EXTERNAL_COMPARATOR_SEAL = (
    "evaluation/target-drift-v2/external-comparator-plan.seal.json"
)
LEANFLOW_ADAPTER_CONTRACT = (
    "evaluation/target-drift-v2/leanflow-adapter-contract.json"
)
LEANFLOW_EXTERNAL_SCHEDULE = (
    "evaluation/target-drift-v2/leanflow-external-schedule.json"
)
LEANFLOW_FIXTURE_REQUEST = (
    "evaluation/target-drift-v2/leanflow-excluded-fixture-request.json"
)
LEANFLOW_LEDGER_CONTRACT = (
    "evaluation/target-drift-v2/leanflow-external-completion-ledger-contract.json"
)
LEANFLOW_PLUMBING_SEAL = (
    "evaluation/target-drift-v2/leanflow-external-plumbing.seal.json"
)
LEANFLOW_FAKE_ADAPTER = "tools/fake_leanflow_target_drift_adapter.py"
LEANFLOW_SCHEDULE_BUILDER = "tools/build_leanflow_target_drift_schedule.py"
LEANFLOW_LEDGER_BUILDER = "tools/build_leanflow_target_drift_completion_ledger.py"
ANONYMOUS_CANDIDATE_RECORD = (
    "evaluation/target-drift-v2/checker-image-candidate-record.json"
)
ANONYMOUS_ISOLATION_CANDIDATE_RECORD = (
    "evaluation/target-drift-v2/checker-image-isolation-candidate-record.json"
)
ANONYMOUS_AGENT_LIFECYCLE_RECORD = (
    "evaluation/target-drift-v2/agent-lifecycle-candidate-record.json"
)
ANONYMOUS_AGENT_IMAGE_RECORD = (
    "evaluation/target-drift-v2/agent-image-candidate-record.json"
)
ANONYMOUS_AGENT_OUTER_BOUNDARY_RECORD = (
    "evaluation/target-drift-v2/agent-outer-boundary-candidate-record.json"
)
SOURCE_AUDIT_PUBLIC_BASE_COMMIT = "705dfe1ab1b8e0d318097981a7322336686dd5c8"
SOURCE_AUDIT_PUBLIC_BLOB_IDS = (
    "0537c8e69233b46c27233323815d782962fef392",
    "18181fcdebff02bf840485004a8289cf12e140f9",
)
SOURCE_AUDIT_BASE_MANIFEST = (
    "evaluation/source-contract-audit-v1/pre-amendment/base.json"
)
SOURCE_AUDIT_AMENDMENT = "evaluation/source-contract-audit-v1/amendment.json"
SOURCE_AUDIT_VALIDATOR = "tools/validate_source_contract_audit.py"

DELAYED_IMPLEMENTATION_IDS = (
    "DELAYED-FEEDBACK-SOURCE-ACCOUNTING",
    "DELAYED-FEEDBACK-CAUSAL-PROCESSING",
    "DELAYED-SAPO-ACTIVE-ALLOCATION",
    "DELAYED-SAPO-ELIMINATION-ACTION-LAW",
    "DELAYED-SAPO-GOOD-EVENT-D9-PROJECTION",
    "DELAYED-SAPO-D8-D9-ASSEMBLY",
)
DELAYED_DIAGNOSTIC_ID = "DELAYED-SAPO-D10-D12-GAP-ORDERING-AUDIT"
DELAYED_PROCESSED_PREFIX_ID = "DELAYED-SAPO-D1-ACTIVE-COUNT-WIDTH-PRODUCER"
DELAYED_TRACE_SUMMARY_ID = "DELAYED-SAPO-PROCESSED-TRACE-SUMMARY-ADAPTER"
DELAYED_ORDERED_TRANSITION_ID = "DELAYED-SAPO-ORDERED-NO-SWITCH-PROCESS-ONE"
DELAYED_ORDERED_TRACE_ID = "DELAYED-SAPO-ORDERED-NO-SWITCH-TRACE-ORDERING"
DELAYED_D11_DOMAIN_ID = "DELAYED-SAPO-D11-NONNEGATIVE-GAP-HALF-SET"
DELAYED_LINE10_INITIALIZATION_ID = "DELAYED-SAPO-LINE10-ELIMINATED-ARM-INITIALIZATION"
DELAYED_CENTRAL_ENDPOINT_ID = "NEURIPS-2025-DELAYED-BOBW-CENTRAL-ENDPOINTS"
SUCCINCT_AUDIT_ID = "NEURIPS-2025-SUCCINCT-LOWER-BOUND-GEOMETRY-AUDIT"
SGB_AUDIT_ID = "NEURIPS-2025-STOCHASTIC-GRADIENT-BANDIT-MECHANISM-AUDIT"
SGB_FOLLOW_ON_ID = "NEURIPS-2025-SGB-PHASE-TRANSITION-FOLLOWON"
CH15_SCOPED_ENDPOINT_ID = "TEXTBOOK-PART-IV-CH15-GAUSSIAN-MINIMAX-LOWER-BOUND"
THEOREM_AUDIT_COMPARISON_SOURCE = (
    "research-wiki/papers/theorem-audit-comparison.json"
)
THEOREM_AUDIT_COMPARISON_DESTINATION = "evidence/theorem-audit-comparison.json"
THEOREM_AUDIT_ROW_IDS = (
    "textbook-chapter-15-scoped-positive-control",
    "delayed-bobw-source-frozen-audit",
    "succinct-lower-bound-source-frozen-audit",
    "stochastic-gradient-bandit-source-frozen-audit",
)
SGB_FINITE_ALGEBRA_FILE = "BanditRLProof/Algorithms/StochasticGradientBanditAudit.lean"
SGB_GENERATED_HISTORY_FILE = (
    "BanditRLProof/Algorithms/StochasticGradientBanditTrajectoryAudit.lean"
)
SGB_TWO_ARM_RATE_FILE = (
    "BanditRLProof/Algorithms/StochasticGradientBanditTwoArmRate.lean"
)
SGB_EXPONENTIAL_AUDIT_FILE = (
    "BanditRLProof/Algorithms/StochasticGradientBanditExponentialAudit.lean"
)
SGB_GENERATED_EQUATION_8_FILE = (
    "BanditRLProof/Algorithms/StochasticGradientBanditConditionalExponentialAudit.lean"
)
SGB_SUCCESSOR_RECURRENCE_FILE = (
    "BanditRLProof/Algorithms/StochasticGradientBanditTwoArmRecurrence.lean"
)
SGB_INITIAL_RECURRENCE_FILE = (
    "BanditRLProof/Algorithms/StochasticGradientBanditTwoArmInitialRecurrence.lean"
)
SGB_MEASURABLE_RECURRENCE_FILE = (
    "BanditRLProof/Algorithms/StochasticGradientBanditTwoArmMeasurableRecurrence.lean"
)
SGB_PATH_INTEGRABILITY_FILE = (
    "BanditRLProof/Algorithms/StochasticGradientBanditTwoArmPathIntegrability.lean"
)
SGB_FIXED_IID_FILE = (
    "BanditRLProof/Algorithms/StochasticGradientBanditTwoArmFixedIID.lean"
)
SGB_UNCONDITIONAL_RECURRENCE_FILE = (
    "BanditRLProof/Algorithms/"
    "StochasticGradientBanditTwoArmUnconditionalRecurrence.lean"
)
SGB_THEOREM_ONE_FILE = (
    "BanditRLProof/Algorithms/"
    "StochasticGradientBanditTwoArmTheoremOne.lean"
)
SGB_THEOREM_FOUR_CONTRACT_AUDIT_FILE = (
    "BanditRLProof/Algorithms/"
    "StochasticGradientBanditTheoremFourContractAudit.lean"
)
SGB_COROLLARY_ONE_FILE = (
    "BanditRLProof/Algorithms/StochasticGradientBanditCorollaryOne.lean"
)
SGB_THEOREM_TWO_STARVATION_FILE = (
    "BanditRLProof/Algorithms/"
    "StochasticGradientBanditTheoremTwoStarvation.lean"
)
SGB_THEOREM_TWO_NTH_PULL_FILE = (
    "BanditRLProof/Algorithms/"
    "StochasticGradientBanditTheoremTwoNthPull.lean"
)
SGB_FINITE_ALGEBRA_DECLARATION_COUNT = 26
SGB_GENERATED_HISTORY_DECLARATION_COUNT = 18
SGB_TWO_ARM_RATE_DECLARATION_COUNT = 18
SGB_EXPONENTIAL_AUDIT_DECLARATION_COUNT = 14
SGB_GENERATED_EQUATION_8_DECLARATION_COUNT = 4
SGB_SUCCESSOR_RECURRENCE_DECLARATION_COUNT = 10
SGB_INITIAL_RECURRENCE_DECLARATION_COUNT = 3
SGB_MEASURABLE_RECURRENCE_DECLARATION_COUNT = 25
SGB_PATH_INTEGRABILITY_DECLARATION_COUNT = 19
SGB_FIXED_IID_DECLARATION_COUNT = 9
SGB_UNCONDITIONAL_RECURRENCE_DECLARATION_COUNT = 37
SGB_THEOREM_ONE_DECLARATION_COUNT = 32
SGB_THEOREM_ONE_STACK_DECLARATION_COUNT = 215
SGB_THEOREM_FOUR_CONTRACT_AUDIT_DECLARATION_COUNT = 8
SGB_HISTORICAL_DECLARATION_COUNT = (
    SGB_THEOREM_ONE_STACK_DECLARATION_COUNT
    + SGB_THEOREM_FOUR_CONTRACT_AUDIT_DECLARATION_COUNT
)
SGB_COROLLARY_ONE_DECLARATION_COUNT = 23
SGB_THEOREM_TWO_STARVATION_DECLARATION_COUNT = 18
SGB_THEOREM_TWO_NTH_PULL_DECLARATION_COUNT = 24
SGB_TOTAL_DECLARATION_COUNT = (
    SGB_HISTORICAL_DECLARATION_COUNT
    + SGB_COROLLARY_ONE_DECLARATION_COUNT
    + SGB_THEOREM_TWO_STARVATION_DECLARATION_COUNT
    + SGB_THEOREM_TWO_NTH_PULL_DECLARATION_COUNT
)
SGB_GENERATED_TRAJECTORY_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.trajectoryKernel",
    "BanditRLProof.StochasticGradientBandit.trajectoryMeasure_condDistrib_action_zero_given_environment",
    "BanditRLProof.StochasticGradientBandit.trajectoryMeasure_condDistrib_action",
    "BanditRLProof.StochasticGradientBandit.trajectoryMeasure_condDistrib_nextPair_given_environment_prefix",
})
SGB_CONDITIONAL_LAW_BRIDGE_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.integral_measurableEnvironmentInitialPairKernel_sourceIncrement_eq_expectedSourceIncrement",
    "BanditRLProof.StochasticGradientBandit.integral_historyStepKernel_sourceIncrement_eq_expectedSourceIncrement",
    "BanditRLProof.StochasticGradientBandit.integral_measurableEnvironmentHistoryStepKernel_sourceIncrement_eq_expectedSourceIncrement",
    "BanditRLProof.StochasticGradientBandit.integral_measurableEnvironmentHistoryStepKernel_sourceIncrement_eq_gapCoordinate",
})
SGB_TWO_ARM_RATE_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.historyParameter_sum_eq_initial",
    "BanditRLProof.StochasticGradientBandit.twoArmParameterAt_sum_eq_zero",
    "BanditRLProof.StochasticGradientBandit.twoArmProbabilityAt_zero_div_failure_eq_exp_two_mul",
    "BanditRLProof.StochasticGradientBandit.twoArmProbabilityAt_exp_two_mul_failure_eq_success",
})
SGB_EXPONENTIAL_AUDIT_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.sourceC",
    "BanditRLProof.StochasticGradientBandit.sourceC_terms_summable",
    "BanditRLProof.StochasticGradientBandit.sourceC_mono",
    "BanditRLProof.StochasticGradientBandit.sourceC_le_exp_two_mul",
    "BanditRLProof.StochasticGradientBandit.exp_mul_le_sourceEqEight",
    "BanditRLProof.StochasticGradientBandit.integral_exp_mul_le_sourceEqEight_of_ae_abs_le_one",
})
SGB_GENERATED_EQUATION_8_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.integral_measurableEnvironmentInitialPairKernel_exp_actionReward_le_sourceEqEight_of_mean",
    "BanditRLProof.StochasticGradientBandit.integral_historyStepKernel_exp_actionReward_le_sourceEqEight",
    "BanditRLProof.StochasticGradientBandit.integral_historyStepKernel_exp_actionReward_le_sourceEqEight_of_mean",
    "BanditRLProof.StochasticGradientBandit.integral_measurableEnvironmentHistoryStepKernel_exp_actionReward_le_sourceEqEight_of_mean",
})
SGB_INITIAL_RECURRENCE_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.softmaxProbability_zeroInitialization_finTwo",
    "BanditRLProof.StochasticGradientBandit.integral_twoArmInitialPairKernel_exp_forwardIncrement_le",
    "BanditRLProof.StochasticGradientBandit.integral_twoArmInitialPairKernel_exp_inverseIncrement_le",
})
SGB_SUCCESSOR_RECURRENCE_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.integral_twoArmHistoryStepKernel_exp_forwardSuccessor_le_add_success_sq",
    "BanditRLProof.StochasticGradientBandit.integral_twoArmHistoryStepKernel_exp_inverseSuccessor_le_sub_failure_sq",
})
SGB_TRAJECTORY_COND_DISTRIB_RECURRENCE_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.trajectoryPrefix_condDistrib_integral_forwardSuccessor_le",
    "BanditRLProof.StochasticGradientBandit.trajectoryPrefix_condDistrib_integral_inverseSuccessor_le",
})
SGB_PATH_INTEGRABILITY_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.integrable_measurableTwoArmInitialPairKernel_sourceIncrement_of_contract",
    "BanditRLProof.StochasticGradientBandit.integrable_measurableTwoArmHistoryStepKernel_sourceIncrement_of_contract",
    "BanditRLProof.StochasticGradientBandit.integrable_twoArmForwardTrajectorySuccessorPotential",
    "BanditRLProof.StochasticGradientBandit.integrable_twoArmInverseTrajectorySuccessorPotential",
    "BanditRLProof.StochasticGradientBandit.twoArmForwardTrajectorySuccessor_condExp_ae_eq_integral_condDistrib",
    "BanditRLProof.StochasticGradientBandit.twoArmInverseTrajectorySuccessor_condExp_ae_eq_integral_condDistrib",
})
SGB_CONDITIONAL_RECURRENCE_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.twoArmForwardTrajectorySuccessor_condExp_le_recurrenceBound",
    "BanditRLProof.StochasticGradientBandit.twoArmInverseTrajectorySuccessor_condExp_le_recurrenceBound",
})
SGB_FIXED_IID_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.twoArmFixedIIDRewardKernel",
    "BanditRLProof.StochasticGradientBandit.twoArmFixedIIDRewardKernel_apply",
    "BanditRLProof.StochasticGradientBandit.twoArmFixedIIDRewardKernel_isMarkov",
    "BanditRLProof.StochasticGradientBandit.twoArmFixedIIDEnvironment",
    "BanditRLProof.StochasticGradientBandit.twoArmFixedIIDEnvironment_initialFeedback_apply",
    "BanditRLProof.StochasticGradientBandit.twoArmFixedIIDEnvironment_feedback_apply",
    "BanditRLProof.StochasticGradientBandit.twoArmFixedIIDReward_aestronglyMeasurable",
    "BanditRLProof.StochasticGradientBandit.twoArmFixedIIDEnvironment_contract",
    "BanditRLProof.StochasticGradientBandit.integral_twoArmFixedIIDHistoryStepKernel_sourceIncrement_eq_gapCoordinate",
})
SGB_UNCONDITIONAL_RECURRENCE_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.twoArmTrajectoryParameterZero",
    "BanditRLProof.StochasticGradientBandit.twoArmForwardPotential",
    "BanditRLProof.StochasticGradientBandit.twoArmInversePotential",
    "BanditRLProof.StochasticGradientBandit.twoArmSuccessProbability",
    "BanditRLProof.StochasticGradientBandit.twoArmFailureMass",
    "BanditRLProof.StochasticGradientBandit.twoArmForwardUnconditionalRecurrence",
    "BanditRLProof.StochasticGradientBandit.twoArmInverseUnconditionalRecurrence",
    "BanditRLProof.StochasticGradientBandit.twoArmForwardFiniteIteration",
    "BanditRLProof.StochasticGradientBandit.twoArmInverseFailureMassSqTelescope",
    "BanditRLProof.StochasticGradientBandit.twoArmInverseFailureMassSqSum_le_initial_div",
    "BanditRLProof.StochasticGradientBandit.twoArmForwardInitialUnconditionalRecurrence",
    "BanditRLProof.StochasticGradientBandit.twoArmInverseInitialUnconditionalRecurrence",
    "BanditRLProof.StochasticGradientBandit.twoArmForwardFiniteIteration_from_source_initial",
    "BanditRLProof.StochasticGradientBandit.twoArmFullFailureMassSqSum_le",
})
SGB_THEOREM_ONE_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.twoArmTrajectorySourceIncrement_condExp_ae_eq_successFailure",
    "BanditRLProof.StochasticGradientBandit.integral_twoArmTrajectoryParameterZero_eq_successFailureSum",
    "BanditRLProof.StochasticGradientBandit.twoArmGeneratedExpectedPseudoRegret_eq_parameter_add_failureSq",
    "BanditRLProof.StochasticGradientBandit.integral_twoArmTrajectoryParameterZero_le_source_log_bound",
    "BanditRLProof.StochasticGradientBandit.integral_twoArmSampledPseudoRegret_eq_generated",
    "BanditRLProof.StochasticGradientBandit.twoArmGeneratedExpectedPseudoRegret_le_sourceTheoremOne",
    "BanditRLProof.StochasticGradientBandit.integral_twoArmSampledPseudoRegret_le_sourceTheoremOne",
    "BanditRLProof.StochasticGradientBandit.twoArmFixedIIDDirac_theoremOne",
})
SGB_THEOREM_FOUR_CONTRACT_AUDIT_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.theoremFourStepOneMargin",
    "BanditRLProof.StochasticGradientBandit.theoremFourStepFourSurvivalLowerBound",
    "BanditRLProof.StochasticGradientBandit.theoremFourStepOneMargin_pos",
    "BanditRLProof.StochasticGradientBandit.theoremFourStepFourSurvivalLowerBound_pos",
    "BanditRLProof.StochasticGradientBandit.theoremFourStepFour_survivalMass_ge",
    "BanditRLProof.StochasticGradientBandit.theoremFourStepFour_survivalMass_pos",
    "BanditRLProof.StochasticGradientBandit.theoremFourFiniteGeometricPhaseMass_le_inv",
    "BanditRLProof.StochasticGradientBandit.theoremFourFiniteTransientMass_le_inv",
})
SGB_COROLLARY_ONE_REPRESENTATIVE_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.twoArmSampledPseudoRegret_le_gap_mul_horizon",
    "BanditRLProof.StochasticGradientBandit.sourceTheoremOne_constant_le_inv_eta",
    "BanditRLProof.StochasticGradientBandit.corollaryOne_piecewise_bound",
    "BanditRLProof.StochasticGradientBandit.twoArmFixedIIDDirac_corollaryOne_piecewise",
    "BanditRLProof.StochasticGradientBandit.twoArmFixedIIDDirac_corollaryOne",
})
SGB_THEOREM_TWO_STARVATION_REPRESENTATIVE_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.twoArmStepOneStarvationEvent",
    "BanditRLProof.StochasticGradientBandit.measurableSet_twoArmStepOneStarvationEvent",
    "BanditRLProof.StochasticGradientBandit.twoArmSampledPseudoRegret_eq_gap_mul_horizon_sub_of_optimalPullCount_eq",
    "BanditRLProof.StochasticGradientBandit.twoArmStepOneStarvationEvent_sampledPseudoRegret_eq",
    "BanditRLProof.StochasticGradientBandit.twoArmStepOneStarvationEvent_charge_mul_probability_le_integral",
    "BanditRLProof.StochasticGradientBandit.twoArmFixedIIDStepOneStarvationEvent_charge_mul_probability_le_integral",
})
SGB_THEOREM_TWO_NTH_PULL_REPRESENTATIVE_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.twoArmNthOptimalPullTime",
    "BanditRLProof.StochasticGradientBandit.isStoppingTime_twoArmNthOptimalPullTime",
    "BanditRLProof.StochasticGradientBandit.twoArmNthOptimalPullTime_eq_top_iff",
    "BanditRLProof.StochasticGradientBandit.twoArmNthOptimalPullTime_spec",
    "BanditRLProof.StochasticGradientBandit.measurable_twoArmNthOptimalPullReward",
    "BanditRLProof.StochasticGradientBandit.twoArmNthOptimalPullReward_eq_of_time_eq",
    "BanditRLProof.StochasticGradientBandit.measurable_twoArmNthOptimalPullSuccessProbability",
    "BanditRLProof.StochasticGradientBandit.twoArmNthOptimalPullSuccessProbability_eq_of_time_eq",
})
SGB_THEOREM_TWO_TERMINAL_DECLARATION = (
    "BanditRLProof.StochasticGradientBandit."
    "twoArmRademacherDirac_theoremTwo_polynomialRegret"
)
CH16_COMPILED_ID = "TEXTBOOK-PART-IV-CH16-CONSISTENCY-DINF-DEPENDENCY-SLICE"
CH16_EVENT_REGRET_ID = "TEXTBOOK-PART-IV-CH16-EVENT-REGRET-PRODUCERS"
CH16_TERMINAL_ID = "TEXTBOOK-PART-IV-CH16-SOURCE-TERMINALS"
CH16_COMPILED_DECLARATIONS = frozenset({
    "BanditRLProof.LowerBounds.IsConsistentRegret",
    "BanditRLProof.LowerBounds.IsConsistentPolicyOver",
    "BanditRLProof.LowerBounds.IsConsistentRegret.add",
    "BanditRLProof.LowerBounds.IsConsistentRegret.eventually_add_le_rpow",
    "BanditRLProof.LowerBounds.IsConsistentRegret.eventually_log_add_div_log_le",
    "BanditRLProof.LowerBounds.divergenceInfimum",
    "BanditRLProof.LowerBounds.divergenceInfimum_le",
    "BanditRLProof.LowerBounds.parametricDivergenceInfimum",
    "BanditRLProof.LowerBounds.parametricDivergenceInfimum_le",
    "BanditRLProof.LowerBounds.unitGaussianDivergenceInfimum",
    "BanditRLProof.LowerBounds.unitGaussianDivergenceInfimum_le_perturbed",
    "BanditRLProof.LowerBounds.unitGaussianDivergenceInfimum_ge",
    "BanditRLProof.LowerBounds.unitGaussianDivergenceInfimum_eq",
    "BanditRLProof.LowerBounds.banditHistoryRelativeEntropy_eq_expectedPulls_mul_of_only_arm_changed",
    "BanditRLProof.LowerBounds.oneArmMajorityPullEvent",
    "BanditRLProof.LowerBounds.measurableSet_oneArmMajorityPullEvent",
    "BanditRLProof.LowerBounds.bretagnolleHuberScale_expectedPulls_mul_armKL_le_majorityErrors",
    "BanditRLProof.LowerBounds.bretagnolleHuberScale_mul_eq_exp",
    "BanditRLProof.LowerBounds.exp_testing_bound_of_majority_regret_bounds",
    "BanditRLProof.LowerBounds.expectedPullCount_ge_log_regret_of_exp_testing_bound",
})
CH16_EVENT_REGRET_DECLARATIONS = frozenset({
    "BanditRLProof.LowerBounds.finiteHistoryGapPseudoRegret",
    "BanditRLProof.LowerBounds.canonicalGapExpectedPseudoRegret",
    "BanditRLProof.LowerBounds.measurable_finiteHistoryGapPseudoRegret",
    "BanditRLProof.LowerBounds.finiteHistoryGapPseudoRegret_ne_top",
    "BanditRLProof.LowerBounds.finiteHistoryGapPseudoRegret_toReal",
    "BanditRLProof.LowerBounds.sum_canonicalRealizedExpectedPullCountThrough_general",
    "BanditRLProof.LowerBounds.canonicalRealizedExpectedPullCountThrough_ne_top",
    "BanditRLProof.LowerBounds.canonicalGapExpectedPseudoRegret_eq_sum_expectedPulls",
    "BanditRLProof.LowerBounds.canonicalGapExpectedPseudoRegret_ne_top",
    "BanditRLProof.LowerBounds.canonicalGapExpectedPseudoRegretReal",
    "BanditRLProof.LowerBounds.oneArmMajority_forces_gapPseudoRegret",
    "BanditRLProof.LowerBounds.oneArmMajority_compl_forces_gapPseudoRegret",
    "BanditRLProof.LowerBounds.oneArmMajority_probability_charge_le_expectedPseudoRegret",
    "BanditRLProof.LowerBounds.oneArmMajority_compl_probability_charge_le_expectedPseudoRegret",
    "BanditRLProof.LowerBounds.expectedPullCount_ge_log_gapPseudoRegret_of_only_arm_changed",
})
EXPECTED_INDEX_EXCEPTIONS = ()
SOURCE_RESULT_IDS = (
    "RL-UNBOUNDED-HITTINGAFTER-EXPECTED-UPPER-BOUND",
    "ETC-CANONICAL-SUBGAUSSIAN-REGRET",
    "TEXTBOOK-PART-IV-CH13-BASIC-IDEAS-LEAN-SPINE",
    "TEXTBOOK-PART-IV-THEOREM-13-1-GAUSSIAN-MINIMAX",
    "TEXTBOOK-PART-IV-CH14-INFORMATION-THEORY-LEAN-SPINE",
    "TEXTBOOK-PART-IV-CH15-GAUSSIAN-KL-DEPENDENCY-SLICE",
    "TEXTBOOK-PART-IV-CH15-SAME-POLICY-HISTORY-KL-DECOMPOSITION",
    CH15_SCOPED_ENDPOINT_ID,
    "TEXTBOOK-PART-IV-CH16-CONSISTENCY-DINF-DEPENDENCY-SLICE",
    "TEXTBOOK-PART-IV-CH16-EVENT-REGRET-PRODUCERS",
    "TEXTBOOK-PART-IV-CH16-SOURCE-TERMINALS",
    "TEXTBOOK-PART-IV-CH17-FIRST-MOMENT-AND-TAIL-DEPENDENCY-SLICE",
    "TEXTBOOK-PART-IV-CH17-SOURCE-TERMINALS",
) + DELAYED_IMPLEMENTATION_IDS + (
    DELAYED_DIAGNOSTIC_ID,
    DELAYED_PROCESSED_PREFIX_ID,
    DELAYED_TRACE_SUMMARY_ID,
    DELAYED_ORDERED_TRANSITION_ID,
    DELAYED_ORDERED_TRACE_ID,
    DELAYED_D11_DOMAIN_ID,
    DELAYED_LINE10_INITIALIZATION_ID,
    DELAYED_CENTRAL_ENDPOINT_ID,
    SUCCINCT_AUDIT_ID,
    SGB_AUDIT_ID,
    SGB_FOLLOW_ON_ID,
    "TARGET-DRIFT-V2-CONTROLLED-EVALUATION",
)

TARGET_DRIFT_TOOLS = (
    "tools/analyze_target_drift_execution.py",
    "tools/assemble_target_drift_grades.py",
    "tools/audit_target_drift_wording.py",
    "tools/build_target_drift_completion_ledger.py",
    "tools/check_target_drift_container_controller.py",
    "tools/check_target_drift_inner.py",
    "tools/check_target_drift_run.py",
    "tools/codex_target_drift_adapter.py",
    "tools/fake_target_drift_adapter.py",
    "tools/fake_target_drift_cache_prelude.py",
    "tools/fake_target_drift_checker_sandbox.py",
    "tools/fetch_target_drift_sources.py",
    "tools/export_target_drift_grader_pack.py",
    "tools/finalize_target_drift_config.py",
    "tools/launch_target_drift_checker_container.py",
    "tools/launch_target_drift_agent_container.py",
    "tools/prepare_target_drift_agent_image.py",
    "tools/prepare_target_drift_checker_image.py",
    "tools/prepare_target_drift_checker_probe_config.py",
    "tools/prepare_target_drift_execution.py",
    "tools/prepare_target_drift_grading.py",
    "tools/prepare_target_drift_smoke.py",
    "tools/record_target_drift_agent_image_probe.py",
    "tools/record_target_drift_agent_lifecycle_probe.py",
    "tools/record_target_drift_checker_isolation_probe.py",
    "tools/run_target_drift_execution.py",
    "tools/run_target_drift_schedule.py",
    "tools/run_target_drift_smoke.py",
    "tools/target_drift_checker_cache_manifest.py",
    "tools/target_drift_agent_pid1.py",
    "tools/target_drift_agent_outer_controller.py",
    "tools/target_drift_agent_outer_probe.py",
    "tools/target_drift_agent_model_probe.py",
    "tools/target_drift_agent_excluded_adapter.py",
    "tools/test_target_drift_agent_image.py",
    "tools/test_target_drift_agent_outer_boundary.py",
    "tools/test_target_drift_analysis.py",
    "tools/test_target_drift_agent_lifecycle.py",
    "tools/test_target_drift_completion_ledger.py",
    "tools/test_target_drift_grader_export.py",
    "tools/test_target_drift_grading.py",
    "tools/test_codex_target_drift_adapter.py",
    "tools/test_fetch_target_drift_sources.py",
    "tools/test_target_drift_execution.py",
    "tools/test_target_drift_wording_record.py",
    "tools/test_target_drift_runtime.py",
    "tools/test_target_drift_smoke.py",
    LEANFLOW_SCHEDULE_BUILDER,
    LEANFLOW_LEDGER_BUILDER,
    LEANFLOW_FAKE_ADAPTER,
    "tools/leanflow_target_drift_adapter.py",
    "tools/test_leanflow_target_drift_adapter.py",
    "tools/validate_leanflow_source_preflight.py",
    "tools/test_leanflow_source_preflight.py",
    "tools/test_target_drift_external_comparator.py",
    "tools/validate_target_drift_suite.py",
    "tools/validate_target_drift_suite_v2.py",
    "tools/validate_target_drift_external_comparator.py",
)

# The evaluation layer is result-free by construction.  New tracked files must
# be reviewed and added explicitly so that run records, grades, or analyses can
# never enter the anonymous artifact through a recursive directory copy.
TARGET_DRIFT_PROTOCOL_FILES = (
    "evaluation/target-drift-v1/README.md",
    "evaluation/target-drift-v1/challenges.json",
    "evaluation/target-drift-v1/execution-template.json",
    "evaluation/target-drift-v1/grading-rubric.json",
    "evaluation/target-drift-v1/prompts/abrl.md",
    "evaluation/target-drift-v1/prompts/compile-only.md",
    "evaluation/target-drift-v1/prompts/source-aware-blueprint.md",
    "evaluation/target-drift-v1/protocol.json",
    "evaluation/target-drift-v1/source-files.template.json",
    "evaluation/target-drift-v2/README.md",
    "evaluation/target-drift-v2/adapter-contract.json",
    "evaluation/target-drift-v2/agent-image-sources.json",
    "evaluation/target-drift-v2/agent-image.Containerfile",
    "evaluation/target-drift-v2/agent-codex-native.apparmor",
    "evaluation/target-drift-v2/agent-lifecycle.Containerfile",
    "evaluation/target-drift-v2/agent-sandbox-contract.json",
    "evaluation/target-drift-v2/agent-excluded-execution-contract.json",
    "evaluation/target-drift-v2/agent-excluded-execution-request.json",
    PUBLIC_CANDIDATE_RECORD,
    PUBLIC_ISOLATION_CANDIDATE_RECORD,
    PUBLIC_AGENT_LIFECYCLE_RECORD,
    PUBLIC_AGENT_IMAGE_RECORD,
    PUBLIC_AGENT_OUTER_BOUNDARY_RECORD,
    "evaluation/target-drift-v2/checker-image-sbom.template.json",
    "evaluation/target-drift-v2/checker-image.Containerfile",
    "evaluation/target-drift-v2/checker-isolation-probe.excluded-fixture.json",
    "evaluation/target-drift-v2/checker-isolation-probe.template.json",
    "evaluation/target-drift-v2/checker-sandbox-contract.json",
    "evaluation/target-drift-v2/execution-template.json",
    "evaluation/target-drift-v2/external-comparator-plan.json",
    "evaluation/target-drift-v2/external-comparator-plan.seal.json",
    LEANFLOW_ADAPTER_CONTRACT,
    "evaluation/target-drift-v2/leanflow-real-adapter-contract.json",
    LEANFLOW_EXTERNAL_SCHEDULE,
    LEANFLOW_FIXTURE_REQUEST,
    LEANFLOW_LEDGER_CONTRACT,
    LEANFLOW_PLUMBING_SEAL,
    "evaluation/target-drift-v2/grader-prompt.md",
    "evaluation/target-drift-v2/grading-rubric.json",
    "evaluation/target-drift-v2/missing-run-policy.json",
    "evaluation/target-drift-v2/paired-requirements.json",
    "evaluation/target-drift-v2/protocol.json",
    "evaluation/target-drift-v2/resource-policy.json",
    "evaluation/target-drift-v2/source-files.template.json",
    "evaluation/target-drift-v2/text-only-audit-prompt.md",
    "evaluation/target-drift-v2/wording-negative-control-record.json",
)

TARGET_DRIFT_WORKFLOW_FILES = (
    ".github/workflows/leanflow-source-preflight.yml",
    ".github/workflows/target-drift-agent-image.yml",
    ".github/workflows/target-drift-agent-lifecycle.yml",
)

SOURCE_CONTRACT_AUDIT_FILES = (
    "evaluation/source-contract-audit-v1/README.md",
    "evaluation/source-contract-audit-v1/protocol.json",
    "evaluation/source-contract-audit-v1/reviewer-a.json",
    "evaluation/source-contract-audit-v1/reviewer-b.json",
    "evaluation/source-contract-audit-v1/adjudication.json",
    "evaluation/source-contract-audit-v1/summary.json",
    "evaluation/source-contract-audit-v1/amendment.json",
    "evaluation/source-contract-audit-v1/pre-amendment/base.json",
    "evaluation/source-contract-audit-v1/pre-amendment/target-drift-v1-challenges.json",
    "evaluation/source-contract-audit-v1/pre-amendment/target-drift-v2-paired-requirements.json",
)

SOURCE_CONTRACT_AUDIT_TOOLS = (
    "tools/validate_source_contract_audit.py",
    "tools/test_source_contract_audit.py",
)

EXPLICIT_COPIES = {
    ".gitattributes": ".gitattributes",
    "lean-toolchain": "lean-toolchain",
    "lakefile.lean": "lakefile.lean",
    "lake-manifest.json": "lake-manifest.json",
    "BanditRLProof.lean": "BanditRLProof.lean",
    "Tests.lean": "Tests.lean",
    "tools/ProofGraphExport.lean": "tools/ProofGraphExport.lean",
    "tools/proof_graph_lab.py": "tools/proof_graph_lab.py",
    "tools/test_proof_graph_lab.py": "tools/test_proof_graph_lab.py",
    "artifact/anonymous-supplement/README.md": "README.md",
    "artifact/anonymous-supplement/LICENSE": "LICENSE",
    "artifact/anonymous-supplement/THIRD_PARTY_NOTICES.md": "THIRD_PARTY_NOTICES.md",
    "artifact/anonymous-supplement/verify_artifact.py": "artifact/verify_artifact.py",
    "research-wiki/retrieval-index/local_lean_declarations.json":
        "evidence/local_lean_declarations.json",
    "research-wiki/papers/neurips-2025-delayed-bobw-audit.md":
        "evidence/delayed-feedback-audit.md",
    "proof-obligations/PAPER-AUDIT-NEURIPS-2025-DELAYED-BOBW-FEASIBILITY.md":
        "evidence/delayed-feedback-proof-obligations.md",
    "proof-obligations/PAPER-AUDIT-NEURIPS-2025-SUCCINCT-LOWER-BOUNDS.md":
        "evidence/succinct-lower-bound-proof-obligations.md",
    "proof-obligations/PAPER-AUDIT-NEURIPS-2025-STOCHASTIC-GRADIENT-BANDIT.md":
        "evidence/stochastic-gradient-bandit-proof-obligations.md",
}

EVIDENCE_JSON = {
    THEOREM_AUDIT_COMPARISON_SOURCE:
        THEOREM_AUDIT_COMPARISON_DESTINATION,
    "research-wiki/papers/prospective-audit-2025-freeze.json":
        "evidence/source-freeze.json",
    "research-wiki/proof-graph/benchmark_measurements.json":
        "evidence/proof-graph/historical-local-measurements.json",
    "research-wiki/proof-graph/benchmark_roots.json":
        "evidence/proof-graph/benchmark_roots.json",
    "research-wiki/proof-graph/benchmark_replication.json":
        "evidence/proof-graph/benchmark_replication.json",
    "research-wiki/proof-graph/cng_candidate_evaluation.json":
        "evidence/proof-graph/cng_candidate_evaluation.json",
    "research-wiki/proof-graph/cng_candidate_roots.json":
        "evidence/proof-graph/cng_candidate_roots.json",
    "research-wiki/proof-graph/novelty_audit.json":
        "evidence/proof-graph/novelty_audit.json",
    "research-wiki/proof-graph/proof_cost.schema.json":
        "evidence/proof-graph/proof_cost.schema.json",
}

# These versioned files are duplicated at their authoring-tree paths because
# the shipped proof-graph unit tests deliberately check their cross-file
# contracts in place.  The reader-facing copies above remain the stable
# evidence entrypoints.
PROOF_GRAPH_TEST_EVIDENCE = (
    "research-wiki/proof-graph/benchmark_report.json",
    "research-wiki/proof-graph/benchmark_replication.json",
    "research-wiki/proof-graph/benchmark_roots.json",
    "research-wiki/proof-graph/cng_candidate_evaluation.json",
    "research-wiki/proof-graph/cng_candidate_roots.json",
    "research-wiki/proof-graph/novelty_audit.json",
    "research-wiki/proof-graph/proof_cost.schema.json",
)


def canonical_json(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def is_text_payload_path(rel):
    path = Path(rel)
    return path.name in TEXT_PAYLOAD_NAMES or path.suffix in TEXT_PAYLOAD_SUFFIXES


def canonical_text_bytes(rel, data):
    if not is_text_payload_path(rel):
        return data
    text = data.decode("utf-8")
    return text.replace("\r\n", "\n").replace("\r", "\n").encode("utf-8")


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha256_file(path):
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def require_safe_relative(path):
    pure = Path(path)
    if pure.is_absolute() or ".." in pure.parts or not pure.parts:
        raise ValueError("unsafe archive path: {!r}".format(path))
    return pure.as_posix()


def require_anonymous_bytes(rel, data):
    lowered = data.lower()
    for marker in BLOCKED_BYTES:
        if marker in lowered:
            raise ValueError("identity marker in {}: {}".format(rel, marker.decode("ascii")))
    if WINDOWS_PATH.search(data):
        raise ValueError("absolute Windows path in {}".format(rel))
    if HOST_HOME.search(data):
        raise ValueError("absolute host home path in {}".format(rel))
    if EMAIL.search(data):
        raise ValueError("email address in {}".format(rel))


def sanitize_json(value):
    if isinstance(value, dict):
        cleaned = {}
        for key, item in value.items():
            if key == "dependency_build_root":
                cleaned[key] = "<isolated-build-root>"
            elif key in ("frozen_git_commit", "git_commit"):
                cleaned["frozen_source_snapshot"] = "<anonymous-source-snapshot>"
            else:
                cleaned[key] = sanitize_json(item)
        return cleaned
    if isinstance(value, list):
        return [sanitize_json(item) for item in value]
    return value


def git_tracked_files():
    result = subprocess.run(
        ["git", "ls-files", "-z"],
        cwd=str(REPO_ROOT),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
    )
    return {item.decode("utf-8").replace("\\", "/")
            for item in result.stdout.split(b"\0") if item}


def source_tree_files(tracked):
    files = []
    for prefix in ("BanditRLProof", "Tests"):
        for path in sorted((REPO_ROOT / prefix).rglob("*.lean")):
            rel = path.relative_to(REPO_ROOT).as_posix()
            if rel not in tracked:
                raise ValueError("untracked Lean source under allowlisted tree: " + rel)
            files.append(rel)
    return files


def evaluation_files(tracked):
    allowed = set(TARGET_DRIFT_PROTOCOL_FILES)
    actual = {
        rel for rel in tracked
        if rel.startswith("evaluation/target-drift-v1/")
        or rel.startswith("evaluation/target-drift-v2/")
    }
    missing = sorted(allowed - actual)
    unexpected = sorted(actual - allowed)
    if missing:
        raise ValueError("missing allowlisted evaluation source: " + ", ".join(missing))
    if unexpected:
        raise ValueError(
            "unreviewed evaluation file would enter result-free artifact: "
            + ", ".join(unexpected)
        )
    return sorted(allowed)


def anonymous_base_manifest(payload):
    base_paths = [
        rel for rel in sorted(payload)
        if rel == "BanditRLProof.lean"
        or rel == "Tests.lean"
        or rel in ("lean-toolchain", "lakefile.lean", "lake-manifest.json")
        or rel.startswith("BanditRLProof/")
        or rel.startswith("Tests/")
    ]
    digest = hashlib.sha256()
    rows = []
    for rel in base_paths:
        data = payload[rel]
        item_digest = sha256_bytes(data)
        rows.append({"path": rel, "bytes": len(data), "sha256": item_digest})
        digest.update(rel.encode("utf-8") + b"\0")
        digest.update(item_digest.encode("ascii") + b"\n")
    tree_digest = digest.hexdigest()
    return {
        "schema_version": 1,
        "status": "anonymous-source-snapshot",
        "tree_sha256": tree_digest,
        "schema_compatibility_reference": tree_digest[:40],
        "git_object_database_included": False,
        "materializable_by_target_drift_runner": False,
        "interpretation": (
            "The full digest binds the packaged Lean/test base. The 40-hex reference is only "
            "a schema-compatible anonymous placeholder, not a Git commit object."
        ),
        "files": rows,
    }


def anonymous_agent_image_candidate(candidate, anonymous_reference):
    """Keep only self-contained qualitative evidence from the public CI run.

    Public-run timestamps, durations, image/source digests, and the downloaded
    artifact inventory are useful in the public repository but are unique
    linkage fingerprints in a double-blind archive.  The anonymous supplement
    therefore uses a positive allowlist and retains only claims that can be
    interpreted without locating the public workflow run.
    """
    def require_dict(parent, key):
        value = parent.get(key)
        if not isinstance(value, dict):
            raise ValueError("combined agent-image candidate is missing " + key)
        return value

    def pick(parent, keys, label):
        missing = [key for key in keys if key not in parent]
        if missing:
            raise ValueError(
                "combined agent-image candidate is missing {} fields: {}".format(
                    label, ", ".join(missing)
                )
            )
        return {key: parent[key] for key in keys}

    workflow = require_dict(candidate, "workflow_run")
    public_candidate = require_dict(candidate, "candidate")
    sandbox = require_dict(candidate, "sandbox_probe")
    lifecycle = require_dict(candidate, "lifecycle_probe")
    checks = require_dict(candidate, "hash_chain_checks")
    if not checks or any(type(value) is not bool for value in checks.values()):
        raise ValueError("combined agent-image hash checks must be literal booleans")
    nonclaims = candidate.get("nonclaims")
    if not isinstance(nonclaims, list) or not all(
        isinstance(value, str) for value in nonclaims
    ):
        raise ValueError("combined agent-image nonclaims must be a string list")

    anonymous_candidate = {
        **pick(candidate, ("schema_version", "suite_id", "evidence_type"), "top-level"),
        "recorded_at_utc": "<redacted-public-run-time>",
        "workflow_run": {
            "id": "<redacted-public-run-id>",
            "url": "<redacted-public-run-url>",
            "head_commit": "<anonymous-builder-snapshot>",
            **pick(
                workflow,
                ("conclusion", "artifact_retention_days"),
                "workflow",
            ),
            "job_duration": "<redacted-public-run-duration>",
        },
        "candidate": {
            **pick(
                public_candidate,
                (
                    "status",
                    "published",
                    "codex_version",
                    "toolchain_release",
                    "lean_version",
                    "lake_version",
                    "offline_toolchain_probe",
                    "runtime",
                    "apparmor_profile",
                ),
                "candidate",
            ),
            "workspace_base_commit": anonymous_reference,
        },
        "sandbox_probe": pick(
            sandbox,
            (
                "status",
                "workspace_write_succeeded",
                "persistent_outside_workspace_write_denied",
                "provider_auth_unreadable",
                "openai_api_key_absent",
                "outer_same_ipv4_endpoint_reachable",
                "inner_network_denied",
                "inner_network_denial_stage",
                "inner_network_errno",
                "inner_network_error_name",
                "fresh_pid_namespace",
                "observed_apparmor_profile",
                "observed_apparmor_mode",
                "apparmor_profile_attached",
            ),
            "sandbox probe",
        ),
        "lifecycle_probe": pick(
            lifecycle,
            (
                "status",
                "controller_pid",
                "pre_crash_heartbeat_observations",
                "post_cleanup_heartbeat_observation",
                "escaped_descendant_heartbeat_frozen",
                "container_absent_after_control_loss",
                "controller_exit_reason",
                "direct_child_return_code",
            ),
            "lifecycle probe",
        ),
        "hash_chain_checks": dict(checks),
        "nonclaims": list(nonclaims),
    }
    return anonymous_candidate


def anonymous_agent_outer_boundary_candidate(candidate, anonymous_reference):
    """Retain qualitative fake-only evidence without public-run fingerprints."""
    def require_dict(parent, key):
        value = parent.get(key)
        if not isinstance(value, dict):
            raise ValueError("agent outer-boundary candidate is missing " + key)
        return value

    def pick(parent, keys, label):
        missing = [key for key in keys if key not in parent]
        if missing:
            raise ValueError(
                "agent outer-boundary candidate is missing {} fields: {}".format(
                    label, ", ".join(missing)
                )
            )
        return {key: parent[key] for key in keys}

    workflow = require_dict(candidate, "workflow_run")
    checkout = require_dict(candidate, "probe_checkout")
    public_candidate = require_dict(candidate, "candidate")
    cross_probe = require_dict(candidate, "cross_probe_bindings")
    outer = require_dict(candidate, "outer_boundary_component")
    control = require_dict(outer, "control_evidence")
    fake_handoff = require_dict(outer, "trusted_client_fake_auth_handoff")
    worker = require_dict(outer, "worker_boundary")
    nested = require_dict(outer, "nested_codex_sandbox_observation")
    pid1 = require_dict(outer, "pid1_observation")
    checks = require_dict(candidate, "hash_chain_checks")
    if not checks or any(type(value) is not bool for value in checks.values()):
        raise ValueError("agent outer-boundary hash checks must be literal booleans")
    if not all(checks.values()):
        raise ValueError("agent outer-boundary hash checks must all pass")
    nonclaims = candidate.get("nonclaims")
    if not isinstance(nonclaims, list) or not all(
        isinstance(value, str) for value in nonclaims
    ):
        raise ValueError("agent outer-boundary nonclaims must be a string list")
    artifacts = candidate.get("artifacts")
    if not isinstance(artifacts, list) or len(artifacts) != 29:
        raise ValueError("agent outer-boundary artifact inventory must have 29 files")
    source_bindings = candidate.get("source_bindings")
    expected_source_binding_paths = (
        ".github/workflows/target-drift-agent-image.yml",
        "evaluation/target-drift-v2/agent-codex-native.apparmor",
        "evaluation/target-drift-v2/agent-image-sources.json",
        "evaluation/target-drift-v2/agent-image.Containerfile",
        "evaluation/target-drift-v2/agent-sandbox-contract.json",
        "tools/codex_target_drift_adapter.py",
        "tools/prepare_target_drift_agent_image.py",
        "tools/target_drift_agent_pid1.py",
        "tools/target_drift_agent_model_probe.py",
        "tools/target_drift_agent_outer_controller.py",
        "tools/target_drift_agent_outer_probe.py",
        "tools/launch_target_drift_agent_container.py",
        "tools/record_target_drift_agent_image_probe.py",
        "tools/record_target_drift_agent_lifecycle_probe.py",
    )
    if not isinstance(source_bindings, list) or tuple(
        item.get("path") if isinstance(item, dict) else None
        for item in source_bindings
    ) != expected_source_binding_paths:
        raise ValueError("agent outer-boundary source bindings must match 14 reviewed files")
    if workflow.get("conclusion") != "success":
        raise ValueError("agent outer-boundary workflow must have succeeded")
    expected_false_candidate_flags = (
        "published",
        "production_sealed",
        "provider_credential_used",
        "provider_request_or_model_invocation_occurred",
    )
    if any(public_candidate.get(key) is not False
           for key in expected_false_candidate_flags):
        raise ValueError(
            "agent outer-boundary record must remain unpublished, unsealed, and provider-free"
        )
    control_files = control.get("files")
    expected_control_files = (
        "controller-report.json",
        "pid1-exit.json",
        "pid1-ready.json",
        "root-only-sentinel",
    )
    if not isinstance(control_files, list) or tuple(
        item.get("path") if isinstance(item, dict) else None
        for item in control_files
    ) != expected_control_files:
        raise ValueError("agent outer-boundary control inventory changed")

    return {
        **pick(candidate, ("schema_version", "suite_id", "evidence_type"), "top-level"),
        "recorded_at_utc": "<redacted-public-run-time>",
        "workflow_run": {
            "id": "<redacted-public-run-id>",
            "url": "<redacted-public-run-url>",
            "head_commit": "<anonymous-builder-snapshot>",
            **pick(
                workflow,
                ("event", "conclusion", "artifact_retention_days"),
                "workflow",
            ),
            "job_duration": "<redacted-public-run-duration>",
        },
        "probe_checkout": {
            "pull_request_merge_commit": "<redacted-public-probe-commit>",
            "pull_request_head_commit": "<anonymous-builder-snapshot>",
            "pull_request_merge_tree": "<redacted-public-tree>",
            "pull_request_head_tree": "<redacted-public-tree>",
            **pick(checkout, ("trees_identical", "interpretation"), "probe checkout"),
        },
        "candidate": {
            **pick(
                public_candidate,
                (
                    "status",
                    "codex_version",
                    "toolchain_release",
                    "published",
                    "production_sealed",
                    "provider_credential_used",
                    "provider_request_or_model_invocation_occurred",
                ),
                "candidate",
            ),
            "workspace_base_commit": anonymous_reference,
        },
        "cross_probe_bindings": pick(
            cross_probe,
            (
                "same_container_image_across_sbom_isolation_outer_and_lifecycle",
                "offline_isolation_status",
                "outer_launcher_status",
                "destructive_lifecycle_status",
            ),
            "cross-probe bindings",
        ),
        "outer_boundary_component": {
            **pick(outer, ("status",), "outer boundary"),
            "control_evidence": {
                **pick(
                    control,
                    ("expected_file_count", "observed_file_count", "exact_expected_files"),
                    "control evidence",
                ),
                "files": [{"path": item["path"]} for item in control_files],
            },
            "trusted_client_fake_auth_handoff": pick(
                fake_handoff,
                (
                    "fixed_fake_sentinel_only",
                    "bytes",
                    "read_only_descriptor",
                    "trusted_worker_consumed_fixed_fake_auth",
                    "descriptor_closed_before_sandbox",
                    "environment_marker_removed_before_sandbox",
                ),
                "fake-auth handoff",
            ),
            "worker_boundary": pick(
                worker, ("uid", "gid", "effective_capabilities_hex"), "worker boundary"
            ),
            "nested_codex_sandbox_observation": pick(
                nested,
                (
                    "uid",
                    "gid",
                    "effective_capabilities_hex",
                    "outer_auth_mount_unreadable",
                    "outer_auth_mount_read_errno",
                    "outer_auth_mount_read_error_name",
                    "root_control_output_unreadable",
                    "root_control_output_read_errno",
                    "root_control_output_read_error_name",
                    "trusted_auth_fd_env_absent",
                    "trusted_auth_fd_target_absent",
                    "network_denied",
                    "network_errno",
                    "network_error_name",
                    "copied_agent_input_readable",
                    "read_only_agent_input_immutable",
                    "workspace_write_succeeded",
                ),
                "nested sandbox observation",
            ),
            "pid1_observation": pick(
                pid1,
                (
                    "controller_pid",
                    "control_channel",
                    "exit_reason",
                    "child_return_code",
                    "container_log_bytes",
                    "interpreter_shutdown_fatal_absent_from_captured_log",
                ),
                "PID-1 observation",
            ),
        },
        "hash_chain_checks": dict(checks),
        "nonclaims": list(nonclaims),
    }


def anonymous_checker_image_candidate(candidate, anonymous_reference):
    """Remove public-run linkage fields from a checker-image candidate record."""
    workflow = candidate.get("workflow_run")
    public_candidate = candidate.get("candidate")
    checks = candidate.get("hash_chain_checks")
    nonclaims = candidate.get("nonclaims")
    if not isinstance(workflow, dict) or not isinstance(public_candidate, dict):
        raise ValueError("checker-image candidate structure changed")
    if not isinstance(checks, dict) or not checks or any(
        type(value) is not bool for value in checks.values()
    ):
        raise ValueError("checker-image hash checks must be literal booleans")
    if not isinstance(nonclaims, list) or not all(
        isinstance(value, str) for value in nonclaims
    ):
        raise ValueError("checker-image nonclaims must be a string list")

    def pick(parent, keys, label):
        missing = [key for key in keys if key not in parent]
        if missing:
            raise ValueError(
                "checker-image candidate is missing {} fields: {}".format(
                    label, ", ".join(missing)
                )
            )
        return {key: parent[key] for key in keys}

    candidate_fields = (
        "status",
        "published",
        "toolchain_release",
        "lean_version",
        "lake_version",
        "offline_toolchain_probe",
        "worker_uid",
    )
    result = {
        **pick(candidate, ("schema_version", "suite_id", "evidence_type"), "top-level"),
        "recorded_at_utc": "<redacted-public-run-time>",
        "workflow_run": {
            "id": "<redacted-public-run-id>",
            "url": "<redacted-public-run-url>",
            "head_commit": "<anonymous-builder-snapshot>",
            **pick(
                workflow,
                ("conclusion", "artifact_retention_days"),
                "workflow",
            ),
            "job_duration": "<redacted-public-run-duration>",
        },
        "candidate": {
            **pick(public_candidate, candidate_fields, "candidate"),
            "workspace_base_commit": anonymous_reference,
        },
        "hash_chain_checks": dict(checks),
        "nonclaims": list(nonclaims),
    }
    isolation = candidate.get("isolation_probes")
    if isolation is not None:
        if not isinstance(isolation, dict) or not isolation or any(
            type(value) is not bool for value in isolation.values()
        ):
            raise ValueError("checker isolation probes must be literal booleans")
        result["candidate"].update(pick(
            public_candidate,
            ("worker_effective_capabilities_hex", "runtime"),
            "isolation candidate",
        ))
        result["isolation_probes"] = dict(isolation)
    return result


def anonymous_agent_lifecycle_candidate(candidate):
    """Retain the lifecycle result without its public workflow fingerprint."""
    workflow = candidate.get("workflow_run")
    public_candidate = candidate.get("candidate")
    runtime = candidate.get("runtime")
    checks = candidate.get("hash_chain_checks")
    nonclaims = candidate.get("nonclaims")
    if not all(isinstance(value, dict) for value in (
        workflow, public_candidate, runtime, checks
    )):
        raise ValueError("agent lifecycle candidate structure changed")
    if not checks or any(type(value) is not bool for value in checks.values()):
        raise ValueError("agent lifecycle hash checks must be literal booleans")
    if not isinstance(nonclaims, list) or not all(
        isinstance(value, str) for value in nonclaims
    ):
        raise ValueError("agent lifecycle nonclaims must be a string list")

    def pick(parent, keys, label):
        missing = [key for key in keys if key not in parent]
        if missing:
            raise ValueError(
                "agent lifecycle candidate is missing {} fields: {}".format(
                    label, ", ".join(missing)
                )
            )
        return {key: parent[key] for key in keys}

    return {
        **pick(candidate, ("schema_version", "suite_id", "evidence_type"), "top-level"),
        "recorded_at_utc": "<redacted-public-run-time>",
        "workflow_run": {
            "id": "<redacted-public-run-id>",
            "url": "<redacted-public-run-url>",
            "head_commit": "<anonymous-builder-snapshot>",
            **pick(
                workflow,
                ("conclusion", "artifact_retention_days"),
                "workflow",
            ),
            "job_duration": "<redacted-public-run-duration>",
        },
        "candidate": pick(
            public_candidate,
            (
                "status",
                "published",
                "controller_pid",
                "control_loss_reason",
                "direct_child_return_code",
                "pre_crash_heartbeat_observations",
                "post_cleanup_heartbeat_observation",
                "escaped_descendant_heartbeat_frozen",
                "container_absent_after_control_loss",
            ),
            "candidate",
        ),
        "runtime": pick(
            runtime,
            (
                "client_version",
                "server_version",
                "server_os",
                "storage_driver",
                "security_options",
            ),
            "runtime",
        ),
        "hash_chain_checks": dict(checks),
        "nonclaims": list(nonclaims),
    }


def anonymous_source_preflight_workflow():
    path = REPO_ROOT / SOURCE_PREFLIGHT_WORKFLOW
    if not path.is_file() or path.is_symlink():
        raise ValueError("source-preflight workflow is missing or not regular")
    public_data = canonical_text_bytes(SOURCE_PREFLIGHT_WORKFLOW, path.read_bytes())
    if sha256_bytes(public_data) != PUBLIC_SOURCE_PREFLIGHT_WORKFLOW_SHA256:
        raise ValueError("public source-preflight workflow SHA-256 changed")
    public_text = public_data.decode("utf-8")
    if PUBLIC_SOURCE_PREFLIGHT_REPOSITORY not in public_text:
        raise ValueError("public source-preflight repository binding is missing")
    anonymous_text = public_text.replace(
        PUBLIC_SOURCE_PREFLIGHT_REPOSITORY,
        ANONYMOUS_SOURCE_PREFLIGHT_REPOSITORY,
    )
    anonymous_text = anonymous_text.replace(
        PUBLIC_SOURCE_PREFLIGHT_REPOSITORY_NAME,
        ANONYMOUS_SOURCE_PREFLIGHT_REPOSITORY_NAME,
    )
    anonymous_data = anonymous_text.encode("utf-8")
    return anonymous_data, sha256_bytes(anonymous_data)


def anonymize_evaluation_bytes(rel, data, anonymous_reference):
    if not rel.endswith((".json", ".md", ".py", ".yml", ".Containerfile")):
        return data
    # Normalize before matching the guarded redaction blocks.  add_payload
    # applies the same canonicalization to every allowlisted text artifact.
    text = canonical_text_bytes(rel, data).decode("utf-8")
    if (
        rel in SOURCE_PREFLIGHT_ANONYMIZED_FILES
        and rel != "evaluation/target-drift-v2/README.md"
    ):
        anonymous_workflow, anonymous_workflow_sha256 = (
            anonymous_source_preflight_workflow()
        )
        if rel == SOURCE_PREFLIGHT_WORKFLOW:
            text = anonymous_workflow.decode("utf-8")
        else:
            text = text.replace(
                PUBLIC_SOURCE_PREFLIGHT_REPOSITORY,
                ANONYMOUS_SOURCE_PREFLIGHT_REPOSITORY,
            )
            text = text.replace(
                PUBLIC_SOURCE_PREFLIGHT_REPOSITORY_NAME,
                ANONYMOUS_SOURCE_PREFLIGHT_REPOSITORY_NAME,
            )
            text = text.replace(
                PUBLIC_SOURCE_PREFLIGHT_WORKFLOW_SHA256,
                anonymous_workflow_sha256,
            )
    if rel == "evaluation/target-drift-v2/README.md":
        source_block = (
            "The protocol requires every future evaluated workspace to be built from commit\n"
            "`{}`, the public base immediately\n"
            "before the source-frozen paper audit and challenge artifacts.  This prevents\n"
            "the common Lean tree or the ABRL overlay from containing case-specific audit\n"
            "answers.  The compile-only and source-aware conditions use an explicit core\n"
            "allowlist; the ABRL condition uses the same base with `evaluation/` removed."
        ).format(PUBLIC_WORKSPACE_BASE_COMMIT)
        anonymous_block = (
            "The formal protocol requires a production Git base that predates the\n"
            "source-frozen audit and challenge artifacts.  That repository identifier is\n"
            "redacted here.  The 40-hex value in packaged machine fields is a non-Git\n"
            "placeholder derived from the anonymous source-tree digest; this archive has\n"
            "no Git object database and cannot materialize the preregistered workspaces.\n"
            "The three condition definitions are retained only for protocol inspection."
        )
        if source_block not in text:
            raise ValueError("target-drift README base-commit paragraph changed")
        text = text.replace(source_block, anonymous_block)
        text = text.replace(
            "GitHub Actions [run {}]({})".format(
                PUBLIC_CANDIDATE_RUN_ID, PUBLIC_CANDIDATE_RUN_URL
            ),
            "A public result-free CI candidate build (run metadata redacted)",
        )
        text = text.replace(
            "checker-image-candidate-32137509103.json",
            "checker-image-candidate-record.json",
        )
        text = text.replace(
            "GitHub Actions [run {}]({})".format(
                PUBLIC_ISOLATION_CANDIDATE_RUN_ID,
                PUBLIC_ISOLATION_CANDIDATE_RUN_URL,
            ),
            "A public result-free candidate build and isolation run "
            "(run metadata redacted)",
        )
        text = text.replace(
            "checker-image-candidate-32419343467.json",
            "checker-image-isolation-candidate-record.json",
        )
        text = text.replace(
            "GitHub Actions [run {}]({})".format(
                PUBLIC_AGENT_LIFECYCLE_RUN_ID,
                PUBLIC_AGENT_LIFECYCLE_RUN_URL,
            ),
            "A public result-free agent lifecycle candidate run "
            "(run metadata redacted)",
        )
        text = text.replace(
            "agent-lifecycle-candidate-32436339541.json",
            "agent-lifecycle-candidate-record.json",
        )
        text = text.replace(
            "[run {}]({})".format(
                PUBLIC_AGENT_IMAGE_RUN_ID, PUBLIC_AGENT_IMAGE_RUN_URL,
            ),
            "a public result-free combined agent-image run "
            "(run metadata redacted)",
        )
        text = text.replace(
            "agent-image-candidate-32464814750.json",
            "agent-image-candidate-record.json",
        )
        text = text.replace(
            "[run {}]({})".format(
                PUBLIC_AGENT_OUTER_BOUNDARY_RUN_ID,
                PUBLIC_AGENT_OUTER_BOUNDARY_RUN_URL,
            ),
            "a public result-free fake-only outer-boundary component run "
            "(run metadata redacted)",
        )
        text = text.replace(
            "agent-outer-boundary-candidate-32735680163.json",
            "agent-outer-boundary-candidate-record.json",
        )
        # Rebind the new source-preflight prose only after the older public CI
        # run links above have been matched and redacted.  Rebinding the public
        # repository slug first would mutate those URLs and bypass their exact
        # redaction guards.
        anonymous_workflow, anonymous_workflow_sha256 = (
            anonymous_source_preflight_workflow()
        )
        text = text.replace(
            PUBLIC_SOURCE_PREFLIGHT_REPOSITORY,
            ANONYMOUS_SOURCE_PREFLIGHT_REPOSITORY,
        )
        text = text.replace(
            PUBLIC_SOURCE_PREFLIGHT_REPOSITORY_NAME,
            ANONYMOUS_SOURCE_PREFLIGHT_REPOSITORY_NAME,
        )
        text = text.replace(
            PUBLIC_SOURCE_PREFLIGHT_WORKFLOW_SHA256,
            anonymous_workflow_sha256,
        )
    candidate_records = {
        PUBLIC_CANDIDATE_RECORD: (
            PUBLIC_CANDIDATE_RUN_ID, PUBLIC_CANDIDATE_RUN_URL,
        ),
        PUBLIC_ISOLATION_CANDIDATE_RECORD: (
            PUBLIC_ISOLATION_CANDIDATE_RUN_ID,
            PUBLIC_ISOLATION_CANDIDATE_RUN_URL,
        ),
        PUBLIC_AGENT_LIFECYCLE_RECORD: (
            PUBLIC_AGENT_LIFECYCLE_RUN_ID, PUBLIC_AGENT_LIFECYCLE_RUN_URL,
        ),
        PUBLIC_AGENT_IMAGE_RECORD: (
            PUBLIC_AGENT_IMAGE_RUN_ID, PUBLIC_AGENT_IMAGE_RUN_URL,
        ),
        PUBLIC_AGENT_OUTER_BOUNDARY_RECORD: (
            PUBLIC_AGENT_OUTER_BOUNDARY_RUN_ID,
            PUBLIC_AGENT_OUTER_BOUNDARY_RUN_URL,
        ),
    }
    if rel in candidate_records:
        candidate = json.loads(text)
        workflow_run = candidate.get("workflow_run")
        if not isinstance(workflow_run, dict):
            raise ValueError("candidate build record is missing workflow metadata")
        expected_run_id, expected_run_url = candidate_records[rel]
        if str(workflow_run.get("id")) != expected_run_id:
            raise ValueError("candidate build run identifier changed")
        if workflow_run.get("url") != expected_run_url:
            raise ValueError("candidate build run URL changed")
        if rel in (PUBLIC_CANDIDATE_RECORD, PUBLIC_ISOLATION_CANDIDATE_RECORD):
            candidate = anonymous_checker_image_candidate(
                candidate, anonymous_reference
            )
        elif rel == PUBLIC_AGENT_LIFECYCLE_RECORD:
            candidate = anonymous_agent_lifecycle_candidate(candidate)
        elif rel == PUBLIC_AGENT_IMAGE_RECORD:
            candidate = anonymous_agent_image_candidate(
                candidate, anonymous_reference
            )
        elif rel == PUBLIC_AGENT_OUTER_BOUNDARY_RECORD:
            candidate = anonymous_agent_outer_boundary_candidate(
                candidate, anonymous_reference
            )
        text = canonical_json(candidate).decode("utf-8")
    text = text.replace(PUBLIC_WORKSPACE_BASE_COMMIT, anonymous_reference)
    return text.encode("utf-8")


def rebind_anonymous_external_comparator(payload):
    """Bind comparator plans and result-free plumbing to packaged bytes."""
    required = (
        TARGET_DRIFT_V2_PROTOCOL,
        EXTERNAL_COMPARATOR_PLAN,
        EXTERNAL_COMPARATOR_SEAL,
        LEANFLOW_ADAPTER_CONTRACT,
        LEANFLOW_EXTERNAL_SCHEDULE,
        LEANFLOW_FIXTURE_REQUEST,
        LEANFLOW_LEDGER_CONTRACT,
        LEANFLOW_PLUMBING_SEAL,
        LEANFLOW_FAKE_ADAPTER,
        LEANFLOW_SCHEDULE_BUILDER,
        LEANFLOW_LEDGER_BUILDER,
        "evaluation/target-drift-v1/challenges.json",
        "evaluation/target-drift-v2/paired-requirements.json",
    )
    missing = [rel for rel in required if rel not in payload]
    if missing:
        raise ValueError(
            "anonymous comparator rebinding is missing: " + ", ".join(missing)
        )

    source_protocol_sha = sha256_bytes(canonical_text_bytes(
        TARGET_DRIFT_V2_PROTOCOL, read_regular(TARGET_DRIFT_V2_PROTOCOL)
    ))
    source_plan_sha = sha256_bytes(canonical_text_bytes(
        EXTERNAL_COMPARATOR_PLAN, read_regular(EXTERNAL_COMPARATOR_PLAN)
    ))
    packaged_protocol_sha = sha256_bytes(payload[TARGET_DRIFT_V2_PROTOCOL])
    plan = json.loads(payload[EXTERNAL_COMPARATOR_PLAN].decode("utf-8"))
    if (
        plan.get("primary_protocol") != TARGET_DRIFT_V2_PROTOCOL
        or plan.get("primary_protocol_sha256") != source_protocol_sha
        or plan.get("primary_outcomes_observed_at_freeze") is not False
        or plan.get("comparator_outcomes_observed_at_freeze") is not False
    ):
        raise ValueError("source external-comparator plan binding changed")
    plan["primary_protocol_sha256"] = packaged_protocol_sha
    plan_data = canonical_json(plan)
    require_anonymous_bytes(EXTERNAL_COMPARATOR_PLAN, plan_data)
    payload[EXTERNAL_COMPARATOR_PLAN] = plan_data

    seal = json.loads(payload[EXTERNAL_COMPARATOR_SEAL].decode("utf-8"))
    if (
        seal.get("plan_path") != EXTERNAL_COMPARATOR_PLAN
        or seal.get("primary_protocol_path") != TARGET_DRIFT_V2_PROTOCOL
        or seal.get("plan_sha256") != source_plan_sha
        or seal.get("primary_protocol_sha256") != source_protocol_sha
        or seal.get("primary_outcomes_observed_at_seal") is not False
        or seal.get("comparator_outcomes_observed_at_seal") is not False
    ):
        raise ValueError("source external-comparator seal binding changed")
    seal["plan_sha256"] = sha256_bytes(plan_data)
    seal["primary_protocol_sha256"] = packaged_protocol_sha
    seal_data = canonical_json(seal)
    require_anonymous_bytes(EXTERNAL_COMPARATOR_SEAL, seal_data)
    payload[EXTERNAL_COMPARATOR_SEAL] = seal_data

    source_schedule_sha = sha256_file(REPO_ROOT / LEANFLOW_EXTERNAL_SCHEDULE)
    source_challenges_sha = sha256_file(
        REPO_ROOT / "evaluation/target-drift-v1/challenges.json"
    )
    source_paired_sha = sha256_file(
        REPO_ROOT / "evaluation/target-drift-v2/paired-requirements.json"
    )
    schedule = json.loads(payload[LEANFLOW_EXTERNAL_SCHEDULE].decode("utf-8"))
    if (
        schedule.get("external_comparator_plan_sha256") != source_plan_sha
        or schedule.get("challenge_manifest_sha256") != source_challenges_sha
        or schedule.get("paired_requirements_sha256") != source_paired_sha
        or schedule.get("outcomes_observed") is not False
        or schedule.get("provider_execution_enabled") is not False
        or schedule.get("planned_run_count") != 30
    ):
        raise ValueError("source LeanFlow schedule binding changed")
    schedule["external_comparator_plan_sha256"] = sha256_bytes(plan_data)
    schedule["challenge_manifest_sha256"] = sha256_bytes(
        payload["evaluation/target-drift-v1/challenges.json"]
    )
    schedule["paired_requirements_sha256"] = sha256_bytes(
        payload["evaluation/target-drift-v2/paired-requirements.json"]
    )
    schedule_data = canonical_json(schedule)
    require_anonymous_bytes(LEANFLOW_EXTERNAL_SCHEDULE, schedule_data)
    payload[LEANFLOW_EXTERNAL_SCHEDULE] = schedule_data

    source_contract_sha = sha256_file(REPO_ROOT / LEANFLOW_ADAPTER_CONTRACT)
    source_fixture_adapter_sha = sha256_file(REPO_ROOT / LEANFLOW_FAKE_ADAPTER)
    contract = json.loads(payload[LEANFLOW_ADAPTER_CONTRACT].decode("utf-8"))
    if (
        contract.get("external_comparator_plan_sha256") != source_plan_sha
        or contract.get("schedule_sha256") != source_schedule_sha
        or contract.get("fixture_entrypoint_sha256") != source_fixture_adapter_sha
        or contract.get("status") != "provider_disabled_result_free_fixture_only"
    ):
        raise ValueError("source LeanFlow adapter-contract binding changed")
    contract["external_comparator_plan_sha256"] = sha256_bytes(plan_data)
    contract["schedule_sha256"] = sha256_bytes(schedule_data)
    contract["fixture_entrypoint_sha256"] = sha256_bytes(
        payload[LEANFLOW_FAKE_ADAPTER]
    )
    contract_data = canonical_json(contract)
    require_anonymous_bytes(LEANFLOW_ADAPTER_CONTRACT, contract_data)
    payload[LEANFLOW_ADAPTER_CONTRACT] = contract_data

    source_fixture_request_sha = sha256_file(REPO_ROOT / LEANFLOW_FIXTURE_REQUEST)
    fixture_request = json.loads(payload[LEANFLOW_FIXTURE_REQUEST].decode("utf-8"))
    if (
        fixture_request.get("schedule_sha256") != source_schedule_sha
        or fixture_request.get("adapter_contract_sha256") != source_contract_sha
        or fixture_request.get("provider_mode") != "disabled"
        or fixture_request.get("model_invocations_allowed") != 0
        or fixture_request.get("result_eligible") is not False
    ):
        raise ValueError("source LeanFlow fixture-request binding changed")
    packaged_schedule_sha = sha256_bytes(schedule_data)
    fixture_request["schedule_sha256"] = packaged_schedule_sha
    fixture_request["adapter_contract_sha256"] = sha256_bytes(contract_data)
    fixture_request["opaque_run_id"] = sha256_bytes((
        "leanflow-excluded-fixture:{}:{}".format(
            packaged_schedule_sha, fixture_request["semantic_run_id"]
        )
    ).encode("utf-8"))
    fixture_request_data = canonical_json(fixture_request)
    require_anonymous_bytes(LEANFLOW_FIXTURE_REQUEST, fixture_request_data)
    payload[LEANFLOW_FIXTURE_REQUEST] = fixture_request_data

    source_ledger_contract_sha = sha256_file(REPO_ROOT / LEANFLOW_LEDGER_CONTRACT)
    source_ledger_builder_sha = sha256_file(REPO_ROOT / LEANFLOW_LEDGER_BUILDER)
    ledger_contract = json.loads(payload[LEANFLOW_LEDGER_CONTRACT].decode("utf-8"))
    if (
        ledger_contract.get("schedule_sha256") != source_schedule_sha
        or ledger_contract.get("builder_sha256") != source_ledger_builder_sha
        or ledger_contract.get("status") != "schema_frozen_results_absent"
        or ledger_contract.get("results_must_be_absent") is not True
    ):
        raise ValueError("source LeanFlow completion-ledger binding changed")
    ledger_contract["schedule_sha256"] = packaged_schedule_sha
    ledger_contract["builder_sha256"] = sha256_bytes(payload[LEANFLOW_LEDGER_BUILDER])
    ledger_contract_data = canonical_json(ledger_contract)
    require_anonymous_bytes(LEANFLOW_LEDGER_CONTRACT, ledger_contract_data)
    payload[LEANFLOW_LEDGER_CONTRACT] = ledger_contract_data

    source_plumbing_seal = json.loads(
        canonical_text_bytes(
            LEANFLOW_PLUMBING_SEAL, read_regular(LEANFLOW_PLUMBING_SEAL)
        ).decode("utf-8")
    )
    expected_source_bindings = {
        "external_comparator_plan_sha256": source_plan_sha,
        "adapter_contract_sha256": source_contract_sha,
        "schedule_sha256": source_schedule_sha,
        "fixture_request_sha256": source_fixture_request_sha,
        "completion_ledger_contract_sha256": source_ledger_contract_sha,
        "fixture_entrypoint_sha256": source_fixture_adapter_sha,
        "schedule_builder_sha256": sha256_file(REPO_ROOT / LEANFLOW_SCHEDULE_BUILDER),
        "completion_ledger_builder_sha256": source_ledger_builder_sha,
    }
    if (
        any(source_plumbing_seal.get(key) != value
            for key, value in expected_source_bindings.items())
        or source_plumbing_seal.get("provider_calls_observed_at_seal") is not False
        or source_plumbing_seal.get("formalization_outcomes_observed_at_seal") is not False
        or source_plumbing_seal.get("results_and_completion_ledger_must_be_absent") is not True
    ):
        raise ValueError("source LeanFlow plumbing seal binding changed")
    plumbing_seal = json.loads(payload[LEANFLOW_PLUMBING_SEAL].decode("utf-8"))
    plumbing_seal.update({
        "external_comparator_plan_sha256": sha256_bytes(plan_data),
        "adapter_contract_sha256": sha256_bytes(contract_data),
        "schedule_sha256": packaged_schedule_sha,
        "fixture_request_sha256": sha256_bytes(fixture_request_data),
        "completion_ledger_contract_sha256": sha256_bytes(ledger_contract_data),
        "fixture_entrypoint_sha256": sha256_bytes(payload[LEANFLOW_FAKE_ADAPTER]),
        "schedule_builder_sha256": sha256_bytes(payload[LEANFLOW_SCHEDULE_BUILDER]),
        "completion_ledger_builder_sha256": sha256_bytes(
            payload[LEANFLOW_LEDGER_BUILDER]
        ),
    })
    plumbing_seal_data = canonical_json(plumbing_seal)
    require_anonymous_bytes(LEANFLOW_PLUMBING_SEAL, plumbing_seal_data)
    payload[LEANFLOW_PLUMBING_SEAL] = plumbing_seal_data


def anonymous_snapshot_binding(data):
    """Return a domain-separated non-Git binding for one packaged snapshot."""
    return hashlib.sha1(b"anonymous-source-audit-snapshot\0" + data).hexdigest()


def rebind_anonymous_source_contract_audit(payload, anonymous_reference):
    """Remove authoring-repository fingerprints while preserving audit checks."""
    required = set(SOURCE_CONTRACT_AUDIT_FILES + SOURCE_CONTRACT_AUDIT_TOOLS)
    missing = sorted(required - set(payload))
    if missing:
        raise ValueError(
            "anonymous source-contract audit rebinding is missing: "
            + ", ".join(missing)
        )

    base = json.loads(payload[SOURCE_AUDIT_BASE_MANIFEST].decode("utf-8"))
    if base.get("base_git_commit") != SOURCE_AUDIT_PUBLIC_BASE_COMMIT:
        raise ValueError("source-contract audit base commit changed")
    snapshots = base.get("snapshots", {})
    if set(snapshots) != {"challenge_manifest", "paired_requirements"}:
        raise ValueError("source-contract audit snapshot set changed")
    public_blob_ids = set(SOURCE_AUDIT_PUBLIC_BLOB_IDS)
    observed_blob_ids = {
        row.get("git_blob_sha1") for row in snapshots.values()
        if isinstance(row, dict)
    }
    if observed_blob_ids != public_blob_ids:
        raise ValueError("source-contract audit Git-blob bindings changed")
    base["base_git_commit"] = anonymous_reference
    anonymous_blob_bindings = {}
    for label, row in snapshots.items():
        snapshot_path = row.get("snapshot_path")
        if snapshot_path not in payload:
            raise ValueError("source-contract audit snapshot payload is missing")
        snapshot_data = payload[snapshot_path]
        if row.get("sha256") != sha256_bytes(snapshot_data):
            raise ValueError("source-contract audit snapshot SHA-256 changed")
        row.pop("git_blob_sha1")
        binding = anonymous_snapshot_binding(snapshot_data)
        row["snapshot_binding_sha1"] = binding
        anonymous_blob_bindings[label] = binding
    base_data = canonical_json(base)
    require_anonymous_bytes(SOURCE_AUDIT_BASE_MANIFEST, base_data)
    payload[SOURCE_AUDIT_BASE_MANIFEST] = base_data

    amendment = json.loads(payload[SOURCE_AUDIT_AMENDMENT].decode("utf-8"))
    base_ref = amendment.get("pre_amendment_base", {})
    if base_ref.get("base_git_commit") != SOURCE_AUDIT_PUBLIC_BASE_COMMIT:
        raise ValueError("source-contract amendment base commit changed")
    base_ref["base_git_commit"] = anonymous_reference
    base_ref["manifest_sha256"] = sha256_bytes(base_data)
    primary_inputs = amendment.get("primary_inputs", {})
    primary_paths = {
        "challenge_manifest": "evaluation/target-drift-v1/challenges.json",
        "paired_requirements": "evaluation/target-drift-v2/paired-requirements.json",
    }
    if set(primary_inputs) != set(primary_paths):
        raise ValueError("source-contract amendment primary inputs changed")
    for label, path in primary_paths.items():
        if primary_inputs[label].get("path") != path or path not in payload:
            raise ValueError("source-contract amendment primary path changed")
        primary_inputs[label]["after_sha256"] = sha256_bytes(payload[path])
    derived = amendment.get("derived_bindings_after", {})
    if not isinstance(derived, dict) or not derived:
        raise ValueError("source-contract amendment derived bindings are absent")
    for row in derived.values():
        path = row.get("path") if isinstance(row, dict) else None
        if path not in payload:
            raise ValueError("source-contract amendment derived payload is missing")
        key = "after_sha256" if "after_sha256" in row else "sha256"
        row[key] = sha256_bytes(payload[path])
    amendment_data = canonical_json(amendment)
    require_anonymous_bytes(SOURCE_AUDIT_AMENDMENT, amendment_data)
    payload[SOURCE_AUDIT_AMENDMENT] = amendment_data

    validator = payload[SOURCE_AUDIT_VALIDATOR].decode("utf-8")
    public_function = (
        "def git_blob_sha1(path: Path) -> str:\n"
        "    payload = path.read_bytes()\n"
        "    header = f\"blob {len(payload)}\\0\".encode(\"ascii\")\n"
        "    return hashlib.sha1(header + payload).hexdigest()"
    )
    anonymous_function = (
        "def snapshot_binding_sha1(path: Path) -> str:\n"
        "    payload = path.read_bytes()\n"
        "    return hashlib.sha1(\n"
        "        b\"anonymous-source-audit-snapshot\\0\" + payload\n"
        "    ).hexdigest()"
    )
    if public_function not in validator:
        raise ValueError("source-contract validator Git-blob helper changed")
    validator = validator.replace(public_function, anonymous_function)
    validator = validator.replace("git_blob_sha1", "snapshot_binding_sha1")
    validator = validator.replace(
        SOURCE_AUDIT_PUBLIC_BASE_COMMIT, anonymous_reference
    )
    for public_blob, binding in zip(
        SOURCE_AUDIT_PUBLIC_BLOB_IDS,
        (
            anonymous_blob_bindings["challenge_manifest"],
            anonymous_blob_bindings["paired_requirements"],
        ),
    ):
        validator = validator.replace(public_blob, binding)
    validator_data = validator.encode("utf-8")
    require_anonymous_bytes(SOURCE_AUDIT_VALIDATOR, validator_data)
    payload[SOURCE_AUDIT_VALIDATOR] = validator_data

    forbidden = (
        SOURCE_AUDIT_PUBLIC_BASE_COMMIT.encode("ascii"),
        *(item.encode("ascii") for item in SOURCE_AUDIT_PUBLIC_BLOB_IDS),
    )
    for rel in required:
        lowered = payload[rel].lower()
        if any(item in lowered for item in forbidden):
            raise ValueError(
                "authoring Git fingerprint remains in anonymous source-contract audit: "
                + rel
            )


def selected_source_records():
    raw = load_json(REPO_ROOT / "website" / "content" / "results.json")
    by_id = {row["id"]: row for row in raw["results"]}
    missing = sorted(set(SOURCE_RESULT_IDS) - set(by_id))
    if missing:
        raise ValueError("missing source result records: " + ", ".join(missing))
    records = {}
    for item in SOURCE_RESULT_IDS:
        source = by_id[item]
        records[item] = {
            "id": source["id"],
            "title": source["title"],
            "status": source["status"],
            "informal": source["informal"],
            "declarations": list(source.get("declarations", [])),
            "depends_on": list(source.get("depends_on", [])),
            "missing": list(source.get("missing", [])),
        }
    return records


def validate_delayed_counts(records):
    if any(records[item]["status"] != "compiled" for item in DELAYED_IMPLEMENTATION_IDS):
        raise ValueError("implementation-facing delayed records must remain compiled")
    implementation_count = sum(
        len(records[item]["declarations"]) for item in DELAYED_IMPLEMENTATION_IDS
    )
    diagnostic = records[DELAYED_DIAGNOSTIC_ID]
    processed_prefix = records[DELAYED_PROCESSED_PREFIX_ID]
    trace_summary = records[DELAYED_TRACE_SUMMARY_ID]
    ordered_transition = records[DELAYED_ORDERED_TRANSITION_ID]
    ordered_trace = records[DELAYED_ORDERED_TRACE_ID]
    d11_domain = records[DELAYED_D11_DOMAIN_ID]
    line10_initialization = records[DELAYED_LINE10_INITIALIZATION_ID]
    central_endpoint = records[DELAYED_CENTRAL_ENDPOINT_ID]
    if implementation_count != 89:
        raise ValueError("delayed implementation count drifted to {}".format(implementation_count))
    if diagnostic["status"] != "partial" or len(diagnostic["declarations"]) != 19:
        raise ValueError(
            "D.10--D.12 diagnostic/repair record must remain partial with 19 declarations"
        )
    if processed_prefix["status"] != "compiled" or len(processed_prefix["declarations"]) != 16:
        raise ValueError(
            "D.1 processed-prefix producer must remain compiled with 16 declarations"
        )
    if trace_summary["status"] != "compiled" or len(trace_summary["declarations"]) != 9:
        raise ValueError(
            "processed-trace-summary adapter must remain compiled with 9 declarations"
        )
    if (
        ordered_transition["status"] != "compiled"
        or len(ordered_transition["declarations"]) != 15
    ):
        raise ValueError(
            "ordered no-switch transition must remain compiled with 15 declarations"
        )
    if ordered_trace["status"] != "compiled" or len(ordered_trace["declarations"]) != 12:
        raise ValueError(
            "ordered no-switch trace must remain compiled with 12 declarations"
        )
    if d11_domain["status"] != "compiled" or len(d11_domain["declarations"]) != 6:
        raise ValueError(
            "D.11 nonnegative-gap domain must remain compiled with 6 declarations"
        )
    if (
        line10_initialization["status"] != "compiled"
        or len(line10_initialization["declarations"]) != 31
    ):
        raise ValueError(
            "Algorithm 5 line-10 initialization must remain compiled with 31 declarations"
        )
    if central_endpoint["status"] != "partial":
        raise ValueError("delayed central endpoint must remain partial")


def validate_succinct_count(records):
    succinct = records[SUCCINCT_AUDIT_ID]
    if succinct["status"] != "partial" or len(succinct["declarations"]) != 54:
        raise ValueError(
            "succinct geometry audit must remain partial with 54 declarations"
        )


def validate_sgb_count(records, index):
    historical = records[SGB_AUDIT_ID]
    follow_on = records[SGB_FOLLOW_ON_ID]
    historical_list = historical["declarations"]
    follow_on_list = follow_on["declarations"]
    historical_declarations = set(historical_list)
    follow_on_declarations = set(follow_on_list)
    declarations = historical_declarations | follow_on_declarations
    rows = {
        row["full_name"]: row for row in index["declarations"]
        if row["full_name"] in declarations
    }
    finite_count = sum(
        row["file"] == SGB_FINITE_ALGEBRA_FILE for row in rows.values()
    )
    generated_history_count = sum(
        row["file"] == SGB_GENERATED_HISTORY_FILE for row in rows.values()
    )
    two_arm_rate_count = sum(
        row["file"] == SGB_TWO_ARM_RATE_FILE for row in rows.values()
    )
    exponential_audit_count = sum(
        row["file"] == SGB_EXPONENTIAL_AUDIT_FILE for row in rows.values()
    )
    generated_equation_8_count = sum(
        row["file"] == SGB_GENERATED_EQUATION_8_FILE for row in rows.values()
    )
    successor_recurrence_count = sum(
        row["file"] == SGB_SUCCESSOR_RECURRENCE_FILE for row in rows.values()
    )
    initial_recurrence_count = sum(
        row["file"] == SGB_INITIAL_RECURRENCE_FILE for row in rows.values()
    )
    measurable_recurrence_count = sum(
        row["file"] == SGB_MEASURABLE_RECURRENCE_FILE for row in rows.values()
    )
    path_integrability_count = sum(
        row["file"] == SGB_PATH_INTEGRABILITY_FILE for row in rows.values()
    )
    fixed_iid_count = sum(
        row["file"] == SGB_FIXED_IID_FILE for row in rows.values()
    )
    unconditional_recurrence_count = sum(
        row["file"] == SGB_UNCONDITIONAL_RECURRENCE_FILE
        for row in rows.values()
    )
    theorem_one_count = sum(
        row["file"] == SGB_THEOREM_ONE_FILE for row in rows.values()
    )
    theorem_four_contract_audit_count = sum(
        row["file"] == SGB_THEOREM_FOUR_CONTRACT_AUDIT_FILE
        for row in rows.values()
    )
    theorem_four_contract_names = {
        row["full_name"] for row in rows.values()
        if row["file"] == SGB_THEOREM_FOUR_CONTRACT_AUDIT_FILE
    }
    corollary_one_count = sum(
        row["file"] == SGB_COROLLARY_ONE_FILE for row in rows.values()
    )
    corollary_one_names = {
        row["full_name"] for row in rows.values()
        if row["file"] == SGB_COROLLARY_ONE_FILE
    }
    theorem_two_starvation_count = sum(
        row["file"] == SGB_THEOREM_TWO_STARVATION_FILE
        for row in rows.values()
    )
    theorem_two_starvation_names = {
        row["full_name"] for row in rows.values()
        if row["file"] == SGB_THEOREM_TWO_STARVATION_FILE
    }
    theorem_two_nth_pull_count = sum(
        row["file"] == SGB_THEOREM_TWO_NTH_PULL_FILE
        for row in rows.values()
    )
    theorem_two_nth_pull_names = {
        row["full_name"] for row in rows.values()
        if row["file"] == SGB_THEOREM_TWO_NTH_PULL_FILE
    }
    layer_counts = (
        finite_count,
        generated_history_count,
        two_arm_rate_count,
        exponential_audit_count,
        generated_equation_8_count,
        successor_recurrence_count,
        initial_recurrence_count,
        measurable_recurrence_count,
        path_integrability_count,
        fixed_iid_count,
        unconditional_recurrence_count,
        theorem_one_count,
    )
    expected_layer_counts = (
        SGB_FINITE_ALGEBRA_DECLARATION_COUNT,
        SGB_GENERATED_HISTORY_DECLARATION_COUNT,
        SGB_TWO_ARM_RATE_DECLARATION_COUNT,
        SGB_EXPONENTIAL_AUDIT_DECLARATION_COUNT,
        SGB_GENERATED_EQUATION_8_DECLARATION_COUNT,
        SGB_SUCCESSOR_RECURRENCE_DECLARATION_COUNT,
        SGB_INITIAL_RECURRENCE_DECLARATION_COUNT,
        SGB_MEASURABLE_RECURRENCE_DECLARATION_COUNT,
        SGB_PATH_INTEGRABILITY_DECLARATION_COUNT,
        SGB_FIXED_IID_DECLARATION_COUNT,
        SGB_UNCONDITIONAL_RECURRENCE_DECLARATION_COUNT,
        SGB_THEOREM_ONE_DECLARATION_COUNT,
    )
    if (
        historical["status"] != "partial"
        or follow_on["status"] != "partial"
        or len(historical_list) != len(historical_declarations)
        or len(historical_declarations) != SGB_HISTORICAL_DECLARATION_COUNT
        or len(follow_on_list) != len(follow_on_declarations)
        or len(follow_on_declarations) !=
            SGB_COROLLARY_ONE_DECLARATION_COUNT
            + SGB_THEOREM_TWO_STARVATION_DECLARATION_COUNT
            + SGB_THEOREM_TWO_NTH_PULL_DECLARATION_COUNT
        or historical_declarations & follow_on_declarations
        or len(declarations) != SGB_TOTAL_DECLARATION_COUNT
        or set(rows) != declarations
        or layer_counts != expected_layer_counts
        or sum(layer_counts) != SGB_THEOREM_ONE_STACK_DECLARATION_COUNT
        or theorem_four_contract_audit_count !=
            SGB_THEOREM_FOUR_CONTRACT_AUDIT_DECLARATION_COUNT
        or theorem_four_contract_names !=
            SGB_THEOREM_FOUR_CONTRACT_AUDIT_DECLARATIONS
        or sum(layer_counts) + theorem_four_contract_audit_count !=
            len(historical_declarations)
        or corollary_one_count != SGB_COROLLARY_ONE_DECLARATION_COUNT
        or theorem_two_starvation_count !=
            SGB_THEOREM_TWO_STARVATION_DECLARATION_COUNT
        or theorem_two_nth_pull_count !=
            SGB_THEOREM_TWO_NTH_PULL_DECLARATION_COUNT
        or corollary_one_names | theorem_two_starvation_names |
            theorem_two_nth_pull_names !=
            follow_on_declarations
        or not SGB_COROLLARY_ONE_REPRESENTATIVE_DECLARATIONS.issubset(
            corollary_one_names
        )
        or not SGB_THEOREM_TWO_STARVATION_REPRESENTATIVE_DECLARATIONS.issubset(
            theorem_two_starvation_names
        )
        or not SGB_THEOREM_TWO_NTH_PULL_REPRESENTATIVE_DECLARATIONS.issubset(
            theorem_two_nth_pull_names
        )
        or SGB_THEOREM_TWO_TERMINAL_DECLARATION in declarations
        or not SGB_GENERATED_TRAJECTORY_DECLARATIONS.issubset(declarations)
        or not SGB_CONDITIONAL_LAW_BRIDGE_DECLARATIONS.issubset(declarations)
        or not SGB_TWO_ARM_RATE_DECLARATIONS.issubset(declarations)
        or not SGB_EXPONENTIAL_AUDIT_DECLARATIONS.issubset(declarations)
        or not SGB_GENERATED_EQUATION_8_DECLARATIONS.issubset(declarations)
        or not SGB_INITIAL_RECURRENCE_DECLARATIONS.issubset(declarations)
        or not SGB_SUCCESSOR_RECURRENCE_DECLARATIONS.issubset(declarations)
        or not SGB_TRAJECTORY_COND_DISTRIB_RECURRENCE_DECLARATIONS.issubset(
            declarations
        )
        or not SGB_PATH_INTEGRABILITY_DECLARATIONS.issubset(declarations)
        or not SGB_CONDITIONAL_RECURRENCE_DECLARATIONS.issubset(declarations)
        or not SGB_FIXED_IID_DECLARATIONS.issubset(declarations)
        or not SGB_UNCONDITIONAL_RECURRENCE_DECLARATIONS.issubset(
            declarations
        )
        or not SGB_THEOREM_ONE_DECLARATIONS.issubset(declarations)
        or not SGB_THEOREM_FOUR_CONTRACT_AUDIT_DECLARATIONS.issubset(
            declarations
        )
    ):
        raise ValueError(
            "stochastic-gradient-bandit audit must remain partial with exactly "
            "288 declarations: historical 223 = frozen 215-declaration "
            "Theorem-1 stack + 8 Theorem-4 contract-audit leaves, followed by "
            "23 Corollary-1 companion declarations + 18 deterministic "
            "Theorem-2 starvation-consumer declarations + 24 chronological "
            "nth-pull declarations; selected-IID/future-cylinder, conditional "
            "no-return, and the Theorem-2 terminal must remain blocked"
        )
    return {
        "generated_trajectory_compiled":
            SGB_GENERATED_TRAJECTORY_DECLARATIONS.issubset(declarations),
        "conditional_law_bridge_compiled":
            SGB_CONDITIONAL_LAW_BRIDGE_DECLARATIONS.issubset(declarations),
        "two_arm_equation_11_compiled":
            SGB_TWO_ARM_RATE_DECLARATIONS.issubset(declarations),
        "source_equation_8_compiled":
            SGB_EXPONENTIAL_AUDIT_DECLARATIONS.issubset(declarations),
        "generated_equation_8_kernel_bridge_compiled":
            SGB_GENERATED_EQUATION_8_DECLARATIONS.issubset(declarations),
        "two_arm_initial_recurrence_compiled":
            SGB_INITIAL_RECURRENCE_DECLARATIONS.issubset(declarations),
        "fixed_history_successor_recurrence_compiled":
            SGB_SUCCESSOR_RECURRENCE_DECLARATIONS.issubset(declarations),
        "trajectory_cond_distrib_recurrence_compiled":
            SGB_TRAJECTORY_COND_DISTRIB_RECURRENCE_DECLARATIONS.issubset(
                declarations
            ),
        "path_integrability_compiled":
            SGB_PATH_INTEGRABILITY_DECLARATIONS.issubset(declarations),
        "conditional_expectation_one_step_recurrence_compiled":
            SGB_CONDITIONAL_RECURRENCE_DECLARATIONS.issubset(declarations),
        "fixed_iid_contract_compiled":
            SGB_FIXED_IID_DECLARATIONS.issubset(declarations),
        "unconditional_recurrence_iteration_compiled":
            SGB_UNCONDITIONAL_RECURRENCE_DECLARATIONS.issubset(declarations),
        "generic_expected_failure_mass_bound_compiled":
            SGB_UNCONDITIONAL_RECURRENCE_DECLARATIONS.issubset(declarations),
        "source_theorem_one_compiled":
            SGB_THEOREM_ONE_DECLARATIONS.issubset(declarations),
        "source_theorem_four_contract_audit_compiled":
            theorem_four_contract_names ==
            SGB_THEOREM_FOUR_CONTRACT_AUDIT_DECLARATIONS,
        "source_corollary_one_compiled":
            SGB_COROLLARY_ONE_REPRESENTATIVE_DECLARATIONS.issubset(
                corollary_one_names
            ),
        "source_theorem_two_deterministic_starvation_consumer_compiled":
            SGB_THEOREM_TWO_STARVATION_REPRESENTATIVE_DECLARATIONS.issubset(
                theorem_two_starvation_names
            ),
        "source_theorem_two_nth_pull_bridge_compiled":
            SGB_THEOREM_TWO_NTH_PULL_REPRESENTATIVE_DECLARATIONS.issubset(
                theorem_two_nth_pull_names
            ),
        "source_theorem_two_endpoint_verified": False,
    }


def validate_theorem_audit_comparison(records, index, comparison=None,
                                      source_freeze=None):
    if comparison is None:
        comparison = load_json(REPO_ROOT / THEOREM_AUDIT_COMPARISON_SOURCE)
    if source_freeze is None:
        source_freeze = load_json(
            REPO_ROOT / "research-wiki" / "papers" /
            "prospective-audit-2025-freeze.json"
        )
    rows = comparison.get("rows")
    if comparison.get("schema_version") != 1 or not isinstance(rows, list):
        raise ValueError("theorem-audit comparison schema is invalid")
    if tuple(row.get("id") for row in rows) != THEOREM_AUDIT_ROW_IDS:
        raise ValueError("theorem-audit comparison row inventory/order drifted")
    by_id = {row["id"]: row for row in rows}
    if len(by_id) != len(rows):
        raise ValueError("theorem-audit comparison row IDs must be unique")

    freeze_cards = {
        row.get("card_id") for row in source_freeze.get("papers", [])
    }
    expected_freeze_cards = {
        "PPR-SCHLISSELBERG-LANCEWICKI-AUER-MANSOUR-2025-DELAYED-BOBW",
        "PPR-ZENG-HONORIO-2025-SUCCINCT-LOWER-BOUNDS",
        "PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB",
    }
    if freeze_cards != expected_freeze_cards:
        raise ValueError("theorem-audit comparison source-freeze inventory drifted")
    if source_freeze.get("selection_status") != (
        "source_locked_with_record_specific_timing"
    ):
        raise ValueError("source-lock portfolio timing status drifted")
    expected_freeze_timing = {
        "PPR-SCHLISSELBERG-LANCEWICKI-AUER-MANSOUR-2025-DELAYED-BOBW":
            "co_published_with_initial_feasibility_slice",
        "PPR-ZENG-HONORIO-2025-SUCCINCT-LOWER-BOUNDS":
            "locked_before_case_specific_lean_slice",
        "PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB":
            "locked_before_case_specific_lean_slice",
    }
    freeze_timing = {
        row.get("card_id"): row.get("selection_timing")
        for row in source_freeze.get("papers", [])
    }
    if freeze_timing != expected_freeze_timing:
        raise ValueError("source-lock case-specific timing drifted")
    timing_note = source_freeze.get("timing_note", "")
    if "does not assert that every case was frozen" not in timing_note:
        raise ValueError("source-lock timing limitation is missing")

    delayed_ids = list(DELAYED_IMPLEMENTATION_IDS) + [
        DELAYED_DIAGNOSTIC_ID,
        DELAYED_PROCESSED_PREFIX_ID,
        DELAYED_TRACE_SUMMARY_ID,
        DELAYED_ORDERED_TRANSITION_ID,
        DELAYED_ORDERED_TRACE_ID,
        DELAYED_D11_DOMAIN_ID,
        DELAYED_LINE10_INITIALIZATION_ID,
    ]
    specs = {
        "textbook-chapter-15-scoped-positive-control": {
            "role": "scoped_positive_control",
            "evidence_record_ids": [CH15_SCOPED_ENDPOINT_ID],
            "central_endpoint_record_id": CH15_SCOPED_ENDPOINT_ID,
            "promotion_status": "compiled",
            "compiled_declaration_count": 12,
            "scoped_endpoint_verified": True,
        },
        "delayed-bobw-source-frozen-audit": {
            "role": "source_frozen_external_audit",
            "source_freeze_card_id":
                "PPR-SCHLISSELBERG-LANCEWICKI-AUER-MANSOUR-2025-DELAYED-BOBW",
            "evidence_record_ids": delayed_ids,
            "central_endpoint_record_id": DELAYED_CENTRAL_ENDPOINT_ID,
            "promotion_status": "partial",
            "compiled_declaration_count": 197,
            "declaration_count_breakdown": {
                "implementation_facing": 89,
                "diagnostic_conditional_repair": 19,
                "processed_prefix": 16,
                "processed_trace_summary_adapter": 9,
                "ordered_no_switch_transition": 15,
                "ordered_no_switch_trace_ordering": 12,
                "nonnegative_gap_d11_domain": 6,
                "line10_eliminated_arm_initialization": 31,
            },
        },
        "succinct-lower-bound-source-frozen-audit": {
            "role": "source_frozen_external_audit",
            "source_freeze_card_id":
                "PPR-ZENG-HONORIO-2025-SUCCINCT-LOWER-BOUNDS",
            "evidence_record_ids": [SUCCINCT_AUDIT_ID],
            "central_endpoint_record_id": SUCCINCT_AUDIT_ID,
            "promotion_status": "partial",
            "compiled_declaration_count": 54,
        },
        "stochastic-gradient-bandit-source-frozen-audit": {
            "role": "source_frozen_external_audit",
            "source_freeze_card_id":
                "PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB",
            "evidence_record_ids": [SGB_AUDIT_ID, SGB_FOLLOW_ON_ID],
            "central_endpoint_record_id": SGB_AUDIT_ID,
            "promotion_status": "partial",
            "compiled_declaration_count": SGB_TOTAL_DECLARATION_COUNT,
            "theorem_one_endpoint_verified": True,
            "corollary_one_endpoint_verified": True,
            "theorem_two_endpoint_verified": False,
            "theorem_four_endpoint_verified": False,
            "declaration_count_breakdown": {
                "finite_action_algebra": SGB_FINITE_ALGEBRA_DECLARATION_COUNT,
                "generated_history_and_kernel_bridge":
                    SGB_GENERATED_HISTORY_DECLARATION_COUNT,
                "two_arm_zero_sum_and_equation_11":
                    SGB_TWO_ARM_RATE_DECLARATION_COUNT,
                "source_c_and_equation_8":
                    SGB_EXPONENTIAL_AUDIT_DECLARATION_COUNT,
                "generated_equation_8_kernel_bridge":
                    SGB_GENERATED_EQUATION_8_DECLARATION_COUNT,
                "fixed_history_successor_recurrence":
                    SGB_SUCCESSOR_RECURRENCE_DECLARATION_COUNT,
                "two_arm_initial_recurrence":
                    SGB_INITIAL_RECURRENCE_DECLARATION_COUNT,
                "measurable_contract_and_cond_distrib_transport":
                    SGB_MEASURABLE_RECURRENCE_DECLARATION_COUNT,
                "path_integrability_and_conditional_recurrence":
                    SGB_PATH_INTEGRABILITY_DECLARATION_COUNT,
                "fixed_iid_source_contract_bridge":
                    SGB_FIXED_IID_DECLARATION_COUNT,
                "unconditional_recurrence_and_failure_mass":
                    SGB_UNCONDITIONAL_RECURRENCE_DECLARATION_COUNT,
                "source_theorem_one_terminal":
                    SGB_THEOREM_ONE_DECLARATION_COUNT,
                "source_theorem_four_contract_audit":
                    SGB_THEOREM_FOUR_CONTRACT_AUDIT_DECLARATION_COUNT,
                "source_corollary_one_companion":
                    SGB_COROLLARY_ONE_DECLARATION_COUNT,
                "source_theorem_two_deterministic_starvation_consumer":
                    SGB_THEOREM_TWO_STARVATION_DECLARATION_COUNT,
                "source_theorem_two_nth_pull_bridge":
                    SGB_THEOREM_TWO_NTH_PULL_DECLARATION_COUNT,
            },
        },
    }
    index_names = {row.get("full_name") for row in index.get("declarations", [])}
    for row_id, spec in specs.items():
        row = by_id[row_id]
        for key, expected in spec.items():
            if row.get(key) != expected:
                raise ValueError(
                    "theorem-audit comparison {} drift for {}".format(key, row_id)
                )
        if not isinstance(row.get("contract_stress"), list) or not row["contract_stress"]:
            raise ValueError("theorem-audit comparison stress list is empty for " + row_id)
        if not isinstance(row.get("strongest_compiled_bridge"), str) or not row["strongest_compiled_bridge"]:
            raise ValueError("theorem-audit comparison bridge is empty for " + row_id)
        if not isinstance(row.get("scope_boundary"), str) or not row["scope_boundary"]:
            raise ValueError("theorem-audit comparison scope boundary is empty for " + row_id)
        evidence_records = [records[item] for item in spec["evidence_record_ids"]]
        evidence_count = sum(len(record["declarations"]) for record in evidence_records)
        if evidence_count != spec["compiled_declaration_count"]:
            raise ValueError("theorem-audit comparison declaration count drift for " + row_id)
        evidence_names = {
            name for record in evidence_records for name in record["declarations"]
        }
        if len(evidence_names) != spec["compiled_declaration_count"]:
            raise ValueError("theorem-audit comparison declaration overlap drift for " + row_id)
        if not evidence_names.issubset(index_names):
            raise ValueError("theorem-audit comparison references an unindexed declaration")
        if row_id == "delayed-bobw-source-frozen-audit":
            expected_delayed_names = {
                index_row["full_name"]
                for index_row in index.get("declarations", [])
                if str(index_row.get("file", "")).startswith(
                    "BanditRLProof/DelayedFeedback/"
                )
                and index_row.get("file")
                != "BanditRLProof/DelayedFeedback/MultiRegimeContract.lean"
            }
            if evidence_names != expected_delayed_names:
                raise ValueError(
                    "delayed theorem-audit declarations must equal the exact "
                    "non-generic DelayedFeedback declaration set"
                )
        central = records[spec["central_endpoint_record_id"]]
        if spec["role"] == "source_frozen_external_audit":
            expected_endpoint_verified = (
                row_id == "stochastic-gradient-bandit-source-frozen-audit"
            )
            if (
                row.get("source_freeze_card_id") not in freeze_cards
                or central["status"] != "partial"
                or row.get("paper_endpoint_verified") is not
                    expected_endpoint_verified
                or not isinstance(row.get("blocking_obligations"), list)
                or not row["blocking_obligations"]
            ):
                raise ValueError(
                    "external theorem-audit endpoint boundary drift for " + row_id
                )
            if row_id == "stochastic-gradient-bandit-source-frozen-audit" and (
                "paper_endpoint_verified refers only to Theorem 1"
                not in row.get("scope_boundary", "")
                or "Conditional no-return probability >= 1/2"
                not in row.get("scope_boundary", "")
                or "asymptotic terminal remain blocked"
                not in row.get("scope_boundary", "")
                or not any(
                    "selected-reward IID/future-cylinder law" in item
                    for item in row.get("blocking_obligations", [])
                )
            ):
                raise ValueError(
                    "SGB theorem-audit endpoint scope must remain Theorem-1-only "
                    "with Theorem 2 blocked"
                )
        elif (
            central["status"] != "compiled"
            or row.get("scoped_endpoint_verified") is not True
            or row.get("blocking_obligations") != []
            or "paper_endpoint_verified" in row
        ):
            raise ValueError("Chapter 15 scoped positive-control boundary drift")
    return sanitize_json(comparison)


def validate_ch16_boundary(records):
    compiled = records[CH16_COMPILED_ID]
    compiled_list = compiled["declarations"]
    compiled_names = set(compiled_list)
    event_regret = records[CH16_EVENT_REGRET_ID]
    event_regret_list = event_regret["declarations"]
    event_regret_names = set(event_regret_list)
    terminal = records[CH16_TERMINAL_ID]
    if (
        compiled["status"] != "compiled"
        or len(compiled_list) != len(compiled_names)
        or compiled_names != CH16_COMPILED_DECLARATIONS
    ):
        raise ValueError(
            "Chapter 16 dependency slice must remain compiled with exactly "
            "the frozen 20 unique declarations"
        )
    if (
        event_regret["status"] != "compiled"
        or len(event_regret_list) != len(event_regret_names)
        or event_regret_names != CH16_EVENT_REGRET_DECLARATIONS
    ):
        raise ValueError(
            "Chapter 16 event-regret slice must remain compiled with exactly "
            "the frozen 15 unique declarations"
        )
    if terminal["status"] != "blocked" or terminal["declarations"]:
        raise ValueError(
            "Chapter 16 source terminals must remain blocked and declaration-free"
        )
    return {
        "dependency_declaration_count": len(compiled_names),
        "event_regret_declaration_count": len(event_regret_names),
        "finite_mean_gap_bridge_verified": False,
        "source_terminals_verified": False,
    }


def build_claim_ledger(proof_report):
    records = selected_source_records()
    index = load_json(REPO_ROOT / "research-wiki" / "retrieval-index" /
                      "local_lean_declarations.json")
    validate_delayed_counts(records)
    validate_succinct_count(records)
    sgb_evidence = validate_sgb_count(records, index)
    theorem_audit_comparison = validate_theorem_audit_comparison(records, index)
    ch16_evidence = validate_ch16_boundary(records)
    index_names = {row["full_name"] for row in index["declarations"]}
    delayed_directory_rows = [
        row for row in index["declarations"]
        if str(row.get("file", "")).startswith("BanditRLProof/DelayedFeedback/")
    ]
    delayed_generic_rows = [
        row for row in delayed_directory_rows
        if row.get("file") == "BanditRLProof/DelayedFeedback/MultiRegimeContract.lean"
    ]
    if len(delayed_directory_rows) != 202 or len(delayed_generic_rows) != 5:
        raise ValueError(
            "DelayedFeedback directory boundary must remain 197 source-audit "
            "+ 5 generic declarations"
        )
    referenced = {
        name for record in records.values() for name in record["declarations"]
    }
    missing = sorted(referenced - index_names)
    expected_missing = sorted(EXPECTED_INDEX_EXCEPTIONS)
    if missing != expected_missing:
        raise ValueError(
            "unexpected result/index mismatch: "
            f"actual_missing={missing[:8]!r}; expected_exceptions={expected_missing[:8]!r}"
        )

    cng = load_json(REPO_ROOT / "research-wiki" / "proof-graph" /
                    "cng_candidate_evaluation.json")
    shared = proof_report["shared_library"]
    best_zdd = min(row["nonterminal_nodes"] for row in proof_report["zdd"]["orders"])
    target_id = "TARGET-DRIFT-V2-CONTROLLED-EVALUATION"
    if records[target_id]["status"] != "planned" or records[target_id]["declarations"]:
        raise ValueError("target-drift record must remain planned and result-free")
    return {
        "schema_version": 1,
        "status_vocabulary": ["compiled", "partial", "blocked", "prototype", "planned"],
        "index_counts": {
            "source_declarations": len(index["declarations"]),
            "generated_declaration_exceptions": list(EXPECTED_INDEX_EXCEPTIONS),
            "interpretation": "Counter-specific artifact size; not theorem coverage or an evaluation score.",
        },
        "table_rows": [
            {
                "artifact": "RL random-time route",
                "status": "compiled",
                "source_record_ids": ["RL-UNBOUNDED-HITTINGAFTER-EXPECTED-UPPER-BOUND"],
                "boundary": "Fixed-index and L1 consumers under recorded assumptions; not optional stopping or full UCB-VI.",
            },
            {
                "artifact": "ETC finite-history route",
                "status": "compiled",
                "source_record_ids": ["ETC-CANONICAL-SUBGAUSSIAN-REGRET"],
                "boundary": "Exact local endpoint; external theorem cards are retrieval evidence only.",
            },
            {
                "artifact": "Textbook Chapters 13--17",
                "status": "partial",
                "source_record_ids": [item for item in SOURCE_RESULT_IDS if item.startswith("TEXTBOOK-PART-IV-")],
                "boundary": "Chapter 15 Lemma 15.1 and the exact Theorem 15.2 expected-pseudo-regret/minimax terminals compile, with a Chapter 13 constant-1/54 consumer. Chapter 16 additionally compiles 20 analytic/information dependencies and 15 canonical gap-event/regret declarations, including both exact event charges and a conditional factor-one-quarter logarithmic consumer. Its finite-mean arm-law-to-gap bridge and all Chapter 16--17 source terminals remain open.",
            },
            {
                "artifact": "Delayed best-of-both-worlds audit",
                "status": "partial",
                "source_record_ids": list(DELAYED_IMPLEMENTATION_IDS) + [
                    DELAYED_DIAGNOSTIC_ID,
                    DELAYED_PROCESSED_PREFIX_ID,
                    DELAYED_TRACE_SUMMARY_ID,
                    DELAYED_ORDERED_TRANSITION_ID,
                    DELAYED_ORDERED_TRACE_ID,
                    DELAYED_D11_DOMAIN_ID,
                    DELAYED_LINE10_INITIALIZATION_ID,
                    DELAYED_CENTRAL_ENDPOINT_ID,
                ],
                "boundary": "197 = 89 implementation-facing + 19 diagnostic/conditional/repair + 16 processed-prefix + 9 processed-trace-summary adapter + 15 ordered no-switch transition + 12 ordered trace + 6 nonnegative-gap D.11-domain + 31 Algorithm-5 line-10 initialization declarations. The D.11 leaf is restricted to nonnegative stochastic loss gaps, and line 10 is only an initializer. D.13, EAP/BSC evolution beyond initialization, a generated trajectory, D.4 probability, switch logic, an unconditional source elimination theorem, and every source-paper regret endpoint remain open.",
            },
            {
                "artifact": "Succinct geometry audit",
                "status": "partial",
                "source_record_ids": [SUCCINCT_AUDIT_ID],
                "boundary": "54 declarations compile Definitions 3.1--3.3 and Lemmas 3.1--3.4, including finite-Bessel strict representation-size minimality and uniqueness for the same vector; a global R boundedness obligation is explicit; no Lemma 3.5--3.6, Theorem 3.8, or regret endpoint.",
            },
            {
                "artifact": "Stochastic-gradient-bandit Theorem 1, Corollary 1, and blocked Theorem-2 follow-on",
                "status": "partial",
                "source_record_ids": [SGB_AUDIT_ID, SGB_FOLLOW_ON_ID],
                "boundary": "288 declarations preserve the historical 223 = 215-declaration Theorem-1 stack + 8 Appendix-E/Theorem-4 contract leaves, then add a 23-declaration compiled Corollary-1 bounded companion, an 18-declaration deterministic Appendix-C Step-1 starvation consumer, and a 24-declaration chronological nth-pull bridge. Corollary 1 is a direct Theorem-1 consumer for T >= 2 and eta_T = sqrt(log T / T), not independent Theorem-2 evidence. The nth-pull layer proves a zero-based WithTop stopping time, exact finite count/action identification, and measurable stopped reward and post-pull probability. It is not composed with the fixed-cutoff consumer and proves no adaptive selected-reward IID, future-cylinder law, conditional no-return probability >= 1/2, Rademacher/binomial ballot phase, or asymptotic terminal. The frozen K = 2 Theorem-2 center therefore remains blocked. Theorem 4 also remains open. Dirac refers only to the Unit environment prior, not to the arm reward laws.",
            },
            {
                "artifact": "Proof graph / curvature--noise--gap",
                "status": "prototype",
                "source_record_ids": [],
                "boundary": "Deterministic structural measurements and eight finite leaves; no search-speed or theory-discovery claim.",
            },
            {
                "artifact": "Matched workflow study",
                "status": "planned",
                "source_record_ids": [target_id],
                "boundary": "Protocol and challenge allocation only; no model run, grade, causal result, or numerical outcome.",
            },
        ],
        "source_records": records,
        "theorem_audit_comparison": theorem_audit_comparison,
        "delayed_feedback": {
            "implementation_facing_ids": list(DELAYED_IMPLEMENTATION_IDS),
            "implementation_facing_declaration_count": 89,
            "diagnostic_id": DELAYED_DIAGNOSTIC_ID,
            "diagnostic_conditional_repair_declaration_count": 19,
            "processed_prefix_id": DELAYED_PROCESSED_PREFIX_ID,
            "processed_prefix_declaration_count": 16,
            "processed_trace_summary_id": DELAYED_TRACE_SUMMARY_ID,
            "processed_trace_summary_declaration_count": 9,
            "ordered_no_switch_transition_id": DELAYED_ORDERED_TRANSITION_ID,
            "ordered_no_switch_transition_declaration_count": 15,
            "ordered_no_switch_trace_id": DELAYED_ORDERED_TRACE_ID,
            "ordered_no_switch_trace_declaration_count": 12,
            "d11_domain_id": DELAYED_D11_DOMAIN_ID,
            "d11_domain_declaration_count": 6,
            "line10_initialization_id": DELAYED_LINE10_INITIALIZATION_ID,
            "line10_initialization_declaration_count": 31,
            "central_endpoint_id": DELAYED_CENTRAL_ENDPOINT_ID,
            "source_audit_declaration_count": 197,
            "generic_multiregime_contract_declaration_count": 5,
            "directory_declaration_count": 202,
            "paper_endpoint_verified": False,
        },
        "succinct_geometry": {
            "source_record_id": SUCCINCT_AUDIT_ID,
            "declaration_count": 54,
            "paper_endpoint_verified": False,
        },
        "stochastic_gradient_bandit": {
            "source_record_id": SGB_AUDIT_ID,
            "follow_on_source_record_id": SGB_FOLLOW_ON_ID,
            "declaration_count": SGB_TOTAL_DECLARATION_COUNT,
            "historical_declaration_count":
                SGB_HISTORICAL_DECLARATION_COUNT,
            "theorem_one_stack_declaration_count":
                SGB_THEOREM_ONE_STACK_DECLARATION_COUNT,
            "theorem_four_contract_audit_declaration_count":
                SGB_THEOREM_FOUR_CONTRACT_AUDIT_DECLARATION_COUNT,
            "corollary_one_declaration_count":
                SGB_COROLLARY_ONE_DECLARATION_COUNT,
            "theorem_two_deterministic_starvation_consumer_declaration_count":
                SGB_THEOREM_TWO_STARVATION_DECLARATION_COUNT,
            "theorem_two_nth_pull_bridge_declaration_count":
                SGB_THEOREM_TWO_NTH_PULL_DECLARATION_COUNT,
            "finite_algebra_declaration_count": SGB_FINITE_ALGEBRA_DECLARATION_COUNT,
            "generated_history_declaration_count": SGB_GENERATED_HISTORY_DECLARATION_COUNT,
            "two_arm_rate_declaration_count": SGB_TWO_ARM_RATE_DECLARATION_COUNT,
            "exponential_audit_declaration_count":
                SGB_EXPONENTIAL_AUDIT_DECLARATION_COUNT,
            "generated_equation_8_declaration_count":
                SGB_GENERATED_EQUATION_8_DECLARATION_COUNT,
            "successor_recurrence_declaration_count":
                SGB_SUCCESSOR_RECURRENCE_DECLARATION_COUNT,
            "initial_recurrence_declaration_count":
                SGB_INITIAL_RECURRENCE_DECLARATION_COUNT,
            "measurable_recurrence_declaration_count":
                SGB_MEASURABLE_RECURRENCE_DECLARATION_COUNT,
            "path_integrability_declaration_count":
                SGB_PATH_INTEGRABILITY_DECLARATION_COUNT,
            "fixed_iid_declaration_count":
                SGB_FIXED_IID_DECLARATION_COUNT,
            "unconditional_recurrence_declaration_count":
                SGB_UNCONDITIONAL_RECURRENCE_DECLARATION_COUNT,
            "theorem_one_declaration_count":
                SGB_THEOREM_ONE_DECLARATION_COUNT,
            "generated_trajectory_compiled":
                sgb_evidence["generated_trajectory_compiled"],
            "conditional_law_bridge_compiled":
                sgb_evidence["conditional_law_bridge_compiled"],
            "two_arm_equation_11_compiled":
                sgb_evidence["two_arm_equation_11_compiled"],
            "source_equation_8_compiled":
                sgb_evidence["source_equation_8_compiled"],
            "generated_equation_8_kernel_bridge_compiled":
                sgb_evidence["generated_equation_8_kernel_bridge_compiled"],
            "two_arm_initial_recurrence_compiled":
                sgb_evidence["two_arm_initial_recurrence_compiled"],
            "fixed_history_successor_recurrence_compiled":
                sgb_evidence["fixed_history_successor_recurrence_compiled"],
            "trajectory_cond_distrib_recurrence_compiled":
                sgb_evidence["trajectory_cond_distrib_recurrence_compiled"],
            "path_integrability_compiled":
                sgb_evidence["path_integrability_compiled"],
            "conditional_expectation_one_step_recurrence_compiled":
                sgb_evidence[
                    "conditional_expectation_one_step_recurrence_compiled"
                ],
            "fixed_iid_contract_compiled":
                sgb_evidence["fixed_iid_contract_compiled"],
            "unconditional_recurrence_iteration_compiled":
                sgb_evidence["unconditional_recurrence_iteration_compiled"],
            "generic_expected_failure_mass_bound_compiled":
                sgb_evidence["generic_expected_failure_mass_bound_compiled"],
            "source_theorem_one_compiled":
                sgb_evidence["source_theorem_one_compiled"],
            "source_theorem_four_contract_audit_compiled":
                sgb_evidence["source_theorem_four_contract_audit_compiled"],
            "source_corollary_one_compiled":
                sgb_evidence["source_corollary_one_compiled"],
            "source_corollary_one_is_direct_theorem_one_consumer": True,
            "source_theorem_two_deterministic_starvation_consumer_compiled":
                sgb_evidence[
                    "source_theorem_two_deterministic_starvation_consumer_compiled"
                ],
            "source_theorem_two_nth_pull_bridge_compiled":
                sgb_evidence[
                    "source_theorem_two_nth_pull_bridge_compiled"
                ],
            "source_theorem_two_status": "blocked",
            "source_theorem_two_endpoint_verified":
                sgb_evidence["source_theorem_two_endpoint_verified"],
            "coordinate_update_integrability_verified": True,
            "uniform_reward_regularities_verified": False,
            "learning_rate_regime_verified": False,
            "global_tower_iteration_verified": True,
            "expected_failure_mass_verified": True,
            "paper_endpoint_verified": True,
            "paper_endpoint_verified_scope": "Theorem 1 only",
            "theorem_four_endpoint_verified": False,
        },
        "textbook_chapter_16": {
            "compiled_source_record_id": CH16_COMPILED_ID,
            "compiled_event_regret_record_id": CH16_EVENT_REGRET_ID,
            "blocked_terminal_record_id": CH16_TERMINAL_ID,
            "dependency_declaration_count":
                ch16_evidence["dependency_declaration_count"],
            "event_regret_declaration_count":
                ch16_evidence["event_regret_declaration_count"],
            "finite_mean_gap_bridge_verified":
                ch16_evidence["finite_mean_gap_bridge_verified"],
            "source_terminals_verified":
                ch16_evidence["source_terminals_verified"],
        },
        "proof_graph": {
            "status": "prototype",
            "standalone_fixed_charge_sum": shared["standalone_fixed_charge_sum"],
            "union_fixed_charge": shared["union_fixed_charge"],
            "shared_declaration_count": shared["shared_declaration_count"],
            "best_zdd_nonterminal_nodes": best_zdd,
            "cng_root_count": cng["candidate_support"]["root_count"],
            "structural_discovery_established": cng["structural_discovery_established"],
            "search_speedup_established": False,
        },
        "matched_workflow_study": {
            "source_record_id": target_id,
            "numerical_results_present": False,
            "provider_runs_present": False,
            "grades_present": False,
            "analysis_results_present": False,
        },
    }


def add_payload(payload, rel, data):
    rel = require_safe_relative(rel)
    if rel in payload:
        raise ValueError("duplicate archive path: " + rel)
    data = canonical_text_bytes(rel, data)
    require_anonymous_bytes(rel, data)
    payload[rel] = data


def read_regular(rel):
    path = REPO_ROOT / rel
    if not path.is_file() or path.is_symlink():
        raise ValueError("missing or non-regular allowlisted file: " + rel)
    try:
        path.resolve().relative_to(REPO_ROOT.resolve())
    except ValueError:
        raise ValueError("allowlisted file resolves outside repository: " + rel)
    return path.read_bytes()


def proof_report_from_path(path):
    report = load_json(path)
    required = ("shared_library", "zdd", "hypergraph", "graph")
    if any(key not in report for key in required):
        raise ValueError("proof-graph report is missing structural fields")
    return sanitize_json(report)


def validate_graph_pair(graph_path, report):
    expected = report["graph"].get("sha256")
    raw_graph = graph_path.read_bytes()
    actual = sha256_bytes(raw_graph)
    if expected != actual:
        raise ValueError("proof graph/report SHA-256 mismatch")
    graph = json.loads(raw_graph.decode("utf-8"))
    counts = graph.get("counts")
    if counts != report["graph"].get("counts"):
        raise ValueError("proof graph/report count mismatch")
    # The submitted pair is authenticated in its original byte presentation.
    # The anonymous archive then stores canonical JSON and rebinds its report
    # to those exact packaged bytes, avoiding CRLF/LF hash drift.
    graph_data = canonical_json(graph)
    report["graph"]["sha256"] = sha256_bytes(graph_data)
    return graph_data, report


def build_payload(proof_graph=None, proof_report_path=None, allow_missing_graph=False):
    if (proof_graph is None) != (proof_report_path is None):
        raise ValueError("proof graph and report must be supplied together")
    if proof_graph is None and not allow_missing_graph:
        raise ValueError("submission build requires --proof-graph and --proof-graph-report")

    tracked = git_tracked_files()
    payload = {}
    for source, destination in sorted(EXPLICIT_COPIES.items()):
        add_payload(payload, destination, read_regular(source))
    for rel in source_tree_files(tracked):
        add_payload(payload, rel, read_regular(rel))
    # Build the anonymous base binding before adding the evaluation layer.  The
    # protocol's public Git commit is replaced by a schema-compatible opaque
    # reference; the archive intentionally contains no Git object database.
    base_manifest = anonymous_base_manifest(payload)
    anonymous_reference = base_manifest["schema_compatibility_reference"]
    add_payload(payload, "evidence/anonymous-base-manifest.json",
                canonical_json(base_manifest))
    for rel in evaluation_files(tracked):
        data = anonymize_evaluation_bytes(rel, read_regular(rel), anonymous_reference)
        destination = rel
        if rel == PUBLIC_CANDIDATE_RECORD:
            destination = ANONYMOUS_CANDIDATE_RECORD
        elif rel == PUBLIC_ISOLATION_CANDIDATE_RECORD:
            destination = ANONYMOUS_ISOLATION_CANDIDATE_RECORD
        elif rel == PUBLIC_AGENT_LIFECYCLE_RECORD:
            destination = ANONYMOUS_AGENT_LIFECYCLE_RECORD
        elif rel == PUBLIC_AGENT_IMAGE_RECORD:
            destination = ANONYMOUS_AGENT_IMAGE_RECORD
        elif rel == PUBLIC_AGENT_OUTER_BOUNDARY_RECORD:
            destination = ANONYMOUS_AGENT_OUTER_BOUNDARY_RECORD
        add_payload(payload, destination, data)
    for rel in TARGET_DRIFT_WORKFLOW_FILES:
        if rel not in tracked:
            raise ValueError("untracked or missing target-drift workflow: " + rel)
        data = anonymize_evaluation_bytes(rel, read_regular(rel), anonymous_reference)
        add_payload(payload, rel, data)
    for rel in TARGET_DRIFT_TOOLS:
        if rel not in tracked:
            raise ValueError("untracked or missing target-drift tool: " + rel)
        data = anonymize_evaluation_bytes(rel, read_regular(rel), anonymous_reference)
        add_payload(payload, rel, data)
    for rel in SOURCE_CONTRACT_AUDIT_FILES + SOURCE_CONTRACT_AUDIT_TOOLS:
        if rel not in tracked:
            raise ValueError("untracked or missing source-contract audit evidence: " + rel)
        data = anonymize_evaluation_bytes(rel, read_regular(rel), anonymous_reference)
        add_payload(payload, rel, data)
    rebind_anonymous_external_comparator(payload)
    rebind_anonymous_source_contract_audit(payload, anonymous_reference)
    for source, destination in sorted(EVIDENCE_JSON.items()):
        value = sanitize_json(load_json(REPO_ROOT / source))
        add_payload(payload, destination, canonical_json(value))
    for rel in PROOF_GRAPH_TEST_EVIDENCE:
        value = sanitize_json(load_json(REPO_ROOT / rel))
        add_payload(payload, rel, canonical_json(value))

    if proof_report_path is None:
        report = sanitize_json(load_json(
            REPO_ROOT / "research-wiki" / "proof-graph" / "benchmark_report.json"
        ))
    else:
        proof_graph = Path(proof_graph).resolve()
        proof_report_path = Path(proof_report_path).resolve()
        if not proof_graph.is_file() or proof_graph.is_symlink():
            raise ValueError("proof graph is missing or non-regular")
        if not proof_report_path.is_file() or proof_report_path.is_symlink():
            raise ValueError("proof graph report is missing or non-regular")
        report = proof_report_from_path(proof_report_path)
        graph_data, report = validate_graph_pair(proof_graph, report)
        add_payload(payload, "evidence/proof-graph/current-proof-graph.json", graph_data)
        add_payload(payload, "evidence/proof-graph/current-benchmark-report.json",
                    canonical_json(report))

    ledger = build_claim_ledger(report)
    add_payload(payload, "evidence/claim-ledger.json", canonical_json(ledger))
    return payload


def manifest_for(payload, graph_included):
    entries = []
    digest = hashlib.sha256()
    for rel in sorted(payload):
        data = payload[rel]
        item = {
            "path": rel,
            "bytes": len(data),
            "sha256": sha256_bytes(data),
        }
        entries.append(item)
        digest.update(rel.encode("utf-8") + b"\0")
        digest.update(item["sha256"].encode("ascii") + b"\0")
        digest.update(str(item["bytes"]).encode("ascii") + b"\n")
    anonymous_base = json.loads(payload["evidence/anonymous-base-manifest.json"].decode("utf-8"))
    return {
        "schema_version": 1,
        "artifact_title": "ABRL anonymous Lean/code artifact",
        "archive_root": ARCHIVE_ROOT,
        "source_tree_digest": digest.hexdigest(),
        "file_count": len(entries),
        "files": entries,
        "proof_graph": {
            "included": graph_included,
            "interpretation": "Environment-level direct-constant dependency export; not an elaborator trace.",
        },
        "anonymous_base": {
            "tree_sha256": anonymous_base["tree_sha256"],
            "git_object_database_included": False,
            "target_drift_materialization_ready": False,
        },
        "anonymity": {
            "positive_allowlist": True,
            "authoring_repository_metadata_included": False,
            "source_pdfs_included": False,
            "unrun_evaluation_outputs_included": False,
        },
    }


def write_zip(output_path, payload, manifest):
    output_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_data = canonical_json(manifest)
    require_anonymous_bytes("ARTIFACT_MANIFEST.json", manifest_data)
    with zipfile.ZipFile(str(output_path), "w", compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        complete = dict(payload)
        complete["ARTIFACT_MANIFEST.json"] = manifest_data
        for rel in sorted(complete):
            info = zipfile.ZipInfo(ARCHIVE_ROOT + "/" + rel, FIXED_ZIP_TIME)
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, complete[rel], compress_type=zipfile.ZIP_DEFLATED,
                             compresslevel=9)


def build_archive(output_path, proof_graph=None, proof_report_path=None,
                  allow_missing_graph=False):
    payload = build_payload(proof_graph, proof_report_path, allow_missing_graph)
    manifest = manifest_for(payload, proof_graph is not None)
    write_zip(Path(output_path), payload, manifest)
    return {
        "archive": Path(output_path).name,
        "bytes": Path(output_path).stat().st_size,
        "file_count": manifest["file_count"],
        "sha256": sha256_file(Path(output_path)),
        "source_tree_digest": manifest["source_tree_digest"],
        "proof_graph_included": manifest["proof_graph"]["included"],
    }


def build_parser():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--proof-graph", type=Path, required=True,
                        help="current compact JSON produced by proof_graph_export")
    parser.add_argument("--proof-graph-report", type=Path, required=True,
                        help="benchmark report whose graph digest matches --proof-graph")
    return parser


def main(argv=None):
    args = build_parser().parse_args(argv)
    result = build_archive(
        args.output_dir / ARCHIVE_NAME,
        proof_graph=args.proof_graph,
        proof_report_path=args.proof_graph_report,
    )
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
