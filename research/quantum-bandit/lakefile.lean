import Lake
open Lake DSL
package quantum_bandit_adapter where
  version := v!"0.1.0"
require bandit_rl_proof from "../.."
require aspbe from "../../../quantum"
@[default_target]
lean_lib QuantumBanditAdapter
lean_lib Canary
lean_lib AdaptiveTranscript
lean_lib AdaptiveTranscriptCanary
lean_exe dependency_export where
  root := `DependencyExport
  supportInterpreter := true
lean_exe adaptive_dependency_export where
  root := `AdaptiveDependencyExport
  supportInterpreter := true
