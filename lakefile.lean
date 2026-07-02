import Lake
open Lake DSL

package bandit_rl_proof where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

@[default_target]
lean_lib BanditRLProof

lean_lib Tests
