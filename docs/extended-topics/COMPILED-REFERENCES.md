# Compiled proof references at `280378670ca4647440f795aae1905149eff0063b`

Selected direct proof-value references; arrow points to a dependency.
Type-only references and external Mathlib references remain in the JSON report.
This is not a teaching graph or a utility score.

```mermaid
flowchart TD
  n0["Concentration.HasMGFUpperBoundAt.measure_ge_le_exp_add"]
  n1["arm_adaptive_mean_tail"]
  n2["fixed_mgf_abs_tail"]
  n3["independent_sum_mgf"]
  n4["lintegral_pullCount_threshold"]
  n5["robustMean_tail"]
  n6["robust_expected_regret"]
  n7["robust_integral_count_le"]
  n8["robust_large_count_tail"]
  n9["robust_lintegral_count_le"]
  n10["robust_selected_gap_le"]
  n11["robust_selected_small_radius_tail"]
  n12["scheduled_adaptive_mean_tail"]
  n13["scheduled_mean_tail"]
  n14["scheduled_tail_sum_le_two"]
  n15["truncated_centered_mgf"]
  n16["truncated_mean_tail"]
  n17["truncated_sum_abs_tail"]
  n18["truncated_sum_mean_tail"]
  n19["tuned_radius_le"]
  n20["UCB.meanGap_le_two_radius_of_confidenceScore_max"]
  n21["UCB.natCast_pullCount_le_threshold_add_selectedLargePullCount_indicator_sum"]
  n22["integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount"]
  n1 -->|"value"| n12
  n2 -->|"value"| n0
  n4 -->|"value"| n21
  n5 -->|"value"| n1
  n6 -->|"value"| n7
  n6 -->|"value"| n22
  n7 -->|"value"| n9
  n8 -->|"value"| n11
  n9 -->|"value"| n4
  n9 -->|"value"| n8
  n9 -->|"value"| n14
  n10 -->|"value"| n20
  n11 -->|"value"| n5
  n11 -->|"value"| n10
  n12 -->|"value"| n13
  n13 -->|"value"| n16
  n13 -->|"value"| n19
  n16 -->|"value"| n18
  n17 -->|"value"| n2
  n17 -->|"value"| n3
  n17 -->|"value"| n15
  n18 -->|"value"| n17
  classDef frozen fill:#e2e8f0,stroke:#475569
  class n0 frozen
  class n20 frozen
  class n21 frozen
  class n22 frozen
```

Raw compiled graph SHA-256: `40a228cfca9ce30a98a0d7af5eb16aa22f62e0759ae57e2f383f8566e394e973`.
