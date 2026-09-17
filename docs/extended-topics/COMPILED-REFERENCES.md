# Compiled proof references at `ae3e6571fd39c4730d59dbc38466f9211bad2cce`

Selected direct proof-value references; arrow points to a dependency.
Type-only references and external Mathlib references remain in the JSON report.
This is not a teaching graph or a utility score.

```mermaid
flowchart TD
  n0["Concentration.HasMGFUpperBoundAt.measure_ge_le_exp_add"]
  n1["adaptive_corrupted_clipped_mean_tail"]
  n2["arm_adaptive_mean_tail"]
  n3["arm_corrupted_clipped_mean_tail"]
  n4["bounded_centering_mgf"]
  n5["clipped_centered_mgf"]
  n6["clipped_mean_tail"]
  n7["clipped_observed_prefix"]
  n8["clipped_prefix_corruption_le"]
  n9["clipped_sum_abs_tail"]
  n10["fixed_mgf_abs_tail"]
  n11["independent_sum_mgf"]
  n12["integral_clip_bias_le"]
  n13["integral_sq_clip_le"]
  n14["lintegral_pullCount_threshold"]
  n15["observed_corrupted_clipped_mean_tail"]
  n16["robustMean_tail"]
  n17["robust_expected_regret"]
  n18["robust_integral_count_le"]
  n19["robust_large_count_tail"]
  n20["robust_lintegral_count_le"]
  n21["robust_selected_gap_le"]
  n22["robust_selected_small_radius_tail"]
  n23["scheduled_adaptive_clipped_mean_tail"]
  n24["scheduled_adaptive_mean_tail"]
  n25["scheduled_clipped_mean_tail"]
  n26["scheduled_mean_tail"]
  n27["scheduled_tail_sum_le_two"]
  n28["sum_mean_tail_of_centered"]
  n29["truncated_centered_mgf"]
  n30["truncated_mean_tail"]
  n31["truncated_sum_abs_tail"]
  n32["truncated_sum_mean_tail"]
  n33["tuned_radius_le"]
  n34["UCB.meanGap_le_two_radius_of_confidenceScore_max"]
  n35["UCB.natCast_pullCount_le_threshold_add_selectedLargePullCount_indicator_sum"]
  n36["integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount"]
  n1 -->|"value"| n8
  n1 -->|"value"| n23
  n2 -->|"value"| n24
  n3 -->|"value"| n1
  n5 -->|"value"| n4
  n5 -->|"value"| n13
  n6 -->|"value"| n9
  n6 -->|"value"| n12
  n6 -->|"value"| n28
  n9 -->|"value"| n5
  n9 -->|"value"| n10
  n9 -->|"value"| n11
  n10 -->|"value"| n0
  n14 -->|"value"| n35
  n15 -->|"value"| n1
  n15 -->|"value"| n7
  n16 -->|"value"| n2
  n17 -->|"value"| n18
  n17 -->|"value"| n36
  n18 -->|"value"| n20
  n19 -->|"value"| n22
  n20 -->|"value"| n14
  n20 -->|"value"| n19
  n20 -->|"value"| n27
  n21 -->|"value"| n34
  n22 -->|"value"| n16
  n22 -->|"value"| n21
  n23 -->|"value"| n25
  n24 -->|"value"| n26
  n25 -->|"value"| n6
  n25 -->|"value"| n33
  n26 -->|"value"| n30
  n26 -->|"value"| n33
  n29 -->|"value"| n4
  n30 -->|"value"| n32
  n31 -->|"value"| n10
  n31 -->|"value"| n11
  n31 -->|"value"| n29
  n32 -->|"value"| n28
  n32 -->|"value"| n31
  classDef frozen fill:#e2e8f0,stroke:#475569
  class n0 frozen
  class n34 frozen
  class n35 frozen
  class n36 frozen
```

Raw compiled graph SHA-256: `c71bb8531d0ae22f9102d94ae3414f0988a0066d3d5a56fa5b399b5c3ecc6516`.
