# Architect

One route: nonnegative cumulative endpoints -> interval integrability from ContinuousOn Ici0 -> constant endpoint integral comparison using antitonicity -> finite sum -> adjacent interval telescope. Reuse pinned Mathlib intervalIntegral.integral_mono_on, ContinuousOn.intervalIntegrable_of_Icc and sum_integral_adjacent_intervals. Search actual local/card APIs before creating a general-purpose theorem. General sum inequality is mathlib-candidate, source-qualified wrapper must remain thin.

Future inverse-square-root energy summation can reuse the existing public Tsallis.two_mul_sqrt_sub_sqrt_le_sub_div_sqrt supporting-line inequality with reversed endpoints; do not copy its proof. Existing positive-eta weighted_potential_sum cannot cover initial zero energy without explicit branch treatment. Future actual OSD/state and zero-energy minimum correction remain open.
