# Architect: dependencies and single proof route

L1: AEStronglyMeasurable.measurable_mk + Measurable.of_comap_le -> Measurable.exists_eq_measurable_comp -> existing continuous Set.projIcc, subtype coercion, projIcc_of_mem -> ae_all_iff. A single policy for every t is chosen before horizons. No extra global bound is assumed; projection supplies a globally bounded version.

L2: AEStronglyMeasurable.measurable_mk -> existing predictable_private_seed_independent -> IndepFun.congr using exact original-to-version AE equality. Both Y/S ambient measurability are retained, seed independent of WHOLE infinite target stream. Neither bounds nor same law added to independence target.

L3: L2 -> ambient AEStronglyMeasurable.mono from F_t<=generatedInfo<=ambient -> memLp_of_bounded -> expectedFixedMinimum_eq_variance + iid_cumulative_prediction_decomposition -> finite sum of integral_nonneg squares. Output remains the original P. Alternatively L1 and AE integral transport can audit equivalence, but is not a competing proof route.

Owning module BanditRLProof/OnlineGuessingAECausal.lean, namespace BanditRL.OnlineLearning, existing project/pins. No new clipping definition; use mathlib Set.projIcc directly (a Tsallis-local clippedUnitReal wrapper already exists and is not duplicated). Three route-specific derived statements, not generic theory copied from mathlib or three new source theorems. No external/Optlib dependency or pin/toolchain upgrade. Foundational API probes are retrieval evidence only.

Lean graph: planned three canonical public declaration nodes and actual reviewed VALUE dependencies; no solid edge inferred from imports. Overview: only named AE subobligation, no chapter badge. Conceptual graph: none-found-with-reason; this is a standard measurable-version/factorization transport within the same information model, not an independently established cross-setting functor. Source-qualified Book mapping will reuse shared registry IDs. No competing multi-chapter writing.
