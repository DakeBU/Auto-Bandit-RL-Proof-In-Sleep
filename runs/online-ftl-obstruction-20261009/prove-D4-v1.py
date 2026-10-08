from append_leaf_v1 import *
assert load(RUN/'D3-attempt-v1.json')['actual_build_exit']==0
body=''' := by
  have hy := dyadicObservation_unit
  have hn : ¬ ∃ a : ℝ, Tendsto (fun T : ℕ =>
      comparatorRegret (fun t x => (x - dyadicObservation t)^2)
        (meanPredict dyadicObservation) 0 T / (T : ℝ)) atTop (nhds a) := by
    rintro ⟨a, ha⟩
    have hs := (meanPredict_fixedRegret_limit_iff dyadicObservation hy 0 a).mp ha
    have hh := (tendsto_const_nhds.sub dyadic_empiricalMean_subsequences.1).pow 2
    have hl := (tendsto_const_nhds.sub dyadic_empiricalMean_subsequences.2).pow 2
    have eh : -a = ((0 : ℝ) - 2/3)^2 :=
      tendsto_nhds_unique (hs.comp dyadic_horizons_tendsto.1) hh
    have el : -a = ((0 : ℝ) - 1/3)^2 :=
      tendsto_nhds_unique (hs.comp dyadic_horizons_tendsto.2) hl
    norm_num at eh el
    linarith
  refine ⟨meanPredict_noRegret dyadicObservation hy,
    meanPredict_bestRegret_average_tendsto_zero dyadicObservation hy, hn, ?_⟩
  intro hL
  obtain ⟨a, ha, hlim⟩ := hL 0 (by norm_num)
  exact hn ⟨a, hlim⟩
'''
append_leaf(3,body)
