from common_v1 import *
fixed(proving=True);assert load(RUN/'initial-leaf-compiled-v2.json')['initial_source_bound_closed_locally']
write(RUN/'30_lower-refined-v1.md','Single staged /root lowerworker / medium. Use produced feasible empirical-mean leaders and actual Lemma1.2; subtract hindsight sum; split true stability sum into initial and shifted positive rounds. Apply newly compiled initial1/4 and unchanged stability at t+1. Exact range(T-1), real denominator t+2; same causal predictor and final comparator. No certificate/extra hypothesis; all original public bytes preserved.')
old=PUBLIC.read_bytes();end=b'end BanditRL.OnlineLearning\r\n' if old.endswith(b'\r\n') else b'end BanditRL.OnlineLearning\n';assert old.endswith(end)
write(RUN/'snapshots/initial-compiled-before-refined.raw',old)
header=load(CONTRACT/'new-public-headers-v1.json')['meanPredict_regret_refined']
body=''' := by
  cases T with
  | zero => omega
  | succ n =>
    have hleader := lemma_1_2 (Set.Icc (0 : ℝ) 1) (fun t x => (x - y t)^2)
      (empiricalMean y) (n + 1)
      (fun k hk hkT => empiricalMean_mem y k hk
        (fun i hi => hy i (lt_of_lt_of_le hi hkT)))
      (fun k hk hkT u hu => empiricalMean_minimizes y k hk u)
    let f : ℕ → ℝ := fun t =>
      (meanPredict y t - y t)^2 - (empiricalMean y (t + 1) - y t)^2
    have hreg : (∑ t ∈ Finset.range (n + 1), (meanPredict y t - y t)^2) -
        (∑ t ∈ Finset.range (n + 1), (empiricalMean y (n + 1) - y t)^2) ≤
        ∑ t ∈ Finset.range (n + 1), f t := by
      simp only [f, Finset.sum_sub_distrib]
      linarith
    have hinitial : f 0 ≤ (1 : ℝ) / 4 :=
      meanPredict_initial_stability y (hy 0 (by omega))
    have hrest : (∑ t ∈ Finset.range n, f (t + 1)) ≤
        ∑ t ∈ Finset.range n, 4 / ((t : ℝ) + 2) := by
      apply Finset.sum_le_sum
      intro t ht
      have hs := meanPredict_stability y (t + 1)
        (fun i hi => hy i (by have := Finset.mem_range.mp ht; omega))
      simpa only [f, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hs
    have htotal : (∑ t ∈ Finset.range (n + 1), f t) ≤
        (1 : ℝ) / 4 + ∑ t ∈ Finset.range n, 4 / ((t : ℝ) + 2) := by
      rw [Finset.sum_range_succ']
      exact (add_le_add hrest hinitial).trans_eq (add_comm _ _)
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hreg.trans htotal

'''
PUBLIC.write_bytes(old[:-len(end)]+('/-- Orabona v10 Theorem 1.3 proof, printed p5: retain the sharp initial term and exact positive-round tail. -/\n'+header+body).encode('utf-8')+end)
fixed(proving=True)
gate('focused-refined-v1','lake','build','BanditRLProof.OnlineLearningFTL')
write(RUN/'refined-focused-compiled-v1.json',dict(status='focused compiled; full type/axiom/canary/VALUE/BODY/combined/site/FINAL/PR pending',public_name=PRE+'meanPredict_regret_refined',chapter_complete=False,goal_complete=False))
