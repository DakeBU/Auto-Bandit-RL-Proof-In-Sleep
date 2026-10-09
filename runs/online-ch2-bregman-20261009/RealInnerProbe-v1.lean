import BanditRLProof.OnlineBregmanProximal
import Mathlib.Analysis.InnerProductSpace.Basic
set_option pp.all true in
#check RCLike.inner_apply'
#synth Inner ℝ ℝ
#synth InnerProductSpace ℝ ℝ
#reduce inner ℝ (2 : ℝ) 3
example (a b : ℝ) : inner ℝ a b = a * b := by
  exact RCLike.inner_apply' a b
