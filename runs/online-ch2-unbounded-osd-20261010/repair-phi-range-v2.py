from body_repair import *
repair('phi_range',2,[
 ('Real.rpow_one_add_lt_one_add_mul_self','rpow_one_add_lt_one_add_mul_self'),
 ('(by norm_num : (0 : ℝ) ∈ Icc 0 1)','(by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)'),
 ('(show β ∈ Icc 0 1 from ⟨hb0.le, hb1.le⟩)','(show β ∈ Set.Icc 0 1 from ⟨hb0.le, hb1.le⟩)')],
 'Strict Bernoulli is a global declaration; interval membership annotations had ambiguous Set/Finset namespace and inferred Nat endpoints',
 'Use the actual global Bernoulli name and explicitly Set.Icc real membership; all analytic proof expressions and frozen terminal unchanged')
