from body_repair import *
repair('phi_range',3,[('''    simpa using rpow_one_add_lt_one_add_mul_self
      (by norm_num : (-1 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≠ 0) hb0 hb1''','''    convert rpow_one_add_lt_one_add_mul_self
      (by norm_num : (-1 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≠ 0) hb0 hb1 using 1 <;> norm_num''')],
 'Ordinary simp leaves the real numeral sum1+1 in the Bernoulli base',
 'Normalize the explicit real base2 with convert/norm_num; concavity, derivatives and frozen terminal are unchanged')
