from body_repair import *
repair('switching_loss_regular',2,[('''        simp only [switchLoss, inner_sub_right, mul_sub, abs_mul]''','''        change |switchSlope T t * inner ℝ v x - switchSlope T t * inner ℝ v y| = _
        rw [← mul_sub, ← inner_sub_right, abs_mul]''')],
    'simplifier left an unfactored difference inside absolute value',
    'Explicitly expose the real expression and factor the common switching slope before applying abs_mul')
