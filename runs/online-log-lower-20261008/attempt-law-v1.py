from common_v1 import *
headers=load(CONTRACT/'planned-public-headers-v1.json')
bodies={
'branch_mass': ''' := by
  simp only [pathWeight, Bool.false_eq_true, ↓reduceIte]
  ring
''',
'pathWeight_nonneg': ''' := by
  induction h with
  | nil => norm_num [pathWeight]
  | cons b h ih =>
    cases b
    · exact mul_nonneg ih (sub_nonneg.mpr (probability_mem h).2.le)
    · exact mul_nonneg ih (probability_mem h).1.le
''',
'prefix_mass_one': ''' := by
  induction T with
  | zero => simp [pathWeight]
  | succ T ih =>
    rw [sum_vectors_succ]
    simpa only [branch_mass] using ih
''',
'prefix_distribution': ''' := by
  constructor
  · intro v _
    exact pathWeight_nonneg v.toList
  · exact prefix_mass_one T
''',
'prefixMeasure_probability': ''' := by
  exact BanditRLProof.Exp3.finiteActionMeasure_isProbabilityMeasure
    univ (fun v => pathWeight v.toList) (prefix_distribution T)
''',
'pathExpectation_integral': ''' := by
  exact BanditRLProof.Exp3.integral_finiteActionMeasure_eq_sum
    univ (fun v => pathWeight v.toList) (prefix_distribution T) (fun v => f v.toList)
'''}
aux='''
/-- Split all newest-first histories into the next bit and the prior history. -/
private def vectorConsEquiv (T : ℕ) :
    Bool × List.Vector Bool T ≃ List.Vector Bool (T + 1) where
  toFun p := p.1 ::ᵥ p.2
  invFun v := (v.head, v.tail)
  left_inv p := by cases p; simp
  right_inv v := List.Vector.cons_head_tail v

theorem sum_vectors_succ (T : ℕ) (f : List Bool → ℝ) :
    (∑ v : List.Vector Bool (T + 1), f v.toList) =
      ∑ v : List.Vector Bool T, (f (false :: v.toList) + f (true :: v.toList)) := by
  rw [← (vectorConsEquiv T).sum_comp (fun v => f v.toList)]
  rw [Fintype.sum_prod_type]
  simp [vectorConsEquiv, Finset.sum_add_distrib, add_comm]

'''
ending='end BanditRL.OnlineLearning.GuessingLower'
source=PUBLIC.read_text(encoding='utf-8')
addition=headers['branch_mass']+bodies['branch_mass']+'\n'+headers['pathWeight_nonneg']+bodies['pathWeight_nonneg']+aux
addition+='\n'.join(headers[n]+bodies[n] for n in list(bodies)[2:])
write(RUN/'leaves/law-v1.lean',source[:source.rindex(ending)]+addition+'\n'+ending+'\n')
write(RUN/'law-addition-v1.lean.txt',addition)
gate('law-attempt-v1','lake','env','lean',RUN/'leaves/law-v1.lean')
