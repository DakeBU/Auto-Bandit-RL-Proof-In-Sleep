from common_v1 import *
headers=load(CONTRACT/'planned-public-headers-v1.json')
bodies={
'causalPredict_prefix':''' := by
  have hprefix : List.ofFn (fun i : Fin t => y i) = List.ofFn (fun i : Fin t => z i) := by
    apply congrArg List.ofFn
    funext i
    exact hpast i i.isLt
  exact congrArg (fun l => A l.reverse) hprefix
''',
'binary_mean_minimizer':''' := by
  have hy : ∀ t < h.length, binaryValues h t ∈ Icc (0 : ℝ) 1 := by
    intro t _
    unfold binaryValues
    split_ifs <;> norm_num
  exact ⟨empiricalMean_mem (binaryValues h) h.length hpos hy,
    fun u _ => empiricalMean_minimizes (binaryValues h) h.length hpos u⟩
''',
'conditional_square_lower':''' := by
  nlinarith [sq_nonneg (x - polyaNext h)]
'''}
aux='''
theorem binaryStream_cons_prefix (b : Bool) (h : List Bool) (t : ℕ) (ht : t < h.length) :
    binaryStream (b :: h) t = binaryStream h t := by
  unfold binaryStream
  simp only [List.reverse_cons]
  rw [List.getElem?_append_left (by simpa using ht)]

theorem binaryStream_cons_last (b : Bool) (h : List Bool) :
    binaryStream (b :: h) h.length = b := by
  simp [binaryStream, List.reverse_cons, List.getElem?_append_right]

theorem binaryValues_cons_prefix (b : Bool) (h : List Bool) (t : ℕ) (ht : t < h.length) :
    binaryValues (b :: h) t = binaryValues h t := by
  simp only [binaryValues, binaryStream_cons_prefix b h t ht]

theorem causalPredict_history (A : List Bool → ℝ) (h : List Bool) :
    causalPredict A (binaryStream h) h.length = A h := by
  have hp : List.ofFn (fun i : Fin h.length => binaryStream h i) = h.reverse := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_ofFn]
      simp [binaryStream, hj]
  simp only [causalPredict, hp, List.reverse_reverse]

theorem causalPredict_cons_last (A : List Bool → ℝ) (b : Bool) (h : List Bool) :
    causalPredict A (binaryStream (b :: h)) h.length = A h := by
  rw [causalPredict_prefix A (binaryStream (b :: h)) (binaryStream h) h.length
    (binaryStream_cons_prefix b h)]
  exact causalPredict_history A h

'''
addition='\n'.join(headers[n]+body for n,body in bodies.items())+aux
ending='end BanditRL.OnlineLearning.GuessingLower';source=PUBLIC.read_text(encoding='utf-8')
write(RUN/'causal-addition-v1.lean.txt',addition)
write(RUN/'leaves/causal-v1.lean',source[:source.rindex(ending)]+addition+'\n'+ending+'\n')
gate('causal-attempt-v1','lake','env','lean',RUN/'leaves/causal-v1.lean')
