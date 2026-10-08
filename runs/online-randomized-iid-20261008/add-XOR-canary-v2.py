from common_reviewed_v2 import *

headers_fixed(7)
assert load(RUN/'canary-core-focused-build-v3-exit.json')['exit_code']==0
write(RUN/'snapshots'/'canary-core-compiled-v3.raw',CANARY.read_bytes())
context='''
/-- Four equally likely bit-pairs: all three pairs are independent, but not all three jointly. -/
local instance : MeasurableSpace (Fin 4) := ⊤
local instance : MeasurableSingletonClass (Fin 4) := ⟨fun _ => trivial⟩

def fourLaw : Measure (Fin 4) :=
  (1 / 4 : ℝ≥0∞) • Measure.dirac 0 + (1 / 4 : ℝ≥0∞) • Measure.dirac 1 +
    (1 / 4 : ℝ≥0∞) • Measure.dirac 2 + (1 / 4 : ℝ≥0∞) • Measure.dirac 3

instance fourLaw_probability : IsProbabilityMeasure fourLaw := by
  constructor
  norm_num [fourLaw]

def xorX (q : Fin 4) : ℝ := if q.val < 2 then 0 else 1
def xorY (q : Fin 4) : ℝ := if q.val % 2 = 0 then 0 else 1
def xorTape (q : Fin 4) : ℝ := if xorX q = xorY q then 0 else 1

'''
proof=''' := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  by_cases h0s : (0 : ℝ) ∈ s <;> by_cases h1s : (1 : ℝ) ∈ s <;>
    by_cases h0t : (0 : ℝ) ∈ t <;> by_cases h1t : (1 : ℝ) ∈ t <;>
    norm_num [fourLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
      Set.indicator_apply, xorX, xorY, xorTape, h0s, h1s, h0t, h1t]

'''
for name,left,right in [('xor_targets_independent','xorX','xorY'),
        ('xor_tape_individually_independent_X','xorTape','xorX'),
        ('xor_tape_individually_independent_Y','xorTape','xorY')]:
    context+='theorem '+name+' : IndepFun '+left+' '+right+' fourLaw'+proof
context+='''theorem xor_seed_past_not_independent_current :
    ¬ IndepFun (fun q => (xorTape q, xorX q)) xorY fourLaw := by
  intro h
  have he := h.measure_inter_preimage_eq_mul {((0 : ℝ), (0 : ℝ))} {(0 : ℝ)}
    (measurableSet_singleton _) (measurableSet_singleton _)
  norm_num [fourLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
    Set.indicator_apply, xorX, xorY, xorTape] at he

theorem xor_seed_not_independent_whole_pair :
    ¬ IndepFun xorTape (fun q => (xorX q, xorY q)) fourLaw := by
  intro h
  exact xor_seed_past_not_independent_current
    (independent_private_seed_pair fourLaw xorTape xorX xorY (measurable_of_countable _)
      (measurable_of_countable _) (measurable_of_countable _) h xor_targets_independent)

theorem pairwise_seed_independence_is_insufficient :
    IndepFun xorX xorY fourLaw ∧ IndepFun xorTape xorX fourLaw ∧
      IndepFun xorTape xorY fourLaw ∧
      ¬ IndepFun (fun q => (xorTape q, xorX q)) xorY fourLaw :=
  ⟨xor_targets_independent, xor_tape_individually_independent_X,
    xor_tape_individually_independent_Y, xor_seed_past_not_independent_current⟩
'''
text=CANARY.read_text(encoding='utf8')
assert text.count('end Tests.OnlineGuessingRandomizedIID')==1
CANARY.write_bytes(text.replace('end Tests.OnlineGuessingRandomizedIID',
    context+'\nend Tests.OnlineGuessingRandomizedIID',1).encode('utf8'))
write(RUN/'leaves'/'canary-with-XOR-v2.lean',CANARY.read_bytes())
gate('canary-XOR-focused-build-v2','lake','build','Tests.OnlineGuessingRandomizedIIDCanary')
headers_fixed(7)
print('Actual XOR/four-atom pairwise-independence pitfall and core seeded infinite-IID canary compile.')
