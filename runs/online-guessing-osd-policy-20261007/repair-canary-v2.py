from common_v1 import *
headers()
old=CANARY.read_text(encoding='utf-8');assert old==(RUN/'leaves/whole-canary-before-first-build-v1.lean.txt').read_text(encoding='utf-8')
text=old.replace('simp only [selected, policy, loss, EReal.toReal_coe, zero_sub, abs_neg, output]\n','simp only [selected, policy, loss, EReal.toReal_coe, zero_sub, abs_neg, output]\n  rfl\n')
word=['zero','one','two','three','four']
for family in ['a','b']:
 labels='labels'+family.upper();values=['1','-1','1','-1'] if family=='a' else ['-1','1','-1','1']
 for k in range(4):
  before=f'''theorem g{family}_{word[k]} : g{family} {k} = {values[k]} := by
  rw [selected_rule]
'''
  after=f'''theorem g{family}_{word[k]} : g{family} {k} = {values[k]} := by
  change selected V eta (fun s => loss ({labels} s)) (1 / 2) policy {k} = {values[k]}
  rw [selected_rule eta {labels} (1 / 2) {k}]
  change (if |{labels} {k}| < {family} {k} then 1
    else if {family} {k} < |{labels} {k}| then -1
    else if ht : 0 < ({k} : ℕ) then if |{labels} 0| = 0 then 1 else -1 else 1) = {values[k]}
'''
  assert before in text; text=text.replace(before,after)
 values=['0','1 / 2','0','1 / 2'] if family=='a' else ['1','1 / 2','1','1 / 2']
 for k in range(1,5):
  before=f'''theorem {family}_{word[k]} : {family} {k} = {values[k-1]} := by
  rw [BanditRL.OnlineGuessingSubgradientPolicy.step_clamp]
'''
  after=f'''theorem {family}_{word[k]} : {family} {k} = {values[k-1]} := by
  change output V eta (fun s => loss ({labels} s)) (1 / 2) policy ({k-1} + 1) = {values[k-1]}
  rw [BanditRL.OnlineGuessingSubgradientPolicy.step_clamp eta {labels} (1 / 2) policy {k-1}]
'''
  assert before in text;text=text.replace(before,after)
text=text.replace('have hs : Real.sqrt (4 : ℝ) = 2 := by norm_num','have hs : Real.sqrt (4 : ℕ) = (2 : ℝ) := by norm_num')
extract=lambda value:{m.group(1):m.group(0).strip() for m in re.finditer(r'(?m)^theorem (\w+)\b[\s\S]*?(?= :=)',value)}
assert extract(old)==extract(text)
write(RUN/'canary-body-repair-v2.json',dict(original_failure='public-canary-focused-v1-01.log',original_canary_sha256=sha(CANARY),changes=['Finish definitional selected-rule equality after simplification using rfl','Explicitly unfold aliases and instantiate labels/time before rewriting so higher-order matcher does not infer label stream','Normalize sqrt of exact natural cast used by frozen performance type, not separate real-literal form'],canary_header_changes=False,public_statement_or_body_changes=False,source_contract_changes=False,mathematical_plan_changes=False))
write(RUN/'leaves/whole-canary-body-v2.lean.txt',text);CANARY.write_bytes(text.encode('utf-8'))
headers();gate('public-canary-focused-v2-01','lake','build','BanditRLProof.OnlineGuessingSubgradientPolicy','Tests.OnlineGuessingSubgradientPolicyCanary')
print('Full new canary module actually compiled; original matcher failure retained, all test types and public types unchanged.')
