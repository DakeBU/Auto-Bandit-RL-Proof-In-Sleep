from common_v1 import *
fixed();targets=load(CONTRACT/'targets-v1.json')['targets']
context=(CONTRACT/'public-context-v1.lean').read_text(encoding='utf8')
neutral=(RUN/'neutral-packet-v1.lean').read_text(encoding='utf8')
lines=[context,neutral,'open BanditRL.OnlineLearning\nnamespace DraftTypeVerification\nuniverse v\n']
def proposition(header):
 head=header[len('theorem '):];head=head[head.index(' '):] if ' ' in head else head
 depth=0
 for i,c in enumerate(head):
  if c in '([{':depth+=1
  elif c in ')]}':depth-=1
  elif c==':' and depth==0:
   binders=head[:i].strip().replace('Type*','Type v');body=head[i+1:].strip()
   return ('∀ '+binders+',\n'+body) if binders else body
 raise AssertionError(header)
for i,row in enumerate(targets):
 lines.append(('open NoRegretCounterexample\n' if i==3 else '')+'def A%03d : Prop := '%(i+1)+proposition(row['header'])+'\n')
 lines.append('example : NeutralPacket.B%03d = A%03d := by rfl\n'%(i+1,i+1))
lines+=['''def A010 : Prop := ∀ y : ℕ → ℝ, (∀ t, y t ∈ Set.Icc (0 : ℝ) 1) →
  NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x-y t)^2) (meanPredict y)
example : NeutralPacket.B010 = A010 := by rfl
def A011 : Prop := ∀ (X : Type v) (V : Set X) (f : ℕ → X → ℝ) (p : ℕ → X) (b : X → ℕ → ℝ),
  (∀ u ∈ V, ∀ᶠ N in atTop, comparatorRegret f p u N / N ≤ b u N) →
  (∀ u ∈ V, Tendsto (b u) atTop (nhds 0)) → NoRegret V f p
example : NeutralPacket.B011 = A011 := by rfl
def A012 : Prop := ∀ (X : Type v) (f : ℕ → X → ℝ) (p : ℕ → X) (u : X) (N : ℕ),
  comparatorRegret f p u N = ∑ t ∈ Finset.range N, (f t (p t) - f t u)
example : NeutralPacket.B012 = A012 := by rfl
end DraftTypeVerification
''']
write(RUN/'draft-proposition-identities-v1.lean','\n'.join(lines))
gate('draft-proposition-identities-v1','lake','env','lean',RUN/'draft-proposition-identities-v1.lean')
write(RUN/'draft-type-verification-v1.json',dict(status='twelve proposed closed proposition identities elaborated',targets_sha256=sha(CONTRACT/'targets-v1.json'),neutral_sha256=sha(RUN/'neutral-packet-v1.lean'),type_identity_source_sha256=sha(RUN/'draft-proposition-identities-v1.lean'),actual_public_target_proofs_begun=False,compiled_type_identities_not_target_proofs=True,new_theorem_bodies=0))
fixed()
