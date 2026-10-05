"""Construct unproved, type-checkable targets before any theorem body work."""
from pathlib import Path
import json
run=Path(__file__).parent
context='''import BanditRLProof.OnlineSubgradientPolicy
import BanditRLProof.OnlineHuber
import BanditRLProof.OnlineAffineSubgradient
import BanditRLProof.OnlineOptimalStep
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Tactic

noncomputable section
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineSubgradientPolicy
open scoped InnerProductSpace
namespace BanditRL.OnlineUnitScaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

abbrev V : Domain (E := E) := BanditRL.OnlineHuber.fullSpace
def scaledLoss (c : ℝ) (f : E → EReal) : E → EReal := fun y => f (c • y)
def scaledEta (c : ℝ) (η : ℕ → ℝ) : ℕ → ℝ := fun t => η t / c ^ 2
def scaledPolicy (c : ℝ) (p : SupportPolicy (E := E)) : SupportPolicy (E := E) :=
  fun t past h f => c • p t (fun i => scaledLoss c⁻¹ (past i))
    (fun i => c • h i) (scaledLoss c⁻¹ f)

'''
shared='(c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E))'
newrun='V (scaledEta c η) (fun s => scaledLoss c (loss s)) (c⁻¹ • x₁) (scaledPolicy c p)'
oldrun='V η loss x₁ p'
specs=[
 ('unit_exponents','{D : Type*} [AddCommGroup D] (X L H : D) (h : H + (L - X) = X)',
  'H = X + X - L'),
 ('regret_unit_exponents','{D : Type*} [AddCommGroup D] (X L : D)',
  '(X + X - (X + X - L) = L) ∧ ((X + X - L) + (L - X) + (L - X) = L)'),
 ('inverse_loss','(c : ℝ) (hc : 0 < c) (f : E → EReal)',
  'scaledLoss c⁻¹ (scaledLoss c f) = f'),
 ('proper_scaled_loss','(c : ℝ) (hc : 0 < c) (f : E → EReal) (hf : SourceProper f)',
  'SourceProper (scaledLoss c f)'),
 ('subgradient_scaled','(c : ℝ) (hc : 0 < c) (f : E → EReal) (hf : SourceProper f) (y g : E) (hg : g ∈ SourceSubdifferential f (c • y))',
  'c • g ∈ SourceSubdifferential (scaledLoss c f) y'),
 ('subdifferentiable_scaled','(c : ℝ) (hc : 0 < c) (f : E → EReal) (hf : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V f)',
  'BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (scaledLoss c f)'),
 ('hasGradientAt_scaled','(c : ℝ) (f : E → ℝ) (y g : E) (hf : HasGradientAt f g (c • y))',
  'HasGradientAt (fun z => f (c • z)) (c • g) y'),
 ('gradient_scaled','(c : ℝ) (f : E → ℝ) (y : E) (hf : DifferentiableAt ℝ f (c • y))',
  'gradient (fun z => f (c • z)) y = c • gradient f (c • y)'),
 ('step_scaling','(c : ℝ) (hc : 0 < c) (η : ℝ) (x g : E)',
  'c⁻¹ • (x - η • g) = c⁻¹ • x - (η / c ^ 2) • (c • g)'),
 ('wrong_step_scaling','(c : ℝ) (hc : 0 < c) (η : ℝ) (x g : E)',
  'c • (c⁻¹ • x - η • (c • g)) = x - (c ^ 2 * η) • g'),
 ('scaled_eta_positive','(c : ℝ) (hc : 0 < c) (η : ℕ → ℝ) (t : ℕ) (hη : 0 < η t)',
  '0 < scaledEta c η t'),
 ('history_scaling',shared+' (t : ℕ)',
  'history '+newrun+' t = fun i => c⁻¹ • history '+oldrun+' t i'),
 ('output_scaling',shared+' (t : ℕ)',
  'output '+newrun+' t = c⁻¹ • output '+oldrun+' t'),
 ('selected_scaling',shared+' (t : ℕ)',
  'selected '+newrun+' t = c • selected '+oldrun+' t'),
 ('legal_feedback_scaling',shared+' (T : ℕ) (hproper : ∀ t < T, SourceProper (loss t)) (hlegal : LegalFeedback '+oldrun+' T)',
  'LegalFeedback '+newrun+' T'),
 ('loss_value_scaling',shared+' (t : ℕ)',
  'scaledLoss c (loss t) (output '+newrun+' t) = loss t (output '+oldrun+' t)'),
 ('regret_scaling',shared+' (u : E) (T : ℕ)',
  'regret '+newrun+' (c⁻¹ • u) T = regret '+oldrun+' u T'),
 ('wrong_step_output',shared+' (t : ℕ)',
  'c • output V η (fun s => scaledLoss c (loss s)) (c⁻¹ • x₁) (scaledPolicy c p) t = output V (fun s => c ^ 2 * η s) loss x₁ p t'),
 ('distance_square_scaling','(c : ℝ) (hc : 0 < c) (x u : E)',
  '‖c⁻¹ • x - c⁻¹ • u‖ ^ 2 = ‖x - u‖ ^ 2 / c ^ 2'),
 ('energy_scaling',shared+' (T : ℕ)',
  '(∑ t ∈ range T, ‖selected '+newrun+' t‖ ^ 2) = c ^ 2 * (∑ t ∈ range T, ‖selected '+oldrun+' t‖ ^ 2)'),
 ('upper_bound_scaling','(c : ℝ) (hc : 0 < c) (A B η : ℝ) (hη : 0 < η)',
  'BanditRL.OnlineOptimalStep.upperBound (A / c ^ 2) (c ^ 2 * B) (η / c ^ 2) = BanditRL.OnlineOptimalStep.upperBound A B η'),
 ('regret_fixed_scaled','(c : ℝ) (hc : 0 < c) (η : ℝ) (hη : 0 < η) (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) (hlegal : LegalFeedback V (fun _ => η) loss x₁ p T) (u : E)',
  'regret V (scaledEta c (fun _ => η)) (fun s => scaledLoss c (loss s)) (c⁻¹ • x₁) (scaledPolicy c p) (c⁻¹ • u) T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) + η / 2 * (∑ t ∈ range T, ‖selected V (fun _ => η) loss x₁ p t‖ ^ 2) - ‖output V (fun _ => η) loss x₁ p T - u‖ ^ 2 / (2 * η)'),
]
assert len(specs)==22 and len(set(n for n,b,c in specs))==22
headers={n:'theorem '+n+' '+b+' :\n    '+conclusion for n,b,conclusion in specs}
with (run/'draft-headers-v1.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(headers,f,ensure_ascii=False,indent=2);f.write('\n')
(run/'leaves/context-v1.lean.txt').write_text(context+'end BanditRL.OnlineUnitScaling\n',encoding='utf-8')
(run/'leaves/target-v1.lean.txt').write_text(context+'\n\n'.join(h+' := by' for h in headers.values())+'\n\nend BanditRL.OnlineUnitScaling\n',encoding='utf-8')
(run/'leaves/types-v1.lean').write_text(context+'\n'.join('#check (∀ '+b+',\n    '+conclusion+')' for n,b,conclusion in specs)+'\nend BanditRL.OnlineUnitScaling\n',encoding='utf-8')
print('Draft22 unproved targets, four shared-context definitions; no theorem bodies written.')
