from common import *
context = '''import BanditRLProof.OnlineSubgradientPolicy
import BanditRLProof.OnlineAdaptivePotential
import BanditRLProof.OnlineAdaptiveEnergy

noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace BanditRL.OnlineAdaptiveOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
abbrev Domain := BanditRL.OnlineGradientDescent.Domain E
abbrev SupportPolicy := BanditRL.OnlineSubgradientPolicy.SupportPolicy (E := E)

def state (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) : (t : ℕ) → (Fin (t + 1) → E) × ℝ := by
  classical
  exact Nat.rec (motive := fun t => (Fin (t + 1) → E) × ℝ) ((fun _ => x₁), 0)
    (fun t s =>
      let g := p t (fun i => loss i.val) s.1 (loss t)
      let S := s.2 + ‖g‖ ^ 2
      (Fin.snoc s.1 (if g = 0 then s.1 (Fin.last t) else
        BanditRL.OnlineGradientDescent.project V
          (s.1 (Fin.last t) - (α * D / Real.sqrt S) • g)), S))

def history (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) : Fin (t + 1) → E :=
  (state V α D loss x₁ p t).1

def energy (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) : ℝ :=
  (state V α D loss x₁ p t).2

def output (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) : E :=
  history V α D loss x₁ p t (Fin.last t)

def selected (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) : E :=
  p t (fun i => loss i.val) (history V α D loss x₁ p t) (loss t)

def eta (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) : ℝ :=
  α * D / Real.sqrt (energy V α D loss x₁ p t + ‖selected V α D loss x₁ p t‖ ^ 2)

def LegalFeedback (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (T : ℕ) : Prop :=
  ∀ t < T, selected V α D loss x₁ p t ∈
    SourceSubdifferential (loss t) (output V α D loss x₁ p t)

def regret (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (output V α D loss x₁ p t)).toReal - (loss t u).toReal)
'''
headers = {
'state_succ': '''theorem state_succ (V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) :
    state V α D loss x₁ p (t + 1) =
      (Fin.snoc (history V α D loss x₁ p t)
        (if selected V α D loss x₁ p t = 0 then output V α D loss x₁ p t else
          BanditRL.OnlineGradientDescent.project V
            (output V α D loss x₁ p t - eta V α D loss x₁ p t • selected V α D loss x₁ p t)),
       energy V α D loss x₁ p t + ‖selected V α D loss x₁ p t‖ ^ 2) := by
''',
'regret_bound': '''theorem regret_bound (V : Domain (E := E)) (α D : ℝ) (hα : 0 < α) (hD : 0 ≤ D)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V α D loss x₁ p T)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (u : E) (hu : u ∈ V.carrier) :
    regret V α D loss x₁ p u T ≤
      (1 / (2 * α) + α) * D * Real.sqrt (energy V α D loss x₁ p T) -
      ‖output V α D loss x₁ p T - u‖ ^ 2 * Real.sqrt (energy V α D loss x₁ p T) / (2 * α * D) := by
'''}
write(CONTRACT/'algorithm-definition-context-draft-v1.lean.txt', context)
probe = context+'\n'
for name, header in headers.items():
    write(CONTRACT/('algorithm-'+name+'-header-draft-v1.lean.txt'), header)
    statement = header[len('theorem '+name):].rstrip()[:-len(':= by')]
    probe += '#check (∀ '+statement.replace(' :\n', ',\n', 1).lstrip() + ')\n\n'
write(RUN/'AlgorithmDraftTypeProbeV1.lean', probe+'end BanditRL.OnlineAdaptiveOSD\n')
capture('algorithm-draft-type-probe-v1', 'lake', 'env', 'lean', RUN/'AlgorithmDraftTypeProbeV1.lean', required=False)
write(CONTRACT/'algorithm-assumption-delta-draft-v1.md', '''# Draft algorithm and terminal semantics, not stabilized

Eight actual definitions plus two shared aliases in the draft context. The sole Nat.rec stores finite output history together with cumulative selected squared norms. Initial energy0, initial output x1. A fixed shared SupportPolicy consumes finite past loss functions, the actual output history and the current whole function; action precedes that current feedback. The support and inclusive energy are chosen inside the recurrence; no horizon/comparator/future loss or exogenous schedule enters state. At a zero selected vector the action is unchanged, even after positive energy. At nonzero support use the shared Euclidean nearest projection and alpha D/sqrt(inclusive energy). eta is a public observer of the same recurrence, not a separate future-selected schedule.

The frozen-for-review parent proposal quantifies every T including0 and D>=0, alpha>0. D0 forces a singleton feasible set, so same-trajectory regret and terminal distance vanish. For D>0, zero total energy gives zero weights and nonpositive skipped support-derived losses. Real division is total but source eta at zero prefix is interpreted only through the explicitly prescribed skip, not as a positive step. hlegal requires actual selected global source supports only at played points. SubdifferentiableOn includes SourceProper and feasible support existence, making EReal losses finite before toReal subtraction. The source also states convexity; this sufficient-support formulation generalizes it as in the shared OSD API and needs explicit source review. No bounded gradient, uniform Lipschitz, future-energy oracle or stochastic/adaptive-law hypothesis is added.

Source: Orabona v10 printed39-40/PDF51-52, Eq4.4 and Theorem4.14, as required forward Chapter2 dependencies; this is not a new competing Chapter4 task or Chapter4 completion. alpha1 gives the3/2 coefficient; alpha=sqrt2/2 gives sqrt2 on the same specified run, with the stronger retained negative terminal. D sqrt(2S)=sqrt2 D sqrtS for nonnegative S. Separate source benchmark issue: min over eta>0 of D²/(2eta)+eta S/2 is attained at D/sqrtS when D,S>0; at exactly one zero it has infimum0 without positive minimizer, and at bothzero every eta minimizes. A proposed repair MUST remain separate from pinned source and receive its own review, not silently replace a min statement. No benchmark theorem BODY or source repair accepted here.

No production algorithm file exists. The scratch probe only typechecks draft definitions and two complete propositions, not their proof bodies. First finite leaf proposal is exact state_succ, after context/terminal/causal review; subsequent energy/feasibility/prefix/zero-step/one-step/sum bounds each need dependency-ready frozen headers. Default one lower route; original old library, root, Tests root, website and global frontier remain untouched. Goal active, Chapter2 incomplete.
''')
print('Draft algorithm context and two exact propositions recorded; no production algorithm BODY.', flush=True)
