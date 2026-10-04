Neutral statement/context packet. Reconstruct all twelve declarations in seven slots, including full set equalities, actual causal recursion, same-horizon family and one-sided asymptotics. Do not read any source identity, source file, proof body, prior verdict or other run. Do not compile or infer source acceptance.

Actual scoped context (declaration identifiers neutralized only; mathematics unchanged):
```lean
import BanditRLProof.OnlineSubgradientDescent
import BanditRLProof.OnlineSubgradientAbsolute
import BanditRLProof.OnlineGuessingOGD

noncomputable section
open Set Finset Filter BanditRL.OnlineConvex
open BanditRL.OnlineSubgradientDescent
namespace BanditRL.OnlineGuessingSubgradient

def loss (y x : ℝ) : EReal := ((|x - y| : ℝ) : EReal)
theorem result_1 (y x : ℝ) :
    SourceSubdifferential (loss y) x =
      SourceSubdifferential (fun z : ℝ => ((|z| : ℝ) : EReal)) (x - y)


theorem result_2 (y x : ℝ) (hxy : y < x) :
    SourceSubdifferential (loss y) x = {(1 : ℝ)}


theorem result_3 (y : ℝ) :
    SourceSubdifferential (loss y) y = Icc (-1 : ℝ) 1


theorem result_4 (y x : ℝ) (hxy : x < y) :
    SourceSubdifferential (loss y) x = {(-1 : ℝ)}


theorem result_5 (y x : ℝ) :
    SourceSubdifferential (loss y) x =
      if y < x then {(1 : ℝ)} else if x = y then Icc (-1 : ℝ) 1 else {(-1 : ℝ)}


theorem result_6 (y : ℝ) :
    SubdifferentiableOn BanditRL.OnlineGradientDescent.unitInterval (loss y)


theorem result_7 (y x g : ℝ)
    (hg : g ∈ SourceSubdifferential (loss y) x) : ‖g‖ ≤ 1


theorem result_8 (y x : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1) : ‖currentSubgradient (loss y) x‖ ≤ 1


theorem result_9 (η y x : ℝ) :
    step BanditRL.OnlineGradientDescent.unitInterval η (loss y) x =
      min (max (x - η * currentSubgradient (loss y) x) 0) 1


theorem result_10 (η η' : ℕ → ℝ) (y y' : ℕ → ℝ) (x₁ : ℝ) (t : ℕ)
    (hη : ∀ s < t, η s = η' s) (hy : ∀ s < t, y s = y' s) :
    iterate BanditRL.OnlineGradientDescent.unitInterval η (fun s => loss (y s)) x₁ t =
      iterate BanditRL.OnlineGradientDescent.unitInterval η' (fun s => loss (y' s)) x₁ t


theorem result_11 (y : ℕ → ℝ) (x₁ : ℝ) (hx₁ : x₁ ∈ Icc (0 : ℝ) 1)
    (T : ℕ) (hT : 0 < T) (hy : ∀ t < T, y t ∈ Icc (0 : ℝ) 1) :
    ∀ u ∈ Icc (0 : ℝ) 1,
      (∑ t ∈ range T,
        (|iterate BanditRL.OnlineGradientDescent.unitInterval (fun _ => 1 / Real.sqrt T)
          (fun s => loss (y s)) x₁ t - y t| - |u - y t|)) ≤ Real.sqrt T


theorem result_12 (y : ℕ → ℝ) (x₁ : ℝ)
    (hx₁ : x₁ ∈ Icc (0 : ℝ) 1) (hy : ∀ t, y t ∈ Icc (0 : ℝ) 1)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop,
      (∑ t ∈ range T,
        (|iterate BanditRL.OnlineGradientDescent.unitInterval (fun _ => 1 / Real.sqrt T)
          (fun s => loss (y s)) x₁ t - y t| - |u - y t|)) / T < ε

end BanditRL.OnlineGuessingSubgradient
```

Imported semantic definitions, copied from actual pinned project; definitions are context, not theorem proofs:
```lean
namespace BanditRL.OnlineConvex
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def SourceProper (f : E → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∃ x, ∃ r : ℝ, f x = (r : EReal)

def SourceSubdifferential (f : E → EReal) (x : E) : Set E :=
  {g | ∀ y, f x + (inner ℝ g (y - x) : EReal) ≤ f y}


end BanditRL.OnlineConvex

namespace BanditRL.OnlineGradientDescent
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
structure Domain (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  carrier : Set E
  nonempty : carrier.Nonempty
  closed : IsClosed carrier
  convex : Convex ℝ carrier

def project (V : Domain E) (z : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex V.nonempty
    V.closed.isComplete V.convex z)

end BanditRL.OnlineGradientDescent

namespace BanditRL.OnlineSubgradientDescent
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
abbrev Domain := BanditRL.OnlineGradientDescent.Domain E
def SubdifferentiableOn (V : Domain (E := E)) (f : E → EReal) : Prop :=
  SourceProper f ∧ ∀ x ∈ V.carrier, (SourceSubdifferential f x).Nonempty
def currentSubgradient (f : E → EReal) (x : E) : E :=
  by
    classical
    exact if h : (SourceSubdifferential f x).Nonempty then Classical.choose h else 0
def step (V : Domain (E := E)) (η : ℝ) (f : E → EReal) (x : E) : E :=
  BanditRL.OnlineGradientDescent.project V (x - η • currentSubgradient f x)
def iterate (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) : ℕ → E
  | 0 => x₁
  | t + 1 => step V (η t) (loss t) (iterate V η loss x₁ t)
def regret (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (iterate V η loss x₁ t)).toReal - (loss t u).toReal)

end BanditRL.OnlineSubgradientDescent

namespace BanditRL.OnlineGradientDescent
def unitInterval : Domain ℝ where
  carrier := Icc 0 1
  nonempty := ⟨0, by norm_num⟩
  closed := isClosed_Icc
  convex := convex_Icc 0 1
end BanditRL.OnlineGradientDescent

```

Euclidean scalar norm is |x|, smul is real multiplication, Finset.range T is0,...,T-1; EReal real coercion is finite and toReal recovers real values. SourceSubdifferential global inequality tests every real point. Classical.choose on the Nonempty support predicate fixes one current-function/current-point support; fallback0 only for absent support. project is the chosen true nearest point of the nonempty closed convex carrier. Unit interval is precisely [0,1]. The output at index t starts from the common supplied x1 and uses only inputs at indices less than t. η_T=1/sqrtT can vary between prescribed horizons; no anytime interpretation. No interpretation as Tendsto signed regret0/absolute BigO.
