Fresh restricted reconstruction GPT6Astra/medium. Read ONLY this packet this pass; no source identity/target names/proof bodies/verdicts/other files. Four unproved neutral headers with actual common imports/normed-finiteDim context and projectpredicate name lookup. Reconstruct seven slots per target; named imported predicates cannot be body-inspected this pass, so explicitly separate their interpretation from inspected definitions. Distinguish genuine eventually-neighbourhood finiteness versus finite at one point, global no-bottom supplied versus absent, ambient domain-interior versus final mere nonemptydomain, touching support versus pure global lower bound and outputfunctional possiblyzero. No measurable/probability/Borel/closedness/lsc/loss differentiability/infiniteDim hypothesis/conclusion inferred. Write ONLY blind-reconstruction-v1.md/blind-receipt-v1.json here with solepacket/reportSHA; historynoterased/no compilation/source/human/external/runtime attestation.

```lean
import BanditRLProof.OnlineConvexBarycenter
import BanditRLProof.OnlineConvexExtended
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Intrinsic

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Neutral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open BanditRL.OnlineConvex

theorem N01 (f : E → EReal) (hf : IsConvexExtended f) (x : E) (hneigh : ∀ᶠ y in 𝓝 x, ∃ r : ℝ, f y = (r : EReal)) : ∃ (a : E →L[ℝ] ℝ) (b : ℝ), ((a x + b : ℝ) : EReal) = f x ∧ ∀ y, ((a y + b : ℝ) : EReal) ≤ f y

theorem N02 (f : E → EReal) (hbot : ∀ y, f y ≠ ⊥) (hf : IsConvexExtended f) (x : E) (hx : x ∈ interior (effectiveDomain f)) : ∃ (a : E →L[ℝ] ℝ) (b : ℝ), ((a x + b : ℝ) : EReal) = f x ∧ ∀ y, ((a y + b : ℝ) : EReal) ≤ f y

theorem N03 (f : E → EReal) (hbot : ∀ y, f y ≠ ⊥) (hf : IsConvexExtended f) (x : E) (hx : x ∈ interior (effectiveDomain f)) : ∃ (a : E →L[ℝ] ℝ) (b : ℝ), ∀ y, ((a y + b : ℝ) : EReal) ≤ f y

theorem N04 (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥) (hf : IsConvexExtended f) (hne : (effectiveDomain f).Nonempty) : ∃ (a : E →L[ℝ] ℝ) (b : ℝ), ∀ x, ((a x + b : ℝ) : EReal) ≤ f x

end Neutral
```
