import BanditRLProof.LowerBounds.FixedLengthCoding
import BanditRLProof.LowerBounds.PrefixCodeExchange

namespace BanditRLProof.LowerBounds

theorem uniformPowerTwo_entropy {α : Type*} [Fintype α] (n : ℕ)
    (hcard : Fintype.card α = 2 ^ n) :
    discreteEntropyBaseTwo Finset.univ (fun _ : α => (1 / (2 : ℝ) ^ n)) = n := by
  have htwo : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simp [discreteEntropyBaseTwo, hcard, Real.log_pow, htwo]

theorem fixedLength_uniformPowerTwo_optimal {α : Type*} [Fintype α]
    (n : ℕ) (hcard : Fintype.card α = 2 ^ n) (code : BinaryPrefixCode α)
    (hlen : ∀ a, (code.encode a).length = n) :
    IsOptimalPrefixCode (fun _ : α => 1 / (2 : ℝ) ^ n) code := by
  classical
  have hs : ∑ _ : α, (1 / (2 : ℝ) ^ n) = 1 := by simp [hcard]
  intro other
  rw [expectedCodeLength_fixedLength _ hs code n hlen]
  have h := discreteEntropyBaseTwo_le_expectedCodeLength
    (fun _ : α => 1 / (2 : ℝ) ^ n) (fun _ => by positivity) hs other
  rwa [uniformPowerTwo_entropy n hcard] at h

def ternaryPrefixWord (a : Fin 3) : List Bool :=
  if a.val = 0 then [false] else if a.val = 1 then [true, false] else [true, true]

def ternaryPrefixCode : BinaryPrefixCode (Fin 3) where
  encode := ternaryPrefixWord
  injective := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [ternaryPrefixWord]
  nonempty := by intro a; fin_cases a <;> simp [ternaryPrefixWord]
  prefixFree := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [ternaryPrefixWord]

theorem ternaryPrefixCode_uniform_length :
    expectedCodeLength (fun _ : Fin 3 => (1 / 3 : ℝ)) ternaryPrefixCode = 5 / 3 := by
  norm_num [expectedCodeLength, Fin.sum_univ_succ, ternaryPrefixCode, ternaryPrefixWord]

/-- Uniform masses do not make a constant-length code optimal for every alphabet size. -/
theorem uniform_three_fixedLength_not_optimal (code : BinaryPrefixCode (Fin 3))
    (hlen : ∀ a, (code.encode a).length = 2) :
    ¬ IsOptimalPrefixCode (fun _ : Fin 3 => (1 / 3 : ℝ)) code := by
  intro hopt
  have he := expectedCodeLength_fixedLength (fun _ : Fin 3 => (1 / 3 : ℝ))
    (by norm_num) code 2 hlen
  have h := hopt ternaryPrefixCode
  rw [he, ternaryPrefixCode_uniform_length] at h
  norm_num at h

end BanditRLProof.LowerBounds
