import BanditRLProof.LowerBounds.ArithmeticIntervals

namespace BanditRLProof.TextbookPartIVChapter14ArithmeticIntervalsCanary

open LowerBounds

example {k : ℕ} (p : Fin k → ℝ) (w : List (Fin k)) :
    (arithmeticInterval p w).2 - (arithmeticInterval p w).1 = (w.map p).prod :=
  arithmeticInterval_width p w

#print axioms LowerBounds.arithmeticInterval_width
#print axioms LowerBounds.arithmeticInterval_bounds
#print axioms LowerBounds.arithmeticOffset_separated

end BanditRLProof.TextbookPartIVChapter14ArithmeticIntervalsCanary
