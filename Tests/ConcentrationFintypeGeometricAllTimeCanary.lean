import BanditRLProof

namespace BanditRLProof.ConcentrationFintypeGeometricAllTimeExternalCanary

open MeasureTheory
open scoped ENNReal

#check Concentration.measure_iUnion_iUnion_fintype_le_tsum_of_uniform
#check Concentration.measure_iUnion_iUnion_fintype_le_delta_of_geometricConfidenceShare

noncomputable example
    {Omega Idx : Type} [MeasurableSpace Omega] [Fintype Idx] [Nonempty Idx]
    (mu : Measure Omega) (bad : Nat -> Idx -> Set Omega)
    (delta : Real) (hdelta : 0 <= delta)
    (hbad : forall n i,
      mu (bad n i) <= ENNReal.ofReal
        (Concentration.geometricConfidenceShare delta n /
          (Fintype.card Idx : Real))) :
    mu (⋃ n, ⋃ i, bad n i) <= ENNReal.ofReal delta := by
  exact
    Concentration.measure_iUnion_iUnion_fintype_le_delta_of_geometricConfidenceShare
      mu bad delta hdelta hbad

#print axioms Concentration.measure_iUnion_iUnion_fintype_le_tsum_of_uniform
#print axioms Concentration.measure_iUnion_iUnion_fintype_le_delta_of_geometricConfidenceShare

end BanditRLProof.ConcentrationFintypeGeometricAllTimeExternalCanary
