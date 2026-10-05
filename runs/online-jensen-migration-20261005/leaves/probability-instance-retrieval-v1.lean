import Tests.OnlineJensenCanary

-- Retrieve the actual anonymous instance constants instead of guessing names.
#synth MeasureTheory.IsProbabilityMeasure Tests.OnlineJensenInfinite.law
#synth MeasureTheory.IsProbabilityMeasure Tests.OnlineJensenFinite.law
#print prefix Tests.OnlineJensenInfinite
#print prefix Tests.OnlineJensenFinite
