import PowerLambert.DigitResults
import PowerLambert.EntropyResults

noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace PowerLambert

/-- The complete theorem for the power-exponent Lambert family.
The only hypotheses are the two integer parameter bounds. -/
theorem powerLambert_full_theorem (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
    PositiveWordFrequencies b (lambert b r) ∧
    DisjunctiveInBase b (lambert b r) ∧
    Irrational (lambert b r) ∧
    ¬ NormalInBase b (lambert b r) ∧
    Tendsto (empiricalCircle (circleRadixOrbit b (lambert b r)))
      atTop (𝓝 (limitingLaw b r)) ∧
    Ergodic (fun x : UnitAddCircle => b • x) (limitingLaw b r : Measure UnitAddCircle) ∧
    MeasurePreserving (fun x : UnitAddCircle => b • x)
      (limitingLaw b r : Measure UnitAddCircle) (limitingLaw b r : Measure UnitAddCircle) ∧
    (limitingLaw b r : Measure UnitAddCircle).IsOpenPosMeasure ∧
    NullSingletonClass (limitingLaw b r : Measure UnitAddCircle) ∧
    ZeroMeasureEntropy (fun x : UnitAddCircle => b • x) (limitingLaw b r : Measure UnitAddCircle) ∧
    kolmogorovSinaiEntropy (fun x : UnitAddCircle => b • x)
      (limitingLaw b r : Measure UnitAddCircle) = 0 :=
  ⟨lambert_positiveWordFrequencies hb hr,lambert_disjunctive hb hr,
    lambert_irrational hb hr,lambert_not_normal hb hr,lambert_empirical_tendsto hb hr,
    limitingLaw_ergodic hb hr,(limitingLaw_ergodic hb hr).toMeasurePreserving,
    limitingLaw_fullSupport hb hr,limitingLaw_atomless hb hr,
    limitingLaw_zeroMeasureEntropy hb hr,limitingLaw_entropy_zero hb hr⟩

end PowerLambert
