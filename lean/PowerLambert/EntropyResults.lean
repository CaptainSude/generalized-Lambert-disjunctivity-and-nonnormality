import PowerLambert.EntropyZero
import PowerLambert.EntropyFactor
import PowerLambert.DynamicsLabelApprox

noncomputable section
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology

namespace PowerLambert

theorem orbitGroup_zeroMeasureEntropy (r : ℕ) :
    ZeroMeasureEntropy (modelRotation r) (orbitHaar r) := by
  apply zeroMeasureEntropy_of_periodic_label_approximation
    (orbitRotation_ergodic r).toMeasurePreserving
  intro k hk X hX ε hε
  obtain ⟨Y,hY,P,hP,hperiod,hclose⟩ :=
    exists_periodic_label_approximation_iterate r k hk X hX ε hε
  exact ⟨P,Y,hP,hY,hperiod,hclose⟩

theorem limitingLaw_zeroMeasureEntropy {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    ZeroMeasureEntropy (fun x : UnitAddCircle => b • x)
      (limitingLaw b r : Measure UnitAddCircle) := by
  exact (orbitGroup_zeroMeasureEntropy r).factor (orbitRotation_ergodic r).toMeasurePreserving
    (by fun_prop) (measurable_modelCircle b r) (modelCircle_factor_ae hb hr)

theorem limitingLaw_entropy_zero {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    kolmogorovSinaiEntropy (fun x : UnitAddCircle => b • x)
      (limitingLaw b r : Measure UnitAddCircle) = 0 :=
  (limitingLaw_zeroMeasureEntropy hb hr).kolmogorovSinaiEntropy_eq_zero

end PowerLambert
