import PowerLambert.DynamicsFinite
import PowerLambert.DynamicsFactor
import PowerLambert.DynamicsFrequencies
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Probability.ProbabilityMassFunction.Integrals

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology Classical BoundedContinuousFunction

namespace PowerLambert

theorem integral_limitingLaw (b r : ℕ) (f : UnitAddCircle →ᵇ ℝ) :
    (∫ z, f z ∂(limitingLaw b r : Measure UnitAddCircle)) =
      ∫ x, f (modelCircle b r x) ∂orbitHaar r := by
  change (∫ z, f z ∂Measure.map (modelCircle b r) (orbitHaar r)) = _
  exact integral_map (measurable_modelCircle b r).aemeasurable f.continuous.aestronglyMeasurable

theorem integral_test_modelTrunc_tendsto {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r)
    (f : UnitAddCircle →ᵇ ℝ) :
    Tendsto (fun U : ℕ => ∫ x, f ((modelTrunc b r U x : ℝ) : UnitAddCircle) ∂orbitHaar r)
      atTop (𝓝 (∫ z, f z ∂(limitingLaw b r : Measure UnitAddCircle))) := by
  rw [integral_limitingLaw]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro U
    exact (f.continuous.comp ((AddCircle.continuous_mk' (1 : ℝ)).comp
      (continuous_modelTrunc b r U))).aestronglyMeasurable
  · exact integrable_const _
  · intro U
    exact Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm _)
  · filter_upwards [ae_summable_modelTerm hb hr] with x hx
    exact f.continuous.continuousAt.tendsto.comp
      ((AddCircle.continuous_mk' (1 : ℝ)).continuousAt.tendsto.comp hx.hasSum.tendsto_sum_nat)

theorem integral_empiricalCircle_real (u : ℕ → UnitAddCircle) (N : ℕ)
    (f : UnitAddCircle →ᵇ ℝ) :
    (∫ z, f z ∂(empiricalCircle u N : Measure UnitAddCircle)) =
      ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (N + 1), f (u i) := by
  change (∫ z, f z ∂Measure.map (fun i : Fin (N + 1) => u i)
    (PMF.uniformOfFintype (Fin (N + 1))).toMeasure) = _
  rw [integral_map (measurable_of_finite _).aemeasurable f.continuous.aestronglyMeasurable,
    PMF.integral_eq_sum]
  simp_rw [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => f (u i)) (N + 1)

end PowerLambert
