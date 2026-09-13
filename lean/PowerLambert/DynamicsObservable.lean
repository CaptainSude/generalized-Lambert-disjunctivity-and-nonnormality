import PowerLambert.DynamicsModel
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section
open Set Filter MeasureTheory Topology
open scoped Classical BigOperators ENNReal

namespace PowerLambert

theorem integrable_modelTerm (b r m : ℕ) : Integrable (modelTerm b r m) (orbitHaar r) :=
  (continuous_modelTerm b r m).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem summable_integral_norm_modelTerm {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    Summable (fun m : ℕ => ∫ x, ‖modelTerm b r m x‖ ∂orbitHaar r) := by
  have heq (m : ℕ) : (∫ x, ‖modelTerm b r m x‖ ∂orbitHaar r) =
      (((m + 1 : ℕ) : ℝ) ^ r)⁻¹ * (b - 1 : ℝ)⁻¹ := by
    simp only [Real.norm_eq_abs, abs_of_nonneg (modelTerm_nonneg hb _),
      integral_modelTerm hb, powerModulus, Nat.cast_pow]
  simp_rw [heq]
  exact (summable_power_reciprocals hr).mul_right _

theorem modelTerm_lintegral_norm_tsum_ne_top {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    (∑' m : ℕ, ∫⁻ x, ‖modelTerm b r m x‖ₑ ∂orbitHaar r) ≠ ∞ := by
  simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_modelTerm b r _)]
  exact (summable_integral_norm_modelTerm hb hr).tsum_ofReal_ne_top

/-- The observable series converges at almost every point of its actual
arithmetic Haar probability space. -/
theorem ae_summable_modelTerm {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    ∀ᵐ x ∂orbitHaar r, Summable (fun m : ℕ => modelTerm b r m x) := by
  have hnorm : ∀ᵐ x ∂orbitHaar r, Summable (fun m : ℕ => ‖modelTerm b r m x‖) := by
    apply summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl
      (fun m => (integrable_modelTerm b r m).aestronglyMeasurable)
    simpa only [eLpNorm_one_eq_lintegral_enorm] using modelTerm_lintegral_norm_tsum_ne_top hb hr
  filter_upwards [hnorm] with x hx
  exact hx.of_norm

def modelObservable (b r : ℕ) (x : OrbitGroup r) : ℝ := ∑' m : ℕ, modelTerm b r m x

theorem measurable_modelObservable (b r : ℕ) : Measurable (modelObservable b r) :=
  Measurable.tsum fun m => (continuous_modelTerm b r m).measurable

theorem integrable_modelObservable {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    Integrable (modelObservable b r) (orbitHaar r) := by
  refine ⟨(measurable_modelObservable b r).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  apply lt_of_le_of_lt (lintegral_mono (fun x => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun m => (integrable_modelTerm b r m).aestronglyMeasurable.enorm)]
  exact (modelTerm_lintegral_norm_tsum_ne_top hb hr).lt_top

theorem modelObservable_integerPoint (b r n : ℕ) :
    modelObservable b r (integerPoint r n) = orbitSeries b r n := by
  exact tsum_congr (fun m => modelTerm_integerPoint b r m n)

theorem integral_modelObservable {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    (∫ x, modelObservable b r x ∂orbitHaar r) =
      (∑' m : ℕ, (((m + 1 : ℕ) : ℝ) ^ r)⁻¹) * (b - 1 : ℝ)⁻¹ := by
  change (∫ x, (∑' m, modelTerm b r m x) ∂orbitHaar r) = _
  rw [← integral_tsum_of_summable_integral_norm (fun m => integrable_modelTerm b r m)
    (summable_integral_norm_modelTerm hb hr)]
  simp_rw [integral_modelTerm hb, powerModulus, Nat.cast_pow]
  exact tsum_mul_right

end PowerLambert
