import PowerLambert.EntropyDefs
import PowerLambert.DynamicsFactorIterates

noncomputable section
open Filter Function Set MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal

namespace PowerLambert

/-- Block entropy is unchanged by pulling a finite partition back through
an almost-everywhere commuting measurable factor. -/
theorem labelBlock_entropy_factor {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {T : Ω → Ω} {S : Ξ → Ξ} {φ : Ω → Ξ}
    (hT : MeasurePreserving T μ μ) (hS : Measurable S) (hφ : Measurable φ)
    (hcomm : ∀ᵐ x ∂μ, φ (T x) = S (φ x))
    (k n : ℕ) (X : Ξ → Fin k) (hX : Measurable X) :
    entropy (labelBlock S X n) (Measure.map φ μ) =
      entropy (labelBlock T (X ∘ φ) n) μ := by
  have hae : (labelBlock S X n) ∘ φ =ᵐ[μ] labelBlock T (X ∘ φ) n := by
    filter_upwards [ae_all_semiconj_iterates hT hcomm] with x hx
    funext i
    exact congrArg X (hx i).symm
  calc
    _ = entropy ((labelBlock S X n) ∘ φ) μ := by
      simp only [entropy_def, Measure.map_map (measurable_labelBlock hS hX n) hφ]
    _ = _ := entropy_congr hae

theorem ZeroMeasureEntropy.factor {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {T : Ω → Ω} {S : Ξ → Ξ} {φ : Ω → Ξ}
    (hzero : ZeroMeasureEntropy T μ) (hT : MeasurePreserving T μ μ)
    (hS : Measurable S) (hφ : Measurable φ)
    (hcomm : ∀ᵐ x ∂μ, φ (T x) = S (φ x)) :
    ZeroMeasureEntropy S (Measure.map φ μ) := by
  intro k X hX
  have heq (n : ℕ) := labelBlock_entropy_factor hT hS hφ hcomm k n X hX
  simp_rw [heq]
  exact hzero k (X ∘ φ) (hX.comp hφ)

/-- Kolmogorov--Sinai entropy: the supremum over all finite measurable
partitions of the asymptotic normalized Shannon entropy of their joins.
The limsup convention is total; all rates in the zero-entropy theorem
are proved to converge to zero. -/
def kolmogorovSinaiEntropy {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → Ω) (μ : Measure Ω) : ℝ≥0∞ :=
  ⨆ (k : ℕ) (X : Ω → Fin k) (_ : Measurable X),
    Filter.limsup (fun n : ℕ => ENNReal.ofReal (entropy (labelBlock T X n) μ/(n : ℝ))) atTop

theorem ZeroMeasureEntropy.kolmogorovSinaiEntropy_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {T : Ω → Ω} {μ : Measure Ω}
    (hzero : ZeroMeasureEntropy T μ) : kolmogorovSinaiEntropy T μ = 0 := by
  apply le_antisymm ?_ (show (0 : ℝ≥0∞) ≤ kolmogorovSinaiEntropy T μ from bot_le)
  apply iSup_le
  intro k
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hzero k X hX)
  have heq : Filter.limsup (fun n : ℕ =>
      ENNReal.ofReal (entropy (labelBlock T X n) μ/(n : ℝ))) atTop = (0 : ℝ≥0∞) := by
    convert h.limsup_eq using 1
    · congr 1
    · simp
  exact heq.le

end PowerLambert
