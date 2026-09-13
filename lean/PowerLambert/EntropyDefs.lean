import PFR.ForMathlib.Entropy.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Tactic

noncomputable section
open Function Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology Classical

namespace PowerLambert

/-- The length-n name of a point under a finite measurable labeling. -/
def labelBlock {Ω S : Type*} (T : Ω → Ω) (X : Ω → S) (n : ℕ) : Ω → (Fin n → S) :=
  fun ω i => X (T^[i.val] ω)

/-- Zero measure-theoretic entropy, expressed by vanishing normalized Shannon
entropy of the joined iterates of every finite measurable partition. -/
def ZeroMeasureEntropy {Ω : Type*} [MeasurableSpace Ω] (T : Ω → Ω) (μ : Measure Ω) : Prop :=
  ∀ (k : ℕ) (X : Ω → Fin k), Measurable X →
    Tendsto (fun n : ℕ => ProbabilityTheory.entropy (labelBlock T X n) μ / (n : ℝ))
      atTop (𝓝 0)

lemma measurable_labelBlock {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {T : Ω → Ω} {X : Ω → S} (hT : Measurable T) (hX : Measurable X) (n : ℕ) :
    Measurable (labelBlock T X n) := by
  apply measurable_pi_lambda
  intro i
  exact hX.comp (hT.iterate i.val)

end PowerLambert
