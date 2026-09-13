import PowerLambert.EntropyRare
import PowerLambert.EntropyBlockCore

noncomputable section
open Function Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology Classical

namespace PowerLambert

lemma entropy_labelBlock_le_labelBlock_error {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]
    [DecidableEq S] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : Measurable T) {X Y : Ω → S} (hX : Measurable X) (hY : Measurable Y) (n : ℕ) :
    entropy (labelBlock T X n) μ ≤
      entropy (labelBlock T Y n) μ + entropy (labelBlock T (errorLabel X Y) n) μ := by
  let U : Ω → (Fin n → S) × (Fin n → Option S) :=
    fun ω => (labelBlock T Y n ω, labelBlock T (errorLabel X Y) n ω)
  let R : (Fin n → S) × (Fin n → Option S) → (Fin n → S) :=
    fun p i => (p.2 i).getD (p.1 i)
  have hblockY := measurable_labelBlock hT hY n
  have hblockZ := measurable_labelBlock hT (measurable_errorLabel hX hY) n
  have hU : Measurable U := hblockY.prodMk hblockZ
  have hrecover : labelBlock T X n = R ∘ U := by
    funext ω i
    exact (errorLabel_getD X Y (T^[i.val] ω)).symm
  rw [hrecover]
  exact (entropy_comp_le μ hU R).trans (entropy_pair_le_add hblockY hblockZ μ)

theorem entropy_labelBlock_periodic_error_bound {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]
    [DecidableEq S] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {X Y : Ω → S} (hX : Measurable X) (hY : Measurable Y)
    {P : ℕ} (hP : 0 < P) (hperiod : ∀ ω, Y (T^[P] ω) = Y ω) (n : ℕ) :
    entropy (labelBlock T X n) μ ≤
      Real.log (Fintype.card (Fin P → S)) + (n : ℝ) * entropy (errorLabel X Y) μ := by
  exact (entropy_labelBlock_le_labelBlock_error hT.measurable hX hY n).trans
    (add_le_add (entropy_labelBlock_periodic_le hT.measurable hY hP hperiod n)
      (entropy_labelBlock_le_mul hT (measurable_errorLabel hX hY) n))

end PowerLambert

