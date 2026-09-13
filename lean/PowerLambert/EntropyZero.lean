import PowerLambert.EntropyBlocks

noncomputable section
open Function Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology Classical

namespace PowerLambert

/-- Approximation of every finite measurable partition by periodic labels
forces every normalized finite Shannon block entropy to tend to zero. -/
theorem zeroMeasureEntropy_of_periodic_label_approximation
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (happrox : ∀ (k : ℕ), 0 < k → ∀ (X : Ω → Fin k), Measurable X →
      ∀ ε : ℝ, 0 < ε → ∃ (P : ℕ) (Y : Ω → Fin k),
        0 < P ∧ Measurable Y ∧ (∀ ω, Y (T^[P] ω) = Y ω) ∧
          μ.real {ω | X ω ≠ Y ω} < ε) :
    ZeroMeasureEntropy T μ := by
  intro k X hX
  have hk : 0 < k := by
    have h := (X (Classical.choice μ.nonempty_of_neZero)).isLt
    omega
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hrare⟩ := entropy_errorLabel_small (S := Fin k) (show 0 < ε / 2 by positivity)
  obtain ⟨P, Y, hP, hY, hperiod, herr⟩ := happrox k hk X hX δ hδ
  have herror : entropy (errorLabel X Y) μ < ε / 2 := hrare μ inferInstance X Y hX hY herr
  have hconstant : Tendsto (fun n : ℕ => Real.log (Fintype.card (Fin P → Fin k)) / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop,
      Real.log (Fintype.card (Fin P → Fin k)) / (n : ℝ) < ε / 2 :=
    hconstant.eventually (gt_mem_nhds (by positivity : 0 < ε / 2))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (div_nonneg (entropy_nonneg _ _) (Nat.cast_nonneg n))]
  calc
    entropy (labelBlock T X n) μ / (n : ℝ) ≤
        (Real.log (Fintype.card (Fin P → Fin k)) + (n : ℝ) * entropy (errorLabel X Y) μ) / (n : ℝ) :=
      div_le_div_of_nonneg_right (entropy_labelBlock_periodic_error_bound hT hX hY hP hperiod n) hn'.le
    _ = Real.log (Fintype.card (Fin P → Fin k)) / (n : ℝ) + entropy (errorLabel X Y) μ := by
      field_simp
    _ < ε := by linarith

end PowerLambert
