import PowerLambert.EntropyDefs

noncomputable section
open Function Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Topology Classical

namespace PowerLambert

/-- The finite error alphabet carries its discrete sigma algebra. -/
instance optionMeasurableSpace (S : Type*) [Fintype S] : MeasurableSpace (Option S) := ⊤

instance optionMeasurableSingletonClass (S : Type*) [Fintype S] :
    MeasurableSingletonClass (Option S) := ⟨fun _ => trivial⟩

/-- A finite probability distribution concentrated near one point has small
ordinary Shannon entropy. This is the continuity step in the error encoding. -/
theorem measureEntropy_small_of_concentrated
    {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (s₀ : S) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ν : Measure S), IsProbabilityMeasure ν →
      ν.real ({s₀}ᶜ) < δ → measureEntropy ν < η := by
  let : Nonempty S := ⟨s₀⟩
  have hcard : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have he : 0 < η / Fintype.card S := div_pos hη hcard
  have hcont0 : ContinuousAt negMulLog (0 : ℝ) := continuous_negMulLog.continuousAt
  have hcont1 : ContinuousAt negMulLog (1 : ℝ) := continuous_negMulLog.continuousAt
  obtain ⟨δ₀, hδ₀, h₀⟩ := Metric.continuousAt_iff.mp hcont0 (η / Fintype.card S) he
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousAt_iff.mp hcont1 (η / Fintype.card S) he
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro ν hν herr
  let : IsProbabilityMeasure ν := hν
  have hsmall : ∀ s : S, negMulLog (ν.real {s}) < η / Fintype.card S := by
    intro s
    by_cases hs : s = s₀
    · subst s
      have hprob := probReal_add_probReal_compl (μ := ν) (measurableSet_singleton s₀)
      have heq : |ν.real {s₀} - 1| = ν.real ({s₀}ᶜ) := by
        rw [show ν.real {s₀} - 1 = -ν.real ({s₀}ᶜ) by linarith, abs_neg,
          abs_of_nonneg measureReal_nonneg]
      have hdist : dist (ν.real {s₀}) 1 < δ₁ := by
        rw [Real.dist_eq, heq]
        exact herr.trans_le (min_le_right _ _)
      have hh := h₁ hdist
      simpa only [negMulLog_one, Real.dist_eq, sub_zero, abs_lt] using (abs_lt.mp hh).2
    · have hsub : ({s} : Set S) ⊆ {s₀}ᶜ := by
        intro t ht
        have ht' : t = s := ht
        subst t
        exact hs
      have hp : ν.real {s} ≤ ν.real ({s₀}ᶜ) := measureReal_mono hsub
      have hdist : dist (ν.real {s}) 0 < δ₀ := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
        exact hp.trans_lt (herr.trans_le (min_le_left _ _))
      have hh := h₀ hdist
      have hpos := (abs_lt.mp (by simpa only [negMulLog_zero, Real.dist_eq, sub_zero] using hh)).2
      exact hpos
  rw [measureEntropy_of_isProbabilityMeasure, tsum_fintype]
  calc
    _ < ∑ _s : S, η / Fintype.card S :=
      Finset.sum_lt_sum (fun s hs => (hsmall s).le) ⟨s₀, Finset.mem_univ _, hsmall s₀⟩
    _ = η := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

def errorLabel {Ω S : Type*} [DecidableEq S] (X Y : Ω → S) : Ω → Option S :=
  fun ω => if X ω = Y ω then none else some (X ω)

lemma measurable_errorLabel {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [Fintype S] [MeasurableSingletonClass S] [DecidableEq S]
    {X Y : Ω → S} (hX : Measurable X) (hY : Measurable Y) : Measurable (errorLabel X Y) := by
  unfold errorLabel
  exact Measurable.ite (measurableSet_eq_fun hX hY) measurable_const
    ((measurable_of_finite (f := (some : S → Option S))).comp hX)

lemma errorLabel_getD {Ω S : Type*} [DecidableEq S] (X Y : Ω → S) (ω : Ω) :
    (errorLabel X Y ω).getD (Y ω) = X ω := by
  simp [errorLabel]
  split_ifs <;> simp_all

lemma errorLabel_nondefault {Ω S : Type*} [DecidableEq S] (X Y : Ω → S) :
    errorLabel X Y ⁻¹' ({none}ᶜ : Set (Option S)) = {ω | X ω ≠ Y ω} := by
  ext ω
  simp [errorLabel]

theorem entropy_errorLabel_small {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [DecidableEq S] {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω),
      IsProbabilityMeasure μ → ∀ (X Y : Ω → S), Measurable X → Measurable Y →
        μ.real {ω | X ω ≠ Y ω} < δ → entropy (errorLabel X Y) μ < η := by
  obtain ⟨δ, hδ, hsmall⟩ := measureEntropy_small_of_concentrated (none : Option S) hη
  refine ⟨δ, hδ, ?_⟩
  intro Ω mΩ μ hμ X Y hX hY herr
  let : IsProbabilityMeasure μ := hμ
  have hZ := measurable_errorLabel hX hY
  have hprob : IsProbabilityMeasure (μ.map (errorLabel X Y)) := ⟨by
    rw [Measure.map_apply hZ MeasurableSet.univ]
    simp⟩
  apply hsmall _ hprob
  simpa only [map_measureReal_apply hZ (measurableSet_singleton none).compl,
    errorLabel_nondefault] using herr

end PowerLambert
