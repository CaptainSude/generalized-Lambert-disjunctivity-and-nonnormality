import PowerLambert.DynamicsFinite
import PowerLambert.DynamicsFactor
import PowerLambert.DynamicsFrequencies
import PowerLambert.SeriesNonNormal
import PowerLambert.DynamicsTestIntegral

noncomputable section
open Set Filter MeasureTheory Topology
open scoped Classical BigOperators BoundedContinuousFunction

namespace PowerLambert

theorem boundedContinuous_affine_dist_bound
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (f : X →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : X, |f x - f y| ≤ ε + C * dist x y := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
  refine ⟨2 * ‖f‖ / δ, by positivity, fun x y => ?_⟩
  by_cases hxy : dist x y < δ
  · have h := hclose hxy
    rw [Real.dist_eq] at h
    exact h.le.trans (le_add_of_nonneg_right (by positivity))
  · have hbound : |f x - f y| ≤ 2 * ‖f‖ := by
      have hsum := add_le_add (f.norm_coe_le_norm x) (f.norm_coe_le_norm y)
      have hsum' : |f x| + |f y| ≤ 2 * ‖f‖ := by simpa [Real.norm_eq_abs, two_mul] using hsum
      exact (abs_sub _ _).trans hsum'
    have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hxy)
      (show 0 ≤ 2 * ‖f‖ / δ by positivity)
    have hcancel : 2 * ‖f‖ / δ * δ = 2 * ‖f‖ := by field_simp
    rw [hcancel] at hmul
    linarith

theorem sequenceMean_affine_dist_bound
    {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (u v : ℕ → X)
    {ε C : ℝ} (_hC : 0 ≤ C)
    (h : ∀ x y : X, |f x - f y| ≤ ε + C * dist x y)
    {N : ℕ} (hN : 0 < N) :
    |sequenceMean (fun n => f (u n)) N - sequenceMean (fun n => f (v n)) N| ≤
      ε + C * sequenceMean (fun n => dist (u n) (v n)) N := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    _ ≤ sequenceMean (fun n => |f (u n) - f (v n)|) N := abs_sequenceMean_sub_le _ _ N
    _ ≤ sequenceMean (fun n => ε + C * dist (u n) (v n)) N :=
      sequenceMean_mono (fun n => h (u n) (v n)) N
    _ = _ := by simp [sequenceMean, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul, add_div, hNr]; ring

theorem tendsto_of_uniform_asymptotic_approximation
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (a : ℕ → ℝ) (L : ℝ)
    (hv : ∀ U, Tendsto (v U) atTop (𝓝 (a U)))
    (ha : Tendsto a atTop (𝓝 L))
    (happrox : ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      ∀ N : ℕ, 0 < N → |u N - v U N| < ε) :
    Tendsto u atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨U, hU, haU⟩ := ((happrox (ε / 3) (by positivity)).and
    ((Metric.tendsto_atTop.mp ha (ε / 3) (by positivity)).elim
      (fun M hM => eventually_atTop.2 ⟨M, hM⟩))).exists
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (hv U) (ε / 3) (by positivity)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hNN : N₀ ≤ N := (le_max_left _ _).trans hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hN)
  have haU' : |a U - L| < ε / 3 := haU
  have hvN : |v U N - a U| < ε / 3 := hN₀ N hNN
  rw [Real.dist_eq]
  calc
    |u N - L| ≤ |u N - v U N| + |v U N - a U| + |a U - L| := by
      simpa only [Real.dist_eq] using dist_triangle4 (u N) (v U N) (a U) L
    _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add (hU N hNpos) hvN) haU'
    _ = ε := by ring

theorem circleRadixOrbit_lambert_eq_model_values {b r : ℕ}
    (hb : 2 ≤ b) (hr : 2 ≤ r) (n : ℕ) :
    circleRadixOrbit b (lambert b r) n = (orbitSeries b r n : UnitAddCircle) := by
  have h := congrArg (fun z : ℝ => (z : UnitAddCircle)) (fract_radix_eq_orbitSeries hb hr n)
  simpa only [AddCircle.coe_fract, circleRadixOrbit] using h

/-- Uniform continuity converts the explicit real mean tail estimate
into approximation of every bounded continuous circle test, uniformly
over all positive prefix lengths. -/
theorem test_mean_periodic_approximation {b r : ℕ}
    (hb : 2 ≤ b) (hr : 2 ≤ r) (f : UnitAddCircle →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ U in atTop, ∀ N : ℕ, 0 < N →
      |sequenceMean (fun n => f (circleRadixOrbit b (lambert b r) n)) N -
        sequenceMean (fun n => f (orbitTrunc b r U n : UnitAddCircle)) N| < ε := by
  obtain ⟨C, hC, hbound⟩ := boundedContinuous_affine_dist_bound f (half_pos hε)
  have ht : Tendsto (fun U => C * (reciprocalTail r U / (b - 1 : ℝ))) atTop (𝓝 0) := by
    simpa using ((reciprocalTail_tendsto_zero r).div_const (b - 1 : ℝ)).const_mul C
  filter_upwards [ht.eventually (gt_mem_nhds (half_pos hε))] with U hU
  intro N hN
  have hmean : sequenceMean (fun n => dist (circleRadixOrbit b (lambert b r) n)
      (orbitTrunc b r U n : UnitAddCircle)) N ≤ reciprocalTail r U / (b - 1 : ℝ) := by
    calc
      _ ≤ sequenceMean (fun n => |orbitSeries b r n - orbitTrunc b r U n|) N := by
        apply sequenceMean_mono
        intro n
        rw [circleRadixOrbit_lambert_eq_model_values hb hr]
        exact circle_dist_le_abs _ _
      _ ≤ _ := mean_abs_orbitSeries_sub_trunc_le hb hr hN
  calc
    _ ≤ ε / 2 + C * sequenceMean (fun n => dist (circleRadixOrbit b (lambert b r) n)
        (orbitTrunc b r U n : UnitAddCircle)) N :=
      sequenceMean_affine_dist_bound f _ _ hC hbound hN
    _ ≤ ε / 2 + C * (reciprocalTail r U / (b - 1 : ℝ)) := by gcongr
    _ < ε := by linarith

theorem lambert_test_mean_tendsto {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r)
    (f : UnitAddCircle →ᵇ ℝ) :
    Tendsto (sequenceMean (fun n => f (circleRadixOrbit b (lambert b r) n)))
      atTop (𝓝 (∫ z, f z ∂(limitingLaw b r : Measure UnitAddCircle))) := by
  apply tendsto_of_uniform_asymptotic_approximation _
    (fun U => sequenceMean (fun n => f (orbitTrunc b r U n : UnitAddCircle)))
    (fun U => ∫ x, f (modelTrunc b r U x : UnitAddCircle) ∂orbitHaar r)
  · intro U
    exact sequenceMean_test_orbitTrunc_tendsto b r U (fun z => f (z : UnitAddCircle))
  · exact integral_test_modelTrunc_tendsto hb hr f
  · intro ε hε
    exact test_mean_periodic_approximation hb hr f hε

/-- The specific Lambert constant, rather than an almost-everywhere
choice of starting point, generates the explicit ergodic circle law. -/
theorem lambert_empirical_tendsto {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    Tendsto (empiricalCircle (circleRadixOrbit b (lambert b r))) atTop (𝓝 (limitingLaw b r)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have ht := (lambert_test_mean_tendsto hb hr f).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, integral_empiricalCircle_real, sequenceMean, div_eq_mul_inv, mul_comm]
    using ht

end PowerLambert
