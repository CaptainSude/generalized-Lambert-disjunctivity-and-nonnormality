import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-!
Elementary mean-approximation tools. These lemmas make no assertion about
the Lambert constant until their approximation hypotheses are supplied.
-/

noncomputable section
open Filter Set
open scoped BigOperators Topology Classical

namespace PowerLambert

def sequenceMean (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, u n) / (N : ℝ)

theorem sequenceMean_nonneg {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) (N : ℕ) :
    0 ≤ sequenceMean u N := by
  exact div_nonneg (Finset.sum_nonneg fun n _ => hu n) (Nat.cast_nonneg N)

theorem sequenceMean_mono {u v : ℕ → ℝ} (huv : ∀ n, u n ≤ v n) (N : ℕ) :
    sequenceMean u N ≤ sequenceMean v N := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun n _ => huv n)
    (Nat.cast_nonneg N)

theorem sequenceMean_add (u v : ℕ → ℝ) (N : ℕ) :
    sequenceMean (fun n => u n + v n) N = sequenceMean u N + sequenceMean v N := by
  simp [sequenceMean, Finset.sum_add_distrib, add_div]

theorem abs_sequenceMean_sub_le (u v : ℕ → ℝ) (N : ℕ) :
    |sequenceMean u N - sequenceMean v N| ≤ sequenceMean (fun n => |u n - v n|) N := by
  simp only [sequenceMean, ← sub_div, ← Finset.sum_sub_distrib,
    abs_div, abs_of_nonneg (show (0 : ℝ) ≤ N from Nat.cast_nonneg N)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _)
    (show (0 : ℝ) ≤ N from Nat.cast_nonneg N)

/-- An asymptotic approximation by convergent sequences is convergent. The
approximating sequence may depend on the desired accuracy. -/
theorem exists_tendsto_of_asymptotic_approximation
    {X : Type*} [MetricSpace X] [CompleteSpace X] (u : ℕ → X)
    (h : ∀ ε : ℝ, 0 < ε → ∃ v : ℕ → X, ∃ a : X,
      Tendsto v atTop (𝓝 a) ∧ ∀ᶠ n in atTop, dist (u n) (v n) < ε) :
    ∃ a : X, Tendsto u atTop (𝓝 a) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨v, a, hv, huv⟩ := h (ε / 3) (by positivity)
  obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.mp hv.cauchySeq (ε / 3) (by positivity)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 huv
  refine ⟨max N₁ N₂, fun m hm n hn => ?_⟩
  have hm₁ : N₁ ≤ m := (le_max_left _ _).trans hm
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hm₂ : N₂ ≤ m := (le_max_right _ _).trans hm
  have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
  calc
    dist (u m) (u n) ≤ dist (u m) (v m) + dist (v m) (v n) + dist (v n) (u n) :=
      dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
      rw [dist_comm (v n) (u n)]
      exact add_lt_add (add_lt_add (hN₂ m hm₂) (hN₁ m hm₁ n hn₁)) (hN₂ n hn₂)
    _ = ε := by ring

/-- Mean approximation transfers convergence of scalar orbit averages. -/
theorem exists_sequenceMean_limit_of_approximation (u : ℕ → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ v : ℕ → ℝ, ∃ a : ℝ,
      Tendsto (sequenceMean v) atTop (𝓝 a) ∧
      ∀ᶠ N in atTop, sequenceMean (fun n => |u n - v n|) N < ε) :
    ∃ a : ℝ, Tendsto (sequenceMean u) atTop (𝓝 a) := by
  apply exists_tendsto_of_asymptotic_approximation
  intro ε hε
  obtain ⟨v, a, hva, huv⟩ := h ε hε
  refine ⟨sequenceMean v, a, hva, ?_⟩
  filter_upwards [huv] with N hN
  exact (abs_sequenceMean_sub_le u v N).trans_lt hN

/-- A period-P approximation bounds the lag-P self-distance by the two
approximation errors. -/
theorem periodic_lag_distance_le
    {X : Type*} [PseudoMetricSpace X] (u v : ℕ → X) (P n : ℕ)
    (hv : ∀ n, v (n + P) = v n) :
    dist (u n) (u (n + P)) ≤ dist (u n) (v n) + dist (u (n + P)) (v (n + P)) := by
  rw [hv n, dist_comm (u (n + P)) (v n)]
  exact dist_triangle _ _ _

theorem sum_periodic_lag_distance_le
    {X : Type*} [PseudoMetricSpace X] (u v : ℕ → X) (P N : ℕ)
    (hv : ∀ n, v (n + P) = v n) :
    (∑ n ∈ Finset.range N, dist (u n) (u (n + P))) ≤
      2 * ∑ n ∈ Finset.range (N + P), dist (u n) (v n) := by
  let e : ℕ → ℝ := fun n => dist (u n) (v n)
  have hfirst : (∑ n ∈ Finset.range N, e n) ≤ ∑ n ∈ Finset.range (N + P), e n := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_add_right N P))
      (fun n _ _ => dist_nonneg)
  have hshift : (∑ n ∈ Finset.range N, e (n + P)) ≤
      ∑ n ∈ Finset.range (N + P), e n := by
    have heq := Finset.sum_range_add e P N
    have hnonneg : 0 ≤ ∑ n ∈ Finset.range P, e n :=
      Finset.sum_nonneg fun n _ => dist_nonneg
    simp only [Nat.add_comm P N, Nat.add_comm P] at heq
    linarith
  calc
    (∑ n ∈ Finset.range N, dist (u n) (u (n + P))) ≤
        ∑ n ∈ Finset.range N, (e n + e (n + P)) := by
      exact Finset.sum_le_sum fun n _ => periodic_lag_distance_le u v P n hv
    _ = (∑ n ∈ Finset.range N, e n) + ∑ n ∈ Finset.range N, e (n + P) :=
      Finset.sum_add_distrib
    _ ≤ 2 * ∑ n ∈ Finset.range (N + P), e n := by linarith

/-- Uniformly small mean error yields a small lag correlation, with only
the explicit finite-endpoint correction `(N + P) / N`. -/
theorem sequenceMean_periodic_lag_distance_le
    {X : Type*} [PseudoMetricSpace X] (u v : ℕ → X) (P N : ℕ)
    (hv : ∀ n, v (n + P) = v n) {ε : ℝ}
    (herr : sequenceMean (fun n => dist (u n) (v n)) (N + P) ≤ ε)
    (hN : 0 < N) :
    sequenceMean (fun n => dist (u n) (u (n + P))) N ≤
      2 * ε * (((N + P : ℕ) : ℝ) / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hNP : (0 : ℝ) < (N + P : ℕ) := by exact_mod_cast (by omega : 0 < N + P)
  have he := (div_le_iff₀ hNP).mp herr
  have hs := sum_periodic_lag_distance_le u v P N hv
  apply (div_le_iff₀ hN').2
  calc
    (∑ n ∈ Finset.range N, dist (u n) (u (n + P))) ≤
        2 * ∑ n ∈ Finset.range (N + P), dist (u n) (v n) := hs
    _ ≤ 2 * (ε * ((N + P : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ = 2 * ε * (((N + P : ℕ) : ℝ) / N) * N := by field_simp

/-- A limiting lag self-distance is at most twice the uniform error of
any periodic approximation having that lag as its period. -/
theorem lag_limit_le_twice_periodic_error
    {X : Type*} [PseudoMetricSpace X] (u v : ℕ → X) (P : ℕ)
    (hv : ∀ n, v (n + P) = v n) {ε c : ℝ}
    (herr : ∀ N, 0 < N → sequenceMean (fun n => dist (u n) (v n)) N ≤ ε)
    (hc : Tendsto (sequenceMean (fun n => dist (u n) (u (n + P)))) atTop (𝓝 c)) :
    c ≤ 2 * ε := by
  have hratio : Tendsto (fun N : ℕ => (((N + P : ℕ) : ℝ) / N)) atTop (𝓝 1) := by
    have hzero : Tendsto (fun N : ℕ => (P : ℝ) / N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hone : Tendsto (fun N : ℕ => 1 + (P : ℝ) / N) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hzero
    apply hone.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp [Nat.cast_add, add_div, hn]
  have hb : Tendsto (fun N : ℕ => 2 * ε * (((N + P : ℕ) : ℝ) / N))
      atTop (𝓝 (2 * ε)) := by simpa using hratio.const_mul (2 * ε)
  apply le_of_tendsto_of_tendsto hc hb
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact sequenceMean_periodic_lag_distance_le u v P N hv
    (herr (N + P) (by omega)) hN

/-- Arbitrarily accurate periodic mean approximations are incompatible
with a fixed positive limiting self-distance at every positive lag. -/
theorem not_positive_lag_limits_of_periodic_approximation
    {X : Type*} [PseudoMetricSpace X] (u : ℕ → X)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, 0 < P ∧ ∃ v : ℕ → X,
      (∀ n, v (n + P) = v n) ∧
      ∀ N, 0 < N → sequenceMean (fun n => dist (u n) (v n)) N ≤ ε)
    {c : ℝ} (hc : 0 < c) :
    ¬ (∀ P : ℕ, 0 < P →
      Tendsto (sequenceMean (fun n => dist (u n) (u (n + P)))) atTop (𝓝 c)) := by
  intro hlag
  obtain ⟨P, hP, v, hv, he⟩ := happrox (c / 4) (by positivity)
  have hb := lag_limit_le_twice_periodic_error u v P hv he (hlag P hP)
  linarith

end PowerLambert
