import PowerLambert.SeriesMeans

open scoped BigOperators Topology
open Filter Finset

namespace PowerLambert

lemma summable_linear_div_pow {b : ℕ} (hb : 2 ≤ b) (C H : ℕ) :
    Summable (fun j : ℕ => ((C + j : ℕ) : ℝ) / (b : ℝ) ^ (H + j + 1)) := by
  have hb' : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hsmall : ‖(b : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith))]
    exact inv_lt_one_of_one_lt₀ hb'
  have hs0 := (summable_geometric_of_norm_lt_one hsmall).mul_left (C : ℝ)
  have hs1 := summable_pow_mul_geometric_of_norm_lt_one 1 hsmall
  apply ((hs0.add hs1).mul_right ((b : ℝ)⁻¹ ^ (H + 1))).congr
  intro j
  simp only [Nat.cast_add, pow_one, div_eq_mul_inv, ← inv_pow]
  rw [show H + j + 1 = j + (H + 1) by omega, pow_add]
  ring

lemma orbitSeries_tail_eq_tsum {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) (n H : ℕ) :
    orbitSeries b r (n + H) / (b : ℝ) ^ H =
      ∑' j : ℕ, (powerDivisorCoeff r (n + H + j + 1) : ℝ) / (b : ℝ) ^ (H + j + 1) := by
  rw [orbitSeries_eq_coefficient_expansion hb hr, ← tsum_div_const]
  apply tsum_congr
  intro j
  rw [div_div, ← pow_add]
  congr 2
  omega

lemma summable_coefficient_tail {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) (n H : ℕ) :
    Summable (fun j : ℕ => (powerDivisorCoeff r (n + H + j + 1) : ℝ) / (b : ℝ) ^ (H + j + 1)) := by
  have h := (hasSum_coefficient_expansion hb hr (n + H)).summable.div_const ((b : ℝ) ^ H)
  apply h.congr
  intro j
  rw [div_div, ← pow_add]
  congr 2
  omega

lemma progression_tail_mean_eq_tsum {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r)
    (Q a H N : ℕ) :
    (∑ n ∈ range N, orbitSeries b r (a + Q * n + H) / (b : ℝ) ^ H) / (N : ℝ) =
      ∑' j : ℕ, ((∑ n ∈ range N,
        (powerDivisorCoeff r (a + H + j + 1 + Q * n) : ℝ)) / (N : ℝ)) /
          (b : ℝ) ^ (H + j + 1) := by
  simp_rw [orbitSeries_tail_eq_tsum hb hr]
  have hs : ∀ n ∈ range N, Summable (fun j : ℕ =>
      (powerDivisorCoeff r (a + Q * n + H + j + 1) : ℝ) / (b : ℝ) ^ (H + j + 1)) :=
    fun n hn => summable_coefficient_tail hb hr _ _
  rw [← Summable.tsum_finsetSum hs, ← tsum_div_const]
  apply tsum_congr
  intro j
  rw [← sum_div]
  have hsumeq : (∑ n ∈ range N, (powerDivisorCoeff r (a + Q * n + H + j + 1) : ℝ)) =
      ∑ n ∈ range N, (powerDivisorCoeff r (a + H + j + 1 + Q * n) : ℝ) := by
    apply sum_congr rfl
    intro n hn
    congr 2
    omega
  rw [hsumeq]
  ring

theorem progression_tail_mean_tendsto {b r Q : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r)
    (hQ : 0 < Q) (a H : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, orbitSeries b r (a + Q * n + H) / (b : ℝ) ^ H) / (N : ℝ)) atTop
      (𝓝 (∑' j : ℕ, (∑' d : ℕ, progressionDivisorWeight r Q (a + H + j + 1) d) /
        (b : ℝ) ^ (H + j + 1))) := by
  simp_rw [progression_tail_mean_eq_tsum hb hr]
  apply tendsto_tsum_of_dominated_convergence
    (bound := fun j : ℕ => ((a + H + j + 1 + Q : ℕ) : ℝ) * reciprocalTail r 0 /
      (b : ℝ) ^ (H + j + 1))
  · apply ((summable_linear_div_pow hb (a + H + 1 + Q) H).mul_right (reciprocalTail r 0)).congr
    intro j
    rw [show a + H + 1 + Q + j = a + H + j + 1 + Q by omega]
    ring
  · intro j
    exact (progression_coefficient_mean_tendsto_all hr hQ (by omega)).div_const _
  · filter_upwards [] with N j
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right (progression_coefficient_mean_le hr hQ (by omega)) (by positivity)

end PowerLambert
