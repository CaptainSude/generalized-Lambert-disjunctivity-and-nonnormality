import PowerLambert.SeriesMeansTail

open scoped BigOperators Topology
open Filter Finset

namespace PowerLambert

lemma summable_const_div_pow {b : ℕ} (hb : 2 ≤ b) (C : ℝ) (H : ℕ) :
    Summable (fun j : ℕ => C / (b : ℝ) ^ (H + j + 1)) := by
  have hb' : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hsmall : ‖(b : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith))]
    exact inv_lt_one_of_one_lt₀ hb'
  apply ((summable_geometric_of_norm_lt_one hsmall).mul_left
    (C * (b : ℝ)⁻¹ ^ (H + 1))).congr
  intro j
  simp only [div_eq_mul_inv, ← inv_pow]
  rw [show H + j + 1 = H + 1 + j by omega, pow_add]
  ring

lemma tsum_const_div_pow {b : ℕ} (hb : 2 ≤ b) (C : ℝ) (H : ℕ) :
    (∑' j : ℕ, C / (b : ℝ) ^ (H + j + 1)) = C / (b - 1 : ℝ) / (b : ℝ) ^ H := by
  have hb' : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hb0 : (b : ℝ) ≠ 0 := by linarith
  have hbinv : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb'
  calc
    _ = ∑' j : ℕ, (C * (b : ℝ)⁻¹ ^ (H + 1)) * ((b : ℝ)⁻¹ ^ j) := by
      apply tsum_congr
      intro j
      simp only [div_eq_mul_inv, ← inv_pow]
      rw [show H + j + 1 = H + 1 + j by omega, pow_add]
      ring
    _ = (C * (b : ℝ)⁻¹ ^ (H + 1)) * (1 - (b : ℝ)⁻¹)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hbinv]
    _ = _ := by
      have hb1 : (b : ℝ) - 1 ≠ 0 := by linarith
      rw [inv_pow, pow_succ]
      field_simp
      <;> ring

theorem weighted_near_far_tail_le {b H J : ℕ} (hb : 2 ≤ b) (hHJ : H ≤ J)
    (M : ℕ → ℝ) {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hM : ∀ j, 0 ≤ M j)
    (hnear : ∀ j, H < j → j ≤ J → M j ≤ C)
    (hfar : ∀ j, 0 < j → M j ≤ C * B) :
    (∑' j : ℕ, M (H + j + 1) / (b : ℝ) ^ (H + j + 1)) ≤
      C / (b - 1 : ℝ) * ((b : ℝ) ^ H)⁻¹ +
        C * B / (b - 1 : ℝ) * ((b : ℝ) ^ J)⁻¹ := by
  have hs : Summable (fun j : ℕ => M (H + j + 1) / (b : ℝ) ^ (H + j + 1)) :=
    Summable.of_nonneg_of_le (fun j => div_nonneg (hM _) (by positivity))
      (fun j => div_le_div_of_nonneg_right (hfar _ (by omega)) (by positivity))
      (summable_const_div_pow hb (C * B) H)
  rw [← hs.sum_add_tsum_nat_add (J - H)]
  apply add_le_add
  · calc
      _ ≤ ∑ j ∈ range (J - H), C / (b : ℝ) ^ (H + j + 1) := by
        apply sum_le_sum
        intro j hj
        apply div_le_div_of_nonneg_right (hnear _ (by omega) (by have := mem_range.mp hj; omega))
        positivity
      _ ≤ ∑' j : ℕ, C / (b : ℝ) ^ (H + j + 1) :=
        (summable_const_div_pow hb C H).sum_le_tsum _ (fun j hj => div_nonneg hC (by positivity))
      _ = _ := by rw [tsum_const_div_pow hb]; rfl
  · have ht := (summable_nat_add_iff (J - H)).mpr hs
    have hle : ∀ j : ℕ,
        M (H + (j + (J - H)) + 1) / (b : ℝ) ^ (H + (j + (J - H)) + 1) ≤
          C * B / (b : ℝ) ^ (J + j + 1) := by
      intro j
      rw [show H + (j + (J - H)) + 1 = J + j + 1 by omega]
      exact div_le_div_of_nonneg_right (hfar _ (by omega)) (by positivity)
    calc
      _ ≤ ∑' j : ℕ, C * B / (b : ℝ) ^ (J + j + 1) :=
        Summable.tsum_le_tsum hle ht (summable_const_div_pow hb (C * B) J)
      _ = _ := by rw [tsum_const_div_pow hb]; rfl

end PowerLambert
