import PowerLambert.SeriesBridge
import PowerLambert.ArithmeticProgression
import PowerLambert.ArithmeticMeansEuler
import PowerLambert.Progression
import Mathlib.Analysis.Normed.Group.Tannery

open scoped BigOperators Topology
open Filter Finset

namespace PowerLambert

def progressionDivisorCount (d Q a N : ℕ) : ℕ :=
  ((range N).filter fun n => d ∣ a + Q * n).card

noncomputable def progressionDivisorFrequency (d Q a N : ℕ) : ℝ :=
  (progressionDivisorCount d Q a N : ℝ) / N

lemma progressionDivisorCount_le {d Q a N : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (ha : 0 < a) : progressionDivisorCount d Q a N ≤ (a + Q * N) / d := by
  unfold progressionDivisorCount
  have hcard := card_le_card_of_injOn
    (s := (range N).filter fun n => d ∣ a + Q * n)
    (t := Icc 1 ((a + Q * N) / d)) (fun n => (a + Q * n) / d) ?_ ?_
  · simpa using hcard
  · intro n hn
    obtain ⟨hn, hdiv⟩ := mem_filter.mp hn
    have hpos : 0 < a + Q * n := by omega
    apply mem_Icc.mpr
    constructor
    · exact Nat.div_pos (Nat.le_of_dvd hpos hdiv) hd
    · exact Nat.div_le_div_right (Nat.add_le_add_left
        (Nat.mul_le_mul_left Q (le_of_lt (mem_range.mp hn))) a)
  · intro m hm n hn hmn
    dsimp at hmn
    have hmdiv := (mem_filter.mp hm).2
    have hndiv := (mem_filter.mp hn).2
    have heq : a + Q * m = a + Q * n := by
      rw [← Nat.div_mul_cancel hmdiv, ← Nat.div_mul_cancel hndiv, hmn]
    have hmul : Q * m = Q * n := by omega
    exact Nat.eq_of_mul_eq_mul_left hQ hmul

lemma progressionDivisorFrequency_nonneg (d Q a N : ℕ) :
    0 ≤ progressionDivisorFrequency d Q a N := by
  unfold progressionDivisorFrequency
  positivity

lemma progressionDivisorFrequency_le {d Q a N : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (ha : 0 < a) (hN : 0 < N) :
    progressionDivisorFrequency d Q a N ≤ (a + Q : ℕ) / (d : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : (progressionDivisorCount d Q a N : ℝ) ≤ ((a + Q * N : ℕ) : ℝ) / d :=
    (show (progressionDivisorCount d Q a N : ℝ) ≤ ((a + Q * N) / d : ℕ) by
      exact_mod_cast progressionDivisorCount_le hd hQ ha).trans Nat.cast_div_le
  have hcmul := (le_div_iff₀ hd').mp hc
  unfold progressionDivisorFrequency
  apply (div_le_div_iff₀ hN' hd').mpr
  push_cast at hcmul ⊢
  nlinarith [mul_nonneg (Nat.cast_nonneg a) (sub_nonneg.mpr hN1)]

lemma progressionDivisorFrequency_tendsto {r Q a d : ℕ} (hd : 0 < d) (hQ : 0 < Q) :
    Tendsto (progressionDivisorFrequency (d ^ r) Q a) atTop
      (𝓝 (progressionDivisorWeight r Q a d)) := by
  have hdr : 0 < d ^ r := pow_pos hd _
  unfold progressionDivisorWeight
  by_cases hg : Nat.gcd (d ^ r) Q ∣ a
  · rw [if_pos hg]
    obtain ⟨v, hv⟩ := exists_progression_divisibility_residue hdr hQ hg
    have hmod : 0 < d ^ r / Nat.gcd (d ^ r) Q :=
      Nat.div_pos (Nat.gcd_le_left Q hdr) (Nat.gcd_pos_of_pos_left Q hdr)
    have heq : progressionDivisorFrequency (d ^ r) Q a =
        fun N => (((range N).filter fun n => Nat.ModEq (d ^ r / Nat.gcd (d ^ r) Q) n v).card : ℝ) / N := by
      ext N
      simp only [progressionDivisorFrequency, progressionDivisorCount, hv]
    rw [heq]
    have hlim := residue_frequency (d ^ r / Nat.gcd (d ^ r) Q) v hmod
    have hcast : ((d ^ r / Nat.gcd (d ^ r) Q : ℕ) : ℝ) =
        (d : ℝ) ^ r / Nat.gcd (d ^ r) Q := by
      rw [Nat.cast_div (Nat.gcd_dvd_left _ _) (by
        exact_mod_cast (Nat.gcd_pos_of_pos_left Q hdr).ne'), Nat.cast_pow]
    have hreal : (0 : ℝ) < d := by exact_mod_cast hd
    convert hlim using 1
    rw [hcast]
    field_simp
  · rw [if_neg hg]
    have heq : progressionDivisorFrequency (d ^ r) Q a = fun _ => 0 := by
      ext N
      simp [progressionDivisorFrequency, progressionDivisorCount,
        not_dvd_progression_of_not_gcd_dvd hg]
    rw [heq]
    exact tendsto_const_nhds

lemma progression_coefficient_mean_eq_tsum {r Q a N : ℕ} (hr : 2 ≤ r) (ha : 0 < a) :
    ((∑ n ∈ range N, (powerDivisorCoeff r (a + Q * n) : ℝ)) / (N : ℝ)) =
      ∑' m : ℕ, progressionDivisorFrequency ((m + 1) ^ r) Q a N := by
  have hs : ∀ n ∈ range N, Summable
      (fun m : ℕ => if (m + 1) ^ r ∣ a + Q * n then (1 : ℝ) else 0) :=
    fun n hn => carryCoeff_summable (by omega) (by omega)
  calc
    _ = (∑ n ∈ range N, ∑' m : ℕ,
        if (m + 1) ^ r ∣ a + Q * n then (1 : ℝ) else 0) / (N : ℝ) := by
      congr 1
      apply sum_congr rfl
      intro n hn
      rw [carryCoeff_tsum (by omega) (by omega), carryCoeff_eq_powerDivisorCoeff (by omega) (by omega)]
    _ = (∑' m : ℕ, ∑ n ∈ range N,
        if (m + 1) ^ r ∣ a + Q * n then (1 : ℝ) else 0) / (N : ℝ) := by
      rw [Summable.tsum_finsetSum hs]
    _ = _ := by
      rw [← tsum_div_const]
      apply tsum_congr
      intro m
      simp [progressionDivisorFrequency, progressionDivisorCount, sum_boole]

theorem progression_coefficient_mean_tendsto {r Q a : ℕ} (hr : 2 ≤ r)
    (hQ : 0 < Q) (ha : 0 < a) :
    Tendsto (fun N : ℕ =>
      ((∑ n ∈ range N, (powerDivisorCoeff r (a + Q * n) : ℝ)) / (N : ℝ))) atTop
      (𝓝 (∑' m : ℕ, progressionDivisorWeight r Q a (m + 1))) := by
  simp_rw [progression_coefficient_mean_eq_tsum hr ha]
  apply tendsto_tsum_of_dominated_convergence
    (bound := fun m : ℕ => (a + Q : ℕ) / (((m + 1 : ℕ) : ℝ) ^ r))
  · simpa [div_eq_mul_inv] using (summable_power_reciprocals hr).mul_left ((a + Q : ℕ) : ℝ)
  · intro m
    exact progressionDivisorFrequency_tendsto (by omega) hQ
  · filter_upwards [eventually_gt_atTop 0] with N hN
    intro m
    rw [Real.norm_eq_abs, abs_of_nonneg (progressionDivisorFrequency_nonneg _ _ _ _)]
    simpa only [Nat.cast_pow] using
      progressionDivisorFrequency_le (by positivity : 0 < (m + 1) ^ r) hQ ha hN

lemma progressionDivisorWeight_tsum_shift {r Q a : ℕ} (hr : 2 ≤ r) (hQ : 0 < Q) :
    (∑' m : ℕ, progressionDivisorWeight r Q a (m + 1)) =
      ∑' d : ℕ, progressionDivisorWeight r Q a d := by
  simpa only [sum_range_one, progressionDivisorWeight_zero (by omega : r ≠ 0), zero_add]
    using (summable_progressionDivisorWeight hr hQ).sum_add_tsum_nat_add 1

theorem progression_coefficient_mean_tendsto_all {r Q a : ℕ} (hr : 2 ≤ r)
    (hQ : 0 < Q) (ha : 0 < a) :
    Tendsto (fun N : ℕ =>
      ((∑ n ∈ range N, (powerDivisorCoeff r (a + Q * n) : ℝ)) / (N : ℝ))) atTop
      (𝓝 (∑' d : ℕ, progressionDivisorWeight r Q a d)) := by
  simpa only [progressionDivisorWeight_tsum_shift hr hQ] using
    progression_coefficient_mean_tendsto hr hQ ha

lemma progression_coefficient_mean_le {r Q a N : ℕ} (hr : 2 ≤ r)
    (hQ : 0 < Q) (ha : 0 < a) :
    ((∑ n ∈ range N, (powerDivisorCoeff r (a + Q * n) : ℝ)) / (N : ℝ)) ≤
      (a + Q : ℕ) * reciprocalTail r 0 := by
  by_cases hN : N = 0
  · simp only [hN, range_zero, sum_empty, Nat.cast_zero, div_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (reciprocalTail_nonneg _ _)
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  rw [progression_coefficient_mean_eq_tsum hr ha]
  have hbound : Summable (fun m : ℕ => (a + Q : ℕ) / (((m + 1 : ℕ) : ℝ) ^ r)) := by
    simpa [div_eq_mul_inv] using (summable_power_reciprocals hr).mul_left ((a + Q : ℕ) : ℝ)
  have hle : ∀ m : ℕ, progressionDivisorFrequency ((m + 1) ^ r) Q a N ≤
      (a + Q : ℕ) / (((m + 1 : ℕ) : ℝ) ^ r) := by
    intro m
    simpa only [Nat.cast_pow] using
      progressionDivisorFrequency_le (by positivity : 0 < (m + 1) ^ r) hQ ha hNpos
  calc
    _ ≤ ∑' m : ℕ, (a + Q : ℕ) / (((m + 1 : ℕ) : ℝ) ^ r) :=
      Summable.tsum_le_tsum hle
        (Summable.of_nonneg_of_le (fun m => progressionDivisorFrequency_nonneg _ _ _ _) hle hbound) hbound
    _ = (a + Q : ℕ) * reciprocalTail r 0 := by
      simp only [div_eq_mul_inv, tsum_mul_left, reciprocalTail, Nat.add_zero]

end PowerLambert
