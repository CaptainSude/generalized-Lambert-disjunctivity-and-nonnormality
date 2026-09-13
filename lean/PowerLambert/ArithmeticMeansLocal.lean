import PowerLambert.Arithmetic
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Finset
open scoped BigOperators Topology

namespace PowerLambert

/-- The unrestricted local mean summand when a residue is fixed modulo `p^s`. -/
noncomputable def primeLocalTerm (p r s k : ℕ) : ℝ :=
  (p : ℝ) ^ min (r * k) s / (p : ℝ) ^ (r * k)

theorem primeLocalTerm_nonneg {p r s k : ℕ} : 0 ≤ primeLocalTerm p r s k := by
  exact div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _)

theorem primeLocalTerm_eq_one {p r B k : ℕ} (hp : 2 ≤ p) (hk : k < B) :
    primeLocalTerm p r (r * (B - 1) + 1) k = 1 := by
  have he : r * k ≤ r * (B - 1) + 1 :=
    (Nat.mul_le_mul_left r (show k ≤ B - 1 by omega)).trans (Nat.le_succ _)
  simp [primeLocalTerm, min_eq_left he, pow_ne_zero _ (show (p : ℝ) ≠ 0 by exact_mod_cast (by omega : p ≠ 0))]

theorem primeLocalTerm_tail_bound {p r B : ℕ} (hp : 2 ≤ p) (hr : 2 ≤ r)
    (hB : 1 ≤ B) (n : ℕ) :
    primeLocalTerm p r (r * (B - 1) + 1) (n + B) ≤ (1 / (2 : ℝ)) ^ (n + 1) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : 0 < (p : ℝ) := by linarith
  have hBdecomp : B - 1 + 1 = B := Nat.sub_add_cancel hB
  have hexp : r * (B - 1) + 1 + (n + 1) ≤ r * (n + B) := by
    have hh := Nat.mul_le_mul_right (n + 1) hr
    nlinarith
  have hmin : min (r * (n + B)) (r * (B - 1) + 1) = r * (B - 1) + 1 :=
    min_eq_right (by omega)
  rw [primeLocalTerm, hmin, one_div_pow]
  apply (div_le_div_iff₀ (pow_pos hp0 _) (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
  rw [one_mul]
  calc
    (p : ℝ) ^ (r * (B - 1) + 1) * 2 ^ (n + 1) ≤
        (p : ℝ) ^ (r * (B - 1) + 1) * (p : ℝ) ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hpR _) (pow_nonneg hp0.le _)
    _ = (p : ℝ) ^ (r * (B - 1) + 1 + (n + 1)) := (pow_add _ _ _).symm
    _ ≤ (p : ℝ) ^ (r * (n + B)) := pow_le_pow_right₀ (by linarith) hexp

theorem summable_primeLocalTerm {p r B : ℕ} (hp : 2 ≤ p) (hr : 2 ≤ r) (hB : 1 ≤ B) :
    Summable (primeLocalTerm p r (r * (B - 1) + 1)) := by
  rw [← summable_nat_add_iff B]
  exact Summable.of_nonneg_of_le (fun _ => primeLocalTerm_nonneg)
    (primeLocalTerm_tail_bound hp hr hB)
    (summable_geometric_two.comp_injective (fun m n h => by omega))

/-- Uniform constrained-prime bound, including the residue zero and all recurrent offsets. -/
theorem tsum_primeLocalTerm_le {p r B : ℕ} (hp : 2 ≤ p) (hr : 2 ≤ r) (hB : 1 ≤ B) :
    (∑' k, primeLocalTerm p r (r * (B - 1) + 1) k) ≤ B + 1 := by
  have hs := summable_primeLocalTerm hp hr hB
  have hg : Summable (fun n : ℕ => (1 / (2 : ℝ)) ^ (n + 1)) :=
    summable_geometric_two.comp_injective (fun m n h => by omega)
  have hsum : (∑' n : ℕ, (1 / (2 : ℝ)) ^ (n + 1)) = 1 := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_two]
    norm_num
  rw [← hs.sum_add_tsum_nat_add B]
  have hhead : (∑ k ∈ range B, primeLocalTerm p r (r * (B - 1) + 1) k) = (B : ℝ) := by
    calc
      _ = ∑ _k ∈ range B, (1 : ℝ) :=
        Finset.sum_congr rfl (fun k hk => primeLocalTerm_eq_one hp (Finset.mem_range.mp hk))
      _ = _ := by simp
  rw [hhead]
  apply add_le_add le_rfl
  rw [← hsum]
  exact Summable.tsum_le_tsum (primeLocalTerm_tail_bound hp hr hB)
    ((summable_nat_add_iff B).mpr hs) hg

/-- Conditioning on a particular residue only removes nonnegative local terms. -/
theorem tsum_primeLocalTerm_residue_le {p r B a : ℕ} (hp : 2 ≤ p) (hr : 2 ≤ r)
    (hB : 1 ≤ B) :
    (∑' k, if p ^ min (r * k) (r * (B - 1) + 1) ∣ a then
      primeLocalTerm p r (r * (B - 1) + 1) k else 0) ≤ B + 1 := by
  have hs := summable_primeLocalTerm hp hr hB
  have hle : ∀ k, (if p ^ min (r * k) (r * (B - 1) + 1) ∣ a then
      primeLocalTerm p r (r * (B - 1) + 1) k else 0) ≤
      primeLocalTerm p r (r * (B - 1) + 1) k := by
    intro k
    split_ifs <;> simp [primeLocalTerm_nonneg]
  have hnonneg : ∀ k, 0 ≤ (if p ^ min (r * k) (r * (B - 1) + 1) ∣ a then
      primeLocalTerm p r (r * (B - 1) + 1) k else 0) := by
    intro k
    split_ifs <;> simp [primeLocalTerm_nonneg]
  exact (Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le hnonneg hle hs) hs).trans
    (tsum_primeLocalTerm_le hp hr hB)

theorem tsum_primeLocalTerm_residue_eq_one {p r s a : ℕ} (hr : r ≠ 0) (hs : s ≠ 0)
    (ha : ¬ p ∣ a) :
    (∑' k, if p ^ min (r * k) s ∣ a then primeLocalTerm p r s k else 0) = 1 := by
  rw [tsum_eq_single 0]
  · simp [primeLocalTerm]
  · intro k hk
    have he : min (r * k) s ≠ 0 := by
      have := Nat.mul_pos (Nat.pos_of_ne_zero hr) (Nat.pos_of_ne_zero hk)
      omega
    have hnot : ¬ p ^ min (r * k) s ∣ a := fun h => ha ((dvd_pow_self p he).trans h)
    simp [hnot]

theorem tsum_unconstrained_prime_factor {p r : ℕ} (hp : 2 ≤ p) (hr : r ≠ 0) :
    (∑' k : ℕ, (1 : ℝ) / (p : ℝ) ^ (r * k)) =
      1 / (1 - 1 / (p : ℝ) ^ r) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hpow : (1 : ℝ) < (p : ℝ) ^ r := one_lt_pow₀ hpR hr
  have hq0 : 0 ≤ 1 / (p : ℝ) ^ r := by positivity
  have hq1 : 1 / (p : ℝ) ^ r < 1 := (div_lt_one (by positivity)).mpr hpow
  simp_rw [pow_mul, ← one_div_pow]
  simpa only [one_div_pow, one_div, inv_pow] using tsum_geometric_of_lt_one hq0 hq1

end PowerLambert
