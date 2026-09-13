import PowerLambert.Series
import Mathlib.Algebra.Order.Floor.Ring

open scoped BigOperators Topology
open Filter Finset

namespace PowerLambert

lemma residueTerm_step {b d n : ℕ} (hb : 2 ≤ b) (hd : 0 < d) :
    (b : ℝ) * residueTerm b d n =
      residueTerm b d (n + 1) + if d ∣ n + 1 then 1 else 0 := by
  have hden : (b : ℝ) ^ d - 1 ≠ 0 := ne_of_gt (pow_sub_one_pos hb hd)
  have hmod : (n + 1) % d = (n % d + 1) % d := by
    simp only [Nat.add_mod, Nat.mod_mod]
  have hnmod := Nat.mod_lt n hd
  by_cases h : d ∣ n + 1
  · have hzero := Nat.mod_eq_zero_of_dvd h
    have hlast : n % d + 1 = d := by
      by_contra hne
      have hlt : n % d + 1 < d := by omega
      have heq : (n + 1) % d = n % d + 1 := by rw [hmod, Nat.mod_eq_of_lt hlt]
      omega
    simp only [residueTerm, hzero, pow_zero, h, ↓reduceIte]
    rw [← mul_div_assoc, ← pow_succ', hlast]
    field_simp
    ring
  · have hlt : n % d + 1 < d := by
      have hnonzero : (n + 1) % d ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using h
      by_contra hnlt
      have heq : n % d + 1 = d := by omega
      rw [hmod, heq, Nat.mod_self] at hnonzero
      exact hnonzero rfl
    have hnext : (n + 1) % d = n % d + 1 := by rw [hmod, Nat.mod_eq_of_lt hlt]
    simp only [residueTerm, hnext, h, ↓reduceIte, add_zero]
    rw [← mul_div_assoc, pow_succ']

def carryCoeff (r v : ℕ) : ℕ :=
  ((range v).filter fun m => (m + 1) ^ r ∣ v).card

lemma power_dvd_bound {r v m : ℕ} (hr : 1 ≤ r) (hv : 0 < v)
    (h : (m + 1) ^ r ∣ v) : m < v := by
  have hpower : m + 1 ≤ (m + 1) ^ r := Nat.le_self_pow (by omega) _
  have := Nat.le_of_dvd hv h
  omega

lemma carryCoeff_tsum {r v : ℕ} (hr : 1 ≤ r) (hv : 0 < v) :
    (∑' m : ℕ, if (m + 1) ^ r ∣ v then (1 : ℝ) else 0) = carryCoeff r v := by
  rw [tsum_eq_sum (s := range v)]
  · simp [carryCoeff, sum_boole]
  · intro m hm
    have hn : ¬ (m + 1) ^ r ∣ v := by
      intro hd
      exact hm (mem_range.mpr (power_dvd_bound hr hv hd))
    simp [hn]

lemma carryCoeff_summable {r v : ℕ} (hr : 1 ≤ r) (hv : 0 < v) :
    Summable (fun m : ℕ => if (m + 1) ^ r ∣ v then (1 : ℝ) else 0) := by
  apply summable_of_ne_finset_zero (s := range v)
  intro m hm
  have hn : ¬ (m + 1) ^ r ∣ v := by
    intro hd
    exact hm (mem_range.mpr (power_dvd_bound hr hv hd))
  simp [hn]

lemma orbitSeries_step {b r n : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    (b : ℝ) * orbitSeries b r n = orbitSeries b r (n + 1) + carryCoeff r (n + 1) := by
  calc
    (b : ℝ) * orbitSeries b r n =
        ∑' m : ℕ, (b : ℝ) * residueTerm b ((m + 1) ^ r) n := by
      exact (tsum_mul_left).symm
    _ = ∑' m : ℕ, (residueTerm b ((m + 1) ^ r) (n + 1) +
        if (m + 1) ^ r ∣ n + 1 then 1 else 0) := by
      exact tsum_congr (fun m => residueTerm_step hb (by positivity))
    _ = _ := by
      rw [Summable.tsum_add (orbitSeries_summable hb hr)
        (carryCoeff_summable (by omega : 1 ≤ r) (by omega : 0 < n + 1)),
        carryCoeff_tsum (by omega : 1 ≤ r) (by omega : 0 < n + 1)]
      rfl

theorem exists_nat_radix_prefix {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) (n : ℕ) :
    ∃ k : ℕ, (b : ℝ) ^ n * lambert b r = orbitSeries b r n + k := by
  induction n with
  | zero => exact ⟨0, by simp [orbitSeries_zero]⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨carryCoeff r (n + 1) + b * k, ?_⟩
    rw [pow_succ', mul_assoc, hk, mul_add, orbitSeries_step hb hr]
    push_cast
    ring

theorem fract_radix_eq_orbitSeries {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) (n : ℕ) :
    Int.fract ((b : ℝ) ^ n * lambert b r) = Int.fract (orbitSeries b r n) := by
  obtain ⟨k, hk⟩ := exists_nat_radix_prefix hb hr n
  rw [hk, Int.fract_add_natCast]

end PowerLambert
