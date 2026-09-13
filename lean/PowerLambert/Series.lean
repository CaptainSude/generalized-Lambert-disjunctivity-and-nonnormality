import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

open scoped BigOperators
open Filter Finset

namespace PowerLambert

noncomputable def lambert (b r : ℕ) : ℝ :=
  ∑' m : ℕ, (((b : ℝ) ^ ((m + 1) ^ r) - 1)⁻¹)

noncomputable def residueTerm (b d n : ℕ) : ℝ :=
  (b : ℝ) ^ (n % d) / ((b : ℝ) ^ d - 1)

noncomputable def orbitSeries (b r n : ℕ) : ℝ :=
  ∑' m : ℕ, residueTerm b ((m + 1) ^ r) n

lemma pow_sub_one_pos {b d : ℕ} (hb : 2 ≤ b) (hd : 0 < d) :
    0 < (b : ℝ) ^ d - 1 := by
  have h : 1 < (b : ℝ) := by exact_mod_cast (show 1 < b by omega)
  exact sub_pos.mpr (one_lt_pow₀ h (by omega))

lemma nat_le_pow_sub_one {b d : ℕ} (hb : 2 ≤ b) :
    (d : ℝ) ≤ (b : ℝ) ^ d - 1 := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have hp : 1 ≤ (b : ℝ) ^ d := one_le_pow₀ (by linarith)
    nlinarith

lemma summable_power_reciprocals {r : ℕ} (hr : 2 ≤ r) :
    Summable (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ r)⁻¹) := by
  exact (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by omega))

lemma lambert_summable {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    Summable (fun m : ℕ => (((b : ℝ) ^ ((m + 1) ^ r) - 1)⁻¹)) := by
  refine Summable.of_nonneg_of_le
    (fun m => inv_nonneg.mpr (le_of_lt (pow_sub_one_pos hb (by positivity))))
    ?_ (summable_power_reciprocals hr)
  intro m
  exact inv_anti₀ (by positivity) (by simpa only [Nat.cast_pow] using
    (nat_le_pow_sub_one (d := (m + 1) ^ r) hb))

lemma residueTerm_nonneg {b d n : ℕ} (hb : 2 ≤ b) (hd : 0 < d) :
    0 ≤ residueTerm b d n := by
  unfold residueTerm
  positivity [pow_sub_one_pos hb hd]

lemma residueTerm_le {b d n : ℕ} (hb : 2 ≤ b) (hd : 0 < d) :
    residueTerm b d n ≤ (b : ℝ) ^ n / d := by
  unfold residueTerm
  apply div_le_div₀ (by positivity)
  · exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ b by omega)) (Nat.mod_le _ _)
  · exact_mod_cast hd
  · exact nat_le_pow_sub_one hb

lemma orbitSeries_summable {b r n : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    Summable (fun m : ℕ => residueTerm b ((m + 1) ^ r) n) := by
  apply Summable.of_nonneg_of_le (fun m => residueTerm_nonneg hb (by positivity))
  · intro m
    exact residueTerm_le hb (by positivity)
  · simpa [div_eq_mul_inv, Nat.cast_pow] using (summable_power_reciprocals hr).mul_left ((b : ℝ) ^ n)

lemma residueTerm_periodic (b d : ℕ) : Function.Periodic (residueTerm b d) d := by
  intro n
  simp [residueTerm, Nat.add_mod]

lemma orbitSeries_zero (b r : ℕ) : orbitSeries b r 0 = lambert b r := by
  simp [orbitSeries, residueTerm, lambert]

lemma monotone_prefix_sum_le {f : ℕ → ℝ} (hf : Monotone f) {s d : ℕ}
    (hsd : s ≤ d) :
    (d : ℝ) * (∑ i ∈ range s, f i) ≤ (s : ℝ) * (∑ i ∈ range d, f i) := by
  induction d, hsd using Nat.le_induction with
  | base => exact le_rfl
  | succ d hsd ih =>
    have hsum : (∑ i ∈ range s, f i) ≤ (s : ℝ) * f d := by
      calc
        (∑ i ∈ range s, f i) ≤ ∑ _i ∈ range s, f d :=
          sum_le_sum fun i hi => hf (by have := mem_range.mp hi; omega)
        _ = (s : ℝ) * f d := by simp
    rw [sum_range_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma geometric_prefix_ratio_le {b d s : ℕ} (hb : 2 ≤ b) (hd : 0 < d)
    (hsd : s ≤ d) :
    ((b : ℝ) ^ s - 1) / ((b : ℝ) ^ d - 1) ≤ (s : ℝ) / d := by
  have hb' : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h := monotone_prefix_sum_le
    (f := fun i => (b : ℝ) ^ i) (fun i j hij => pow_le_pow_right₀ hb'.le hij) hsd
  have hm := mul_le_mul_of_nonneg_right h (sub_nonneg.mpr hb'.le)
  rw [mul_assoc, geom_sum_mul, mul_assoc, geom_sum_mul] at hm
  exact (div_le_div_iff₀ (pow_sub_one_pos hb hd) hd').mpr (by nlinarith)

lemma sum_residueTerm_mul (b d q : ℕ) :
    (∑ n ∈ range (q * d), residueTerm b d n) =
      (q : ℝ) * (∑ n ∈ range d, residueTerm b d n) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    have hshift : (∑ x ∈ range d, residueTerm b d (q * d + x)) =
        ∑ x ∈ range d, residueTerm b d x := by
      apply sum_congr rfl
      intro x hx
      simp [residueTerm, Nat.add_mod]
    rw [hshift, Nat.cast_add, Nat.cast_one]
    ring

lemma sum_residueTerm_prefix {b d s : ℕ} (hb : 2 ≤ b) (hsd : s ≤ d) :
    (∑ n ∈ range s, residueTerm b d n) =
      (((b : ℝ) ^ s - 1) / ((b : ℝ) ^ d - 1)) / (b - 1 : ℝ) := by
  have hb' : (b : ℝ) ≠ 1 := by exact_mod_cast (show b ≠ 1 by omega)
  calc
    (∑ n ∈ range s, residueTerm b d n) =
        (∑ n ∈ range s, (b : ℝ) ^ n) / ((b : ℝ) ^ d - 1) := by
      rw [sum_div]
      apply sum_congr rfl
      intro n hn
      simp [residueTerm, Nat.mod_eq_of_lt (lt_of_lt_of_le (mem_range.mp hn) hsd)]
    _ = _ := by rw [geom_sum_eq hb']; ring

lemma sum_residueTerm_period {b d : ℕ} (hb : 2 ≤ b) (hd : 0 < d) :
    (∑ n ∈ range d, residueTerm b d n) = (b - 1 : ℝ)⁻¹ := by
  rw [sum_residueTerm_prefix hb le_rfl, div_self (ne_of_gt (pow_sub_one_pos hb hd))]
  simp

lemma sum_residueTerm_le {b d N : ℕ} (hb : 2 ≤ b) (hd : 0 < d) :
    (∑ n ∈ range N, residueTerm b d n) ≤ (N : ℝ) / d / (b - 1 : ℝ) := by
  have hb' : (0 : ℝ) < b - 1 := by exact_mod_cast (show 0 < (b : ℤ) - 1 by omega)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hN : N = N / d * d + N % d := by
    simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div N d).symm
  have hsum : (∑ n ∈ range N, residueTerm b d n) =
      (N / d : ℕ) / (b - 1 : ℝ) +
        (((b : ℝ) ^ (N % d) - 1) / ((b : ℝ) ^ d - 1)) / (b - 1 : ℝ) := by
    conv_lhs => rw [hN]
    rw [sum_range_add, sum_residueTerm_mul, sum_residueTerm_period hb hd]
    have hshift : (∑ x ∈ range (N % d), residueTerm b d (N / d * d + x)) =
        ∑ x ∈ range (N % d), residueTerm b d x := by
      apply sum_congr rfl
      intro x hx
      simp [residueTerm, Nat.add_mod]
    rw [hshift, sum_residueTerm_prefix hb (Nat.mod_lt N hd).le]
    simp [div_eq_mul_inv]
  rw [hsum]
  calc
    _ ≤ (N / d : ℕ) / (b - 1 : ℝ) + ((N % d : ℕ) : ℝ) / d / (b - 1 : ℝ) :=
      add_le_add_right (div_le_div_of_nonneg_right
        (geometric_prefix_ratio_le hb hd (Nat.mod_lt N hd).le) hb'.le) _
    _ = (N : ℝ) / d / (b - 1 : ℝ) := by
      have hcast : (N : ℝ) = (N / d : ℕ) * (d : ℝ) + (N % d : ℕ) := by exact_mod_cast hN
      rw [hcast]
      field_simp
      <;> ring

end PowerLambert
