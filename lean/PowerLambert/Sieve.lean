import Mathlib.Analysis.PSeries
import Mathlib.Tactic

noncomputable section
open Filter Set
open scoped BigOperators Topology Classical

namespace PowerLambert

/-- A telescoping majorant avoids any numerical zeta-function estimate. -/
theorem inv_pow_le_telescoping (r n : ℕ) (hr : 2 ≤ r) :
    (((n : ℝ) + 3) ^ r)⁻¹ ≤ ((n : ℝ) + 2)⁻¹ - ((n : ℝ) + 3)⁻¹ := by
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h3 : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  have hp : ((n : ℝ) + 3) ^ 2 ≤ ((n : ℝ) + 3) ^ r :=
    pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith) hr
  have hmul : ((n : ℝ) + 2) * ((n : ℝ) + 3) ≤ ((n : ℝ) + 3) ^ r := by
    nlinarith
  calc
    _ ≤ (((n : ℝ) + 2) * ((n : ℝ) + 3))⁻¹ :=
      inv_anti₀ (mul_pos h2 h3) hmul
    _ = _ := by field_simp; ring

theorem sum_inv_pow_from_three_le (r K : ℕ) (hr : 2 ≤ r) :
    (∑ n ∈ Finset.range K, (((n : ℝ) + 3) ^ r)⁻¹) ≤
      (1 / 2 : ℝ) - ((K : ℝ) + 2)⁻¹ := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hn := inv_pow_le_telescoping r K hr
    push_cast
    have h := add_le_add ih hn
    have he : (K : ℝ) + 1 + 2 = (K : ℝ) + 3 := by ring
    rw [he]
    linarith

/-- The uniform 3/4 sieve constant holds already for every finite cutoff. -/
theorem sum_inv_pow_from_two_le (r K : ℕ) (hr : 2 ≤ r) :
    (∑ n ∈ Finset.range K, (((n : ℝ) + 2) ^ r)⁻¹) ≤ (3 / 4 : ℝ) := by
  cases K with
  | zero => norm_num
  | succ K =>
    rw [Finset.sum_range_succ']
    have htail := sum_inv_pow_from_three_le r K hr
    have hp : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hr
    have hfirst : ((2 : ℝ) ^ r)⁻¹ ≤ 1 / 4 := by
      have hi := inv_anti₀ (by norm_num : (0 : ℝ) < (2 : ℝ)^2) hp
      norm_num at hi ⊢
      exact hi
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add]
    have he : (fun n : ℕ => (((n : ℝ) + 1 + 2) ^ r)⁻¹) =
        (fun n : ℕ => (((n : ℝ) + 3) ^ r)⁻¹) := by
      funext n
      congr 2
      ring
    rw [he]
    have hn : 0 ≤ ((K : ℝ) + 2)⁻¹ := by positivity
    linarith

theorem sum_inv_pow_finset_le (r : ℕ) (hr : 2 ≤ r) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 2 ≤ n) :
    (∑ n ∈ S, ((n : ℝ) ^ r)⁻¹) ≤ (3 / 4 : ℝ) := by
  let T := S.image (fun n => n - 2)
  have ht : T ⊆ Finset.range (S.sup id + 1) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    apply Finset.mem_range.mpr
    have hsup : p ≤ S.sup id := Finset.le_sup (f := id) hp
    omega
  have he : (∑ n ∈ S, ((n : ℝ) ^ r)⁻¹) =
      ∑ n ∈ T, (((n : ℝ) + 2) ^ r)⁻¹ := by
    dsimp [T]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      have hcast : ((n - 2 : ℕ) : ℝ) + 2 = n := by
        exact_mod_cast (Nat.sub_add_cancel (hS n hn))
      rw [hcast]
    · intro x hx y hy hxy
      change x - 2 = y - 2 at hxy
      calc
        x = (x - 2) + 2 := (Nat.sub_add_cancel (hS x hx)).symm
        _ = (y - 2) + 2 := congrArg (fun n => n + 2) hxy
        _ = y := Nat.sub_add_cancel (hS y hy)
  rw [he]
  exact (Finset.sum_le_sum_of_subset_of_nonneg ht (by
    intro n _ _
    positivity)).trans (sum_inv_pow_from_two_le r _ hr)

end PowerLambert
