import PowerLambert.Basic

noncomputable section
open Filter Set
open scoped BigOperators Topology Classical
set_option backward.isDefEq.respectTransparency false

namespace PowerLambert

/-- A guarded target coefficient lies strictly inside the prescribed cylinder. -/
theorem guarded_coefficient_mem_cylinder (b l w : ℕ) (hb : 2 ≤ b)
    (hw : w < b ^ l) (R : ℝ)
    (hR0 : 0 ≤ R) (hR : R ≤ 1 / (2 * (b : ℝ) ^ (l + 1))) :
    ((b * w + 1 : ℕ) : ℝ) / (b : ℝ) ^ (l + 1) + R ∈ cylinder b l w := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hp : (0 : ℝ) < (b : ℝ)^l := pow_pos hb0 _
  have hp' : (0 : ℝ) < (b : ℝ)^(l+1) := pow_pos hb0 _
  have hc : (((b * w + 1 : ℕ) : ℝ) / (b : ℝ)^(l+1)) =
      (w : ℝ)/(b : ℝ)^l + 1 / (b : ℝ)^(l+1) := by
    push_cast
    rw [pow_succ]
    field_simp
  rw [hc]
  constructor
  · have : (0 : ℝ) < 1 / (b : ℝ)^(l+1) := by positivity
    change (w : ℝ)/(b : ℝ)^l ≤ _
    linarith
  · have hgap : 1 / (b : ℝ)^(l+1) + 1/(2*(b : ℝ)^(l+1)) < 1/(b : ℝ)^l := by
      rw [pow_succ]
      apply (lt_div_iff₀ hp).mpr
      field_simp
      nlinarith
    change _ < ((w : ℝ)+1)/(b : ℝ)^l
    rw [add_div]
    linarith

theorem cylinder_subset_unit (b l w : ℕ) (hb : 2 ≤ b) (hw : w < b^l) :
    cylinder b l w ⊆ Ico (0 : ℝ) 1 := by
  intro x hx
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hp : (0 : ℝ) < (b : ℝ)^l := pow_pos hb0 _
  have hlo : (0 : ℝ) ≤ w / (b : ℝ)^l := by positivity
  have hhi : ((w : ℝ)+1)/(b : ℝ)^l ≤ 1 := by
    apply (div_le_one hp).mpr
    exact_mod_cast (show w+1 ≤ b^l by omega)
  exact ⟨hlo.trans hx.1, hx.2.trans_le hhi⟩

/-- All controlled coefficients contribute an integer; only the target and tail remain. -/
theorem fract_coefficient_block (b K l A : ℕ) (hb : 2 ≤ b) (hl : l < K)
    (c : ℕ → ℕ) (hc : c l = A)
    (hdiv : ∀ j < K, j ≠ l → b^(j+1) ∣ c j) (R : ℝ) :
    Int.fract ((∑ j ∈ Finset.range K, (c j : ℝ)/(b : ℝ)^(j+1)) + R) =
      Int.fract ((A : ℝ)/(b : ℝ)^(l+1) + R) := by
  let q : ℕ := ∑ j ∈ (Finset.range K).erase l, c j / b^(j+1)
  have hsum : (∑ j ∈ (Finset.range K).erase l, (c j : ℝ)/(b : ℝ)^(j+1)) = (q : ℝ) := by
    dsimp [q]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rcases Finset.mem_erase.mp hj with ⟨hjl, hjK⟩
    have hd := hdiv j (Finset.mem_range.mp hjK) hjl
    rw [Nat.cast_div hd, Nat.cast_pow]
    exact_mod_cast (pow_ne_zero (j+1) (by omega : b ≠ 0))
  have hsplit := Finset.sum_erase_add (Finset.range K) (fun j => (c j : ℝ)/(b : ℝ)^(j+1))
    (Finset.mem_range.mpr hl)
  rw [← hsplit, hsum, hc]
  rw [add_assoc, Int.fract_natCast_add]

end PowerLambert
