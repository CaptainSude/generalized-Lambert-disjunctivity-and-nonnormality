import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

noncomputable section
open Filter Set
open scoped BigOperators Topology Classical

namespace PowerLambert

/-- The count of one residue class differs from N/d by at most one. -/
theorem residue_count_bounds (d a N : ℕ) (hd : 0 < d) :
    (N : ℝ) / d - 1 ≤
      (((Finset.range N).filter (fun n => Nat.ModEq d n a)).card : ℝ) ∧
    (((Finset.range N).filter (fun n => Nat.ModEq d n a)).card : ℝ) ≤
      (N : ℝ) / d + 1 := by
  have he := Nat.count_modEq_card N hd a
  rw [Nat.count_eq_card_filter_range] at he
  have hfloor : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
  have hfloor' : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
    have h := Nat.lt_mul_div_succ N hd
    simpa only [mul_comm] using (show (N : ℝ) < (d : ℝ) * ((N / d : ℕ) + 1) by exact_mod_cast h)
  rw [he]
  split_ifs <;> push_cast <;> constructor <;> linarith

/-- Every fixed residue class has its expected frequency over all prefixes. -/
theorem residue_frequency (d a : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n => Nat.ModEq d n a)).card : ℝ) / N)
      atTop (𝓝 (1 / (d : ℝ))) := by
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun N : ℕ => 1 / (d : ℝ) - (N : ℝ)⁻¹) atTop
      (𝓝 (1 / (d : ℝ))) := by simpa using tendsto_const_nhds.sub hinv
  have hhi : Tendsto (fun N : ℕ => 1 / (d : ℝ) + (N : ℝ)⁻¹) atTop
      (𝓝 (1 / (d : ℝ))) := by simpa using tendsto_const_nhds.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have h := div_le_div_of_nonneg_right (residue_count_bounds d a N hd).1 hNr.le
    convert h using 1 <;> field_simp <;> ring
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have h := div_le_div_of_nonneg_right (residue_count_bounds d a N hd).2 hNr.le
    convert h using 1 <;> field_simp <;> ring

end PowerLambert
