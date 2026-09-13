import PowerLambert.Basic
import Mathlib.NumberTheory.Real.Irrational

noncomputable section
open Filter Set
open scoped Topology

namespace PowerLambert

/-- Disjunctivity in any integer base at least two implies irrationality. -/
theorem DisjunctiveInBase.irrational {b : ℕ} {x : ℝ}
    (h : DisjunctiveInBase b x) : Irrational x := by
  rintro ⟨q,rfl⟩
  have hb : (1 : ℝ)<b := by exact_mod_cast (show 1<b from by have := h.1; omega)
  have hd : (0 : ℝ)<q.den := by exact_mod_cast q.pos
  obtain ⟨l,hl⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hb).eventually
    (eventually_gt_atTop (2*(q.den : ℝ)))).exists
  have hp : 0 < (b : ℝ)^l := pow_pos (by linarith) _
  have hwl : 1 < b^l := by
    have hd1 : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
    exact_mod_cast (show (1 : ℝ)<(b : ℝ)^l by linarith)
  obtain ⟨n,hn⟩ := h.2 l 1 hwl
  simp only [radixOrbit, cylinder, Set.mem_Ico, Nat.cast_one] at hn
  have hz : Int.fract (((b : ℝ)^n*(q : ℝ))*(q.den : ℝ)) = 0 := by
    have heq : (((b : ℝ)^n*(q : ℝ))*(q.den : ℝ)) =
        (((b : ℤ)^n*q.num : ℤ) : ℝ) := by
      rw [Rat.cast_def]
      push_cast
      field_simp
    rw [heq, Int.fract_intCast]
  obtain ⟨z,hz'⟩ := Int.fract_mul_natCast ((b : ℝ)^n*(q : ℝ)) q.den
  rw [hz,sub_zero] at hz'
  have hzpos : 0 < z := by
    exact_mod_cast (show (0 : ℝ)<z from hz' ▸ mul_pos
      ((by positivity : (0 : ℝ)<1/(b : ℝ)^l).trans_le hn.1) hd)
  have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast hzpos
  have hprod := mul_lt_mul_of_pos_right hn.2 hd
  have hfrac : (1+1 : ℝ)/(b : ℝ)^l*(q.den : ℝ)<1 := by
    rw [div_mul_eq_mul_div]
    exact (div_lt_one hp).mpr (by linarith)
  linarith

end PowerLambert
