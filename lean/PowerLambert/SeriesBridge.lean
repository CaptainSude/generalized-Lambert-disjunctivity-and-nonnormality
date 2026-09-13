import PowerLambert.SeriesOrbit
import PowerLambert.SeriesTail
import PowerLambert.Arithmetic

open scoped BigOperators Topology
open Filter Finset

namespace PowerLambert

lemma carryCoeff_eq_powerDivisorCoeff {r v : ℕ} (hr : r ≠ 0) (hv : v ≠ 0) :
    carryCoeff r v = powerDivisorCoeff r v := by
  rw [powerDivisorCoeff_eq_card_filter hr hv]
  unfold carryCoeff
  apply card_bij (fun m _ => m + 1)
  · intro m hm
    obtain ⟨hm, hdiv⟩ := mem_filter.mp hm
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by have := mem_range.mp hm; omega⟩, hdiv⟩
  · intro a ha c hc h
    omega
  · intro d hd
    obtain ⟨hd, hdiv⟩ := mem_filter.mp hd
    obtain ⟨hd1, hdv⟩ := mem_Icc.mp hd
    refine ⟨d - 1, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, by omega⟩
    simpa [Nat.sub_add_cancel hd1] using hdiv

lemma orbitSeries_nonneg {b r n : ℕ} (hb : 2 ≤ b) : 0 ≤ orbitSeries b r n := by
  exact tsum_nonneg fun m => residueTerm_nonneg hb (by positivity)

lemma orbitSeries_le_linear {b r n : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    orbitSeries b r n ≤ (n + 1 : ℕ) * reciprocalTail r 0 / (b - 1 : ℝ) := by
  have hsum := sum_orbitTail_le (U := 0) (N := n + 1) hb hr
  have hterm : orbitSeries b r n ≤ ∑ k ∈ range (n + 1), orbitSeries b r k :=
    single_le_sum (f := fun k => orbitSeries b r k)
      (fun i hi => orbitSeries_nonneg hb) (mem_range.mpr (Nat.lt_succ_self n))
  exact hterm.trans (by simpa [orbitTail, orbitSeries] using hsum)

lemma scaledOrbit_tendsto_zero {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) (n : ℕ) :
    Tendsto (fun k : ℕ => orbitSeries b r (n + k) / (b : ℝ) ^ k) atTop (𝓝 0) := by
  have hb' : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hzero : Tendsto (fun k : ℕ => (1 : ℝ) / (b : ℝ) ^ k) atTop (𝓝 0) := by
    simpa only [pow_zero] using tendsto_pow_const_div_const_pow_of_one_lt 0 hb'
  have hlinear : Tendsto (fun k : ℕ => (k : ℝ) / (b : ℝ) ^ k) atTop (𝓝 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 hb'
  have hbound : Tendsto (fun k : ℕ =>
      ((n + k + 1 : ℕ) : ℝ) * reciprocalTail r 0 / (b - 1 : ℝ) / (b : ℝ) ^ k)
      atTop (𝓝 0) := by
    convert ((hzero.const_mul ((n : ℝ) + 1)).add hlinear).mul_const
      (reciprocalTail r 0 / (b - 1 : ℝ)) using 1
    · ext k
      push_cast
      ring
    · simp
  apply squeeze_zero (fun k => div_nonneg (orbitSeries_nonneg hb) (by positivity))
    (fun k => div_le_div_of_nonneg_right (orbitSeries_le_linear hb hr) (by positivity)) hbound

lemma finite_coefficient_expansion {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) (n K : ℕ) :
    (∑ j ∈ range K, (powerDivisorCoeff r (n + j + 1) : ℝ) / (b : ℝ) ^ (j + 1)) =
      orbitSeries b r n - orbitSeries b r (n + K) / (b : ℝ) ^ K := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih]
    have hstep := orbitSeries_step (n := n + K) hb hr
    rw [carryCoeff_eq_powerDivisorCoeff (by omega : r ≠ 0) (by omega : n + K + 1 ≠ 0)] at hstep
    simp only [Nat.add_assoc] at hstep ⊢
    rw [pow_succ]
    field_simp
    nlinarith

theorem hasSum_coefficient_expansion {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) (n : ℕ) :
    HasSum (fun j : ℕ => (powerDivisorCoeff r (n + j + 1) : ℝ) / (b : ℝ) ^ (j + 1))
      (orbitSeries b r n) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => by positivity)]
  simp_rw [finite_coefficient_expansion hb hr]
  simpa using tendsto_const_nhds.sub (scaledOrbit_tendsto_zero hb hr n)

theorem orbitSeries_eq_coefficient_expansion {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) (n : ℕ) :
    orbitSeries b r n =
      ∑' j : ℕ, (powerDivisorCoeff r (n + j + 1) : ℝ) / (b : ℝ) ^ (j + 1) :=
  (hasSum_coefficient_expansion hb hr n).tsum_eq.symm

theorem lambert_eq_coefficient_expansion {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    lambert b r = ∑' j : ℕ, (powerDivisorCoeff r (j + 1) : ℝ) / (b : ℝ) ^ (j + 1) := by
  simpa only [orbitSeries_zero, Nat.zero_add] using orbitSeries_eq_coefficient_expansion hb hr 0

end PowerLambert
