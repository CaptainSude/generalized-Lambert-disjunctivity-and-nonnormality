import PowerLambert.Word
import PowerLambert.SeriesBridge
import PowerLambert.DensityTransfer

noncomputable section
open Filter Set
open scoped BigOperators Topology Classical
set_option backward.isDefEq.respectTransparency false

namespace PowerLambert

def guardedWordInterval (b l w : ℕ) : Set ℝ :=
  Icc (((b*w+1 : ℕ) : ℝ)/(b : ℝ)^(l+1))
    (((b*w+1 : ℕ) : ℝ)/(b : ℝ)^(l+1) + 1/(2*(b : ℝ)^(l+1)))

theorem isCompact_guardedWordInterval (b l w : ℕ) :
    IsCompact (guardedWordInterval b l w) := isCompact_Icc

theorem guardedWordInterval_subset_cylinder {b l w : ℕ} (hb : 2 ≤ b) (hw : w < b^l) :
    guardedWordInterval b l w ⊆ cylinder b l w := by
  intro x hx
  have h := guarded_coefficient_mem_cylinder b l w hb hw
    (x-(((b*w+1 : ℕ) : ℝ)/(b : ℝ)^(l+1)))
    (sub_nonneg.mpr hx.1) (by have := hx.2; linarith)
  simpa only [add_sub_cancel] using h

/-- A prescribed finite coefficient block and its full remaining carry
place the actual Lambert radix orbit in a closed interval inside the word. -/
theorem radix_mem_guardedWordInterval_of_coefficients {b r l w n H : ℕ}
    (hb : 2 ≤ b) (hr : 2 ≤ r) (hw : w < b^l) (hH : l+1 ≤ H)
    (htarget : powerDivisorCoeff r (n+(l+1)) = b*w+1)
    (hcontrol : ∀ j, 1 ≤ j → j ≤ H → j ≠ l+1 → b^j ∣ powerDivisorCoeff r (n+j))
    (htail : orbitSeries b r (n+H)/(b : ℝ)^H ≤ 1/(2*(b : ℝ)^(l+1))) :
    radixOrbit b (lambert b r) n ∈ guardedWordInterval b l w := by
  let R := orbitSeries b r (n+H)/(b : ℝ)^H
  have hR : 0 ≤ R := div_nonneg (orbitSeries_nonneg hb) (by positivity)
  have hmem : (((b*w+1 : ℕ) : ℝ)/(b : ℝ)^(l+1))+R ∈ cylinder b l w :=
    guarded_coefficient_mem_cylinder b l w hb hw R hR htail
  have hunit := cylinder_subset_unit b l w hb hw hmem
  have hfract := fract_coefficient_block b H l (b*w+1) hb (by omega)
    (fun j => powerDivisorCoeff r (n+j+1))
    (by simpa only [Nat.add_assoc] using htarget)
    (fun j hj hne => by
      simpa only [Nat.add_assoc] using hcontrol (j+1) (by omega) (by omega) (by omega)) R
  have hexp := finite_coefficient_expansion hb hr n H
  have hexp' : (∑ j ∈ Finset.range H,
      (powerDivisorCoeff r (n+j+1) : ℝ)/(b : ℝ)^(j+1))+R = orbitSeries b r n := by
    rw [hexp]
    dsimp [R]
    ring
  rw [hexp', Int.fract_eq_self.mpr hunit] at hfract
  change Int.fract ((b : ℝ)^n*lambert b r) ∈ _
  rw [fract_radix_eq_orbitSeries hb hr, hfract]
  exact ⟨by linarith, by dsimp [R] at *; linarith⟩

end PowerLambert
