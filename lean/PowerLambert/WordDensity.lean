import PowerLambert.ArithmeticControls
import PowerLambert.SeriesTailBound
import PowerLambert.WordVisits

noncomputable section
open Filter Set
open scoped BigOperators Topology Classical
set_option backward.isDefEq.respectTransparency false

namespace PowerLambert

theorem ControlProgression.tail_limit_le {b r H t A : ℕ}
    (P : ControlProgression b r H t A) (hb : 2 ≤ b) :
    (∑' j : ℕ, (∑' d : ℕ, progressionDivisorWeight r P.Q (P.n0+H+j+1) d) /
      (b : ℝ)^(H+j+1)) ≤
    (2*((A : ℝ)+1))/(b-1 : ℝ)*((b : ℝ)^H)⁻¹ +
    (2*((A : ℝ)+1))/(b-1 : ℝ)*(((b : ℝ)+1)^(H*(H+1))/(b : ℝ)^(H^3)) := by
  have h := weighted_near_far_tail_le hb (Nat.le_self_pow (by decide : 3 ≠ 0) H)
    (fun j => ∑' d : ℕ, progressionDivisorWeight r P.Q (P.n0+j) d)
    (C := 2*((A : ℝ)+1)) (B := ((b : ℝ)+1)^(H*(H+1)))
    (by positivity) (by positivity)
    (fun j => tsum_nonneg fun d => progressionDivisorWeight_nonneg r P.Q (P.n0+j) d)
    P.mean_near (fun j _ => P.mean_all j)
  convert h using 1
  · simp only [Nat.add_assoc]
  · ring

/-- Complete arithmetic word construction, after the finite CRT progression
has been supplied: the sieve and the averaged full carry give positive
lower density of actual visits to a closed subinterval of the word. -/
theorem ControlProgression.positiveLowerDensity_guardedWord
    {b r H l w : ℕ} (P : ControlProgression b r H (l+1) (b*w+1))
    (hb : 2 ≤ b) (hr : 2 ≤ r) (hw : w < b^l) (hH : l+1 ≤ H)
    (hsmall :
      (2*((((b*w+1 : ℕ) : ℝ))+1))/(b-1 : ℝ)*((b : ℝ)^H)⁻¹ +
      (2*((((b*w+1 : ℕ) : ℝ))+1))/(b-1 : ℝ)*
        (((b : ℝ)+1)^(H*(H+1))/(b : ℝ)^(H^3)) <
      (1/(2*(b : ℝ)^(l+1)))/16) :
    HasPositiveLowerDensity (fun n =>
      radixOrbit b (lambert b r) n ∈ guardedWordInterval b l w) := by
  let η : ℝ := 1/(2*(b : ℝ)^(l+1))
  let R : ℕ → ℝ := fun m => orbitSeries b r (P.n0+P.Q*m+H)/(b : ℝ)^H
  let L : ℝ := ∑' j : ℕ,
    (∑' d : ℕ, progressionDivisorWeight r P.Q (P.n0+H+j+1) d)/(b : ℝ)^(H+j+1)
  have hb0 : (0 : ℝ)<b := by exact_mod_cast (show 0<b by omega)
  have hη : 0 < η := by dsimp [η]; positivity
  have hlim : Tendsto (fun N : ℕ => (∑ m ∈ Finset.range N,R m)/(N : ℝ)) atTop (𝓝 L) :=
    progression_tail_mean_tendsto hb hr P.Q_pos P.n0 H
  have hL : L < η/16 := (P.tail_limit_le hb).trans_lt hsmall
  have hgood := positiveLowerDensity_powerFree_small_tail r P.u0 P.v hr
    P.u0_pos P.v_pos P.cofactor_coprime R η L hη
    (fun m => div_nonneg (orbitSeries_nonneg hb) (by positivity)) hlim hL
  have hword : HasPositiveLowerDensity (fun m =>
      radixOrbit b (lambert b r) (P.n0+P.Q*m) ∈ guardedWordInterval b l w) := by
    apply hgood.mono
    intro m hm
    apply radix_mem_guardedWordInterval_of_coefficients hb hr hw hH
    · rw [P.cofactor_eq]
      exact powerDivisorCoeff_prime_pow_mul_powerFree (by omega) Nat.prime_two
        (by omega) (by have := P.u0_pos; omega) (P.cofactor_odd m) hm.1
    · exact P.coeff_divisible m
    · exact hm.2.le
  exact hword.of_progression P.n0 P.Q P.Q_pos

end PowerLambert
