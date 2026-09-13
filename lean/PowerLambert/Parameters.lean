import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

noncomputable section
open Filter Set
open scoped BigOperators Topology Classical
namespace PowerLambert

def largePrime (L i : ℕ) : ℕ := Nat.nth Nat.Prime (L + 1 + i)

theorem largePrime_prime (L i : ℕ) : (largePrime L i).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _

theorem largePrime_gt (L i : ℕ) : L < largePrime L i := by
  have h := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).id_le (L+1+i)
  change L+1+i ≤ Nat.nth Nat.Prime (L+1+i) at h
  dsimp [largePrime]
  omega

theorem largePrime_injective (L : ℕ) : Function.Injective (largePrime L) := by
  intro i j hij
  have h := Nat.nth_injective Nat.infinite_setOfPred_prime hij
  omega

theorem cubic_dominates_control_count (H : ℕ) (hH : 3 ≤ H) :
    2 * (H * (H + 1)) + H ≤ H ^ 3 := by
  have h := Nat.mul_le_mul_left (H*(H+1)) hH
  nlinarith

/-- The protected cubic range absorbs every later recurrence of the control primes. -/
theorem far_tail_factor_le (b H : ℕ) (hb : 2 ≤ b) (hH : 3 ≤ H) :
    ((b : ℝ) + 1)^(H*(H+1)) / (b : ℝ)^(H^3) ≤ 1/(b : ℝ)^H := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbase : (b : ℝ)+1 ≤ (b : ℝ)^2 := by nlinarith
  have hcontrol : ((b : ℝ)+1)^(H*(H+1)) ≤ (b : ℝ)^(2*(H*(H+1))) := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity) hbase (H*(H+1))
  apply (div_le_div_iff₀ (pow_pos hb0 _) (pow_pos hb0 _)).mpr
  calc
    _ ≤ (b : ℝ)^(2*(H*(H+1))) * (b : ℝ)^H :=
      mul_le_mul_of_nonneg_right hcontrol (by positivity)
    _ = (b : ℝ)^(2*(H*(H+1))+H) := (pow_add _ _ _).symm
    _ ≤ (b : ℝ)^(H^3) := pow_le_pow_right₀ (by linarith) (cubic_dominates_control_count H hH)
    _ = _ := by ring

theorem exists_small_control_tail (b t : ℕ) (hb : 2 ≤ b) (C η : ℝ)
    (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ H : ℕ, t ≤ H ∧ 3 ≤ H ∧
      C / (b - 1 : ℝ) * ((b : ℝ)^H)⁻¹ +
      C / (b - 1 : ℝ) * (((b : ℝ)+1)^(H*(H+1)) / (b : ℝ)^(H^3)) < η := by
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hi : Tendsto (fun H : ℕ => ((b : ℝ)^H)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by linarith))
  have hl : Tendsto (fun H : ℕ => (2*C/(b-1 : ℝ)) * ((b : ℝ)^H)⁻¹)
      atTop (𝓝 0) := by simpa using hi.const_mul (2*C/(b-1 : ℝ))
  obtain ⟨H, hHt, hH3, hsmall⟩ :=
    ((eventually_ge_atTop t).and ((eventually_ge_atTop 3).and
      (hl.eventually (gt_mem_nhds hη)))).exists
  refine ⟨H, hHt, hH3, ?_⟩
  have hfar := far_tail_factor_le b H hb hH3
  have hc : 0 ≤ C/(b-1 : ℝ) := div_nonneg hC (by linarith)
  have hfar' := mul_le_mul_of_nonneg_left hfar hc
  rw [one_div] at hfar'
  have heq : 2*C/(b-1 : ℝ)*((b : ℝ)^H)⁻¹ =
      2*(C/(b-1 : ℝ)*((b : ℝ)^H)⁻¹) := by ring
  rw [heq] at hsmall
  nlinarith

end PowerLambert
