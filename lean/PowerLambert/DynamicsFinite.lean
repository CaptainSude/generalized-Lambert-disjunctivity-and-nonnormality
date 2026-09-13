import PowerLambert.DynamicsModel
import PowerLambert.DynamicsPeriodic
import PowerLambert.SeriesTail

noncomputable section
open Set Filter MeasureTheory Topology
open scoped Classical BigOperators

namespace PowerLambert

theorem coordinate_cast_compatibility (r m k : ℕ)
    (hd : powerModulus r m ∣ powerModulus r k) (x : OrbitGroup r) :
    ZMod.castHom hd (ZMod (powerModulus r m)) (coordinate r k x) = coordinate r m x := by
  apply congrFun ((denseRange_integerPoint r).equalizer
    ((continuous_of_discreteTopology : Continuous (ZMod.castHom hd (ZMod (powerModulus r m)))).comp
      (continuous_coordinate r k)) (continuous_coordinate r m) ?_) x
  funext n
  simp only [Function.comp_def, coordinate_integerPoint, map_intCast]

theorem modelTerm_eq_larger_coordinate (b r m k : ℕ)
    (hd : powerModulus r m ∣ powerModulus r k) (x : OrbitGroup r) :
    modelTerm b r m x = residueTerm b (powerModulus r m) (coordinate r k x).val := by
  unfold modelTerm
  rw [← coordinate_cast_compatibility r m k hd x, ZMod.castHom_apply, ZMod.cast_eq_val,
    ZMod.val_natCast]
  simp only [residueTerm, Nat.mod_mod]

def modelTrunc (b r U : ℕ) (x : OrbitGroup r) : ℝ :=
  ∑ m ∈ Finset.range U, modelTerm b r m x

theorem continuous_modelTrunc (b r U : ℕ) : Continuous (modelTrunc b r U) := by
  exact continuous_finsetSum _ (fun m _ => continuous_modelTerm b r m)

theorem modelTrunc_integerPoint (b r U n : ℕ) :
    modelTrunc b r U (integerPoint r n) = orbitTrunc b r U n := by
  exact Finset.sum_congr rfl (fun m _ => modelTerm_integerPoint b r m n)

theorem factorial_coordinate_modulus (r U : ℕ) :
    powerModulus r (U.factorial - 1) = U.factorial ^ r := by
  simp only [powerModulus, Nat.sub_add_cancel (Nat.factorial_pos U)]

theorem modelTrunc_eq_factorial_coordinate (b r U : ℕ) (x : OrbitGroup r) :
    modelTrunc b r U x = orbitTrunc b r U (coordinate r (U.factorial - 1) x).val := by
  apply Finset.sum_congr rfl
  intro m hm
  have hd : powerModulus r m ∣ powerModulus r (U.factorial - 1) := by
    rw [factorial_coordinate_modulus]
    exact pow_dvd_pow_of_dvd (Nat.dvd_factorial (by omega) (by have := Finset.mem_range.mp hm; omega)) r
  exact modelTerm_eq_larger_coordinate b r m _ hd x

theorem integral_test_modelTrunc (b r U : ℕ) (g : ℝ → ℝ) :
    (∫ x, g (modelTrunc b r U x) ∂orbitHaar r) =
      sequenceMean (fun n => g (orbitTrunc b r U n)) (U.factorial ^ r) := by
  have heq : (fun x : OrbitGroup r => g (modelTrunc b r U x)) =
      fun x => g (orbitTrunc b r U (coordinate r (U.factorial - 1) x).val) := by
    funext x
    rw [modelTrunc_eq_factorial_coordinate]
  rw [heq, integral_coordinate r (U.factorial - 1)
    (fun a => g (orbitTrunc b r U a.val)),
    sum_zmod_val (powerModulus r (U.factorial - 1)) (fun n => g (orbitTrunc b r U n)),
    factorial_coordinate_modulus]
  simp only [sequenceMean, div_eq_mul_inv, mul_comm]

/-- Exact agreement of finite Haar averages and finite integer-period
averages, followed by convergence along every prefix length. -/
theorem sequenceMean_test_orbitTrunc_tendsto (b r U : ℕ) (g : ℝ → ℝ) :
    Tendsto (sequenceMean (fun n => g (orbitTrunc b r U n))) atTop
      (𝓝 (∫ x, g (modelTrunc b r U x) ∂orbitHaar r)) := by
  rw [integral_test_modelTrunc]
  apply sequenceMean_tendsto_of_periodic (by positivity : 0 < U.factorial ^ r)
  intro n
  change g (orbitTrunc b r U (n + U.factorial ^ r)) = g (orbitTrunc b r U n)
  rw [orbitTrunc_periodic b r U n]

end PowerLambert
