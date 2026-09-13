import PowerLambert.DynamicsObservable
import PowerLambert.DynamicsMeasure
import PowerLambert.SeriesOrbit
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

noncomputable section
open Set Filter MeasureTheory Topology
open scoped Classical BigOperators

namespace PowerLambert

def modelRotation (r : ℕ) (x : OrbitGroup r) : OrbitGroup r := orbitGenerator r + x

def modelCircle (b r : ℕ) (x : OrbitGroup r) : UnitAddCircle :=
  ((modelObservable b r x : ℝ) : UnitAddCircle)

theorem measurable_modelCircle (b r : ℕ) : Measurable (modelCircle b r) :=
  AddCircle.measurable_mk'.comp (measurable_modelObservable b r)

theorem modelTerm_rotation (b r m : ℕ) (x : OrbitGroup r) :
    modelTerm b r m (modelRotation r x) =
      residueTerm b (powerModulus r m) ((coordinate r m x).val + 1) := by
  have hc : coordinate r m (modelRotation r x) =
      (((coordinate r m x).val + 1 : ℕ) : ZMod (powerModulus r m)) := by
    change 1 + coordinate r m x = _
    simp [Nat.cast_add, add_comm]
  unfold modelTerm
  rw [hc, ZMod.val_natCast]
  simp only [residueTerm, Nat.mod_mod]

theorem modelTerm_circle_factor {b : ℕ} (hb : 2 ≤ b) (r m : ℕ) (x : OrbitGroup r) :
    (((b : ℝ) * modelTerm b r m x : ℝ) : UnitAddCircle) =
      ((modelTerm b r m (modelRotation r x) : ℝ) : UnitAddCircle) := by
  rw [modelTerm_rotation]
  unfold modelTerm
  rw [residueTerm_step hb (Nat.pos_of_ne_zero (NeZero.ne (powerModulus r m)))]
  split_ifs <;> simp

theorem circle_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : UnitAddCircle) = ∑ i ∈ s, ((f i : ℝ) : UnitAddCircle) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert, ha, AddCircle.coe_add, ih]

theorem modelCircle_factor_of_summable {b r : ℕ} (hb : 2 ≤ b) (x : OrbitGroup r)
    (hx : Summable (fun m : ℕ => modelTerm b r m x))
    (hy : Summable (fun m : ℕ => modelTerm b r m (modelRotation r x))) :
    modelCircle b r (modelRotation r x) = b • modelCircle b r x := by
  have hfinite (U : ℕ) :
      (((b : ℝ) * ∑ m ∈ Finset.range U, modelTerm b r m x : ℝ) : UnitAddCircle) =
        ((∑ m ∈ Finset.range U, modelTerm b r m (modelRotation r x) : ℝ) : UnitAddCircle) := by
    simp only [Finset.mul_sum, circle_coe_sum]
    exact Finset.sum_congr rfl (fun m _ => modelTerm_circle_factor hb r m x)
  have hleft := (AddCircle.continuous_mk' (1 : ℝ)).continuousAt.tendsto.comp
    (hx.hasSum.tendsto_sum_nat.const_mul (b : ℝ))
  have hright := (AddCircle.continuous_mk' (1 : ℝ)).continuousAt.tendsto.comp hy.hasSum.tendsto_sum_nat
  have heq := tendsto_nhds_unique (hleft.congr hfinite) hright
  change (((b : ℝ) * modelObservable b r x : ℝ) : UnitAddCircle) =
    modelCircle b r (modelRotation r x) at heq
  rw [← heq]
  change (((b : ℝ) * modelObservable b r x : ℝ) : UnitAddCircle) =
    b • ((modelObservable b r x : ℝ) : UnitAddCircle)
  simp [← nsmul_eq_mul]

theorem modelCircle_factor_ae {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    ∀ᵐ x ∂orbitHaar r, modelCircle b r (modelRotation r x) = b • modelCircle b r x := by
  have hrot : MeasurePreserving (modelRotation r) (orbitHaar r) (orbitHaar r) :=
    (orbitRotation_ergodic r).toMeasurePreserving
  filter_upwards [ae_summable_modelTerm hb hr, hrot.quasiMeasurePreserving.ae
    (ae_summable_modelTerm hb hr)] with x hx hy
  exact modelCircle_factor_of_summable hb x hx hy

def limitingLaw (b r : ℕ) : ProbabilityMeasure UnitAddCircle :=
  ProbabilityMeasure.map (⟨orbitHaar r, orbitHaarProbability r⟩ : ProbabilityMeasure (OrbitGroup r))
    (modelCircle b r)

theorem limitingLaw_ergodic {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    Ergodic (fun x : UnitAddCircle => b • x) (limitingLaw b r : Measure UnitAddCircle) := by
  apply ergodic_map_of_ae_semiconj (orbitRotation_ergodic r)
    (measurable_modelCircle b r) (by fun_prop)
  exact modelCircle_factor_ae hb hr

end PowerLambert
