import PowerLambert.DynamicsPeriodicApprox
import PowerLambert.DynamicsFactor
import Mathlib.MeasureTheory.Measure.Real

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology Classical ENNReal symmDiff

namespace PowerLambert

def decodeLabel {k : ℕ} (d : Fin k) (v : Fin k → Bool) : Fin k :=
  if h : ∃ i, v i = true then Classical.choose h else d

theorem decodeLabel_eq {k : ℕ} (d : Fin k) (v : Fin k → Bool) (i : Fin k)
    (hi : v i = true) (hunique : ∀ j, v j = true → j = i) : decodeLabel d v = i := by
  have h : ∃ j, v j = true := ⟨i, hi⟩
  rw [decodeLabel, dif_pos h]
  exact hunique _ (Classical.choose_spec h)

/-- Every finite measurable labeling of the arithmetic Haar model can be
approximated in mismatch probability by a labeling with a finite period. -/
theorem exists_periodic_label_approximation (r k : ℕ) (hk : 0 < k)
    (X : OrbitGroup r → Fin k) (hX : Measurable X) (ε : ℝ) (hε : 0 < ε) :
    ∃ Y : OrbitGroup r → Fin k, Measurable Y ∧
      (∃ P : ℕ, 0 < P ∧ Function.Periodic Y (P • orbitGenerator r)) ∧
      (orbitHaar r).real {x | X x ≠ Y x} < ε := by
  let δ : ℝ := ε / ((k : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hfiber (i : Fin k) : MeasurableSet {x : OrbitGroup r | X x = i} :=
    hX (measurableSet_singleton i)
  have happ (i : Fin k) := exists_periodic_set_approximation r (hfiber i)
    (ENNReal.ofReal_pos.mpr hδ)
  choose t ht hperiod hclose using happ
  choose P hP hper using hperiod
  let Q : ℕ := ∏ i : Fin k, P i
  have hQ : 0 < Q := Finset.prod_pos (fun i _ => hP i)
  have hperQ (i : Fin k) : Function.Periodic (fun x => x ∈ t i) (Q • orbitGenerator r) := by
    obtain ⟨z, hz⟩ := Finset.dvd_prod_of_mem P (Finset.mem_univ i)
    have h := (hper i).nsmul z
    simpa only [smul_smul, Nat.mul_comm z (P i), ← hz] using h
  let code : OrbitGroup r → (Fin k → Bool) := fun x i => if x ∈ t i then true else false
  let Y : OrbitGroup r → Fin k := fun x => decodeLabel ⟨0, hk⟩ (code x)
  have hcode : Measurable code := by
    apply measurable_pi_lambda
    intro i
    exact Measurable.ite (ht i) measurable_const measurable_const
  have hY : Measurable Y := (measurable_of_finite (decodeLabel ⟨0, hk⟩)).comp hcode
  have hYper : Function.Periodic Y (Q • orbitGenerator r) := by
    intro x
    apply congrArg (decodeLabel ⟨0, hk⟩)
    funext i
    dsimp [code]
    have hmem : x + Q • orbitGenerator r ∈ t i ↔ x ∈ t i := Iff.of_eq (hperQ i x)
    by_cases hx : x ∈ t i
    · simp [hx, hmem.mpr hx]
    · have hx' : x + Q • orbitGenerator r ∉ t i := fun h => hx (hmem.mp h)
      simp [hx, hx']
  let U : Set (OrbitGroup r) := ⋃ i : Fin k, t i ∆ {x | X x = i}
  have hsub : {x | X x ≠ Y x} ⊆ U := by
    intro x hxy
    by_contra hxU
    have hmem : ∀ i : Fin k, x ∈ t i ↔ X x = i := by
      intro i
      have hh : x ∉ t i ∆ {x | X x = i} := fun h => hxU (Set.mem_iUnion.mpr ⟨i, h⟩)
      simp only [Set.mem_symmDiff, Set.mem_setOf_eq] at hh
      tauto
    have hdecode : Y x = X x := by
      apply decodeLabel_eq
      · simp only [code, if_pos ((hmem (X x)).mpr rfl)]
      · intro i hi
        by_cases hti : x ∈ t i
        · exact ((hmem i).mp hti).symm
        · simp [code, hti] at hi
    exact hxy hdecode.symm
  have hsum : (∑ i : Fin k, orbitHaar r (t i ∆ {x | X x = i})) ≤
      ENNReal.ofReal ((k : ℝ) * δ) := by
    calc
      _ ≤ ∑ _i : Fin k, ENNReal.ofReal δ := Finset.sum_le_sum (fun i _ => (hclose i).le)
      _ = (k : ℝ≥0∞) * ENNReal.ofReal δ := by simp
      _ = _ := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
  have hkδ : (k : ℝ) * δ < ε := by
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hcancel : δ * ((k : ℝ) + 1) = ε := by dsimp [δ]; exact div_mul_cancel₀ _ hkpos.ne'
    nlinarith
  have hmeasure : orbitHaar r {x | X x ≠ Y x} < ENNReal.ofReal ε := by
    calc
      _ ≤ orbitHaar r U := measure_mono hsub
      _ ≤ ∑ i : Fin k, orbitHaar r (t i ∆ {x | X x = i}) := measure_iUnion_fintype_le _ _
      _ ≤ ENNReal.ofReal ((k : ℝ) * δ) := hsum
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr hkδ
  refine ⟨Y, hY, ⟨Q, hQ, hYper⟩, ?_⟩
  have hreal := (ENNReal.toReal_lt_toReal (measure_ne_top (orbitHaar r) _)
    ENNReal.ofReal_ne_top).mpr hmeasure
  simpa only [Measure.real, ENNReal.toReal_ofReal hε.le] using hreal

theorem exists_periodic_label_approximation_iterate (r k : ℕ) (hk : 0 < k)
    (X : OrbitGroup r → Fin k) (hX : Measurable X) (ε : ℝ) (hε : 0 < ε) :
    ∃ Y : OrbitGroup r → Fin k, Measurable Y ∧
      ∃ P : ℕ, 0 < P ∧ (∀ x, Y ((modelRotation r)^[P] x) = Y x) ∧
        (orbitHaar r).real {x | X x ≠ Y x} < ε := by
  obtain ⟨Y, hY, ⟨P, hP, hper⟩, hclose⟩ :=
    exists_periodic_label_approximation r k hk X hX ε hε
  refine ⟨Y, hY, P, hP, ?_, hclose⟩
  intro x
  change Y (((fun z : OrbitGroup r => orbitGenerator r + z)^[P]) x) = Y x
  rw [add_left_iterate]
  simpa only [add_comm] using hper x

end PowerLambert
