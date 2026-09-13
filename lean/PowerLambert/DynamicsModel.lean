import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.DenseEmbedding
import Mathlib.Dynamics.Ergodic.Action.OfMinimal
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Data.ZMod.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import PowerLambert.Series
import Mathlib.Tactic

/-!
An explicit compact arithmetic model: the closure of the diagonal integer
orbit in the countable product of the finite groups ZMod ((m+1)^r).
-/

noncomputable section
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped Classical BigOperators ENNReal

namespace PowerLambert

def powerModulus (r m : ℕ) : ℕ := (m + 1) ^ r

instance powerModulus_neZero (r m : ℕ) : NeZero (powerModulus r m) :=
  ⟨pow_ne_zero r (by omega)⟩

abbrev ResidueSpace (r : ℕ) := (m : ℕ) → ZMod (powerModulus r m)

def cyclicClosure (r : ℕ) : AddSubgroup (ResidueSpace r) :=
  (AddSubgroup.zmultiples (1 : ResidueSpace r)).topologicalClosure

abbrev OrbitGroup (r : ℕ) := cyclicClosure r

instance orbitGroupSecondCountable (r : ℕ) : SecondCountableTopology (OrbitGroup r) := by
  exact IsInducing.subtypeVal.secondCountableTopology

instance orbitGroupCompact (r : ℕ) : CompactSpace (OrbitGroup r) :=
  isCompact_iff_compactSpace.mp
    (AddSubgroup.isClosed_topologicalClosure (AddSubgroup.zmultiples (1 : ResidueSpace r))).isCompact

instance orbitGroupMeasurable (r : ℕ) : MeasurableSpace (OrbitGroup r) := borel _

instance orbitGroupBorel (r : ℕ) : BorelSpace (OrbitGroup r) := ⟨rfl⟩

def orbitGenerator (r : ℕ) : OrbitGroup r :=
  ⟨1, (AddSubgroup.zmultiples (1 : ResidueSpace r)).le_topologicalClosure
    (AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩)⟩

def integerPoint (r : ℕ) (n : ℤ) : OrbitGroup r := n • orbitGenerator r

@[simp] theorem integerPoint_coe (r : ℕ) (n : ℤ) :
    (integerPoint r n : ResidueSpace r) = n • (1 : ResidueSpace r) := rfl

theorem denseRange_integerPoint (r : ℕ) : DenseRange (integerPoint r) := by
  rw [DenseRange, dense_iff_closure_eq]
  ext x
  simp only [mem_univ, iff_true]
  rw [closure_subtype]
  change (x : ResidueSpace r) ∈ closure (Subtype.val '' range (integerPoint r))
  have heq : Subtype.val '' range (integerPoint r) =
      (AddSubgroup.zmultiples (1 : ResidueSpace r) : Set (ResidueSpace r)) := by
    ext y
    constructor
    · rintro ⟨z, ⟨n, rfl⟩, rfl⟩
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩
    · intro hy
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
      exact ⟨integerPoint r n, ⟨n, rfl⟩, hn⟩
  rw [heq]
  exact x.property

def orbitHaar (r : ℕ) : Measure (OrbitGroup r) :=
  Measure.addHaarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts (OrbitGroup r))

instance orbitHaarProbability (r : ℕ) : IsProbabilityMeasure (orbitHaar r) :=
  ⟨Measure.addHaarMeasure_self⟩

instance orbitHaarIsHaar (r : ℕ) : (orbitHaar r).IsAddHaarMeasure := by
  unfold orbitHaar
  infer_instance

theorem orbitRotation_ergodic (r : ℕ) :
    Ergodic (fun x : OrbitGroup r => orbitGenerator r + x) (orbitHaar r) := by
  apply ergodic_add_left_of_denseRange_zsmul (denseRange_integerPoint r)

instance residueMeasurable (r m : ℕ) : MeasurableSpace (ZMod (powerModulus r m)) := borel _

instance residueBorel (r m : ℕ) : BorelSpace (ZMod (powerModulus r m)) := ⟨rfl⟩

def coordinate (r m : ℕ) : OrbitGroup r →+ ZMod (powerModulus r m) where
  toFun x := x.val m
  map_zero' := rfl
  map_add' _ _ := rfl

theorem continuous_coordinate (r m : ℕ) : Continuous (coordinate r m) :=
  (continuous_apply m).comp continuous_subtype_val

theorem coordinate_surjective (r m : ℕ) : Function.Surjective (coordinate r m) := by
  intro a
  refine ⟨a.val • orbitGenerator r, ?_⟩
  change a.val • (1 : ZMod (powerModulus r m)) = a
  simp

/-- A probability measure invariant under all translations on a finite
group is uniform. -/
theorem finite_invariant_probability_eq_uniform
    {H : Type*} [AddGroup H] [Fintype H] [MeasurableSpace H]
    [MeasurableSingletonClass H] [MeasurableAdd H]
    (μ : Measure H) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant] :
    μ = (PMF.uniformOfFintype H).toMeasure := by
  have heq (a : H) : μ {a} = μ {0} := by
    have h := measure_preimage_add μ a ({a} : Set H)
    have hs : (fun y : H => a + y) ⁻¹' ({a} : Set H) = {0} := by
      ext y
      simp
    rw [hs] at h
    exact h.symm
  have hprod : (Fintype.card H : ℝ≥0∞) * μ {0} = 1 := by
    calc
      _ = ∑ a : H, μ {0} := by simp [nsmul_eq_mul]
      _ = ∑ a : H, μ {a} := Finset.sum_congr rfl (fun a _ => (heq a).symm)
      _ = 1 := by simp
  have hzero : μ {0} = (Fintype.card H : ℝ≥0∞)⁻¹ := by
    calc
      μ {0} = (Fintype.card H : ℝ≥0∞)⁻¹ * ((Fintype.card H : ℝ≥0∞) * μ {0}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
      _ = _ := by rw [hprod, mul_one]
  apply Measure.ext_of_singleton
  intro a
  rw [heq a, hzero, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp

/-- Every coordinate of the arithmetic compact group is uniformly
distributed under its normalized Haar measure. -/
theorem coordinate_map_orbitHaar (r m : ℕ) :
    Measure.map (coordinate r m) (orbitHaar r) =
      (PMF.uniformOfFintype (ZMod (powerModulus r m))).toMeasure := by
  let : IsProbabilityMeasure (Measure.map (coordinate r m) (orbitHaar r)) :=
    ⟨by rw [Measure.map_apply (continuous_coordinate r m).measurable MeasurableSet.univ]; simp⟩
  let : (Measure.map (coordinate r m) (orbitHaar r)).IsAddLeftInvariant :=
    isAddLeftInvariant_map (coordinate r m).toAddHom (continuous_coordinate r m).measurable
      (coordinate_surjective r m)
  exact finite_invariant_probability_eq_uniform _

theorem coordinate_measurePreserving (r m : ℕ) :
    MeasurePreserving (coordinate r m) (orbitHaar r)
      (PMF.uniformOfFintype (ZMod (powerModulus r m))).toMeasure :=
  ⟨(continuous_coordinate r m).measurable, coordinate_map_orbitHaar r m⟩

theorem integral_coordinate (r m : ℕ) (g : ZMod (powerModulus r m) → ℝ) :
    (∫ x, g (coordinate r m x) ∂orbitHaar r) =
      (powerModulus r m : ℝ)⁻¹ * ∑ a : ZMod (powerModulus r m), g a := by
  rw [← integral_map (continuous_coordinate r m).measurable.aemeasurable
      (measurable_of_finite g).aestronglyMeasurable,
    coordinate_map_orbitHaar, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ZMod.card, smul_eq_mul, Finset.mul_sum]

theorem sum_zmod_val (d : ℕ) [NeZero d] (f : ℕ → ℝ) :
    (∑ a : ZMod d, f a.val) = ∑ n ∈ Finset.range d, f n := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ d => exact Fin.sum_univ_eq_sum_range f (d + 1)

def modelTerm (b r m : ℕ) (x : OrbitGroup r) : ℝ :=
  residueTerm b (powerModulus r m) (coordinate r m x).val

theorem continuous_modelTerm (b r m : ℕ) : Continuous (modelTerm b r m) :=
  (continuous_of_discreteTopology : Continuous (fun a : ZMod (powerModulus r m) =>
    residueTerm b (powerModulus r m) a.val)).comp (continuous_coordinate r m)

theorem modelTerm_nonneg {b r m : ℕ} (hb : 2 ≤ b) (x : OrbitGroup r) :
    0 ≤ modelTerm b r m x := residueTerm_nonneg hb (Nat.pos_of_ne_zero (NeZero.ne _))

theorem integral_modelTerm {b : ℕ} (hb : 2 ≤ b) (r m : ℕ) :
    (∫ x, modelTerm b r m x ∂orbitHaar r) =
      (powerModulus r m : ℝ)⁻¹ * (b - 1 : ℝ)⁻¹ := by
  change (∫ x, residueTerm b (powerModulus r m) (coordinate r m x).val ∂orbitHaar r) = _
  rw [integral_coordinate r m (fun a => residueTerm b (powerModulus r m) a.val), sum_zmod_val,
    sum_residueTerm_period hb (Nat.pos_of_ne_zero (NeZero.ne _))]

@[simp] theorem coordinate_integerPoint (r m : ℕ) (n : ℤ) :
    coordinate r m (integerPoint r n) = (n : ZMod (powerModulus r m)) := by
  change n • (1 : ZMod (powerModulus r m)) = _
  simp

theorem modelTerm_integerPoint (b r m n : ℕ) :
    modelTerm b r m (integerPoint r n) = residueTerm b ((m + 1) ^ r) n := by
  unfold modelTerm
  have hn : coordinate r m (integerPoint r (n : ℤ)) = (n : ZMod (powerModulus r m)) := by
    exact (coordinate_integerPoint r m (n : ℤ)).trans (Int.cast_natCast n)
  rw [hn, ZMod.val_natCast]
  simp only [residueTerm, Nat.mod_mod, powerModulus]

end PowerLambert
