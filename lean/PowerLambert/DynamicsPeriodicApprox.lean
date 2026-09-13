import PowerLambert.DynamicsModel
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.Algebra.Ring.Periodic

noncomputable section
open Filter Set MeasureTheory MeasurableSpace
open scoped BigOperators Topology Classical ENNReal symmDiff

namespace PowerLambert

def periodicMeasurableSets {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (g : G) : Set (Set G) :=
  {s | MeasurableSet s ∧ ∃ P : ℕ, 0 < P ∧ Function.Periodic (fun x => x ∈ s) (P • g)}

theorem periodicMeasurableSets_isSetRing {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (g : G) : IsSetRing (periodicMeasurableSets g) where
  empty_mem := ⟨MeasurableSet.empty,1,by omega,fun _ => rfl⟩
  union_mem := by
    rintro s t ⟨hs,P,hP,hPs⟩ ⟨ht,Q,hQ,hQt⟩
    refine ⟨hs.union ht,P*Q,Nat.mul_pos hP hQ,fun x => ?_⟩
    have hs' := hPs.nsmul Q x
    have ht' := hQt.nsmul P x
    simp only [smul_smul, Nat.mul_comm Q P] at hs' ht'
    simp only [Set.mem_union,hs',ht']
  sdiff_mem := by
    rintro s t ⟨hs,P,hP,hPs⟩ ⟨ht,Q,hQ,hQt⟩
    refine ⟨hs.diff ht,P*Q,Nat.mul_pos hP hQ,fun x => ?_⟩
    have hs' := hPs.nsmul Q x
    have ht' := hQt.nsmul P x
    simp only [smul_smul, Nat.mul_comm Q P] at hs' ht'
    simp only [Set.mem_sdiff,hs',ht']

theorem univ_mem_periodicMeasurableSets {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (g : G) : univ ∈ periodicMeasurableSets g :=
  ⟨MeasurableSet.univ,1,by omega,fun _ => rfl⟩

theorem coordinate_preimage_mem_periodicMeasurableSets (r m : ℕ)
    (s : Set (ZMod (powerModulus r m))) :
    (coordinate r m) ⁻¹' s ∈ periodicMeasurableSets (orbitGenerator r) := by
  refine ⟨(continuous_coordinate r m).measurable (Set.toFinite s).measurableSet,
    powerModulus r m,Nat.pos_of_ne_zero (NeZero.ne _),fun x => ?_⟩
  simp only [Set.mem_preimage, map_add, map_nsmul]
  have hg : coordinate r m (orbitGenerator r) = 1 := rfl
  rw [hg]
  simp

/-- Finite-period measurable sets generate the full Borel sigma algebra
of the concrete arithmetic compact group. -/
theorem orbitGroup_measurable_eq_generate_periodic (r : ℕ) :
    (inferInstance : MeasurableSpace (OrbitGroup r)) =
      generateFrom (periodicMeasurableSets (orbitGenerator r)) := by
  apply le_antisymm
  · have hcoord : ∀ m : ℕ,
        @Measurable (OrbitGroup r) (ZMod (powerModulus r m))
          (generateFrom (periodicMeasurableSets (orbitGenerator r))) inferInstance
          (coordinate r m) := by
      intro m s hs
      exact measurableSet_generateFrom (coordinate_preimage_mem_periodicMeasurableSets r m s)
    have hval : @Measurable (OrbitGroup r) (ResidueSpace r)
        (generateFrom (periodicMeasurableSets (orbitGenerator r))) inferInstance Subtype.val := by
      letI : MeasurableSpace (OrbitGroup r) :=
        generateFrom (periodicMeasurableSets (orbitGenerator r))
      exact Measurable.of_eval hcoord
    change borel (OrbitGroup r) ≤ _
    rw [borel_comap, ← BorelSpace.measurable_eq (α := ResidueSpace r)]
    exact hval.comap_le
  · exact generateFrom_le (fun s hs => hs.1)

theorem exists_periodic_set_approximation (r : ℕ) {s : Set (OrbitGroup r)}
    (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t : Set (OrbitGroup r), MeasurableSet t ∧
      (∃ P : ℕ,0<P ∧ Function.Periodic (fun x => x ∈ t) (P • orbitGenerator r)) ∧
      orbitHaar r (t ∆ s) < ε := by
  obtain ⟨t,ht,hclose⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := orbitHaar r) (periodicMeasurableSets_isSetRing (orbitGenerator r))
    ⟨{univ},Set.countable_singleton _,by
      intro s hs
      simpa only [Set.mem_singleton_iff.mp hs] using univ_mem_periodicMeasurableSets (orbitGenerator r),
      by simp⟩
    (orbitGroup_measurable_eq_generate_periodic r) hs hε
  exact ⟨t,ht.1,ht.2,hclose⟩

end PowerLambert
