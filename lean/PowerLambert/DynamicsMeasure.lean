import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-!
The atomlessness consequence of ergodicity and positive mass outside every
finite set. The finite-set condition follows from full support on an infinite
T1 space. No conclusion about a specific Lambert measure is assumed here.
-/

noncomputable section
open MeasureTheory Set Function
open scoped BigOperators Topology Classical

namespace PowerLambert

/-- In a finite invariant measure, every positive-mass singleton is periodic. -/
theorem periodic_of_singleton_measure_ne_zero
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure X} [IsFiniteMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {x : X} (hx : μ {x} ≠ 0) :
    ∃ P : ℕ, 0 < P ∧ IsPeriodicPt T P x := by
  obtain ⟨y, hy, P, hP, hret⟩ :=
    hT.exists_mem_iterate_mem (measurableSet_singleton x).nullMeasurableSet hx
  have hyx : y = x := hy
  subst y
  exact ⟨P, Nat.pos_of_ne_zero hP, hret⟩

/-- An ergodic finite measure whose complement of every finite set has
positive mass has no atoms. -/
theorem nullSingletonClass_of_ergodic_of_finite_compl_ne_zero
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure X} [IsFiniteMeasure μ] {T : X → X}
    (hT : Ergodic T μ)
    (hfinite : ∀ s : Set X, s.Finite → μ sᶜ ≠ 0) :
    NullSingletonClass μ := by
  constructor
  intro x
  by_contra hx
  obtain ⟨P, hP, hperiod⟩ := periodic_of_singleton_measure_ne_zero hT.toMeasurePreserving hx
  let C : Set X := (fun k : ℕ => T^[k] x) '' (Finset.range P : Set ℕ)
  have hCfin : C.Finite := (Finset.finite_toSet _).image _
  have hxC : x ∈ C := by
    exact ⟨0, by simpa using hP, rfl⟩
  have hstable : T '' C ⊆ C := by
    rintro _ ⟨y, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨(k + 1) % P, ?_, ?_⟩
    · exact Finset.mem_range.mpr (Nat.mod_lt _ hP)
    · simpa only [iterate_succ_apply'] using hperiod.iterate_mod_apply (k + 1)
  rcases hT.ae_empty_or_univ_of_image_ae_le hCfin.measurableSet.nullMeasurableSet
      hstable.eventuallySubset with hzero | hone
  · apply hx
    apply measure_mono_null (singleton_subset_iff.mpr hxC)
    simpa only [measure_empty] using measure_congr hzero
  · apply hfinite C hCfin
    simpa only [compl_univ, measure_empty] using measure_congr (Filter.EventuallyEqSet.compl hone)

/-- An ergodic finite measure with full support on an infinite T1 space
is atomless. This is the precise general step used for the limiting law. -/
theorem nullSingletonClass_of_ergodic_of_full_support
    {X : Type*} [TopologicalSpace X] [T1Space X] [Infinite X]
    [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] {T : X → X}
    (hT : Ergodic T μ) : NullSingletonClass μ := by
  apply nullSingletonClass_of_ergodic_of_finite_compl_ne_zero hT
  intro s hs
  exact hs.isClosed.isOpen_compl.measure_ne_zero μ hs.infinite_compl.nonempty

/-- Ergodicity passes through a measurable factor whose commuting
identity holds almost everywhere. -/
theorem ergodic_map_of_ae_semiconj
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {T : X → X} {S : Y → Y} {φ : X → Y}
    (hT : Ergodic T μ) (hφ : Measurable φ) (hS : Measurable S)
    (hcomm : ∀ᵐ x ∂μ, φ (T x) = S (φ x)) :
    Ergodic S (Measure.map φ μ) := by
  have hφmp : MeasurePreserving φ μ (Measure.map φ μ) := ⟨hφ, rfl⟩
  refine ⟨⟨hS, ?_⟩, ⟨fun s hs hInv => ?_⟩⟩
  · rw [Measure.map_map hS hφ]
    have hmaps : S ∘ φ =ᵐ[μ] φ ∘ T := by
      filter_upwards [hcomm] with x hx
      exact hx.symm
    calc
      Measure.map (S ∘ φ) μ = Measure.map (φ ∘ T) μ := Measure.map_congr hmaps
      _ = Measure.map φ (Measure.map T μ) := (Measure.map_map hφ hT.measurable).symm
      _ = Measure.map φ μ := by rw [hT.map_eq]
  · rw [← hφmp.aeconst_preimage hs.nullMeasurableSet]
    apply hT.quasiErgodic.aeconst_set₀ (hφ hs).nullMeasurableSet
    filter_upwards [hcomm] with x hx
    change (φ (T x) ∈ s) = (φ x ∈ s)
    rw [hx]
    exact congrArg (fun a : Set Y => φ x ∈ a) hInv

end PowerLambert
