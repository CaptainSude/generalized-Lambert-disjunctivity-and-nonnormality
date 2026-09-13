import PowerLambert.Disjunctivity
import PowerLambert.SeriesNonNormal
import PowerLambert.DynamicsWeak
import PowerLambert.DynamicsSupport

noncomputable section
open Filter Set MeasureTheory
open scoped Topology

namespace PowerLambert

instance unitAddCircle_infinite : Infinite UnitAddCircle := by
  have : Infinite (Set.Ico (0 : ℝ) (0+1)) :=
    (Set.Ico_infinite (by norm_num : (0 : ℝ)<0+1)).to_subtype
  exact Infinite.of_injective (AddCircle.equivIco (1 : ℝ) 0).symm
    (AddCircle.equivIco (1 : ℝ) 0).symm.injective

theorem limitingLaw_fullSupport {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    (limitingLaw b r : Measure UnitAddCircle).IsOpenPosMeasure :=
  isOpenPosMeasure_of_guarded_word_visits hb (lambert b r) (limitingLaw b r)
    (lambert_empirical_tendsto hb hr) (lambert_positiveLowerDensity_guardedWord hb hr)

theorem limitingLaw_atomless {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    NullSingletonClass (limitingLaw b r : Measure UnitAddCircle) := by
  letI := limitingLaw_fullSupport hb hr
  exact nullSingletonClass_of_ergodic_of_full_support (limitingLaw_ergodic hb hr)

/-- Every finite word has a strictly positive limiting frequency, counted
at all overlapping starting positions, for the actual Lambert constant. -/
theorem lambert_positiveWordFrequencies {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    PositiveWordFrequencies b (lambert b r) := by
  letI := limitingLaw_fullSupport hb hr
  letI := limitingLaw_atomless hb hr
  exact positiveWordFrequencies_of_weak_convergence hb (lambert b r) (limitingLaw b r)
    (lambert_empirical_tendsto hb hr)

theorem lambert_digit_properties {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    PositiveWordFrequencies b (lambert b r) ∧
    DisjunctiveInBase b (lambert b r) ∧
    Irrational (lambert b r) ∧ ¬ NormalInBase b (lambert b r) :=
  ⟨lambert_positiveWordFrequencies hb hr,lambert_disjunctive hb hr,
    lambert_irrational hb hr,lambert_not_normal hb hr⟩

end PowerLambert
