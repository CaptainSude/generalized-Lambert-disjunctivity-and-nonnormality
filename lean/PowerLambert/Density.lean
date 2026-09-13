import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

noncomputable section
open Filter Set
open scoped BigOperators Topology Classical

namespace PowerLambert

def prefixDensity (P : ℕ → Prop) (N : ℕ) : ℝ :=
  ((Finset.range N).filter P).card / (N : ℝ)

/-- Finite Markov bound, without any independence assumption. -/
theorem card_large_mul_le_sum (s : Finset ℕ) (R : ℕ → ℝ) (η : ℝ)
    (hR : ∀ n ∈ s, 0 ≤ R n) :
    (((s.filter (fun n => η ≤ R n)).card : ℝ) * η) ≤ ∑ n ∈ s, R n := by
  calc
    _ = ∑ _n ∈ s.filter (fun n => η ≤ R n), η := by simp
    _ ≤ ∑ n ∈ s.filter (fun n => η ≤ R n), R n := by
      apply Finset.sum_le_sum
      intro n hn
      exact (Finset.mem_filter.mp hn).2
    _ ≤ ∑ n ∈ s, R n := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
        intro n hn _
        exact hR n hn)

/-- Removing an exceptional set loses at most its cardinality. -/
theorem card_filter_inter_lower (s : Finset ℕ) (P Q : ℕ → Prop) :
    (s.filter P).card ≤ (s.filter (fun n => P n ∧ ¬ Q n)).card +
      (s.filter Q).card := by
  calc
    _ ≤ ((s.filter (fun n => P n ∧ ¬ Q n)) ∪ s.filter Q).card := by
      apply Finset.card_le_card
      intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hns, hnP⟩
      by_cases hnQ : Q n
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hns, hnQ⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hns, hnP, hnQ⟩)
    _ ≤ _ := Finset.card_union_le _ _

/-- The arithmetic sieve and mean carry bound can be combined without independence. -/
theorem sieve_carry_card_lower (s : Finset ℕ) (P : ℕ → Prop)
    (R : ℕ → ℝ) (η α β : ℝ) (hη : 0 < η)
    (hR : ∀ n ∈ s, 0 ≤ R n)
    (hP : α * s.card ≤ ((s.filter P).card : ℝ))
    (hmean : (∑ n ∈ s, R n) ≤ β * s.card * η) :
    (α - β) * s.card ≤
      ((s.filter (fun n => P n ∧ R n < η)).card : ℝ) := by
  have hbad := card_large_mul_le_sum s R η hR
  have hbad' : ((s.filter (fun n => η ≤ R n)).card : ℝ) ≤ β * s.card := by
    nlinarith
  have hsplit := card_filter_inter_lower s P (fun n => η ≤ R n)
  simp only [not_le] at hsplit
  have hsplit' : ((s.filter P).card : ℝ) ≤
      ((s.filter (fun n => P n ∧ R n < η)).card : ℝ) +
      ((s.filter (fun n => η ≤ R n)).card : ℝ) := by exact_mod_cast hsplit
  nlinarith

/-- A finite union bound in the form used for the power-free sieve. -/
theorem card_filter_le_sum_bad (s t : Finset ℕ) (P : ℕ → Prop)
    (bad : ℕ → ℕ → Prop)
    (hcover : ∀ n ∈ s, ¬ P n → ∃ p ∈ t, bad p n) :
    (s.filter (fun n => ¬ P n)).card ≤
      ∑ p ∈ t, (s.filter (bad p)).card := by
  calc
    _ ≤ (t.biUnion (fun p => s.filter (bad p))).card := by
      apply Finset.card_le_card
      intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hns, hnP⟩
      obtain ⟨p, hpt, hpn⟩ := hcover n hns hnP
      exact Finset.mem_biUnion.mpr ⟨p, hpt, Finset.mem_filter.mpr ⟨hns, hpn⟩⟩
    _ ≤ _ := Finset.card_biUnion_le

/-- The total one-point error is exactly the number of possible obstructions. -/
theorem sieve_card_lower (s t : Finset ℕ) (P : ℕ → Prop)
    (bad : ℕ → ℕ → Prop) (weight : ℕ → ℝ) (c : ℝ)
    (hcover : ∀ n ∈ s, ¬ P n → ∃ p ∈ t, bad p n)
    (hcount : ∀ p ∈ t, ((s.filter (bad p)).card : ℝ) ≤ s.card * weight p + 1)
    (hweight : (∑ p ∈ t, weight p) ≤ c) :
    (1 - c) * s.card - t.card ≤ ((s.filter P).card : ℝ) := by
  have hu := card_filter_le_sum_bad s t P bad hcover
  have hu' : ((s.filter (fun n => ¬ P n)).card : ℝ) ≤
      ∑ p ∈ t, ((s.filter (bad p)).card : ℝ) := by exact_mod_cast hu
  have hs : (∑ p ∈ t, ((s.filter (bad p)).card : ℝ)) ≤ s.card * c + t.card := by
    calc
      _ ≤ ∑ p ∈ t, ((s.card : ℝ) * weight p + 1) :=
        Finset.sum_le_sum fun p hp => hcount p hp
      _ = s.card * (∑ p ∈ t, weight p) + t.card := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
      _ ≤ _ := by gcongr
  have he := Finset.card_filter_add_card_filter_not (s := s) P
  have he' : ((s.filter P).card : ℝ) + ((s.filter (fun n => ¬ P n)).card : ℝ) = s.card := by
    exact_mod_cast he
  nlinarith

/-- A sublinear number of obstruction errors gives the claimed lower density. -/
theorem eventually_density_lower_of_count_bound
    (P : ℕ → Prop) (error : ℕ → ℝ) (c δ : ℝ)
    (hbound : ∀ N, c * N - error N ≤ ((Finset.range N).filter P).card)
    (herr : Tendsto (fun N : ℕ => error N / N) atTop (𝓝 0))
    (hδ : δ < c) :
    ∀ᶠ N in atTop, δ < prefixDensity P N := by
  have he := herr.eventually (gt_mem_nhds (sub_pos.mpr hδ))
  filter_upwards [he, eventually_ge_atTop 1] with N hN hpos
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc := (div_le_div_of_nonneg_right (hbound N) hNr.le)
  have hid : (c * N - error N) / (N : ℝ) = c - error N / N := by
    field_simp
  rw [hid] at hc
  unfold prefixDensity
  linarith

end PowerLambert
