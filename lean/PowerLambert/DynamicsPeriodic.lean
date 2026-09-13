import PowerLambert.Dynamics
import PowerLambert.Progression
import Mathlib.Data.Nat.Periodic

noncomputable section
open Filter Set
open scoped BigOperators Topology Classical

namespace PowerLambert

theorem periodic_eq_sum_residue_indicators {u : ℕ → ℝ} {P : ℕ}
    (hP : 0 < P) (hu : Function.Periodic u P) (n : ℕ) :
    u n = ∑ a ∈ Finset.range P, if Nat.ModEq P n a then u a else 0 := by
  have heq : (∑ a ∈ Finset.range P, if Nat.ModEq P n a then u a else 0) =
      ∑ a ∈ Finset.range P, if a = n % P then u a else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : a < P := Finset.mem_range.mp ha
    simp only [Nat.ModEq, Nat.mod_eq_of_lt ha', eq_comm]
  rw [heq]
  simpa only [Finset.sum_ite_eq', Finset.mem_range, Nat.mod_lt n hP, ite_true]
    using (hu.map_mod_nat n).symm

theorem sequenceMean_periodic_eq {u : ℕ → ℝ} {P : ℕ}
    (hP : 0 < P) (hu : Function.Periodic u P) (N : ℕ) :
    sequenceMean u N = ∑ a ∈ Finset.range P,
      ((((Finset.range N).filter (fun n => Nat.ModEq P n a)).card : ℝ) / N) * u a := by
  unfold sequenceMean
  have hs : (∑ n ∈ Finset.range N, u n) =
      ∑ n ∈ Finset.range N, ∑ a ∈ Finset.range P,
        if Nat.ModEq P n a then u a else 0 :=
    Finset.sum_congr rfl (fun n _ => periodic_eq_sum_residue_indicators hP hu n)
  rw [hs, Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Every periodic sequence has its period mean as the limit of averages
over all prefixes; no divisibility restriction on prefix lengths is used. -/
theorem sequenceMean_tendsto_of_periodic {u : ℕ → ℝ} {P : ℕ}
    (hP : 0 < P) (hu : Function.Periodic u P) :
    Tendsto (sequenceMean u) atTop (𝓝 (sequenceMean u P)) := by
  have h := tendsto_finsetSum (Finset.range P) (fun a _ =>
    (residue_frequency P a hP).mul_const (u a))
  have heq : (∑ a ∈ Finset.range P, (1 / (P : ℝ)) * u a) = sequenceMean u P := by
    simp only [sequenceMean, Finset.sum_div, one_div]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [heq] at h
  exact h.congr (fun N => (sequenceMean_periodic_eq hP hu N).symm)

/-- Rationally almost periodic scalar sequences have limiting means. -/
theorem exists_sequenceMean_limit_of_periodic_approximation (u : ℕ → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, 0 < P ∧ ∃ v : ℕ → ℝ,
      Function.Periodic v P ∧
      ∀ᶠ N in atTop, sequenceMean (fun n => |u n - v n|) N < ε) :
    ∃ a : ℝ, Tendsto (sequenceMean u) atTop (𝓝 a) := by
  apply exists_sequenceMean_limit_of_approximation
  intro ε hε
  obtain ⟨P, hP, v, hv, he⟩ := h ε hε
  exact ⟨v, sequenceMean v P, sequenceMean_tendsto_of_periodic hP hv, he⟩

end PowerLambert
