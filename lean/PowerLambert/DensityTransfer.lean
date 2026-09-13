import PowerLambert.Density
import PowerLambert.PowerFreeSieve

noncomputable section
open Filter Set
open scoped BigOperators Topology Classical
set_option backward.isDefEq.respectTransparency false

namespace PowerLambert

def HasPositiveLowerDensity (P : ℕ → Prop) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N in atTop, δ ≤ prefixDensity P N

theorem HasPositiveLowerDensity.mono {P Q : ℕ → Prop}
    (h : HasPositiveLowerDensity P) (hPQ : ∀ n, P n → Q n) :
    HasPositiveLowerDensity Q := by
  obtain ⟨δ,hδ,hN⟩ := h
  refine ⟨δ,hδ,hN.mono fun N hn => hn.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast Finset.card_le_card (show (Finset.range N).filter P ⊆
      (Finset.range N).filter Q from fun n hn => by
    obtain ⟨hn,hp⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hn,hPQ n hp⟩)

/-- A positive density along any fixed positive progression gives a
positive density among all integer starting positions. -/
theorem HasPositiveLowerDensity.of_progression {P : ℕ → Prop} (a Q : ℕ)
    (hQ : 0 < Q) (h : HasPositiveLowerDensity (fun m => P (a+Q*m))) :
    HasPositiveLowerDensity P := by
  obtain ⟨δ,hδ,hN⟩ := h
  have hqR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlim : Tendsto (fun N : ℕ => N / (2*Q)) atTop atTop :=
    Nat.tendsto_div_const_atTop (by positivity)
  refine ⟨δ/(4*Q), by positivity, ?_⟩
  filter_upwards [hlim.eventually hN, eventually_ge_atTop (4*Q),
      eventually_ge_atTop (2*a+1)] with N hgood hlarge hoffset
  let M := N/(2*Q)
  have hM : 0 < M := Nat.div_pos (by omega) (by positivity)
  have hMle : M*(2*Q) ≤ N := Nat.div_mul_le_self N (2*Q)
  have hMlt : N < (M+1)*(2*Q) := by
    simpa [M, Nat.mul_comm] using Nat.lt_mul_div_succ N (by positivity : 0 < 2*Q)
  have hfour : N ≤ 4*Q*M := by nlinarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hsub : (((Finset.range M).filter (fun m => P (a+Q*m))).image
      (fun m => a+Q*m)) ⊆ (Finset.range N).filter P := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hm,hp⟩ := Finset.mem_filter.mp hm
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hp⟩
    have hm' := Finset.mem_range.mp hm
    nlinarith
  have hinj : Function.Injective (fun m : ℕ => a+Q*m) := by
    intro m n hmn
    exact Nat.eq_of_mul_eq_mul_left hQ (Nat.add_left_cancel hmn)
  have hc : (((Finset.range M).filter (fun m => P (a+Q*m))).card : ℝ) ≤
      ((Finset.range N).filter P).card := by
    exact_mod_cast (Finset.card_image_of_injective _ hinj ▸ Finset.card_le_card hsub)
  have hg : δ*(M : ℝ) ≤ ((Finset.range M).filter (fun m => P (a+Q*m))).card :=
    (le_div_iff₀ hMR).mp hgood
  have hfourR : (N : ℝ) ≤ 4*(Q : ℝ)*(M : ℝ) := by exact_mod_cast hfour
  apply (le_div_iff₀ hNpos).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<4*Q)).mpr
  nlinarith

/-- The power-free sieve and the complete nonnegative carry tail intersect
in positive density. No probabilistic independence is assumed. -/
theorem positiveLowerDensity_powerFree_small_tail
    (r u v : ℕ) (hr : 2 ≤ r) (hu : 0 < u) (hv : 0 < v) (huv : u.Coprime v)
    (R : ℕ → ℝ) (η L : ℝ) (hη : 0 < η) (hR : ∀ n, 0 ≤ R n)
    (hmean : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, R n)/(N : ℝ))
      atTop (𝓝 L)) (hL : L < η/16) :
    HasPositiveLowerDensity (fun n => PowerFree r (u+v*n) ∧ R n < η) := by
  have hf := powerFree_progression_positive_density r u v hr hu hv huv (1/5) (by norm_num)
  have ht := hmean.eventually (gt_mem_nhds (show L < η/8 by linarith))
  refine ⟨3/40, by norm_num, ?_⟩
  filter_upwards [hf,ht,eventually_ge_atTop 1] with N hfree htail hpos
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfree' : (1/5:ℝ)*N ≤
      ((Finset.range N).filter (fun n => PowerFree r (u+v*n))).card :=
    ((lt_div_iff₀ hN).mp hfree).le
  have htail' : (∑ n ∈ Finset.range N, R n) ≤ (1/8:ℝ)*N*η := by
    have := (div_lt_iff₀ hN).mp htail
    linarith
  have hc := sieve_carry_card_lower (Finset.range N)
    (fun n => PowerFree r (u+v*n)) R η (1/5) (1/8) hη
    (fun n _ => hR n) (by simpa using hfree') (by simpa using htail')
  apply (le_div_iff₀ hN).mpr
  norm_num only [Finset.card_range] at hc
  convert hc using 1
  · rfl
  · congr 2
    ext n
    simp

end PowerLambert
