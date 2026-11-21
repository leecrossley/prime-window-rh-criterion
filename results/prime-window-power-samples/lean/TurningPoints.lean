import MarginCurvature

open Finset
namespace RiemannReduction.PrimeGrid

/-- The minimum of the margin on a finite interval is attained at an endpoint or a doubled prime. -/
theorem block_margin_lower_iff {a b : ℕ} (hab : a ≤ b) (L : ℝ) :
    (∀ j ∈ Icc a b, L ≤ margin j) ↔ L ≤ margin a ∧ L ≤ margin b ∧
      ∀ p : ℕ, p.Prime → a < 2*p → 2*p < b → L ≤ margin (2*p : ℕ) := by
  classical
  constructor
  · intro all
    exact ⟨all a (mem_Icc.mpr ⟨le_rfl, hab⟩), all b (mem_Icc.mpr ⟨hab, le_rfl⟩),
      fun p _ lo hi => all (2*p) (mem_Icc.mpr ⟨lo.le, hi.le⟩)⟩
  · rintro ⟨ha,hb,check⟩ j hj
    let block : Finset ℕ := Icc a b
    obtain ⟨i,hi,minimum⟩ := block.exists_min_image (fun k : ℕ => margin k) ⟨j,hj⟩
    let minimizers : Finset ℕ := block.filter (fun k : ℕ => margin k = margin i)
    have existsMin : minimizers.Nonempty := ⟨i, mem_filter.mpr ⟨hi,rfl⟩⟩
    let n := minimizers.min' existsMin
    have nmem : n ∈ minimizers := min'_mem _ _
    obtain ⟨nb,value⟩ := mem_filter.mp nmem
    obtain ⟨lo,hi⟩ := mem_Icc.mp nb
    have least (k : ℕ) (hk : k ∈ block) : margin n ≤ margin k := value.trans_le (minimum k hk)
    suffices good : L ≤ margin n from good.trans (least j hj)
    by_cases leftEnd : n = a
    · rw [leftEnd]
      exact ha
    by_cases rightEnd : n = b
    · rw [rightEnd]
      exact hb
    by_cases double : ∃ p : ℕ, p.Prime ∧ n = 2*p
    · obtain ⟨p,hp,eq⟩ := double
      rw [eq]
      exact check p hp (by omega) (by omega)
    have prev : n-1 ∈ block := mem_Icc.mpr ⟨by omega, by omega⟩
    have next : n+1 ∈ block := mem_Icc.mpr ⟨by omega, by omega⟩
    have strict : margin n < margin (n-1 : ℕ) := by
      apply lt_of_le_of_ne (least _ prev)
      intro eq
      have also : n-1 ∈ minimizers := mem_filter.mpr ⟨prev, eq.symm.trans value⟩
      have earlier : n ≤ n-1 := min'_le _ _ also
      omega
    have concave := margin_concave_at_non_double (n := n) (by omega)
      (fun p hp eq => double ⟨p,hp,eq⟩)
    linarith [least _ next]

/-- On a finite interval, it suffices to test the two endpoints and interior doubled primes. -/
theorem block_passes_iff_endpoints_and_double_primes {a b : ℕ} (hab : a ≤ b) :
    (∀ j ∈ Icc a b, Passes j) ↔
    Passes a ∧ Passes b ∧ ∀ p : ℕ, p.Prime → a < 2*p → 2*p < b → Passes (2*p) := by
  simpa only [passes_iff_margin] using block_margin_lower_iff hab 0

#print axioms block_passes_iff_endpoints_and_double_primes
end RiemannReduction.PrimeGrid
