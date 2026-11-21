import FifthWindows
import FifthSpectrum

open Lean Elab Command in
run_cmd do
  for name in [`riemannHypothesis, `UpperTheory.FinalTheorems.riemannHypothesis,
      `rhOfAll, `allChi, `UpperTheory.FinalTheorems.everyCharacter] do
    if (← getEnv).contains name then throwError "Unexpected imported declaration {name}"

open Finset
namespace RiemannReduction.PrimeGrid

/-- One allowance chosen before the starting threshold and the block. -/
def SquareBoundBlocks (C : ℝ) : Prop :=
  ∀ m : ℕ, ∃ K ≥ m, ∀ k ∈ Icc K (K^2), -C*k ≤ powerMargin (k^2)

theorem square_bound_blocks_mono {C B : ℝ} (le : C ≤ B) (h : SquareBoundBlocks C) :
    SquareBoundBlocks B := by
  intro m
  obtain ⟨K,start,checks⟩ := h m
  refine ⟨K,start,fun k hk => ?_⟩
  linarith [checks k hk,mul_le_mul_of_nonneg_right le (Nat.cast_nonneg (α := ℝ) k)]

/-- If the allowance can be chosen after seeing a finite block, every real sequence
satisfies the comparison on that block. -/
theorem every_sequence_has_a_block_dependent_allowance (f : ℕ → ℝ) {K : ℕ} (hK : 0 < K) :
    ∃ C ≥ (0:ℝ), ∀ k ∈ Icc K (K^2), -C*k ≤ f k := by
  let C := ∑ i ∈ Icc K (K^2), |f i|
  have pos : 0 ≤ C := Finset.sum_nonneg (fun i _ => abs_nonneg (f i))
  refine ⟨C,pos,fun k hk => ?_⟩
  have size : |f k| ≤ C := Finset.single_le_sum (fun i _ => abs_nonneg (f i)) hk
  have one : (1:ℝ) ≤ k := by exact_mod_cast hK.trans_le (mem_Icc.mp hk).1
  have scale := mul_le_mul_of_nonneg_left one pos
  linarith [neg_abs_le (f k)]

/-- The existence of even one fixed real allowance implies RH. -/
theorem rh_of_any_square_bound {C : ℝ} (h : SquareBoundBlocks C) : RiemannHypothesis := by
  apply rh_of_square_sqrt_windows (C := max C 0) (le_max_right _ _)
  intro m
  obtain ⟨K,start,checks⟩ := square_bound_blocks_mono (le_max_left C 0) h m
  exact ⟨K,start,fun k hk => checks k (by simpa only [pow_two] using hk)⟩

theorem every_late_block_has_a_violation (failure : ¬ RiemannHypothesis) (C : ℝ) :
    ∃ m : ℕ, ∀ K ≥ m, ∃ k ∈ Icc K (K^2), powerMargin (k^2) < -C*k := by
  have no : ¬ SquareBoundBlocks C := fun h => failure (rh_of_any_square_bound h)
  simpa [SquareBoundBlocks,and_assoc] using no

/-- The finite-height spectral data and the identification of its entries as actual
zeta zeros suffice to check the converse for any allowance at least one fifth. -/
theorem square_bound_iff_rh (data : FifthSpectralData)
    (zeros : ∀ i, riemannZeta (data.zero i) = 0) {C : ℝ} (hc : 1/5 ≤ C) :
    SquareBoundBlocks C ↔ RiemannHypothesis := by
  refine ⟨rh_of_any_square_bound, fun rh => ?_⟩
  have line (i : ℕ) : (data.zero i).re = 1/2 := by
    apply rh _ (zeros i)
    · rintro ⟨n,e⟩
      have up := data.positive i
      rw [e] at up
      simp [Complex.mul_im] at up
    · intro e
      have up := data.positive i
      simp [e] at up
  intro m
  refine ⟨max 3 m,le_max_right _ _,fun k hk => ?_⟩
  have k3 : 3 ≤ k := (le_max_left 3 m).trans (mem_Icc.mp hk).1
  have j4 : 4 < k^2 := by nlinarith
  have limit := fifth_at_every_scale_of_line data line j4
  rw [Nat.cast_pow,Real.sqrt_sq (Nat.cast_nonneg k)] at limit
  linarith [mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (α := ℝ) k)]

/-- The 100k allowance holds simultaneously over every root block from K=3
through K=3,200,000, on the explicit analytic inputs recorded in FifthSpectralData. -/
theorem hundred_on_blocks_through_3200000 (data : FifthSpectralData) {K : ℕ}
    (start : 3 ≤ K) (cap : K ≤ 3200000) :
    ∀ k ∈ Icc K (K^2), -(100:ℝ)*k < powerMargin (k^2) := by
  intro k hk
  obtain ⟨lower,upper⟩ := mem_Icc.mp hk
  have k3 : 3 ≤ k := start.trans lower
  have j4 : 4 < k^2 := by nlinarith
  have kp : 0 < (k:ℝ) := Nat.cast_pos.mpr (by omega)
  have kcap : (k:ℝ) ≤ 3200000^2 := by exact_mod_cast upper.trans (Nat.pow_le_pow_left cap 2)
  have root : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  have mass : (4+3*Real.sqrt 2)*(2311/100000) < 1 := by linarith
  have ht : (checkedHeight:ℝ)^2 < (2:ℝ)^83 := by norm_num [checkedHeight]
  have logs := Real.log_lt_log (by norm_num [checkedHeight]) ht
  rw [Real.log_pow,Real.log_pow] at logs
  push_cast at logs
  have logT : Real.log checkedHeight < 29 := by linarith [Real.log_two_lt_d9]
  have tail : 3*(k:ℝ)*Real.log checkedHeight/(Real.pi*checkedHeight) ≤ 99 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.pi*checkedHeight)).mpr
    calc _ ≤ (3*(3200000:ℝ)^2)*29 := mul_le_mul (mul_le_mul_of_nonneg_left kcap (by norm_num))
           logT.le (Real.log_nonneg (by norm_num [checkedHeight])) (by norm_num)
         _ ≤ 99*(3*checkedHeight) := by norm_num [checkedHeight]
         _ ≤ 99*(Real.pi*checkedHeight) := by
           apply mul_le_mul_of_nonneg_left _ (by norm_num)
           exact mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by positivity)
  have budget := normalized_loss_of_spectral_data data j4
  rw [Nat.cast_pow,Real.sqrt_sq (Nat.cast_nonneg k)] at budget
  have div : -(100:ℝ) < powerMargin (k^2)/k := by linarith
  exact (lt_div_iff₀ kp).mp div

#print axioms rh_of_any_square_bound
#print axioms every_sequence_has_a_block_dependent_allowance
#print axioms every_late_block_has_a_violation
#print axioms square_bound_iff_rh
#print axioms hundred_on_blocks_through_3200000
end RiemannReduction.PrimeGrid
