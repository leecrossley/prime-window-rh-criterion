import SmoothedZeroBound
import MobiusBlocks

open Finset
namespace RiemannReduction.DivisorBand
noncomputable section

/-- The zero-location hypothesis alone gives one constant at every root index. -/
theorem square_root_bound_of_rh (rh : RiemannHypothesis) :
    ∃ C > (0:ℝ), ∀ k : ℕ, 3 ≤ k → |D ((k:ℝ)^2)| ≤ C*k := by
  obtain ⟨M,mp,bound⟩ := ZetaWindow.smoothed_psi_on_rh rh
  refine ⟨3*M,by positivity,fun k hk => ?_⟩
  let y := (k:ℝ)^2/4
  have k3 : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hy : 2 ≤ y := by dsimp [y]; nlinarith
  have yp : 0 < y := by linarith
  have one := abs_le.mp (bound hy le_rfl (show y ≤ 2*y by linarith) (by linarith : 2*y ≤ 4*y))
  have two := abs_le.mp (bound hy (show y ≤ 2*y by linarith) (show 2*y ≤ 4*y by linarith) le_rfl)
  have h := deficit_eq_centered_integrals (show 1 ≤ y by linarith)
  have eq : 4*y=(k:ℝ)^2 := by dsimp [y]; ring
  rw [← eq,h,abs_le]
  have sy : Real.sqrt y=(k:ℝ)/2 := by
    rw [show y=((k:ℝ)/2)^2 by dsimp [y]; ring,Real.sqrt_sq (by positivity)]
  have size : y*(M/Real.sqrt y)=M*(k:ℝ)/2 := by
    rw [sy]; dsimp [y]
    field_simp [show (k:ℝ) ≠ 0 by linarith]
    ring
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left one.1 yp.le,
    mul_le_mul_of_nonneg_left one.2 yp.le,mul_le_mul_of_nonneg_left two.1 yp.le,
    mul_le_mul_of_nonneg_left two.2 yp.le]

/-- The constant is chosen before the start of the block. No auxiliary spectral data. -/
theorem square_blocks_iff_rh : (∃ C, PrimeGrid.SquareBoundBlocks C) ↔ RiemannHypothesis := by
  refine ⟨fun ⟨_,blocks⟩ => PrimeGrid.rh_of_any_square_bound blocks,fun rh => ?_⟩
  obtain ⟨C,_,bound⟩ := square_root_bound_of_rh rh
  refine ⟨C,fun m => ⟨max 3 m,le_max_right _ _,fun k hk => ?_⟩⟩
  have lo := (abs_le.mp (bound k ((le_max_left 3 m).trans (mem_Icc.mp hk).1))).1
  have id := D_nat (k^2)
  rw [Nat.cast_pow] at id
  linarith

theorem signed_tail_blocks_iff_rh : (∃ B, TailBoundBlocks B) ↔ RiemannHypothesis :=
  signed_tail_blocks_iff_square_blocks.trans square_blocks_iff_rh

theorem unpaired_blocks_iff_rh : (∃ B, RemainderBoundBlocks B) ↔ RiemannHypothesis :=
  remainder_blocks_iff_square_blocks.trans square_blocks_iff_rh

#print axioms square_root_bound_of_rh
#print axioms square_blocks_iff_rh
#print axioms signed_tail_blocks_iff_rh
#print axioms unpaired_blocks_iff_rh
end
end RiemannReduction.DivisorBand
