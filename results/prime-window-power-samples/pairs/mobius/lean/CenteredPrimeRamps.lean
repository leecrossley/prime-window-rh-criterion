import MobiusRamps
import Formalism.StatementOC

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace RiemannReduction.DivisorBand
noncomputable section

private lemma ramp_agrees {x : ℝ} (hx : 0 ≤ x) : Deduction.G x = Formalism.Gz x := by
  have eq : (Deduction.ramp (fun _ => 1) x).re = Formalism.Sz x := by
    simp only [Deduction.ramp,Complex.re_sum,mul_one,← Complex.ofReal_mul,Complex.ofReal_re,
      Formalism.Sz,Nat.range_succ_eq_Icc_zero]
    let w (n : ℕ) := ArithmeticFunction.vonMangoldt n * max (x/n-1) 0
    have ext : (∑ n ∈ Icc 1 ⌊x⌋₊, w n) = ∑ n ∈ Icc 0 ⌊x⌋₊, w n := by
      apply sum_subset (Icc_subset_Icc (by decide) le_rfl)
      intro n hn off
      have nz : n=0 := by
        by_contra h
        exact off (mem_Icc.mpr ⟨by omega,(mem_Icc.mp hn).2⟩)
      simp [w,nz]
    change (∑ n ∈ Icc 0 ⌊x⌋₊, w n) = _
    rw [← ext]
    apply sum_congr rfl
    intro n hn
    have np := (mem_Icc.mp hn).1
    have le : (n:ℝ) ≤ x := (Nat.cast_le.mpr (mem_Icc.mp hn).2).trans (Nat.floor_le hx)
    simp [w,max_eq_left (sub_nonneg.mpr ((one_le_div (Nat.cast_pos.mpr np)).mpr le))]
  rw [Deduction.G,Formalism.Gz,eq]

theorem deficit_eq_gz {x : ℝ} (xp : 0 < x) :
    D x = -Formalism.Gz x + 3*Formalism.Gz (x/2) - 2*Formalism.Gz (x/4) := by
  have h := ThetaTransfer.deficit_eq_centered_ramps (y := x/4) (by linarith)
  rw [show 4*(x/4)=x by ring,show 2*(x/4)=x/2 by ring,ramp_agrees xp.le,
      ramp_agrees (by linarith : 0 ≤ x/2),ramp_agrees (by linarith : 0 ≤ x/4)] at h
  unfold D c
  linarith

end
end RiemannReduction.DivisorBand
