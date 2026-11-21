import DivisorBand
import DyadicArithmetic

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
namespace RiemannReduction.DivisorBand
noncomputable section

/-- The prime-side dyadic expression and the divisor-side signed expression for the same margin. -/
theorem centered_ramps_eq_moebius (A : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    -Deduction.G x + 3*Deduction.G (x/2) - 2*Deduction.G (x/4) =
      A + dilate μ (residual A) x := by
  have ramps := ThetaTransfer.deficit_eq_centered_ramps (y := x/4) (by linarith)
  rw [show 4*(x/4)=x by ring,show 2*(x/4)=x/2 by ring] at ramps
  rw [← moebius_reconstruction A hx,← ramps]
  unfold D c
  ring

def rampIncrement (x : ℝ) : ℝ := Deduction.G x - 2*Deduction.G (x/2)

theorem margin_eq_increment_drop {x : ℝ} (xp : 0 < x) : D x = rampIncrement (x/2)-rampIncrement x := by
  have ramps := ThetaTransfer.deficit_eq_centered_ramps (y := x/4) (by linarith)
  rw [show 4*(x/4)=x by ring,show 2*(x/4)=x/2 by ring] at ramps
  unfold D c rampIncrement
  rw [show x/2/2=x/4 by ring]
  linarith

/-- Along a dyadic progression the signed margins telescope to the two outer increments. -/
theorem sum_dyadic_margins {x : ℝ} (xp : 0 < x) (n : ℕ) :
    ∑ j ∈ range n, D (2^(j+1)*x) = rampIncrement x-rampIncrement (2^n*x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,ih,margin_eq_increment_drop (by positivity : 0 < (2:ℝ)^(n+1)*x)]
    rw [show 2^(n+1)*x/2=2^n*x by rw [pow_succ]; ring]
    ring

#print axioms centered_ramps_eq_moebius
#print axioms sum_dyadic_margins
end
end RiemannReduction.DivisorBand
