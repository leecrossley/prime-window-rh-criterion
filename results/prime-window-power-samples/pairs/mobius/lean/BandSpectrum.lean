import Mathlib

open Complex
open scoped ComplexConjugate

noncomputable section
namespace ThetaTransfer

/-- Mellin transform of the three-scale prime weight, away from 0 and 1. -/
def bandMellin (b : ℝ) (s : ℂ) : ℂ :=
  (((b : ℂ) ^ s - 1) * ((b : ℂ) ^ s - b)) / (s * (s-1))

/-- Every dilation greater than one preserves every frequency in the open strip. -/
theorem bandMellin_ne_zero_in_strip {b : ℝ} (hb : 1 < b) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) : bandMellin b s ≠ 0 := by
  have hbp : 0 < b := by linarith
  have hn := norm_cpow_eq_rpow_re_of_pos hbp s
  have lo : 1 < ‖(b : ℂ) ^ s‖ := hn ▸ Real.one_lt_rpow hb h0
  have hi : ‖(b : ℂ) ^ s‖ < b := by
    rw [hn]
    simpa using Real.rpow_lt_rpow_of_exponent_lt hb h1
  have z1 : (b : ℂ) ^ s ≠ 1 := fun e => by simp [e] at lo
  have zb : (b : ℂ) ^ s ≠ (b : ℂ) := fun e => by simp [e, abs_of_pos hbp] at hi
  have s0 : s ≠ 0 := fun e => by simp [e] at h0
  have s1 : s ≠ 1 := fun e => by simp [e] at h1
  exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr z1) (sub_ne_zero.mpr zb))
    (mul_ne_zero s0 (sub_ne_zero.mpr s1))

/-- On the critical line each coefficient acquires precisely the phase of b^s.
The remaining real factor, given explicitly, is strictly positive. -/
theorem bandMellin_phase {b : ℝ} (hb : 1 < b) (s : ℂ) (hs : s.re = 1/2) :
    let z := (b : ℂ) ^ s
    let a := (b+1-2*z.re) / normSq s
    bandMellin b s = z * (a : ℂ) ∧ 0 < a := by
  let z := (b : ℂ) ^ s
  change bandMellin b s = z * (((b+1-2*z.re) / normSq s : ℝ) : ℂ) ∧ _
  have hbp : 0 < b := by linarith
  have hn : ‖z‖ = Real.sqrt b := by
    rw [show ‖z‖ = b ^ s.re from norm_cpow_eq_rpow_re_of_pos hbp s, hs, Real.sqrt_eq_rpow]
  have nb : normSq z = b := by rw [normSq_eq_norm_sq, hn, Real.sq_sqrt hbp.le]
  have prod : z * conj z = (b : ℂ) := by rw [mul_conj, nb]
  have num : (z-1)*(z-b) = -z * ((b+1-2*z.re : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, ← Complex.add_conj, Complex.ofReal_add, Complex.ofReal_one]
    linear_combination -prod
  have sc : s-1 = -conj s := by
    apply Complex.ext <;> simp [hs]
    ring
  have den : s*(s-1) = -(normSq s : ℂ) := by rw [sc, mul_neg, mul_conj]
  have sn : 0 < normSq s := normSq_pos.mpr (fun h => by simp [h] at hs)
  constructor
  · change (z-1)*(z-b)/(s*(s-1)) = _
    rw [num, den, Complex.ofReal_div]
    ring
  · apply div_pos _ sn
    have root : 1 < Real.sqrt b := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) hb
    have zr := Complex.re_le_norm z
    rw [hn] at zr
    nlinarith [Real.sq_sqrt hbp.le, sq_pos_of_pos (sub_pos.mpr root)]

#print axioms ThetaTransfer.bandMellin_phase
#print axioms ThetaTransfer.bandMellin_ne_zero_in_strip

end ThetaTransfer
